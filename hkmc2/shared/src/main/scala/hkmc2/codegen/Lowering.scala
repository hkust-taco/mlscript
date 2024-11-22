package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import hkmc2.{semantics => sem}
import hkmc2.semantics.{Term => st}

import syntax.{Literal, Tree}
import semantics.*
import semantics.Term.{Throw => _, *}


abstract class TailOp extends (Result => Block)
object Ret extends TailOp:
  def apply(r: Result): Block = Return(r, implct = false)
object ImplctRet extends TailOp:
  def apply(r: Result): Block = Return(r, implct = true)
object Thrw extends TailOp:
  def apply(r: Result): Block = Throw(r)


class Subst(initMap: Map[Local, Value]):
  val map = initMap
  def +(kv: (Local, Value)): Subst =
    kv match
    case (ns: NamedSymbol, Value.Ref(ts: TempSymbol)) =>
      ts.nameHints += ns.name
    case _ =>
    Subst(map + kv)
  def apply(v: Value): Value = v match
    case Value.Ref(l) => map.getOrElse(l, v)
    case _ => v
object Subst:
  val empty = Subst(Map.empty)
  def subst(using sub: Subst): Subst = sub
end Subst

import Subst.subst


class Lowering(using TL, Raise, Elaborator.State):
  
  def returnedTerm(t: st)(using Subst): Block = term(t)(Ret)
  
  def term(t: st)(k: Result => Block)(using Subst): Block =
    tl.log(s"Lowering.term ${t.showDbg.truncate(100, "[...]")}")
    t match
    case st.Lit(lit) =>
      k(Value.Lit(lit))
    case st.Ret(res) =>
      returnedTerm(res)
    case st.Throw(res) =>
      term(res)(Thrw)
    case st.Asc(lhs, rhs) =>
      term(lhs)(k)
    case st.Tup(fs) =>
      fs.foldRight[Ls[Path] => Block](args => k(Value.Arr(args.reverse)))((a, acc) =>
        args => subTerm(a.value)(r => acc(r :: args))
      )(Nil)
    case st.Ref(sym) =>
      k(subst(Value.Ref(sym)))
    case st.App(f, arg) =>
      arg match
      case Tup(fs) =>
        val as = fs.map:
          case sem.Fld(sem.FldFlags.empty, value, N) => value
          case sem.Fld(sem.FldFlags(false, false, false, true), value, N) => value
          case sem.Fld(flags, value, asc) =>
            TODO("Other argument forms")
        val l = new TempSymbol(summon[Elaborator.State].nextUid, S(t))
        subTerm(f): fr =>
          def rec(as: Ls[st], asr: Ls[Path]): Block = as match
            case Nil => k(Call(fr, asr.reverse))
            case a :: as =>
              subTerm(a): ar =>
                rec(as, ar :: asr)
          rec(as, Nil)
      case _ =>
        TODO("Other argument list forms")
    case st.Blk(Nil, res) => term(res)(k)
    case st.Blk(Lit(Tree.UnitLit(true)) :: stats, res) =>
      subTerm(st.Blk(stats, res))(k)
    case st.Blk((p @ (_: Ref | _: Lit)) :: stats, res) =>
      raise(WarningReport(msg"Pure expression in statement position" -> p.toLoc :: Nil))
      subTerm(st.Blk(stats, res))(k)
    case st.Blk((t: sem.Term) :: stats, res) =>
      subTerm(t)(r => term(st.Blk(stats, res))(k))
    case st.Blk((d: Declaration) :: stats, res) =>
      d match
      case td: TermDefinition =>
        td.body match
        case N => // abstract declarations have no lowering
          term(st.Blk(stats, res))(k)
        case S(bod) =>
          td.k match
          case knd: syntax.Val =>
            assert(td.params.isEmpty)
            subTerm(bod)(r =>
              // Assign(td.sym, r,
              //   term(st.Blk(stats, res))(k)))
              Define(ValDefn(td.owner, knd, td.sym, r),
                term(st.Blk(stats, res))(k)))
          case syntax.Fun =>
            Define(FunDefn(td.sym, td.params, returnedTerm(bod)),
              term(st.Blk(stats, res))(k))
      // case cls: ClassDef =>
      case cls: ClassLikeDef =>
        val bodBlk = cls.body.blk
        val (mtds, rest1) = bodBlk.stats.partitionMap:
          case td: TermDefinition if td.k is syntax.Fun => L(td)
          case s => R(s)
        val (flds, rest2) = rest1.partitionMap:
          case LetDecl(sym: TermSymbol) => L(sym)
          case s => R(s)
        Define(ClsLikeDefn(cls.sym, syntax.Cls,
            mtds.flatMap: td =>
              td.body.map: bod =>
                FunDefn(td.sym, td.params, term(bod)(Ret))
            ,
            flds, term(Blk(rest2, bodBlk.res))(ImplctRet).mapTail:
              case Return(Value.Lit(syntax.Tree.UnitLit(true)), true) => End()
              case t => t
          ),
        term(st.Blk(stats, res))(k))
      case _ =>
        // TODO handle
        term(st.Blk(stats, res))(k)
    case st.Blk((LetDecl(sym)) :: stats, res) =>
      term(st.Blk(stats, res))(k)
    case st.Blk((DefineVar(sym, rhs)) :: stats, res) =>
      subTerm(rhs): r =>
        Assign(sym, r, term(st.Blk(stats, res))(k))
    case Assgn(lhs, rhs) =>
      lhs match
      case Ref(sym: LocalSymbol) =>
        subTerm(rhs): r =>
          Assign(sym, r, k(Value.Lit(syntax.Tree.UnitLit(true))))
      case Sel(prefix, nme) =>
        subTerm(prefix): p =>
          subTerm(rhs): r =>
            AssignField(p, nme, r, k(Value.Lit(syntax.Tree.UnitLit(true))))
      
    case st.Blk((imp @ Import(sym, path)) :: stats, res) =>
      raise(ErrorReport(
        msg"Imports must be at the top level" ->
        imp.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      term(st.Blk(stats, res))(k)
      
    case st.Lam(params, body) =>
      k(Value.Lam(params, returnedTerm(body)))
    
    /* 
    case t @ st.If(Split.Let(sym, trm, tail)) =>
      // term(st.Blk(semantics.LetDecl(sym) :: semantics.DefineVar(sym, trm) :: Nil, st.If(tail)(t.normalized)))(k)
      term(trm): r =>
        Assign(sym, r, term(st.If(tail)(t.normalized))(k))
    
    // TODO rm
    case st.If(Split.Cons(
      Branch(scrut, Pattern.LitPat(tru @ Tree.BoolLit(true)), Split.Else(thn)),
      restSplit
    )) =>
      
      val elseBranch = restSplit match
        case Split.Else(els) => S(els)
        case Split.Nil => N
      
      elseBranch match
      case S(els) if k.isInstanceOf[Ret] =>
        subTerm(scrut): sr =>
          // Match(sr, Case.Lit(tru) -> term(thn)(k) :: Nil,
          //   Some(term(els)(k)), 
          //   Unreachable
          // )
          Match(sr, Case.Lit(tru) -> term(thn)(k) :: Nil,
            N, 
            term(els)(k)
          )
      case _ =>
        val l = new TempSymbol(summon[Elaborator.State].nextUid, S(t))
        subTerm(scrut): sr =>
            Match(sr, Case.Lit(tru) -> subTerm(thn)(r => Assign(l, r, End())) :: Nil,
              elseBranch.map(els => subTerm(els)(r => Assign(l, r, End()))),
              k(Value.Ref(l))
            )
    */
    
    case iftrm: st.IfLike =>
      
      tl.log(s"${iftrm.kw} $iftrm")
      
      val isIf = iftrm.kw match
        case syntax.Keyword.`if` => true
        case syntax.Keyword.`while` => false
      val isWhile = !isIf
      
      var usesResTmp = false
      lazy val l =
        usesResTmp = true
        new TempSymbol(summon[Elaborator.State].nextUid, S(t))
      
      lazy val lbl =
        new TempSymbol(summon[Elaborator.State].nextUid, S(t))
      
      def go(split: Split, topLevel: Bool)(using Subst): Block = split match
        case Split.Let(sym, trm, tl) =>
          term(trm): r =>
            Assign(sym, r, go(tl, topLevel))
        case Split.Cons(Branch(scrut, pat, tail), restSplit) =>
          subTerm(scrut): sr =>
            tl.log(s"Binding scrut $scrut to $sr ${summon[Subst].map}")
            // val cse = 
            def mkMatch(cse: Case -> Block) = Match(sr, cse :: Nil,
                S(go(restSplit, topLevel = true)),
                End()
              )
            pat match
              case Pattern.Lit(lit) => mkMatch(Case.Lit(lit) -> go(tail, topLevel = false))
              case Pattern.ClassLike(cls, trm, args0, _refined) =>
                subTerm(trm): st =>
                  val args = args0.getOrElse(Nil)
                  val clsParams = cls match
                    case cls: ClassSymbol => cls.tree.params
                    case _: ModuleSymbol => Nil
                  assert(args0.isEmpty || clsParams.length === args.length)
                  def mkArgs(args: Ls[(LocalSymbol & NamedSymbol) -> BlockLocalSymbol])(using Subst): Case -> Block = args match
                  // def mkArgs(args: Ls[Param -> BlockLocalSymbol])(using Subst): Block = args match
                    case Nil =>
                      // mkMatch(Case.Cls(cls, st) -> go(tail, topLevel = false))
                      Case.Cls(cls, st) -> go(tail, topLevel = false)
                    case (param, arg) :: args =>
                      // summon[Subst].+(arg -> Value.Ref(new TempSymbol(summon[Elaborator.State].nextUid, N)))
                      // Assign(arg, Select(sr, Tree.Ident("head")), mkArgs(args))
                      
                      val (cse, blk) = mkArgs(args)
                      (cse, Assign(arg, Select(sr, param.id/*FIXME incorrect Ident?*/), blk))
                      // mkMatch(cse -> Assign(arg, Select(sr, param.sym.id/*FIXME incorrect Ident?*/), blk))
                      // Assign(arg, Select(sr, param.sym.id/*FIXME incorrect Ident?*/), mkArgs(args))
                      
                  // val (cse, blk) =
                  // mkMatch(cse -> blk)
                  mkMatch(mkArgs(clsParams.zip(args)))
              case Pattern.Tuple(len, inf) => mkMatch(Case.Tup(len, inf) -> go(tail, topLevel = false))
            // Match(sr, cse :: Nil,
            //   S(go(restSplit, topLevel = true)),
            //   End()
            // )
        case Split.Else(els) =>
          if k.isInstanceOf[TailOp] && isIf then term(els)(k)
          else
            term(els): r =>
              Assign(l, r,
                if isWhile && !topLevel then Break(lbl, toBeginning = true)
                // if isWhile then Break(lbl, toBeginning = !topLevel)
                else End()
              )
        case Split.End =>
          Throw(Instantiate(Select(Value.Ref(Elaborator.Ctx.globalThisSymbol), Tree.Ident("Error")),
            Value.Lit(syntax.Tree.StrLit("match error")) :: Nil)) // TODO add failed-match scrutinee info
      
      if k.isInstanceOf[TailOp] && isIf then go(iftrm.normalized, topLevel = true)
      else
        val body = if isWhile
          then Label(lbl, go(iftrm.normalized, topLevel = true), End())
          else go(iftrm.normalized, topLevel = true)
        Begin(
          body,
          if usesResTmp then k(Value.Ref(l))
          else k(Value.Lit(syntax.Tree.UnitLit(true))) // * it seems this currently never happens
        )
      
    case Sel(prefix, nme) =>
      subTerm(prefix): p =>
        k(Select(p, nme))
        
    case New(cls, as) =>
      subTerm(cls): sr =>
        def rec(as: Ls[st], asr: Ls[Path]): Block = as match
          case Nil => k(Instantiate(sr, asr.reverse))
          case a :: as =>
            subTerm(a): ar =>
              rec(as, ar :: asr)
        rec(as, Nil)
    
    case Try(sub, finallyDo) =>
      val l = new TempSymbol(summon[Elaborator.State].nextUid, S(sub))
      TryBlock(
        term(sub)(p => Assign(l, p, End())),
        term(finallyDo)(_ => End()),
        k(Value.Ref(l))
      )
    
    case Error => End("error")
    
    // case _ =>
    //   subTerm(t)(k)
  
  def subTerm(t: st)(k: Path => Block)(using Subst): Block =
    term(t):
      case v: Value => k(v)
      case p: Path => k(p)
      case r =>
        val l = new TempSymbol(summon[Elaborator.State].nextUid, N)
        Assign(l, r, k(l |> Value.Ref.apply))
  
  
  // val resSym = new TermSymbol(N, Tree.Ident("$res"))
  // def topLevel(t: st): Block =
  //   subTerm(t)(r => codegen.Assign(resSym, r, codegen.End()))(using Subst.empty)
  
  def topLevel(t: st): Block =
    term(t)(ImplctRet)(using Subst.empty)
  
  def program(main: st): Program =
    def go(acc: Ls[Local -> Str], trm: st): Program =
      trm match
      case st.Blk((imp @ Import(sym, path)) :: stats, res) =>
        go(sym -> path.toString :: acc, st.Blk(stats, res))
      case _ => Program(acc.reverse, topLevel(trm))
    go(Nil, main)


