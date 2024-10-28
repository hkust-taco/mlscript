package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import hkmc2.{semantics => sem}
import hkmc2.semantics.{Term => st}

import syntax.{Literal, Tree}
import semantics.*
import semantics.Term.*


abstract class Ret extends (Result => Block)
object Ret extends Ret:
  def apply(r: Result): Block = Return(r, implct = false)
object ImplctRet extends Ret:
  def apply(r: Result): Block = Return(r, implct = true)


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
    tl.log(s"Lowering.term ${t.showDbg.truncate(30, "[...]")}")
    t match
    case st.Lit(lit) =>
      k(Value.Lit(lit))
    case st.Ret(res) =>
      returnedTerm(res)
    case st.Asc(lhs, rhs) =>
      term(lhs)(k)
    case st.Tup(fs) =>
      fs.foldRight[Ls[Path] => Block](args => k(Value.Arr(args.reverse)))((a, acc) =>
        args => subTerm(a.value)(r => acc(r :: args))
      )(Nil)
    case st.Ref(sym) =>
      sym match
      case sym: LocalSymbol =>
        k(subst(Value.Ref(sym)))
      case sym: ClassSymbol =>
        k(subst(Value.Ref(sym)))
      /* // * Old logic that auto-lifted `C` ~> `(...) => new C(...)`
      case sym: ClassSymbol => // TODO rm
        // k(subst(Value.Ref(sym)))
        sym.defn match
        case N => End("error: class has no declaration") // TODO report?
        case S(clsDefn) =>
          if clsDefn.kind is syntax.Mod then
            k(Value.Ref(sym))
          else
            val ps = clsDefn.paramsOpt.getOrElse(Nil)
            val psSyms = ps.map(p => 
              p.copy(sym = new VarSymbol(p.sym.id, summon[Elaborator.State].nextUid)))
            k(Value.Lam(psSyms,
              Return(Instantiate(Value.Ref(sym),
                psSyms.map(p => Value.Ref(p.sym))), false)))
      */
    // * Perhaps this `new` insertion should also be removed...?
    case st.App(Ref(sym: ClassSymbol), Tup(args)) => // TODO check kind is Cls
      args.foldRight[Ls[Path] => Block](args => k(Instantiate(Value.Ref(sym), args.reverse)))((a, acc) =>
        args => subTerm(a.value)(r => acc(r :: args))
      )(Nil)
    case st.App(f, arg) =>
      arg match
      case Tup(fs) =>
        val as = fs.map:
          case sem.Fld(sem.FldFlags.empty, value, N) => value
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
          case _: syntax.Val =>
            assert(td.params.isEmpty)
            term(bod)(r =>
              Assign(td.sym, r,
                term(st.Blk(stats, res))(k)))
          case _ =>
            Define(TermDefn(td.k, td.sym, td.params, returnedTerm(bod)),
              term(st.Blk(stats, res))(k))
      case cls: ClassDef =>
        val bodBlk = cls.body.blk
        val (mtds, rest1) = bodBlk.stats.partitionMap:
          case td: TermDefinition if td.k is syntax.Fun => L(td)
          case s => R(s)
        val (flds, rest2) = rest1.partitionMap:
          case LetDecl(sym: TermSymbol) => L(sym)
          case s => R(s)
        Define(ClsDefn(cls.sym, syntax.Cls,
            mtds.flatMap: td =>
              td.body.map: bod =>
                TermDefn(td.k, td.sym, td.params, term(bod)(Ret))
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
    
    case iftrm: st.If =>
      
      tl.log(s"If $iftrm")
      
      var usesResTmp = false
      lazy val l =
        usesResTmp = true
        new TempSymbol(summon[Elaborator.State].nextUid, S(t))
      
      def go(split: Split)(using Subst): Block = split match
        case Split.Let(sym, trm, tl) =>
          term(trm): r =>
            Assign(sym, r, go(tl))
        case Split.Cons(Branch(scrut, pat, tail), restSplit) =>
          subTerm(scrut): sr =>
            tl.log(s"Binding scrut $scrut to $sr ${summon[Subst].map}")
            val cse = pat match
              case Pattern.LitPat(lit) => Case.Lit(lit) -> go(tail)
              case Pattern.Class(cls, args0, _refined) =>
                val args = args0.getOrElse(Nil)
                val clsDefn = cls.defn.getOrElse(die)
                val clsParams = clsDefn.paramsOpt.getOrElse(Nil)
                assert(args0.isEmpty || clsParams.length === args.length)
                def mkArgs(args: Ls[Param -> BlockLocalSymbol])(using Subst): Case -> Block = args match
                  case Nil => Case.Cls(cls) -> go(tail)
                  case (param, arg) :: args =>
                    // summon[Subst].+(arg -> Value.Ref(new TempSymbol(summon[Elaborator.State].nextUid, N)))
                    // Assign(arg, Select(sr, Tree.Ident("head")), mkArgs(args))
                    val (cse, blk) = mkArgs(args)
                    (cse, Assign(arg, Select(sr, param.sym.id/*FIXME incorrect Ident?*/), blk))
                mkArgs(clsParams.zip(args))
            Match(sr, cse :: Nil,
              // elseBranch,
              S(go(restSplit)),
              End()
            )
        case Split.Else(els) =>
          if k.isInstanceOf[Ret] then term(els)(k)
          else term(els)(r => Assign(l, r, End()))
        case Split.Nil =>
          Throw(Instantiate(Value.Ref(Elaborator.Ctx.errorSymbol),
            Value.Lit(syntax.Tree.StrLit("match error")) :: Nil)) // TODO add failed-match scrutinee info
      
      if k.isInstanceOf[Ret] then go(iftrm.normalized)
      else Begin(
          go(iftrm.normalized),
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


