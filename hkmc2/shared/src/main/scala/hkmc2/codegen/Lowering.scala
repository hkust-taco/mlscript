package hkmc2
package codegen

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import hkmc2.{semantics => sem}
import hkmc2.semantics.{Term => st}
import semantics.Elaborator.State

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
      fs.foldRight[Ls[Arg] => Block](args => k(Value.Arr(args.reverse))){
        case (a: Fld, acc) =>
          args => subTerm(a.term)(r => acc(Arg(false, r) :: args))
        case (s: Spd, acc) =>
          args => subTerm(s.term)(r => acc(Arg(true, r) :: args))
      }(Nil)
    case st.Ref(sym) =>
      k(subst(Value.Ref(sym)))
    case st.App(f, arg) =>
      val isMlsFun = f.symbol.fold(f.isInstanceOf[st.Lam]):
        case _: sem.BuiltinSymbol => true
        case sym: sem.BlockMemberSymbol =>
          sym.trmImplTree.fold(sym.clsTree.isDefined)(_.k is syntax.Fun)
        case _ => false
      arg match
      case Tup(fs) =>
        val as = fs.map:
          case sem.Fld(sem.FldFlags.empty, value, N) => false -> value
          case sem.Fld(sem.FldFlags(false, false, false, true), value, N) => false -> value
          case sem.Fld(flags, value, asc) =>
            TODO("Other argument forms")
          case spd: Spd => true -> spd.term
        val l = new TempSymbol(S(t))
        subTerm(f): fr =>
          def rec(as: Ls[Bool -> st], asr: Ls[Arg]): Block = as match
            case Nil => k(Call(fr, asr.reverse)(isMlsFun))
            case (spd, a) :: as =>
              subTerm(a): ar =>
                rec(as, Arg(spd, ar) :: asr)
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
            val (paramLists, bodyBlock) = setupFunctionDef(td.params, bod, S(td.sym.nme))
            Define(FunDefn(td.sym, paramLists, bodyBlock),
              term(st.Blk(stats, res))(k))
      // case cls: ClassDef =>
      case cls: ClassLikeDef =>
        val bodBlk = cls.body.blk
        val (mtds, rest1) = bodBlk.stats.partitionMap:
          case td: TermDefinition if td.k is syntax.Fun => L(td)
          case s => R(s)
        val (privateFlds, rest2) = rest1.partitionMap:
          case LetDecl(sym: TermSymbol) => L(sym)
          case s => R(s)
        val publicFlds = rest2.collect:
          case td @ TermDefinition(k = (_: syntax.Val)) => td
        Define(ClsLikeDefn(cls.sym, syntax.Cls, N,
            mtds.flatMap: td =>
              td.body.map: bod =>
                val (paramLists, bodyBlock) = setupFunctionDef(td.params, bod, S(td.sym.nme))
                FunDefn(td.sym, paramLists, bodyBlock)
            ,
            privateFlds,
            publicFlds,
            End(),
            term(Blk(rest2, bodBlk.res))(ImplctRet).mapTail:
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
      case sel @ SynthSel(prefix, nme) =>
        subTerm(prefix): p =>
          subTerm(rhs): r =>
            AssignField(p, nme, r, k(Value.Lit(syntax.Tree.UnitLit(true))))(sel.sym)
      case sel @ Sel(prefix, nme) =>
        subTerm(prefix): p =>
          subTerm(rhs): r =>
            AssignField(p, nme, r, k(Value.Lit(syntax.Tree.UnitLit(true))))(sel.sym)
      
    case st.Blk((imp @ Import(sym, path)) :: stats, res) =>
      raise(ErrorReport(
        msg"Imports must be at the top level" ->
        imp.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      term(st.Blk(stats, res))(k)
      
    case st.Lam(params, body) =>
      val (paramLists, bodyBlock) = setupFunctionDef(params :: Nil, body, N)
      if k.isInstanceOf[TailOp] || bodyBlock.size <= 5
      then k(Value.Lam(paramLists.head, bodyBlock))
      else
        val l = new TempSymbol(N)
        Assign(l, Value.Lam(paramLists.head, bodyBlock), k(l |> Value.Ref.apply))
    
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
        val l = new TempSymbol(S(t))
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
        new TempSymbol(S(t))
      
      lazy val lbl =
        new TempSymbol(S(t))
      
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
                    case cls: ClassSymbol => cls.tree.clsParams
                    case _: ModuleSymbol => Nil
                  assert(args0.isEmpty || clsParams.length === args.length)
                  def mkArgs(args: Ls[TermSymbol -> BlockLocalSymbol])(using Subst): Case -> Block = args match
                    case Nil =>
                      Case.Cls(cls, st) -> go(tail, topLevel = false)
                    case (param, arg) :: args =>
                      val (cse, blk) = mkArgs(args)
                      (cse, Assign(arg, Select(sr, param.id/*FIXME incorrect Ident?*/)(S(param)), blk))
                  mkMatch(mkArgs(clsParams.zip(args)))
              case Pattern.Tuple(len, inf) => mkMatch(Case.Tup(len, inf) -> go(tail, topLevel = false))
        case Split.Else(els) =>
          if k.isInstanceOf[TailOp] && isIf then term(els)(k)
          else
            term(els): r =>
              Assign(l, r,
                if isWhile && !topLevel then Continue(lbl)
                else End()
              )
        case Split.End =>
          Throw(Instantiate(Select(Value.Ref(State.globalThisSymbol), Tree.Ident("Error"))(N),
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
      
    case sel @ SynthSel(prefix, nme) =>
      subTerm(prefix): p =>
        k(Select(p, nme)(sel.sym))
        
    case sel @ Sel(prefix, nme) =>
      setupSelection(prefix, nme, sel.sym)(k)
        
        
    case New(cls, as) =>
      subTerm(cls): sr =>
        def rec(as: Ls[st], asr: Ls[Path]): Block = as match
          case Nil => k(Instantiate(sr, asr.reverse))
          case a :: as =>
            subTerm(a): ar =>
              rec(as, ar :: asr)
        rec(as, Nil)
    
    case Try(sub, finallyDo) =>
      val l = new TempSymbol(S(sub))
      TryBlock(
        term(sub)(p => Assign(l, p, End())),
        term(finallyDo)(_ => End()),
        k(Value.Ref(l))
      )

    case Handle(lhs, rhs, defs) =>
      raise(ErrorReport(
        msg"Effect handlers are not enabled" ->
        t.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      End("error")
    
    // * BbML-specific cases: t.Cls#field and mutable operations
    case SelProj(prefix, _, proj) =>
      setupSelection(prefix, proj, N)(k)
    case Region(reg, body) =>
      Assign(reg, Instantiate(Select(Value.Ref(State.globalThisSymbol), Tree.Ident("Region"))(N), Nil), term(body)(k))
    case RegRef(reg, value) =>
      def rec(as: Ls[st], asr: Ls[Path]): Block = as match
        case Nil => k(Instantiate(Select(Value.Ref(State.globalThisSymbol), Tree.Ident("Ref"))(N), asr.reverse))
        case a :: as =>
          subTerm(a): ar =>
            rec(as, ar :: asr)
      rec(reg :: value :: Nil, Nil)
    case Deref(ref) =>
      subTerm(ref): r =>
        k(Select(r, Tree.Ident("value"))(N))
    case SetRef(lhs, rhs) =>
      subTerm(lhs): ref =>
        subTerm(rhs): value =>
          AssignField(ref, Tree.Ident("value"), value, k(value))(N)

    case Error => End("error")
    
    // case _ =>
    //   subTerm(t)(k)
  
  def subTerm(t: st)(k: Path => Block)(using Subst): Block =
    term(t):
      case v: Value => k(v)
      case p: Path => k(p)
      case r =>
        val l = new TempSymbol(N)
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
  
  def setupSelection(prefix: Term, nme: Tree.Ident, sym: Opt[FieldSymbol])(k: Result => Block)(using Subst): Block =
    subTerm(prefix): p =>
      k(Select(p, nme)(sym))
  
  def setupFunctionDef(paramLists: List[ParamList], bodyTerm: Term, name: Option[Str])(using Subst): (List[ParamList], Block) =
    (paramLists, returnedTerm(bodyTerm))


trait LoweringSelSanityChecks
    (instrument: Bool)(using TL, Raise, Elaborator.State)
    extends Lowering:
  
  override def setupSelection(prefix: st, nme: Tree.Ident, sym: Opt[FieldSymbol])(k: Result => Block)(using Subst): Block =
    if instrument then
      subTerm(prefix): p =>
        val selRes = TempSymbol(N, "selRes")
        val split = Split.Cons(
            Branch(
              selRes.ref(),
              Pattern.Lit(syntax.Tree.UnitLit(false)),
              Split.Else(
                Term.Throw(Term.New(SynthSel(State.globalThisSymbol.ref(), Tree.Ident("Error"))(N),
                  Term.Lit(syntax.Tree.StrLit(s"Access to required field '${nme.name}' yielded 'undefined'")) :: Nil)
                ))),
            Split.Else(selRes.ref()))
        Assign(
          selRes,
          Select(p, nme)(sym),
          term(IfLike(syntax.Keyword.`if`, split)(split))(k))
    else
      super.setupSelection(prefix, nme, sym)(k)



trait LoweringTraceLog
    (instrument: Bool)(using TL, Raise, Elaborator.State)
    extends Lowering:
      
  private def selFromGlobalThis(path: Str*): Path =
      path.foldLeft[Path](Value.Ref(State.globalThisSymbol)):
        (qual, name) => Select(qual, Tree.Ident(name))(N)
    
  private def assignStmts(stmts: (Local, Result)*)(rest: Block) =
    stmts.foldRight(rest):
      case ((sym, res), acc) => Assign(sym, res, acc)
  
  private def call(fn: Path, args: Ls[Arg]): Call =
    Call(fn, args)(true)
  
  extension (k: Block => Block)
    def |>: (b: Block): Block = k(b)

  private val traceLogFn = selFromGlobalThis("Predef", "TraceLogger", "log")
  private val traceLogIndentFn = selFromGlobalThis("Predef", "TraceLogger", "indent")
  private val traceLogResetFn = selFromGlobalThis("Predef", "TraceLogger", "resetIndent")
  private val strConcatFn = selFromGlobalThis("String", "prototype", "concat", "call")
  private val inspectFn = selFromGlobalThis("util", "inspect")
  

  override def setupFunctionDef(paramLists: List[ParamList], bodyTerm: st, name: Option[Str])(using Subst): (List[ParamList], Block) = 
    if instrument then
      val (ps, bod) = handleMultipleParamLists(paramLists, bodyTerm)
      val instrumentedBody = setupFunctionBody(ps, bod, name)
      (ps :: Nil, instrumentedBody)
    else
      super.setupFunctionDef(paramLists, bodyTerm, name)

  def handleMultipleParamLists(paramLists: List[ParamList], bod: Term) =
    def go(paramLists: List[ParamList], bod: Term): (ParamList, Term) =
      paramLists match
        case Nil => ???
        case h :: Nil => (h, bod)
        case h :: t => go(t, Term.Lam(h, bod))
    go(paramLists.reverse, bod)
  
  def setupFunctionBody(params: ParamList, bod: Term, name: Option[Str])(using Subst): Block =
    val enterMsgSym = TempSymbol(N, dbgNme = "traceLogEnterMsg")
    val prevIndentLvlSym = TempSymbol(N, dbgNme = "traceLogPrevIndent")
    val resSym = TempSymbol(N, dbgNme = "traceLogRes")
    val retMsgSym = TempSymbol(N, dbgNme = "traceLogRetMsg")
    val psInspectedSyms = params.params.map(p => TempSymbol(N, dbgNme = s"traceLogParam_${p.sym.nme}") -> p.sym)
    val resInspectedSym = TempSymbol(N, dbgNme = "traceLogResInspected")
    
    val psSymArgs = psInspectedSyms.zipWithIndex.foldRight[Ls[Arg]](Arg(false, Value.Lit(Tree.StrLit(")"))) :: Nil):
      case (((s, p), i), acc) => if i == psInspectedSyms.length - 1
        then Arg(false, Value.Ref(s)) :: acc
        else Arg(false, Value.Ref(s)) :: Arg(false, Value.Lit(Tree.StrLit(", "))) :: acc
    
    assignStmts(psInspectedSyms.map: (pInspectedSym, pSym) =>
      pInspectedSym -> call(inspectFn, Arg(false, Value.Ref(pSym)) :: Nil)
    *) |>:
    assignStmts(
      enterMsgSym -> call(
        strConcatFn,
        Arg(false, Value.Lit(Tree.StrLit(s"CALL ${name.getOrElse("[arrow function]")}("))) :: psSymArgs
      ),
      TempSymbol(N) -> call(traceLogFn, Arg(false, Value.Ref(enterMsgSym)) :: Nil),
      prevIndentLvlSym -> call(traceLogIndentFn, Nil)
    ) |>: 
    term(bod)(r =>
    assignStmts(
      resSym -> r,
      resInspectedSym -> call(inspectFn, Arg(false, Value.Ref(resSym)) :: Nil),
      retMsgSym -> call(
        strConcatFn,
        Arg(false, Value.Lit(Tree.StrLit("=> "))) :: Arg(false, Value.Ref(resInspectedSym)) :: Nil
      ),
      TempSymbol(N) -> call(traceLogResetFn, Arg(false, Value.Ref(prevIndentLvlSym)) :: Nil),
      TempSymbol(N) -> call(traceLogFn, Arg(false, Value.Ref(retMsgSym)) :: Nil)
    ) |>:
      Ret(Value.Ref(resSym))
    )


trait LoweringHandler
    (instrument: Bool)(using TL, Raise, Elaborator.State)
    extends Lowering:
  override def term(t: st)(k: Result => Block)(using Subst): Block =
    if !instrument then return super.term(t)(k)
    t match
    case st.Blk(Handle(lhs, rhs, defs) :: stmts, res) =>
      val handlers = defs.map {
        case HandlerTermDefinition(resumeSym, td) => td.body match
          case None => 
            raise(ErrorReport(msg"Handler function definitions cannot be empty" -> td.toLoc :: Nil))
            N
          case Some(bod) =>
            val (paramLists, bodyBlock) = setupFunctionDef(td.params, bod, S(td.sym.nme))      
            S(Handler(td.sym, resumeSym, paramLists, bodyBlock))
      }.collect{ case Some(v) => v }
      val resSym = TempSymbol(S(t))
      subTerm(rhs): cls =>
        HandleBlock(lhs, resSym, cls, handlers, term(st.Blk(stmts, res))(HandleBlockReturn(_)), k(Value.Ref(resSym)))
    case _ => super.term(t)(k)
