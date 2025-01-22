package hkmc2
package codegen

import scala.language.implicitConversions
import scala.annotation.tailrec

import mlscript.utils.*, shorthands.*
import utils.*

import hkmc2.Message.MessageContext

import semantics.*
import hkmc2.{semantics => sem}
import semantics.{Term => st}
import semantics.Term.{Throw => _, *}
import semantics.Elaborator.{State, Ctx}

import syntax.{Literal, Tree}


abstract class TailOp extends (Result => Block)
object Ret extends TailOp:
  def apply(r: Result): Block = Return(r, implct = false)
object ImplctRet extends TailOp:
  def apply(r: Result): Block = Return(r, implct = true)
object Thrw extends TailOp:
  def apply(r: Result): Block = Throw(r)


// * No longer in meaningful use and could be removed if we don't find a use for it:
class Subst(initMap: Map[Local, Value]):
  val map = initMap
  /*
  def +(kv: (Local, Value)): Subst =
    kv match
    case (ns: NamedSymbol, Value.Ref(ts: TempSymbol)) =>
      ts.nameHints += ns.name
    case _ =>
    Subst(map + kv)
  */
  def apply(v: Value): Value = v match
    case Value.Ref(l) => map.getOrElse(l, v)
    case _ => v
object Subst:
  val empty = Subst(Map.empty)
  def subst(using sub: Subst): Subst = sub
end Subst

import Subst.subst


class Lowering(lowerHandlers: Bool, stackLimit: Option[Int])(using TL, Raise, State, Ctx):
  
  def returnedTerm(t: st)(using Subst): Block = term(t)(Ret)
  
  // * Used to work around Scala's @tailrec annotation for those few calls that are not in tail position.
  final def term_nonTail(t: st, inStmtPos: Bool = false)(k: Result => Block)(using Subst): Block =
    term(t: st, inStmtPos: Bool)(k)
  
  @tailrec
  final def term(t: st, inStmtPos: Bool = false)(k: Result => Block)(using Subst): Block =
    tl.log(s"Lowering.term ${t.showDbg.truncate(100, "[...]")}${
      if inStmtPos then " (in stmt)" else ""}${
      t.symbol.fold("")(" – symbol " + _)}")
    def warnStmt = if inStmtPos then
      raise(WarningReport:
        msg"Pure expression in statement position" -> t.toLoc :: Nil)
    t match
    case st.Lit(lit) =>
      if lit =/= Tree.UnitLit(true) then warnStmt
      k(Value.Lit(lit))
    case st.Ret(res) =>
      returnedTerm(res)
    case st.Throw(res) =>
      term(res)(Thrw)
    case st.Asc(lhs, rhs) =>
      term(lhs, inStmtPos = inStmtPos)(k)
    case st.Tup(fs) =>
      fs.foldRight[Ls[Arg] => Block](args => k(Value.Arr(args.reverse))){
        case (a: Fld, acc) =>
          args => subTerm_nonTail(a.term)(r => acc(Arg(false, r) :: args))
        case (s: Spd, acc) =>
          args => subTerm_nonTail(s.term)(r => acc(Arg(true, r) :: args))
      }(Nil)
    case ref @ st.Ref(sym) =>
      sym match
      case sym: BuiltinSymbol =>
        warnStmt
        if sym.binary then
          val t1 = new Tree.Ident("arg1")
          val t2 = new Tree.Ident("arg2")
          val p1 = Param(FldFlags.empty, VarSymbol(t1), N)
          val p2 = Param(FldFlags.empty, VarSymbol(t2), N)
          val ps = PlainParamList(p1 :: p2 :: Nil)
          val bod = st.App(t, st.Tup(List(st.Ref(p1.sym)(t1, 666), st.Ref(p2.sym)(t2, 666)))
            (Tree.Tup(Nil // FIXME should not be required (using dummy value)
              )))(
              Tree.App(Tree.Empty(), Tree.Empty()), // FIXME should not be required (using dummy value)
              FlowSymbol(sym.nme)
            )
          val (paramLists, bodyBlock) = setupFunctionDef(ps :: Nil, bod, S(sym.nme))
          tl.log(s"Ref builtin $sym")
          assert(paramLists.length === 1)
          return k(Value.Lam(paramLists.head, bodyBlock))
        if sym.unary then
          val t1 = new Tree.Ident("arg")
          val p1 = Param(FldFlags.empty, VarSymbol(t1), N)
          val ps = PlainParamList(p1 :: Nil)
          val bod = st.App(t, st.Tup(List(st.Ref(p1.sym)(t1, 666)))
            (Tree.Tup(Nil // FIXME should not be required (using dummy value)
              )))(
              Tree.App(Tree.Empty(), Tree.Empty()), // FIXME should not be required (using dummy value)
              FlowSymbol(sym.nme)
            )
          val (paramLists, bodyBlock) = setupFunctionDef(ps :: Nil, bod, S(sym.nme))
          tl.log(s"Ref builtin $sym")
          assert(paramLists.length === 1)
          return k(Value.Lam(paramLists.head, bodyBlock))
      case bs: BlockMemberSymbol =>
        bs.defn match
        case S(d) if d.isDeclare.isDefined =>
          return term(Sel(State.globalThisSymbol.ref(), ref.tree)(S(bs)))(k)
        case S(td: TermDefinition) if td.k is syntax.Fun =>
          // * Local functions with no parameter lists are getters
          // * and are lowered to functions with an empty parameter list
          // * (non-local functions are compiled into getter methods selected on some prefix)
          if td.params.isEmpty then
            val l = new TempSymbol(S(t))
            return Assign(l, Call(Value.Ref(bs), Nil)(true), k(Value.Ref(l)))
        case S(_) => ()
        case N => () // TODO panic here; can only lower refs to elab'd symbols
      case _ => ()
      warnStmt
      k(subst(Value.Ref(sym)))
    case st.App(Ref(sym: BuiltinSymbol), arg) =>
      arg match
      case st.Tup(Nil) =>
        if !sym.nullary then raise:
          ErrorReport(
            msg"Expected arguments for ${sym.nme}" -> t.toLoc :: Nil, S(arg),
            source = Diagnostic.Source.Compilation)
        k(Value.Ref(sym))
      case st.Tup(Fld(FldFlags.benign(), arg, N) :: Nil) =>
        if !sym.unary then raise:
          ErrorReport(
            msg"Expected a single argument for ${sym.nme}" -> t.toLoc :: Nil, S(arg),
            source = Diagnostic.Source.Compilation)
        subTerm(arg): ar =>
          k(Call(Value.Ref(sym), Arg(false, ar) :: Nil)(true))
      case st.Tup(Fld(FldFlags.benign(), arg1, N) :: Fld(FldFlags.benign(), arg2, N) :: Nil) =>
        if !sym.binary then raise:
          ErrorReport(
            msg"Expected two arguments for ${sym.nme}" -> t.toLoc :: Nil, S(arg),
            source = Diagnostic.Source.Compilation)
        subTerm(arg1): ar1 =>
          subTerm_nonTail(arg2): ar2 =>
            k(Call(Value.Ref(sym), Arg(false, ar1) :: Arg(false, ar2) :: Nil)(true))
      case _ =>
        raise:
          ErrorReport(
            msg"Unexpected arguments for builtin symbol '${sym.nme}'" -> arg.toLoc :: Nil, S(arg),
            source = Diagnostic.Source.Compilation)
        End("error")
    case st.App(f, arg) =>
      val isMlsFun = f.symbol.fold(f.isInstanceOf[st.Lam]):
        case _: sem.BuiltinSymbol => true
        case sym: sem.BlockMemberSymbol =>
          sym.trmImplTree.fold(sym.clsTree.isDefined)(_.k is syntax.Fun)
        case _ => false
      def conclude(fr: Path) =
        arg match
        case Tup(fs) =>
          val as = fs.map:
            case sem.Fld(sem.FldFlags.benign(), value, N) => false -> value
            case sem.Fld(flags, value, asc) =>
              TODO("Other argument forms")
            case spd: Spd => true -> spd.term
          val l = new TempSymbol(S(t))
            def rec(as: Ls[Bool -> st], asr: Ls[Arg]): Block = as match
              case Nil => k(Call(fr, asr.reverse)(isMlsFun))
              case (spd, a) :: as =>
                subTerm_nonTail(a): ar =>
                  rec(as, Arg(spd, ar) :: asr)
            rec(as, Nil)
        case _ =>
          // Application arguments that are not tuples represent spreads, as in `f(...arg)`
          subTerm(arg): ar =>
            k(Call(fr, Arg(spread = true, ar) :: Nil)(isMlsFun))
      f match
      // * Due to whacky JS semantics, we need to make sure that selections leading to a call
      // * are preserved in the call and not moved to a temporary variable.
      case sel @ Sel(prefix, nme) =>
        subTerm(prefix): p =>
          conclude(Select(p, nme)(sel.sym))
      case sel @ SelProj(prefix, _, nme) =>
        subTerm(prefix): p =>
          conclude(Select(p, nme)(sel.sym))
      case _ => subTerm(f)(conclude)
      
    case st.Blk((h @ Handle(lhs, rhs, cls, defs)) :: stmts, res) =>
      if !lowerHandlers then
        raise(ErrorReport(
          msg"Effect handlers are not enabled" ->
          h.toLoc :: Nil,
          source = Diagnostic.Source.Compilation))
        return End("error")
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
      subTerm(rhs): par =>
        HandleBlock(lhs, resSym, par, cls, handlers,
          term_nonTail(st.Blk(stmts, res))(HandleBlockReturn(_)),
          k(Value.Ref(resSym)))
      
    case st.Blk(Nil, res) => term(res)(k)
    case st.Blk((t: sem.Term) :: stats, res) =>
      subTerm(t, inStmtPos = true)(r => term_nonTail(st.Blk(stats, res))(k))
    case st.Blk((d: Declaration) :: stats, res) =>
      d match
      case td: TermDefinition =>
        reportAnnotations(td, td.extraAnnotations)
        td.body match
        case N => // abstract declarations have no lowering
          term(st.Blk(stats, res))(k)
        case S(bod) =>
          td.k match
          case knd: syntax.Val =>
            assert(td.params.isEmpty)
            subTerm_nonTail(bod)(r =>
              // Assign(td.sym, r,
              //   term(st.Blk(stats, res))(k)))
              Define(ValDefn(td.owner, knd, td.sym, r),
                term_nonTail(st.Blk(stats, res))(k)))
          case syntax.Fun =>
            val (paramLists, bodyBlock) = setupFunctionOrByNameDef(td.params, bod, S(td.sym.nme))
            Define(FunDefn(td.owner, td.sym, paramLists, bodyBlock),
              term_nonTail(st.Blk(stats, res))(k))
      case cls: ClassLikeDef if cls.sym.defn.exists(_.isDeclare.isDefined) =>
        // * Declarations have no lowering
        term(st.Blk(stats, res))(k)
      case cls: ClassLikeDef =>
        reportAnnotations(cls, cls.extraAnnotations)
        val bodBlk = cls.body.blk
        val (mtds, rest1) = bodBlk.stats.partitionMap:
          case td: TermDefinition if td.k is syntax.Fun => L(td)
          case s => R(s)
        val (privateFlds, rest2) = rest1.partitionMap:
          case decl @ LetDecl(sym: TermSymbol, annotations) =>
            reportAnnotations(decl, annotations)
            L(sym)
          case s => R(s)
        val publicFlds = rest2.collect:
          case td @ TermDefinition(k = (_: syntax.Val)) => td
        Define(ClsLikeDefn(cls.owner, cls.sym, cls.bsym, cls.kind, cls.paramsOpt, N,
            mtds.flatMap: td =>
              td.body.map: bod =>
                val (paramLists, bodyBlock) = setupFunctionDef(td.params, bod, S(td.sym.nme))
                FunDefn(td.owner, td.sym, paramLists, bodyBlock)
            ,
            privateFlds,
            publicFlds,
            End(),
            term_nonTail(Blk(rest2, bodBlk.res))(ImplctRet)
              // * This is just a minor improvement to get `constructor() {}` instead of `constructor() { null }`
              .mapTail:
                case Return(Value.Lit(syntax.Tree.UnitLit(true)), true) => End()
                case t => t
          ),
        term_nonTail(st.Blk(stats, res))(k))
      case _ =>
        // TODO handle
        term(st.Blk(stats, res))(k)
    case st.Blk((decl @ LetDecl(sym, annotations)) :: (stats @ ((_: DefineVar) :: _)), res) =>
      reportAnnotations(decl, annotations)
      term(st.Blk(stats, res))(k)
    case st.Blk((decl @ LetDecl(sym, annotations)) :: stats, res) =>
      reportAnnotations(decl, annotations)
      term(st.Blk(DefineVar(sym, Term.Lit(Tree.UnitLit(false))) :: stats, res))(k)
    case st.Blk(DefineVar(sym, rhs) :: stats, res) =>
      subTerm(rhs): r =>
        Assign(sym, r, term_nonTail(st.Blk(stats, res))(k))
    case Assgn(lhs, rhs) =>
      lhs match
      case Ref(sym) =>
        subTerm(rhs): r =>
          Assign(sym, r, k(Value.Lit(syntax.Tree.UnitLit(true))))
      case sel @ SynthSel(prefix, nme) =>
        subTerm(prefix): p =>
          subTerm_nonTail(rhs): r =>
            AssignField(p, nme, r, k(Value.Lit(syntax.Tree.UnitLit(true))))(sel.sym)
      case sel @ Sel(prefix, nme) =>
        subTerm(prefix): p =>
          subTerm_nonTail(rhs): r =>
            AssignField(p, nme, r, k(Value.Lit(syntax.Tree.UnitLit(true))))(sel.sym)
      
    case st.Blk((imp @ Import(sym, path)) :: stats, res) =>
      raise(ErrorReport(
        msg"Imports must be at the top level" ->
        imp.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      term(st.Blk(stats, res))(k)
      
    case st.Lam(params, body) =>
      warnStmt
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
          term_nonTail(trm): r =>
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
                subTerm_nonTail(trm): st =>
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
          if k.isInstanceOf[TailOp] && isIf then term_nonTail(els)(k)
          else
            term_nonTail(els): r =>
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
            subTerm_nonTail(a): ar =>
              rec(as, ar :: asr)
        rec(as, Nil)
    
    case Try(sub, finallyDo) =>
      val l = new TempSymbol(S(sub))
      TryBlock(
        subTerm_nonTail(sub)(p => Assign(l, p, End())),
        subTerm_nonTail(finallyDo)(_ => End()),
        k(Value.Ref(l))
      )
    
    // * BbML-specific cases: t.Cls#field and mutable operations
    case sp @ SelProj(prefix, _, proj) =>
      setupSelection(prefix, proj, sp.sym)(k)
    case Region(reg, body) =>
      Assign(reg, Instantiate(Select(Value.Ref(State.globalThisSymbol), Tree.Ident("Region"))(N), Nil),
        term_nonTail(body)(k))
    case RegRef(reg, value) =>
      def rec(as: Ls[st], asr: Ls[Path]): Block = as match
        case Nil => k(Instantiate(Select(Value.Ref(State.globalThisSymbol), Tree.Ident("Ref"))(N), asr.reverse))
        case a :: as =>
          subTerm_nonTail(a): ar =>
            rec(as, ar :: asr)
      rec(reg :: value :: Nil, Nil)
    case Deref(ref) =>
      subTerm(ref): r =>
        k(Select(r, Tree.Ident("value"))(N))
    case SetRef(lhs, rhs) =>
      subTerm(lhs): ref =>
        subTerm_nonTail(rhs): value =>
          AssignField(ref, Tree.Ident("value"), value, k(value))(N)
    
    case Neg(_) =>
      raise(ErrorReport(
        msg"Unexpected type annotations ${t.show}" ->
        t.toLoc :: Nil,
        source = Diagnostic.Source.Compilation))
      End("error")
    case Annotated(Annot.Untyped, receiver) =>
      term(receiver)(k)
    case Annotated(ann, receiver) =>
      raise(WarningReport(
        msg"This annotation has no effect." -> ann.toLoc ::
        msg"Such annotations are not supported on ${receiver.describe} terms." -> receiver.toLoc :: Nil))
      term(receiver)(k)
    case Error => End("error")
    
    // case _ =>
    //   subTerm(t)(k)
  
  def subTerm_nonTail(t: st, inStmtPos: Bool = false)(k: Path => Block)(using Subst): Block =
    subTerm(t: st, inStmtPos: Bool)(k)
  
  inline def subTerm(t: st, inStmtPos: Bool = false)(k: Path => Block)(using Subst): Block =
    term(t, inStmtPos = inStmtPos):
      case v: Value => k(v)
      case p: Path => k(p)
      case r =>
        val l = new TempSymbol(N)
        Assign(l, r, k(l |> Value.Ref.apply))
  
  
  // val resSym = new TermSymbol(N, Tree.Ident("$res"))
  // def topLevel(t: st): Block =
  //   subTerm(t)(r => codegen.Assign(resSym, r, codegen.End()))(using Subst.empty)
  
  def topLevel(t: st): Block =
    val res = term(t)(ImplctRet)(using Subst.empty)
    val stackSafe = stackLimit match
      case None => res
      case Some(lim) => StackSafeTransform(lim).transformTopLevel(res)
    
    if lowerHandlers then HandlerLowering().translateTopLevel(stackSafe)
    else stackSafe
  
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
  
  final def setupFunctionOrByNameDef(paramLists: List[ParamList], bodyTerm: Term, name: Option[Str])
      (using Subst): (List[ParamList], Block) =
    val physicalParams = paramLists match
      case Nil => ParamList(ParamListFlags.empty, Nil, N) :: Nil
      case ps => ps
    setupFunctionDef(physicalParams, bodyTerm, name)
  
  def setupFunctionDef(paramLists: List[ParamList], bodyTerm: Term, name: Option[Str])
      (using Subst): (List[ParamList], Block) =
    (paramLists, returnedTerm(bodyTerm))
  
  def reportAnnotations(target: Statement, annotations: Ls[Annot]): Unit = if annotations.nonEmpty then
    raise(WarningReport(
      (msg"This annotation has no effect." -> annotations.foldLeft[Opt[Loc]](N):
        case (acc, term) => acc match
          case N => term.toLoc
          case S(loc) => S(loc ++ term.toLoc)) ::
      Nil))


trait LoweringSelSanityChecks
        (instrument: Bool)(using TL, Raise, State)
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
        (instrument: Bool)(using TL, Raise, State)
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
  

  override def setupFunctionDef(paramLists: List[ParamList], bodyTerm: st, name: Option[Str])
      (using Subst): (List[ParamList], Block) =
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


