package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import utils.*
import semantics.*
import syntax.Tree
import semantics.Elaborator.{ctx, State}
import hkmc2.Message.MessageContext

import collection.mutable.HashMap


class FirstClassFunctionTransformer
      (using Elaborator.State, Elaborator.Ctx, Raise, DebugPrinter)
    extends BlockTransformer(new SymbolSubst):
  // Anonymous lambdas' parameter lists cannot be retrieved from the term symbol
  private val funDefns = HashMap.empty[BlockMemberSymbol, FunDefn] 
  class CollectFunDefns extends BlockTraverser:
    override def applyFunDefn(fun: FunDefn) =
      funDefns += (fun.sym -> fun)
      super.applyFunDefn(fun)

  private def generateFCFunctionClass(p: Path, params: ParamList) =
    val clsSym = ClassSymbol(
      syntax.Tree.DummyTypeDef(syntax.Cls),
      syntax.Tree.Ident("Function$")
    )
    val defSym = new BlockMemberSymbol("Function$", Nil, false)
    val callDef = FunDefn.withFreshSymbol(Some(clsSym), new BlockMemberSymbol("call", Nil, true), params :: Nil,
      Return(Call(p, params.params.map(_.sym.asSimpleRef.asArg) ne_:: Nil)(true, false, false)))(N, annotations = Nil)
    ClsLikeDefn(None, clsSym, defSym, None, syntax.Cls, None, Nil,
      Some(Select(State.globalThisSymbol.asThis, Tree.Ident("Function"))(Some(ctx.builtins.Function))),
      callDef :: Nil, Nil, Nil, Assign.discard(
        Call(State.builtinOpsMap("super").asSimpleRef, Nil ne_:: Nil)(false, false, false),
        End()), End(), None, None)(N, annotations = Nil)

  private def getParamList(l: BlockMemberSymbol): Option[ParamList] = funDefns.get(l) match
    case Some(fd) => fd.params.headOption
    case _ => l.tsym.flatMap(getParamList)

  private def getParamList(ts: TermSymbol): Option[ParamList] =
    ts.irFunDefn.flatMap(_.params.headOption)

  override def applyPath(p: Path)(k: Path => Block): Block = p match
    case ref @ Value.MemberRef(l, disamb) => disamb match
      case s: TermSymbol if s.k is syntax.Fun =>
        val params = getParamList(l).getOrElse(lastWords(s"Cannot get ${l.nme}'s parameter list."))
        val clsDef = generateFCFunctionClass(ref, params)
        val tmp = new TempSymbol(None)
        val cls = clsDef.sym.asMemberRef(clsDef.isym)
        Scoped(Set(clsDef.sym, tmp), Define(clsDef, Assign(tmp, Instantiate(false, cls, Nil :: Nil), k(tmp.asSimpleRef))))
      case _ => k(p)
    case sel: Select => sel.symbol match
      case Some(s: TermSymbol) if (s.k is syntax.Fun) =>
        val params = getParamList(s).getOrElse:
          raise:
            ErrorReport(msg"Cannot get ${s.nme}'s parameter list."
              -> sel.toLoc :: Nil,
              source = Diagnostic.Source.Compilation)
          PlainParamList(Nil)
        val clsDef = generateFCFunctionClass(sel, params)
        val tmp = new TempSymbol(None)
        val cls = clsDef.sym.asMemberRef(clsDef.isym)
        Scoped(Set(clsDef.sym, tmp), Define(clsDef, Assign(tmp, Instantiate(false, cls, Nil :: Nil), k(tmp.asSimpleRef))))
      case Some(_) => k(p)
      case _ =>
        raise(ErrorReport(msg"Cannot determine if ${sel.name.name} is a function." -> sel.toLoc :: Nil,
          source = Diagnostic.Source.Compilation))
        k(p)
    case _ => k(p)

  override def applyResult(r: Result)(k: Result => Block): Block = r match
    case c @ Call(fun, argss) => applyListOf(argss, (args, k2) => applyArgs(args)(k2)): argss2 =>
      def call(f: Path) = Call(f, argss2.ne_!)(c.isMlsFun, c.mayRaiseEffects, c.explicitTailCall)
      fun match
        case ref @ Value.SimpleRef(sym) => sym match
          case _: VarSymbol |  _: TempSymbol => k(call(ref.selSN("call")))
          case _ => k(call(fun))
        case ref @ Value.MemberRef(_, _) => k(call(fun))
        case sel: Select => sel.symbol match
          case Some(s: TermSymbol) =>
            if s.k is syntax.Fun then k(call(fun))
            else k(call(sel.selSN("call")))
          case _ =>
            raise(ErrorReport(msg"Cannot determine if ${sel.name.name} is a function object." -> fun.toLoc :: Nil,
                source = Diagnostic.Source.Compilation))
            k(call(fun))
        case s: DynSelect =>
          raise(ErrorReport(msg"Cannot determine if the dynamic selection is a function object." -> s.toLoc :: Nil,
              source = Diagnostic.Source.Compilation))
          k(call(fun))
        case _ => k(call(fun))
    case _: Lambda => lastWords("Lambda functions should be rewritten into function definitions first.")
    case _ => super.applyResult(r)(k)
  
  class DesugarMultipleParamList extends BlockTransformer(new SymbolSubst):
    override def applyFunDefn(fd: FunDefn): FunDefn = fd.params match
      case Nil => fd
      case _ :: Nil => fd
      case head :: tail =>
        def rec(params: List[ParamList]): Block = params match
          case head :: rest =>
            val newBody = rec(rest)
            val funSym = new BlockMemberSymbol("lambda$", Nil, false)
            val funDef = FunDefn.withFreshSymbol(None, funSym, head :: Nil, newBody)(N, annotations = Nil)
            Scoped(Set(funSym), Define(funDef, Return(funDef.sym.asMemberRef(funDef.dSym))))
          case Nil => fd.body
        FunDefn.withFreshSymbol(fd.owner, fd.sym, head :: Nil, rec(tail))(fd.configOverride, fd.annotations)
  
  def transform(b: Block): Block =
    val desugared = new DesugarMultipleParamList().applyBlock(b)
    new CollectFunDefns().applyBlock(desugared)
    applyBlock(desugared)
