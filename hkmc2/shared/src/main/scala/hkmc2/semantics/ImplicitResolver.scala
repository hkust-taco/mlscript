package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import utils.TraceLogger

import syntax.Tree
import syntax.{Fun, Ins, Mod}
import semantics.Term
import semantics.Elaborator.State
import ImplicitResolver.ICtx.Type
import ImplicitResolver.TyParamSymbol

import Message.MessageContext

class CtxArgImpl extends CtxArg:
  
  var arg: Opt[Term] = N
  override def term: Opt[Term] = arg
  
  def populate(term: Term): Unit = 
    arg = S(term)
    
  def showDbg: Str = s"CtxArg ${term.fold("‹unpopulated›")(_.showDbg)}"

object ImplicitResolver:
  
  type TyParamSymbol = LocalSymbol & NamedSymbol
  
  /*
   * An "implicit" or "instance" context, as opposed to the one in Elaborator.
   */
  case class ICtx(
    parent: Opt[ICtx], 
    iEnv: Map[Type.Sym, Ls[(Type, ICtx.Instance)]],
    tEnv: Map[TyParamSymbol, Type]
  ):
    
    def +(typ: Type.Concrete, sym: Symbol): ICtx =
      val newLs = (typ -> ICtx.Instance(sym)) :: iEnv.getOrElse(typ.toSym, Nil)
      val newEnv = iEnv + (typ.toSym -> newLs)
      copy(iEnv = newEnv)
    
    def withTypeArg(param: TyParamSymbol, arg: Type): ICtx =
      copy(tEnv = tEnv + (param -> arg))
    
    def get(query: Type.Concrete): Opt[ICtx.Instance] =
      iEnv.getOrElse(query.toSym, Nil)
        .find: (typ, _) => 
          compare(query, typ)
        .map: (_, instance) => 
          instance
    
    private def compare(a: Type, b: Type): Boolean = (a, b) match
      case (Type.Unspecified, _) => true
      case (_, Type.Unspecified) => true
      case (a: Type.Sym, b: Type.Sym) if a == b => true
      case (a @ Type.Sym(aSym: VarSymbol), b) if tEnv contains aSym => 
        compare(tEnv(aSym), b)
      case (a, b @ Type.Sym(bSym: VarSymbol)) if tEnv contains bSym => 
        compare(a, tEnv(bSym))
      case (Type.App(qSym, qArgs), Type.App(tSym, tArgs)) =>
        compare(qSym, tSym) && 
        (qArgs.length == tArgs.length) && 
        (qArgs zip tArgs).forall((a, b) => compare(a, b))
      case _ => false
  
  object ICtx:
    
    enum Type:
      /** 
       * A symbol type, can be either concrete (a type symbol) or 
       * abstract (a var symbol representing a type param).
       */
      case Sym(sym: BaseTypeSymbol | VarSymbol)
      /**
       * An application of a symbol type to a list of type arguments.
       */
      case App(t: Sym, typeArgs: Ls[Type])
      /**
       * A type that is not specified. 
       * This is for when the type is not known because no type inference is done.
       */
      case Unspecified
      
      def show: Str = this match
        case Sym(sym) => sym.id.name
        case App(t, args) => s"${t.show}[${args.map(_.show).mkString(", ")}]"
        case Unspecified => "‹unspecified›"
    
    object Type:
      type Concrete = Sym | App
      extension (t: Concrete)
        def toSym: Sym = t match
          case sym: Sym => sym
          case App(sym, _) => sym
    
    final case class Instance(sym: Symbol)
    
    val empty = ICtx(N, Map.empty, Map.empty)
    
  def ictx(using ICtx) = summon[ICtx]

class ImplicitResolver(tl: TraceLogger)
(using raise: Raise, state: State):
  import tl.*
  import ImplicitResolver.ICtx
  import ImplicitResolver.ictx
  
  def resolve(t: Term)(using ictx: ICtx): Unit = t match
    case blk: Term.Blk => 
      resolveBlk(blk)
    case Apps(Term.TyApp(base, targs), argss) if argss.nonEmpty =>
      resolveApp(base, S(targs), argss)
      t.subTerms.foreach(resolve(_))
    case Apps(base, argss) if argss.nonEmpty =>
      resolveApp(base, N, argss)
      t.subTerms.foreach(resolve(_))
    case _ => 
      t.subTerms.foreach(resolve(_))
  
  def resolveApp(base: Term, targs: Opt[List[Term]], argss: List[Term])(using ICtx) =
  trace[Unit](s"Resolving App: $base; $targs; $argss", _ => s"~> $base; $targs; $argss"):
    base match
      case ModuleChecker.MethodDef(tdf) =>
        given withTypeArgs: ICtx = tdf.tparams match
          case S(tparams) => targs match
            case S(targs) =>
              if tparams.length != targs.length then
                raise(ErrorReport(msg"Expected ${tparams.length.toString()} type arguments, " +
                  msg"got ${targs.length.toString()}" -> base.toLoc :: Nil))
              (tparams zip targs).foldLeft(ictx):
                case (ictx, (tparam, targ)) => (tparam.sym, resolveType(targ)) match
                  case (sym: TyParamSymbol, S(typ)) =>
                    log(s"Resolving App with type arg ${sym} = $typ")
                    ictx.withTypeArg(sym, typ)
                  case _ => ictx
            case N => tparams.foldLeft(ictx): 
              case (ictx, tparam) => 
                log(s"Resolving App with type arg ${tparam.sym} = ${Type.Unspecified}")
                ictx.withTypeArg(tparam.sym, Type.Unspecified)
          // No type parameters for the definition.
          case N => ictx
        val paramss = tdf.params
        (paramss zip argss).foreach: 
          case (ps, Term.Tup(args)) =>
            if ps.paramCountUB
            then if ps.paramCountLB != args.length then
              raise(ErrorReport(msg"Expected ${ps.paramCountLB.toString()} arguments, " +
                msg"got ${args.length.toString()}" -> base.toLoc :: Nil))
            else if ps.paramCountLB > args.length then
              raise(ErrorReport(msg"Expected at least ${ps.paramCountLB.toString()} arguments, " +
                msg"got ${args.length.toString()}" -> base.toLoc :: Nil))
            (ps.params zip args).foreach((p, arg) => resolveArg(p, arg)(base))
          case _ =>
            lastWords("Other argument forms.")
      case _ => // Not module method app, do nothing.
  
  def resolveArg(p: Param, a: Elem)(t: Term)(using ictx: ICtx): Unit = a match
    case arg: CtxArgImpl =>
      log(s"Resolving contextual argument, expecting a ${p.sign}")
      p.sign match
        case S(sign) => resolveType(sign) match
          case S(tpe: Type.Concrete) =>
            ictx.get(tpe) match
              case S(i) =>
                log(s"Populate contextual parameter ${p} with instance ${i}")
                arg.populate(i.sym.ref())
              case N =>
                raise(ErrorReport(
                  msg"Missing instance for contextual parameter ${tpe.show}" -> p.toLoc ::
                  msg"Required by module method application at: " -> t.toLoc ::
                  msg"Expected: ${tpe.show}; Available: ${ictx.iEnv.toString()}" -> N :: Nil))
          case N =>
        case N =>
          // By the syntax of contextual parameter, the type signature should be present.
          lastWords(s"No type signature for contextual parameter ${p.showDbg} at ${p.toLoc}")
    case _ =>
      a.subTerms.foreach(resolve(_))
  
  def resolveBlk(blk: Term.Blk)(using ictx: ICtx): ICtx =
  trace[ICtx](s"Resolving block: $blk", _ => s"~> $blk"):
    def go(rest: Ls[Statement])(using ictx: ICtx): ICtx = rest match
      case Nil => ictx
      case stmt :: rest => 
        log(s"Resolving statement: $stmt")
        given newICtx: ICtx = stmt match
          // Case: instance definition. 
          // Add the instance to the context.
          case t @ TermDefinition(_, Ins, sym, _, _, sign, _, _, _, _) => 
            log(s"Resolving instance definition ${t.showDbg}")
            sign match
              case N =>
                // By the syntax of instance defintiion, the type signature should be present.
                lastWords(s"No type signature for instance definition ${t.showDbg} at ${t.toLoc}")
              case S(sign) => resolveType(sign) match
                case N => ictx
                case S(typ) => ictx + (typ, sym)
          
          // Case: function definition. 
          // Add the contextual parameters to the context and use the context to resolve the body.
          // Resolve other subterms with the original context.
          case t @ TermDefinition(_, Fun, _, pss, _, _, _, _, _, _) =>
            log(s"Resolving function definition $t")
            val withCtxArgs = pss
              .filter(_.flags.ctx)
              .foldLeft(ictx): (ictx, ps) => 
                ps.params.foldLeft(ictx): (ictx, p) => 
                  log(s"Resolving function parameter ${p.showDbg}")
                  p.sign match
                    case N =>
                      // By the syntax of contextual parameter, the type signature should be present.
                      lastWords(s"No type signature for contextual parameter ${t.showDbg} at ${t.toLoc}")
                    case S(sign) => resolveType(sign) match
                      case N => ictx
                      case S(tpe) => ictx + (tpe, p.sym)
            t.subTerms.foreach: st => 
              if t.body.exists(st == _)
              then resolve(st)(using withCtxArgs)
              else resolve(st)
            ictx
          
          // Default Case. Simply resovle all subterms.
          case _ =>
            stmt.subTerms.foreach(resolve(_))
            ictx
        
        go(rest)
    
    val newICtx = go(blk.stats)(using ictx)
    resolve(blk.res)(using newICtx)
    newICtx
  
  /** Resolve the type signature of a term. */
  def resolveType(t: Term): Opt[ICtx.Type.Concrete] = t match
      // If the term is a type application, e.g., T[A, ...],
      // resolve the type constructor and arguments respectively.
      case Term.TyApp(con, args) => 
        (resolveType(con), args.map(resolveType(_)).sequence) match
          case (S(sym: ICtx.Type.Sym), S(typeArgs)) =>
            S(ICtx.Type.App(sym, typeArgs))
          case _ =>
            // Either the type constructor or the arguments is not resolved.
            // The error should have been reported.
            N
      // Otherwise, resolve the term directly.
      case _ => t.symbol match
        // A VarSymbol is probably a type parameter.
        case S(sym: VarSymbol) if ModuleChecker.isTypeParam(sym) =>
          S(ICtx.Type.Sym(sym))
        case S(sym) => sym.asTpe match
          // A BaseTypeSymbol is some concrete type.
          case S(tpe: BaseTypeSymbol) =>
            S(ICtx.Type.Sym(tpe))
          // A TypeAliasSymbol is a type alias that require further resolution.
          case S(tpe: TypeAliasSymbol) =>
            tpe.defn match
              case S(tpe) => 
                tpe.rhs.flatMap(resolveType(_))
              case N => 
                // No definition for the type alias. 
                // There must be an error reported on elaborating the type alias.
                N
          case N =>
            raise(ErrorReport(msg"Expected a type, got ${t.describe}" -> t.toLoc :: Nil))
            N
        case N =>
          raise(ErrorReport(msg"Expected a type symbol, got ${t.describe}" -> t.toLoc :: Nil))
          N

end ImplicitResolver

object ModuleChecker:
  
  /** Checks if a term is a reference to a type parameter. */
  def isTypeParam(t: Term): Bool = t.symbol
    .filter(_.isInstanceOf[VarSymbol])
    .flatMap(_.asInstanceOf[VarSymbol].decl)
    .exists(_.isInstanceOf[TyParam])
    
  def isTypeParam(sym: VarSymbol): Bool = sym.decl
    .exists(_.isInstanceOf[TyParam])
  
  /** Checks if a term evaluates to a module value. */
  def evalsToModule(t: Term): Bool = 
    def isModule(t: Tree): Bool = t match
      case Tree.TypeDef(Mod, _, _, _) => true
      case _ => false
    def returnsModule(t: Tree.TermDef): Bool = t.annotatedResultType match
      case S(Tree.TypeDef(Mod, _, N, N)) => true
      case _ => false
    t match
      case Term.Blk(_, res) => evalsToModule(res)
      case Term.App(lhs, rhs) => lhs.symbol match
        case S(sym: BlockMemberSymbol) => sym.trmTree.exists(returnsModule)
        case _ => false
      case t => t.symbol match
        case S(sym: BlockMemberSymbol) => sym.modTree.exists(isModule)
        case _ => false
  
  /**
   * An extractor that extracts the (tree) definition of a module method.
   */
  object MethodTreeDef:
    def unapply(t: Term): Opt[Tree.TermDef] = t match
      case t @ Term.Sel(pre, _) if evalsToModule(pre) => 
        t.symbol match
        case S(sym: BlockMemberSymbol) => sym.trmTree match
          case S(tree @ Tree.TermDef(k = Fun)) => S(tree)
          case _ => N
        case _ => N
      case t @ Term.SynthSel(pre, _) if evalsToModule(pre) => t.symbol match
        case S(sym: BlockMemberSymbol) => sym.trmTree match
          case S(tree @ Tree.TermDef(k = Fun)) => S(tree)
          case _ => N
        case _ => N
      case _ => N
  
  object MethodDef:
    def unapply(t: Term): Opt[TermDefinition] = t match
      case t @ Term.Sel(pre, _) if evalsToModule(pre) => t.symbol match
        case S(sym: BlockMemberSymbol) => sym.defn match
          case S(defn @ TermDefinition(k = Fun)) => S(defn)
          case _ => N
        case _ => N
      case t @ Term.SynthSel(pre, _) if evalsToModule(pre) => t.symbol match
        case S(sym: BlockMemberSymbol) => sym.defn match
          case S(defn @ TermDefinition(k = Fun)) => S(defn)
          case _ => N
        case _ => N
      case _ => N
  

extension [T](xs: Ls[Opt[T]])
  def sequence: Opt[Ls[T]] =
    xs.foldRight(S(Nil): Opt[Ls[T]]): (x, acc) => 
      for 
        x <- x
        acc <- acc
      yield x :: acc
