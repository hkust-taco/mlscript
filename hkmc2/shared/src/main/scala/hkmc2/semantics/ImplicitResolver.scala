package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import utils.TraceLogger

import syntax.Tree
import syntax.{Fun, Ins, Mod, ImmutVal}
import syntax.Keyword.{`if`}
import semantics.Term
import semantics.Elaborator.State
import ImplicitResolver.ICtx.Type

import Message.MessageContext
import scala.annotation.tailrec

class CtxArgImpl extends CtxArg:
  
  var arg: Opt[Term] = N
  override def term: Opt[Term] = arg
  
  def populate(term: Term): Unit = 
    arg = S(term)
    
  def showDbg: Str = s"CtxArg ${term.fold("‹unpopulated›")(_.showDbg)}"

object ImplicitResolver:
  
  /*
   * An "implicit" or "instance" context, as opposed to the one in Elaborator.
   * 
   * Essentially, the resolver does the following:
   * 
   * 1. If it sees an application with contextual arguments to be resolved, 
   *   it resolves the contextual arguments from the instance environment. 
   *   If the type of the contextual arguments involve type parameters, 
   *   it resolves the actual types from the type environment.
   * 
   * 2. If it sees an instance definition, 
   *   it adds the instance to the instance environment.
   * 
   * 3. If it sees an application with contextual arguments to be resolved and type arguments specified, 
   *   it resolves the contextual arguments from the instance environment,
   *   and adds the type arguments to the type environment.
   * 
   * @param parent the parent context, if any
   * @param iEnv the instance environment, mapping types to instances
   * @param tEnv the type environment, mapping type parameters to concrete types
   */
  case class ICtx(
    parent: Opt[ICtx], 
    iEnv: Map[Type.Sym, Ls[(Type, ICtx.Instance)]],
    tEnv: Map[VarSymbol, Type]
  ):
    
    def +(typ: Type.Concrete, sym: Symbol): ICtx =
      val newLs = (typ -> ICtx.Instance(sym)) :: iEnv.getOrElse(typ.toSym, Nil)
      val newEnv = iEnv + (typ.toSym -> newLs)
      copy(iEnv = newEnv)
    
    def withTypeArg(param: VarSymbol, arg: Type): ICtx =
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
  
  enum Expect:
    case Module(reason: Opt[Message])
    case NonModule(reason: Opt[Message])
    case Any
    
  extension (e: Expect)
    def message: Ls[Message -> Opt[Loc]] = e match
      case Expect.Module(msg) => msg.toList.map(_ -> N)
      case Expect.NonModule(msg) => msg.toList.map(_ -> N)
      case Expect.Any => Nil
    
    def module = e match
      case Expect.Module(_) => true
      case _ => false
    
    def nonModule = e match
      case Expect.NonModule(_) => true
      case _ => false
  
  import Expect.*
  
  /** 
   * Resolve the term `t` in the context of `ictx`.
   * 
   * Here, 'resolve' means to:
   * 1. check the modulefulness of terms: moduleful term should appear only in some specific places
   * 2. resovle any unpopulated contextual arguments
   * 
   * @param t the term to resolve
   * @param expect the expected modulefulness of the term
   */
  def resolve(t: Term, expect: Expect)(using ictx: ICtx): Unit = 
  trace[Unit](s"Resolving term: $t (expect module $expect)", _ => s"~> $t"):
    val evalsToModule = ModuleChecker.evalsToModule(t)
    log(s"Resolving term ${t.showDbg}, evalsToModule = $evalsToModule")
    if expect.module && !evalsToModule then
      raise(ErrorReport(msg"Expected a module, found non-moduleful ${t.describe}." -> t.toLoc 
        :: expect.message))
    if expect.nonModule && evalsToModule then
      raise(ErrorReport(msg"Unexpected moduleful ${t.describe}." -> t.toLoc 
        :: expect.message))
    
    t match
      // The modulefulness of t is already checked, 
      // even for the block-like terms such as Blk and IfLike. 
      // In other words, at this point, even if t is a nested Blk and IfLike,
      // its modulefulness should be the same as the `expect`ed one.
      // Because of this, we don't pass the `expect` to the subterms to check them recursively,
      // we purely traverse the subterms with `expect = Any` here.
      case blk: Term.Blk => 
        resolveBlk(blk)
      case t: Term.IfLike =>
        t.subTerms.foreach(resolve(_, expect = Any))
      case Term.Sel(p, _) =>
        resolve(p, expect = Any)
      case Term.SynthSel(p, _) =>
        resolve(p, expect = Any)
      
      case Apps(Term.TyApp(base, targs), argss) =>
        resolveApp(base, S(targs), argss)
      case Apps(base, argss) if argss.nonEmpty =>
        resolveApp(base, N, argss)
      
      case _ => 
        t.subTerms.foreach(resolve(_, expect = NonModule(N)))
  
  def resolveApp(base: Term, targs: Opt[List[Term]], argss: List[Term])(using ICtx) =
  trace[Unit](s"Resolving app: $base; $targs; $argss", _ => s"~> $base; $targs; $argss"):
    resolve(base, expect = Any)
    
    object FunctionDef:
      def unapply(t: Term): Opt[TermDefinition] = t.symbol match
        case S(sym: BlockMemberSymbol) => sym.defn match
          case S(defn @ TermDefinition(k = Fun)) => S(defn)
          case _ => N
        case _ => N
    
    base match
      case FunctionDef(tdf) =>
        given withTypeArgs: ICtx = tdf.tparams match
          case S(tparams) => targs match
            case S(targs) =>
              if tparams.length != targs.length then
                raise(ErrorReport(msg"Expected ${tparams.length.toString()} type arguments, " +
                  msg"got ${targs.length.toString()}" -> base.toLoc :: Nil))
              (tparams zip targs).foldLeft(ictx):
                case (ictx, (tparam, targ)) => (tparam.sym, resolveType(targ)) match
                  case (sym: VarSymbol, S(typ)) =>
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
          case (ps, as) =>
            val (argCountUB, argCountLB) = as match
              // Tup: regular arguments
              case tup: Term.Tup => (
                !tup.fields.exists(_.isInstanceOf[Spd]),
                tup.fields.map:
                  case _: Fld => 1
                  case _: Spd => 0
                  case _: CtxArg => 1
                .sum,
              )
              // Other: spread arguments
              case _ => (false, 0)
            
            (ps.paramCountUB, argCountUB) match
              case (true, true) => if ps.paramCountLB != argCountLB then
                raise(ErrorReport(msg"Expected ${ps.paramCountLB.toString()} arguments, " +
                  msg"got ${argCountLB.toString()}" -> base.toLoc :: Nil))
              case (true, false) => if ps.paramCountLB < argCountLB then
                raise(ErrorReport(msg"Expected ${ps.paramCountLB.toString()} arguments, " +
                  msg"got at least ${argCountLB.toString()}" -> base.toLoc :: Nil))
              case (false, true) => if ps.paramCountLB > argCountLB then
                raise(ErrorReport(msg"Expected at least ${ps.paramCountLB.toString()} arguments, " +
                  msg"got ${argCountLB.toString()}" -> base.toLoc :: Nil))
              case (false, false) => ()
            
            val args = as match
              case Term.Tup(args) => args
              case spd => Spd(true, spd) :: Nil
            
            // If some some arguments are spread, 
            // we are not able to pair the parameters and arguments statically.
            // We will try to pair and resolve all arguments before the first spread.
            @tailrec
            def go(ps: Ls[Param], as: Ls[Elem], pairing: Bool): Unit = (ps, as) match
              // If there is a spread argument, later arguments are not paired.
              // We don't consume parameters after the spread.
              case (ps, (a: Spd) :: as) =>
                resolve(a.term, expect = NonModule(N))
                go(ps, as, false)
              case (ps, a :: as) if !pairing =>
                a.subTerms.foreach(resolve(_, expect = NonModule(N)))
                go(ps, as, false)
              
              // If `pairing`, we are still able to pair the parameters and arguments.
              case (p :: ps, (a: CtxArg) :: as) =>
                resolveArg(p, a)(base)
                go(ps, as, true)
              case (p :: ps, (a: Fld) :: as) =>
                resolve(a.term, 
                  // note: we accept regular arguments for module parameters
                  expect = if p.flags.mod 
                    then Any
                    else NonModule(S(msg"Module argument passed to a non-module parameter."))
                )
                go(ps, as, true)
              
              
              // If there are more arguments, all of them go to `restParam`.
              // We don't resovle them as contextual arguments but as regular arguments.
              case (Nil, a :: as) =>
                a.subTerms.foreach(resolve(_, expect = NonModule(N)))
                go(Nil, as, pairing)
              // If there are more parameters, there must be a spread argument before.
              case (p :: ps, Nil) => ()
              
              case (Nil, Nil) => ()
              
            go(ps.params, args, true)
      case _ => 
        // Not module method app.
        targs.foreach(_.foreach(resolve(_, expect = NonModule(N))))
        argss.foreach(resolve(_, expect = NonModule(N)))
  
  def resolveArg(p: Param, a: Elem)(t: Term)(using ictx: ICtx): Unit = a match
    case arg: CtxArgImpl =>
      log(s"Resolving contextual argument, expecting a ${p.sign}")
      p.sign match
        case S(sign) => resolveType(sign) match
          case S(tpe: Type.Concrete) =>
            ictx.get(tpe) match
              case S(i) =>
                log(s"Populate contextual parameter ${p} with instance ${i}")
                val ref = i.sym.ref()
                resolve(ref,
                  // note: we accept regular arguments for module parameters
                  expect = if p.flags.mod 
                    then Any 
                    else NonModule(S(msg"Module argument passed to a non-module parameter.")),
                )
                arg.populate(ref)
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
      lastWords(s"Attempting to resolve a non-contextual-placeholder argument ${a.showDbg}")

  
  def resolveParam(p: Param)(using ictx: ICtx): Unit =
    log(s"Resolving parameter ${p.showDbg}")
    if p.flags.mod then
      if p.sign.isEmpty then
        raise(ErrorReport(msg"Module parameter must have explicit type." -> p.sym.toLoc :: Nil))
    p.sign.foreach:
      resolve(_, 
        expect = if p.flags.mod 
          then Module(S(msg"Module parameter must have a module type."))
          else NonModule(S(msg"Non-module parameter must have a non-module type.")),
      )
  
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
          
          // Case: Fun/Val definition. 
          // Add the contextual parameters to the context and use the context to resolve the body.
          // Resolve other subterms with the original context.
          case t @ TermDefinition(_, Fun | ImmutVal, _, pss, tps, sign, body, _, TermDefFlags(isMethod, isModTyped), annotations) =>
            log(s"Resolving ${t.k.desc} definition $t")
            
            if isMethod && isModTyped then
              raise(ErrorReport(msg"${t.k.desc.capitalize} returning modules should not be a class member." -> t.toLoc :: Nil))
            
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
            
            pss.foreach(_.params.foreach(resolveParam(_)))
            tps.getOrElse(Nil).flatMap(_.subTerms).foreach(resolve(_, expect = NonModule(N)))
            sign.foreach(resolve(_,
              expect = if isModTyped
                then Module(S(msg"${t.k.desc.capitalize} marked as returning a 'module' must have a module return type."))
                else NonModule(S(msg"${t.k.desc.capitalize} must be marked as returning a 'module' in order to have a module return type."))
            ))

            body.foreach(resolve(_,
              expect = if isModTyped
                then Module(S(msg"${t.k.desc.capitalize} marked as returning a 'module' but not returning a module."))
                else NonModule(S(msg"${t.k.desc.capitalize} must be marked as returning a 'module' in order to return a module."))
            )(using withCtxArgs))
            annotations.flatMap(_.subTerms).foreach(resolve(_, expect = NonModule(N)))
            
            ictx
          
          case c: ClassLikeDef =>
            c.paramsOpt.foreach(_.foreach(resolveParam(_)))
            resolve(c.body.blk, expect = NonModule(N))
            
            ictx
          
          // Default Case. Simply resovle all subterms.
          case t: Term =>
            resolve(t, expect = NonModule(N))
            ictx
          case _ =>
            stmt.subTerms.foreach(resolve(_, expect = NonModule(N)))
            ictx
        
        go(rest)
    
    val newICtx = go(blk.stats)(using ictx)
    resolve(blk.res, expect = Any)(using newICtx)
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
  
  extension (s: Split)
    private def results: Ls[Term] = 
      def go(s: Split): Ls[Term] = s match
        case Split.Cons(head, tail) => go(head.continuation) ::: go(tail)
        case Split.Let(_, _, tail) => go(tail)
        case Split.Else(term) => term :: Nil
        case Split.End => Nil
      go(s)
    
  
  /** Checks if a term is a reference to a type parameter. */
  def isTypeParam(t: Term): Bool = t.symbol
    .filter(_.isInstanceOf[VarSymbol])
    .flatMap(_.asInstanceOf[VarSymbol].decl)
    .exists(_.isInstanceOf[TyParam])
    
  def isTypeParam(sym: VarSymbol): Bool = sym.decl
    .exists(_.isInstanceOf[TyParam])
  
  /** 
   * Checks if a term evaluates to a module value.
   */
  def evalsToModule(t: Term): Bool =
    def returnsModule(t: Tree.TermDef): Bool = t.annotatedResultType match
      case S(Tree.TypeDef(Mod, _, N, N)) => true
      case _ => false
    def checkDecl(decl: Declaration): Bool = decl match
      // All TypeLikeDef are not modules, except for modules themselves.
      // Objects use ModuleDef but is not a module.
      case ModuleDef(kind = Mod) =>
        true
      case _: TypeLikeDef =>
        false
      // Check Member/Local symbols
      case defn: TermDefinition => 
        defn.flags.isModTyped
      case defn: Param =>
        defn.flags.mod
      case defn: TyParam =>
        defn.flags.mod
    def checkSym(sym: Symbol): Bool = sym match
      case sym if sym.isModule => true
      case sym: (BuiltinSymbol | TopLevelSymbol) => false
      case sym: BlockLocalSymbol => sym.decl match
        case S(decl) => checkDecl(decl)
        case N =>
          // Most local symbols are let-bindings 
          // which do not have a definition at this point.
          false
      case sym: MemberSymbol[?] => sym.defn match
        case S(defn) => checkDecl(defn)
        case N =>
          // At this point all member symbols should have definition,
          // except for the class(-like) that are currently being elaborated.
          false
      case sym => 
        lastWords(s"Unsupported symbol kind ${sym}")
    t match
      case Term.Blk(_, res) => evalsToModule(res)
      case Term.IfLike(`if`, split) => split.results.exists(evalsToModule(_))
      case Term.App(base, _) => base.symbol match
        case S(sym: BlockMemberSymbol) => sym.trmTree.exists(returnsModule)
        case _ => evalsToModule(base)
      case Term.TyApp(base, _) => evalsToModule(base)
      case t: Term.Ref => checkSym(t.sym)
      case t => t.symbol.exists(checkSym)

extension [T](xs: Ls[Opt[T]])
  def sequence: Opt[Ls[T]] =
    xs.foldRight(S(Nil): Opt[Ls[T]]): (x, acc) => 
      for 
        x <- x
        acc <- acc
      yield x :: acc
