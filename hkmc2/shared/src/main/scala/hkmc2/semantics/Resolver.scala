package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import utils.TraceLogger

import syntax.Tree
import syntax.Tree.{DummyTup, DummyApp}
import syntax.{Fun, Ins, Mod, ImmutVal, MutVal}
import syntax.Keyword.{`if`}
import Elaborator.State
import Resolvable.*
import typing.Type

import Message.MessageContext
import scala.annotation.tailrec

object Resolver:
  
  /**
   * An "implicit" or "instance" context, as opposed to the one in
   * Elaborator.
   *
   * Essentially, the resolver does the following:
   *
   * 1. If it sees an application with contextual arguments to be
   *    resolved, it resolves the contextual arguments from the instance
   *    environment. If the type of the contextual arguments involve
   *    type parameters, it resolves the actual types from the type
   *    environment.
   *
   * 2. If it sees an instance definition, it adds the instance to the
   *    instance environment.
   *
   * 3. If it sees an application with contextual arguments to be
   *    resolved and type arguments specified, it resolves the
   *    contextual arguments from the instance environment, and adds the
   *    type arguments to the type environment.
   *
   * @param parent the parent context, if any
   * @param iEnv the instance environment, mapping types to instances
   * @param tEnv the type environment, mapping type parameters to
   * concrete types
   */
  case class ICtx(
    parent: Opt[ICtx], 
    iEnv: Map[Type, Ls[(Type, ICtx.Instance)]],
    tEnv: Map[VarSymbol, Type]
  ):
    
    def +(typ: Type, ins: Symbol): ICtx = typ match
      case Type.NotImplemented => lastWords("Cannot add instance with a not-yet implemented type.")
      case Type.Error => this
      case _ => copy(iEnv = 
        iEnv + (typ.key -> ((typ -> ICtx.Instance(ins)) :: iEnv.getOrElse(typ.key, Nil)))  
      )
    
    def withTypeArg(param: VarSymbol, arg: Type): ICtx =
      copy(tEnv = tEnv + (param -> arg))
    
    extension (t: Type)
      private def key: Type = t match
        case Type.Ref(base, _) => Type.Ref(base, Nil)
        case _ => t
    extension (lhs: Type)
      private def =:= (rhs: Type): Bool = lhs <:< rhs && rhs <:< lhs
      private def <:< (rhs: Type): Bool = (lhs, rhs) match
        case (_, Type.Top) => true
        
        // If LHS/RHS is unspecified (not substituted into a concrete type),
        // we consider LHS/RHS is always a subtype of LHS/RHS.
        case (lhs: Type.Ref, rhs @ Type.Ref(_: VarSymbol, Nil)) => true
        case (lhs @ Type.Ref(_: VarSymbol, Nil), rhs: Type.Ref) => true
        
        case (lhs: Type.Ref, rhs: Type.Ref) =>
          lhs.sym === rhs.sym // TODO: subtyping for Ref
          && (lhs.args.length == rhs.args.length)
          && (lhs.args zip rhs.args).forall((a, b) => a.lb =:= b.lb && a.ub =:= b.ub) // suppose invariant
        case (lhs: Type.Fun, rhs: Type.Fun) =>
          (lhs.args.length == rhs.args.length)
          && (lhs.args zip rhs.args).forall((a, b) => b <:< a) // contravariant
          && (lhs.ret <:< rhs.ret) // covariant
          && (lhs.eff, rhs.eff).match
            case (N, N) => true
            case (S(le), S(re)) => le <:< re // covariant
            case _ => false
        case (lhs: Type.Neg, rhs) => ???
        case (lhs, rhs: Type.Neg) => ???
        case (lhs, rhs: Type.Union) => lhs <:< rhs.lhs || lhs <:< rhs.rhs
        case (lhs, rhs: Type.Inter) => lhs <:< rhs.lhs && lhs <:< rhs.rhs
        case (lhs, rhs) => lhs === rhs

    def query(q: Type): Ls[Message -> Opt[Loc]] \/ ICtx.Instance =
      q match
        case Type.NotImplemented => lastWords("Cannot resolve instance for a not-yet implemented type.")
        case q @ Type.Ref(sym: VarSymbol, args) if !tEnv.contains(sym) => L:
          msg"Illegal query for an unspecified type variable ${q.show}." -> N :: Nil
        case q =>
          q.subst:
            case ty @ Type.Ref(sym: VarSymbol, Nil) =>
              tEnv.getOrElse(sym, ty)
            case ty @ Type.Ref(sym: VarSymbol, args) =>
              lastWords(s"Unsupported substitution with type arguments")
          .into: qq =>
            iEnv.getOrElse(qq.key, Nil)
              .find: (ty, _instance) =>
                ty <:< qq
              .map: (_ty, instance) =>
                instance
              .toRight:
                msg"Missing instance: Expected: ${showTy(q)}; Available: ${showEnv}" -> N :: Nil
    
    def showEnv: Str =
      iEnv.values
        .flatMap(_.map((typ, instance) => s"${typ.show}"))
        .toList
        .distinct
        .mkStringOr(", ", els = "‹none available›")
    
    def showTy(ty: Type): Str = ty match
      case Type.Ref(sym: VarSymbol, Nil) =>
        s"${tEnv.get(sym).map(_.show).getOrElse("‹unspecified›")} (type parameter ${ty.show})"
      case Type.Ref(sym: VarSymbol, args) =>
        s"${tEnv.get(sym).map(_.show).getOrElse("‹unspecified›")}${args.map(_.show).mkString("[", ", ", "]")} (type parameter ${ty.show})"
      case _ => 
        s"${ty.show}"
  
  enum Expect:
    case Module(reason: Opt[Message])
    case NonModule(reason: Opt[Message])
    case Class(reason: Opt[Message])
    case Any
    
    def message: Ls[Message -> Opt[Loc]] = this match
      case Expect.Module(msg) => msg.toList.map(_ -> N)
      case Expect.NonModule(msg) => msg.toList.map(_ -> N)
      case Expect.Class(msg) => msg.toList.map(_ -> N)
      case Expect.Any => Nil
    
    def `module` = isInstanceOf[Module]
    def `class` = isInstanceOf[Class]
    def nonModule = isInstanceOf[NonModule]
    
    override def toString: Str = this match
      case _: Module => "Module"
      case _: NonModule => "NonModule"
      case _: Class => "Class"
      case _: Any => "Any"
  
  object Expect:
    def fromModulefulness(mf: Modulefulness): Expect =
      if mf.modified then
        Expect.Module(N)
      else
        Expect.NonModule(N)
  
  object ICtx:
    
    case class Instance(sym: Symbol)
    
    val empty = ICtx(N, Map.empty, Map.empty)
    
  def ictx(using ICtx) = summon[ICtx]
  
end Resolver

/**
  * Resolver for the module system.
  *
  * Resolver mainly resolves the terms, definitions and symbols that are
  * not yet ready during the elaboration. In addition, it also performs
  * some checks on the modulefulness of the terms.
  *
  * Here are some notes that I used for reasoning about the design.
  *
  * ### Static Members vs. Class Members
  *
  * An important feature in MLscript is that the program should be
  * compilable without type checking, and the user experience of doing
  * so should be good and not error prone. (See:
  * https://github.com/hkust-taco/mlscript-design-docs/blob/main/wiki/module-methods.md)
  * A consequence of this design is that the definition of a method may
  * not always be present at compilation-time, because the type
  * information of the object is absent.
  *
  * In contrast, for a function, the definition is always known at the
  * call sites at compilation time. This is important because most
  * call-site features require the definition to be known. For example,
  * by-name, lazy and implicit parameters all require the definition so
  * that the compiler can perform the correct elaboration and
  * resolution.
  *
  * ### Module Methods & Modulefulness Check
  *
  * In addition to functions, module methods also always have the
  * definition present at compilation-time. We will now start to refer
  * to the module methods as "functions".
  *
  * The definition of module functions are always present because of
  * some restrictions on modules. Only declarations that have a
  * signature and marked as `module` may bind to a module value. For
  * example, 
  *
  * ```mls
  * val v: module M
  * fun f(module m: M): module M
  * ```
  *
  * This preserves the module definition even if the module is bound to
  * other names. In order to maintain the correctness of this system,
  * the resolver performs the extra checks to ensure that the definition
  * of a module is never lost during re-binding. 
  *
  * 1. Only declarations that have a signature and marked as `module`
  *    may bind to a module value.
  * 2. Only declarations of static members may bind to a module value.
  *
  * If a term evaluates to a module value (e.g., an application to a
  * function returning a module, a reference to a module variable), it
  * is said to be moduleful. All moduleful terms must only occur at
  * certain locations in the program. For example, a moduleful term must
  * not occur as a scrutinee because it may be re-bound to a different
  * name, during when the module definition is lost.
  *
  * ### Symbol Resolution
  *
  * The resolver also resolves extra symbols that are not resolved
  * during the elaboration. Consider the following example:
  *
  * ```mls
  * val m: module M = M.v.v
  * module M with
  *   val v: module M = M
  * ```
  *
  * At the time of elaboration on `M.v.v`, the elaborator hasn't
  * elaborated the module `M` yet, so it merely knows that `M` is a
  * module and `v` is a member of `M`. It doesn't know that `M.v` is a
  * module, so it cannot resolve `M.v.v` to the correct member symbol.
  * Therefore, resolution of such symbols is deferred to the resolver. 
  */
class Resolver(tl: TraceLogger)
(using raise: Raise, state: State, ctx: Elaborator.Ctx):
  import tl.*
  import Resolver.*
  import Expect.*
  import ModuleChecker.*

  /**
    * Traverse a block and resolve any resolvable sub-terms. This is
    * usually the entry point for the resolver.
    */
  def traverseBlock(blk: Term.Blk)(using ICtx): ICtx =
  trace(s"Traversing block: $blk"):
    traverseStmts(blk.stats).givenIn:
      traverse(blk.res, expect = Any)
      ictx
  
  @tailrec
  final def traverseStmts(stmts: Ls[Statement])(using ICtx): ICtx = stmts match
    case Nil => ictx
    case stmt :: rest => 
      log(s"Traversing statement: $stmt")
      val newICtx = stmt match
        case tdf: Definition =>
          traverseDefn(tdf)
        
        case t: Term =>
          traverse(t, expect = NonModule(N))
          ictx
        
        // Default Case. e.g., import statements, let bindings.
        case _ =>
          stmt.subTerms.foreach(traverse(_, expect = NonModule(N)))
          ictx
      
      traverseStmts(rest)(using newICtx)
    
  
  def expand2DotClass(t: Resolvable, expect: Expect.Module | Expect.Class) = t.resolvedSym match
    case S(bsym: BlockMemberSymbol) if bsym.hasLiftedClass => 
      val sym = expect match
        case _: Expect.Module => bsym.asMod
        case _: Expect.Class => bsym.asCls
      sym.foreach: sym =>
        if sym isnt ctx.builtins.Array then
          t.expand(S(Term.SynthSel(t.duplicate, new Tree.Ident("class"))(S(sym), S(Type.Ref(sym, Nil)))))
    case _ =>
      ()
  
  /**
    * Traverse a term: traverse the sub-terms, resolve the term, and
    * check the modulefulness of the term.
    */
  def traverse(t: Term, expect: Expect)(using ictx: ICtx): Unit =
  trace(s"Traversing term: $t"):
    
    t match
      case blk: Term.Blk =>
        traverseBlock(blk)
      case Term.Rcd(mut, stats) =>
        traverseStmts(stats)
      
      case t: Term.IfLike =>
        def split(s: Split): Unit = s match
          case Split.Cons(head, tail) =>
            traverse(head.scrutinee, expect = NonModule(N))
            head.pattern.subTerms.foreach(traverse(_, expect = NonModule(N)))
            split(head.continuation)
            split(tail)
          case Split.Let(sym, term, tail) =>
            traverse(term, expect = NonModule(N))
            split(tail)
          case Split.Else(default) =>
            traverse(default, expect = Any)
          case Split.End =>
        split(t.desugared)
      
      case Term.Handle(lhs, rhs, args, derivedClsSym, defs, body) =>
        traverse(rhs, expect = Class(S("The 'handle' keyword requires a statically known class.")))
        args.foreach(traverse(_, expect = NonModule(N)))
        defs.foreach(d => traverseDefn(d.td))
        traverse(body, expect = NonModule(N))
        
      case Term.New(cls, args, rft) =>
        traverse(cls, expect = Class(S("The 'new' keyword requires a statically known class; use the 'new!' operator for dynamic instantiation.")))
        args.foreach(traverse(_, expect = NonModule(N)))
        rft.foreach((sym, bdy) => traverseBlock(bdy.blk))
      
      case t: Resolvable =>
        resolve(t, prefer = expect, inAppPrefix = false, inTyPrefix = false, inCtxPrefix = false)
        t.expanded match
        case t: Resolvable => expect match
          case expect: Expect.Class => expand2DotClass(t, expect = expect)
          case _ =>
        case _ =>
      
      case _ =>
        t.subTerms.foreach(traverse(_, expect = NonModule(N)))
    
    
    /* Post Traversal - Checks */
    
    // * The `module checks` checks the term's all possibly overloaded
    // * definitions / declarations. It raise errors only if the term
    // * can only be interpreted as a module.
    
    // TODO: currently it checks for only overloaded statically
    // known classes, it might require checking other definitions also
    // later.
    
    val evalsToModule = ModuleChecker.evalsToModule(t, prefer = expect)
    val evalsToStaticClass = ModuleChecker.isStaticClass(t)
    log(s"Checking ${t}: expect ${expect}, evalsToModule = ${evalsToModule}, evalsToStaticClass = ${evalsToStaticClass}")
    
    if expect.`module` && !evalsToModule then
      raise(ErrorReport(msg"Expected a module; found non-moduleful ${t.describe}." -> t.toLoc 
        :: expect.message))
    if expect.nonModule && evalsToModule && !evalsToStaticClass then
      raise(ErrorReport(msg"Unexpected moduleful ${t.describe}." -> t.toLoc 
        :: expect.message))
    
    if expect.`class` && !evalsToStaticClass then
      raise(ErrorReport(msg"Expected a statically known class; found ${t.describe}." -> t.toLoc
        :: expect.message))
    
  end traverse
  
  def traverseDefn(defn: Definition)(using ICtx): ICtx =
  trace(s"Resolving definition: $defn"):
    def traverseTermDef(tdf: TermDefinition) =
      val TermDefinition(_k, _sym, _tsym, 
        pss, tps, sign, body, 
        _resSym, TermDefFlags(isMethod), modulefulness, annotations, comp
      ) = tdf
      /** 
       * Add the contextual parameters in pss to the ICtx so that they
       * can later be referred (be resolved to) in the body of the term
       * definition.
       */
      def withCtxParams(using ICtx): ICtx = pss
        .filter(_.flags.ctx)
        .foldLeft(ictx): (ictx, ps) => 
          ps.params.foldLeft(ictx): (ictx, p) => 
            p.sign match
              case S(sign) =>
                ictx + (resolveSign(sign, expect = Any), p.sym)
              case N =>
                // The type signature should be present because of the syntax of contextual parameter.
                lastWords(s"No type signature for contextual parameter ${defn.showDbg} at ${defn.toLoc}")
      
      if isMethod && modulefulness.isModuleful then
        raise(ErrorReport(msg"${tdf.k.desc.capitalize} returning modules should not be a class member." -> defn.toLoc :: Nil))
      
      pss.foreach(_.allParams.foreach(traverseParam(_)))
      tps.getOrElse(Nil).flatMap(_.subTerms).foreach(traverse(_, expect = NonModule(N)))
      sign.foreach(traverseSign(_,
        expect = if modulefulness.modified
          then Module(S(msg"${tdf.k.desc.capitalize} marked as returning a 'module' must have a module return type."))
          else NonModule(S(msg"${tdf.k.desc.capitalize} must be marked as returning a 'module' in order to have a module return type."))
      ))
      
      body.foreach(traverse(_,
        expect = if modulefulness.modified
          then Module(S(msg"${tdf.k.desc.capitalize} marked as returning a 'module' but not returning a module."))
          else NonModule(S(msg"${tdf.k.desc.capitalize} must be marked as returning a 'module' in order to return a module."))
      )(using withCtxParams))
      annotations.flatMap(_.subTerms).foreach(traverse(_, expect = NonModule(N)))
    
    def traverseClassLikeDef(cld: ClassLikeDef) =
      /**
       * Add the contextual parameters in the class-like definition to
       * the ICtx so that they can later be referred (be resolved to) in
       * the body of the class-like definition.
       */
      def withCtxParams(using ICtx): ICtx = (cld.paramsOpt.toList.iterator ++ cld.auxParams)
        .filter(_.flags.ctx)
        .foldLeft(ictx): (ictx, ps) => 
          ps.params.foldLeft(ictx): (ictx, p) => 
            p.sign match
              case S(sign) => 
                val sym = p.fldSym.getOrElse(die)
                ictx + (resolveSign(sign, expect = Any), sym)
              case N =>
                // The type signature should be present because of the syntax of contextual parameter.
                lastWords(s"No type signature for contextual parameter ${defn.showDbg} at ${defn.toLoc}")
      
      cld.paramsOpt.foreach(_.allParams.foreach(traverseParam(_)))
      cld.annotations.flatMap(_.subTerms).foreach(traverse(_, expect = NonModule(N)))
      cld.ext.foreach(traverse(_, expect = NonModule(N)))

      traverseBlock(cld.body.blk)(using withCtxParams)
    
    defn match
    
    // Case: instance definition. Add the instance to the context.
    case defn @ TermDefinition(k = Ins, sym = sym, flags = TermDefFlags(isMethod), sign = sign) =>
      log(s"Resolving instance definition ${defn.showDbg}")
      traverseTermDef(defn)
      sign match
        case N =>
          // By the syntax of instance defintiion, the type signature should be present.
          lastWords(s"No type signature for instance definition ${defn.showDbg} at ${defn.toLoc}")
        case S(sign) => 
          ictx + (resolveSign(sign, expect = Any), sym)
    
    // Case: Fun/Val definition. 
    case defn @ TermDefinition(k = Fun | ImmutVal | MutVal) =>
      log(s"Resolving ${defn.k.desc} definition $defn")
      traverseTermDef(defn)
      ictx
    
    // Case: Class-like definition. Add the contextual parameters to the
    // context and use the context to traverse through the body.
    // Traverse through other subterms with original context.
    case defn: ClassLikeDef =>
      log(s"Resolving ${defn.kind.desc} definition $defn")
      
      // For pattern definitions, we need to traverse through the pattern body.
      defn match
        case defn: PatternDef =>
          defn.pattern.subTerms.foreach(traverse(_, expect = NonModule(N)))
        case _: ClassLikeDef => ()
      
      traverseClassLikeDef(defn)
      ictx
    
    // Case: other definition forms. Just traverse through the sub-terms.
    case t =>
      t.subTerms.foreach(traverse(_, expect = NonModule(N)))
      ictx
  
  /**
    * Resolve a resolvable term. This involves:
    * 1. Resolving the sub-terms of the term. Because resolving a term
    *    may require the sub-terms to be resolved first.
    * 3. Resolving the (new) symbol of the term. If a term is moduleful,
    *    the symbol should be some module symbol. The implicit arguments
    *    resolved in the previous step should also be used to resolve
    *    the symbol of the term.
    * 2. Resolving the implicit arguments of the term. This may change
    *    the semantic of the term, so it has to done before the symbol
    *    resolution.
    *
    * @param inAppPrefix if true, the currently resolving term is the
    * prefix of an App. The eta-expansion should only happens on the
    * outer-most App term, rather than on the in-between App terms
    * (otherwise the expansion might be redundant).
    * 
    * @param inCtxPrefix if true, the currently resolving term is the
    * prefix of an App where the implicit arguments are explicitly
    * specified, e.g., `f(using 42)`. The implicit arguments should be
    * resolved on the the App `f(using 42)`, but not on the base of the
    * App `f`.
    * @param inTyPrefix if true, the currently resolving term is the
    * prefix of an TyApp, e.g., `f[Int]`. The implicit arguments should
    * be resolved on the the TyApp `f[Int]`, but not on the base of the
    * TyApp `f`.
    */
  def resolve(t: Resolvable, prefer: Expect, inAppPrefix: Bool, inCtxPrefix: Bool, inTyPrefix: Bool)(using ICtx): (Opt[CallableDefinition], ICtx) =
  trace[(Opt[CallableDefinition], ICtx)](
    s"Resolving resolvable term: ${t}, (inPrefix = ${inTyPrefix})", 
    _ => s"~> ${t.expanded} (sym = ${t.resolvedSym}, typ = ${t.resolvedTyp})"
  ):
    // Resolve the sub-resolvable-terms of the term. 
    val (defn, newICtx1) = 
      t match
      // Note: the arguments of the App are traversed later because the
      // definition is required.
      case Term.App(lhs: Resolvable, args) =>
        val result = args match
          case t @ Term.CtxTup(_) => 
            resolve(lhs, prefer = prefer, inAppPrefix = true, inCtxPrefix = true, inTyPrefix = inTyPrefix)
          case _ => 
            resolve(lhs, prefer = prefer, inAppPrefix = true, inCtxPrefix = inCtxPrefix, inTyPrefix = inTyPrefix)
        resolveSymbol(t, prefer = prefer)
        resolveType(t, prefer = prefer)
        result
      case Term.App(lhs, _) =>
        traverse(lhs, expect = Any)
        (t.callableDefn, ictx)
      
      case Term.TyApp(lhs: Resolvable, targs) =>
        resolve(lhs, prefer = prefer, inAppPrefix = inAppPrefix, inCtxPrefix = inCtxPrefix, inTyPrefix = true)
        targs.foreach(traverse(_, expect = Any))
        resolveSymbol(t, prefer = prefer)
        resolveType(t, prefer = prefer)
        (t.callableDefn, ictx)
      case Term.TyApp(lhs, targs) =>
        traverse(lhs, expect = Any)
        targs.foreach(traverse(_, expect = Any))
        (t.callableDefn, ictx)
      
      case AnySel(pre: Resolvable, id) =>
        resolve(pre, prefer = prefer, inAppPrefix = false, inCtxPrefix = false, inTyPrefix = false)
        resolveSymbol(t, prefer = prefer)
        resolveType(t, prefer = prefer)
        (t.callableDefn, ictx)
      case AnySel(pre, id) =>
        traverse(pre, expect = Any)
        (t.callableDefn, ictx)
      
      case Term.Ref(_: BlockMemberSymbol) =>
        resolveSymbol(t, prefer = prefer)
        resolveType(t, prefer = prefer)
        (t.callableDefn, ictx)
      case Term.Ref(_) =>
        resolveSymbol(t, prefer = prefer)
        resolveType(t, prefer = prefer)
        (N, ictx)
    
    t.expandedResolvableIn: t =>
      log(s"Resolving resolvable term ${t} with sym = ${t.resolvedSym}, typ = ${t.resolvedTyp}: ${defn}")
      
      // Fill the context with possibly the type arguments information.
      val newICtx2 = newICtx1.givenIn:
        defn match
        case S(defn) =>
          val tparams: Opt[Ls[Param]] = defn.tparams
          val targs: Opt[Ls[Term]] = t match
            case Term.TyApp(lhs, targs) => S(targs)
            case _ => N
          val newICtx = (tparams, targs) match
            case (S(tparams), S(targs)) =>
              if tparams.length != targs.length then
                raise(ErrorReport(msg"Expected ${tparams.length.toString()} type arguments, " +
                  msg"got ${targs.length.toString()}" -> t.toLoc :: Nil))
              (tparams zip targs).foldLeft(ictx):
                case (ictx, (tparam, targ)) => 
                  val sym = tparam.sym
                  val typ = resolveSign(targ, expect = Any)
                  log(s"Resolving App with type arg ${sym} = $typ")
                  ictx.withTypeArg(sym, typ)
            case (S(tparams), N) => tparams.foldLeft(ictx): 
              case (ictx, tparam) => 
                log(s"Resolving App with type arg ${tparam.sym} unspecified")
                ictx
            case (N, _) => ictx
          newICtx
        case N =>
          ictx
      
      // Resolve the implicit arguments.
      newICtx2.givenIn:
        // Create a new term definition for App terms. The new term
        // definition is for handling partial applications. 
        //
        // For example: In `fun f(a)(b) = 42`, f's definition should
        // indicate that it accepts two argument lists; f(42)'s definition
        // should indicate that it accepts one argument list; f(42)(43)'s
        // definition should indicate that it accepts zero argument lists.
        //
        // Currently, only parameters are processed for these new term
        // definitions. The type parameters and result type are kept
        // as-is. In the future we may take them into consideration as
        // well.
        val newDefn: Opt[CallableDefinition] = t match
          case Term.App(lhs, as) => defn match
            case S(defn @ CallableDefinition(params = ps :: pss)) =>
              val (argCountUB, argCountLB) = as match
              // Tup: regular arguments
              case tup: (Term.Tup | Term.CtxTup) => 
                val fields = tup match
                  case Term.Tup(fs) => fs
                  case Term.CtxTup(fs) => fs
                (
                  !fields.exists(_.isInstanceOf[Spd]),
                  (
                    fields.count:
                      case Fld(asc = S(_)) => false
                      case _: Fld => true
                      case _: Spd => false
                  ) + (
                    fields.collectFirst:
                      case Fld(asc = S(_)) => 1
                    .getOrElse(0)
                  )
                )
              // Other: spread arguments
              case _ => (false, 0)
              
              (ps.paramCountUB, argCountUB) match
                case (true, true) => if ps.paramCountLB != argCountLB then
                  raise(ErrorReport(msg"Expected ${ps.paramCountLB.toString()} arguments, " +
                    msg"got ${argCountLB.toString()}" -> as.toLoc :: Nil))
                case (true, false) => if ps.paramCountLB < argCountLB then
                  raise(ErrorReport(msg"Expected ${ps.paramCountLB.toString()} arguments, " +
                    msg"got at least ${argCountLB.toString()}" -> as.toLoc :: Nil))
                case (false, true) => if ps.paramCountLB > argCountLB then
                  raise(ErrorReport(msg"Expected at least ${ps.paramCountLB.toString()} arguments, " +
                    msg"got ${argCountLB.toString()}" -> as.toLoc :: Nil))
                case (false, false) => ()
              
              /**
               * Zip (pair) a list of parameter and a list of arguments.
               *
               * If there are some spread parameters, we are not able to
               * pair all the parameters and arguments statically. We will
               * try to pair as many as possible.
               */
              @tailrec
              def zip(ps: Ls[Param], as: Ls[Elem], recordArgs: Ls[Fld], beforeSpread: Bool): Ls[Fld] = (ps, as) match
                // The spread argument takes all the remaining arguments.
                case (ps, (a: Spd) :: as) =>
                  traverse(a.term, expect = NonModule(N))
                  zip(ps, as, recordArgs, false)
                case (ps, a :: as) if !beforeSpread =>
                  a.subTerms.foreach(traverse(_, expect = NonModule(N)))
                  zip(ps, as, recordArgs, false)
                
                // Pair the parameter and the argument.
                case (p :: ps, (a @ Fld(asc = N)) :: as) =>
                  traverse(a.term, 
                    // note: we accept regular arguments for module parameters
                    expect = if p.modulefulness.isModuleful
                      then Any
                      else NonModule(S(msg"Module argument passed to a non-module parameter."))
                  )
                  zip(ps, as, recordArgs, true)
                
                // Record Arguments. They are pushed to the last parameter.
                case (_, (a @ Fld(asc = S(_))) :: as) =>
                  zip(ps, as, a :: recordArgs, true)
                
                // If there are more parameters, there must be a spread
                // argument, or some record arguments before.
                case (p :: ps, Nil) =>
                  recordArgs.reverse
                  
                // If there are more arguments, all of them go to `restParam`.
                case (Nil, a :: as) =>
                  a.subTerms.foreach(traverse(_, expect = NonModule(N)))
                  zip(Nil, as, recordArgs, beforeSpread)
                
                case (Nil, Nil) => 
                  recordArgs.reverse
              end zip
              
              // Application arguments that are not tuples represent spreads, as in `f(...arg)`
              val args = as match
                case Term.Tup(args) => args
                case Term.CtxTup(args) => args
                case spd => Spd(true, spd) :: Nil
              
              // The lhs of the App is already traversed by the recursive
              // `traverse` or `resolve` at the beginning.
              val recordArgs = zip(ps.params, args, Nil, true)
              recordArgs.foreach:
                _.subTerms.foreach(traverse(_, expect = NonModule(N)))
              S(defn.copy(params = pss))
            case _ =>
              traverse(as, expect = NonModule(N))
              N
          case _ => defn
        
        // Resolve the implicit arguments.
        newDefn match
        case S(defn) if !inCtxPrefix && !inTyPrefix =>
          /**
           * Resolve all possible implicit arguments and perform eta-expansion.
           * 
           * @return (1) A lambda accepting a term, applying the implicit
           * arguments and performing eta-expansion on the term, and
           * return the result. (2) The residual parameter lists that are not
           * consumed by this resolution.
           */
          def expand(pss: Ls[ParamList], lam: Term => Term, bod: Term => Term): (Term => Term, Ls[ParamList]) =
            pss match
              // The current parameter list is not a using clause, and
              // there are more using clauses in later parameter lists,
              // so perform eta-expansion.
              case (ps @ ParamList(
                flags = ParamListFlags(ctx = false)
              )) :: pss if !inAppPrefix && pss.exists(_.flags.ctx) =>
                val as = ps.params.map(p => Fld(p.flags, p.sym.ref().dontResolve, N))
              //   val as = ps.params.map(p => Fld(p.flags, p.sym.ref().resolve, N))
                val newLam = (t: Term) => 
                  lam(Term.Lam(ps, t))
                val newBod = (t: Term) =>
                  Term.App(bod(t), Term.Tup(as)(DummyTup))(DummyApp, N, FlowSymbol("implicit app")).dontResolve
                expand(pss, newLam, newBod)
              // The current parameter list is a using clause, so resolve
              // implicit arguments from the context.
              case (ps @ ParamList(
                flags = ParamListFlags(ctx = true)
              )) :: pss =>
                val as = ps.params.map(resolveArg(_)(t))
                val newBod = (t: Term) =>
                  Term.App(bod(t), Term.Tup(as)(DummyTup))(DummyApp, N, FlowSymbol("implicit app")).dontResolve
                expand(pss, lam, newBod)
              case _ =>
                ((t: Term) => lam(bod(t)), pss)
          
          val (expansionFn, pss) = expand(defn.params, identity, identity)
          if defn.params.length =/= pss.length then
            val expansion = expansionFn(t.duplicate)
            t.expand(S(expansion))
            expansion match // * expansion may change the semantics, thus symbol is also changed
            case r: Resolvable => 
              resolveSymbol(r, prefer = prefer)
              resolveType(r, prefer = prefer)
            case _ => ()
          
          (S(defn.copy(params = pss)), ictx)
        case S(defn) =>
          t.dontResolve
          (S(defn), ictx)
        case _ =>
          t.dontResolve
          (N, ictx)
  
  /**
   * Resolve the symbol for a resolvable term, which was not resolved by
   * the elaborator due to unready definitions. After the symbol
   * resolution, the term is expanded into the same term, 
   *
   * In particular, for Sel and SynthSel terms, it checks the definition
   * of the prefix (note that the prefix should be resolved before this
   * term is resolved), and if prefix is moduleful, it resolves the
   * symbol for the member to be selected.
   *
   * Then, for all terms including Sel and SynthSel, it unwraps the
   * parameters as an App, even for a generalized "App" that has no
   * parameter list (in order to handle implicit applications), and
   * resolves the symbol for the result of this App.
   *
   * This also expands the LHS `Foo` of a selection to `Foo.class` if
   * the selection is selecting a static member from a lifted module.
   */
  def resolveSymbol(t: Resolvable, prefer: Expect)(using ictx: ICtx): Unit =
  trace[Unit](
    s"Resolving symbol for term: ${t} (prefer = ${prefer})", 
    _ => s"-> (sym = ${t.resolvedSym}, typ = ${t.resolvedTyp})"
  ):
    // If the term has an expansion already, it is likely that there is
    // an internal error because otherwise we should resolve the symbol
    // of the expansion instead.
    /*
    if t.hasExpansion then lastWords:
      s"resolveSymbol: term ${t} already has an expansion ~> ${t.expanded}, " +
      s"thus the resolver cannot resolve its symbol"
    */
    // * We can't perform the check because of UCS and handler reusing terms.
    
    t.expandedResolvableIn: t =>
      t match
      
      // The symbol resolution already failed in the elaborator. We will
      // not try to resolve it again in the resolver.
      case _ if t.symbol.exists(_.isInstanceOf[ErrorSymbol]) => ()
      
      case t @ AnySel(lhs: Resolvable, id) => lhs.expandedResolvableIn: lhs =>
        log(s"Resolving symbol for ${t}, defn = ${lhs.defn}")
        lhs.singletonDefn.foreach: mdef =>
          val fsym = mdef.body.members.get(id.name)
          fsym match
          case S(fldSym) => 
            val bsym = fldSym.asBlkMember.getOrElse:
              lastWords(s"${mdef}: field symbol found ${fldSym} but no block member symbol")
            log(s"Resolving symbol for ${t}, defn = ${lhs.defn}")
            t.expand(S(t.withSym(bsym)))
            expand2DotClass(lhs, expect = Expect.Module(N))
            log(s"Resolved symbol for ${t}: ${bsym}")
          case N => 
            t.expand(S(t.withSym(ErrorSymbol(id.name, Tree.Dummy))))
            raise: 
              ErrorReport(
                msg"${mdef.kind.desc.capitalize} '${mdef.sym.nme}' " +
                msg"does not contain member '${id.name}'" -> t.toLoc :: Nil,
                extraInfo = S(mdef))
      case _ =>
  
  /**
   * Resolve the type for a resolvable term representing an expression
   * (as opposed to a term representing a type, i.e., signature). The
   * resolvable term should should already be symbol-resolved by
   * `resolveSymbol`. After this type resolution, the resolvable term is
   * expanded into a copy of the term with the `typ` field set to the
   * resolved type.
   */
  def resolveType(t: Resolvable, prefer: Expect)(using ictx: ICtx): Unit = t.expandedResolvableIn: t =>
    trace[Unit](
      s"Resolving the type for term: ${t} (prefer = ${prefer}, sym = ${t.resolvedSym})", 
      _ => s"-> typ = ${t.resolvedTyp})"
    ):
      def disambSym(bms: BlockMemberSymbol): Opt[FieldSymbol] = prefer match
        case _: Module => bms.asMod
        case _: Class => bms.asCls
        case _: NonModule => 
          val trmSym = bms.defn match
          case S(defn: TermDefinition) => S(defn.tsym)
          case _ => N
          trmSym orElse bms.asPrincipal
        case _: Any => bms.defn match
          case S(defn: TermDefinition) => S(defn.tsym)
          case S(defn: ClassDef) => S(defn.sym)
          case S(defn: ModuleOrObjectDef) => S(defn.sym)
          case _ => N
      
      t match
      case t @ Apps(base: Resolvable, ass) => 
        val decl = base.resolvedSym match
          case S(bms: BlockMemberSymbol) => 
            val disambBms = disambSym(bms)
            log(s"Disambiguate ${bms} into ${disambBms} (defn = ${disambBms.map(_.defn)})")
            disambBms match
            case S(disambBms) => disambBms.defn
            case N => bms.defn
          case S(bls: BlockLocalSymbol) => bls.decl
          case S(fs: FieldSymbol) => fs.defn
          case _ => N
        log(s"Declaration: ${decl}")
        decl match
        case S(defn: TermDefinition) if defn.params.length === ass.length =>
          val ty = defn.sign.map(resolveSign(_, expect = Expect.fromModulefulness(defn.modulefulness)))
          ty.foreach(ty => t.expand(S(t.withTyp(ty))))
        case S(defn: Param) if ass.isEmpty =>
          val ty = defn.sign.map(resolveSign(_, expect = Expect.fromModulefulness(defn.modulefulness)))
          ty.foreach(ty => t.expand(S(t.withTyp(ty))))
        case S(defn: ModuleOrObjectDef) if ass.isEmpty =>
          val ty = Type.Ref(defn.sym, Nil)
          t.expand(S(t.withTyp(ty)))
        case _ =>
      case _ =>
  end resolveType
  
  def resolveArg(p: Param)(lhs: Term)(using ictx: ICtx): Elem =
    log(s"Resolving implicit argument, expecting a ${p.sign}")
    p.sign match
      case S(sign) => 
        val ty = resolveSign(sign, expect = if p.modulefulness.modified then Module(N) else NonModule(N))
        log(s"Resolving implicit argument, expecting a ${ty.show}")
        ictx.query(ty) match
        case R(i) =>
          log(s"Resolved ${p.sign} with instance ${i}")
          val ref = i.sym.ref()
          traverse(ref,
            // note: we accept regular arguments for module parameters
            expect = if p.modulefulness.isModuleful
              then Any
              else NonModule(S(msg"Module argument passed to a non-module parameter.")),
          )
          Fld(p.flags, ref, N)
        case L(msgs) =>
          raise(ErrorReport(
            msg"Cannot query instance of type ${ictx.showTy(ty)} for call: " -> lhs.toLoc ::
            msg"Required by contextual parameter declaration: " -> p.toLoc :: msgs))
          Fld(FldFlags.empty, Term.Error, N)
      case N =>
        // By the syntax of contextual parameter, 
        // the type signature should be present.
        lastWords(s"No type signature for contextual parameter ${p.showDbg} at ${p.toLoc}")
  
  def traverseParam(p: Param)(using ictx: ICtx): Unit =
    log(s"Resolving parameter ${p.showDbg}")
    if p.modulefulness.modified then
      if p.sign.isEmpty then
        raise(ErrorReport(msg"Module parameter must have explicit type." -> p.sym.toLoc :: Nil))
    p.sign.foreach:
      traverseSign(_, 
        expect = if p.modulefulness.modified
          then Module(S(msg"Module parameter must have a module type."))
          else NonModule(S(msg"Non-module parameter must have a non-module type.")),
      )
  
  /**
   * Traverse through a term that is expected to be a type. In this
   * process, it reports any non-type terms, checks if the term
   * satisfies the expectation, resolves the symbol of the term, and
   * checks the arity of type params/args.
   *
   * @param inAppPrefix if true, the currently traversing term is the
   * prefix of an TyApp. 
   * @param expect the expectation on the type. See [[Expect]] for
   * details.
   */
  def traverseSign(t: Term, expect: Expect, inAppPrefix: Bool = false)(using ictx: ICtx): Unit =
  trace(s"Traversing type ${t}, expecting ${expect}"):
    
    // * Traverse through the sub-terms.
    t match
    case Term.Ref(_) =>
    case Term.Lit(_) =>
    case Term.Tup(_) => t.subTerms.foreach(traverse(_, expect = NonModule(N)))
    case Term.UnitVal() =>
    // Literals with operators. e.g., -42
    case Term.App(Term.Ref(_: BuiltinSymbol), Term.Tup(Fld(term = Term.Lit(_)) :: Nil)) =>
    
    // Selection. The prefix should be a term, rather than a type, that
    // can be selected from.
    case AnySel(base, _) =>
      base.subTerms.foreach(traverse(_, expect = Any))
    
    // Type Application. Traverse the type constructor and arguments,
    // respectively.
    case Term.TyApp(con, targs) => 
      traverseSign(con, expect = expect, inAppPrefix = true)
      targs.foreach(traverseSign(_, expect = Expect.NonModule(S("Type arguments should be non-moduleful types."))))
    
    // Complex type: Function type, Wildcard type, Composed type,
    // Negation type, Forall type, 
    case t: (Term.FunTy | Term.WildcardTy | Term.CompType | Term.Neg | Term.Forall | Term.Tup) =>
      t.subTerms.foreach(traverseSign(_, expect = Expect.NonModule(N)))
    
    // t is not a type.
    case _ => 
      raise(ErrorReport(msg"Expected a type, got ${t.describe}" -> t.toLoc :: Nil))
      return
    
    val typ = resolveSign(t, expect = expect)
    
    // * Resolve the symbol and type of the term.
    t match
      case t: Resolvable =>
        resolveSymbol(t, prefer = expect)
        t.expandedResolvableIn(_.withTyp(typ))
      case _ => ()
    
    // * Check if the term satisfies the expectation.
    // * Check the arity of type params/args.
    typ match 
      case Type.Ref(sym: TypeSymbol, targs) if !inAppPrefix =>
        sym.defn.flatMap(CallableDefinition.fromDefn(_)).foreach: 
          case CallableDefinition(tparams = tparams) =>
            val tparamsNum = tparams.map(_.length)
            val targsNum = targs.length
            if tparamsNum.getOrElse(0) =/= targsNum then
              val tparamsMsg = tparamsNum.getOrElse("no").toString
              val targsMsg = if targsNum === 0 then "none" else targsNum.toString
              raise:
                ErrorReport:
                  msg"Expected ${tparamsMsg} type arguments, "
                  + msg"got ${targsMsg}" -> t.toLoc :: Nil
      case Type.Ref(sym: VarSymbol, targs) if !inAppPrefix =>
        // TODO: check arity?
      case _ =>
  
  /**
   * Given a symbol-resolved term that represents a type, resolve the
   * type that it represents.
   */
  def resolveSign(t: Term, expect: Expect): Type = 
    def raiseError(sym: Opt[Symbol] = N) =
      val defnMsg = sym match
        case S(sym: FieldSymbol) => sym.defn match
          case S(defn: TermDefinition) => s" denoting ${defn.k.desc} '${defn.sym.nme}'"
          case S(defn: ClassLikeDef) => s" denoting ${defn.kind.desc} '${defn.sym.nme}'"
          case _ => ""
        case _ => ""
      
      expect match
      case expect: Module => raise:
        ErrorReport(msg"Expected a module type; found ${t.describe}${defnMsg}." -> t.toLoc
          :: expect.message)
      case expect: Class => raise:
        ErrorReport(msg"Expected a statically resolvable class; found ${t.describe}${defnMsg}." -> t.toLoc
          :: expect.message)
      case expect: NonModule => raise:
        ErrorReport(msg"Expected a non-module type; found ${t.describe}${defnMsg}." -> t.toLoc
          :: expect.message)
      case _ => raise:
        ErrorReport(msg"Expected a type, got ${t.describe}${defnMsg}" -> t.toLoc :: Nil)
      Type.Error
    
    t match
      // If the term is a type application, e.g., T[A, ...], resolve the
      // type constructor and arguments respectively.
      case Term.TyApp(con, args) => resolveSign(con, expect = expect) match
        case Type.Ref(sym, Nil) =>
          Type.Ref(sym, args.map(resolveSign(_, expect = Any)))
        case _ =>
          raise(ErrorReport(msg"Expected a type constructor, got ${t.describe}" -> t.toLoc :: Nil))
          Type.Error
      
      case Term.Lit(_) => if expect.module 
        then raiseError()
        else Type.NotImplemented // TODO: Support Lit
      case Term.UnitVal() => if expect.module
        then raiseError()
        else Type.NotImplemented // TODO: Support UnitVal
      case Term.App(Term.Ref(_: BuiltinSymbol), Term.Tup(Fld(term = Term.Lit(_)) :: Nil)) => if expect.module
        then raiseError()
        else Type.NotImplemented // TODO: Support Lit with operator
      case _: (Term.FunTy | Term.WildcardTy | Term.CompType | Term.Neg | Term.Forall | Term.Tup | Term.Lit) => if expect.module
        then raiseError()
        else Type.NotImplemented // TODO: Support complex types
      
      // Otherwise, resolve the term directly.
      case _ => t.resolvedSym match
        // A VarSymbol is probably a type parameter.
        case S(sym: VarSymbol) if ModuleChecker.isTypeParam(sym) =>
          if expect.module 
          then raiseError(S(sym))
          else Type.Ref(sym, Nil)
        case S(tsym) =>
          val dtsym = expect match
          case expect: Module => tsym.asMod.getOrElse(raiseError(S(tsym)))
          case expect: Class => tsym.asCls.getOrElse(raiseError(S(tsym)))
          case expect: NonModule => tsym.asNonModTpe.getOrElse(raiseError(S(tsym)))
          case _ => tsym.asTpe.getOrElse(raiseError(S(tsym)))
          dtsym match
            case dtsym: TypeSymbol => Type.Ref(dtsym, Nil)
            case _ => Type.Error
        case N =>
          raise(ErrorReport(msg"Expected a type, got a non-type ${t.describe}" -> t.toLoc :: Nil))
          Type.Error

end Resolver

object AnySel:
  def unapply(t: (Term.Sel | Term.SynthSel)): S[(Term, Tree.Ident)] = t match
    case Term.Sel(lhs, id) => S((lhs, id))
    case Term.SynthSel(lhs, id) => S((lhs, id))

object ModuleChecker:
  
  extension (s: Split)
    private def results: Ls[Term] = 
      def go(s: Split): Ls[Term] = s match
        case Split.Cons(head, tail) => go(head.continuation) ::: go(tail)
        case Split.Let(_, _, tail) => go(tail)
        case Split.Else(term) => term :: Nil
        case Split.End => Nil
      go(s)
  
  /** Checks if a symbol is of a type parameter. */
  def isTypeParam(sym: VarSymbol): Bool = sym.decl
    .exists(_.isInstanceOf[TyParam])
  
  import Resolver.Expect
  
  /** Checks the term's modulefulness. */
  def evalsToModule(t: Term, prefer: Expect): Bool =
    def checkDecl(decl: Declaration): Bool = decl match
      /* Type Declaration / Defintiions */
      // A type is not moduleful if it is not a module. (obvious!)
      case ModuleOrObjectDef(kind = Mod) => true
      // Objects use ModuleDef but is not moduleful.
      case _: TypeLikeDef => false
      
      /* Term Declarationis / Definitions */
      case defn: TermDefinition => defn.modulefulness.isModuleful
      case defn: Param => defn.modulefulness.isModuleful
      // A type param is not a module because it is a type.
      case defn: TyParam => false
    
    def checkSym(sym: Symbol): Bool = sym match
      case sym: BuiltinSymbol => false
      case sym: BlockLocalSymbol => sym.decl.exists(checkDecl)
      case sym: FieldSymbol => prefer match
        case Expect.Module(_) => sym.existsModuleful
        case _ => !sym.existsNonModuleful
      
      case sym => lastWords(s"unsupported symbol type ${sym.getClass} (${sym})")
    
    t match
      case Term.Blk(_, res) => evalsToModule(res, prefer = prefer)
      case Term.IfLike(`if`, split) => split.results.exists(evalsToModule(_, prefer = prefer))
      case t: Resolvable => t.resolvedTyp match
        case S(ty) => ty.symbol.map(checkSym(_)).getOrElse(false)
        case N => false
      case _ => false
  
  def isStaticClass(t: Term): Bool = t.resolvedSym.exists(_.asCls.isDefined)
