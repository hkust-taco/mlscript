package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import utils.TraceLogger

import syntax.Tree
import syntax.{Fun, Ins, Mod, ImmutVal}
import syntax.Keyword.{`if`}
import semantics.Term
import semantics.Elaborator.State
import Resolver.ICtx.Type

import Message.MessageContext
import scala.annotation.tailrec
import hkmc2.syntax.MutVal
import hkmc2.semantics.ClassDef.Parameterized
import hkmc2.semantics.ClassDef.Plain
import hkmc2.syntax.Tree.Ident
import java.sql.Ref

object Resolver:
  
  /*
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
    
    def showEnv: Str =
      iEnv.values
        .flatMap(_.map((typ, instance) => s"${typ.show}"))
        .mkString("(", ", ", ")")
    
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
       * A type that is not specified. This is for when the type is not
       * known because no type inference is done.
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
(using raise: Raise, state: State):
  import tl.*
  import Resolver.ICtx
  import Resolver.ictx
  
  enum Expect:
    case Module(reason: Opt[Message])
    case NonModule(reason: Opt[Message])
    case Any
    
    def message: Ls[Message -> Opt[Loc]] = this match
      case Expect.Module(msg) => msg.toList.map(_ -> N)
      case Expect.NonModule(msg) => msg.toList.map(_ -> N)
      case Expect.Any => Nil
    
    def module = isInstanceOf[Module]
    
    def nonModule = this match
      case Expect.NonModule(_) => true
      case _ => false
    
  end Expect
  import Expect.*
  
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
          resolveDefn(tdf)
        
        case t: Term =>
          traverse(t, expect = NonModule(N))
          ictx
        
        // Default Case. e.g., import statements, let bindings.
        case _ =>
          stmt.subTerms.foreach(traverse(_, expect = NonModule(N)))
          ictx
      
      traverseStmts(rest)(using newICtx)
    
  
  /**
    * Traverse a term: traverse the sub-terms, resolve the term, and
    * check the modulefulness of the term.
    */
  def traverse(t: Term, expect: Expect)(using ictx: ICtx): Unit =
  trace(s"Traversing term: $t"):
    def check(body: => Unit) =
      body
      val evalsToModule = ModuleChecker.evalsToModule(t)
      if expect.module && !evalsToModule then
        raise(ErrorReport(msg"Expected a module, found non-moduleful ${t.describe}." -> t.toLoc 
          :: expect.message))
      if expect.nonModule && evalsToModule then
        raise(ErrorReport(msg"Unexpected moduleful ${t.describe}." -> t.toLoc 
          :: expect.message))
    
    check:
      t match
        case blk: Term.Blk =>
          traverseBlock(blk)
        case Term.Rcd(stats) =>
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
          split(t.normalized)
        
        case Term.New(cls, args, rft) =>
          traverse(cls, expect = Any)
          args.foreach(traverse(_, expect = NonModule(N)))
          rft.foreach((sym, bdy) => traverseBlock(bdy.blk))
        
        case t: Resolvable =>
          resolve(t)
        
        case _ => 
          t.subTerms.foreach(traverse(_, expect = NonModule(N)))

  def resolveDefn(defn: Definition)(using ICtx): ICtx =
  trace(s"Resolving definition: $defn"):
    def resolveCtxParams(pss: Ls[ParamList]): ICtx = pss
      .filter(_.flags.ctx)
      .foldLeft(ictx): (ictx, ps) => 
        ps.params.foldLeft(ictx): (ictx, p) => 
          p.sign match
            case S(sign) => resolveType(sign) match
              case N => ictx
              case S(tpe) => ictx + (tpe, p.sym)
            case N =>
              // The type signature should be present because of the syntax of contextual parameter.
              lastWords(s"No type signature for contextual parameter ${defn.showDbg} at ${defn.toLoc}")
    
    def traverseTermDef(tdf: TermDefinition) = tdf match
    case TermDefinition(_, _, _, pss, tps, sign, body, _, TermDefFlags(isMethod), modulefulness, annotations) =>
      if isMethod && modulefulness.isModuleful then
        raise(ErrorReport(msg"${tdf.k.desc.capitalize} returning modules should not be a class member." -> defn.toLoc :: Nil))
      
      pss.foreach(_.allParams.foreach(resolveParam(_)))
      tps.getOrElse(Nil).flatMap(_.subTerms).foreach(traverse(_, expect = NonModule(N)))
      sign.foreach(traverse(_,
        expect = if modulefulness.modified
          then Module(S(msg"${tdf.k.desc.capitalize} marked as returning a 'module' must have a module return type."))
          else NonModule(S(msg"${tdf.k.desc.capitalize} must be marked as returning a 'module' in order to have a module return type."))
      ))
      
      body.foreach(traverse(_,
        expect = if modulefulness.modified
          then Module(S(msg"${tdf.k.desc.capitalize} marked as returning a 'module' but not returning a module."))
          else NonModule(S(msg"${tdf.k.desc.capitalize} must be marked as returning a 'module' in order to return a module."))
      )(using resolveCtxParams(pss)))
      annotations.flatMap(_.subTerms).foreach(traverse(_, expect = NonModule(N)))
    
    defn match
    
    // Case: instance definition. Add the instance to the context.
    case defn @ TermDefinition(_, Ins, sym, pss, tps, sign, body, _, TermDefFlags(isMethod), modulefulness, annotations) =>
      log(s"Resolving instance definition ${defn.showDbg}")
      traverseTermDef(defn)
      sign match
        case N =>
          // By the syntax of instance defintiion, the type signature should be present.
          lastWords(s"No type signature for instance definition ${defn.showDbg} at ${defn.toLoc}")
        case S(sign) => resolveType(sign) match
          case N => ictx
          case S(typ) => ictx + (typ, sym)
    
    // Case: Fun/Val definition. 
    case defn @ TermDefinition(_, Fun | ImmutVal | MutVal, _, pss, tps, sign, body, _, TermDefFlags(isMethod), modulefulness, annotations) =>
      log(s"Resolving ${defn.k.desc} definition $defn")
      traverseTermDef(defn)
      ictx
    
    // Case: Class-like definition. Add the contextual parameters to the
    // context and use the context to traverse through the body.
    // Traverse through other subterms with original context.
    case defn: ClassLikeDef =>
      log(s"Resolving ${defn.kind.desc} definition $defn")
      
      defn.paramsOpt.foreach(_.allParams.foreach(resolveParam(_)))
      defn.annotations.flatMap(_.subTerms).foreach(traverse(_, expect = NonModule(N)))
      defn.ext.foreach(traverse(_, expect = NonModule(N)))

      traverseBlock(defn.body.blk)(using resolveCtxParams(defn.paramsOpt.toList))
    
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
    * @param inTyPrefix if true, the currently resolving term is the
    * prefix of an TyApp which the implicit arguments shouldn't be
    * resolved on it, but on the TyApp instead.
    */
  def resolve(t: Resolvable, inTyPrefix: Bool = false)(using ICtx): (Opt[TermDefinition], ICtx) =
  trace[(Opt[TermDefinition], ICtx)](s"Resolving resolvable term: ${t}, (inPrefix = ${inTyPrefix})", _ => s"~> ${t}"):
    // Resolve the sub-resolvable-terms of the term. 
    val (defn, newICtx1) = t match
      // Note: the arguments of the App are traversed later because the
      // definition is required.
      case Term.App(lhs: Resolvable, _) =>
        val result = resolve(lhs)
        resolveSymbol(t)
        result
      case Term.App(lhs, _) =>
        traverse(lhs, expect = Any)
        (t.termDefn, ictx)
      
      case Term.TyApp(lhs: Resolvable, targs) =>
        resolve(lhs, inTyPrefix = true)
        targs.foreach(traverse(_, expect = Any))
        resolveSymbol(t)
        (t.termDefn, ictx)
      case Term.TyApp(lhs, targs) =>
        traverse(lhs, expect = Any)
        targs.foreach(traverse(_, expect = Any))
        (t.termDefn, ictx)
      
      case AnySel(pre: Resolvable, id) =>
        resolve(pre)
        resolveSymbol(t)
        (t.termDefn, ictx)
      case AnySel(pre, id) =>
        traverse(pre, expect = Any)
        (t.termDefn, ictx)
      
      case Term.Ref(_) =>
        resolveSymbol(t)
        (t.termDefn, ictx)
    
    log(s"Resolving resolvable with defn = ${defn}")
    
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
              case (ictx, (tparam, targ)) => (tparam.sym, resolveType(targ)) match
                case (sym: VarSymbol, S(typ)) =>
                  log(s"Resolving App with type arg ${sym} = $typ")
                  ictx.withTypeArg(sym, typ)
                case _ => ictx
          case (S(tparams), N) => tparams.foldLeft(ictx): 
            case (ictx, tparam) => 
              log(s"Resolving App with type arg ${tparam.sym} = ${Type.Unspecified}")
              ictx.withTypeArg(tparam.sym, Type.Unspecified)
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
      // should indicate that it accepts one argument list; f(42, 43)'s
      // definition should indicate that it accepts zero argument lists.
      //
      // Currently, only parameters are processed for these new term
      // definitions. The type parameters and result type are kept
      // as-is. In the future we may take them into consideration as
      // well.
      val newDefn: Opt[TermDefinition] = t match
      case Term.App(lhs, as) => defn match
        case S(defn @ TermDefinition(params = ps :: pss)) =>
          val (argCountUB, argCountLB) = as match
          // Tup: regular arguments
          case tup: Term.Tup => (
            !tup.fields.exists(_.isInstanceOf[Spd]),
            tup.fields.map:
              case Fld(asc = S(_)) => 0
              case _: Fld => 1
              case _: Spd => 0
            .sum +
            tup.fields.exists:
              case Fld(asc = S(_)) => true
              case _ => false
            .into(if _ then 1 else 0)
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
          
          val args = as match
            case Term.Tup(args) => args
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
      case S(defn) if !inTyPrefix =>
        def resolveParamList(pss: Ls[ParamList], ass: Ls[Term.Tup]): (Ls[ParamList], Ls[Term.Tup]) = pss match
          case ParamList(flags = ParamListFlags(ctx = true), params = ps) :: pss =>
            val as = ps.map(resolveArg(_)(t))
            resolveParamList(pss, Term.Tup(as)(Tree.Tup(Nil)) :: ass)
          case _ => (pss, ass.reverse)
        
        val (pss, ass) = resolveParamList(defn.params, Nil)
        t.withIArgs(ass)
        
        // new implicit application may change the semantics
        if ass.nonEmpty then
          resolveSymbol(t)
          
        (S(defn.copy(params = pss)), ictx)
      case _ =>
        t.withIArgs(Nil)
        (N, ictx)
  
  /**
   * Resolve the symbol for a resolvable term, which was not resolved by
   * the elaborator due to unready or missing definitions.
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
   */
  def resolveSymbol(t: Resolvable)(using ictx: ICtx): Unit =
    // The symbol resolution already failed in the elaborator. We will
    // not try to resolve it again in the resolver.
    if t.symbol.exists(_.isInstanceOf[ErrorSymbol]) then return
    
    t match
    case t @ AnySel(lhs: Resolvable, id) =>
      log(s"Resolving symbol for ${t}, defn = ${lhs.defn}")
      lhs.typeDefn match
        case S(mdef @ ModuleDef(kind = Mod)) => mdef.body.members.get(id.name) match
          case S(sym) =>
            t match
              case t: Term.Sel => t.sym = S(sym)
              case t: Term.SynthSel => t.sym = S(sym)
            log(s"Resolved symbol for ${t}: ${sym}")
          case N => raise: 
            ErrorReport(
              msg"${mdef.kind.desc.capitalize} '${mdef.sym.nme}' " +
              msg"does not contain member '${id.name}'" -> t.toLoc :: Nil)
        case _ =>
    case _ =>
    
    t match
    case t @ Apps(base: Resolvable, pss) =>
      base.termDefn match
        case S(lhsDefn) if lhsDefn.params.length == pss.length + t.iargsLs.map(_.length).getOrElse(0) =>
          log(s"Resolving symbol for ${t}: defn = ${lhsDefn}")
          val sym = lhsDefn.modulefulness.msym
          t match
            case t: Term.Sel => sym.map(sym => t.sym = S(sym))
            case t: Term.SynthSel => sym.map(sym => t.sym = S(sym))
            case t: Term.App => sym.map(sym => t.sym = S(sym))
            case t: Term.TyApp => sym.map(sym => t.sym = S(sym))
            case t: Term.Ref => sym.map(sym => t.resSym = S(sym))
          log(s"Resolved symbol for ${t}: ${lhsDefn.sym}")
        case _ =>
    case _ =>
    
    t match
    // If a reference was not resolved to take implicit arguments or
    // return some module type, then its result symbol is the same as
    // the symbol it refers to.
    case t: Term.Ref if t.resSym.isEmpty =>
      t.resSym = S(t.sym)
    // If a type application was not resolved to take implicit
    // arguments, then its result symbol is the same as the symbol of its
    // LHS.
    case t: Term.TyApp if t.sym.isEmpty =>
      t.sym = t.lhs.resolvedSymbol
    case _ =>
  
  def resolveArg(p: Param)(lhs: Term)(using ictx: ICtx): Elem =
    log(s"Resolving implicit argument, expecting a ${p.sign}")
    p.sign match
      case S(sign) => resolveType(sign) match
        case S(tpe: Type.Concrete) =>
          ictx.get(tpe) match
            case S(i) =>
              log(s"Resolved ${p.sign} with instance ${i}")
              val ref = i.sym.ref()
              traverse(ref,
                // note: we accept regular arguments for module parameters
                expect = if p.modulefulness.isModuleful
                  then Any
                  else NonModule(S(msg"Module argument passed to a non-module parameter.")),
              )
              Fld(p.flags, ref, N)
            case N =>
              raise(ErrorReport(
                msg"Missing instance for contextual parameter of type `${tpe.show}` in this call" -> lhs.toLoc ::
                msg"Required by contextual parameter declaration: " -> p.toLoc ::
                msg"Expected: ${tpe.show}; Available: ${ictx.showEnv}" -> N :: Nil))
              Fld(FldFlags.empty, Term.Error, N)
        case N =>
          // There is an error during resolving the type signature.
          // The error should have been reported.
          Fld(FldFlags.empty, Term.Error, N)
      case N =>
        // By the syntax of contextual parameter, 
        // the type signature should be present.
        lastWords(s"No type signature for contextual parameter ${p.showDbg} at ${p.toLoc}")
  
  def resolveParam(p: Param)(using ictx: ICtx): Unit =
    log(s"Resolving parameter ${p.showDbg}")
    if p.modulefulness.modified then
      if p.sign.isEmpty then
        raise(ErrorReport(msg"Module parameter must have explicit type." -> p.sym.toLoc :: Nil))
    p.sign.foreach:
      traverse(_, 
        expect = if p.modulefulness.modified
          then Module(S(msg"Module parameter must have a module type."))
          else NonModule(S(msg"Non-module parameter must have a non-module type.")),
      )
  
  def resolveType(t: Term): Opt[ICtx.Type.Concrete] = t match
      // If the term is a type application, e.g., T[A, ...], resolve the
      // type constructor and arguments respectively.
      case Term.TyApp(con, args) => 
        (resolveType(con), args.map(resolveType(_)).sequence) match
          case (S(sym: ICtx.Type.Sym), S(typeArgs)) =>
            S(ICtx.Type.App(sym, typeArgs))
          case _ =>
            // Either the type constructor or the arguments is not
            // resolved. The error should have been reported.
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
          // A TypeAliasSymbol is a type alias that require further
          // resolution.
          case S(tpe: TypeAliasSymbol) =>
            tpe.defn match
              case S(tpe) => 
                tpe.rhs.flatMap(resolveType(_))
              case N => 
                // No definition for the type alias. There must be an
                // error reported on elaborating the type alias.
                N
          case N =>
            raise(ErrorReport(msg"Expected a type, got ${t.describe}" -> t.toLoc :: Nil))
            N
        case N =>
          raise(ErrorReport(msg"Expected a type symbol, got ${t.describe}" -> t.toLoc :: Nil))
          N

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
  
  /** Checks the term's modulefulness. */
  def evalsToModule(t: Term): Bool =
    def checkDecl(decl: Declaration): Bool = decl match
      /* Type Declaration / Defintiions */
      // A type is not moduleful if it is not a module. (obvious!)
      case ModuleDef(kind = Mod) => true
      // Objects use ModuleDef but is not moduleful.
      case _: TypeLikeDef => false
      
      /* Term Declarationis / Definitions */
      case defn: TermDefinition => defn.modulefulness.isModuleful
      case defn: Param => defn.modulefulness.isModuleful
      // A type param is not a module because it is a type.
      case defn: TyParam => false
    
    def checkSym(sym: Symbol): Bool = sym match
      case sym if sym.isModule => true
      case sym: (BuiltinSymbol | TopLevelSymbol) => false
      case sym: BlockLocalSymbol => sym.decl.exists(checkDecl)
      case sym: MemberSymbol[?] => sym.defn.exists(checkDecl)
      case sym => lastWords(s"unsupported symbol type ${sym}")
    
    t match
      case Term.Blk(_, res) => evalsToModule(res)
      case Term.IfLike(`if`, split) => split.results.exists(evalsToModule(_))
      case t => t.resolvedSymbol.exists(checkSym)

extension [T](xs: Ls[Opt[T]])
  def sequence: Opt[Ls[T]] =
    xs.foldRight(S(Nil): Opt[Ls[T]]): (x, acc) => 
      for 
        x <- x
        acc <- acc
      yield x :: acc
