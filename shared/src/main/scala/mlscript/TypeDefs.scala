package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

class TypeDefs extends NuTypeDefs { Typer: Typer =>
  import TypeProvenance.{apply => tp}
  
  
  trait AnyTypeDef {
    // val kind: TypeDefKind
    // val nme: TypeName
    // val tparamsargs: List[(TypeName, TypeVariable)]
  }
  
  /**
   * TypeDef holds information about declarations like classes, interfaces, and type aliases
   *
   * @param kind tells if it's a class, interface or alias
   * @param nme name of the defined type
   * @param tparamsargs list of type parameter names and their corresponding type variable names used in the definition of the type
   * @param tvars
   * @param bodyTy type of the body, this means the fields of a class or interface or the type that is being aliased
   * @param mthDecls method type declarations in a class or interface, not relevant for type alias
   * @param mthDefs method definitions in a class or interface, not relevant for type alias
   * @param baseClasses base class if the class or interface inherits from any
   * @param toLoc source location related information
   * @param positionals positional term parameters of the class
   * @param adtData maps a class to its ADT by name
   */
  case class TypeDef(
    kind: TypeDefKind,
    nme: TypeName,
    tparamsargs: List[(TypeName, TypeVariable)],
    bodyTy: SimpleType,
    mthDecls: List[MethodDef[Right[Term, Type]]],
    mthDefs: List[MethodDef[Left[Term, Type]]],
    baseClasses: Set[TypeName],
    toLoc: Opt[Loc],
    positionals: Ls[Str],
    adtData: Opt[AdtInfo] = N,
  ) {
    def allBaseClasses(ctx: Ctx)(implicit traversed: Set[TypeName]): Set[TypeName] =
      baseClasses.map(v => TypeName(v.name)) ++
        baseClasses.iterator.filterNot(traversed).flatMap(v =>
          ctx.tyDefs.get(v.name).fold(Set.empty[TypeName])(_.allBaseClasses(ctx)(traversed + v)))
    val (tparams: List[TypeName], targs: List[TypeVariable]) = tparamsargs.unzip
    // * This is lazy so that the variable is not created if the type doesn't end up being processed,
    // * which may happen if it is ill-formed.
    lazy val thisTv: TypeVariable = freshVar(noProv, N, S("this"), Nil, TypeRef(nme, targs)(noProv) :: Nil)(1) // FIXME coudl N here result in divergence? cf. absence of shadow
    var tvarVariances: Opt[VarianceStore] = N
    def getVariancesOrDefault: collection.Map[TV, VarianceInfo] =
      tvarVariances.getOrElse(Map.empty[TV, VarianceInfo].withDefaultValue(VarianceInfo.in))
  }
  
  /** Represent a set of methods belonging to some owner type.
    * This includes explicitly declared/defined as well as inherited methods. */
  private case class MethodSet(
    ownerType: TypeName,
    parents: List[MethodSet],
    decls: Map[Str, MethodType],
    defns: Map[Str, MethodType],
  ) {
    private def &(that: MethodSet)(tn: TypeName, overridden: Set[Str])(implicit raise: Raise): MethodSet =
      MethodSet(
        tn,
        this.parents ::: that.parents,
        mergeMap(this.decls, that.decls)(_ & _),
        (this.defns.iterator ++ that.defns.iterator).toSeq.groupMap(_._1)(_._2).flatMap {
          case _ -> Nil => die
          case mn -> (defn :: Nil) => S(mn -> defn)
          case mn -> defns if overridden(mn) => N  // ignore an inherited method definition if it's overridden
          case mn -> defns =>
            err(msg"An overriding method definition must be given when inheriting from multiple method definitions" -> tn.toLoc
              :: msg"Definitions of method $mn inherited from:" -> N
              :: defns.iterator.map(mt => msg"• ${mt.parents.head}" -> mt.prov.loco).toList)
            S(mn -> MethodType(defns.head.level, N, tn :: Nil, isInherited = false)(
              TypeProvenance(tn.toLoc, "inherited method declaration")))
        }
      )
    /** Returns a `MethodSet` of the _inherited_ methods only,
      *   disregarding the current MethodSet's methods... 
      * Useful for subsumption checking
      *   as inherited and current methods should be considered separately 
      * An overriding definition is required when multiple method definitions are inherited.
      *   An error is raised if no overriding definition is given. */
    def processInheritedMethods(implicit ctx: Ctx, raise: Raise): MethodSet =
      processInheritedMethodsHelper(includeCurrentMethods = false)
    private def processInheritedMethodsHelper(includeCurrentMethods: Bool)
        (implicit ctx: Ctx, raise: Raise): MethodSet = {
      def addParent(mt: MethodSet): MethodSet = {
        val td = ctx.tyDefs(ownerType.name)
        def addThis(mt: MethodType): MethodType =
          mt.copy(body = mt.body.map(b => b.copy(_1 = td.thisTv)))(mt.prov)
        def add(mt: MethodType): MethodType =
          mt.copy(parents = ownerType :: mt.parents)(mt.prov)
        mt.copy(decls = mt.decls.view.mapValues(addThis).mapValues(add).toMap, defns = mt.defns.view.mapValues(addThis).toMap)
      }
      parents.map(_.processInheritedMethodsHelper(true))
        .reduceOption(_.&(_)(ownerType, defns.keySet)).map(addParent)
        .foldRight(if (includeCurrentMethods) this else copy(decls = Map.empty, defns = Map.empty)) {
          (mds1, mds2) =>
            mds2.copy(decls = mds1.decls ++ mds2.decls, defns = mds1.defns ++ mds2.defns)
        }
    }
  }
  
  def tparamField(clsNme: TypeName, tparamNme: TypeName, visible: Bool): Var =
    Var(tparamField(clsNme.name, tparamNme.name, visible))

  def tparamField(clsNme: String, tparamNme: String, visible: Bool): String =
    if (!visible) clsNme + "#" + tparamNme else tparamNme
  
  def clsNameToNomTag(td: NuTypeDef)(prov: TypeProvenance, ctx: Ctx): ClassTag = {
    require((td.kind is Cls) || (td.kind is Mod), td.kind)
    ClassTag(Var(td.nme.name),
        if(newDefs && td.nme.name =/= "Object")
          Set.single(TN("Object"))
            | ctx.tyDefs2.get(td.nme.name).map(_.inheritedTags).getOrElse(Set.empty)
        else ctx.allBaseClassesOf(td.nme.name)
      )(prov)
  }
  def clsNameToNomTag(td: TypeDef)(prov: TypeProvenance, ctx: Ctx): ClassTag = {
    require((td.kind is Cls) || (td.kind is Mod), td.kind)
    ClassTag(Var(td.nme.name), ctx.allBaseClassesOf(td.nme.name))(prov)
  }
  def trtNameToNomTag(td: TypeDef)(prov: TypeProvenance, ctx: Ctx): TraitTag = {
    require(td.kind is Trt)
    TraitTag(Var(td.nme.name), Set.empty)(prov)
  }
  def trtNameToNomTag(td: NuTypeDef)(prov: TypeProvenance, ctx: Ctx): TraitTag = {
    require(td.kind is Trt)
    TraitTag(Var(td.nme.name), ctx.tyDefs2.get(td.nme.name).map(_.inheritedTags).getOrElse(Set.empty))(prov)
  }
  
  def baseClassesOf(tyd: mlscript.TypeDef): Set[TypeName] =
    if (tyd.kind === Als) Set.empty else baseClassesOf(tyd.body)
  
  private def baseClassesOf(ty: Type): Set[TypeName] = ty match {
      case Inter(l, r) => baseClassesOf(l) ++ baseClassesOf(r)
      case TypeName(nme) => Set.single(TypeName(nme))
      case AppliedType(b, _) => baseClassesOf(b)
      case Record(_) => Set.empty
      case _: Union => Set.empty
      case _ => Set.empty // TODO TupleType?
    }
  
  
  
  /** Only supports getting the fields of a valid base class type.
   * Notably, does not traverse type variables. 
   * Note: this does not retrieve the positional fields implicitly defined by tuples */
  def fieldsOf(ty: SimpleType, paramTags: Bool)(implicit ctx: Ctx): Map[Var, FieldType] =
  // trace(s"Fields of $ty {${travsersed.mkString(",")}}")
  {
    ty match {
      case tr @ TypeRef(td, targs) =>
        fieldsOf(tr.expandWith(paramTags, selfTy = false), paramTags)
      case ComposedType(false, l, r) =>
        mergeMap(fieldsOf(l, paramTags), fieldsOf(r, paramTags))(_ && _)
      case RecordType(fs) => fs.toMap
      case p: ProxyType => fieldsOf(p.underlying, paramTags)
      case Without(base, ns) => fieldsOf(base, paramTags).filter(ns contains _._1)
      case TypeBounds(lb, ub) => fieldsOf(ub, paramTags)
      case _: TypeTag | _: FunctionType | _: ArrayBase | _: TypeVariable
        | _: NegType | _: ExtrType | _: ComposedType | _: SpliceType
        | _: ConstrainedType | _: PolymorphicType | _: Overload
        => Map.empty
    }
  }
  // ()
  
  def processTypeDefs(newDefs0: List[mlscript.TypeDef])(implicit ctx: Ctx, raise: Raise): Ctx = {
    var allDefs = ctx.tyDefs
    val allEnv = ctx.env.clone
    val allMthEnv = ctx.mthEnv.clone
    val newDefsInfo = newDefs0.iterator.map { case td => td.nme.name -> (td.kind, td.tparams.size) }.toMap
    val newDefs = newDefs0.flatMap { td0 =>
      val n = td0.nme.name.capitalize
      val td = if (td0.nme.name.isCapitalized) td0
      else {
        err(msg"Type names must start with a capital letter", td0.nme.toLoc)
        td0.copy(nme = td0.nme.copy(n).withLocOf(td0.nme)).withLocOf(td0)
      }
      if (reservedTypeNames.contains(n)) {
        err(msg"Type name '$n' is reserved.", td.nme.toLoc)
      }
      td.tparams.groupBy(_.name).foreach { case s -> tps if tps.sizeIs > 1 => err(
          msg"Multiple declarations of type parameter ${s} in ${td.kind.str} definition" -> td.toLoc
            :: tps.map(tp => msg"Declared at" -> tp.toLoc))
        case _ =>
      }
      allDefs.get(n) match {
        case S(other) =>
          err(msg"Type '$n' is already defined.", td.nme.toLoc)
          N
        case N =>
          val dummyTargs = td.tparams.map(p =>
            freshVar(originProv(p.toLoc, s"${td.kind.str} type parameter", p.name), N, S(p.name))(ctx.lvl + 1))
          val tparamsargs = td.tparams.lazyZip(dummyTargs)
          val bodyTy =
            typePolyType(td.body, simplify = false)(ctx, raise, tparamsargs.map(_.name -> _).toMap, newDefsInfo)
          val td1 = TypeDef(td.kind, td.nme, tparamsargs.toList, bodyTy,
            td.mthDecls, td.mthDefs, baseClassesOf(td), td.toLoc, td.positionals.map(_.name), td.adtInfo)
          allDefs += n -> td1
          S(td1)
      }
    }
    import ctx.{tyDefs => oldDefs}
    /* Type the bodies of type definitions, ensuring the correctness of parent types
     * and the regularity of the definitions, then register the constructors and types in the context. */
    def typeTypeDefs(implicit ctx: Ctx): Ctx =
      ctx.copy(tyDefs = oldDefs ++ newDefs.flatMap { td =>
        implicit val prov: TypeProvenance = tp(td.toLoc, "type definition")
        val n = td.nme
        def gatherMthNames(td: TypeDef): (Set[Var], Set[Var]) =
          td.baseClasses.iterator.flatMap(bn => ctx.tyDefs.get(bn.name)).map(gatherMthNames(_)).fold(
            (td.mthDecls.iterator.map(md => md.nme.copy().withLocOf(md)).toSet,
            td.mthDefs.iterator.map(md => md.nme.copy().withLocOf(md)).toSet)
          ) { case ((decls1, defns1), (decls2, defns2)) => (
            (decls1.toSeq ++ decls2.toSeq).groupBy(identity).map { case (mn, mns) =>
              if (mns.sizeIs > 1) Var(mn.name).withLoc(td.toLoc) else mn }.toSet,
            defns1 ++ defns2
          )}
        def checkCycle(ty: SimpleType)(implicit travsersed: Set[TypeName \/ TV]): Bool =
            // trace(s"Cycle? $ty {${travsersed.mkString(",")}}") {
            ty match {
          case TypeRef(tn, _) if travsersed(L(tn)) =>
            err(msg"illegal cycle involving type ${tn}", prov.loco)
            false
          case tr @ TypeRef(tn, targs) => checkCycle(tr.expand)(travsersed + L(tn))
          case ComposedType(_, l, r) => checkCycle(l) && checkCycle(r)
          case NegType(u) => checkCycle(u)
          case p: ProxyType => checkCycle(p.underlying)
          case Without(base, _) => checkCycle(base)
          case TypeBounds(lb, ub) => checkCycle(lb) && checkCycle(ub)
          case tv: TypeVariable => travsersed(R(tv)) || {
            val t2 = travsersed + R(tv)
            tv.assignedTo match {
              case S(ty) =>
                checkCycle(ty)(t2)
              case N =>
                tv.lowerBounds.forall(checkCycle(_)(t2)) && tv.upperBounds.forall(checkCycle(_)(t2))
            }
          }
          case PolymorphicType(_, body) => checkCycle(body)
          case Overload(alts) => alts.forall(checkCycle)
          case ConstrainedType(cs, bod) =>
            cs.forall(lu => checkCycle(lu._1) && checkCycle(lu._2)) && checkCycle(bod)
          case _: ExtrType | _: TypeTag | _: FunctionType | _: RecordType | _: ArrayBase | _: SpliceType => true
        }
        // }()
        val rightParents = td.kind match {
          case Als => checkCycle(td.bodyTy)(Set.single(L(td.nme)))
          case Mod =>
            err(msg"modules cannot inherit from other types", prov.loco)
            false
          case k: ObjDefKind =>
            val parentsClasses = MutSet.empty[TypeRef]
            def checkParents(ty: SimpleType): Bool = ty match {
              // case ClassTag(Var("string"), _) => true // Q: always?
              case _: TypeTag => true // Q: always? // FIXME actually no
              case tr @ TypeRef(tn2, _) =>
                val td2 = ctx.tyDefs(tn2.name)
                td2.kind match {
                  case Cls =>
                    if (td.kind is Cls) {
                      parentsClasses.isEmpty || {
                        err(msg"${td.kind.str} $n cannot inherit from class ${tn2
                            } as it already inherits from class ${parentsClasses.head.defn}",
                          prov.loco)
                        false
                      } tap (_ => parentsClasses += tr)
                    } else
                      checkParents(tr.expand)
                  case Trt => checkParents(tr.expand)
                  case Mod =>
                    err(msg"cannot inherit from a module", prov.loco)
                    false
                  case Als => 
                    err(msg"cannot inherit from a type alias", prov.loco)
                    false
                  case Mxn =>
                    err(msg"cannot inherit from a mixin", prov.loco)
                    false
                }
              case ComposedType(false, l, r) => checkParents(l) && checkParents(r)
              case ComposedType(true, l, r) =>
                err(msg"cannot inherit from a type union", prov.loco)
                false
              case tv: TypeVariable =>
                err(msg"cannot inherit from a type variable", prov.loco)
                false
              case _: FunctionType | _: Overload =>
                err(msg"cannot inherit from a function type", prov.loco)
                false
              case _: NegType =>
                err(msg"cannot inherit from a type negation", prov.loco)
                false
              case _: TupleType =>
                err(msg"cannot inherit from a tuple type", prov.loco)
                false
              case _: ArrayType => 
                err(msg"cannot inherit from a array type", prov.loco)
                false
              case _: SpliceType =>
                err(msg"cannot inherit from a splice type", prov.loco)
                false
              case _: Without =>
                err(msg"cannot inherit from a field removal type", prov.loco)
                false
              case _: TypeBounds =>
                err(msg"cannot inherit from type bounds", prov.loco)
                false
              case _: PolymorphicType =>
                err(msg"cannot inherit from a polymorphic type", prov.loco)
                false
              case _: ConstrainedType =>
                err(msg"cannot inherit from a constrained type", prov.loco)
                false
              case _: RecordType | _: ExtrType => true
              case p: ProxyType => checkParents(p.underlying)
            }
            lazy val checkAbstractAddCtors = {
              val (decls, defns) = gatherMthNames(td)
              val isTraitWithMethods = (k is Trt) && defns.nonEmpty
              val fields = fieldsOf(td.bodyTy, true)
              fields.foreach {
                // * Make sure the LB/UB of all inherited type args are consistent.
                // * This is not actually necessary for soundness
                // *  (if they aren't, the object type just won't be instantiable),
                // *  but will help report inheritance errors earlier (see test BadInherit2).
                case (nme, FieldType(S(lb), ub)) => constrain(lb, ub)
                case _ => ()
              }
              (decls -- defns) match {
                case absMths if absMths.nonEmpty || isTraitWithMethods =>
                  if (ctx.get(n.name).isEmpty) // The class may already be defined in an erroneous program
                    ctx += n.name -> AbstractConstructor(absMths, isTraitWithMethods)
                case _ =>
                  val fields = fieldsOf(td.bodyTy, paramTags = true)
                  val tparamTags = td.tparamsargs.map { case (tp, tv) =>
                    // `false` means using `C#A` (old type member names)
                    tparamField(td.nme, tp, false) -> FieldType(Some(tv), tv)(tv.prov) }
                  val ctor = k match {
                    case Cls =>
                      val nomTag = clsNameToNomTag(td)(originProv(td.nme.toLoc, "class", td.nme.name), ctx)
                      val fieldsRefined = fields.iterator.map(f =>
                        if (f._1.name.isCapitalized) f
                        else {
                          val fv = freshVar(noProv, N,
                            S(f._1.name.drop(f._1.name.indexOf('#') + 1)) // strip any "...#" prefix
                          )(1).tap(_.upperBounds ::= f._2.ub)
                          f._1 -> (
                            if (f._2.lb.isDefined) FieldType(Some(fv), fv)(f._2.prov)
                            else fv.toUpper(f._2.prov)
                          )
                        }).toList
                      PolymorphicType(MinLevel, FunctionType(
                        singleTup(RecordType.mk(fieldsRefined.filterNot(_._1.name.isCapitalized))(noProv)),
                        nomTag & RecordType.mk(
                          fieldsRefined ::: tparamTags
                        )(noProv)
                        // * TODO try later:
                        // TypeRef(td.nme, td.tparamsargs.unzip._2)(noProv) & RecordType.mk(fieldsRefined)(noProv)
                      )(originProv(td.nme.toLoc, "class constructor", td.nme.name)))
                    case Trt =>
                      val nomTag = trtNameToNomTag(td)(originProv(td.nme.toLoc, "trait", td.nme.name), ctx)
                      val tv = freshVar(noProv, N)(1)
                      tv.upperBounds ::= td.bodyTy
                      PolymorphicType(MinLevel, FunctionType(
                        singleTup(tv), tv & nomTag & RecordType.mk(tparamTags)(noProv)
                      )(originProv(td.nme.toLoc, "trait constructor", td.nme.name)))
                    case _ => ??? // TODO
                  }
                  ctx += n.name -> VarSymbol(ctor, Var(n.name))
              }
              true
            }
            checkParents(td.bodyTy) && checkCycle(td.bodyTy)(Set.single(L(td.nme))) && checkAbstractAddCtors
          case _ => ??? // TODO
        }
        def checkRegular(ty: SimpleType)(implicit reached: Map[Str, Ls[SimpleType]]): Bool = ty match {
          case tr @ TypeRef(defn, targs) => reached.get(defn.name) match {
            case None => checkRegular(tr.expandWith(false, selfTy = false))(reached + (defn.name -> targs))
            case Some(tys) =>
              // Note: this check *has* to be relatively syntactic because
              //    the termination of constraint solving relies on recursive type occurrences
              //    obtained from unrolling a recursive type to be *equal* to the original type
              //    and to have the same has hashCode (see: the use of a cache MutSet)
              if (defn === td.nme && tys =/= targs) {
                err(msg"Type definition is not regular: it occurs within itself as ${
                  expandType(tr).show(Typer.newDefs)
                }, but is defined as ${
                  expandType(TypeRef(defn, td.targs)(noProv)).show(Typer.newDefs)
                }", td.toLoc)(raise)
                false
              } else true
          }
          case _ => ty.children(includeBounds = false).forall(checkRegular)
        }
        // Note: this will end up going through some types several times... We could make sure to
        //    only go through each type once, but the error messages would be worse.
        if (rightParents && (irregularTypes || checkRegular(td.bodyTy)(Map(n.name -> td.targs))))
          td.nme.name -> td :: Nil
        else Nil
      })
    def typeMethods(implicit ctx: Ctx): Ctx = {
      /* Perform subsumption checking on method declarations and definitions by rigidifying class type variables,
       * then register the method signatures in the context */
      def checkSubsume(td: TypeDef, mds: MethodSet): Unit = {
        val tn = td.nme
        val MethodSet(_, _, decls, defns) = mds
        val MethodSet(_, _, declsInherited, defnsInherited) = mds.processInheritedMethods
        val rigidtargs = {
          implicit val state: MutMap[TV, ST] = MutMap.empty
          td.targs.map(freshenAbove(ctx.lvl, _, true))
        }
        val targsMap = td.targs.lazyZip(rigidtargs).toMap[SimpleType, SimpleType]
        def ss(mt: MethodType, bmt: MethodType)(implicit prov: TypeProvenance) = {
          // implicit val ec: Opt[ExtrCtx] = N
          constrain(subst(mt.bodyPT, targsMap).instantiate, subst(bmt.bodyPT, targsMap).rigidify)
        }
        def registerImplicitSignatures(mn: Str, mthTy: MethodType) = ctx.getMth(N, mn) match {
          // If the currently registered method belongs to one of the base classes of this class,
          // then we don't need to do anything.
          // This is because implicit method calls always default to the parent methods.
          case S(MethodType(_, _, parents, _)) if {
            val bcs = ctx.allBaseClassesOf(tn.name)
            parents.forall(prt => bcs(TypeName(prt.name)))
          } =>
          // If this class is one of the base classes of the parent(s) of the currently registered method,
          // then we need to register the new method. Only happens when the class definitions are "out-of-order",
          // and can disambiguate implicit calls previously marked as ambiguous.
          // Example:
            // class B: A
            //   method F: 0
            // class C: A
            //   method F: 42
            // class A
            //   method F: int
          case S(MethodType(_, _, parents, _)) if {
            val v = TypeName(tn.name)
            parents.forall(prt => ctx.allBaseClassesOf(prt.name).contains(v)) 
          } => ctx.addMth(N, mn, mthTy)
          // If this class is unrelated to the parent(s) of the currently registered method,
          //  then we mark it as ambiguous:
          case S(mt2) =>
            // Create an ambiguous method "placeholder" (i.e., it has no `body`)
            val ambiguousMth =
              MethodType(0, N, (mt2.parents ::: mthTy.parents).distinct, isInherited = false)(mt2.prov)
            ctx.addMth(N, mn, ambiguousMth)
          case N => ctx.addMth(N, mn, mthTy)
        }
        def overrideError(mn: Str, mt: MethodType, mt2: MethodType) = {
          mt2.parents.foreach(parent => 
            err(msg"Overriding method ${parent}.${mn} without explicit declaration is not allowed." -> mt.prov.loco ::
              msg"Note: method definition inherited from" -> mt2.prov.loco :: Nil)(raise))
          println(s">> Checking subsumption (against inferred type) for inferred type of $mn : $mt")
        }
        declsInherited.foreach { case mn -> mt =>
          ctx.addMth(S(tn.name), mn, mt)
        }
        defnsInherited.foreach { case mn -> mt => 
          println(s">> Checking subsumption for inferred type of $mn : $mt")
          (if (decls.isDefinedAt(mn) && !defns.isDefinedAt(mn)) decls.get(mn) else N).orElse(declsInherited.get(mn))
            .foreach(ss(mt, _)(mt.prov))
          if (!declsInherited.get(mn).exists(decl => !decl.isInherited && decl.parents.last === mt.parents.last))
            ctx.addMth(S(tn.name), mn, mt)
        }
        decls.foreach { case mn -> mt =>
          println(s">> Checking subsumption for declared type of $mn : $mt")
          ((declsInherited.get(mn), defnsInherited.get(mn)) match {
            case (S(decl), S(defn)) =>
              if (!defns.isDefinedAt(mn)) defn.parents.foreach(parent => 
                err(msg"Overriding method ${parent}.${mn} without an overriding definition is not allowed." -> mt.prov.loco ::
                  msg"Note: method definition inherited from" -> defn.prov.loco :: Nil)(raise))
              S(decl)
            case (S(decl), N) => S(decl)
            case (N, S(defn)) =>
              overrideError(mn, mt, defn)
              S(defn)
            case (N, N) => N
          }).foreach(ss(mt, _)(mt.prov))
          ctx.addMth(S(tn.name), mn, mt)
          registerImplicitSignatures(mn, mt)
        }
        defns.foreach { case mn -> mt => 
          implicit val prov: TypeProvenance = mt.prov
          println(s">> Checking subsumption for inferred type of $mn : $mt")
          decls.get(mn).orElse((declsInherited.get(mn), defnsInherited.get(mn)) match {
            case (S(decl), S(defn)) if defn.parents.toSet.subsetOf(decl.parents.toSet) => S(decl)
            case (_, S(defn)) =>
              overrideError(mn, mt, defn)
              S(defn)
            case (S(decl), N) => S(decl)
            case (N, N) => N
          }).foreach(ss(mt, _))
          if (!decls.isDefinedAt(mn)) {
            // If the class declares that method explicitly,
            //   the declared signature is used so we don't have to do anything
            // If the class does not declare that method explicitly (it could be inherited),
            //   we still want to make the method available using its inferred signature
            //   both for implicit method calls and for explicit ones
            ctx.addMth(S(tn.name), mn, mt)
            registerImplicitSignatures(mn, mt)
          }
          ctx.addMthDefn(tn.name, mn, mt)
        }
      }
      
      newDefs.foreach { td => if (ctx.tyDefs.isDefinedAt(td.nme.name)) {
        /* Recursive traverse the type definition and type the bodies of method definitions 
         * by applying the targs in `TypeRef` and rigidifying class type parameters. */
        val rigidtargs = {
          implicit val state: MutMap[TV, ST] = MutMap.empty
          td.targs.map(freshenAbove(ctx.lvl, _, true))
        }
        val reverseRigid = rigidtargs.lazyZip(td.targs).toMap
        def rec(tr: TypeRef, top: Bool = false)(ctx: Ctx): MethodSet = ctx.tyDefs.get(tr.defn.name) match {
              case N =>
                err(msg"type identifier not found: ${tr.defn.name}" -> tr.prov.loco :: Nil)
                MethodSet(tr.defn, Nil, Map.empty, Map.empty)
              case S(td2) =>
          implicit val thisCtx: Ctx = ctx.nest
          val targsMap = td2.tparams.iterator.map(_.name).zip(tr.targs).toMap
          val declared = MutMap.empty[Str, Opt[Loc]]
          val defined = MutMap.empty[Str, Opt[Loc]]
          
          def filterTR(ty: SimpleType): List[TypeRef] = ty match {
            case ProxyType(und) => filterTR(und)
            case tr: TypeRef => tr :: Nil
            case ComposedType(false, l, r) => filterTR(l) ::: filterTR(r)
            case _ => Nil
          }
          def go(md: MethodDef[_ <: Term \/ Type]): (Str, MethodType) = {
            val thisTag = TraitTag(Var("this"), Set.empty)(noProv) // or Skolem?!
            // val thisTag = SkolemTag(thisCtx.lvl/*TODO correct?*/, Var("this"))(noProv)
            val thisTy = thisTag & tr
            thisCtx += "this" -> VarSymbol(thisTy, Var("this"))
            val MethodDef(rec, prt, nme, tparams, rhs) = md
            val prov: TypeProvenance = tp(md.toLoc,
              (if (!top) "inherited " else "")
              + "method " + rhs.fold(_ => "definition", _ => "declaration"))
            val fullName = s"${td.nme.name}.${nme.name}"
            if (top) {
              if (!nme.name.isCapitalized)
                err(msg"Method names must start with a capital letter", nme.toLoc)
              rhs.fold(_ => defined, _ => declared).get(nme.name) match {
                case S(loco) => err(
                  msg"Method '$fullName' is already ${rhs.fold(_ => "defined", _ => "declared")}" -> nme.toLoc ::
                  msg"at" -> loco :: Nil)
                case N =>
              }
              tparams.groupBy(_.name).foreach {
                case s -> tps if tps.sizeIs > 1 => err(
                  msg"Multiple declarations of type parameter ${s} in ${prov.desc}" -> md.toLoc ::
                  tps.map(tp => msg"Declared at" -> tp.toLoc))
                case _ =>
              }
              val tp1s = td2.tparams.iterator.map(tp => tp.name -> tp).toMap
              tparams.foreach(tp2 => tp1s.get(tp2.name) match {
                case S(tp1) => warn(
                  msg"Method type parameter ${tp1}" -> tp1.toLoc ::
                  msg"shadows class type parameter ${tp2}" -> tp2.toLoc :: Nil)
                case N =>
              })
            }
            rhs.fold(_ => defined, _ => declared) += nme.name -> nme.toLoc
            val dummyTargs2 = tparams.map(p =>
              TraitTag(Var(p.name), Set.empty)(originProv(p.toLoc, "method type parameter", p.name))) // FIXME or Skolem?!
            val targsMap2 = targsMap ++ tparams.iterator.map(_.name).zip(dummyTargs2).toMap
            val reverseRigid2 = reverseRigid ++ dummyTargs2.map(t => t ->
              freshVar(t.prov, N, S(t.id.idStr))(thisCtx.lvl + 1)) +
                (thisTag -> td.thisTv) +
                (td.thisTv -> td.thisTv) // needed to prevent the type variable from being refreshed during substitution!
            val bodyTy: PolymorphicType = subst(rhs.fold(term =>
              ctx.getMthDefn(prt.name, nme.name)
                .fold(typeLetRhs(rec, nme.name, term)(thisCtx, raise, targsMap2,
                    genLambdas = !distributeForalls || generalizeCurriedFunctions)) { mt =>
                  // Now buckle-up because this is some seriously twisted stuff:
                  //    If the method is already in the environment,
                  //    it means it belongs to a previously-defined class/trait (not the one being typed),
                  //    in which case we need to perform a substitution on the corresponding method body...
                  val targsMap3 = td2.targs.lazyZip(tr.targs).toMap[ST, ST] +
                    (td2.thisTv -> td.thisTv) +
                    (td.thisTv -> td.thisTv)
                  // Subsitute parent this TVs to current this TV.
                  PolymorphicType(mt.bodyPT.level, subst(mt.bodyPT.body, targsMap3) match {
                    // Try to wnwrap one layer of prov, which would have been wrapped by `MethodType.bodyPT`,
                    // and will otherwise mask the more precise new prov that contains "inherited"
                    case ProvType(underlying) => underlying
                    case pt => pt
                  })
                },
              ty => {
                implicit val tp: TP = prov
                thisCtx.nextLevel { newCtx =>
                  PolymorphicType(ctx.lvl, typeType(ty)(newCtx, raise, targsMap2))
                }
                // ^ Note: we need to go to the next level here,
                //    which is also done automatically by `typeLetRhs` in the case above
              }), reverseRigid2)
            val mthTy = MethodType(bodyTy.level, S((td.thisTv, bodyTy.body)), td2.nme :: Nil, false)(prov)
            if (rhs.isRight || !declared.isDefinedAt(nme.name)) {
              if (top) thisCtx.addMth(S(td.nme.name), nme.name, mthTy)
              thisCtx.addMth(N, nme.name, mthTy)
            }
            nme.name -> mthTy
          }
          MethodSet(td2.nme, filterTR(tr.expand).map(rec(_)(thisCtx)),
            td2.mthDecls.iterator.map(go).toMap, td2.mthDefs.iterator.map(go).toMap)
        }
        val mds = rec(TypeRef(td.nme, rigidtargs)(tp(td.toLoc, "type definition")), true)(ctx)
        checkSubsume(td, mds)
      }}
      ctx
    }

    typeMethods(typeTypeDefs(ctx.copy(env = allEnv, mthEnv = allMthEnv, tyDefs = allDefs)))
  }
  
  /**
    * Finds the variances of all type variables in the given type definitions with the given
    * context using a fixed point computation. The algorithm starts with each type variable
    * as bivariant by default and each type defintion position as covariant and
    * then keeps updating the position variance based on the types it encounters.
    * 
    * It uses the results to update variance info in the type defintions
    *
    * @param tyDefs
    * @param ctx
    */
  def computeVariances(tyDefs: List[TypeDef], ctx: Ctx): Unit = {
    println(s"VARIANCE ANALYSIS")
    var varianceUpdated: Bool = false;
    
    /** Update variance information for all type variables belonging
      * to a type definition.
      *
      * @param ty
      *   type tree to check variance for
      * @param curVariance
      *   variance of current position where the type tree has been found
      * @param tyDef
      *   type definition which is currently being processed
      * @param visited
      *   set of type variables visited along with the variance
      *   true polarity if covariant position visit
      *   false polarity if contravariant position visit
      *   both if invariant position visit
      */
    def updateVariance(ty: SimpleType, curVariance: VarianceInfo)(implicit tyDef: TypeDef, visited: MutSet[Bool -> TypeVariable]): Unit = {
      def fieldVarianceHelper(fieldTy: FieldType): Unit = {
          fieldTy.lb.foreach(lb => updateVariance(lb, curVariance.flip))
          updateVariance(fieldTy.ub, curVariance)
      }
      
      trace(s"upd[$curVariance] $ty") { // Note: could simplify this (at some perf cost) by just using ty.childrenPol
        ty match {
          case ProxyType(underlying) => updateVariance(underlying, curVariance)
          case _: TypeTag => ()
          case ExtrType(pol) => ()
          case t: TypeVariable =>
            // update the variance information for the type variable
            val tvv = tyDef.tvarVariances.getOrElse(die)
            val oldVariance = tvv.getOrElseUpdate(t, VarianceInfo.bi)
            val newVariance = oldVariance && curVariance
            if (newVariance =/= oldVariance) {
              tvv(t) = newVariance
              println(s"UPDATE ${tyDef.nme.name}.$t from $oldVariance to $newVariance")
              varianceUpdated = true
            }
            val (visitLB, visitUB) = (
              !curVariance.isContravariant && !visited(true -> t),
              !curVariance.isCovariant && !visited(false -> t),
            )
            t.assignedTo match {
              case S(ty) =>
                if (visitLB || visitUB) {
                  visited += true -> t; visited += false -> t
                  updateVariance(ty, curVariance)
                }
              case N =>
                if (visitLB) visited += true -> t
                if (visitUB) visited += false -> t
                if (visitLB) t.lowerBounds.foreach(lb => updateVariance(lb, VarianceInfo.co))
                if (visitUB) t.upperBounds.foreach(ub => updateVariance(ub, VarianceInfo.contra))
            }
          case RecordType(fields) => fields.foreach {
            case (_ , fieldTy) => fieldVarianceHelper(fieldTy)
          }
          case NegType(negated) =>
            updateVariance(negated, curVariance.flip)
          case TypeRef(defn, targs) =>
            // it's possible that the type definition may not exist in the
            // context because it is malformed or incorrect. Do nothing in
            // such cases
            ctx.tyDefs.get(defn.name).foreach(typeRefDef => {
              // variance for all type parameters of type definitions has been preset
              // do nothing if variance for the parameter does not exist
              targs.zip(typeRefDef.tparamsargs).foreach { case (targ, (_, tvar)) =>
                typeRefDef.tvarVariances.getOrElse(die).get(tvar).foreach {
                  case in @ VarianceInfo(false, false) => updateVariance(targ, in)
                  case VarianceInfo(true, false) => updateVariance(targ, curVariance)
                  case VarianceInfo(false, true) => updateVariance(targ, curVariance.flip)
                  case VarianceInfo(true, true) => ()
                }
              }
            })
          case ComposedType(pol, lhs, rhs) =>
            updateVariance(lhs, curVariance)
            updateVariance(rhs, curVariance)
          case TypeBounds(lb, ub) =>
            updateVariance(lb, VarianceInfo.contra)
            updateVariance(ub, VarianceInfo.co)
          case ArrayType(inner) => fieldVarianceHelper(inner)
          case TupleType(fields) => fields.foreach {
              case (_ , fieldTy) => fieldVarianceHelper(fieldTy)
            }
          case SpliceType(elems) =>
            elems.foreach {
              case L(ty) => updateVariance(ty, curVariance)
              case R(fld) => fieldVarianceHelper(fld)
            }
          case FunctionType(lhs, rhs) =>
            updateVariance(lhs, curVariance.flip)
            updateVariance(rhs, curVariance)
          case Without(base, names) => updateVariance(base, curVariance.flip)
          case Overload(alts) => alts.foreach(updateVariance(_, curVariance))
          case PolymorphicType(lvl, bod) =>
            // * It seems we should want to ignore from the analysis
            // *  those type vars that are being quantified...
            // *  When the same variable occurs both as quantified and not quantified
            // *  in a type, this could make a difference
            // *  (like it used to in `analysis/Weird.mls`)
            updateVariance(bod, curVariance)
          case ConstrainedType(cs, bod) =>
            cs.foreach { lu =>
              updateVariance(lu._1, VarianceInfo.co)
              updateVariance(lu._2, VarianceInfo.contra)
            }
            updateVariance(bod, curVariance)
        }
      }()
    }
    
    // set default value for all type variables as bivariant
    // this prevents errors when printing type defintions in
    // DiffTests for type variables that are not used at all
    // and hence are not set in the variance info map
    tyDefs.foreach { t =>
      if (t.tvarVariances.isEmpty) {
        // * ^ This may not be empty if the type def was (erroneously) defined several types in the same block
        t.tvarVariances = S(MutMap.empty)
        t.tparamsargs.foreach { case (_, tvar) => t.tvarVariances.getOrElse(die).put(tvar, VarianceInfo.bi) }
      }
    }
    
    var i = 1
    do trace(s"⬤ ITERATION $i") {
      val visitedSet: MutSet[Bool -> TypeVariable] = MutSet()
      varianceUpdated = false;
      tyDefs.foreach {
        case t @ TypeDef(k, nme, _, body, mthDecls, mthDefs, _, _, _, _) =>
          trace(s"${k.str} ${nme.name}  ${
                t.tvarVariances.getOrElse(die).iterator.map(kv => s"${kv._2} ${kv._1}").mkString("  ")}") {
            updateVariance(body, VarianceInfo.co)(t, visitedSet)
            val stores = (mthDecls ++ mthDefs).foreach { mthDef => 
              val mthBody = ctx.mthEnv.getOrElse(
                Right(Some(nme.name), mthDef.nme.name),
                throw new Exception(s"Method ${mthDef.nme.name} does not exist in the context")
              ).body
              mthBody.foreach { case (_, body) => updateVariance(body, VarianceInfo.co)(t, visitedSet) }
            }
          }()
      }
      i += 1
    }() while (varianceUpdated)
    println(s"DONE")
  }
  
  type VarianceStore = MutMap[TypeVariable, VarianceInfo]
  object VarianceStore { def empty: VarianceStore = MutMap.empty }
  
}
