package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

/** A class encapsulating type inference state.
 *  It uses its own internal representation of types and type variables, using mutable data structures.
 *  Inferred SimpleType values are then turned into CompactType values for simplification.
 *  In order to turn the resulting CompactType into a mlscript.Type, we use `expandCompactType`.
 */
class Typer(var dbg: Boolean, var verbose: Bool, var explainErrors: Bool) extends ConstraintSolver with TypeSimplifier {
  
  type Raise = Diagnostic => Unit
  type Binding = Str -> TypeScheme
  type Bindings = Map[Str, TypeScheme]
  
  case class TypeDef(
    kind: TypeDefKind,
    nme: Primitive,
    tparams: List[Primitive],
    body: Type,
    mthDecls: Map[Str, MethodDef],
    mthDefs: Map[Str, MethodDef],
    baseClasses: Set[Var],
    toLoc: Opt[Loc],
  ) {
    def allBaseClasses(ctx: Ctx)(implicit traversed: Set[Var]): Set[Var] =
      baseClasses.map(v => Var(v.name.toList.mapHead(_.toLower).mkString)) ++
        baseClasses.iterator.filterNot(traversed).flatMap(v =>
          ctx.tyDefs.getOrElse(v.name, ctx.tyDefs("nothing")).allBaseClasses(ctx)(traversed + v))
  }
  case class MethodDef(
    rec: Bool,
    prt: Primitive,
    nme: Primitive,
    tparams: List[Primitive],
    rhs: Term \/ Type,
    toLoc: Opt[Loc]
  )
  
  case class Ctx(parent: Opt[Ctx], env: MutMap[Str, TypeScheme], lvl: Int, inPattern: Bool, tyDefs: Map[Str, TypeDef],
    mthDecls: Map[Str, Map[Str, PolymorphicType]], mthDefs: Map[Str, Map[Str, PolymorphicType]],
    targsMaps: MutMap[Str, MutMap[Str, Map[Str, TypeVariable]]]) {
    def +=(b: Binding): Unit = env += b
    def ++=(bs: IterableOnce[Binding]): Unit = bs.iterator.foreach(+=)
    def get(name: Str): Opt[TypeScheme] = env.get(name) orElse parent.dlof(_.get(name))(N)
    def contains(name: Str): Bool = env.contains(name) || parent.exists(_.contains(name))
    def nest: Ctx = copy(Some(this), MutMap.empty)
    def nextLevel: Ctx = copy(lvl = lvl + 1)
  }
  object Ctx {
    def init: Ctx = Ctx(
      parent = N,
      env = MutMap.from(builtinBindings),
      lvl = 0,
      inPattern = false,
      tyDefs = Map.from(builtinTypes.map(t => t.nme.name -> t)),
      mthDecls = Map.empty,
      mthDefs = Map.empty,
      targsMaps = MutMap.empty)
  }
  implicit def lvl(implicit ctx: Ctx): Int = ctx.lvl
  
  import TypeProvenance.{apply => tp}
  def ttp(trm: Term, desc: Str = ""): TypeProvenance =
    TypeProvenance(trm.toLoc, if (desc === "") trm.describe else desc)
  
  val noProv: TypeProvenance = tp(N, "expression")
  
  val TopType: ExtrType = ExtrType(false)(noProv)
  val BotType: ExtrType = ExtrType(true)(noProv)
  val UnitType: ClassTag = ClassTag(Var("unit"), Set.empty)(noProv)
  val BoolType: ClassTag = ClassTag(Var("bool"), Set.empty)(noProv)
  val TrueType: ClassTag = ClassTag(Var("true"), Set.single(Var("bool")))(noProv)
  val FalseType: ClassTag = ClassTag(Var("false"), Set.single(Var("bool")))(noProv)
  val IntType: ClassTag = ClassTag(Var("int"), Set.single(Var("number")))(noProv)
  val DecType: ClassTag = ClassTag(Var("number"), Set.empty)(noProv)
  val StrType: ClassTag = ClassTag(Var("string"), Set.empty)(noProv)
  
  val ErrTypeId: SimpleTerm = Var("error")
  
  private val primTypes =
    List("unit" -> UnitType, "bool" -> BoolType, "int" -> IntType, "number" -> DecType, "string" -> StrType,
      "anything" -> TopType, "nothing" -> BotType)
  
  val builtinTypes: Ls[TypeDef] =
    TypeDef(Cls, Primitive("int"), Nil, Top, Map.empty, Map.empty, Set.single(Var("number")), N) ::
    TypeDef(Cls, Primitive("number"), Nil, Top, Map.empty, Map.empty, Set.empty, N) ::
    TypeDef(Cls, Primitive("bool"), Nil, Top, Map.empty, Map.empty, Set.empty, N) ::
    TypeDef(Cls, Primitive("true"), Nil, Top, Map.empty, Map.empty, Set.single(Var("bool")), N) ::
    TypeDef(Cls, Primitive("false"), Nil, Top, Map.empty, Map.empty, Set.single(Var("bool")), N) ::
    TypeDef(Cls, Primitive("string"), Nil, Top, Map.empty, Map.empty, Set.empty, N) ::
    TypeDef(Als, Primitive("anything"), Nil, Top, Map.empty, Map.empty, Set.empty, N) ::
    TypeDef(Als, Primitive("nothing"), Nil, Bot, Map.empty, Map.empty, Set.empty, N) ::
    Nil
  val builtinBindings: Bindings = {
    val tv = freshVar(noProv)(1)
    import FunctionType.{ apply => fun }
    Map(
      "true" -> TrueType,
      "false" -> FalseType,
      "document" -> BotType,
      "window" -> BotType,
      "not" -> fun(BoolType, BoolType)(noProv),
      "succ" -> fun(IntType, IntType)(noProv),
      "log" -> PolymorphicType(0, fun(tv, UnitType)(noProv)),
      "discard" -> PolymorphicType(0, fun(tv, UnitType)(noProv)),
      "add" -> fun(IntType, fun(IntType, IntType)(noProv))(noProv),
      "sub" -> fun(IntType, fun(IntType, IntType)(noProv))(noProv),
      "mul" -> fun(IntType, fun(IntType, IntType)(noProv))(noProv),
      "div" -> fun(IntType, fun(IntType, IntType)(noProv))(noProv),
      "sqrt" -> fun(IntType, IntType)(noProv),
      "lt" -> fun(IntType, fun(IntType, BoolType)(noProv))(noProv),
      "le" -> fun(IntType, fun(IntType, BoolType)(noProv))(noProv),
      "gt" -> fun(IntType, fun(IntType, BoolType)(noProv))(noProv),
      "ge" -> fun(IntType, fun(IntType, BoolType)(noProv))(noProv),
      "concat" -> fun(StrType, fun(StrType, StrType)(noProv))(noProv),
      "eq" -> {
        val v = freshVar(noProv)(1)
        PolymorphicType(0, fun(v, fun(v, BoolType)(noProv))(noProv))
      },
      "ne" -> {
        val v = freshVar(noProv)(1)
        PolymorphicType(0, fun(v, fun(v, BoolType)(noProv))(noProv))
      },
      "error" -> BotType,
      "+" -> fun(IntType, fun(IntType, IntType)(noProv))(noProv),
      "<" -> fun(IntType, fun(IntType, BoolType)(noProv))(noProv),
      "id" -> {
        val v = freshVar(noProv)(1)
        PolymorphicType(0, fun(v, v)(noProv))
      },
      "if" -> {
        val v = freshVar(noProv)(1)
        PolymorphicType(0, fun(BoolType, fun(v, fun(v, v)(noProv))(noProv))(noProv))
      },
    ) ++ primTypes ++ primTypes.map(p => "" + p._1.head.toUpper + p._1.tail -> p._2) // TODO settle on naming convention...
  }
  
  def clsNameToNomTag(td: TypeDef)(prov: TypeProvenance, ctx: Ctx): SimpleType =
    ClassTag(Var(td.nme.name.head.toLower.toString + td.nme.name.tail),
      td.allBaseClasses(ctx)(Set.single(Var(td.nme.name))))(prov)
  def trtNameToNomTag(td: TypeDef)(prov: TypeProvenance, ctx: Ctx): SimpleType =
    TraitTag(Var(td.nme.name.head.toLower.toString + td.nme.name.tail))(prov)
  
  def baseClassesOf(tyd: mlscript.TypeDef): Set[Var] =
    if (tyd.kind === Als) Set.empty else baseClassesOf(tyd.body)
  
  private def baseClassesOf(ty: Type): Set[Var] = ty match {
      case Inter(l, r) => baseClassesOf(l) ++ baseClassesOf(r)
      case Primitive(nme) => Set.single(Var(nme))
      case AppliedType(b, _) => baseClassesOf(b)
      case Record(_) => Set.empty
      case _: Union => Set.empty
      case _ => Set.empty // TODO TupleType?
    }
  
  def targsMapOf(ty: Type)(implicit ctx: Ctx, raise: Raise, lookup: Option[(Str, Option[Str])] = N,
    vars: Map[Str, SimpleType] = Map.empty): Map[Str, SimpleType] = ty match {
    case Inter(l, r) => targsMapOf(l) ++ targsMapOf(r)
    case AppliedType(b, ts) => ctx.tyDefs.get(b.name).fold(Map.empty[Str, SimpleType]) {
      td => td.tparams.map(_.name).zip(ts.map(typeType(_)(ctx.nextLevel, raise, lookup, vars))).toMap
    }
    case _ => Map.empty
  }

  def processTypeDefs(newDefs0: List[mlscript.TypeDef])(implicit ctx: Ctx, raise: Raise): Ctx = {
    var allDefs = ctx.tyDefs
    var allEnv = ctx.env.clone
    var allTargsMaps = ctx.targsMaps
    val newDefs = newDefs0.map { td =>
      implicit val prov: TypeProvenance = tp(td.toLoc, "data definition")
      val n = td.nme
      allDefs.get(n.name).foreach { other =>
        err(msg"Type '$n' is already defined.", td.nme.toLoc)
      }
      if (!n.name.head.isUpper) err(
        msg"Type names must start with a capital letter", n.toLoc)
      val td1 = TypeDef(td.kind, td.nme, td.tparams, td.body, 
        td.mths.filter(_.rhs.isRight)
          .map(md => md.nme.name -> MethodDef(md.rec, md.prt, md.nme, md.tparams, md.rhs, md.toLoc)).toMap,
        td.mths.filter(_.rhs.isLeft)
          .map(md => md.nme.name -> MethodDef(md.rec, md.prt, md.nme, md.tparams, md.rhs, md.toLoc)).toMap,
        baseClassesOf(td), td.toLoc)
      allDefs += n.name -> td1
      td1
    }
    import ctx.{tyDefs => oldDefs}
    // implicit val newCtx = ctx.copy(tyDefs = newDefs)
    ctx.copy(env = allEnv, tyDefs = allDefs, targsMaps = allTargsMaps) |> { implicit ctx =>
      ctx.copy(tyDefs = oldDefs ++ newDefs.flatMap { td =>
        implicit val prov: TypeProvenance = tp(td.toLoc, "data definition")
        val n = td.nme
        val dummyTargs = td.tparams.map(p => freshVar(noProv/*TODO*/)(ctx.lvl + 1))
        allTargsMaps += n.name -> MutMap("" -> td.tparams.map(_.name).zip(dummyTargs).toMap)
        val body_ty = typeType(td.body, simplify = false)(ctx.nextLevel, raise, S((n.name, N)))
        var fields = SortedMap.empty[Var, SimpleType]
        def checkCycleComputeFields(ty: SimpleType, computeFields: Bool)
            (implicit travsersed: Set[TypeDef]): Bool =
              trace(s"Cycle? $ty {${travsersed.mkString(",")}}"){ty match {
          case _: ObjectTag => true
          case TypeRef(td, _) if travsersed(td) =>
            err(msg"illegal cycle involving type ${td.nme.name}", prov.loco)
            false
          case tr @ TypeRef(td, targs) => checkCycleComputeFields(tr.expand, computeFields)(travsersed + td)
          case ComposedType(_, l, r) => checkCycleComputeFields(l, computeFields) && checkCycleComputeFields(r, computeFields)
          case tv: TypeVariable => true
          case _: FunctionType | _: TupleType => true
          case NegType(u) => checkCycleComputeFields(u, computeFields)
          case RecordType(fs) =>
            fs.foreach(f => fields += f._1 -> (fields.getOrElse(f._1, TopType) & f._2))
            true
          case _: ExtrType => true
          case p: ProxyType => checkCycleComputeFields(p.underlying, computeFields)
          case Without(base, _) => checkCycleComputeFields(base, computeFields)
        }}()
        val rightParents = td.kind match {
          case Als => checkCycleComputeFields(body_ty, computeFields = false)(Set.single(td))
          // case k @ (Cls | Trt) =>
          case k: ObjDefKind =>
            val parentsClasses = MutSet.empty[TypeRef]
            def checkParents(ty: SimpleType): Bool = ty match {
              // case ClassTag(Var("string"), _) => true // Q: always?
              case _: ObjectTag => true // Q: always? // FIXME actually no
              case tr @ TypeRef(td2, _) =>
                td2.kind match {
                  case Cls =>
                    if (td.kind is Cls) {
                      parentsClasses.isEmpty || {
                        err(msg"${td.kind.str} $n cannot inherit from class ${tr.defn.nme
                            } as it already inherits from class ${parentsClasses.head.defn.nme}",
                          prov.loco)
                        false
                      } tap (_ => parentsClasses += tr)
                    } else checkParents(tr.expand)
                  case Trt | Als => checkParents(tr.expand)
                }
              case ComposedType(false, l, r) => checkParents(l) && checkParents(r)
              case ComposedType(true, l, r) =>
                err(msg"cannot inherit from a type union", prov.loco)
                false
              case tv: TypeVariable =>
                err(msg"cannot inherit from a type variable", prov.loco)
                false
              case _: FunctionType =>
                err(msg"cannot inherit from a function type", prov.loco)
                false
              case _: NegType =>
                err(msg"cannot inherit from a type negation", prov.loco)
                false
              case _: TupleType =>
                err(msg"cannot inherit from a tuple type", prov.loco)
                false
              case _: Without =>
                err(msg"cannot inherit from a field removal type", prov.loco)
                false
              case _: RecordType | _: ExtrType => true
              case p: ProxyType => checkParents(p.underlying)
            }
            checkParents(body_ty) &&
                checkCycleComputeFields(body_ty, computeFields = td.kind is Cls)(Set.single(td)) && {
              val ctor = k match {
                case Cls =>
                  val nomTag = clsNameToNomTag(td)(noProv/*FIXME*/, ctx)
                  val fieldsRefined = RecordType(fields.iterator.map(f => f._1 -> freshVar(noProv)(1).tap(_.upperBounds ::= f._2)).toList)(noProv)
                  PolymorphicType(0, FunctionType(fieldsRefined, nomTag & fieldsRefined)(noProv/*FIXME*/))
                case Trt =>
                  val nomTag = trtNameToNomTag(td)(noProv/*FIXME*/, ctx)
                  val tv = freshVar(noProv)(1)
                  tv.upperBounds ::= body_ty
                  PolymorphicType(0, FunctionType(tv, tv & nomTag)(noProv/*FIXME*/))
              }
              ctx += n.name -> ctor
              true
            }
        }
        def checkRegular(ty: SimpleType)(implicit reached: Map[Str, Ls[SimpleType]]): Bool = ty match {
          case tr @ TypeRef(defn, targs) => reached.get(defn.nme.name) match {
            case None => checkRegular(tr.expand)(reached + (defn.nme.name -> targs))
            case Some(tys) =>
              // TODO less syntactic check...
              if (tys =/= targs) {
                if (defn.nme.name === td.nme.name)
                  err(msg"Type definition is not regular: it occurs within itself as ${
                  expandType(tr, true).show
                  }, but is defined as ${
                  expandType(TypeRef(defn, dummyTargs)(noProv, ctx), true).show
                  }", td.toLoc)(raise, noProv)
                false
              } else true
          }
          case _ => ty.children.forall(checkRegular)
        }
        // Note: this will end up going through some types several times... We could make sure to
        //    only go through each type once, but the error messages would be worse.
        if (rightParents && checkRegular(body_ty)(Map(n.name -> dummyTargs)))
          td.nme.name -> td :: Nil
        else Nil
      })
    } |> { implicit ctx =>
      val newMthDecls = MutMap.from(ctx.mthDecls)
      val newMthDefs = MutMap.from(ctx.mthDefs)
      newDefs.foreach { td =>
        implicit val prov: TypeProvenance = tp(td.toLoc, "data definition")
        val tn = td.nme
        val decls = MutMap.empty[Str, PolymorphicType]
        val defs = MutMap.empty[Str, PolymorphicType]
        td.mthDecls.valuesIterator.foreach { case MethodDef(rec, prt, nme, tparams, R(ty), loc) =>
            implicit val prov: TypeProvenance = tp(loc, "method declaration")
            val dummyTargs2 = tparams.map(p => freshVar(noProv/*TODO*/)(ctx.lvl + 2))
            allTargsMaps(tn.name) += nme.name -> tparams.map(_.name).zip(dummyTargs2).toMap
            if (!nme.name.head.isUpper)
              err(msg"Method names must start with a capital letter", loc)
            decls += nme.name -> PolymorphicType(1, typeType(ty)(ctx.nest.nextLevel, raise, S((tn.name, S(nme.name)))))
          case _ => ???
        }
        td.mthDefs.valuesIterator.foreach { case MethodDef(rec, prt, nme, tparams, L(term), loc) =>
            implicit val prov: TypeProvenance = tp(loc, "method definition")
            val dummyTargs2 = tparams.map(p => freshVar(noProv/*TODO*/)(ctx.lvl + 2))
            allTargsMaps(tn.name) += nme.name -> tparams.map(_.name).zip(dummyTargs2).toMap
            if (!nme.name.head.isUpper)
              err(msg"Method names must start with a capital letter", nme.toLoc)
            if (defs.isDefinedAt(nme.name))
              err(msg"Method '${tn}.${nme.name}' is already defined.", nme.toLoc)
            defs += nme.name -> typeLetRhs(rec, nme.name, term)(ctx.nest.nextLevel, raise, S((tn.name, S(nme.name))))
          case _ => ???
        }
        newMthDecls += tn.name -> 
          ((td.baseClasses.flatMap(t => newMthDecls.getOrElse(t.name, Map.empty))).toMap ++ decls.toMap)
        newMthDefs += tn.name ->
          ((td.baseClasses.flatMap(t => newMthDefs.getOrElse(t.name, Map.empty))).toMap ++ defs.toMap)
      }
      ctx.copy(mthDecls = newMthDecls.toMap, mthDefs = newMthDefs.toMap)
    } |> { implicit ctx =>
      val newEnv = MutMap.from(ctx.env)
      val newMthDecls = ctx.mthDecls
      val newMthDefs = ctx.mthDefs
      newDefs.foreach { td =>
        implicit val prov: TypeProvenance = tp(td.toLoc, "data definition")
        val tn = td.nme
        val decls = newMthDecls(tn.name)
        val defs = newMthDefs(tn.name)
        val targsMap = targsMapOf(td.body)(ctx, raise, S((tn.name, N)))
        val subsmap = td.baseClasses.flatMap(b => allTargsMaps.getOrElse(b.name, MutMap.empty).getOrElse("", Map.empty))
          .map { case targ -> tv => tv -> targsMap.getOrElse(targ, tv) }.toMap
        def ss(mt: TypeScheme, amt: TypeScheme)(implicit raise: Raise, prov: TypeProvenance) = amt match {
          case pt: PolymorphicType => constrain(mt.instantiate, subspt(pt, subsmap).rigidify)(raise, prov)
          case st: SimpleType => constrain(mt.instantiate, subsst(st, subsmap))(raise, prov)
        }
        def subspt(ts: PolymorphicType, map: Map[TypeVariable, SimpleType]): PolymorphicType =
          PolymorphicType(ts.level, subsst(ts.body, map))
        def subsst(ts: SimpleType, map: Map[TypeVariable, SimpleType]): SimpleType = ts match {
          case FunctionType(lhs, rhs) => FunctionType(subsst(lhs, map), subsst(rhs, map))(ts.prov)
          case RecordType(fields) => RecordType(fields.map { case fn -> ft => fn -> subsst(ft, map) })(ts.prov)
          case TupleType(fields) => TupleType(fields.map { case fn -> ft => fn -> subsst(ft, map) })(ts.prov)
          case ComposedType(pol, lhs, rhs) => ComposedType(pol, subsst(lhs, map), subsst(rhs, map))(ts.prov)
          case NegType(negated) => NegType(subsst(negated, map))(ts.prov)
          case Without(base, names) => Without(subsst(base, map), names)(ts.prov)
          case ProxyType(underlying) => ProxyType(subsst(underlying, map))(ts.prov)
          case t@TypeRef(defn, targs) => TypeRef(defn, targs.map(subsst(_, map)))(t.prov, t.ctx)
          case tv: TypeVariable => map.getOrElse(tv, tv)
          case _: ObjectTag | _: ExtrType => ts
        }
        td.mthDecls.valuesIterator.foreach { case MethodDef(rec, prt, nme, tparams, R(ty), loc) =>
            implicit val prov: TypeProvenance = tp(loc, "method declaration")
            val mt = decls(nme.name)
            td.baseClasses.foreach(bc => newMthDecls.get(bc.name).foreach(_.get(nme.name).foreach(ss(mt, _))))
          case _ => ???
        }
        td.mthDefs.valuesIterator.foreach { case MethodDef(rec, prt, nme, tparams, L(term), loc) =>
            implicit val prov: TypeProvenance = tp(loc, "method definition")
            val mt = defs(nme.name)
            newMthDecls.get(tn.name).foreach(_.get(nme.name).foreach(ss(mt, _)))
            td.baseClasses.foreach { bc => 
              if (td.mthDecls.isDefinedAt(bc.name))
                newMthDecls.get(bc.name).foreach(_.get(nme.name).foreach(ss(mt, _)))
              newMthDefs.get(bc.name).foreach(_.get(nme.name).foreach { bmt =>
                if (!newMthDecls.get(bc.name).exists(_.isDefinedAt(nme.name))) {
                  err(msg"Overiding method ${bc.name}.${nme.name} without explicit declaration is not allowed.", loc)
                  ss(mt, bmt)
                }
              })
            }
          case _ => ???
        }
        newEnv ++= defs.map{ case mn -> mt => s"${tn.name}.${mn}" -> mt } ++
          decls.map{ case mn -> mt => s"${tn.name}.${mn}" -> mt }
      }
      ctx.copy(env = newEnv, mthDecls = newMthDecls.toMap, mthDefs = newMthDefs.toMap)
    }
  }
  // TODO record provenances!
  def typeType(ty: Type, simplify: Bool = true)(implicit ctx: Ctx, raise: Raise,
    lookup: Option[(Str, Option[Str])] = N, vars: Map[Str, SimpleType] = Map.empty): SimpleType = {
    val typeType = ()
    def typeNamed(ty: Type, name: Str): Opt[TypeDef] = {
      val res = ctx.tyDefs.get(name)
      if (res.isEmpty)
        err("type identifier not found: " + name, ty.toLoc)(raise, tp(ty.toLoc, "missing type"));
      res
    }
    val allVars = vars ++ (lookup match {
      case S((tn, S(mn))) => ctx.targsMaps.get(tn).fold(Map.empty[Str, SimpleType])(_.getOrElse("", Map.empty)) ++
        ctx.targsMaps.get(tn).fold(Map.empty[Str, SimpleType])(_.getOrElse(mn, Map.empty)) 
      case S((tn, N)) => ctx.targsMaps.get(tn).fold(Map.empty[Str, SimpleType])(_.getOrElse("", Map.empty))
      case N => Map.empty
    })
    val localVars = mutable.Map.empty[TypeVar, TypeVariable]
    def rec(ty: Type)(implicit ctx: Ctx): SimpleType = ty match {
      case Top => ExtrType(false)(tp(ty.toLoc, "top type"))
      case Bot => ExtrType(true)(tp(ty.toLoc, "bottom type"))
      case Tuple(fields) => TupleType(fields.map(f => f._1 -> rec(f._2)))(tp(ty.toLoc, "tuple type"))
      case Inter(lhs, rhs) => (if (simplify) rec(lhs) & (rec(rhs), _: TypeProvenance)
          else ComposedType(false, rec(lhs), rec(rhs)) _
        )(tp(ty.toLoc, "intersection type"))
      case Union(lhs, rhs) => (if (simplify) rec(lhs) | (rec(rhs), _: TypeProvenance)
          else ComposedType(true, rec(lhs), rec(rhs)) _
        )(tp(ty.toLoc, "union type"))
      case Neg(t) => NegType(rec(t))(tp(ty.toLoc, "type negation"))
      case Record(fs) => RecordType.mk(fs.map { nt =>
          if (nt._1.name.head.isUpper)
            err(msg"Field identifiers must start with a small letter", nt._1.toLoc)(raise, noProv)
          nt._1 -> rec(nt._2)
        })(tp(ty.toLoc, "record type"))
      case Function(lhs, rhs) => FunctionType(rec(lhs), rec(rhs))(tp(ty.toLoc, "function type"))
      case Literal(lit) => ClassTag(lit, Set.single(lit.baseClass))(tp(ty.toLoc, "literal type"))
      case Primitive(name) =>
        val tpr = tp(ty.toLoc, "type reference")
        allVars.get(name) orElse
          typeNamed(ty, name).flatMap(td =>
            if (td.tparams.nonEmpty) {
              err(msg"Type $name takes parameters", ty.toLoc)(raise, tpr)
              N
            } else S(TypeRef(td, Nil)(tpr, ctx))
          ) getOrElse freshVar(noProv) // TODO use ty's prov
      case tv: TypeVar =>
        localVars.getOrElseUpdate(tv, new TypeVariable(ctx.lvl, Nil, Nil)(tp(ty.toLoc, "type variable")))
      case AppliedType(base, targs) => typeNamed(ty, base.name) match {
        case Some(td) =>
          val tpnum = td.tparams.size
          val realTargs = if (targs.size === tpnum) targs.map(rec) else {
            err(msg"Wrong number of type arguments – expected ${tpnum.toString}, found ${targs.size.toString}",
              ty.toLoc)(raise, noProv /*FIXME*/);
            (targs.iterator.map(rec) ++ Iterator.continually(freshVar(noProv)))
              .take(tpnum).toList
          }
          TypeRef(td,
            realTargs)(tp(ty.toLoc, "applied type reference"), ctx)
        case None => freshVar(noProv) // TODO use ty's prov
      }
      case Recursive(uv, body) => ??? // TODO
      case Rem(base, fs) => Without(rec(base), fs
        .toSet)(tp(ty.toLoc, "function type")) // TODO use ty's prov
    }
    rec(ty)
  }
  
  def typePattern(pat: Term)(implicit ctx: Ctx, raise: Raise): SimpleType =
    typeTerm(pat)(ctx.copy(inPattern = true), raise)
  
  
  def typeStatement(s: DesugaredStatement, allowPure: Bool)
        (implicit ctx: Ctx, raise: Raise): PolymorphicType \/ Ls[Binding] = s match {
    case Def(isrec, nme, L(rhs)) => // TODO reject R(..)
      val ty_sch = typeLetRhs(isrec, nme, rhs)
      ctx += nme -> ty_sch
      R(nme -> ty_sch :: Nil)
    case t @ Tup(fs) if !allowPure => // Note: not sure this is still used!
      val thing = fs match {
        case (S(_), _) :: Nil => "field"
        case Nil => "empty tuple"
        case _ => "tuple"
      }
      warn(s"Useless $thing in statement position.", t.toLoc)
      L(PolymorphicType(0, typeTerm(t)))
    case t: Term =>
      val ty = typeTerm(t)
      if (!allowPure) {
        if (t.isInstanceOf[Var] || t.isInstanceOf[Lit])
          warn("Pure expression does nothing in statement position.", t.toLoc)
        else
          constrain(mkProxy(ty, TypeProvenance(t.toCoveringLoc, "expression in statement position")), UnitType)(
            raise = err => raise(Warning( // Demote constraint errors from this to warnings
              msg"Expression in statement position should have type `unit`." -> N ::
              msg"Use the `discard` function to discard non-unit values, making the intent clearer." -> N ::
              err.allMsgs)),
            prov = TypeProvenance(t.toLoc, t.describe))
      }
      L(PolymorphicType(0, ty))
    case _ =>
      err(msg"Illegal position for this ${s.describe} statement.", s.toLoc)(raise, noProv)
      R(Nil)
  }
  
  /** Infer the type of a let binding right-hand side. */
  def typeLetRhs(isrec: Boolean, nme: Str, rhs: Term)
        (implicit ctx: Ctx, raise: Raise, lookup: Option[(Str, Option[Str])] = N): PolymorphicType = {
    val res = if (isrec) {
      val e_ty = freshVar(TypeProvenance(rhs.toLoc, "let-bound value"))(lvl + 1)
      ctx += nme -> e_ty
      val ty = typeTerm(rhs)(ctx.nextLevel, raise, lookup)
      constrain(ty, e_ty)(raise, TypeProvenance(rhs.toLoc, "binding of " + rhs.describe))
      e_ty
    } else typeTerm(rhs)(ctx.nextLevel, raise, lookup)
    PolymorphicType(lvl, res)
  }
  
  def mkProxy(ty: SimpleType, prov: TypeProvenance): SimpleType = {
    ProxyType(ty)(prov)
    // TODO switch to return this in perf mode:
    // ty
  }
  
  // TODO also prevent rebinding of "not"
  val reservedNames: Set[Str] = Set("|", "&", "~", ",", "neg", "and", "or")
  
  object ValidVar {
    def unapply(v: Var)(implicit raise: Raise): S[Str] = S {
      if (reservedNames(v.name))
        err(s"Illegal use of ${if (v.name.head.isLetter) "keyword" else "operator"}: " + v.name,
          v.toLoc)(raise, ttp(v))
      v.name
    }
  }
  object ValidPatVar {
    def unapply(v: Var)(implicit ctx: Ctx, raise: Raise): Opt[Str] =
      if (ctx.inPattern && v.isPatVar) {
        ctx.parent.dlof(_.get(v.name))(N).map(_.instantiate(0).unwrapProxies) |>? {
          case S(ClassTag(Var(v.name), _)) =>
            warn(msg"Variable name '${v.name}' already names a symbol in scope. " +
              s"If you want to refer to that symbol, you can use `scope.${v.name}`; " +
              s"if not, give your future readers a break and use another name :^)", v.toLoc)
        }
        ValidVar.unapply(v)
      } else N
  }
  
  /** Infer the type of a term. */
  def typeTerm(term: Term)(implicit ctx: Ctx, raise: Raise, lookup: Option[(Str, Option[Str])] = N): SimpleType
        = trace(s"$lvl. Typing ${if (ctx.inPattern) "pattern" else "term"} $term") {
    implicit val prov: TypeProvenance = ttp(term)
    
    def con(lhs: SimpleType, rhs: SimpleType, res: SimpleType): SimpleType = {
      var alreadyReportedAnError = false
      constrain(lhs, rhs)({
        case err: TypeError if alreadyReportedAnError => () // silence further errors from this location
        case err: TypeError =>
          alreadyReportedAnError = true
          constrain(errType, res)(_ => (), noProv) // This is just to get error types leak into the result
          raise(err)
        case diag => raise(diag)
      }, prov)
      res
    }
    term match {
      case v @ Var("_") => // TODO parse this differently... or handle consistently everywhere
        freshVar(tp(v.toLoc, "wildcard"))
      case Asc(trm, ty) =>
        val trm_ty = typeTerm(trm)
        val ty_ty = typeType(ty)(ctx.copy(inPattern = false), raise, lookup)
        con(trm_ty, ty_ty, ty_ty)
        if (ctx.inPattern) trm_ty else ty_ty
      case (v @ ValidPatVar(nme)) =>
        val prov = tp(if (verboseConstraintProvenanceHints) v.toLoc else N, "variable")
        ctx.env.get(nme).map(_.instantiate) // Note: only look at ctx.env, and not the outer ones!
          .getOrElse(new TypeVariable(lvl, Nil, Nil)(prov).tap(ctx += nme -> _))
      case v @ ValidVar(name) =>
        val ty = ctx.get(name).getOrElse {
          // TODO: delay type expansion to message display and show the expected type here!
          err("identifier not found: " + name, term.toLoc)
        }.instantiate
        mkProxy(ty, prov)
        // ^ TODO maybe use a description passed in param?
        // currently we get things like "flows into variable reference"
        // but we used to get the better "flows into object receiver" or "flows into applied expression"...
      case lit: Lit => ClassTag(lit, Set.single(lit.baseClass))(prov)
      case App(Var("neg" | "~"), trm) => typeTerm(trm).neg(prov)
      case App(App(Var("|"), lhs), rhs) =>
        typeTerm(lhs) | (typeTerm(rhs), prov)
      case App(App(Var("&"), lhs), rhs) =>
        typeTerm(lhs) & (typeTerm(rhs), prov)
      case Rcd(fs) => // TODO rm: no longer used?
        RecordType.mk(fs.map { case (n, t) => 
            if (n.name.head.isUpper)
              err(msg"Field identifiers must start with a small letter", term.toLoc)(raise, noProv)
            (n, typeTerm(t))
          })(tp(term.toLoc, "record literal"))
      case tup: Tup =>
        typeTerms(tup :: Nil, false, Nil)
      case Bra(false, trm: Blk) => typeTerm(trm)
      case Bra(rcd, trm @ (_: Tup | _: Blk)) => typeTerms(trm :: Nil, rcd, Nil)
      case Bra(_, trm) => typeTerm(trm)
      case Blk((s: Term) :: Nil) => typeTerm(s)
      case Blk(Nil) => UnitType
      case pat if ctx.inPattern =>
        err(msg"Unsupported pattern shape${
          if (dbg) " ("+pat.getClass.toString+")" else ""}:", pat.toLoc)(raise, ttp(pat))
      case Lam(pat, body) =>
        val newBindings = mutable.Map.empty[Str, TypeVariable]
        val newCtx = ctx.nest
        val param_ty = typePattern(pat)(newCtx, raise)
        newCtx ++= newBindings
        val body_ty = typeTerm(body)(newCtx, raise)
        FunctionType(param_ty, body_ty)(tp(term.toLoc, "function"))
      case App(App(Var("and"), lhs), rhs) =>
        val lhs_ty = typeTerm(lhs)
        val newCtx = ctx.nest // TODO use
        val rhs_ty = typeTerm(lhs)
        ??? // TODO
      case App(f, a) =>
        val f_ty = typeTerm(f)
        val a_ty = typeTerm(a)
        val res = freshVar(prov)
        val arg_ty = mkProxy(a_ty, tp(a.toCoveringLoc, "argument"))
        val appProv = tp(f.toCoveringLoc, "applied expression")
        val fun_ty = mkProxy(f_ty, appProv)
        val resTy = con(fun_ty, FunctionType(arg_ty, res)(prov), res)
        val raw_fun_ty = fun_ty.unwrapProxies
        resTy
      case Sel(obj, name) =>
        val o_ty = typeTerm(obj)
        val res = freshVar(prov)
        val obj_ty = mkProxy(o_ty, tp(obj.toCoveringLoc, "receiver"))
        con(obj_ty, RecordType.mk((name, res) :: Nil)(prov), res)
      case Let(isrec, nme, rhs, bod) =>
        val n_ty = typeLetRhs(isrec, nme, rhs)
        val newCtx = ctx.nest
        newCtx += nme -> n_ty
        typeTerm(bod)(newCtx, raise)
      // case Blk(s :: stmts) =>
      //   val (newCtx, ty) = typeStatement(s)
      //   typeTerm(Blk(stmts))(newCtx, lvl, raise)
      case Blk(stmts) => typeTerms(stmts, false, Nil)(ctx.nest, raise, prov)
      case Bind(l, r) =>
        val l_ty = typeTerm(l)
        val newCtx = ctx.nest // so the pattern's context don't merge with the outer context!
        val r_ty = typePattern(r)(newCtx, raise)
        ctx ++= newCtx.env
        con(l_ty, r_ty, r_ty)
      case Test(l, r) =>
        val l_ty = typeTerm(l)
        val newCtx = ctx.nest
        val r_ty = typePattern(r)(newCtx, raise) // TODO make these bindings flow
        con(l_ty, r_ty, TopType)
        BoolType
      case With(t, rcd) =>
        val t_ty = typeTerm(t)
        val rcd_ty = typeTerm(rcd)
        (t_ty without rcd.fields.iterator.map(_._1).toSet) & (rcd_ty, prov)
      case CaseOf(s, cs) =>
        val s_ty = typeTerm(s)
        val (tys, cs_ty) = typeArms(s |>? {
          case v: Var => v
          case Asc(v: Var, _) => v
        }, cs)
        val req = tys.foldRight(BotType: SimpleType) {
          case ((a_ty, tv), req) => a_ty & tv | req & a_ty.neg()
        }
        con(s_ty, req, cs_ty)
    }
  }(r => s"$lvl. : ${r}")
  
  def typeArms(scrutVar: Opt[Var], arms: CaseBranches)
      (implicit ctx: Ctx, raise: Raise, lvl: Int)
      : Ls[SimpleType -> SimpleType] -> SimpleType = arms match {
    case NoCases => Nil -> BotType
    case Wildcard(b) =>
      val fv = freshVar(tp(arms.toLoc, "wildcard pattern"))
      val newCtx = ctx.nest
      scrutVar match {
        case Some(v) =>
          newCtx += v.name -> fv
          val b_ty = typeTerm(b)(newCtx, raise)
          (fv -> TopType :: Nil) -> b_ty
        case _ =>
          (fv -> TopType :: Nil) -> typeTerm(b)
      }
    case Case(pat, bod, rest) =>
      val patTy = pat match {
        case lit: Lit =>
          ClassTag(lit, Set.single(lit.baseClass))(tp(pat.toLoc, "literal pattern"))
        case Var(nme) =>
          val tpr = tp(pat.toLoc, "type pattern")
          ctx.tyDefs.get(nme) match {
            case None =>
              err("type identifier not found: " + nme, pat.toLoc)(raise, tpr)
              val e = ClassTag(ErrTypeId, Set.empty)(tpr)
              return ((e -> e) :: Nil) -> e
            case Some(td) =>
              td.kind match {
                case Als => err(msg"can only match on classes and traits", pat.toLoc)(raise, tpr)
                case Cls => clsNameToNomTag(td)(tp(pat.toLoc, "class pattern"), ctx)
                case Trt => trtNameToNomTag(td)(tp(pat.toLoc, "trait pattern"), ctx)
              }
          }
      }
      val newCtx = ctx.nest
      val (req_ty, bod_ty, (tys, rest_ty)) = scrutVar match {
        case S(v) =>
          val tv = freshVar(tp(v.toLoc, "refined scrutinee"))
          newCtx += v.name -> tv
          val bod_ty = typeTerm(bod)(newCtx, raise)
          (patTy -> tv, bod_ty, typeArms(scrutVar, rest))
        case N =>
          val bod_ty = typeTerm(bod)(newCtx, raise)
          (patTy -> TopType, bod_ty, typeArms(scrutVar, rest))
      }
      (req_ty :: tys) -> (bod_ty | rest_ty)
  }
  
  def typeTerms(term: Ls[Statement], rcd: Bool, fields: List[Opt[Var] -> SimpleType])
        (implicit ctx: Ctx, raise: Raise, prov: TypeProvenance): SimpleType
      = term match {
    case (trm @ Var(nme)) :: sts if rcd => // field punning
      typeTerms(Tup(S(trm) -> trm :: Nil) :: sts, rcd, fields)
    case Blk(sts0) :: sts1 => typeTerms(sts0 ::: sts1, rcd, fields)
    case Tup(Nil) :: sts => typeTerms(sts, rcd, fields)
    case Tup((no, trm) :: ofs) :: sts =>
      val ty = {
        trm match  {
          case Bra(false, t) if ctx.inPattern => // we use syntax `(x: (p))` to type `p` as a pattern and not a type...
            typePattern(t)
          case _ => ctx.copy(inPattern = ctx.inPattern && no.isEmpty) |> { implicit ctx => // TODO change this?
            if (ofs.isEmpty) typeTerm(Bra(rcd, trm))
            // ^ This is to type { a: ... } as { a: { ... } } to facilitate object literal definitions;
            //   not sure that's a good idea...
            else typeTerm(trm)
          }
        }
      }
      val res_ty = no |> {
        case S(nme) if ctx.inPattern =>
          // TODO in 'opaque' definitions we should give the exact specified type and not something more precise
          // as in `(x: Int) => ...` should not try to refine the type of `x` further
          
          val prov = tp(trm.toLoc, "parameter type")
          val t_ty = 
            // TODO in positive position, this should create a new VarType instead! (i.e., an existential)
            new TypeVariable(lvl, Nil, Nil)(prov)//.tap(ctx += nme -> _)
          
          // constrain(ty, t_ty)(raise, prov)
          constrain(t_ty, ty)(raise, prov)
          ctx += nme.name -> t_ty
          
          t_ty
          // ty
          // ComposedType(false, t_ty, ty)(prov)
          // ComposedType(true, t_ty, ty)(prov) // loops!
          
        case S(nme) =>
          ctx += nme.name -> ty
          ty
        case _ =>
          ty
      }
      typeTerms(Tup(ofs) :: sts, rcd, (no, res_ty) :: fields)
    case (trm: Term) :: Nil =>
      if (fields.nonEmpty)
        warn("Previous field definitions are discarded by this returned expression.", trm.toLoc)
      typeTerm(trm)
    // case (trm: Term) :: Nil =>
    //   assert(!rcd)
    //   val ty = typeTerm(trm)
    //   typeBra(Nil, rcd, (N, ty) :: fields)
    case s :: sts =>
      val (diags, desug) = s.desugared
      diags.foreach(raise)
      val newBindings = desug.flatMap(typeStatement(_, allowPure = false).toOption)
      ctx ++= newBindings.flatten
      typeTerms(sts, rcd, fields)
    case Nil =>
      if (rcd) {
        val fs = fields.reverseIterator.zipWithIndex.map {
          case ((S(n), t), i) =>
            n -> t
          case ((N, t), i) =>
            // err("Missing name for record field", t.prov.loco)
            warn("Missing name for record field", t.prov.loco)
            (Var("_" + (i + 1)), t)
        }.toList
        RecordType.mk(fs)(prov)
      } else TupleType(fields.map { case S(n) -> t => S(n) -> t case N -> t => N -> t }.reverse)(prov)
  }
  
  
  /** Convert an inferred SimpleType into the immutable Type representation. */
  def expandType(st: SimpleType, polarity: Bool): Type = {
    
    // TODO improve/simplify? (take inspiration from other impls?)
    //    see: duplication of recursive.get(st_pol) logic
    
    val recursive = mutable.Map.empty[SimpleType -> Bool, TypeVar]
    def go(st: SimpleType, polarity: Boolean)(implicit inProcess: Set[SimpleType -> Bool]): Type = {
      val st_pol = st -> polarity
      if (inProcess(st_pol)) recursive.getOrElseUpdate(st_pol, freshVar(st.prov)(0).asTypeVar)
      else (inProcess + st_pol) pipe { implicit inProcess => st match {
        case tv: TypeVariable =>
          val bounds = if (polarity) tv.lowerBounds else tv.upperBounds
          val bound =
            if (polarity) bounds.foldLeft(BotType: SimpleType)(_ | _)
            else bounds.foldLeft(TopType: SimpleType)(_ & _)
          if (inProcess(bound -> polarity))
            recursive.getOrElseUpdate(bound -> polarity, freshVar(st.prov)(0).asTypeVar)
          else {
            val boundTypes = bounds.map(go(_, polarity))
            val mrg = if (polarity) Union else Inter
            recursive.get(st_pol) match {
              case Some(variable) =>
                Recursive(variable, boundTypes.reduceOption(mrg).getOrElse(if (polarity) Bot else Top))
              case None => boundTypes.foldLeft[Type](tv.asTypeVar)(mrg)
            }
          }
        case _ =>
          val res = st match {
            case FunctionType(l, r) => Function(go(l, !polarity), go(r, polarity))
            case ComposedType(true, l, r) => Union(go(l, polarity), go(r, polarity))
            case ComposedType(false, l, r) => Inter(go(l, polarity), go(r, polarity))
            case RecordType(fs) => Record(fs.map(nt => nt._1 -> go(nt._2, polarity)))
            case TupleType(fs) => Tuple(fs.map(nt => nt._1 -> go(nt._2, polarity)))
            case NegType(t) => Neg(expandType(t, !polarity))
            case ExtrType(true) => Bot
            case ExtrType(false) => Top
            case ProxyType(und) => go(und, polarity)
            case tag: ObjectTag => tag.id match {
              case Var(n) => Primitive(n)
              case lit: Lit => Literal(lit)
            }
            case TypeRef(td, Nil) => Primitive(td.nme.name)
            case TypeRef(td, targs) =>
              AppliedType(Primitive(td.nme.name), targs.map(expandType(_, polarity)))
            case Without(base, names) => Rem(expandType(base, polarity), names.toList)
            case _: TypeVariable => die
          }
          recursive.get(st_pol) match {
            case Some(variable) =>
              Recursive(variable, res)
            case None => res
          }
      }
    }}
    
    go(st, polarity)(Set.empty)
  }
  
}
