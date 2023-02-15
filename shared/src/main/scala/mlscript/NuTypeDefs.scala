package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

class NuTypeDefs extends ConstraintSolver { self: Typer =>
  import TypeProvenance.{apply => tp}
  
  
  sealed abstract class NuDeclInfo
  
  case class FunInfo() extends NuDeclInfo
  case class TypeDefInfo() extends NuDeclInfo
  
  
  // * For now these are just unused stubs to be completed and used later
  
  sealed abstract class TypedNuDecl {
    def name: Str
    def freshen(implicit ctx: Ctx): TypedNuDecl = this match {
      case m @ TypedNuMxn(td, thisTV, superTV, ttu) =>
        implicit val freshened: MutMap[TV, ST] = MutMap.empty
        implicit val shadows: Shadows = Shadows.empty
        TypedNuMxn(td, thisTV, superTV, ttu.freshenAbove(m.level, rigidify = false))
      case _ => ???
    }
  }
  
  sealed trait TypedNuTermDef extends TypedNuDecl {
    override def toString: String = this match {
      case _ => ???
    }
  }
  
  sealed abstract class TypedNuTypeDef(kind: TypeDefKind) extends TypedNuDecl {
    def nme: TypeName
  }
  // case class TypedNuTypeDef(
  //   kind: TypeDefKind,
  //   nme: TypeName,
  //   tparamsargs: List[(TypeName, TypeVariable)],
  //   bodyTy: SimpleType,
  //   baseClasses: Set[TypeName],
  //   toLoc: Opt[Loc],
  // )
  
  case class TypedNuAls(nme: TypeName) extends TypedNuTypeDef(Als) {
    def name: Str = nme.name
  }
  
  // case class TypedNuCls(nme: TypeName) extends TypedNuTypeDef(Als) with TypedNuTermDef {
  case class TypedNuCls(td: NuTypeDef, ttu: TypedTypingUnit, params: Ls[Var -> FieldType]) extends TypedNuTypeDef(Cls) with TypedNuTermDef {
  // case class TypedNuCls(td: NuTypeDef, paramTypes: Ls[ST], ttu: TypedTypingUnit) extends TypedNuTypeDef(Cls) with TypedNuTermDef {
    def nme: TypeName = td.nme
    def name: Str = nme.name
  }
  
  case class TypedNuMxn(td: NuTypeDef, thisTV: ST, superTV: ST, ttu: TypedTypingUnit) extends TypedNuTypeDef(Mxn) with TypedNuTermDef {
    def level = thisTV.level - 1 // TODO cleaner
    def nme: TypeName = td.nme
    def name: Str = nme.name
    // def freshen(implicit ctx: Ctx): TypedNuMxn = TypedNuMxn(td, 
  }
  
  case class TypedNuFun(fd: NuFunDef, ty: ST) extends TypedNuDecl with TypedNuTermDef {
    def name: Str = fd.nme.name
  }
  
  case class TypedTypingUnit(entities: Ls[TypedNuDecl], result: Opt[ST]) {
    // def freshen(implicit ctx: Ctx): TypedTypingUnit = ???
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, shadows: Shadows, freshened: MutMap[TV, ST])
          : TypedTypingUnit =
      TypedTypingUnit(entities, result.map(_.freshenAbove(lim, rigidify)))
  }
  
  def typeTypingUnit(tu: TypingUnit, allowPure: Bool)(implicit ctx: Ctx, raise: Raise): TypedTypingUnit =
      trace(s"${ctx.lvl}. Typing $tu") {
      // trace(s"${ctx.lvl}. Typing $tu") { ctx.nextLevel { implicit ctx: Ctx =>
    // val named = mutable.Map.empty[Str, LazyTypeInfo[TypedNuTermDef]]
    val named = mutable.Map.empty[Str, LazyTypeInfo]
    // val namedTerms = mutable.Map.empty[Var, LazyTypeInfo[TypedNuTypeDef]]
    // val namedTypes = mutable.Map.empty[TypeName, LazyTypeInfo[TypedNuTypeDef]]
    // val namedTerms = mutable.Map.empty[Str, LazyTypeInfo[ST]]
    // val namedTypes = mutable.Map.empty[Str, LazyTypeInfo[TypedNuTypeDef]]
    // val infos = tu.entities.collect {
    //   case fd: NuFunDef => fd.nme.name -> new LazyTypeInfo(lvl, fd)
    //   case td: NuTypeDef => td.nme.name -> new LazyTypeInfo(lvl, td)
    // }
    val infos = tu.entities.collect {
      case decl: NuDecl =>
        val lti = new LazyTypeInfo(lvl, decl)
        // def registerTerm = 
        named.updateWith(decl.name) {
          case sv @ S(v) =>
            ???
          case N =>
            S(lti)
        }
        decl.name -> lti
        // decl match {
        //   case fd: NuFunDef =>
        //     registerTerm
        //     fd.nme.name -> lti
        //   case td: NuTypeDef =>
        //     registerTerm
        //     td.nme.name -> new LazyTypeInfo(lvl, td)
        // }
    }
    ctx ++= infos
    def go(stmts: Ls[Statement])(implicit ctx: Ctx): Opt[ST] = stmts match {
      case s :: stmts =>
        val res_ty = s match {
          // case NuFunDef(isLetRec, nme, targs, rhs) =>
          // case fd: NuFunDef =>
          //   ???
          // case td: NuTypeDef =>
          //   ???
          case decl: NuDecl =>
            val lti = named.getOrElse(decl.name, die)
            // completeTypeInfo()
            lti.complete()
            // UnitType
            N
          // case ds: DesugaredStatement =>
          //   val (poly_ty, bindings) = typeStatement(ds, allowPure)
          //   poly_ty.instantiate
          case s: Statement =>
            val (diags, dss) = s.desugared
            diags.foreach(raise)
            // typeStatement(desug, allowPure)
            // go(dss ::: stmts)
            S(typeTerms(dss, false, Nil)(ctx, raise, TypeProvenance(s.toLoc, s match {
              case trm: Term => trm.describe
              case s => ???
            }), Map.empty, genLambdas = false))
        }
        stmts match {
          case Nil => res_ty
          case stmts =>
            // TODO check discarded non-unit values
            go(stmts)
        }
      // case Nil => UnitType
      case Nil => N
    }
    val res_ty = go(tu.entities)
    // TypedTypingUnit(infos.unzip._2.map(_.complete()), S(res_ty))
    TypedTypingUnit(infos.unzip._2.map(_.complete()), res_ty)
  }()
  // }(raise, noProv/*TODO*/)}()
  
  // class TypedTypingUnit(tu: TypingUnit)(implicit ctx: Ctx, raise: Raise) {
  // }
  
  
}

