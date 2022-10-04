package mlscript.compiler

import mlscript.*
import mlscript.utils.StringOps

class ClassLifter { self: ClassLifter =>

  type ClassName = String
  type FieldName = String

  var retSeq: List[NuTypeDef] = Nil;
  var anonymCnt: Int = 0;

  private def genAnoName(textNm: String = "Ano"): String = {
    anonymCnt = anonymCnt + 1
    textNm ++ "$_" ++ anonymCnt.toString()
  }
  private def isAnoName(text: String): Boolean = text.contains("$_")
  private def genParName(clsNm: String): String = "par$" ++ clsNm
  private def genInnerName(outerCls: NuTypeDef, innerNm: String) = outerCls.nme.name ++ "$" ++ innerNm
  private def genNameString(implicit parFields: List[ParFields]): String = {
    parFields.map{_.outerNm}.reverse.mkString("$")
  }
  private def tupleEntityToStr(fld: (Option[Var], Fld)): Option[String] = fld match{
    case (None, Fld(_, _, Var(nm))) => Some(nm)
    case (Some(Var(nm)), _) => Some(nm)
    case _ => None
  }
  private def tupleEntityMapTrm(f: Term => Term)(fld: (Option[Var], Fld)): (Option[Var], Fld) = fld match {
    case (None, snd@Fld(_, _, trm)) => (None, snd.copy(value = f(trm)))
    case _ => fld
  }
  private def tupleEntityRenameVar(f: Var => Var)(fld: (Option[Var], Fld)): (Option[Var], Fld) = fld match {
    case (None, snd@Fld(_, _, nmV: Var)) => (None, snd.copy(value = f(nmV)))
    case (Some(nmV), snd) => (Some(f(nmV)), snd)
    case _ => fld
  }

  private def knowCls(searchField: TypingUnit, clsNm: String): Option[NuTypeDef] = {
    searchField.entities.flatMap{
      case cls@NuTypeDef(_, TypeName(nm), _, _, _, _) if nm === clsNm => Some(cls)
      case _ => None
    }.headOption
  }

  case class ParFields(parVName: String, outerNm: String, supClsList: List[NuTypeDef]){
    override def toString(): String = parVName ++ "#" ++ outerNm ++ ":" ++ supClsList.map(_.nme.name).mkString("[", ", ", "]")
    def findCls(clsNm: String): Option[(NuTypeDef, NuTypeDef)] = {
      supClsList.flatMap{
        clsDef => ClassLifter.this.knowCls(clsDef.body, clsNm).map((clsDef, _))
      }.headOption
    }
    def findClsRenamed(clsNm: String): Option[NuTypeDef] = {
      this.findCls(clsNm).map{
        case (outer, inner) => inner.copy(nme = TypeName(genInnerName(outer, inner.nme.name)))
      }
    }
  }
  abstract class FieldType
  case class UnKnown() extends FieldType
  case class FieldNameType() extends FieldType
  case class ClassNameType() extends FieldType

  private def searchField(cls: NuTypeDef, fldNm: String): FieldType = {
    if(cls.params.fields.flatMap(tupleEntityToStr).contains(fldNm)){
      FieldNameType()
    }
    else {
      cls.body.entities.flatMap{
        case NuFunDef(_, Var(nm), _, _) if nm === fldNm => Some(FieldNameType())
        case NuTypeDef(_, TypeName(nm), _, _, _, _) if nm === fldNm => Some(ClassNameType())
        case _ => None 
      }.headOption.getOrElse(UnKnown())
    }
  }
  private def selPath2Term(path: List[String], varNm: Var): Term = path match {
    case Nil => varNm
    case (head :: tail) => Sel(selPath2Term(tail, Var(head)), varNm)
  }
  private def buildPath(name: String)(implicit parFields: List[ParFields], globalFlds: TypingUnit): (Term, Option[Term]) = {
    type FoldResult = (FieldType, List[String], String) //status, parPath, clsName
    // println(s"building path to $name in $parFields")
    if(parFields.isEmpty) (Var(name), None)
    else {
      val re = parFields.updated(0, ParFields("this", parFields.head.outerNm, parFields.head.supClsList)).foldLeft[FoldResult]((UnKnown(), Nil, ""))(
        (rlt, fields) => rlt match{
          case (_: UnKnown, parPath, _) =>
            val tmp = fields.supClsList.map(cls => (searchField(cls, name), cls)).filterNot(_._1.isInstanceOf[UnKnown]).headOption
            tmp match{
              case Some((_: FieldNameType, _)) => (FieldNameType(), fields.parVName :: parPath, "")
              case Some((_: ClassNameType, cls)) => (ClassNameType(), fields.parVName :: parPath, genInnerName(cls, name))
              case None => (UnKnown(), fields.parVName :: parPath, "")
            }
          case _ => rlt
        }
      );
      // println("result: " ++ re.toString())
      re._1 match {
        case _: FieldNameType =>
          (selPath2Term(re._2, Var(name)), None)
        case _: ClassNameType =>
          if(re._2.length > 1){
            (Var(re._3), Some(selPath2Term(re._2.tail, Var(re._2.head))))
          }
          else {
            (Var(re._3), Some(Var(re._2.head)))
          }
        case _: UnKnown =>
          // println(s"cannot find identifier $name")
          // println(s"searching field: ${parFields.mkString("[", ", ", "]")}")
          (Var(name), None)
      }
    }
  }
  private def np2Str(namePath: List[String]): String = namePath.reverse.mkString("_")
  private def toFldsEle(trm: Term): (Option[Var], Fld) = (None, Fld(false, false, trm))
  private def findTpDef(clsName: String)(implicit parFields: List[ParFields], globalFlds: TypingUnit): Option[NuTypeDef] = {
    (parFields.flatMap{ lvl => lvl.findClsRenamed(clsName)}++knowCls(globalFlds, clsName)).headOption
  }

  private def getSupClsesByType(tp: NuTypeDef)(implicit parFields: List[ParFields], globalFlds: TypingUnit): List[NuTypeDef] = {
    def getParentClsByTerm(parentTerm: Term): List[NuTypeDef] = parentTerm match{
      case Var(nm) => findTpDef(nm).toList
      case App(Var(nm), _: Tup) => findTpDef(nm).toList
      case App(App(Var("&"), t1), t2) => getParentClsByTerm(t1) ++ getParentClsByTerm(t2)
      case Bra(true, Rcd(flds)) => 
        val newCls = NuTypeDef(Trt, TypeName(""), Nil, Tup(flds.map(x => x.copy(_1 = Some(x._1)))), Nil, TypingUnit(Nil))
        List(newCls)
      case TyApp(Var(nm), targs) => findTpDef(nm).toList
      //SPECIAL CARE: Tup related issue
      case Tup(flds) => flds.filter(_._1.isEmpty).flatMap(fld => getParentClsByTerm(fld._2.value))
    }
    
    tp :: tp.parents.flatMap(getParentClsByTerm).flatMap(getSupClsesByType)
  }

  private def liftTerm(target: Term)(implicit localVars: Set[String], parFields: List[ParFields], globalFlds: TypingUnit, knownTypeParams: List[TypeName]): Term = {
    def fldMapForRcd(oflds: List[(Var, Fld)], func: Term => Term): List[(Var, Fld)] = {
      oflds.map{ case (vdef, Fld(b1, b2, oTerm)) => (vdef, Fld(b1, b2, func(oTerm)))}
    }
    // println(s"lifting expr ${mlscript.codegen.Helpers.inspect(target)}")
    target match{
      case Var(name) if !localVars.contains(name) => buildPath(name)._1
      case Lam(Var(nm), body) => 
        Lam(Var(nm), liftTerm(body)(localVars + nm, parFields, globalFlds, knownTypeParams))
      case Lam(Asc(Var(nm), _), body) => 
        Lam(Var(nm), liftTerm(body)(localVars + nm, parFields, globalFlds, knownTypeParams))
      case Lam(Tup(vars), body) =>
        val nEle = vars.flatMap(tupleEntityToStr).toSet
        Lam(Tup(vars), liftTerm(body)(localVars ++ nEle, parFields, globalFlds, knownTypeParams))
      case Tup(flds) => 
        val nEle = flds.flatMap(tupleEntityToStr).toSet
        val f = (otrm: Term) => liftTerm(otrm)(localVars ++ nEle, parFields, globalFlds, knownTypeParams)
        Tup(flds.map(tupleEntityMapTrm(f)))
      case Rcd(flds) =>
        val nEle = flds.map{case (Var(nm), _) => nm}.toSet
        val f = (otrm: Term) => liftTerm(otrm)(localVars ++ nEle, parFields, globalFlds, knownTypeParams)
        Rcd(fldMapForRcd(flds, f))
      case Let(isrec, vName@Var(name), rhs, body) =>
        Let(isrec, vName, liftTerm(rhs), liftTerm(body)(localVars + name, parFields, globalFlds, knownTypeParams))
      
      //calling constructors
      case App(Var(nm), rhs@Tup(flds)) => 
        // println(s"here: nm = $nm, parFields = ${parFields.mkString("[", ", ", "]")}")
        val (nName, parArg) = buildPath(nm)
        parArg match{
          case None => App(nName, Tup(flds.map(tupleEntityMapTrm(liftTerm))))
          case Some(parNm) => 
            App(nName, Tup(toFldsEle(parNm) :: flds.map(tupleEntityMapTrm(liftTerm))))
        }
      case New(Some((TypeName(nm), rhs@Tup(flds))), TypingUnit(Nil)) =>
        val (Var(nName), parArg) = buildPath(nm)
        parArg match{
          case None => New(Some((TypeName(nName), Tup(flds.map(tupleEntityMapTrm(liftTerm))))), TypingUnit(Nil))
          case Some(parNm) => 
            New(Some((TypeName(nName), Tup(toFldsEle(parNm) :: flds.map(tupleEntityMapTrm(liftTerm))))), TypingUnit(Nil))
        }
      case New(Some((TypeName(nm), rhs@Tup(flds))), nBody) => 
        findTpDef(nm) match {
          case Some(nmType@NuTypeDef(_, _, _, params, parents, _)) => 
            val nuTypeNm = genAnoName(nm);
            val renamedParams = Tup(params.fields.map(tupleEntityRenameVar{(x: Var) => Var("prm$" ++ nm ++ x.name)}))
            val nType = NuTypeDef(Cls, TypeName(nuTypeNm), knownTypeParams, renamedParams, List(App(Var(nm), renamedParams)), nBody)
            val lfedTypeNm = liftNestedClass(nType)
            if(parFields.isEmpty) New(Some((lfedTypeNm, Tup(flds.map(tupleEntityMapTrm(liftTerm))))), TypingUnit(Nil))
            else New(Some((lfedTypeNm, Tup(toFldsEle(Var("this")) :: flds.map(tupleEntityMapTrm(liftTerm))))), TypingUnit(Nil))
          case None => 
            //user wants to inherit from an unknown class: should throw error
            ???
        }
      case New(None, nBody) =>
        val nuTypeNm = genAnoName()
        val nType = NuTypeDef(Cls, TypeName(nuTypeNm), knownTypeParams, Tup(Nil), Nil, nBody)
        val lfedTypeNm = liftNestedClass(nType);
        New(Some((lfedTypeNm, Tup(
          if(parFields.nonEmpty) List(toFldsEle(Var("this")))
          else Nil
        ))), TypingUnit(Nil))
      case Bra(true, Rcd(flds)) => 
        val nTypeNm = genAnoName()
        val newCls = NuTypeDef(Trt, TypeName(nTypeNm), knownTypeParams, Tup(flds.map(x => x.copy(_1 = Some(x._1)))), Nil, TypingUnit(Nil))
        val retTypeNm = liftNestedClass(newCls)(Nil, globalFlds)
        Var(retTypeNm.name)
      case _ => 
        target.map(liftTerm)
    }
  }
  private def isTypeUsed(trm: Located)(implicit varNm: TypeName): Boolean = trm match{
    case Asc(trm, TypeName(ty)) if ty === varNm.name => true
    //SPECIAL CARE: Tup related issue
    case Tup(tupLst) if tupLst.find{
                          case (Some(_), Fld(_, _, Var(name))) => name === varNm.name
                          case _ => false
                        }.isDefined 
        => true
    case TyApp(_, targs) if targs.contains(varNm) => true 
    case trm => trm.children.find(isTypeUsed).isDefined
  }
  private def isTypeUsedInUnit(unt: TypingUnit)(implicit varNm: TypeName): Boolean = {
    unt.entities.find{
      case trm: Term => isTypeUsed(trm)
      case NuFunDef(_, _, targs, Left(trm)) =>
        if(targs.contains(varNm)) false
        else isTypeUsed(trm)
      //poly type functions
      case NuFunDef(_, _, targs, Right(polyType)) => ???
      //typeDefs: should be filtered out in advance
      case _: NuTypeDef => throw new Exception("should not reach")
    }.isDefined
  }

  private def liftNestedClass(tyDef: NuTypeDef)(implicit parFields: List[ParFields], globalFlds: TypingUnit): TypeName = {
    val NuTypeDef(kind, TypeName(tpName), tparams, params, parents, body) = tyDef
    // println("find parents" + parents.map(mlscript.codegen.Helpers.inspect(_)).mkString("[", ", ", "]"))
    // println(s"lift class ${tyDef.nme.name}: ")
    // println(PrettyPrinter.show(rawBody))
    val knownTypeParams = (tparams ++ parFields.map(_.supClsList.head).flatMap(_.tparams)).distinct
    val innerClasses = body.entities.flatMap{
      case subTypeDef: NuTypeDef => Some(subTypeDef) 
      case _ => None
    }
    val liftedTypeName = genNameString(ParFields("", tpName, Nil) :: parFields);
    val nTypeDef = tyDef.copy(nme = TypeName(liftedTypeName))
    val parVariableNm = genParName(liftedTypeName)
    val nParamList = {
      if(parFields.size > 0) {Tup((None, Fld(false, true, Var(genParName(genNameString)))) :: params.fields)}
      else {params}
    }
    val supCls = getSupClsesByType(nTypeDef)
    val nParFields = ParFields(parVariableNm, tpName, supCls) :: parFields
    // println(s"handle $tpName, using ${nParFields.mkString("[", ", ", "]")}")
    val nBody = TypingUnit(body.entities.flatMap{
      case term: Term => Some(liftTerm(term)(Set(), nParFields, globalFlds, knownTypeParams))
      case _: NuTypeDef => None
      case self@NuFunDef(isLetRec, nm, tpNmList, funBody) => 
      funBody match{
        case Left(bodyTerm) => Some(NuFunDef(isLetRec, nm, tpNmList, Left(liftTerm(bodyTerm)(Set(), nParFields, globalFlds, (knownTypeParams++tpNmList).distinct))))
        case Right(_) => Some(self)
      }
    })
    val nParents = parents.map(liftTerm(_)(Set(), nParFields, globalFlds, knownTypeParams))
    val nTypeParams = (knownTypeParams.filter(
      tp => isTypeUsedInUnit(nBody)(tp) || isTypeUsed(nParamList)(tp) || parents.find(isTypeUsed(_)(tp)).isDefined
    ) ++ (if(isAnoName(tpName)) {Nil} else tparams)).distinct

    innerClasses.map(cls => liftNestedClass(cls)(nParFields, globalFlds))
    retSeq = retSeq.appended(NuTypeDef(kind, TypeName(liftedTypeName), nTypeParams, nParamList, nParents, nBody))
    TypeName(liftedTypeName)
  }

  def liftClass(tyDef: NuTypeDef): List[NuTypeDef] = {
    retSeq = Nil
    liftNestedClass(tyDef)(Nil, TypingUnit(Nil))
    val re = retSeq.toList
    // println("<<<<<<<<<<<<<<<< class lifting result ================");
    // println(s"$tyDef\n================>");
    // re.map(tpDefi => PrettyPrinter.showTypeDef(tpDefi, 0)).map(println(_));
    // re.map(_.show).map(println(_));
    // println("================ class lifting result >>>>>>>>>>>>>>>>");
    re
  }
  def liftEntities(entities: List[Statement]): List[Statement] = {
    retSeq = Nil
    entities.flatMap{
      case nType: NuTypeDef => Some(nType)
      case _ => None
    }.map(liftNestedClass(_)(Nil, TypingUnit(entities)))
    val nEtts = entities.flatMap{
      case _: NuTypeDef => None
      case trm: Term => Some(liftTerm(trm)(Set(), Nil, TypingUnit(entities), Nil))
      case NuFunDef(isLetRec, funNm, tpLs, Left(trm)) => Some(NuFunDef(isLetRec, funNm, tpLs, Left(liftTerm(trm)(Set(), Nil, TypingUnit(entities), tpLs))))
      case rest => Some(rest)
    }
    val re = retSeq.toList
    // println("================ class lifting result >>>>>>>>>>>>>>>>");
    // re.map(tpDefi => PrettyPrinter.showTypeDef(tpDefi, 0)).map(println(_));
    // println(PrettyPrinter.show(TypingUnit(nEtts)))
    // println("<<<<<<<<<<<<<<<< class lifting result ================");
    re ++ nEtts
  }
  def liftTypingUnit(rawUnit: TypingUnit): TypingUnit = {
    TypingUnit(liftEntities(rawUnit.entities))
  }
}
