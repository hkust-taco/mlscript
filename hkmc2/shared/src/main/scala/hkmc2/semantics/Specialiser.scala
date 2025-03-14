package hkmc2
package semantics

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import hkmc2.Message.MessageContext
import hkmc2.semantics.Elaborator.*
import hkmc2.semantics.Split.{Let, Else}
import hkmc2.semantics.Term.*
import hkmc2.syntax.Tree
import hkmc2.syntax.Tree.{Ident, IntLit, StrLit, UnitLit, BoolLit}
import hkmc2.utils.TraceLogger


class SimpleSub(val ectx: Elaborator.Ctx, val tl: TraceLogger)(using Elaborator.State):
  import tl.*

  private val specialisationPoints = mutable.Map[Symbol, SpecPoint]()

  case class SpecPoint(
    paramSym: Symbol,
    parentFunctionSym: Symbol,
    concreteTypes: mutable.Set[SimpleType] = mutable.Set.empty,
    typeVars: mutable.Set[VariableState] = mutable.Set.empty
  ):
    def addConcrete(ty: SimpleType): Unit =
      log(s"Adding concrete type $ty to spec point ${paramSym.nme}")
      concreteTypes += ty
      
    def addVar(vs: VariableState): Unit =
      log(s"Adding var ${vs.uniqueName} to spec point ${paramSym.nme}")
      typeVars += vs
      
    def updateFromVars(): Unit =
      typeVars.foreach { vs =>
        vs.lowerBounds.foreach { bound =>
          if isConcreteType(bound) then
            log(s"Found concrete bound $bound for var ${vs.uniqueName} in spec point ${paramSym.nme}")
            concreteTypes += bound
        }
      }
    
    override def toString: String = 
      val typeStrs = concreteTypes.toList.map(ty => coalesceType(ty))
      s"${paramSym.nme} in ${parentFunctionSym.nme} can be specialised for: [${typeStrs.mkString(", ")}]"

  case class ClassInfo(
    sym: ClassSymbol,
    memberSym: BlockMemberSymbol,
    params: Ls[Str] = Nil,
    supers: Ls[SimpleType] = Nil,
    members: Map[Str, SimpleType] = Map.empty,
    fields: Map[Str, SimpleType] = Map.empty
  ):
    override def toString: String = 
      val superStr = if supers.isEmpty then "" else s" extends ${supers.mkString(" with ")}"
      val fieldsStr = if fields.isEmpty then "" else fields.map { case (n, t) => s"val $n: $t" }.mkString(", ")
      val membersStr = members.map { case (n, t) => s"$n: $t" }.mkString(", ")
      val contentStr = (if fieldsStr.nonEmpty && membersStr.nonEmpty then s"$fieldsStr; $membersStr" 
                        else fieldsStr + membersStr)
      s"class ${sym.nme}$superStr { $contentStr }"

  object VariableState:
    private var nextIdCounter = 0
    def nextId =
      val id = nextIdCounter
      nextIdCounter += 1
      id

  class VariableState(var lowerBounds: Ls[SimpleType] = Nil, var upperBounds: Ls[SimpleType] = Nil):
    private val id = VariableState.nextId
    val uniqueName: String = s"'${('a' + id % 26).toChar}${if id >= 26 then (id / 26).toString else ""}"

  
  enum SimpleType:
    case Variable(state: VariableState)
    case Primitive(name: Str)
    case Function(lhs: SimpleType, rhs: SimpleType)
    case Record(fields: Ls[(Str, SimpleType)])
    case ClassType(info: ClassInfo)
    case SpecialisableType(specPoint: SpecPoint, underlying: SimpleType)
    
    override def toString: String = this match
      case Variable(state) => s"${state.uniqueName}"
      case Primitive(name) => name
      case Function(lhs, rhs) => s"(${lhs} -> ${rhs})"
      case Record(fields) => fields.map(f => s"${f._1}: ${f._2}").mkString("{ ", "; ", " }")
      case ClassType(info) => info.toString
      case SpecialisableType(specPoint, underlying) => s"spec[${underlying}]"

  import SimpleType.*

  val IntType = Primitive("Int")
  val BoolType = Primitive("Bool")
  val StrType = Primitive("Str")
  val UnitType = Primitive("Unit")
  val AnyType = Primitive("Any")
  val NumType = Primitive("Num")

  def freshVar: Variable = Variable(VariableState())

  def isConcreteType(ty: SimpleType): Boolean = ty match
    case Variable(_) => false
    case Function(lhs, rhs) => isConcreteType(lhs) && isConcreteType(rhs)
    case Record(fields) => fields.forall((_, t) => isConcreteType(t))
    case SpecialisableType(_, underlying) => isConcreteType(underlying)
    case Primitive(_) => true
    case ClassType(_) => true
  
  class TypeContext(val mapping: Map[Symbol, SimpleType] = Map.empty):
    def get(sym: Symbol): Option[SimpleType] = mapping.get(sym)
    def getOrFresh(sym: Symbol): SimpleType = mapping.getOrElse(sym, freshVar)
    def +(pair: (Symbol, SimpleType)): TypeContext = TypeContext(mapping + pair)
    def ++(pairs: Iterable[(Symbol, SimpleType)]): TypeContext = TypeContext(mapping ++ pairs)
    override def toString: String = mapping.map { case (sym, ty) => s"$sym: $ty" }.mkString(", ")

  def initialContext(using state: Elaborator.State): TypeContext =
    val builtinTypes = Map(
      state.builtinOpsMap.values.map { sym =>
        val opType = sym.nme match
          case "+" | "-" | "*" | "/" | "%" => 
            Function(Record(Ls("_0" -> NumType, "_1" -> NumType)), NumType)
          case "==" | "!=" | "===" | "!==" | "<" | "<=" | ">" | ">=" =>
            val tv = freshVar
            Function(Record(Ls("_0" -> tv, "_1" -> tv)), BoolType)
          case "&&" | "||" => 
            Function(Record(Ls("_0" -> BoolType, "_1" -> BoolType)), BoolType)
          case "!" => Function(BoolType, BoolType)
          case "~" => Function(IntType, IntType)
          case "typeof" => Function(AnyType, StrType)
          case _ => freshVar
        
        sym.asInstanceOf[Symbol] -> opType
      }.toSeq*
    )
    
    TypeContext(builtinTypes)

  def constrain(lhs: SimpleType, rhs: SimpleType)(using cache: mutable.Set[(SimpleType, SimpleType)] = mutable.Set.empty): Unit =
    if cache.contains(lhs -> rhs) then return () else cache += lhs -> rhs
    
    log(s"Constraining ${lhs} <: ${rhs}")
    
    (lhs, rhs) match
      case (concrete, SpecialisableType(specPoint, underlying)) =>
        if isConcreteType(concrete) then
          log(s"Recording concrete type ${concrete} for specialisation point ${specPoint.paramSym.nme}")
          specPoint.addConcrete(concrete)
        else 
          concrete match
            case Variable(vs) =>
              log(s"Recording variable ${vs.uniqueName} for specialisation point ${specPoint.paramSym.nme}")
              specPoint.addVar(vs)
            case _ => 
              log(s"Non-concrete, non-variable type ${concrete} flowing into spec param ${specPoint.paramSym.nme}")
        
        constrain(concrete, underlying)
        
      case (SpecialisableType(specPoint, underlying), other) =>
        constrain(underlying, other)
        
      case (Primitive(n0), Primitive(n1)) if n0 == n1 => ()
      case (_, Primitive("Any")) => ()
      case (Primitive(n0), Primitive(n1)) if n0 == "Int" && n1 == "Num" => ()
      case (Function(l0, r0), Function(l1, r1)) =>
        constrain(l1, l0)
        constrain(r0, r1)
      case (Record(fs0), Record(fs1)) =>
        fs1.foreach { case (n1, t1) =>
          fs0.find(_._1 == n1) match
            case None => 
              log(s"Error: missing field: $n1 in $lhs")
            case Some((_, t0)) => 
              (t0, t1) match
                case (SpecialisableType(specPoint, underlying), concrete) if isConcreteType(concrete) =>
                  log(s"Record field: recording concrete type ${concrete} for specialisation point ${specPoint.paramSym.nme}")
                  specPoint.addConcrete(concrete)
                  constrain(underlying, concrete)
                case _ => constrain(t0, t1)
        }
      case (Variable(lhs), Variable(rhs)) if lhs == rhs => ()
      case (Variable(lhs), rhs) =>
        lhs.upperBounds = rhs :: lhs.upperBounds
        lhs.lowerBounds.foreach(constrain(_, rhs))
        
        specialisationPoints.values.foreach { specPoint =>
          if specPoint.typeVars.contains(lhs) && isConcreteType(rhs) then
            log(s"Variable ${lhs.uniqueName} tracked by ${specPoint.paramSym.nme} now bound to concrete type $rhs")
            specPoint.addConcrete(rhs)
        }
        
      case (lhs, Variable(rhs)) =>
        rhs.lowerBounds = lhs :: rhs.lowerBounds
        rhs.upperBounds.foreach(constrain(lhs, _))
        
        if isConcreteType(lhs) then
          specialisationPoints.values.foreach { specPoint =>
            if specPoint.typeVars.contains(rhs) then
              log(s"Variable ${rhs.uniqueName} tracked by ${specPoint.paramSym.nme} now has concrete lower bound $lhs")
              specPoint.addConcrete(lhs)
          }
          
      case (ClassType(info), Record(fields)) =>
        fields.foreach { case (fieldName, fieldType) =>
          info.members.get(fieldName).orElse(info.fields.get(fieldName)) match
            case Some(memberType) => constrain(memberType, fieldType)
            case None => log(s"Error: class ${info.sym.nme} has no member or field named '${fieldName}'")
        }
      case (ClassType(info), Function(paramType, resultType)) =>
        if info.params.length == 1 then
          val fieldType = info.fields.getOrElse(info.params.head, freshVar)
          constrain(paramType, fieldType)
          constrain(ClassType(info), resultType)
        else if info.params.isEmpty then
          log(s"Error: class ${info.sym.nme} has no parameters but is used with arguments")
        else
          paramType match
            case Record(fields) if fields.size == info.params.size =>
              info.params.zip(fields).foreach { case (paramName, (_, fieldType)) =>
                val classFieldType = info.fields.getOrElse(paramName, freshVar)
                constrain(fieldType, classFieldType)
              }
              constrain(ClassType(info), resultType)
            case _ => log(s"Error: class ${info.sym.nme} expects ${info.params.length} parameters")
      case _ => log(s"Error: cannot constrain $lhs <: $rhs")
  
  def term(t: Term)(using ctx: TypeContext): SimpleType =
    log(s"Typing term: ${t.showDbg}")
    val typed = t match
      case Error | Missing => freshVar
      case UnitVal() => UnitType
      case b: Blk => block(b)
      case Lit(lit) => lit match
        case Tree.IntLit(_) => IntType
        case Tree.StrLit(_) => StrType
        case Tree.BoolLit(_) => BoolType
        case Tree.UnitLit(_) => UnitType
        case Tree.DecLit(_) => NumType

      case ifLike @ IfLike(kw, desugared) =>
        log(s"Typing if-like expression with keyword: $kw")
        
        def typeSplit(split: Split): SimpleType = split match
          case Split.Cons(head, tail) =>
            val Branch(scrutinee, pattern, continuation) = head
            val scrutType = term(scrutinee)
            
            if kw == syntax.Keyword.`if` then constrain(scrutType, BoolType)
            
            pattern match
              case Pattern.Lit(lit) if lit.isInstanceOf[Tree.BoolLit] =>
              case _ => log(s"Pattern matching on: ${pattern.showDbg}")
            
            val branchType = typeSplit(continuation)
            val tailType = typeSplit(tail)
            val resultType = freshVar

            constrain(branchType, resultType)
            constrain(tailType, resultType)
            resultType
            
          case Split.Let(sym, t, tail) =>
            log(s"Processing let binding in conditional: ${sym.nme}")
            val bindingType = term(t)
            val extendedCtx = ctx + (sym -> bindingType)
            term(IfLike(kw, tail)(tail))(using extendedCtx)
            
          case Split.Else(default) =>
            log(s"Processing else branch")
            term(default)
            
          case Split.End => UnitType
        
        val splitType = typeSplit(desugared)
        if kw == syntax.Keyword.`while` then UnitType else splitType
      
      case app @ App(lhs, rhs) =>
        val resultType = freshVar
        val lhsType = term(lhs)
        val rhsType = rhs match
          case Tup(fields) if fields.length > 1 =>
            Record(fields.zipWithIndex.map { 
              case (Fld(_, t, _), idx) => s"_${idx}" -> term(t)
              case (_, idx) => s"_${idx}" -> freshVar
            })
          case Tup(fields) if fields.length == 1 =>
            fields.head match
              case Fld(_, t, _) => term(t)
              case _ => freshVar
          case _ => term(rhs)
        
        log(s"Application: constraining $lhsType and $rhsType")
        
        lhsType match
          case Function(Record(namedParams), retType) =>
            rhsType match
              case Record(numericFields) if numericFields.forall(_._1.startsWith("_")) && 
                                           namedParams.length == numericFields.length =>
                log(s"Handling application with named parameters and positional arguments")
                namedParams.zip(numericFields).foreach { 
                  case ((paramName, paramType), (_, argType)) =>
                    constrain(argType, paramType)
                    
                    (paramType, argType) match
                      case (SpecialisableType(specPoint, _), concrete) if isConcreteType(concrete) =>
                        log(s"Direct arg flow: recording concrete type ${concrete} for specialisation point ${specPoint.paramSym.nme}")
                        specPoint.addConcrete(concrete)
                      case _ => ()
                }
                constrain(retType, resultType)
              case _ => constrain(lhsType, Function(rhsType, resultType))
          case _ => constrain(lhsType, Function(rhsType, resultType))
          
        resultType
      
      case New(cls, args, _) =>
        val clsType = term(cls)
        val argTypes = args.map(term)
        
        cls.symbol match
          case Some(clsSym) =>
            ctx.get(clsSym) match
              case Some(ClassType(classInfo)) => 
                if classInfo.params.length != args.length then
                  log(s"Error: ${clsSym.nme} constructor expects ${classInfo.params.length} arguments, but got ${args.length}")
                val instanceFields = classInfo.params.zip(argTypes).toMap
                ClassType(classInfo.copy(fields = classInfo.fields ++ instanceFields))
              case _ => clsType
          case None => clsType

      case Ref(sym) => 
        log(s"Looking up symbol reference: ${sym.nme}")
        val symType = ctx.getOrFresh(sym)
        log(s"Found type for ${sym.nme}: ${symType}")
        symType match
          case ClassType(info) if info.params.nonEmpty =>
            if info.params.length == 1 then
              val paramType = info.fields.getOrElse(info.params.head, freshVar)
              Function(paramType, symType)
            else
              val recordFields = info.params.map { paramName =>
                val fieldType = info.fields.getOrElse(paramName, freshVar)
                paramName -> fieldType
              }
              Function(Record(recordFields), symType)
          case classType @ ClassType(info) if info.params.isEmpty =>
            log(s"Using class ${info.sym.nme} as a value")
            classType
          case _ => symType
      
      case Sel(prefix, name) =>
        val prefixType = term(prefix)
        
        prefixType match
          case ClassType(classInfo) =>
            classInfo.members.get(name.name) match
              case Some(methodType) => methodType
              case None => classInfo.fields.getOrElse(name.name, {
                log(s"Error: No member or field '${name.name}' found in class ${classInfo.sym.nme}")
                freshVar
              })
          
          case Variable(vs) =>
            val resultType = freshVar
            vs.upperBounds.foreach {
              case ClassType(classInfo) =>
                classInfo.members.get(name.name).orElse(classInfo.fields.get(name.name)) match
                  case Some(memberType) => constrain(resultType, memberType)
                  case None => ()
              case _ => ()
            }
            constrain(prefixType, Record(List(name.name -> resultType)))
            resultType
          
          case _ =>
            val resultType = freshVar
            constrain(prefixType, Record(List(name.name -> resultType)))
            resultType
      
      case SynthSel(prefix, name) =>
        val prefixType = term(prefix)
        
        prefixType match
          case ClassType(classInfo) =>
            classInfo.members.get(name.name).orElse(classInfo.fields.get(name.name)) match
              case Some(memberType) => memberType
              case None =>
                log(s"Error: No member or field '${name.name}' found in class ${classInfo.sym.nme}")
                freshVar
          
          case Variable(vs) =>
            val resultType = freshVar
            vs.upperBounds.foreach {
              case ClassType(classInfo) =>
                classInfo.members.get(name.name).orElse(classInfo.fields.get(name.name)) match
                  case Some(memberType) => constrain(resultType, memberType)
                  case None => ()
              case _ => ()
            }
            constrain(prefixType, Record(List(name.name -> resultType)))
            resultType
          
          case _ =>
            val resultType = freshVar
            constrain(prefixType, Record(List(name.name -> resultType)))
            resultType
      case _ => freshVar

    log(s"❁ Type for ${t.showDbg}: ${coalesceType(typed)}")
    typed

  def block(b: Blk)(using ctx: TypeContext): SimpleType =
    var currentCtx = ctx
    b.stats.foreach {
      case LetDecl(sym, _) =>
        val varTy = freshVar
        currentCtx = currentCtx + (sym -> varTy)
      
      case DefineVar(sym, rhs) =>
        val rhsTy = term(rhs)(using currentCtx)
        currentCtx.get(sym).foreach(constrain(rhsTy, _))
        currentCtx = currentCtx + (sym -> rhsTy)
      
      case cls: ClassDef =>
        log(s"Processing class: ${cls.sym.nme}")
        
        val members = mutable.Map.empty[String, SimpleType]
        val fields = mutable.Map.empty[String, SimpleType]
        val paramNames = cls.paramsOpt.map { params => params.params.map(_.sym.name) }.getOrElse(Nil)
        
        paramNames.foreach { paramName => fields(paramName) = freshVar }
        
        val classInfo = ClassInfo(cls.sym, cls.bsym, paramNames, Nil, Map.empty, fields.toMap)
        val classType = ClassType(classInfo)
        
        currentCtx = currentCtx + (cls.sym -> classType)
        currentCtx = currentCtx + (cls.bsym -> classType)
        
        cls.body.blk.stats.foreach {
          case td: TermDefinition =>
            val methodType = td.body match
              case Some(Ref(sym)) if fields.contains(sym.nme) => fields(sym.nme)
              case Some(body) => term(body)(using currentCtx)
              case None => freshVar
            
            members(td.sym.nme) = methodType
          
          case _ => // Skip other statements
        }
        
        val updatedClassInfo = classInfo.copy(members = members.toMap)
        val updatedClassType = ClassType(updatedClassInfo)
        
        currentCtx = currentCtx + (cls.sym -> updatedClassType)
        currentCtx = currentCtx + (cls.bsym -> updatedClassType)

      case _ => // Skip other statements including function definitions; they will be processed later
    }

    b.stats.foreach {
      case td: TermDefinition =>
        log(s"Processing function definition: ${td.sym.nme}")
        val paramTypes = td.params.flatMap(paramList => 
          paramList.params.map(param => {
            val paramType = freshVar
            
            val isSpecialised = param.flags.spec
            log(s"Parameter ${param.sym.nme} of function ${td.sym.nme} has spec=${isSpecialised}")
            
            val finalType = if isSpecialised then
              val specPoint = specialisationPoints.getOrElseUpdate(
                param.sym, 
                SpecPoint(param.sym, td.sym)
              )
              SpecialisableType(specPoint, paramType)
            else paramType
              
            log(s"Assigned type ${finalType} to parameter ${param.sym.nme}")
            param.sym -> finalType
          })
        ).toMap
        
        val functionCtx = currentCtx ++ paramTypes
        
        val resultType = td.body match
          case Some(body) => 
            val bodyType = term(body)(using functionCtx)
            log(s"Function ${td.sym.nme} body has type: ${bodyType}")
            bodyType
          case None => freshVar
        
        val functionType = if td.params.nonEmpty then
          td.params.foldRight(resultType): (paramList, currentReturnType) =>
            if paramList.params.length == 1 then
              val paramSym = paramList.params.head.sym
              val paramType = paramTypes.getOrElse(paramSym, freshVar)
              Function(paramType, currentReturnType)
            else
              val recordType = Record(paramList.params.map(param => 
                param.sym.nme -> paramTypes.getOrElse(param.sym, freshVar)
              ))
              Function(recordType, currentReturnType)
        else resultType
        
        log(s"Function ${td.sym.nme} has type: ${functionType}")
        currentCtx = currentCtx + (td.sym -> functionType)

      case _ => // Skip other statements
    }

    b.stats.foreach {
      case t: Term => term(t)(using currentCtx)
      case _ => // Skip other statements
    }
    term(b.res)(using currentCtx)
  
  def formatTypeForName(ty: SimpleType): String =
    coalesceType(ty)
      .replace(" ", "_")
      .replace("->", "To")
      .replace("{", "")
      .replace("}", "")
      .replace(";", "_")
      .replace(":", "_")
      .replace("|", "Or")
      .replace("&", "And")
      .replace("'", "")
      .replace("μ", "")
      .replace(".", "")

  def getSpecialisedParamIndices(funcSym: Symbol): List[Int] =
    specialisationPoints.values
      .filter(_.parentFunctionSym == funcSym)
      .map { specPoint =>
        val paramName = specPoint.paramSym.nme
        
        specialisationPoints.values
          .filter(_.parentFunctionSym == funcSym)
          .toList.indexWhere(_.paramSym.nme == paramName)
      }
      .filter(_ >= 0)
      .toList

  def typeToPattern(ty: SimpleType): Pattern = ty match
    case Primitive("Int") =>
      val intSym = ectx.builtins.Int
      val classSel = SynthSel(intSym.ref(), Ident("class"))(Some(intSym.asCls.get))
      Pattern.ClassLike(intSym.asCls.get, classSel, None, false)(Tree.Empty())
    case Primitive("Num") =>
      val numSym = ectx.builtins.Num
      val classSel = SynthSel(numSym.ref(), Ident("class"))(Some(numSym.asCls.get))
      Pattern.ClassLike(numSym.asCls.get, classSel, None, false)(Tree.Empty())
    case Primitive("Bool") =>
      val boolSym = ectx.builtins.Bool
      val classSel = SynthSel(boolSym.ref(), Ident("class"))(Some(boolSym.asCls.get))
      Pattern.ClassLike(boolSym.asCls.get, classSel, None, false)(Tree.Empty())
    case Primitive("Str") =>
      val strSym = ectx.builtins.Str
      val classSel = SynthSel(strSym.ref(), Ident("class"))(Some(strSym.asCls.get))
      Pattern.ClassLike(strSym.asCls.get, classSel, None, false)(Tree.Empty())
    case ClassType(info) =>
      val classSel = SynthSel(info.memberSym.ref(), Ident("class"))(Some(info.sym))
      Pattern.ClassLike(info.sym, classSel, None, false)(Tree.Empty())
    case _ =>
      Pattern.Lit(BoolLit(true))

  def processTree(term: Term): Term =
    case class SpecContext(funcs: mutable.Buffer[TermDefinition] = mutable.Buffer.empty)
    
    def process(t: Term)(implicit ctx: SpecContext): Term = t match
      case app @ App(lhs, rhs @ Tup(fields)) =>
        lhs match
          case Ref(funcSym) =>
            val specialisedIndices = getSpecialisedParamIndices(funcSym)
            
            if specialisedIndices.isEmpty then app else
              log(s"Found function ${funcSym.nme} call with specialised params: ${specialisedIndices}")
              
              val memberSymbols = specialisedIndices.map { idx =>
                val argName = s"${funcSym.nme}_arg$idx"
                val arg = fields(idx) match
                  case Fld(_, arg, _) => process(arg)
                  case _ => lastWords(s"Expected Fld at index $idx")
                
                idx -> (new BlockMemberSymbol(argName, Nil), arg)
              }.toMap
              
              val termDefs = memberSymbols.map { case (idx, (memberSym, arg)) =>
                val resSym = FlowSymbol(s"result of ${memberSym.nme}")
                
                TermDefinition(
                  owner = None,
                  k = syntax.ImmutVal,
                  sym = memberSym,
                  params = Nil,
                  tparams = None,
                  sign = None,
                  body = Some(arg),
                  resSym = resSym,
                  flags = TermDefFlags(false),
                  annotations = Nil
                )
              }.toList
              
              val newFields = fields.zipWithIndex.map {
                case (field @ Fld(flags, _, asc), idx) if memberSymbols.contains(idx) =>
                  val (memberSym, _) = memberSymbols(idx)
                  Fld(flags, memberSym.ref(), asc)
                
                case (field @ Fld(flags, _, asc), idx) if specialisedIndices.contains(idx) && !memberSymbols.contains(idx) =>
                  val argName = s"${funcSym.nme}_arg$idx"
                  val existingMemberSym = new BlockMemberSymbol(argName, Nil)
                  Fld(flags, existingMemberSym.ref(), asc)
                
                case (field, _) => 
                  field match
                    case Fld(flags, arg, asc) => Fld(flags, process(arg), asc)
                    case other => other
              }
  
              val specPoints = specialisedIndices.flatMap { idx =>
                specialisationPoints.values.find(sp => 
                  sp.parentFunctionSym == funcSym && 
                  specialisationPoints.values.filter(_.parentFunctionSym == funcSym).toList.indexWhere(_.paramSym.nme == sp.paramSym.nme) == idx
                )
              }.filter(sp => sp.concreteTypes.nonEmpty)
              
              if specPoints.isEmpty then app else 
                val scrutSyms = specPoints.zipWithIndex.map { case (sp, i) =>
                  val idx = specialisedIndices(i)
                  val (memberSym, _) = memberSymbols(idx)
                  TempSymbol(Some(memberSym.ref()), s"$$scrut${i}")
                }
                
                def generateCombinations(
                  points: List[SpecPoint], 
                  current: List[(SpecPoint, SimpleType)] = Nil
                ): List[List[(SpecPoint, SimpleType)]] = points match
                  case Nil => List(current)
                  case point :: rest =>
                    point.concreteTypes.toList.flatMap { ty =>
                      generateCombinations(rest, current :+ (point -> ty))
                    }
                
                val typeCombinations = generateCombinations(specPoints.toList)
                
                val branches = typeCombinations.map { combination =>
                  val patterns = combination.zip(scrutSyms).map { case ((specPoint, ty), scrutSym) =>
                    (scrutSym.ref(), typeToPattern(ty))
                  }
                  
                  val (firstScrutinee, firstPattern) = patterns.head
                  
                  val innerSplit = patterns.tail.foldRight(Split.Else(app)) { 
                    case ((scrutinee, pattern), innerTail) =>
                      Split.Cons(Branch(scrutinee, pattern, innerTail), Split.End)
                  }
                    
                  Branch(firstScrutinee, firstPattern, innerSplit)
                }
                
                val defaultBranch = Split.End
                
                val splitWithBranches = branches.foldRight(defaultBranch) { (branch, tail) =>
                  Split.Cons(branch, tail)
                }
                
                val letBindings = scrutSyms.zip(specPoints).foldRight(splitWithBranches) { case ((scrutSym, specPoint), split) =>
                  val idx = specialisedIndices(specPoints.toList.indexOf(specPoint))
                  val (memberSym, _) = memberSymbols(idx)
                  Split.Let(scrutSym, memberSym.ref(), split)
                }
                
                val ifLikeTerm = IfLike(syntax.Keyword.`if`, letBindings)(letBindings)
                val finalTerm = Blk(termDefs, ifLikeTerm)
                
                finalTerm
          case _ => app
            
      case tup @ Tup(fields) =>
        val newFields = fields.map {
          case Fld(flags, arg, asc) => Fld(flags, process(arg), asc)
          case other => other
        }
        Tup(newFields)(tup.tree)
      
      case blk @ Blk(stats, res) =>
        implicit val blockCtx = SpecContext()
        
        val funcsToSpecialize = stats.collect {
          case td: TermDefinition if specialisationPoints.values.exists(sp => 
            sp.parentFunctionSym == td.sym && sp.concreteTypes.nonEmpty) => td
        }
        
        funcsToSpecialize.foreach { td =>
          val specPoints = specialisationPoints.values.filter(sp => 
            sp.parentFunctionSym == td.sym && sp.concreteTypes.nonEmpty).toList
          
          def generateCombinations(
            points: List[SpecPoint], 
            current: List[(Symbol, SimpleType)] = Nil
          ): List[List[(Symbol, SimpleType)]] = points match
            case Nil => List(current)
            case point :: rest =>
              point.concreteTypes.toList.flatMap { ty =>
                generateCombinations(rest, current :+ (point.paramSym -> ty))
              }
          
          val typeCombinations = generateCombinations(specPoints)
          
          typeCombinations.foreach { typeCombination =>
            val suffix = typeCombination.map { case (_, ty) => formatTypeForName(ty) }.mkString("_")
            val specialisedName = s"${td.sym.nme}_$suffix"
            log(s"Creating specialised function: $specialisedName")
    
            val specialisedSym = new BlockMemberSymbol(specialisedName, Nil)
            val typeList = typeCombination.map(_._2).toList
            log(s"Generated specialised version ${specialisedName} for ${td.sym.nme} with types [${typeList.mkString(", ")}]")
            
            blockCtx.funcs += TermDefinition(
              td.owner, 
              td.k, 
              specialisedSym, 
              td.params, 
              td.tparams, 
              td.sign, 
              td.body.map(body => process(body)(blockCtx)),  
              td.resSym, 
              td.flags, 
              td.annotations
            )
          }
        }
        
        val newStats = stats.map(stat => processStatement(stat)(blockCtx))
        val newRes = process(res)(blockCtx)
        Blk(newStats ++ blockCtx.funcs, newRes)
      case ifLike @ IfLike(kw, desugared) => IfLike(kw, processSplit(desugared)(using SpecContext()))(ifLike.normalized)
      case Lam(params, body) => Lam(params, process(body)(using SpecContext()))
      case TyApp(lhs, targs) => TyApp(process(lhs)(using SpecContext()), targs.map(arg => process(arg)(using SpecContext())))
      case sel @ Sel(prefix, name) => Sel(process(prefix)(using SpecContext()), name)(sel.sym)
      case sel @ SynthSel(prefix, name) => SynthSel(process(prefix)(using SpecContext()), name)(sel.sym)
      case New(cls, args, rft) => New(process(cls)(using SpecContext()), args.map(arg => process(arg)(using SpecContext())), rft)
      case other => other
  
    def processStatement(stat: Statement)(implicit ctx: SpecContext): Statement = stat match
      case t: Term => process(t)
      
      case LetDecl(sym, annots) => LetDecl(sym, annots)
      case DefineVar(sym, rhs) => DefineVar(sym, process(rhs))
      case td: TermDefinition => 
        td.body match
          case Some(body) => 
            TermDefinition(td.owner, td.k, td.sym, td.params, td.tparams, 
                           td.sign, Some(process(body)), td.resSym, td.flags, td.annotations)
          case None => td
      case other => other
    
    def processSplit(split: Split)(implicit ctx: SpecContext): Split = split match
      case Split.Cons(head, tail) =>
        val Branch(scrutinee, pattern, continuation) = head
        val newScrutinee = process(scrutinee) match
          case ref: Ref => ref
          case other => 
            ErrorReport(msg"Warning: Expected Ref but got ${other.getClass.getSimpleName} in Branch" -> other.toLoc :: Nil)
            scrutinee
        Split.Cons(Branch(newScrutinee, pattern, processSplit(continuation)), processSplit(tail))
      case Split.Let(sym, t, tail) => Split.Let(sym, process(t), processSplit(tail))
      case Split.Else(default) => Split.Else(process(default))
      case Split.End => Split.End

    implicit val rootCtx = SpecContext()
    process(term)(rootCtx)

  def analyzeTermTypes(t: Term): Term =
    specialisationPoints.clear()
    
    val ctx = initialContext
    val resultType = term(t)(using ctx)
    log(s"Result type: ${coalesceType(resultType)}")
    
    specialisationPoints.values.foreach(_.updateFromVars())
    
    if specialisationPoints.nonEmpty then
      log("=== Specialisation Opportunities ===")
      specialisationPoints.values.foreach { specPoint =>
        if specPoint.concreteTypes.nonEmpty then
          log(specPoint.toString)
      }
      log("====================================")
      
      processTree(t)
    else t
  
  def coalesceType(ty: SimpleType): String =
    val recursive = mutable.Map[(VariableState, Boolean), String]()
    
    def go(ty: SimpleType, polar: Boolean, inProcess: Set[(VariableState, Boolean)]): String = ty match
      case Primitive(name) => name
      case Function(lhs, rhs) => s"(${go(lhs, !polar, inProcess)} -> ${go(rhs, polar, inProcess)})"
      case Record(fields) => 
        fields.map { case (name, fieldTy) => 
          s"$name: ${go(fieldTy, polar, inProcess)}" 
        }.mkString("{ ", "; ", " }")
      case ClassType(info) => info.toString
      case SpecialisableType(_, underlying) => s"spec(${go(underlying, polar, inProcess)})"
      case Variable(vs) =>
        val vs_pol = vs -> polar
        
        if inProcess.contains(vs_pol) then recursive.getOrElseUpdate(vs_pol, vs.uniqueName) else
          val bounds = if polar then vs.lowerBounds else vs.upperBounds
          
          if bounds.isEmpty then vs.uniqueName else
            val boundTypes = bounds.map(go(_, polar, inProcess + vs_pol))
            val mrg = if polar then " | " else " & "
            val res = boundTypes.mkString(mrg)
            
            recursive.get(vs_pol).fold(res)(recVar => s"μ$recVar.$res")
    
    go(ty, true, Set.empty)
