package hkmc2
package semantics

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import hkmc2.Message.MessageContext
import hkmc2.semantics.Term.*
import hkmc2.syntax.Tree
import hkmc2.syntax.Tree.Ident
import hkmc2.utils.TraceLogger


class Specialiser(val ectx: Elaborator.Ctx, val tl: TraceLogger)(using Elaborator.State):
  import tl.*
  
  enum SimpleType:
    case Variable(state: VariableState)
    case Primitive(name: Str)
    case Function(lhs: SimpleType, rhs: SimpleType)
    case Record(fields: Ls[(Str, SimpleType)])
    case ClassType(info: ClassInfo)
    case SpecialisableType(underlying: SimpleType)
    
    override def toString: String = this match
      case Variable(state) => s"${state.uniqueName}"
      case Primitive(name) => name
      case Function(lhs, rhs) => s"(${lhs} -> ${rhs})"
      case Record(fields) => fields.map(f => s"${f._1}: ${f._2}").mkString("{ ", "; ", " }")
      case ClassType(info) => info.toString
      case SpecialisableType(underlying) => s"spec[${underlying}]"
  
  import SimpleType.*
  
  object VariableState:
    private var nextIdCounter = 0
    def nextId =
      val id = nextIdCounter
      nextIdCounter += 1
      id
  
  class VariableState(var lowerBounds: Ls[SimpleType] = Nil, var upperBounds: Ls[SimpleType] = Nil):
    private val id = VariableState.nextId
    val uniqueName: String = s"'${('a' + id % 26).toChar}${if id >= 26 then (id / 26).toString else ""}"
  
  def freshVar: Variable = Variable(VariableState())
  
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

  val functionSpecs = mutable.Map[Symbol, Ls[(Symbol, Int)]]()

  def isConcreteType(ty: SimpleType): Boolean = ty match
    case Variable(_) => false
    case Function(lhs, rhs) => isConcreteType(lhs) && isConcreteType(rhs)
    case Record(fields) => fields.forall((_, t) => isConcreteType(t))
    case SpecialisableType(underlying) => isConcreteType(underlying)
    case Primitive(_) => true
    case ClassType(_) => true

  case class SpecialisationTracker(
    paramSym: Symbol,
    functionSym: Symbol,
    paramIndex: Int,
    concreteTypes: mutable.Set[SimpleType] = mutable.Set.empty,
    flowSources: mutable.Set[Variable] = mutable.Set.empty
  ):
    def addConcreteType(ty: SimpleType): Unit =
      if isConcreteType(ty) then
        log(s"Adding concrete type $ty to specialized parameter ${paramSym.nme}")
        concreteTypes += ty
    
    def addFlowSource(variable: Variable): Unit =
      log(s"Adding flow source ${variable.state.uniqueName} to specialized parameter ${paramSym.nme}")
      flowSources += variable
      val concreteBounds = (variable.state.upperBounds ++ variable.state.lowerBounds).filter(isConcreteType)
      concreteBounds.foreach(addConcreteType)
    
    def updateFromVariable(variable: Variable): Unit =
      if flowSources.contains(variable) then
        val newConcreteBounds = (variable.state.upperBounds ++ variable.state.lowerBounds).filter(isConcreteType)
        newConcreteBounds.foreach(addConcreteType)

  case class SpecPoint(
    app: App,
    functionSym: Symbol,
    argumentTypes: mutable.Map[Int, mutable.Set[SimpleType]] = mutable.Map.empty,
    rawArgumentTypes: mutable.Map[Int, SimpleType] = mutable.Map.empty,
  ):
    def recordArgumentType(paramIndex: Int, ty: SimpleType): Unit =
      rawArgumentTypes(paramIndex) = ty
      
      ty match
        case concrete if isConcreteType(concrete) =>
          log(s"Recording concrete argument type $concrete at parameter index $paramIndex for application of ${functionSym.nme}")
          argumentTypes.getOrElseUpdate(paramIndex, mutable.Set.empty) += concrete
        case Variable(vs) =>
          val concreteBounds = (vs.upperBounds ++ vs.lowerBounds).filter(isConcreteType)
          if concreteBounds.nonEmpty then
            log(s"Variable at parameter index $paramIndex has concrete bounds: ${concreteBounds}")
            argumentTypes.getOrElseUpdate(paramIndex, mutable.Set.empty) ++= concreteBounds
          else
            log(s"Variable at parameter index $paramIndex has no concrete bounds yet")
        case _ =>
          log(s"Non-concrete type $ty at parameter index $paramIndex - cannot determine specializations")
    
    def updateArgumentTypes(): Unit =
      rawArgumentTypes.foreach { case (paramIndex, ty) =>
        ty match
          case Variable(vs) =>
            val concreteBounds = (vs.upperBounds ++ vs.lowerBounds).filter(isConcreteType)
            if concreteBounds.nonEmpty then
              log(s"Updating call site: Variable at parameter index $paramIndex now has concrete bounds: ${concreteBounds}")
              argumentTypes.getOrElseUpdate(paramIndex, mutable.Set.empty) ++= concreteBounds
          case concrete if isConcreteType(concrete) =>
            argumentTypes.getOrElseUpdate(paramIndex, mutable.Set.empty) += concrete
          case _ => ()
      }
    
    def getSpecialisations: Ls[Ls[SimpleType]] =
      if argumentTypes.isEmpty then Nil
      else
        val specializedIndices = argumentTypes.keys.toList.sorted
        val paramTypeSets = specializedIndices.map(i => argumentTypes(i).toList)
        
        def cartesianProduct(sets: Ls[Ls[SimpleType]]): Ls[Ls[SimpleType]] = sets match
          case Nil => Ls(Nil)
          case head :: tail =>
            val tailProduct = cartesianProduct(tail)
            head.flatMap(h => tailProduct.map(h :: _))
        
        cartesianProduct(paramTypeSets).filter(_.nonEmpty)
    
    override def toString: String = 
      val specialisations = getSpecialisations
      val loc = app.tree match
        case Tree.DummyApp => "unknown location"
        case _ => app.toLoc.map(_.toString).getOrElse("unknown location")
      if specialisations.isEmpty then
        s"${functionSym.nme} at $loc cannot be specialized (no concrete argument types)"
      else
        val specParamInfo = functionSpecs.get(functionSym).getOrElse(Nil)
        if specialisations.length == 1 then
          val paramTypeStrs = specialisations.head.zip(specParamInfo).map { case (ty, (paramSym, paramIndex)) =>
            s"${paramSym.nme}: ${coalesceType(ty)}"
          }
          s"${functionSym.nme} at $loc can be specialised for (${paramTypeStrs.mkString(", ")})"
        else
          val specializationStrs = specialisations.map { types =>
            val paramTypeStrs = types.zip(specParamInfo).map { case (ty, (paramSym, paramIndex)) =>
              s"${paramSym.nme}: ${coalesceType(ty)}"
            }
            paramTypeStrs.mkString("(", ", ", ")")
          }
          s"${functionSym.nme} at $loc can be specialised for [${specializationStrs.mkString(", ")}]"

  private val specPoints = mutable.Map[App, SpecPoint]()
  
  val IntType = Primitive("Int")
  val BoolType = Primitive("Bool")
  val StrType = Primitive("Str")
  val UnitType = Primitive("Unit")
  val AnyType = Primitive("Any")
  val NumType = Primitive("Num")
  
  class Ctx(val mapping: Map[Symbol, SimpleType] = Map.empty):
    def get(sym: Symbol): Option[SimpleType] = mapping.get(sym)
    def getOrFresh(sym: Symbol): SimpleType = mapping.getOrElse(sym, freshVar)
    def +(pair: (Symbol, SimpleType)): Ctx = Ctx(mapping + pair)
    def ++(pairs: Iterable[(Symbol, SimpleType)]): Ctx = Ctx(mapping ++ pairs)
    override def toString: String = mapping.map { case (sym, ty) => s"$sym: $ty" }.mkString(", ")
  
  def initialContext(using state: Elaborator.State): Ctx =
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
    
    Ctx(builtinTypes)

  def preprocessSpecialisation(t: Term): Term = 
      trace[Term](s"Preprocessing specialisation for term: ${t.showDbg}", r => s"~> preprocessed"):
        
        def collectSpecialisedFunctions(term: Statement): Unit = term match
          case Blk(stats, res) =>
            stats.foreach(collectSpecialisedFunctions)
            collectSpecialisedFunctions(res)
            
          case td: TermDefinition => val specs = td.params.flatMap(p => p.params).zipWithIndex
            .filter { case (p: Param, _) => p.flags.spec }
            .map((p, idx) => (p.sym, idx))
            
            if specs.nonEmpty then
              log(s"Found function ${td.sym.nme} with specialised parameters: ${specs.map(_._1.nme).mkString(", ")}")
              functionSpecs.update(td.sym, specs)
              
          case cls: ClassDef => cls.body.blk.stats.foreach(collectSpecialisedFunctions)
            
          case _ => term.subStatements.foreach(collectSpecialisedFunctions)
        
        def wrapSpecialisedFunctionValues(term: Term, inCallPosition: Bool = false): Term = term match
          case app @ App(lhs, rhs) =>
            val wrappedLhs = wrapSpecialisedFunctionValues(lhs, inCallPosition = true)
            val wrappedRhs = rhs match
              case Tup(fields) =>
                val wrappedFields = fields.map {
                  case Fld(flags, termArg, asc) => Fld(flags, wrapSpecialisedFunctionValues(termArg, inCallPosition = false), asc)
                  case other => other
                }
                Tup(wrappedFields)(rhs.asInstanceOf[Tup].tree)
              case other => wrapSpecialisedFunctionValues(other, inCallPosition = false)
            
            App(wrappedLhs, wrappedRhs)(app.tree, app.resSym)
            
          case ref @ Ref(sym) if functionSpecs.contains(sym) && !inCallPosition =>
            log(s"Wrapping specialised function ${sym.nme} used as value")
          
            def findFunctionDef(term: Statement): Option[TermDefinition] = term match
              case td: TermDefinition if td.sym == sym => Some(td)
              case Blk(stats, res) => 
                stats.collectFirst { case td: TermDefinition if td.sym == sym => td }
                  .orElse(findFunctionDef(res))
              case cls: ClassDef =>
                cls.body.blk.stats.collectFirst { case td: TermDefinition if td.sym == sym => td }
              case _ => None
            
            findFunctionDef(t) match
              case Some(funcDef) =>
                val allLambdaParams = funcDef.params.zipWithIndex.flatMap { case (paramList, listIndex) =>
                  paramList.params.zipWithIndex.map { case (param, paramIndex) =>
                    val paramName = if funcDef.params.length == 1 then s"_${paramIndex}" else s"_${listIndex}_${paramIndex}"
                    val lambdaParamSym = VarSymbol(Ident(paramName))
                    Param(FldFlags.empty, lambdaParamSym, N)
                  }
                }
                
                if allLambdaParams.nonEmpty then
                  val callArgs = if funcDef.params.length == 1 then
                    val argFields = allLambdaParams.map(param => PlainFld(param.sym.ref()))
                    Tup(argFields)(Tree.DummyTup)
                  else
                    val argFields = allLambdaParams.map(param => PlainFld(param.sym.ref()))
                    Tup(argFields)(Tree.DummyTup)
                  
                  val appSym = FlowSymbol(s"‹wrapped-${sym.nme}-call›")
                  val functionCall = App(ref, callArgs)(Tree.DummyApp, appSym)
                  
                  val paramList = PlainParamList(allLambdaParams)
                  Lam(paramList, functionCall)
                else ref
              case None => ref
                
          case Lam(params, body) =>
            Lam(params, wrapSpecialisedFunctionValues(body, inCallPosition = false))
            
          case IfLike(kw, desugared) =>
            IfLike(kw, wrapSpecialisedSplit(desugared))(IfLike(kw, desugared)(desugared).normalized)
            
          case Blk(stats, res) =>
            val wrappedStats = stats.map {
              case DefineVar(sym, rhs) => DefineVar(sym, wrapSpecialisedFunctionValues(rhs, inCallPosition = false))
              case td: TermDefinition => 
                td.copy(body = td.body.map(wrapSpecialisedFunctionValues(_, inCallPosition = false)))
              case cls: ClassDef =>
                val wrappedBody: Blk = cls.body.blk.copy(
                  stats = cls.body.blk.stats.map {
                    case innerTd: TermDefinition => 
                      innerTd.copy(body = innerTd.body.map(wrapSpecialisedFunctionValues(_, inCallPosition = false)))
                    case other => other
                  },
                  res = wrapSpecialisedFunctionValues(cls.body.blk.res, inCallPosition = false)
                )
                ClassDef(cls.owner, cls.kind, cls.sym, cls.bsym, cls.tparams, cls.paramsOpt, cls.ext, ObjBody(wrappedBody), cls.annotations)
              case t: Term => wrapSpecialisedFunctionValues(t, inCallPosition = false)
              case other => other
            }
            Blk(wrappedStats, wrapSpecialisedFunctionValues(res, inCallPosition = false))
            
          case Sel(prefix, name) =>
            Sel(wrapSpecialisedFunctionValues(prefix, inCallPosition = false), name)(term.asInstanceOf[Sel].sym)
            
          case SynthSel(prefix, name) =>
            SynthSel(wrapSpecialisedFunctionValues(prefix, inCallPosition = false), name)(term.asInstanceOf[SynthSel].sym)
            
          case TyApp(lhs, targs) =>
            TyApp(wrapSpecialisedFunctionValues(lhs, inCallPosition = true), targs.map(wrapSpecialisedFunctionValues(_, inCallPosition = false)))
            
          case New(cls, args, rft) =>
            New(wrapSpecialisedFunctionValues(cls, inCallPosition = true), args.map(wrapSpecialisedFunctionValues(_, inCallPosition = false)), rft)
            
          case Tup(fields) =>
            val wrappedFields = fields.map {
              case Fld(flags, fieldTerm, asc) =>
                Fld(flags, wrapSpecialisedFunctionValues(fieldTerm, inCallPosition = false), asc)
              case other => other
            }
            Tup(wrappedFields)(term.asInstanceOf[Tup].tree)
            
          case other => other
        
        def wrapSpecialisedSplit(split: Split): Split = split match
          case Split.Cons(head, tail) =>
            val Branch(scrutinee, pattern, continuation) = head
            Split.Cons(
              Branch(wrapSpecialisedFunctionValues(scrutinee, inCallPosition = false) match { 
                case ref: Ref => ref 
                case _ => scrutinee 
              }, pattern, wrapSpecialisedSplit(continuation)), 
              wrapSpecialisedSplit(tail)
            )
          case Split.Let(sym, termVal, tail) => 
            Split.Let(sym, wrapSpecialisedFunctionValues(termVal, inCallPosition = false), wrapSpecialisedSplit(tail))
          case Split.Else(default) => 
            Split.Else(wrapSpecialisedFunctionValues(default, inCallPosition = false))
          case Split.End => Split.End
        
        functionSpecs.clear()
        specPoints.clear()
        
        collectSpecialisedFunctions(t)
        if functionSpecs.nonEmpty then wrapSpecialisedFunctionValues(t, inCallPosition = false) else t
  
  def constrain(lhs: SimpleType, rhs: SimpleType)(using cache: mutable.Set[(SimpleType, SimpleType)] = mutable.Set.empty): Unit =
    if cache.contains(lhs -> rhs) then return () else cache += lhs -> rhs
    
    log(s"Constraining ${lhs} <: ${rhs}")
    
    (lhs, rhs) match
      case (SpecialisableType(underlying), other) => constrain(underlying, other)
      case (other, SpecialisableType(underlying)) => constrain(other, underlying)
      case (Primitive(n0), Primitive(n1)) if n0 == n1 => ()
      case (_, Primitive("Any")) => ()
      case (Primitive(n0), Primitive(n1)) if n0 == "Int" && n1 == "Num" => ()
      case (Function(l0, r0), Function(l1, r1)) =>
        constrain(l1, l0)
        constrain(r0, r1)
      case (Record(fs0), Record(fs1)) =>
        fs1.foreach { case (n1, t1) =>
          fs0.find(_._1 == n1) match
            case None => log(s"Error: missing field: $n1 in $lhs")
            case Some((_, t0)) => constrain(t0, t1)
        }
      case (Variable(lhs), Variable(rhs)) if lhs == rhs => ()
      case (Variable(lhs), rhs) =>
        lhs.upperBounds = rhs :: lhs.upperBounds
        lhs.lowerBounds.foreach(constrain(_, rhs))
      case (lhs, Variable(rhs)) =>
        rhs.lowerBounds = lhs :: rhs.lowerBounds
        rhs.upperBounds.foreach(constrain(lhs, _))
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
  
  def term(t: Term)(using ctx: Ctx): SimpleType =
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
        
        lhs.symbol match
          case Some(functionSym) if functionSpecs.contains(functionSym) =>
            log(s"Found application of specialized function: ${functionSym.nme}")
            val specParams = functionSpecs(functionSym)
            val callSiteSpec = specPoints.getOrElseUpdate(app, SpecPoint(app, functionSym))
            
            rhsType match
              case Record(fields) =>
                specParams.foreach { case (paramSym, paramIndex) =>
                  if paramIndex < fields.length then
                    val argType = fields(paramIndex)._2
                    log(s"Recording argument type ${argType} for specialized parameter ${paramSym.nme} at index ${paramIndex}")
                    callSiteSpec.recordArgumentType(paramIndex, argType)
                }
              case singleArgType =>
                specParams.foreach { case (paramSym, paramIndex) =>
                  if paramIndex == 0 then
                    log(s"Recording single argument type ${singleArgType} for specialized parameter ${paramSym.nme}")
                    callSiteSpec.recordArgumentType(paramIndex, singleArgType)
                }
          case _ => log(s"Application of non-specialized function or unknown symbol")
        
        lhsType match
          case Function(Record(namedParams), retType) =>
            rhsType match
              case Record(numericFields) if numericFields.forall(_._1.startsWith("_")) && 
                                           namedParams.length == numericFields.length =>
                log(s"Handling application with named parameters and positional arguments")
                namedParams.zip(numericFields).foreach { 
                  case ((paramName, paramType), (_, argType)) => constrain(argType, paramType)
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
      case Lam(params, body) =>
        log(s"Processing lambda with params: ${params.showDbg}")
        val paramTypes = params.params.map { param =>
          val paramType = freshVar
          param.sym -> paramType
        }.toMap
        
        val lambdaCtx = ctx ++ paramTypes
        val bodyType = term(body)(using lambdaCtx)
        
        if params.params.length == 1 then
          val paramSym = params.params.head.sym
          val paramType = paramTypes.getOrElse(paramSym, freshVar)
          Function(paramType, bodyType)
        else
          val recordType = Record(params.params.map(param => 
            param.sym.nme -> paramTypes.getOrElse(param.sym, freshVar)
          ))
          Function(recordType, bodyType)
      case _ => freshVar
    
    log(s"❁ Type for ${t.showDbg}: ${coalesceType(typed)}")
    typed
  
  def block(b: Blk)(using ctx: Ctx): SimpleType =
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

      case td: TermDefinition =>
        val specs = td.params.flatMap(p => p.params).zipWithIndex.filter{ case (p: Param, _) => p.flags.spec }.map((p, idx) => (p.sym, idx))
        functionSpecs.update(td.sym, specs)
      
      case _ => // Skip other statements including function definitions; they will be processed later
    }
    
    b.stats.foreach {
      case td: TermDefinition =>
        log(s"Processing function definition: ${td.sym.nme}")
        val paramTypes = td.params.flatMap(paramList => 
          paramList.params.zipWithIndex.map { case (param, idx) =>
            val paramType = freshVar
            
            val isSpecialised = param.flags.spec
            log(s"Parameter ${param.sym.nme} of function ${td.sym.nme} has spec=${isSpecialised}")
            
            val finalType = if isSpecialised then SpecialisableType(paramType) else paramType
              
            log(s"Assigned type ${finalType} to parameter ${param.sym.nme}")
            param.sym -> finalType
          }
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
      .replace("(", "")
      .replace(")", "")
      .replace(";", "_")
      .replace(":", "_")
      .replace("|", "Or")
      .replace("&", "And")
      .replace("'", "")
      .replace("μ", "")
      .replace(".", "")
  
  class SpecCtx(
    val funcs: mutable.Buffer[TermDefinition] = mutable.Buffer.empty,
    val typeContext: mutable.Map[Symbol, Set[SimpleType]] = mutable.Map.empty
  ):
    def +(sym: Symbol, ty: SimpleType): SpecCtx =
      typeContext(sym) = typeContext.getOrElse(sym, Set.empty) + ty
      this
    
    def ++(mappings: Iterable[(Symbol, SimpleType)]): SpecCtx =
      mappings.foreach { case (sym, ty) => this + (sym, ty) }
      this
      
    def nest: SpecCtx = new SpecCtx(mutable.Buffer.empty, mutable.Map.empty ++ typeContext)
  
  def toInternalType(ty: SimpleType): Pattern = ty match
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
    case _: Function =>
      val funcSym = ectx.builtins.Function
      val classSel = SynthSel(funcSym.ref(), Ident("class"))(Some(funcSym.asCls.get))
      Pattern.ClassLike(funcSym.asCls.get, classSel, None, false)(Tree.Empty())
    case _ => Pattern.Lit(Tree.BoolLit(true))

  def simpleTypeToTerm(ty: SimpleType): Term = ty match
    case Primitive("Int") => ectx.builtins.Int.ref()
    case Primitive("Bool") => ectx.builtins.Bool.ref() 
    case Primitive("Str") => ectx.builtins.Str.ref()
    case Primitive("Num") => ectx.builtins.Num.ref()
    case Primitive("Unit") => ectx.builtins.Unit.ref()
    case Primitive("Any") => ectx.builtins.Object.ref()
    case ClassType(info) => info.memberSym.ref()
    case Function(lhs, rhs) => FunTy(simpleTypeToTerm(lhs), simpleTypeToTerm(rhs), N)
    case Variable(vs) =>
      val concreteBounds = (vs.upperBounds ++ vs.lowerBounds).filter(isConcreteType)
      if concreteBounds.nonEmpty then simpleTypeToTerm(concreteBounds.head)
      else ectx.builtins.Object.ref()
    case SpecialisableType(underlying) => simpleTypeToTerm(underlying)
    case _ => ectx.builtins.Object.ref()
  
  def process(term: Term)(using ctx: SpecCtx = new SpecCtx()): Term =
    val specialisedFunctions = mutable.Map[String, Symbol]()

    def collectSpecialisedFunctions(t: Statement): Unit = t match
      case Blk(stats, res) =>
        stats.foreach:
          case td: TermDefinition if td.sym.nme.contains('_') && specPoints.values.exists(cs => td.sym.nme.startsWith(s"${cs.functionSym.nme}_")) =>
            log(s"Registering specialised function: ${td.sym.nme}")
            specialisedFunctions(td.sym.nme) = td.sym
          case Blk(innerStats, _) =>
            innerStats.foreach(collectSpecialisedFunctions)
          case _ =>
        collectSpecialisedFunctions(res)
      case _ =>
    
    def go(t: Term): Term = t match
      case app @ App(lhs, rhs @ Tup(fields)) =>
        lhs match
          case Ref(funcSym) =>
            specPoints.get(app) match
              case None =>
                App(lhs, Tup(fields.map {
                  case Fld(flags, arg, asc) => Fld(flags, go(arg), asc)
                  case other => other
                })(rhs.tree))(app.tree, app.resSym)
              
              case Some(callSiteSpec) =>
                val specializations = callSiteSpec.getSpecialisations
                val specParams = functionSpecs.getOrElse(funcSym, Nil)
                
                if specializations.isEmpty then
                  log(s"No concrete specializations for ${funcSym.nme}")
                  App(lhs, Tup(fields.map {
                    case Fld(flags, arg, asc) => Fld(flags, go(arg), asc)
                    case other => other
                  })(rhs.tree))(app.tree, app.resSym)
                else
                  log(s"Found ${specializations.length} specializations for ${funcSym.nme}")
                  
                  val scrutSyms = specParams.map { case (paramSym, paramIndex) =>
                    val arg = if paramIndex < fields.length then
                      fields(paramIndex) match
                        case Fld(_, arg, _) => go(arg)
                        case _ => lastWords(s"Expected Fld at param index $paramIndex")
                    else
                      lastWords(s"Parameter index $paramIndex out of bounds for ${fields.length} fields")
                    
                    TempSymbol(Some(arg), s"${funcSym.nme}_param${paramIndex}")
                  }
                  
                  val newFields = fields.zipWithIndex.map { case (field, idx) =>
                    specParams.find(_._2 == idx) match
                      case Some((paramSym, _)) =>
                        val scrutIndex = specParams.indexWhere(_._1 == paramSym)
                        field match
                          case Fld(flags, _, asc) => Fld(flags, scrutSyms(scrutIndex).ref(), asc)
                          case other => other
                      case None =>
                        field match
                          case Fld(flags, arg, asc) => Fld(flags, go(arg), asc)
                          case other => other
                  }
                  
                  // Code to build nice branches for application selection
                  sealed trait TypeBranchNode
                  case class LeafNode(term: Term) extends TypeBranchNode
                  case class BranchNode(branches: Map[SimpleType, (Int, TypeBranchNode)]) extends TypeBranchNode
                  
                  def buildBranchTree(specs: List[List[SimpleType]], specIndices: List[Int]): TypeBranchNode =
                    if specs.isEmpty then return LeafNode(App(lhs, Tup(newFields)(rhs.tree))(app.tree, app.resSym))
                    
                    if specIndices.isEmpty then
                      val suffix = specs.head.map(formatTypeForName).mkString("_")
                      val specialisedName = s"${funcSym.nme}_$suffix"
                      
                      specialisedFunctions.get(specialisedName) match
                        case Some(specialisedSym) =>
                          log(s"Using specialised function $specialisedName")
                          val specialisedRef = Ref(specialisedSym)(lhs.asInstanceOf[Ref].tree, 0)
                          LeafNode(App(specialisedRef, Tup(newFields)(rhs.tree))(app.tree, app.resSym))
                        case None =>
                          log(s"Warning: Specialised function $specialisedName not found")
                          LeafNode(App(lhs, Tup(newFields)(rhs.tree))(app.tree, app.resSym))
                    else
                      val specIdx = specIndices.head
                      val nextSpecIndices = specIndices.tail
                      
                      val groupedByParamType = specs.groupBy(types => 
                        if specIdx < types.length then types(specIdx) else null
                      ).filter(_._1 != null)
                      
                      val branches = groupedByParamType.map { case (paramType, typeSpecs) =>
                        val nextNode = buildBranchTree(typeSpecs, nextSpecIndices)
                        paramType -> (specIdx, nextNode)
                      }
                      
                      BranchNode(branches)
                  
                  def branchTreeToSplit(node: TypeBranchNode, fallback: Split): Split = node match 
                    case LeafNode(term) => Split.Else(term)
                    case BranchNode(branches) =>
                      branches.foldLeft(fallback) { case (acc, (ty, (specIdx, childNode))) =>
                        val pattern = toInternalType(ty)
                        Split.Cons(
                          Branch(scrutSyms(specIdx).ref(), pattern, branchTreeToSplit(childNode, Split.End)), 
                          acc
                        )
                      }
                  
                  val specIndices = (0 until specParams.length).toList
                  val branchTree = buildBranchTree(specializations, specIndices)
                  val optimizedBranching = branchTreeToSplit(branchTree, Split.End)
                  val letBindings = scrutSyms.foldRight(optimizedBranching) { (scrutSym, split) =>
                    Split.Let(scrutSym, scrutSym.trm.getOrElse(Term.Error), split)
                  }
      
                  IfLike(syntax.Keyword.`if`, letBindings)(letBindings)
          case _ => 
            App(go(lhs), go(rhs))(app.tree, app.resSym)
      
      case tup @ Tup(fields) =>
        val newFields = fields.map {
          case Fld(flags, arg, asc) => Fld(flags, go(arg), asc)
          case other => other
        }
        Tup(newFields)(tup.tree)
      
      case blk @ Blk(stats, res) =>
        val blockCtx = ctx.nest
        
        val funcsToSpecialise = stats.collect {
          case td: TermDefinition if functionSpecs.contains(td.sym) &&
                                    specPoints.values.exists(cs => cs.functionSym == td.sym && cs.getSpecialisations.nonEmpty) => td
        }
        
        val specialisations = mutable.Map[TermDefinition, List[TermDefinition]]()
        
        funcsToSpecialise.foreach { td =>
          val specParams = functionSpecs.getOrElse(td.sym, Nil)
          val relevantCallSites = specPoints.values.filter(_.functionSym == td.sym).toList
          
          log(s"Function ${td.sym.nme} has ${specParams.length} specializable parameters and ${relevantCallSites.length} call sites")
          
          val allSpecializations = relevantCallSites.flatMap(_.getSpecialisations).distinct
          
          allSpecializations.foreach { typeVector =>
            val suffix = typeVector.map(formatTypeForName).mkString("_")
            val specialisedName = s"${td.sym.nme}_$suffix"
            log(s"Creating specialised function: $specialisedName")
            
            val specialisedSym = new BlockMemberSymbol(specialisedName, Nil)
            specialisedFunctions(specialisedName) = specialisedSym

            val paramTypeMap = typeVector.zip(specParams).map { case (ty, (paramSym, paramIndex)) =>
              paramSym -> ty
            }.toMap
            
            val specialisedBody = td.body match
              case Some(body) => 
                log(s"Processing body of $specialisedName with specialized parameter types")
                
                val bodySpecialiser = new Specialiser(ectx, tl)

                def convertSimpleType(ty: SimpleType, targetSpecialiser: Specialiser): targetSpecialiser.SimpleType =
                  ty match
                    case Primitive(name) => targetSpecialiser.SimpleType.Primitive(name)
                    case Variable(state) => 
                      val concreteBounds = state.upperBounds.filter(isConcreteType) ++ state.lowerBounds.filter(isConcreteType)
                      if concreteBounds.nonEmpty then
                        convertSimpleType(concreteBounds.head, targetSpecialiser)
                      else
                        targetSpecialiser.freshVar
                    case Function(lhs, rhs) => 
                      targetSpecialiser.SimpleType.Function(
                        convertSimpleType(lhs, targetSpecialiser), 
                        convertSimpleType(rhs, targetSpecialiser)
                      )
                    case Record(fields) => 
                      targetSpecialiser.SimpleType.Record(fields.map((name, fieldTy) => 
                        name -> convertSimpleType(fieldTy, targetSpecialiser)
                      ))
                    case ClassType(info) => 
                      targetSpecialiser.SimpleType.ClassType(targetSpecialiser.ClassInfo(
                        info.sym, info.memberSym, info.params, 
                        info.supers.map(convertSimpleType(_, targetSpecialiser)),
                        info.members.map((k, v) => k -> convertSimpleType(v, targetSpecialiser)),
                        info.fields.map((k, v) => k -> convertSimpleType(v, targetSpecialiser))
                      ))
                    case SpecialisableType(underlying) => 
                      targetSpecialiser.SimpleType.SpecialisableType(convertSimpleType(underlying, targetSpecialiser))
                

                val baseCtx = bodySpecialiser.initialContext
                val specializedCtx = baseCtx ++ paramTypeMap.map((k, v) => (k, convertSimpleType(v, bodySpecialiser)))
                
                Some(bodySpecialiser.specialise(body)(using specializedCtx))
              case None => None

            val specializedParams = td.params.map { paramList =>
              val updatedParams = paramList.params.map { param =>
                paramTypeMap.get(param.sym) match
                  case Some(specialisedType) =>
                    log(s"Updating parameter ${param.sym.nme} type from generic to ${specialisedType}")
                    param.copy(sign = Some(simpleTypeToTerm(specialisedType)))
                  case None => param
              }
              paramList.copy(params = updatedParams)
            }
            
            val specializedFn = TermDefinition(
              td.owner, 
              td.k, 
              specialisedSym, 
              specializedParams,
              td.tparams, 
              td.sign, 
              specialisedBody,  
              td.resSym, 
              td.flags, 
              td.annotations
            )
            
            specialisations(td) = specializedFn :: specialisations.getOrElse(td, Nil)
          }
        }
        
        val newStats = stats.flatMap { stat => stat match
          case td: TermDefinition if specialisations.contains(td) => 
            processStatement(td) :: specialisations(td).map(processStatement)
          case _ => List(processStatement(stat))
        }
        
        val newRes = go(res)
        Blk(newStats, newRes) 

      case ifLike @ IfLike(kw, desugared) => IfLike(kw, processSplit(desugared))(ifLike.normalized)
      case Lam(params, body) => Lam(params, go(body))
      case TyApp(lhs, targs) => TyApp(go(lhs), targs.map(go))
      case sel @ Sel(prefix, name) => Sel(go(prefix), name)(sel.sym)
      case sel @ SynthSel(prefix, name) => SynthSel(go(prefix), name)(sel.sym)
      case New(cls, args, rft) => New(go(cls), args.map(go), rft)
      case other => other
    
    def processStatement(stat: Statement): Statement = stat match
      case t: Term => go(t)
      case LetDecl(sym, annots) => LetDecl(sym, annots)
      case DefineVar(sym, rhs) => DefineVar(sym, go(rhs))
      case td: TermDefinition => 
        val hasSpecParams = td.params.flatMap(_.params).exists(_.flags.spec)
        td.copy(body = td.body.map {
          case b: Blk if !hasSpecParams => go(b)
          case b => b
        })
      case other => other
    
    def processSplit(split: Split): Split = split match
      case Split.Cons(head, tail) =>
        val Branch(scrutinee, pattern, continuation) = head
        val newScrutinee = go(scrutinee) match
          case ref: Ref => ref
          case other => scrutinee
        Split.Cons(Branch(newScrutinee, pattern, processSplit(continuation)), processSplit(tail))
      case Split.Let(sym, t, tail) => Split.Let(sym, go(t), processSplit(tail))
      case Split.Else(default) => Split.Else(go(default))
      case Split.End => Split.End
    
    collectSpecialisedFunctions(term)
    go(term)
  
  def specialise(t: Term)(using ctx: Ctx): Term =
    val nt = preprocessSpecialisation(t)
    val resultType = term(nt)
    log(s"Result type: ${coalesceType(resultType)}")

    log(s"Function details:\n${functionSpecs.map((f, ps) => s"Function $f has ${if !ps.nonEmpty then "no " else ""}specialisable parameters${ps.map((n, i) => s"$n at index $i").mkString(": ", ", ", ".")}").mkString("\n")}")
    
    log("Updating call sites with resolved types...")
    specPoints.values.foreach(_.updateArgumentTypes())
    
    if specPoints.nonEmpty then
      log("=== Specialisation Opportunities ===")
      specPoints.values.filter(sp => functionSpecs.get(sp.functionSym).getOrElse(Nil).nonEmpty).foreach { specPoint =>
        log(specPoint.toString)
      }
      log("====================================")
      process(nt)
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
      case SpecialisableType(underlying) => s"spec(${go(underlying, polar, inProcess)})"
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

  def topLevel(t: Term): Term = 
    specPoints.clear()
    functionSpecs.clear()
    specialise(t)(using initialContext)
