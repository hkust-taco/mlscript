package hkmc2
package semantics

import scala.collection.immutable.Queue
import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import hkmc2.Message.MessageContext
import hkmc2.semantics.Elaborator.*
import hkmc2.semantics.Split.{Let, Else}
import hkmc2.semantics.Term.*
import hkmc2.syntax.Tree
import hkmc2.syntax.Tree.{Ident, IntLit, StrLit, UnitLit}
import hkmc2.utils.TraceLogger

object Specialiser:
  transparent inline def ctx(using Ctx): Ctx = summon
  transparent inline def state(using Elaborator.State): Elaborator.State = summon
  private transparent inline def wq(using Queue[TermDefinition]): Queue[TermDefinition] = summon

  import hkmc2.semantics.Elaborator.Ctx.Elem

  extension (ctx: Ctx)
    def elem_+(local: Str -> Ctx.Elem): Ctx = ctx.copy(ctx.outer, env = ctx.env + local)
    def map(f: Str -> Ctx.Elem => Str -> Ctx.Elem): Ctx =
      ctx.copy(parent = ctx.parent.map(_.map(f)), env = ctx.env.map(f))
    def showDbg: Str = ctx.env.map((k, v) => s"$k -> ${v}").mkString(", ")

  final case class Binding(val sym: Symbol, val typ: Opt[Ref]) extends Elem:
    def nme: Str = sym.nme
    def symbol: Opt[Symbol] = S(sym)
    def ref(id: Ident)(using Elaborator.State): Term = ??? // TODO: Make own context; this is dumb

  final case class TD(val td: TermDefinition) extends Elem:
    def nme: Str = td.sym.nme
    def symbol: Opt[Symbol] = S(td.sym)
    def ref(id: Ident = Ident(""))(using Elaborator.State): Term = td.sym.ref()

  object Spec:
    val empty: Spec = Spec(Nil)
  final case class Spec(val tys: Ls[Symbol -> (Ref | SynthSel)])

  type Ctxl[T] = Ctx ?=> T
  type Apps = Map[Str, Ls[Spec]]

class Specialiser(val tl: TraceLogger)(using Raise, Elaborator.State):
  import tl.*
  import Specialiser.*

  private val tInt: Ref = Ref(TopLevelSymbol("import#Prelude"))(Ident("Int"), 0)
  private val tStr: Ref = Ref(TopLevelSymbol("import#Prelude"))(Ident("Str"), 0)
  private val tUnit: Ref = Ref(TopLevelSymbol("import#Prelude"))(Ident("Unit"), 0)

  def block(blk: Blk, apps: Apps): Ctxl[(Blk, Apps)] = trace(s"Specialising block ${blk.showDbg}"):
    @annotation.tailrec
    def go(sts: Ls[Statement], acc: Ls[Statement], apps: Apps): Ctxl[(Blk, Apps)] =
      log(s"Specialising ${sts.headOption.map(_.showDbg).getOrElse("block end. \n")}")
      sts match
        case (b: Blk) :: sts =>
          val (newBlk, lowerApps) = block(b, apps)(using ctx.nest(N))
          go(sts, newBlk :: acc, lowerApps)
        case (t: Term) :: sts =>
          val (newTerm, lowerApps) = term(t, apps)(using ctx.nest(N))
          go(sts, newTerm :: acc, lowerApps)

        case (l: LetDecl) :: sts =>
          ctx.get(l.sym.nme) match
            case S(_) => go(sts, l :: acc, apps)
            case N => go(sts, l :: acc, apps)(using ctx elem_+ l.sym.nme -> Binding(l.sym, N))
        case (d: DefineVar) :: sts =>
          val ntyp: Opt[Ref] = d.rhs match
            case Lit(lit) => lit.asTree match
              case _: IntLit => S(tInt)
              case _: StrLit => S(tStr)
              case _: UnitLit => S(tUnit)
              case _ => N
            case _ => N // TODO: Infer type from other bindings; tuple type inference
          ctx.map((k, v) => if k == d.sym.nme then k -> Binding(d.sym, ntyp) else k -> v).givenIn:
            go(sts, d :: acc, apps)
        case (td : TermDefinition) :: sts => go(sts, acc, apps)(using ctx elem_+ td.sym.nme -> TD(td))

        case (i: Import) :: sts => go(sts, i :: acc, apps)
        case (md @ ModuleDef(_, sym, _, _, _, _, _, bdy, _)) :: sts =>
          val (newBlk, lowerApps) = block(bdy.blk, apps)(using ctx.nest(S(sym)))
          go(sts, md.copy(body = bdy.copy(blk = newBlk)) :: acc, lowerApps)
        case (pd @ PatternDef(_, sym, _, _, _, bdy, _)) :: sts =>
          val (newBlk, lowerApps) = block(bdy.blk, apps)(using ctx.nest(S(sym)))
          go(sts, pd.copy(body = bdy.copy(blk = newBlk)) :: acc, lowerApps)
        case (p @ ClassDef.Parameterized(_, _, sym, _, _, _, _, bdy, _, _)) :: sts =>
          val (newBlk, lowerApps) = block(bdy.blk, apps)(using ctx.nest(S(sym)))
          go(sts, p.copy(body = bdy.copy(blk = newBlk)) :: acc, lowerApps)
        case (pl @ ClassDef.Plain(_, _, sym, _, _, _, bdy, _, _)) :: sts =>
          val (newBlk, lowerApps) = block(bdy.blk, apps)(using ctx.nest(S(sym)))
          go(sts, pl.copy(body = bdy.copy(blk = newBlk)) :: acc, lowerApps)
        case (t: TypeLikeDef) :: sts => go(sts, t :: acc, apps)

        case Nil =>
          log(s"Res: ${blk.res.showDbg}")
          val (newRes, lowerApps) = term(blk.res, apps)

          val tds = ctx.env.collect{case (_, v: TD) => v.td}.toList
          log(s"Ctx: ${ctx.showDbg}")
          log(s"Term definitions: ${tds}")
          log(s"Applications: ${lowerApps}")

          val wq = tds.map(td => td -> lowerApps.getOrElse(td.sym.nme, Nil)).foldLeft(Queue.empty[TermDefinition -> Ls[Spec]]):
            (acc, v) => acc.enqueue(v)
          log(s"Queue: ${wq}")

          val newStats = processQueue(wq)(using ctx, tds)

          (Blk(tds ::: newStats ::: acc.reverse, newRes), lowerApps)

    def processQueue(q: Queue[TermDefinition -> Ls[Spec]])(using ctx: Ctx, tds: Ls[TermDefinition]): Ls[Statement] = q match
      case q if q.isEmpty => Nil
      case q => 
        log(s"Processing queue: ${q}")
        val ((td, typs), nq) = q.dequeue
        log(s"Processing ${td.sym} with ${typs}")
        val (speccedDefs, nnq) = typs.foldLeft((Ls.empty[Statement], nq))((acc, app) =>
          val name = app.tys.map {
            case (_, s: SynthSel) => s.nme
            case (_, r: Ref) => r.tree.name
          }.mkString(td.sym.nme + "_", "_", "")
          val (nt, apps) = td.body match // FIXME
            case S(body) => term(body, Map.empty)(using ctx elem_++ app.tys.foldLeft(Ls.empty[Str -> Binding])((acc, v) => v._2 match
              case r: Ref => v._1.nme -> Binding(v._1, S(r)) :: acc
            )).mapFirst(S(_))
            case N => (N, Nil)
          log(s"Chain specialising ${td.sym} containing ${apps}")
          val newSpeccs = apps.foldLeft(Ls.empty[TermDefinition -> Ls[Spec]])((acc, v) => tds.find(_.sym.nme == v._1).map(_ -> v._2 :: acc).getOrElse(acc))
          (td.copy(sym = BlockMemberSymbol(name, td.sym.trees), body = nt) :: acc._1, nq.enqueueAll(newSpeccs)))
        speccedDefs ++ processQueue(nnq)


    go(blk.stats, Nil, apps)

  def term(t: Term, apps: Apps): Ctxl[(Term, Apps)] = trace(s"Specialising term ${t.showDbg}"):
    t match
      case app @ App(lhs, rhs) =>
        lhs match
          case s @ SynthSel(_, n) => 
            val name = n.name
            log(s"Ctx: ${ctx.showDbg}")
            val params = ctx.get(name).map { case td: TD => td.td.params }.getOrElse(Nil)
            val typ: Spec = rhs match
              case Tup(fields) => fields.zip(params.head.params).foldLeft(Spec(Nil)):
                (acc, fieldPair) => fieldPair._1 match
                case Fld(_, Lit(lit), _) => lit.asTree match
                  case _: IntLit => acc.copy(tys = (fieldPair._2.sym -> tInt) :: acc.tys)
                  case _: StrLit => acc.copy(tys = (fieldPair._2.sym -> tStr) :: acc.tys)
                  case _: UnitLit => acc.copy(tys = (fieldPair._2.sym -> tUnit) :: acc.tys)
                  case _ => acc
                case Fld(_, Ref(r), _) => acc.copy(tys = fieldPair._2.sym -> ctx.get(r.nme).flatMap(_.asInstanceOf[Binding].typ).get :: acc.tys) // FIXME
                case _ => acc
              case _ => Spec(Nil)

            // log(s"Found application of ${name} with types ${typ.showDbg}")
            val newApps = apps + (name -> (typ :: apps.getOrElse(name, Nil).filterNot(_ == typ)))

            val newName: Ident = Ident(name + typ.tys.map{ case (_, r: Ref) => r.tree.name }.mkString("_", "_", ""))
            val specApp: App = app.copy(lhs = s.copy(nme = newName)(s.sym))(app.tree, app.resSym)
            (specApp, newApps)
          // TODO: Fix these two
          case r: Ref => 
            val name = r.sym.nme
            val typ: Opt[Ref] = rhs match
              case Tup(fields) => fields.head match // FIXME: This can obviously be more than primitives
                case Fld(_, Lit(lit), _) => lit.asTree match
                  case _: IntLit => S(tInt)
                  case _: StrLit => S(tStr)
                  case _: UnitLit => S(tUnit)
                  case _ => N
                case Fld(_, Ref(r), _) => ctx.get(r.nme).flatMap(_.asInstanceOf[Binding].typ)
                case _ => N
              case _ => N

            log(s"Found application of ${name} with type ${typ.map(_.tree.name).getOrElse("error")}")
            val newApps = typ match
              case Some(t) => apps + (name -> (t :: apps.getOrElse(name, Nil).filterNot(_ == t)))
              case N => apps

            // val newName: Ident = Ident(name + "_" + typ.map(_.tree.name).getOrElse("oops"))
            // (specApp, newApps)
            (t, apps)
          case _: Sel => (t, apps)
          case _ =>
            raise(ErrorReport(msg"I messed up :(" -> t.toLoc :: Nil)) // FIXME
            (t, apps)
      case il @ IfLike(_, desug) => desug match
        case Let(s, b, t) =>
          val (nb, lowerApps) = term(b, apps)
          (il.copy(desugared = Let(s, nb, t))(il.normalized), lowerApps)
        case Else(d) =>
          val (nd, lowerApps) = term(d, apps)
          (il.copy(desugared = Else(nd))(il.normalized), lowerApps)
        case _ => (il, apps)
      case Lam(params, body) => // TODO: specialise the lambda
        val (newBody, newApps) = term(body, apps)
        (Lam(params, newBody), newApps)
      case Forall(tvs, outer, body) => // FIXME
        val (newTerm, newApps) = term(body, apps)
        (Forall(tvs, outer, newTerm), newApps)
      case Quoted(b) =>
        val (newTerm, newApps) = term(b, apps)
        (Quoted(newTerm), newApps)
      case Unquoted(b) =>
        val (newTerm, newApps) = term(b, apps)
        (Unquoted(newTerm), newApps)
      case Region(name, body) =>
        val (newTerm, newApps) = term(body, apps)
        (Region(name, newTerm), newApps)
      case Deref(ref) =>
        val (newTerm, newApps) = term(ref, apps)
        (Deref(newTerm), newApps)
      case Ret(expr) =>
        val (newTerm, newApps) = term(expr, apps)
        (Ret(newTerm), newApps)
      case Throw(expr) =>
        val (newTerm, newApps) = term(expr, apps)
        (Throw(newTerm), newApps)
      case Try(body, finallyDo) =>
        val (b1, apps1) = term(body, apps)
        val (b2, apps2) = term(finallyDo, apps1)
        (Try(b1, b2), apps2)
      case b: Blk => block(b, apps)
      case _ => (t, apps) // TODO: Handle the few other term types

  def topLevel(b: Blk): Blk = b
    // block(b, Map.empty)(using Ctx.empty)._1

end Specialiser

class SimpleSub(val tl: TraceLogger):
  import tl.*

  case class ClassInfo(
    sym: ClassSymbol,
    params: Ls[Str] = Nil,
    supers: Ls[SimpleType] = Nil,
    members: Map[Str, SimpleType] = Map.empty,
    fields: Map[Str, SimpleType] = Map.empty
  ):
    override def toString: String = 
      val superStr = if supers.isEmpty then "" else 
        s" extends ${supers.mkString(" with ")}"
      val fieldsStr = if fields.isEmpty then "" else 
        fields.map { case (n, t) => s"val $n: $t" }.mkString(", ")
      val membersStr = members.map { case (n, t) => s"$n: $t" }.mkString(", ")
      val contentStr = (if fieldsStr.nonEmpty && membersStr.nonEmpty then s"$fieldsStr; $membersStr" 
                       else fieldsStr + membersStr)
      s"class ${sym.nme}$superStr { $contentStr }"

  enum SimpleType:
    case Variable(state: VariableState)
    case Primitive(name: Str)
    case Function(lhs: SimpleType, rhs: SimpleType)
    case Record(fields: Ls[(Str, SimpleType)])
    case ClassType(info: ClassInfo)
    
    override def toString: String = this match
      case Variable(state) => s"${state.uniqueName}"
      case Primitive(name) => name
      case Function(lhs, rhs) => s"(${lhs} -> ${rhs})"
      case Record(fields) => fields.map(f => s"${f._1}: ${f._2}").mkString("{ ", "; ", " }")
      case ClassType(info) => info.toString

  import SimpleType.*
  
  class VariableState(var lowerBounds: Ls[SimpleType] = Nil, var upperBounds: Ls[SimpleType] = Nil):
    private val id = VariableState.nextId
    val uniqueName: String = s"'${('a' + id % 26).toChar}${if id >= 26 then (id / 26).toString else ""}"
  
  object VariableState:
    private var nextIdCounter = 0
    def nextId =
      val id = nextIdCounter
      nextIdCounter += 1
      id
  
  class TypeContext(val mapping: Map[Symbol, SimpleType] = Map.empty):
    def get(sym: Symbol): Option[SimpleType] = mapping.get(sym)
    def getOrFresh(sym: Symbol): SimpleType = mapping.getOrElse(sym, freshVar())
    def +(pair: (Symbol, SimpleType)): TypeContext = TypeContext(mapping + pair)
    def ++(pairs: Iterable[(Symbol, SimpleType)]): TypeContext = TypeContext(mapping ++ pairs)
    override def toString: String = mapping.map { case (sym, ty) => s"$sym: $ty" }.mkString(", ")
  
  val IntType = Primitive("Int")
  val BoolType = Primitive("Bool")
  val StrType = Primitive("Str")
  val UnitType = Primitive("Unit")
  val AnyType = Primitive("Any")
  val NumType = Primitive("Num")
  
  def freshVar(): Variable = Variable(VariableState())
  
  def createInitialContext()(using state: Elaborator.State): TypeContext =
    val builtinTypes = Map(
      state.builtinOpsMap.values.map { sym =>
        val opType = sym.nme match
          case "+" | "-" | "*" | "/" | "%" => 
            Function(Record(Ls("_0" -> NumType, "_1" -> NumType)), NumType)
          case "==" | "!=" | "===" | "!==" | "<" | "<=" | ">" | ">=" =>
            val tv = freshVar()
            Function(Record(Ls("_0" -> tv, "_1" -> tv)), BoolType)
          case "&&" | "||" => 
            Function(Record(Ls("_0" -> BoolType, "_1" -> BoolType)), BoolType)
          case "!" => Function(BoolType, BoolType)
          case "~" => Function(IntType, IntType)
          case "typeof" => Function(AnyType, StrType)
          case _ => freshVar()
        
        sym.asInstanceOf[Symbol] -> opType
      }.toSeq*
    )
    
    TypeContext(builtinTypes)
    
  def constrain(lhs: SimpleType, rhs: SimpleType)(using cache: mutable.Set[(SimpleType, SimpleType)] = mutable.Set.empty): Unit =
    if cache.contains(lhs -> rhs) then return () else cache += lhs -> rhs
    
    log(s"Constraining ${lhs} <: ${rhs}")
    
    (lhs, rhs) match
      case (Primitive(n0), Primitive(n1)) if n0 == n1 => ()
      case (Function(l0, r0), Function(l1, r1)) =>
        constrain(l1, l0)
        constrain(r0, r1)
      case (Record(fs0), Record(fs1)) =>
        fs1.foreach { case (n1, t1) =>
          fs0.find(_._1 == n1) match
            case None => 
              log(s"Error: missing field: $n1 in $lhs")
            case Some((_, t0)) => 
              constrain(t0, t1)
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
          val fieldType = info.fields.getOrElse(info.params.head, freshVar())
          constrain(paramType, fieldType)
          constrain(ClassType(info), resultType)
        else if info.params.isEmpty then
          log(s"Error: class ${info.sym.nme} has no parameters but is used with arguments")
        else
          paramType match
            case Record(fields) if fields.size == info.params.size =>
              info.params.zip(fields).foreach { case (paramName, (_, fieldType)) =>
                val classFieldType = info.fields.getOrElse(paramName, freshVar())
                constrain(fieldType, classFieldType)
              }
              constrain(ClassType(info), resultType)
            case _ =>
              log(s"Error: class ${info.sym.nme} expects ${info.params.length} parameters")
      case _ => 
        log(s"Error: cannot constrain $lhs <: $rhs")
  
  def typeTerm(term: Term)(using ctx: TypeContext): SimpleType =
    log(s"Typing term: ${term.showDbg}")
    
    term match
      case Error | Missing => 
        freshVar()
      
      case UnitVal() => 
        UnitType

      case Lit(lit) => lit match
        case Tree.IntLit(_) => IntType
        case Tree.StrLit(_) => StrType
        case Tree.BoolLit(_) => BoolType
        case Tree.UnitLit(_) => UnitType
        case _ => Primitive("Unknown")
      
      case app @ App(lhs, rhs) =>
        val resultType = freshVar()
        val lhsType = typeTerm(lhs)
        val rhsType = rhs match
          case Tup(fields) if fields.length > 1 =>
            Record(fields.zipWithIndex.map { 
              case (Fld(_, term, _), idx) => s"_${idx}" -> typeTerm(term)
              case (_, idx) => s"_${idx}" -> freshVar()
            })
          case Tup(fields) if fields.length == 1 =>
            fields.head match
              case Fld(_, term, _) => typeTerm(term)
              case _ => freshVar()
          case _ => typeTerm(rhs)
        
        constrain(lhsType, Function(rhsType, resultType))
        resultType
      
      case New(cls, args, _) =>
        val clsType = typeTerm(cls)
        val argTypes = args.map(typeTerm)
        
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
              val paramType = info.fields.getOrElse(info.params.head, freshVar())
              Function(paramType, symType)
            else
              val recordFields = info.params.map { paramName =>
                val fieldType = info.fields.getOrElse(paramName, freshVar())
                paramName -> fieldType
              }
              Function(Record(recordFields), symType)
          case _ => symType
      
      case Sel(prefix, name) =>
        val prefixType = typeTerm(prefix)
        
        prefixType match
          case ClassType(classInfo) =>
            classInfo.members.get(name.name) match
              case Some(methodType) => methodType
              case None => classInfo.fields.getOrElse(name.name, {
                log(s"Error: No member or field '${name.name}' found in class ${classInfo.sym.nme}")
                freshVar()
              })
          
          case Variable(vs) =>
            val resultType = freshVar()
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
            val resultType = freshVar()
            constrain(prefixType, Record(List(name.name -> resultType)))
            resultType
      
      case SynthSel(prefix, name) =>
        val prefixType = typeTerm(prefix)
        
        prefixType match
          case ClassType(classInfo) =>
            classInfo.members.get(name.name).orElse(classInfo.fields.get(name.name)) match
              case Some(memberType) => memberType
              case None =>
                log(s"Error: No member or field '${name.name}' found in class ${classInfo.sym.nme}")
                freshVar()
          
          case Variable(vs) =>
            val resultType = freshVar()
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
            val resultType = freshVar()
            constrain(prefixType, Record(List(name.name -> resultType)))
            resultType
      
      case Blk(stats, res) =>
        var currentCtx = ctx
        
        stats.foreach {
          case LetDecl(sym, _) =>
            val varTy = freshVar()
            currentCtx = currentCtx + (sym -> varTy)
          
          case DefineVar(sym, rhs) =>
            val rhsTy = typeTerm(rhs)(using currentCtx)
            currentCtx.get(sym).foreach(constrain(rhsTy, _))
            currentCtx = currentCtx + (sym -> rhsTy)
          
          case td: TermDefinition =>
            log(s"Processing function definition: ${td.sym.nme}")
            val paramTypes = td.params.flatMap(paramList => 
              paramList.params.map(param => {
                val paramType = freshVar()
                log(s"Assigned type ${paramType} to parameter ${param.sym.nme}")
                param.sym -> paramType
              })
            ).toMap
            
            val functionCtx = currentCtx ++ paramTypes
            
            val resultType = td.body match
              case Some(body) => 
                val bodyType = typeTerm(body)(using functionCtx)
                log(s"Function ${td.sym.nme} body has type: ${bodyType}")
                bodyType
              case None => 
                freshVar()
            
            val functionType = if td.params.nonEmpty then
              td.params.foldRight(resultType): (paramList, currentReturnType) =>
                if paramList.params.length == 1 then
                  val paramSym = paramList.params.head.sym
                  val paramType = paramTypes.getOrElse(paramSym, freshVar())
                  Function(paramType, currentReturnType)
                else
                  val recordType = Record(paramList.params.map(param => 
                    param.sym.nme -> paramTypes.getOrElse(param.sym, freshVar())
                  ))
                  Function(recordType, currentReturnType)
            else
              resultType
            
            log(s"Function ${td.sym.nme} has type: ${functionType}")
            currentCtx = currentCtx + (td.sym -> functionType)
          
          case cls: ClassDef =>
            log(s"Processing class: ${cls.sym.nme}")
            
            val members = mutable.Map.empty[String, SimpleType]
            val fields = mutable.Map.empty[String, SimpleType]
            
            val paramNames = cls.paramsOpt.map { params =>
              params.params.map(_.sym.name)
            }.getOrElse(Nil)
            
            paramNames.foreach { paramName =>
              fields(paramName) = freshVar()
            }
            
            val classInfo = ClassInfo(cls.sym, paramNames, Nil, Map.empty, fields.toMap)
            val classType = ClassType(classInfo)
            
            currentCtx = currentCtx + (cls.sym -> classType)
            currentCtx = currentCtx + (cls.bsym -> classType)
            
            cls.body.blk.stats.foreach {
              case td: TermDefinition =>
                val methodType = td.body match
                  case Some(Ref(sym)) if fields.contains(sym.nme) =>
                    fields(sym.nme)
                  case Some(body) =>
                    typeTerm(body)(using currentCtx)
                  case None =>
                    freshVar()
                
                members(td.sym.nme) = methodType
              
              case _ => // Skip other statements
            }
            
            val updatedClassInfo = classInfo.copy(members = members.toMap)
            val updatedClassType = ClassType(updatedClassInfo)
            
            currentCtx = currentCtx + (cls.sym -> updatedClassType)
            currentCtx = currentCtx + (cls.bsym -> updatedClassType)
          case _ => // Skip other statements
        }
        
        typeTerm(res)(using currentCtx)
      case _ => freshVar()
  
  def analyzeTermTypes(term: Term)(using state: Elaborator.State): Unit =
    val ctx = createInitialContext()
    val resultType = typeTerm(term)(using ctx)
    log(s"Result type: ${coalesceType(resultType)}")
  
  def coalesceType(ty: SimpleType): String =
    val recursive = mutable.Map[(VariableState, Boolean), String]()
    
    def go(ty: SimpleType, polar: Boolean, inProcess: Set[(VariableState, Boolean)]): String = ty match
      case Primitive(name) => name
      
      case Function(lhs, rhs) =>
        s"(${go(lhs, !polar, inProcess)} -> ${go(rhs, polar, inProcess)})"
      
      case Record(fields) => 
        fields.map { case (name, fieldTy) => 
          s"$name: ${go(fieldTy, polar, inProcess)}" 
        }.mkString("{ ", "; ", " }")
      
      case ClassType(info) => info.toString
      
      case Variable(vs) =>
        val vs_pol = vs -> polar
        
        if inProcess.contains(vs_pol) then
          recursive.getOrElseUpdate(vs_pol, vs.uniqueName)
        else
          val bounds = if polar then vs.lowerBounds else vs.upperBounds
          
          if bounds.isEmpty then vs.uniqueName
          else
            val boundTypes = bounds.map(go(_, polar, inProcess + vs_pol))
            val mrg = if polar then " | " else " & "
            val res = boundTypes.mkString(mrg)
            
            recursive.get(vs_pol).fold(res)(recVar => s"μ$recVar.$res")
    
    go(ty, true, Set.empty)
