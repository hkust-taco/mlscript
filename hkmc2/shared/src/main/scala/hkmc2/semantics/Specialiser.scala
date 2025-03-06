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
    //
end Specialiser

class SimpleSub(val tl: TraceLogger):
  import tl.*

  // New ClassInfo class to encapsulate class information
  case class ClassInfo(
    sym: ClassSymbol,
    supers: Ls[SimpleType] = Nil,
    members: Map[Str, SimpleType] = Map.empty
  ):
    override def toString: String = 
      val superStr = if supers.isEmpty then "" else 
        s" extends ${supers.mkString(" with ")}"
      s"class ${sym.nme}$superStr { ${members.map { case (n, t) => s"$n: $t" }.mkString(", ")} }"

  enum SimpleType:
    case Variable(state: VariableState)
    case Primitive(name: Str)
    case Function(lhs: SimpleType, rhs: SimpleType)
    case Record(fields: Ls[(Str, SimpleType)])
    case ClassType(info: ClassInfo) // Now uses ClassInfo
    
    override def toString: String = this match
      case Variable(state) => s"${state.uniqueName}"
      case Primitive(name) => name
      case Function(lhs, rhs) => s"(${lhs} -> ${rhs})"
      case Record(fields) => fields.map(f => s"${f._1}: ${f._2}").mkString("{ ", "; ", " }")
      case ClassType(info) => info.toString // Delegates to ClassInfo's toString

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
    
    def getOrFresh(sym: Symbol): SimpleType = 
      mapping.getOrElse(sym, {
        log(s"Warning: Symbol not found in context: $sym")
        freshVar()
      })
    def +(pair: (Symbol, SimpleType)): TypeContext = TypeContext(mapping + pair)
    def ++(pairs: Iterable[(Symbol, SimpleType)]): TypeContext = TypeContext(mapping ++ pairs)
    override def toString: String = mapping.map { case (sym, ty) => s"$sym: $ty" }.mkString(", ")
  
  // Common primitive types
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
    
  def unwrapSingleElementTuple(ty: SimpleType): SimpleType = ty match
    case Record(fields) if fields.size == 1 && fields.head._1 == "_0" => 
      fields.head._2
    case _ => ty
    
  def constrain(lhs: SimpleType, rhs: SimpleType)(using cache: mutable.Set[(SimpleType, SimpleType)] = mutable.Set.empty): Unit =
    if cache.contains(lhs -> rhs) then return () else cache += lhs -> rhs
    
    log(s"Constraining ${lhs} <: ${rhs}")
    
    (lhs, rhs) match
      case (Primitive(n0), Primitive(n1)) if n0 == n1 => 
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
      case (ClassType(info0), ClassType(info1)) =>
        if info0.sym == info1.sym then
          info1.members.foreach { case (name, memberType1) =>
            info0.members.get(name) match
              case None => 
                log(s"Error: missing member: $name in class ${info0.sym}")
              case Some(memberType0) => 
                constrain(memberType0, memberType1)
          }
        else
          val isSubtype = info0.supers.exists {
            case ClassType(superInfo) if superInfo.sym == info1.sym => true
            case superType => 
              val superResult = mutable.Set[(SimpleType, SimpleType)]()
              constrain(superType, rhs)(using superResult)
              superResult.nonEmpty
          }
          
          if !isSubtype then
            log(s"Error: class ${info0.sym} is not a subtype of ${info1.sym}")
      
      case (Variable(lhs), rhs) =>
        lhs.upperBounds = rhs :: lhs.upperBounds
        lhs.lowerBounds.foreach(constrain(_, rhs))
      
      case (lhs, Variable(rhs)) =>
        rhs.lowerBounds = lhs :: rhs.lowerBounds
        rhs.upperBounds.foreach(constrain(lhs, _))
      
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
      
      case Ref(sym) => ctx.getOrFresh(sym)
      
      case app @ App(lhs, rhs) =>
        val resultType = freshVar()
        
        if lhs.symbol.flatMap(_.asCls).isDefined then
          lhs.symbol.flatMap(_.asCls) match
            case Some(classSym) =>
              log(s"Class constructor call for ${classSym.nme}")
              
              ctx.get(classSym) orElse ctx.get(lhs.symbol.flatMap(_.asBlkMember).getOrElse(classSym)) match
                case Some(ClassType(classInfo)) =>
                  val argTypes = rhs match
                    case Tup(fields) => fields.map {
                      case Fld(_, term, _) => typeTerm(term)
                      case _ => freshVar()
                    }
                    case _ => List(typeTerm(rhs))
                    
                  val paramToArgMap = classInfo.sym.tree.paramLists.headOption
                    .map(_.fields.map(_.toString))
                    .getOrElse(Nil)
                    .zip(argTypes)
                    .toMap
                  
                  val instanceMembers = classInfo.members.map { case (name, memberType) =>
                    memberType match
                      case _: Variable if classInfo.members.contains(name) && paramToArgMap.contains(name) => 
                        name -> paramToArgMap(name)
                      case _ => 
                        name -> memberType
                  }
                  
                  ClassType(ClassInfo(classInfo.sym, classInfo.supers, instanceMembers))
                case _ =>
                  val lhsType = typeTerm(lhs)
                  val rhsType = processArg(rhs)
                  constrain(lhsType, Function(rhsType, resultType))
                  resultType
            case None =>
              val lhsType = typeTerm(lhs)
              val rhsType = processArg(rhs)
              constrain(lhsType, Function(rhsType, resultType))
              resultType
        else
          val lhsType = typeTerm(lhs)
          val rhsType = processArg(rhs)
          constrain(lhsType, Function(rhsType, resultType))
          resultType
      
      case TyApp(lhs, targs) => 
        typeTerm(lhs)
      
      case Lam(params, body) =>
        val paramTypes = params.params.map(_ => freshVar())
        val paramTypePairs = params.params.zip(paramTypes).map { case (param, ty) => param.sym -> ty }
        val bodyType = typeTerm(body)(using ctx ++ paramTypePairs)
        
        if paramTypes.length == 1 then
          Function(paramTypes.head, bodyType)
        else
          val paramRecord = Record(params.params.zip(paramTypes).map { 
            case (param, ty) => param.sym.nme -> ty 
          })
          Function(paramRecord, bodyType)
      
      case FunTy(lhs, rhs, _) => 
        Function(typeTerm(lhs), typeTerm(rhs))
      
      case Tup(fields) =>
        Record(fields.zipWithIndex.map { 
          case (fld, idx) => fld match
            case Fld(_, term, _) => s"_${idx}" -> typeTerm(term)
            case _ => s"_${idx}" -> freshVar()
        })
      
      case New(cls, args, _) =>
        val clsType = typeTerm(cls)
        val argTypes = args.map(typeTerm)
        
        cls.symbol match
          case Some(sym) =>
            ctx.get(sym) match
              case Some(ClassType(classInfo)) => ClassType(classInfo)
              case otherType =>
                log(s"Warning: Symbol $sym does not reference a class: $otherType")
                clsType
          case None =>
            log(s"Warning: Cannot resolve class symbol for new expression")
            clsType
      
      case Sel(prefix, name) =>
        val prefixType = typeTerm(prefix)
        
        prefixType match
          case ClassType(classInfo) =>
            classInfo.members.get(name.name) match
              case Some(memberType) => memberType
              case None => 
                log(s"Error: No member named ${name.name} found in class")
                freshVar()
          
          case Variable(vs) =>
            val resultType = freshVar()
            
            vs.upperBounds.foreach {
              case ClassType(classInfo) if classInfo.members.contains(name.name) =>
                constrain(resultType, classInfo.members(name.name))
              case _ =>
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
              // Special handling for class instances - check members map directly
              classInfo.members.get(name.name) match
                case Some(memberType) => memberType
                case None => 
                  log(s"Error: No member named ${name.name} found in class")
                  freshVar()
            case Variable(vs) =>
              // Handle type variables as before
              val resultType = freshVar()
              
              vs.upperBounds.foreach {
                case ClassType(classInfo) if classInfo.members.contains(name.name) =>
                  constrain(resultType, classInfo.members(name.name))
                case _ =>
              }
              
              constrain(prefixType, Record(List(name.name -> resultType)))
              resultType
            case _ =>
              // Default case for non-class types
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
            currentCtx.get(sym).foreach(symTy => constrain(rhsTy, symTy))
            currentCtx = currentCtx + (sym -> rhsTy)
          
          case td: TermDefinition =>
            val resultTy = freshVar()
            val paramSymToType = mutable.Map.empty[Symbol, SimpleType]
            
            // Create the function type, remembering the parameter types
            val functionType = if td.params.nonEmpty then
              td.params.reverse.foldLeft(resultTy: SimpleType) { (currentReturnType, paramLs) =>
                if paramLs.params.length == 1 then
                  // Single parameter case
                  val paramTy = freshVar()
                  paramSymToType(paramLs.params.head.sym) = paramTy
                  Function(paramTy, currentReturnType)
                else
                  // Multiple parameters case - use record
                  val paramTypes = paramLs.params.map { param =>
                    val paramTy = freshVar()
                    paramSymToType(param.sym) = paramTy
                    paramTy
                  }
                  
                  Function(
                    Record(paramLs.params.zip(paramTypes).map { 
                      case (param, ty) => param.sym.nme -> ty 
                    }),
                    currentReturnType
                  )
              }
            else
              resultTy
            
            // Add the function to the context
            currentCtx = currentCtx + (td.sym -> functionType)
            
            // Type check the function body
            td.body.foreach { body =>
              var bodyCtx = currentCtx
              
              // Use the same parameter types from the function type
              val paramCtx = paramSymToType.toMap
              bodyCtx = bodyCtx ++ paramCtx
              
              val bodyTy = typeTerm(body)(using bodyCtx)
              constrain(bodyTy, resultTy)
            }
            
            td.sign.foreach { returnTy =>
              val inferredReturnTy = typeTerm(returnTy)(using currentCtx)
              constrain(resultTy, inferredReturnTy)
            }
          
          case cls: ClassDef =>
            log(s"Processing class: ${cls.bsym}")
            
            val members = mutable.Map.empty[String, SimpleType]
            val paramSymToType = mutable.Map.empty[Symbol, SimpleType]
            
            cls.paramsOpt.foreach { params =>
              params.params.foreach { param =>
                val paramType = freshVar()
                members += (param.sym.name -> paramType)
                paramSymToType += (param.sym -> paramType)
              }
            }
            
            cls.body.blk.stats.foreach {
              case td: TermDefinition =>
                val methodType = td.body match
                  case Some(body) =>
                    val methodCtx = currentCtx ++ paramSymToType
                    body match
                      case Ref(sym) if paramSymToType.contains(sym) => paramSymToType(sym)
                      case _ => typeTerm(body)(using methodCtx) 
                  case None => freshVar()
                
                members += (td.sym.nme -> methodType)
              case _ =>
            }
            
            val classInfo = ClassInfo(cls.sym, Nil, members.toMap)
            val classType = ClassType(classInfo)
            currentCtx = currentCtx + (cls.sym -> classType)
            currentCtx = currentCtx + (cls.bsym -> classType)
            
          case stmt => 
            stmt.subTerms.foreach(term => typeTerm(term)(using currentCtx))
        }
        
        typeTerm(res)(using currentCtx)
      
      case Asc(term, ty) =>
        val termTy = typeTerm(term)
        val ascTy = typeTerm(ty)
        constrain(termTy, ascTy)
        ascTy
      
      case CompType(lhs, rhs, true) =>
        val lhsTy = typeTerm(lhs)
        val rhsTy = typeTerm(rhs)
        val resultTy = freshVar()
        constrain(lhsTy, resultTy)
        constrain(rhsTy, resultTy)
        resultTy
      
      case CompType(lhs, rhs, false) =>
        val lhsTy = typeTerm(lhs)
        val rhsTy = typeTerm(rhs)
        val resultTy = freshVar()
        constrain(resultTy, lhsTy)
        constrain(resultTy, rhsTy)
        resultTy
      
      case Neg(rhs) => 
        typeTerm(rhs)
      
      case Deref(ref) =>
        val refTy = typeTerm(ref)
        freshVar()
      
      case RegRef(reg, value) => 
        typeTerm(value)
      
      case Assgn(lhs, rhs) =>
        val lhsTy = typeTerm(lhs)
        val rhsTy = typeTerm(rhs)
        constrain(rhsTy, lhsTy)
        UnitType
      
      case SetRef(ref, value) =>
        typeTerm(ref)
        typeTerm(value)
        UnitType
      
      case Ret(result) => typeTerm(result)
      
      case Throw(result) =>
        typeTerm(result)
        freshVar()
      
      case Try(body, finallyDo) =>
        val bodyTy = typeTerm(body)
        typeTerm(finallyDo)
        bodyTy
      
      case Annotated(annot, target) => typeTerm(target)
      
      case _ =>
        log(s"Unhandled term type: ${term.getClass.getSimpleName}")
        freshVar()
  
  def processArg(arg: Term)(using TypeContext): SimpleType = arg match
    case Tup(fields) if fields.length > 1 =>
      Record(fields.zipWithIndex.map { 
        case (fld, idx) => fld match
          case Fld(_, term, _) => s"_${idx}" -> typeTerm(term)
          case _ => s"_${idx}" -> freshVar()
      })
    
    case Tup(fields) if fields.length == 1 =>
      fields.head match
        case Fld(_, term, _) => typeTerm(term)
        case _ => freshVar()
    
    case _ => 
      typeTerm(arg)
  
  def analyzeTermTypes(term: Term)(using state: Elaborator.State): Unit =
    val ctx = createInitialContext()
    val resultType = typeTerm(term)(using ctx)
    log(s"Result type: ${coalesceType(resultType)}")
  
  def coalesceType(ty: SimpleType): String =
    val recursive = mutable.Map[(VariableState, Boolean), String]()
    
    def go(ty: SimpleType, polar: Boolean, inProcess: Set[(VariableState, Boolean)]): String = ty match
      case Primitive(name) => 
        name
      
      case Function(lhs, rhs) =>
        s"(${go(lhs, !polar, inProcess)} -> ${go(rhs, polar, inProcess)})"
      
      case Record(fields) => 
        fields.map { case (name, fieldTy) => 
          s"$name: ${go(fieldTy, polar, inProcess)}" 
        }.mkString("{ ", "; ", " }")
      
      case ClassType(info) =>
        val superStr = if info.supers.isEmpty then "" else 
          s" extends ${info.supers.map(s => go(s, polar, inProcess)).mkString(" with ")}"
        val memberStr = info.members.map { case (n, t) => 
          s"$n: ${go(t, polar, inProcess)}" 
        }.mkString(", ")
        s"class ${info.sym.nme}$superStr { $memberStr }"
      
      case Variable(vs) =>
        val vs_pol = vs -> polar
        
        if inProcess.contains(vs_pol) then
          recursive.getOrElseUpdate(vs_pol, vs.uniqueName)
        else
          val bounds = if polar then vs.lowerBounds else vs.upperBounds
          
          if bounds.isEmpty then
            vs.uniqueName
          else
            val boundTypes = bounds.map(go(_, polar, inProcess + vs_pol))
            val mrg = if polar then " | " else " & "
            val res = boundTypes.mkString(mrg)
            
            recursive.get(vs_pol).fold(res)(recVar => s"μ$recVar.$res")
    
    go(ty, true, Set.empty)
