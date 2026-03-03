package hkmc2.codegen

import scala.collection.mutable.{Map => MutMap}

import mlscript.utils._, shorthands._

import hkmc2._
import hkmc2.Message.MessageContext
import hkmc2.document._
import hkmc2.semantics._
import hkmc2.syntax._
import hkmc2.semantics.Elaborator.State
import hkmc2.utils.Scope
import hkmc2.utils.Scope.scope

object Printer:
  def getVar(l: Local)(using Raise, Scope): String = l match
    case ts: semantics.TermSymbol =>
      ts.id.name
    case ts: semantics.BlockMemberSymbol => // this means it's a locally-defined member
      ts.nme
      // ts.trmTree
    case ts: semantics.InnerSymbol => ts.nme
    case ts: semantics.BuiltinSymbol => ts.nme
    case _ => scope.lookup(l) match
      case S(str) => str
      case N => s"‹not in scope: ${l}›"

  def mkDocument(blk: Block)(using Raise, Scope): Document = blk match
    case Match(scrut, arms, dflt, rest) =>
      def case_doc(c: Case) = c match
        case Case.Lit(lit) => doc"${lit.idStr}"
        case Case.Cls(cls, path) => doc"${cls.nme}"
        case Case.Tup(len, inf) => doc"tuple$len"
        case _ => TODO(c)
      val docCases = arms
        .map{ case (c, b) => doc"${case_doc(c)} => #{  # ${mkDocument(b)} #} " }
        .mkDocument(sep = doc" # ")
      val docDefault = dflt.fold(doc"")(e => doc" # else #{  # ${mkDocument(e)} #} ")
      doc"match ${mkDocument(scrut)} #{  # ${docCases}$docDefault #}  # ${mkDocument(rest)}"
    case Return(res, implct) => doc"return ${mkDocument(res)}"
    case Throw(exc) => doc"throw ${mkDocument(exc)}"
    case Label(label, loop, body, rest) =>
      val l2 = scope.allocateName(label)
      doc"labelled ${if loop then "loop" else "block"} $l2 = ${mkDocument(body)}; # ${mkDocument(rest)}"
    case Break(label) =>
      doc"break ${getVar(label)}"
    case Continue(label) =>
      doc"continue ${getVar(label)}"
    case Begin(sub, rest) =>
      doc"begin #{  # ${mkDocument(sub)}; # ${mkDocument(rest)} #} "
    case TryBlock(sub, finallyDo, rest) =>
      doc"try #{  # ${mkDocument(sub)} #  #} finally #  #{ ${mkDocument(finallyDo)}; #  #} ${mkDocument(rest)}"
    case Assign(lhs, rhs, rest) =>
      val docLhs = scope.lookup(lhs).getOrElse(scope.allocateName(lhs))
      doc"set $docLhs = ${mkDocument(rhs)}; # ${mkDocument(rest)}"
    case AssignField(lhs, nme, rhs, rest) =>
      doc"set ${mkDocument(lhs)}.${nme.name} = ${mkDocument(rhs)}; # ${mkDocument(rest)}"
    case Define(defn, rest) =>
      doc"define ${mkDocument(defn)}; # ${mkDocument(rest)}"
    case Scoped(_, body) => mkDocument(body)
    case End("") => doc"end"
    case End(msg) => doc"end /* ${msg} */"
    case _ => TODO(blk)
  
  def mkDocument(c: ClsLikeBody)(using Raise, Scope): Document =
    mkDocument(c.privateFields, c.publicFields, c.methods, N, c.ctor)
  
  def mkDocument(
      privateFields: List[TermSymbol],
      publicFields: List[(BlockMemberSymbol, TermSymbol)],
      methods: List[FunDefn],
      preCtor: Opt[Block],
      ctor: Block
  )(using Raise, Scope): Document =
    val privFields = privateFields.map(x => doc"private val ${x.id.name}").mkDocument(sep = doc" # ")
    val pubFields = publicFields.map(x => doc"val ${x._1.nme}").mkDocument(sep = doc" # ")
    val docPrivFlds = if privateFields.isEmpty then doc"" else doc" # ${privFields}"
    val docPubFlds = if publicFields.isEmpty then doc"" else doc" # ${pubFields}"
    val docPreCtor = preCtor match
      case Some(End(_)) => doc""
      case Some(value) => doc" # preCtor { #{  # ${mkDocument(value)} #}  # }"
      case None => doc""
    val docCtor = ctor match
      case End(_) => doc""
      case _ => doc" # ctor { #{  # ${mkDocument(ctor)} #}  # }"
    
    val mtds = methods.map(mkDocument).mkDocument(sep = doc" # ")
    val docMethods = if methods.isEmpty then doc"" else doc" # ${mtds}"
    if publicFields.isEmpty && privateFields.isEmpty && methods.isEmpty then doc""
    else doc" { #{ ${docPrivFlds}${docPubFlds}${docPreCtor}${docCtor}${docMethods} #}  # }"

  def mkDocument(defn: Defn)(using Raise, Scope): Document = defn match
    case FunDefn(own, sym, dSym, params, body) =>
      val docParams = doc"${own.fold("")(_.toString + "::")}${sym.nme}${
        params.map(_.params.map(x => scope.allocateName(x.sym)).mkDocument("(", ", ", ")")).mkDocument("")}"
      val docBody = mkDocument(body)
      doc"fun ${docParams} { #{  # ${docBody} #}  # }"
    case ValDefn(tsym, sym, rhs) =>
      doc"val ${tsym.nme} = ${mkDocument(rhs)}"
    case ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentSym, methods,
        privateFields, publicFields, preCtor, ctor, mod, bufferable)
    =>
      val clsParams = paramsOpt.fold(Nil)(_.paramSyms)
      val auxClsParams = auxParams.flatMap(_.paramSyms)
      val ctorParams = (clsParams ++ auxClsParams).map(p => scope.allocateName(p))
      val docCtorParams = if clsParams.isEmpty then doc"" else doc"(${ctorParams.mkDocument(", ")})"
      val docStaged = if isym.defn.forall(_.hasStagedModifier.isEmpty) then doc"" else doc"staged "
      val docBody = mkDocument(privateFields, publicFields, methods, S(preCtor), ctor)
      val docPreCtor = mkDocument(preCtor)
      val clsType = k match
        case Cls => "class"
        case Pat => "pattern"
        case Obj => "object"
        case Mod => "module"
      val docCls = doc"${docStaged}${clsType} ${own.fold("")(_.toString+"::")}${sym.nme}${docCtorParams}${docBody}"
      val docModule = mod match
        case Some(mod) =>
          val docStaged = if mod.isym.defn.forall(_.hasStagedModifier.isEmpty) then doc"" else doc"staged "
          val docBody = mkDocument(mod)
          doc" with # ${docStaged}module ${own.fold("")(_.toString+"::")}${sym.nme}${docBody}"
        case None => doc""
      doc"${docCls}${docModule}"
  
  def mkDocument(arg: Arg)(using Raise, Scope): Document =
    val doc = mkDocument(arg.value)
    if arg.spread.nonEmpty
      then doc"...${doc}"
      else doc

  def mkDocument(value: Value)(using Raise, Scope): Document = value match
    case Value.Ref(l, _) => getVar(l)
    case Value.This(sym) => doc"this"
    case Value.Lit(lit) => doc"${lit.idStr}"
  
  def mkDocument(path: Path)(using Raise, Scope): Document = path match
    case Select(qual, name) =>
      val docQual = mkDocument(qual)
      doc"${docQual}.${name.name}"
    case x: Value => mkDocument(x)
    case _ => TODO(path)

  def mkDocument(result: Result)(using Raise, Scope): Document = result match
    case Call(fun, args) => doc"${mkDocument(fun)}(${args.map(mkDocument).mkDocument(", ")})"
    case Instantiate(mut, cls, args) =>
      doc"new ${if mut then "mut " else ""}${mkDocument(cls)}(${args.map(mkDocument).mkDocument(", ")})"
    case Lambda(params, body) =>
      val docParams = params.params.map(x => scope.allocateName(x.sym)).mkDocument(", ")
      doc"(${docParams}) => ${mkDocument(body)}"
    case Tuple(mut, elems) =>
      val docElems = elems.map(x => mkDocument(x)).mkDocument(", ")
      doc"${if mut then "mut " else ""}[${docElems}]"
    case Record(mut, args) =>
      doc"${if mut then "mut " else ""}{ ${
        args.map(x => x.idx.fold(doc"...")(p => mkDocument(p) :: ": ") :: mkDocument(x.value)).mkDocument(", ")
      } }"
    case DynSelect(qual, fld, arrayIdx) =>
      doc"${mkDocument(qual)}${if arrayIdx then "." else "!"}${mkDocument(fld)}"
    case x: Path => mkDocument(x)
  
  def mkDocument(prog: Program)(using Raise, Scope): Document = scope.nest.givenIn:
    val docImports = prog.imports.map:
      case (local, path) =>
        val docLocal = scope.allocateName(local)
        doc"import ${docLocal};"
    doc" ${docImports.mkDocument(sep = doc" # ")} # ${mkDocument(prog.main)}"
  
