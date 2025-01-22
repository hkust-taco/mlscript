package hkmc2.codegen

import scala.collection.mutable.{Map => MutMap}

import mlscript.utils._, shorthands._

import hkmc2._
import hkmc2.Message.MessageContext
import hkmc2.document._
import hkmc2.semantics.Elaborator.State
import hkmc2.utils.Scope

object Printer:
  def getVar(l: Local)(using Raise, Scope): String = l match
    case ts: semantics.TermSymbol =>
      ts.id.name
    case ts: semantics.BlockMemberSymbol => // this means it's a locally-defined member
      ts.nme
      // ts.trmTree
    case ts: semantics.InnerSymbol => ts.nme
    case ts: semantics.BuiltinSymbol => ts.nme
    case _ => summon[Scope].lookup_!(l)

  def mkDocument(blk: Block)(using Raise, Scope): Document = blk match
    case Match(scrut, arms, dflt, rest) =>
      def case_doc(c: Case) = c match
        case Case.Lit(lit) => doc"${lit.idStr}"
        case Case.Cls(cls, path) => doc"${cls.nme}"
        case Case.Tup(len, inf) => doc"tuple$len"
      val docCases = arms
        .map{ case (c, b) => doc"${case_doc(c)} => #{  # ${mkDocument(b)} #} " }
        .mkDocument(sep = doc" # ")
      val docDefault = dflt.map(mkDocument).getOrElse(doc"")
      doc"match ${mkDocument(scrut)} #{  # ${docCases} # else #{  # ${docDefault} #}  #} "
    case Return(res, implct) => doc"return ${mkDocument(res)}"
    case Throw(exc) => doc"throw ${mkDocument(exc)}"
    case Label(label, body, rest) =>
      val l2 = summon[Scope].allocateName(label)
      doc"label $l2 = ${mkDocument(body)} in # ${mkDocument(rest)}"
    case Break(label) =>
      doc"break ${getVar(label)}"
    case Continue(label) =>
      doc"continue ${getVar(label)}"
    case Begin(sub, rest) =>
      doc"begin #{  # ${mkDocument(sub)}; # ${mkDocument(rest)} #} "
    case TryBlock(sub, finallyDo, rest) =>
      doc"try #{  # ${mkDocument(sub)} #  #} finally #  #{ ${mkDocument(finallyDo)} in #  #} ${mkDocument(rest)}"
    case Assign(lhs, rhs, rest) =>
      val docLhs = summon[Scope].lookup(lhs).getOrElse(summon[Scope].allocateName(lhs))
      doc"set $docLhs = ${mkDocument(rhs)} in # ${mkDocument(rest)}"
    case AssignField(lhs, nme, rhs, rest) =>
      doc"set ${mkDocument(lhs)}.${nme.name} = ${mkDocument(rhs)} in # ${mkDocument(rest)}"
    case Define(defn, rest) => {
      doc"define ${mkDocument(defn)} in # ${mkDocument(rest)}"
    }
    case End("") => doc"end"
    case End(msg) => doc"end ${msg}"
  
  def mkDocument(defn: Defn)(using Raise, Scope): Document = defn match
    case FunDefn(sym, params, body) =>
      val docParams = doc"${params.map(_.params.map(x => summon[Scope].allocateName(x.sym)).mkString("(", ", ", ")")).mkString}"
      val docBody = mkDocument(body)
      doc"fun ${sym.nme}${docParams} { #{  # ${docBody} #}  # }"
    case ValDefn(owner, k, sym, rhs) =>
      doc"val ${sym.nme} = ${mkDocument(rhs)}"
    case ClsLikeDefn(sym, k, parentSym, methods, privateFields, publicFields, preCtor, ctor) =>
      def optFldBody(t: semantics.TermDefinition) =
        t.body match
          case Some(x) => doc" = ..."
          case None => doc""
      val clsDefn = sym.defn.getOrElse(die)
      val clsParams = clsDefn.paramsOpt.fold(Nil)(_.paramSyms)
      val ctorParams = clsParams.map(p => summon[Scope].allocateName(p))
      val privFields = privateFields.map(x => doc"let ${x.id.name} = ...").mkDocument(sep = doc" # ")
      val pubFields = publicFields.map(x => doc"${x.k.str} ${x.sym.nme}${optFldBody(x)}").mkDocument(sep = doc" # ")
      val docPrivFlds = if privateFields.isEmpty then doc"" else doc" # ${privFields}"
      val docPubFlds = if publicFields.isEmpty then doc"" else doc" # ${pubFields}"
      val docBody = if publicFields.isEmpty && privateFields.isEmpty then doc"" else doc" { #{ ${docPrivFlds}${docPubFlds} #}  # }"
      val docCtorParams = if clsParams.isEmpty then doc"" else doc"(${ctorParams.mkString(", ")})"
      doc"class ${sym.nme}${docCtorParams}${docBody}"
  
  def mkDocument(arg: Arg)(using Raise, Scope): Document =
    val doc = mkDocument(arg.value)
    if arg.spread
      then doc"...${doc}"
      else doc

  def mkDocument(value: Value)(using Raise, Scope): Document = value match
    case Value.Ref(l) => getVar(l)
    case Value.This(sym) => doc"this"
    case Value.Lit(lit) => doc"${lit.idStr}"
    case Value.Lam(params, body) =>
      val docParams = params.params.map(x => summon[Scope].allocateName(x.sym)).mkString(", ")
      doc"(${docParams}) => ${mkDocument(body)}"
    case Value.Arr(elems) =>
      val docElems = elems.map(x => mkDocument(x)).mkString(", ")
      doc"[${docElems}]"
  
  def mkDocument(path: Path)(using Raise, Scope): Document = path match
    case Select(qual, name) =>
      val docQual = mkDocument(qual)
      doc"${docQual}.${name.name}"
    case x: Value => mkDocument(x)

  def mkDocument(result: Result)(using Raise, Scope): Document = result match
    case Call(fun, args) => doc"${mkDocument(fun)}(${args.map(mkDocument).mkString(", ")})"
    case Instantiate(cls, args) => doc"new ${mkDocument(cls)}(${args.map(mkDocument).mkString(", ")})"
    case x: Path => mkDocument(x)
  
  def mkDocument(prog: Program)(using Raise, Scope): Document = {
    val docImports = prog.imports.map:
      case (local, path) =>
        val docLocal = summon[Scope].allocateName(local)
        doc"import ${docLocal}"
    doc" ${docImports.mkDocument(sep = doc" # ")} # ${mkDocument(prog.main)}"
  }
