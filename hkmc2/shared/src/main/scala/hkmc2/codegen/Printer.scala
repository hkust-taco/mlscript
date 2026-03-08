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
import hkmc2.document.Document.{braced, bracedbk}

object Printer:
  
  def print(l: Local)(using Raise, Scope, ShowCfg): Document =
    // * Symbols that are not local symbols in scope should be printed using their dbgName
    // *  – these will appear like `x¹²` and will be globally unique.
    scope.lookup(l) match
      case S(str) => str
      case N => l.dbgName
  
  def print(blk: Block)(using Raise, Scope, ShowCfg): Document = blk match
    case Match(scrut, arms, dflt, rest) =>
      def case_doc(c: Case) = c match
        case Case.Lit(lit) => doc"${lit.idStr}"
        case Case.Cls(cls, path) => doc"${print(cls)}"
        case Case.Tup(len, inf) => doc"Array($len${if inf then "+" else ""})"
        case _ => TODO(c)
      val docCases = arms
        .map{ case (c, b) => doc"${case_doc(c)} => #{  # ${print(b)} #} " }
        .mkDocument(sep = doc" # ")
      val docDefault = dflt.fold(doc"")(e => doc" # else #{  # ${print(e)} #} ")
      doc"match ${print(scrut)} #{  # ${docCases}$docDefault #}  # ${print(rest)}"
    case Return(res, implct) => if implct then print(res) else doc"return ${print(res)}"
    case Throw(exc) => doc"throw ${print(exc)}"
    case Label(label, loop, body, rest) =>
      val l2 = scope.allocateName(label)
      doc"labelled ${if loop then "loop" else "block"} $l2 = ${print(body)}; # ${print(rest)}"
    case Break(label) =>
      doc"break ${print(label)}"
    case Continue(label) =>
      doc"continue ${print(label)}"
    case Begin(sub, rest) =>
      doc"begin #{  # ${print(sub)}; # ${print(rest)} #} "
    case TryBlock(sub, finallyDo, rest) =>
      doc"try #{  # ${print(sub)} #  #} finally #  #{ ${print(finallyDo)}; #  #} ${print(rest)}"
    case Assign(_: NoSymbol, rhs, rest) =>
      doc"do ${print(rhs)}; # ${print(rest)}"
    case Assign(lhs, rhs, rest) =>
      doc"set ${print(lhs)} = ${print(rhs)}; # ${print(rest)}"
    case AssignField(lhs, nme, rhs, rest) =>
      doc"set ${print(lhs)}.${nme.name} = ${print(rhs)}; # ${print(rest)}"
    case Define(defn, rest) =>
      doc"define ${print(defn)}; # ${print(rest)}"
    case Scoped(syms, body) =>
      scope.nest.givenIn:
        import hkmc2.given_Ordering_Uid // Not sure why needed...
        val names = syms.toList.sortBy(_.uid).map(s => scope.allocateName(s))
        doc"let ${names.mkDocument(", ")}; # ${print(body)}"
    case End("") => doc"end"
    case End(msg) => doc"end /* ${msg} */"
    case _ => TODO(blk)
  
  def print(c: ClsLikeBody)(using Raise, Scope, ShowCfg): Document =
    print(c.privateFields, c.publicFields, c.methods, N, c.ctor)
  
  def print(
      privateFields: List[TermSymbol],
      publicFields: List[(BlockMemberSymbol, TermSymbol)],
      methods: List[FunDefn],
      preCtor: Opt[Block],
      ctor: Block
  )(using Raise, Scope, ShowCfg): Document =
    val privFields = privateFields.map(x => doc"private val ${print(x)};").mkDocument(sep = doc" # ")
    val pubFields = publicFields.map(x => doc"val (${print(x._1)}) ${print(x._2)};").mkDocument(sep = doc" # ")
    val docPrivFlds = if privateFields.isEmpty then doc"" else doc" # ${privFields}"
    val docPubFlds = if publicFields.isEmpty then doc"" else doc" # ${pubFields}"
    val docPreCtor = preCtor match
      case Some(End(_)) => doc""
      case Some(value) => doc" # preCtor ${bracedbk(print(value))}"
      case None => doc""
    val docCtor = ctor match
      case End(_) => doc""
      case _ => doc" # ctor ${bracedbk(print(ctor))}"
    
    val mtds = methods.map(print).mkDocument(sep = doc" # ")
    val docMethods = if methods.isEmpty then doc"" else doc" # ${mtds}"
    if publicFields.isEmpty && privateFields.isEmpty && methods.isEmpty then doc""
    else doc" " :: braced(doc"${docPrivFlds}${docPubFlds}${docPreCtor}${docCtor}${docMethods}")
  
  def print(defn: Defn)(using Raise, Scope, ShowCfg): Document = defn match
    case FunDefn(own, sym, dSym, params, body) =>
      val docParams = doc"${print(sym)}${
        params.map(_.params.map(x => scope.allocateName(x.sym)).mkDocument("(", ", ", ")")).mkDocument("")}"
      val docBody = print(body)
      doc"fun ${docParams} ${bracedbk(docBody)}"
    case ValDefn(tsym, sym, rhs) =>
      doc"val ${print(tsym)} = ${print(rhs)}"
    case ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentSym, methods,
        privateFields, publicFields, preCtor, ctor, mod, bufferable)
    =>
      val clsParams = paramsOpt.fold(Nil)(_.paramSyms)
      val auxClsParams = auxParams.flatMap(_.paramSyms)
      val ctorParams = (clsParams ++ auxClsParams).map(p => scope.allocateName(p))
      val docCtorParams = if clsParams.isEmpty then doc"" else doc"(${ctorParams.mkDocument(", ")})"
      val docStaged = if isym.defn.forall(_.hasStagedModifier.isEmpty) then doc"" else doc"staged "
      val docBody = print(privateFields, publicFields, methods, S(preCtor), ctor)
      val docPreCtor = print(preCtor)
      val clsType = k match
        case Cls => "class"
        case Pat => "pattern"
        case Obj => "object"
        case Mod => "module"
      val docCls = doc"${docStaged}${clsType} ${print(sym)}${docCtorParams}${docBody}"
      val docModule = mod match
        case Some(mod) =>
          val docStaged = if mod.isym.defn.forall(_.hasStagedModifier.isEmpty) then doc"" else doc"staged "
          val docBody = print(mod)
          doc" ${bracedbk(docStaged)} # module ${print(sym)}${docBody}"
        case None => doc""
      doc"${docCls}${docModule}"
  
  def print(arg: Arg)(using Raise, Scope, ShowCfg): Document =
    val doc = print(arg.value)
    if arg.spread.nonEmpty
      then doc"...${doc}"
      else doc

  def print(value: Value)(using Raise, Scope, ShowCfg): Document = value match
    case Value.Ref(l, _) => print(l)
    case Value.This(sym) => doc"this"
    case Value.Lit(lit) => doc"${lit.idStr}"
  
  def print(path: Path)(using Raise, Scope, ShowCfg): Document = path match
    case sel @ Select(qual, name) =>
      val docQual = print(qual)
      doc"${docQual}.${sel.symbol.fold(name.name+"﹖")(sym =>
        if summon[ShowCfg].debug then s"‹${sym}›" else sym.dbgName)}"
    case x: Value => print(x)
    case _ => TODO(path)
  
  def print(result: Result)(using Raise, Scope, ShowCfg): Document = result match
    case Call(fun, args) => doc"${print(fun)}(${args.map(print).mkDocument(", ")})"
    case Instantiate(mut, cls, args) =>
      doc"new ${if mut then "mut " else ""}${print(cls)}(${args.map(print).mkDocument(", ")})"
    case Lambda(params, body) =>
      val docParams = params.params.map(x => scope.allocateName(x.sym)).mkDocument(", ")
      doc"(${docParams}) => ${print(body)}"
    case Tuple(mut, elems) =>
      val docElems = elems.map(x => print(x)).mkDocument(", ")
      doc"${if mut then "mut " else ""}[${docElems}]"
    case Record(mut, args) =>
      doc"${if mut then "mut " else ""}{ ${
        args.map(x => x.idx.fold(doc"...")(p => print(p) :: ": ") :: print(x.value)).mkDocument(", ")
      } }"
    case DynSelect(qual, fld, arrayIdx) =>
      doc"${print(qual)}${if arrayIdx then "." else "!"}${print(fld)}"
    case x: Path => print(x)
  
  def print(imports: Ls[Local -> Str])(using Raise, Scope, ShowCfg): Document =
    imports.map: (local, path) =>
        val docLocal = scope.allocateName(local)
        doc"import ${docLocal}; # "
      .mkDocument()
  
  def print(prog: Program)(using Raise, Scope, ShowCfg): Document =
    doc"${print(prog.imports)}${print(prog.main)}"
  
  def worksheet(prog: Program)(using Raise, Scope, ShowCfg): Document =
    doc"${print(prog.imports)}${
      prog.main match
      case Scoped(syms, body) =>
        // * The top-level Scoped block in a worksheet contains symbols that are actually
        // * still visible in the following blocks;
        // * therefore, we want to avoid printing them with fresh names but use their `dbgName`s instead.
        scope.nest.givenIn:
          import hkmc2.given_Ordering_Uid // Not sure why needed...
          val names = syms.toList.sortBy(_.uid).map:
            case s: TempSymbol => scope.allocateName(s)
            case s => s.dbgName
          doc"let ${names.mkString(", ")}; # ${print(body)}"
      case m => print(m)
    }"
  
