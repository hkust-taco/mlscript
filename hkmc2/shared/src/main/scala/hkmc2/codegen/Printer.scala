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


/** `SymbolPrinter` is used for printing symbols that are not locally bound, so that they are consistent
  * with the debug-printed names shown in other parts of the compiler, such as showAsTreee. */
class Printer(using Raise, ShowCfg, SymbolPrinter, Config):
  
  val showPurity =
    false
    // true
  
  def print(l: Local)(using Scope): Document =
    // * Symbols that are not local symbols in scope should be printed using their dbgName
    // *  – these will appear like `x¹²` and will be globally unique.
    scope.lookup(l) match
      case S(str) => str
      case N => summon[SymbolPrinter].printSymbol(l)
  
  def print(blk: Block)(using Scope): Document = blk match
    case Match(scrut, arms, dflt, rest) =>
      def case_doc(c: Case) = c match
        case Case.Lit(lit) => doc"${lit.idStr}"
        case Case.Cls(cls, path) => doc"${print(cls)}"
        case Case.Tup(len, inf) => doc"Array($len${if inf then "+" else ""})"
        case Case.Field(name, safe) => doc"${if safe then "" else "Object "}{ ${name.name} }"
      val docCases = arms
        .map{ case (c, b) => doc"${case_doc(c)} => #{  # ${print(b)} #} " }
        .mkDocument(sep = doc" # ")
      val docDefault = dflt.fold(doc"")(e => doc" # else #{  # ${print(e)} #} ")
      doc"match ${print(scrut)} #{  # ${docCases}$docDefault #}  # ${print(rest)}"
    case Return(res, implct) => if implct then print(res) else doc"return ${print(res)}"
    case Throw(exc) => doc"throw ${print(exc)}"
    case Label(label, loop, body, rest) =>
      val l2 = scope.allocateOrGetName(label)
      // * ^ if we print the same block with a top-level label more than once, using `scope.allocateName` will crash...
      doc"${if loop then "loop" else "block"} $l2: #{  # ${print(body)} #}  # ${print(rest)}"
    case Break(label) =>
      doc"break ${print(label)}"
    case Continue(label) =>
      doc"continue ${print(label)}"
    case Begin(sub, rest) =>
      doc"begin #{  # ${print(sub)}; #}  # ${print(rest)}"
    case TryBlock(sub, finallyDo, rest) =>
      doc"try #{  # ${print(sub)} #  #} finally #  #{ ${print(finallyDo)}; #  #} ${print(rest)}"
    case Assign(_: NoSymbol, rhs, rest) =>
      doc"do ${print(rhs)}; # ${print(rest)}"
    case Assign(lhs, rhs, rest) =>
      doc"set ${print(lhs)} = ${print(rhs)}; # ${print(rest)}"
    case AssignField(lhs, nme, rhs, rest) =>
      doc"set ${print(lhs)}.${nme.name} = ${print(rhs)}; # ${print(rest)}"
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) =>
      doc"set ${print(lhs)}${if arrayIdx then "." else "!"}${print(fld)} = ${print(rhs)}; # ${print(rest)}"
    case Define(defn, rest) =>
      doc"define ${print(defn.sym)} as ${print(defn)}; # ${print(rest)}"
    case Scoped(syms, body) =>
      scope.nest.givenIn:
        import hkmc2.given_Ordering_Uid // Not sure why needed...
        val names = syms.toList.sortBy(_.uid).map(s => scope.allocateName(s))
        doc"let ${names.mkDocument(", ")}; # ${print(body)}"
    case End(msg) if msg.nonEmpty && config.commentGeneratedCode => doc"end /* ${msg} */"
    case End(_) => doc"end"
    case Unreachable(msg) => doc"unreachable /* ${msg} */"
    case _ => TODO(blk)
  
  def print(
      privateFields: List[TermSymbol],
      publicFields: List[(BlockMemberSymbol, TermSymbol)],
      methods: List[FunDefn],
      preCtor: Opt[Block],
      ctor: Block,
      ctorSym: Opt[TermSymbol],
  )(using Scope): Document =
    val privFields = privateFields.map(x => doc"private val ${print(x)};").mkDocument(sep = doc" # ")
    val pubFields = publicFields.map(x => doc"val ${print(x._1)};").mkDocument(sep = doc" # ")
    val docPrivFlds = if privateFields.isEmpty then doc"" else doc" # ${privFields}"
    val docPubFlds = if publicFields.isEmpty then doc"" else doc" # ${pubFields}"
    val docPreCtor = preCtor match
      case Some(End(_)) => doc""
      case Some(value) => print(value) :: doc"; # "
      case None => doc""
    val docCtor = ctor match
      case End(_) => doc""
      case _ => doc" # constructor${ctorSym.fold(doc"")(doc" " :: print(_))} ${
        bracedbk(docPreCtor :: print(ctor))}"
    val mtds = methods.map(m => doc"method ${print(m.sym)} = " :: print(m)).mkDocument(sep = doc" # ")
    val docMethods = if methods.isEmpty then doc"" else doc" # ${mtds}"
    if publicFields.isEmpty
    && privateFields.isEmpty
    && methods.isEmpty
    && preCtor.forall(_.isEmpty)
    && ctor.isEmpty
    then doc""
    else doc" " :: braced(doc"${docPrivFlds}${docPubFlds}${docCtor}${docMethods}")
  
  def print(defn: Defn)(using Scope): Document = defn match
    case FunDefn(own, sym, dSym, params, body) =>
      scope.nest.givenIn:
        val docParams = doc"${
          params.map(_.params.map(x => scope.allocateName(x.sym)).mkDocument("(", ", ", ")")).mkDocument("")}"
        val docBody = print(body)
        doc"fun ${print(dSym)}${docParams} ${bracedbk(docBody)}"
    case ValDefn(tsym, sym, rhs) =>
      doc"val ${print(tsym)} = ${print(rhs)}"
    case ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentSym, methods,
        privateFields, publicFields, preCtor, ctor, mod, bufferable)
    => scope.nest.givenIn:
      val clsParams = paramsOpt.fold(Nil)(_.paramSyms)
      val auxClsParams = auxParams.flatMap(_.paramSyms)
      val ctorParams = (clsParams ++ auxClsParams).map(p => scope.allocateName(p))
      val docCtorParams = if clsParams.isEmpty then doc"" else doc"(${ctorParams.mkDocument(", ")})"
      val docStaged = if isym.defn.forall(_.hasStagedModifier.isEmpty) then doc"" else doc"staged "
      val docBody = print(privateFields, publicFields, methods, S(preCtor), ctor, ctorSym)
      val clsType = k.str
      val docCls = doc"${docStaged}${clsType} ${print(isym)}${docCtorParams}${docBody}"
      val docModule = mod match
        case Some(mod) =>
          val docStaged = if mod.isym.defn.forall(_.hasStagedModifier.isEmpty) then doc"" else doc"staged "
          val docBody = print(mod.privateFields, mod.publicFields, mod.methods, N, mod.ctor, N)
          doc" # ${docStaged}module ${print(mod.isym)}${docBody}"
        case None => doc""
      doc"${docCls}${docModule}"
  
  private def showSymbol(name: Str, sym: Opt[DefinitionSymbol[?]]): Document =
    sym.fold(doc"${name}﹖")(sym =>
      if summon[ShowCfg].debug then doc"‹${sym.toString}›" else summon[SymbolPrinter].printSymbol(sym))
  
  def print(arg: Arg)(using Scope): Document =
    val doc = print(arg.value)
    if arg.spread.nonEmpty
      then doc"...${doc}"
      else doc

  def print(value: Value)(using Scope): Document = value match
    case Value.Ref(l, N) => print(l)
    case Value.Ref(l, disamb) => showSymbol(l.nme, disamb)
    case Value.This(sym) => doc"this"
    case Value.Lit(lit) => doc"${lit.idStr}"
  
  def print(path: Path)(using Scope): Document = path match
    case sel @ Select(qual, name) =>
      val docQual = print(qual)
      doc"${docQual}.${showSymbol(name.name, sel.symbol)}"
    case DynSelect(qual, fld, arrayIdx) =>
      doc"${print(qual)}${if arrayIdx then "." else "!"}${print(fld)}"
    case x: Value => print(x)
    // case _ => TODO(path)
  
  def print(result: Result)(using Scope): Document =
    (if !showPurity || result.isPure then "" else "!") ::
    result.match
    case Call(fun, args) => doc"${print(fun)}(${args.map(print).mkDocument(", ")})"
    case Instantiate(mut, cls, args) =>
      doc"new ${if mut then "mut " else ""}${print(cls)}(${args.map(print).mkDocument(", ")})"
    case Lambda(params, body) =>
      scope.nest.givenIn:
        val docParams = params.params.map(x => scope.allocateName(x.sym)).mkDocument(", ")
        doc"(${docParams}) => ${print(body)}"
    case Tuple(mut, elems) =>
      val docElems = elems.map(x => print(x)).mkDocument(", ")
      doc"${if mut then "mut " else ""}[${docElems}]"
    case Record(mut, args) =>
      doc"${if mut then "mut " else ""}{ ${
        args.map(x => x.idx.fold(doc"...")(p => print(p) :: ": ") :: print(x.value)).mkDocument(", ")
      } }"
    case x: Path => print(x)
  
  def print(imports: Ls[Local -> Str])(using Scope): Document =
    imports.map: (local, path) =>
        val docLocal = scope.allocateName(local)
        doc"import ${docLocal}; # "
      .mkDocument()
  
  def print(prog: Program)(using Scope): Document =
    doc"${print(prog.imports)}${print(prog.main)}"
  
  def worksheet(prog: Program)(using Scope): Document =
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
            case s => summon[SymbolPrinter].printSymbol(s)
          doc"let ${names.mkString(", ")}; # ${print(body)}"
      case m => print(m)
    }"
  
