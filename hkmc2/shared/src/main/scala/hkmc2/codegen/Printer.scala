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
class Printer(using Raise, ShowCfg, State, SymbolPrinter, Config):
  
  val showPurity =
    false
    // true
  
  def print(l: Symbol)(using Scope): Document =
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
    case Return(res) => doc"return ${print(res)}"
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
      doc"try #{  # ${print(sub)} #}  # finally #{  # ${print(finallyDo)}; #  #} ${print(rest)}"
    case Assign(_: NoSymbol, rhs, rest) =>
      doc"do ${print(rhs)}; # ${print(rest)}"
    case Assign(lhs: (LocalVarSymbol | TermSymbol), rhs, rest) =>
      doc"set ${print(lhs)} = ${print(rhs)}; # ${print(rest)}"
    case asf @ AssignField(lhs, nme, rhs, rest) =>
      doc"set ${print(lhs)}.${showMemberSymbol(nme.name, asf.symbol)} = ${print(rhs)}; # ${print(rest)}"
    case AssignDynField(lhs, fld, arrayIdx, rhs, rest) =>
      doc"set ${print(lhs)}${if arrayIdx then "." else "!"}${print(fld)} = ${print(rhs)}; # ${print(rest)}"
    case Define(defn, rest) =>
      doc"${printFlags(defn)}define ${print(defn.sym)} as ${print(defn)}; # ${print(rest)}"
    case Scoped(syms, body) =>
      scope.nest.givenIn:
        import hkmc2.given_Ordering_Uid // Not sure why needed...
        val names = syms.toList.sortBy(_.uid).map(s => scope.allocateName(s))
        doc"let ${names.mkDocument(", ")}; # ${print(body)}"
    case End(msg) if msg.nonEmpty && config.commentGeneratedCode => doc"end /* ${msg} */"
    case End(_) => doc"end"
    case Unreachable(msg) => doc"unreachable /* ${msg} */"
    case _ => TODO(blk)
  
  def printFlags(defn: Defn)(using Scope): Document =
    // val overrides = defn match
    // case fun: FunDefn =>
    //   fun.configOverride
    // case cls: ClsLikeDefn =>
    //   if cls.isStaged then doc"staged " else doc""
    // case _ => doc""
    // defn.configOverride.map: cfg =>
    //   if cfg.staged then doc"staged " else doc""
    if defn.annotations.isEmpty then doc""
    else defn.annotations.map(_.show).mkDocument(doc" ") :: doc" # "
  
  def print(
      privateFields: Ls[TermSymbol],
      publicFields: Ls[(BlockMemberSymbol, TermSymbol)],
      methods: Ls[FunDefn],
      auxParams: Ls[ParamList],
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
      case End(_) =>
        ctorSym match
        case S(ctorSym) => doc" # constructor ${print(ctorSym)}"
        case N => doc""
      case _ => doc" # constructor${ctorSym.fold(doc"")(doc" " :: print(_))}${printParamLists(auxParams)} ${
        bracedbk(docPreCtor :: print(ctor))}"
    val mtds = methods.map(m => doc"method ${print(m.sym)} = " :: print(m)).mkDocument(sep = doc" # ")
    val docMethods = if methods.isEmpty then doc"" else doc" # ${mtds}"
    if publicFields.isEmpty
    && privateFields.isEmpty
    && methods.isEmpty
    && preCtor.forall(_.isEmpty)
    && ctor.isEmpty
    && ctorSym.isEmpty
    then doc""
    else doc" " :: braced(doc"${docPrivFlds}${docPubFlds}${docCtor}${docMethods}")
  
  def printParamLists(paramss: Ls[ParamList])(using Scope): Document =
    paramss
      .map: pl =>
        val allParams =
          pl.params.map(x => scope.allocateName(x.sym)) ++
          pl.restParam.map(x => "..." + scope.allocateName(x.sym))
        allParams.mkDocument("(", ", ", ")")
      .mkDocument("")
  
  def print(defn: Defn)(using Scope): Document = defn match
    case fun @ FunDefn(own, sym, dSym, paramss, body) =>
      scope.nest.givenIn:
        val docParams = printParamLists(paramss)
        val docBody = print(body)
        val docStaged = if fun.isStaged then doc"staged " else doc""
        doc"${docStaged}fun ${print(dSym)}${docParams} ${bracedbk(docBody)}"
    case ValDefn(tsym, sym, rhs) =>
      doc"val ${print(tsym)} = ${print(rhs)}"
    case cls @ ClsLikeDefn(own, isym, sym, ctorSym, k, paramsOpt, auxParams, parentSym, methods,
        privateFields, publicFields, preCtor, ctor, mod, bufferable)
    => scope.nest.givenIn:
      val ctorParams = printParamLists(paramsOpt.toList)
      val docStaged = if cls.isStaged then doc"staged " else doc""
      val docBody = print(privateFields, publicFields, methods, auxParams, S(preCtor), ctor, ctorSym)
      val clsType = k.str
      val docCls = doc"${docStaged}${clsType}${parentSym.fold(doc"")(doc" extends " :: print(_))} ${print(isym)}${ctorParams}${docBody}"
      val docModule = mod match
        case Some(mod) =>
          val docStaged = if mod.isStaged then doc"staged " else doc""
          val docBody = print(mod.privateFields, mod.publicFields, mod.methods, Nil, N, mod.ctor, N)
          doc" # ${docStaged}module ${print(mod.isym)}${docBody}"
        case None => doc""
      doc"${docCls}${docModule}"
  
  private def showMemberSymbol(name: Str, sym: Opt[MemberSymbol]): Document =
    sym.fold(doc"${name}﹖")(sym =>
      if summon[ShowCfg].debug then doc"‹${sym.toString}›" else summon[SymbolPrinter].printSymbol(sym))
  
  def print(arg: Arg)(using Scope): Document =
    val doc = print(arg.value)
    if arg.spread.nonEmpty
      then doc"...${doc}"
      else doc
  
  def print(value: Value)(using Scope): Document = value match
    case Value.SimpleRef(l) => print(l)
    case Value.MemberRef(bms, disamb) => showMemberSymbol(bms.nme, S(disamb))
    case Value.This(sym) if sym === State.globalThisSymbol => showMemberSymbol(sym.nme, S(sym.asDefnSym))
    case Value.This(sym) => doc"${print(sym)}.this"
    case Value.Lit(lit) => doc"${lit.idStr}"
  
  def print(path: Path)(using Scope): Document = path match
    case sel @ Select(qual, name) =>
      val docQual = print(qual)
      doc"${docQual}.${showMemberSymbol(name.name, sel.symbol)}"
    case DynSelect(qual, fld, arrayIdx) =>
      doc"${print(qual)}${if arrayIdx then "." else "!"}${print(fld)}"
    case x: Value => print(x)
    // case _ => TODO(path)
  
  def print(result: Result)(using Scope): Document =
    (if !showPurity || result.isPure then "" else "!") ::
    result.match
    case Call(fun, argss) =>
      val chainedArgs = argss.map(args => doc"(${args.map(print).mkDocument(", ")})").mkDocument("")
      doc"${print(fun)}${chainedArgs}"
    case Instantiate(mut, cls, argss) =>
      val chainedArgs = argss.map(args => doc"(${args.map(print).mkDocument(", ")})").mkDocument("")
      doc"new ${if mut then "mut " else ""}${print(cls)}${chainedArgs}"
    case Lambda(params, body) =>
      scope.nest.givenIn:
        val allParams =
          params.params.map(x => scope.allocateName(x.sym)) ++
          params.restParam.map(x => "..." + scope.allocateName(x.sym))
        val docParams = allParams.mkDocument("(", ", ", ")")
        doc"$docParams => ${bracedbk(print(body))}"
    case Tuple(mut, elems) =>
      val docElems = elems.map(x => print(x)).mkDocument(", ")
      doc"${if mut then "mut " else ""}[${docElems}]"
    case Record(mut, args) =>
      doc"${if mut then "mut " else ""}{ ${
        args.map(x => x.idx.fold(doc"...")(p => print(p) :: ": ") :: print(x.value)).mkDocument(", ")
      } }"
    case x: Path => print(x)
  
  def print(imports: Ls[ImportSymbol -> Str])(using Scope): Document =
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
  
