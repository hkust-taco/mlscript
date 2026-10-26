package hkmc2
package semantics

import java.lang.reflect.Modifier
import org.scalatest.funsuite.AnyFunSuite
import scala.collection.mutable
import scala.jdk.CollectionConverters.*

import hkmc2.utils.*, shorthands.*
import io.PlatformPath.given


/** Diff tests cannot observe whether a completed artifact keeps its compilation
  * session alive. Walk strong references instead of relying on GC timing, and
  * report a retaining path when the lifetime contract is violated.
  */
class ResolverRetentionTest extends AnyFunSuite:
  private final class DiagnosticCollector:
    val diagnostics = mutable.ArrayBuffer.empty[Diagnostic]
    def report(diagnostic: Diagnostic): Unit = diagnostics += diagnostic

  private def fields(value: AnyRef): Iterator[(Str, AnyRef)] =
    def from(cls: Class[?]): Iterator[(Str, AnyRef)] =
      if cls == null || cls == classOf[Object] then Iterator.empty
      else
        val own = cls.getDeclaredFields.iterator.filterNot(field => Modifier.isStatic(field.getModifiers)).flatMap: field =>
          if field.trySetAccessible() then Option(field.get(value)).iterator.map(field.getName -> _)
          else Iterator.empty
        own ++ from(cls.getSuperclass)
    from(value.getClass)

  private def children(value: AnyRef): Iterator[(Str, AnyRef)] = value match
    case value if value.getClass.getName.startsWith("hkmc2.") => fields(value)
    case entries: scala.collection.Map[?, ?] => entries.iterator.zipWithIndex.flatMap:
      case ((key: AnyRef, item: AnyRef), index) => Iterator(s"key[$index]" -> key, s"value[$index]" -> item)
      case _ => Iterator.empty
    case entries: java.util.Map[?, ?] => entries.entrySet.iterator.asScala.zipWithIndex.flatMap:
      case (entry, index) => Iterator(s"key[$index]" -> entry.getKey, s"value[$index]" -> entry.getValue).collect:
        case (name, item: AnyRef) => name -> item
    case array: Array[?] => array.iterator.zipWithIndex.collect:
      case (item: AnyRef, index) => s"[$index]" -> item
    case entries: Iterable[?] => entries.iterator.zipWithIndex.collect:
      case (item: AnyRef, index) => s"[$index]" -> item
    case product: Product => product.productIterator.zipWithIndex.collect:
      case (item: AnyRef, index) => s"_$index" -> item
    case value if value.getClass.getName.startsWith("scala.") => fields(value)
    case _ => Iterator.empty

  private def retainingPath(root: AnyRef)(unwanted: AnyRef => Bool): Opt[Str] =
    val parents = new java.util.IdentityHashMap[AnyRef, (AnyRef, Str)]
    val pending = mutable.Queue(root)
    parents.put(root, (root, "artifact"))
    def path(value: AnyRef): Str =
      val (parent, name) = parents.get(value)
      if value eq root then name else s"${path(parent)}.$name"
    while pending.nonEmpty do
      val value = pending.dequeue()
      if unwanted(value) then return S(s"${path(value)} (${value.getClass.getName})")
      children(value).foreach: (name, child) =>
        if child != null && !parents.containsKey(child) then
          parents.put(child, (value, name))
          pending.enqueue(child)
    N

  private def graphSize(root: AnyRef, state: NewResolverState): (Int, Int, Int) =
    val visited = new java.util.IdentityHashMap[AnyRef, java.lang.Boolean]
    val pending = mutable.Queue(root)
    var listeners = 0
    var candidates = 0
    while pending.nonEmpty do
      val value = pending.dequeue()
      if visited.put(value, java.lang.Boolean.TRUE) == null then
        value match
          case data: Publisher.Data[?] if data.owner eq state =>
            listeners += data.listeners.size
            candidates += data.shapes.size
          case _ => ()
        children(value).foreach: (_, child) =>
          if child != null && !visited.containsKey(child) then pending.enqueue(child)
    val sources = state.owner.resolutionSources
    val metadata = sources.definitions.size + sources.sites.size + sources.parameterSignatures.size + sources.recordReads.size
    (listeners, candidates, metadata)

  // Repeated reads from equal graph contexts must merge their ownership without
  // accumulating tracking records. Diff tests cannot observe that storage bound
  // or verify that pruning releases metadata for entries that remain reachable.
  test("shared cache entries retain all readers with bounded temporary tracking"):
    given owner: Elaborator.State = new Elaborator.State
    val root = owner.newResolverState.context
    val live = TermSymbol(syntax.Fun, N, syntax.Tree.Ident("live"))
    val dead = TermSymbol(syntax.Fun, N, syntax.Tree.Ident("dead"))
    val writing = root.forCode(S(dead))
    val reading = root.forCode(S(live))
    val cache = root.state.reportedArities
    val seen = root.state.arrayIndexErrors
    val shared = new Identity[Term](Term.UnitVal())
    val unused = new Identity[Term](Term.UnitVal())
    cache.update(shared, mutable.Set(1))(using writing)
    cache.update(unused, mutable.Set(2))(using writing)
    assert(seen.add(shared)(using writing))
    assert(seen.add(unused)(using writing))
    (1 to 1000).foreach: _ =>
      assert(cache.get(shared)(using reading).get.toSet == Set(1))
      assert(seen(shared)(using reading))
    assert(cache.uses.size == 2 && seen.uses.size == 2)
    root.state.workspace.retention.finish(_ == live)
    assert(cache.get(shared)(using reading).get.toSet == Set(1))
    assert(cache.get(unused)(using reading).isEmpty)
    assert(seen(shared)(using reading))
    assert(!seen(unused)(using reading))
    List(cache, seen).foreach: table =>
      val retained = retainingPath(table)(_.isInstanceOf[ResolutionRetention.Uses])
      assert(retained.isEmpty, retained.getOrElse(""))

  // Registration count should grow the edge list, not duplicate graph contexts.
  // Also check the distinct owners at invocation: sharing the graph must not
  // attribute all these callbacks to whichever body registered first or last.
  test("listeners share graph origins without retaining their owned execution views"):
    given owner: Elaborator.State = new Elaborator.State
    val root = owner.newResolverState.context
    val bodies = List("first", "second").map(name => S(TermSymbol(syntax.Fun, N, syntax.Tree.Ident(name))))
    val source = new Host[Int]:
      def showDbg(using DebugPrinter): Str = "listener context retention"
    val observed = mutable.ArrayBuffer.empty[Opt[AnyDefinitionSymbol]]
    (1 to 1000).foreach: _ =>
      bodies.foreach: body =>
        val context = root.forCode(body)
        assert(context.graph eq root)
        assert(root == context && context == root && root.hashCode == context.hashCode)
        source.addShapeListener(_ => (current: ResolutionContext) ?=> observed += current.code)(using context)
    source.inferenceHost(using root).publish(1)(using root)
    assert(observed.toList == List.fill(1000)(bodies).flatten)
    val retained = retainingPath(source):
      case context: ResolutionContext => context.code.nonEmpty
      case _ => false
    assert(retained.isEmpty, retained.getOrElse(""))

  test("unreachable generic bodies do not grow a compiled interface's retained inference graph"):
    val cctx = TestFolders.compilerCtx(os.pwd)
    given DebugPrinter = new DebugPrinter()
    val trace = TraceLogger.silent
    val collector = new DiagnosticCollector
    given Raise = collector.report
    val prelude = cctx.getPrelude(cctx.paths.preludeFile)(using trace, summon[Raise]).ctx
    def measure(unused: Int): (Int, Int, Int) =
      val dir = os.temp.dir(prefix = "resolver-dead-code-")
      val file = dir / "Library.mls"
      val definitions = (1 to unused).map(index =>
        s"""  private fun unused$index[A](value: A) =
           |    fun wrap[B](item: B) = [item, {stored: item}]
           |    wrap[A](value)""".stripMargin).mkString("\n")
      os.write(file,
        s"""#lang(0.3.x, strictResolution: true)
           |module Library with
           |  private fun forward[A](value: A) = value
           |  fun identity[A](value: A) = forward(value)
           |$definitions
           |""".stripMargin)
      val artifact = cctx.getElaboratedBlock(file, prelude)(using trace, summon[Raise])
      assert(collector.diagnostics.isEmpty, collector.diagnostics.map(_.theMsg).mkString("\n"))
      graphSize(artifact, artifact.state.newResolverState)
    val small = measure(1)
    val large = measure(40)
    assert(large == small, s"Unused bodies retained listeners/candidates/metadata: $small -> $large")

  test("compiled artifacts release compilation services, workspaces, and interning builders"):
    val cctx = TestFolders.compilerCtx(os.pwd)
    given DebugPrinter = new DebugPrinter()
    val trace = TraceLogger.silent
    val collector = new DiagnosticCollector
    given Raise = collector.report
    val prelude = cctx.getPrelude(cctx.paths.preludeFile)(using trace, summon[Raise]).ctx
    val dir = os.temp.dir(prefix = "resolver-retention-")
    val file = dir / "Library.mls"
    os.write(file,
      """#lang(0.3.x, strictResolution: true)
        |module Library with
        |  class Item(val value: Int)
        |  private fun forward[A](value: A) = value
        |  fun identity[A](value: A) = forward(value)
        |  fun example() = identity(Item(1)).value
        |  class Child(val extra: Int) extends Item(1)
        |  fun captured[A](value: A) = () => forward(value)
        |  fun annotated(callback: Int -> Int): Int = callback(1)
        |  fun rest(...values: Array[Int]): Int = values.length
        |  fun optional(value?: Int) = value
        |  @annotations.bufferable
        |  class Buffered with
        |    fun read(): Int = 1
        |""".stripMargin)
    val artifact = cctx.getElaboratedBlock(file, prelude)(using trace, summon[Raise])
    assert(collector.diagnostics.isEmpty, collector.diagnostics.map(_.theMsg).mkString("\n"))
    val originalSize = graphSize(artifact, artifact.state.newResolverState)
    val consumer = dir / "Consumer.mls"
    os.write(consumer,
      """#lang(0.3.x, strictResolution: true)
        |import "./Library.mls"
        |module Consumer with
        |  fun read(): Int = Library.Buffered.read(null, 0)()
        |""".stripMargin)
    val imported = cctx.getElaboratedBlock(consumer, prelude)(using trace, summon[Raise])
    assert(collector.diagnostics.isEmpty, collector.diagnostics.map(_.theMsg).mkString("\n"))
    assert(graphSize(artifact, artifact.state.newResolverState) == originalSize,
      "Observing a generated member must not extend the finished exporter's graph or metadata")
    List(artifact, imported).foreach: root =>
      val retained = retainingPath(root): value =>
        value.isInstanceOf[Elaborator] || value.isInstanceOf[CompilerCtx] ||
          value.isInstanceOf[ResolutionWorkspace] || value.isInstanceOf[ResolutionRetention.Uses] ||
          value.isInstanceOf[DeclaredType.References] || (value eq collector)
      assert(retained.isEmpty, retained.getOrElse(""))
