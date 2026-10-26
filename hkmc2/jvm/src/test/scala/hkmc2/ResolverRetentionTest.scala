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
          value.isInstanceOf[ResolutionWorkspace] || value.isInstanceOf[DeclaredType.References] || (value eq collector)
      assert(retained.isEmpty, retained.getOrElse(""))
