package hkmc2.io

import org.scalatest.funsuite.AnyFunSuite
import hkmc2.utils.*, shorthands.*


class VirtualPathTests extends AnyFunSuite:
  
  test("basic path creation and toString"):
    val path = VirtualPath("foo/bar")
    assert(path.toString == "foo/bar")
  
  test("/ operator with simple fragment"):
    val path = VirtualPath("foo")
    val result = path / "bar"
    assert(result.toString == "foo/bar")
  
  test("/ operator with fragment starting with ."):
    val path = VirtualPath("foo")
    val result = path / "./bar"
    assert(result.toString == "foo/bar", "Current directory '.' should be removed")
  
  test("/ operator with fragment starting with ./"):
    val path = VirtualPath("foo/baz")
    val result = path / "./bar"
    assert(result.toString == "foo/baz/bar", "Current directory '.' should be removed")
  
  test("/ operator with fragment containing .."):
    val path = VirtualPath("foo/baz")
    val result = path / "../bar"
    assert(result.toString == "foo/bar", "Parent directory '..' should navigate up one level")
  
  test("/ operator with multiple .. segments"):
    val path = VirtualPath("a/b/c")
    val result = path / "../../d"
    assert(result.toString == "a/d", "Multiple '..' should navigate up multiple levels")
  
  test("/ operator with . in the middle of path"):
    val path = VirtualPath("foo")
    val result = path / "bar/./baz"
    assert(result.toString == "foo/bar/baz", "Current directory '.' in middle should be removed")
  
  test("/ operator with .. in the middle of path"):
    val path = VirtualPath("foo")
    val result = path / "bar/../baz"
    assert(result.toString == "foo/baz", "Parent directory '..' in middle should collapse segments")
  
  test("/ operator with absolute path"):
    val path = VirtualPath("/abs/path")
    val result = path / "./file.txt"
    assert(result.toString == "/abs/path/file.txt", "Should work with absolute paths")
  
  test("/ operator with RelPath containing ."):
    val path = VirtualPath("foo")
    val relPath = VirtualRelPath("./bar")
    val result = path / relPath
    assert(result.toString == "foo/bar", "RelPath with '.' should be normalized")
  
  test("/ operator with RelPath containing .."):
    val path = VirtualPath("foo/baz")
    val relPath = VirtualRelPath("../bar")
    val result = path / relPath
    assert(result.toString == "foo/bar", "RelPath with '..' should be normalized")
  
  test("/ operator with RelPath containing multiple . and .."):
    val path = VirtualPath("a/b")
    val relPath = VirtualRelPath("./c/../d")
    val result = path / relPath
    assert(result.toString == "a/b/d", "Complex RelPath should be normalized")
  
  test("normalization with too many .. segments"):
    val path = VirtualPath("foo")
    val result = path / "../../bar"
    assert(result.toString == "../bar", "Extra '..' should be preserved for relative paths")
  
  test("normalization resulting in just ."):
    val path = VirtualPath("foo")
    val result = path / ".."
    assert(result.toString == ".", "Navigating up from single segment should result in '.'")
  
  test("/ operator with trailing slash"):
    val path = VirtualPath("foo/")
    val result = path / "bar"
    assert(result.toString == "foo/bar", "Should handle trailing slash correctly")
  
  test("path segments"):
    val path = VirtualPath("foo/bar/baz")
    assert(path.segments == List("foo", "bar", "baz"))
  
  test("last segment"):
    val path = VirtualPath("foo/bar/baz.txt")
    assert(path.last == "baz.txt")
  
  test("baseName"):
    val path = VirtualPath("foo/bar/baz.txt")
    assert(path.baseName == "baz")
  
  test("ext"):
    val path = VirtualPath("foo/bar/baz.txt")
    assert(path.ext == "txt")
  
  test("up"):
    val path = VirtualPath("foo/bar/baz")
    assert(path.up.toString == "foo/bar")
  
  test("isAbsolute - relative path"):
    val path = VirtualPath("foo/bar")
    assert(!path.isAbsolute)
  
  test("isAbsolute - absolute path"):
    val path = VirtualPath("/foo/bar")
    assert(path.isAbsolute)
  
  test("complex normalization case"):
    val path = VirtualPath("a/b/c")
    val result = path / "./d/../e/./f"
    assert(result.toString == "a/b/c/e/f", "Complex path with mixed . and .. should normalize correctly")
  
  test("normalization with only ."):
    val path = VirtualPath("foo")
    val result = path / "."
    assert(result.toString == "foo", "Single '.' should result in same path")
  
  test("normalization preserves absolute paths"):
    val path = VirtualPath("/a/b")
    val result = path / "../c"
    assert(result.toString == "/a/c", "Absolute paths should remain absolute after normalization")
  
  test("RelPath / operator"):
    val rel1 = VirtualRelPath("foo/bar")
    val rel2 = VirtualRelPath("baz")
    val result = rel1 / rel2
    assert(result.toString == "foo/bar/baz")
  
  // * Paths are used as keys, both of the compilation-unit cache and of the file system,
  // * so paths built from strings must be canonical and not just those built with `/`.
  
  test("paths built from a string are normalized"):
    assert(Path("/a/./b.mls").toString == "/a/b.mls", "'.' should be removed")
    assert(Path("/a//b.mls").toString == "/a/b.mls", "Repeated separators should be collapsed")
    assert(Path("/a/c/../b.mls").toString == "/a/b.mls", "'..' should be resolved")
    assert(Path("/a/b/").toString == "/a/b", "Trailing separators should be removed")
    assert(Path("./a/b.mls").toString == "a/b.mls", "Leading '.' should be removed")
  
  test("spellings of the same path are equal and usable as one key"):
    val spellings = Ls("/a/b.mls", "/a/./b.mls", "/a//b.mls", "/a/c/../b.mls", "/./a/b.mls")
    val paths = spellings.map(Path(_))
    paths.foreach: p =>
      assert(p == paths.head, s"'$p' should equal '${paths.head}'")
      assert(p.hashCode == paths.head.hashCode, s"'$p' should hash like '${paths.head}'")
    assert(paths.toSet.sizeIs == 1, "All spellings should collapse to a single key")
  
  test("a path built from a string matches the same path built with /"):
    assert(Path("/a") / RelPath("./b.mls") == Path("/a/b.mls"))
    assert(Path("/a/b") / RelPath("../c.mls") == Path("/a/c.mls"))

  test("'..' is resolved against the most recent segment, not the first one"):
    // * Only unresolvable leading `..` may be kept; a `..` following a real segment must pop it,
    // * even when the path starts with `..`.
    assert(Path("../a/..").toString == "..")
    assert(Path("../a/b/../..").toString == "..")
    assert(Path("../../a/..").toString == "../..")

  test("absolute paths cannot escape above the root"):
    assert(Path("/../a").toString == "/a")
    assert(Path("/a/../..").toString == "/")

  test("in-memory filesystem string paths use the same normalized keys"):
    val fs = new InMemoryFileSystem(Map("/a/./b.mls" -> "initial"))
    assert(fs.read("/a/b.mls") == "initial")
    fs.write("/a/c/../b.mls", "updated")
    assert(fs.read("/a/./b.mls") == "updated")
