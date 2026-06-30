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
