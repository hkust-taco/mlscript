package hkmc2
package io

private[io] object PlatformFileSystem:
  def default: FileSystem = new node.NodeFileSystem
