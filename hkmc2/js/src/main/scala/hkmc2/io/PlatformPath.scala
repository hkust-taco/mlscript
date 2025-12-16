package hkmc2
package io

/**
 * Platform-specific factory for creating Path instances
 */
private[io] object PathFactory:
  def fromString(str: String) = new VirtualPath(str)
  def separator: String = VirtualPath.sep
  def relPathFromString(str: String) = new VirtualRelPath(str)
  def relPathUp = new VirtualRelPath("..")
