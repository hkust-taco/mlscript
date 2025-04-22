package hkmc2.codegen.llir

final class FreshInt:
  private var counter = 0
  def make: Int = {
    val tmp = counter
    counter += 1
    tmp
  }

