package mlscript.utils


class Identity[T <: AnyRef](val value: T) {
  
  override def equals(other: Any): Boolean = other match {
    case that: Identity[_] => (that.value: Any) is this.value
    case _ => false
  }
  
  override def hashCode(): Int = System.identityHashCode(value)
  
}

