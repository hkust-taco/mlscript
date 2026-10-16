package hkmc2
package codegen

import hkmc2.utils.*, shorthands.*
import semantics.*


/** The runtime binding shared by the interpretations of a member name.
  * Explicit function companions carry the class value on the function. Otherwise the IR class
  * owns the binding, including its generated constructor and companion module. Private bindings
  * need distinct storage so they cannot replace inherited public properties with the same name.
  */
object MemberStorage:
  def symbol(sym: DefinitionSymbol[?]): DefinitionSymbol[?] = sym match
    case ctor: ClassCtorSymbol => symbol(ctor.associatedCls)
    case cls: BaseTypeSymbol => cls.irTermCompanion match
      case S(_: ClassCtorSymbol) | N => cls.irClassContainer.asDefnSym
      case S(term) => term
    case _ => sym
  
  /** An absent owner denotes ordinary public/local storage. Read current IR definitions so
    * copied classes and synthetic modules do not depend on stale semantic definitions. */
  def privateOwner(sym: DefinitionSymbol[?]): Opt[InnerSymbol] = symbol(sym) match
    case term: TermSymbol => term.owner.filter(_ => term.isPrivate)
    case cls: InnerSymbol => cls.asDefnSym.irClsLikeDefn.flatMap: definition =>
      if (definition.visibility is Visibility.Private) && definition.companion.forall(_.visibility is Visibility.Private)
      then definition.owner.filterNot(_.isInstanceOf[TopLevelSymbol])
      else N
    case _ => N
  
end MemberStorage
