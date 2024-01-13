package mlscript.ucs.old

import mlscript._
import mlscript.utils._
import mlscript.utils.shorthands._
import scala.collection.immutable.Set
import scala.collection.mutable.{Set => MutSet, Buffer}

final case class LetBinding(val kind: LetBinding.Kind, val recursive: Bool, val name: Var, val term: Term)

object LetBinding {
  sealed abstract class Kind

  object Kind {
    case object ScrutineeAlias extends Kind {
      override def toString: String = "scrutinee alias"
    }
    case object FieldExtraction extends Kind {
      override def toString: String = "pattern destruction"
    }
    case object InterleavedLet extends Kind {
      override def toString: String = "interleaved let"
    }
  }
}

trait WithBindings { this: MutCaseOf =>
  private val bindingsSet: MutSet[LetBinding] = MutSet.empty
  private val bindings: Buffer[LetBinding] = Buffer.empty

  def addBindings(newBindings: IterableOnce[LetBinding]): Unit = {
    newBindings.iterator.foreach {
      case binding if bindingsSet.contains(binding) => ()
      case binding =>
        bindingsSet += binding
        bindings += binding
    }
  }

  def getBindings: Iterable[LetBinding] = bindings

  def withBindings(newBindings: IterableOnce[LetBinding]): MutCaseOf = {
    addBindings(newBindings)
    this
  }
}
