package simplesub

import scala.util.chaining._
import scala.collection.mutable.{Map => MutMap, SortedMap => SortedMutMap, Set => MutSet}
import scala.collection.immutable.SortedSet


// Helper methods for simple types

abstract class TypeImpl { self: Type =>
  
  lazy val typeVars: Set[TypeVar] = this match {
    case uv: TypeVar => Set(uv)
    case Recursive(n, b) => b.typeVars - n
    case _ => children.iterator.flatMap(_.typeVars).toSet
  }
  
  protected def conjuncts: List[PlainType] = this match {
    case Top => Nil
    case Inter(l, r) => l.conjuncts ::: r.conjuncts
    case ty: PlainType => ty :: Nil
    case _ => throw new AssertionError(s"wrong mix of polarities: $this")
  }
  protected def disjuncts: List[PlainType] = this match {
    case Bot => Nil
    case Union(l, r) => l.disjuncts ::: r.disjuncts
    case ty: PlainType => ty :: Nil
    case _ => throw new AssertionError(s"wrong mix of polarities: $this")
  }
  lazy val normalize: Type = {
    def merge(components: List[Type])(pol: Boolean): Type = {
      val atoms = components.collect { case a: Atom => a }
      val funs = components.collect { case Function(l, r) => (l, r) }
      val rcds = components.collect { case Record(fs) => fs }
      val recs = components.collect { case r @ Recursive(_, _) => r }
      val (extr: Type, mrg, grm) = if (pol) (Bot, Union, Inter) else (Top, Inter, Union)
      val fun = funs.reduceOption[(Type, Type)] { case ((l0,r0), (l1,r1)) => (grm(l0,l1), mrg(r0,r1)) }
      val rcd = rcds.reduceOption { (fs0, fs1) =>
        if (pol) {
          val fs1m = fs1.toMap
          fs0.flatMap { case (k, v) => fs1m.get(k).map(k -> mrg(v, _)) }
        } else mergeMaps(fs0.toMap, fs1.toMap)(mrg).toList
      }
      val normalized =
        atoms.distinct.sortBy(_.hash) :::
        fun.map(lr => Function(lr._1.normalize, lr._2.normalize)).toList :::
        rcd.map(fs => Record(fs.map(nt => nt._1 -> nt._2.normalize).sortBy(_._1))).toList :::
        recs.map(r => Recursive(r.uv, r.body.normalize)).sortBy(_.uv.hash)
      normalized.reduceOption(mrg).getOrElse(extr)
    }
    this match {
      case Bot | Union(_, _) => merge(disjuncts)(true)
      case Top | Inter(_, _) => merge(conjuncts)(false)
      case Record(Nil) => Top
      case Record(fs) => Record(fs.map(nt => nt._1 -> nt._2.normalize))
      case Function(l, r) => Function(l.normalize, r.normalize)
      case Recursive(v, b) => Recursive(v, b.normalize)
      case _: NullaryType => this
    }
  }
  
  def show: String = this match {
    case Top => "⊤"
    case Bot => "⊥"
    case Primitive(name) => name
    case uv: TypeVar => uv.nameHint + uv.hash
    case Recursive(n, b) => s"${b.show} as ${n.nameHint+n.hash}"
    case Function(l, r) => s"(${l.show} -> ${r.show})"
    case Record(fs) => fs.map(nt => s"${nt._1}: ${nt._2.show}").mkString("{", ", ", "}")
    case Union(l, r) => s"(${l.show} ∨ ${r.show})"
    case Inter(l, r) => s"(${l.show} ∧ ${r.show})"
  }
  
  def children: List[Type] = this match {
    case _: NullaryType => Nil
    case Function(l, r) => l :: r :: Nil
    case Record(fs) => fs.map(_._2)
    case Union(l, r) => l :: r :: Nil
    case Inter(l, r) => l :: r :: Nil
    case Recursive(n, b) => b :: Nil
  }
  
  def map(f: Type => Type): Type = this match {
    case _: NullaryType => this
    case Function(l, r) => Function(f(l), f(r))
    case Record(fs) => Record(fs.map(nt => nt._1 -> f(nt._2)))
    case Union(l, r) => Union(f(l), f(r))
    case Inter(l, r) => Inter(f(l), f(r))
    case Recursive(n, b) => Recursive(n, f(b))
  }
  
}


// Helper methods for normalized polar type representations

abstract class PolarityImpl { pol: Polarity =>
  
  private lazy val mergeString = " " + mergeSymbol + " "
  
  def merge(lhs: Type, rhs: Type): Type = (lhs.rec, rhs.rec).pipe {
      case (Some(rec0), Some(rec1)) => rhs.substVar(rec1, rec0)
      case _ => rhs
    }.pipe { rhs =>
      val fields = mergeOptions(lhs.fields, rhs.fields)(mergeFields)
      val fun = mergeOptions(lhs.fun, rhs.fun){
        case ((l0,r0), (l1,r1)) => (Negated.merge(l0, l1), merge(r0, r1)) }
      val newRec = lhs.rec orElse rhs.rec
      val newAtoms = (lhs.atoms ++ rhs.atoms).filterNot(newRec.contains[Atom]) // comply with invariant
      Type(newAtoms, fields, fun, newRec)
    }
  
  abstract class TypeImpl { self: Type =>
    
    def substVar(uv0: TypeVar, uv1: TypeVar): Type = {
      val newRec = if (rec.contains(uv0)) Some(uv1) else rec
      Type(
        atoms.map(v => if (v eq uv0) uv1 else v)
          .filterNot(newRec.contains[Atom]), // to comply with the invariant
        fields.map(_.view.mapValues(_.substVar(uv0, uv1)).toMap),
        fun.map { case (l, r) => (l.substVar(uv0, uv1), r.substVar(uv0, uv1)) },
        newRec
      )
    }
    def substAtom(uv0: TypeVar, uv1: Atom): Type =
      if (rec.contains(uv0)) empty.copy(atoms = Set(uv1))
      // ^ substituting an 'as' type replaces the whole thing!
      else Type(
        atoms.map(v => if (v eq uv0) uv1 else v)
          .filterNot(rec.contains[Atom]), // to comply with the invariant
        fields.map(_.view.mapValues(_.substAtom(uv0, uv1)).toMap),
        fun.map { case (l, r) => (l.substAtom(uv0, uv1), r.substAtom(uv0, uv1)) },
        rec
      )
    
    lazy val typeVars: Set[TypeVar] =
      atoms.collect { case uv: TypeVar => uv } ++
        fields.iterator.flatMap(_.valuesIterator.flatMap(_.typeVars)) ++
        fun.iterator.flatMap(lr => lr._1.typeVars ++ lr._2.typeVars) -- rec.toList
    
    private def sortedFields = fields.toList.flatMap(_.toList).sortBy(_._1)
    
    def variableOccurrences: List[TypeVar] = rec.toList ++
      atoms.iterator.collect { case uv: TypeVar => uv }.toList.sortBy(_.hash) ++
      sortedFields.flatMap(_._2.variableOccurrences) ++
      fun.iterator.flatMap(lr => lr._1.variableOccurrences ++ lr._2.variableOccurrences)
    
    /** Computes the set of polar co-occurrences for all variables present in this Type. */
    def coOccurrences: collection.Map[(TypeVar, Polarity), SortedSet[Atom]] = {
      val allAtoms = SortedSet.from(atoms) ++ rec.iterator
      val base = allAtoms.iterator.collect { case tv: TypeVar => (tv -> pol) -> allAtoms }
      val rest =
        fields.iterator.flatMap(_.iterator).flatMap(nt => nt._2.coOccurrences.iterator) ++
        fun.iterator.flatMap(pa => pa._1.coOccurrences.iterator ++ pa._2.coOccurrences.iterator)
      val res = SortedMutMap.empty[(TypeVar, Polarity), SortedSet[Atom]]
      (base ++ rest).foreach { case (k, v) =>
        res(k) = res.get(k) match {
          case Some(v2) => v & v2
          case None => v
        }
      }
      res
    }
    
    // Idea: if a type var 'a always occurs positively (resp. neg) along with some 'b AND vice versa,
    //      this means that the two are undistinguishable, and they can therefore be unified.
    //    Ex: ('a & 'b) -> ('a, 'b) is the same as 'a -> ('a, 'a)
    //    Ex: ('a & 'b) -> 'b -> ('a, 'b) is NOT the same as 'a -> 'a -> ('a, 'a)
    //      there is no value of 'a that can make 'a -> 'a -> ('a, 'a) <: (a & b) -> b -> (a, b) work
    //      we'd require 'a :> b | a & b <: a & b, which are NOT valid bounds!
    //    Ex: 'a -> 'b -> 'a | 'b is the same as 'a -> 'a -> 'a
    //    Justification: the other var 'b can always be taken to be 'a & 'b (resp. a | b)
    //      without loss of gen. Indeed, on the pos side we'll have 'a <: 'a & 'b and 'b <: 'a & 'b
    //      and on the neg side, we'll always have 'a and 'b together, i.e., 'a & 'b
    // Additional idea: remove variables which always occur both positively AND negatively together
    //      with some other type.
    //    This would arise from constraints such as: 'a :> Int <: 'b and 'b <: Int
    //      (contraints which basically say 'a =:= 'b =:= Int)
    //    Ex: 'a ∧ Int -> 'a ∨ Int is the same as Int -> Int
    //    Currently, we only do this for Ctor types.
    //    In principle it could be done for functions and records, too.
    //    Note: conceptually, this idea subsumes the simplification that removes variables occurring
    //        exclusively in positive or negative positions.
    //      Indeed, if 'a never occurs positively, it's like it always occurs both positively AND
    //      negatively along with the type Bot, so we can replace it with Bot.
    //      However, this specific optim is already done in the type expansion algorithm.
    def trySimplify: Option[Type] = {
      val oc = coOccurrences
      oc.toList.sortBy(_._1).foreach { case ((tv1, pol), as) =>
        as.toList.sortBy(_.hash).foreach { case tv2: TypeVar if !(tv2 is tv1) =>
          if (oc(tv2 -> pol)(tv1)) return Some(substVar(tv2, tv1))
          else ()
        case atom: Primitive if (oc.get(tv1, !pol).exists(_(atom))) =>
          return Some(substAtom(tv1, atom))
        case _ => ()
        }
      }
      None
    }
    /** Simplifies a Type based on co-occurrence analysis. */
    def simplify: Type = trySimplify.fold(this)(_.simplify)
    
    def showIn(ctx: Map[TypeVar, String], outerPrec: Int): String = {
      val firstComponents =
        (if (fields.forall(_.isEmpty)) Nil
          else sortedFields.iterator.map(nt => s"${nt._1}: ${nt._2.showIn(ctx, 0)}")
                .mkStringOr(", ", "{", "}") :: Nil
        ) ++ atoms.toList.sortBy(_.hash).map {
              case uv: TypeVar => ctx(uv)
              case Primitive(name) => name }
      val funStr = fun.map { lr =>
        val str = lr._1.showIn(ctx, 2) + " -> " + lr._2.showIn(ctx, 1)
        if (firstComponents.nonEmpty) "(" + str + ")" else str }
      val components = firstComponents ++ funStr
      val body = components.mkStringOr(mergeString,
        els = if (fields.isEmpty) extremumSymbol else Negated.extremumSymbol)
      val innerPrec = if (fun.nonEmpty) 1 else 2
      val realOuterPrec = if (rec.nonEmpty) if (fun.nonEmpty) 3 else 0 else outerPrec
      val needsParens = innerPrec < realOuterPrec
      val withParens = if (needsParens) s"(${body})" else body
      rec.fold(withParens)(r => withParens + " as " + ctx(r))
    }
    
    def show: String = {
      val vars = variableOccurrences.distinct
      val ctx = vars.zipWithIndex.map {
        case (tv, idx) =>
          def nme = {
            assert(idx <= 'z' - 'a', "TODO handle case of not enough chars")
            ('a' + idx).toChar.toString
          }
          tv -> ("'" + nme)
      }.toMap
      showIn(ctx, 0)
    }
    
  }
  
}
