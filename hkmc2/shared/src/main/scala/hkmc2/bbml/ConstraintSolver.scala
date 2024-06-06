package hkmc2
package bbml

import scala.collection.mutable

type Cache = mutable.HashSet[(Type, Type)]
class ConstraintSolver(raise: Raise):
  // TODO: sort dnf
  // TODO: lowerbound & upperbound fun?
  private def constrainDNF(disj: NormalForm.Disj)(using cache: Cache) = () // TODO

  private def constrainImpl(lhs: Type, rhs: Type)(using cache: Cache) =
    if cache((lhs, rhs)) then () else constrainDNF(NormalForm.dnf(Type.ComposedType(lhs, Type.NegType(rhs), false))(using raise))
  def constrain(lhs: Type, rhs: Type): Unit =
    constrainImpl(lhs, rhs)(using mutable.HashSet.empty)
