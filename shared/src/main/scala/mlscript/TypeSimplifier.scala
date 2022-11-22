package mlscript

import scala.collection.mutable.{Map => MutMap, Set => MutSet, LinkedHashMap, LinkedHashSet}
import scala.collection.immutable.{SortedMap, SortedSet}
import scala.util.chaining._
import mlscript.utils._, shorthands._

trait TypeSimplifier { self: Typer =>
  
  
  
  /** Remove bounds that are not reachable by traversing the type, following variances.
    * Note that doing this on annotated type signatures would need to use polarity None
    *   because a type signature can both be used (positively) and checked against (negatively). */
  def removeIrrelevantBounds(ty: SimpleType, pol: Opt[Bool] = S(true), inPlace: Bool = false)
        (implicit ctx: Ctx): SimpleType =
  {
    
    val pols = ty.getVarsPol(S(true))
    
    println(s"Pols ${pols}")
    
    val renewed = MutMap.empty[TypeVariable, TypeVariable]
    
    def renew(tv: TypeVariable): TypeVariable =
      renewed.getOrElseUpdate(tv,
        if (inPlace) tv
        else freshVar(noProv, tv.nameHint)(tv.level) tap { fv => println(s"Renewed $tv ~> $fv") })
    
    def process(ty: ST, parent: Opt[Bool -> TV]): ST =
        // trace(s"process($ty)") {
        ty match {
      
      case tv: TypeVariable =>
        parent.filter(_._2 === tv).foreach(p => return ExtrType(p._1)(noProv))
        
        var isNew = false
        val nv = renewed.getOrElseUpdate(tv, { isNew = true; renew(tv) })
        
        if (isNew) {
          nv.lowerBounds = if (pols(tv).forall(_ === true))
              tv.lowerBounds.iterator.map(process(_, S(true -> tv))).reduceOption(_ | _).filterNot(_.isBot).toList
            else Nil
          nv.upperBounds = if (pols(tv).forall(_ === false))
              tv.upperBounds.iterator.map(process(_, S(false -> tv))).reduceOption(_ & _).filterNot(_.isTop).toList
            else Nil
        }
        
        nv
        
      case ComposedType(true, l, r) => process(l, parent) | process(r, parent)
      case ComposedType(false, l, r) => process(l, parent) & process(r, parent)
      case NegType(ty) => process(ty, parent.map(_.mapFirst(!_))).neg(ty.prov)

      case ProvType(ty) if inPlace => ProvType(process(ty, parent))(ty.prov)
      case ProvType(ty) => process(ty, parent)
      
      case tr @ TypeRef(defn, targs) if builtinTypes.contains(defn) => process(tr.expand, parent)
      
      case RecordType(fields) => RecordType.mk(fields.flatMap { case (v @ Var(fnme), fty) =>
        // * We make a pass to transform the LB and UB of variant type parameter fields into their exterma
        val prefix = fnme.takeWhile(_ =/= '#')
        val postfix = fnme.drop(prefix.length + 1)
        lazy val default = fty.update(process(_ , N), process(_ , N))
        if (postfix.isEmpty) v -> default :: Nil
        else {
          val td = ctx.tyDefs(prefix)
          td.tvarVariances.fold(v -> default :: Nil)(tvv =>
            tvv(td.tparamsargs.find(_._1.name === postfix).getOrElse(die)._2) match {
              case VarianceInfo(true, true) => Nil
              case VarianceInfo(co, contra) =>
                if (co) v -> FieldType(S(BotType), process(fty.ub, N))(fty.prov) :: Nil
                else if (contra) v -> FieldType(fty.lb.map(process(_, N)), TopType)(fty.prov) :: Nil
                else  v -> default :: Nil
            })
        }
      })(ty.prov)
      
      case _ => ty.mapPol(N)((_, ty) => process(ty, N))
      
    }
    // }(r => s"= $r")
    
    process(ty, N)
    
  }
  
  
  
  /** Transform the type recursively, putting everything in Disjunctive Normal Forms and reconstructing class types
    * from their structural components. */
  def normalizeTypes_!(st: SimpleType, pol: Opt[Bool] = S(true))(implicit ctx: Ctx): SimpleType =
  {
    
    val allVarPols = st.getVarsPol(pol)
    println(s"allVarPols: ${allVarPols.iterator.map(e => s"${printPol(e._2)}${e._1}").mkString(", ")}")
    
    val processed = MutSet.empty[TV]
    
    def helper(dnf: DNF, pol: Opt[Bool]): ST =
    {
      println(s"DNF: $dnf")
      
      val cs = dnf.cs
      val (csNegs, otherCs) = cs.partitionMap {
        case c @ Conjunct(l, vs, r, nvs) if l.isTop && vs.isEmpty && !(r.isBot && nvs.isEmpty) =>
          // L(r, nvs)
          L(c)
        case c => R(c)
      }
      
      // * The goal here is to normalize things like `... | ~A | ~B | ~C` the same as we would `... | ~T`
      // *  where `T` is `A & B & C`.
      // * It is fine to call `go` because we made sure A, B, C, etc. do not themsleves have any negative components.
      val csNegs2 = if (csNegs.isEmpty) BotType
        else go(csNegs.foldLeft(TopType: ST)(_ & _.toType().neg()), pol.map(!_)).neg()
      
      val otherCs2 = otherCs.sorted.map { c =>
        c.vars.foreach(processVar)
        c.nvars.foreach(processVar)
        
        c.toTypeWith(_ match {
          
          case LhsRefined(bo, tts, rcd, trs) =>
            // * The handling of type parameter fields is currently a little wrong here,
            // *  because we remove:
            // *    - type parameter fields of parent classes,
            // *        whereas they could _in principle_ be refined and
            // *        not correspond exactly to these of the currenly-reconstructed class;
            // *        and
            // *    - type parameter fields of the current trait tags
            // *        whereas we don't actually reconstruct applied trait types...
            // *        it would be better to just reconstruct them (TODO)
            
            val trs2 = trs.map {
              case (d, tr @ TypeRef(defn, targs)) =>
                d -> TypeRef(defn, tr.mapTargs(pol)((pol, ta) => go(ta, pol)))(tr.prov)
            }
            
            val traitPrefixes =
              tts.iterator.collect{ case TraitTag(Var(tagNme)) => tagNme.capitalize }.toSet
            
            bo match {
              case S(cls @ ClassTag(Var(tagNme), ps)) if !primitiveTypes.contains(tagNme) =>
                val clsNme = tagNme.capitalize
                val clsTyNme = TypeName(tagNme.capitalize)
                val td = ctx.tyDefs(clsNme)
                
                val rcdMap  = rcd.fields.toMap
                
                val rcd2  = rcd.copy(rcd.fields.mapValues(_.update(go(_, pol.map(!_)), go(_, pol))))(rcd.prov)
                println(s"rcd2 ${rcd2}")
                
                val vs = td.getVariancesOrDefault
                
                // * Reconstruct a TypeRef from its current structural components
                val typeRef = TypeRef(td.nme, td.tparamsargs.zipWithIndex.map { case ((tp, tv), tpidx) =>
                  val fieldTagNme = tparamField(clsTyNme, tp)
                  val fromTyRef = trs2.get(clsTyNme).map(_.targs(tpidx) |> { ta => FieldType(S(ta), ta)(noProv) })
                  fromTyRef.++(rcd2.fields.iterator.filter(_._1 === fieldTagNme).map(_._2))
                    .foldLeft((BotType: ST, TopType: ST)) {
                      case ((acc_lb, acc_ub), FieldType(lb, ub)) =>
                        (acc_lb | lb.getOrElse(BotType), acc_ub & ub)
                    }.pipe {
                      case (lb, ub) =>
                        vs(tv) match {
                          case VarianceInfo(true, true) => TypeBounds.mk(BotType, TopType)
                          case VarianceInfo(false, false) => TypeBounds.mk(lb, ub)
                          case VarianceInfo(co, contra) =>
                            if (co) ub else lb
                        }
                    }
                })(noProv)
                println(s"typeRef ${typeRef}")
                
                val clsFields = fieldsOf(typeRef.expandWith(paramTags = true), paramTags = true)
                println(s"clsFields ${clsFields.mkString(", ")}")
                
                val cleanPrefixes = ps.map(_.name.capitalize) + clsNme ++ traitPrefixes
                
                val cleanedRcd = RecordType(
                  rcd2.fields.filterNot { case (field, fty) =>
                    // * This is a bit messy, but was the only way I was able to achieve maximal simplification:
                    // *  We remove fields that are already inclued by definition of the class by testing for subtyping
                    // *  with BOTH the new normalized type (from `clsFields`) AND the old one too (from `rcdMap`).
                    // *  The reason there's a difference is probably because:
                    // *    - Subtye checking with <:< is an imperfect heuristic and may stop working after normalizing.
                    // *    - Recursive types will be normalized progressively...
                    // *        at this point we may look at some bounds that have not yet been normalized.
                    clsFields.get(field).exists(cf => cf <:< fty ||
                      rcdMap.get(field).exists(cf <:< _))
                  }
                )(rcd2.prov)
                
                val rcd2Fields  = rcd2.fields.unzip._1.toSet
                
                // * Which fields were NOT part of the original type,
                // *  and should therefore be excluded from the reconstructed TypeRef:
                val removedFields = clsFields.keysIterator
                  .filterNot(field => field.name.isCapitalized || rcd2Fields.contains(field)).toSortedSet
                val withoutType = if (removedFields.isEmpty) typeRef
                  else typeRef.without(removedFields)
                
                // * Whether we need a `with` (which overrides field types)
                // *  as opposed to simply an intersection (which refines them):
                val needsWith = !rcd2.fields.forall {
                  case (field, fty) =>
                    clsFields.get(field).forall(cf => fty <:< cf || rcdMap.get(field).exists(_ <:< cf))
                }
                val withType = if (needsWith) if (cleanedRcd.fields.isEmpty) withoutType
                  else WithType(withoutType, cleanedRcd.sorted)(noProv) else typeRef & cleanedRcd.sorted
                
                val withTraits = tts.toArray.sorted // TODO also filter out tts that are inherited by the class
                  .foldLeft(withType: ST)(_ & _)
                
                val trs3 = trs2 - td.nme // TODO also filter out class refs that are inherited by the class
                
                trs3.valuesIterator.foldLeft(withTraits)(_ & _)
                
              case _ =>
                lazy val nFields = rcd.fields
                  .filterNot(traitPrefixes contains _._1.name.takeWhile(_ =/= '#'))
                  .mapValues(_.update(go(_, pol.map(!_)), go(_, pol)))
                val (res, nfs) = bo match {
                  case S(tt @ TupleType(fs)) =>
                    val arity = fs.size
                    val (componentFields, rcdFields) = rcd.fields
                      .filterNot(traitPrefixes contains _._1.name.takeWhile(_ =/= '#'))
                      .partitionMap(f =>
                        if (f._1.name.length > 1 && f._1.name.startsWith("_")) {
                          val namePostfix = f._1.name.tail
                          if (namePostfix.forall(_.isDigit)) {
                            val index = namePostfix.toInt
                            if (index <= arity && index > 0) L(index -> f._2)
                            else R(f)
                          }
                          else R(f)
                        } else R(f)
                      )
                    val componentFieldsMap = componentFields.toMap
                    val tupleComponents = fs.iterator.zipWithIndex.map { case ((nme, ty), i) =>
                      nme -> (ty && componentFieldsMap.getOrElse(i + 1, TopType.toUpper(noProv))).update(go(_, pol.map(!_)), go(_, pol))
                    }.toList
                    S(TupleType(tupleComponents)(tt.prov)) -> rcdFields.mapValues(_.update(go(_, pol.map(!_)), go(_, pol)))
                  case S(ct: ClassTag) => S(ct) -> nFields
                  case S(ft @ FunctionType(l, r)) =>
                    S(FunctionType(go(l, pol.map(!_)), go(r, pol))(ft.prov)) -> nFields
                  case S(at @ ArrayType(inner)) =>
                    S(ArrayType(inner.update(go(_, pol.map(!_)), go(_, pol)))(at.prov)) -> nFields
                  case S(sp @ SpliceType(elems)) =>
                    S(sp.updateElems(go(_, pol), go(_, pol.map(!_)), go(_, pol))) -> nFields
                  case S(wt @ Without(b: ComposedType, ns @ empty())) =>
                    S(Without(b.map(go(_, pol)), ns)(wt.prov)) -> nFields // FIXME very hacky
                  case S(wt @ Without(b, ns)) => S(Without(go(b, pol), ns)(wt.prov)) -> nFields
                  case N => N -> nFields
                }
                LhsRefined(res, tts, rcd.copy(nfs)(rcd.prov).sorted, trs2).toType(sort = true)
            }
          case LhsTop => TopType
        }, {
          case RhsBot => BotType
          case RhsField(n, t) => RecordType(n -> t.update(go(_, pol.map(!_)), go(_, pol)) :: Nil)(noProv)
          case RhsBases(ots, rest, trs) =>
            // Note: could recosntruct class tags for these, but it would be pretty verbose,
            //    as in showing `T & ~C[?] & ~D[?, ?]` instead of just `T & ~c & ~d`
            // ots.map { case t @ (_: ClassTag | _: TraitTag) => ... }
            val r = rest match {
              case v @ S(R(RhsField(n, t))) => RhsField(n, t.update(go(_, pol.map(!_)), go(_, pol))).toType(sort = true)
              case v @ S(L(bty)) => go(bty, pol)
              case N => BotType
            }
            trs.valuesIterator.map(go(_, pol)).foldLeft(BotType: ST)(_ | _) |
            ots.sorted.foldLeft(r)(_ | _)
        }, sort = true)
      }.foldLeft(BotType: ST)(_ | _) |> factorize(ctx)
      otherCs2 | csNegs2
    }
        
    def go(ty: ST, pol: Opt[Bool]): ST = trace(s"norm[${printPol(pol)}] $ty") {
      pol match {
        case S(p) => helper(DNF.mk(ty, p)(ctx, ptr = true, etf = false), pol)
        case N =>
          val dnf1 = DNF.mk(ty, false)(ctx, ptr = true, etf = false)
          val dnf2 = DNF.mk(ty, true)(ctx, ptr = true, etf = false)
          TypeBounds.mk(helper(dnf1, S(false)), helper(dnf2, S(true)))
      }
    }(r => s"~> $r")
    
    def processVar(tv: TV): Unit = {
      processed.setAndIfUnset(tv) {
        tv.lowerBounds = tv.lowerBounds.map(go(_, S(true)))
        tv.upperBounds = tv.upperBounds.map(go(_, S(false)))
      }
    }
    
    go(st, pol)
    
  }
  
  
  
  /** Remove polar type variables, unify indistinguishable ones, and inline the bounds of non-recursive ones. */
  def simplifyType(st: SimpleType, pol: Opt[Bool] = S(true), removePolarVars: Bool = true, inlineBounds: Bool = true)(implicit ctx: Ctx): SimpleType = {
    
    
    
    // * * Analysis 1: count number of TV occurrences at each polarity
    // *  and find whether they're used in invariant positions
    // *  (in which case we won't inline their bounds, to avoid producing ugly type intervals in the final result).
    
    val occNums: MutMap[(Bool, TypeVariable), Int] = LinkedHashMap.empty[(Bool, TypeVariable), Int].withDefaultValue(0)
    val occursInvariantly = MutSet.empty[TV]
    
    val analyzed1 = MutSet.empty[PolarVariable]
    
    // * Note: it is important here to make sure the interpretation of invariant position
    // *    coincides with that of the later `transform` function.
    // *  In particular, the traversal of fields with identical UB/LB is considered invariant.
    object Analyze1 extends Traverser.InvariantFields {
      override def apply(pol: Opt[Bool])(st: ST): Unit = trace(s"analyze1[${printPol(pol)}] $st") {
        st match {
          case tv: TV =>
            if (pol.isEmpty) occursInvariantly += tv
            pol.fold {
              occNums(true -> tv) += 1
              occNums(false -> tv) += 1
            }{ pol => occNums(pol -> tv) += 1 }
            if (pol =/= S(false))
              analyzed1.setAndIfUnset(tv -> true) { tv.lowerBounds.foreach(apply(S(true))) }
            if (pol =/= S(true))
              analyzed1.setAndIfUnset(tv -> false) { tv.upperBounds.foreach(apply(S(false))) }
          case _ =>
            super.apply(pol)(st)
        }
      }()
    }
    Analyze1(pol)(st)
    
    println(s"[inv] ${occursInvariantly.iterator.mkString(", ")}")
    println(s"[nums] ${occNums.iterator
      .map(occ => s"${printPol(S(occ._1._1))}${occ._1._2} ${occ._2}")
      .mkString(" ; ")
    }")
    
    
    
    // * * Analysis 2: find the polar co-occurrences of each TV
    
    val coOccurrences: MutMap[(Bool, TypeVariable), MutSet[SimpleType]] = LinkedHashMap.empty
    
    val analyzed2 = MutSet.empty[ST -> Bool]
    
    def analyze2(st: SimpleType, pol: Bool): Unit =
      analyzeImpl(st.unwrapProvs, pol)
    
    def analyzeImpl(st: SimpleType, pol: Bool): Unit =
        trace(s"analyze2[${printPol(S(pol))}] $st") {
        // trace(s"analyze2[${printPol(S(pol))}] $st       ${analyzed2}") {
          analyzed2.setAndIfUnset(st -> pol) {
            st match {
      case RecordType(fs) => fs.foreach { f => f._2.lb.foreach(analyze2(_, !pol)); analyze2(f._2.ub, pol) }
      case TupleType(fs) => fs.foreach { f => f._2.lb.foreach(analyze2(_, !pol)); analyze2(f._2.ub, pol) }
      case ArrayType(inner) =>
        inner.lb.foreach(analyze2(_, !pol))
        analyze2(inner.ub, pol)
      case SpliceType(elems) => elems.foreach {
        case L(l) => analyze2(l, pol)
        case R(r) => 
          r.lb.foreach(analyze2(_, !pol))
          analyze2(r.ub, pol)
      }
      case FunctionType(l, r) => analyze2(l, !pol); analyze2(r, pol)
      case tv: TypeVariable => process(tv, pol)
      case _: ObjectTag | ExtrType(_) => ()
      case ct: ComposedType => process(ct, pol)
      case NegType(und) => analyze2(und, !pol)
      case ProxyType(underlying) => analyze2(underlying, pol)
      case tr @ TypeRef(defn, targs) =>
        val _ = tr.mapTargs(S(pol)) { (pol, ta) =>
          if (pol =/= S(false)) analyze2(ta, true)
          if (pol =/= S(true)) analyze2(ta, false)
        }
      case Without(base, names) => analyze2(base, pol)
      case TypeBounds(lb, ub) =>
        if (pol) analyze2(ub, true) else analyze2(lb, false)
    }
    }
    }()
    
    def process(st: SimpleType, pol: Bool) = {
      val newOccs = MutSet.empty[SimpleType]
      def go(st: SimpleType): Unit = goImpl(st.unwrapProvs)
      def goImpl(st: SimpleType): Unit =
          trace(s"go $st   (${newOccs.mkString(", ")})") {
            st match {
        case ComposedType(p, l, r) =>
          // println(s">> $pol $l $r")
          if (p === pol) { go(l); go(r) }
          else { analyze2(l, pol); analyze2(r, pol) } // TODO compute intersection if p =/= pol
        case _: BaseType | _: TypeRef => newOccs += st; analyze2(st, pol)
        case tv: TypeVariable =>
          // println(s"$tv ${newOccs.contains(tv)}")
          if (!newOccs.contains(tv)) {
            newOccs += st
            (if (pol) tv.lowerBounds else tv.upperBounds).foreach(go)
          }
        case _ => analyze2(st, pol)
      }
      }()
      go(st)
      var firstTime = false
      newOccs.foreach {
        case tv: TypeVariable =>
          // println(s">>>> $tv $newOccs ${coOccurrences.get(pol -> tv)}")
          coOccurrences.get(pol -> tv) match {
            case Some(os) => os.filterInPlace(newOccs) // computes the intersection
            case None => coOccurrences(pol -> tv) = newOccs.clone()
          }
          // println(s">> $pol ${coOccurrences.get(pol -> tv)}")
        case _ => ()
      }
    }
    
    if (pol =/= S(false)) analyze2(st, true)
    if (pol =/= S(true)) analyze2(st, false)
    
    println(s"[occs] ${coOccurrences.iterator
      .map(occ => s"${printPol(S(occ._1._1))}${occ._1._2} ${occ._2.mkString("{",",","}")}")
      .mkString(" ; ")
    }")
    
    
    
    // * * Processing: decide what type variables to remove/unify/inline bounds of.
    // * NOTE: This phase logically unifies type variables by merging their bounds and co-occurrence reults.
    // *  In particular, it may change the recursive-ness of type variables!
    // *  (We may unfy a non-rec TV with a rec one, makingthe non-rec TV recursive.)
    
    // * This will be filled during the processing phase, to guide the transformation phase:
    val varSubst = MutMap.empty[TypeVariable, Option[TypeVariable]]
    
    // val allVars = st.getVars
    val allVars = analyzed1.iterator.map(_._1).toSortedSet
    
    var recVars = MutSet.from(allVars.iterator.filter(_.isRecursive_$))
    
    println(s"[vars] ${allVars}")
    println(s"[rec] ${recVars}")
    // println(s"[bounds] ${st.showBounds}")
    
    // * Remove polar type variables that only occur once, including if they are part of a recursive bounds graph:
    if (inlineBounds) occNums.iterator.foreach { case (k @ (pol, tv), num) =>
      assert(num > 0)
      if (num === 1 && !occNums.contains(!pol -> tv)) {
        println(s"0[1] $tv")
        varSubst += tv -> None
      }
    }
    
    // * Simplify away those non-recursive variables that only occur in positive or negative positions
    // *  (i.e., polar ones):
    allVars.foreach { case v0 => if (!recVars.contains(v0)) {
      (coOccurrences.get(true -> v0), coOccurrences.get(false -> v0)) match {
        case (Some(_), None) | (None, Some(_)) =>
          if (removePolarVars) {
            println(s"1[!] $v0")
            varSubst += v0 -> None
          }; ()
        case occ => assert(occ =/= (None, None), s"$v0 has no occurrences...")
      }
    }}
    
    // * Remove variables that are 'dominated' by another type or variable
    // *  A variable v dominated by T if T is in both of v's positive and negative cooccurrences
    allVars.foreach { case v => if (!varSubst.contains(v)) {
      println(s"2[v] $v ${coOccurrences.get(true -> v)} ${coOccurrences.get(false -> v)}")
      
      coOccurrences.get(true -> v).iterator.flatMap(_.iterator).foreach {
        
        case atom @ (_: BaseType | _: TypeRef)
          if !recVars(v) // can't reduce recursive sandwiches, obviously
          && coOccurrences.get(false -> v).exists(_(atom))
        =>
          println(s"  [..] $v ${atom}")
          varSubst += v -> None; ()
        
        case w: TV if !(w is v) && !varSubst.contains(w) && !varSubst.contains(v) && !recVars(v)
          && coOccurrences.get(false -> v).exists(_(w))
        =>
          // * Here we know that v is 'dominated' by w, so v can be inlined.
          // * Note that we don't want to unify the two variables here
          // *  – if v has bounds and does not dominate w, then doing so would be wrong.
          
          // * Logic to preserve name hints, but seems overkill and did not seem to have any effect so far:
          // if (coOccurrences.get(true -> w).exists(_(v)) && coOccurrences.get(false -> w).exists(_(v)) && v.nameHint.nonEmpty && !recVars(w)) {
          //   println(s"  [..] $w ${v}")
          //   varSubst += w -> N
          // } else {
          
          println(s"  [..] $v ${w}")
          varSubst += v -> N
          
          // }
          
        case _ =>
      }
    }}
    
    // * Unify equivalent variables based on polar co-occurrence analysis:
    allVars.foreach { case v =>
      if (!varSubst.contains(v))
        trace(s"3[v] $v +${coOccurrences.get(true -> v).mkString} -${coOccurrences.get(false -> v).mkString}") {
        
        def go(pol: Bool): Unit = coOccurrences.get(pol -> v).iterator.flatMap(_.iterator).foreach {
          
          case w: TypeVariable if !(w is v) && !varSubst.contains(w) //&& (if (pol) )
              // && (recVars.contains(v) === recVars.contains(w))
              // * ^ Note: We no longer avoid merging rec and non-rec vars,
              // *    even though the non-rec one may not be strictly polar (as an example of this, see [test:T1]).
              // *    We may introduce recursive types anyway so the `recVars` info here is no longer up to date.
              && (v.nameHint.nonEmpty || w.nameHint.isEmpty
              // * ^ Don't merge in this direction if that would override a nameHint
                || varSubst.contains(v) // * we won't be able to do it the other way
                // || varSubst.contains(v)
              )
            =>
            trace(s"[w] $w ${printPol(S(pol))}${coOccurrences.get(pol -> w).mkString}") {
              
              // * The bounds opposite to the polarity where the two variables co-occur
              val otherBounds = (if (pol) v.upperBounds else v.lowerBounds)
              val otherBounds2 = (if (pol) w.upperBounds else w.lowerBounds)
              
              if (otherBounds =/= otherBounds2)
                // * ^ This is a bit of an ugly heuristic to simplify a couple of niche situations...
                // *    More principled/regular approaches could be to either:
                // *      1. just not merge things with other bounds; or
                // *      2. merge non-recursive things with other bounds but be more careful in the `transform` part
                // *        that we don't import these other bounds when inlining bounds...
                // *    Choice (2.) seems tricky to implement.
                println(s"$v and $w have non-equal other bounds and won't be merged")
              
              else if (coOccurrences.get(pol -> w).forall(_(v))) {
                
                // * Unify w into v
                
                println(s"  [U] $w := $v")
                
                varSubst += w -> S(v)
                
                // * Since w gets unified with v, we need to merge their bounds,
                // * and also merge the other co-occurrences of v and w from the other polarity (!pol).
                // * For instance,
                // *  consider that if we merge v and w in `(v & w) -> v & x -> w -> x`
                // *  we get `v -> v & x -> v -> x`
                // *  and the old positive co-occ of v, {v,x} should be changed to just {v,x} & {w,v} == {v}!
                v.lowerBounds :::= w.lowerBounds
                v.upperBounds :::= w.upperBounds
                
                // TODO when we have `assignedTo` use that instead here?
                w.lowerBounds = v :: Nil
                w.upperBounds = v :: Nil
                
                // * When removePolarVars is enabled, wCoOcss/vCoOcss may not be defined:
                coOccurrences.get((!pol) -> w).foreach { wCoOccs =>
                  coOccurrences.get((!pol) -> v) match {
                    case S(vCoOccs) => vCoOccs.filterInPlace(t => t === v || wCoOccs(t))
                    case N => coOccurrences((!pol) -> v) = wCoOccs
                  }
                }
                
              }
              
            }()
            
          case _ =>
          
        }
        
        go(true)
        go(false)
        
      }()
    }
    
    println(s"[sub] ${varSubst.map(k => k._1.toString + " -> " + k._2).mkString(", ")}")
    println(s"[bounds] ${st.showBounds}")
    
    
    
    // * * Transformation: transform the type recursively,
    // * applying the var substitution and simplifying some things on the fly.
    
    // * The recursive vars may have changed due to the previous phase!
    recVars = MutSet.from(allVars.iterator.filter(v => !varSubst.contains(v) && v.isRecursive_$))
    println(s"[rec] ${recVars}")
    
    val renewals = MutMap.empty[TypeVariable, TypeVariable]
    
    def mergeTransform(pol: Bool, tv: TV, parent: Opt[TV]): ST =
      transform(merge(pol, if (pol) tv.lowerBounds else tv.upperBounds), S(pol), parent)
    
    def transform(st: SimpleType, pol: Opt[Bool], parent: Opt[TV]): SimpleType =
          trace(s"transform[${printPol(pol)}] $st") {
        def transformField(f: FieldType): FieldType = f match {
          case FieldType(S(lb), ub) if lb === ub =>
            val b = transform(ub, N, N)
            FieldType(S(b), b)(f.prov)
          case _ => f.update(transform(_, pol.map(!_), N), transform(_, pol, N))
        }
        st match {
      case RecordType(fs) => RecordType(fs.mapValues(_ |> transformField))(st.prov)
      case TupleType(fs) => TupleType(fs.mapValues(_ |> transformField))(st.prov)
      case ArrayType(inner) => ArrayType(inner |> transformField)(st.prov)
      case sp @ SpliceType(elems) => SpliceType(elems map {
        case L(l) => L(transform(l, pol, N)) 
        case R(r) => R(transformField(r))})(st.prov)
      case FunctionType(l, r) => FunctionType(transform(l, pol.map(!_), N), transform(r, pol, N))(st.prov)
      case _: ObjectTag | ExtrType(_) => st
      case tv: TypeVariable if parent.exists(_ === tv) =>
        if (pol.getOrElse(lastWords(s"parent in invariant position $tv $parent"))) BotType else TopType
      case tv: TypeVariable =>
        varSubst.get(tv) match {
          case S(S(tv)) =>
            println(s"-> $tv")
            transform(tv, pol, parent)
          case S(N) =>
            println(s"-> bound")
            pol.fold(
              TypeBounds.mk(mergeTransform(true, tv, parent), mergeTransform(false, tv, parent))
            )(mergeTransform(_, tv, parent))
          case N =>
            var wasDefined = true
            val res = renewals.getOrElseUpdate(tv, {
              wasDefined = false
              val nv = freshVar(noProv, tv.nameHint)(tv.level)
              println(s"Renewed $tv ~> $nv")
              nv
            })
            pol match {
              case S(pol) if inlineBounds && !occursInvariantly(tv) && !recVars.contains(tv) =>
                // * Inline the bounds of non-rec non-invar-occ type variables
                println(s"Inlining bounds of $tv (~> $res)")
                if (pol) mergeTransform(true, tv, S(tv)) | res
                else mergeTransform(false, tv, S(tv)) & res
              case _ if (!wasDefined) =>
                def setBounds = {
                  trace(s"Setting bounds of $res...") {
                    res.lowerBounds = tv.lowerBounds.map(transform(_, S(true), S(tv)))
                    res.upperBounds = tv.upperBounds.map(transform(_, S(false), S(tv)))
                    res
                  }()
                }
                pol match {
                  case polo @ S(pol)
                    if coOccurrences.get(!pol -> tv).isEmpty // * If tv is polar...
                  =>
                    val bounds = if (pol) tv.lowerBounds else tv.upperBounds
                    
                    // * only true if we do a pass of `removeIrrelevantBounds` before calling `simplifyType`:
                    // assert(tv.lowerBounds.isEmpty || tv.upperBounds.isEmpty, (tv, tv.lowerBounds, tv.upperBounds))
                    
                    // println(s">?> $tv $res $bounds ${tv.lowerBounds} ${tv.upperBounds}")
                    
                    if (bounds.forall { // * If tv only has type variables as upper bounds, inline it
                      case tv2: TV => varSubst.get(tv2).forall(_.isDefined)
                      case _ => false
                    }) {
                      println(s"NEW SUBS $tv -> N")
                      varSubst += tv -> N
                      transform(merge(pol, bounds), polo, parent)
                    }
                    else setBounds
                  case _ => setBounds
                }
              case _ => res
            }
        }
      case ty @ ComposedType(true, l, r) => transform(l, pol, parent) | transform(r, pol, parent)
      case ty @ ComposedType(false, l, r) => transform(l, pol, parent) & transform(r, pol, parent)
      case NegType(und) => transform(und, pol.map(!_), N).neg()
      case WithType(base, RecordType(fs)) => WithType(transform(base, pol, N), 
        RecordType(fs.mapValues(_.update(transform(_, pol.map(!_), N), transform(_, pol, N))))(noProv))(noProv)
      case ProxyType(underlying) => transform(underlying, pol, parent)
      case tr @ TypeRef(defn, targs) =>
        TypeRef(defn, tr.mapTargs(pol)((pol, ty) => transform(ty, pol, N)))(tr.prov)
      case wo @ Without(base, names) =>
        if (names.isEmpty) transform(base, pol, N)
        else if (pol === S(true)) transform(base, pol, N).withoutPos(names)
        else transform(base, pol, N).without(names)
      case tb @ TypeBounds(lb, ub) =>
        pol.fold[ST](TypeBounds.mk(transform(lb, S(false), parent), transform(ub, S(true), parent), noProv))(pol =>
          if (pol) transform(ub, S(true), parent) else transform(lb, S(false), parent))
    }
    }(r => s"~> $r")
    
    transform(st, pol, N)
    
    
  }
  
  
  
  /** Remove recursive types that have 'skidded' across several type variables
    *   due to the (crucially important) type variable bounds propagation logic of the constraint solver.
    * For example, when `?a :> ?b` and we constrain `?a <! {x: ?a}`, we will end up registering `?b <! {x: ?a}`.
    * So if no other upper bounds end up in ?a AND ?a is polar
    *   (so that ?a occurrences are indistinguishable from `{x: ?a}`),
    *   we'll eventually want to refactor ?b's recursive upper bound structure into just `?b <! ?a`. */
  def unskidTypes_!(st: SimpleType, pol: Bool = true)(implicit ctx: Ctx): SimpleType = {
    
    val allVarPols = st.getVarsPol(S(pol))
    println(s"allVarPols: ${allVarPols.iterator.map(e => s"${printPol(e._2)}${e._1}").mkString(", ")}")
    
    val processed = MutSet.empty[TV]
    
    // TODO improve: map values should actually be lists as several TVs may have an identical bound
    val consed = allVarPols.iterator.collect { case (tv, S(pol)) =>
      if (pol) (true, tv.lowerBounds.foldLeft(BotType: ST)(_ | _)) -> tv
      else (false, tv.upperBounds.foldLeft(TopType: ST)(_ & _)) -> tv
    }.toMap
    
    println(s"consed: $consed")
    
    def process(pol: Opt[Bool], st: ST, parent: Opt[TV]): ST =
        // trace(s"cons[${printPol(pol)}] $st") {
          st.unwrapProvs match {
      case tv: TV =>
        processed.setAndIfUnset(tv) {
          tv.lowerBounds = tv.lowerBounds.map(process(S(true), _, S(tv)))
          tv.upperBounds = tv.upperBounds.map(process(S(false), _, S(tv)))
        }
        tv
      case _ =>
        lazy val mapped = st.mapPol(pol, smart = true)(process(_, _, parent))
        pol match {
          case S(p) =>
            // println(s"!1! ${st} ${consed.get(p -> st)}")
            consed.get(p -> st) match {
              case S(tv) if parent.forall(_ isnt tv) =>
                println(s"!unskid-1! ${st} -> $tv")
                process(pol, tv, parent)
              case _ =>
                // println(s"!2! ${mapped} ${consed.get(p -> mapped)}")
                consed.get(p -> mapped) match {
                  case S(tv) if parent.forall(_ isnt tv) =>
                    println(s"!unskid-2! ${mapped} -> $tv")
                    process(pol, tv, parent)
                  case _ => mapped
                }
            }
          case N => mapped
        }
    }
    // }(r => s"~> $r")
    
    process(S(pol), st, N)
  }
  
  
  
  /** Unify polar recursive type variables that have the same structure.
    * For example, `?a <: {x: ?a}` and `?b <: {x: ?b}` will be unified if they are bith polar. */
  def factorRecursiveTypes_!(st: SimpleType, approximateRecTypes: Bool, pol: Opt[Bool] = S(true))(implicit ctx: Ctx): SimpleType = {
    
    val allVarPols = st.getVarsPol(pol)
    println(s"allVarPols: ${allVarPols.iterator.map(e => s"${printPol(e._2)}${e._1}").mkString(", ")}")
    
    val processed = MutSet.empty[TV]
    
    val varSubst = MutMap.empty[TV, TV]
    
    allVarPols.foreach {
      case (tv1, S(p1)) =>
        println(s"Consider $tv1")
        (if (p1) tv1.lowerBounds else tv1.upperBounds) match {
          case b1 :: Nil => 
            allVarPols.foreach {
              case (tv2, S(p2)) if p2 === p1 && (tv2 isnt tv1) && !varSubst.contains(tv1) && !varSubst.contains(tv2) =>
                (if (p2) tv2.lowerBounds else tv2.upperBounds) match {
                  case b2 :: Nil =>
                    
                    // TODO could be smarter, using sets of assumed equalities instead of just one:
                    def unify(ty1: ST, ty2: ST): Bool = {
                      
                      def nope: false = { println(s"Nope(${ty1.getClass.getSimpleName}): $ty1 ~ $ty2"); false }
                      
                      def unifyF(f1: FieldType, f2: FieldType): Bool = (f1, f2) match {
                        case (FieldType(S(l1), u1), FieldType(S(l2), u2)) => unify(l1, l2) && unify(u1, u2)
                        case (FieldType(N, u1), FieldType(N, u2)) => unify(u1, u2)
                        case _ => nope
                      }
                      
                      (ty1, ty2) match {
                        case (`tv1`, `tv2`) | (`tv2`, `tv1`) => true
                        case (v1: TypeVariable, v2: TypeVariable) => (v1 is v2) || nope
                        case (NegType(negated1), NegType(negated2)) => unify(negated1, negated2)
                        case (ClassTag(id1, parents1), ClassTag(id2, parents2)) => id1 === id2 || nope
                        case (ArrayType(inner1), ArrayType(inner2)) => unifyF(inner1, inner2)
                        case (TupleType(fields1), TupleType(fields2)) =>
                          (fields1.size === fields2.size || nope) && fields1.map(_._2).lazyZip(fields2.map(_._2)).forall(unifyF)
                        case (FunctionType(lhs1, rhs1), FunctionType(lhs2, rhs2)) => unify(lhs1, lhs2) && unify(rhs1, rhs2)
                        case (Without(base1, names1), Without(base2, names2)) => unify(base1, base2) && (names1 === names2 || nope)
                        case (TraitTag(id1), TraitTag(id2)) => id1 === id2 || nope
                        case (ExtrType(pol1), ExtrType(pol2)) => pol1 === pol2 || nope
                        case (TypeBounds(lb1, ub1), TypeBounds(lb2, ub2)) =>
                          unify(lb1, lb2) && unify(ub1, ub2)
                        case (ComposedType(pol1, lhs1, rhs1), ComposedType(pol2, lhs2, rhs2)) =>
                          (pol1 === pol2 || nope) && unify(lhs1, lhs2) && unify(rhs1, rhs2)
                        case (RecordType(fields1), RecordType(fields2)) =>
                          fields1.size === fields2.size && fields1.lazyZip(fields2).forall((f1, f2) =>
                            (f1._1 === f2._1 || nope) && unifyF(f1._2, f2._2))
                        case (WithType(base1, rcd1), WithType(base2, rcd2)) =>
                          unify(base1, base2) && unify(rcd1, rcd2)
                        case (ProxyType(underlying1), _) => unify(underlying1, ty2)
                        case (_, ProxyType(underlying2)) => unify(ty1, underlying2)
                        case (TypeRef(defn1, targs1), TypeRef(defn2, targs2)) =>
                          (defn1 === defn2 || nope) && targs1.lazyZip(targs2).forall(unify)
                        case _ => nope
                      }
                    }
                    
                    println(s"Consider $tv1 ~ $tv2")
                    if (unify(b1, b2)) {
                      println(s"Yes! $tv2 := $tv1")
                      varSubst += tv2 -> tv1
                    }
                    
                  case _ =>
                }
              case _ =>
            }
          case _ =>
        }
      case _ =>
    }
    
    println(s"[subs] ${varSubst}")
    
    if (varSubst.nonEmpty) subst(st, varSubst.toMap, substInMap = true) else st
    
  }
  
  
  
  abstract class SimplifyPipeline {
    def debugOutput(msg: => Str): Unit
    
    def apply(st: ST)(implicit ctx: Ctx): ST = {
      var cur = st
      
      cur = removeIrrelevantBounds(cur, inPlace = false)
      debugOutput(s"⬤ Cleaned up: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      cur = unskidTypes_!(cur)
      debugOutput(s"⬤ Unskid: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      cur = simplifyType(cur)
      debugOutput(s"⬤ Type after simplification: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      // * Has a very small (not worth it?) positive effect here:
      // cur = factorRecursiveTypes_!(cur, approximateRecTypes = false)
      // debugOutput(s"⬤ Factored: ${cur}")
      // debugOutput(s" where: ${cur.showBounds}")
      
      cur = normalizeTypes_!(cur)
      debugOutput(s"⬤ Normalized: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      cur = removeIrrelevantBounds(cur, inPlace = true)
      debugOutput(s"⬤ Cleaned up: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      cur = unskidTypes_!(cur)
      debugOutput(s"⬤ Unskid: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      // * The DNFs introduced by `normalizeTypes_!` may lead more coocc info to arise
      // *  by merging things like function types together...
      // * So we need another pass of simplification!
      cur = simplifyType(cur)
      // cur = simplifyType(simplifyType(cur)(ct)
      debugOutput(s"⬤ Resim: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      cur = factorRecursiveTypes_!(cur, approximateRecTypes = false)
      debugOutput(s"⬤ Factored: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      cur
    }
  }
  
}
