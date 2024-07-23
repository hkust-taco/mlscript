package mlscript

import scala.collection.mutable.{Map => MutMap, Set => MutSet, LinkedHashMap, LinkedHashSet}
import scala.collection.immutable.{SortedMap, SortedSet}
import scala.util.chaining._
import mlscript.utils._, shorthands._


trait TypeSimplifier { self: Typer =>
  
  
  def printPols(pols: Map[TypeVariable, Opt[Bool]]): Str =
    pols.iterator.map(e => s"${printPol(e._2)}${e._1}").mkString(", ")
  
  
  /** Remove bounds that are not reachable by traversing the type following variances.
    * Note that doing this on annotated type signatures would need to use polarity None
    *   because a type signature can both be used (positively) and checked against (negatively). */
  def removeIrrelevantBounds(ty: TypeLike, pol: Opt[Bool], reverseBoundsOrder: Bool, inPlace: Bool = false)
        (implicit ctx: Ctx): TypeLike =
  {
    val _ctx = ctx
    
    val allVarPols = ty.getVarsPol(PolMap(pol))
    println(s"allVarPols: ${printPols(allVarPols)}")
    
    val renewed = MutMap.empty[TypeVariable, TypeVariable]
    
    def renew(tv: TypeVariable): TypeVariable =
      renewed.getOrElseUpdate(tv,
        if (inPlace) tv
        else freshVar(noProv, S(tv), tv.nameHint)(tv.level) tap { fv => println(s"Renewed $tv ~> $fv") })
    
    def processLike(ty: TypeLike): TypeLike = ty match {
      case ty: ST => process(ty, N)
      case OtherTypeLike(tu) =>
        tu.map(process(_, N))
    }
    def process(ty: ST, parent: Opt[Bool -> TV], canDistribForall: Opt[Level] = N): ST =
        // trace(s"process($ty) $canDistribForall") {
        ty match {
      
      case SkolemTag(tv: TypeVariable) => process(tv, parent)
      
      case tv: TypeVariable =>
        parent.filter(_._2 === tv).foreach(p => return ExtrType(p._1)(noProv))
        
        var isNew = false
        val nv = renewed.getOrElseUpdate(tv, { isNew = true; renew(tv) })
        
        if (isNew) tv.assignedTo match {
        case S(ty) =>
          // * If the variable is polar, we turn the `assignedTo` into a simple bound.
          // *  I'm not actually sure if that's useful/a good idea.
          // *  Maybe we should process with the appropriate parent, but still generate an `assignedTo`?
          // * (Tried it, and it makes almost no difference in the end result.)
          allVarPols(tv) match {
            case p if p.isEmpty || nv.assignedTo.nonEmpty =>
              nv.assignedTo = S(process(ty, N))
            case N => die // covered
            case S(true) =>
              nv.lowerBounds =
                (process(ty, S(true -> tv)) :: Nil).filterNot(_.isBot)
            case S(false) =>
              nv.upperBounds =
                (process(ty, S(false -> tv)) :: Nil).filterNot(_.isTop)
          }
        case N =>
          nv.lowerBounds = if (allVarPols(tv).forall(_ === true))
              (if (reverseBoundsOrder) tv.lowerBounds.reverseIterator
                else tv.lowerBounds.iterator
              ).map(process(_, S(true -> tv)))
                .reduceOption(_ | _).filterNot(_.isBot).toList
            else Nil
          nv.upperBounds = if (allVarPols(tv).forall(_ === false))
              (if (reverseBoundsOrder) tv.upperBounds.reverseIterator
                else tv.upperBounds.iterator
              ).map(process(_, S(false -> tv)))
                .reduceOption(_ &- _).filterNot(_.isTop).toList
            else Nil
        }
        
        nv
        
      case ComposedType(true, l, r) =>
        process(l, parent, canDistribForall = canDistribForall) |
          process(r, parent, canDistribForall = canDistribForall)
      case ComposedType(false, l, r) =>
        process(l, parent, canDistribForall = canDistribForall) &
          process(r, parent, canDistribForall = canDistribForall)
      case NegType(ty) => process(ty, parent.map(_.mapFirst(!_))).neg(ty.prov)

      case ProvType(ty) if inPlace =>
        ProvType(process(ty, parent, canDistribForall = canDistribForall))(ty.prov)
      case ProvType(ty) => process(ty, parent, canDistribForall = canDistribForall)
      
      case tr @ TypeRef(defn, targs) if builtinTypes.contains(defn) && tr.canExpand =>
        process(tr.expandOrCrash, parent)
      
      case RecordType(fields) => RecordType.mk(fields.flatMap { case (v @ Var(fnme), fty) =>
        // * We make a pass to transform the LB and UB of variant type parameter fields into their extrema
        val prefix = fnme.takeWhile(_ =/= '#')
        val postfix = fnme.drop(prefix.length + 1)
        lazy val default = fty.update(process(_ , N), process(_ , N))
        if (postfix.isEmpty || prefix.isEmpty) v -> default :: Nil
        else ctx.tyDefs.get(prefix) match {
          case S(td) =>
            td.tvarVariances.fold(v -> default :: Nil)(tvv =>
              tvv(td.tparamsargs.find(_._1.name === postfix).getOrElse(die)._2) match {
                case VarianceInfo(true, true) => Nil
                case VarianceInfo(co, contra) =>
                  if (co) v -> FieldType(S(BotType), process(fty.ub, N))(fty.prov) :: Nil
                  else if (contra) v -> FieldType(fty.lb.map(process(_, N)), TopType)(fty.prov) :: Nil
                  else  v -> default :: Nil
              })
          case N =>
            // v -> default :: Nil
            ctx.tyDefs2.get(prefix) match {
              case S(info) =>
                info.result match {
                  case S(cls: TypedNuCls) =>
                    cls.varianceOf(cls.tparams.find(_._1.name === postfix).getOrElse(die)._2) match {
                      case VarianceInfo(true, true) => Nil
                      case VarianceInfo(co, contra) =>
                        if (co) v -> FieldType(S(BotType), process(fty.ub, N))(fty.prov) :: Nil
                        else if (contra) v -> FieldType(fty.lb.map(process(_, N)), TopType)(fty.prov) :: Nil
                        else  v -> default :: Nil
                    }
                  case S(trt: TypedNuTrt) => // TODO factor w/ above & generalize
                    trt.tparams.iterator.find(_._1.name === postfix).flatMap(_._3).getOrElse(VarianceInfo.in) match {
                      case VarianceInfo(true, true) => Nil
                      case VarianceInfo(co, contra) =>
                        if (co) v -> FieldType(S(BotType), process(fty.ub, N))(fty.prov) :: Nil
                        else if (contra) v -> FieldType(fty.lb.map(process(_, N)), TopType)(fty.prov) :: Nil
                        else  v -> default :: Nil
                    }
                  case S(_) => ??? // TODO:
                  case N =>
                    ??? // TODO use info.explicitVariances
                }
              case N => lastWords(s"'$prefix' not found")
            }
        }
      })(ty.prov)
      
      case PolymorphicType(plvl, bod) =>
        val res = process(bod, parent, canDistribForall = S(plvl))
        canDistribForall match {
          case S(outerLvl) if distributeForalls =>
            implicit val ctx: Ctx = _ctx.copy(lvl = outerLvl + 1)
            PolymorphicType(plvl, res).instantiate
          case _ =>
            PolymorphicType.mk(plvl, res)
        }
      
      case ft @ FunctionType(l, r) =>
        FunctionType(process(l, N), process(r, N, canDistribForall = canDistribForall))(ft.prov)
      
      case _ =>
        
        ty.mapPol(N, smart = true)((_, ty) => process(ty, N))
      
    }
    // }(r => s"= $r")
    
    processLike(ty)
    
  }
  
  
  
  /** Transform the type recursively, putting everything in Disjunctive Normal Forms and reconstructing class types
    * from their structural components.
    * Note that performing this _in place_ is not fully correct,
    *   as this will lead us to assume TV bounds while simplifying the TV bounds themselves!
    *     – see [test:T3] –
    *   However, I think this only manifests in contrived manually-constructed corner cases like 
    *   unguarded recursive types such as `C['a] | 'a as 'a`.
    */
  def normalizeTypes_!(st: TypeLike, pol: Opt[Bool])(implicit ctx: Ctx): TypeLike =
  {
    val _ctx = ctx
    
    lazy val allVarPols = st.getVarsPol(PolMap(pol))
    println(s"allVarPols: ${printPols(allVarPols)}")
    
    val processed = MutSet.empty[TV]
    
    def helper(dnf: DNF, pol: Opt[Bool], canDistribForall: Opt[Level] = N): ST =
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
        else go(csNegs.foldLeft(TopType: ST)(_ & _.toType(sort = true).neg()), pol.map(!_)).neg() // TODO sort?! csNegs and toType
      
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
              tts.iterator.collect{ case TraitTag(Var(tagNme), _) => tagNme.capitalize }.toSet
            
            bo match {
              case S(cls @ ClassTag(Var(tagNme), ps))
                if !primitiveTypes.contains(tagNme)
                && ctx.tyDefs.contains(tagNme.capitalize)
                && !newDefs
              =>
                val clsNme = tagNme.capitalize // TODO rm capitalize
                val clsTyNme = TypeName(clsNme)
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
                          case VarianceInfo(false, false) =>
                            // * FIXME: this usage of type bounds is wrong!
                            // * We're here using it as though it meant a bounded wildcard,
                            // * for the purpose of type pretty-printing...
                            // * But this is inconsistent with other uses of these types as *absolute* type ranges!
                            TypeBounds.mk(lb, ub)
                            // * However, the fix is to make all TR arguments actual bounded wildcards
                            // * which is not easy as it requires extensive refactoring
                            // * 
                            // * Note that the version below doesn't work because the refinement redundancy tests
                            // * below require non-polar types to compare against, so TypeBounds is inadequate.
                            /* 
                            pol match {
                              case N => ???
                                TypeBounds.mk(lb, ub)
                              case S(true) => 
                                TypeBounds.mk(lb, ub)
                              case S(false) => 
                                TypeBounds.mk(ub, lb)
                            }
                            */
                            // * FIXME In fact, the use of such subtyping checks should render
                            // * all uses of TypeBounds produced by the simplifier inadequate!
                            // * We should find a proper solution to this at some point...
                            // * (Probably by only using proper wildcards in the type simplifier.)
                          case VarianceInfo(co, contra) =>
                            if (co) ub else lb
                        }
                    }
                })(noProv)
                println(s"typeRef ${typeRef}")
                
                val clsFields = fieldsOf(typeRef.expandWith(paramTags = true, selfTy = false), paramTags = true)
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
                
              case S(cls @ ClassTag(Var(clsNme), ps))
                if !primitiveTypes.contains(clsNme)
                && ctx.tyDefs2.contains(clsNme)
                && ctx.tyDefs2(clsNme).result.isDefined
              =>
                val clsTyNme = TypeName(clsNme)
                val lti = ctx.tyDefs2(clsNme)
                val cls = lti.result match {
                  case S(r: TypedNuCls) => r
                  case _ => die 
                }
                
                val rcdMap  = rcd.fields.toMap
                
                val rcd2  = rcd.copy(rcd.fields.mapValues(_.update(go(_, pol.map(!_)), go(_, pol))))(rcd.prov)
                println(s"rcd2 ${rcd2}")
                
                // val vs =
                //   // td.getVariancesOrDefault
                //   // Map.empty[TV, VarianceInfo].withDefaultValue(VarianceInfo.in)
                //   cls.variances
                
                // * Reconstruct a TypeRef from its current structural components
                val typeRef = TypeRef(cls.td.nme, cls.tparams.zipWithIndex.map { case ((tp, tv, vi), tpidx) =>
                  val fieldTagNme = tparamField(clsTyNme, tp)
                  val fromTyRef = trs2.get(clsTyNme).map(_.targs(tpidx) |> { ta => FieldType(S(ta), ta)(noProv) })
                  fromTyRef.++(rcd2.fields.iterator.filter(_._1 === fieldTagNme).map(_._2))
                    .foldLeft((BotType: ST, TopType: ST)) {
                      case ((acc_lb, acc_ub), FieldType(lb, ub)) =>
                        (acc_lb | lb.getOrElse(BotType), acc_ub & ub)
                    }.pipe {
                      case (lb, ub) =>
                        cls.varianceOf(tv) match {
                          case VarianceInfo(true, true) => TypeBounds.mk(BotType, TopType)
                          case VarianceInfo(false, false) => TypeBounds.mk(lb, ub)
                          case VarianceInfo(co, contra) =>
                            if (co) ub else lb
                        }
                    }
                })(noProv)
                println(s"typeRef ${typeRef}")
                
                val clsFields = fieldsOf(typeRef.expandWith(paramTags = true, selfTy = false), paramTags = true)
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
                
                val withTraits = tts.toArray.sorted // TODO also filter out tts that are inherited by the class
                  .foldLeft(typeRef & cleanedRcd: ST)(_ & _)
                
                val trs3 = trs2 - cls.nme // TODO also filter out class refs that are inherited by the class
                
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
                      .partitionMap(f => f._1.toIndexOption.filter((0 until arity).contains).map(_ -> f._2).toLeft(f))
                    val componentFieldsMap = componentFields.toMap
                    val tupleComponents = fs.iterator.zipWithIndex.map { case ((nme, ty), i) =>
                      nme -> (ty && componentFieldsMap.getOrElse(i, TopType.toUpper(noProv))).update(go(_, pol.map(!_)), go(_, pol))
                    }.toList
                    S(TupleType(tupleComponents)(tt.prov)) -> rcdFields.mapValues(_.update(go(_, pol.map(!_)), go(_, pol)))
                  case S(ct: ClassTag) => S(ct) -> nFields
                  case S(ft @ FunctionType(l, r)) =>
                    S(FunctionType(
                      go(l, pol.map(!_)),
                      go(r, pol, canDistribForall =
                        canDistribForall.orElse(Option.when(dnf.isPolymorphic)(dnf.polymLevel)))
                    )(ft.prov)) -> nFields
                  case S(ot @ Overload(alts)) =>
                    S(ot.mapAltsPol(pol)((p, t) => go(t, p))) -> nFields
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
      val res = otherCs2 | csNegs2
      val cons = dnf.cons.map { case (lo,hi) => (go(lo,S(true)), go(hi,S(false))) }
      val base = ConstrainedType.mk(cons, res)
      canDistribForall match {
        case S(outerLvl) if distributeForalls =>
          implicit val ctx: Ctx = _ctx.copy(lvl = outerLvl + 1)
          PolymorphicType(dnf.polymLevel, base).instantiate
        case _ => PolymorphicType.mk(dnf.polymLevel, base)
      }
    }
    
    def goLike(ty: TL, pol: Opt[Bool], canDistribForall: Opt[Level] = N): TL = trace(s"normLike[${printPol(pol)}] $ty") { ty match {
      case ty: ST => go(ty, pol)
      case OtherTypeLike(tu) => tu.mapPol(pol, true)((p, t) => go(t, p))
    }}()
    def go(ty: ST, pol: Opt[Bool], canDistribForall: Opt[Level] = N): ST = trace(s"norm[${printPol(pol)}] $ty") {
      pol match {
        case S(p) => helper(DNF.mk(MaxLevel, Nil, ty, p)(ctx, ptr = true, etf = false), pol, canDistribForall)
        case N =>
          val dnf1 = DNF.mk(MaxLevel, Nil, ty, false)(ctx, ptr = true, etf = false)
          val dnf2 = DNF.mk(MaxLevel, Nil, ty, true)(ctx, ptr = true, etf = false)
          TypeBounds.mk(helper(dnf1, S(false), canDistribForall), helper(dnf2, S(true), canDistribForall))
      }
    }(r => s"~> $r")
    
    def processVar(tv: TV): Unit = {
      processed.setAndIfUnset(tv) {
        tv.assignedTo match {
          case S(ty) =>
            tv.assignedTo = S(go(ty, N))
          case N =>
            // tv.lowerBounds = tv.lowerBounds.map(go(_, S(true)))
            // tv.upperBounds = tv.upperBounds.map(go(_, S(false)))
            tv.lowerBounds = tv.lowerBounds.reduceOption(_ | _).fold(nil[ST])(go(_, S(true)) :: Nil)
            tv.upperBounds = tv.upperBounds.reduceOption(_ & _).fold(nil[ST])(go(_, S(false)) :: Nil)
        }
      }
    }
    
    goLike(st, pol)
    
  }
  
  
  
  /** Remove polar type variables, unify indistinguishable ones, and inline the bounds of non-recursive ones. */
  def simplifyType(st: TypeLike, removePolarVars: Bool, pol: Opt[Bool], inlineBounds: Bool = true)(implicit ctx: Ctx): TypeLike = {
    
    
    // * There are two main analyses, which are quite subtle.
    // * TODO: add assertion to check that their results are consistent!
    
    
    // * * Analysis 1: count number of TV occurrences at each polarity
    // *  and find whether they're used in invariant positions
    // *  (in which case we won't inline their bounds, to avoid producing ugly type intervals in the final result).
    
    val occNums: MutMap[(Bool, TypeVariable), Int] = LinkedHashMap.empty[(Bool, TypeVariable), Int].withDefaultValue(0)
    val occursInvariantly = MutSet.empty[TV]
    
    val analyzed1 = MutSet.empty[PolarVariable]
    
    // * Note: it is important here to make sure the interpretation of invariant position
    // *    coincides with that of the later `transform` function.
    // *  In particular, the traversal of fields with identical UB/LB is considered invariant.
    object Analyze1 extends Traverser2.InvariantFields {
      override def apply(pol: PolMap)(st: ST): Unit = trace(s"analyze1[${(pol)}] $st") {
        st match {
          case tv: TV =>
            pol(tv) match {
              case S(pol) =>
                occNums(pol -> tv) += 1
              case N =>
                occursInvariantly += tv
                occNums(true -> tv) += 1
                occNums(false -> tv) += 1
            }
            tv.assignedTo match {
              case S(ty) =>
                // * This is quite subtle!
                // * We should traverse assigned type variables as though they weren't there,
                // * but they may appear in their own assignment,
                // * so we still need to check they haven't been traversed yet.
                // * Moreover, traversing them at different polarities may produce different results
                // * (think of `'A# -> 'A#` where 'A# := 'X`),
                // * so we should remember the traversal polarity in the cache.
                // * Thanks to the invariant that the assignment shouldn't have a higher level than
                // * the type variable itself, I think it is fine to never re-traverse the assignment
                // * at the same polarity *even though the polmap may be different*.
                analyzed1.setAndIfUnset(tv -> pol(tv).getOrElse(false)) { apply(pol)(ty) }
              case N =>
                if (pol(tv) =/= S(false))
                  analyzed1.setAndIfUnset(tv -> true) { tv.lowerBounds.foreach(apply(pol.at(tv.level, true))) }
                if (pol(tv) =/= S(true))
                  analyzed1.setAndIfUnset(tv -> false) { tv.upperBounds.foreach(apply(pol.at(tv.level, false))) }
            }
          case _ =>
            super.apply(pol)(st)
        }
      }()
    }
    Analyze1.applyLike(PolMap(pol))(st)
    
    println(s"[inv] ${occursInvariantly.mkString(", ")}")
    println(s"[nums] ${occNums.iterator
      .map(occ => s"${printPol(S(occ._1._1))}${occ._1._2} ${occ._2}")
      .mkString(" ; ")
    }")
    
    
    
    // * * Analysis 2: find the polar co-occurrences of each TV
    
    // * Note: for negatively-quantified vars, the notion of co-occurrence is reversed (wrt unions/inters)...
    
    val coOccurrences: MutMap[(Bool, TypeVariable), LinkedHashSet[SimpleType]] = MutMap.empty
    
    // * Remember which TVs we analyzed at which polarity
    val analyzed2 = MutSet.empty[Bool -> ST]
    // * The above is not enough. Sometimes we want to analyze a group of bounds and co-occurring types altogether.
    // * However, the TV component of these types may have polarities that change depending on the context!
    // * So we can't just assign a polarity to th ewhole thing...
    // * Instead, we remember the polarities of each of these type subexpressions.
    val analyzed22 = MutSet.empty[Set[Opt[Bool] -> ST]]
    
    
    // **********************
    // * An alternative approach that tries to learn more co-occurrence info by
    // * accumulating the effective bounds on type vriables
    // * (ie including those not specified in the TV itself).
    // * Commented because this still needs work before it can be used (Q: should it be?).
    // **********************
    /*
    val lbs, ubs = MutMap.empty[TV, MutSet[ST]]
    def getLbs(tv: TV) = lbs.getOrElseUpdate(tv, MutSet.empty)
    def getUbs(tv: TV) = ubs.getOrElseUpdate(tv, MutSet.empty)
    
    def getBounds(ty: ST, pol: Bool): Set[ST] = {
      val traversed = MutSet.empty[TV]
      def go(ty: ST): Set[ST] = ty.unwrapProxies match { // TODO(later) guard against bad rec types?
        case tv2: TV =>
          if (traversed.add(tv2)) tv2.assignedTo match {
            case S(ty2) => go(ty2) + tv2
            case N =>
              Set.single(tv2) ++
                (if (pol) tv2.lowerBounds else tv2.upperBounds).iterator.flatMap(go)
          } else Set.empty
        case ComposedType(p, l, r) =>
          if (p === pol) go(l) ++ go(r)
          else Set.single(ty) ++ (go(l) & go(r))
        case _ => Set.single(ty)
      }
      go(ty)
    }
    analyzed1.foreach { case (tv, pol) =>
      val bs = getBounds(tv, pol)
      println(tv,pol,bs)
      (if (pol) getLbs(tv) else getUbs(tv)) ++= bs.iterator.filterNot(_ is tv)
      bs.foreach {
        case tv2: TV if tv2 isnt tv =>
          (if (pol) getUbs(tv2) else getLbs(tv2)) += tv
        case _ =>
      }
    }
    println(s"Bounds:")
    s"${lbs.foreach { case (tv, bs) =>
      println(s" $tv")
      bs.foreach(b => println(s"\t:> $b"))
    }}"
    s"${ubs.foreach { case (tv, bs) =>
      println(s" $tv")
      bs.foreach(b => println(s"\t<: $b"))
    }}"
    */
    
    
    // FIXME Currently we don't traverse TVs witht he correct PolMap, which introduces misatches with other analyses in tricky cases
    def analyze2(st: TL, pol: PolMap): Unit =
      Analyze2.applyLike(pol)(st.unwrapProvs)
    
    object Analyze2 extends Traverser2 {
      override def apply(pol: PolMap)(st: ST): Unit = trace(s"analyze2[${(pol)}] $st") {
          st match {
            case tv: TypeVariable =>
              pol(tv) match {
                case S(pol_tv) =>
                  if (analyzed2.add(pol_tv -> tv))
                    processImpl(st, pol, pol_tv)
                case N =>
                  if (analyzed2.add(true -> tv))
                    // * To compute the positive co-occurrences
                    processImpl(st, pol.at(tv.level, true), true)
                  if (analyzed2.add(false -> tv))
                    // * To compute the negative positive co-occurrences
                    processImpl(st, pol.at(tv.level, false), false)
                  
              }
            case ct: ComposedType =>
                def getComponents(ty: ST): Set[Opt[Bool] -> ST] = ty.unwrapProxies match {
                  case tv: TV => Set.single(pol(tv) -> tv)
                  case ty @ ComposedType(p, l, r) =>
                    if (p === ct.pol) getComponents(l) ++ getComponents(r)
                    else Set.single(N -> ty)
                  case _ => Set.single(N -> ty)
                }
              val comps = getComponents(ct)
              println(s"Components $comps")
              if (analyzed22.add(comps))
                processImpl(st, pol, ct.pol)
              else println(s"Found in $analyzed22")
            case _ =>
              super.apply(pol)(st)
          }
      }()
    }
    
    def processImpl(st: SimpleType, pol: PolMap, occPol: Bool) = {
      val newOccs = LinkedHashSet.empty[SimpleType]
      
      println(s">> Processing $st at [${printPol(S(occPol))}]")
      
      def go(ty: ST): Unit =
          trace(s"go $ty   (${newOccs.mkString(", ")})") {
            ty.unwrapProxies match {
        case tv2: TV =>
          // println(s"${printPol(pol(tv2))}$tv2")
          if (newOccs.add(tv2)) tv2.assignedTo match {
            case S(ty2) => go(ty2)
            case N =>
              pol(tv2) match {
                case S(p) =>
                  (if (p) tv2.lowerBounds else tv2.upperBounds).foreach(go)
                  // (if (p) getLbs(tv2) else getUbs(tv2)).foreach(go)
                case N =>
                  trace(s"Analyzing invar-occ of $tv2") {
                    analyze2(tv2, pol)
                  }()
              }
          }
        case ComposedType(p, l, r) if p === occPol => go(l); go(r)
        case _ => newOccs += ty; ()
      }}()
      go(st)
      
      println(s">> Occurrences $newOccs")
      newOccs.foreach {
        case tv: TypeVariable =>
          def occ(pol: Bool): Unit = {
            val occs = if (pol === occPol) newOccs else MutSet.single[ST](tv)
            println(s">>>> occs[${printPol(pol)}$tv] := $occs  <~ ${coOccurrences.get(pol -> tv)}")
            coOccurrences.get(pol -> tv) match {
              case Some(os) =>
                // Q: filter out vars of different level?
                os.filterInPlace(occs) // computes the intersection
              case None => coOccurrences(pol -> tv) = LinkedHashSet.from(occs) // copy not needed?
            }
          }
          pol(tv) match {
            case S(p) =>
              occ(p)
            case N =>
              occ(true)
              occ(false)
          }
        case _ => ()
      }
      newOccs.foreach {
        case tv: TypeVariable => ()
        case ty => analyze2(ty, pol)
      }
    }
    
    analyze2(st, PolMap(pol))
    
    
    coOccurrences.foreach(kv => assert(kv._2.nonEmpty))
    
    println(s"[occs] ${coOccurrences.iterator
      .map(occ => s"${printPol(S(occ._1._1))}${occ._1._2} ${occ._2.mkString("{",",","}")}")
      .mkString(" ; ")
    }")
    
    
    
    // * * Processing: decide what type variables to remove/unify/inline bounds of.
    // * NOTE: This phase logically unifies type variables by merging their bounds and co-occurrence reults.
    // *  In particular, it may change the recursive-ness of type variables!
    // *  (We may unfy a non-rec TV with a rec one, makingthe non-rec TV recursive.)
    
    // * This will be filled during the processing phase, to guide the transformation phase:
    val varSubst = MutMap.empty[TypeVariable, Option[ST]]
    
    // val allVars = st.getVars
    val allVars = analyzed1.iterator.map(_._1).toSortedSet
    
    def computeRecVars =
      allVars.iterator.filter(v => !varSubst.contains(v) && (
        v.isRecursive_$(omitIrrelevantVars = false)
        // * Note: a more precise version could be the following,
        // * but it doesn't seem to change anything in our test suite, so I left if commented for now:
        // // * Only consider recursive those variables that recursive in their *reachable* bounds:
        // occNums.contains(true -> v) && v.isPosRecursive_$(false) || occNums.contains(false -> v) && v.isNegRecursive_$(false)
      )).toSet
    
    var recVars = computeRecVars
    
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
          println(s"1[!] $v0")
          varSubst += v0 -> None
        case occ => assert(occ =/= (None, None), s"$v0 has no occurrences...")
      }
    }}
    
    // * Remove variables that are 'dominated' by another type or variable
    // *  A variable v dominated by T if T is in both of v's positive and negative cooccurrences
    allVars.foreach { case v => if (v.assignedTo.isEmpty && !varSubst.contains(v)) {
      println(s"2[v] $v ${coOccurrences.get(true -> v)} ${coOccurrences.get(false -> v)}")
      
      coOccurrences.get(true -> v).iterator.flatMap(_.iterator).foreach {
        
        case atom @ (_: BaseType | _: TypeRef)
          if !recVars(v) // can't reduce recursive sandwiches, obviously
          && coOccurrences.get(false -> v).exists(_(atom))
        =>
          val bundle = TypeBounds.mkSafe(
              v.upperBounds.foldLeft(atom)(_ &- _),
              v.lowerBounds.foldLeft(atom)(_ | _),
            )
          println(s"  [..] $v := ${bundle}")
          varSubst += v -> S(bundle)
        
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
          
          val bundle = TypeBounds.mkSafe(
              v.upperBounds.foldLeft(w: ST)(_ &- _),
              v.lowerBounds.foldLeft(w: ST)(_ | _),
            )
          println(s"  [..] $v := ${bundle}")
          varSubst += v -> S(bundle)
          
          // }
          
        case _ =>
      }
    }}
    
    // * Unify equivalent variables based on polar co-occurrence analysis:
    allVars.foreach { case v =>
      if (!v.assignedTo.isDefined && !varSubst.contains(v)) // TODO also handle v.assignedTo.isDefined?
        trace(s"3[v] $v +${coOccurrences.get(true -> v).mkString} -${coOccurrences.get(false -> v).mkString}") {
        
        def go(pol: Bool): Unit = coOccurrences.get(pol -> v).iterator.flatMap(_.iterator).foreach {
          
          case w: TypeVariable if !(w is v) && !w.assignedTo.isDefined && !varSubst.contains(w) //&& (if (pol) )
              // && (recVars.contains(v) === recVars.contains(w))
              // * ^ Note: We no longer avoid merging rec and non-rec vars,
              // *    even though the non-rec one may not be strictly polar (as an example of this, see [test:T1]).
              // *    We may introduce recursive types anyway so the `recVars` info here is no longer up to date.
              && (v.nameHint.nonEmpty || w.nameHint.isEmpty
              // * ^ Don't merge in this direction if that would override a nameHint
                || varSubst.contains(v) // * we won't be able to do it the other way
                // || varSubst.contains(v)
              )
              && (v.level === w.level)
              // ^ Don't merge variables of differing levels
            =>
            trace(s"[w] $w ${printPol(S(pol))}${coOccurrences.get(pol -> w).mkString}") {
              
              // * The bounds opposite to the polarity where the two variables co-occur
              // * We don't want to merge variables when this would introduce
              val otherBounds = (if (pol) v.upperBounds else v.lowerBounds)
              val otherBounds2 = (if (pol) w.upperBounds else w.lowerBounds)
              
              // if (otherBounds =/= otherBounds2)
              if (otherBounds.toSet =/= otherBounds2.toSet)
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
    recVars = computeRecVars
    println(s"[rec] ${recVars}")
    
    val renewals = MutMap.empty[TypeVariable, TypeVariable]
    
    val semp = Set.empty[TV]
    
    def mergeTransform(pol: Bool, polmap: PolMap, tv: TV, parents: Set[TV], canDistribForall: Opt[Level]): ST =
      transform(tv.assignedTo match {
        case S(ty) => ty
        case N => merge(pol, if (pol) tv.lowerBounds else tv.upperBounds)
      }, polmap.at(tv.level, pol), parents, canDistribForall)
    
    def transformLike(ty: TL, pol: PolMap): TL = ty match {
      case ty: ST => transform(ty, pol, semp)
      case OtherTypeLike(tu) => tu.mapPolMap(pol)((p,t) => transform(t, p, semp))
    }
    def transform(st: SimpleType, pol: PolMap, parents: Set[TV], canDistribForall: Opt[Level] = N): SimpleType =
          trace(s"transform[${printPol(pol)}] $st   (${parents.mkString(", ")})  $pol  $canDistribForall") {
        def transformField(f: FieldType): FieldType = f match {
          case FieldType(S(lb), ub) if lb === ub =>
            val b = transform(ub, pol.invar, semp)
            FieldType(S(b), b)(f.prov)
          case _ => f.update(transform(_, pol.contravar, semp), transform(_, pol, semp))
        }
        st match {
      case RecordType(fs) => RecordType(fs.mapValues(_ |> transformField))(st.prov)
      case TupleType(fs) => TupleType(fs.mapValues(_ |> transformField))(st.prov)
      case ArrayType(inner) => ArrayType(inner |> transformField)(st.prov)
      case sp @ SpliceType(elems) => SpliceType(elems map {
        case L(l) => L(transform(l, pol, semp)) 
        case R(r) => R(transformField(r))})(st.prov)
      case FunctionType(l, r) =>
        FunctionType(transform(l, pol.contravar, semp),
          transform(r, pol, semp, canDistribForall))(st.prov)
      case ot @ Overload(as) =>
        ot.mapAltsPol(pol)((p, t) => transform(t, p, parents, canDistribForall))
      case SkolemTag(id) => transform(id, pol, parents)
      case _: ObjectTag | _: Extruded | _: ExtrType => st
      case tv: TypeVariable if parents(tv) =>
        pol(tv) match {
          case S(true) => BotType
          case S(false) => TopType
          case N => transform(tv, pol, parents - tv)
        }
      case tv: TypeVariable =>
        varSubst.get(tv) match {
          case S(S(tv2)) =>
            println(s"-> $tv2")
            transform(tv2, pol, parents + tv, canDistribForall)
          case S(N) =>
            println(s"-> bound ${pol(tv)}")
            val p = pol(tv)
            if (!removePolarVars && (
                   tv.lowerBounds.isEmpty && p.contains(true)
                || tv.upperBounds.isEmpty && p.contains(false)
                || tv.lowerBounds.isEmpty && tv.upperBounds.isEmpty
            )) ClassTag(Var("?"), Set.empty)(noProv)
            else p.fold {
              // TypeBounds.mk(mergeTransform(true, tv, parents + tv), mergeTransform(false, tv, parents + tv)) // FIXME polarities seem inverted
              lastWords("Should not be replacing an invariant type variable by its bound...") // ?
              pol.quantifPolarity(tv.level).base match {
                case S(true) =>
                  TypeBounds.mkSafe(mergeTransform(false, pol, tv, parents + tv, canDistribForall),
                    mergeTransform(true, pol, tv, parents + tv, canDistribForall))
                case S(false) =>
                  TypeBounds.mkSafe(mergeTransform(true, pol, tv, parents + tv, canDistribForall),
                    mergeTransform(false, pol, tv, parents + tv, canDistribForall))
                case N => ???
              }
            }(mergeTransform(_, pol, tv, parents + tv, canDistribForall))
          case N =>
            var wasDefined = true
            val res = renewals.getOrElseUpdate(tv, {
              wasDefined = false
              val nv = freshVar(noProv, S(tv), tv.nameHint)(tv.level)
              println(s"Renewed $tv ~> $nv")
              nv
            })
            pol(tv) match {
              case S(p) if inlineBounds && !occursInvariantly(tv) && !recVars.contains(tv) =>
                // * Inline the bounds of non-rec non-invar-occ type variables
                println(s"Inlining [${printPol(p)}] bounds of $tv (~> $res)")
                // if (p) mergeTransform(true, pol, tv, Set.single(tv), canDistribForall) | res
                // else mergeTransform(false, pol, tv, Set.single(tv), canDistribForall) & res
                if (p) mergeTransform(true, pol, tv, parents + tv, canDistribForall) | res
                else mergeTransform(false, pol, tv, parents + tv, canDistribForall) & res
              case poltv if (!wasDefined) =>
                def setBounds = {
                  trace(s"Setting [±] bounds of $res... (failing ${printPol(poltv)}, inlineBounds $inlineBounds, !occursInvariantly ${!occursInvariantly(tv)}, !recVars.contains(tv) ${!recVars.contains(tv)})") {
                    tv.assignedTo match {
                      case S(ty) =>
                        res.assignedTo = S(transform(ty, pol.invar, semp, canDistribForall))
                      case N =>
                        if (occNums.contains(true -> tv))
                          res.lowerBounds = tv.lowerBounds.map(transform(_, pol.at(tv.level, true), Set.single(tv)))
                        if (occNums.contains(false -> tv))
                          res.upperBounds = tv.upperBounds.map(transform(_, pol.at(tv.level, false), Set.single(tv)))
                    }
                    res
                  }()
                }
                poltv match {
                  case polo @ S(p)
                    if coOccurrences.get(!p -> tv).isEmpty // * If tv is polar...
                    && tv.assignedTo.isEmpty // TODO handle?
                  =>
                    val bounds = if (p) tv.lowerBounds else tv.upperBounds
                    
                    // * only true if we do a pass of `removeIrrelevantBounds` before calling `simplifyType`:
                    // assert(tv.lowerBounds.isEmpty || tv.upperBounds.isEmpty, (tv, tv.lowerBounds, tv.upperBounds))
                    
                    // println(s">?> $tv $res $bounds ${tv.lowerBounds} ${tv.upperBounds}")
                    
                    if (bounds.forall { // * If tv only has type variables as upper bounds, inline it
                      case tv2: TV => varSubst.get(tv2).forall(_.isDefined)
                      case _ => false
                    }) {
                      println(s"NEW SUBS $tv -> N")
                      varSubst += tv -> N
                      transform(merge(p, bounds), pol, parents + tv, canDistribForall)
                    }
                    else setBounds
                  case _ => setBounds
                }
              case _ => res
            }
        }
      case ty @ ComposedType(true, l, r) =>
        transform(l, pol, parents, canDistribForall) | transform(r, pol, parents, canDistribForall)
      case ty @ ComposedType(false, l, r) =>
        transform(l, pol, parents, canDistribForall) & transform(r, pol, parents, canDistribForall)
      case NegType(und) => transform(und, pol.contravar, semp).neg()
      case WithType(base, RecordType(fs)) => WithType(transform(base, pol, semp, canDistribForall), 
        RecordType(fs.mapValues(_.update(transform(_, pol.contravar, semp), transform(_, pol, semp))))(noProv))(noProv)
      case ProxyType(underlying) => transform(underlying, pol, parents, canDistribForall)
      case tr @ TypeRef(defn, targs) =>
        TypeRef(defn, tr.mapTargs(pol)((pol, ty) => transform(ty, pol, semp)))(tr.prov)
      case wo @ Without(base, names) =>
        if (names.isEmpty) transform(base, pol, semp, canDistribForall)
        else if (pol.base === S(true)) transform(base, pol, semp, canDistribForall).withoutPos(names)
        else transform(base, pol, semp, canDistribForall).without(names)
      case tb @ TypeBounds(lb, ub) =>
        pol.base.fold[ST](TypeBounds.mkSafe(
          transform(lb, PolMap.neg, parents, canDistribForall),
          transform(ub, PolMap.pos, parents, canDistribForall),
          // transform(lb, pol, parents, canDistribForall),
          // transform(ub, pol, parents, canDistribForall),
          // transform(lb, pol.contravar, parents, canDistribForall),
          // transform(ub, pol.covar, parents, canDistribForall),
          noProv
        ))(p =>
          if (p) transform(ub, pol, parents) else transform(lb, pol, parents)
        )
      case PolymorphicType(plvl, bod) =>
        val res = transform(bod, pol.enter(plvl), parents, canDistribForall = S(plvl))
        canDistribForall match {
          case S(outerLvl) if distributeForalls =>
            ctx.copy(lvl = outerLvl + 1) |> { implicit ctx =>
              PolymorphicType(plvl, res).instantiate
            }
          case _ =>
            PolymorphicType.mk(plvl, res)
        }
      case ConstrainedType(cs, bod) =>
        ConstrainedType(
          cs.map { case (lo, hi) =>
            (transform(lo, PolMap.pos, semp), transform(hi, PolMap.posAtNeg, semp))
          },
          transform(bod, pol, parents)
        )
    }
    }(r => s"~> $r")
    
    transformLike(st, PolMap(pol))
    
    
  }
  
  
  
  /** Remove recursive types that have 'skidded' across several type variables
    *   due to the (crucially important) type variable bounds propagation logic of the constraint solver.
    * For example, when `?a :> ?b` and we constrain `?a <! {x: ?a}`, we will end up registering `?b <! {x: ?a}`.
    * So if no other upper bounds end up in ?a AND ?a is polar
    *   (so that ?a occurrences are indistinguishable from `{x: ?a}`),
    *   we'll eventually want to refactor ?b's recursive upper bound structure into just `?b <! ?a`. */
  def unskidTypes_!(st: TypeLike, pol: Bool)(implicit ctx: Ctx): TypeLike = {
    
    val allVarPols = st.getVarsPol(PolMap(S(pol)))
    println(s"allVarPols: ${printPols(allVarPols)}")
    
    val processed = MutSet.empty[TV]
    
    // TODO improve: map values should actually be lists as several TVs may have an identical bound
    val consed = allVarPols.iterator.collect {
      case (tv @ AssignedVariable(ty), S(pol)) =>
        if (pol) (true, ty) -> tv
        else (false, ty) -> tv
      case (tv, S(pol)) =>
        if (pol) (true, tv.lowerBounds.foldLeft(BotType: ST)(_ | _)) -> tv
        else (false, tv.upperBounds.foldLeft(TopType: ST)(_ &- _)) -> tv
    }.filter { case ((pol, bnd), tv) => bnd.getVarsImpl(includeBounds = false).contains(tv) }.toMap
    
    println(s"consed: $consed")
    
    // * Q: shouldn't this use a PolMap instead?
    // * It should actually be sound not to, though, as the handling is symmetric...
    def process(pol: Opt[Bool], st: ST, parent: Opt[TV]): ST =
        // trace(s"cons[${printPol(pol)}] $st") {
          st.unwrapProvs match {
      case tv @ AssignedVariable(ty) =>
        processed.setAndIfUnset(tv) {
          // tv.assignedTo = S(process(pol, ty, S(tv))) // * WRONG!
          tv.assignedTo = S(process(N, ty, S(tv)))
        }
        tv
      case tv: TV =>
        processed.setAndIfUnset(tv) {
          tv.lowerBounds = tv.lowerBounds.map(process(S(true), _, S(tv)))
          tv.upperBounds = tv.upperBounds.map(process(S(false), _, S(tv)))
        }
        tv
      case _ =>
        lazy val mapped = st.mapPol(pol, smart = true)(process(_, _, parent))
        // println(s"mapped $mapped")
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
    
    def processLike(pol: Opt[Bool], ty: TL): TL = ty match {
      case ty: ST => process(pol, ty, N)
      case OtherTypeLike(tu) => tu.mapPol(pol, smart = true)(process(_, _, N))
    }
    
    processLike(S(pol), st)
  }
  
  
  
  /** Unify polar recursive type variables that have the same structure.
    * For example, `?a <: {x: ?a}` and `?b <: {x: ?b}` will be unified if they are bith polar. */
  def factorRecursiveTypes_!(st: TypeLike, approximateRecTypes: Bool, pol: Opt[Bool])(implicit ctx: Ctx): TypeLike = {
    
    val allVarPols = st.getVarsPol(PolMap(pol))
    println(s"allVarPols: ${printPols(allVarPols)}")
    
    val processed = MutSet.empty[TV]
    
    val varSubst = MutMap.empty[TV, TV]
    
    allVarPols.foreach {
      case (tv1, S(p1)) =>
        println(s"Consider $tv1")
        (tv1.assignedTo.map(_::Nil).getOrElse(if (p1) tv1.lowerBounds else tv1.upperBounds)) match {
          case b1 :: Nil => 
            allVarPols.foreach {
              case (tv2, S(p2)) if p2 === p1 && (tv2 isnt tv1) && !varSubst.contains(tv1) && !varSubst.contains(tv2) =>
                (tv2.assignedTo.map(_::Nil).getOrElse(if (p2) tv2.lowerBounds else tv2.upperBounds)) match {
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
                        case (TraitTag(id1, _), TraitTag(id2, _)) => id1 === id2 || nope
                        case (SkolemTag(id1), SkolemTag(id2)) => id1 === id2 || nope
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
    
    if (varSubst.nonEmpty) substLike(st, varSubst.toMap, substInMap = true) else st
    
  }
  
  
  
  abstract class SimplifyPipeline {
    def debugOutput(msg: => Str): Unit
    
    def apply(st: TL, pol: Opt[Bool], removePolarVars: Bool = true)(implicit ctx: Ctx): TypeLike = {
      var cur = st
      
      debugOutput(s"⬤ Initial: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      cur = removeIrrelevantBounds(cur, pol,
        reverseBoundsOrder = true, // bounds are accumulated by type inference in reverse order of appearance; so nicer to reverse them here
        inPlace = false)
      debugOutput(s"⬤ Cleaned up: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      pol.foreach(pol => cur = unskidTypes_!(cur, pol))
      debugOutput(s"⬤ Unskid: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      cur = simplifyType(cur, removePolarVars, pol)
      debugOutput(s"⬤ Type after simplification: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      // * Has a very small (not worth it?) positive effect here:
      // cur = factorRecursiveTypes_!(cur, approximateRecTypes = false)
      // debugOutput(s"⬤ Factored: ${cur}")
      // debugOutput(s" where: ${cur.showBounds}")
      
      cur = normalizeTypes_!(cur, pol)
      debugOutput(s"⬤ Normalized: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      cur = removeIrrelevantBounds(cur, pol,
        reverseBoundsOrder = false,
        inPlace = true)
      debugOutput(s"⬤ Cleaned up: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      pol.foreach(pol => cur = unskidTypes_!(cur, pol))
      debugOutput(s"⬤ Unskid: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      // * The DNFs introduced by `normalizeTypes_!` may lead more coocc info to arise
      // *  by merging things like function types together...
      // * So we need another pass of simplification!
      cur = simplifyType(cur, removePolarVars, pol)
      debugOutput(s"⬤ Resim: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      cur = factorRecursiveTypes_!(cur, approximateRecTypes = false, pol)
      debugOutput(s"⬤ Factored: ${cur}")
      debugOutput(s" where: ${cur.showBounds}")
      
      cur
    }
  }
  
}
