package mlscript

import scala.collection.mutable.{Map => MutMap, Set => MutSet, LinkedHashMap, LinkedHashSet}
import scala.collection.immutable.{SortedMap, SortedSet}
import scala.util.chaining._
import mlscript.utils._, shorthands._

trait TypeSimplifier { self: Typer =>
  
  
  
  def removeIrrelevantBounds(ty: SimpleType, pol: Opt[Bool] = S(true), inPlace: Bool = false)(implicit ctx: Ctx): SimpleType = {
    
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
      
      case _ => ty.map(process(_, N))
      
    }
    // }(r => s"= $r")
    
    process(ty, N)
    
  }
  
  
  
  def normalizeTypes_!(st: SimpleType, pol: Opt[Bool] = S(true))(implicit ctx: Ctx): SimpleType = {
    
    // implicit val cache: MutMap[TV, Opt[Bool]] = MutMap.empty
    val allVarPols = st.getVarsPol(pol)
    println(s"allVarPols: ${allVarPols.iterator.map(e => s"${printPol(e._2)}${e._1}").mkString(", ")}")
    val processed = MutSet.empty[TV]
    // val consed = allVarPols.iterator.filter(_._2.isDefined).map { case (tv, pol) =>
    
    val recVars = MutSet.from(
      // TODOne rm/update logic?
      // allVars.iterator.filter(tv => tv.lowerBounds.nonEmpty || tv.upperBounds.nonEmpty))
      allVarPols.keysIterator.filter(tv => tv.isBadlyRecursive(MutMap.empty[TV, Opt[Bool]]).isDefined))
    println(s"recVars: $recVars")
    
    def helper(dnf: DNF, pol: Opt[Bool]): ST = {
        println(s"DNF: $dnf")
        // val dnf @ DNF(cs) = DNF.mk(ty, pol)(ctx, preserveTypeRefs = true)
        val cs = dnf.cs
        val (csNegs, otherCs) = cs.partitionMap {
          case c @ Conjunct(l, vs, r, nvs) if l.isTop && vs.isEmpty && !(r.isBot && nvs.isEmpty) =>
            // L(r, nvs)
            L(c)
          case c => R(c)
        }
        // val csNegs2 = csNegs.sorted.map { c =>
        //  
        // }
        val csNegs2 = if (csNegs.isEmpty) BotType else go(csNegs.foldLeft(TopType: ST)(_ & _.toType().neg()), pol.map(!_)).neg()
        // val csNegs2 = if (csNegs.isEmpty) TopType else helper(DNF.mk(csNegs.foldLeft(TopType: ST)(_ & _.toType()), pol.map(!_))(ctx, ptr = true, etf = false), pol.map(!_))
        // val csNegs2 = DNF.mk(csNegs.foldLeft(TopType: ST)(_ & _.toType().neg()), true)(ctx, ptr = true, etf = false).toType().neg()
        // val csNegs2 = csNegs.foldLeft(TopType: ST)(_ & _.toType().neg()).neg()
        // val csNegs2 = csNegs.foldLeft(TopType: ST)(_ & _.neg.toType()).neg()
        // val otherCs2 = cs.sorted.map { c =>
        val otherCs2 = otherCs.sorted.map { c =>
          // c.vars.foreach(go(pol, _))
          // c.nvars.foreach(go(pol.map(!_), _))
          c.vars.foreach(processVar)
          c.nvars.foreach(processVar)
          // c.copy(vars = c.vars.map(renew), nvars = c.nvars.map(renew)).toTypeWith(_ match {
          c.toTypeWith(_ match {
            
            case LhsRefined(bo, tts, rcd, trs) =>
              // The handling of type parameter fields is currently a little wrong here,
              //  because we remove:
              //    - type parameter fields of parent classes,
              //        whereas they could _in principle_ be refined and
              //        not correspond exactly to these of the currenly-reconstructed class;
              //        and
              //    - type parameter fields of the current trait tags
              //        whereas we don't actually reconstruct applied trait types...
              //        it would be better to just reconstruct them (TODO)
              
              val trs2 = trs.map {
                case (d, tr @ TypeRef(defn, targs)) =>
                  // TODOne actually make polarity optional and recurse with None
                  // d -> TypeRef(defn, targs.map(targ =>
                  //   TypeBounds(go(targ, false), go(targ, true))(noProv)))(tr.prov)
                  d -> TypeRef(defn, targs.map(go(_, N)))(tr.prov) // TODO improve with variance analysis
              }
              
              val traitPrefixes =
                tts.iterator.collect{ case TraitTag(Var(tagNme)) => tagNme.capitalize }.toSet
              bo match {
                case S(cls @ ClassTag(Var(tagNme), ps)) if !primitiveTypes.contains(tagNme) =>
                  val clsNme = tagNme.capitalize
                  val clsTyNme = TypeName(tagNme.capitalize)
                  val td = ctx.tyDefs(clsNme)
                  val typeRef = TypeRef(td.nme, td.tparams.zipWithIndex.map { case (tp, tpidx) =>
                    // val fieldTagNme = tparamField(TypeName(clsNme), tp)
                    val fieldTagNme = tparamField(clsTyNme, tp)
                    // rcd.fields.iterator.filter(_._1 === fieldTagNme).map {
                    //   case (_, FunctionType(lb, ub)) =>
                    //     TypeBounds.mk(go(lb, false), go(ub, true))
                    // }.foldLeft(TypeBounds(BotType, TopType)(noProv): ST)(_ & _)
                    
                    /* 
                    rcd.fields.iterator.filter(_._1 === fieldTagNme).collectFirst {
                      case (_, FieldType(lb, ub)) if lb.exists(ub >:< _) => ub
                      case (_, FieldType(lb, ub)) =>
                        TypeBounds.mk(go(lb.getOrElse(BotType), S(false)), go(ub, S(true)))
                    }.getOrElse(TypeBounds(BotType, TopType)(noProv))
                    */
                    
                    // val fromTyRef = trs2.get(clsTyNme).map(tr => FieldType(tr.targs(tpidx)))
                    val fromTyRef = trs.get(clsTyNme).map(_.targs(tpidx) |> { ta => FieldType(S(ta), ta)(noProv) })
                    
                    (fromTyRef ++ rcd.fields.iterator.filter(_._1 === fieldTagNme).map(_._2)).foldLeft((BotType: ST, TopType: ST)) {
                      // case ((acc_lb, acc_ub), (_, FunctionType(lb, ub))) => (acc_lb | lb, acc_ub & ub)
                      // // case ((acc_lb, acc_ub), (_, _)) => die
                      // case ((acc_lb, acc_ub), (_, ty)) => lastWords(s"$fieldTagNme = $ty")
                      
                      // case ((acc_lb, acc_ub), FieldType(lb, ub)) if lb.exists(ub >:< _) => ub
                      // case ((acc_lb, acc_ub), (_, FieldType(lb, ub))) =>
                      case ((acc_lb, acc_ub), FieldType(lb, ub)) =>
                        // // TypeBounds.mk(go(lb.getOrElse(BotType), false), go(ub, true))
                        // (acc_lb.fold(lb)(_ | lb.getOrElse(BotType)), acc_ub & ub)
                        (acc_lb | lb.getOrElse(BotType), acc_ub & ub)
                    }.pipe {
                      // case (lb, ub) => TypeBounds.mk(go(lb, false), go(ub, true))
                      case (lb, ub) => TypeBounds.mk(go(lb, S(false)), go(ub, S(true)))
                    }
                    // rcd.fields.iterator.filter(_._1 === fieldTagNme).map {
                    //   case (_, ft: FunctionType) => ft
                    //   case _ => die
                    // }.foldLeft(FunctionType(BotType, TopType)(noProv): ST)(_ & _)
                  })(noProv)
                  val clsFields = fieldsOf(
                    typeRef.expandWith(paramTags = false), paramTags = false)
                  val cleanPrefixes = ps.map(v => v.name.capitalize) + clsNme ++ traitPrefixes
                  val cleanedRcd = rcd.copy(
                    rcd.fields.filterNot { case (field, fty) =>
                      // println(s"F1 $field $fty ${clsFields.get(field)} ${clsFields.get(field).map(_ <:< fty)}")
                      cleanPrefixes.contains(field.name.takeWhile(_ != '#')) ||
                        clsFields.get(field).exists(_ <:< fty)
                    }.mapValues(_.update(go(_, pol.map(!_)), go(_, pol)))
                  )(rcd.prov)
                  val removedFields = clsFields.keysIterator
                    .filterNot(field => rcd.fields.exists(_._1 === field)).toSortedSet
                  val needsWith = !rcd.fields.forall {
                    case (field, fty) =>
                      // println(s"F2 $field $fty ${clsFields.get(field)} ${clsFields.get(field).map(_ <:< fty)}")
                      clsFields.get(field).forall(fty <:< _)
                  }
                  val withoutType = if (removedFields.isEmpty) typeRef
                    // else Without(typeRef, removedFields)(noProv)
                    else typeRef.without(removedFields)
                  // println(s"!! ${withoutType}")
                  val withType = if (needsWith) if (cleanedRcd.fields.isEmpty) withoutType
                    else WithType(withoutType, cleanedRcd.sorted)(noProv) else typeRef & cleanedRcd.sorted
                  
                  val withTrs =
                    // TODO merge these with reconstructed ones...
                    trs2.valuesIterator.foldLeft(withType)(_ & _)
                  
                  tts.toArray.sorted // TODO also filter out tts that are inherited by the class
                    .foldLeft(withType: ST)(_ & _)
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
                      // S(FunctionType(go(l, pol.map(!_)), go(r, pol))(ft.prov)) -> nFields
                      S(FunctionType(go(l, pol.map(!_)), go(r, pol))(ft.prov)) -> nFields
                    // case S(at @ ArrayType(inner)) => S(ArrayType(go(inner, pol))(at.prov)) -> nFields
                    case S(at @ ArrayType(inner)) =>
                      S(ArrayType(inner.update(go(_, pol.map(!_)), go(_, pol)))(at.prov)) -> nFields
                    case S(wt @ Without(b: ComposedType, ns @ empty())) => S(Without(b.map(go(_, pol)), ns)(wt.prov)) -> nFields // FIXME very hacky
                    case S(wt @ Without(b, ns)) => S(Without(go(b, pol), ns)(wt.prov)) -> nFields
                    // case S(wt @ Without(b, ns)) => S(go(b, pol).without(ns)) -> nFields
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
        // (otherCs2 ++ csNegs2).foldLeft(BotType: ST)(_ | _) |> factorize(ctx)
        otherCs2 | csNegs2
        }
        
        // /* 
        // mkDNF(ty, pol)(ctx, ptr = true, etf = false, cache) match {
        // // mkDNF(ty, pol)(ctx, ptr = false, etf = false, cache) match {
        //   case R(dnf) => helper(dnf, pol)
        //   case L((dnf1, dnf2)) => TypeBounds.mk(helper(dnf1, S(false)), helper(dnf2, S(true)))
        // }
        // */
        // pol match {
        //   case S(p) => helper(DNF.mk(ty, p)(ctx, ptr = true, etf = false), pol)
        //   case N =>
        //     val dnf1 = DNF.mk(ty, false)(ctx, ptr = true, etf = false)
        //     val dnf2 = DNF.mk(ty, true)(ctx, ptr = true, etf = false)
        //     // if (dnf1 === dnf2) R(dnf1)
        //     // else 
        //     // L(dnf1 -> dnf2)
        //     TypeBounds.mk(helper(dnf1, S(false)), helper(dnf2, S(true)))
        // }
        
    def go(ty: ST, pol: Opt[Bool]): ST =
    trace(s"norm[${printPol(pol)}] $ty") {
      // process(pol, ty)
      pol match {
        case S(p) => helper(DNF.mk(ty, p)(ctx, ptr = true, etf = false), pol)
        case N =>
          val dnf1 = DNF.mk(ty, false)(ctx, ptr = true, etf = false)
          val dnf2 = DNF.mk(ty, true)(ctx, ptr = true, etf = false)
          // if (dnf1 === dnf2) R(dnf1)
          // else 
          // L(dnf1 -> dnf2)
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
  
  
  
  def simplifyType(st: SimpleType, pol: Opt[Bool] = S(true), removePolarVars: Bool = true, inlineBounds: Bool = true)(implicit ctx: Ctx): SimpleType = {
    
    val coOccurrences: MutMap[(Bool, TypeVariable), MutSet[SimpleType]] = LinkedHashMap.empty
    val occNums: MutMap[(Bool, TypeVariable), Int] = LinkedHashMap.empty[(Bool, TypeVariable), Int].withDefaultValue(0)
    
    // val analyzed = MutSet.empty[PolarVariable]
    // val analyzed2 = MutSet.empty[TypeRef -> Bool]
    // val analyzed2 = MutSet.empty[TypeRef]
    val analyzed2 = MutSet.empty[ST -> Bool]
    
    val occursInvariantly = MutSet.empty[TV]
    
    val analyzed0 = MutSet.empty[PolarVariable]
    
    def analyze1(pol: Opt[Bool], st: SimpleType): Unit = trace(s"analyze1[${printPol(pol)}] $st") { st match {
      case tv: TV =>
        if (pol.isEmpty) occursInvariantly += tv
        // analyzed0.setAnd(tv -> pol) { occNums(pol -> tv) += 1 } {
        // occNums(pol -> tv) += 1
        pol.fold {
          occNums(true -> tv) += 1
          occNums(false -> tv) += 1
        }{ pol =>
          occNums(pol -> tv) += 1
        }
        if (pol =/= S(false)) analyzed0.setAndIfUnset(tv -> true) {
          tv.lowerBounds.foreach(analyze1(S(true), _))
        }
        if (pol =/= S(true)) analyzed0.setAndIfUnset(tv -> false) {
          tv.upperBounds.foreach(analyze1(S(false), _))
        }
      case _ =>
        st.childrenPol(pol).foreach {
          // case (S(pol), st) => analyze1(pol, st)
          // case (N, st) => analyze1(true, st); analyze1(false, st)
          case (pol, st) => analyze1(pol, st)
        }
    }
    }()
    analyze1(pol, st)
    // if (pol =/= S(false)) analyze1(true, st)
    // if (pol =/= S(true)) analyze1(false, st)
    
    println(s"[inv] ${occursInvariantly.iterator.mkString(", ")}")
    println(s"[nums] ${occNums.iterator
      .map(occ => s"${printPol(S(occ._1._1))}${occ._1._2} ${occ._2}")
      .mkString(" ; ")
    }")
    
    
    def analyze2(st: SimpleType, pol: Bool): Unit =
      // analyzeImpl(st.unwrapProxies, pol)
      analyzeImpl(st.unwrapProvs, pol)
    def analyzeImpl(st: SimpleType, pol: Bool): Unit =
        trace(s"analyze2[${printPol(S(pol))}] $st") {
        // trace(s"analyze2[${printPol(S(pol))}] $st       ${analyzed2}") {
        // trace(s"analyze2[${printPol(S(pol))}] $st       ${coOccurrences.filter(_._1._2.nameHint.contains("head"))}") {
          analyzed2.setAndIfUnset(st -> pol) {
          // analyzed2.setAnd(st -> pol) {
          //   st match {
          //     case tv: TV => occNums(pol -> tv) += 1
          //     case _ =>
          //   }
          // } {
            st match {
      // case RecordType(fs) => fs.foreach(f => analyze2(f._2, pol))
      // case TupleType(fs) => fs.foreach(f => analyze2(f._2, pol))
      // case ArrayType(inner) => analyze2(inner, pol)
      case RecordType(fs) => fs.foreach { f => f._2.lb.foreach(analyze2(_, !pol)); analyze2(f._2.ub, pol) }
      case TupleType(fs) => fs.foreach { f => f._2.lb.foreach(analyze2(_, !pol)); analyze2(f._2.ub, pol) }
      case ArrayType(inner) =>
        inner.lb.foreach(analyze2(_, !pol))
        analyze2(inner.ub, pol)
      case FunctionType(l, r) => analyze2(l, !pol); analyze2(r, pol)
      case tv: TypeVariable =>
        // println(s"! $pol $tv ${coOccurrences.get(pol -> tv)}")
        // coOccurrences(pol -> tv) = MutSet(tv)
        // processBounds(tv, pol)
        // if (!analyzed(tv -> pol)) {
          // analyzed(tv -> pol) = true
          process(tv, pol)
        // }
        // analyzed.setAndIfUnset(tv -> pol) { process(tv, pol) }
        // analyzed.setAnd(tv -> pol) { occNums(pol -> tv) += 1 } { process(tv, pol) }
      case _: ObjectTag | ExtrType(_) => ()
      case ct: ComposedType =>
        // val newOccs = MutSet.empty[SimpleType]
        // def go(st: SimpleType): Unit = st match {
        //   case ComposedType(p, l, r) =>
        //     // println(s">> $pol $l $r")
        //     if (p === pol) { go(l); go(r) }
        //     else { analyze2(l, pol); analyze2(r, pol) } // TODO compute intersection if p =/= pol
        //   case _: BaseType => newOccs += st; analyze2(st, pol)
        //   case tv: TypeVariable => newOccs += st; processBounds(tv, pol)
        //   case _ => analyze2(st, pol)
        // }
        // go(ct)
        // // println(s"newOccs ${newOccs}")
        // newOccs.foreach {
        //   case tv: TypeVariable =>
        //     println(s">>>> $tv $newOccs ${coOccurrences.get(pol -> tv)}")
        //     coOccurrences.get(pol -> tv) match {
        //       case Some(os) => os.filterInPlace(newOccs) // computes the intersection
        //       case None => coOccurrences(pol -> tv) = newOccs
        //     }
        //   case _ => ()
        // }
        process(ct, pol)
      case NegType(und) => analyze2(und, !pol)
      case ProxyType(underlying) => analyze2(underlying, pol)
      // case tr @ TypeRef(defn, targs) =>
      //   // analyze2(tr.expand, pol) // FIXME this may diverge; use variance-analysis-based targ traversal instead
      //   if (analyzed2.contains(tr -> pol)) ()
      //   else {
      //     analyzed2 += tr -> pol
      //     analyze2(tr.expand, pol)
      //   }
      case tr @ TypeRef(defn, targs) =>
        // TODO improve with variance analysis
        targs.foreach(analyze2(_, true))
        targs.foreach(analyze2(_, false))
      case Without(base, names) => analyze2(base, pol)
      case TypeBounds(lb, ub) =>
        if (pol) analyze2(ub, true) else analyze2(lb, false)
    }
    }
    }()
    // }(_ => s"~> ${coOccurrences.filter(_._1._2.nameHint.contains("head"))}")
    // def processBounds(tv: TV, pol: Bool) = {
    //   if (!analyzed(tv -> pol)) {
    //     analyzed(tv -> pol) = true
    //     (if (pol) tv.lowerBounds else tv.upperBounds).foreach(analyze2(_, pol))
    //   }
    // }
    // def process(st: SimpleType, pol: Bool, newOccs: MutSet[SimpleType]) = {
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
        // TODO simple TypeRefs
        case tv: TypeVariable =>
          // println(s"$tv ${newOccs.contains(tv)}")
          // occNums(pol -> tv) += 1
          // if (!analyzed.contains(tv -> pol)) 
          // occNums(pol -> tv) += 1
          if (!newOccs.contains(tv)) {
            // analyzed(tv -> pol) = true
            newOccs += st
            // processBounds(tv, pol)
            // (if (pol) tv.lowerBounds else tv.upperBounds).foreach(process(_, pol, newOccs))
            // (if (pol) tv.lowerBounds else tv.upperBounds).foreach(go)
            // (if (pol) tv.lowerBounds.iterator ++ otherLBs(tv) else tv.upperBounds.iterator ++ otherUBs(tv)).foreach(go)
            (if (pol) tv.lowerBounds else tv.upperBounds).foreach(go)
            // analyze2(tv, pol)
          }
        case _ => analyze2(st, pol)
      }
      }()
      go(st)
      // println(newOccs)
      var firstTime = false
      newOccs.foreach {
        case tv: TypeVariable =>
          println(s">>>> $tv $newOccs ${coOccurrences.get(pol -> tv)}")
          // occNums(pol -> tv) += 1
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
    
    // println(s"[occs] ${coOccurrences}")
    println(s"[occs] ${coOccurrences.iterator
      .map(occ => s"${printPol(S(occ._1._1))}${occ._1._2} ${occ._2.mkString("{",",","}")}")
      .mkString(" ; ")
    }")
    
    // This will be filled up after the analysis phase, to influence the reconstruction phase:
    val varSubst = MutMap.empty[TypeVariable, Option[TypeVariable]]
    
    // val allVars = st.getVars
    val allVars = st.getVarsPol(pol).keySet
    
    var recVars = MutSet.from(
      // TODOne rm/update logic?
      // allVars.iterator.filter(tv => tv.lowerBounds.nonEmpty || tv.upperBounds.nonEmpty))
      allVars.iterator.filter(tv => tv.isBadlyRecursive(MutMap.empty[TV, Opt[Bool]]).isDefined))
    // var badRecVars = MutSet.from(
    //   allVars.iterator.filter(tv => tv.isBadlyRecursive(MutMap.empty[TV, Opt[Bool]]).contains(false)))
    // var badRecVars = recVars.map { tv =>
    // }
    
    println(s"[vars] ${allVars}")
    // println(s"[bounds] ${st.showBounds}")
    println(s"[rec] ${recVars}")
    // println(s"[bad rec] ${badRecVars}")
    
    occNums.iterator.foreach { case (k @ (pol, tv), num) =>
      assert(num > 0)
      // if (num === 1 && !occNums.contains(!pol -> tv)) {
      if (inlineBounds && !occNums.contains(!pol -> tv)) {
        if (num === 1) {
          println(s"0[1] $tv")
          varSubst += tv -> None
        } /* else (if (pol) tv.lowerBounds else tv.upperBounds) match {
          case (tv2: TV) :: Nil if !varSubst.contains(tv2) =>
            println(s"[n] $tv -> $tv2")
            // varSubst += tv -> S(tv2)
            varSubst += tv -> N
          case _ =>
        } */
      }
    }
    
    // Simplify away those non-recursive variables that only occur in positive or negative positions:
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
    
    // Unify equivalent variables based on polar co-occurrence analysis:
    val pols = true :: false :: Nil
    allVars.foreach { case v => if (!varSubst.contains(v)) {
      println(s"3[v] $v ${coOccurrences.get(true -> v)} ${coOccurrences.get(false -> v)}")
      pols.foreach { pol =>
        coOccurrences.get(pol -> v).iterator.flatMap(_.iterator).foreach {
          case w: TypeVariable if !(w is v) && !varSubst.contains(w)
              // && (recVars.contains(v) === recVars.contains(w))
              // ^ Note: We avoid merging rec and non-rec vars, because the non-rec one may not be strictly polar
              //       As an example of this, see [test:T1].
              && (v.nameHint.nonEmpty || w.nameHint.isEmpty)
              // ^ Don't merge in this direction if that would override a nameHint
            =>
            println(s"  [w] $w ${coOccurrences.get(pol -> w)}")
            if (coOccurrences.get(pol -> w).forall(_(v))) {
              println(s"  [U] $w := $v") // we unify w into v
              varSubst += w -> S(v)
              // * Since w gets unified with v, we need to merge their bounds,
              // * and also merge the other co-occurrences of v and w from the other polarity (!pol).
              // * For instance,
              // *  consider that if we merge v and w in `(v & w) -> v & x -> w -> x`
              // *  we get `v -> v & x -> v -> x`
              // *  and the old positive co-occ of v, {v,x} should be changed to just {v,x} & {w,v} == {v}!
              recVars -= w
              v.lowerBounds :::= w.lowerBounds
              v.upperBounds :::= w.upperBounds
              
              // When removePolarVars is enabled, wCoOcss/vCoOcss may not be defined:
              // for {
              //   wCoOccs <- coOccurrences.get((!pol) -> w)
              //   vCoOccs <- coOccurrences.get((!pol) -> v)
              // } vCoOccs.filterInPlace(t => t === v || wCoOccs(t))
              coOccurrences.get((!pol) -> w).foreach { wCoOccs =>
                coOccurrences.get((!pol) -> v) match {
                  case S(vCoOccs) => vCoOccs.filterInPlace(t => t === v || wCoOccs(t))
                  case N => coOccurrences((!pol) -> v) = wCoOccs
                }
              }
              
            }
          case _ =>
        }
      }
    }}
    
    println(s"[sub] ${varSubst.map(k => k._1.toString + " -> " + k._2).mkString(", ")}")
    
    println(s"[bounds] ${st.showBounds}")
    
    // The rec vars may have changed!
    
    // TODO filter out varSubst keys?
    
    // recVars = MutSet.from(
    //   // TODOne rm/update logic?
    //   // allVars.iterator.filter(tv => tv.lowerBounds.nonEmpty || tv.upperBounds.nonEmpty))
    //   allVars.iterator.filter(tv => tv.isBadlyRecursive(MutMap.empty[TV, Opt[Bool]]).isDefined))
    recVars = MutSet.from(
      allVars.iterator.filter(tv =>
        // tv.lbRecOccs.forall(_ =/= S(false)) && tv.ubRecOccs.forall(_ =/= S(true))
        (tv.lbRecOccs, tv.ubRecOccs) match {
          // case (S(N), _) | (_, S(N)) => true
          case (S(N | S(true)), _) | (_, S(N | S(false))) => true
          // case (S(S(false)), _) => false
          // case (_, S(S(true))) => false
          // case (N, N) => false
          // case (S(S(false)), _) | (_, S(S(true))) | (N, N) => false
          case _ => false
        }
      ))
    println(s"[real rec] ${recVars}")
    
    val renewals = MutMap.empty[TypeVariable, TypeVariable]
    
    def mergeTransform(pol: Bool, ts: Ls[ST], parent: Opt[TV]): ST =
      if (pol) transform(ts.foldLeft(BotType: ST)(_ | _), S(pol), parent)
      else transform(ts.foldLeft(TopType: ST)(_ & _), S(pol), parent)
    
    def transform(st: SimpleType, pol: Opt[Bool], parent: Opt[TV]): SimpleType =
          trace(s"transform[${printPol(pol)}] $st") {
          def transformField(f: FieldType): FieldType = f match {
            // case FieldType(S(lb), ub) =>
            // case FieldType(N, ub) => 
            case FieldType(S(lb), ub) if lb === ub =>
              val b = transform(ub, N, N)
              FieldType(S(b), b)(f.prov)
            case _ => f.update(transform(_, pol.map(!_), N), transform(_, pol, N))
          }
        st match {
      // case RecordType(fs) => RecordType(fs.map(f => f._1 -> transform(f._2, pol)))(st.prov)
      // case TupleType(fs) => TupleType(fs.map(f => f._1 -> transform(f._2, pol)))(st.prov)
      // case ArrayType(inner) => ArrayType(transform(inner, pol))(st.prov)
      // case FunctionType(l, r) => FunctionType(transform(l, pol.map(!_)), transform(r, pol))(st.prov)
      // 
      // case RecordType(fs) => RecordType(fs.mapValues(_.update(transform(_, !pol), transform(_, pol))))(st.prov)
      // case TupleType(fs) => TupleType(fs.mapValues(_.update(transform(_, !pol), transform(_, pol))))(st.prov)
      // case ArrayType(inner) => ArrayType(inner.update(transform(_, !pol), transform(_, pol)))(st.prov)
      // case FunctionType(l, r) => FunctionType(transform(l, !pol), transform(r, pol))(st.prov)
      // 
      // case RecordType(fs) => RecordType(fs.mapValues(_.update(transform(_, pol.map(!_)), transform(_, pol))))(st.prov)
      // case TupleType(fs) => TupleType(fs.mapValues(_.update(transform(_, pol.map(!_)), transform(_, pol))))(st.prov)
      // case ArrayType(inner) => ArrayType(inner.update(transform(_, pol.map(!_)), transform(_, pol)))(st.prov)
      // case FunctionType(l, r) => FunctionType(transform(l, pol.map(!_)), transform(r, pol))(st.prov)
      // 
      case RecordType(fs) => RecordType(fs.mapValues(_ |> transformField))(st.prov)
      case TupleType(fs) => TupleType(fs.mapValues(_ |> transformField))(st.prov)
      case ArrayType(inner) => ArrayType(inner |> transformField)(st.prov)
      case FunctionType(l, r) => FunctionType(transform(l, pol.map(!_), N), transform(r, pol, N))(st.prov)
      
      case _: ObjectTag | ExtrType(_) => st
      case tv: TypeVariable if parent.exists(_ === tv) => if (pol.get) BotType else TopType
      case tv: TypeVariable =>
        // println(s"transform[${printPol(pol)}] $tv")
        // println(s"tv $tv ${tv.upperBounds}")
        varSubst.get(tv) match {
          case S(S(ty)) =>
            println(s"-> $ty"); 
            transform(ty, pol, parent)
          // case S(N) => pol.fold(die)(pol => ExtrType(pol)(noProv))
          // case S(N) => pol.fold(TypeBounds(BotType, TopType)(noProv):ST)(pol => ExtrType(pol)(noProv))
          case S(N) =>
            println(s"-> bound");
            pol.fold(
            TypeBounds.mk(mergeTransform(true, tv.lowerBounds, parent), mergeTransform(false, tv.upperBounds, parent)): ST
          )(pol =>
            // (if (pol) tv.lowerBounds else tv.upperBounds).foldLeft(ExtrType(pol)(noProv)))
            // mergeTransform(pol, tv))
            mergeTransform(pol, if (pol) tv.lowerBounds else tv.upperBounds, parent))
          case N =>
            var wasDefined = true
            val res = renewals.getOrElseUpdate(tv, {
              wasDefined = false
              val nv = freshVar(noProv, tv.nameHint)(tv.level)
              println(s"Renewed $tv ~> $nv")
              nv
            })
            // if (inlineBounds(tv))
            if (inlineBounds && pol.isDefined && !occursInvariantly(tv) && !recVars.contains(tv)) { // inline the bounds of non-rec vars
              // mergeTransform(pol.get, tv :: (if (pol.get) tv.lowerBounds else tv.upperBounds))
              // mergeTransform(pol.get, if (pol.get) tv.lowerBounds else tv.upperBounds)
              println(s"Inlining bounds of $tv (~> $res)")
              if (pol.get) mergeTransform(true, tv.lowerBounds, S(tv)) | res
              else mergeTransform(false, tv.upperBounds, S(tv)) & res
            } else 
            if (!wasDefined) {
              /* 
              println(s"Setting bounds of $res")
              res.lowerBounds = tv.lowerBounds.map(transform(_, S(true), S(tv)))
              res.upperBounds = tv.upperBounds.map(transform(_, S(false), S(tv)))
              
              // res
              
              // It used to be that pol/coOcc info was no longer be valid here, but that should be fixed
              // /* 
              // (coOccurrences.get(true -> v0), coOccurrences.get(false -> v0)) match { // TODO dedup
              //   case (Some(_), None) | (None, Some(_)) =>
              if (pol.isDefined && coOccurrences.get(!pol.get -> tv).isEmpty) { // if the variable is polar
                val allBounds = res.lowerBounds ++ res.upperBounds
                // assert(allBounds.size === res.lowerBounds.size)
                assert(res.lowerBounds.isEmpty || res.upperBounds.isEmpty)
                println(s"$tv $res $allBounds ${tv.lowerBounds} ${tv.upperBounds}")
                if (allBounds.forall { case tv2: TV => true; case _ => false }) { // Q: filter out same as tv?
                  println(s"NEW SUBS $tv -> N")
                  varSubst += tv -> N
                  merge(pol.get, allBounds)
                  // merge(pol.get, allBounds.filterNot(_ === tv))
                  // merge(pol.get, allBounds.filterNot(parent.contains))
                } else res
              }
              else res
              // */
              */
              
              def setBounds = {
                println(s"Setting bounds of $res")
                res.lowerBounds = tv.lowerBounds.map(transform(_, S(true), S(tv)))
                res.upperBounds = tv.upperBounds.map(transform(_, S(false), S(tv)))
                res
              }
              
              if (pol.isDefined && coOccurrences.get(!pol.get -> tv).isEmpty) { // if the variable is polar
                // val allBounds = tv.lowerBounds ++ tv.upperBounds
                val allBounds = if (pol.get) tv.lowerBounds else tv.upperBounds
                
                // * only true if we do a pass of `removeIrrelevantBounds` before calling `simplifyType`:
                // assert(tv.lowerBounds.isEmpty || tv.upperBounds.isEmpty, (tv, tv.lowerBounds, tv.upperBounds))
                
                println(s">?> $tv $res $allBounds ${tv.lowerBounds} ${tv.upperBounds}")
                if (allBounds.forall { case tv2: TV => varSubst.get(tv2).forall(_.isDefined); case _ => false }) { // Q: filter out same as tv?
                  println(s"NEW SUBS $tv -> N")
                  varSubst += tv -> N
                  mergeTransform(pol.get, allBounds, parent)
                  // merge(pol.get, allBounds)
                  // merge(pol.get, allBounds.filterNot(_ === tv))
                  // merge(pol.get, allBounds.filterNot(parent.contains))
                } else setBounds
              }
              else setBounds
              
            } else res
        }
      case ty @ ComposedType(true, l, r) => transform(l, pol, parent) | transform(r, pol, parent)
      case ty @ ComposedType(false, l, r) => transform(l, pol, parent) & transform(r, pol, parent)
      case NegType(und) => transform(und, pol.map(!_), N).neg()
      case WithType(base, RecordType(fs)) => WithType(transform(base, pol, N), 
        RecordType(fs.mapValues(_.update(transform(_, pol.map(!_), N), transform(_, pol, N))))(noProv))(noProv)
      case ProxyType(underlying) => transform(underlying, pol, parent)
      case tr @ TypeRef(defn, targs) =>
        // transform(tr.expand, pol) // FIXedME may diverge; and we should try to keep these!
        // TypeRef(defn, targs.map(targ => TypeBounds(transform(targ, false), transform(targ, true))(noProv)))(tr.prov)
        TypeRef(defn, targs.map(transform(_, N, N)))(tr.prov) // TODO improve with variance analysis
      case wo @ Without(base, names) =>
        if (names.isEmpty) transform(base, pol, N)
        // else Without(transform(base, pol, N), names)(wo.prov)
        else if (pol === S(true)) transform(base, pol, N).withoutPos(names)
        else transform(base, pol, N).without(names)
      case tb @ TypeBounds(lb, ub) =>
        pol.fold[ST](TypeBounds.mk(transform(lb, S(false), parent), transform(ub, S(true), parent), noProv))(pol =>
          if (pol) transform(ub, S(true), parent) else transform(lb, S(false), parent))
    }
    }(r => s"~> $r")
    transform(st, pol, N)
    
  }
  
  
  
  def unskidTypes_!(st: SimpleType, pol: Bool = true)(implicit ctx: Ctx): SimpleType = {
    // implicit val cache: MutMap[TV, Opt[Bool]] = MutMap.empty
    val allVarPols = st.getVarsPol(S(pol))
    println(s"allVarPols: ${allVarPols.iterator.map(e => s"${printPol(e._2)}${e._1}").mkString(", ")}")
    val processed = MutSet.empty[TV]
    // val consed = allVarPols.iterator.filter(_._2.isDefined).map { case (tv, pol) =>
    
    // FIXME values should actually be lists as several TVs may have the same bound
    val consed = allVarPols.iterator.collect { case (tv, S(pol)) =>
      if (pol) (true, tv.lowerBounds.foldLeft(BotType: ST)(_ | _)) -> tv
      else (false, tv.upperBounds.foldLeft(TopType: ST)(_ & _)) -> tv
    }.toMap
    
    println(s"consed: $consed")
    
    // def process(st: ST, pol: Opt[Bool]): ST = st match {
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
        // // val found = 
        // pol match {
        //   case S(p) =>
        //     consed.get(p -> st) match {
        //       case S(tv) if parent.forall(_ isnt tv) =>
        //         tv
        //       case _ => st.mapPol(pol)(process(_, _, parent))
        //     }
        //   case N => st.mapPol(pol)(process(_, _, parent))
        // }
        /* 
        val mapped = st.mapPol(pol)(process(_, _, parent))
        pol match {
          case S(p) =>
            consed.get(p -> mapped) match {
              case S(tv) if parent.forall(_ isnt tv) =>
                tv
              case _ => mapped
            }
          case N => mapped
        }
        */
        lazy val mapped = st.mapPol(pol, smart = true)(process(_, _, parent))
        pol match {
          case S(p) =>
            // println(s"!1! ${st} ${consed.get(p -> st)}")
            consed.get(p -> st) match {
              case S(tv) if parent.forall(_ isnt tv) =>
                println(s"!unskid-1! ${st} -> $tv")
                // tv
                process(pol, tv, parent)
              case _ =>
                // println(s"!2! ${mapped} ${consed.get(p -> mapped)}")
                consed.get(p -> mapped) match {
                  case S(tv) if parent.forall(_ isnt tv) =>
                    println(s"!unskid-2! ${mapped} -> $tv")
                    // tv
                    process(pol, tv, parent)
                  case _ => mapped
                }
            }
          case N => mapped
        }
    }
    // }(r => s"~> $r")
    process(S(pol), st, N)
    // st
  }
  
  
  
  def factorRecursiveTypes_!(st: SimpleType, approximateRecTypes: Bool, pol: Opt[Bool] = S(true))(implicit ctx: Ctx): SimpleType = {
    
    // implicit val cache: MutMap[TV, Opt[Bool]] = MutMap.empty
    val allVarPols = st.getVarsPol(pol)
    println(s"allVarPols: ${allVarPols.iterator.map(e => s"${printPol(e._2)}${e._1}").mkString(", ")}")
    val processed = MutSet.empty[TV]
    // val consed = allVarPols.iterator.filter(_._2.isDefined).map { case (tv, pol) =>
    
    val recVars = MutSet.from(
      // TODOne rm/update logic?
      // allVars.iterator.filter(tv => tv.lowerBounds.nonEmpty || tv.upperBounds.nonEmpty))
      allVarPols.keysIterator.filter(tv => tv.isBadlyRecursive(MutMap.empty[TV, Opt[Bool]]).isDefined))
    println(s"recVars: $recVars")
    
    
    val varSubst = MutMap.empty[TV, TV]
    
    allVarPols.foreach {
      case (tv1, S(p1)) =>
        println(s"Consider $tv1")
        // val b1 = if (p1) tv1.lowerBounds.head
        (if (p1) tv1.lowerBounds else tv1.upperBounds) match {
          case b1 :: Nil => 
            // println(s"b $b")
            allVarPols.foreach {
              case (tv2, S(p2)) if p2 === p1 && (tv2 isnt tv1) && !varSubst.contains(tv1) && !varSubst.contains(tv2) =>
                (if (p2) tv2.lowerBounds else tv2.upperBounds) match {
                  case b2 :: Nil => 
                    // val b1 = if (p1)
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
                        // case (ProvType(underlying1), ProvType(underlying2)) => nope // TODO
                        // case (ProxyType(underlying1), ProxyType(underlying2)) => unify(underlying1, underlying2)
                        case (WithType(base1, rcd1), WithType(base2, rcd2)) =>
                          unify(base1, base2) && unify(rcd1, rcd2)
                        case (ProxyType(underlying1), _) => unify(underlying1, ty2)
                        case (_, ProxyType(underlying2)) => unify(ty1, underlying2)
                        case (TypeRef(defn1, targs1), TypeRef(defn2, targs2)) =>
                          (defn1 === defn2 || nope) && targs1.lazyZip(targs2).forall(unify)
                        // case (NegTrait(tt1), NegTrait(tt2)) =>
                        // case (NegVar(tv1), NegVar(tv2)) =>
                        case _ => nope
                      }
                    }
                    println(s"Consider $tv1 ~ $tv2")
                    if (unify(b1, b2)) {
                      println(s"Yes! $tv2 := $tv1")
                      varSubst += tv2 -> tv1
                    }
                  case _ => ()
                }
              // case tv2 => 
              //   println(s"Not considered $tv1 ~ $tv2")
              case _ => ()
            }
          case _ => ()
        }
      case _ => ()
    }
    
    println(s"[subs] ${varSubst}")
    
    if (varSubst.nonEmpty) subst(st, varSubst.toMap, substInMap = true) else st
    
  }
  
  
    
}
