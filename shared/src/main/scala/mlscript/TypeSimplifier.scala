package mlscript

import scala.collection.mutable.{Map => MutMap, Set => MutSet, LinkedHashMap, LinkedHashSet}
import scala.collection.immutable.{SortedMap, SortedSet}
import scala.util.chaining._
import mlscript.utils._, shorthands._

trait TypeSimplifier { self: Typer =>
  
  
  // TODO inline logic
  private def mkDNF(ty: SimpleType, pol: Opt[Bool])(implicit ctx: Ctx, ptr: PreserveTypeRefs, etf: ExpandTupleFields, cache: MutMap[TV, Opt[Bool]]): Either[(DNF, DNF), DNF] = {
    // implicit val preserveTypeRefs: Bool = true
    // println(s"mk[${printPol(pol)}] ${ty}")
    pol match {
      case S(true) => R(DNF.mk(ty, true))
      case S(false) => R(DNF.mk(ty, false))
      case N =>
        // TODO less inefficient! don't recompute
        val dnf1 = DNF.mk(ty, true)
        // if (dnf1.cs.exists(_.vars.nonEmpty))
        val dnf2 = DNF.mk(ty, false)
        // if (dnf1.cs.forall(_.vars.isEmpty) && dnf1 === dnf2) R(dnf1)
        println(s"vars ${dnf1.cs.map(_.vars)}")
        if (dnf1.cs.forall(_.vars.forall(_.isBadlyRecursive =/= S(false))) && dnf1 === dnf2) R(dnf1)
        else L(dnf1 -> dnf2)
    }
  }
  
  def removeIrrelevantBounds(ty: SimpleType, pol: Opt[Bool] = S(true))(implicit ctx: Ctx): SimpleType = {
    
    val pols = ty.getVarsPol(S(true))
    
    println(s"Pols ${pols}")
    
    val renewed = MutMap.empty[TypeVariable, TypeVariable]
    
    def renew(tv: TypeVariable): TypeVariable =
      renewed.getOrElseUpdate(tv,
        freshVar(noProv, tv.nameHint)(tv.level) tap { fv => println(s"Renewed $tv ~> $fv") })
    
    // def process(ty: ST): ST =
    //     // trace(s"process($ty)") {
    //     trace(s"process($ty)  ${renewed}") {
    //     ty.map {
    //   case tv: TypeVariable =>
    //     var isNew = false
    //     val nv = renewed.getOrElseUpdate(tv, {isNew = true; renew(tv)})
    //     // renewed.getOrElseUpdate(tv,
    //     //   freshVar(noProv, tv.nameHint)(tv.level) tap { fv => println(s"Renewed $tv ~> $fv") })
    //     // val nv = renew(v)
    //     if (isNew) {
    //       if (pols(tv).forall(_ === true)) nv.lowerBounds = tv.lowerBounds.map(process)
    //       if (pols(tv).forall(_ === false)) nv.upperBounds = tv.upperBounds.map(process).tap(b=>println(s"${b.map(_.getClass)}"))
    //     }
    //     println(tv, nv, nv.lowerBounds, nv.upperBounds)
    //     nv
    //   case st => process(st)
    // }
    // }(r => s"= $r")
    
    def process(ty: ST): ST =
        // trace(s"process($ty)") {
        ty match {
      case tv: TypeVariable =>
        var isNew = false
        val nv = renewed.getOrElseUpdate(tv, {isNew = true; renew(tv)})
        // renewed.getOrElseUpdate(tv,
        //   freshVar(noProv, tv.nameHint)(tv.level) tap { fv => println(s"Renewed $tv ~> $fv") })
        // val nv = renew(v)
        if (isNew) {
          if (pols(tv).forall(_ === true)) nv.lowerBounds = tv.lowerBounds.map(process)
          if (pols(tv).forall(_ === false)) nv.upperBounds = tv.upperBounds.map(process)//.tap(b=>println(s"${b.map(_.getClass)}"))
        }
        // println(tv, nv, nv.lowerBounds, nv.upperBounds)
        nv
      case st => st.map(process)
    }
    // }(r => s"= $r")
    
    process(ty)
  }
  
  def canonicalizeType(ty: SimpleType, pol: Opt[Bool] = S(true))(implicit ctx: Ctx): SimpleType = {
    // type PolarType = (DNF, Bool)
    // type PolarType = DNF
    type PolarType = (DNF, Opt[Bool])
    
    // val r = removeIrrelevantBounds(ty, pol)
    // println(r)
    // println(r.showBounds)
    
    val recursive = MutMap.empty[PolarType, TypeVariable]
    val recursiveVars = MutSet.empty[TypeVariable] // For rec nonpolar vars
    
    val renewed = MutMap.empty[TypeVariable, TypeVariable]
    
    implicit val cache: MutMap[TV, Opt[Bool]] = MutMap.empty
    
    val allVars = ty.getVars
    def renew(tv: TypeVariable): TypeVariable =
      renewed.getOrElseUpdate(tv,
        freshVar(noProv, tv.nameHint)(tv.level) tap { fv => println(s"Renewed $tv ~> $fv") })
    
    def goDeep(ty: SimpleType, pol: Opt[Bool])(implicit inProcess: Set[PolarType]): SimpleType = ty match {
        case tv: TV if recursiveVars.contains(tv) => renew(tv)
        case _ =>
      // go1(go0(ty, pol), pol)
      go0(ty, pol) match {
        case R(dnf) => go1(dnf, pol)
        case L((dnf1, dnf2)) =>
          TypeBounds.mk(go1(dnf1, S(false)), go1(dnf2, S(true)), noProv)
      }
    }
    
    // Turn the outermost layer of a SimpleType into a DNF, leaving type variables untransformed
    def go0(ty: SimpleType, pol: Opt[Bool])(implicit inProcess: Set[PolarType]): Either[(DNF, DNF), DNF] = 
    trace(s"ty[${printPol(pol)}] $ty") {
      
      implicit val etf: ExpandTupleFields = false
      
      // TODO should we also coalesce nvars? is it bad if we don't? -> probably, yes...
      def rec(dnf: DNF, done: Set[TV], pol: Bool): DNF = dnf.cs.iterator.map { c =>
        // val vs = c.vars.filterNot(done)
        // val vs = c.vars.filterNot(v => recursiveVars.contains(v) || v.isRecursive === S(false) && {
        //   recursiveVars += v
        //   val nv = renew(v)
        //   nv.lowerBounds = v.lowerBounds.map(goDeep(_, S(true)))
        //   nv.upperBounds = v.upperBounds.map(goDeep(_, S(false)))
        //   true
        // } || done(v))
        val vs = c.vars.filterNot(v => recursiveVars.contains(v) || v.isBadlyRecursive === S(false) && {
          println(s"$v is badly recursive...")
          recursiveVars += v
          val nv = renew(v)
          nv.lowerBounds = v.lowerBounds.map(goDeep(_, S(true)))
          nv.upperBounds = v.upperBounds.map(goDeep(_, S(false)))
          true
        // } || done(v))
        } || done(v) && {println(s"Done $v"); true})
        vs.iterator.map { tv =>
        // vs.iterator.filter(_.isRecursive =/= S(false)).map { tv =>
          println(s"Consider $tv ${tv.lowerBounds} ${tv.upperBounds}")
          val b =
            if (pol) tv.lowerBounds.foldLeft(tv:ST)(_ | _)
            else tv.upperBounds.foldLeft(tv:ST)(_ & _)
          // println(s"b $b")
          val bd = rec(DNF.mk(b, pol)(ctx, ptr = true), done + tv, pol)
          // println(s"bd $bd")
          bd
        }
        .foldLeft(DNF(c.copy(vars = c.vars.filterNot(vs))::Nil))(_ & _)
      }.foldLeft(DNF.extr(false))(_ | _)
      
      // rec(DNF.mk(ty, pol)(ctx), Set.empty)
      mkDNF(ty, pol)(ctx, ptr = true, etf = false, cache) match {
      // mkDNF(ty, pol)(ctx, ptr = true, etf = false, cache) match {
        case R(dnf) =>
          // println(dnf.cs.map(_.vars.isEmpty))
          pol.fold(R(dnf))(p => R(rec(dnf, Set.empty, p)))
        case L((dnf1, dnf2)) => L(rec(dnf1, Set.empty, false), rec(dnf2, Set.empty, true))
      }
      
    }(r => s"-> $r")
    
    // Merge the bounds of all type variables of the given DNF, and traverse the result
    def go1(ty: DNF, pol: Opt[Bool])
        (implicit inProcess: Set[PolarType]): SimpleType = trace(s"DNF[${printPol(pol)}] $ty") {
      if (ty.isBot) ty.toType(sort = true) else {
        val pty = ty -> pol
        // val pty = ty
        if (inProcess.contains(pty))
          recursive.getOrElseUpdate(pty,
            freshVar(noProv)(ty.level) tap { fv => println(s"Fresh rec $pty ~> $fv") })
        else {
          (inProcess + pty) pipe { implicit inProcess =>
            val res = DNF(ty.cs.map { case Conjunct(lnf, vars, rnf, nvars) =>
              def adapt(pol: Opt[Bool])(l: LhsNf): LhsNf = l match {
                case LhsRefined(b, ts, RecordType(fs), trs) => LhsRefined(
                  b.map {
                    case ft @ FunctionType(l, r) =>
                      FunctionType(goDeep(l, pol.map(!_)), goDeep(r, pol))(noProv)
                    // case wo @ Without(b, ns) if ns.isEmpty =>
                    // case wo @ Without(tr @ TypeRef(defn, targs), ns) if ns.isEmpty =>
                    //   // FIXME hacky!!
                    //   // FIXedME recurse in type args!!! not sound otherwise
                    //   // TODO actually make polarity optional and recurse with None
                    //   Without(TypeRef(defn, targs.map(targ =>
                    //     TypeBounds(goDeep(targ, false), goDeep(targ, true))(noProv)))(tr.prov), ns)(wo.prov)
                    case wo @ Without(b, ns) =>
                      Without(goDeep(b, pol), ns)(noProv)
                    case ft @ TupleType(fs) =>
                      TupleType(fs.mapValues(_.update(goDeep(_, pol.map(!_)), goDeep(_, pol))))(noProv)
                    case ar @ ArrayType(inner) =>
                      ArrayType(inner.update(goDeep(_, pol.map(!_)), goDeep(_, pol)))(noProv)
                    case pt: ClassTag => pt
                  },
                  ts,
                  // RecordType(fs.map(f => f._1 -> goDeep(f._2, pol)))(noProv)
                  RecordType(fs.map {
                    // case (nme, ty) if nme.name.isCapitalized && nme.name.contains('#') =>
                    //   ty match {
                    //     // case FunctionType(lb, ub) =>
                    //     //   nme -> FunctionType(goDeep(lb, pol.map(!_)), goDeep(ub, pol))(ty.prov)
                    //     // case _ => lastWords(s"$nme: $ty")
                    //     case FieldType(lb, ub) =>
                    //       nme -> FieldType(lb.map(goDeep(_, pol.map(!_))), goDeep(ub, pol))(ty.prov)
                    //   }
                    // case (nme, ty) => nme -> goDeep(ty, pol)
                    case (nme, fty @ FieldType(lb, ub)) =>
                      nme -> FieldType(lb.map(goDeep(_, pol.map(!_))), goDeep(ub, pol))(fty.prov)
                  })(noProv),
                  trs.map {
                    case (d, tr @ TypeRef(defn, targs)) =>
                      // TODO actually make polarity optional and recurse with None
                      d -> TypeRef(defn, targs.map(targ =>
                        TypeBounds.mk(goDeep(targ, S(false)), goDeep(targ, S(true)), noProv)))(tr.prov)
                  }
                )
                case LhsTop => LhsTop
              }
              //     RecordType(fs.mapValues(_.update(goDeep(_, !pol), goDeep(_, pol))))(noProv)
              //   )
              //   case LhsTop => LhsTop
              // }
              // def adapt2(pol: Bool)(l: RhsNf): RhsNf = l match {
              //   case RhsField(name, ty) => RhsField(name, ty.update(goDeep(_, !pol), goDeep(_, pol)))
              def adapt2(pol: Opt[Bool])(l: RhsNf): RhsNf = l match {
                // case RhsField(name, ty) => RhsField(name, goDeep(ty, pol))
                case RhsField(name, ty) => RhsField(name, ty.update(goDeep(_, pol.map(!_)), goDeep(_, pol)))
                case RhsBases(prims, bf) =>
                  // TODO refactor to handle goDeep returning something else...
                  RhsBases(prims, bf match {
                    case N => N
                    case S(L(bt)) => goDeep(bt, pol) match {
                      case bt: MiscBaseType => S(L(bt))
                      case ExtrType(true) => N
                      case _ => ???
                    }
                    case S(R(r)) => S(R(RhsField(r.name, r.ty.update(goDeep(_, pol.map(!_)), goDeep(_, pol)))))
                  })
                case RhsBot => RhsBot
              }
              Conjunct(adapt(pol)(lnf), vars.map(renew), adapt2(pol.map(!_))(rnf), nvars.map(renew))
            })
            val adapted = res.toType(sort = true)
            recursive.get(pty) match {
              case Some(v) =>
                println(s"!!!")
                // pol match {
                //   // case S(pol) =>
                //   //   val bs = if (pol) v.lowerBounds else v.upperBounds
                //   //   if (bs.isEmpty) { // it's possible we have already set the bounds in a sibling call
                //   //     if (pol) v.lowerBounds ::= adapted else v.upperBounds ::= adapted
                //   //   }
                //   case S(true) =>
                //     // it's possible we have already set the bounds in a sibling call
                //     if (v.lowerBounds.isEmpty) {
                //       v.lowerBounds ::= adapted
                //     }
                //   case N =>
                //     v.lowerBounds ::= adapted
                //     v.upperBounds ::= adapted
                // }
                if (v.lowerBounds.isEmpty && pol =/= S(false)) {
                // if (v.lowerBounds.isEmpty) {
                  v.lowerBounds ::= adapted
                }
                if (v.upperBounds.isEmpty && pol =/= S(true)) {
                // if (v.upperBounds.isEmpty) {
                  v.upperBounds ::= adapted
                }
                v
              case None =>
                // println(s"!??")
                adapted
            }
          }
        }
      }
    }(r => s"~> $r")
    
    goDeep(ty, pol)(Set.empty)
    
  }
  
  
  /** Precondition: we assume that the type has been through canonicalizeType,
    * so that all type variables that still have bounds are recursive ones... */
  def simplifyType(st: SimpleType, pol: Opt[Bool] = S(true), removePolarVars: Bool = true)(implicit ctx: Ctx): SimpleType = {
    
    val coOccurrences: MutMap[(Bool, TypeVariable), MutSet[SimpleType]] = LinkedHashMap.empty
    
    // val analyzed = MutSet.empty[PolarVariable]
    // val analyzed2 = MutSet.empty[TypeRef -> Bool]
    // val analyzed2 = MutSet.empty[TypeRef]
    val analyzed2 = MutSet.empty[ST -> Bool]
    
    // def analyze(st: SimpleType, pol: Bool): Unit = st match {
    //   case RecordType(fs) => fs.foreach { f => f._2.lb.foreach(analyze(_, !pol)); analyze(f._2.ub, pol) }
    //   case TupleType(fs) => fs.foreach { f => f._2.lb.foreach(analyze(_, !pol)); analyze(f._2.ub, pol) }
    //   case ArrayType(inner) =>
    //     inner.lb.foreach(analyze(_, !pol))
    //     analyze(inner.ub, pol)
    def analyze(st: SimpleType, pol: Bool): Unit =
        trace(s"analyze[${printPol(S(pol))}] $st") {
        // trace(s"analyze[${printPol(S(pol))}] $st       ${analyzed2}") {
        // trace(s"analyze[${printPol(S(pol))}] $st       ${coOccurrences.filter(_._1._2.nameHint.contains("head"))}") {
          analyzed2.setAndIfUnset(st -> pol) {
            st match {
      // case RecordType(fs) => fs.foreach(f => analyze(f._2, pol))
      // case TupleType(fs) => fs.foreach(f => analyze(f._2, pol))
      // case ArrayType(inner) => analyze(inner, pol)
      case RecordType(fs) => fs.foreach { f => f._2.lb.foreach(analyze(_, !pol)); analyze(f._2.ub, pol) }
      case TupleType(fs) => fs.foreach { f => f._2.lb.foreach(analyze(_, !pol)); analyze(f._2.ub, pol) }
      case ArrayType(inner) =>
        inner.lb.foreach(analyze(_, !pol))
        analyze(inner.ub, pol)
      case FunctionType(l, r) => analyze(l, !pol); analyze(r, pol)
      case tv: TypeVariable =>
        // println(s"! $pol $tv ${coOccurrences.get(pol -> tv)}")
        // coOccurrences(pol -> tv) = MutSet(tv)
        // processBounds(tv, pol)
        // if (!analyzed(tv -> pol)) {
          // analyzed(tv -> pol) = true
          process(tv, pol)
        // }
      case _: ObjectTag | ExtrType(_) => ()
      case ct: ComposedType =>
        // val newOccs = MutSet.empty[SimpleType]
        // def go(st: SimpleType): Unit = st match {
        //   case ComposedType(p, l, r) =>
        //     // println(s">> $pol $l $r")
        //     if (p === pol) { go(l); go(r) }
        //     else { analyze(l, pol); analyze(r, pol) } // TODO compute intersection if p =/= pol
        //   case _: BaseType => newOccs += st; analyze(st, pol)
        //   case tv: TypeVariable => newOccs += st; processBounds(tv, pol)
        //   case _ => analyze(st, pol)
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
      case NegType(und) => analyze(und, !pol)
      case ProxyType(underlying) => analyze(underlying, pol)
      // case tr @ TypeRef(defn, targs) =>
      //   // analyze(tr.expand, pol) // FIXME this may diverge; use variance-analysis-based targ traversal instead
      //   if (analyzed2.contains(tr -> pol)) ()
      //   else {
      //     analyzed2 += tr -> pol
      //     analyze(tr.expand, pol)
      //   }
      case tr @ TypeRef(defn, targs) =>
        // TODO improve with variance analysis
        targs.foreach(analyze(_, true))
        targs.foreach(analyze(_, false))
      case Without(base, names) => analyze(base, pol)
      case TypeBounds(lb, ub) =>
        if (pol) analyze(ub, true) else analyze(lb, false)
    }}
    }()
    // }(_ => s"~> ${coOccurrences.filter(_._1._2.nameHint.contains("head"))}")
    // def processBounds(tv: TV, pol: Bool) = {
    //   if (!analyzed(tv -> pol)) {
    //     analyzed(tv -> pol) = true
    //     (if (pol) tv.lowerBounds else tv.upperBounds).foreach(analyze(_, pol))
    //   }
    // }
    // def process(st: SimpleType, pol: Bool, newOccs: MutSet[SimpleType]) = {
    def process(st: SimpleType, pol: Bool) = {
      val newOccs = MutSet.empty[SimpleType]
      def go(st: SimpleType): Unit =
          trace(s"go $st   (${newOccs.mkString(", ")})") {
          st match {
        case ComposedType(p, l, r) =>
          // println(s">> $pol $l $r")
          if (p === pol) { go(l); go(r) }
          else { analyze(l, pol); analyze(r, pol) } // TODO compute intersection if p =/= pol
        case _: BaseType | _: TypeRef => newOccs += st; analyze(st, pol)
        // TODO simple TypeRefs
        case tv: TypeVariable =>
          // println(s"$tv ${newOccs.contains(tv)}")
          if (!newOccs.contains(tv)) {
            // analyzed(tv -> pol) = true
            newOccs += st
            // processBounds(tv, pol)
            // (if (pol) tv.lowerBounds else tv.upperBounds).foreach(process(_, pol, newOccs))
            (if (pol) tv.lowerBounds else tv.upperBounds).foreach(go)
            // analyze(tv, pol)
          }
        case _ => analyze(st, pol)
      }
      }()
      go(st)
      var firstTime = false
      newOccs.foreach {
        case tv: TypeVariable =>
          println(s">>>> $tv $newOccs ${coOccurrences.get(pol -> tv)}")
          coOccurrences.get(pol -> tv) match {
            case Some(os) => os.filterInPlace(newOccs) // computes the intersection
            case None => coOccurrences(pol -> tv) = newOccs.clone()
          }
          // println(s">> $pol ${coOccurrences.get(pol -> tv)}")
        case _ => ()
      }
    }
    
    if (pol =/= S(false)) analyze(st, true)
    if (pol =/= S(true)) analyze(st, false)
    
    // println(s"[occs] ${coOccurrences}")
    println(s"[occs] ${coOccurrences.iterator
      .map(occ => s"${printPol(S(occ._1._1))}${occ._1._2} ${occ._2.mkString("{",",","}")}")
      .mkString(" ; ")
    }")
    
    // This will be filled up after the analysis phase, to influence the reconstruction phase:
    val varSubst = MutMap.empty[TypeVariable, Option[TypeVariable]]
    
    // val allVars = st.getVars
    val allVars = st.getVarsPol(pol).keySet
    
    val recVars = MutSet.from(
      // TODOne rm/update logic?
      // allVars.iterator.filter(tv => tv.lowerBounds.nonEmpty || tv.upperBounds.nonEmpty))
      allVars.iterator.filter(tv => tv.isBadlyRecursive(MutMap.empty[TV, Opt[Bool]]).isDefined))
    
    println(s"[vars] ${allVars}")
    println(s"[bounds] ${st.showBounds}")
    println(s"[rec] ${recVars}")
    
    // Simplify away those non-recursive variables that only occur in positive or negative positions:
    allVars.foreach { case v0 => if (!recVars.contains(v0)) {
      (coOccurrences.get(true -> v0), coOccurrences.get(false -> v0)) match {
        case (Some(_), None) | (None, Some(_)) =>
          if (removePolarVars) {
            println(s"[!] $v0")
            varSubst += v0 -> None
          }; ()
        case occ => assert(occ =/= (None, None), s"$v0 has no occurrences...")
      }
    }}
    // Unify equivalent variables based on polar co-occurrence analysis:
    val pols = true :: false :: Nil
    allVars.foreach { case v => if (!varSubst.contains(v)) {
      println(s"[v] $v ${coOccurrences.get(true -> v)} ${coOccurrences.get(false -> v)}")
      pols.foreach { pol =>
        coOccurrences.get(pol -> v).iterator.flatMap(_.iterator).foreach {
          case w: TypeVariable if !(w is v) && !varSubst.contains(w)
              && (recVars.contains(v) === recVars.contains(w))
              && (v.nameHint.nonEmpty || w.nameHint.isEmpty)
              // ^ Don't merge in this direction if that would override a nameHint
            =>
            // Note: We avoid merging rec and non-rec vars, because the non-rec one may not be strictly polar ^
            //       As an example of this, see [test:T1].
            println(s"[w] $w ${coOccurrences.get(pol -> w)}")
            if (coOccurrences.get(pol -> w).forall(_(v))) {
              println(s"[U] $w := $v") // we unify w into v
              varSubst += w -> Some(v)
              // Since w gets unified with v, we need to merge their bounds if they are recursive,
              // and otherwise merge the other co-occurrences of v and w from the other polarity (!pol).
              // For instance,
              //  consider that if we merge v and w in `(v & w) -> v & x -> w -> x`
              //  we get `v -> v & x -> v -> x`
              //  and the old positive co-occ of v, {v,x} should be changed to just {v,x} & {w,v} == {v}!
              // recVars.get(w) match {
              //   case Some(b_w) => // `w` is a recursive variable, so `v` is too (see `recVars.contains` guard above)
              /* 
              if (false && recVars.contains(w)) { // `w` is a recursive variable, so `v` is too (see `recVars.contains` guard above)
                assert(w.lowerBounds.isEmpty || w.upperBounds.isEmpty)
                val (pol, b_w) = (w.lowerBounds, w.upperBounds) match {
                  case (Nil, b) => false -> b
                  case (b, Nil) => true -> b
                  case _ => die
                }
                assert(!coOccurrences.contains((!pol) -> w)) // recursive types have strict polarity
                recVars -= w // w is merged into v, so we forget about it
                val b_v = recVars(v) // `v` is recursive so `recVars(v)` is defined
                // and record the new recursive bound for v:
                // recVars += v -> (() => CompactType.merge(pol)(b_v(), b_w()))
                if (pol) v.lowerBounds :::= b_w
                else v.upperBounds :::= b_w
              } else { // `w` is NOT recursive
              */
                /* 
                val wCoOcss = coOccurrences((!pol) -> w)
                // ^ this must be defined otherwise we'd already have simplified away the non-rec variable
                coOccurrences((!pol) -> v).filterInPlace(t => t === v || wCoOcss(t))
                // ^ `w` is not recursive, so `v` is not either, and the same reasoning applies
                */
                recVars -= w
                v.lowerBounds :::= w.lowerBounds
                v.upperBounds :::= w.upperBounds
                // When removePolarVars is enabled, wCoOcss/vCoOcss may not be defined:
                for {
                  wCoOcss <- coOccurrences.get((!pol) -> w)
                  vCoOcss <- coOccurrences.get((!pol) -> v)
                } vCoOcss.filterInPlace(t => t === v || wCoOcss(t))
              // }
            }; ()
          // case atom: BaseType if !recVars(v) && coOccurrences.get(!pol -> v).exists(_(atom)) =>
          case atom @ (_: BaseType | _: TypeRef)
            if !recVars(v) // can't reduce recursive sandwiches, obviously
            && coOccurrences.get(!pol -> v).exists(_(atom)) =>
          // case atom @ (_: BaseType | _: TypeRef | _: TV) if !recVars(v) && coOccurrences.get(!pol -> v).exists(_(atom)) =>
            println(s"[..] $v ${atom}")
            varSubst += v -> None; ()
          
          // TODO try to preserve name hints?
          case w: TV if !(w is v) && !varSubst.contains(w) && !recVars(v) && coOccurrences.get(!pol -> v).exists(_(w)) =>
            println(s"[..] $v := ${w}")
            varSubst += v -> S(w); ()
          case _ =>
        }
      }
    }}
    println(s"[sub] ${varSubst.map(k => k._1.toString + " -> " + k._2).mkString(", ")}")
    
    
    val renewals = MutMap.empty[TypeVariable, TypeVariable]
    
    def transform(st: SimpleType, pol: Opt[Bool]): SimpleType = st match {
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
      case RecordType(fs) => RecordType(fs.mapValues(_.update(transform(_, pol.map(!_)), transform(_, pol))))(st.prov)
      case TupleType(fs) => TupleType(fs.mapValues(_.update(transform(_, pol.map(!_)), transform(_, pol))))(st.prov)
      case ArrayType(inner) => ArrayType(inner.update(transform(_, pol.map(!_)), transform(_, pol)))(st.prov)
      case FunctionType(l, r) => FunctionType(transform(l, pol.map(!_)), transform(r, pol))(st.prov)
      
      case _: ObjectTag | ExtrType(_) => st
      case tv: TypeVariable =>
        varSubst.get(tv) match {
          case S(S(ty)) => transform(ty, pol)
          case S(N) => pol.fold(die)(pol => ExtrType(pol)(noProv))
          case N =>
            var wasDefined = true
            val res = renewals.getOrElseUpdate(tv, {
              wasDefined = false
              val nv = freshVar(noProv, tv.nameHint)(tv.level)
              println(s"Renewed $tv ~> $nv")
              nv
            })
            if (!wasDefined) {
              res.lowerBounds = tv.lowerBounds.map(transform(_, S(true)))
              res.upperBounds = tv.upperBounds.map(transform(_, S(false)))
            }
            res
        }
      case ty @ ComposedType(true, l, r) => transform(l, pol) | transform(r, pol)
      case ty @ ComposedType(false, l, r) => transform(l, pol) & transform(r, pol)
      case NegType(und) => transform(und, pol.map(!_)).neg()
      case ProxyType(underlying) => transform(underlying, pol)
      case tr @ TypeRef(defn, targs) =>
        // transform(tr.expand, pol) // FIXedME may diverge; and we should try to keep these!
        // TypeRef(defn, targs.map(targ => TypeBounds(transform(targ, false), transform(targ, true))(noProv)))(tr.prov)
        TypeRef(defn, targs.map(transform(_, N)))(tr.prov) // TODO improve with variance analysis
      case wo @ Without(base, names) =>
        if (names.isEmpty) transform(base, pol)
        else Without(transform(base, pol), names)(wo.prov)
      case tb @ TypeBounds(lb, ub) =>
        pol.fold[ST](TypeBounds.mk(transform(lb, S(false)), transform(ub, S(true)), noProv))(pol =>
          if (pol) transform(ub, S(true)) else transform(lb, S(false)))
    }
    transform(st, pol)
    
  }
  
  def reconstructClassTypes(st: SimpleType, pol: Opt[Bool], ctx: Ctx): SimpleType = {
    
    implicit val cache: MutMap[TV, Opt[Bool]] = MutMap.empty
    
    implicit val ctxi: Ctx = ctx
    val renewed = MutMap.empty[TypeVariable, TypeVariable]
    
    def renew(tv: TypeVariable): TypeVariable =
      if (tv.lowerBounds.isEmpty && tv.upperBounds.isEmpty) tv
      else renewed.get(tv) match {
        case S(tv2) => tv2
        case N =>
          val tv2 = freshVar(tv.prov, tv.nameHint)(tv.level)
          renewed += tv -> tv2
          tv2.lowerBounds = tv.lowerBounds.map(go(_, S(true)))
          tv2.upperBounds = tv.upperBounds.map(go(_, S(false)))
          tv2
      }
    
    def go(st: SimpleType, pol: Opt[Bool]): SimpleType =
        trace(s"recons[${printPol(pol)}] $st  (${st.getClass.getSimpleName})") {
        st match {
      case ExtrType(_) => st
      case tv: TypeVariable => renew(tv)
      // case NegType(und) => go(und, !pol).neg()
      // case TypeBounds(lb, ub) => if (pol) go(ub, true) else go(lb, false)
      case NegType(und) => go(und, pol.map(!_)).neg()
      case TypeBounds(lb, ub) =>
        pol.fold[ST](TypeBounds.mk(go(lb, S(false)), go(ub, S(true)), noProv))(pol =>
          if (pol) go(ub, S(true)) else go(lb, S(false)))
      
      // case RecordType(fs) => RecordType(fs.mapValues(_.update(go(_, !pol), go(_, pol))))(st.prov)
      // case TupleType(fs) => TupleType(fs.mapValues(_.update(go(_, !pol), go(_, pol))))(st.prov)
      // case ArrayType(inner) => ArrayType(inner.update(go(_, !pol), go(_, pol)))(st.prov)
      // 
      // case RecordType(fs) => RecordType(fs.mapValues(go(_, pol)))(st.prov)
      // case TupleType(fs) => TupleType(fs.mapValues(go(_, pol)))(st.prov)
      // case ArrayType(inner) => ArrayType(go(inner, pol))(st.prov)
      // 
      case RecordType(fs) => RecordType(fs.mapValues(_.update(go(_, pol.map(!_)), go(_, pol))))(st.prov)
      case TupleType(fs) => TupleType(fs.mapValues(_.update(go(_, pol.map(!_)), go(_, pol))))(st.prov)
      case ArrayType(inner) => ArrayType(inner.update(go(_, pol.map(!_)), go(_, pol)))(st.prov)
      
      // case FunctionType(l, r) => FunctionType(go(l, !pol), go(r, pol))(st.prov)
      case FunctionType(l, r) => FunctionType(go(l, pol.map(!_)), go(r, pol))(st.prov)
      case ProvType(underlying) => ProvType(go(underlying, pol))(st.prov)
      case ProxyType(underlying) => go(underlying, pol)
      case wo @ Without(base, names) =>
        if (pol === S(true)) go(base, pol).withoutPos(names)
        else go(base, pol).without(names)
      case tr @ TypeRef(defn, targs) => tr.copy(targs = targs.map { targ =>
          // TypeBounds.mk(go(targ, false), go(targ, true), targ.prov)
          go(targ, N)
        })(tr.prov)
      case ty @ (ComposedType(_, _, _) | _: ObjectTag) =>
        
        def helper(dnf: DNF, pol: Opt[Bool]): ST = {
        println(s"DNF: $dnf")
        // val dnf @ DNF(cs) = DNF.mk(ty, pol)(ctx, preserveTypeRefs = true)
        val cs = dnf.cs
        cs.sorted.map { c =>
          c.copy(vars = c.vars.map(renew), nvars = c.nvars.map(renew)).toTypeWith(_ match {
            
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
                  val td = ctx.tyDefs(clsNme)
                  val typeRef = TypeRef(td.nme, td.tparams.map { tp =>
                    val fieldTagNme = tparamField(TypeName(clsNme), tp)
                    // rcd.fields.iterator.filter(_._1 === fieldTagNme).map {
                    //   case (_, FunctionType(lb, ub)) =>
                    //     TypeBounds.mk(go(lb, false), go(ub, true))
                    // }.foldLeft(TypeBounds(BotType, TopType)(noProv): ST)(_ & _)
                    
                    rcd.fields.iterator.filter(_._1 === fieldTagNme).collectFirst {
                      case (_, FieldType(lb, ub)) if lb.exists(ub >:< _) => ub
                      case (_, FieldType(lb, ub)) =>
                        TypeBounds.mk(go(lb.getOrElse(BotType), S(false)), go(ub, S(true)))
                    }.getOrElse(TypeBounds(BotType, TopType)(noProv))
                    
                    rcd.fields.iterator.filter(_._1 === fieldTagNme).foldLeft((BotType: ST, TopType: ST)) {
                      // case ((acc_lb, acc_ub), (_, FunctionType(lb, ub))) => (acc_lb | lb, acc_ub & ub)
                      // // case ((acc_lb, acc_ub), (_, _)) => die
                      // case ((acc_lb, acc_ub), (_, ty)) => lastWords(s"$fieldTagNme = $ty")
                      
                      // case ((acc_lb, acc_ub), FieldType(lb, ub)) if lb.exists(ub >:< _) => ub
                      case ((acc_lb, acc_ub), (_, FieldType(lb, ub))) =>
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
                    else Without(typeRef, removedFields)(noProv)
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
                    case S(wt @ Without(b, ns)) => S(Without(go(b, pol), ns)(wt.prov)) -> nFields
                    case N => N -> nFields
                  }
                  LhsRefined(res, tts, rcd.copy(nfs)(rcd.prov).sorted, trs2).toType(sort = true)
              }
            case LhsTop => TopType
          }, {
            case RhsBot => BotType
            case RhsField(n, t) => RecordType(n -> t.update(go(_, pol.map(!_)), go(_, pol)) :: Nil)(noProv)
            case RhsBases(ots, rest) =>
              // Note: could recosntruct class tags for these, but it would be pretty verbose,
              //    as in showing `T & ~C[?] & ~D[?, ?]` instead of just `T & ~c & ~d`
              // ots.map { case t @ (_: ClassTag | _: TraitTag) => ... }
              val r = rest match {
                case v @ S(R(RhsField(n, t))) => RhsField(n, t.update(go(_, pol.map(!_)), go(_, pol))).toType(sort = true)
                case v @ S(L(bty)) => go(bty, pol)
                case N => BotType
              }
              ots.sorted.foldLeft(r)(_ | _)
          }, sort = true)
        }.foldLeft(BotType: ST)(_ | _) |> factorize
        }
        mkDNF(ty, pol)(ctx, ptr = true, etf = false, cache) match {
        // mkDNF(ty, pol)(ctx, ptr = false, etf = false, cache) match {
          case R(dnf) => helper(dnf, pol)
          case L((dnf1, dnf2)) => TypeBounds.mk(helper(dnf1, S(false)), helper(dnf2, S(true)))
        }
        
    }
    }(r => s"=> $r")
    
    go(st, pol)
    
  }
    
}
