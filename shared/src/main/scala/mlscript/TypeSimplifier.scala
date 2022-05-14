package mlscript

import scala.collection.mutable.{Map => MutMap, Set => MutSet, LinkedHashMap, LinkedHashSet}
import scala.collection.immutable.{SortedMap, SortedSet}
import scala.util.chaining._
import mlscript.utils._, shorthands._

trait TypeSimplifier { self: Typer =>
  
  
  /* 
  // TODO rm this?! not sure still useful
  // TODO inline logic
  private def mkDNF(ty: SimpleType, pol: Opt[Bool])(implicit ctx: Ctx, ptr: PreserveTypeRefs, etf: ExpandTupleFields, cache: MutMap[TV, Opt[Bool]]): Either[(DNF, DNF), DNF] = {
    // implicit val preserveTypeRefs: Bool = true
    // println(s"mk[${printPol(pol)}] ${ty}")
    pol match {
      case S(true) => R(DNF.mk(ty, true))
      case S(false) => R(DNF.mk(ty, false))
      case N =>
        // TODO less inefficient! don't recompute
        // val dnf1 = DNF.mk(ty, true)
        val dnf1 = DNF.mk(ty, false)
        // if (dnf1.cs.exists(_.vars.nonEmpty))
        // val dnf2 = DNF.mk(ty, false)
        val dnf2 = DNF.mk(ty, true)
        // // if (dnf1.cs.forall(_.vars.isEmpty) && dnf1 === dnf2) R(dnf1)
        // // println(s"vars ${dnf1.cs.map(_.vars)}")
        // // if (dnf1.cs.forall(_.vars.forall(_.isBadlyRecursive =/= S(false))) && dnf1 === dnf2) R(dnf1)
        // if (dnf1 === dnf2) R(dnf1)
        // else 
        L(dnf1 -> dnf2)
    }
  }
  */
  
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
    
    // def process(ty: ST, parents: Set[TV]): ST = // TODO mk parents an option?
    //     // trace(s"process($ty)") {
    //     ty match {
    //   case tv: TypeVariable if parents(tv) => freshVar(noProv)
    //   case tv: TypeVariable =>
    //     var isNew = false
    //     val nv = renewed.getOrElseUpdate(tv, {isNew = true; renew(tv)})
    //     // renewed.getOrElseUpdate(tv,
    //     //   freshVar(noProv, tv.nameHint)(tv.level) tap { fv => println(s"Renewed $tv ~> $fv") })
    //     // val nv = renew(v)
    //     if (isNew) {
    //       if (pols(tv).forall(_ === true)) nv.lowerBounds = tv.lowerBounds.map(process(_, Set.single(tv)))
    //       if (pols(tv).forall(_ === false)) nv.upperBounds = tv.upperBounds.map(process(_, Set.single(tv)))//.tap(b=>println(s"${b.map(_.getClass)}"))
    //     }
    //     // println(tv, nv, nv.lowerBounds, nv.upperBounds)
    //     nv
    //   // case ComposedType(_, l, r) => ty.map(process(_, parents))
    //   case _: ProxyType | _: ComposedType | _: NegType => ty.map(process(_, parents))
    //   case _ => ty.map(process(_, Set.empty))
    // }
    // // }(r => s"= $r")
    def process(ty: ST, parent: Opt[Bool -> TV]): ST =
        // trace(s"process($ty)") {
        ty match {
      // case tv: TypeVariable if parent.exists(_._2 === tv) => if parent.get.
      case tv: TypeVariable =>
        parent.filter(_._2 === tv).foreach(p => return ExtrType(p._1)(noProv))
        var isNew = false
        val nv = renewed.getOrElseUpdate(tv, {isNew = true; renew(tv)})
        // renewed.getOrElseUpdate(tv,
        //   freshVar(noProv, tv.nameHint)(tv.level) tap { fv => println(s"Renewed $tv ~> $fv") })
        // val nv = renew(v)
        if (isNew) {
          
          // if (pols(tv).forall(_ === true)) nv.lowerBounds = tv.lowerBounds.map(process(_, S(true -> tv)))
          // if (pols(tv).forall(_ === false)) nv.upperBounds = tv.upperBounds.map(process(_, S(false -> tv)))
          // //.tap(b=>println(s"${b.map(_.getClass)}"))
          
          if (pols(tv).forall(_ === true)) nv.lowerBounds =
            tv.lowerBounds.iterator.map(process(_, S(true -> tv))).reduceOption(_ | _).filterNot(_.isBot).toList
          if (pols(tv).forall(_ === false)) nv.upperBounds =
            tv.upperBounds.iterator.map(process(_, S(false -> tv))).reduceOption(_ & _).filterNot(_.isTop).toList
          
        }
        // println(tv, nv, nv.lowerBounds, nv.upperBounds)
        nv
      // case ComposedType(_, l, r) => ty.map(process(_, parents))
      case ComposedType(true, l, r) => process(l, parent) | process(r, parent)
      case ComposedType(false, l, r) => process(l, parent) & process(r, parent)
      // case _: ProxyType | _: ComposedType | _: NegType => ty.map(process(_, parent))
      case NegType(ty) => process(ty, parent.map(_.mapFirst(!_))).neg(ty.prov)
      
      // case ProvType(ty) => ProvType(process(ty, parent))(ty.prov)
      case ProvType(ty) => process(ty, parent)
      
      case _ => ty.map(process(_, N))
    }
    // }(r => s"= $r")
    
    process(ty, N)
  }
  
  
  
  
  
  
  
  
  
  def coalesceTypes_!(st: SimpleType, approximateRecTypes: Bool, pol: Opt[Bool] = S(true))(implicit ctx: Ctx): SimpleType = {
    
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
    
    // def process(pol: Opt[Bool], st: ST, parent: Opt[TV]): ST =
    def process(pol: Opt[Bool], st: ST): ST =
    // st.unwrapProvs match {
    //   case tv: TV =>
    //     processed.setAndIfUnset(tv) {
    //       tv.lowerBounds = tv.lowerBounds.map(process(S(true), _, S(tv)))
    //       tv.upperBounds = tv.upperBounds.map(process(S(false), _, S(tv)))
    //     }
    //     tv
    //   case _ =>
    //     st
    // }
    trace(s"coal[${printPol(pol)}] $st") {
      
      pol match {
        case N =>
          st.mapPol(pol, smart = true)(process)
          
          // * Doesn't seem to change anything:
          /* 
          val dnf1 = DNF.mk(st, false)(ctx, ptr = true, etf = false)
          println(s"dnf1 = $dnf1")
          val dnf2 = DNF.mk(st, true)(ctx, ptr = true, etf = false)
          println(s"dnf2 = $dnf2")
          if (dnf1 === dnf2)
            dnf1.toType(sort = true).mapPol(pol)(process)
          else TypeBounds.mk(
            dnf1.toType(sort = true).mapPol(pol)(process),
            dnf2.toType(sort = true).mapPol(pol)(process),
            noProv
          )
          */
        
        // /* 
        case S(p) =>
          
          val dnf = DNF.mk(st, p)(ctx, ptr = true, etf = false)
          println(s"dnf = $dnf")
          
          dnf.cs.foreach { c =>
            (c.vars.iterator ++ c.nvars).foreach { tv =>
              processed.setAndIfUnset(tv) {
                tv.lowerBounds = tv.lowerBounds.map(process(S(true), _))
                tv.upperBounds = tv.upperBounds.map(process(S(false), _))
              }
            }
          }
          
          // dnf.toType(sort = true)
          
          // dnf.toType(sort = true).mapPol(pol, smart = true)(process)
          val newTy = dnf.toType(sort = true)
          newTy.mapPol(pol, smart = true)((pol, ty) =>
            // if (ty === st) ty // Sometimes the DNF of T will include T itself, such as when T is a class type ref
            if (ty === st) ty.mapPol(pol, smart = true)(process) // Sometimes the DNF of T will include T itself, such as when T is a class type ref
            else process(pol, ty))
          
        // */
        /* 
        case S(p) =>
          
          var dnf = DNF.mk(st, p)(ctx, ptr = true, etf = false)
          println(s"dnf = $dnf")
          
          // var vars = 
          
          dnf.cs.foreach { c =>
            (c.vars.iterator ++ c.nvars).foreach { tv =>
            // c.nvars.foreach { tv =>
              processed.setAndIfUnset(tv) {
                println(s"Processing $tv")
                tv.lowerBounds = tv.lowerBounds.map(process(S(true), _))
                tv.upperBounds = tv.upperBounds.map(process(S(false), _))
              }
            }
          }
          
          implicit val etf: ExpandTupleFields = false
          def rec(dnf: DNF, done: Set[TV], pol: Bool, parents: Set[TV]): DNF = dnf.cs.iterator.map { c =>
            // val vs = c.vars.filterNot(done)
            // val vs = c.vars.filterNot(v => recursiveVars.contains(v) || v.isRecursive === S(false) && {
            //   recursiveVars += v
            //   val nv = renew(v)
            //   nv.lowerBounds = v.lowerBounds.map(goDeep(_, S(true)))
            //   nv.upperBounds = v.upperBounds.map(goDeep(_, S(false)))
            //   true
            // } || done(v))
            // val vs = c.vars.filterNot(parents).filterNot(tv => recVars.contains(tv) || allVarPols(tv).isEmpty && {
            val vs = c.vars.filterNot(parents).filterNot(tv => recVars.contains(tv) && {
              // println(s"$tv is badly recursive...")
              println(s"let's not coalesce $tv...")
              // // recursiveVars += tv
              // // val nv = renew(tv)
              // // val newParents = parents + tv
              // // nv.lowerBounds = tv.lowerBounds.map(goDeep(_, S(true), newParents))
              // // nv.upperBounds = tv.upperBounds.map(goDeep(_, S(false), newParents))
              // preserveBounds(tv, parents)
              /* 
              // TODO dedup
              processed.setAndIfUnset(tv) {
                tv.lowerBounds = tv.lowerBounds.map(process(S(true), _))
                tv.upperBounds = tv.upperBounds.map(process(S(false), _))
              }
              */
              true
            // } || done(tv))
            } || done(tv) && {println(s"Done $tv"); true})
            vs.iterator.map { tv =>
            // vs.iterator.filter(_.isRecursive =/= S(false)).map { tv =>
              // println(s"Consider $tv ${tv.lowerBounds} ${tv.upperBounds}")
              val b =
                if (pol) tv.lowerBounds.foldLeft(tv:ST)(_ | _)
                else tv.upperBounds.foldLeft(tv:ST)(_ & _)
              // val b =
              //   if (pol) tv.lowerBounds.foldLeft(BotType:ST)(_ | _)
              //   else tv.upperBounds.foldLeft(TopType:ST)(_ & _)
              // println(s"b $b")
              // val bd = rec(DNF.mk(b, pol)(ctx, ptr = true), done + tv, pol, parents + tv)
              // val bd = rec(DNF.mk(b, pol)(ctx, ptr = true, etf = false), done + tv, pol, parents ++ vs)
              val bd = rec(DNF.mk(b, pol)(ctx, ptr = true), done + tv, pol, parents ++ vs)
              // println(s"bd $bd")
              bd
            }
            .foldLeft(DNF(c.copy(vars = c.vars.filterNot(vs))::Nil))(_ & _)
          }.foldLeft(DNF.extr(false))(_ | _)
          
          dnf = rec(dnf, Set.empty, p, Set.empty)
          println(s"dnf := $dnf")
          
          // TODO coalesce neg vars?
          
          // dnf.cs.foreach { c =>
          //   // (c.vars.iterator ++ c.nvars).foreach { tv =>
          //   c.nvars.foreach { tv =>
          //     processed.setAndIfUnset(tv) {
          //       tv.lowerBounds = tv.lowerBounds.map(process(S(true), _))
          //       tv.upperBounds = tv.upperBounds.map(process(S(false), _))
          //     }
          //   }
          // }
          
          dnf.toType(sort = true)
          // dnf.toType(sort = true).mapPol(pol)(process)
        */
      }
      
    }(r => s"~> $r")
    process(pol, st)
  }
  
  
  
  
  
  
  
  
  def canonicalizeType(ty: SimpleType, pol: Opt[Bool] = S(true))(implicit ctx: Ctx): SimpleType = {
    // type PolarType = (DNF, Bool)
    // type PolarType = DNF
    type PolarType = (DNF, Opt[Bool])
    
    import Set.{empty => semp}
    
    // val r = removeIrrelevantBounds(ty, pol)
    // println(r)
    // println(r.showBounds)
    
    val recursive = MutMap.empty[PolarType, TypeVariable]
    
    // TODO rename (no longer just rec vars)
    val recursiveVars = MutSet.empty[TypeVariable] // For rec nonpolar vars
    
    val renewed = MutMap.empty[TypeVariable, TypeVariable]
    
    implicit val cache: MutMap[TV, Opt[Bool]] = MutMap.empty
    
    val allVars = ty.getVars
    def renew(tv: TypeVariable): TypeVariable =
      renewed.getOrElseUpdate(tv,
        freshVar(noProv, tv.nameHint)(tv.level) tap { fv => println(s"Renewed $tv ~> $fv") })
    
    // def preserveBoudns(tv: TV, parents: Set[TV])(implicit inProcess: Set[PolarType]): TV = {
    // def preserveBoudns(tv: TV, parents: Set[TV], inProcess: Set[PolarType] = Set.empty): TV = {
    def preserveBounds(tv: TV, parents: Set[TV]): TV = {
      recursiveVars += tv
      val nv = renew(tv)
      // val newParents = parents + tv
      val newParents = Set.single(tv)
      // nv.lowerBounds = tv.lowerBounds.map(goDeep(_, S(true), newParents)(Set.empty))
      // nv.upperBounds = tv.upperBounds.map(goDeep(_, S(false), newParents)(Set.empty))
      // implicit val inProcess: Set[PolarType] = semp
      nv.lowerBounds = tv.lowerBounds.reduceOption(_ | _)
        .map(goDeep(_, S(true), newParents)(Set.empty)).filterNot(_ === BotType).toList
      nv.upperBounds = tv.upperBounds.reduceOption(_ & _)
        .map(goDeep(_, S(false), newParents)(Set.empty)).filterNot(_ === TopType).toList
      nv
    }
    
    def goDeep(ty: SimpleType, pol: Opt[Bool], parents: Set[TV])(implicit inProcess: Set[PolarType]): SimpleType = ty.unwrapProvs match {
        case v: TV if parents(v) =>
          ??? // uh? // TODO rm parents?
          if (pol.getOrElse(die)) // doesn't really make sense to have a parent in invariant pos
            BotType else TopType
        case tv: TV if recursiveVars.contains(tv) => renew(tv)
        case v: TV if pol.isEmpty =>
          println(s"$v is in a bad place...")
          // recursiveVars += v
          // val nv = renew(v)
          // val newParents = parents + v
          // nv.lowerBounds = v.lowerBounds.map(goDeep(_, S(true), newParents))
          // nv.upperBounds = v.upperBounds.map(goDeep(_, S(false), newParents))
          // nv
          preserveBounds(v, parents)
        case _ =>
      // go1(go0(ty, pol), pol)
      go0(ty, pol, parents) match {
        case R(dnf) => go1(dnf, pol, parents)
        case L((dnf1, dnf2)) =>
          TypeBounds.mk(go1(dnf1, S(false), parents), go1(dnf2, S(true), parents), noProv)
      }
    }
    
    // Turn the outermost layer of a SimpleType into a DNF, leaving type variables untransformed
    def go0(ty: SimpleType, pol: Opt[Bool], parents: Set[TV])(implicit inProcess: Set[PolarType]): Either[(DNF, DNF), DNF] = 
    trace(s"ty[${printPol(pol)}] $ty") {
      
      implicit val etf: ExpandTupleFields = false
      
      // TODO should we also coalesce nvars? is it bad if we don't? -> probably, yes...
      def rec(dnf: DNF, done: Set[TV], pol: Bool, parents: Set[TV]): DNF = dnf.cs.iterator.map { c =>
        // val vs = c.vars.filterNot(done)
        // val vs = c.vars.filterNot(v => recursiveVars.contains(v) || v.isRecursive === S(false) && {
        //   recursiveVars += v
        //   val nv = renew(v)
        //   nv.lowerBounds = v.lowerBounds.map(goDeep(_, S(true)))
        //   nv.upperBounds = v.upperBounds.map(goDeep(_, S(false)))
        //   true
        // } || done(v))
        val vs = c.vars.filterNot(parents).filterNot(v => recursiveVars.contains(v) || v.isBadlyRecursive === S(false) && {
          println(s"$v is badly recursive...")
          // recursiveVars += v
          // val nv = renew(v)
          // val newParents = parents + v
          // nv.lowerBounds = v.lowerBounds.map(goDeep(_, S(true), newParents))
          // nv.upperBounds = v.upperBounds.map(goDeep(_, S(false), newParents))
          preserveBounds(v, parents)
          true
        // } || done(v))
        } || done(v) && {println(s"Done $v"); true})
        vs.iterator.map { tv =>
        // vs.iterator.filter(_.isRecursive =/= S(false)).map { tv =>
          // println(s"Consider $tv ${tv.lowerBounds} ${tv.upperBounds}")
          val b =
            if (pol) tv.lowerBounds.foldLeft(tv:ST)(_ | _)
            else tv.upperBounds.foldLeft(tv:ST)(_ & _)
          // println(s"b $b")
          // val bd = rec(DNF.mk(b, pol)(ctx, ptr = true), done + tv, pol, parents + tv)
          val bd = rec(DNF.mk(b, pol)(ctx, ptr = true), done + tv, pol, parents ++ vs)
          // println(s"bd $bd")
          bd
        }
        .foldLeft(DNF(c.copy(vars = c.vars.filterNot(vs))::Nil))(_ & _)
      }.foldLeft(DNF.extr(false))(_ | _)
      
      /* 
      if (pol.isEmpty && ty.isInstanceOf[TV]) {
        val v = ty.asInstanceOf[TV]
        ???
        println(s"$v is in a bad place...")
        recursiveVars += v
        val nv = renew(v)
        nv.lowerBounds = v.lowerBounds.map(goDeep(_, S(true)))
        nv.upperBounds = v.upperBounds.map(goDeep(_, S(false)))
        R(DNF.mk(nv, true))
      }
      else
      */
      
      /* 
      // rec(DNF.mk(ty, pol)(ctx), Set.empty)
      mkDNF(ty, pol)(ctx, ptr = true, etf = false, cache) match {
      // mkDNF(ty, pol)(ctx, ptr = true, etf = false, cache) match {
        case R(dnf) =>
          // println(dnf.cs.map(_.vars.isEmpty))
          // pol.fold(R(dnf))(p => R(rec(dnf, Set.empty, p)))
          
          // pol.fold({
          //   // R(dnf)
          //   val a = rec(dnf, Set.empty, false, parents)
          //   val b = rec(dnf, Set.empty, true, parents) // TODO rm for perf
          //   // assert(a === b, a -> b)
          //   // if (a === b) ???
          //   if (a === b)
          //   R(a)
          //   else L(a -> b)
          //   // else L(b -> a)
          // })(p => R(rec(dnf, semp, p, parents)))
          
          R(rec(dnf, semp, pol.get, parents))
          
          // pol.fold(R(dnf))(p => {
          //   val a = rec(dnf, Set.empty, p)
          //   val b = rec(dnf, Set.empty, !p)
          //   R(a)
          // })
        case L((dnf1, dnf2)) => L(rec(dnf1, semp, false, parents), rec(dnf2, semp, true, parents))
      }
      */
      
      pol match {
        // case S(true) => R(DNF.mk(ty, true))
        // case S(false) => R(DNF.mk(ty, false))
        case S(p) => R(rec(DNF.mk(ty, p)(ctx, ptr = true, etf = false), semp, p, parents))
        case N =>
          val dnf1 = rec(DNF.mk(ty, false)(ctx, ptr = true, etf = false), semp, false, parents)
          val dnf2 = rec(DNF.mk(ty, true)(ctx, ptr = true, etf = false), semp, true, parents)
          if (dnf1 === dnf2) R(dnf1)
          else 
          L(dnf1 -> dnf2)
      }
      
    }(r => s"-> $r")
    
    // Merge the bounds of all type variables of the given DNF, and traverse the result
    def go1(ty: DNF, pol: Opt[Bool], parents: Set[TV])
        (implicit inProcess: Set[PolarType]): SimpleType = trace(s"DNF[${printPol(pol)}] $ty") {
      if (ty.isBot) ty.toType(sort = true) else {
        val pty = ty -> pol
        // val pty = ty
        if (inProcess.contains(pty))
          recursive.getOrElseUpdate(pty,
            freshVar(noProv)(ty.level) tap { fv => println(s"Fresh rec $pty ~> $fv") })
        else {
          (inProcess + pty) pipe { implicit inProcess =>
            def processField(f: FieldType): FieldType = f match {
              case fty @ FieldType(S(lb), ub) if lb === ub =>
                val res = goDeep(ub, N, semp)
                FieldType(S(res), res)(fty.prov)
              case fty @ FieldType(lb, ub) =>
                FieldType(lb.map(goDeep(_, pol.map(!_), semp)), goDeep(ub, pol, semp))(fty.prov)
            }
            val res = DNF(ty.cs.map { case Conjunct(lnf, vars, rnf, nvars) =>
              def adapt(pol: Opt[Bool])(l: LhsNf): LhsNf = l match {
                case LhsRefined(b, ts, RecordType(fs), trs) => LhsRefined(
                  b.map {
                    case ft @ FunctionType(l, r) =>
                      FunctionType(goDeep(l, pol.map(!_), semp), goDeep(r, pol, semp))(noProv)
                    // case wo @ Without(b, ns) if ns.isEmpty =>
                    // case wo @ Without(tr @ TypeRef(defn, targs), ns) if ns.isEmpty =>
                    //   // FIXME hacky!!
                    //   // FIXedME recurse in type args!!! not sound otherwise
                    //   // TODO actually make polarity optional and recurse with None
                    //   Without(TypeRef(defn, targs.map(targ =>
                    //     TypeBounds(goDeep(targ, false), goDeep(targ, true))(noProv)))(tr.prov), ns)(wo.prov)
                    case wo @ Without(b, ns) =>
                      Without(goDeep(b, pol, parents), ns)(noProv)
                    case ft @ TupleType(fs) =>
                      // TupleType(fs.mapValues(_.update(goDeep(_, pol.map(!_), semp), goDeep(_, pol, semp))))(noProv)
                      // TupleType(fs.mapValues {
                      //   case fty @ FieldType(S(lb), ub) if lb === ub =>
                      //     val res = goDeep(ub, N, semp)
                      //     FieldType(S(res), res)(fty.prov)
                      //   case f => f.update(goDeep(_, pol.map(!_), semp), goDeep(_, pol, semp))
                      // })(noProv)
                      TupleType(fs.mapValues(processField))(noProv)
                    // case ar @ ArrayType(fty @ FieldType(S(lb), ub)) if lb === ub =>
                    //   val res = goDeep(ub, N, semp)
                    //   ArrayType(FieldType(S(res), res)(fty.prov))(noProv)
                    // case ar @ ArrayType(inner) =>
                    //   ArrayType(inner.update(goDeep(_, pol.map(!_), semp), goDeep(_, pol, semp)))(noProv)
                    case ar @ ArrayType(inner) =>
                      ArrayType(processField(inner))(noProv)
                    case pt: ClassTag => pt
                  },
                  ts,
                  // RecordType(fs.map(f => f._1 -> goDeep(f._2, pol)))(noProv)
                  // RecordType(fs.map {
                  //   // case (nme, ty) if nme.name.isCapitalized && nme.name.contains('#') =>
                  //   //   ty match {
                  //   //     // case FunctionType(lb, ub) =>
                  //   //     //   nme -> FunctionType(goDeep(lb, pol.map(!_)), goDeep(ub, pol))(ty.prov)
                  //   //     // case _ => lastWords(s"$nme: $ty")
                  //   //     case FieldType(lb, ub) =>
                  //   //       nme -> FieldType(lb.map(goDeep(_, pol.map(!_))), goDeep(ub, pol))(ty.prov)
                  //   //   }
                  //   // case (nme, ty) => nme -> goDeep(ty, pol)
                  //   case (nme, fty @ FieldType(S(lb), ub)) if lb === ub =>
                  //     val res = goDeep(ub, N, semp)
                  //     nme -> FieldType(S(res), res)(fty.prov)
                  //   case (nme, fty @ FieldType(lb, ub)) =>
                  //     nme -> FieldType(lb.map(goDeep(_, pol.map(!_), semp)), goDeep(ub, pol, semp))(fty.prov)
                  // })(noProv),
                  RecordType(fs.mapValues(processField))(noProv),
                  trs.map {
                    case (d, tr @ TypeRef(defn, targs)) =>
                      // TODO actually make polarity optional and recurse with None
                      // d -> TypeRef(defn, targs.map(targ =>
                      //   TypeBounds.mk(goDeep(targ, S(false)), goDeep(targ, S(true)), noProv)))(tr.prov)
                      d -> TypeRef(defn, targs.map(targ =>
                        goDeep(targ, N, semp)))(tr.prov)
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
                // case RhsField(name, ty) => RhsField(name, ty.update(goDeep(_, pol.map(!_), semp), goDeep(_, pol, semp)))
                case RhsField(name, ty) => RhsField(name, processField(ty))
                case RhsBases(prims, bf) =>
                  // TODO refactor to handle goDeep returning something else...
                  RhsBases(prims, bf match {
                    case N => N
                    case S(L(bt)) => goDeep(bt, pol, parents) match {
                      case bt: MiscBaseType => S(L(bt))
                      case ExtrType(true) => N
                      case _ => ???
                    }
                    case S(R(r)) =>
                      // S(R(RhsField(r.name, r.ty.update(goDeep(_, pol.map(!_), semp), goDeep(_, pol, semp)))))
                      S(R(RhsField(r.name, processField(r.ty))))
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
    
    goDeep(ty, pol, semp)(semp)
    
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
    /* 
    def analyze0(pol: Bool, st: SimpleType): Unit = trace(s"analyze0[${printPol(S(pol))}] $st") { st match {
      case tv: TV =>
        // analyzed0.setAnd(tv -> pol) { occNums(pol -> tv) += 1 } {
        occNums(pol -> tv) += 1
        analyzed0.setAndIfUnset(tv -> pol) {
          // tv.lowerBounds.foreach(analyze0(true, _))
          // tv.upperBounds.foreach(analyze0(false, _))
          if (pol) tv.lowerBounds.foreach(analyze0(true, _))
          else tv.upperBounds.foreach(analyze0(false, _))
        }
      case _ =>
        st.childrenPol(S(pol)).foreach {
          case (S(pol), st) => analyze0(pol, st)
          case (N, st) => analyze0(true, st); analyze0(false, st)
        }
    }
    }()
    // analyze0(pol, st)
    if (pol =/= S(false)) analyze0(true, st)
    if (pol =/= S(true)) analyze0(false, st)
    */
    def analyze0(pol: Opt[Bool], st: SimpleType): Unit = trace(s"analyze0[${printPol(pol)}] $st") { st match {
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
          tv.lowerBounds.foreach(analyze0(S(true), _))
        }
        if (pol =/= S(true)) analyzed0.setAndIfUnset(tv -> false) {
          tv.upperBounds.foreach(analyze0(S(false), _))
        }
      case _ =>
        st.childrenPol(pol).foreach {
          // case (S(pol), st) => analyze0(pol, st)
          // case (N, st) => analyze0(true, st); analyze0(false, st)
          case (pol, st) => analyze0(pol, st)
        }
    }
    }()
    analyze0(pol, st)
    // if (pol =/= S(false)) analyze0(true, st)
    // if (pol =/= S(true)) analyze0(false, st)
    
    println(s"[inv] ${occursInvariantly.iterator.mkString(", ")}")
    println(s"[nums] ${occNums.iterator
      .map(occ => s"${printPol(S(occ._1._1))}${occ._1._2} ${occ._2}")
      .mkString(" ; ")
    }")
    
    
    // === TODO RM ===
    // val otherEdges = st.getVars.iterator.foreach { tv1 =>
    //   tv1.lowerBounds.foreach {
    //     case tv2: TV => tv1 -> L(tv2)
    //     case _ =>
    //   }
    //   tv1.upperBounds.foreach {
    //     case tv2: TV => tv1 -> R(tv2)
    //     case _ =>
    //   }
    // }
    import collection.mutable
    // val otherLBs, otherUBs = mutable.Map.empty[TV, mutable.Buffer[TV]]
    val otherLBs, otherUBs = mutable.Map.empty[TV, mutable.Buffer[TV]].withDefault(_ => mutable.Buffer.empty)
    /* 
    st.getVars.iterator.foreach { tv1 =>
      tv1.lowerBounds.foreach {
        // case tv2: TV => otherLBs.getOrElseUpdate(tv2, mutable.Buffer.empty) += tv1
        case tv2: TV => otherLBs(tv2) += tv1
        case _ =>
      }
      tv1.upperBounds.foreach {
        // case tv2: TV => otherUBs.getOrElseUpdate(tv2, mutable.Buffer.empty) += tv1
        case tv2: TV => otherUBs(tv2) += tv1
        case _ =>
      }
    }
    */
    
    // def analyze(st: SimpleType, pol: Bool): Unit = st match {
    //   case RecordType(fs) => fs.foreach { f => f._2.lb.foreach(analyze(_, !pol)); analyze(f._2.ub, pol) }
    //   case TupleType(fs) => fs.foreach { f => f._2.lb.foreach(analyze(_, !pol)); analyze(f._2.ub, pol) }
    //   case ArrayType(inner) =>
    //     inner.lb.foreach(analyze(_, !pol))
    //     analyze(inner.ub, pol)
    def analyze(st: SimpleType, pol: Bool): Unit =
      // analyzeImpl(st.unwrapProxies, pol)
      analyzeImpl(st.unwrapProvs, pol)
    def analyzeImpl(st: SimpleType, pol: Bool): Unit =
        trace(s"analyze[${printPol(S(pol))}] $st") {
        // trace(s"analyze[${printPol(S(pol))}] $st       ${analyzed2}") {
        // trace(s"analyze[${printPol(S(pol))}] $st       ${coOccurrences.filter(_._1._2.nameHint.contains("head"))}") {
          analyzed2.setAndIfUnset(st -> pol) {
          // analyzed2.setAnd(st -> pol) {
          //   st match {
          //     case tv: TV => occNums(pol -> tv) += 1
          //     case _ =>
          //   }
          // } {
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
        // analyzed.setAndIfUnset(tv -> pol) { process(tv, pol) }
        // analyzed.setAnd(tv -> pol) { occNums(pol -> tv) += 1 } { process(tv, pol) }
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
    }
    }
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
      def go(st: SimpleType): Unit = goImpl(st.unwrapProvs)
      def goImpl(st: SimpleType): Unit =
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
          // occNums(pol -> tv) += 1
          // if (!analyzed.contains(tv -> pol)) 
          // occNums(pol -> tv) += 1
          if (!newOccs.contains(tv)) {
            // analyzed(tv -> pol) = true
            newOccs += st
            // processBounds(tv, pol)
            // (if (pol) tv.lowerBounds else tv.upperBounds).foreach(process(_, pol, newOccs))
            // (if (pol) tv.lowerBounds else tv.upperBounds).foreach(go)
            (if (pol) tv.lowerBounds.iterator ++ otherLBs(tv) else tv.upperBounds.iterator ++ otherUBs(tv)).foreach(go)
            // analyze(tv, pol)
          }
        case _ => analyze(st, pol)
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
      if (!occNums.contains(!pol -> tv)) {
        if (num === 1) {
          println(s"[1] $tv")
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
              // && (recVars.contains(v) === recVars.contains(w))
              // ^ Note: We avoid merging rec and non-rec vars, because the non-rec one may not be strictly polar
              //       As an example of this, see [test:T1].
              && (v.nameHint.nonEmpty || w.nameHint.isEmpty)
              // ^ Don't merge in this direction if that would override a nameHint
            =>
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
                if (pol) v.lowerBounds ::
                 b_w
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
                
              // }
            }; ()
          // case atom: BaseType if !recVars(v) && coOccurrences.get(!pol -> v).exists(_(atom)) =>
          case atom @ (_: BaseType | _: TypeRef)
            if !recVars(v) // can't reduce recursive sandwiches, obviously
            && coOccurrences.get(!pol -> v).exists(_(atom)) =>
          // case atom @ (_: BaseType | _: TypeRef | _: TV) if !recVars(v) && coOccurrences.get(!pol -> v).exists(_(atom)) =>
            println(s"[..] $v ${atom}")
            varSubst += v -> None; ()
          
          // TODO-simplif rm: // TODO try to preserve name hints?
          case w: TV if !(w is v) && !varSubst.contains(w) && !recVars(v) && coOccurrences.get(!pol -> v).exists(_(w)) =>
            println(s"[..] $v := ${w}")
            varSubst += v -> S(w); ()
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
            TypeBounds(mergeTransform(true, tv.lowerBounds, parent), mergeTransform(false, tv.upperBounds, parent))(noProv): ST
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
                val allBounds = tv.lowerBounds ++ tv.upperBounds
                // assert(allBounds.size === tv.lowerBounds.size)
                assert(tv.lowerBounds.isEmpty || tv.upperBounds.isEmpty)
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
        else Without(transform(base, pol, N), names)(wo.prov)
      case tb @ TypeBounds(lb, ub) =>
        pol.fold[ST](TypeBounds.mk(transform(lb, S(false), parent), transform(ub, S(true), parent), noProv))(pol =>
          if (pol) transform(ub, S(true), parent) else transform(lb, S(false), parent))
    }
    }(r => s"~> $r")
    transform(st, pol, N)
    
  }
  def merge(pol: Bool, ts: Ls[ST]): ST =
    if (pol) ts.foldLeft(BotType: ST)(_ | _)
    else ts.foldLeft(TopType: ST)(_ & _)
  
  
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
  
  def reconstructClassTypes(st: SimpleType, pol: Opt[Bool], ctx: Ctx): SimpleType = {
    
    implicit val cache: MutMap[TV, Opt[Bool]] = MutMap.empty
    
    if (dbg) {
      val allVarPols = st.getVarsPol(pol)
      println(s"allVarPols: ${allVarPols.iterator.map(e => s"${printPol(e._2)}${e._1}").mkString(", ")}")
    }
    
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
        else if (names.isEmpty) { assert(base.isInstanceOf[ComposedType]); base.map(go(_, pol)) } // FIXME very hacky
        else go(base, pol).without(names)
      case tr @ TypeRef(defn, targs) => tr.copy(targs = targs.map { targ =>
          // TypeBounds.mk(go(targ, false), go(targ, true), targ.prov)
          go(targ, N)
        })(tr.prov)
      // case ty @ (ComposedType(_, _, _) | _: ObjectTag) =>
      case ty @ (ComposedType(_, _, _) | _: ObjectTag | _: WithType) =>
        
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
                    case S(wt @ Without(b: ComposedType, ns @ empty())) => S(Without(b.map(go(_, pol)), ns)(wt.prov)) -> nFields // FIXME very hacky
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
        }.foldLeft(BotType: ST)(_ | _) |> factorize(ctx)
        }
        /* 
        mkDNF(ty, pol)(ctx, ptr = true, etf = false, cache) match {
        // mkDNF(ty, pol)(ctx, ptr = false, etf = false, cache) match {
          case R(dnf) => helper(dnf, pol)
          case L((dnf1, dnf2)) => TypeBounds.mk(helper(dnf1, S(false)), helper(dnf2, S(true)))
        }
        */
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
        
    }
    }(r => s"=> $r")
    
    go(st, pol)
    
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
                        case (`tv1`, `tv2`) => true
                        case (v1: TypeVariable, v2: TypeVariable) => (v1 is v2) || nope
                        case (NegType(negated1), NegType(negated2)) => unify(negated1, negated2)
                        case (ClassTag(id1, parents1), ClassTag(id2, parents2)) => id1 === id2 || nope
                        case (ArrayType(inner1), ArrayType(inner2)) => nope // TODO
                        case (TupleType(fields1), TupleType(fields2)) => nope // TODO
                        case (FunctionType(lhs1, rhs1), FunctionType(lhs2, rhs2)) => nope // TODO
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
                        case (ProvType(underlying1), ProvType(underlying2)) => nope // TODO
                        case (WithType(base1, rcd1), WithType(base2, rcd2)) =>
                          unify(base1, base2) && unify(rcd1, rcd2)
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
    
    
    /* 
    def analyze(pol: Opt[Bool], st: ST): Unit = st match {
      case tv: TV =>
        
      case _ =>
        st.childrenPol(pol)(analyze)
    }
    */
    /* 
    def process(pol: Opt[Bool], st: ST): ST =
    trace(s"factor[${printPol(pol)}] $st") {
      
      pol match {
        case N =>
          st.mapPol(pol, smart = true)(process)
        case S(p) =>
          
          val dnf = DNF.mk(st, p)(ctx, ptr = true, etf = false)
          println(s"dnf = $dnf")
          
          dnf.cs.foreach { c =>
            (c.vars.iterator ++ c.nvars).foreach { tv =>
              processed.setAndIfUnset(tv) {
                tv.lowerBounds = tv.lowerBounds.map(process(S(true), _))
                tv.upperBounds = tv.upperBounds.map(process(S(false), _))
              }
            }
          }
          
          // dnf.toType(sort = true)
          dnf.toType(sort = true).mapPol(pol, smart = true)(process)
      }
      
    }(r => s"~> $r")
    process(pol, st)
    */
    // def transform(pol: Opt[Bool], st: ST): ST =
    
    if (varSubst.nonEmpty) subst(st, varSubst.toMap, substInMap = true) else st
    
  }
  
  
    
}
