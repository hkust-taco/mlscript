package mlscript

import scala.collection.mutable.{Map => MutMap, Set => MutSet, LinkedHashMap, LinkedHashSet}
import scala.collection.immutable.{SortedMap, SortedSet}
import scala.util.chaining._
import mlscript.utils._, shorthands._

trait TypeSimplifier { self: Typer =>
  
  
  def canonicalizeType(ty: SimpleType, pol: Bool = true): SimpleType = {
    type PolarType = (DNF, Boolean)
    
    val recursive = MutMap.empty[PolarType, TypeVariable]
    
    val renewed = MutMap.empty[TypeVariable, TypeVariable]
    
    val allVars = ty.getVars
    def renew(tv: TypeVariable): TypeVariable =
      renewed.getOrElseUpdate(tv,
        freshVar(noProv)(0) tap { fv => println(s"Renewed $tv ~> $fv") })
    
    def goDeep(ty: SimpleType, pol: Boolean)(implicit inProcess: Set[PolarType]): SimpleType =
      go1(go0(ty, pol), pol)
    
    // Turn the outermost layer of a SimpleType into a DNF, leaving type variables untransformed
    def go0(ty: SimpleType, pol: Boolean)(implicit inProcess: Set[PolarType]): DNF = 
    trace(s"ty[$pol] $ty") {
      
      // TODO should we also coalesce nvars? is it bad if we don't?
      def rec(dnf: DNF, done: Set[TV]): DNF = dnf.cs.iterator.map { c =>
        val vs = c.vars.filterNot(done)
        vs.map { tv =>
          println(s"Consider $tv ${tv.lowerBounds} ${tv.upperBounds}")
          val b =
            if (pol) tv.lowerBounds.foldLeft(tv:ST)(_ | _)
            else tv.upperBounds.foldLeft(tv:ST)(_ & _)
          // println(s"b $b")
          val bd = rec(DNF.mk(b, pol), done + tv)
          // println(s"bd $bd")
          bd
        }
        .foldLeft(DNF(c.copy(vars = c.vars.filterNot(vs))::Nil))(_ & _)
      }.foldLeft(DNF.extr(false))(_ | _)
      
      rec(DNF.mk(ty, pol), Set.empty)
      
    }(r => s"-> $r")
    
    // Merge the bounds of all type variables of the given DNF, and traverse the result
    def go1(ty: DNF, pol: Boolean)
        (implicit inProcess: Set[PolarType]): SimpleType = trace(s"DNF[$pol] $ty") {
      if (ty.isBot) ty.toType else {
        val pty = ty -> pol
        if (inProcess.contains(pty))
          recursive.getOrElseUpdate(pty, freshVar(noProv)(0))
        else {
          (inProcess + pty) pipe { implicit inProcess =>
            val res = DNF(ty.cs.map { case Conjunct(lnf, vars, rnf, nvars) =>
              def adapt(pol: Bool)(l: LhsNf): LhsNf = l match {
                case LhsRefined(b, RecordType(fs)) => LhsRefined(
                  b.map {
                    case ft @ FunctionType(l, r) =>
                      FunctionType(goDeep(l, !pol), goDeep(r, pol))(noProv)
                    case wo @ Without(b, ns) =>
                      Without(goDeep(b, pol), ns)(noProv)
                    case ft @ TupleType(fs) =>
                      TupleType(fs.map(f => f._1 -> goDeep(f._2, pol)))(noProv)
                    case pt: PrimType => pt
                  },
                  RecordType(fs.map(f => f._1 -> goDeep(f._2, pol)))(noProv)
                )
                case LhsTop => LhsTop
              }
              def adapt2(pol: Bool)(l: RhsNf): RhsNf = l match {
                case RhsField(name, ty) => RhsField(name, goDeep(ty, pol))
                case RhsBases(prims, bty, f) =>
                  RhsBases(prims, bty.flatMap(goDeep(_, pol) match {
                    case bt: BaseType => S(bt)
                    case ExtrType(true) => N
                    // case _ => ??? // TODO
                  })
                  , f.map(f => RhsField(f.name, goDeep(f.ty, pol))))
                case RhsBot => RhsBot
              }
              Conjunct(adapt(pol)(lnf), vars.map(renew), adapt2(!pol)(rnf), nvars.map(renew))
            })
            val adapted = res.toType
            recursive.get(pty) match {
              case Some(v) =>
                val bs = if (pol) v.lowerBounds else v.upperBounds
                if (bs.isEmpty) { // it's possible we have already set the bounds in a sibling call
                  if (pol) v.lowerBounds ::= adapted else v.upperBounds ::= adapted
                }
                v
              case None => adapted
            }
          }
        }
      }
    }(r => s"~> $r")
    
    goDeep(ty, pol)(Set.empty)
    
  }
  
  
  def simplifyType(st: SimpleType, pol: Bool = true, removePolarVars: Bool = true): SimpleType = {
    
    val coOccurrences: MutMap[(Boolean, TypeVariable), MutSet[SimpleType]] = LinkedHashMap.empty
    
    val analyzed = MutSet.empty[PolarVariable]
    
    def analyze(st: SimpleType, pol: Boolean): Unit = st match {
      case RecordType(fs) => fs.foreach(f => analyze(f._2, pol))
      case TupleType(fs) => fs.foreach(f => analyze(f._2, pol))
      case FunctionType(l, r) => analyze(l, !pol); analyze(r, pol)
      case tv: TypeVariable =>
        println(s"! $pol $tv ${coOccurrences.get(pol -> tv)}")
        coOccurrences(pol -> tv) = MutSet(tv)
        processBounds(tv, pol)
      case PrimType(_, _) | ExtrType(_) => ()
      case ct: ComposedType =>
        val newOccs = MutSet.empty[SimpleType]
        def go(st: SimpleType): Unit = st match {
          case ComposedType(p, l, r) =>
            println(s">> $pol $l $r")
            if (p === pol) { go(l); go(r) }
            else { analyze(l, pol); analyze(r, pol) } // TODO compute intersection if p =/= pol
          case _: BaseType => newOccs += st; analyze(st, pol)
          case tv: TypeVariable => newOccs += st; processBounds(tv, pol)
          case _ => analyze(st, pol)
        }
        go(ct)
        newOccs.foreach {
          case tv: TypeVariable =>
            println(s">>>> $tv $newOccs ${coOccurrences.get(pol -> tv)}")
            coOccurrences.get(pol -> tv) match {
              case Some(os) => os.filterInPlace(newOccs) // computes the intersection
              case None => coOccurrences(pol -> tv) = newOccs
            }
          case _ => ()
        }
      case NegType(und) => analyze(und, !pol)
      case ProxyType(underlying) => analyze(underlying, pol)
      case tr @ TypeRef(defn, targs) => analyze(tr.expand(_ => ()), pol) // TODO try to keep them?
      case Without(base, names) => analyze(base, pol)
    }
    def processBounds(tv: TV, pol: Bool) = {
      if (!analyzed(tv -> pol)) {
        analyzed(tv -> pol) = true
        (if (pol) tv.lowerBounds else tv.upperBounds).foreach(analyze(_, pol))
      }
    }
    
    analyze(st, pol)
    
    println(s"[occs] ${coOccurrences}")
    
    // This will be filled up after the analysis phase, to influence the reconstruction phase:
    val varSubst = MutMap.empty[TypeVariable, Option[TypeVariable]]
    
    val allVars = st.getVars
    val recVars = MutSet.from(
      allVars.iterator.filter(tv => tv.lowerBounds.nonEmpty || tv.upperBounds.nonEmpty))
    
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
          case w: TypeVariable if !(w is v) && !varSubst.contains(w) && (recVars.contains(v) === recVars.contains(w)) =>
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
              if (recVars.contains(w)) { // `w` is a recursive variable, so `v` is too (see `recVars.contains` guard above)
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
                /* 
                val wCoOcss = coOccurrences((!pol) -> w)
                // ^ this must be defined otherwise we'd already have simplified away the non-rec variable
                coOccurrences((!pol) -> v).filterInPlace(t => t === v || wCoOcss(t))
                // ^ `w` is not recursive, so `v` is not either, and the same reasoning applies
                */
                // When removePolarVars is enabled, wCoOcss/vCoOcss may not be defined:
                for {
                  wCoOcss <- coOccurrences.get((!pol) -> w)
                  vCoOcss <- coOccurrences.get((!pol) -> v)
                } vCoOcss.filterInPlace(t => t === v || wCoOcss(t))
              }
            }; ()
          case atom: BaseType if (coOccurrences.get(!pol -> v).exists(_(atom))) =>
            varSubst += v -> None; ()
          case _ =>
        }
      }
    }}
    println(s"[sub] ${varSubst.map(k => k._1.toString + " -> " + k._2).mkString(", ")}")
    
    
    val renewals = MutMap.empty[TypeVariable, TypeVariable]
    
    def transform(st: SimpleType, pol: Boolean): SimpleType = st match {
      case RecordType(fs) => RecordType(fs.map(f => f._1 -> transform(f._2, pol)))(st.prov)
      case TupleType(fs) => TupleType(fs.map(f => f._1 -> transform(f._2, pol)))(st.prov)
      case FunctionType(l, r) => FunctionType(transform(l, !pol), transform(r, pol))(st.prov)
      case PrimType(_, _) | ExtrType(_) => st
      case tv: TypeVariable =>
        varSubst.get(tv) match {
          case S(S(ty)) => transform(ty, pol)
          case S(N) => ExtrType(pol)(noProv)
          case N =>
            var wasDefined = true
            val res = renewals.getOrElseUpdate(tv, {
              wasDefined = false
              val nv = freshVar(noProv)(0)
              println(s"Renewed $tv ~> $nv")
              nv
            })
            if (!wasDefined) {
              res.lowerBounds = tv.lowerBounds.map(transform(_, true))
              res.upperBounds = tv.upperBounds.map(transform(_, false))
            }
            res
        }
      case ty @ ComposedType(true, l, r) => transform(l, pol) | transform(r, pol)
      case ty @ ComposedType(false, l, r) => transform(l, pol) & transform(r, pol)
      case NegType(und) => transform(und, !pol).neg()
      case ProxyType(underlying) => transform(underlying, pol)
      case tr @ TypeRef(defn, targs) => transform(tr.expand(_ => ()), pol) // TODO try to keep them?
      case wo @ Without(base, names) => Without(transform(base, pol), names)(wo.prov)
    }
    transform(st, pol)
    
  }
  
}
