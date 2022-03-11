package mlscript

import scala.collection.mutable.{Map => MutMap, Set => MutSet, LinkedHashMap, LinkedHashSet}
import scala.collection.immutable.{SortedMap, SortedSet}
import scala.util.chaining._
import mlscript.utils._, shorthands._

trait TypeSimplifier { self: Typer =>
  
  
  def canonicalizeType(ty: SimpleType, pol: Bool = true)(implicit ctx: Ctx): SimpleType = {
    type PolarType = (DNF, Bool)
    
    val recursive = MutMap.empty[PolarType, TypeVariable]
    
    val renewed = MutMap.empty[TypeVariable, TypeVariable]
    
    val allVars = ty.getVars
    def renew(tv: TypeVariable): TypeVariable =
      renewed.getOrElseUpdate(tv,
        freshVar(noProv, tv.nameHint)(tv.level) tap { fv => println(s"Renewed $tv ~> $fv") })
    
    def goDeep(ty: SimpleType, pol: Bool)(implicit inProcess: Set[PolarType]): SimpleType =
      go1(go0(ty, pol), pol)
    
    // Turn the outermost layer of a SimpleType into a DNF, leaving type variables untransformed
    def go0(ty: SimpleType, pol: Bool)(implicit inProcess: Set[PolarType]): DNF = 
    trace(s"ty[$pol] $ty") {
      
      // TODO should we also coalesce nvars? is it bad if we don't?
      def rec(dnf: DNF, done: Set[TV]): DNF = dnf.cs.iterator.map { c =>
        val vs = c.vars.filterNot(done)
        vs.iterator.map { tv =>
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
    def go1(ty: DNF, pol: Bool)
        (implicit inProcess: Set[PolarType]): SimpleType = trace(s"DNF[$pol] $ty") {
      if (ty.isBot) ty.toType(sort = true) else {
        val pty = ty -> pol
        if (inProcess.contains(pty))
          recursive.getOrElseUpdate(pty, freshVar(noProv)(ty.level))
        else {
          (inProcess + pty) pipe { implicit inProcess =>
            val res = DNF(ty.cs.map { case Conjunct(lnf, vars, rnf, nvars) =>
              def adapt(pol: Bool)(l: LhsNf): LhsNf = l match {
                case LhsRefined(b, ts, RecordType(fs)) => LhsRefined(
                  b.map {
                    case ft @ FunctionType(l, r) =>
                      FunctionType(goDeep(l, !pol), goDeep(r, pol))(noProv)
                    case wo @ Without(b, ns) =>
                      Without(goDeep(b, pol), ns)(noProv)
                    case ft @ TupleType(fs) =>
                      TupleType(fs.map(f => f._1 -> goDeep(f._2, pol)))(noProv)
                    case ar @ ArrayType(inner) =>
                      ArrayType(goDeep(inner, pol))(noProv)
                    case pt: ClassTag => pt
                  },
                  ts,
                  RecordType(fs.map(f => f._1 -> goDeep(f._2, pol)))(noProv)
                )
                case LhsTop => LhsTop
              }
              def adapt2(pol: Bool)(l: RhsNf): RhsNf = l match {
                case RhsField(name, ty) => RhsField(name, goDeep(ty, pol))
                case RhsBases(prims, bf) =>
                  // TODO refactor to handle goDeep returning something else...
                  RhsBases(prims, bf match {
                    case N => N
                    case S(L(bt)) => goDeep(bt, pol) match {
                      case bt: MiscBaseType => S(L(bt))
                      case ExtrType(true) => N
                      case _ => ???
                    }
                    case S(R(r)) => S(R(RhsField(r.name, goDeep(r.ty, pol))))
                  })
                case RhsBot => RhsBot
              }
              Conjunct(adapt(pol)(lnf), vars.map(renew), adapt2(!pol)(rnf), nvars.map(renew))
            })
            val adapted = res.toType(sort = true)
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
  
  
  def simplifyType(st: SimpleType, pol: Bool = true, removePolarVars: Bool = true)(implicit ctx: Ctx): SimpleType = {
    
    val coOccurrences: MutMap[(Bool, TypeVariable), MutSet[SimpleType]] = LinkedHashMap.empty
    
    val analyzed = MutSet.empty[PolarVariable]
    
    def analyze(st: SimpleType, pol: Bool): Unit = st match {
      case RecordType(fs) => fs.foreach(f => analyze(f._2, pol))
      case TupleType(fs) => fs.foreach(f => analyze(f._2, pol))
      case ArrayType(inner) => analyze(inner, pol)
      case FunctionType(l, r) => analyze(l, !pol); analyze(r, pol)
      case tv: TypeVariable =>
        // println(s"! $pol $tv ${coOccurrences.get(pol -> tv)}")
        coOccurrences(pol -> tv) = MutSet(tv)
        processBounds(tv, pol)
      case _: ObjectTag | ExtrType(_) => ()
      case ct: ComposedType =>
        val newOccs = MutSet.empty[SimpleType]
        def go(st: SimpleType): Unit = st match {
          case ComposedType(p, l, r) =>
            // println(s">> $pol $l $r")
            if (p === pol) { go(l); go(r) }
            else { analyze(l, pol); analyze(r, pol) } // TODO compute intersection if p =/= pol
          case _: BaseType => newOccs += st; analyze(st, pol)
          case tv: TypeVariable => newOccs += st; processBounds(tv, pol)
          case _ => analyze(st, pol)
        }
        go(ct)
        newOccs.foreach {
          case tv: TypeVariable =>
            // println(s">>>> $tv $newOccs ${coOccurrences.get(pol -> tv)}")
            coOccurrences.get(pol -> tv) match {
              case Some(os) => os.filterInPlace(newOccs) // computes the intersection
              case None => coOccurrences(pol -> tv) = newOccs
            }
          case _ => ()
        }
      case NegType(und) => analyze(und, !pol)
      case ProxyType(underlying) => analyze(underlying, pol)
      case tr @ TypeRef(defn, targs) => analyze(tr.expand, pol) // FIXME this may diverge; use variance-analysis-based targ traversal instead
      case Without(base, names) => analyze(base, pol)
      case TypeBounds(lb, ub) =>
        if (pol) analyze(ub, true) else analyze(ub, false)
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
    
    def transform(st: SimpleType, pol: Bool): SimpleType = st match {
      case RecordType(fs) => RecordType(fs.map(f => f._1 -> transform(f._2, pol)))(st.prov)
      case TupleType(fs) => TupleType(fs.map(f => f._1 -> transform(f._2, pol)))(st.prov)
      case ArrayType(inner) => ArrayType(transform(inner, pol))(st.prov)
      case FunctionType(l, r) => FunctionType(transform(l, !pol), transform(r, pol))(st.prov)
      case _: ObjectTag | ExtrType(_) => st
      case tv: TypeVariable =>
        varSubst.get(tv) match {
          case S(S(ty)) => transform(ty, pol)
          case S(N) => ExtrType(pol)(noProv)
          case N =>
            var wasDefined = true
            val res = renewals.getOrElseUpdate(tv, {
              wasDefined = false
              val nv = freshVar(noProv, tv.nameHint)(tv.level)
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
      case tr @ TypeRef(defn, targs) => transform(tr.expand, pol) // FIXME may diverge; and we should try to keep these!
      case wo @ Without(base, names) =>
        if (names.isEmpty) transform(base, pol)
        else Without(transform(base, pol), names)(wo.prov)
      case tb @ TypeBounds(lb, ub) =>
        if (pol) transform(ub, true) else transform(lb, false)
    }
    transform(st, pol)
    
  }
  
  def reconstructClassTypes(st: SimpleType, pol: Bool, ctx: Ctx): SimpleType = {
    
    implicit val ctxi: Ctx = ctx
    val renewed = MutMap.empty[TypeVariable, TypeVariable]
    
    def renew(tv: TypeVariable): TypeVariable =
      if (tv.lowerBounds.isEmpty && tv.upperBounds.isEmpty) tv
      else renewed.get(tv) match {
        case S(tv2) => tv2
        case N =>
          val tv2 = freshVar(tv.prov, tv.nameHint)(tv.level)
          renewed += tv -> tv2
          tv2.lowerBounds = tv.lowerBounds.map(go(_, true))
          tv2.upperBounds = tv.upperBounds.map(go(_, false))
          tv2
      }
    
    def go(st: SimpleType, pol: Bool): SimpleType = st match {
      case ExtrType(_) => st
      case tv: TypeVariable => renew(tv)
      case NegType(und) => go(und, !pol).neg()
      case TypeBounds(lb, ub) => if (pol) go(ub, true) else go(lb, false)
      case RecordType(fs) => RecordType(fs.mapValues(go(_, pol)))(st.prov)
      case TupleType(fs) => TupleType(fs.mapValues(go(_, pol)))(st.prov)
      case ArrayType(inner) => ArrayType(go(inner, pol))(st.prov)
      case FunctionType(l, r) => FunctionType(go(l, !pol), go(r, pol))(st.prov)
      case ProvType(underlying) => ProvType(go(underlying, pol))(st.prov)
      case ProxyType(underlying) => go(underlying, pol)
      case wo @ Without(base, names) =>
        if (pol) go(base, pol).withoutPos(names)
        else go(base, pol).without(names)
      case tr @ TypeRef(defn, targs) => tr.copy(targs = targs.map { targ =>
          TypeBounds.mk(go(targ, false), go(targ, true), targ.prov)
        })(tr.prov)
      case ty @ ComposedType(true, l, r) => go(l, pol) | go(r, pol)
      case ty @ (ComposedType(false, _, _) | _: ObjectTag) =>
        val dnf @ DNF(cs) = DNF.mk(ty, pol)
        cs.sorted.map { c =>
          c.copy(vars = c.vars.map(renew), nvars = c.nvars.map(renew)).toTypeWith(_ match {
            case LhsRefined(bo, tts, rcd) =>
              bo match {
                case S(cls @ ClassTag(Var(tagNme), ps)) if !primitiveTypes.contains(tagNme) =>
                  val clsNme = tagNme.capitalize
                  val td = ctx.tyDefs(clsNme)
                  val typeRef = TypeRef(td.nme, td.tparams.map { tp =>
                    val fieldTagNme = tparamField(TypeName(clsNme), tp)
                    rcd.fields.iterator.filter(_._1 === fieldTagNme).collectFirst {
                      case (_, FunctionType(ub, lb)) if lb >:< ub => lb
                      case (_, FunctionType(lb, ub)) =>
                        TypeBounds.mk(go(lb, false), go(ub, true))
                    }.getOrElse(TypeBounds(BotType, TopType)(noProv))
                  })(noProv)
                  val clsFields = fieldsOf(
                    typeRef.expandWith(paramTags = false), paramTags = false)
                  val cleanPrefixes = ps.map(v => v.name.capitalize) + clsNme
                  val cleanedRcd = rcd.copy(
                    rcd.fields.filterNot { case (field, fty) =>
                      // println(s"F1 $field $fty ${clsFields.get(field)} ${clsFields.get(field).map(_ <:< fty)}")
                      cleanPrefixes.contains(field.name.takeWhile(_ != '#')) ||
                        clsFields.get(field).exists(_ <:< fty)
                    }.mapValues(go(_, pol))
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
                  tts.toArray.sorted // TODO also filter out tts that are inherited by the class
                    .foldLeft(withType: ST)(_ & _)
                case _ =>
                  lazy val nFields = rcd.fields.filterNot(_._1.name.isCapitalized).mapValues(go(_, pol))
                  val (res, nfs) = bo match {
                    case S(tt @ TupleType(fs)) =>
                      val arity = fs.size
                      val (componentFields, rcdFields) = rcd.fields
                        .filterNot(_._1.name.isCapitalized)
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
                        nme -> go(ty & componentFieldsMap.getOrElse(i + 1, TopType), pol)
                      }.toList
                      S(TupleType(tupleComponents)(tt.prov)) -> rcdFields.mapValues(go(_, pol))
                    case S(ct: ClassTag) => S(ct) -> nFields
                    case S(ft @ FunctionType(l, r)) =>
                      S(FunctionType(go(l, !pol), go(r, pol))(ft.prov)) -> nFields
                    case S(at @ ArrayType(inner)) => S(ArrayType(go(inner, pol))(at.prov)) -> nFields
                    case S(wt @ Without(b, ns)) => S(Without(go(b, pol), ns)(wt.prov)) -> nFields
                    case N => N -> nFields
                  }
                  LhsRefined(res, tts, rcd.copy(nfs)(rcd.prov).sorted).toType(sort = true)
              }
            case LhsTop => TopType
          }, {
            case RhsBot => BotType
            case RhsField(n, t) => RecordType(n -> go(t, pol) :: Nil)(noProv)
            case RhsBases(ots, rest) =>
              // Note: could recosntruct class tags for these, but it would be pretty verbose,
              //    as in showing `T & ~C[?] & ~D[?, ?]` instead of just `T & ~c & ~d`
              // ots.map { case t @ (_: ClassTag | _: TraitTag) => ... }
              val r = rest match {
                case v @ S(R(RhsField(n, t))) => RhsField(n, go(t, pol)).toType(sort = true)
                case v @ S(L(bty)) => go(bty, pol)
                case N => BotType
              }
              ots.sorted.foldLeft(r)(_ | _)
          }, sort = true)
        }.foldLeft(BotType: ST)(_ | _)
    }
    
    go(st, pol)
    
  }
    
}
