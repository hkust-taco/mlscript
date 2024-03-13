package mlscript

import scala.collection.mutable
import scala.collection.mutable.{Map => MutMap, Set => MutSet}
import scala.collection.immutable.{SortedSet, SortedMap}
import SortedSet.{empty => ssEmp}, SortedMap.{empty => smEmp}
import scala.util.chaining._
import scala.annotation.tailrec
import mlscript.utils._, shorthands._
import mlscript.Message._

class NormalForms extends TyperDatatypes { self: Typer =>
  
  type ExpandTupleFields >: Bool
  type PreserveTypeRefs >: Bool
  
  def preserveTypeRefs(implicit ptr: PreserveTypeRefs): Bool = ptr === true
  def expandTupleFields(implicit etf: ExpandTupleFields): Bool = etf === true
  
  
  private def mergeTypeRefs(pol: Bool, trs1: SortedMap[TN, TR], trs2: SortedMap[TN, TR])(implicit ctx: Ctx): SortedMap[TN, TR] =
    mergeSortedMap(trs1, trs2) { (tr1, tr2) =>
      assert(tr1.defn === tr2.defn)
      assert(tr1.targs.size === tr2.targs.size)
      TypeRef(tr1.defn, (tr1.targs lazyZip tr2.targs).map((ta1, ta2) => 
          if (pol) TypeBounds.mk(ta1 & ta2, ta1 | ta2) else TypeBounds.mk(ta1 | ta2, ta1 & ta2)
        ))(noProv)
    }
  
  
  sealed abstract class LhsNf {
    final def compareEquiv(that: LhsNf): Int = (this, that) match {
      case (LhsRefined(b1, ts1, r1, trs1), LhsRefined(b2, ts2, r2, trs2)) =>
        var cmp = (b1, b2) match {
          case (S(c1), S(c2)) => c1.compareEquiv(c2)
          case (S(c1), N) => -1
          case (N, S(c2)) => 1
          case (N, N) => 0
        }
        if (cmp =/= 0) return cmp
        // * Just compare the heads for simplicity...
        cmp = (trs1.headOption, trs2.headOption) match {
          case (S((n1, _)), S((n2, _))) =>
            n1.compare(n2) // * in principle we could go on to compare the tails if this is 0
          case (S(_), N) => 1
          case (N, S(_)) => -1
          case (N, N) => 0
        }
        if (cmp =/= 0) return cmp
        cmp = -trs1.sizeCompare(trs2)
        if (cmp =/= 0) return cmp
        cmp = ts1.sizeCompare(ts2.size)
        if (cmp =/= 0) return cmp
        cmp = r1.fields.sizeCompare(r2.fields)
        cmp
      case (LhsTop, _) => 1
      case (_, LhsTop) => -1
    }
    def toTypes: Ls[SimpleType] = toType() :: Nil
    def toType(sort: Bool = false): SimpleType =
      if (sort) mkType(true) else underlying
    private def mkType(sort: Bool): SimpleType = this match {
      case LhsRefined(bo, ts, r, trs) =>
        val sr = if (sort) r.sorted else r
        val bo2 = bo.filter {
          case ClassTag(id, parents) => !trs.contains(TypeName(id.idStr.capitalize))
          case _ => true
        }
        val trsBase = trs.valuesIterator.foldRight(bo2.fold[ST](sr)(_ & sr))(_ & _)
        (if (sort) ts.toArray.sorted else ts.toArray).foldLeft(trsBase)(_ & _)
      case LhsTop => TopType
    }
    lazy val underlying: SimpleType = mkType(false)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level =
      this match {
        case LhsRefined(base, ttags, reft, trefs) =>
          (base.iterator.map(_.levelBelow(ub)) ++ ttags.iterator.map(_.levelBelow(ub)) ++
            reft.fields.iterator.values.map(_.levelBelow(ub)) ++ trefs.iterator.values.map(_.levelBelow(ub))
          ).reduceOption(_ max _).getOrElse(MinLevel)
        case LhsTop => MinLevel
      }
    def freshenAbove(lim: Int, rigidify: Bool)
          (implicit ctx: Ctx, freshened: MutMap[TV, ST]): LhsNf = this match {
      case LhsRefined(bo, ts, r, trs) =>
        LhsRefined(bo.map(_.freshenAbove(lim, rigidify)), ts, r.freshenAbove(lim, rigidify),
          trs.view.mapValues(_.freshenAbove(lim, rigidify)).to(SortedMap))
      case LhsTop => this
    }
    def hasTag(ttg: AbstractTag): Bool = this match {
      case LhsRefined(bo, ts, r, trs) => ts(ttg)
      case LhsTop => false
    }
    def size: Int = this match {
      case LhsRefined(bo, ts, r, trs) => bo.size + ts.size + r.fields.size + trs.size
      case LhsTop => 0
    }
    def & (that: AbstractTag): LhsNf = this match {
      case LhsTop => LhsRefined(N, SortedSet.single(that), RecordType.empty, smEmp)
      case LhsRefined(b, ts, r, trs) => LhsRefined(b, ts + that, r, trs)
    }
    def & (that: BaseTypeOrTag, pol: Bool)(implicit ctx: Ctx, etf: ExpandTupleFields): Opt[LhsNf] = (this, that) match {
      case (LhsTop, that: TupleType) => S(LhsRefined(S(that), ssEmp, if (expandTupleFields) that.toRecord else RecordType.empty, smEmp))
      case (LhsTop, that: BaseType) => S(LhsRefined(S(that), ssEmp, RecordType.empty, smEmp))
      case (LhsTop, that: AbstractTag) => S(LhsRefined(N, SortedSet.single(that), RecordType.empty, smEmp))
      case (LhsRefined(b1, ts, r1, trs), that: AbstractTag) => S(LhsRefined(b1, ts + that, r1, trs))
      case (LhsRefined(b1, ts, r1, trs), that: BaseType) =>
        var r1Final = r1
        ((b1, that) match {
          case (S(p0 @ ClassTag(pt0, ps0)), p1 @ ClassTag(pt1, ps1)) =>
            // println(s"!GLB! $this $that ${p0.glb(p1)}")
            p0.glb(p1)
          
          case (S(l @ FunctionType(l0, r0)), FunctionType(l1, r1))
          if approximateNegativeFunction && !pol =>
            S(FunctionType(l0 | l1, r0 & r1)(l.prov))
          
          // * Note: it also feels natural to simplify `f: int -> int & nothing -> string`
          // * to just `f: int -> int`, but these types are not strictly-speaking equivalent;
          // * indeed, we could still call such a function as `f error : string`...
          // * (This is similar to how `{ x: nothing }` is not the same as `nothing`.)
          // * Note: in any case it should be fine to make this approximation in positive positions.
          // * Still, it seems making this approximation is morally correct even in negative positions,
          // * at least in a CBV setting, since the only way to use the bad function component is
          // * by passing a non-returning computation. So this should be semantically sound.
          case (S(FunctionType(AliasOf(TupleType(fs)), _)), _: Overload | _: FT)
          if fs.exists(_._2.ub.isBot) => S(that)
          case (sov @ S(Overload(alts)), FunctionType(AliasOf(TupleType(fs)), _))
          if fs.exists(_._2.ub.isBot) => sov
          
          case (S(ov @ Overload(alts)), ft: FunctionType) =>
            def go(alts: Ls[FT]): Ls[FT] = alts match {
              case (f @ FunctionType(l, r)) :: alts =>
                /* // * Note: A simpler version that gets most of the way there:
                if (l >:< ft.lhs) FunctionType(l, r & ft.rhs)(f.prov) :: alts
                else if (r >:< ft.rhs) FunctionType(l | ft.lhs, r)(f.prov) :: alts
                else f :: go(alts)
                */
                val l_LT_lhs = l <:< ft.lhs
                lazy val l_GT_lhs = ft.lhs <:< l
                lazy val r_LT_rhs = r <:< ft.rhs
                lazy val r_GT_rhs = ft.rhs <:< r
                if (l_LT_lhs && r_GT_rhs) ft :: alts
                else if (l_GT_lhs && r_LT_rhs) f :: alts
                else if (l_LT_lhs && l_GT_lhs) FunctionType(l, r & ft.rhs)(f.prov) :: alts
                else if (r_LT_rhs && r_GT_rhs) FunctionType(l | ft.lhs, r)(f.prov) :: alts
                else f :: go(alts)
              case Nil => ft :: Nil
            }
            S(Overload(go(alts))(ov.prov))
          case (S(ft: FunctionType), _: Overload | _: FT) =>
            return LhsRefined(S(Overload(ft :: Nil)(that.prov)), ts, r1, trs) & (that, pol)
          case (S(Overload(alts1)), ov2 @ Overload(a2 :: alts2)) =>
            alts2 match {
              case Nil => 
                return this & (a2, pol)
              case _ =>
                return this & (a2, pol) flatMap (_ & (Overload(alts2)(ov2.prov), pol))
            }
          
          case (S(TupleType(fs0)), tup @ TupleType(fs1)) =>
            if (fs0.size === fs1.size) {
              if (expandTupleFields)
                r1Final = RecordType(mergeSortedMap(r1Final.fields, tup.toRecord.fields)(_ && _).toList)(noProv)
              S(TupleType(tupleIntersection(fs0, fs1))(noProv))
            } else N
          case (S(ArrayType(ar)), tup @ TupleType(fs)) =>
            if (expandTupleFields)
              r1Final = RecordType(mergeSortedMap(r1Final.fields, tup.toRecord.fields)(_ && _).toList)(noProv)
            S(TupleType(fs.map { ty =>
              ty._1 -> (ar && ty._2)
            })(noProv))
          case (S(TupleType(fs)), ArrayType(ar)) =>
            S(TupleType(fs.map { ty =>
              ty._1 -> (ty._2 && ar)
            })(noProv))
          case (S(ArrayType(i1)), ArrayType(i2)) =>
            // Array[p] & Array[q] => Array[p & q]
            S(ArrayType(i1 && i2)(noProv))
            
          case (S(w1 @ Without(b1, ns1)), w2 @ Without(b2, ns2)) if ns1 === ns2 =>
            S(Without(b1 & b2, ns1)(w1.prov & w2.prov))
          // The following cases are quite hacky... if we find two incompatible Without types,
          //  just make a new dummy Without type to merge them.
          // The workaround is due to the fact that unlike other types, we can't fully
          //  reduce Without types away, so they are "unduly" treated as `BaseType`s.
          // This will be fixed whe we support proper TV bounds for homomorphic type computations
          case (S(b), w: Without) => S(Without(b & w, ssEmp)(noProv))
          case (S(w: Without), b) => S(Without(w & b, ssEmp)(noProv))
            
          case (S(_: TypeTag), _: FunctionType | _: ArrayBase | _: Overload)
            |  (S(_: FunctionType | _: ArrayBase | _: Overload), _: TypeTag)
            |  (S(_: FunctionType), _: ArrayBase | _: Overload)
            |  (S(_: ArrayBase | _: Overload), _: FunctionType)
            |  (S( _: ArrayBase), _: Overload)
            |  (S(_: Overload), _: ArrayBase)
            => N
          
          case (S(Overload(Nil)), _) | (S(_), Overload(Nil)) =>
            die // Overload must have nonempty alts
          
          case (S(_: SpliceType), _) | (S(_), _: SpliceType) => ??? // TODO
          
          case (N, tup: TupleType) =>
            if (expandTupleFields)
              r1Final = RecordType(mergeSortedMap(r1Final.fields, tup.toRecord.fields)(_ && _).toList)(noProv)
            S(that)
          case (N, _) => S(that)
        }) map { b => LhsRefined(S(b), ts, r1Final, trs) }
    }
    def & (that: RecordType): LhsNf = this match {
      case LhsTop => LhsRefined(N, ssEmp, that, smEmp)
      case LhsRefined(b1, ts, r1, trs) =>
        LhsRefined(b1, ts,
          RecordType(recordIntersection(r1.fields, that.fields))(noProv/*TODO*/), trs)
    }
    def & (that: TypeRef, pol: Bool)(implicit ctx: Ctx, etf: ExpandTupleFields): Opt[LhsNf] = this match {
      case LhsTop => S(LhsRefined(N, ssEmp, RecordType.empty, SortedMap.single(that.defn -> that)))
      case LhsRefined(b, ts, rt, trs) =>
        val trs2 = trs + (that.defn -> trs.get(that.defn).fold(that) { other =>
          var thatTargs = that.targs
          assert(thatTargs.sizeCompare(other.targs) === 0)
          val newTargs = other.mapTargs(S(true)) { (vce, otherTarg) =>
            val thatTarg = thatTargs.head
            thatTargs = thatTargs.tail
            vce match {
              case S(true) => otherTarg & thatTarg
              case S(false) => otherTarg | thatTarg
              case N =>
                if (pol) TypeBounds.mk(otherTarg | thatTarg, otherTarg & thatTarg)
                else TypeBounds.mk(otherTarg & thatTarg, otherTarg | thatTarg)
            }
          }
          TypeRef(that.defn, newTargs)(that.prov)
        })
        val res = LhsRefined(b, ts, rt, trs2)
        that.mkClsTag.fold(S(res): Opt[LhsNf])(res & (_, pol))
    }
    def & (that: LhsNf, pol: Bool)(implicit ctx: Ctx, etf: ExpandTupleFields): Opt[LhsNf] = (this, that) match {
      case (_, LhsTop) => S(this)
      case (LhsTop, _) => S(that)
      case (_, LhsRefined(bo, ts, rt, trs)) =>
        ts.iterator.foldLeft(
          trs.valuesIterator.foldLeft((bo.fold(some(this & rt))(this & rt & (_, pol))))(_.getOrElse(return N) & (_, pol))
        )(_.getOrElse(return N) & (_, pol))
    }
    def <:< (that: RhsNf)(implicit ctx: Ctx): Bool = (this, that) match {
      case (LhsRefined(_, _, reft, trs), RhsField(nme, ft)) => reft <:< RecordType(nme -> ft :: Nil)(noProv)
      case (lhs @ LhsRefined(bse, tts, reft, trs), RhsBases(tags, rest, trefs)) =>
        tags.exists(tag =>
          bse match {
            case S(cls: ClassTag) => tag.id === cls.id || lhs.allTags.contains(tag.id)
            case _ => false
          }
        ) || (rest match {
          case S(R(f: RhsField)) => this <:< f
          case S(L(rhs @ (_: FunctionType | _: Overload | _: ArrayBase | _: TupleType))) =>
            bse.exists(_ <:< rhs)
          case S(L(wt: Without)) => return underlying <:< that.underlying
          case N => false
        }) || trefs.exists { case (_, tr) =>
          underlying <:< tr
        }
      case (LhsTop, _) => false
      case (_, RhsBot) => false
    }
    def <:< (that: LhsNf)(implicit ctx: Ctx): Bool = (this, that) match {
      case (_, LhsTop) => true
      case (LhsTop, _) => false
      case (LhsRefined(b1, ts1, rt1, trs1), LhsRefined(b2, ts2, rt2, trs2)) =>
        b2.forall(b2 => b1.exists(_ <:< b2)) &&
          ts2.forall(ts1) && rt1 <:< rt2 &&
          trs2.valuesIterator.forall(tr2 => trs1.valuesIterator.exists(_ <:< tr2))
    }
    def isTop: Bool = isInstanceOf[LhsTop.type]
  }
  case class LhsRefined(base: Opt[BaseType], ttags: SortedSet[AbstractTag], reft: RecordType, trefs: SortedMap[TypeName, TypeRef]) extends LhsNf {
    // assert(!trefs.exists(primitiveTypes contains _._1.name))
    lazy val allTags: Set[IdentifiedTerm] = ttags.iterator.foldLeft(base match {
        case S(cls: ClassTag) => cls.parentsST + cls.id
        case _ => Set.empty[IdentifiedTerm]
      }) {
        case (acc, tt: TraitTag) => acc ++ tt.parentsST + tt.id
        case (acc, _) => acc
      }
    override def toString: Str = s"${base.getOrElse("")}${reft}${
      (ttags.iterator ++ trefs.valuesIterator).map("∧"+_).mkString}"
  }
  case object LhsTop extends LhsNf {
    override def toString: Str = "⊤"
  }
  
  
  sealed abstract class RhsNf {
    final def compareEquiv(that: RhsNf): Int = (this, that) match {
      case (RhsField(n1, t1), RhsField(n2, t2)) => n1.compare(n2)
      case (RhsBases(ps1, bf1, trs1), RhsBases(ps2, bf2, trs2)) =>
        var cmp = ps1.minOption match {
          case S(m1) => ps2.minOption match {
            case S(m2) => m1.compare(m2)
            case N => ps1.size.compare(ps2.size)
          }
          case N => ps1.size.compare(ps2.size)
        }
        if (cmp =/= 0) return cmp
        cmp = (trs1.headOption, trs2.headOption) match {
          case (S((n1, _)), S((n2, _))) => n1.compare(n2)
          case (S(_), N) => 1
          case (N, S(_)) => -1
          case (N, N) => 0
        }
        if (cmp =/= 0) return cmp
        cmp = -trs1.sizeCompare(trs2)
        cmp
      case (_: RhsBases, _) => -1
      case (_, _: RhsBases) => 1
      case (_: RhsField, _) => -1
      case (_, _: RhsField) => 1
      case (RhsBot, RhsBot) => 0
    }
    def toTypes: Ls[SimpleType] = toType() :: Nil
    def toType(sort: Bool = false): SimpleType =
      if (sort) mkType(true) else underlying
    private def mkType(sort: Bool): SimpleType = this match {
      case RhsField(n, t) => RecordType(n -> t :: Nil)(noProv) // FIXME prov
      case RhsBases(ps, bf, trs) =>
        val sr = bf.fold(BotType: ST)(_.fold(identity, _.toType(sort)))
        val trsBase = trs.valuesIterator.foldRight(sr)(_ | _)
        (if (sort) ps.sorted else ps).foldLeft(trsBase)(_ | _)
      case RhsBot => BotType
    }
    lazy val underlying: SimpleType = mkType(false)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level =
      underlying.levelBelow(ub) // TODO avoid forcing `underlying`!
    def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): RhsNf
    def hasTag(ttg: AbstractTag): Bool = this match {
      case RhsBases(ts, _, trs) => ts.contains(ttg)
      case RhsBot | _: RhsField => false
    }
    def | (that: TypeRef, pol: Bool)(implicit ctx: Ctx): Opt[RhsNf] = this match {
      case RhsBot => S(RhsBases(Nil, N, SortedMap.single(that.defn -> that)))
      case RhsField(name, ty) => this | name -> ty
      case RhsBases(prims, bf, trs) =>
        val trs2 = trs + (that.defn -> trs.get(that.defn).fold(that) { other =>
          var thatTargs = that.targs
          assert(thatTargs.sizeCompare(other.targs) === 0)
          val newTargs = other.mapTargs(S(true)) { (vce, otherTarg) =>
            val thatTarg = thatTargs.head
            thatTargs = thatTargs.tail
            vce match {
              case S(true) => otherTarg | thatTarg
              case S(false) => otherTarg & thatTarg
              case N =>
                if (pol) TypeBounds.mk(otherTarg & thatTarg, otherTarg | thatTarg)
                else TypeBounds.mk(otherTarg | thatTarg, otherTarg & thatTarg)
            }
          }
          TypeRef(that.defn, newTargs)(that.prov)
        })
        S(RhsBases(prims, bf, trs2))
    }
    def | (that: RhsNf, pol: Bool)(implicit ctx: Ctx): Opt[RhsNf] = that match {
      case RhsBases(prims, bf, trs) =>
        val thisWithTrs = trs.valuesIterator.foldLeft(this)(_ | (_, pol) getOrElse (return N))
        val tmp = prims.foldLeft(thisWithTrs)(_ | _ getOrElse (return N))
        S(bf.fold(tmp)(_.fold(tmp | _ getOrElse (return N),
          tmp | _.name_ty getOrElse (return N))))
      case RhsField(name, ty) => this | name -> ty
      case RhsBot => S(this)
    }
    def tryMergeInter(that: RhsNf)(implicit ctx: Ctx): Opt[RhsNf] = (this, that) match {
      case (RhsBot, _) | (_, RhsBot) => S(RhsBot)
      case (RhsField(name1, ty1), RhsField(name2, ty2)) if name1 === name2 => S(RhsField(name1, ty1 && ty2))
      case (RhsBases(prims1, S(R(r1)), trs1), RhsBases(prims2, S(R(r2)), trs2))
        if prims1 === prims2 && trs1 === trs2 && r1.name === r2.name
        => S(RhsBases(prims1, S(R(RhsField(r1.name, r1.ty && r2.ty))), trs1))
      case (RhsBases(prims1, bf1, trs1), RhsBases(prims2, bf2, trs2))
        if prims1 === prims2 && bf1 === bf2 && trs1.keySet === trs2.keySet
        => // * eg for merging `~Foo[S] & ~Foo[T]`:
          S(RhsBases(prims1, bf1, mergeTypeRefs(false, trs1, trs2)))
      case (RhsBases(prims1, bf1, trs1), RhsBases(prims2, bf2, trs2)) =>
        N // TODO could do some more merging here – for the possible base types
      case _ => N
    }
    def | (that: AbstractTag): RhsNf = this match {
      case RhsBot => RhsBases(that :: Nil, N, smEmp)
      case rf: RhsField => RhsBases(that :: Nil, S(R(rf)), smEmp)
      case RhsBases(ps, bf, trs) => RhsBases(that :: ps, bf, trs)
    }
    // TODO use inheritance hierarchy to better merge these
    def | (that: BaseTypeOrTag): Opt[RhsNf] = (this, that) match {
      case (RhsBot, p: TypeTag) => S(RhsBases(p::Nil,N,smEmp))
      case (RhsBot, that: MiscBaseType) => S(RhsBases(Nil,S(L(that)),smEmp))
      case (RhsBases(ps, bf, trs), p: ClassTag) =>
        S(RhsBases(if (ps.contains(p)) ps else p :: ps , bf, trs))
      case (RhsBases(ps, N, trs), that: MiscBaseType) => S(RhsBases(ps, S(L(that)), trs))
      case (RhsBases(ps, S(L(t1@TupleType(fs1))), trs), t2@TupleType(fs2)) =>
        if (fs1.size =/= fs2.size) 
          RhsBases(ps, S(L(t1.toArray)), trs) | t2.toArray // upcast tuples of different sizes to array
        else S(RhsBases(ps, S(L(TupleType(fs1.lazyZip(fs2).map {
          case ((S(n1), ty1), (S(n2), ty2)) => (if (n1 === n2) S(n1) else N, ty1 || ty2)
          case ((n1o, ty1), (n2o, ty2)) => (n1o orElse n2o, ty1 || ty2)
        })(noProv))), trs))
      case (RhsBases(ps, S(L(ArrayType(_))), trs), t@TupleType(_)) => this | t.toArray
      case (RhsBases(ps, S(L(t@TupleType(_))), trs), ar@ArrayType(_)) => RhsBases(ps, S(L(t.toArray)), trs) | ar
      case (RhsBases(ps, S(L(ArrayType(ar1))), trs), ArrayType(ar2)) => 
        S(RhsBases(ps, S(L(ArrayType(ar1 || ar2)(noProv))), trs))
      case (RhsBases(_, S(L(_: Without)), _), _) | (_, _: Without) => die // Without should be handled elsewhere
      case (RhsBases(ps, S(L(bt)), trs), _) if (that === bt) => S(this)
      
      // * Note: despite erased first-class polymorphism meaning we no longer have
      // * `(A -> B) & (C -> D) =:= (A | C) -> (B & D)`,
      // * I think we do still have `(A -> B) | (C -> D) =:= (A & C) -> (B | D)`,
      // * because these two types still have no other meaningful LUB.
      case (RhsBases(ps, S(L(FunctionType(l0, r0))), trs), FunctionType(l1, r1)) =>
        S(RhsBases(ps, S(L(FunctionType(l0 & l1, r0 | r1)(noProv))), trs))
      case (RhsBases(ps, S(L(ov @ Overload(fts))), trs), FunctionType(l2, r2)) =>
        S(RhsBases(ps, S(L(Overload(fts.map {
          case ft1  @FunctionType(l1, r1) =>
            FunctionType(l1 & l2, r1 | r2)(ft1.prov)
        })(ov.prov))), trs))
      case (RhsBases(ps, S(L(ft: FunctionType)), trs), ov: Overload) =>
        RhsBases(ps, S(L(ov)), trs) | ft
      
      // * TODO? or it might be counter-productive if it leads to bigger types due by distribution
      // case (RhsBases(ps, S(L(ov1: Overload)), trs), ov2: Overload) => ???
        
      case (RhsBases(_, S(L(_: Overload)), _), _) | (_, _: Overload) =>
        N
      
      case (RhsBases(ps, bf, trs), tt: AbstractTag) =>
        S(RhsBases(if (ps.contains(tt)) ps else tt :: ps, bf, trs))
      case (f @ RhsField(_, _), p: TypeTag) => S(RhsBases(p::Nil, S(R(f)), smEmp))
      case (f @ RhsField(_, _), _: FunctionType | _: ArrayBase) =>
        // S(RhsBases(Nil, S(that), S(f)))
        N // can't merge a record and a function or a tuple -> it's the same as Top
        // NOTE: in the future, if we do actually register fields in named tuples
        //  (so their fields is not pure compiler fiction,
        //    as it is currently and in TypeScript arrays),
        //  we will want to revisit this...
      case
          (RhsBases(_, S(L(_: FunctionType)), _), _: ArrayBase)
        | (RhsBases(_, S(L(_: ArrayBase)), _), _: FunctionType)
        | (RhsBases(_, S(R(_)), _), _: FunctionType | _: ArrayBase)
        => N
      case (RhsBases(_, Some(Left(SpliceType(_))), _), _) | (_, _: SpliceType) => ??? // TODO
    }
    def | (that: (Var, FieldType)): Opt[RhsNf] = this match {
      case RhsBot => S(RhsField(that._1, that._2))
      case RhsField(n1, t1) if n1 === that._1 => S(RhsField(n1, t1 || that._2))
      case RhsBases(p, N, trs) => S(RhsBases(p, S(R(RhsField(that._1, that._2))), trs))
      case RhsBases(p, S(R(RhsField(n1, t1))), trs) if n1 === that._1 =>
        S(RhsBases(p, S(R(RhsField(n1, t1 || that._2))), trs))
      case _: RhsField | _: RhsBases => N
    }
    // def <:< (that: RhsNf)(implicit ctx: Ctx): Bool = this.underlying <:< that.underlying
    def <:< (that: RhsNf)(implicit ctx: Ctx): Bool = (this, that) match {
      case (RhsBases(tags, S(R(fld)), trs), fld2: RhsField) =>
        tags.isEmpty && trs.valuesIterator.forall(_ <:< fld2.underlying) && fld <:< fld2
      case (RhsBases(tags, _, trs), fld2: RhsField) => false
      case (RhsField(nme, fty), RhsBases(tags2, S(R(fld)), trs2)) => this <:< fld
      case (RhsField(nme, fty), RhsBases(tags2, S(L(_)) | N, trs2)) => false
      case (RhsField(nme, fty), RhsField(nme2, fty2)) => nme === nme2 && fty <:< fty2
      case (RhsBases(tags1, res1, trs1), rhs @ RhsBases(tags2, res2, trs2)) =>
        tags1.forall(tag1 =>
          tags2.exists(_.id === tag1.id) // TODO also take parents into account...
        ) && trs1.forall { case (_, tr1) =>
          // tr1 <:< rhs.underlying // * probably not necessary
          trs2.exists { case (_, tr2) => tr1 <:< tr2 }
        } && ((res1, res2) match {
          case (S(L(b)), S(L(b2))) => b <:< b2
          case (N, _) => true
          case _ => false
        })
      case (RhsBot, _) => true
      case (_, RhsBot) => false
    }
    def isBot: Bool = isInstanceOf[RhsBot.type]
  }
  case class RhsField(name: Var, ty: FieldType) extends RhsNf {
    def name_ty: Var -> FieldType = name -> ty
    def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): RhsField =
      RhsField(name, ty.update(self.freshenAbove(lim, _, rigidify = rigidify), self.freshenAbove(lim, _, rigidify = rigidify)))
    override def toString: Str = s"{${name.name}:$ty}"
  }
  case class RhsBases(tags: Ls[TypeTag], rest: Opt[MiscBaseType \/ RhsField], trefs: SortedMap[TypeName, TypeRef]) extends RhsNf {
    def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): RhsBases =
      RhsBases(tags, rest.map(_ match {
        case L(v) => L(v.freshenAboveImpl(lim, rigidify))
        case R(v) => R(v.freshenAbove(lim, rigidify))
      }), trefs.view.mapValues(_.freshenAbove(lim, rigidify)).to(SortedMap))
    override def toString: Str =
      s"${tags.mkString("|")}${rest.fold("")("|" + _.fold(""+_, ""+_))}${trefs.valuesIterator.map("|"+_).mkString}"
  }
  case object RhsBot extends RhsNf {
    def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): this.type = this
    override def toString: Str = "⊥"
  }
  
  
  case class Conjunct(lnf: LhsNf, vars: SortedSet[TypeVariable], rnf: RhsNf, nvars: SortedSet[TypeVariable]) {
    final def compareEquiv(that: Conjunct): Int =
      // trace(s"compareEquiv($this, $that)")(compareEquivImpl(that))(r => s"= $r")
      compareEquivImpl(that)
    final def compareEquivImpl(that: Conjunct): Int = {
      var cmp = lnf.compareEquiv(that.lnf)
      if (cmp =/= 0) return cmp
      cmp = rnf.compareEquiv(that.rnf)
      if (cmp =/= 0) return cmp
      cmp = -vars.sizeCompare(that.vars)
      if (cmp =/= 0) return cmp
      cmp = -nvars.sizeCompare(that.nvars)
      cmp
    }
    def toType(sort: Bool = false): SimpleType =
      toTypeWith(_.toType(sort), _.toType(sort), sort)
    def toTypeWith(f: LhsNf => SimpleType, g: RhsNf => SimpleType, sort: Bool = false): SimpleType =
      ((if (sort) vars.toArray.sorted.iterator else vars.iterator) ++ Iterator(g(rnf).neg())
        ++ (if (sort) nvars.toArray.sorted.iterator else nvars).map(_.neg())).foldLeft(f(lnf))(_ & _)
    lazy val level: Int = levelBelow(MaxLevel)(MutSet.empty)
    def levelBelow(ub: Level)(implicit cache: MutSet[TV]): Level =
      (vars.iterator ++ nvars).map(_.levelBelow(ub)).++(Iterator(lnf.levelBelow(ub), rnf.levelBelow(ub))).max
    def freshenAbove(lim: Int, rigidify: Bool)(implicit ctx: Ctx, freshened: MutMap[TV, ST]): Conjunct = {
      val (vars2, tags2) = vars.toBuffer[TV].partitionMap(
        _.freshenAbove(lim, rigidify) match { case tv: TV => L(tv); case tt: AbstractTag => R(tt); case _ => die })
      val (nvars2, ntags2) = nvars.toBuffer[TV].partitionMap(
        _.freshenAbove(lim, rigidify) match { case tv: TV => L(tv); case tt: AbstractTag => R(tt); case _ => die })
      Conjunct(
        tags2.foldLeft(lnf.freshenAbove(lim, rigidify))(_ & _), vars2.toSortedSet,
        ntags2.foldLeft(rnf.freshenAbove(lim, rigidify))(_ | _), nvars2.toSortedSet)
    }
    def - (fact: Factorizable): Conjunct = fact match {
      case tv: TV => Conjunct(lnf, vars - tv, rnf, nvars)
      case NegVar(tv) => Conjunct(lnf, vars, rnf, nvars - tv)
      case tt: AbstractTag => lnf match {
        case LhsRefined(b, tts, rft, trs) =>
          if (tts(tt)) copy(lnf = LhsRefined(b, tts - tt, rft, trs)) else this
        case LhsTop => this
      }
      case NegAbsTag(tt) => rnf match {
        case RhsBases(tts, r, trs) => copy(rnf = RhsBases(tts.filterNot(_ === tt), r, trs))
        case RhsBot | _: RhsField => this
      }
    }
    def <:< (that: Conjunct)(implicit ctx: Ctx): Bool =
      // trace(s"?? $this <:< $that") {
      that.vars.forall(vars) &&
        lnf <:< that.lnf &&
        that.rnf <:< rnf &&
        that.nvars.forall(nvars)
      // }(r => s"!! $r")
    def & (that: Conjunct, pol: Bool)(implicit ctx: Ctx, etf: ExpandTupleFields): Opt[Conjunct] =
      // trace(s"?? $this & $that ${lnf & that.lnf} ${rnf | that.rnf}") {
      if (lnf <:< that.rnf) N
      else S(Conjunct.mk(lnf & (that.lnf, pol) getOrElse (return N), vars | that.vars
        , rnf | (that.rnf, pol) getOrElse (return N)
        , nvars | that.nvars, pol))
      // }(r => s"!! $r")
    def neg: Disjunct = Disjunct(rnf, nvars, lnf, vars)
    /** `tryMergeUnion` tries to compute the union of two conjuncts as a conjunct,
      * failing if this merging cannot be done without losing information.
      * This ends up simplifying away things like:
      *   {x: int} | {y: int} ~> anything
      *   (A -> B) | {x: C}   ~> anything  */
    def tryMergeUnion(that: Conjunct)(implicit ctx: Ctx, etf: ExpandTupleFields): Opt[Conjunct] = (this, that) match {
      case _ if this <:< that => S(that)
      case _ if that <:< this => S(this)
      case (Conjunct(LhsTop, vs1, r1, nvs1), Conjunct(LhsTop, vs2, r2, nvs2))
        if vs1 === vs2 && nvs1 === nvs2
      =>
        S(Conjunct(LhsTop, vs1, r1 tryMergeInter r2 getOrElse (return N), nvs1))
        // * Conceptually, `tryMergeInter` could return None either because the ThsNfs cannot be merged
        // *  or because merging them would return bottom... but conjuncts cannot represent bottom.
      case (Conjunct(LhsRefined(bse1, ts1, rcd1, trs1), vs1, r1, nvs1)
          , Conjunct(LhsRefined(bse2, ts2, rcd2, trs2), vs2, r2, nvs2))
        if bse1 === bse2 && ts1 === ts2 && vs1 === vs2 && r1 === r2 && nvs1 === nvs2
        && trs1.keySet === trs2.keySet
      =>
        val trs = mergeTypeRefs(true, trs1, trs2)
        val rcd = RecordType(recordUnion(rcd1.fields, rcd2.fields))(noProv)
        S(Conjunct(LhsRefined(bse1, ts1, rcd, trs), vs1, r1, nvs1))
      case (Conjunct(LhsRefined(bse1, ts1, rcd1, trs1), vs1, r1, nvs1)
          , Conjunct(LhsRefined(bse2, ts2, rcd2, trs2), vs2, r2, nvs2))
        if ts1 === ts2 && vs1 === vs2 && r1 === r2 && nvs1 === nvs2
        && trs1 === trs2 // TODO!!
      =>
        val ts = ts1
        
        val rcdU = RecordType(recordUnion(
          if (expandTupleFields) rcd1.fields
            else bse1.map(_.toRecord.fields).fold(rcd1.fields)(recordIntersection(rcd1.fields, _)),
          if (expandTupleFields) rcd2.fields
            else bse2.map(_.toRecord.fields).fold(rcd2.fields)(recordIntersection(rcd2.fields, _)),
        ))(noProv)
        
        // Example:
        //    Why is it sound to merge (A -> B) & {R} | (C -> D) & {S}
        //    into ((A & C) -> (B | D)) & ({R} | {S}) ?
        //  Because the former can be distributed to
        //    (A -> B | C -> D) & (A -> B | {S}) & ({R} | C -> D) & ({R} | {S})
        //    == ((A & C) -> (B | D)) & Top & Top & ({R} | {S})
        (bse1, bse2) match {
          case (S(FunctionType(l1, r1)), S(FunctionType(l2, r2))) => // TODO Q: records ok here?!
            S(Conjunct(
              LhsRefined(S(FunctionType(l1 & l2, r1 | r2)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
          case (S(tup1 @ TupleType(fs1)), S(tup2 @ TupleType(fs2))) => // TODO Q: records ok here?!
            if (fs1.size =/= fs2.size) S(Conjunct(
              LhsRefined(S(ArrayType(tup1.inner || tup2.inner)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
            else S(Conjunct(
              LhsRefined(S(TupleType(tupleUnion(fs1, fs2))(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
          case (S(tup @ TupleType(fs)), S(ArrayType(ar))) =>
            S(Conjunct(LhsRefined(S(ArrayType(tup.inner || ar)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
          case (S(ArrayType(ar)), S(tup @ TupleType(fs))) =>
            S(Conjunct(
              LhsRefined(S(ArrayType(tup.inner || ar)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
          case (S(ArrayType(ar1)), S(ArrayType(ar2))) =>
            S(Conjunct(LhsRefined(S(ArrayType(ar1 || ar2)(noProv)), ts, rcdU, trs1), vs1, RhsBot, nvs1))
          case (N, N)
            | (S(_: FunctionType), S(_: ArrayBase)) | (S(_: ArrayBase), S(_: FunctionType))
          =>
            S(Conjunct(LhsRefined(N, ts, rcdU, trs1), vs1, RhsBot, nvs1))
          case _ => N
        }
        case _ => N
      }
    private lazy val mkString: Str =
      (Iterator(lnf).filter(_ =/= LhsTop) ++ vars
        ++ (Iterator(rnf).filter(_ =/= RhsBot) ++ nvars).map("~("+_+")")).mkString("∧")
    override def toString: Str = mkString
  }
  
  object Conjunct {
    def of(tvs: SortedSet[TypeVariable]): Conjunct = Conjunct(LhsTop, tvs, RhsBot, ssEmp)
    def mk(lnf: LhsNf, vars: SortedSet[TypeVariable], rnf: RhsNf, nvars: SortedSet[TypeVariable], pol: Bool)(implicit ctx: Ctx, etf: ExpandTupleFields): Conjunct = {
      Conjunct(lnf, vars, rnf match {
        case RhsField(name, ty) => RhsField(name, ty)
        case RhsBases(prims, bf, trs) =>
          RhsBases(prims.filter(lnf & (_, pol) pipe (_.isDefined)), bf.filter {
            case L(b) => lnf & (b, pol) pipe (_.isDefined)
            case R(r) => true
          }, trs)
        case RhsBot => RhsBot
      }, nvars)
    }
    /** Scala's standard library is weird. I would have normally made Conjunct extend Ordered[Conjunct],
      * but the contract of Ordered says that `equals` and `hashCode` should be "consistent" with `compare`,
      * which I understand as two things comparing to 0 HAVING to be equal and to have the same hash code...
      * But achieving this is very expensive for general type forms.
      * All we want to do here is to define an ordering between implicit equivalence classes
      * whose members are not necessarily equal. Which is fine since we only use this to do stable sorts. */
    implicit object Ordering extends Ordering[Conjunct] {
      def compare(x: Conjunct, y: Conjunct): Int = x.compareEquiv(y)
    }
  }
  
  
  case class Disjunct(rnf: RhsNf, vars: SortedSet[TypeVariable], lnf: LhsNf, nvars: SortedSet[TypeVariable]) {
    def neg: Conjunct = Conjunct(lnf, nvars, rnf, vars)
    def | (that: Disjunct, pol: Bool)(implicit ctx: Ctx, etf: ExpandTupleFields): Opt[Disjunct] =
      S(Disjunct(rnf | (that.rnf, pol) getOrElse (return N), vars | that.vars,
        lnf & (that.lnf, pol) getOrElse (return N), nvars | that.nvars))
    override def toString: Str =
      (Iterator(rnf).filter(_ =/= RhsBot) ++ vars
        ++ (Iterator(lnf).filter(_ =/= LhsTop) ++ nvars).map("~"+_)).mkString("∨")
  }
  
  object Disjunct {
    def of(tvs: SortedSet[TypeVariable]): Disjunct = Disjunct(RhsBot, tvs, LhsTop, ssEmp)
  }
  
  
  /** `polymLevel` denotes the level at which this type is quantified (MaxLevel if it is not) */
  case class DNF(polymLevel: Int, cons: Constrs, cs: Ls[Conjunct]) {
    assert(polymLevel <= MaxLevel, polymLevel)
    private def levelBelow(ub: Level): Level =
      cs.iterator.map(_.levelBelow(ub)(MutSet.empty)).maxOption.getOrElse(MinLevel)
    lazy val levelBelowPolym = levelBelow(polymLevel)
    def isBot: Bool = cs.isEmpty
    def toType(sort: Bool = false): SimpleType = ConstrainedType.mk(cons, if (cs.isEmpty) BotType else {
      val css = if (sort) cs.sorted else cs
      PolymorphicType.mk(polymLevel, css.map(_.toType(sort)).foldLeft(BotType: ST)(_ | _))
    })
    lazy val level: Level =
      cs.maxByOption(_.level).fold(MinLevel)(_.level)
    def isPolymorphic: Bool = level > polymLevel
    lazy val effectivePolymLevel: Level = if (isPolymorphic) polymLevel else level
    def instantiate(implicit ctx: Ctx, shadows: Shadows): (Constrs, Ls[Conjunct]) =
      if (isPolymorphic) {
        implicit val state: MutMap[TV, ST] = MutMap.empty
        (
          cons.map { case (l, r) => (
            l.freshenAbove(polymLevel, rigidify = false),
            r.freshenAbove(polymLevel, rigidify = false)
          )},
          cs.map(_.freshenAbove(polymLevel, rigidify = false))
        )
      } else (cons, cs)
    def rigidify(implicit ctx: Ctx, shadows: Shadows): Ls[Conjunct] =
      if (isPolymorphic) {
        implicit val state: MutMap[TV, ST] = MutMap.empty
        cs.map(_.freshenAbove(polymLevel, rigidify = true))
      } else cs
    def & (that: DNF, pol: Bool)(implicit ctx: Ctx, etf: ExpandTupleFields): DNF = {
      val (newLvl, thisCs, thatCs, thisCons, thatCons) = levelWith(that)
      thatCs.map(DNF(newLvl, thisCons ::: thatCons, thisCs) &
        (_, pol)).foldLeft(DNF.extr(false))(_ | _)
    }
    /** Returns new DNF components for `this` and `that`
      * with their polymorphism levels harmonized to a single level. */
    private def levelWith(that: DNF)(implicit ctx: Ctx)
          : (Level, Ls[Conjunct], Ls[Conjunct], Constrs, Constrs) = {
      // println(s"--- $levelBelowPolym ${that.polymLevel} ${that.levelBelow(polymLevel)}")
      
      implicit val freshened: MutMap[TV, ST] = MutMap.empty
      
      // * Some easy cases to avoid having to adjust levels when we can:
      if (levelBelowPolym <= that.polymLevel && that.levelBelowPolym <= polymLevel)
        (polymLevel min that.polymLevel, cs, that.cs, cons, that.cons)
      else if (levelBelow(that.polymLevel) <= polymLevel
          && levelBelowPolym <= that.polymLevel)
        (that.polymLevel, cs, that.cs, cons, that.cons)
      else if (that.levelBelow(polymLevel) <= that.polymLevel
          && that.levelBelowPolym <= polymLevel)
        (polymLevel, cs, that.cs, cons, that.cons)
      
      // * The two difficult cases:
      else if (that.polymLevel > polymLevel) ctx.copy(lvl = that.polymLevel + 1) |> {
          implicit ctx =>
        assert((polymLevel max that.polymLevel) === that.polymLevel)
        (polymLevel max that.polymLevel,
          cs.map(_.freshenAbove(polymLevel, rigidify = false)),
          that.cs,
          cons.mapKeys(_.freshenAbove(polymLevel, rigidify = false))
            .mapValues(_.freshenAbove(polymLevel, rigidify = false)),
          that.cons
        )
      }
      else if (polymLevel > that.polymLevel) ctx.copy(lvl = polymLevel + 1) |> {
          implicit ctx =>
        assert((polymLevel max that.polymLevel) === polymLevel)
        (polymLevel max that.polymLevel,
          cs,
          that.cs.map(_.freshenAbove(that.polymLevel, rigidify = false)),
          cons,
          that.cons.mapKeys(_.freshenAbove(polymLevel, rigidify = false))
            .mapValues(_.freshenAbove(polymLevel, rigidify = false)),
        )
      }
      
      // * One more easy case:
      else (polymLevel, cs, that.cs, cons, that.cons) ensuring (that.polymLevel === polymLevel)
    }
    def | (that: DNF)(implicit ctx: Ctx, etf: ExpandTupleFields): DNF = {
      val (newLvl, thisCs, thatCs, thisCons, thatCons) = levelWith(that)
      // println(s"-- $polymLevel ${that.polymLevel} $newLvl")
      thatCs.foldLeft(DNF(newLvl, thisCons ::: thatCons, thisCs))(_ | _)
      // ^ Note: conjuncting the constrained-type constraints here is probably the wrong thing to do...
    }
    def & (that: Conjunct, pol: Bool)(implicit ctx: Ctx, etf: ExpandTupleFields): DNF =
      DNF(polymLevel, cons, cs.flatMap(_ & (that, pol))) // TODO may need further simplif afterward
    def | (that: Conjunct)(implicit ctx: Ctx, etf: ExpandTupleFields): DNF = {
      def go(cs: Ls[Conjunct], acc: Ls[Conjunct], toMerge: Conjunct): Ls[Conjunct] = 
        // trace(s"go?? $cs $acc M $toMerge") {
        cs match {
        case c :: cs =>
          if (c <:< toMerge) acc.reverse ::: toMerge :: cs
          else if (toMerge <:< c) acc.reverse ::: c :: cs
          else c.tryMergeUnion(toMerge) match {
            case Some(value) => acc.reverse ::: value :: cs
            case None => go(cs, c :: acc, toMerge)
          }
        case Nil => (toMerge :: acc).reverse
      }
      // }(r => s"go!! $r")
      DNF(polymLevel,
        cons, // FIXME?!
        go(cs, Nil, that))
    }
    override def toString: Str = s"DNF($polymLevel, ${cs.mkString(" | ")})${
      if (cons.isEmpty) ""
      else s"{${cons.mkString(", ")}}"
    }"
  }
  
  object DNF {
    def of(polymLvl: Level, cons: Constrs, lnf: LhsNf): DNF =
      of(polymLvl, cons, Conjunct(lnf, ssEmp, RhsBot, ssEmp) :: Nil)
    def of(polymLvl: Level, cons: Constrs, cs: Ls[Conjunct]): DNF = {
      val res = DNF(polymLvl, cons, cs)
      val epl = res.effectivePolymLevel
      if (epl < polymLvl) res.copy(polymLevel = epl)
      else res
    }
    def extr(dir: Bool): DNF = if (dir) of(MinLevel, Nil, LhsTop) else DNF(MinLevel, Nil, Nil)
    def merge(dir: Bool, pol: Bool)(l: DNF, r: DNF)(implicit ctx: Ctx, etf: ExpandTupleFields): DNF =
      if (dir) l | r else l & (r, pol)
    
    def mkDeep(polymLvl: Level, cons: Constrs, ty: SimpleType, pol: Bool)
          (implicit ctx: Ctx, ptr: PreserveTypeRefs = false, etf: ExpandTupleFields = true, expandedTVs: Set[TV] = Set.empty): DNF = {
      mk(polymLvl, cons, mkDeepST(polymLvl, cons, ty, pol), pol)
    }
    def mkDeepST(polymLvl: Level, cons: Constrs, ty: SimpleType, pol: Bool)
          (implicit ctx: Ctx, ptr: PreserveTypeRefs = false, etf: ExpandTupleFields = true): ST =
            // trace(s"mkDeepST[$pol,$polymLvl](${ty})") {
              ty match {
      case ProvType(und) =>
        mkDeepST(polymLvl, cons, und, pol).withProv(ty.prov)
      case TypeBounds(lb, ub) => mkDeepST(polymLvl, cons, if (pol) ub else lb, pol).withProv(ty.prov)
      case _ =>
        val dnf = mk(polymLvl, cons, ty, pol)
        def go(polo: Opt[Bool], st: ST): ST = polo match {
          case _ if st === ty => ty.mapPol(polo)(go)
          case S(pol) => mkDeepST(polymLvl, cons, st, pol)(ctx, ptr = true, etf = false)
          case N => TypeBounds.mk(
            mkDeepST(polymLvl, cons, st, false)(ctx, ptr = true, etf = false),
            mkDeepST(polymLvl, cons, st, true)(ctx, ptr = true, etf = false))
        }
        dnf.toType().mapPol(S(pol))(go)
    }
    // }(r => s"= $r")
    
    def mk(polymLvl: Level, cons: Constrs, ty: SimpleType, pol: Bool)(implicit ctx: Ctx, ptr: PreserveTypeRefs = false, etf: ExpandTupleFields = true, expandedTVs: Set[TV] = Set.empty): DNF =
        // trace(s"DNF[${printPol(pol)},$ptr,$etf,$polymLvl](${ty})") {
        (if (pol) ty.pushPosWithout else ty) match {
      case bt: BaseType => DNF.of(polymLvl, cons, LhsRefined(S(bt), ssEmp, if (expandTupleFields) bt.toRecord else RecordType.empty, smEmp))
      case tt: AbstractTag => DNF.of(polymLvl, cons, LhsRefined(N, SortedSet.single(tt), RecordType.empty, smEmp))
      case rcd: RecordType => DNF.of(polymLvl, cons, LhsRefined(N, ssEmp, rcd, smEmp))
      case ExtrType(pol) => extr(!pol)
      case ty @ ComposedType(p, l, r) => merge(p, pol)(mk(polymLvl, cons, l, pol), mk(polymLvl, cons, r, pol))
      case NegType(und) => DNF.of(polymLvl, cons, CNF.mk(polymLvl, Nil, und, !pol).ds.map(_.neg))
      case tv @ AssignedVariable(ty) if !preserveTypeRefs && !expandedTVs.contains(tv) =>
        (expandedTVs + tv) |> { implicit expandedTVs => DNF.mk(polymLvl, cons, ty, pol) }
      case tv: TypeVariable => DNF.of(polymLvl, cons, Conjunct.of(SortedSet.single(tv)) :: Nil)
      case ProxyType(underlying) => mk(polymLvl, cons, underlying, pol)
      case tr @ TypeRef(defn, targs) =>
        // * TODO later: when proper TypeRef-based simplif. is implemented, can remove this special case
        if (preserveTypeRefs && !primitiveTypes.contains(defn.name) || !tr.canExpand) {
          of(polymLvl, cons, LhsRefined(tr.mkClsTag, ssEmp, RecordType.empty, SortedMap(defn -> tr)))
        } else mk(polymLvl, cons, tr.expandOrCrash, pol)
      case TypeBounds(lb, ub) => mk(polymLvl, cons, if (pol) ub else lb, pol)
      case PolymorphicType(lvl, bod) => mk(lvl, cons, bod, pol)
      case ConstrainedType(cs, bod) => mk(polymLvl, cs ::: cons, bod, pol)
    }
    // }(r => s"= $r")
  }
  
  
  case class CNF(ds: Ls[Disjunct]) {
    def & (that: CNF): CNF = that.ds.foldLeft(this)(_ & _)
    def | (that: CNF, pol: Bool)(implicit ctx: Ctx, etf: ExpandTupleFields): CNF = that.ds.map(this | (_, pol)).foldLeft(CNF.extr(false))(_ & _)
    def & (that: Disjunct): CNF =
      // TODO try to merge it with the others if possible
      CNF(that :: ds)
    def | (that: Disjunct, pol: Bool)(implicit ctx: Ctx, etf: ExpandTupleFields): CNF = CNF(ds.flatMap(_ | (that, pol)))
    override def toString: Str = s"CNF(${ds.mkString(" & ")})"
  }
  
  object CNF {
    def of(rnf: RhsNf): CNF = CNF(Disjunct(rnf, ssEmp, LhsTop, ssEmp) :: Nil)
    def of(bt: BaseType): CNF =
      CNF.of(RhsBot | bt getOrElse (return CNF.extr(true)))
    def of(tvs: SortedSet[TypeVariable]): CNF = CNF(Disjunct.of(tvs) :: Nil)
    def of(rcd: RecordType): CNF = CNF(rcd.fields.iterator.map(f =>
      Disjunct(RhsField(f._1, f._2), ssEmp, LhsTop, ssEmp)).toList)
    def extr(pol: Bool): CNF = if (pol) CNF(Nil) else of(RhsBot)
    def merge(pol: Bool)(l: CNF, r: CNF)(implicit ctx: Ctx, etf: ExpandTupleFields): CNF = if (pol) l | (r, pol) else l & r
    def mk(polymLvl: Level, cons: Constrs, ty: SimpleType, pol: Bool)(implicit ctx: Ctx, ptr: PreserveTypeRefs, etf: ExpandTupleFields, expandedTVs: Set[TV] = Set.empty): CNF =
      // trace(s"?CNF $ty") {
      ty match {
        case bt: BaseType => of(bt)
        case tt: AbstractTag => of(RhsBases(tt :: Nil, N, smEmp))
        case rt @ RecordType(fs) => of(rt)
        case ExtrType(pol) => extr(!pol)
        case ty @ ComposedType(p, l, r) => merge(p)(mk(polymLvl, cons, l, pol), mk(polymLvl, cons, r, pol))
        case NegType(und) => CNF(DNF.mk(polymLvl, cons, und, !pol).cs.map(_.neg))
        case tv @ AssignedVariable(ty) if !preserveTypeRefs && !expandedTVs.contains(tv) =>
          (expandedTVs + tv) |> { implicit expandedTVs => CNF.mk(polymLvl, cons, ty, pol) }
        case tv: TypeVariable => of(SortedSet.single(tv))
        case ProxyType(underlying) => mk(polymLvl, cons, underlying, pol)
        case tr @ TypeRef(defn, targs) =>
          if (preserveTypeRefs && !primitiveTypes.contains(defn.name) || !tr.canExpand) {
            CNF(Disjunct(RhsBases(Nil, N, SortedMap.single(defn -> tr)), ssEmp, LhsTop, ssEmp) :: Nil)
          } else mk(polymLvl, cons, tr.expandOrCrash, pol)
        case TypeBounds(lb, ub) => mk(polymLvl, cons, if (pol) ub else lb, pol)
        case PolymorphicType(lvl, bod) => mk(lvl, cons, bod, pol)
        case ConstrainedType(cs, bod) => mk(lvl, cs ::: cons, bod, pol)
      }
      // }(r => s"!CNF $r")
  }
  
  
}
