package hkmc2
package typing

import scala.collection.mutable

import mlscript.utils.*, shorthands.*
import Message.MessageContext
import semantics.*, semantics.Term.*

import Producer as P
import Consumer as C
import Label as L
import hkmc2.syntax.Tree


class TypeChecker(using Raise, Elaborator.State):
  
  // val uid = Uid.FlowPoint.State()
  
  // def typeStat(s: Statement): Producer = t match
  
  def typeProd(t: Term): Producer = t match
    case Ref(sym: VarSymbol) =>
      val rc = sym.refsNumber
      // assert(rc > 0) // FIXME
      if rc === 1 then P.Flow(sym)
      else P.Lab(P.Flow(sym), L.Exit(sym, rc, false))
    case Ref(cls: ClassSymbol) => P.Ctor(cls, Nil)
    case Ref(cls: ModuleSymbol) => P.Ctor(cls, Nil)
    case Ref(ts: TermSymbol) =>
      ts.defn match
        case S(td: TermDefinition) =>
          td.params match
            case Nil => P.Flow(td.resSym)
    case Blk(stats, res) =>
      // val p1 = stats.map(typeStat)
      // val p2 = typeProd(res)
      // p1 ::: p2 :: Nil
      // assert(stats.isEmpty, stats) // TODO
      // TODO(stats, stats.nonEmpty) // TODO
      stats.foreach:
        case t: TermDefinition =>
          t.sign.map(typeProd)
          t.params.map(_.params).map(typeParams)
          t.body.map(typeProd)
          P.Ctor(LitSymbol(Tree.UnitLit(true)), Nil)
        case t: Term =>
          typeProd(t)
        case _: ClassDef =>
          // println(s"TODO ${t.showDbg}")
          // TODO
        case _: ModuleDef =>
          // TODO
      typeProd(res)
    case Lit(lit) =>
      P.Ctor(LitSymbol(lit), Nil)
    case app @ App(r @ Ref(ts: TermSymbol), tup @ Tup(args)) =>
      val rc = ts.refsNumber
      assert(rc > 0)
      ts.defn match
      case S(td: TermDefinition) =>
        td.params match
          case Nil =>
            val f = typeProd(r)
            constrain(P.exitIf(f, ts, r.refNum, rc), C.Fun(typeProd(tup), C.Flow(app.resSym)))
          case ParamList(_, ps) :: Nil =>
            // App applies to the leftmost parameter list
            // TODO: how to recursively check the subsequent Apps (if any)?
            if ps.size != args.size then
              raise(ErrorReport(
                msg"Expected ${ps.size.toString} arguments, but got ${
                  args.size.toString}" -> t.toLoc :: Nil))
            // val p1 = ps.zip(args).map: (p, a) =>
            val p1 = ps.zip(args).foreach:
              case (p, a: Fld) =>
                constrain(P.enterIf(typeProd(a.term), ts, r.refNum, rc), C.Flow(p.sym.asInstanceOf/*FIXME*/))
            constrain(P.Flow(td.resSym), C.Flow(app.resSym))
        // P.Flow(td.resSym)
        P.Flow(app.resSym)
    case App(lhs, rhs) =>
      val c = C.Fun(typeProd(lhs), typeCons(rhs))
      ???
    case FunTy(lhs, rhs, _) =>
      P.Fun(typeCons(lhs), typeProd(rhs), Nil)
    // case Ref(ClassSymbol(Ident("true"))) =>
    //   P.Ctor(LitSymbol(Tree.UnitLit(true)), Nil)
    case Tup(fields) =>
      P.Ctor(TupSymbol(S(fields.size)), fields.map:
        case f: Fld => typeProd(f.term))
    case Error =>
      P.Ctor(Extr(false), Nil)
    case _ => P.Flow(FlowSymbol("TODO")) // TODO
  
  def typeParams(ps: Ls[Param]): Ls[(C, P)] =
    ps.map: p =>
      (C.Flow(p.sym.asInstanceOf/*FIXME*/), P.Flow(p.sym.asInstanceOf/*FIXME*/))
  
  def typeCons(t: Term): Consumer = t match
    case Ref(sym: VarSymbol) => C.Flow(sym)
    case Ref(cls: ClassSymbol) => C.Ctor(cls, Nil)
    case Ref(ts: TermSymbol) => ???
    case Tup(fields) =>
      C.Ctor(TupSymbol(S(fields.size)), fields.map:
        case f: Fld => typeCons(f.term))
    // case _ => TODO(t)
  
  case class CCtx(path: Ls[L])
  
  def constrain(lhs: P, rhs: C): Unit = constrain(lhs, Nil, Nil, rhs)(CCtx(Nil))
  
  // def constrain(lhs: P, path: Path, rhs: C): Unit = (lhs, rhs) match
  def constrain(lhs: P, exits: Ls[L.Exit], enter: Ls[L.Enter], rhs: C)(implicit cctx: CCtx): Unit = (lhs, rhs) match
    case (P.Lab(b, l), _) =>
      // constrain(b, l :: path, rhs)
      // constrain(b, ???, ???, rhs)
      // println(s"TODO $lhs")
      constrain(b, exits, enter, rhs) // FIXME
    case (P.Flow(sym), C.Flow(sym2)) =>
      sym.outFlows += sym2
    case (P.Flow(sym), rhs) =>
      sym.outFlows2 += rhs
    case (P.Ctor(sym, args), C.Flow(sym2)) =>
      sym2.inFlows += ConcreteProd(Path.Plain(Nil), P.Ctor(sym, args))
    case (P.Fun(lhs1, rhs1, caps), C.Fun(lhs2, rhs2)) =>
      // val p1 = constrain(lhs2, path, lhs1)
      // val p2 = constrain(rhs1, path, rhs2)
      // caps.foreach((p, c) => constrain(p, path, c))
      def loop(exits: Ls[L.Exit], enter: Ls[L.Enter]): Unit = exits match
        case Nil =>
          enter match
            case Nil =>
              val p1 = constrain(lhs2, exits, enter, lhs1)
              val p2 = constrain(rhs1, exits, enter, rhs2)
              caps.foreach((p, c) => constrain(p, exits, enter, c))
            case e :: enters =>
              
              loop(exits, enters)
        case e :: exits =>
          
          loop(exits, enter)
      loop(exits, enter)
    // case _ => ???




