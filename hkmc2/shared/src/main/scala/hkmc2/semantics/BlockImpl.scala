package hkmc2
package semantics

import mlscript.utils.*, shorthands.*
import syntax.Tree.*
import hkmc2.syntax.TypeOrTermDef


trait BlockImpl:
  self: Block =>
  
  val desugStmts = stmts.map(_.desugared)
  
  val definedSymbols: Array[Str -> BlockMemberSymbol] =
    desugStmts
      .flatMap:
        case td: syntax.TypeOrTermDef =>
          td.name match
            case L(_) => Nil
            case R(id) =>
              id.name -> R(td) :: (
                td.symbName match
                case S(sid: Ident) => id.name -> L(sid.name) :: Nil
                case _ => Nil
              )
        case _ => Nil
      .groupMap(_._1)(_._2).flatMap:
        case (nme, snmes_tds) =>
          val (symNmes, tds) = snmes_tds.partitionMap(identity)
          val sym = BlockMemberSymbol(nme, tds)
          nme -> sym :: symNmes.map(_ -> sym)
      .toArray.sortBy(_._1)
  
end BlockImpl


