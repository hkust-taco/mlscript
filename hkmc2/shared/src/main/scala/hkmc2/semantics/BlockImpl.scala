package hkmc2
package semantics

import hkmc2.utils.*, shorthands.*
import syntax.Tree
import syntax.Tree.*
import hkmc2.syntax.{PossiblyAnnotated, TypeOrTermDef}


trait BlockImpl(using Elaborator.State):
  self: Block =>
  
  def withStmts(newStmts: Ls[Tree]): Block =
    if newStmts is stmts then this else Block(newStmts).withLocOf(this)
  
  def :+(stmt: Tree): Block =
    Block(stmts :+ stmt).withLocOf(self.mkLocWith(stmt))
  
  val desugStmts =
    def desug(stmts: Ls[Tree]): Ls[Tree] =
      stmts match
      case syntax.Desugared(PossiblyAnnotated(anns, Assert(kw, cond, N, els))) :: stmts =>
        PossiblyAnnotated(anns, Assert(kw, cond, S(Block(stmts)), els)) :: Nil
      case syntax.Desugared(PossiblyAnnotated(anns, td: TypeDef)) :: stmts =>
        val ctors = td.withPart.toList.flatMap:
          case Block(sts) => sts.flatMap:
            case Constructor(Block(ctors)) => ctors
            case _ => Nil
          case _ => Nil
        // A temporary solution for ADTs, which desugars ADTs to normal class definitions.
        // This will be removed after we truly support ADTs correctly.
        // TODO: No raise contextual variable. Only `Error` nodes are returned if there is an error. 
        lazy val (headId, headPs) = td.baseHead match
          case id: Ident => (id, Nil)
          case App(id: Ident, TyTup(ps)) => (id, ps)
          case _ => TODO(s"unexpected ADT head shape: ${td.baseHead}")
        // Temporarily use `data` annotation to distinguish the following ctors:
        // - Ctor(...)
        // - Ctor[...](...) extends ADT[...]
        // since the former will be desugared to `class Ctor[...](...) extends ADT[...]`,
        // where `Ctor[...]` and `ADT[...]` share the same type parameter list
        def getPossibleGenericAnns(decl: Tree, anns: Ls[Tree]) = decl match
          case InfixApp(_, Keywrd(syntax.Keyword.`extends`), _) =>
            Keywrd(syntax.Keyword.data) :: anns
          case _ => anns
        // Generate `extends` suffix if it is not provided by users
        // Also check if the number of type parameters is correct
        def genExt(decl: Tree) = decl match
          case InfixApp(_, Keywrd(syntax.Keyword.`extends`), ext) => ext match
            case _: Ident if headPs.isEmpty => ext
            case App(id: Ident, TyTup(ps)) if id.name == headId.name && ps.length == headPs.length => ext
            case _ => Error()
          case _ => headPs match
            case Nil => headId
            case ps =>
              App(headId, TyTup(ps.map {
                case m @ Modified(Keywrd(syntax.Keyword.`in`) | Keywrd(syntax.Keyword.`out`), _) => m
                case t => Tup(Tree.Modified(Keywrd(syntax.Keyword.`in`), t) :: Tree.Modified(Keywrd(syntax.Keyword.`out`), t) :: Nil)
              }))
        // Insert type parameters for constructors.
        // e.g. `class Foo[T] with constructor Bar(x: T)` will be desugared to
        // `class Bar[T](x: T) extends Foo[T]`
        // Otherwise, the elaborator will complain `T` is not defined.
        def genCtorHead(decl: Tree) = decl match
          case InfixApp(decl, Keywrd(syntax.Keyword.`extends`), _) => decl // check will be applied in genExt
          case App(_: Ident, tup: TyTup) => Error()
          case App(id: Ident, ps: Tup) => App(App(id, TyTup(headPs)), ps)
          case id: Ident => App(id, TyTup(headPs))
          case _ => Error()
        // Only fields modified by `val` can be extracted by pattern matching.
        // For ADTs, all fields can be extracted, but we don't want to add `val`s manumally.
        def insertVal(decl: Tree): Tree = decl match
          case id: Ident => id
          case App(f, Tup(ps)) => App(f, Tup(ps.map(p => TermDef(syntax.ImmutVal, p, N))))
          case App(f, tup: TyTup) => App(insertVal(f), tup)
          case _ => Error()
        PossiblyAnnotated(anns, td) :: (
          ctors.map(head => PossiblyAnnotated(getPossibleGenericAnns(head, anns), TypeDef(syntax.Cls,
            td.name match
                case L(_) => head
                case R(name) =>
                  InfixApp(insertVal(genCtorHead(head)), Keywrd(syntax.Keyword.`extends`), genExt(head))
            , N)))
        ) ::: desug(stmts)
      case stmt :: stmts =>
        stmt.desugared match
        case PossiblyAnnotated(anns, h @ Hndl(body = N)) =>
          PossiblyAnnotated(anns, h.copy(body = S(Block(stmts)))) :: Nil
        case stmt => stmt :: desug(stmts)
      case Nil => Nil
    desug(stmts)
  
  val definedSymbols: Array[Str -> BlockMemberSymbol] =
    desugStmts
      .flatMap:
        case PossiblyAnnotated(_, td: syntax.TypeOrTermDef) =>
          td.name match
            case L(_) => Nil
            case R(id) =>
              id.name -> R(td) :: (
                td.symbName match
                case S(R(sid)) => id.name -> L(sid.name) :: Nil
                case _ => Nil
              )
        case _ => Nil
      .groupMap(_._1)(_._2).flatMap:
        case (nme, snmes_tds) =>
          val (symNmes, tds) = snmes_tds.partitionMap(identity)
          val sym = new BlockMemberSymbol(nme, tds)
          sym.sourceAliases = symNmes
          nme -> sym :: symNmes.map(_ -> sym)
      .toArray.sortBy(_._1)
  
end BlockImpl


