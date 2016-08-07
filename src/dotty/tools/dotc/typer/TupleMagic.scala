package dotty.tools.dotc.typer

import dotty.tools.dotc.ast.{tpd, untpd}
import dotty.tools.dotc.ast.Trees.{Apply, Select}
import dotty.tools.dotc.ast.tpd.MaybePoly
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Symbols._
import dotty.tools.dotc.core.StdNames._
import dotty.tools.dotc.core.Types._
import dotty.tools.dotc.core.Decorators._
import dotty.tools.dotc.core.Denotations._
import dotty.tools.dotc.typer.ErrorReporting._

/**
  * This object handles various magic operations relating to tuples.
  *
  *   The goal of these magics is to make tuples feel more open and intuitive.
  *
  *    Assign must be handled by the Typer because update methods can have return types.
  *    Tuples are uniquely involved in assign in various ways:
  *      1. Right hand side of curried update method can be a Tuple that requires un-tuple. X(1) = (2,3)
  *      2. Possible update variable in a tuple. (a,b) = (1,2)
  *
  *    The tendrils of TupleMagics are spread throughout the compiler, the goal of this object is to collect them in one place.
  *      And to keep the rest of the compiler code pure of its abominate rituals.
  *
  *      define:
  *        UnTuple : to take args out of an untpd.Tuple
  *        SplitTuple : to access t._1,t._2,t._3 etc.
  */
object TupleMagic {

  //COMPLETED:
  // curried update method
  // assign accros (nested) tuples
  // split tuples into update(a,b)(x,y,z)
  // () as empty tuple for varargs falls out automagically
  // untuple of functions (i.e. function (A,B)=>C is also Tuple2[A,B]=>C)
  // support swap syntax (a,b) = (b,a)
  //IN PROGRESS:
  // todo handle | types... i.e. PolyType()
  // todo check behaiours of call-by-name update in every case
  // todo make sure x.setter_= methods also work
  // todo write comprehensive tests
  // todo investigate the List(a,b,c):_* issue
    //todo make sure List(a,b,c):_* works in nested tuples
  //DELIBERATION:
  // todo: find Tuple extractor/unapply implemenation to check for code duplication
  // todo allow  _ in assignment into LHS tuples
  // todo avoid redundant hold of RHS tuple value
  // todo: product/tuple OR type, i.e. (Int,Int)#OR =:= Int
  //CANCLED:
  // partial var/val declaration inside assignment over tuples
     // looks very ugly and internal val a,b,c = 3 would be horrible.
  // no generalization to CaseClass(a,b) = (1,2) since that calls into CaseClass$.update(a,b)(1,2), while (a,b) = (1,2) was just a parsing error.
  // allow method1(a,b,c); method2()=(a,b,c); method1(method2())
    //on second thought, better not due to ambiguity
    //update method is special case due to syntax of assignments
  //////////

  /** @return whether or not typedTree is a Tuple
    */
  def isTuple(typedTree:tpd.Tree)
             (implicit ctx: Context):Boolean = {
    def unExpr(wrapped:Type) = wrapped match {
      case ExprType(resTpe) => defn.isTupleType(resTpe) /*def xx:(A,B); (a,b) = xx*/
      case tpe: RefinedType => defn.isTupleType(tpe)    /*val xx:(A,B); (a,b) = xx*/
      case _tpe => unexpected(_tpe) /*???*/
    }
    def unexpected(tpe:Type) = { //this is a debugging method
      ctx.error(s"RHS type is probably not a Tuple: ${tpe.show}")
      ctx.error(s"And direct tuple check returns: ${defn.isTupleType(tpe)}")
      defn.isTupleType(tpe)
    }
    //todo: there should be a more generic extractor to deal with this somewhere...
    typedTree.tpe match {
      case ntpe:NamedType => ntpe.denot match {
        //case symDenot:SymDenotation => unExpr(symDenot.info)
        case sngDenot:SingleDenotation => unExpr(sngDenot.infoOrCompleter)
        case _den =>
          ctx.error(s"RHS denotation not a SingleDenotation, what does this mean?!: ${_den.show}");
          false
      }
      case tpe:RefinedType => defn.isTupleType(tpe)
      case tpe => unexpected(tpe) /*???*/
    }
  }

  /** @ruturn ( val hold = tuple() , List(hold._1,hold._2,...) )
    */
  def splitTuple(tuple:tpd.Tree)
                (implicit ctx: Context):(untpd.ValDef,List[untpd.Select]) = {
    val name = ctx.freshName().toTermName
    val hold = untpd.Ident(name)
    //todo: it sees silly to make this ValDef out of untpd.TypedSplices, but idk how to properly construct tpd.ValDef
    (untpd.ValDef(name,untpd.TypedSplice(tpd.TypeTree(tuple)),untpd.TypedSplice(tuple)),
      tuple.tpe.fields.indices/*this is a bit sketchy*/
        .map(i=>untpd.Select(hold,nme.productAccessorName(1 + i))).toList)
  }

  /** This method is called in typechecker because update methods can have a ruturn type.
    *
    * It handles assignment involving either update methods or RHS tuples.
    *  This is done by reshaping the tree.
    *
    * Note: much of this handling is done recursively:
    *   LHS tuple assingmentmets split appart,
    *   then typechecker is called again on individual parts which could be split further.
    */
  def assignmentMagic(tree: untpd.Assign, pt: Type)
                     (implicit ctx: Context):Option[tpd.Tree] = {

    /** Assignment with tuple on LHS: (a,b,c) = ...
      */
    def assignSplitTuple(lhs:untpd.Tuple,rhs:untpd.Tree):untpd.Tree = {
      //no eager splitting of untpd.Tuple to support swap syntax.
      val typedRhs = ctx.typer.typed(rhs)
      if (isTuple(typedRhs)){
        val (hold,rhsParts) = splitTuple(typedRhs)
        if (rhsParts.length != lhs.trees.length) errorTree(lhs,s"Tuple sizes do not match: $lhs ≠ $rhs:${typedRhs.tpe}")
        else untpd.Block(hold,untpd.Tuple((lhs.trees,rhsParts).zipped.map(untpd.Assign)))
      } else errorTree(rhs,s"RHS of assignment is not a Tuple:")
    }

    /** Handles update methods
      *  first try backward compatible un-curried update method,
      *  if typecheck fails: use once-curried update method
      */
    def compatibleUpdate(canCopy: untpd.Tree,
                         update: untpd.Tree,
                         lhsArgs: List[untpd.Tree]):tpd.Tree =
      ctx.typer.tryEither { implicit ctx => // obj(x) = y
        ctx.typer.typed(untpd.cpy.Apply(canCopy)(update, lhsArgs :+ tree.rhs),pt)
      } { (_,_) => ctx.typer.typed(curriedUpdate(canCopy,update,lhsArgs),pt) }

    def curriedUpdate(canCopy: untpd.Tree,
                      update: untpd.Tree,
                      lhsArgs: List[untpd.Tree]):untpd.Tree =
      tree.rhs match { // extract args from RHS
        case untpd.Tuple(rhsArgs) => // obj(x) = (a,b,c)
          untpd.Apply(untpd.cpy.Apply(canCopy)(update,lhsArgs),rhsArgs)
        case maybeTuple =>
          val typedRhs = ctx.typer.typed(maybeTuple)
          if(isTuple(typedRhs)) { // obj(x) = abc:(A,B,C)
            val (hold,rhsParts) = splitTuple(typedRhs)
            untpd.Block(hold,
              untpd.Apply(untpd.cpy.Apply(canCopy)(update,lhsArgs),rhsParts))
          } else // obj(x) = a:A
            untpd.Apply(untpd.cpy.Apply(canCopy)(update,lhsArgs),
              untpd.TypedSplice(typedRhs) :: Nil)
      }

    tree.lhs match {
      case lhs: untpd.Tuple => Some(ctx.typer.typed(assignSplitTuple(lhs,tree.rhs),pt))
      case lhs: untpd.Apply => Some(compatibleUpdate(lhs/*canCopy*/, untpd.Select(lhs.fun, nme.update), lhs.args))
      case untpd.TypedSplice(Apply(MaybePoly(Select(lhsPrefix, selected), targs), lhsArgs))
        if selected == nme.apply => //todo: so far do not know how to test this case...
        val rawUpdate: untpd.Tree = untpd.Select(untpd.TypedSplice(lhsPrefix), nme.update)
        val wrappedUpdate =
          if (targs.isEmpty) rawUpdate
          else untpd.TypeApply(rawUpdate, targs.map(untpd.TypedSplice))
        Some(compatibleUpdate(lhsPrefix/*canCopy*/, wrappedUpdate, lhsArgs.map(untpd.TypedSplice)))
      case _ => None
    }
  }

}