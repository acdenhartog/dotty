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
  *
  *    Assign must be handled by the Typer because update methods can have return types.
  *    Tuples are uniquely involved in assign in various ways:
  *      1. Right hand side of curried update method can be a Tuple that requires un-tuple. X(1) = (2,3)
  *      2. Possible update variable in a tuple. (a,b) = (1,2)
  *         (no generalization to CaseClass(a,b) = (1,2) since that calls into CaseClass.update(a,b)(1,2), while (a,b) = (1,2) is just a parsing error in vanilla scala.)
  *         //todo find where match { is defined, there also can be = if rhs is a Tuple
  *          //or wait, how does that work for x(y) = ???, is apply a free exit too?
  *
  *    Un-tuple also needs to be done by the Typer.
  *
  *
  *    also want to fix: { case (a,b) => }
  *                      ((a,b) => would be nicer)
  *
  *
  *    The tendrils of TupleMagics are spread throughout the compiler, the goal of this object is to collect them in one place.
  *      And to keep the rest of the compiler code pure of its abominate rituals.
  *
  *
  *      define:
  *        UnTuple : to take args out of an untpd.Tuple
  *        SplitTuple : to access t._1,t._2,t._3 etc.
  */
object TupleMagic {

  /*Consider the types:

      (A,B)    == Tuple[A,B]
      (A,B)=>C != Tuple[A,B]=>C

    This is confusing and arbitrary.
     ((A,B))=>C should not exist.*/
//  implicit def tuple2Function[A,B,C](fn:(A,B)=>C):Tuple2[A,B]=>C = t => fn(t._1,t._2)
//  List(1,2,3).zip(List("A","B","C")).map{ case (1,b)=>s"$b"; case (2,b)=>s"$b"; case (a,b)=>s"$b$a" }
//  List(1,2,3).zip(List("A","B","C")).map( (a:Int,b:String) => s"$b$a" )
//  List(1,2,3).zip(List("A","B","C")).map(tuple2Function((a,b)=>s"$b$a"))
//  (List(1,2,3),List("A","B","C"),List(1.2,1.3,1.4)).zipped.map((a,b,c)=>s"$a$b$c") //this works... hmm

  /*Note:

      def byName(a: =>Int, b: =>Int) = ...
      def rnd:Int = ...
      def dtup = (rnd,rnd)
      val vtup = (rnd,rnd)

      byName(dtup)
      byName(vtup)
      byName{(rnd,rnd)}
      byName(rnd,rnd)

      Only the last one is "really" pass-by-name
   */



  def isTuple(typedTree:tpd.Tree)
             (implicit ctx: Context) = {

    def unexpected(_tpe:Type) = { //this is a debugging method
      ctx.error(s"RHS type is probably not a Tuple: ${_tpe.show}")
      ctx.error(s"And direct tuple check returns: ${defn.isTupleType(_tpe)}")
      defn.isTupleType(_tpe)
    }

    def unExpr(wrapped:Type) = wrapped match {
      case ExprType(resTpe) => defn.isTupleType(resTpe) /*def xx:(A,B); (a,b) = xx*/
      case tpe: RefinedType => defn.isTupleType(tpe)    /*val xx:(A,B); (a,b) = xx*/
      case _tpe => unexpected(_tpe) /*???*/
    }

    //todo: there should be a more generic extractor to deal with this somewhere...
    typedTree.tpe match {
      case ntpe:NamedType => ntpe.denot match {
        //case symDenot:SymDenotation => unExpr(symDenot.info)
        case sngDenot:SingleDenotation => unExpr(sngDenot.infoOrCompleter)
        case _den =>
          ctx.error(s"RHS denotation not a SymDenotation, what does this mean?!: ${_den.show}");
          false
      }
      case tpe:RefinedType => defn.isTupleType(tpe)
      case _tpe => unexpected(_tpe) /*???*/
    }
  }

  //todo: find Tuple extractor/unapply implemenation to check for code duplication
  def splitTuple(tuple:tpd.Tree)
                (implicit ctx: Context):(untpd.ValDef,List[untpd.Select]) = {
    val name = ctx.freshName().toTermName
    val hold = untpd.Ident(name)
    //todo: it sees silly to make this ValDef out of untpd.TypedSplices, but idk how to properly construct a tpd.ValDef
    (untpd.ValDef(name,untpd.TypedSplice(tpd.TypeTree(tuple)),untpd.TypedSplice(tuple)),
      tuple.tpe.fields.indices //this is a bit sketchy
        .map(i=>untpd.Select(hold,nme.productAccessorName(1 + i))).toList)
  }

  def maybeUnTuple(maybeTuple:untpd.Tree):List[untpd.Tree] =
    maybeTuple match {
      case untpd.Tuple(args) => args
      case notTuple => notTuple :: Nil
    }

  def assignSplitTuple(lhs:untpd.Tuple,rhs:untpd.Tree)
                      (implicit ctx: Context):untpd.Tree = {
    rhs match {
      case untpd.Tuple(rhsTrees) =>
        if (rhsTrees.length != lhs.trees.length)
          errorTree(rhs,s"Tuple sizes do not match.")
        else untpd.Block((lhs.trees,rhsTrees).zipped.map(untpd.Assign),untpd.EmptyTree)
      case maybeTuple =>
        val typedRhs = ctx.typer.typed(maybeTuple)
        if (isTuple(typedRhs)){
          val (hold,parts) = splitTuple(typedRhs)
          if (parts.length != lhs.trees.length)
            errorTree(lhs,s"Tuple sizes do not match: $lhs ≠ $rhs:${typedRhs.tpe}")
          else untpd.Block(hold :: (lhs.trees,parts).zipped.map(untpd.Assign),untpd.EmptyTree)
        } else errorTree(rhs,s"RHS of assignment is not a Tuple:")
    }
  }

  def assignmentMagic(tree: untpd.Assign, pt: Type)
                     (implicit ctx: Context):Option[tpd.Tree] = {

    def updateMagic(canCopy: untpd.Tree,
                    update: untpd.Tree,
                    lhsArgs: List[untpd.Tree]):tpd.Tree =
      ctx.typer.tryEither { implicit ctx =>
        ctx.typer.typed(untpd.cpy.Apply(canCopy)(update, lhsArgs :+ tree.rhs),pt)
      } { (_,_) => //curried mode
        ctx.typer.typed(untpd.Apply(untpd.cpy.Apply(canCopy)(update,lhsArgs),maybeUnTuple(tree.rhs)),pt)
      }

    tree.lhs match {
      case lhs: untpd.Tuple => Some(ctx.typer.typed(assignSplitTuple(lhs,tree.rhs),pt))
      case lhs: untpd.Apply => Some(updateMagic(lhs, untpd.Select(lhs.fun, nme.update), lhs.args))
      case untpd.TypedSplice(Apply(MaybePoly(Select(fn, app), targs), lhsArgs)) if app == nme.apply =>
        //todo: no idea what code produces this case, so this is untested:
        val rawUpdate: untpd.Tree = untpd.Select(untpd.TypedSplice(fn), nme.update)
        val wrappedUpdate =
          if (targs.isEmpty) rawUpdate else untpd.TypeApply(rawUpdate, targs map untpd.TypedSplice)
        Some(updateMagic(fn, wrappedUpdate, lhsArgs map untpd.TypedSplice))
      case _ => None
    }
  }


  //todo: maybe allow method1(a,b,c); method2():(a,b,c); method1(method2())
  def applySplitTuple(fn:tpd.Tree,tuple:tpd.Tree)
                     (implicit ctx: Context):untpd.Block = {
    val (hold,parts) = splitTuple(tuple)
    untpd.Block(hold,untpd.Apply(fn,parts))
  }


  //todo maybe find auto-tupling to move it here?
}