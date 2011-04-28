(* =====================================================================
 * FILE          : travrules.sig
 * DESCRIPTION   : Sets of rules for traversing terms.  Used for
 *	           simpification and term traversal.
 *
 * AUTHOR        : Donald Syme
 *                 Based loosely on ideas from window inference.
 * ===================================================================== *)

signature Travrules =
sig
   include Abbrev

   (* ---------------------------------------------------------------------
    * preorders
    *
    * Nb. Preorders must be constants.  This restriction may be lifted
    * in the future.
    *
    * Once things are set up, the user of this module generally
    * specifies a preorder as a term, e.g. (--`$=`--).
    * ---------------------------------------------------------------------*)

  datatype preorder = PREORDER of term
                                   * (thm -> thm -> thm)
                                   * ({Rinst:term,arg:term} -> thm)
  val samerel : term -> term -> bool

  val mk_preorder : (thm * thm) -> preorder;
  val find_relation : term -> preorder list -> preorder;

   (* ---------------------------------------------------------------------
    * type travrules
    *
    * An object of type "travrules" specifies a colelction of theorems
    * and procedures which are used when automatically traversing a term.
    *
    * The collection of rules may contain rules for multiple relations.
    * The traversal engine is trying to reduce the "current term"
    * via various "reducers" under the "current relation".
    * In normal equality reasoning (see SIMP_TAC) the relation is (--`$=`--).
    *
    * Traversal is achieved by means of congruence procedures.
    * A congruence procedure has ML type
    *       {solver, depther} -> conv
    * where "conv" here is interpreted in the wider sense that the
    * function will return a theorem showing REL(t1,t2) for the
    * relation over which the congruence procedure acts.
    *
    * Congruence procedures are typically simple layers on top
    * of a congruence theorem (though they may also implement an
    * infinite class of congurence theorems).  For example,
    *    !f x. (x = x') ==> (f = f') --> (f x = f' x')
    * is a very simple congruence theorem for constructs of
    * the form (--`f x`--) under the (--`$=`--) relation.
    * (Nb. This congruence procedure is actually implemented
    * by a special procedure for efficiency reasons).
    *
    * Congruence procedures are typically created by using
    * the function CONGRULE.
    *
    * Congruence rules may have side conditions which should be solved
    * by the solver provided to the congruence procedure.  If they
    * are not solved they can be added as assumptions to the theorem
    * returned, and will need to be discharged by the user after
    * traversal.
    * ---------------------------------------------------------------------*)

   datatype travrules = TRAVRULES of {
       relations : preorder list,
       congprocs : Opening.congproc list,
       weakenprocs : Opening.congproc list
    };


   (* ---------------------------------------------------------------------
    * Basic operations on travruless
    *  merge should only be used on non-overlapping travrule fragments.
    * ---------------------------------------------------------------------*)

  val merge_travrules: travrules list -> travrules

  val gen_mk_travrules :
    {relations : preorder list,
     congprocs : Opening.congproc list,
     weakenprocs : Opening.congproc list} -> travrules


  val mk_travrules : preorder list -> thm list -> travrules
  val cong2proc : preorder list -> thm -> Opening.congproc

  (* the equality case - all theorems are interpeted as equality congruences *)
  val EQ_preorder : preorder
  val EQ_tr : travrules

end (* sig *)



