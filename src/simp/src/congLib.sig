(* ========================================================================= *)
(* Simplification of terms similar to SIMP_CONV but regarding arbitrary      *)
(* preorders instead of just equality                                        *)
(* Created by Thomas Tuerk, March 2006                                       *)
(* ========================================================================= *)

signature congLib =
sig
  include Abbrev

  (* ---------------------------------------------------------------------
  * congLib
  *
  * SIMP_CONV as defined in simpLib is a very useful tool. However,
  * it is limited to simplify a term t1 to a term t2 which is equivalent
  * according to the congruence =. The underlying traverser (TRAVERSER.sml)
  * however is able to handle arbitrary congruences.
  *
  * This lib tries to provide this ability of the traverser to handle arbitrary
  * congruences (or in fact preorders) to the end user. Therefore, an
  * interface similar to the interface of SimpLib is provided.
  *)


  (* ---------------------------------------------------------------------
  * congsetfrag
  *
  * Similar to ssfrag the datatype congsetfrag is a type used to construct
  * congsets. It contains:
  *    relations: a list of preorders, that may be used for simplification
  *               a preorder is defined as in travrules. You may use mk_preorder from
  *               to create preorders
  *    rewrs:     a set of rewrite theorems
  *               unlike simpLib conditional and ordered rewriting is not supported
  *               ad the moment. Therefore rewrite thms have to be of the form
  *               (R x y) where R is a preorder contained in relations or the equality.
  *               Additionally it is possible to provide theorems that use
  *               allquantification and that are conjunctions of such theorems.
  *               Notice, that providing rewrites like (x + y = y + x) will cause the
  *               simplification to loop, because no ordered rewriting is provided.
  *    congs:     The congruence rules for the preorders. These rules are just defined
  *               as congruence rules, for the simplifier, since both are in fact
  *               congruence rules for the traverser. This means a congruence Rule is of
  *               the form
  *               R1 x1 y1 ==> R2 x2 y2 ==> ... Rn xn yn ==> R x y
  *               When simplifing a term t that matches x, where x contains x1, ... xn, *               it first simplifies (x1 to y1 according to R1) then
  *               (x2 to y2 according to R2)... and finally return R x y where
  *               (y is instanciated by the match and the values for y1 ... yn.
  *    dprocs:    a list of decision procedures as used by the traverser
  *               normally, you won't need dprocs. However, it provides some interface *               to convert terms much more intelligent as rewrs do.
  *)
  datatype congsetfrag = CSFRAG of
    {relations : Travrules.preorder list,
     rewrs  : thm list,
     congs  : thm list,
     dprocs : Traverse.reducer list
     };

  (* ---------------------------------------------------------------------
  * congset
  *
  * The real datastructure. It contains processed informations of consetfrags
  *)
  type congset;


  (*Some elemantary functions to handle congsets and congsetfrags*)

  (*The empty congset, containing just equality*)
  val empty_congset : congset;

  (*Creates a congset out of a list of congsetfrags*)
  val mk_congset : congsetfrag list -> congset

  (*Adds a congsetfrag to a congset*)
  val cs_addfrag : congset -> congsetfrag -> congset

  (*Merges several congsetfrags*)
  val merge_cs : congsetfrag list -> congsetfrag

  (*creates a congsetfrag just containing rewrites*)
  val csfrag_rewrites : thm list -> congsetfrag

  (*adds rewrites to a congsetfrag*)
  val add_csfrag_rewrites : congsetfrag -> thm list -> congsetfrag



  (* ---------------------------------------------------------------------
  * CONGRUENCE_SIMP_CONV
  *
  * This is the main function. It is quite similar to SIMP_CONV. Additionally to
  * SIMP_CONV, it takes as the first argument the relation it
  * should simplify according to and as the second argument a congset.
  * The other parameters are just like the parameters of SIMP_CONV.
  * Notice, that CONGRUENCE_SIMP_CONV ``$=`` empty_congset shoult behave
  * exactly like SIMP_CONV.
  * ---------------------------------------------------------------------*)

  val CONGRUENCE_SIMP_CONV: term -> congset -> simpLib.simpset -> thm list -> term -> thm


  (*
  * CONGRUENCE_SIMP_QCONV
  *
  * Similar to CONGRUENCE_SIMP_CONV. However, CONGRUENCE_SIMP_CONV returns R x x, if
  * it can not simplify x. CONGRUENCE_SIMP_QCONV will fail in this case.
  *)
  val CONGRUENCE_SIMP_QCONV: term -> congset -> simpLib.simpset -> thm list -> term -> thm


  (* ---------------------------------------------------------------------
  * CONGRUENCE_EQ_SIMP_CONV
  *
  * CONGRUENCE_SIMP_CONV with the equality relation, i.e. CONGRUENCE_SIMP_CONV ``$=``
  * ---------------------------------------------------------------------*)
  val CONGRUENCE_EQ_SIMP_CONV: congset -> simpLib.simpset -> thm list -> term -> thm


  (* ---------------------------------------------------------------------
  * Tactics and rule similar to simpLib. They all use the equality relation as
  * starting relation. However, by congruence rules, some other relations may be used
  * for subterms
  * ---------------------------------------------------------------------*)

  val CONGRUENCE_SIMP_RULE : congset -> simpLib.simpset -> thm list -> thm -> thm
  val CONGRUENCE_SIMP_TAC : congset -> simpLib.simpset -> thm list -> tactic
  val ASM_CONGRUENCE_SIMP_TAC : congset -> simpLib.simpset -> thm list -> tactic
  val FULL_CONGRUENCE_SIMP_TAC : congset -> simpLib.simpset -> thm list -> tactic


end

