signature decidable_separationLogicLib =
sig

include Abbrev;

(*Contains theorems that state that the universe of
  some type is infinite. This theorem for :num is
  added automatically. If you are interested to
  use ds_inference_UNROLL_COLLAPSE with other types
  as values, a theorem should be added to this list.*)
val INFINITE_UNIV___THMs : thm list ref;


(* Splits a list according to the cons operator.
   Examples:

   "e1::e2::l" is returned as (["e1", "e2"], "l")
   "e1::(l1++l2)" is returned as (["e1"], "l1++l2")
   "[e1;e2;e3]" is returned as (["e1", "e2", "e3"], "[]")
*)
val strip_cons : term -> term list * term;



(* destructs a term of the from
   
   LIST_DS_ENTAILS (pfL, sfL) (pfL', sfL')

   and returns the lists pfL, sfL, pfL', sfL'.
*)

val dest_LIST_DS_ENTAILS : 
   term -> (term * term * term * term * term * term);



(* destructors with the standard meaning *)
val dest_pf_equal : term -> term * term;
val is_pf_equal : term -> bool;

val dest_pf_unequal : term -> term * term;
val is_pf_unequal : term -> bool;

val is_sf_emp : term -> bool;

val dest_sf_ls : term -> term * term * term;
val is_sf_ls : term -> bool;

val dest_sf_points_to : term -> term * term * (term * term) list * term;
val is_sf_points_to : term -> bool;

val dest_sf_tree : term -> (term list * term) * term * term;
val is_sf_tree : term -> bool;

val dest_sf_bin_tree : term -> term * term * term * term;
val is_sf_bin_tree : term -> bool;

val dest_sf_tree_ext : term -> term * (term list * term) * term * term;
val is_sf_tree_ext : term -> bool;

val dest_dse_var : term -> term;
val is_dse_var : term -> bool;

val dest_dse_const : term -> term;
val is_dse_const : term -> bool;

val is_dse_nil : term -> bool;




(* Given a term t of the form
   
   LIST_DS_ENTAILS (c1, c2) ([pf1, pf2, pf3 ... pfn], [sf1 ... ]) ([pf'1, ...], [sf'1...])

   GEN_SWAP_CONV n1 m1 n2 m2 n3 m3 n4 m4 n5 m5 n6 m6 t 

   constructs a term t' by SWAPING the elements of the argumenst lists.
   Element m1 in [pf1, ...] bubbles up to position n1. 
   m2 n2 modify [sf1...] etc. 
   m5 n5 handles c1, m6 n6 c2


   Example:

   The list
   [0,1,2,3,4,5,6] with n = 1, m = 4 is transformed to
   [0,4,1,2,3,5,6]

   The theorem t = t' is returned
*)
val GEN_SWAP_CONV : int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> int -> term -> thm

(* SWAP_CONV p n m is 
   a wrapper for GEN_SWAP_CONV 
   with all int-arguments set to 0 except one pair of n arguments, which
   is selected by the p argument.
*)
val SWAP_CONV : int -> int -> int -> term -> thm



(*
   Given a term t of the form
   
   LIST_DS_ENTAILS (c1,c2) ([pf1, pf2, pf3 ... pfn], sfL) ([pf1', ...], sfL')

   ds_DIRECT_EQUATIONS_CONV [b1, b2, b3, ...] [b1', b2', ...] 
   
   turns pf_n('), iff pf_n(') is of the form (e1 = e2) or (e1 /= e2) and iff
   b_n(') is true.
*) 
val ds_TURN_EQUATIONS_CONV : bool list -> bool list -> term -> thm; 

(* Turns equations and disequations automatically, thus that constansts are on the right side, while 
   variables are on the left. If these rules are not sufficient, a comparision of the string representation
   is used *)
   
val ds_AUTO_DIRECT_EQUATIONS_CONV : term -> thm; 


(************************************************************
 Inferences
 ************************************************************)


val ds_inference_REMOVE_TRIVIAL___CONV : term -> thm;
val ds_inference_INCONSISTENT___CONV : term -> thm;
val ds_inference_AXIOM___CONV : term -> thm;
val ds_inference_SUBSTITUTION___CONV : term -> thm;
val ds_inference_HYPOTHESIS___CONV : term -> thm;
val ds_inference_FRAME___CONV : term -> thm;
val ds_inference_FRAME___IMPL_CONV : term -> thm;
val ds_inference_NIL_NOT_LVAL___CONV : term -> thm;
val ds_inference_NIL_NOT_LVAL___CONV___overeager : bool -> term -> thm;
val ds_inference_PARTIAL___CONV : term -> thm;
val ds_inference_PARTIAL___CONV___overeager : bool -> term -> thm;
val ds_inference_PRECONDITION_STRENGTHEN___CONV : term -> thm;
val ds_inference_SIMPLE_UNROLL___CONV : term -> thm;
val ds_inference_PRECONDITION_CASES___CONV : term -> thm;
val ds_inference_UNROLL_LIST___NON_EMPTY___CONV : term -> thm;
val ds_inference_UNROLL_LIST___CONV : term -> thm;
val ds_inference_UNROLL_BIN_TREE___CONV : term -> thm;
val ds_inference_UNROLL_RIGHT_CASES___CONV : term -> thm;
val ds_inference_APPEND_LIST___CONV : term -> thm;

val ds_DECIDE_CONV : term -> thm;
val ds_DECIDE : term -> thm;


end

