(****************************************************************************)
(* FILE          : decisionLib.sml  (was DecisionUser)                      *)
(* DESCRIPTION   : User-level combined decision procedure.                  *)
(*                                                                          *)
(* AUTHOR        : R.J.Boulton                                              *)
(* DATE          : 22nd February 1995                                       *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 3rd September 1996                                       *)
(****************************************************************************)


structure decisionLib =
struct

local open Lib Term Drule Tactic Tactical Conv
      infix THEN

val _ = LazyThm.set_proof_mode LazyThm.Lazy;

val number_of_vars = length o free_vars o (fn (tm,_) => tm);

fun lambda_free tm =
   case (dest_term tm)
   of LAMB _ => false
    | COMB {Rator,Rand} => lambda_free Rator andalso lambda_free Rand
    | _ => true;

fun LIST_UNDISCH_TAC [] = ALL_TAC
  | LIST_UNDISCH_TAC (h :: hs) = LIST_UNDISCH_TAC hs THEN UNDISCH_TAC h;

in

fun DECISION_TAC conv p : Abbrev.tactic =
   fn gl as (hs,_) => (LIST_UNDISCH_TAC (filter p hs) THEN CONV_TAC conv) gl;

val show_proving = ref false;

fun DECIDE_CONV tm =
   (NumArith.reset_multiplication_theorems ();
    Decide.DECIDE_FORMULA_CONV (!show_proving) number_of_vars
       [DecideNum.num_proc,DecideProp.prop_proc,DecidePair.pair_proc,
        DecideTypes.types_proc,DecideUninterp.uninterp_proc]
          DecisionConv.ALL_CONV tm);

val DECIDE = EQT_ELIM o DECIDE_CONV;

val DECIDE_TAC = DECISION_TAC DECIDE_CONV lambda_free;

end;

end; (* decisionLib *)
