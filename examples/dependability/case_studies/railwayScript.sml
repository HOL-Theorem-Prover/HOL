(* ========================================================================= *)
(* File Name: RailwayScript.sml                                              *)
(*---------------------------------------------------------------------------*)
(* Description: Formal Fault Tree based Dependability Analysis of            *)
(*                Railway Level Crossing using Theorem Proving               *)
(*                HOL4-Kananaskis                                            *)
(*                                                                           *)
(*              Author :  Waqar Ahmad                                        *)
(*                                                                           *)
(*          School of Electrical Engineering and Computer Sciences (SEECS)   *)
(*          National University of Sciences and Technology (NUST), PAKISTAN  *)
(*                                                                           *)
(*                                                                           *)
(* ========================================================================= *)

(*app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory",
          "real_probabilityTheory", "numTheory", "transcTheory",
          "rich_listTheory", "pairTheory", "extra_pred_setTools",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory", "real_measureTheory", "real_lebesgueTheory",
          "real_sigmaTheory","dep_rewrite","RBDTheory","FT_deepTheory","VDCTheory",
          "smart_gridTheory","ASN_gatewayTheory"];*)
open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory
     prim_recTheory real_probabilityTheory seqTheory pred_setTheory res_quanTheory
     sortingTheory res_quanTools listTheory transcTheory rich_listTheory pairTheory
     combinTheory realLib  optionTheory util_probTheory extrealTheory real_measureTheory
     real_lebesgueTheory real_sigmaTheory satTheory numTheory dep_rewrite
      RBDTheory FT_deepTheory VDCTheory smart_gridTheory ASN_gatewayTheory
      extra_pred_setTools;

fun K_TAC _ = ALL_TAC;

open HolKernel boolLib bossLib Parse;
val _ = new_theory "railway";

(*--------------------*)
val op by = BasicProvers.byA;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
(*---------------------------*)

(*--------------------------------------*)
Definition in_events_def :
in_events p L = (!z. MEM z L ==> z IN events p)
End
(*--------------------------------------*)
Definition two_dim_fail_event_list_def :
two_dim_fail_event_list p L t = MAP (\a. fail_event_list p a t) L
End
(*--------------------------------------*)
Definition three_dim_fail_event_list_def :
three_dim_fail_event_list p L t = MAP (\a. two_dim_fail_event_list p a t) L
End
(*--------------------------------------*)

Theorem railway_FT_equi_RBD :
 prob_space p /\ in_events p (fail_event_list p [x1;x2;x3;x4;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16] t) ==>
((FTree p (OR[OR(gate_list (fail_event_list p [x3;x4] t));
                    OR(gate_list (fail_event_list p [x5;x6] t));
                    AND[OR (gate_list (fail_event_list p [x9;x10] t));
                        OR(gate_list (fail_event_list p [x13;x14] t));
                        OR(gate_list (fail_event_list p [x15;x16] t));
                        OR(gate_list (fail_event_list p [x11;x12] t))];
                    OR(gate_list (fail_event_list p [x7;x8] t));
                    OR(gate_list (fail_event_list p [x1;x2] t))])) =
(rbd_struct p
  ((parallel
     of series of (λa. parallel (rbd_list a)))
        (three_dim_fail_event_list p [[[x3; x4; x5; x6; x7; x8; x1; x2]];
         [[x9; x10]; [x13; x14]; [x15; x16]; [x11; x12]]] t))))
Proof
RW_TAC list_ss[three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def,rbd_struct_def,FTree_def,of_DEF,o_THM,fail_event_list_def,rbd_list_def,gate_list_def]
>> RW_TAC std_ss[UNION_EMPTY,UNION_ASSOC]
>> RW_TAC std_ss[INTER_ASSOC]
>> ONCE_REWRITE_TAC[INTER_COMM]
>> DEP_REWRITE_TAC[INTER_PSPACE]
>> RW_TAC std_ss[]
>> DEP_REWRITE_TAC[EVENTS_INTER,EVENTS_UNION]
>> FULL_SIMP_TAC list_ss[in_events_def]
>> DEP_REWRITE_TAC[EVENTS_INTER,EVENTS_UNION]
>> FULL_SIMP_TAC list_ss[in_events_def]
>> SRW_TAC[][EXTENSION,GSPECIFICATION]
>> SET_TAC[]
QED

(*--------------------------------------*)

Definition one_minus_exp_func_list_def :
one_minus_exp_func_list C t = MAP (λa. 1 - exp (-(a * (t:real)))) C
End


(*--------------------------------------*)
Theorem fail_prob_railway_FT :
(0 <= t) /\ prob_space p /\
mutual_indep p
  (FLAT
     (FLAT
        (FLAT
           [three_dim_fail_event_list p
              [[[x3; x4; x5; x6; x7; x8; x1; x2]];
               [[x9; x10]; [x13; x14]; [x15; x16]; [x11; x12]]] t]))) /\
(∀x'.
   MEM x'
     (FLAT
        (FLAT
           (FLAT
              [three_dim_fail_event_list p
                 [[[x3; x4; x5; x6; x7; x8; x1; x2]];
                  [[x9; x10]; [x13; x14]; [x15; x16]; [x11; x12]]]
                 t]))) ⇒
   x' ∈ events p) /\
 exp_dist_list p [x1;x2;x3;x4;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16] [c1;c2;c3;c4;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15;c16] ==>
(prob p (FTree p (OR[OR(gate_list (fail_event_list p [x3;x4] t));
                    OR(gate_list (fail_event_list p [x5;x6] t));
                    AND[OR (gate_list (fail_event_list p [x9;x10] t));
                        OR(gate_list (fail_event_list p [x13;x14] t));
                        OR(gate_list (fail_event_list p [x15;x16] t));
                        OR(gate_list (fail_event_list p [x11;x12] t))];
                    OR(gate_list (fail_event_list p [x7;x8] t));
                    OR(gate_list (fail_event_list p [x1;x2] t))])) =
(1 −
exp (-(c3 * t)) * exp (-(c4 * t)) * exp (-(c5 * t)) * exp (-(c6 * t)) *
exp (-(c7 * t)) * exp (-(c8 * t)) * exp (-(c1 * t)) * exp (-(c2 * t)) *
(1 −
 (1 − exp (-(c9 * t)) * exp (-(c10 * t))) *
 (1 − exp (-(c13 * t)) * exp (-(c14 * t))) *
 (1 − exp (-(c15 * t)) * exp (-(c16 * t))) *
 (1 − exp (-(c11 * t)) * exp (-(c12 * t))))))
Proof
RW_TAC std_ss[]
>> DEP_REWRITE_TAC[railway_FT_equi_RBD]
>> RW_TAC std_ss[in_events_def]
>- (FULL_SIMP_TAC list_ss[three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def])
>> RW_TAC std_ss[of_DEF]
>> DEP_REWRITE_TAC[REWRITE_RULE[of_DEF]rel_parallel_of_series_parallel_rbd]
>> RW_TAC std_ss[]
>- (Q.EXISTS_TAC `[]`
   >> RW_TAC list_ss[]
   >> FULL_SIMP_TAC list_ss[three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def])
>> RW_TAC list_ss[list_prod_def,one_minus_list_def,list_prob_def,o_THM,three_dim_fail_event_list_def,in_events_def,two_dim_fail_event_list_def,fail_event_list_def]
>> RW_TAC real_ss[REAL_MUL_ASSOC]
>> FULL_SIMP_TAC list_ss[exp_dist_list_def,VDCTheory.exp_dist_def,CDF_def,distribution_def,fail_event_def]
>> RW_TAC real_ss[REAL_MUL_ASSOC]
QED

val _ = export_theory();
