(* ========================================================================= *)
(* File Name: transform_FT_RBDScript.sml                                     *)
(*---------------------------------------------------------------------------*)
(* Description: Either way Transformation of RBD and FT Modes                *)
(*                                                                           *)
(*                                                                           *)
(*                HOL4-Kananaskis                                            *)
(*                                                                           *)
(*              Author :  Waqar Ahmed                                        *)
(*                                                                           *)
(*          School of Electrical Engineering and Computer Sciences (SEECS)   *)
(*          National University of Sciences and Technology (NUST), PAKISTAN  *)
(*                                                                           *)
(*                                                                           *)
(* ========================================================================= *)
(*---------------------*)
(*app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory",
          "real_probabilityTheory", "numTheory", "dep_rewrite", "transcTheory",
          "rich_listTheory", "pairTheory", "combinTheory","limTheory","sortingTheory",
          "realLib", "optionTheory","satTheory", "util_probTheory", "extrealTheory",
          "real_measureTheory", "real_lebesgueTheory","real_sigmaTheory","RBDTheory",
          "FT_deepTheory","VDCTheory","ASN_gatewayTheory","extra_pred_setTools"];*)

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory real_probabilityTheory
     seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools listTheory transcTheory
     rich_listTheory pairTheory combinTheory realLib  optionTheory dep_rewrite
      util_probTheory extrealTheory real_measureTheory real_lebesgueTheory real_sigmaTheory satTheory numTheory
      RBDTheory FT_deepTheory VDCTheory ASN_gatewayTheory extra_pred_setTools;
open HolKernel boolLib bossLib Parse;
val _ = new_theory "transform_FT_RBD";
(*--------------------*)
val op by = BasicProvers.byA;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
(*---------------------------*)

(*--------AND_to_series-------------------*)
Theorem AND_to_series :
!p L. FTree p (AND (gate_list L)) =
          rbd_struct p (series (rbd_list L))
Proof
RW_TAC std_ss[series_rbd_eq_big_inter,AND_gate_eq_big_inter]
QED

(*---------OR_to_parallel-----------------------------*)
Theorem OR_to_parallel :
!p L. FTree p (OR (gate_list L)) =
          rbd_struct p (parallel (rbd_list L))
Proof
GEN_TAC >> Induct
>- (RW_TAC std_ss[gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def])
>> RW_TAC std_ss[gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def]
QED

(*-----------AND-OR-to-series-parallel----------------------------*)
Theorem AND_OR_to_series_parallel :
!p L. (FTree p ((AND of (\a. OR (gate_list a))) L) =
          rbd_struct p ((series of (\a. parallel (rbd_list a))) L))
Proof
GEN_TAC >> Induct
>- (RW_TAC list_ss[of_DEF,o_DEF,gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def])
>> RW_TAC list_ss[of_DEF,o_DEF,gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def]
>> FULL_SIMP_TAC std_ss[of_DEF,o_DEF,OR_to_parallel]
QED

(*-----------------------OR_AND_to_parallel_series---------------------------------------*)
Theorem OR_AND_to_parallel_series :
!p L. (FTree p ((OR of (\a. AND (gate_list a))) L) =
          rbd_struct p ((parallel of (\a. series (rbd_list a))) L))
Proof

GEN_TAC >> Induct
>- (RW_TAC list_ss[of_DEF,o_DEF,gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def])
>> RW_TAC list_ss[of_DEF,o_DEF,gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def]
>> FULL_SIMP_TAC std_ss[of_DEF,o_DEF,AND_to_series]
QED

(*-------------NAND_gate_transform------------------------*)
Theorem NAND_gate_transform :
!L1 L2 n p. (FTree p (AND (gate_list (compl_list p L1 ++ L2)))) =
                 (rbd_struct p (series (rbd_list (compl_list p L1 ++ L2))))
Proof
RW_TAC std_ss[]
>> MP_TAC(Q.ISPECL [`p:α event # α event event # (α event -> real)`,`(compl_list p L1 ++ L2)`] AND_to_series)
>> RW_TAC std_ss[]
QED

(*-------------NOR_gate_transform------------------------*)
Theorem NOR_gate_transform :
!p L. p_space p DIFF FTree p (OR (gate_list L)) =
          p_space p DIFF rbd_struct p (parallel (rbd_list L))
Proof

GEN_TAC >> Induct
>- (RW_TAC std_ss[gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def])
>> RW_TAC std_ss[gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def]
>> RW_TAC std_ss[OR_to_parallel]
QED
(*-------------Inhibit_gate_transform------------------------*)
Theorem Inhibit_gate_transform :
!p A B C. prob_space p /\ C IN events p ==>
              (FTree p (AND [OR [atomic A; atomic B]; NOT (atomic C)]) =
              (rbd_struct p (parallel [atomic A; atomic B]) INTER
               (p_space p DIFF rbd_struct p (atomic C))))
Proof
RW_TAC list_ss[FTree_def,rbd_struct_def, UNION_EMPTY]
>> SUBST_OCCS_TAC [([1], SPECL [``(p_space p DIFF C):('a->bool)``, ``p_space p:('a->bool)``]
                               INTER_COMM)]
>> DEP_REWRITE_TAC[INTER_PSPACE]
>> DEP_REWRITE_TAC[EVENTS_COMPL]
>> RW_TAC std_ss[]
QED
(*-------------comp_gate_transform------------------------*)
Theorem comp_gate_transform :
!p A B. prob_space p /\ A IN events p /\ B IN events p ==>
            (FTree p (OR [AND [atomic A; atomic B]; NOT (OR [atomic A; atomic B])]) =
            rbd_struct p (series [atomic A; atomic B]) UNION
                         (p_space p DIFF rbd_struct p (parallel [atomic A; atomic B])))
Proof
RW_TAC list_ss[FTree_def,rbd_struct_def, UNION_EMPTY]
QED
(*-------------k_out_N_to_majority_voting_gate------------------------*)
Theorem k_out_N_to_majority_voting_gate :
!p X k n.
      majority_voting_FT_gate p X k n = K_out_N_struct p X k n
Proof
RW_TAC std_ss[majority_voting_FT_gate_def,K_out_N_struct_def]
QED

val _ = export_theory();
