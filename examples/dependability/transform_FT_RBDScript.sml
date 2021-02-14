(* ========================================================================= *)
(* File Name: transform_FT_RBD.sml                                           *)
(*---------------------------------------------------------------------------*)
(* Description:  Transform RBD to FT either way                              *)
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
(*------new tactics for set simplification----*)
(*--------------------*)
infixr 0 ++ << || ORELSEC ## --> THENC;
infix 1 >> |->;
fun parse_with_goal t (asms, g) =
  let
    val ctxt = free_varsl (g::asms)
  in
    Parse.parse_in_context ctxt t
  end;

val PARSE_TAC = fn tac => fn q => W (tac o parse_with_goal q);
val Suff = PARSE_TAC SUFF_TAC;
val POP_ORW = POP_ASSUM (fn thm => ONCE_REWRITE_TAC [thm]);
val !! = REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;
val std_ss' = simpLib.++ (std_ss, boolSimps.ETA_ss);
val op by = BasicProvers.byA;
(*---------------------------*)

(*--------AND_to_series-------------------*)
val AND_to_series = store_thm("AND_to_series",
  ``!p L. FTree p (AND (gate_list L)) =
          rbd_struct p (series (rbd_list L))``,
RW_TAC std_ss[series_rbd_eq_big_inter,AND_gate_eq_big_inter]);

(*---------OR_to_parallel-----------------------------*)
val OR_to_parallel = store_thm("OR_to_parallel",
  ``!p L. FTree p (OR (gate_list L)) =
          rbd_struct p (parallel (rbd_list L))``,
GEN_TAC ++ Induct
>> (RW_TAC std_ss[gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def])
++ RW_TAC std_ss[gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def]);

(*-----------AND-OR-to-series-parallel----------------------------*)
val AND_OR_to_series_parallel = store_thm("AND_OR_to_series_parallel",
  ``!p L. (FTree p ((AND of (\a. OR (gate_list a))) L) =
          rbd_struct p ((series of (\a. parallel (rbd_list a))) L))``,
GEN_TAC ++ Induct
>> (RW_TAC list_ss[of_DEF,o_DEF,gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def])
++ RW_TAC list_ss[of_DEF,o_DEF,gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def]
++ FULL_SIMP_TAC std_ss[of_DEF,o_DEF,OR_to_parallel]);

(*-----------------------OR_AND_to_parallel_series---------------------------------------*)
val OR_AND_to_parallel_series = store_thm("OR_AND_to_parallel_series",
  ``!p L. (FTree p ((OR of (\a. AND (gate_list a))) L) =
          rbd_struct p ((parallel of (\a. series (rbd_list a))) L))``,

GEN_TAC ++ Induct
>> (RW_TAC list_ss[of_DEF,o_DEF,gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def])
++ RW_TAC list_ss[of_DEF,o_DEF,gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def]
++ FULL_SIMP_TAC std_ss[of_DEF,o_DEF,AND_to_series]);

(*-------------NAND_gate_transform------------------------*)
val NAND_gate_transform = store_thm("NAND_gate_transform",
  ``!L1 L2 n p. (FTree p (AND (gate_list (compl_list p L1 ++ L2)))) =
                 (rbd_struct p (series (rbd_list (compl_list p L1 ++ L2)))) ``,
RW_TAC std_ss[]
++ MP_TAC(Q.ISPECL [`p:α event # α event event # (α event -> real)`,`(compl_list p L1 ++ L2)`] AND_to_series)
++ RW_TAC std_ss[]);

(*-------------NOR_gate_transform------------------------*)
val NOR_gate_transform = store_thm("NOR_gate_transform",
  ``!p L. p_space p DIFF FTree p (OR (gate_list L)) =
          p_space p DIFF rbd_struct p (parallel (rbd_list L))``,

GEN_TAC ++ Induct
>> (RW_TAC std_ss[gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def])
++ RW_TAC std_ss[gate_list_def,FTree_def,gate_list_def,rbd_list_def,rbd_struct_def]
++ RW_TAC std_ss[OR_to_parallel]);
(*-------------Inhibit_gate_transform------------------------*)
val Inhibit_gate_transform = store_thm("Inhibit_gate_transform",
  ``!p A B C. prob_space p /\ C IN events p ==>
              (FTree p (AND [OR [atomic A; atomic B]; NOT (atomic C)]) =
              (rbd_struct p (parallel [atomic A; atomic B]) INTER
               (p_space p DIFF rbd_struct p (atomic C)))) ``,
RW_TAC list_ss[FTree_def,rbd_struct_def, UNION_EMPTY]
++ SUBST_OCCS_TAC [([1], SPECL [``(p_space p DIFF C):('a->bool)``, ``p_space p:('a->bool)``]
                               INTER_COMM)]
++ DEP_REWRITE_TAC[INTER_PSPACE]
++ DEP_REWRITE_TAC[EVENTS_COMPL]
++ RW_TAC std_ss[]);
(*-------------comp_gate_transform------------------------*)
val comp_gate_transform = store_thm("comp_gate_transform",
  ``!p A B. prob_space p /\ A IN events p /\ B IN events p ==>
            (FTree p (OR [AND [atomic A; atomic B]; NOT (OR [atomic A; atomic B])]) =
            rbd_struct p (series [atomic A; atomic B]) UNION
                         (p_space p DIFF rbd_struct p (parallel [atomic A; atomic B])))``,
RW_TAC list_ss[FTree_def,rbd_struct_def, UNION_EMPTY]);
(*-------------k_out_N_to_majority_voting_gate------------------------*)
val k_out_N_to_majority_voting_gate = store_thm(
  "k_out_N_to_majority_voting_gate",
  ``!p X k n.
      majority_voting_FT_gate p X k n = K_out_N_struct p X k n``,
RW_TAC std_ss[majority_voting_FT_gate_def,K_out_N_struct_def]);

val _ = export_theory();
