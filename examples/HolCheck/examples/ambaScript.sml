
(* Definitions for AMBA SoC bus protocol. See AMBA Specification v2.0 from ARM for details  *)
(* This file mainly demos composing of model checked APB and AHB theorems using HOL *)

open HolKernel Parse boolLib bossLib

val _ = new_theory "amba"

(* app load ["bddTools","amba_apb_def","mod16Theory","amba_ahb_def","decompTools","envTheory"]; *)

open boolSyntax bossLib Ho_Rewrite Tactical Tactic PairRules pairSyntax Drule
open amba_ahbTheory amba_apbTheory amba_common bddTools mod16Theory commonTools decompTools ksTheory muSyntaxTheory setLemmasTheory envTheory

val ahb_nm = 8;  (* 1..16 *)
val ahb_ns = 16; (* 1..16 *)

(*----------------------- Bridging -------------------------- *)

val Rb_state = list_mk_pair((strip_pair Rpm_state)@(strip_pair Rs_state))
val Rb_state' = ksTools.mk_primed_state Rb_state

(* AHB-APB bridge is just the conjunction of the APB master with a generic AHB slave *)
(* Note that the actual bridging code has been abstracted out. We just assume the master and slave handle their
   syncing correctly. This code can be added in later, if required: all its signals can be hidden, so it doesn't matter *)
val Rb = Define `TRANS_B (^Rb_state,^Rb_state') =
	 TRANS_APB_M (^Rpm_state,^Rpm_state') /\
         TRANS_AHB_S ^(fromMLnum (ahb_ns-1)) (^Rs_state,^Rs_state')
`;

val Ib = Define `INIT_B (^Rb_state) = T`;

val I1pb = Define `INIT_APB_B (^Rb_state) = ^(rhs(concl(Drule.SPEC_ALL INIT_APB_def)))`;

(* APB transition relation with master substituted by the bridge with ahb vars hidden away by exists quant*)
val R1pb = Define `TRANS_APB_B (^Rp_state,^Rp_state') =
(^(list_mk_exists((strip_pair Rs_state)@(strip_pair Rs_state'),lhs(concl(Drule.SPEC_ALL Rb))))) /\
^(list_mk_conj(List.tabulate(num_apb_slaves,fn n => lhs(concl(Drule.SPEC_ALL (SPEC (fromMLnum n) TRANS_APB_S_def))))))  /\
^(list_mk_conj(List.tabulate(num_apb_slaves,fn n => lhs(concl(Drule.SPEC_ALL (SPEC (fromMLnum n) TRANS_BUS_def))))))
`;

val r1hbt = (list_mk_exists
    ((strip_pair bbv)@(strip_pair bbv')@(strip_pair hwsv)@(strip_pair hwsv'),
     list_mk_conj [``INIT_AHB (^I1h_state) ==> (MOD16_IS_ZERO (^bbv') /\ MOD16_IS_ZERO (^hwsv'))``,
		   lhs(concl(Drule.SPEC_ALL TRANS_CNT_def)),
		   (list_mk_exists
		    ((strip_pair mask_vars)@(strip_pair mask_vars'),
		     list_mk_conj [``INIT_AHB (^I1h_state) ==> NO_MASK (^mask_vars)``,
				   lhs(concl(Drule.SPEC_ALL (SPEC (fromMLnum (nm-1)) (GEN ``n:num`` TRANS_A_def)))),
				   list_mk_exists((strip_pair transm_vars)@(strip_pair transm_vars')
						  @(strip_pair burstm_vars)@(strip_pair burstm_vars'),
						  (list_mk_conj[``INIT_AHB (^I1h_state) ==>
								  !m. m<16 ==> IDLEM m (^transm_vars)``,
								list_mk_conj(List.tabulate(nm,
									fn n => lhs(concl(Drule.SPEC_ALL
									(SPEC (fromMLnum n) TRANS_AHB_M_def))))),
								lhs(concl(Drule.SPEC_ALL TRANS_X_def))]))])),
		   list_mk_exists
		   ((strip_pair slvsplt_vars)@(strip_pair slvsplt_vars'),
		    list_mk_conj([``INIT_AHB (^I1h_state) ==> NO_HSLVSPLT (^slvsplt_vars)``,
				    ``^(list_mk_exists((strip_pair Rpm_state)@(strip_pair Rpm_state'),
				       (lhs(concl(Drule.SPEC_ALL Rb)))))``,
				  list_mk_conj(List.tabulate(ns-1,fn n => lhs(concl(Drule.SPEC_ALL
									(SPEC (fromMLnum n) TRANS_AHB_S_def)
    ))))]))]))

(* AHB transition relation with one generic slave replaced by the bridge with apb signals hidden *)
val R1hb = Define `TRANS_AHB_B (^R1h_state,^R1h_state') = ^r1hbt`; (*FIXME: ML chokes if I put the term itself here*)

(* theorems *)

val maindefs = [TRANS_AHB_M_def,TRANS_X_def,(*TRANS_D_def,*)TRANS_CNT_def,TRANS_AHB_S_def,amba_ahb_I1rh]
val abbrev_defs = [IDLE_def,BUSY_def,NOSEQ_def,SEQ_def,OKAY_def,ERROR_def,RETRY_def,SPLIT_def,SINGLE_def,INC4_def,
                   INC4M_def,BURSTM0_def,TRANSM0_def,TRANSM1_def,IDLEM_def,BUSYM_def,NOSEQM_def,SEQM_def,ALL_SPLIT_def,
		   MASK_def,BUSREQ_def,HSPLIT_def,NO_BUSREQ_def,NO_HSPLIT_def,NO_MASK_def,INIT_GRANT_def,GRANT_def,
		   INIT_MASTER_def, MASTER_def,HSLVSPLT_def,SLVSPLT_def,NO_HSLVSPLT_def,HSEL_def,BB_INC_def,WS_INC_def]

val unroll_ahb_CONV2 = unroll_ahb_CONV maindefs TRANS_A_def abbrev_defs

(* APB is the same as APB with bridge instead of master whose ahb signals are hidden *)
val apb1 = save_thm("APB_BRIDGE",prove(``^(lhs(concl (Drule.SPEC_ALL TRANS_APB_def))) = ^(lhs(concl (Drule.SPEC_ALL R1pb)))``,
REWRITE_TAC [TRANS_APB_def,R1pb,Rb]
THEN EQ_TAC THENL [
STRIP_TAC THEN CONJ_TAC THENL [
  REPEAT (CONV_TAC (Conv.LAST_EXISTS_CONV Conv.EXISTS_AND_CONV))
  THEN CONJ_TAC THENL [
    ASM_REWRITE_TAC [],
    MAP_EVERY EXISTS_TAC (exv (fst (strip_exists(fst(dest_conj(rhs(concl (Drule.SPEC_ALL R1pb)))))))
    (findAss (rhs(concl (Drule.SPEC_ALL
			     (unroll_ahb_CONV2 (rhs(concl(Drule.SPEC_ALL(SPEC (fromMLnum (ns-1)) TRANS_AHB_S_def))))))))))
    THEN (CONV_TAC unroll_ahb_CONV2)
    THEN EVAL_TAC
    ],
  ASM_REWRITE_TAC []
  ],
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []
]));

(* AHB is the same as AHB with bridge as a generic slave whose apb signals are hidden *)
val ahb1 = save_thm("AHB_BRIDGE",prove(``^(lhs(concl (Drule.SPEC_ALL TRANS_AHB_def))) = ^(lhs(concl (Drule.SPEC_ALL R1hb)))``,
PURE_REWRITE_TAC [TRANS_AHB_def,R1hb,Rb]
THEN EQ_TAC THENL [
 STRIP_TAC
 THEN MAP_EVERY EXISTS_TAC ((strip_pair bbv)@(strip_pair bbv')@(strip_pair hwsv)@(strip_pair hwsv'))
 THEN REPEAT CONJ_TAC THEN PURE_ASM_REWRITE_TAC [] THENL [
  MAP_EVERY EXISTS_TAC ((strip_pair mask_vars)@(strip_pair mask_vars'))
  THEN REPEAT CONJ_TAC THEN PURE_ASM_REWRITE_TAC []
  THEN MAP_EVERY EXISTS_TAC ((strip_pair transm_vars)@(strip_pair transm_vars')
						  @(strip_pair burstm_vars)@(strip_pair burstm_vars'))
  THEN REPEAT CONJ_TAC THEN PURE_ASM_REWRITE_TAC [],
  MAP_EVERY EXISTS_TAC ((strip_pair slvsplt_vars)@(strip_pair slvsplt_vars'))
  THEN REPEAT CONJ_TAC THEN PURE_ASM_REWRITE_TAC []
  THEN MAP_EVERY EXISTS_TAC (exv ((strip_pair Rpm_state)@(strip_pair Rpm_state'))
     (findAss (rhs(concl (Drule.SPEC_ALL TRANS_APB_M_def)))))
  THEN REWRITE_TAC [TRANS_APB_M_def]
 ],
 STRIP_TAC
 THEN MAP_EVERY EXISTS_TAC ((strip_pair bbv)@(strip_pair bbv')@(strip_pair hwsv)@(strip_pair hwsv'))
 THEN REPEAT CONJ_TAC THEN PURE_ASM_REWRITE_TAC [] THENL [
  MAP_EVERY EXISTS_TAC ((strip_pair mask_vars)@(strip_pair mask_vars'))
  THEN REPEAT CONJ_TAC THEN PURE_ASM_REWRITE_TAC []
  THEN MAP_EVERY EXISTS_TAC ((strip_pair transm_vars)@(strip_pair transm_vars')
						  @(strip_pair burstm_vars)@(strip_pair burstm_vars'))
  THEN REPEAT CONJ_TAC THEN PURE_ASM_REWRITE_TAC [],
  MAP_EVERY EXISTS_TAC ((strip_pair slvsplt_vars)@(strip_pair slvsplt_vars'))
  THEN REPEAT CONJ_TAC THEN PURE_ASM_REWRITE_TAC []
 ]
]));

(*----------------------- Parallel synchronous composition -------------------------- *)

val S01 = rhs(concl (SPEC_ALL INIT_APB_def))
val TS1 = [(".",rhs(concl (SPEC_ALL TRANS_APB_def)))]
val S02 = rhs(concl (SPEC_ALL INIT_AHB_def))
val TS2 = [(".",rhs(concl (SPEC_ALL TRANS_AHB_def)))]
val nm1 = "apb"
val nm2 = "ahb"
val cst = mk_prod(type_of (rand(lhs(concl(SPEC_ALL INIT_APB_def)))),
				type_of (rand(lhs(concl(SPEC_ALL INIT_AHB_def))))) (*type of state of product model*)
val env = inst [alpha|->cst] ``EMPTY_ENV``

val (gpscth,ks1_def,s1,s2) = mk_gen_par_sync_comp_thm S01 TS1 nm1 S02 TS2 nm2 env

val _ = save_thm("APB_LIFT",gpscth) (* if well-formed f holds in APB then it holds in APB x AHB *)
val _ = save_thm("amba_ks1_def",ks1_def)
val _ = Define `amba_s1 (^s1) = T`
val _ = Define `amba_s2 (^s2) = T`

(*
now we can call (inan interactive session)

mk_par_sync_comp_thm (amba_gpscth,amba_ks1_def,
		      rand(lhs(concl (SPEC_ALL amba_s1_def))), (* s1 *)
		      rand(lhs(concl (SPEC_ALL amba_s2_def)))) (* s2 *)
                      f NONE

for some APB property f
*)

val _ = export_theory()

