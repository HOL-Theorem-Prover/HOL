open HolKernel Parse boolLib bossLib

val _ = new_theory "amba"; 

open boolSyntax;
open bossLib;
(*open ctl2muTheory;
open cearTools;*)
open Ho_Rewrite;
open amba_ahbTheory;
open amba_apbTheory;
open Tactical;
open Tactic;
open PairRules;
open bddTools;

(* AHB-APB bridge is just the conjunction of the APB master with a generic AHB slave *)
val Rb = Define `TRANS_B ((paddr_0:bool,pwrite:bool,psel_0:bool,penable:bool,pdata_0:bool,m_0_0:bool,s_0_0_0:bool,hsel_1:bool,haddr_0:bool,hreadyout:bool,hresp_0:bool,hresp_1:bool,hws0:bool,hws1:bool,hws2:bool,hws3:bool,htrans_0:bool,htrans_1:bool,hburst_0:bool,bb2:bool),(paddr_0':bool,pwrite':bool,psel_0':bool,penable':bool,pdata_0':bool,m_0_0':bool,s_0_0_0':bool,hsel_1':bool,haddr_0':bool,hreadyout':bool,hresp_0':bool,hresp_1':bool,hws0':bool,hws1':bool,hws2':bool,hws3':bool,htrans_0':bool,htrans_1':bool,hburst_0':bool,bb2':bool)) = 
TRANS_M ((paddr_0:bool,pwrite:bool,psel_0:bool,penable:bool,pdata_0:bool,m_0_0:bool,s_0_0_0:bool),(paddr_0':bool,pwrite':bool,psel_0':bool,penable':bool,pdata_0':bool,m_0_0':bool,s_0_0_0':bool)) /\ TRANS_S_1 ((hsel_1:bool,haddr_0:bool,hreadyout:bool,hresp_0:bool,hresp_1:bool,hws0:bool,hws1:bool,hws2:bool,hws3:bool,htrans_0:bool,htrans_1:bool,hburst_0:bool,bb2:bool),(hsel_1':bool,haddr_0':bool,hreadyout':bool,hresp_0':bool,hresp_1':bool,hws0':bool,hws1':bool,hws2':bool,hws3':bool,htrans_0':bool,htrans_1':bool,hburst_0':bool,bb2':bool))
`;

val Ib = Define `INIT_B (hsel_1:bool,haddr_0:bool,hreadyout:bool,hresp_0:bool,hresp_1:bool,hws0:bool,hws1:bool,hws2:bool,hws3:bool,htrans_0:bool,htrans_1:bool,hburst_0:bool,bb2:bool) = T`;

val I1pb = Define `INIT_APB_B (paddr_0:bool,pwrite:bool,psel_0:bool,penable:bool,pdata_0:bool,m_0_0:bool,s_0_0_0:bool,hsel_1:bool,haddr_0:bool,hreadyout:bool,hresp_0:bool,hresp_1:bool,hws0:bool,hws1:bool,hws2:bool,hws3:bool,htrans_0:bool,htrans_1:bool,hburst_0:bool,bb2:bool) = ^(rhs(concl(Drule.SPEC_ALL INIT_APB_def)))`;

(* APB transition relation with master substituted by the bridge with ahb vars hidden away by exists quant*)
val R1pb = Define `TRANS_APB_B ((paddr_0:bool,pwrite:bool,psel_0:bool,penable:bool,pdata_0:bool,m_0_0:bool,s_0_0_0:bool),(paddr_0':bool,pwrite':bool,psel_0':bool,penable':bool,pdata_0':bool,m_0_0':bool,s_0_0_0':bool)) =
(?hsel_1 haddr_0 hreadyout hresp_0 hresp_1 hws0 hws1 hws2 hws3 htrans_0 htrans_1 hburst_0 bb2 hsel_1' haddr_0' hreadyout' hresp_0' hresp_1' hws0' hws1' hws2' hws3' htrans_0' htrans_1' hburst_0' bb2'. ^(lhs(concl(Drule.SPEC_ALL Rb)))) /\
^(lhs(concl(Drule.SPEC_ALL TRANS_S_def)))
`;

(* AHB transition relation with one generic slave replaced by the bridge with apb signals hidden *)
val R1hb = Define `TRANS_AHB_B ((htrans_0:bool,htrans_1:bool,htrans_m2_0:bool,htrans_m2_1:bool,htrans_m1_0:bool,htrans_m1_1:bool,htrans_m0_0:bool,htrans_m0_1:bool,hreadyout:bool,hresp_0:bool,hresp_1:bool,hgrant_0:bool,hgrant_1:bool,hgrant_2:bool,hbusreq_0:bool,hbusreq_1:bool,hbusreq_2:bool,hsel_0:bool,hsel_1:bool,haddr_0:bool,hws0:bool,hws1:bool,hws2:bool,hws3:bool,hmaster_0:bool,hburst_0:bool,hburst_m2_0:bool,hburst_m1_0:bool,bb0:bool,bb1:bool,bb2:bool,bb3:bool,hslv0splt_0:bool,hslv0splt_1:bool,hsplit_0,hsplit_1:bool,hmask_0:bool,hmask_1:bool),(htrans_0':bool,htrans_1':bool,htrans_m2_0':bool,htrans_m2_1':bool,htrans_m1_0':bool,htrans_m1_1':bool,htrans_m0_0':bool,htrans_m0_1':bool,hreadyout':bool,hresp_0':bool,hresp_1':bool,hgrant_0':bool,hgrant_1':bool,hgrant_2':bool,hbusreq_0':bool,hbusreq_1':bool,hbusreq_2':bool,hsel_0':bool,hsel_1':bool,haddr_0':bool,hws0':bool,hws1':bool,hws2':bool,hws3':bool,hmaster_0':bool,hburst_0':bool,hburst_m2_0':bool,hburst_m1_0':bool,bb0':bool,bb1':bool,bb2':bool,bb3':bool,hslv0splt_0':bool,hslv0splt_1':bool,hsplit_0',hsplit_1':bool,hmask_0':bool,hmask_1':bool)) = 
^(lhs(concl(Drule.SPEC_ALL TRANS_A_def)))  /\
^(lhs(concl(Drule.SPEC_ALL TRANS_CNT_def))) /\
^(lhs(concl(Drule.SPEC_ALL TRANS_M_0_def)))  /\ 
^(lhs(concl(Drule.SPEC_ALL TRANS_M_1_def))) /\
^(lhs(concl(Drule.SPEC_ALL TRANS_M_2_def))) /\
^(lhs(concl(Drule.SPEC_ALL TRANS_X_def))) /\  
^(lhs(concl(Drule.SPEC_ALL TRANS_D_def))) /\ 
^(lhs(concl(Drule.SPEC_ALL TRANS_S_0_def))) /\ 
(?paddr_0 pwrite psel_0 penable pdata_0 m_0_0 s_0_0_0 paddr_0' pwrite' psel_0' penable' pdata_0' m_0_0' s_0_0_0'. ^(lhs(concl(Drule.SPEC_ALL Rb))))`; 


(* theorems *)


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
     (REWRITE_RULE [IDLE_def,BUSY_def,NOSEQ_def,SEQ_def,OKAY_def,ERROR_def,RETRY_def,SPLIT_def,SINGLE_def,INC4_def] TRANS_S_1_def)))))) 
    THEN REWRITE_TAC [TRANS_S_1_def,IDLE_def,BUSY_def,NOSEQ_def,SEQ_def,OKAY_def,ERROR_def,RETRY_def,SPLIT_def,SINGLE_def,INC4_def] 
    ],
  ASM_REWRITE_TAC [] 
  ], 
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] 
])); 

(* AHB is the same as AHB with bridge as a generic slave whose apb signals are hidden *)
val ahb1 = save_thm("AHB_BRIDGE",prove(``^(lhs(concl (Drule.SPEC_ALL TRANS_AHB_def))) = ^(lhs(concl (Drule.SPEC_ALL R1hb)))``,
REWRITE_TAC [TRANS_AHB_def,R1hb,Rb]
THEN EQ_TAC THENL [
STRIP_TAC THEN REPEAT CONJ_TAC THEN ASM_REWRITE_TAC []
THEN MAP_EVERY EXISTS_TAC (exv (fst (strip_exists(List.last(strip_conj(rhs(concl (Drule.SPEC_ALL R1hb)))))))  
    (findAss (rhs(concl (Drule.SPEC_ALL TRANS_M_def)))))
THEN REWRITE_TAC [TRANS_M_def],
REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []
]));

(* APB + AHB ks *)

(* if f holds in APB then it holds in APB x AHB *)

(* first we need an R and I which are apb with the variables of AHB added in  *)

val I1ph = Define `INIT_APB_H(paddr_0:bool,pwrite:bool,psel_0:bool,penable:bool,pdata_0:bool,m_0_0:bool,s_0_0_0:bool,htrans_0:bool,htrans_1:bool,htrans_m2_0:bool,htrans_m2_1:bool,htrans_m1_0:bool,htrans_m1_1:bool,htrans_m0_0:bool,htrans_m0_1:bool,hreadyout:bool,hresp_0:bool,hresp_1:bool,hgrant_0:bool,hgrant_1:bool,hgrant_2:bool,hbusreq_0:bool,hbusreq_1:bool,hbusreq_2:bool,hsel_0:bool,hsel_1:bool,haddr_0:bool,hws0:bool,hws1:bool,hws2:bool,hws3:bool,hmaster_0:bool,hburst_0:bool,hburst_m2_0:bool,hburst_m1_0:bool,bb0:bool,bb1:bool,bb2:bool,bb3:bool,hslv0splt_0:bool,hslv0splt_1:bool,hsplit_0:bool,hsplit_1:bool,hmask_0:bool,hmask_1:bool) = 
	   ^(snd(dest_eq (concl(Drule.SPEC_ALL INIT_APB_def))))`;

val R1ph = Define `TRANS_APB_H((paddr_0:bool,pwrite:bool,psel_0:bool,penable:bool,pdata_0:bool,m_0_0:bool,s_0_0_0:bool,htrans_0:bool,htrans_1:bool,htrans_m2_0:bool,htrans_m2_1:bool,htrans_m1_0:bool,htrans_m1_1:bool,htrans_m0_0:bool,htrans_m0_1:bool,hreadyout:bool,hresp_0:bool,hresp_1:bool,hgrant_0:bool,hgrant_1:bool,hgrant_2:bool,hbusreq_0:bool,hbusreq_1:bool,hbusreq_2:bool,hsel_0:bool,hsel_1:bool,haddr_0:bool,hws0:bool,hws1:bool,hws2:bool,hws3:bool,hmaster_0:bool,hburst_0:bool,hburst_m2_0:bool,hburst_m1_0:bool,bb0:bool,bb1:bool,bb2:bool,bb3:bool,hslv0splt_0:bool,hslv0splt_1:bool,hsplit_0:bool,hsplit_1:bool,hmask_0:bool,hmask_1:bool),(paddr_0':bool,pwrite':bool,psel_0':bool,penable':bool,pdata_0':bool,m_0_0':bool,s_0_0_0':bool,htrans_0':bool,htrans_1':bool,htrans_m2_0':bool,htrans_m2_1':bool,htrans_m1_0':bool,htrans_m1_1':bool,htrans_m0_0':bool,htrans_m0_1':bool,hreadyout':bool,hresp_0':bool,hresp_1':bool,hgrant_0':bool,hgrant_1':bool,hgrant_2':bool,hbusreq_0':bool,hbusreq_1':bool,hbusreq_2':bool,hsel_0':bool,hsel_1':bool,haddr_0':bool,hws0':bool,hws1':bool,hws2':bool,hws3':bool,hmaster_0':bool,hburst_0':bool,hburst_m2_0':bool,hburst_m1_0':bool,bb0':bool,bb1':bool,bb2':bool,bb3':bool,hslv0splt_0':bool,hslv0splt_1':bool,hsplit_0':bool,hsplit_1':bool,hmask_0':bool,hmask_1':bool)) = ^(snd(dest_eq (concl(Drule.SPEC_ALL TRANS_APB_def))))`;



(*
val R1rph = REWRITE_RULE [Rm,Rs,m_idle,m_busy,m_noseq,m_seq,s_ok,s_err,s_retry,s_split,burst_single,burst_inc4] R1ph; 

val T1ph =  [(".",snd(dest_eq (concl(Drule.SPEC_ALL R1ph))))];
val T1rph = [(".",snd(dest_eq (concl(Drule.SPEC_ALL R1rph))))];


(*val bvmph = bvmp@bvmb;*)

val pstate = rand (lhs (concl(Drule.SPEC_ALL I1p)))
val pstate' = snd(pairSyntax.dest_pair(rand (lhs (concl(Drule.SPEC_ALL R1rp)))))
val hstate = rand (lhs (concl(Drule.SPEC_ALL I1rh)))
val hstate' = snd(pairSyntax.dest_pair(rand (lhs (concl(Drule.SPEC_ALL R1rh)))))
val astate = pairSyntax.list_mk_pair ((pairSyntax.strip_pair pstate)@(pairSyntax.strip_pair hstate))
val astate' = pairSyntax.list_mk_pair ((pairSyntax.strip_pair pstate')@(pairSyntax.strip_pair hstate'))

(* now the same for AHB *)
val I1hp = Define `INIT_AHB_P((^astate)) = ^(snd(dest_eq (concl(Drule.SPEC_ALL I1h))))`;
val R1hp = Define `TRANS_AHB_P((^astate),(^astate')) = ^(snd(dest_eq (concl(Drule.SPEC_ALL R1h))))`;
val R1rhp = REWRITE_RULE [Rm,Rs,m_idle,m_busy,m_noseq,m_seq,s_ok,s_err,s_retry,s_split,burst_single,burst_inc4] R1hp;
val T1hp =  [(".",snd(dest_eq (concl(Drule.SPEC_ALL R1hp))))];
val T1rhp = [(".",snd(dest_eq (concl(Drule.SPEC_ALL R1rhp))))];

(*val bvmhp = bvmh@bvmb;*)
*) 


val _ = export_theory()
