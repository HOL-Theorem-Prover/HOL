open HolKernel Parse boolLib bossLib

val _ = new_theory "amba_ahb"; 

open boolSyntax;
open bossLib;
open ctl2muTheory;
open cearTools;
open Ho_Rewrite;
open Tactical;
open Tactic;
open PairRules;
open holCheckTools
open bddTools
open ctlTheory
open ctlSyntax
open ksTools


(* transfer types {3-9} *)
val m_idle = Define `IDLE  (htrans_0,htrans_1) =  ~htrans_0 /\ ~htrans_1`;
val m_busy = Define `BUSY  (htrans_0,htrans_1) =   htrans_0 /\ ~htrans_1`;
val m_noseq= Define `NOSEQ (htrans_0,htrans_1) =  ~htrans_0 /\  htrans_1`;
val m_seq =  Define `SEQ   (htrans_0,htrans_1) =   htrans_0 /\  htrans_1`;

(* slave responses {3-21} *)
val s_ok =    Define `OKAY  (hresp_0,hresp_1) =  ~hresp_0 /\ ~hresp_1`;
val s_err =   Define `ERROR (hresp_0,hresp_1) =   hresp_0 /\ ~hresp_1`;
val s_retry = Define `RETRY (hresp_0,hresp_1) =  ~hresp_0 /\  hresp_1`;
val s_split = Define `SPLIT (hresp_0,hresp_1) =   hresp_0 /\  hresp_1`;

(* burst types {3-11} TODO: fill in the rest *)
val burst_single = Define `SINGLE (hburst_0) = ~hburst_0`;
val burst_inc4 =   Define `INC4   (hburst_0) =  hburst_0`;

(* HTRANS = IDLE  and no one is requesting the bus*)
val Im = Define `INIT_M (htrans_0,htrans_1,hbusreq_0,hbusreq_1,hbusreq_2,bb0,bb1,bb2,bb3,htrans_m1_0,htrans_m1_1,htrans_m2_0,htrans_m2_1) = IDLE(htrans_0,htrans_1) /\ IDLE(htrans_m1_0,htrans_m1_1) /\ IDLE(htrans_m2_0,htrans_m2_1) /\ ~hbusreq_0 /\ ~hbusreq_1 /\ ~hbusreq_2 /\ ~bb0 /\ ~bb1 /\ ~bb2 /\ ~bb3`;

(* HREADYOUT [FAQ] /\ HRESP = OKAY [FAQ] *)
val Is = Define `INIT_S (hsel_0,hsel_1,haddr_0,hreadyout,hresp_0,hresp_1,hws0,hws1,hws2,hws3,hslv0splt_0,hslv0splt_1,hsplit_0,hsplit_1) = hreadyout /\ OKAY(hresp_0,hresp_1) /\ ~hws0 /\ ~hws1 /\ ~hws2 /\ ~hws3 /\ ~hslv0splt_0 /\ ~hslv0splt_1 /\ ~hsplit_0 /\ ~hsplit_1 /\ (hsel_0=~haddr_0) /\ (hsel_1 = haddr_0)`;

(* 0 is dummy master
   1 is default master 
   2 is another master *)
(* ~hgrant_0 /\ hgrant_1 /\ ~hgrant_2 [default master has the bus :FAQ] *)
val Ia = Define `INIT_A (hgrant_0,hgrant_1,hgrant_2,hmaster_0,hmask_0,hmask_1) = ~hgrant_0 /\ hgrant_1 /\ ~hgrant_2 /\ ~hmaster_0 /\ ~hmask_0 /\ ~hmask_1`;

(* arbiter: simple priority based *)
val Ra = Define `TRANS_A ((hreadyout:bool,hbusreq_1:bool,hbusreq_2:bool,hgrant_0:bool,hgrant_1:bool,hgrant_2:bool,hmaster_0:bool,hburst_0:bool,bb2:bool,hmask_0:bool,hmask_1:bool,hresp_0:bool,hresp_1:bool,hsplit_0:bool,hsplit_1:bool),(hreadyout':bool,hbusreq_1':bool,hbusreq_2':bool,hgrant_0':bool,hgrant_1':bool,hgrant_2':bool,hmaster_0':bool,hburst_0':bool,bb2':bool,hmask_0':bool,hmask_1':bool,hresp_0':bool,hresp_1':bool,hsplit_0':bool,hsplit_1':bool)) =
(* give to #2 unless I want it, defaulting to me *)
     (hgrant_1' =  (if hmask_0 then F else hbusreq_1) \/ ~(if hmask_1 then F else hbusreq_2)) /\ 
(* give it to me if I want and #1 does not, defaulting to #1 *)
     (hgrant_2' =  ~(if hmask_0 then F else hbusreq_1) /\ (if hmask_1 then F else hbusreq_2)) /\ 
(* dummy master is only granted if all other masters are waiting on split transfers *)
     (hgrant_0' = (hsplit_0 /\ hsplit_1) \/ (hmask_0 /\ hmask_1)) /\ 
(* whoever is granted gets bus ownership when hreadyout goes high *)
     (hmaster_0' = if ~hreadyout then hmaster_0 else ~hgrant_1) /\
(* record the number of a split master for future masking/unmasking *)
     (hmask_0' = if SPLIT(hresp_0,hresp_1) /\ ~hreadyout /\ ~hmaster_0 then T else if hsplit_0 then F else hmask_0) /\        
     (hmask_1' = if SPLIT(hresp_0,hresp_1) /\ ~hreadyout /\ hmaster_0 then T else if hsplit_1 then F else hmask_1)         
`; 

(* dummy master just generates IDLE transfers *)
val Rm0 = Define `TRANS_M_0 ((hgrant_0:bool,htrans_m0_0:bool,htrans_m0_1:bool,hbusreq_0:bool),(hgrant_0':bool,htrans_m0_0':bool,htrans_m0_1':bool,hbusreq_0':bool)) = 
	  (hgrant_0 ==> IDLE(htrans_m0_0',htrans_m0_1')) /\ (* signal IDLE on grant *)
          (hbusreq_0' = F)`; 

(* default master is #1, gets the bus if no one asks for it*) 
val Rm1 = Define `TRANS_M_1  ((hgrant_1:bool,htrans_m1_0:bool,htrans_m1_1:bool,hbusreq_1:bool,hresp_0:bool,hresp_1:bool,hreadyout:bool,hburst_m1_0:bool,bb2:bool),(hgrant_1':bool,htrans_m1_0':bool,htrans_m1_1':bool,hbusreq_1':bool,hresp_0':bool,hresp_1':bool,hreadyout':bool,hburst_m1_0':bool,bb2':bool)) = 	 
(* keep requesting bus if you get ownership (so arbiter only takes it away for higher priorty req) until transfer is done *)
	 (~(OKAY(hresp_0,hresp_1) /\ hreadyout) /\ hgrant_1   ==> hbusreq_1') /\ 
(* starting transfer (if not already in the middle of one) *) 
	 (hreadyout /\ IDLE(htrans_m1_0,htrans_m1_1) /\ OKAY(hresp_0,hresp_1) /\ hgrant_1
                            ==> NOSEQ(htrans_m1_0',htrans_m1_1')) /\ 
(* switch to SEQ mode (latching hmaster_0 is ok here because I know I have at least one more bus cycle) *)
         (NOSEQ(htrans_m1_0,htrans_m1_1)  /\ OKAY(hresp_0,hresp_1) /\ INC4(hburst_m1_0)  /\ hgrant_1  
                            ==> (BUSY(htrans_m1_0',htrans_m1_1') \/ SEQ(htrans_m1_0',htrans_m1_1')) /\ INC4(hburst_m1_0')) /\
(* mid-burst bookkeeping - may signal BUSY or SEQ after a SEQ (as long as burst beats remain) (ditto latching) *)
         (SEQ(htrans_m1_0,htrans_m1_1)  /\ OKAY(hresp_0,hresp_1) /\ ~bb2  /\ hgrant_1
                            ==> (BUSY(htrans_m1_0',htrans_m1_1') \/ SEQ(htrans_m1_0',htrans_m1_1')) /\ INC4(hburst_m1_0')) /\
(* mid-burst bookkeeping - may not signal BUSY after a BUSY (as long as burst beats remain) (ditto latching) *)
(* specification does not say this but we need it to prevent livelock *)
         (BUSY(htrans_m1_0,htrans_m1_1) /\ ~bb2   /\ OKAY(hresp_0,hresp_1) /\ hgrant_1 
                            ==> (SEQ(htrans_m1_0',htrans_m1_1')) /\ INC4(hburst_m1_0')) /\
(* response to first cycle of retry - no need to reset bb; they take an extra cycle to reset but retry is two cycle so no prob *)
	 (~hreadyout /\ RETRY(hresp_0,hresp_1) /\ hgrant_1
	                    ==> IDLE(htrans_m1_0',htrans_m1_1')) /\
(* response to second cycle of retry - {3-22} says master *must* retry *)
	 (hreadyout /\ RETRY(hresp_0,hresp_1) /\ hgrant_1
	                    ==> NOSEQ(htrans_m1_0',htrans_m1_1')) /\
(* response to first cycle of error ;{3-23} gives the option of continuing or cancelling transfer - we choose cancel*)
	 (~hreadyout /\ ERROR(hresp_0,hresp_1) /\ hgrant_1
	                    ==> IDLE(htrans_m1_0',htrans_m1_1')) /\
(* response to second cycle of error ;{3-23} gives the option of continuing or cancelling transfer - we choose cancel*)
	 (hreadyout /\ ERROR(hresp_0,hresp_1) /\ hgrant_1
	                    ==> IDLE(htrans_m1_0',htrans_m1_1')) 
`; 

(* a generic master *)
val Rm2 = Define `TRANS_M_2  ((hgrant_2:bool,htrans_m2_0:bool,htrans_m2_1:bool,hbusreq_2:bool,hresp_0:bool,hresp_1:bool,hreadyout:bool,hburst_m2_0:bool,bb2:bool),(hgrant_2':bool,htrans_m2_0':bool,htrans_m2_1':bool,hbusreq_2':bool,hresp_0':bool,hresp_1':bool,hreadyout':bool,hburst_m2_0':bool,bb2':bool)) = 	 
(* keep requesting bus if you get ownership (so arbiter only takes it away for higher priorty req) until transfer is done *)
	  (~(OKAY(hresp_0,hresp_1) /\ hreadyout) /\ hgrant_2 ==> hbusreq_2') /\
(* starting transfer (if not already in the middle of one) *) 
	 (hreadyout  /\ IDLE(htrans_m2_0,htrans_m2_1)  /\ OKAY(hresp_0,hresp_1) /\ hgrant_2
                            ==> NOSEQ(htrans_m2_0',htrans_m2_1')) /\ 
(* switch to SEQ mode (latching hmaster_0 is ok here because I know I have at least one more bus cycle) *)
         (NOSEQ(htrans_m2_0,htrans_m2_1) /\ OKAY(hresp_0,hresp_1) /\ INC4(hburst_m2_0) /\ hgrant_2
                            ==> (BUSY(htrans_m2_0',htrans_m2_1') \/ SEQ(htrans_m2_0',htrans_m2_1')) /\ INC4(hburst_m2_0')) /\
(* mid-burst bookkeeping - may signal BUSY or SEQ after a SEQ (as long as burst beats remain) (ditto latching) *)
         (SEQ(htrans_m2_0,htrans_m2_1) /\ ~bb2  /\ OKAY(hresp_0,hresp_1) /\ hgrant_2
                            ==> (BUSY(htrans_m2_0',htrans_m2_1') \/ SEQ(htrans_m2_0',htrans_m2_1')) /\ INC4(hburst_m2_0')) /\
(* mid-burst bookkeeping - may not signal BUSY after a BUSY (as long as burst beats remain) (ditto latching) *)
(* specification does not say this but we need it to prevent livelock *)
         (BUSY(htrans_m2_0,htrans_m2_1) /\ ~bb2   /\ OKAY(hresp_0,hresp_1) /\ hgrant_2 
                            ==> (SEQ(htrans_m2_0',htrans_m2_1')) /\ INC4(hburst_m2_0')) /\
(* response to first cycle of retry - no need to reset bb; they take an extra cycle to reset but retry is two cycle so no prob *)
	 (~hreadyout /\ RETRY(hresp_0,hresp_1) /\ hgrant_2
	                    ==> IDLE(htrans_m2_0',htrans_m2_1')) /\
(* response to second cycle of retry - {3-22} says master *must* retry *)
	 (hreadyout /\ RETRY(hresp_0,hresp_1) /\ hgrant_2
	                    ==> NOSEQ(htrans_m2_0',htrans_m2_1')) /\
(* response to first cycle of error ;{3-23} gives the option of continuing or cancelling transfer - we choose cancel*)
	 (~hreadyout /\ ERROR(hresp_0,hresp_1) /\ hgrant_2
	                    ==> IDLE(htrans_m2_0',htrans_m2_1')) /\
(* response to second cycle of error ;{3-23} gives the option of continuing or cancelling transfer - we choose cancel*)
	 (hreadyout /\ ERROR(hresp_0,hresp_1) /\ hgrant_2
	                    ==> IDLE(htrans_m2_0',htrans_m2_1')) 
`;

(* mux, which sends the current bus owner's signals through *)
(* technically we should be using hmaster_0 here but can't because it is triggered in the same cycle (see Ra and {3-31})*)
val Rx = Define `TRANS_X ((hreadyout:bool,hgrant_1:bool,hgrant_2:bool,htrans_0:bool,htrans_1:bool,hburst_0:bool,htrans_m1_0:bool,htrans_m1_1:bool,hburst_m1_0:bool,htrans_m2_0:bool,htrans_m2_1:bool,hburst_m2_0:bool,htrans_m0_0:bool,htrans_m0_1:bool),(hreadyout':bool,hgrant_1':bool,hgrant_2':bool,htrans_0':bool,htrans_1':bool,hburst_0':bool,htrans_m0_0':bool,htrans_m0_1':bool)) =
(htrans_0' = if ~hreadyout then htrans_0 else if hgrant_1 then htrans_m1_0 else if hgrant_2 then htrans_m2_0 else htrans_m0_0) /\ 
(htrans_1' = if ~hreadyout then htrans_1 else if hgrant_1 then htrans_m1_1 else if hgrant_2 then htrans_m2_1 else htrans_m0_1) /\ 
(hburst_0' = if ~hreadyout then hburst_0 else if hgrant_1 then hburst_m1_0 else if hgrant_2 then hburst_m2_0 else F)`;

(* decoder, decodes higher order address bits to figure out which slave is being targeted *)
val Rd = Define `TRANS_D ((hsel_0:bool,hsel_1:bool,haddr_0:bool,hgrant_1:bool,hgrant_2:bool, hreadyout:bool,htrans_0:bool,htrans_1:bool),(hsel_0':bool,hsel_1':bool,haddr_0':bool,hgrant_1':bool,hgrant_2':bool, hreadyout':bool,htrans_0':bool,htrans_1':bool)) =  
(* we only decode if hreadyout goes high, else hold old value *)
 (hsel_0' = if hreadyout then ~haddr_0 else hsel_0) /\ 
 (hsel_1' = if hreadyout then haddr_0 else hsel_1) 
`;

(* global counters go here *)
val RCn = Define `TRANS_CNT ((hws0:bool,hws1:bool,hws2:bool,hws3:bool,hreadyout:bool,bb0:bool,bb1:bool,bb2:bool,bb3:bool,hburst_0:bool,htrans_0:bool,htrans_1:bool),(hws0':bool,hws1':bool,hws2':bool,hws3':bool, hreadyout':bool,bb0':bool,bb1':bool,bb2':bool,bb3':bool,hburst_0':bool,htrans_0':bool,htrans_1':bool)) = 
(* wait state counter *)
(* climb to hws2 on ~hreadyout, resetting on hreadyout (slaves do this if hws2 is reached) *)
    (hws0' = ~hreadyout) /\ 
    (hws1' = ~hreadyout /\ hws0) /\ 
    (hws2' = ~hreadyout /\ hws1) /\ 
(*  (hws3' = ~hreadyout /\ hws2) /\ *) (* no need for this because the last waitstate is when slave drives hreadyout high on *next* tick *)
(* burst beat counter *) 
(* climb to bb2; bb1-2 reset after bb2 goes high; hold on ~hreadyout \/ BSY*)
    (bb0' = hreadyout /\ NOSEQ(htrans_0,htrans_1)) /\ 
    (bb1' = ~bb2 /\ SEQ(htrans_0,htrans_1)  /\ if hreadyout /\ ~BUSY(htrans_0,htrans_1) then bb0 else bb1) /\ 
    (bb2' = ~bb2 /\ SEQ(htrans_0,htrans_1)  /\ if hreadyout /\ ~BUSY(htrans_0,htrans_1) then bb1 else bb2)  
(*  (bb3' = ~bb3 /\ SEQ(htrans_0,htrans_1)  /\ if hreadyout then bb2 else bb3) *)
`;

(* slave 1 (SPLIT-capable) *)
val Rs0 = Define `TRANS_S_0 ((hsel_0:bool,haddr_0:bool,hreadyout:bool,hresp_0:bool,hresp_1:bool,hws0:bool,hws1:bool,hws2:bool,hws3:bool,htrans_0:bool,htrans_1:bool,hburst_0:bool,bb2:bool,hslv0splt_0:bool,hslv0splt_1:bool,hsplit_0:bool,hsplit_1:bool,hgrant_0:bool,hmaster_0:bool),(hsel_0':bool,haddr_0':bool,hreadyout':bool,hresp_0':bool,hresp_1':bool,hws0':bool,hws1':bool,hws2':bool,hws3':bool,htrans_0':bool,htrans_1':bool,hburst_0':bool,bb2':bool,hslv0splt_0':bool,hslv0splt_1':bool,hsplit_0':bool,hsplit_1':bool,hgrant_0':bool,hmaster_0':bool)) =
(* force hreadyout to high because slave can't do more than 4 (TODO:16 in spec) wait states *)   
         (hsel_0 /\ hws2 ==> hreadyout') /\
(* signal end of transfer (single or part of a burst) (don't need to check for rdy because value of rdy irrelevent to address phase) *)
	 (hsel_0 /\ (NOSEQ(htrans_0,htrans_1) \/ SEQ(htrans_0,htrans_1)) /\  OKAY(hresp_0,hresp_1) ==> OKAY(hresp_0',hresp_1') /\ hreadyout') /\ 
(* {3-9} slave response to IDLE is READY + OKAY *)  
         (hsel_0 /\ IDLE(htrans_0,htrans_1) ==> hreadyout' /\  OKAY(hresp_0',hresp_1')) /\
(* {3-9} slave response to BUSY is OKAY *)  
         (hsel_0 /\ BUSY(htrans_0,htrans_1) ==> OKAY(hresp_0',hresp_1')) /\
(* drive second cycle of RETRY *)
	 (hsel_0 /\ ~hreadyout /\ ~(IDLE(htrans_0,htrans_1) \/ BUSY(htrans_0,htrans_1)) /\ RETRY(hresp_0,hresp_1) 
                ==> hreadyout' /\ RETRY(hresp_0',hresp_1')) /\
(* drive second cycle of ERROR *)
	 (hsel_0 /\ ~hreadyout  /\ ~(IDLE(htrans_0,htrans_1) \/ BUSY(htrans_0,htrans_1)) /\ ERROR(hresp_0,hresp_1) 
                ==> hreadyout' /\ ERROR(hresp_0',hresp_1')) /\
(* drive second cycle of SPLIT *)
	 (hsel_0 /\ ~hreadyout  /\ ~(IDLE(htrans_0,htrans_1) \/ BUSY(htrans_0,htrans_1)) /\ SPLIT(hresp_0,hresp_1) 
                ==> hreadyout' /\ SPLIT(hresp_0',hresp_1')) /\
(* if m0 is granted then respond with OK always (to prevent RETRY or SPLIT on m0 *)
	 (hsel_0 /\ hgrant_0 ==>  OKAY(hresp_0',hresp_1')) /\
(* if SPLITing record current master's number *)
	 (hslv0splt_0' = if (hsel_0 /\ ~hreadyout /\ SPLIT(hresp_0,hresp_1) /\ ~hmaster_0) then ~hmaster_0 else hslv0splt_0) /\
	 (hslv0splt_1' = if (hsel_0 /\ ~hreadyout /\ SPLIT(hresp_0,hresp_1) /\ hmaster_0) then hmaster_0 else hslv0splt_1) /\ 
(* note we don't do anything about slave asserting HSPLIT because abstracting that away *)
(* however, we do need to ensure that if we have split on Mx, we don't assert HSPLITy where x!=y *)
(* with >1 split-capable slave we would have to use HSPLITx to avoid conflict, but with only one we can access HSPLIT directly *)
	 (~hslv0splt_0 /\ ~hslv0splt_1 ==> ~hsplit_0' /\ ~hsplit_1') /\   
	 (hslv0splt_0 /\ ~hslv0splt_1 ==> ~hsplit_1') /\   
	 (~hslv0splt_0 /\ hslv0splt_1 ==> ~hsplit_0')    
(* WIP:we leave it to the arbiter to drive down hslv0splt once it sees hsplit asserted *)
`;

(* slave 2 *)
val Rs1 = Define `TRANS_S_1 ((hsel_1:bool,haddr_0:bool,hreadyout:bool,hresp_0:bool,hresp_1:bool,hws0:bool,hws1:bool,hws2:bool,hws3:bool,htrans_0:bool,htrans_1:bool,hburst_0:bool,bb2:bool),(hsel_1':bool,haddr_0':bool,hreadyout':bool,hresp_0':bool,hresp_1':bool,hws0':bool,hws1':bool,hws2':bool,hws3':bool,htrans_0':bool,htrans_1':bool,hburst_0':bool,bb2':bool)) =
(* force hreadyout to high because slave can't do more than 4 (TODO:16 in spec) wait states *)   
         (hsel_1 /\ hws2 ==> hreadyout') /\
(* signal end of transfer (single or part of a burst) (don't need to check for rdy because value of rdy irrelevent to address phase) *)
	 (hsel_1 /\ (NOSEQ(htrans_0,htrans_1) \/ SEQ(htrans_0,htrans_1)) /\  OKAY(hresp_0,hresp_1) ==> OKAY(hresp_0',hresp_1') /\ hreadyout') /\ 
(* {3-9} slave response to IDLE is READY + OKAY *)  
         (hsel_1 /\ IDLE(htrans_0,htrans_1) ==> hreadyout' /\  OKAY(hresp_0',hresp_1'))  /\
(* {3-9} slave response to BUSY is OKAY *)  
         (hsel_1 /\ BUSY(htrans_0,htrans_1) ==> OKAY(hresp_0',hresp_1')) /\
(* drive second cycle of RETRY *)
	 (hsel_1 /\ ~hreadyout  /\ ~(IDLE(htrans_0,htrans_1) \/ BUSY(htrans_0,htrans_1)) /\ RETRY(hresp_0,hresp_1) 
		==> hreadyout' /\ RETRY(hresp_0',hresp_1')) /\
(* drive second cycle of ERROR *)
	 (hsel_1 /\ ~hreadyout  /\ ~(IDLE(htrans_0,htrans_1) \/ BUSY(htrans_0,htrans_1)) /\ ERROR(hresp_0,hresp_1) 
                ==> hreadyout' /\ ERROR(hresp_0',hresp_1')) /\
(* this slave is not SPLIT-capable *)
         (hsel_1 ==> ~SPLIT(hresp_0',hresp_1'))
`;


val I1h = Define `INIT_AHB (htrans_0:bool,htrans_1:bool,htrans_m2_0:bool,htrans_m2_1:bool,htrans_m1_0:bool,htrans_m1_1:bool,htrans_m0_0:bool,htrans_m0_1:bool,hreadyout:bool,hresp_0:bool,hresp_1:bool,hgrant_0:bool,hgrant_1:bool,hgrant_2:bool,hbusreq_0:bool,hbusreq_1:bool,hbusreq_2:bool,hsel_0:bool,hsel_1:bool,haddr_0:bool,hws0:bool,hws1:bool,hws2:bool,hws3:bool,hmaster_0:bool,hburst_0:bool,hburst_m2_0:bool,hburst_m1_0:bool,bb0:bool,bb1:bool,bb2:bool,bb3:bool,hslv0splt_0:bool,hslv0splt_1:bool,hsplit_0:bool,hsplit_1:bool,hmask_0:bool,hmask_1:bool) = 
^(lhs(concl(Drule.SPEC_ALL Im))) /\
^(lhs(concl(Drule.SPEC_ALL Ia))) /\
^(lhs(concl(Drule.SPEC_ALL Is)))`;

val R1h = Define `TRANS_AHB ((htrans_0:bool,htrans_1:bool,htrans_m2_0:bool,htrans_m2_1:bool,htrans_m1_0:bool,htrans_m1_1:bool,htrans_m0_0:bool,htrans_m0_1:bool,hreadyout:bool,hresp_0:bool,hresp_1:bool,hgrant_0:bool,hgrant_1:bool,hgrant_2:bool,hbusreq_0:bool,hbusreq_1:bool,hbusreq_2:bool,hsel_0:bool,hsel_1:bool,haddr_0:bool,hws0:bool,hws1:bool,hws2:bool,hws3:bool,hmaster_0:bool,hburst_0:bool,hburst_m2_0:bool,hburst_m1_0:bool,bb0:bool,bb1:bool,bb2:bool,bb3:bool,hslv0splt_0:bool,hslv0splt_1:bool,hsplit_0:bool,hsplit_1:bool,hmask_0:bool,hmask_1:bool),(htrans_0':bool,htrans_1':bool,htrans_m2_0':bool,htrans_m2_1':bool,htrans_m1_0':bool,htrans_m1_1':bool,htrans_m0_0':bool,htrans_m0_1':bool,hreadyout':bool,hresp_0':bool,hresp_1':bool,hgrant_0':bool,hgrant_1':bool,hgrant_2':bool,hbusreq_0':bool,hbusreq_1':bool,hbusreq_2':bool,hsel_0':bool,hsel_1':bool,haddr_0':bool,hws0':bool,hws1':bool,hws2':bool,hws3':bool,hmaster_0':bool,hburst_0':bool,hburst_m2_0':bool,hburst_m1_0':bool,bb0':bool,bb1':bool,bb2':bool,bb3':bool,hslv0splt_0':bool,hslv0splt_1':bool,hsplit_0':bool,hsplit_1':bool,hmask_0':bool,hmask_1':bool)) = 
^(lhs(concl(Drule.SPEC_ALL Ra)))  /\
^(lhs(concl(Drule.SPEC_ALL RCn))) /\
^(lhs(concl(Drule.SPEC_ALL Rm0)))  /\ 
^(lhs(concl(Drule.SPEC_ALL Rm1))) /\
^(lhs(concl(Drule.SPEC_ALL Rm2))) /\
^(lhs(concl(Drule.SPEC_ALL Rx))) /\  
^(lhs(concl(Drule.SPEC_ALL Rd))) /\ 
^(lhs(concl(Drule.SPEC_ALL Rs0))) /\ 
^(lhs(concl(Drule.SPEC_ALL Rs1)))`;

val _ = export_theory()