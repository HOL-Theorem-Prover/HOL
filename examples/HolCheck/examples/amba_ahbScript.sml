
(* Definitions for AMBA AHB bus. See AMBA Specification v2.0 from ARM for details  *)

open HolKernel Parse boolLib bossLib 
(* app load ["pairSyntax","mod16Theory","commonTools","ksTools","listSyntax"] *)

val _ = new_theory("amba_ahb")

open HolKernel Parse boolLib bossLib

open pairSyntax boolTheory listSyntax
open mod16Theory commonTools ksTools amba_common



(* -------------------- abbreviations for readibility of main defs -------------------- *)

val BB_INC_def = Define `BB_INC n (^bbv) = if n=4 then MOD16_INC4 (^bbv) else MOD16_INC (^bbv)`;

val WS_INC_def = Define `WS_INC n (^hwsv) = if n=4 then MOD16_INC4 (^hwsv) else MOD16_INC (^hwsv)`;

(* transfer types {3-9} *)
val IDLE_def = Define `IDLE  (htrans_0,htrans_1) =  ~htrans_0 /\ ~htrans_1`;
val BUSY_def = Define `BUSY  (htrans_0,htrans_1) =   htrans_0 /\ ~htrans_1`;
val NOSEQ_def = Define `NOSEQ (htrans_0,htrans_1) =  ~htrans_0 /\  htrans_1`;
val SEQ_def =  Define `SEQ   (htrans_0,htrans_1) =   htrans_0 /\  htrans_1`;

(* slave responses {3-21} *)
val OKAY_def =    Define `OKAY  (hresp_0,hresp_1) =  ~hresp_0 /\ ~hresp_1`;
val ERROR_def =   Define `ERROR (hresp_0,hresp_1) =   hresp_0 /\ ~hresp_1`;
val RETRY_def = Define `RETRY (hresp_0,hresp_1) =  ~hresp_0 /\  hresp_1`;
val SPLIT_def = Define `SPLIT (hresp_0,hresp_1) =   hresp_0 /\  hresp_1`;

(* burst types {3-11} TODO: fill in the rest *)
val SINGLE_def = Define `SINGLE (hburst_0) = ~hburst_0`;
val INC4_def =   Define `INC4   (hburst_0) =  hburst_0`;

val INC4M_def = Define `INC4M n (^burstm_vars) = 
if n=0 then INC4(hburstm_0_0) 
else if n=1 then INC4(hburstm_1_0) 
else if n=2 then INC4(hburstm_2_0) 
else if n=3 then INC4(hburstm_3_0) 
else if n=4 then INC4(hburstm_4_0) 
else if n=5 then INC4(hburstm_5_0) 
else if n=6 then INC4(hburstm_6_0) 
else if n=7 then INC4(hburstm_7_0) 
else if n=8 then INC4(hburstm_8_0) 
else if n=9 then INC4(hburstm_9_0) 
else if n=10 then INC4(hburstm_10_0) 
else if n=11 then INC4(hburstm_11_0) 
else if n=12 then INC4(hburstm_12_0) 
else if n=13 then INC4(hburstm_13_0) 
else if n=14 then INC4(hburstm_14_0)  else INC4(hburstm_15_0) `;

val BURSTM0_def = Define `BURSTM0 n (^burstm_vars) = 
if n=0 then hburstm_0_0
else if n=1 then hburstm_1_0 
else if n=2 then hburstm_2_0 
else if n=3 then hburstm_3_0 
else if n=4 then hburstm_4_0 
else if n=5 then hburstm_5_0 
else if n=6 then hburstm_6_0 
else if n=7 then hburstm_7_0 
else if n=8 then hburstm_8_0 
else if n=9 then hburstm_9_0 
else if n=10 then hburstm_10_0 
else if n=11 then hburstm_11_0 
else if n=12 then hburstm_12_0 
else if n=13 then hburstm_13_0 
else if n=14 then hburstm_14_0  else hburstm_15_0`; 

val TRANSM0_def = Define `TRANSM0 n (^transm_vars) = 
if n=0 then htransm_0_0 
else if n=1 then htransm_1_0
else if n=2 then htransm_2_0
else if n=3 then htransm_3_0
else if n=4 then htransm_4_0
else if n=5 then htransm_5_0
else if n=6 then htransm_6_0
else if n=7 then htransm_7_0
else if n=8 then htransm_8_0
else if n=9 then htransm_9_0
else if n=10 then htransm_10_0
else if n=11 then htransm_11_0
else if n=12 then htransm_12_0
else if n=13 then htransm_13_0
else if n=14 then htransm_14_0 else htransm_15_0`;

val TRANSM1_def = Define `TRANSM1 n (^transm_vars) = 
if n=0 then htransm_0_1 
else if n=1 then htransm_1_1
else if n=2 then htransm_2_1
else if n=3 then htransm_3_1
else if n=4 then htransm_4_1
else if n=5 then htransm_5_1
else if n=6 then htransm_6_1
else if n=7 then htransm_7_1
else if n=8 then htransm_8_1
else if n=9 then htransm_9_1
else if n=10 then htransm_10_1
else if n=11 then htransm_11_1
else if n=12 then htransm_12_1
else if n=13 then htransm_13_1
else if n=14 then htransm_14_1 else htransm_15_1`;

val IDLEM_def = Define `IDLEM n (^transm_vars) = 
if n=0 then IDLE(htransm_0_0,htransm_0_1) 
else if n=1 then IDLE(htransm_1_0,htransm_1_1)
else if n=2 then IDLE(htransm_2_0,htransm_2_1)
else if n=3 then IDLE(htransm_3_0,htransm_3_1)
else if n=4 then IDLE(htransm_4_0,htransm_4_1)
else if n=5 then IDLE(htransm_5_0,htransm_5_1)
else if n=6 then IDLE(htransm_6_0,htransm_6_1)
else if n=7 then IDLE(htransm_7_0,htransm_7_1)
else if n=8 then IDLE(htransm_8_0,htransm_8_1)
else if n=9 then IDLE(htransm_9_0,htransm_9_1)
else if n=10 then IDLE(htransm_10_0,htransm_10_1)
else if n=11 then IDLE(htransm_11_0,htransm_11_1)
else if n=12 then IDLE(htransm_12_0,htransm_12_1)
else if n=13 then IDLE(htransm_13_0,htransm_13_1)
else if n=14 then IDLE(htransm_14_0,htransm_14_1) else IDLE(htransm_15_0,htransm_15_1)`;

val BUSYM_def = Define `BUSYM n (^transm_vars) = 
if n=0 then BUSY(htransm_0_0,htransm_0_1) 
else if n=1 then BUSY(htransm_1_0,htransm_1_1)
else if n=2 then BUSY(htransm_2_0,htransm_2_1)
else if n=3 then BUSY(htransm_3_0,htransm_3_1)
else if n=4 then BUSY(htransm_4_0,htransm_4_1)
else if n=5 then BUSY(htransm_5_0,htransm_5_1)
else if n=6 then BUSY(htransm_6_0,htransm_6_1)
else if n=7 then BUSY(htransm_7_0,htransm_7_1)
else if n=8 then BUSY(htransm_8_0,htransm_8_1)
else if n=9 then BUSY(htransm_9_0,htransm_9_1)
else if n=10 then BUSY(htransm_10_0,htransm_10_1)
else if n=11 then BUSY(htransm_11_0,htransm_11_1)
else if n=12 then BUSY(htransm_12_0,htransm_12_1)
else if n=13 then BUSY(htransm_13_0,htransm_13_1)
else if n=14 then BUSY(htransm_14_0,htransm_14_1) else BUSY(htransm_15_0,htransm_15_1)`;

val NOSEQM_def = Define `NOSEQM n (^transm_vars) = 
if n=0 then NOSEQ(htransm_0_0,htransm_0_1) 
else if n=1 then NOSEQ(htransm_1_0,htransm_1_1)
else if n=2 then NOSEQ(htransm_2_0,htransm_2_1)
else if n=3 then NOSEQ(htransm_3_0,htransm_3_1)
else if n=4 then NOSEQ(htransm_4_0,htransm_4_1)
else if n=5 then NOSEQ(htransm_5_0,htransm_5_1)
else if n=6 then NOSEQ(htransm_6_0,htransm_6_1)
else if n=7 then NOSEQ(htransm_7_0,htransm_7_1)
else if n=8 then NOSEQ(htransm_8_0,htransm_8_1)
else if n=9 then NOSEQ(htransm_9_0,htransm_9_1)
else if n=10 then NOSEQ(htransm_10_0,htransm_10_1)
else if n=11 then NOSEQ(htransm_11_0,htransm_11_1)
else if n=12 then NOSEQ(htransm_12_0,htransm_12_1)
else if n=13 then NOSEQ(htransm_13_0,htransm_13_1)
else if n=14 then NOSEQ(htransm_14_0,htransm_14_1) else NOSEQ(htransm_15_0,htransm_15_1)`;

val SEQM_def = Define `SEQM n (^transm_vars) = 
if n=0 then SEQ(htransm_0_0,htransm_0_1) 
else if n=1 then SEQ(htransm_1_0,htransm_1_1)
else if n=2 then SEQ(htransm_2_0,htransm_2_1)
else if n=3 then SEQ(htransm_3_0,htransm_3_1)
else if n=4 then SEQ(htransm_4_0,htransm_4_1)
else if n=5 then SEQ(htransm_5_0,htransm_5_1)
else if n=6 then SEQ(htransm_6_0,htransm_6_1)
else if n=7 then SEQ(htransm_7_0,htransm_7_1)
else if n=8 then SEQ(htransm_8_0,htransm_8_1)
else if n=9 then SEQ(htransm_9_0,htransm_9_1)
else if n=10 then SEQ(htransm_10_0,htransm_10_1)
else if n=11 then SEQ(htransm_11_0,htransm_11_1)
else if n=12 then SEQ(htransm_12_0,htransm_12_1)
else if n=13 then SEQ(htransm_13_0,htransm_13_1)
else if n=14 then SEQ(htransm_14_0,htransm_14_1) else SEQ(htransm_15_0,htransm_15_1)`;

val ALL_SPLIT_def = Define `ALL_SPLIT (^split_vars) = hsplit_15 /\ hsplit_14 /\ hsplit_13 /\ hsplit_12 /\ hsplit_11 /\ hsplit_10 /\ hsplit_9 /\ hsplit_8 /\ hsplit_7 /\ hsplit_6 /\ hsplit_5 /\ hsplit_4 /\ hsplit_3 /\ hsplit_2 /\ hsplit_1`;

(* FIXME: autogen this on number of masters *)
val MASK_def = Define `MASK n (^mask_vars) = 
if n=0 then hmask_0 
else if n=1 then hmask_1
else if n=2 then hmask_2
else if n=3 then hmask_3
else if n=4 then hmask_4
else if n=5 then hmask_5
else if n=6 then hmask_6
else if n=7 then hmask_7
else if n=8 then hmask_8
else if n=9 then hmask_9
else if n=10 then hmask_10
else if n=11 then hmask_11
else if n=12 then hmask_12
else if n=13 then hmask_13
else if n=14 then hmask_14 else hmask_15`;

val BUSREQ_def = Define `BUSREQ n (^busreq_vars) = 
if n=0 then hbusreq_0 
else if n=1 then hbusreq_1
else if n=2 then hbusreq_2
else if n=3 then hbusreq_3
else if n=4 then hbusreq_4
else if n=5 then hbusreq_5
else if n=6 then hbusreq_6
else if n=7 then hbusreq_7
else if n=8 then hbusreq_8
else if n=9 then hbusreq_9
else if n=10 then hbusreq_10
else if n=11 then hbusreq_11
else if n=12 then hbusreq_12
else if n=13 then hbusreq_13
else if n=14 then hbusreq_14 else hbusreq_15`;

val HSPLIT_def = Define `HSPLIT n (^split_vars) = 
if n=0 then hsplit_0 
else if n=1 then hsplit_1
else if n=2 then hsplit_2
else if n=3 then hsplit_3
else if n=4 then hsplit_4
else if n=5 then hsplit_5
else if n=6 then hsplit_6
else if n=7 then hsplit_7
else if n=8 then hsplit_8
else if n=9 then hsplit_9
else if n=10 then hsplit_10
else if n=11 then hsplit_11
else if n=12 then hsplit_12
else if n=13 then hsplit_13
else if n=14 then hsplit_14 else hsplit_15`;

val NO_BUSREQ_def = Define `NO_BUSREQ (^busreq_vars) = ^nbrr`;

val NO_HSPLIT_def = Define `NO_HSPLIT (^split_vars) = ^nhsr`;

val NO_MASK_def = Define `NO_MASK (^mask_vars) = ^nmr`;

val INIT_GRANT_def = Define `INIT_GRANT (^grant_vars) = MOD16_N2B ^(fromMLnum (nm-1)) (^grant_vars)`

val GRANT_def = Define `GRANT n (^grant_vars) = MOD16_N2B n (^grant_vars)`;

val INIT_MASTER_def = Define `INIT_MASTER (^master_vars) = MOD16_N2B ^(fromMLnum (nm-1)) (^master_vars)`;

val MASTER_def = Define `MASTER n (^master_vars) = MOD16_N2B n (^master_vars)`;

val HSEL_def = Define `HSEL n (^hselv) = MOD16_N2B n (^hselv)`;

val SLVSPLT_def = Define `SLVSPLT n (^slvsplt_vars) = (EL n ^ssv)`;

(* nth slave has split on mth master (if m is 0, then no split since you can't split on dummy master) *)
(* this assumes a slave may split on no more than one master at a time *)
val HSLVSPLT_def = Define `HSLVSPLT n m (^slvsplt_vars) = MOD16_N2B m (EL n ^ssv)`

val NO_HSLVSPLT_def = Define `NO_HSLVSPLT (^slvsplt_vars) = ^nss`;

(* -------------------- init state predicates --------------------------------------------*)

(* HTRANS = IDLE  and no one is requesting the bus*)
    (*(!n. n<16 ==> (^(mk_pabs(transm_vars, ``IDLEM n (^transm_vars)``))) (^transm_vars)) /\ *)

val Im = Define `INIT_M (^Im_state) = 
    IDLE(htrans_0,htrans_1) /\ 
    NO_BUSREQ (^busreq_vars) 
    `;
val INIT_M_def = Im;

(* HREADYOUT [FAQ] /\ HRESP = OKAY [FAQ] *)
(* (hsel_0=~haddr_0) /\ (hsel_1 = haddr_0) *)
val Is = Define `INIT_S (^Is_state)=
    hreadyout /\ 
    OKAY(hresp_0,hresp_1) /\         
    NO_HSPLIT (^split_vars) /\
    HSEL 0 (^hselv)`;
val INIT_S_def = Is;

(* 0 is dummy master
   15 is default master (hence INIT_GRANT's defn) *)
(* default master has the bus :FAQ *)
val Ia = Define `INIT_A (^Ia_state) = 
    INIT_GRANT (^grant_vars) /\ 
    INIT_MASTER (^master_vars)`; 
val INIT_A_def = Ia;

(* -------------------- transition relation predicates --------------------------------------------*)

(* arbiter: simple priority based *)
val Ra = Define `TRANS_A n (^Ra_state,^Ra_state') =
    (if n=0 then hgrant_0' else if ~MASK n (^mask_vars) /\ BUSREQ n (^busreq_vars) /\ IDLE (^htransv) then GRANT n  (^grant_vars')
				else TRANS_A (n-1)  (^Ra_state,^Ra_state')) /\ 
(* whoever is granted gets bus ownership when hreadyout goes high *)
	 ((^master_vars') = if ~hreadyout then (^master_vars) else (^grant_vars))
`;
val TRANS_A_def = Ra;

(* default master is nm-1, gets the bus if no one asks for it*) 
val Rm = Define `TRANS_AHB_M n (^Rm_state,^Rm_state') =
if n=0 then (* dummy master *)
    (MASTER n (^grant_vars) ==> IDLE(htransm_0_0',htransm_0_1')) /\ (* always signal IDLE on grant *)
	(~BUSREQ n (^busreq_vars')) (* dummy never requests the bus *)
else (* generic master *)
(* keep requesting bus if you get ownership (so arbiter only takes it away for higher priorty req) until transfer is done *)
    (~(OKAY(hresp_0,hresp_1) /\ hreadyout) /\ MASTER n (^grant_vars)  ==> BUSREQ n (^busreq_vars')) /\ 
(* latch busreq until grant *)
    (BUSREQ n (^busreq_vars) /\ ~GRANT n (^grant_vars) ==> BUSREQ n (^busreq_vars')) /\
(* starting transfer (if not already in the middle of one) *) 
    (hreadyout /\ IDLEM n (^transm_vars) /\ OKAY(hresp_0,hresp_1) /\ MASTER n (^grant_vars)
                            ==> NOSEQM n (^transm_vars')) /\ 
(* do not start transfer if not master, or not ok+rdy *) 
    ((~(hreadyout /\ OKAY(hresp_0,hresp_1)) \/ ~MASTER n (^grant_vars))
                            ==> ~NOSEQM n (^transm_vars')) /\ 
(* switch to SEQ mode *)
    (NOSEQM n (^transm_vars)  /\ OKAY(hresp_0,hresp_1) /\ INC4M n (^burstm_vars)  /\ MASTER n (^grant_vars) 
                            ==> (BUSYM n (^transm_vars') \/ SEQM n (^transm_vars')) /\ INC4M n (^burstm_vars')) /\
(* mid-burst bookkeeping - may signal BUSY or SEQ after a SEQ (as long as burst beats remain)  *)
    (SEQM n (^transm_vars)  /\ OKAY(hresp_0,hresp_1) /\ ~MOD16_N2B ^(fromMLnum (nb-1)) (bb3,bb2,bb1,bb0)  /\ MASTER n (^grant_vars)
                            ==> (BUSYM n (^transm_vars') \/ SEQM n (^transm_vars')) /\ INC4M n (^burstm_vars')) /\
(* end-burst bookkeeping - must signal IDLE when burst beats finish - this is to prevent a single master from taking over the 
   bus forever, since arbiter only grants if the bus is idle  *)
    (SEQM n (^transm_vars)  /\ OKAY(hresp_0,hresp_1) /\ MOD16_N2B ^(fromMLnum (nb-1)) (bb3,bb2,bb1,bb0)  /\ MASTER n (^grant_vars)
                            ==> IDLEM n (^transm_vars')) /\
(* mid-burst bookkeeping - may not signal BUSY after a BUSY (as long as burst beats remain) ) *)
(* specification does not say this but we need it to prevent livelock *)
    (BUSYM n (^transm_vars)) /\ ~MOD16_N2B ^(fromMLnum (nb-1)) (bb3,bb2,bb1,bb0) /\ OKAY(hresp_0,hresp_1) /\ MASTER n (^grant_vars) 
                            ==> (SEQM n (^transm_vars') /\ INC4M n (^burstm_vars')) /\
(* response to first cycle of retry - no need to reset bb; they take an extra cycle to reset but retry is two cycle so no prob *)
	 (~hreadyout /\ RETRY(hresp_0,hresp_1) /\ GRANT n (^grant_vars)
	                    ==> IDLEM n (^transm_vars')) /\
(* response to second cycle of retry - {3-22} says master *must* retry *)
	 (hreadyout /\ RETRY(hresp_0,hresp_1) /\ GRANT n (^grant_vars)
	                    ==> NOSEQM n (^transm_vars')) /\
(* response to first cycle of error ;{3-23} gives the option of continuing or cancelling transfer - we choose cancel*)
	 (~hreadyout /\ ERROR(hresp_0,hresp_1) /\GRANT n (^grant_vars) 
	                    ==> IDLEM n (^transm_vars')) /\
(* response to second cycle of error ;{3-23} gives the option of continuing or cancelling transfer - we choose cancel*)
	 (hreadyout /\ ERROR(hresp_0,hresp_1) /\ GRANT n (^grant_vars)
	                    ==> IDLEM n (^transm_vars'))  /\
(* record the number of a split master for future masking/unmasking *)
	 (if SPLIT(hresp_0,hresp_1) /\ ~hreadyout /\ MASTER n (^master_vars) then MASK n (^mask_vars')  
	  else if HSPLIT n (^split_vars) then ~MASK n (^mask_vars') 
	       else MASK n (^mask_vars') = MASK n (^mask_vars))
`; 
val TRANS_AHB_M_def = Rm;

(* slave (SPLIT-capable) *)
val Rs = Define `TRANS_AHB_S n (^Rs_state,^Rs_state') = 
(* latch hsel if hreadyout is low, otherwise hsel is free: this should be moved to the decoder*)
         (~hreadyout ==> (^hselv'=^hselv)) /\
(* force hreadyout to high because slave can't do more than nw  wait states *)   
         (HSEL n (^hselv) /\ MOD16_N2B ^(fromMLnum (nw-1)) (hws3,hws2,hws1,hws0) ==> hreadyout') /\
(* signal end of transfer (single or part of a burst) (don't need to check for rdy because value of rdy irrelevent to address phase) *)
	 (HSEL n (^hselv) /\ (NOSEQ(htrans_0,htrans_1) \/ SEQ(htrans_0,htrans_1)) /\  OKAY(hresp_0,hresp_1) 
	  ==> OKAY(hresp_0',hresp_1') /\ hreadyout') /\ 
(* {3-9} slave response to IDLE is READY + OKAY *)  
         (HSEL n (^hselv) /\ IDLE(htrans_0,htrans_1) ==> hreadyout' /\  OKAY(hresp_0',hresp_1')) /\
(* {3-9} slave response to BUSY is OKAY *)  
         (HSEL n (^hselv) /\ BUSY(htrans_0,htrans_1) ==> OKAY(hresp_0',hresp_1')) /\
(* if m0 is granted then respond with OK always (to prevent RETRY or SPLIT on m0 *)
	 (HSEL n (^hselv) /\ GRANT 0 (^grant_vars) ==>  OKAY(hresp_0',hresp_1')) /\
(* disable all but ok response*)
	 (HSEL n (^hselv) ==> (~SPLIT(hresp_0',hresp_1') /\ ~RETRY(hresp_0',hresp_1') /\ ~ERROR(hresp_0',hresp_1'))) /\ 
(* disable assertion of HSPLIT*)
	 (!m. m<^(fromMLnum nm) ==> (\m. ~HSPLIT m (^split_vars')) m) /\ 
(* drive second cycle of RETRY *)
	 (HSEL n (^hselv) /\ ~hreadyout /\ ~(IDLE(htrans_0,htrans_1) \/ BUSY(htrans_0,htrans_1)) /\ RETRY(hresp_0,hresp_1) 
                ==> hreadyout' /\ RETRY(hresp_0',hresp_1')) /\
(* drive second cycle of ERROR *)
	 (HSEL n (^hselv) /\ ~hreadyout  /\ ~(IDLE(htrans_0,htrans_1) \/ BUSY(htrans_0,htrans_1)) /\ ERROR(hresp_0,hresp_1) 
                ==> hreadyout' /\ ERROR(hresp_0',hresp_1')) /\
(* drive second cycle of SPLIT *)
	 (HSEL n (^hselv) /\ ~hreadyout  /\ ~(IDLE(htrans_0,htrans_1) \/ BUSY(htrans_0,htrans_1)) /\ SPLIT(hresp_0,hresp_1) 
                ==> hreadyout' /\ SPLIT(hresp_0',hresp_1')) /\
(* if SPLITing record current master's number *)
	 (if (HSEL n (^hselv) /\ ~hreadyout /\ SPLIT(hresp_0,hresp_1)) 
	      then !m. m<16 ==> MASTER m (^master_vars) ==> HSLVSPLT n m (^slvsplt_vars')
	  else (SLVSPLT n (^slvsplt_vars') = SLVSPLT n (^slvsplt_vars))) /\
(* note we don't do anything about slave asserting HSPLIT because abstracting that away *)
(* however, we do need to ensure that if we have split on Mx, we don't assert HSPLITy where x!=y *)
(* with >1 split-capable slave we would have to use HSPLITx to avoid conflict, but with only one we can access HSPLIT directly *)
	 (!m. m<^(fromMLnum nm) ==> (\m. ~HSLVSPLT n m (^slvsplt_vars) ==> ~HSPLIT m (^split_vars')) m) /\
(* since slave can only split on one master, do not split if have already done so*)
	 (~HSLVSPLT n 0 (^slvsplt_vars) ==> ~SPLIT(hresp_0',hresp_1')) /\
(* if asserting hsplit, drive down hslvsplt (again since can only split on at most one master)   *)
	  (!m. m<^(fromMLnum nm) ==> (\m. HSLVSPLT n m (^slvsplt_vars) /\ HSPLIT m (^split_vars)
				      ==> HSLVSPLT n 0  (^slvsplt_vars')) m)
`;
val TRANS_AHB_S_def = Rs;

(*(* make sure non-existent slaves are never selected *)
         (~HSEL 8 (^hselv') /\ ~HSEL 9 (^hselv') /\ ~HSEL 10 (^hselv') /\ ~HSEL 11 (^hselv') /\ 
	  ~HSEL 12 (^hselv') /\ ~HSEL 13 (^hselv') /\ ~HSEL 14 (^hselv') /\ ~HSEL 15 (^hselv')) /\*)

(* mux, which sends the current bus owner's signals through *)
(* technically we should be using hmaster_0 (rather than hgrant) here but can't because 
   it is triggered in the same cycle (see Ra and {3-31})*)
(* FIXME: previously we had no such thing as hburst_m_0 which has now appeared via BURSTM0 0. might create problems *)
val Rx = Define `TRANS_X (^Rx_state,^Rx_state') =
(htrans_0 = !n. n <^(fromMLnum nm) ==> (\n. MASTER n (^grant_vars) ==> TRANSM0 n (^transm_vars)) n) /\ 
(htrans_1 = !n. n <^(fromMLnum nm) ==> (\n. MASTER n (^grant_vars) ==> TRANSM1 n (^transm_vars)) n) /\ 
(hburst_0 = !n. n <^(fromMLnum nm) ==> (\n. MASTER n (^grant_vars) ==> BURSTM0 n (^burstm_vars)) n) /\
(htrans_0' = !n. n <^(fromMLnum nm) ==> (\n. MASTER n (^grant_vars') ==> TRANSM0 n (^transm_vars')) n) /\ 
(htrans_1' = !n. n <^(fromMLnum nm) ==> (\n. MASTER n (^grant_vars') ==> TRANSM1 n (^transm_vars')) n) /\ 
(hburst_0' = !n. n <^(fromMLnum nm) ==> (\n. MASTER n (^grant_vars') ==> BURSTM0 n (^burstm_vars')) n)`; 
val TRANS_X_def = Rx;

(* FIXME: right now we are abtracting this out. wen we have arrays, this should be fixed *)
(* decoder, decodes higher order address bits to figure out which slave is being targeted *)
(*val Rd = Define `TRANS_D (^Rd_state,^Rd_state') = 
(* we only decode if hreadyout goes high, else hold old value *)
 (hsel_0' = if hreadyout then ~haddr_0 else hsel_0) /\ 
 (hsel_1' = if hreadyout then haddr_0 else hsel_1) 
`;*)

(* global counters go here *)
val RCn = Define `TRANS_CNT (^RCn_state,^RCn_state') =
(* wait state counter *)
(* climb to hws2 on ~hreadyout, resetting on hreadyout (slaves do this if hws2 is reached) *)
(~hreadyout ==> ((hws3',hws2',hws1',hws0') = WS_INC ^(fromMLnum nw) (hws3,hws2,hws1,hws0))) /\ 
(* burst beat counter *) 
(* start counting at noseq, increment for every seq, but hold if busy, reset if idle or ~hreadyout*)
(* not sure if I should hold or reset if idle; or does that depend on where the counter is?*)
(* FIXME: get rid of having to have a lambda here*)
    ((bb3',bb2',bb1',bb0') = (\(bb3,bb2,bb1,bb0). 
			      if hreadyout then 
				  if NOSEQ(htrans_0,htrans_1) then MOD16_ONE(bb3,bb2,bb1,bb0)
				  else if SEQ(htrans_0,htrans_1) then BB_INC ^(fromMLnum nb) (bb3,bb2,bb1,bb0)
				       else if BUSY(htrans_0,htrans_1) then MOD16_HOLD(bb3,bb2,bb1,bb0) 
					    else MOD16_ZERO(bb3,bb2,bb1,bb0)
			      else MOD16_ZERO(bb3,bb2,bb1,bb0)) (bb3,bb2,bb1,bb0))
`;
val TRANS_CNT_def = RCn;

(*    (hws0' = ~hreadyout) /\ 
    (hws1' = ~hreadyout /\ hws0) /\ 
    (hws2' = ~hreadyout /\ hws1) /\ 
(*  (hws3' = ~hreadyout /\ hws2) *) (*no need for this because the last waitstate is when slave drives hreadyout high on *next* tick *)*)

val I1h = Define `INIT_AHB (^I1h_state) = 
^(lhs(concl(Drule.SPEC_ALL Im))) /\
^(lhs(concl(Drule.SPEC_ALL Is))) /\ 
^(lhs(concl(Drule.SPEC_ALL Ia))) `; 
val INIT_AHB_def = I1h;

val Rr = list_mk_exists
    ((strip_pair bbv)@(strip_pair bbv')@(strip_pair hwsv)@(strip_pair hwsv'),
     list_mk_conj [``INIT_AHB (^I1h_state) ==> (MOD16_IS_ZERO (^bbv') /\ MOD16_IS_ZERO (^hwsv'))``,
		   lhs(concl(Drule.SPEC_ALL RCn)),
		   (list_mk_exists
		    ((strip_pair mask_vars)@(strip_pair mask_vars'),
		     list_mk_conj [``INIT_AHB (^I1h_state) ==> NO_MASK (^mask_vars)``,
				   lhs(concl(Drule.SPEC_ALL (SPEC (fromMLnum (nm-1)) (GEN ``n:num`` Ra)))),
				   list_mk_exists((strip_pair transm_vars)@(strip_pair transm_vars')
						  @(strip_pair burstm_vars)@(strip_pair burstm_vars'),
						  (list_mk_conj[``INIT_AHB (^I1h_state) ==> !m. m<16 ==> IDLEM m (^transm_vars)``,
								list_mk_conj(List.tabulate(nm,
									fn n => lhs(concl(Drule.SPEC_ALL (SPEC (fromMLnum n) Rm))))), 
								lhs(concl(Drule.SPEC_ALL Rx))]))])),
		   list_mk_exists
		   ((strip_pair slvsplt_vars)@(strip_pair slvsplt_vars'),
		    list_mk_conj([``INIT_AHB (^I1h_state) ==> NO_HSLVSPLT (^slvsplt_vars)``,
				  list_mk_conj(List.tabulate(ns,fn n => lhs(concl(Drule.SPEC_ALL (SPEC (fromMLnum n) Rs)))))]))])

(*^(lhs(concl(Drule.SPEC_ALL Rd)))*)
val R1h = Define `TRANS_AHB (^R1h_state,^R1h_state') = ^Rr`;
val TRANS_AHB_def = R1h;

val abbrev_defs = [IDLE_def,BUSY_def,NOSEQ_def,SEQ_def,OKAY_def,ERROR_def,RETRY_def,SPLIT_def,SINGLE_def,INC4_def,
                   INC4M_def,BURSTM0_def,TRANSM0_def,TRANSM1_def,IDLEM_def,BUSYM_def,NOSEQM_def,SEQM_def,ALL_SPLIT_def,
		   MASK_def,BUSREQ_def,HSPLIT_def,NO_BUSREQ_def,NO_HSPLIT_def,NO_MASK_def,INIT_GRANT_def,GRANT_def,
		   INIT_MASTER_def, MASTER_def,HSLVSPLT_def,SLVSPLT_def,NO_HSLVSPLT_def,HSEL_def,BB_INC_def,WS_INC_def]

val I1rh = save_thm("amba_ahb_I1rh",SIMP_RULE (pure_ss++BETA_ss++pairSimps.PAIR_ss++ARITH_ss)  
		     ([INIT_M_def,INIT_S_def,INIT_A_def,COND_CLAUSES]@abbrev_defs@m16n2b@m16exp) INIT_AHB_def)

val Rc = rhs(concl(SPEC_ALL TRANS_AHB_def))

val R1rh = save_thm("amba_ahb_R1rh", EVERY_CONJ_CONV (STRIP_QUANT_CONV 
		(EVERY_CONJ_CONV (STRIP_QUANT_CONV (EVERY_CONJ_CONV 
		(unroll_ahb_CONV [TRANS_AHB_M_def,TRANS_X_def,(*TRANS_D_def,*)TRANS_CNT_def,TRANS_AHB_S_def,I1rh] 
				 TRANS_A_def abbrev_defs))))) Rc)

val _ = export_theory()
