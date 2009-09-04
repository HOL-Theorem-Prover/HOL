open HolKernel Parse boolLib bossLib metisLib;


(*****************************************************************************)
(* A handshaking device DEV is a SAFE_DEV which satisfies liveness.          *)
(* This file contains definitions and theorems to support the proof that     *)
(* handshaking circuits satisfy DEV                                          *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)
(******************************************************************************
* Load theories
* (commented out for compilation)
******************************************************************************)
(*
quietdec := true;
map load  ["metisLib","composeTheory"];
open composeTheory metisLib;
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib metisLib;

(******************************************************************************
* Open theories
******************************************************************************)
open composeTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Function used with PAT_ASSUM:   PAT_ASSUM <term> kill                     *)
(*****************************************************************************)
val kill = (fn theorem => K ALL_TAC theorem);

val _ = new_theory "dev";

(*****************************************************************************)
(* LIV (livenes) - a busy device finishes its computation eventually         *)
(*****************************************************************************)
val LIV_def = Define `LIV (load,inp,done,out) =
      (!t. ~(done t) ==> (?t'. (t' > t) /\ (done t')))`;


(*****************************************************************************)
(* DEV - a handshaking device satisfies safety and liveness                  *)
(*****************************************************************************)
val DEV_def = Define `DEV f p = SAFE_DEV f p /\ LIV p`;


(*****************************************************************************)
(* MIN_LEMMA - if a signal s is false at time t and is true at time (t+d),   *)
(* then there exists a `minimum` t' > t such that (s t')                     *)
(*****************************************************************************)
val MIN_LEMMA = store_thm("MIN_LEMMA",
    ``!t. ~(s t) /\ (s (t+d)) ==>
          (?t'. (t' > t) /\ (!tt. t <= tt /\ tt < t' ==> ~(s tt)) /\ s t')``,
    completeInduct_on `d`
    THEN RW_TAC arith_ss []
    THEN Cases_on `d`
    THENL [
    PROVE_TAC [arithmeticTheory.ADD_CLAUSES]
    , (* end of Cases_on `d` *)
    `n < (SUC n)` by RW_TAC arith_ss []
    THEN `!t. ~s t /\ s (t + n) ==>
              ?t'. (t' > t) /\ (!tt. t <= tt /\ tt < t' ==> ~s tt) /\ s t'`
          by metisLib.METIS_TAC []
    THEN Cases_on `s (t+1)`
    THENL [
    `!tt. t <= tt /\ tt < (t+1) ==> ~s tt` by REWRITE_TAC []
    THENL [
    RW_TAC arith_ss []
    THEN `t=tt` by RW_TAC arith_ss []
    THEN RW_TAC arith_ss []
    , (* end of `!tt. t <= tt /\ tt < (t+1) ==> ~s tt` *)
    `(t+1) > t` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `(t+1)` THEN PROVE_TAC []
    ]
    , (* end of Cases_on `s (t+1)` *)
    `SUC n = n+1` by RW_TAC arith_ss []
    THEN `(n+1)+t = (t+1)+n` by RW_TAC arith_ss []
    THEN `s ((t+1)+n)` by PROVE_TAC []
    THEN `?t'. (t' > (t+1)) /\ (!tt. (t+1) <= tt /\ tt < t' ==> ~s tt) /\ s t'`
         by metisLib.METIS_TAC []
    THEN `!tt. t <= tt /\ tt < t' ==> ~s tt` by REWRITE_TAC []
    THENL [
    RW_TAC arith_ss []
    THEN Cases_on `t=tt`
    THENL [
    RW_TAC arith_ss []
    , (* end of `Cases_on `t=tt`` *)
    RW_TAC arith_ss []
    ]
    , (* end of `!tt. t <= tt /\ tt < t' ==> ~s tt` *)
    `t' > t` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `t'` THEN PROVE_TAC []
    ]]]);



(*****************************************************************************)
(* LIV_LEMMA - if a device satisfies LIV and is busy at time t, then there   *)
(* exists a time t' > t which determines the exact moment the computation    *)
(* finishes                                                                  *)
(*****************************************************************************)
val LIV_LEMMA = store_thm("LIV_LEMMA",
    ``LIV (load,inp,done,out) ==>
     (!t. ~(done t) ==> ?t'. (t' >  t) /\ (HOLDF (t,t') done) /\ (done t'))``,
    RW_TAC arith_ss [LIV_def,HOLDF_def]
    THEN `?t'. t' > t /\ done t'` by PROVE_TAC []
    THEN `?d. d = t'-t` by RW_TAC arith_ss []
    THEN `t+d = t'` by RW_TAC arith_ss []
    THEN `done (t+d)` by PROVE_TAC []
    THEN metisLib.METIS_TAC [MIN_LEMMA]);



(*****************************************************************************)
(* ATM - atomic circuits satisfy DEV                                         *)
(*****************************************************************************)
val ATM = store_thm("ATM",
    ``ATM f (load,inp,done,out) ==> DEV f (load,inp,done,out)``,
    RW_TAC arith_ss [DEV_def,ATM_def,LIV_def]
    THEN IMP_RES_TAC ATM_def THEN IMP_RES_TAC SAFE_ATM
    THEN `c0 t` by PROVE_TAC [ATM_def, NOT_def, POSEDGE_def,
                              POSEDGE, POSEDGE_IMPL]
    THEN Cases_on `t`
    THENL [
    (* t = 0  is vacuously true as ~POSEDGE s 0 *)
    `~(POSEDGE load 0)` by REWRITE_TAC [POSEDGE]
    THEN `~(c0 0)` by PROVE_TAC [POSEDGE_IMPL]
    , (* end of Cases_on `t` *)
    `POSEDGE load (SUC n)` by PROVE_TAC [POSEDGE_IMPL]
    THEN `load (SUC n)` by PROVE_TAC [POSEDGE_def]
    THEN `~(POSEDGE load (SUC (SUC n)))` by RW_TAC arith_ss [POSEDGE_def]
    THEN `!t. c0 t = POSEDGE load t` by PROVE_TAC [POSEDGE_IMPL]
    THEN `c0 (SUC (SUC n)) = POSEDGE load (SUC (SUC n))` by PROVE_TAC []
    THEN `done (SUC (SUC n))` by PROVE_TAC [NOT_def]
    THEN `(SUC (SUC n)) > SUC n` by RW_TAC arith_ss []
    THEN `!tt. (SUC n) <= tt /\ tt < (SUC (SUC n)) ==> (tt = SUC n)`
         by RW_TAC arith_ss []
    THEN `!tt. (SUC n) <= tt /\ tt < (SUC (SUC n)) ==> ~(done tt)`
         by RW_TAC arith_ss []
    THEN `!tt. SUC n <= tt /\ tt < (SUC (SUC n)) ==> ~(done tt)`
         by RW_TAC arith_ss []
    THEN `HOLDF (SUC n,(SUC (SUC n))) done` by RW_TAC arith_ss [HOLDF_def]
    THEN Q.EXISTS_TAC `SUC(SUC n)`
    THEN PROVE_TAC []
    ]);



(*****************************************************************************)
(* HOLDT_NOT_POSEDGE' - if a signal is T during an internval,                *)
(* then no positive edge occurs in this period.                              *)
(*****************************************************************************)
val HOLDT_NOT_POSEDGE' = store_thm("HOLDT_NOT_POSEDGE'",
     ``(!t. t0 <= t /\ t < t1 ==> s t) ==>
       !t. t0 < t /\ t <= t1 ==> ~POSEDGE s t``,
   Induct_on `t1`
   THENL [
   RW_TAC arith_ss []
   , (* end of base case *)
   `SUC t1 = t1 + 1` by RW_TAC arith_ss []
   THEN RW_TAC arith_ss []
   THEN Cases_on `t=t1+1`
   THENL [
   `s t1` by RW_TAC arith_ss []
   THEN PROVE_TAC [POSEDGE]
   , (* end of Cases_on `t=t1+1` *)
   RW_TAC arith_ss []]]);



(*****************************************************************************)
(* SEQ - sequential circuits satisfy DEV                                     *)
(*****************************************************************************)
val SEQ = store_thm("SEQ",
    ``SEQ (DEV f) (DEV g) (load,inp,done,out) ==>
      DEV (g o f) (load,inp,done,out)``,
    RW_TAC arith_ss [DEV_def,SEQ_def,LIV_def]
    THEN IMP_RES_TAC SEQ_def THEN IMP_RES_TAC SAFE_SEQ
    THEN `LIV (c0,inp,c1,data)` by RW_TAC arith_ss [LIV_def]
    THEN `LIV (c1,data,c2,out)` by RW_TAC arith_ss [LIV_def]
    THEN `!tt. ~(c1 tt) ==> (?tt'. tt' > tt /\ HOLDF (tt,tt') c1 /\ c1 tt')`
         by IMP_RES_TAC LIV_LEMMA
    THEN `!tt. ~(c2 tt) ==> (?tt'. tt' > tt /\ HOLDF (tt,tt') c2 /\ c2 tt')`
         by IMP_RES_TAC LIV_LEMMA
    THEN Cases_on `c1 t`
    THENL [
    Cases_on `c2 t`
    THENL [
    PROVE_TAC [AND_def] (* c1 t /\ c2 t *)
    , (* end of Cases_on `c2 t` *)
    `?tt'. tt' > t /\ HOLDF (t,tt') c2 /\ c2 tt'` (* c1 t /\ ~(c2 t) *)
           by PROVE_TAC []
    THEN `!time. t <= time /\ time < tt' ==> c0 time`
         by PROVE_TAC [HOLDF_def,NOT_def,OR_def]
    THEN `!time. t < time /\ time <= tt' ==> ~(POSEDGE c0 time)`
         by PROVE_TAC [HOLDT_NOT_POSEDGE']
    THEN `!t. c1 t /\ ~(POSEDGE c0 (t+1)) ==> c1 (t+1)`
         by PROVE_TAC [SAFE_DEV_def]
    THEN `t < tt'` by RW_TAC arith_ss []
    THEN `!time. time <= tt' ==> t < time ==> c1 time`
         by IMP_RES_TAC DONE_INTERVAL
    THEN `c1 tt'` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `tt'`
    THEN PROVE_TAC [AND_def]
    ]
    , (* end of Cases_on `c1 t` *)
    `?t'. t' > t /\ HOLDF (t,t') c1 /\ c1 t'` by RW_TAC arith_ss []
    THEN `?t'. t' > t /\  c1 t'` by RW_TAC arith_ss []
    THEN Cases_on `c2 t'`
    THENL [
    PROVE_TAC [AND_def] (* c1 t' /\ c2 t' *)
    , (* end of Cases_on `c2 t'` *)
    `?tt'. tt' > t' /\ HOLDF (t',tt') c2 /\ c2 tt'` (* c1 t' /\ ~(c2 t') *)
         by PROVE_TAC []
    THEN `!time. t' <= time /\ time < tt' ==> c0 time`
         by PROVE_TAC [HOLDF_def,NOT_def,OR_def]
    THEN `!time. t' < time /\ time <= tt' ==> ~(POSEDGE c0 time)`
         by PROVE_TAC [HOLDT_NOT_POSEDGE']
    THEN `!t. c1 t /\ ~(POSEDGE c0 (t+1)) ==> c1 (t+1)`
         by PROVE_TAC [SAFE_DEV_def]
    THEN `t' < tt'` by RW_TAC arith_ss []
    THEN `!time. time <= tt' ==> t' < time ==> c1 time`
         by IMP_RES_TAC DONE_INTERVAL
    THEN `c1 tt'` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `tt'`
    THEN `tt' > t` by RW_TAC arith_ss []
    THEN PROVE_TAC [AND_def]
    ]
    ]);



(*****************************************************************************)
(* PAR - parallel circuits satisfy DEV                                       *)
(*****************************************************************************)

val PAR = store_thm("PAR",
    ``PAR (DEV f) (DEV g) (load,inp,done,out) ==>
      DEV (\x. (f x, g x)) (load,inp,done,out)``,
    REWRITE_TAC [DEV_def,PAR_def,LIV_def]
    THEN STRIP_TAC THEN CONJ_TAC
    THEN `PAR (SAFE_DEV f) (SAFE_DEV g) (load,inp,done,out)`
         by IMP_RES_TAC PAR_def
    THEN IMP_RES_TAC SAFE_PAR
    THEN `LIV (start,inp,done',data')` by RW_TAC arith_ss [LIV_def]
    THEN `LIV (start,inp,done'',data'')` by RW_TAC arith_ss [LIV_def]
    THEN `!tt. ~(done' tt) ==> (?tt'. tt' > tt /\ HOLDF (tt,tt') done' /\ done' tt')`
         by IMP_RES_TAC LIV_LEMMA
    THEN `!tt. ~(done'' tt) ==> (?tt'. tt' > tt /\ HOLDF (tt,tt') done'' /\ done'' tt')`
         by IMP_RES_TAC LIV_LEMMA
    THEN REPEAT STRIP_TAC
    THEN Cases_on `done' t`
    THENL [
    Cases_on `done'' t`
    THENL [
    PROVE_TAC [AND_def]
    , (* end of Cases_on `done'' t` *)
    `?t2. t2 > t /\ HOLDF (t,t2) done'' /\ done'' t2`
        by RW_TAC arith_ss []  (* done' t /\ ~done'' t *)
    THEN `!tt. t < tt /\ tt <= t2 ==> ~(POSEDGE start tt)`
         by REWRITE_TAC []
    THENL [
    `HOLDF (t,t2) done`  by PROVE_TAC [HOLDF_def, AND_def]
    THEN `HOLDF (t+1,t2+1) c1` by PROVE_TAC [HOLDF_DEL]
    THEN `HOLDF (t+1,t2+1) start` by PROVE_TAC [HOLDF_def,AND_def]
    THEN `!tt. (t+1) <= tt /\ tt < (t2+1) ==> ~(POSEDGE start tt)`
         by PROVE_TAC [HOLDF_def, POSEDGE_def]
    THEN `!t1 t2 tt. (t1+1) <= tt /\ tt < (t2+1) = (t1 < tt /\ tt <= t2)`
         by RW_TAC arith_ss [] THEN PROVE_TAC []
    , (* end of `!tt. t < tt /\ tt <= t2 ==> ~(POSEDGE start tt)` *)
    `t < t2` by RW_TAC arith_ss []
    THEN `!t. ~POSEDGE start (t + 1) ==> done' t ==> done' (t + 1)`
         by IMP_RES_TAC SAFE_DEV_def
    THEN `!t. done' t /\ ~POSEDGE start (t + 1) ==> done' (t + 1)`
         by PROVE_TAC []
    THEN `!t'. t' <= t2 ==> t < t' ==> done' t'` by IMP_RES_TAC DONE_INTERVAL
    THEN `done' t2` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `t2` THEN PROVE_TAC [AND_def]
    ]
    ]
    , (* end of Cases_on `done' t` *)
    `?t1. t1 > t /\ HOLDF (t,t1) done' /\ done' t1`
         by RW_TAC arith_ss [] (* ~done' t *)
    THEN Cases_on `done'' t1`
    THENL [
    Q.EXISTS_TAC `t1` THEN PROVE_TAC [AND_def]
    , (* end of Cases_on `done'' t1` *)
    `?t2. t2 > t1 /\ HOLDF (t1,t2) done'' /\ done'' t2`
          by RW_TAC arith_ss []
    THEN `!tt. t1 < tt /\ tt <= t2 ==> ~(POSEDGE start tt)` by REWRITE_TAC []
    THENL [
    `HOLDF (t1,t2) done` by PROVE_TAC [HOLDF_def, AND_def]
    THEN `HOLDF (t1+1,t2+1) c1` by PROVE_TAC [HOLDF_DEL]
    THEN `HOLDF (t1+1,t2+1) start` by PROVE_TAC [HOLDF_def,AND_def]
    THEN `!tt. (t1+1) <= tt /\ tt < (t2+1) ==> ~(POSEDGE start tt)`
         by PROVE_TAC [HOLDF_def, POSEDGE_def]
    THEN `!t1 t2 tt. (t1+1) <= tt /\ tt < (t2+1) = (t1 < tt /\ tt <= t2)`
         by RW_TAC arith_ss []
    THEN PROVE_TAC []
    , (* end of `!tt. t1 < tt /\ tt <= t2 ==> ~(POSEDGE start tt)` *)
    `t1 < t2` by RW_TAC arith_ss []
    THEN `!t. ~POSEDGE start (t + 1) ==> done' t ==> done' (t + 1)`
         by IMP_RES_TAC SAFE_DEV_def
    THEN `!t. done' t /\ ~POSEDGE start (t + 1) ==> done' (t + 1)`
         by PROVE_TAC []
    THEN `!t'. t' <= t2 ==> t1 < t' ==> done' t'` by IMP_RES_TAC DONE_INTERVAL
    THEN `done' t2` by RW_TAC arith_ss []
    THEN `t2 > t` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `t2` THEN PROVE_TAC [AND_def]
    ]]]);


(*****************************************************************************)
(* ITE - conditional circuits satisfy DEV                                    *)
(*****************************************************************************)
val ITE = store_thm("ITE",
    ``ITE (DEV e) (DEV f) (DEV g) (load,inp,done,out) ==>
      DEV (\x. (if e x then f x else g x)) (load,inp,done,out)``,
    RW_TAC arith_ss [DEV_def,ITE_def,LIV_def] (* proof of SAFE_DEV /\ LIV *)
    THENL [
    REPEAT (PAT_ASSUM ``!(t:num). X`` kill)
    THEN `ITE (SAFE_DEV e) (SAFE_DEV f) (SAFE_DEV g) (load,inp,done,out)`
              by (ONCE_REWRITE_TAC [ITE_def]
                   THEN REPEAT Q.ID_EX_TAC
                   THEN ASM_REWRITE_TAC [])
    THEN IMP_RES_TAC SAFE_ITE
    , (* end of proof of SAFE_DEV *)
    `LIV (start,inp,done_e,data_e)` by RW_TAC arith_ss [LIV_def]
    THEN `LIV (start_f,q,done_f,data_f)` by RW_TAC arith_ss [LIV_def]
    THEN `LIV (start_g,q,done_g,data_g)` by RW_TAC arith_ss [LIV_def]
    THEN `!tt. ~(done_e tt) ==> (?tt'. tt' > tt /\ HOLDF (tt,tt') done_e /\ done_e tt')`
         by IMP_RES_TAC LIV_LEMMA
    THEN `!tt. ~(done_f tt) ==> (?tt'. tt' > tt /\ HOLDF (tt,tt') done_f /\ done_f tt')`
         by IMP_RES_TAC LIV_LEMMA
    THEN `!tt. ~(done_g tt) ==> (?tt'. tt' > tt /\ HOLDF (tt,tt') done_g /\ done_g tt')`
         by IMP_RES_TAC LIV_LEMMA
    THEN REPEAT (PAT_ASSUM ``LIV X`` kill)
    THEN Cases_on `done_e t`
    THENL [
    Cases_on `done_f t`
    THENL [
    Cases_on `done_g t`
    THENL [
    PROVE_TAC [AND_def] (* done_e t /\ done_f t /\ done_g t *)
    , (* end of Cases_on `done_g t` *)
    `?tg. tg > t /\ HOLDF (t,tg) done_g /\ done_g tg`
          by RW_TAC arith_ss [] (* done_e t /\ done_f t /\ ~done_g t *)
    THEN `!tt. t < tt /\ tt <= tg ==> ~(POSEDGE start tt)` by REWRITE_TAC []
    THENL [
    `HOLDF (t,tg) done`  by PROVE_TAC [HOLDF_def, AND_def]
    THEN `HOLDF (t+1,tg+1) c1` by PROVE_TAC [HOLDF_DEL]
    THEN `HOLDF (t+1,tg+1) start` by PROVE_TAC [HOLDF_def,AND_def]
    THEN `!tt. (t+1) <= tt /\ tt < (tg+1) ==> ~(POSEDGE start tt)`
         by PROVE_TAC [HOLDF_def, POSEDGE_def]
    THEN `!t1 t2 tt. (t1+1) <= tt /\ tt < (t2+1) = (t1 < tt /\ tt <= t2)`
         by RW_TAC arith_ss [] THEN PROVE_TAC []
    , (* end of `!tt. t < tt /\ tt <= tg ==> ~(POSEDGE start tt)` *)
    `t < tg` by RW_TAC arith_ss []
    THEN `!t. ~POSEDGE start (t + 1) ==> done_e t ==> done_e (t + 1)`
         by IMP_RES_TAC SAFE_DEV_def
    THEN `!t. done_e t /\ ~POSEDGE start (t + 1) ==> done_e (t + 1)`
         by PROVE_TAC []
    THEN `!t'. t' <= tg ==> t < t' ==> done_e t'` by IMP_RES_TAC DONE_INTERVAL
    THEN `done_e tg` by RW_TAC arith_ss []
    THEN `!tt. t < tt /\ tt <= tg ==> done_e tt` by RW_TAC arith_ss []
    THEN `!t'. t <= t' ==> t' <= tg ==> done_e t'` by IMP_RES_TAC INTERVAL_LEMMA
    THEN `!tt. t <= tt /\ tt < tg ==> done_e tt` by RW_TAC arith_ss []
    THEN `!tt. tt <= tg ==> t < tt ==> ~(POSEDGE done_e tt)`
         by IMP_RES_TAC HOLDT_NOT_POSEDGE'
    THEN `!tt. t < tt /\ tt <= tg ==> ~(POSEDGE start_f tt)`
         by PROVE_TAC [POSEDGE_IMPL, POSEDGE_def, POSEDGE, AND_def]
    THEN `!t. ~POSEDGE start_f (t + 1) ==> done_f t ==> done_f (t + 1)`
         by IMP_RES_TAC SAFE_DEV_def
    THEN `!t. done_f t /\ ~POSEDGE start_f (t + 1) ==> done_f (t + 1)`
         by PROVE_TAC []
    THEN `!t'. t' <= tg ==> t < t' ==> done_f t'` by IMP_RES_TAC DONE_INTERVAL
    THEN `done_f tg` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `tg` THEN PROVE_TAC [AND_def]
    ]
    ]
    , (* end of Cases_on `done_f t` *)
    `?tf. tf > t /\ HOLDF (t,tf) done_f /\ done_f tf`
        by RW_TAC arith_ss [] (* done_e t /\ ~done_f t *)
    THEN `!tt. t < tt /\ tt <= tf ==> ~(POSEDGE start tt)` by REWRITE_TAC []
    THENL [
    `HOLDF (t,tf) done`  by PROVE_TAC [HOLDF_def, AND_def]
    THEN `HOLDF (t+1,tf+1) c1` by PROVE_TAC [HOLDF_DEL]
    THEN `HOLDF (t+1,tf+1) start` by PROVE_TAC [HOLDF_def,AND_def]
    THEN `!tt. (t+1) <= tt /\ tt < (tf+1) ==> ~(POSEDGE start tt)`
           by PROVE_TAC [HOLDF_def, POSEDGE_def]
    THEN `!t1 t2 tt. (t1+1) <= tt /\ tt < (t2+1) = (t1 < tt /\ tt <= t2)`
        by RW_TAC arith_ss [] THEN PROVE_TAC []
    , (* end of `!tt. t < tt /\ tt <= tf ==> ~(POSEDGE start tt)` *)
    `t < tf` by RW_TAC arith_ss []
    THEN `!t. ~POSEDGE start (t + 1) ==> done_e t ==> done_e (t + 1)`
         by IMP_RES_TAC SAFE_DEV_def
    THEN `!t. done_e t /\ ~POSEDGE start (t + 1) ==> done_e (t + 1)`
         by PROVE_TAC []
    THEN `!t'. t' <= tf ==> t < t' ==> done_e t'` by IMP_RES_TAC DONE_INTERVAL
    THEN `done_e tf` by RW_TAC arith_ss []
    THEN Cases_on `done_g tf`
    THENL [
    Q.EXISTS_TAC `tf`
    THEN PROVE_TAC [AND_def]
    , (* end of Cases_on `done_g tf` *)
    `?tg. tg > tf /\ HOLDF (tf,tg) done_g /\ done_g tg`
          by RW_TAC arith_ss [] (* done_e tf /\ done_f tf /\ ~done_g tf *)
    THEN `!tt. tf < tt /\ tt <= tg ==> ~(POSEDGE start tt)` by REWRITE_TAC []
    THENL [
    `HOLDF (tf,tg) done` by PROVE_TAC [HOLDF_def, AND_def]
    THEN `HOLDF (tf+1,tg+1) c1` by PROVE_TAC [HOLDF_DEL]
    THEN `HOLDF (tf+1,tg+1) start` by PROVE_TAC [HOLDF_def,AND_def]
    THEN `!tt. (tf+1) <= tt /\ tt < (tg+1) ==> ~(POSEDGE start tt)`
         by PROVE_TAC [HOLDF_def, POSEDGE_def]
    THEN `!t1 t2 tt. (t1+1) <= tt /\ tt < (t2+1) = (t1 < tt /\ tt <= t2)`
         by RW_TAC arith_ss [] THEN PROVE_TAC []
    , (* end of `!tt. tf < tt /\ tt <= tg ==> ~(POSEDGE start tt)` *)
    `t < tg` by RW_TAC arith_ss []
    THEN `tf < tg` by RW_TAC arith_ss []
    THEN `!t. ~POSEDGE start (t + 1) ==> done_e t ==> done_e (t + 1)`
         by IMP_RES_TAC SAFE_DEV_def
    THEN `!t. done_e t /\ ~POSEDGE start (t + 1) ==> done_e (t + 1)`
         by PROVE_TAC []
    THEN `!t'. t' <= tg ==> tf < t' ==> done_e t'` by IMP_RES_TAC DONE_INTERVAL
    THEN `done_e tg` by RW_TAC arith_ss []
    THEN `!tt. tf < tt /\ tt <= tg ==> done_e tt` by RW_TAC arith_ss []
    THEN `!t'. tf <= t' ==> t' <= tg ==> done_e t'` by IMP_RES_TAC INTERVAL_LEMMA
    THEN `!tt. tf <= tt /\ tt < tg ==> done_e tt` by RW_TAC arith_ss []
    THEN `!tt. tt <= tg ==> tf < tt ==> ~(POSEDGE done_e tt)`
         by IMP_RES_TAC HOLDT_NOT_POSEDGE'
    THEN `!tt. tf < tt /\ tt <= tg ==> ~(POSEDGE start_f tt)`
         by PROVE_TAC [POSEDGE_IMPL, POSEDGE_def, POSEDGE, AND_def]
    THEN `!t. ~POSEDGE start_f (t + 1) ==> done_f t ==> done_f (t + 1)`
         by IMP_RES_TAC SAFE_DEV_def
    THEN `!t. done_f t /\ ~POSEDGE start_f (t + 1) ==> done_f (t + 1)`
         by PROVE_TAC []
    THEN `!t'. t' <= tg ==> tf < t' ==> done_f t'` by IMP_RES_TAC DONE_INTERVAL
    THEN `done_f tg` by RW_TAC arith_ss []
    THEN `tg > t` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `tg` THEN PROVE_TAC [AND_def]
    ]]]]
    , (* end of Cases_on `done_e t` *)
    `?te. te > t /\ HOLDF (t,te) done_e /\ done_e te`
          by RW_TAC arith_ss []  (* ~done_e t *)
    THEN Cases_on `done_f te`
    THENL [
    Cases_on `done_g te`
    THENL [
    Q.EXISTS_TAC `te` THEN PROVE_TAC [AND_def]
    , (* end of Cases_on `done_g te` *)
    `?tg. tg > te /\ HOLDF (te,tg) done_g /\ done_g tg`
           by RW_TAC arith_ss [] (* ~done_e t /\ done_f te /\ ~done_g te *)
    THEN `!tt. te < tt /\ tt <= tg ==> ~(POSEDGE start tt)` by REWRITE_TAC []
    THENL [
    `HOLDF (te,tg) done` by PROVE_TAC [HOLDF_def, AND_def]
    THEN `HOLDF (te+1,tg+1) c1` by PROVE_TAC [HOLDF_DEL]
    THEN `HOLDF (te+1,tg+1) start` by PROVE_TAC [HOLDF_def,AND_def]
    THEN `!tt. (te+1) <= tt /\ tt < (tg+1) ==> ~(POSEDGE start tt)`
         by PROVE_TAC [HOLDF_def, POSEDGE_def]
    THEN `!t1 t2 tt. (t1+1) <= tt /\ tt < (t2+1) = (t1 < tt /\ tt <= t2)`
         by RW_TAC arith_ss [] THEN PROVE_TAC []
    , (* end of `!tt. te < tt /\ tt <= tg ==> ~(POSEDGE start tt)` *)
    `t < tg` by RW_TAC arith_ss []
    THEN `te < tg` by RW_TAC arith_ss []
    THEN `!t. ~POSEDGE start (t + 1) ==> done_e t ==> done_e (t + 1)`
         by IMP_RES_TAC SAFE_DEV_def
    THEN `!t. done_e t /\ ~POSEDGE start (t + 1) ==> done_e (t + 1)`
         by PROVE_TAC []
    THEN `!t'. t' <= tg ==> te < t' ==> done_e t'` by IMP_RES_TAC DONE_INTERVAL
    THEN `done_e tg` by RW_TAC arith_ss []
    THEN `!tt. te < tt /\ tt <= tg ==> done_e tt` by RW_TAC arith_ss []
    THEN `!t'. te <= t' ==> t' <= tg ==> done_e t'` by IMP_RES_TAC INTERVAL_LEMMA
    THEN `!tt. te <= tt /\ tt < tg ==> done_e tt` by RW_TAC arith_ss []
    THEN `!tt. tt <= tg ==> te < tt ==> ~(POSEDGE done_e tt)`
         by IMP_RES_TAC HOLDT_NOT_POSEDGE'
    THEN `!tt. te < tt /\ tt <= tg ==> ~(POSEDGE start_f tt)`
         by PROVE_TAC [POSEDGE_IMPL, POSEDGE_def, POSEDGE, AND_def]
    THEN `!t. ~POSEDGE start_f (t + 1) ==> done_f t ==> done_f (t + 1)`
         by IMP_RES_TAC SAFE_DEV_def
    THEN `!t. done_f t /\ ~POSEDGE start_f (t + 1) ==> done_f (t + 1)`
         by PROVE_TAC []
    THEN `!t'. t' <= tg ==> te < t' ==> done_f t'` by IMP_RES_TAC DONE_INTERVAL
    THEN `done_f tg` by RW_TAC arith_ss []
    THEN `tg > t` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `tg` THEN PROVE_TAC [AND_def]
    ]
    ]
    , (* end of Cases_on `done_f te` *)
    `?tf. tf > te /\ HOLDF (te,tf) done_f /\ done_f tf`
          by RW_TAC arith_ss [] (* done_e te /\ ~done_f te *)
    THEN `!tt. te < tt /\ tt <= tf ==> ~(POSEDGE start tt)` by REWRITE_TAC []
    THENL [
    `HOLDF (te,tf) done`         by PROVE_TAC [HOLDF_def, AND_def]
    THEN `HOLDF (te+1,tf+1) c1` by PROVE_TAC [HOLDF_DEL]
    THEN `HOLDF (te+1,tf+1) start` by PROVE_TAC [HOLDF_def,AND_def]
    THEN `!tt. (te+1) <= tt /\ tt < (tf+1) ==> ~(POSEDGE start tt)`
         by PROVE_TAC [HOLDF_def, POSEDGE_def]
    THEN `!t1 t2 tt. (t1+1) <= tt /\ tt < (t2+1) = (t1 < tt /\ tt <= t2)`
         by RW_TAC arith_ss [] THEN PROVE_TAC []
    , (* end of `!tt. te < tt /\ tt <= tf ==> ~(POSEDGE start tt)` *)
    `te < tf` by RW_TAC arith_ss []
    THEN `!t. ~POSEDGE start (t + 1) ==> done_e t ==> done_e (t + 1)`
         by IMP_RES_TAC SAFE_DEV_def
    THEN `!t. done_e t /\ ~POSEDGE start (t + 1) ==> done_e (t + 1)`
         by PROVE_TAC []
    THEN `!t'. t' <= tf ==> te < t' ==> done_e t'` by IMP_RES_TAC DONE_INTERVAL
    THEN `done_e tf` by RW_TAC arith_ss []
    THEN Cases_on `done_g tf`
    THENL [
    `tf > t` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `tf` THEN PROVE_TAC [AND_def]
    , (* end of Cases_on `done_g tf` *)
    `?tg. tg > tf /\ HOLDF (tf,tg) done_g /\ done_g tg`
         by RW_TAC arith_ss [] (* done_e tf /\ done_f tf /\ ~done_g tf *)
    THEN `tg > t` by RW_TAC arith_ss []
    THEN `!tt. tf < tt /\ tt <= tg ==> ~(POSEDGE start tt)` by REWRITE_TAC []
    THENL [
    `HOLDF (tf,tg) done` by PROVE_TAC [HOLDF_def, AND_def]
    THEN `HOLDF (tf+1,tg+1) c1` by PROVE_TAC [HOLDF_DEL]
    THEN `HOLDF (tf+1,tg+1) start` by PROVE_TAC [HOLDF_def,AND_def]
    THEN `!tt. (tf+1) <= tt /\ tt < (tg+1) ==> ~(POSEDGE start tt)`
         by PROVE_TAC [HOLDF_def, POSEDGE_def]
    THEN `!t1 t2 tt. (t1+1) <= tt /\ tt < (t2+1) = (t1 < tt /\ tt <= t2)`
         by RW_TAC arith_ss [] THEN PROVE_TAC []
    , (* end of `!tt. tf < tt /\ tt <= tg ==> ~(POSEDGE start tt)` *)
    `t < tg` by RW_TAC arith_ss []
    THEN `tf < tg` by RW_TAC arith_ss []
    THEN `!t. ~POSEDGE start (t + 1) ==> done_e t ==> done_e (t + 1)`
          by IMP_RES_TAC SAFE_DEV_def
    THEN `!t. done_e t /\ ~POSEDGE start (t + 1) ==> done_e (t + 1)`
          by PROVE_TAC []
    THEN `!t'. t' <= tg ==> tf < t' ==> done_e t'` by IMP_RES_TAC DONE_INTERVAL
    THEN `done_e tg` by RW_TAC arith_ss []
    THEN `!tt. tf < tt /\ tt <= tg ==> done_e tt` by RW_TAC arith_ss []
    THEN `!t'. tf <= t' ==> t' <= tg ==> done_e t'` by IMP_RES_TAC INTERVAL_LEMMA
    THEN `!tt. tf <= tt /\ tt < tg ==> done_e tt` by RW_TAC arith_ss []
    THEN `!tt. tt <= tg ==> tf < tt ==> ~(POSEDGE done_e tt)`
         by IMP_RES_TAC HOLDT_NOT_POSEDGE'
    THEN `!tt. tf < tt /\ tt <= tg ==> ~(POSEDGE start_f tt)`
         by PROVE_TAC [POSEDGE_IMPL, POSEDGE_def, POSEDGE, AND_def]
    THEN `!t. ~POSEDGE start_f (t + 1) ==> done_f t ==> done_f (t + 1)`
         by IMP_RES_TAC SAFE_DEV_def
    THEN `!t. done_f t /\ ~POSEDGE start_f (t + 1) ==> done_f (t + 1)`
         by PROVE_TAC []
    THEN `!t'. t' <= tg ==> tf < t' ==> done_f t'` by IMP_RES_TAC DONE_INTERVAL
    THEN `done_f tg` by RW_TAC arith_ss []
    THEN `tg > t` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `tg` THEN PROVE_TAC [AND_def]
    ]]]]]]);



(*****************************************************************************)
(* REC_e_g_LEMMA - if the recursive circuit holds the state                  *)
(* (~(done t0) /\ done_e t0 /\ done_g t0), then there is no positive edge at *)
(* start_f in the next time and done_e and done_g remain asserted            *)
(*****************************************************************************)

val REC_e_g_LEMMA = store_thm("REC_e_g_LEMMA",
    ``~(done t0) /\ done_e t0 /\ done_g t0 /\
      CALL (load,inp,done,done_g,data_g,start_e,inp_e) /\
      DFF (inp_e,start_e,q) /\ SELECT (done_e,data_e,start_f,start_g) /\
      FINISH (done_e,done_f,done_g,done) /\
      SAFE_DEV f1 (start_e,inp_e,done_e,data_e) /\
      SAFE_DEV f2 (start_f,q,done_f,out) /\
      SAFE_DEV f3 (start_g,q,done_g,data_g)
      ==> (~POSEDGE start_f (t0+1)) /\ done_e (t0+1) /\ done_g (t0+1)``,
    REWRITE_TAC [SAFE_DEV_def,FINISH_def,CALL_def,SELECT_def]
    THEN STRIP_TAC
    THEN `~(c1 (t0+1))` by PROVE_TAC [DEL_def]
    THEN `~(POSEDGE done_g (t0+1))` by PROVE_TAC [POSEDGE]
    THEN `~(sel (t0+1))` by PROVE_TAC [POSEDGE_IMPL,POSEDGE]
    THEN `~(POSEDGE start_e (t0+1))` by PROVE_TAC [OR_def,AND_def,POSEDGE]
    THEN `~POSEDGE start_f (t0+1)` by PROVE_TAC [POSEDGE_def,POSEDGE,
         POSEDGE_IMPL,AND_def]
    THEN `~POSEDGE start_g (t0+1)` by PROVE_TAC [POSEDGE_def,POSEDGE,
         POSEDGE_IMPL,AND_def]
    THEN `done_e (t0+1)` by PROVE_TAC []
    THEN `done_g (t0+1)` by PROVE_TAC []
    THEN PROVE_TAC []);



(*****************************************************************************)
(* REC_e_f_g - if the recursive circuit holds the state                      *)
(* (~done t0 /\ done_e t0 /\ done_f t0 /\ done_g t0),                        *)
(* then done will be asserted evetually                                      *)
(*****************************************************************************)
val REC_e_f_g = store_thm("REC_e_f_g",
    ``~(done t0) /\ done_e t0 /\ done_f t0 /\ done_g t0 /\
      CALL (load,inp,done,done_g,data_g,start_e,inp_e) /\
      DFF (inp_e,start_e,q) /\ SELECT (done_e,data_e,start_f,start_g) /\
      FINISH (done_e,done_f,done_g,done) /\
      DEV f1 (start_e,inp_e,done_e,data_e) /\
      DEV f2 (start_f,q,done_f,out) /\
      DEV f3 (start_g,q,done_g,data_g)
      ==> ?t1. t1 > t0 /\ HOLDF (t0,t1) done /\ done t1``,
    RW_TAC arith_ss [DEV_def,SAFE_DEV_def,FINISH_def]
    THEN Cases_on `done_g (t0-1)`
    THENL [
    Cases_on `t0`
    THENL [
    `done_e 1` by REWRITE_TAC []
    THENL [
    `?c0 c1 start sel.
        POSEDGE_IMP (load,c0) /\ DEL (done,c1) /\ AND (c0,c1,start) /\
        OR (start,sel,start_e) /\ POSEDGE_IMP (done_g,sel) /\
        MUX (sel,data_g,inp,inp_e)` by PROVE_TAC [CALL_def]
    THEN `~(POSEDGE done_g (0+1))` by PROVE_TAC [POSEDGE]
    THEN `~(sel (0+1))` by PROVE_TAC [POSEDGE,POSEDGE_IMPL]
    THEN `~(c1 (0+1))` by PROVE_TAC [DEL_def]
    THEN `1 = 0 + 1` by RW_TAC arith_ss []
    THEN `~(POSEDGE start_e 1)` by PROVE_TAC [AND_def,OR_def,POSEDGE]
    THEN PROVE_TAC []
    , (* end of `done_e 1` *)
    `done_f 1 /\ done_g 1` by REWRITE_TAC []
    THENL [
    `?start' not_e.
        POSEDGE_IMP (done_e,start') /\ AND (start',data_e,start_f) /\
        NOT (data_e,not_e) /\ AND (not_e,start',start_g)`
        by PROVE_TAC [SELECT_def]
    THEN `~(POSEDGE start_f (0+1))`
        by PROVE_TAC [POSEDGE,POSEDGE_IMPL,AND_def]
    THEN `~(POSEDGE start_g (0+1))`
        by PROVE_TAC [POSEDGE,POSEDGE_IMPL,AND_def]
    THEN `1 = 0 + 1` by RW_TAC arith_ss []
    THEN PROVE_TAC []
    , (* end of `done_f 1 /\ done_g 1` *)
    `1 = 0 + 1` by RW_TAC arith_ss []
    THEN `c3 1` by PROVE_TAC [DEL_def]
    THEN `!t. 0 <= t /\ t < (0+1) ==> (t=0)` by RW_TAC arith_ss []
    THEN `HOLDF (0,1) done` by PROVE_TAC [HOLDF_def]
    THEN `1 > 0` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `1`
    THEN PROVE_TAC [AND_def]
    ]
    ]
    , (* end of Cases_on `t0` *)
    `SUC n - 1 + 1 = SUC n` by RW_TAC arith_ss []
    THEN `c3 (SUC n)` by PROVE_TAC [DEL_def]
    THEN PROVE_TAC [AND_def]
    ]
    , (* end of Cases_on `done_g (t0-1)` *)

    `~(POSEDGE start_e (t0+1))` by REWRITE_TAC []
    THENL [
    `?c0 c1 start sel.
            POSEDGE_IMP (load,c0) /\ DEL (done,c1) /\ AND (c0,c1,start) /\
            OR (start,sel,start_e) /\ POSEDGE_IMP (done_g,sel) /\
            MUX (sel,data_g,inp,inp_e)`
         by PROVE_TAC [CALL_def]
    THEN `?start' not_e.
             POSEDGE_IMP (done_e,start') /\ AND (start',data_e,start_f) /\
             NOT (data_e,not_e) /\ AND (not_e,start',start_g)`
             by PROVE_TAC [SELECT_def]
    THEN `~(start (t0+1))` by REWRITE_TAC []
    THENL [
    Cases_on `t0`
    THENL [
    PROVE_TAC [DEL_def,AND_def] (* t0 = 0 *)
    , (* end of Cases_on `t0` *)
    PROVE_TAC [AND_def, DEL_def] (* t0 > 0 *)
    ]
    , (* end of `~(start (t0+1))` *)
    `~(sel (t0+1))` by REWRITE_TAC []
    THENL [
    `~(POSEDGE done_g (t0+1))` by PROVE_TAC [POSEDGE,POSEDGE_def]
    THEN PROVE_TAC [POSEDGE_IMPL,POSEDGE]
    , (* end of `~(sel (t0+1))` *)
    PROVE_TAC [POSEDGE,OR_def]
    ]
    ]
    , (* end of ~(POSEDGE start_e (t0+1)) *)
    `?start' not_e.
          POSEDGE_IMP (done_e,start') /\ AND (start',data_e,start_f) /\
          NOT (data_e,not_e) /\ AND (not_e,start',start_g)`
          by PROVE_TAC [SELECT_def]
    THEN `?c2 c3 c4.
             DEL (done_g,c3) /\ AND (done_g,c3,c4) /\
             AND (done_f,done_e,c2) /\ AND (c2,c4,done)`
             by PROVE_TAC [FINISH_def]
    THEN `done_e (t0+1)` by PROVE_TAC []
    THEN `~(POSEDGE done_e (t0+1))` by PROVE_TAC [POSEDGE,POSEDGE_def]
    THEN `~(start' (t0+1))` by PROVE_TAC [POSEDGE_IMPL,POSEDGE,POSEDGE_def]
    THEN `~(start_f (t0+1))` by PROVE_TAC [AND_def,POSEDGE_IMPL,POSEDGE,POSEDGE_def]
    THEN `~(POSEDGE start_f (t0+1))` by PROVE_TAC [AND_def,POSEDGE_IMPL,
             POSEDGE,POSEDGE_def]
    THEN `~(POSEDGE start_g (t0+1))` by PROVE_TAC [AND_def,POSEDGE_IMPL,
             POSEDGE,POSEDGE_def]
    THEN `done_f (t0+1) /\ done_g (t0+1)` by PROVE_TAC []
    THEN `t0 + 1 > t0` by RW_TAC arith_ss []
    THEN `!tt. t0 <= tt /\ tt < (t0+1) ==> ~(done tt)` by REWRITE_TAC []
    THENL [
    RW_TAC arith_ss []
    THEN Cases_on `t0 = tt`
    THENL [
    PROVE_TAC []
    , (* end of Cases_on `t0 = tt` *)
    `t0 < tt` by RW_TAC arith_ss []
    THEN `~(t0 < tt /\ tt < (t0+1))` by RW_TAC arith_ss []
    THEN PROVE_TAC [] (* t0 < tt *)
    ]
    , (* end of `!tt. t0 <= tt /\ tt < (t0+1) ==> ~(done tt)` *)
    `HOLDF (t0,t0+1) done` by PROVE_TAC [HOLDF_def]
    THEN `c3 (t0+1)` by PROVE_TAC [DEL_def,AND_def]
    THEN `done (t0+1)` by PROVE_TAC [DEL_def,AND_def]
    THEN Q.EXISTS_TAC `t0+1` THEN PROVE_TAC []
    ]]]);


(*****************************************************************************)
(* REC_e_NOTf_g - if the recursive circuit holds the state                   *)
(* (~done t0 /\ done_e t0 /\ ~done_f t0 /\ done_g t0),                       *)
(* then done will be asserted evetually                                      *)
(*****************************************************************************)

val REC_e_NOTf_g = store_thm("REC_e_NOTf_g",
    ``~(done t0) /\ done_e t0 /\ ~(done_f t0) /\ done_g t0 /\
      CALL (load,inp,done,done_g,data_g,start_e,inp_e) /\
      DFF (inp_e,start_e,q) /\ SELECT (done_e,data_e,start_f,start_g) /\
      FINISH (done_e,done_f,done_g,done) /\
      DEV f1 (start_e,inp_e,done_e,data_e) /\
      DEV f2 (start_f,q,done_f,out) /\
      DEV f3 (start_g,q,done_g,data_g)
      ==> ?t1. t1 > t0 /\ HOLDF (t0,t1) done /\ done t1``,
    RW_TAC arith_ss [DEV_def]
    THEN Cases_on `done_f (t0+1)`
    THENL [
    REPEAT (PAT_ASSUM ``LIV X`` kill)
    THEN `done_e (t0 + 1) /\ done_g (t0 + 1)`
         by (MP_TAC REC_e_g_LEMMA THEN ASM_REWRITE_TAC [] THEN PROVE_TAC[])
    THEN `done (t0+1)` by FULL_SIMP_TAC std_ss [FINISH_def,AND_def,DEL_def]
    THEN `!tt. t0 <= tt /\ tt < (t0+1) ==> ~(done tt)` by REWRITE_TAC []
    THENL [
    RW_TAC arith_ss [] THEN Cases_on `t0 = tt`
    THENL [
    RW_TAC arith_ss []
    , (* end of Cases_on `t0 = tt` *)
    `t0 < tt` by RW_TAC arith_ss []
    THEN `~(t0 < tt /\ tt < (t0+1))` by RW_TAC arith_ss []
    THEN PROVE_TAC []
    ]
    , (* end of `!tt. t0 <= tt /\ tt < (t0+1) ==> ~(done tt)` *)
    `HOLDF (t0,t0+1) done` by PROVE_TAC [HOLDF_def]
    THEN `t0 +1 > t0` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `t0+1` THEN PROVE_TAC []
    ]
    , (* end of Cases_on `done_f (t0+1)` *)
   `done_e (t0 + 1) /\ done_g (t0 + 1)`
     by (MP_TAC REC_e_g_LEMMA THEN ASM_REWRITE_TAC [] THEN PROVE_TAC[])
   THEN `?tt0. tt0 = t0 + 1` by RW_TAC arith_ss []
   THEN `done_e tt0 /\ done_g tt0 /\ ~(done_f tt0)` by RW_TAC arith_ss []
   THEN `done_g (tt0-1)` by RW_TAC arith_ss []
   THEN `?t1. t1 > tt0 /\ HOLDF (tt0,t1) done_f /\ done_f t1`
        by PROVE_TAC [LIV_LEMMA]
   THEN REPEAT (PAT_ASSUM ``LIV X`` kill)
   THEN PAT_ASSUM ``~(done_f (t0:num))`` kill
   THEN PAT_ASSUM ``~(done_f ((t0:num)+1))`` kill
   THEN PAT_ASSUM ``done_e (t0:num)`` kill
   THEN PAT_ASSUM ``done_g (t0:num)`` kill
   THEN PAT_ASSUM ``done_e ((t0:num)+1)`` kill
   THEN PAT_ASSUM ``done_g ((t0:num)+1)`` kill
   THEN `!tt. tt0 < tt /\ tt <= t1 ==> done_g tt /\ done_e tt`
        by PROVE_TAC [BASE_LEMMA]
   THEN `HOLDF (t0,t1) done` by REWRITE_TAC []
   THENL [
   `HOLDF (tt0,t1) done` by FULL_SIMP_TAC std_ss [FINISH_def,AND_def,HOLDF_def]
   THEN `!tt. t0 + 1 <= tt /\ tt < t1 ==> ~(done tt)` by PROVE_TAC [HOLDF_def]
   THEN `!tt. t0 < tt /\ tt <= (t1-1) ==> ~(done tt)` by RW_TAC arith_ss []
   THEN `!tt. t0 <= tt /\ tt <= (t1-1) ==> ~(done tt)` by PROVE_TAC [INTERVAL_LEMMA]
   THEN `!tt. t0 <= tt /\ tt < t1 ==> ~(done tt)` by RW_TAC arith_ss []
   THEN PROVE_TAC [HOLDF_def]
   , (* end of `HOLDF (t0,t1) done` *)
   `?c2 c3 c4. DEL (done_g,c3) /\ AND (done_g,c3,c4) /\
         AND (done_f,done_e,c2) /\ AND (c2,c4,done)`
         by PROVE_TAC [FINISH_def]
   THEN `done_g t1 /\ done_e t1` by RW_TAC arith_ss []
   THEN `t1 > t0` by RW_TAC arith_ss []
   THEN Cases_on `done t1`
   THENL [
   Q.EXISTS_TAC `t1` THEN PROVE_TAC []
   , (* end of Cases_on `done t1` *)
   `~POSEDGE start_f (t1 + 1) /\ done_e (t1 + 1) /\ done_g (t1+1)`
        by (MP_TAC (Q.INST [`t0` |-> `t1`] REC_e_g_LEMMA)
            THEN ASM_REWRITE_TAC [] THEN PROVE_TAC[])
   THEN `done_f (t1+1)` by FULL_SIMP_TAC std_ss [SAFE_DEV_def]
   THEN `done (t1+1)` by FULL_SIMP_TAC std_ss [FINISH_def,AND_def,DEL_def]
   THEN `!tt. t0 <= tt /\ tt < t1 ==> ~(done tt)` by PROVE_TAC [HOLDF_def]
   THEN `!tt. t0 <= tt /\ tt <= t1 ==> ~(done tt)` by REWRITE_TAC []
   THENL [
   RW_TAC arith_ss [] THEN Cases_on `t1=tt`
   THENL [
   PROVE_TAC []
   , (* end of Cases_on `t1=tt` *)
   RW_TAC arith_ss []
   ]
   , (* end of `!tt. t0 <= tt /\ tt <= t1 ==> ~(done tt)` *)
   `!tt. t0 <= tt /\ tt < (t1+1) ==> ~done tt`
        by RW_TAC arith_ss []
   THEN `HOLDF (t0,t1+1) done` by PROVE_TAC [HOLDF_def]
   THEN `t1+1 > t0` by RW_TAC arith_ss []
   THEN Q.EXISTS_TAC `t1+1` THEN PROVE_TAC []
   ]]]]);



(*****************************************************************************)
(* REC_e_g - if the recursive circuit holds the state                        *)
(* (~done t0 /\ done_e t0 /\ done_g t0),                                     *)
(* then done will be asserted evetually                                      *)
(*****************************************************************************)

val REC_e_g = store_thm("REC_e_g",
    ``~done t0 /\ done_e t0 /\ done_g t0 /\
      CALL (load,inp,done,done_g,data_g,start_e,inp_e) /\
      DFF (inp_e,start_e,q) /\ SELECT (done_e,data_e,start_f,start_g) /\
      FINISH (done_e,done_f,done_g,done) /\
      DEV f1 (start_e,inp_e,done_e,data_e) /\
      DEV f2 (start_f,q,done_f,out) /\
      DEV f3 (start_g,q,done_g,data_g) ==>
      ?t1. t1 > t0 /\ HOLDF (t0,t1) done /\ done t1``,
    Cases_on `done_f t0`
    THENL [metisLib.METIS_TAC [REC_e_f_g],
           metisLib.METIS_TAC [REC_e_NOTf_g]]);



(*****************************************************************************)
(* REC_LIV_LEMMA - the recursive circuit can be triggered by an external     *)
(* client or internally by the recursive call. Both types of call are        *)
(* characterised by the state:                                               *)
(* done_e t /\ done_g (t+1) /\ POSEDGE start_e (t+1)                         *)
(* If such state holds, then done will be asserted eventually                *)
(*****************************************************************************)

val REC_LIV_LEMMA = store_thm("REC_LIV_LEMMA",
    ``CALL (load,inp,done,done_g,data_g,start_e,inp_e) /\
      DFF (inp_e,start_e,q) /\ SELECT (done_e,data_e,start_f,start_g) /\
      FINISH (done_e,done_f,done_g,done) /\
      (!x. ~f1 x ==> variant (f3 x) < variant x) /\
      done_e t /\ done_g (t + 1) /\ POSEDGE start_e (t + 1) /\
      DEV f1 (start_e,inp_e,done_e,data_e) /\
      DEV f2 (start_f,q,done_f,out) /\ DEV f3 (start_g,q,done_g,data_g)
      ==> ?t'. t' > (t+1) /\ HOLDF (t+1,t') done /\ done t'``,
    RW_TAC arith_ss []
    THEN completeInduct_on `variant (inp_e (t+1))`
    THEN REPEAT STRIP_TAC
    THEN `?te. te > t + 1 /\ HOLDF (t + 1,te) done_e /\ done_e te /\
          (data_e te = f1 (inp_e (t+1)))` by REWRITE_TAC []
    THENL [
    `SAFE_DEV f1 (start_e,inp_e,done_e,data_e)` by IMP_RES_TAC DEV_def
    THEN IMP_RES_TAC SAFE_DEV_def
    THEN Q.EXISTS_TAC `t'`
    THEN RW_TAC arith_ss []
    , (* end of `?te. te > t+1 /\ HOLDF (t+1,te) done_e /\ ... *)
    Cases_on `data_e te`
    THENL [
    PAT_ASSUM ``!(m:num). X`` kill (* delete the ind hyp *)
    THEN `done_g te` by REWRITE_TAC []
    THENL [
    `!tt. (t+1) <= tt /\ tt < te ==> ~(done_e tt)` by PROVE_TAC [HOLDF_def]
    THEN `?start' not_e. POSEDGE_IMP (done_e,start') /\ AND (start',data_e,start_f) /\
                   NOT (data_e,not_e) /\ AND (not_e,start',start_g)`
         by PROVE_TAC [SELECT_def]
    THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(start' tt)`
            by PROVE_TAC [POSEDGE_def, POSEDGE,POSEDGE_IMPL]
    THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(start_g tt)` by FULL_SIMP_TAC std_ss [AND_def]
    THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(POSEDGE start_g tt)` by RW_TAC std_ss [POSEDGE_def]
    THEN `!tt. (t+1) < tt /\ tt < te ==> ~(POSEDGE start_g tt)` by RW_TAC arith_ss []
    THEN `~(POSEDGE start_g te)` by FULL_SIMP_TAC std_ss [NOT_def,AND_def,POSEDGE_def]
    THEN `!tt. (t+1) < tt /\ tt <= te ==> ~(POSEDGE start_g tt)`
           by PROVE_TAC [INTERVAL_LEMMA]
    THEN `SAFE_DEV f3 (start_g,q,done_g,data_g)` by PROVE_TAC [DEV_def]
    THEN `(!t. done_g t /\ ~POSEDGE start_g (t + 1) ==> done_g (t + 1))`
         by FULL_SIMP_TAC std_ss [SAFE_DEV_def]
    THEN `t + 1 < te ==> !t'. t' <= te ==> t + 1 < t' ==> done_g t'`
           by IMP_RES_TAC DONE_INTERVAL
    THEN `done_g te` by RW_TAC arith_ss []
    , (* end of `done_g te` *)
    `HOLDF (t+1,te) done` by FULL_SIMP_TAC std_ss [FINISH_def,HOLDF_def,AND_def]
    THEN Cases_on `done te`
    THENL [
    PROVE_TAC []
    , (* end of Cases_on `done te` *)
    PAT_ASSUM ``data_e (te:num) = X`` kill
    THEN PAT_ASSUM ``data_e (te:num)`` kill
    THEN PAT_ASSUM ``done_e (t:num)`` kill
    THEN PAT_ASSUM ``!x.X`` kill
    THEN PAT_ASSUM ``done_g ((t:num)+1)`` kill
    THEN PAT_ASSUM ``POSEDGE start_e ((t:num)+1)`` kill
    THEN PAT_ASSUM ``HOLDF ((t:num)+1,(te:num)) done_e`` kill
    THEN `?t1. t1 > te /\ HOLDF (te,t1) done /\ done t1`
        by metisLib.METIS_TAC [REC_e_g]
    THEN `HOLDF (t+1,t1) done` by PROVE_TAC [HOLDF_TRANS]
    THEN `t1 > t+1` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `t1` THEN PROVE_TAC []
    ]
    ]
    , (* end of Cases_on `data_e te` *)
    `POSEDGE start_g te` by REWRITE_TAC []
    THENL [

    PAT_ASSUM ``!(m:num). m < X ==> Y`` kill
    THEN `?start' not_e. POSEDGE_IMP (done_e,start') /\
           AND (start',data_e,start_f) /\ NOT (data_e,not_e) /\
           AND (not_e,start',start_g)`
       by (FULL_SIMP_TAC std_ss [SELECT_def] THEN METIS_TAC[])
    THEN `POSEDGE done_e te` by IMP_RES_TAC HOLDF_POSEDGE
    THEN `~(done_e (te-1))` by FULL_SIMP_TAC std_ss [POSEDGE_def]
    THEN `~(POSEDGE done_e (te-1))` by FULL_SIMP_TAC std_ss [POSEDGE_def]
    THEN `~(start' (te-1))` by PROVE_TAC [POSEDGE,POSEDGE_def,
                               POSEDGE_IMP_def, POSEDGE_IMPL]
    THEN `start' te` by PROVE_TAC [POSEDGE,POSEDGE_def,
                            POSEDGE_IMP_def, POSEDGE_IMPL]
    THEN FULL_SIMP_TAC std_ss [AND_def,NOT_def, POSEDGE_def]
    , (* end of `POSEDGE start_g te` *)
    `done_g (te-1)` by REWRITE_TAC []
    THENL [
    PAT_ASSUM ``!(m:num). m < X ==> Y`` kill
    THEN `?start' not_e. POSEDGE_IMP (done_e,start') /\
           AND (start',data_e,start_f) /\ NOT (data_e,not_e) /\
           AND (not_e,start',start_g)` by PROVE_TAC [SELECT_def]
    THEN `!t0 t1 s. HOLDF (t0 + 1,t1) s ==> !t. t0 < t /\ t <= t1 - 1 ==> ~s t`
            by RW_TAC arith_ss [HOLDF_def]
    THEN `!tt. (t < tt /\ tt <= (te-1) ==> ~(POSEDGE start_g tt))`
           by PROVE_TAC [POSEDGE_def, POSEDGE_IMP_def, AND_def]
    THEN `!tt. ((t+1) < tt /\ tt <= (te-1) ==> ~(POSEDGE start_g tt))`
          by RW_TAC arith_ss []
    THEN `SAFE_DEV f3 (start_g,q,done_g,data_g)` by FULL_SIMP_TAC std_ss [DEV_def]
    THEN `(!t. done_g t /\ ~POSEDGE start_g (t + 1) ==> done_g (t + 1))`
         by FULL_SIMP_TAC std_ss [SAFE_DEV_def]
    THEN `t+1 < te` by RW_TAC arith_ss []
    THEN `t + 1 < te - 1 ==> !t'. t + 1 < t' ==> t' <= te - 1 ==> done_g t'`
          by IMP_RES_TAC DONE_INTERVAL
    THEN Cases_on `t+1 < te-1`
    THENL [
    RW_TAC arith_ss []
    , (* end of Cases_on `t+1 < te-1` *)
    `t+1 = te-1` by RW_TAC arith_ss [] THEN PROVE_TAC []
    ]
    , (* end of `done_g (te-1)` *)
    `?tg. (tg > te) /\ HOLDF (te,tg) done_g /\ done_g tg /\
         (data_g tg = f3 (inp_e (t+1)))` by REWRITE_TAC []
    THENL [
    PAT_ASSUM ``!(m:num). m < X ==> Y`` kill
    THEN `SAFE_DEV f3 (start_g,q,done_g,data_g)` by PROVE_TAC [DEV_def]
    THEN `(?tg. tg > (te-1+1) /\ HOLDF (te-1+1,tg) done_g /\ done_g tg /\
             (data_g tg = f3 (q (te-1+1))))` by REWRITE_TAC []
    THENL [
    IMP_RES_TAC SAFE_DEV_def
    THEN `te-1+1 = te` by RW_TAC arith_ss []
    THEN `POSEDGE start_g (te-1+1)` by PROVE_TAC []
    THEN PROVE_TAC []
    , (* end of (?tg. tg > (te-1+1) /\ HOLDF (te-1+1,tg) done_g /\ ..) *)
    `?c0 c1 start sel. POSEDGE_IMP (load,c0) /\ DEL (done,c1) /\
           AND (c0,c1,start) /\ OR (start,sel,start_e) /\ POSEDGE_IMP (done_g,sel) /\
           MUX (sel,data_g,inp,inp_e)` by (FULL_SIMP_TAC std_ss [CALL_def] THEN PROVE_TAC[])
    THEN `tg > te` by RW_TAC arith_ss []
    THEN `te-1+1 = te` by RW_TAC arith_ss []
    THEN `HOLDF (te,tg) done_g` by PROVE_TAC []
    THEN `q te = inp_e (t+1)` by ASM_REWRITE_TAC []
    THENL [
    `!tt. (t+1) < tt /\ tt <= te ==> ~(sel tt)` by ASM_REWRITE_TAC []
    THENL [
    `t + 1 < (te-1) ==> !tt. tt <= (te-1) ==> t + 1 < tt ==> done_g tt`
        by ASM_REWRITE_TAC []
    THENL [
    `!tt. (t+1) <= tt /\ tt < te ==> ~(done_e tt)` by PROVE_TAC [HOLDF_def]
    THEN `?start' not_e. POSEDGE_IMP (done_e,start') /\
            AND (start',data_e,start_f) /\ NOT (data_e,not_e) /\
            AND (not_e,start',start_g)` by (FULL_SIMP_TAC std_ss [SELECT_def] THEN PROVE_TAC[])
    THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(start' tt)`
          by PROVE_TAC [POSEDGE_def, POSEDGE,POSEDGE_IMPL]
    THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(start_g tt)` by FULL_SIMP_TAC std_ss [AND_def]
    THEN `!tt. (t+1) <= tt /\ tt < te ==> ~(POSEDGE start_g tt)`
          by PROVE_TAC [POSEDGE_def]
    THEN `!tt. (t+1) < tt /\ tt < te ==> ~(POSEDGE start_g tt)` by RW_TAC arith_ss []
    THEN `!tt. (t+1) < tt /\ tt <= (te-1) ==> ~(POSEDGE start_g tt)`
         by RW_TAC arith_ss []
    THEN `(!t. done_g t /\ ~POSEDGE start_g (t + 1) ==> done_g (t + 1))`
         by FULL_SIMP_TAC std_ss [SAFE_DEV_def]
    THEN IMP_RES_TAC DONE_INTERVAL
    , (* `t + 1 < (te-1) ==> !tt. tt <= (te-1) ==> t + 1 < tt ==> done_g tt` *)
    Cases_on `t+1 < (te-1)`
    THENL [
    `!tt. (t+1) < tt /\ tt <= (te-1) ==> done_g tt` by RW_TAC arith_ss []
    THEN `!tt. (t+1) <= tt ==> tt <= (te-1) ==> done_g tt` by IMP_RES_TAC INTERVAL_LEMMA
    THEN `!tt. (t+1) <= tt /\ tt <= (te-1) ==> done_g tt` by RW_TAC arith_ss []
    THEN `!tt. tt <= te - 1 ==> t + 1 < tt ==> ~POSEDGE done_g tt`
          by IMP_RES_TAC HOLDT_NOT_POSEDGE
    THEN `!tt. tt <= te - 1 ==> t + 1 < tt ==> ~(sel tt)`
          by PROVE_TAC [POSEDGE_IMPL,POSEDGE,POSEDGE_def]
    THEN `!tt. te <= tt /\ tt < tg ==> ~(done_g tt)` by FULL_SIMP_TAC std_ss [HOLDF_def]
    THEN `~(done_g te)` by RW_TAC arith_ss []
    THEN `~(sel te)` by PROVE_TAC [POSEDGE_def,POSEDGE,POSEDGE_IMPL]
    THEN `!tt. t+1 < tt /\ tt < te ==> ~sel tt` by RW_TAC arith_ss []
    THEN `!tt. tt <= te ==> t + 1 < tt ==> ~sel tt` by IMP_RES_TAC INTERVAL_LEMMA
    THEN RW_TAC arith_ss []
    , (* end of `t+1 < (te-1)` *)
    `t+1 = te-1` by RW_TAC arith_ss []
    THEN RW_TAC arith_ss []
    THEN `tt=te` by RW_TAC arith_ss []
    THEN `!tt. te <= tt /\ tt < tg ==> ~(done_g tt)` by FULL_SIMP_TAC std_ss [HOLDF_def]
    THEN `~(done_g te)` by RW_TAC arith_ss []
    THEN PROVE_TAC [POSEDGE_def,POSEDGE,POSEDGE_IMPL]
    ]
    ]
    , (* end of `!tt. (t+1) < tt /\ tt <= te ==> ~(sel tt)` *)
    `!tt. t + 1 < tt /\ tt <= te ==> ~(start_e tt)` by ASM_REWRITE_TAC []
    THENL [
    `HOLDF (t+1,te) done` by FULL_SIMP_TAC std_ss [FINISH_def,HOLDF_def,AND_def]
    THEN `HOLDF ((t+1)+1,te+1) c1` by IMP_RES_TAC HOLDF_DEL
    THEN `!tt. t + 1 +1 <= tt /\ tt < (te+1) ==> ~(c1 tt)` by FULL_SIMP_TAC std_ss [HOLDF_def]
    THEN `!tt. t + 1 < tt /\ tt <= te ==> ~(c1 tt)` by RW_TAC arith_ss []
    THEN FULL_SIMP_TAC std_ss [AND_def,OR_def]
    , (* end of `!tt. t + 1 < tt /\ tt <= te ==> ~(start_e tt)` *)
    `!tt. 0 < (t+1) /\ (t+1) < tt /\ tt <= te ==> ~(start_e tt)` by RW_TAC arith_ss []
    THEN `0 < t + 1 ==> !tt. (t+1) < tt ==> tt <= te ==> (q tt = (inp_e (t + 1)))`
          by IMP_RES_TAC DFF_INTERVAL2
    THEN RW_TAC arith_ss []
    ]
    ]
    , (* end of `q te = inp_e (t+1)` *)
    Q.EXISTS_TAC `tg` THEN RW_TAC arith_ss []
    ]
    ]
    , (* end of `?tg. (tg > te) /\ HOLDF (te,tg) done_g /\ ... *)
    `POSEDGE start_e tg` by ASM_REWRITE_TAC []
    THENL [
    PAT_ASSUM ``!(m:num). m < X ==> Y`` kill
    THEN `!tt. te <= tt /\ tt < tg ==> ~(done_g tt)` by FULL_SIMP_TAC std_ss [HOLDF_def]
    THEN `~(done_g (tg-1))` by RW_TAC arith_ss []
    THEN `tg-1 > 0` by RW_TAC arith_ss []
    THEN `POSEDGE done_g ((tg-1)+1)` by RW_TAC arith_ss [POSEDGE]
    THEN `tg-1+1 = tg` by RW_TAC arith_ss []
    THEN `POSEDGE done_g tg` by PROVE_TAC []
    THEN `?c0 c1 start sel. POSEDGE_IMP (load,c0) /\
              DEL (done,c1) /\ AND (c0,c1,start) /\
              OR (start,sel,start_e) /\ POSEDGE_IMP (done_g,sel) /\
              MUX (sel,data_g,inp,inp_e)` by
          (FULL_SIMP_TAC std_ss [CALL_def] THEN PROVE_TAC[])
    THEN `~(sel (tg-1)) /\ sel tg` by PROVE_TAC [POSEDGE,POSEDGE_def,POSEDGE_IMPL]
    THEN `HOLDF (t+1,te) done` by FULL_SIMP_TAC std_ss [FINISH_def,HOLDF_def,AND_def]
    THEN `HOLDF (te,tg) done` by  FULL_SIMP_TAC std_ss [FINISH_def,HOLDF_def,AND_def]
    THEN `HOLDF (t+1,tg) done` by IMP_RES_TAC HOLDF_TRANS
    THEN `HOLDF (t+1+1,tg+1) c1` by IMP_RES_TAC HOLDF_DEL
    THEN `!tt. t+1+1 <= tt /\ tt < tg+1 ==> ~(c1 tt)` by FULL_SIMP_TAC std_ss [HOLDF_def]
    THEN `~(c1 (tg-1))` by RW_TAC arith_ss []
    THEN FULL_SIMP_TAC std_ss [AND_def,OR_def,POSEDGE_def]
    , (* end of `POSEDGE start_e tg` *)
    `done_e (tg-1)` by ASM_REWRITE_TAC []
    THENL [
    PAT_ASSUM ``!(m:num). m < X ==> Y`` kill
    THEN Cases_on `te < (tg-1)`
    THENL [
     `?c0 c1 start sel. POSEDGE_IMP (load,c0) /\ DEL (done,c1) /\
           AND (c0,c1,start) /\ OR (start,sel,start_e) /\
           POSEDGE_IMP (done_g,sel) /\ MUX (sel,data_g,inp,inp_e)`
         by (FULL_SIMP_TAC std_ss  [CALL_def] THEN PROVE_TAC[])
    THEN `!tt. te <= tt /\ tt < tg ==> ~(done_g tt)` by FULL_SIMP_TAC std_ss [HOLDF_def]
    THEN `!tt. te <= tt /\ tt <= (tg-1) ==> ~(done_g tt)` by RW_TAC arith_ss []
    THEN `!tt. te <= tt /\ tt <= (tg-1) ==> ~(sel tt)`
          by PROVE_TAC [POSEDGE,POSEDGE_def,POSEDGE_IMPL]
    THEN `HOLDF (te,tg) done` by  FULL_SIMP_TAC std_ss [FINISH_def,HOLDF_def,AND_def]
    THEN `HOLDF (te+1,tg+1) c1` by IMP_RES_TAC HOLDF_DEL
    THEN `!tt. te+1 <= tt /\ tt < tg+1 ==> ~(c1 tt)` by FULL_SIMP_TAC std_ss [HOLDF_def]
    THEN `!tt. te < tt /\ tt <= (tg-1) ==> ~(c1 tt)` by RW_TAC arith_ss []
    THEN `!tt. te < tt /\ tt <= (tg-1) ==> ~(sel tt)` by RW_TAC arith_ss []
    THEN `!tt. te < tt /\ tt <= (tg-1) ==> ~(start tt)` by FULL_SIMP_TAC std_ss [AND_def]
    THEN `!tt. te < tt /\ tt <= (tg-1) ==> ~(POSEDGE start_e tt)`
          by FULL_SIMP_TAC std_ss [OR_def,POSEDGE_def]
    THEN `SAFE_DEV f1 (start_e,inp_e,done_e,data_e)` by PROVE_TAC [DEV_def]
    THEN `!t. done_e t /\ ~POSEDGE start_e (t + 1) ==> done_e (t + 1)`
         by FULL_SIMP_TAC std_ss [SAFE_DEV_def]
    THEN `!tt. tt <= tg - 1 ==> te < tt ==> done_e tt` by IMP_RES_TAC DONE_INTERVAL
    THEN `done_e (tg-1)` by RW_TAC arith_ss []
    , (* end of Cases_on `te < (tg-1)` *)
    `te = tg-1` by RW_TAC arith_ss [] THEN RW_TAC arith_ss []
    ]
    , (* end of `done_e (tg-1)` *)
    `?ttg. ttg = tg-1` by RW_TAC arith_ss []
    THEN `variant (f3 (inp_e (t+1))) < v` by REWRITE_TAC []
    THENL [
    PAT_ASSUM ``!(m:num). m < X ==> Y`` kill
    THEN `~f1 (inp_e (t+1))` by PROVE_TAC []
    THEN PROVE_TAC []
    , (* end of `variant (f3 (inp_e (t+1))) < v` *)
    (* manipulating in the ind hyp *)
    PAT_ASSUM ``!(m:num). (m < v) ==> X`` (fn th => ASSUME_TAC
        (SPEC ``((variant:'a->num) ((f3:'a->'a) ((inp_e:num->'a) (t+1)))):num`` th))
    THEN ASSUM_LIST (fn thl => ASSUME_TAC(MP (el 1 thl) (el 2 thl)))
    THEN PAT_ASSUM ``variant X < Y ==> Z`` kill
    THEN PAT_ASSUM ``!(variant':'a->num) (inp_e':num->'a) (t':num). X``
        (fn th => ASSUME_TAC (SPEC ``variant:'a->num`` th))
    THEN PAT_ASSUM ``!(inp_e':num->'a) (t':num). X``
        (fn th => ASSUME_TAC (SPEC ``inp_e:num->'a`` th))
    THEN PAT_ASSUM ``!(t':num). X``
        (fn th => ASSUME_TAC (SPEC ``ttg:num`` th))
    (* end of manipulating the ind hyp *)
    THEN `variant (f3 (inp_e (t+1))) = variant ((inp_e (ttg+1)))`
         by REWRITE_TAC []
    THENL [
    `f3 (inp_e (t+1)) = (inp_e (ttg+1))` by REWRITE_TAC []
    THENL [
    `tg > (te-1)+1` by RW_TAC arith_ss []
    THEN `HOLDF ((te-1)+1,tg) done_g` by RW_TAC arith_ss []
    THEN `POSEDGE done_g tg` by IMP_RES_TAC HOLDF_POSEDGE
    THEN `?c0 c1 start sel. POSEDGE_IMP (load,c0) /\ DEL (done,c1) /\
           AND (c0,c1,start) /\ OR (start,sel,start_e) /\ POSEDGE_IMP (done_g,sel) /\
           MUX (sel,data_g,inp,inp_e)` by (FULL_SIMP_TAC std_ss [CALL_def] THEN PROVE_TAC [])
    THEN `sel tg` by PROVE_TAC [POSEDGE_IMPL]
    THEN `inp_e tg = data_g tg` by (FULL_SIMP_TAC std_ss [MUX_def] THEN PROVE_TAC[])
    THEN RW_TAC arith_ss []
    , (* end of `f3 (inp_e (t+1)) = (inp_e (ttg+1))` *)
    PROVE_TAC []
    ]
    , (* end of `variant (f3 (inp_e (t+1))) = variant ((inp_e (ttg+1)))` *)
    (* application of the ind hyp *)
    `?tf'. tf' > ttg + 1 /\ HOLDF (ttg + 1,tf') done /\ done tf'`
          by REWRITE_TAC []
    THENL [
    `tg = tg-1+1` by RW_TAC arith_ss []
    THEN `done_e ttg /\ done_g (ttg + 1) /\ POSEDGE start_e (ttg + 1)`
          by PROVE_TAC []
    THEN PROVE_TAC []
    , (* end of `?tf'. tf' > ttg + 1 /\ HOLDF (ttg + 1,tf') done /\ done tf'` *)
    `tf' > t+1` by RW_TAC arith_ss []
    THEN `HOLDF (t+1,tf') done` by REWRITE_TAC []
    THENL [
    `ttg+1 = tg` by RW_TAC arith_ss []
    THEN `HOLDF (tg,tf') done` by PROVE_TAC []
    THEN `HOLDF (t+1,te) done` by FULL_SIMP_TAC std_ss [FINISH_def,HOLDF_def,AND_def]
    THEN `HOLDF (te,tg) done` by FULL_SIMP_TAC std_ss  [FINISH_def,HOLDF_def,AND_def]
    THEN `HOLDF (t+1,tg) done` by PROVE_TAC [HOLDF_TRANS]
    THEN PROVE_TAC [HOLDF_TRANS]
    , (* end of `HOLDF (t+1,tf') done` *)
    Q.EXISTS_TAC `tf'` THEN PROVE_TAC []
    ] ] ] ] ] ] ] ] ] ] ]);




(*****************************************************************************)
(* REC_NOTg - if the recursive circuit holds the state                       *)
(* (~done_g t0), then done will be asserted evetually                        *)
(*****************************************************************************)

val REC_NOTg = store_thm("REC_NOTg",
    ``~done_g t0 /\
      TOTAL (f1,f2,f3) /\
      CALL (load,inp,done,done_g,data_g,start_e,inp_e) /\
      DFF (inp_e,start_e,q) /\ SELECT (done_e,data_e,start_f,start_g) /\
      FINISH (done_e,done_f,done_g,done) /\
      DEV f1 (start_e,inp_e,done_e,data_e) /\
      DEV f2 (start_f,q,done_f,out) /\
      DEV f3 (start_g,q,done_g,data_g) ==>
      ?t1. t1 > t0 /\ HOLDF (t0,t1) done /\ done t1``,
    RW_TAC arith_ss []
    THEN `?tg. tg > t0 /\ HOLDF (t0,tg) done_g /\ done_g tg`
         by PROVE_TAC [DEV_def,LIV_LEMMA]
    THEN Cases_on `done_e tg`
    THENL [
    `~done tg` by REWRITE_TAC []
    THENL [
    `?c2 c3 c4. DEL (done_g,c3) /\ AND (done_g,c3,c4) /\
                AND (done_f,done_e,c2) /\ AND (c2,c4,done)`
          by PROVE_TAC [FINISH_def]
    THEN `!tt. t0 <= tt /\ tt < tg ==> ~(done_g tt)`
         by PROVE_TAC [HOLDF_def]
    THEN `~(done_g (tg-1))` by RW_TAC arith_ss []
    THEN `tg-1+1 = tg` by RW_TAC arith_ss []
    THEN PROVE_TAC [DEL_def,AND_def]
    , (* end of `~done tg` *)
    PAT_ASSUM ``TOTAL X`` kill
    THEN PAT_ASSUM ``~(done_g (t0:num))`` kill
    THEN `?t1. t1 > tg /\ HOLDF (tg,t1) done /\ done t1`
         by metisLib.METIS_TAC [REC_e_g]
    THEN `HOLDF (t0,tg) done` by PROVE_TAC [HOLDF_def,FINISH_def,AND_def]
    THEN `HOLDF (t0,t1) done` by PROVE_TAC [HOLDF_TRANS]
    THEN `t1 > t0` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `t1`
    THEN PROVE_TAC []
    ] (* `~done tg` *)
    , (* end of Cases_on `done_e tg` *)

    `HOLDF (t0,tg) done` by PROVE_TAC [HOLDF_def,FINISH_def,AND_def]
    THEN PAT_ASSUM ``~(done_g (t0:num))`` kill
    THEN `?te. te > tg /\ HOLDF (tg,te) done_e /\ done_e te`
         by PROVE_TAC [DEV_def,LIV_LEMMA]
    THEN `!tt. tg < tt /\ tt <= (te-1) ==> done_g tt` by REWRITE_TAC []
    THENL [
    Cases_on `tg = te-1`
    THENL [
    RW_TAC arith_ss []
    , (* end of Cases_on `tg=te-1` *)
    `!t. done_g t /\ ~POSEDGE start_g (t + 1) ==> done_g (t + 1)`
          by PROVE_TAC [SAFE_DEV_def,DEV_def]
    THEN `tg < (te-1)` by RW_TAC arith_ss []
    THEN `!tt. tg <= tt /\ tt < te ==> ~(done_e tt)`
         by PROVE_TAC [HOLDF_def]
    THEN `!tt. (tg-1) < tt /\ tt <= (te-1) ==> ~(done_e tt)` by RW_TAC arith_ss []
    THEN `!tt. (tg-1) < tt /\ tt <= (te-1) ==> ~(POSEDGE done_e tt)`
         by PROVE_TAC [POSEDGE,POSEDGE_def]
    THEN `!tt. (tg-1) < tt /\ tt <= (te-1) ==> ~(POSEDGE start_g tt)`
         by PROVE_TAC [SELECT_def,POSEDGE_IMPL,POSEDGE,POSEDGE_def,AND_def]
    THEN `!tt. tg < tt /\ tt <= (te-1) ==> ~(POSEDGE start_g tt)`
         by RW_TAC arith_ss []
    THEN `!t. t <= te - 1 ==> tg < t ==> done_g t` by IMP_RES_TAC DONE_INTERVAL
    THEN PROVE_TAC []
    ] (* Cases_on `tg=te-1` *)
    , (* end of `!tt. tg < tt /\ tt <= (te-1) ==> done_g tt` *)
    Cases_on `done_g te`
    THENL [
    Cases_on `done_f te`
    THENL [
    Cases_on `done te`
    THENL [
    `HOLDF (t0,te) done` by PROVE_TAC [FINISH_def,HOLDF_def,AND_def,HOLDF_TRANS]
    THEN `te > t0` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `te`
    THEN PROVE_TAC []
    , (* end of Cases_on `done te` *)
    (* done_e te /\ done_g te /\ done_f te /\ ~done te *)
    `?t1. t1 > te /\ HOLDF (te,t1) done /\ done t1`
       by metisLib.METIS_TAC [REC_e_f_g]
    THEN `HOLDF (t0,t1) done` by PROVE_TAC [FINISH_def,HOLDF_def,AND_def,HOLDF_TRANS]
    THEN `t1 > t0` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `t1` THEN PROVE_TAC []
    ] (* Cases_on `done te` *)
    , (* end of Cases_on `done_f te` *)
    (* done_e te /\ done_g te /\  ~done_f te *)
    `~(done te)` by PROVE_TAC [FINISH_def,AND_def]
    THEN `?t1. t1 > te /\ HOLDF (te,t1) done /\ done t1`
         by metisLib.METIS_TAC [REC_e_g]
    THEN `HOLDF (t0,t1) done`
         by PROVE_TAC [FINISH_def,HOLDF_def,AND_def,HOLDF_TRANS]
    THEN `t1 > t0` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `t1` THEN PROVE_TAC []
    ] (* Cases_on `done_f te` *)
    , (* end of Cases_on `done_g te` *)
    `?tg'. tg' >= te /\ HOLDF (te,tg'+1) done_g /\ done_g (tg'+1)`
          by REWRITE_TAC []
    THENL [
    `?ttg'. ttg' > te /\ HOLDF (te,ttg') done_g /\ done_g ttg'`
            by PROVE_TAC [DEV_def,LIV_LEMMA]
    THEN `?tg'. ttg' = tg'+1` by REWRITE_TAC []
    THENL
    [
    Cases_on `ttg'`
    THENL [
    RW_TAC arith_ss []
    , (* end of Cases_on `ttg'` *)
    `SUC n = n+1` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `n`
    THEN PROVE_TAC []
    ] (* Cases_on `ttg'` *)
    , (* end of `?tg'. ttg' = tg'+1` *)
    `HOLDF (te,tg'+1) done_g /\ done_g (tg'+1)` by PROVE_TAC []
    THEN `tg' >= te` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `tg'` THEN PROVE_TAC []
    ]
    , (* end of  `?tg'. tg' >= te /\ HOLDF (te,tg'+1) done_g /\ ... *)
    `done_e tg'` by REWRITE_TAC []
    THENL [
    `!t. done_e t /\ ~POSEDGE start_e (t + 1) ==> done_e (t + 1)`
             by PROVE_TAC [DEV_def,SAFE_DEV_def]
    THEN `!tt. te <= tt /\ tt < (tg'+1) ==> ~(done_g tt)` by PROVE_TAC [HOLDF_def]
    THEN `!tt. te <= tt /\ tt < (tg'+1) ==> ~(POSEDGE done_g tt)`
         by PROVE_TAC [POSEDGE,POSEDGE_def]
    THEN `!tt. te <= tt /\ tt < (tg'+1) ==> ~(POSEDGE start_e tt)`
         by REWRITE_TAC []
    THENL [
    `?c0 c1 start sel.
           POSEDGE_IMP (load,c0) /\ DEL (done,c1) /\ AND (c0,c1,start) /\
           OR (start,sel,start_e) /\ POSEDGE_IMP (done_g,sel) /\
           MUX (sel,data_g,inp,inp_e)` by PROVE_TAC [CALL_def]
    THEN RW_TAC arith_ss []
    THEN Cases_on `te=tg'`
    THENL [
    `tt=te` by RW_TAC arith_ss []
    THEN `~(POSEDGE done_g tg')` by PROVE_TAC [POSEDGE_def]
    THEN `~(sel tg')` by PROVE_TAC [POSEDGE_IMPL,POSEDGE]
    THEN `!tt. tg <= tt /\ tt < te ==> ~(done_e tt)` by PROVE_TAC [HOLDF_def]
    THEN `~(done_e (te-1))` by RW_TAC arith_ss []
    THEN `~(done (te-1))` by PROVE_TAC [FINISH_def,AND_def]
    THEN `te-1+1 = te` by RW_TAC arith_ss []
    THEN `~(c1 te)` by PROVE_TAC [DEL_def]
    THEN `~(start_e te)` by PROVE_TAC [AND_def,OR_def]
    THEN PROVE_TAC [POSEDGE]
    , (* end of Cases_on `te=tg'` *)
    `te < tg'` by RW_TAC arith_ss []
    THEN `tt <= tg'` by RW_TAC arith_ss []
    THEN `!tt. te <= tt /\ tt <= tg' ==> ~(POSEDGE done_g tt)`
         by RW_TAC arith_ss []
    THEN `!tt. te <= tt /\ tt <= tg' ==> ~(sel tt)`
         by PROVE_TAC [POSEDGE_IMPL,POSEDGE,POSEDGE_def]
    THEN `HOLDF (te,tg'+1) done` by PROVE_TAC [HOLDF_def,FINISH_def,AND_def]
    THEN `!tt. (te+1) <= tt /\ tt < (tg'+1+1) ==> ~(c1 tt)`
         by PROVE_TAC [HOLDF_def,HOLDF_DEL]
    THEN `!tt. te < tt /\ tt <= tg' ==> ~(c1 tt)`
         by RW_TAC arith_ss []
    THEN `!tt. tg <= tt /\ tt < te ==> ~(done tt)`
         by PROVE_TAC [HOLDF_def,FINISH_def,AND_def]
    THEN `~(done (te-1))` by RW_TAC arith_ss []
    THEN `te-1+1 = te` by RW_TAC arith_ss []
    THEN `~(c1 te)` by PROVE_TAC [DEL_def]
    THEN `!tt. te <= tt /\ tt <= tg' ==> ~c1 tt`
         by PROVE_TAC [INTERVAL_LEMMA]
    THEN `!tt. te <= tt /\ tt <= tg' ==> ~start_e tt`
         by PROVE_TAC [AND_def,OR_def]
    THEN `!tt. te <= tt /\ tt <= tg' ==> ~POSEDGE start_e tt`
         by PROVE_TAC [POSEDGE_def,POSEDGE]
    THEN RW_TAC arith_ss []
    ] (* Cases_on `te=tg'` *)
    , (* end of `!tt. te <= tt /\ tt < (tg'+1) ==> ~(POSEDGE start_e tt)` *)
    Cases_on `te = tg'`
    THENL [
    RW_TAC arith_ss []
    , (* end of Cases_on `te = tg'` *)
    `te < tg'` by RW_TAC arith_ss []
    THEN `!tt. te < tt /\ tt <= tg' ==> ~POSEDGE start_e tt`
         by RW_TAC arith_ss []
    THEN `tg' <= tg' ==> done_e tg'` by IMP_RES_TAC DONE_INTERVAL
    THEN RW_TAC arith_ss []
    ] (* Cases_on `te = tg'` *)

    ] (* `!tt. te <= tt /\ tt < (tg'+1) ==> ~(POSEDGE start_e tt)` *)
    , (* end of `done_e tg' *)
    `POSEDGE start_e (tg'+1)` by REWRITE_TAC []
    THENL [
    `!tt. te <= tt /\ tt < (tg'+1) ==> ~(done_g tt)` by PROVE_TAC [HOLDF_def]
    THEN `tg'+1-1 = tg'` by RW_TAC arith_ss []
    THEN `~(done_g tg')` by RW_TAC arith_ss []
    THEN Cases_on `te=tg'`
    THENL [
    `HOLDF (tg,te) done` by PROVE_TAC [HOLDF_def,FINISH_def,AND_def]
    THEN `!tt. tg <= tt /\ tt < te ==> ~done tt` by PROVE_TAC [HOLDF_def]
    THEN `~(done (te-1))` by RW_TAC arith_ss []
    THEN `te-1+1= te` by RW_TAC arith_ss []
    THEN `?c0 c1 start sel.
           POSEDGE_IMP (load,c0) /\ DEL (done,c1) /\ AND (c0,c1,start) /\
           OR (start,sel,start_e) /\ POSEDGE_IMP (done_g,sel) /\
           MUX (sel,data_g,inp,inp_e)` by PROVE_TAC [CALL_def]
    THEN `~(c1 te)` by PROVE_TAC [DEL_def]
    THEN `~(start te)` by PROVE_TAC [AND_def]
    THEN `~(POSEDGE done_g te)` by PROVE_TAC [POSEDGE_def]
    THEN `~(sel te)` by PROVE_TAC [POSEDGE_IMPL,POSEDGE]
    THEN `~(start_e te)` by PROVE_TAC [OR_def]
    THEN `POSEDGE done_g (te+1)` by PROVE_TAC [POSEDGE]
    THEN `sel (te+1)` by PROVE_TAC [POSEDGE_IMPL,POSEDGE]
    THEN PROVE_TAC [OR_def,POSEDGE_def,POSEDGE]
    , (* end of Cases_on `te=tg'` *)
    `te < tg'` by RW_TAC arith_ss []
    THEN `~(done_g (tg'-1))` by RW_TAC arith_ss []
    THEN `~(done (tg'-1))` by PROVE_TAC [FINISH_def,AND_def]
    THEN `?c0 c1 start sel.
           POSEDGE_IMP (load,c0) /\ DEL (done,c1) /\ AND (c0,c1,start) /\
           OR (start,sel,start_e) /\ POSEDGE_IMP (done_g,sel) /\
           MUX (sel,data_g,inp,inp_e)` by PROVE_TAC [CALL_def]
    THEN `tg'-1+1=tg'` by RW_TAC arith_ss []
    THEN `~(c1 tg')` by PROVE_TAC [DEL_def]
    THEN `~(sel tg')` by PROVE_TAC [POSEDGE_def,POSEDGE,POSEDGE_IMPL]
    THEN `~(start_e tg')` by PROVE_TAC [AND_def,OR_def]
    THEN `sel (tg'+1)` by PROVE_TAC [POSEDGE_def,POSEDGE,POSEDGE_IMPL]
    THEN PROVE_TAC [OR_def,POSEDGE_def,POSEDGE]
    ] (* Cases_on `te=tg'` *)
    , (* end of `POSEDGE start_e (tg'+1)` *)
    `?variant. !x. ~f1 x ==> variant (f3 x) < variant x`
         by PROVE_TAC [TOTAL_def]
    THEN `tg'+1 > t0` by RW_TAC arith_ss []
    THEN `HOLDF (tg,te) done /\ HOLDF (te,tg'+1) done`
         by PROVE_TAC [FINISH_def,HOLDF_def,AND_def]
    THEN `HOLDF (t0,tg'+1) done` by PROVE_TAC [HOLDF_TRANS]
    THEN PAT_ASSUM ``TOTAL X`` kill
    THEN PAT_ASSUM ``(tg:num) > t0`` kill
    THEN PAT_ASSUM ``HOLDF ((t0:num),tg) done_g`` kill
    THEN PAT_ASSUM ``done_g (tg:num)`` kill
    THEN PAT_ASSUM ``~(done_e (tg:num))``kill
    THEN PAT_ASSUM ``HOLDF ((t0:num),(tg:num)) done`` kill
    THEN PAT_ASSUM ``done_e (te:num)`` kill
    THEN PAT_ASSUM ``(te:num) > (tg:num)`` kill
    THEN PAT_ASSUM ``HOLDF ((tg:num),(te:num)) done_e`` kill
    THEN PAT_ASSUM ``~(done_g (te:num))`` kill
    THEN PAT_ASSUM ``(tg':num) >= (te:num)`` kill
    THEN PAT_ASSUM ``HOLDF ((te:num),(tg':num)+1) done_g`` kill
    THEN PAT_ASSUM ``HOLDF ((tg:num),(te:num)) done`` kill
    THEN PAT_ASSUM ``HOLDF ((te:num),(tg':num)+1) done`` kill
    THEN `?t1. t1 > tg'+1 /\ HOLDF (tg'+1,t1) done /\ done t1`
         by metisLib.METIS_TAC [REC_LIV_LEMMA]
    THEN `HOLDF (t0,t1) done` by PROVE_TAC [HOLDF_TRANS]
    THEN `t1 > t0` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `t1` THEN PROVE_TAC []
    ] (* `POSEDGE start_e (tg'+1)` *)
    ] (* `done_e tg' *)
    ] (* `?tg'. tg' >= te /\ HOLDF (te,tg'+1) done_g /\ ... *)
    ] (* Cases_on `done_g te` *)
    ] (* `!tt. tg < tt /\ tt <= (te-1) ==> done_g tt` *)
    ] (* Cases_on `done_e tg` *)
);


(*****************************************************************************)
(* REC - recursive circuits satisfy DEV                                      *)
(*****************************************************************************)
val REC = Q.store_thm("REC",
    `TOTAL (f1,f2,f3) /\
     REC (DEV f1) (DEV f2) (DEV f3) (load,inp,done,out) ==>
     DEV  (TAILREC f1 f2 f3) (load,inp,done,out)`,
    RW_TAC arith_ss [DEV_def,REC_def,LIV_def]
    THENL [
    REPEAT (Q.PAT_ASSUM `!(t:num). X` kill)
    THEN `REC (SAFE_DEV f1) (SAFE_DEV f2) (SAFE_DEV f3) (load,inp,done,out)`
         by IMP_RES_TAC REC_def
    THEN IMP_RES_TAC SAFE_REC
    , (* end of RW_TAC arith_ss [DEV_def,REC_def,LIV_def] *)
    Cases_on `done_e t`
    THENL [
    Cases_on `done_g t`
    THENL [
    Q.PAT_ASSUM `TOTAL X` kill
    THEN `DEV f1 (start_e,inp_e,done_e,data_e)` by PROVE_TAC [LIV_def,DEV_def]
    THEN `DEV f2 (start_f,q,done_f,out)` by PROVE_TAC [LIV_def,DEV_def]
    THEN `DEV f3 (start_g,q,done_g,data_g)` by PROVE_TAC [LIV_def,DEV_def]
    THEN REPEAT (Q.PAT_ASSUM `SAFE_DEV X Y` kill)
    THEN REPEAT (Q.PAT_ASSUM `!(t:num). X` kill)
    THEN metisLib.METIS_TAC [REC_e_g]
    , (* end of Cases_on `done_g t` *)
    `DEV f1 (start_e,inp_e,done_e,data_e)` by PROVE_TAC [LIV_def,DEV_def]
    THEN `DEV f2 (start_f,q,done_f,out)` by PROVE_TAC [LIV_def,DEV_def]
    THEN `DEV f3 (start_g,q,done_g,data_g)` by PROVE_TAC [LIV_def,DEV_def]
    THEN REPEAT (Q.PAT_ASSUM `SAFE_DEV X Y` kill)
    THEN REPEAT (Q.PAT_ASSUM `!(t:num). X` kill)
    THEN Q.PAT_ASSUM `~(done (t:num))` kill
    THEN Q.PAT_ASSUM `done_e (t:num)` kill
    THEN metisLib.METIS_TAC [REC_NOTg]
    ] (* Cases_on `done_g t` *)

    , (* end of Cases_on `done_e t` *)
    `LIV (start_e,inp_e,done_e,data_e)` by PROVE_TAC [LIV_def]
    THEN `?te. te > t /\ HOLDF (t,te) done_e /\ done_e te`
         by PROVE_TAC [LIV_LEMMA]
    THEN Cases_on `done_g te`
    THENL [
    Cases_on `done_f te`
    THENL [
    Cases_on `done te`
    THENL [
    Q.EXISTS_TAC `te`
    THEN PROVE_TAC []
    , (* end of Cases_on `done te` *)
    `DEV f1 (start_e,inp_e,done_e,data_e)` by PROVE_TAC [LIV_def,DEV_def]
    THEN `DEV f2 (start_f,q,done_f,out)` by PROVE_TAC [LIV_def,DEV_def]
    THEN `DEV f3 (start_g,q,done_g,data_g)` by PROVE_TAC [LIV_def,DEV_def]
    THEN REPEAT (Q.PAT_ASSUM `SAFE_DEV X Y` kill)
    THEN REPEAT (Q.PAT_ASSUM `!(t:num). X` kill)
    THEN Q.PAT_ASSUM `TOTAL X` kill
    THEN Q.PAT_ASSUM `LIV X` kill
    THEN `?t1. t1 > te /\ HOLDF (te,t1) done /\ done t1`
         by metisLib.METIS_TAC [REC_e_f_g]
    THEN `t1 > t` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `t1` THEN PROVE_TAC []
    ] (* Cases_on `done te` *)
    , (* end of Cases_on `done_f te` *)
    `~(done te)` by PROVE_TAC [FINISH_def,AND_def]
    THEN `DEV f1 (start_e,inp_e,done_e,data_e)` by PROVE_TAC [LIV_def,DEV_def]
    THEN `DEV f2 (start_f,q,done_f,out)` by PROVE_TAC [LIV_def,DEV_def]
    THEN `DEV f3 (start_g,q,done_g,data_g)` by PROVE_TAC [LIV_def,DEV_def]
    THEN REPEAT (Q.PAT_ASSUM `SAFE_DEV X Y` kill)
    THEN REPEAT (Q.PAT_ASSUM `!(t:num). X` kill)
    THEN Q.PAT_ASSUM `TOTAL X` kill
    THEN Q.PAT_ASSUM `LIV X` kill
    THEN `?t1. t1 > te /\ HOLDF (te,t1) done /\ done t1`
         by metisLib.METIS_TAC [REC_e_NOTf_g]
    THEN `t1 > t` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `t1` THEN PROVE_TAC []
    ] (* Cases_on `done_f te` *)
    , (* end of Cases_on `done_g te` *)
    `DEV f1 (start_e,inp_e,done_e,data_e)` by PROVE_TAC [LIV_def,DEV_def]
    THEN `DEV f2 (start_f,q,done_f,out)` by PROVE_TAC [LIV_def,DEV_def]
    THEN `DEV f3 (start_g,q,done_g,data_g)` by PROVE_TAC [LIV_def,DEV_def]
    THEN REPEAT (Q.PAT_ASSUM `SAFE_DEV X Y` kill)
    THEN REPEAT (Q.PAT_ASSUM `!(t:num). X` kill)
    THEN Q.PAT_ASSUM `LIV X` kill
    THEN Q.PAT_ASSUM `~(done (t:num))` kill
    THEN Q.PAT_ASSUM `~(done_e (t:num))` kill
    THEN Q.PAT_ASSUM `HOLDF (t:num,te:num) done_e` kill
    THEN `?t1. t1 > te /\ HOLDF (te,t1) done /\ done t1`
          by metisLib.METIS_TAC [REC_NOTg]
    THEN `t1 > t` by RW_TAC arith_ss []
    THEN Q.EXISTS_TAC `t1` THEN PROVE_TAC []
    ] (* Cases_on `done_g te` *)
    ] (* Cases_on `done_e t` *)
    ] (* RW_TAC arith_ss [DEV_def,REC_def,LIV_def] *)
);



val _ = export_theory();
