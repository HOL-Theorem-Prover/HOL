(* ========================================================================= *)
(* FILE          : coprocessorScript.sml                                     *)
(* DESCRIPTION   : A collection of lemmas used to verify the coprocessor     *)
(*                 instructions                                              *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005                                                      *)
(* ========================================================================= *)

(* interactive use:
  app load ["pred_setSimps", "wordsLib", "armLib",
            "my_listTheory", "io_onestepTheory", "iclass_compLib",
            "armTheory", "coreTheory", "lemmasTheory"];
*)

open HolKernel boolLib bossLib;
open Q arithmeticTheory rich_listTheory wordsTheory;
open my_listTheory io_onestepTheory iclass_compLib armLib;
open armTheory coreTheory lemmasTheory;

val _ = new_theory "coprocessor";

(* ------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val Abbr = BasicProvers.Abbr;
fun Abbrev_wrap eqth =
    EQ_MP (SYM (Thm.SPEC (concl eqth) markerTheory.Abbrev_def)) eqth;

val FST_COND_RAND = ISPEC `FST` COND_RAND;
val SND_COND_RAND = ISPEC `SND` COND_RAND;

val std_ss = bossLib.std_ss ++ boolSimps.LET_ss ++
             rewrites [FST_COND_RAND,SND_COND_RAND];

val arith_ss = bossLib.arith_ss ++ boolSimps.LET_ss;

val SIZES_ss = wordsLib.SIZES_ss;

(* ------------------------------------------------------------------------- *)

val BUSY_WAIT_LEM = prove(
  `!t i. t < BUSY_WAIT (onfq,ooonfq,oniq,oooniq,cpsrf,cpsri,pipebabt) i /\
        ~IS_RESET i t ==>
     ?NFQ NIQ ABORT DATA. (i t = (T,ABORT,NFQ,NIQ,DATA,F,T)) /\ ~pipebabt /\
         ((t = 0) ==> (PROJ_DATA (i 0) = DATA) /\
              (cpsrf \/ ooonfq) /\
              (cpsri \/ oooniq)) /\
         ((t = 1) ==> (cpsrf \/ onfq) /\ (cpsri \/ oniq)) /\
          (1 < t ==>  (cpsrf \/ PROJ_NFIQ (i (t - 2))) /\
                      (cpsri \/ PROJ_NIRQ (i (t - 2))))`,
  NTAC 2 STRIP_TAC
    \\ REWRITE_TAC [BUSY_WAIT_def,BUSY_WAIT_DONE_def,CP_INTERRUPT_def]
    \\ STRIP_TAC \\ IMP_RES_TAC whileTheory.LESS_LEAST \\ POP_ASSUM MP_TAC
    \\ PAT_ASSUM `~IS_RESET i t` MP_TAC
    \\ SIMP_TAC std_ss [IS_RESET_def,IS_BUSY_def,IS_ABSENT_def,IS_ABORT_def,
         IS_IRQ_def,IS_FIQ_def]
    \\ Cases_on `(t = 0)`
    \\ Cases_on `(t = 1)`
    \\ FULL_SIMP_TAC std_ss []
    << [Cases_on_arm6inp `i 0`, Cases_on_arm6inp `i 1`,
        Cases_on_arm6inp `i (t:num)`]
    \\ ASM_SIMP_TAC arith_ss [PROJ_NRESET_def,PROJ_DATA_def,PROJ_CPB_def,
         PROJ_CPA_def,PROJ_ABORT_def,PROJ_NFIQ_def,PROJ_NIRQ_def]);

val arm6state_inp = ``<|state := ARM6 (DP reg psr areg din alua alub dout)
   (CTRL pipea pipeaval pipeb pipebval ireg iregval ointstart onewinst endinst
      obaselatch opipebll nxtic nxtis nopc1 oorst resetlatch onfq ooonfq
      oniq oooniq pipeaabt pipebabt iregabt2 dataabt2 aregn2 mrq2 nbw nrw
      sctrlreg psrfb oareg mask orp oorp mul mul2 borrow2 mshift);
    inp := (inp : num -> bool # bool # bool # bool # word32 # bool # bool)|>``;

val COPROC_BUSY_WAIT = store_thm("COPROC_BUSY_WAIT",
  `!t x. Abbrev (x = (^arm6state_inp)) /\
   DECODE_INST ireg IN {cdp_und; mrc; mcr; stc; ldc} /\
   (aregn2 = 2w) /\
   CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg /\
   Abbrev (i = (CPSR_READ psr) %% 7) /\
   Abbrev (f = (CPSR_READ psr) %% 6) /\
   Abbrev (b = BUSY_WAIT (onfq,ooonfq,oniq,oooniq,f,i,pipebabt) inp) /\
   Abbrev (w = 1 + b) /\
   Abbrev (x0 = SINIT INIT_ARM6 x) /\
   (!t. t < w ==> ~IS_RESET inp t) ==> (t < w ==>
   ?alua' alub' dout' obaselatch' nbw' nrw' psrfb' oareg' mask' orp' oorp'
    mul' mul2' borrow2' mshift'.
   ((FUNPOW (SNEXT NEXT_ARM6) t x0) = <| state := ARM6
      (DP reg psr (REG_READ6 reg usr 15w) ireg alua' alub' dout')
      (CTRL (if t = 0 then pipea else PROJ_DATA (inp 0)) T pipeb T ireg T
         F (t = 0) (t = 0) obaselatch' (t = 0) (DECODE_INST ireg) t3
         (~(t = 0) /\ DECODE_INST ireg IN {stc; ldc} /\ ~IS_BUSY inp (t - 1))
         F F (if t = 0 then onfq else PROJ_NFIQ (inp (t - 1)))
         (if t = 0 then ooonfq else
            if t = 1 then onfq else PROJ_NFIQ (inp (t - 2)))
         (if t = 0 then oniq else PROJ_NIRQ (inp (t - 1)))
         (if t = 0 then oooniq else
            if t = 1 then oniq else PROJ_NIRQ (inp (t - 2)))
         (if t = 0 then pipeaabt else PROJ_ABORT (inp 0)) ((t = 0) /\ pipebabt)
         (( t = 0) /\ iregabt2) ((t = 0) /\ dataabt2)
         2w ((t = 0) /\ mrq2) nbw' nrw' sctrlreg psrfb' oareg'
         mask' orp' oorp' mul' mul2' borrow2' mshift');
       inp := ADVANCE t inp |>))`,
  NTAC 3 STRIP_TAC \\ UNABBREV_TAC `b`
    \\ ASM_SIMP_TAC (std_ss++STATE_INP_ss) [Abbr`x`,Abbr`x0`,Abbr`w`,
         IS_BUSY_def,SINIT_def,INIT_ARM6_def,num2exception_exception2num,
         IC_def,ABORTINST_def,NXTIC_def,DECODE_PSR_def]
    \\ STRIP_TAC \\ Induct_on `t`
    >> RW_TAC std_ss [FUNPOW,ADVANCE_ZERO]
    \\ STRIP_TAC
    \\ POP_ASSUM (fn th =>
         `t < 1 + BUSY_WAIT (onfq,ooonfq,oniq,oooniq,f,i,pipebabt) inp /\
          t < BUSY_WAIT (onfq,ooonfq,oniq,oooniq,f,i,pipebabt) inp`
      by SIMP_TAC arith_ss [th])
    \\ PAT_ASSUM `!x. a ==> b` IMP_RES_TAC
    \\ PAT_ASSUM `a ==> b` IMP_RES_TAC
    \\ SIMP_TAC arith_ss []
    \\ ASM_SIMP_TAC (std_ss++STATE_INP_ss) [FUNPOW_SUC]
    \\ POP_ASSUM (K ALL_TAC)
    \\ ASM_SIMP_TAC (arith_ss++STATE_INP_ss)
         [SNEXT_def,ADD1,GSYM io_onestepTheory.ADVANCE_COMP,ADVANCE_def]
    \\ IMP_RES_TAC BUSY_WAIT_LEM \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
    \\ FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++ICLASS_ss) []
    \\ ASM_SIMP_TAC (std_ss++CDP_UND_ss++MRC_ss++MCR_ss++LDC_ss++STC_ss) []
    \\ ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss++PBETA_ss)
         [PROJ_NFIQ_def,PROJ_NIRQ_def,PROJ_CPB_def]
    \\ Cases_on `t = 0` >> RW_TAC arith_ss [AREGN1_def,PROJ_ABORT_def]
    \\ Cases_on `t = 1` \\ FULL_SIMP_TAC arith_ss
         [AREGN1_def,PROJ_ABORT_def,state_arm6_11,dp_11,ctrl_11]);

local
  val nc = armLib.tupleCases
       ``(onfq,ooonfq,oniq,oooniq,cpsrf,cpsri,pipebabt) :
          bool # bool # bool # bool # bool # bool # bool``
in
  fun Cases_on_x tm = FULL_STRUCT_CASES_TAC (SPEC tm nc)
end;

val EXISTS_BUSY_WAIT = prove(
  `!x i. i IN STRM_ARM6 ==> ?t. BUSY_WAIT_DONE x i t`,
  STRIP_TAC \\ Cases_on_x `x`
    \\ RW_TAC std_ss [IN_DEF,STRM_ARM6_def,BUSY_WAIT_DONE_def,CP_INTERRUPT_def]
    \\ METIS_TAC []);

val LEAST_BETA = prove(`!n P. (LEAST n. P n) = $LEAST P`,
  METIS_TAC [whileTheory.LEAST_DEF]);

val EXISTS_BUSY_WAIT_IMP_BUSY_WAIT_DONE = save_thm
  ("EXISTS_BUSY_WAIT_IMP_BUSY_WAIT_DONE",
   (SIMP_RULE std_ss [GSYM BUSY_WAIT_def,EXISTS_BUSY_WAIT,
      (GSYM o SPECL [`n`,`BUSY_WAIT_DONE x i`]) LEAST_BETA] o
    DISCH `i IN STRM_ARM6` o DISCH `Abbrev (t = $LEAST (BUSY_WAIT_DONE x i))` o
    SIMP_RULE std_ss [DECIDE ``a /\ b ==> b``] o
    SPECL [`BUSY_WAIT_DONE x i`,`BUSY_WAIT_DONE x i`]) whileTheory.LEAST_ELIM);

val BUSY_WAIT_COR = prove(
  `!i t. i IN STRM_ARM6 /\
     BUSY_WAIT_DONE (onfq,ooonfq,oniq,oooniq,cpsrf,cpsri,pipebabt) i t /\
     ~IS_RESET i t ==>
  ?ABORT NFQ NIQ DATA CPA CPB. (i t = (T,ABORT,NFQ,NIQ,DATA,CPA,CPB)) /\
   ((CPA ==> CPB) /\
    (CPB ==> CP_INTERRUPT (onfq,ooonfq,oniq,oooniq,cpsrf,cpsri,pipebabt) i t))`,
  NTAC 2 STRIP_TAC
    \\ SIMP_TAC std_ss [STRM_ARM6_def,BUSY_WAIT_DONE_def,IN_DEF,IS_RESET_def,
         IS_ABSENT_def,IS_BUSY_def,IS_ABORT_def]
    \\ STRIP_TAC \\ PAT_ASSUM `!t. PROJ_CPA (i t) ==> PROJ_CPB (i t)`
         (SPEC_THEN `t` ASSUME_TAC)
    \\ Cases_on `t = 0` \\ FULL_SIMP_TAC std_ss []
    << [Cases_on_arm6inp `i 0`,  Cases_on_arm6inp `i (t:num)`]
    \\ FULL_SIMP_TAC arith_ss [PROJ_NRESET_def,PROJ_DATA_def,PROJ_CPB_def,
         PROJ_CPA_def,PROJ_ABORT_def]);

val EXISTS_AREGN = SIMP_RULE (std_ss++pred_setSimps.PRED_SET_ss) []
  (prove(`?aregn:word3. ~(aregn IN {0w; 2w; 5w; 6w; 7w})`,
    EXISTS_TAC `1w`
      \\ SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++SIZES_ss) [n2w_11]));

val FINISH_OFF3 =
   Cases_on `CPB` \\ ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) []
     \\ RW_TAC (std_ss++SIZES_ss) [Abbr`ointstart'`,n2w_11]
     \\ NTAC 2 (FULL_SIMP_TAC std_ss []) \\ POP_ASSUM_LIST (K ALL_TAC)
     \\ PROVE_TAC [EXISTS_AREGN];

val COPROC_BUSY_WAIT2 = prove(
  `!t x. Abbrev (x = (^arm6state_inp)) /\ inp IN STRM_ARM6 /\
   DECODE_INST ireg IN {cdp_und; mrc; mcr; stc; ldc} /\
   (aregn2 = 2w) /\
   CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg /\
   Abbrev (i = (CPSR_READ psr) %% 7) /\
   Abbrev (f = (CPSR_READ psr) %% 6) /\
   Abbrev (nbs = DECODE_MODE ((4 >< 0) (CPSR_READ psr))) /\
   Abbrev (b = BUSY_WAIT (onfq,ooonfq,oniq,oooniq,f,i,pipebabt) inp) /\
   Abbrev (w = 1 + b) /\
   Abbrev (x0 = SINIT INIT_ARM6 x) /\
   (!t. t < w ==> ~IS_RESET inp t) ==>
   ?alua' alub' dout' newinst obaselatch' pipeaabt' pipebabt' iregabt' dataabt'
    aregn' mrq' nbw' nrw' psrfb' oareg' mask' orp' oorp'  mul' mul2' borrow2'
    mshift'.
    ~(aregn' IN {0w; 2w; 5w}) /\
    ((aregn' = 7w) ==> ~f) /\ ((aregn' = 6w) ==> ~i) /\
   (let ic = DECODE_INST ireg
    and CPB = PROJ_CPB (inp b)
    and ointstart' = CP_INTERRUPT (onfq,ooonfq,oniq,oooniq,f,i,pipebabt) inp b
    in
    let Rn = (19 >< 16) ireg
    and offset = ((7 -- 0) ireg) << 2
    and newinst = (ic = cdp_und) \/ CPB /\ ointstart' in
    let nxtic = if newinst then
         if ointstart' then swi_ex else DECODE_INST pipeb else ic in
      FUNPOW (SNEXT NEXT_ARM6) w x0  =
       <| state := ARM6 (DP (if CPB then reg else INC_PC reg) psr
                (if CPB then REG_READ6 reg usr 15w
                 else if ic IN {stc; ldc} then
                   (if ~(ireg %% 24) then $K else if ireg %% 23 then $+ else $-)
                      (REG_READ6 reg nbs Rn) offset
                 else REG_READ6 reg usr 15w + 4w)
                (if newinst then pipeb else ireg)
                (if ic IN {stc; ldc} then REG_READ6 reg nbs Rn else alua')
                (if ic IN {stc; ldc} then offset else alub') dout')
           (CTRL (PROJ_DATA (inp 0)) T
             (if newinst then PROJ_DATA (inp 0) else pipeb) T
             (if newinst then pipeb else ireg) T
             ointstart' newinst newinst obaselatch' newinst nxtic
             (if newinst then t3 else
                if (ic = mrc) \/ (ic = mcr) then t4 else tn)
             (ic IN {stc; ldc} /\ ~CPB) F F (PROJ_NFIQ (inp b))
             (if w = 1 then onfq else PROJ_NFIQ (inp (b - 1)))
             (PROJ_NIRQ (inp b))
             (if w = 1 then oniq else PROJ_NIRQ (inp (b - 1)))
             pipeaabt' (if newinst then pipebabt' else pipebabt)
             (if newinst then iregabt' else pipebabt) (newinst /\ dataabt')
             (if ointstart' then aregn' else 2w) mrq' nbw' (~newinst /\ nrw')
             sctrlreg psrfb' oareg'
             (if newinst then MASK nxtic t3 mask' ARB else mask')
             orp' oorp' mul' mul2' borrow2' mshift'); inp := ADVANCE w inp |>)`,
  REPEAT STRIP_TAC
    \\ RULE_ASSUM_TAC (SIMP_RULE std_ss [DECODE_PSR_def])
    \\ `?t. t < w /\ (w = SUC t)` by SIMP_TAC arith_ss [Abbr`w`,ADD1]
    \\ `b = t` by (UNABBREV_TAC `w` \\ DECIDE_TAC)
    \\ POP_ASSUM SUBST_ALL_TAC \\ POP_ASSUM SUBST1_TAC
    \\ RES_MP_TAC [`b:num` |-> `t:num`] COPROC_BUSY_WAIT
    \\ POP_ASSUM IMP_RES_TAC
    \\ ASM_SIMP_TAC (arith_ss++STATE_INP_ss) [FUNPOW_SUC]
    \\ POP_ASSUM (K ALL_TAC)
    \\ markerLib.RM_ABBREV_TAC "w"
    \\ ABBREV_TAC `ointstart' =
         CP_INTERRUPT (onfq,ooonfq,oniq,oooniq,f,i,pipebabt) inp t`
    \\ IMP_RES_TAC EXISTS_BUSY_WAIT_IMP_BUSY_WAIT_DONE
    \\ RES_TAC \\ IMP_RES_TAC BUSY_WAIT_COR \\ NTAC 9 (POP_ASSUM (K ALL_TAC ))
    \\ `CPB ==> ointstart'` by ASM_SIMP_TAC std_ss [Abbr `ointstart'`]
    \\ `(PROJ_CPB (inp t) = CPB) /\ (PROJ_CPA (inp t) = CPA)`
    by ASM_SIMP_TAC std_ss [PROJ_CPB_def,PROJ_CPA_def]
    \\ `~(t = 0) ==> ~pipebabt`
    by (STRIP_TAC \\
        `0 < BUSY_WAIT (onfq,ooonfq,oniq,oooniq,f,i,pipebabt) inp /\
         ~IS_RESET inp 0` by ASM_SIMP_TAC arith_ss [] \\
        METIS_TAC [BUSY_WAIT_LEM])
    \\ `(t = 0) ==> (DATA = PROJ_DATA (inp 0))`
    by (STRIP_TAC \\ FULL_SIMP_TAC std_ss [PROJ_DATA_def])
    \\ ASM_SIMP_TAC (arith_ss++STATE_INP_ss) [SNEXT_def,ADD1,
         GSYM io_onestepTheory.ADVANCE_COMP,ADVANCE_def,PROJ_CPB_def,
         PROJ_NFIQ_def,PROJ_NIRQ_def]
    \\ FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++ICLASS_ss)
         [PROJ_NRESET_def,IS_FIQ_def,IS_IRQ_def]
    \\ ASM_SIMP_TAC (std_ss++CDP_UND_ss++MRC_ss++MCR_ss++LDC_ss++STC_ss) []
    \\ ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss++PBETA_ss) []
    \\ PAT_ABBREV_TAC `ointstart2 = CPA \/ q`
    \\ `ointstart2 = ointstart'`
    by (ASM_SIMP_TAC std_ss [Abbr `ointstart2`,Abbr `ointstart'`,
          CP_INTERRUPT_def,IS_FIQ_def,IS_IRQ_def,IS_ABSENT_def,PROJ_CPA_def]
            \\ Cases_on `t = 0` >> (FULL_SIMP_TAC std_ss [] \\
                 POP_ASSUM_LIST (K ALL_TAC) \\ PROVE_TAC [])
            \\ Cases_on `t = 1` \\ FULL_SIMP_TAC arith_ss [])
    \\ POP_ASSUM SUBST1_TAC \\ POP_ASSUM (K ALL_TAC)
    \\ ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss) [IF_NEG,TO_WRITE_READ6]
    \\ FULL_SIMP_TAC (std_ss++ALU_ss) [state_arm6_11,ctrl_11,dp_11,LSL_ZERO,
         LSL_TWO,ALUOUT_ALU_logic,ALUOUT_ADD,ALUOUT_SUB,AREGN1_def]
    \\ (Cases_on `CPA` \\ FULL_SIMP_TAC std_ss
         [CP_INTERRUPT_def,IS_ABSENT_def,IS_FIQ_def,IS_IRQ_def]
    >> (SIMP_TAC (std_ss++boolSimps.LIFT_COND_ss++SIZES_ss) [n2w_11] \\
          POP_ASSUM_LIST (K ALL_TAC) \\ METIS_TAC [])
    \\ Cases_on `t = 0` >> FINISH_OFF3
    \\ Cases_on `t = 1` \\ FINISH_OFF3));

val COPROC_BUSY_WAIT2 = save_thm("COPROC_BUSY_WAIT2",
  (PairRules.PBETA_RULE o REWRITE_RULE [LET_THM]) COPROC_BUSY_WAIT2);

(* ------------------------------------------------------------------------- *)

val lem = prove(
  `!P b:num c. (!a. a < b ==> P a) /\ c <= b ==> (!a. a < c ==> P a)`,
  RW_TAC arith_ss []);

val lem2 = prove(
  `!ic. ic IN {stc; ldc} ==>
         (ic IN {cdp_und; mrc; mcr; stc; ldc} /\
          ~(ic = cdp_und) /\ ~(ic = mrc) /\ ~(ic = mcr))`,
  RW_TAC (std_ss++pred_setSimps.PRED_SET_ss) []);

val BUSY_EXISTS = store_thm("BUSY_EXISTS",
  `!inp b. inp IN STRM_ARM6 /\
       Abbrev (b = BUSY_WAIT (onfq,ooonfq,oniq,oooniq,f,i,pipebabt) inp) /\
       ~IS_BUSY inp b ==> ?n. IS_BUSY (ADVANCE b inp) n`,
  RW_TAC arith_ss [IN_DEF,STRM_ARM6_def,ADVANCE_def,IS_BUSY_def]
    \\ METIS_TAC [ADD_COMM,LESS_ADD]);

val BUSY_EXISTS_COR =
  let val x = (SIMP_RULE std_ss [] o
     DISCH `inp IN STRM_ARM6 /\
       Abbrev (b = BUSY_WAIT (onfq,ooonfq,oniq,oooniq,f,i,pipebabt) inp) /\
       ~IS_BUSY inp b` o
     SPEC `\n. IS_BUSY (ADVANCE b inp) n`) whileTheory.LEAST_EXISTS
  in
    (GEN_ALL o SIMP_RULE std_ss [IS_BUSY_def,ADVANCE_def])
      (MATCH_MP (METIS_PROVE [] ``(a ==> b) /\ (a ==> (b = c)) ==> (a ==> c)``)
                (CONJ (SPECL [`inp`,`b`] BUSY_EXISTS) x))
  end;

val CP_TRANSFER_LEM = prove(
  `!p w' w b inp.
         inp IN STRM_ARM6 /\
         Abbrev (b = BUSY_WAIT (onfq,ooonfq,oniq,oooniq,f,i,pipebabt) inp) /\
         ~PROJ_CPB (inp b) /\
         Abbrev (w = w' + (LEAST n. IS_BUSY (ADVANCE b inp) n)) /\
         Abbrev (w' = 1 + b) /\
         (SUC p + w' <= w) /\ (!t. t < w ==> ~IS_RESET inp t) ==>
     ?ABORT NFQ NIQ DATA CPA.
        (inp (p + w') =
           (T,ABORT,NFQ,NIQ,DATA,CPA /\ (SUC p + w' = w),SUC p + w' = w))`,
  REPEAT STRIP_TAC \\ MAP_EVERY UNABBREV_TAC [`w`,`w'`]
    \\ FULL_SIMP_TAC arith_ss []
    \\ `b + (p + 1) < b + ((LEAST n. IS_BUSY (ADVANCE b inp) n) + 1)`
    by DECIDE_TAC
    \\ RES_TAC
    \\ FULL_SIMP_TAC arith_ss [IS_RESET_def,IS_BUSY_def,ADVANCE_def]
    \\ `PROJ_CPB (inp (b + LEAST n. PROJ_CPB (inp (b + n)))) /\
        !n.  n < (LEAST n. PROJ_CPB (inp (b + n))) ==> ~PROJ_CPB (inp (b + n))`
    by (NTAC 4 (POP_ASSUM (K ALL_TAC)) \\ IMP_RES_TAC BUSY_EXISTS_COR \\
          ASM_SIMP_TAC std_ss [])
    \\ ABBREV_TAC `l = LEAST n. PROJ_CPB (inp (b + n))`
    \\ Cases_on `p + 1 < l`
    << [
      RES_TAC \\ `~PROJ_CPA (inp (b + (p + 1)))`
         by (FULL_SIMP_TAC std_ss [IN_DEF,STRM_ARM6_def,
               IS_ABSENT_def,IS_BUSY_def] \\ METIS_TAC []),
        `p + 1 = l` by DECIDE_TAC \\ POP_ASSUM (SUBST_ALL_TAC o SYM)]
    \\ Cases_on_arm6inp `inp (b + (p + 1))`
    \\ FULL_SIMP_TAC arith_ss [PROJ_NRESET_def,PROJ_CPB_def,PROJ_CPA_def]);

val CP_TRANSFER_LEM0 = (SIMP_RULE arith_ss [] o SPEC `0`) CP_TRANSFER_LEM;

val finish_rws =
  [REG_WRITE_WRITE,REG_WRITE_WRITE_PC,REG_READ_WRITE,ADD4_ADD4,
   GSYM WORD_ADD_SUB_SYM,WORD_ADD_SUB,REWRITE_RULE [word_0] WORD_ADD_0];

val FINISH_OFF3 = let val
  rw_tac = RW_TAC arith_ss ([Abbr`wb_addr`,Abbr`Rn`,GSYM WORD_ADD_SUB_ASSOC,
             AC WORD_ADD_ASSOC WORD_ADD_COMM] @ finish_rws)
 in
   REPEAT CONJ_TAC << [
     rw_tac, rw_tac,
     RW_TAC arith_ss [] \\ POP_ASSUM_LIST (K ALL_TAC) \\ PROVE_TAC [],
     RW_TAC (arith_ss++SIZES_ss) [AREGN1_def,n2w_11]
       \\ FULL_SIMP_TAC (std_ss++SIZES_ss) [n2w_11]
       \\ POP_ASSUM_LIST (K ALL_TAC) \\ METIS_TAC [EXISTS_AREGN],
     POP_ASSUM_LIST (K ALL_TAC) \\ METIS_TAC []]
 end;

val LDC_STC_THM = store_thm("LDC_STC_THM",
  `!t x. Abbrev (x = (^arm6state_inp)) /\ inp IN STRM_ARM6 /\
   DECODE_INST ireg IN {stc; ldc} /\
   (aregn2 = 2w) /\
   CONDITION_PASSED (NZCV (CPSR_READ psr)) ireg /\
   Abbrev (i = (CPSR_READ psr) %% 7) /\
   Abbrev (f = (CPSR_READ psr) %% 6) /\
   Abbrev (nbs = DECODE_MODE ((4 >< 0) (CPSR_READ psr))) /\
   Abbrev (b = BUSY_WAIT (onfq,ooonfq,oniq,oooniq,f,i,pipebabt) inp) /\
   Abbrev (w = 1 + b + (LEAST n. IS_BUSY (ADVANCE b inp) n)) /\
   Abbrev (x0 = SINIT INIT_ARM6 x) /\
   (!t. t < w ==> ~IS_RESET inp t) /\
   ~IS_BUSY inp b ==>
   let CPB = PROJ_CPB (inp (w - 1)) in
   let Rn = (19 >< 16) ireg
   and offset = (7 -- 0) ireg << 2 in
   let wb_addr = (if ireg %% 23 then $+ else $-) (REG_READ6 reg nbs Rn) offset
   in
     (1 + b < t /\ t <= w ==>
        ?alua' alub' dout' newinst ointstart' obaselatch' onfq' ooonfq'
         oniq' oooniq' pipeaabt' pipebabt' iregabt' dataabt' aregn' mrq' nbw'
         nrw' psrfb' oareg' mask' orp' oorp'  mul' mul2' borrow2' mshift'.
      ~(aregn' IN {0w; 2w; 5w}) /\
      ((aregn' = 7w) ==> ~f) /\ ((aregn' = 6w) ==> ~i) /\
      (let nxtic1 = if ointstart' then swi_ex else DECODE_INST pipeb in
       FUNPOW (SNEXT NEXT_ARM6) t x0 =
       <| state := ARM6
         (DP (if ireg %% 21 /\ ~(Rn = 15w) then
                REG_WRITE (INC_PC reg) nbs Rn wb_addr
              else INC_PC reg) psr
            (if t = w then REG_READ6 (INC_PC reg) nbs 15w else
               (if ~(ireg %% 24) then $K else if ireg %% 23 then $+ else $-)
                  (REG_READ6 reg nbs Rn + n2w (4 * (t - (b + 1)))) offset)
            (if t = w then pipeb else ireg) (REG_READ6 reg nbs Rn) offset dout')
         (CTRL (PROJ_DATA (inp 0)) T
            (if t = w then PROJ_DATA (inp 0) else pipeb) T
            (if t = w then pipeb else ireg) T ointstart' (t = w) (t = w)
            obaselatch' (t = w) (if (t = w) then nxtic1 else DECODE_INST ireg)
            (if (t = w) then t3 else tn) (~(t = w)) F F onfq' ooonfq'
            oniq' oooniq' pipeaabt' pipebabt'
            (if t = w then iregabt' else pipebabt') dataabt'
            (if ointstart' then aregn' else 2w)
            mrq' nbw' (~(t = w) /\ (DECODE_INST ireg = stc)) sctrlreg psrfb'
            oareg' (if t = w then MASK nxtic1 t3 mask' ARB else mask')
            orp' oorp' mul' mul2' borrow2' mshift'); inp := ADVANCE t inp |>))`,
  REWRITE_TAC [DECODE_PSR_def] \\ REPEAT STRIP_TAC
    \\ BasicProvers.LET_ELIM_TAC \\ SIMP_TAC std_ss [markerTheory.Abbrev_def]
    \\ IMP_RES_TAC LESS_ADD
    \\ `?w'. w' = 1 + b` by METIS_TAC []
    \\ `w' <= w` by DECIDE_TAC
    \\ `!t. t < w' ==> ~IS_RESET inp t`
    by METIS_TAC [(BETA_RULE o SPEC `\t. ~IS_RESET inp t`) lem]
    \\ `~PROJ_CPB (inp (w' - 1))`
    by METIS_TAC [IS_BUSY_def,DECIDE ``!x. 1 + x - 1 = x``]
    \\ `Abbrev (w' = 1 + b)`
    by ASM_SIMP_TAC std_ss [Abbr`w`,markerTheory.Abbrev_def]
    \\ IMP_RES_TAC lem2
    \\ RES_MP_TAC [`w:num` |-> `w':num`] COPROC_BUSY_WAIT2
    \\ PAT_ASSUM `p + (1 + d) = t` (SUBST_ALL_TAC o SYM)
    \\ ONCE_REWRITE_TAC [onestepTheory.FUNPOW_COMP]
    \\ markerLib.RM_ABBREV_TAC "w'"
    \\ PAT_ASSUM `w' = 1 + d`
         (fn th => (SUBST_ALL_TAC o SYM) th \\ (ASSUME_TAC o Abbrev_wrap) th)
    \\ PAT_ASSUM `FUNPOW (SNEXT NEXT_ARM6) w' x = q` SUBST1_TAC
    \\ ASM_SIMP_TAC std_ss []
    \\ Induct_on `p` >> FULL_SIMP_TAC arith_ss []
    \\ REPEAT STRIP_TAC
    \\ Cases_on `p = 0`
    << [
      FULL_SIMP_TAC (arith_ss++STATE_INP_ss) [numeralTheory.numeral_funpow,
             SNEXT_def,GSYM io_onestepTheory.ADVANCE_COMP,ADVANCE_def]
        \\ `(w' - 1 = b)` by ASM_SIMP_TAC arith_ss [Abbr`w'`]
        \\ POP_ASSUM SUBST_ALL_TAC
        \\ `0 < (LEAST n. PROJ_CPB (inp (b + n)))`
        by FULL_SIMP_TAC arith_ss [Abbr`w`,IS_BUSY_def,ADVANCE_def]
        \\ IMP_RES_TAC BUSY_EXISTS_COR \\ NTAC 3 (POP_ASSUM (K ALL_TAC))
        \\ RES_MP_TAC [] CP_TRANSFER_LEM0
        \\ FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++ICLASS_ss) []
        \\ ASM_SIMP_TAC (std_ss++LDC_ss++STC_ss) []
        \\ ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss++PBETA_ss++ALU_ss)
             [IF_NEG,TO_WRITE_READ6,LSL_ZERO,LSL_TWO,ALUOUT_ALU_logic,
              ALUOUT_ADD,ALUOUT_SUB,METIS_PROVE [] ``a /\ b \/ a = a``]
        \\ FULL_SIMP_TAC arith_ss [state_arm6_11,dp_11,ctrl_11,iseq_distinct]
        \\ CONV_TAC (DEPTH_CONV EXISTS_AND_REORDER_CONV)
        \\ FINISH_OFF3,
      `w' < p + w' /\ p + w' <= w` by DECIDE_TAC
        \\ PAT_ASSUM `q ==> r ==> s` IMP_RES_TAC
        \\ ASM_SIMP_TAC (std_ss++STATE_INP_ss) [FUNPOW_SUC]
        \\ POP_ASSUM (K ALL_TAC)
        \\ ASM_SIMP_TAC (arith_ss++STATE_INP_ss)
             [SNEXT_def,ADD1,GSYM io_onestepTheory.ADVANCE_COMP,ADVANCE_def]
        \\ (RES_MP1_TAC [] CP_TRANSFER_LEM >> METIS_TAC [IS_BUSY_def])
        \\ `(p + w' - b = p + 1) /\ (p + w' - (b + 1) = p)`
        by ASM_SIMP_TAC arith_ss [Abbr`w'`]
        \\ FULL_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss++ICLASS_ss) []
        \\ ASM_SIMP_TAC (std_ss++LDC_ss++STC_ss) []
        \\ ASM_SIMP_TAC (std_ss++boolSimps.CONJ_ss++PBETA_ss++ALU_ss)
             [IF_NEG,TO_WRITE_READ6,LSL_ZERO,LSL_TWO,ALUOUT_ALU_logic,
              ALUOUT_ADD,ALUOUT_SUB,METIS_PROVE [] ``a /\ b \/ a = a``]
        \\ FULL_SIMP_TAC arith_ss [state_arm6_11,dp_11,ctrl_11,ADD1,
             LEFT_ADD_DISTRIB,GSYM word_add_n2w]
        \\ CONV_TAC (DEPTH_CONV EXISTS_AND_REORDER_CONV)
        \\ FINISH_OFF3]);

val NOT_INTERRUPT = GEN_ALL (prove(
 `!w b inp.
     inp IN STRM_ARM6 /\
     Abbrev (b = BUSY_WAIT x inp) /\
     Abbrev (w = 1 + b + (LEAST n. IS_BUSY (ADVANCE b inp) n)) /\
     ~IS_BUSY inp b ==>
     1 + b < w`,
  REPEAT STRIP_TAC \\ IMP_RES_TAC EXISTS_BUSY_WAIT_IMP_BUSY_WAIT_DONE
    \\ Cases_on_x `x` \\ IMP_RES_TAC BUSY_EXISTS_COR
    \\ Cases_on `(LEAST n. PROJ_CPB (inp (b + n))) = 0`
    \\ FULL_SIMP_TAC arith_ss
         [Abbr`w`,IS_BUSY_def,ADVANCE_def,BUSY_WAIT_DONE_def]));

val x = METIS_PROVE []
  ``!a2 a9 a10 a13 a14.
    (a2 /\ a9 /\ a10 /\ a13 ==> a14) ==>
    ((a1 /\ a2 /\ a3 /\ a4 /\ a5 /\ a6 /\ a7 /\
      a8 /\ a9 /\ a10 /\ a11 /\ a12 /\ a13 ==> (a14 ==> a15)) =
     (a1 /\ a2 /\ a3 /\ a4 /\ a5 /\ a6 /\ a7 /\
      a8 /\ a9 /\ a10 /\ a11 /\ a12 /\ a13 ==> a15))``;

val x2 = (GEN_ALL o REWRITE_RULE [NOT_INTERRUPT] o
  SPECL [`inp IN STRM_ARM6`,`Abbrev (b = BUSY_WAIT x inp)`,
         `Abbrev (w = 1 + b + (LEAST n. IS_BUSY (ADVANCE b inp) n))`,
         `~IS_BUSY inp b`,`1 + b < w`]) x;

val LDC_STC_THM2 = save_thm("LDC_STC_THM2",
  (SIMP_RULE std_ss [x2,LESS_EQ_REFL] o SPEC `w`) LDC_STC_THM);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
