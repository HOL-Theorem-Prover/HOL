(* app load ["metisLib","armTheory","coreTheory","lemmasTheory","io_onestepTheory"]; *)
open HolKernel boolLib bossLib Q arithmeticTheory io_onestepTheory
     armTheory coreTheory lemmasTheory;

(* -------------------------------------------------------- *)

val _ = new_theory "interrupts";

val _ = numLib.prefer_num();

val std_ss = std_ss ++ boolSimps.LET_ss;
val arith_ss = arith_ss ++ boolSimps.LET_ss;

(* -------------------------------------------------------- *)

val EXISTS_LEAST_NOT_RESET = prove(
  `!t i. i IN STRM_ARM6 /\ IS_RESET i t ==> ?t2. IS_RESET i t2 /\ ~IS_RESET i (t2 + 1) /\ ~IS_RESET i (t2 + 2)`,
  RW_TAC bool_ss [IN_DEF,STRM_ARM6_def]
    THEN FIRST_X_ASSUM (SPEC_THEN `t` (STRIP_ASSUME_TAC o CONV_RULE numLib.EXISTS_LEAST_CONV))
    THEN POP_ASSUM (SPEC_THEN `t2 - 1` (ASSUME_TAC o SIMP_RULE arith_ss []))
    THEN EXISTS_TAC `t2 - 1` THEN Cases_on `t2`
    THEN FULL_SIMP_TAC arith_ss [ADD1] THEN FULL_SIMP_TAC bool_ss []
    THEN `n = t` by DECIDE_TAC THEN ASM_REWRITE_TAC []
);

val LEAST_NOT_RESET = save_thm("LEAST_NOT_RESET",
  GEN_ALL (MATCH_MP (PROVE [] ``((a ==> b) /\ (b ==> c)) ==> (a ==> c)``)
    (CONJ (SPEC_ALL EXISTS_LEAST_NOT_RESET) ((SIMP_RULE std_ss [] o
       SPEC `\t. IS_RESET i t /\ ~IS_RESET i (t + 1) /\ ~IS_RESET i (t + 2)`) whileTheory.LEAST_EXISTS_IMP)))
);

(* -------------------------------------------------------- *)

val IS_RESET_LEM = prove(
  `!i t. ~IS_RESET i t ==> FST (i t)`,
  NTAC 2 STRIP_TAC THEN REWRITE_TAC [IS_RESET_def]
    THEN SPEC_THEN `i t` (fn th => ONCE_REWRITE_TAC [th]) form_4tuple
    THEN SIMP_TAC std_ss [PROJ_NRESET_def]
);

val IS_RESET_THM = store_thm("IS_RESET_THM",
  `!i x. (!t. ~(t < x) \/ ~IS_RESET i t) ==>
       (!t. (t < x) ==> FST (i t))`,
  PROVE_TAC [IS_RESET_LEM]
);

val IS_RESET_THM2 = store_thm("IS_RESET_THM2",
  `!y x i. (!t. ~(t < x) \/ ~IS_RESET i t) /\ y <= x==>
       (!t. (t < y) ==> FST (i t))`,
  metisLib.METIS_TAC [IS_RESET_THM,LESS_LESS_EQ_TRANS]
);

(* -------------------------------------------------------- *)

val AFTER_RESET1_def = Define`
  AFTER_RESET1 (ARM6 dp
    (CTRL pipea pipeaval pipeb pipebval ireg iregval
          ointstart onewinst endinst obaselatch opipebll nxtic nxtis
          nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
          aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
          mask orp oorp mul mul2 borrow2 mshift)) =
   oorst /\ resetlatch`;

val AFTER_RESET2_def = Define`
  AFTER_RESET2 (ARM6 dp
    (CTRL pipea pipeaval pipeb pipebval ireg iregval
          ointstart onewinst endinst obaselatch opipebll nxtic nxtis
          nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
          aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
          mask orp oorp mul mul2 borrow2 mshift)) =
   ~iregval /\ oorst /\ resetlatch`;

val AFTER_RESET3_def = Define`
  AFTER_RESET3 (ARM6 dp
    (CTRL pipea pipeaval pipeb pipebval ireg iregval
          ointstart onewinst endinst obaselatch opipebll nxtic nxtis
          nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
          aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
          mask orp oorp mul mul2 borrow2 mshift)) =
   ~iregval /\ opipebll /\ oorst /\ resetlatch`;

val AFTER_RESET4_def = Define`
  AFTER_RESET4 (ARM6 dp
    (CTRL pipea pipeaval pipeb pipebval ireg iregval
          ointstart onewinst endinst obaselatch opipebll nxtic nxtis
          nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
          aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
          mask orp oorp mul mul2 borrow2 mshift)) =
   pipeaval /\ pipebval /\ ~iregval /\ opipebll /\ oorst /\ resetlatch`;

val AFTER_NRESET1_def = Define`
  AFTER_NRESET1 (ARM6 dp
    (CTRL pipea pipeaval pipeb pipebval ireg iregval
          ointstart onewinst endinst obaselatch opipebll nxtic nxtis
          nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
          aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
          mask orp oorp mul mul2 borrow2 mshift)) =
  pipeaval /\ pipebval /\ ~iregval /\ opipebll /\ ~oorst /\ resetlatch`;
   

val AFTER_NRESET2_def = Define`
  AFTER_NRESET2 (ARM6 dp
    (CTRL pipea pipeaval pipeb pipebval ireg iregval
          ointstart onewinst endinst obaselatch opipebll nxtic nxtis
          nopc1 oorst resetlatch onfq ooonfq oniq oooniq pipeaabt pipebabt iregabt2 dataabt2
          aregn2 mrq2 nbw nrw sctrlreg psrfb oareg
          mask orp oorp mul mul2 borrow2 mshift)) =
   pipeaval /\ pipebval /\ iregval /\ ointstart /\ endinst /\ onewinst /\
   opipebll /\ (nxtic = swi_ex) /\ (nxtis = t3) /\ ~nopc1 /\
   ~oorst /\ ~resetlatch /\ (aregn2 = 0) /\ mrq2 /\ ~nrw /\ (mask = ARB)`;

(* -------------------------------------------------------- *)

val IS_RESET_EXISTS = prove(
  `(!i t. IS_RESET i t ==> ?onfq oniq abort data. i t = (F,onfq,oniq,abort,data)) /\
    !i t. ~IS_RESET i t ==> ?onfq oniq abort data. i t = (T,onfq,oniq,abort,data)`,
  RW_TAC bool_ss [IS_RESET_def]
    THEN Cases_on `i t`
    THEN Cases_on `r` THEN Cases_on `r'` THEN Cases_on `r`
    THEN FULL_SIMP_TAC std_ss [PROJ_NRESET_def]
);

fun add_rws f rws =
  let val cmp_set = f()
      val _ = computeLib.add_thms rws cmp_set
    (*  val _ = computeLib.set_skip cmp_set ``COND`` NONE *)
  in
    cmp_set
end;

fun reset_rws() =
  add_rws computeLib.bool_compset
    [pairTheory.FST,pairTheory.SND,LET_THM,pairTheory.UNCURRY_DEF,
     REWRITE_RULE [DECODE_PSR,COND_PAIR] NEXT_ARM6_def,RESETLATCH_def,AFTER_RESET1_def];

fun reset_rws2() = add_rws reset_rws [AFTER_RESET2_def,IREGVAL_def,PIPESTATIREGWRITE_def];
fun reset_rws3() = add_rws reset_rws2 [AFTER_RESET3_def,PIPEBLL_def,ABORTINST_def,IC_def,NEWINST_def];
fun reset_rws4() = add_rws reset_rws3 [AFTER_RESET4_def,PIPEALL_def,PIPEAVAL_def,PIPESTATAWRITE_def,PIPESTATBWRITE_def];
fun reset_rws5() = add_rws reset_rws4 [AFTER_NRESET1_def,ENDINST_def,RWA_def,PCCHANGE_def,RESETSTART_def];
fun reset_rws6() = add_rws reset_rws5 [AFTER_NRESET2_def,NOPC_def,AREGN1_def,NRW_def,NMREQ_def,
                                               MASK_def,NXTIC_def,NXTIS_def,INTSEQ_def,iclass_distinct,GSYM iclass_distinct];

val AFTER_RESET1_THM = prove(
  `!a t i. IS_RESET i t ==> AFTER_RESET1 (NEXT_ARM6 a (i t))`,
  Cases THEN Cases_on `d` THEN Cases_on `c`
    THEN REPEAT STRIP_TAC THEN IMP_RES_TAC IS_RESET_EXISTS
    THEN ASM_REWRITE_TAC [] THEN CONV_TAC (computeLib.CBV_CONV (reset_rws()))
);

val AFTER_RESET2_THM = prove(
  `!a t i. AFTER_RESET1 a /\ IS_RESET i t ==> AFTER_RESET2 (NEXT_ARM6 a (i t))`,
  Cases THEN Cases_on `d` THEN Cases_on `c`
    THEN RW_TAC std_ss [AFTER_RESET1_def] THEN IMP_RES_TAC IS_RESET_EXISTS
    THEN ASM_REWRITE_TAC [] THEN CONV_TAC (computeLib.CBV_CONV (reset_rws2()))
);

val AFTER_RESET3_THM = prove(
  `!a t i. AFTER_RESET2 a /\ IS_RESET i t ==> AFTER_RESET3 (NEXT_ARM6 a (i t))`,
  Cases THEN Cases_on `d` THEN Cases_on `c`
    THEN RW_TAC std_ss [AFTER_RESET2_def] THEN IMP_RES_TAC IS_RESET_EXISTS
    THEN ASM_REWRITE_TAC [] THEN CONV_TAC (computeLib.CBV_CONV (reset_rws3()))
);

val AFTER_RESET4_THM = prove(
  `!a t i. AFTER_RESET3 a /\ IS_RESET i t ==> AFTER_RESET4 (NEXT_ARM6 a (i t))`,
  Cases THEN Cases_on `d` THEN Cases_on `c`
    THEN RW_TAC std_ss [AFTER_RESET3_def] THEN IMP_RES_TAC IS_RESET_EXISTS
    THEN ASM_REWRITE_TAC [] THEN CONV_TAC (computeLib.CBV_CONV (reset_rws4()))
);

val AFTER_NRESET1_THM = prove(
  `!a t i. AFTER_RESET4 a /\ ~IS_RESET i t ==> AFTER_NRESET1 (NEXT_ARM6 a (i t))`,
  Cases THEN Cases_on `d` THEN Cases_on `c`
    THEN RW_TAC std_ss [AFTER_RESET4_def] THEN IMP_RES_TAC IS_RESET_EXISTS
    THEN ASM_REWRITE_TAC [] THEN CONV_TAC (computeLib.CBV_CONV (reset_rws5()))
);

val AFTER_NRESET2_THM = prove(
  `!a t i. AFTER_NRESET1 a /\ ~IS_RESET i t ==> AFTER_NRESET2 (NEXT_ARM6 a (i t))`,
  Cases THEN Cases_on `d` THEN Cases_on `c`
    THEN RW_TAC std_ss [AFTER_NRESET1_def] THEN IMP_RES_TAC IS_RESET_EXISTS
    THEN ASM_REWRITE_TAC [] THEN CONV_TAC (computeLib.CBV_CONV (reset_rws6()))
);

val AFTER_NRESET2_THM2 = prove(
  `!x. IS_RESET x.inp 0 /\ IS_RESET x.inp 1 /\ IS_RESET x.inp 2 /\ IS_RESET x.inp 3 /\
           ~IS_RESET x.inp 4 /\ ~IS_RESET x.inp 5 ==>
           AFTER_NRESET2 ((FUNPOW (SNEXT NEXT_ARM6) 6 x).state)`,
  Cases THEN SIMP_TAC (srw_ss()) [] THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC (SPECL [`a`,`0`] AFTER_RESET1_THM) THEN POP_ASSUM (SPEC_THEN `a` ASSUME_TAC)
    THEN IMP_RES_TAC (SPECL [`a`,`1`] AFTER_RESET2_THM)
    THEN IMP_RES_TAC (SPECL [`a`,`2`] AFTER_RESET3_THM)
    THEN IMP_RES_TAC (SPECL [`a`,`3`] AFTER_RESET4_THM)
    THEN IMP_RES_TAC (SPECL [`a`,`4`] AFTER_NRESET1_THM)
    THEN IMP_RES_TAC (SPECL [`a`,`5`] AFTER_NRESET2_THM)
    THEN ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss) [numeralTheory.numeral_funpow,SNEXT_def,ADVANCE_def]
);

val lem = prove(
  `!t1 t2 i. IS_RESET (ADVANCE t1 i) t2 = IS_RESET i (t1 + t2)`,
  SIMP_TAC bool_ss [IS_RESET_def,ADVANCE_def]
);

val SPEC_AFTER_NRESET2 = save_thm("SPEC_AFTER_NRESET2",
  (GEN_ALL o SIMP_RULE arith_ss [] o DISCH `2 < t` o SPEC_ALL o INST [`t` |-> `t - 3`] o
   SIMP_RULE (srw_ss()) [lem] o SPEC `<| state := a; inp := ADVANCE t i|>`) AFTER_NRESET2_THM2
);

val AFTER_NRESET2_THM3 = store_thm("AFTER_NRESET2_THM3",
  `!a.  AFTER_NRESET2 a ==> (INIT_ARM6 a = a)`,
  Cases THEN Cases_on `d` THEN Cases_on `c`
    THEN RW_TAC std_ss [AFTER_NRESET2_def,INIT_ARM6_def,MASK_def,exception2num_thm,num2exception_thm]
);

val AFTER_NRESET2_THM4 = store_thm("AFTER_NRESET2_THM4",
  `!a. AFTER_NRESET2 a ==>
     (SND (SND (TRIPLE_ARM_EX (ABS_ARM6 a))) = reset) /\
     (TRIPLE_ARM_EX (ABS_ARM6 a) =
       (FST (TRIPLE_ARM_EX (ABS_ARM6 a)),FST (SND (TRIPLE_ARM_EX (ABS_ARM6 a))),reset))`,
  Cases THEN Cases_on `d` THEN Cases_on `c`
    THEN RW_TAC std_ss [AFTER_NRESET2_def,ABS_ARM6_def,TRIPLE_ARM_EX_def,reset]
);

val TRIPLE_ARM_EX_THM = store_thm("TRIPLE_ARM_EX_THM",
  `!a. ARM_EX (FST (TRIPLE_ARM_EX a)) (FST (SND (TRIPLE_ARM_EX a))) (SND (SND (TRIPLE_ARM_EX a))) = a`,
  Cases THEN SIMP_TAC std_ss [TRIPLE_ARM_EX_def]
);

(* -------------------------------------------------------- *)

val lem = prove(
  `!i t. i IN STRM_ARM6 /\ IS_RESET i t /\ ~IS_RESET i (t + 1) ==> IS_RESET i (t - 1)`,
  RW_TAC bool_ss [IN_DEF,STRM_ARM6_def]
    THEN Cases_on `t` THEN FULL_SIMP_TAC arith_ss [ADD1]
    THEN PAT_ASSUM `!t. a ==> b` (SPEC_THEN `n + 1` IMP_RES_TAC)
    THEN FULL_SIMP_TAC arith_ss []
);

val lem2 = prove(
  `!i t. i IN STRM_ARM6 /\ IS_RESET i t /\ ~IS_RESET i (t + 1) ==>
           IS_RESET i (t - 1) /\ IS_RESET i (t - 2)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC lem
    THEN FULL_SIMP_TAC bool_ss [IN_DEF,STRM_ARM6_def]
    THEN Cases_on `t` THEN FULL_SIMP_TAC arith_ss [ADD1]
    THEN PAT_ASSUM `!t. a ==> b` (SPEC_THEN `n` IMP_RES_TAC)
    THEN FULL_SIMP_TAC arith_ss []
);

val PREVIOUS_THREE_RESET = store_thm("PREVIOUS_THREE_RESET",
  `!i t. i IN STRM_ARM6 /\ IS_RESET i t /\ ~IS_RESET i (t + 1) ==>
           IS_RESET i (t - 1) /\ IS_RESET i (t - 2) /\ IS_RESET i (t - 3)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC lem
    THEN FULL_SIMP_TAC bool_ss [IN_DEF,STRM_ARM6_def]
    THEN Cases_on `t` THEN FULL_SIMP_TAC arith_ss [ADD1]
    THEN PAT_ASSUM `!t. a ==> b` (fn th => IMP_RES_TAC (SPEC `n` th) THEN ASSUME_TAC th)
    THEN FULL_SIMP_TAC arith_ss []
    THEN POP_ASSUM (SPEC_THEN `n - 1` IMP_RES_TAC)
    THEN FULL_SIMP_TAC arith_ss []
    THEN PROVE_TAC [DECIDE ``!n. ~(n = 0) ==> (n - 1 + 3 = n + 2)``]
);

val LEAST_RESET_GT_TWO = store_thm("LEAST_RESET_GT_TWO",
  `!i t. i IN STRM_ARM6 /\ IS_RESET i t ==>
        2 < (LEAST t. IS_RESET i t /\ ~IS_RESET i (t + 1) /\ ~IS_RESET i (t + 2))`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC LEAST_NOT_RESET
    THEN PAT_ASSUM `IS_RESET i t` (K ALL_TAC)
    THEN IMP_RES_TAC PREVIOUS_THREE_RESET
    THEN REPEAT (PAT_ASSUM `~a ==> b` (K ALL_TAC))
    THEN ABBREV_TAC `l = LEAST t. IS_RESET i t /\ ~IS_RESET i (t + 1) /\ ~IS_RESET i (t + 2)`
    THEN Cases_on `(l = 0) \/ (l = 1) \/ (l = 2)`
    THEN FULL_SIMP_TAC arith_ss [IN_DEF,STRM_ARM6_def]
    THEN POP_ASSUM (fn th => FULL_SIMP_TAC arith_ss [th])
    THEN PAT_ASSUM `!n. IS_RESET i t ==> b` IMP_RES_TAC
    THEN FULL_SIMP_TAC arith_ss []
);

(* -------------------------------------------------------- *)

val AREGN1_THM = store_thm("AREGN1_THM",
  `!resetstart dataabt1 fiqactl irqactl coproc1 iregabt2.
     (num2exception (AREGN1 resetstart dataabt1 fiqactl irqactl coproc1 iregabt2) = software) =
     ~resetstart /\ ~dataabt1 /\ ~fiqactl /\ ~irqactl /\ ~coproc1 /\ ~iregabt2`,
  RW_TAC std_ss [AREGN1_def,num2exception_thm]
);

val interrupt_exists = store_thm("interrupt_exists",
  `?aregn. ~(num2exception aregn IN {reset; undefined; software; address}) /\ aregn < 8`,
  EXISTS_TAC `3`
    THEN RW_TAC std_ss [pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY,
                        num2exception_thm,exception_distinct]
);

val AREGN1_LT_8 = store_thm("AREGN1_LT_8",
  `!resetstart dataabt1 fiqactl irqactl coproc1 iregabt2.
      AREGN1 resetstart dataabt1 fiqactl irqactl coproc1 iregabt2 < 8`,
  RW_TAC std_ss [AREGN1_def]
);

val AREGN1_BIJ = store_thm("AREGN1_BIJ",
  `!resetstart dataabt1 fiqactl irqactl coproc1 iregabt2.
      exception2num (num2exception (AREGN1 resetstart dataabt1 fiqactl irqactl coproc1 iregabt2)) =
        AREGN1 resetstart dataabt1 fiqactl irqactl coproc1 iregabt2`,
  SIMP_TAC std_ss [AREGN1_LT_8,GSYM exception2num_num2exception]
);

(* -------------------------------------------------------- *)

val NOT_RESET = store_thm("NOT_RESET",
  `!x y dataabt1 fiqactl irqactl coproc1 iregabt2.
    ~IS_Reset (case num2exception (AREGN1 F dataabt1 fiqactl irqactl coproc1 iregabt2) of
                  reset -> SOME (Reset x)
               || undefined -> NONE
               || software -> NONE
               || pabort -> SOME Prefetch
               || dabort -> SOME (Dabort y)
               || address -> NONE
               || interrupt -> SOME Irq
               || fast -> SOME Fiq)`,
  RW_TAC std_ss [AREGN1_def,IS_Reset_def,num2exception_thm]
);

val NOT_RESET2 = store_thm("NOT_RESET2",
  `!x y ointstart aregn.
     ~(num2exception aregn IN {reset; undefined; software; address}) ==>
     (IS_Reset (
        case num2exception (if ointstart then aregn else 2) of
           reset -> SOME (Reset (ARM x z))
     || undefined -> NONE
     || software -> NONE
     || pabort -> SOME Prefetch
     || dabort -> SOME (Dabort y)
     || address -> NONE
     || interrupt -> SOME Irq
     || fast -> SOME Fiq) = F)`,
  RW_TAC std_ss [AREGN1_def,IS_Reset_def,num2exception_thm]
    THEN Cases_on `num2exception aregn`
    THEN RW_TAC std_ss [num2exception_thm]
    THEN FULL_SIMP_TAC std_ss [exception_distinct,pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY]
);

(* -------------------------------------------------------- *)

val SIMP_IS_Dabort = store_thm("SIMP_IS_Dabort",
  `!x y dataabt1 fiqactl irqactl coproc1 iregabt2.
    (IS_Dabort (
     (case (num2exception (AREGN1 F dataabt1 fiqactl irqactl coproc1 iregabt2)) of
        reset -> SOME (Reset x)
     || undefined -> NONE
     || software -> NONE
     || pabort -> SOME Prefetch
     || dabort -> SOME (Dabort y)
     || address -> NONE
     || interrupt -> SOME Irq
     || fast -> SOME Fiq))) = dataabt1`,
  RW_TAC std_ss [AREGN1_def,num2exception_thm,IS_Dabort_def]
);

val SIMP_PROJ_Dabort = store_thm("SIMP_PROJ_Dabort",
  `!x y fiqactl irqactl coproc1 iregabt2.
    (PROJ_Dabort
     (case (num2exception (AREGN1 F T fiqactl irqactl coproc1 iregabt2)) of
        reset -> SOME (Reset x)
     || undefined -> NONE
     || software -> NONE
     || pabort -> SOME Prefetch
     || dabort -> SOME (Dabort y)
     || address -> NONE
     || interrupt -> SOME Irq
     || fast -> SOME Fiq)) = y`,
  RW_TAC std_ss [AREGN1_def,num2exception_thm,PROJ_Dabort_def]
);

val SIMP_interrupt2exception = store_thm("SIMP_interrupt2exception",
  `!cpsr exc ireg x y nxtic pipeb resetstart dataabt1 nfq niq iregabt2.
    ~(exc = software) \/ ~CONDITION_PASSED (NZCV (w2n cpsr)) ireg ==>
    ((interrupt2exception (cpsr,exc,ireg)
     (case (num2exception
        (AREGN1 resetstart dataabt1 fiqactl irqactl F iregabt2)) of
        reset -> SOME (Reset (ARM x z))
     || undefined -> NONE
     || software -> NONE
     || pabort -> SOME Prefetch
     || dabort -> SOME (Dabort y)
     || address -> NONE
     || interrupt -> SOME Irq
     || fast -> SOME Fiq)) =
    num2exception (AREGN1 resetstart dataabt1 fiqactl irqactl F iregabt2))`,
  RW_TAC std_ss [DECODE_PSR_def,AREGN1_def,num2exception_thm,NXTIC_def,interrupt2exception_def]
);

val SIMP_interrupt2exception2 = store_thm("SIMP_interrupt2exception2",
  `!cpsr ireg x y nxtic pipeb resetstart dataabt1 nfq niq coproc1 iregabt2.
    ((DECODE_INST ireg = cdp_und) = coproc1) /\
     CONDITION_PASSED (NZCV (w2n cpsr)) ireg ==>
    ((interrupt2exception (cpsr,software,ireg)
     (case (num2exception
        (AREGN1 resetstart dataabt1 fiqactl irqactl coproc1 iregabt2)) of
        reset -> SOME (Reset (ARM x z))
     || undefined -> NONE
     || software -> NONE
     || pabort -> SOME Prefetch
     || dabort -> SOME (Dabort y)
     || address -> NONE
     || interrupt -> SOME Irq
     || fast -> SOME Fiq)) =
    num2exception (AREGN1 resetstart dataabt1 fiqactl irqactl coproc1 iregabt2))`,
  RW_TAC std_ss [DECODE_PSR_def,AREGN1_def,num2exception_thm,NXTIC_def,interrupt2exception_def]
);

val SIMP_interrupt2exception3 = store_thm("SIMP_interrupt2exception3",
  `!x y cpsr ireg aregn ointstart.
    ~(DECODE_INST ireg = cdp_und) /\
    ~(num2exception aregn IN {reset; undefined; software; address}) ==>
    ((interrupt2exception (cpsr,software,ireg)
     (case (num2exception (if ointstart then aregn else 2)) of
        reset -> SOME (Reset (ARM x z))
     || undefined -> NONE
     || software -> NONE
     || pabort -> SOME Prefetch
     || dabort -> SOME (Dabort y)
     || address -> NONE
     || interrupt -> SOME Irq
     || fast -> SOME Fiq)) =
    num2exception (if ointstart then aregn else 2))`,
  RW_TAC std_ss [DECODE_PSR_def,num2exception_thm,interrupt2exception_def]
    THEN Cases_on `num2exception aregn`
    THEN RW_TAC std_ss [num2exception_thm]
    THEN FULL_SIMP_TAC std_ss [exception_distinct,pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY]
);

(* -------------------------------------------------------- *)

val IS_Reset_IMP_EXISTS_SOME_Reset = store_thm("IS_Reset_IMP_EXISTS_SOME_Reset",
  `!i. IS_Reset i ==> (?s. i = SOME (Reset s))`,
  Cases THEN RW_TAC std_ss [IS_Reset_def]
    THEN Cases_on `x`
    THEN FULL_SIMP_TAC std_ss [interrupts_case_def]
    THEN PROVE_TAC []
);

(* -------------------------------------------------------- *)

val _ = export_theory();
