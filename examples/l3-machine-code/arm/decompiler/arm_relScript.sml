open HolKernel Parse boolLib bossLib
open armTheory armLib arm_stepTheory pred_setTheory pairTheory optionTheory
open arithmeticTheory wordsTheory wordsLib addressTheory combinTheory pairSyntax
open sumTheory whileTheory

open arm_decompTheory progTheory;

val _ = new_theory "arm_rel";

infix \\
val op \\ = op THEN;

(* we define a total-correctness machine-code Hoare triple *)

val TRIPLE_def = Define `
  TRIPLE (assert,model) pre code post =
    FST post ==> FST pre /\
    SPEC model (assert (SND pre)) code (assert (SND post))`;


(* theorems about this Hoare triple *)

val TRIPLE_COMPOSE = store_thm("TRIPLE_COMPOSE",
  ``!i p c m q. TRIPLE i p c m /\ TRIPLE i m c q ==> TRIPLE i p c q``,
  SIMP_TAC std_ss [TRIPLE_def,FORALL_PROD] THEN REPEAT STRIP_TAC
  THEN METIS_TAC [SPEC_COMPOSE,UNION_IDEMPOT]);

val TRIPLE_EXTEND = store_thm("TRIPLE_EXTEND",
  ``!i p c q c'. TRIPLE i p c q ==> c SUBSET c' ==> TRIPLE i p c' q``,
  SIMP_TAC std_ss [TRIPLE_def,FORALL_PROD] THEN REPEAT STRIP_TAC
  \\ METIS_TAC [SPEC_SUBSET_CODE]);

val TRIPLE_REFL = store_thm("TRIPLE_REFL",
  ``!i c p. TRIPLE i p c p``,
  SIMP_TAC std_ss [FORALL_PROD,TRIPLE_def,SPEC_REFL]);

val TRIPLE_COMPOSE_ALT = store_thm("TRIPLE_COMPOSE_ALT",
  ``!i p c m q. TRIPLE i m c q ==> TRIPLE i p c m ==> TRIPLE i p c q``,
  REPEAT STRIP_TAC \\ MATCH_MP_TAC TRIPLE_COMPOSE
  \\ Q.EXISTS_TAC `m` \\ FULL_SIMP_TAC std_ss []);

val COND_MERGE = store_thm("COND_MERGE",
  ``(x1 ==> f (g x2)) /\ (~x1 ==> f (g y2)) ==>
    f (g (if x1 then x2 else y2))``,
  Cases_on `x1` \\ FULL_SIMP_TAC std_ss []);

val TERM_TAILREC_def = Define `
  TERM_TAILREC f g (d:'a -> bool # 'b) x =
    let (cond,y) = d (WHILE g f x) in
      (cond /\ (?n. ~g (FUNPOW f n x)),y)`;

val SHORT_TERM_TAILREC_def = Define `
  SHORT_TERM_TAILREC (f:'a -> 'a + (bool # 'b)) =
    TERM_TAILREC (OUTL o f) (ISL o f) (OUTR o f)`;

val TERM_TAILREC_THM = store_thm("TERM_TAILREC_THM",
  ``TERM_TAILREC f g d x = if g x then TERM_TAILREC f g d (f x) else d x``,
  REVERSE (Cases_on `g x`) \\ FULL_SIMP_TAC std_ss [TERM_TAILREC_def,LET_DEF]
  \\ ASM_SIMP_TAC std_ss [Once WHILE] THEN1
   (Cases_on `d x` \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `0` \\ FULL_SIMP_TAC std_ss [FUNPOW])
  \\ Cases_on `(d (WHILE g f (f x)))` \\ FULL_SIMP_TAC std_ss []
  \\ Cases_on `q` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
  THEN1 (Cases_on `n` \\ FULL_SIMP_TAC std_ss [FUNPOW] \\ METIS_TAC [])
  \\ Q.EXISTS_TAC `SUC n` \\ FULL_SIMP_TAC std_ss [FUNPOW]);

val TRIPLE_TERM_TAILREC = prove(
  ``(!x. ~FST (post (F,x))) ==>
    (!x. TRIPLE i (pre x) c (if g x then pre (f x) else post (d x))) ==>
    (!x. TRIPLE i (pre x) c (post (TERM_TAILREC f g d x)))``,
  Cases_on `i` \\ SIMP_TAC std_ss [TERM_TAILREC_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ REVERSE (Cases_on `?n. ~g (FUNPOW f n x)`) THEN1
   (FULL_SIMP_TAC std_ss [] \\ Cases_on `d (WHILE g f x)`
    \\ FULL_SIMP_TAC std_ss [TRIPLE_def])
  \\ Q.PAT_ASSUM `!c. ~bbb` (K ALL_TAC)
  \\ FULL_SIMP_TAC std_ss [] \\ POP_ASSUM MP_TAC \\ Q.SPEC_TAC (`x`,`x`)
  \\ Induct_on `n` \\ FULL_SIMP_TAC std_ss [FUNPOW] \\ REPEAT STRIP_TAC THEN1
   (Q.PAT_ASSUM `!x.bbb` (MP_TAC o Q.SPEC `x`)
    \\ ONCE_REWRITE_TAC [WHILE] \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `d x` \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ REVERSE (`q' /\ (?n. ~g (FUNPOW f n x)) = q'` by ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `q'` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `0` \\ FULL_SIMP_TAC std_ss [FUNPOW])
  \\ REPEAT STRIP_TAC \\ REVERSE (Cases_on `g x`) THEN1
   (POP_ASSUM (MP_TAC) \\ POP_ASSUM (K ALL_TAC) \\ POP_ASSUM (K ALL_TAC)
    \\ Q.PAT_ASSUM `!x.bbb` (MP_TAC o Q.SPEC `x`)
    \\ ONCE_REWRITE_TAC [WHILE] \\ FULL_SIMP_TAC std_ss []
    \\ Cases_on `d x` \\ FULL_SIMP_TAC std_ss []
    \\ REPEAT STRIP_TAC \\ FULL_SIMP_TAC std_ss []
    \\ REVERSE (`q' /\ (?n. ~g (FUNPOW f n x)) = q'` by ALL_TAC)
    \\ FULL_SIMP_TAC std_ss [] \\ Cases_on `q'` \\ FULL_SIMP_TAC std_ss []
    \\ Q.EXISTS_TAC `0` \\ FULL_SIMP_TAC std_ss [FUNPOW])
  \\ MATCH_MP_TAC TRIPLE_COMPOSE
  \\ Q.EXISTS_TAC `pre (f x)` \\ STRIP_TAC THEN1 METIS_TAC []
  \\ RES_TAC \\ ONCE_REWRITE_TAC [WHILE] \\ FULL_SIMP_TAC std_ss []
  \\ `(?n. ~g (FUNPOW f n (f x))) = (?n. ~g (FUNPOW f n x))` by ALL_TAC THEN1
   (REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC
    THEN1 (Q.EXISTS_TAC `SUC n'` \\ FULL_SIMP_TAC std_ss [FUNPOW])
    \\ Cases_on `n'` \\ FULL_SIMP_TAC std_ss [FUNPOW] \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss []);

val my_sum_case_def = Define `
  my_sum_case f1 f2 x = case x of INL y => f1 y | INR y => f2 y`;

val my_sum_case_thm = prove(
  ``!x. my_sum_case pre post x = if ISL x then pre (OUTL x) else post (OUTR x)``,
  Cases \\ SRW_TAC [] [my_sum_case_def]);

val SHORT_TERM_TAILREC = store_thm("SHORT_TERM_TAILREC",
  ``(!x. TRIPLE i (pre x) c (my_sum_case pre post (f x))) ==>
    (!c x state. ~(FST (post (F,x)))) ==>
    (!x. TRIPLE i (pre x) c (post (SHORT_TERM_TAILREC f x)))``,
  SIMP_TAC std_ss [SHORT_TERM_TAILREC_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] TRIPLE_TERM_TAILREC)
  \\ FULL_SIMP_TAC std_ss [my_sum_case_thm]);

val TRIPLE_FRAME_BOOL = store_thm("TRIPLE_FRAME_BOOL",
  ``!i. TRIPLE i (c1,pre) code (c2,post) ==>
        !c. TRIPLE i (c /\ c1,pre) code (c /\ c2,post)``,
  SIMP_TAC std_ss [TRIPLE_def,FORALL_PROD] \\ REPEAT STRIP_TAC
  \\ Cases_on `c` \\ FULL_SIMP_TAC std_ss []);


(* definition of ARM_ASSERT and ARM_TOTAL_NEXT *)

val _ = Hol_datatype `
  arm_assertion = ARM_ASSERTION of
                    (* mode *) word5 =>
                    (* pc *) word32 =>
                    (* r0 *) word32 =>
                    (* r1 *) word32 =>
                    (* r2 *) word32 =>
                    (* r3 *) word32 =>
                    (* r4 *) word32 =>
                    (* r5 *) word32 =>
                    (* r6 *) word32 =>
                    (* r7 *) word32 =>
                    (* r8 *) word32 =>
                    (* r9 *) word32 =>
                    (* r10 *) word32 =>
                    (* r11 *) word32 =>
                    (* r12 *) word32 =>
                    (* r13 *) word32 =>
                    (* r14 *) word32 =>
                    (* n *) bool =>
                    (* z *) bool =>
                    (* c *) bool =>
                    (* v *) bool =>
                    (* domain of fps *) word5 set =>
                    (* fp registers *) (word5 -> word64) =>
                    (* rmode *) word2 =>
                    (* fp_n *) bool =>
                    (* fp_z *) bool =>
                    (* fp_c *) bool =>
                    (* fp_v *) bool =>
                    (* domain of memory *) word32 set =>
                    (* memory *) (word32 -> word8)`;
val arm_assert_tm =
  ``ARM_ASSERTION mode r15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
                  n z c v dfps fps rmode fp_n fp_z fp_c fp_v dm m``

val ARM_ASSERT_def = Define `
  ARM_ASSERT ^arm_assert_tm =
    arm_OK mode *
    arm_PC r15 *
    arm_REG (R_mode mode 0w) r0 *
    arm_REG (R_mode mode 1w) r1 *
    arm_REG (R_mode mode 2w) r2 *
    arm_REG (R_mode mode 3w) r3 *
    arm_REG (R_mode mode 4w) r4 *
    arm_REG (R_mode mode 5w) r5 *
    arm_REG (R_mode mode 6w) r6 *
    arm_REG (R_mode mode 7w) r7 *
    arm_REG (R_mode mode 8w) r8 *
    arm_REG (R_mode mode 9w) r9 *
    arm_REG (R_mode mode 10w) r10 *
    arm_REG (R_mode mode 11w) r11 *
    arm_REG (R_mode mode 12w) r12 *
    arm_REG (R_mode mode 13w) r13 *
    arm_REG (R_mode mode 14w) r14 *
    arm_CPSR_N n *
    arm_CPSR_Z z *
    arm_CPSR_C c *
    arm_CPSR_V v *
    arm_FP_REGISTERS dfps fps *
    arm_FP_FPSCR_RMode rmode *
    arm_FP_FPSCR_N fp_n *
    arm_FP_FPSCR_Z fp_z *
    arm_FP_FPSCR_C fp_c *
    arm_FP_FPSCR_V fp_v *
    arm_MEMORY dm m`;

val L3_ARM_def = Define `
  L3_ARM = (ARM_ASSERT, ARM_MODEL)`;

val INTRO_TRIPLE_L3_ARM = store_thm("INTRO_TRIPLE_L3_ARM",
  ``(side ==> SPEC ARM_MODEL (ARM_ASSERT pre) code (ARM_ASSERT post)) ==>
    !c. TRIPLE L3_ARM (c, pre) code (c /\ side, post)``,
  SIMP_TAC std_ss [L3_ARM_def,TRIPLE_def]);

val _ = export_theory()
