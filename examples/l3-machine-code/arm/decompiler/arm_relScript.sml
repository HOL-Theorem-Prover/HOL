
open HolKernel Parse boolLib bossLib; val _ = new_theory "arm_rel";

open armTheory armLib arm_stepTheory pred_setTheory pairTheory optionTheory;
open arithmeticTheory wordsTheory wordsLib addressTheory combinTheory pairSyntax;
open sumTheory whileTheory;

open arm_decompTheory progTheory;

infix \\
val op \\ = op THEN;

val RW = REWRITE_RULE
val RW1 = ONCE_REWRITE_RULE


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
                    (* fps *) (word5 -> word64) =>
                    (* rmode *) word2 =>
                    (* fp_n *) bool =>
                    (* fp_z *) bool =>
                    (* fp_c *) bool =>
                    (* fp_v *) bool =>
                    (* domain of memory *) word32 set =>
                    (* memory *) (word32 -> word8)`;

val arm_assert_tm =
  ``ARM_ASSERTION r15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
                  n z c v fps rmode fp_n fp_z fp_c fp_v dm m``

val arm_FP_REGS_def = Define `
  arm_FP_REGS (fps:word5 -> word64) =
    arm_FP_REG 0w (fps 0w) *
    arm_FP_REG 1w (fps 1w) *
    arm_FP_REG 2w (fps 2w) *
    arm_FP_REG 3w (fps 3w) *
    arm_FP_REG 4w (fps 4w) *
    arm_FP_REG 5w (fps 5w) *
    arm_FP_REG 6w (fps 6w) *
    arm_FP_REG 7w (fps 7w) *
    arm_FP_REG 8w (fps 8w) *
    arm_FP_REG 9w (fps 9w) *
    arm_FP_REG 10w (fps 10w) *
    arm_FP_REG 11w (fps 11w) *
    arm_FP_REG 12w (fps 12w) *
    arm_FP_REG 13w (fps 13w) *
    arm_FP_REG 14w (fps 14w) *
    arm_FP_REG 15w (fps 15w) *
    arm_FP_REG 16w (fps 16w) *
    arm_FP_REG 17w (fps 17w) *
    arm_FP_REG 18w (fps 18w) *
    arm_FP_REG 19w (fps 19w) *
    arm_FP_REG 20w (fps 20w) *
    arm_FP_REG 21w (fps 21w) *
    arm_FP_REG 22w (fps 22w) *
    arm_FP_REG 23w (fps 23w) *
    arm_FP_REG 24w (fps 24w) *
    arm_FP_REG 25w (fps 25w) *
    arm_FP_REG 26w (fps 26w) *
    arm_FP_REG 27w (fps 27w) *
    arm_FP_REG 28w (fps 28w) *
    arm_FP_REG 29w (fps 29w) *
    arm_FP_REG 30w (fps 30w) *
    arm_FP_REG 31w (fps 31w)`;

val ARM_ASSERT_def = Define `
  ARM_ASSERT ^arm_assert_tm =
    arm_PC r15 *
    arm_REG RName_0usr r0 *
    arm_REG RName_1usr r1 *
    arm_REG RName_2usr r2 *
    arm_REG RName_3usr r3 *
    arm_REG RName_4usr r4 *
    arm_REG RName_5usr r5 *
    arm_REG RName_6usr r6 *
    arm_REG RName_7usr r7 *
    arm_REG RName_8usr r8 *
    arm_REG RName_9usr r9 *
    arm_REG RName_10usr r10 *
    arm_REG RName_11usr r11 *
    arm_REG RName_12usr r12 *
    arm_REG RName_SPusr r13 *
    arm_REG RName_LRusr r14 *
    arm_CPSR_N n *
    arm_CPSR_Z z *
    arm_CPSR_C c *
    arm_CPSR_V v *
    arm_FP_REGS fps *
    arm_FP_FPSCR_RMode rmode *
    arm_FP_FPSCR_N fp_n *
    arm_FP_FPSCR_Z fp_z *
    arm_FP_FPSCR_C fp_c *
    arm_FP_FPSCR_V fp_v *
    arm_MEMORY dm m`;

val L3_ARM_def = Define `
  L3_ARM = (ARM_ASSERT, L3_ARM_MODEL)`;

val INTRO_TRIPLE_L3_ARM = store_thm("INTRO_TRIPLE_L3_ARM",
  ``(side ==> SPEC L3_ARM_MODEL (ARM_ASSERT pre) code (ARM_ASSERT post)) ==>
    !c. TRIPLE L3_ARM (c, pre) code (c /\ side, post)``,
  SIMP_TAC std_ss [L3_ARM_def,TRIPLE_def]);

val _ = export_theory();
