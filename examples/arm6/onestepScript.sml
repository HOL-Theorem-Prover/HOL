(* app load ["combinTheory","arithmeticTheory","prim_recTheory"]; *)
open HolKernel boolLib Q Parse bossLib simpLib numLib
     combinTheory arithmeticTheory prim_recTheory;

(* --------------------------------------------------------*)

val _ = new_theory "onestep";

(* --------------------------------------------------------*)
val FUNPOW_THM = store_thm("FUNPOW_THM",
  `!f n x. FUNPOW f n (f x) = f (FUNPOW f n x)`,
  Induct_on `n` THEN ASM_REWRITE_TAC [FUNPOW]
);

val FUNPOW_EVAL = store_thm("FUNPOW_EVAL",
  `!f n x. FUNPOW f n x = if n = 0 then x else FUNPOW f (n-1) (f x)`,
  Induct_on `n` THEN RW_TAC arith_ss [FUNPOW]
);

val FUNPOW_COMP_LEMMA = prove(
  `!f a b x. FUNPOW f (a+b) x = FUNPOW f a (FUNPOW f b x)`,
  Induct_on `b` THEN ASM_REWRITE_TAC [ADD_CLAUSES,FUNPOW]
);
(* --------------------------------------------------------*)

(*--------------------------------------------------------
  - Iterated Maps ----------------------------------------
  --------------------------------------------------------*)

val IMAP_def = Define `
  IMAP f init next =
    (!a. (f 0 a = init a)) /\
    (!t a. (f (SUC t) a = next (f t a)))`;

val IS_IMAP_def = Define`
  IS_IMAP f = ?init next. IMAP f init next`;

(*--------------------------------------------------------
  - Data Abstraction Criterion ---------------------------
  --------------------------------------------------------*)

val DATA_ABSTRACTION_def = Define `
  DATA_ABSTRACTION abs init init' =
    !a. ?b. abs (init' b) = init a`;

(*--------------------------------------------------------
  - Immersions : General, Uniform and Adjunct ------------
  --------------------------------------------------------*)

val IMMERSION_def = Define `
  IMMERSION imm =
    ((!a. imm a 0 = 0) /\
     (!a t1 t2. t1 < t2 ==> imm a t1 < imm a t2))`;

val UIMMERSION_def = Define `
  UIMMERSION imm f dur =
    ((!a. 0 < dur a) /\
     (!a. imm a 0 = 0) /\
     (!a t. imm a (SUC t) = dur (f (imm a t) a) + imm a t))`;

val AUIMMERSION_def = Define `
  AUIMMERSION imm1 imm2 f dur1 dur2 =
    ((UIMMERSION imm2 f dur2) /\
     (!a. 0 < dur1 a) /\
     (!a. imm1 a 0 = 0) /\
     (!a t. imm1 a (SUC t) = dur1 (f (imm2 a t) a) + imm1 a t))`;

val UNIFORM_def = Define`
  UNIFORM imm f = ?dur. UIMMERSION imm f dur`;

val ADJUNCT_def = Define`
  ADJUNCT imm1 imm2 f = ?dur1 dur2. AUIMMERSION imm1 imm2 f dur1 dur2`;

(*--------------------------------------------------------
  - Correctness Definitions ------------------------------
  --------------------------------------------------------*)

val CORRECT_def = Define `
  CORRECT spec impl imm abs =
    IMMERSION imm /\ DATA_ABSTRACTION abs (spec 0) (impl 0) /\
    (!t a. spec t (abs a) = abs (impl (imm a t) a))`;

val CORRECT_SUP_def = Define `
  CORRECT_SUP spec impl imm1 imm2 abs =
    IMMERSION imm1 /\ IMMERSION imm2 /\ DATA_ABSTRACTION abs (spec 0) (impl 0) /\
    (!r a. spec (imm1 a r) (abs a) = abs (impl (imm2 a r) a))`;

val IS_CORRECT_def = Define`
  IS_CORRECT spec impl = ?imm abs. CORRECT spec impl imm abs`;

val IS_CORRECT_SUP_def = Define`
  IS_CORRECT_SUP spec impl = ?imm1 imm2 abs. CORRECT_SUP spec impl imm1 imm2 abs`;
 
(*--------------------------------------------------------
  - Time-Consistent State Functions ----------------------
  --------------------------------------------------------*)

val TCON_def = Define `
  TCON f = !t1 t2 a. f (t1 + t2) a = f t1 (f t2 a)`;

val TCON_IMMERSION_def = Define `
  TCON_IMMERSION f imm =
    !t1 t2 a.
      f (imm (f (imm a t2) a) t1 + imm a t2) a =
      f (imm (f (imm a t2) a) t1) (f (imm a t2) a)`;

(*--------------------------------------------------------
  - Uniform Immersions are Immersions --------------------
  --------------------------------------------------------*)

val SUC_COMM_LEMMA = prove(
  `!t p. t + (SUC p + 1) = SUC (t + (p + 1))`,
  ARITH_TAC
);

val UIMMERSION_MONO_LEMMA = prove(
  `!imm f dur a t. UIMMERSION imm f dur ==> imm a t < imm a (SUC t)`,
  RW_TAC bool_ss [UIMMERSION_def,ADD_COMM,LESS_NOT_EQ,LESS_ADD_NONZERO]
);

val UIMMERSION_MONO_LEMMA2 = prove(
  `!imm f dur a t p. UIMMERSION imm f dur ==> imm a t < imm a (t + (p + 1))`,
  REPEAT STRIP_TAC
   THEN IMP_RES_TAC UIMMERSION_MONO_LEMMA
   THEN Induct_on `p`
   THENL [
     ASM_REWRITE_TAC [SYM ONE,GSYM ADD1,UIMMERSION_MONO_LEMMA],
     FULL_SIMP_TAC bool_ss  [SUC_COMM_LEMMA,LESS_IMP_LESS_ADD,ADD_COMM,UIMMERSION_def]
   ]
);

val UIMMERSION_IS_IMMERSION_LEMMA = store_thm("UIMMERSION_IS_IMMERSION_LEMMA",
  `!imm f dur. UIMMERSION imm f dur ==> IMMERSION imm`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC UIMMERSION_MONO_LEMMA2
    THEN FULL_SIMP_TAC bool_ss [UIMMERSION_def]
    THEN RW_TAC bool_ss [IMMERSION_def]
    THEN IMP_RES_TAC LESS_ADD_1
    THEN ASM_REWRITE_TAC [UIMMERSION_MONO_LEMMA2]
);

val UNIFORM_IMP_IMMERSION = store_thm("UNIFORM_IMP_IMMERSION",
  `!imm f. UNIFORM imm f ==> IMMERSION imm`,
  PROVE_TAC [UNIFORM_def,UIMMERSION_IS_IMMERSION_LEMMA]
);

(*--------------------------------------------------------
  - Uniform Adjunct Immersions are Immersions ------------
  --------------------------------------------------------*)

val AUIMMERSION_MONO_LEMMA = prove(
  `!f imm1 imm2 dur1 dur2 a t.
     AUIMMERSION imm1 imm2 f dur1 dur2 ==> imm1 a t < imm1 a (SUC t)`,
  RW_TAC bool_ss [AUIMMERSION_def,ADD_COMM,LESS_NOT_EQ,LESS_ADD_NONZERO]
);

val AUIMMERSION_MONO_LEMMA2 = prove(
  `!f imm1 imm2 dur1 dur2 a t p.
     AUIMMERSION imm1 imm2 f dur1 dur2 ==>imm1 a t < imm1 a (t + (p + 1))`,
  REPEAT STRIP_TAC
   THEN IMP_RES_TAC AUIMMERSION_MONO_LEMMA
   THEN Induct_on `p` THENL [
     ASM_REWRITE_TAC [SYM ONE,GSYM ADD1,AUIMMERSION_MONO_LEMMA],
     FULL_SIMP_TAC bool_ss [SUC_COMM_LEMMA,LESS_IMP_LESS_ADD,ADD_COMM,AUIMMERSION_def]
  ]
);

val AUIMMERSION_IS_IMMERSION_LEMMA = store_thm("AUIMMERSION_IS_IMMERSION_LEMMA",
  `!f imm1 imm2 dur1 dur2.
      AUIMMERSION imm1 imm2 f dur1 dur2 ==> IMMERSION imm1 /\ IMMERSION imm2`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC AUIMMERSION_MONO_LEMMA2
    THEN FULL_SIMP_TAC bool_ss [AUIMMERSION_def]
    THEN IMP_RES_TAC UIMMERSION_IS_IMMERSION_LEMMA
    THEN RW_TAC bool_ss [IMMERSION_def]
    THEN IMP_RES_TAC LESS_ADD_1
    THEN ASM_REWRITE_TAC [AUIMMERSION_MONO_LEMMA2]
);

val ADJUNCT_IMP_IMMERSIONS = store_thm("ADJUNCT_IMP_IMMERSIONS",
  `!imm1 imm2 f. ADJUNCT imm1 imm2 f ==> IMMERSION imm1 /\ IMMERSION imm2`,
  PROVE_TAC [ADJUNCT_def,AUIMMERSION_IS_IMMERSION_LEMMA]
);

(*--------------------------------------------------------
  - Correct then Super Correct ---------------------------
  --------------------------------------------------------*)

val CORRECT_IMP_CORRECT_SUP = store_thm("CORRECT_IMP_CORRECT_SUP",
  `!spec impl. IS_CORRECT spec impl ==> IS_CORRECT_SUP spec impl`,
  RW_TAC bool_ss [IS_CORRECT_def,IS_CORRECT_SUP_def]
    THEN EXISTS_TAC `\a t. t`
    THEN EXISTS_TAC `imm`
    THEN EXISTS_TAC `abs`
    THEN FULL_SIMP_TAC arith_ss [CORRECT_def,CORRECT_SUP_def,IMMERSION_def]
);

(*--------------------------------------------------------
  - Time-Consistency Results -----------------------------
  --------------------------------------------------------*)

val TC_IMP_IMAP = store_thm("TC_IMP_IMAP",
  `!f. TCON f ==> IS_IMAP f`,
  RW_TAC bool_ss [TCON_def,IMAP_def,IS_IMAP_def]
    THEN EXISTS_TAC `f 0`
    THEN EXISTS_TAC `f (SUC 0)`
    THEN POP_ASSUM (fn th => ASSUME_TAC (GEN_ALL (ONCE_REWRITE_RULE [ADD_COMM] (SPECL [`1`,`t`] th))))
    THEN ASM_REWRITE_TAC [ADD1,SYM ONE]
);

val TC_THM = store_thm("TC_THM",
  `!f. TCON f = IS_IMAP f /\ (!t a. f 0 (f t a) = f t a)`,
  STRIP_TAC THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL [
      PROVE_TAC [TC_IMP_IMAP],
      FULL_SIMP_TAC bool_ss [TCON_def]
        THEN POP_ASSUM (fn th => REWRITE_TAC [GSYM (REDUCE_RULE (SPECL [`0`,`t`] th))]),
      FULL_SIMP_TAC bool_ss [TCON_def,IS_IMAP_def,IMAP_def]
        THEN Induct_on `t1` THEN ASM_REWRITE_TAC [ADD_CLAUSES]
    ]
);

val TC_I_LEMMA = store_thm("TC_I_LEMMA",
  `!f next. IMAP f I next ==> TCON f`,
  PROVE_TAC [TC_THM,IS_IMAP_def,IMAP_def,I_THM]
);

val TC_IMP_TC_IMMERSION = store_thm("TC_IMP_TC_IMMERSION",
  `!f. TCON f ==> !imm. TCON_IMMERSION f imm`,
  RW_TAC bool_ss [TCON_def,TCON_IMMERSION_def]
);

val IMAP_INIT = store_thm("IMAP_INIT",
  `!f init next. IMAP f init next ==> (f 0 = init)`,
   RW_TAC bool_ss [IMAP_def,FUN_EQ_THM]
);

val STATE_FUNPOW_LEMMA = store_thm("STATE_FUNPOW_LEMMA",
  `!f init next. IMAP f init next ==> (!t a. f t a = FUNPOW next t (init a))`,
  REWRITE_TAC [IMAP_def]
   THEN REPEAT STRIP_TAC
   THEN Induct_on `t`
   THEN ASM_REWRITE_TAC [FUNPOW,FUNPOW_THM]
);

val STATE_FUNPOW_LEMMA2 = store_thm("STATE_FUNPOW_LEMMA2",
  `!f init next. IMAP f init next ==> (!t a. f t a = FUNPOW next t (f 0 a))`,
  PROVE_TAC [IMAP_INIT,STATE_FUNPOW_LEMMA]
);

val TC_IMMERSION_LEMMA = store_thm("TC_IMMERSION_LEMMA",
  `!f imm. IMMERSION imm /\ TCON_IMMERSION f imm ==> (!t a. f 0 (f (imm a t) a) = f (imm a t) a)`,
  RW_TAC bool_ss [TCON_IMMERSION_def,IMMERSION_def]
    THEN POP_ASSUM (fn th => ASSUME_TAC (SPECL [`0`,`t`,`a`] th))
    THEN PAT_ASSUM `!a. imm a 0 = 0` (fn th => RULE_ASSUM_TAC (SIMP_RULE arith_ss [th]))
    THEN POP_ASSUM (fn th => REWRITE_TAC [SYM th])
);

val TC_IMMERSION_LEMMA2 = store_thm("TC_IMMERSION_LEMMA2",
  `!f imm. IMMERSION imm /\ IS_IMAP f ==>
     (TCON_IMMERSION f imm = !t a. f 0 (f (imm a t) a) = f (imm a t) a)`,
  RW_TAC bool_ss [IS_IMAP_def,IMMERSION_def,TCON_IMMERSION_def]
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC THENL [
     POP_ASSUM (fn th => ASSUME_TAC (SPECL [`0`,`t`] th))
       THEN PAT_ASSUM `!a. imm a 0 = 0` (fn th => RULE_ASSUM_TAC (SIMP_RULE arith_ss [th]))
       THEN PROVE_TAC [],
     IMP_RES_TAC IMAP_INIT
       THEN POP_ASSUM (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]))
       THEN IMP_RES_TAC STATE_FUNPOW_LEMMA
       THEN ASSUME_TAC FUNPOW_COMP_LEMMA
       THEN ASM_REWRITE_TAC []
   ]
);

(*--------------------------------------------------------
  - Time-Consistency One-Step Theorems -------------------
  --------------------------------------------------------*)

val SPLIT_ITER_LEMMA = prove(
  `!f init next dur. IMAP f init next ==>
    (!t a. f (SUC t) a = (FUNPOW next 1 (f t a)))`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC STATE_FUNPOW_LEMMA
    THEN FULL_SIMP_TAC bool_ss [FUNPOW_COMP_LEMMA,UIMMERSION_def,ONE,
                                ADD_CLAUSES,FUNPOW,FUNPOW_THM]
);

val TC_ONE_STEP_THM = store_thm("TC_ONE_STEP_THM",
  `!f. TCON f =
         IS_IMAP f /\
         (!a. f 0 (f 0 a) = f 0 a) /\
         (!a. f 0 (f 1 a) = f 1 a)`,
  RW_TAC bool_ss [TC_THM]
    THEN EQ_TAC THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC []
    THEN FULL_SIMP_TAC bool_ss [IS_IMAP_def]
    THEN Induct_on `t`
    THENL [
      ASM_REWRITE_TAC [],
      IMP_RES_TAC SPLIT_ITER_LEMMA
        THEN POP_ASSUM (fn th => REWRITE_TAC [th])
        THEN PAT_ASSUM `f 0 (f t a) = f t a` (fn th => ONCE_REWRITE_TAC [SYM th])
        THEN IMP_RES_TAC IMAP_INIT
        THEN IMP_RES_TAC STATE_FUNPOW_LEMMA
        THEN POP_ASSUM (fn th => ASM_REWRITE_TAC [GSYM th])
        THEN POP_ASSUM (fn th => ASM_REWRITE_TAC [SYM th])
    ]
);

val SPLIT_ITER_LEMMA' = prove(
  `!f init next imm dur. IMAP f init next /\ UIMMERSION imm f dur ==>
    (!t a. f (dur (f 0 (f (imm a t) a)) + imm a t) a =
           FUNPOW next (imm (f (imm a t) a) 1) (f (imm a t) a))`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC STATE_FUNPOW_LEMMA
    THEN FULL_SIMP_TAC bool_ss [FUNPOW_COMP_LEMMA,UIMMERSION_def,ONE,
                                ADD_CLAUSES,FUNPOW,FUNPOW_THM]
);

val TC_IMMERSION_ONE_STEP_THM = store_thm("TC_IMMERSION_ONE_STEP_THM",
  `!f imm . IS_IMAP f /\ UNIFORM imm f ==>
    (TCON_IMMERSION f imm =
       (!a. f 0 (f (imm a 0) a) = f (imm a 0) a) /\
       (!a. f 0 (f (imm a 1) a) = f (imm a 1) a))`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC UNIFORM_IMP_IMMERSION
    THEN EQ_TAC THEN STRIP_TAC
    THEN ASM_SIMP_TAC bool_ss [TC_IMMERSION_LEMMA,TC_IMMERSION_LEMMA2]
    THEN Induct
    THENL [
      ASM_REWRITE_TAC [],
      GEN_TAC THEN FULL_SIMP_TAC bool_ss [UNIFORM_def,IS_IMAP_def]
        THEN PAT_ASSUM `UIMMERSION imm f dur`
             (fn th => REWRITE_TAC [REWRITE_RULE [UIMMERSION_def] th] THEN
             ASSUME_TAC th)
        THEN PAT_ASSUM `!a. f 0 (f (imm a t) a) = f (imm a t) a`
             (fn th => (ONCE_REWRITE_TAC [GSYM th] THEN ASSUME_TAC th))
        THEN IMP_RES_TAC SPLIT_ITER_LEMMA'
        THEN POP_ASSUM (fn th => REWRITE_TAC [th])
        THEN POP_ASSUM (fn th => (ONCE_REWRITE_TAC [GSYM th] THEN
             ASSUME_TAC th))
        THEN IMP_RES_TAC STATE_FUNPOW_LEMMA2
        THEN POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
        THEN ASM_REWRITE_TAC []
    ]
);

(*--------------------------------------------------------
  - Correctnes One-Step Theorems -------------------------
  --------------------------------------------------------*)

val ONE_STEP_LEMMA = prove(
  `!f imm dur.
     UNIFORM imm f /\ TCON_IMMERSION f imm ==>
     (!t a. imm a (SUC t) = (imm (f (imm a t) a) 1 + imm a t))`,
  REPEAT STRIP_TAC
   THEN IMP_RES_TAC UNIFORM_IMP_IMMERSION
   THEN IMP_RES_TAC TC_IMMERSION_LEMMA
   THEN FULL_SIMP_TAC bool_ss [UNIFORM_def,UIMMERSION_def,ONE,ADD_CLAUSES]
);

val ONE_STEP_THM = store_thm("ONE_STEP_THM",
  `!spec impl imm abs.
      (UNIFORM imm impl /\
       TCON spec /\
       TCON_IMMERSION impl imm) ==>
      (CORRECT spec impl imm abs =
        DATA_ABSTRACTION abs (spec 0) (impl 0) /\
        (!a. spec 0 (abs a) = abs (impl (imm a 0) a)) /\
         !a. spec 1 (abs a) = abs (impl (imm a 1) a))`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC ONE_STEP_LEMMA
    THEN EQ_TAC
    THEN RW_TAC bool_ss [CORRECT_def]
    THENL [
       IMP_RES_TAC UNIFORM_IMP_IMMERSION,
       Induct_on `t` THENL [
         ASM_REWRITE_TAC [],
         PAT_ASSUM `!t a. imm a (SUC t) = imm (impl (imm a t) a) 1 + imm a t`
           (fn th => REWRITE_TAC [th])
           THEN PAT_ASSUM `TCON_IMMERSION impl imm`
                (fn th => REWRITE_TAC [REWRITE_RULE [TCON_IMMERSION_def] th])
           THEN PAT_ASSUM `!a. spec 1 (abs a) = abs (impl (imm a 1) a)`
                (fn th => REWRITE_TAC [ONE,GSYM th])
           THEN POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
           THEN RULE_ASSUM_TAC (REWRITE_RULE [TCON_def])
           THEN PAT_ASSUM `!t1 t2 a. spec (t1 + t2) a = spec t1 (spec t2 a)`
                (fn th => REWRITE_TAC [SYM ONE,GSYM (SPECL [`SUC 0`,`t`] th)])
           THEN SIMP_TAC arith_ss [ADD1]
       ]
    ]
);

(* --------------------------------------------------------*)

val IMAP_COMP = store_thm("IMAP_COMP",
  `!f init next. IMAP f init next ==>
     (!t a. f t a = if t = 0 then init a else next (f (t-1) a))`,
   REPEAT STRIP_TAC THEN FULL_SIMP_TAC bool_ss [IMAP_def]
    THEN RW_TAC bool_ss []
    THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_ZERO_LT_ZERO])
    THEN IMP_RES_TAC LESS_ADD_1
    THEN RW_TAC arith_ss [GSYM ADD1]
);

val UIMMERSION_ONE = store_thm("UIMMERSION_ONE",
  `!f init next imm dur.
     IMAP f init next /\ UIMMERSION imm f dur ==>
     !a. imm a 1 = dur (init a)`,
  RW_TAC bool_ss [UIMMERSION_def,IMAP_def,ONE,ADD_0]
);

(* --------------------------------------------------------*)
(* --------------------------------------------------------*)

val _ = export_theory();
