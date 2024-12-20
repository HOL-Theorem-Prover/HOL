(* ========================================================================= *)
(* FILE          : onestepScript.sml                                         *)
(* DESCRIPTION   : Algebraic framework for verifying processor correctness   *)
(*                                                                           *)
(* AUTHOR        : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2000 - 2004                                               *)
(* ========================================================================= *)

open HolKernel boolLib bossLib Q;
open simpLib numLib;
open combinTheory arithmeticTheory prim_recTheory pred_setTheory;

val _ = new_theory "onestep";

(* ------------------------------------------------------------------------- *)

val FUNPOW_THM = store_thm("FUNPOW_THM",
  `!f n x. FUNPOW f n (f x) = f (FUNPOW f n x)`,
  Induct_on `n` \\ ASM_REWRITE_TAC [FUNPOW]);

val FUNPOW_EVAL = store_thm("FUNPOW_EVAL",
  `!f n x. FUNPOW f n x = if n = 0 then x else FUNPOW f (n-1) (f x)`,
  Induct_on `n` \\ RW_TAC arith_ss [FUNPOW]);

val FUNPOW_COMP = store_thm("FUNPOW_COMP",
  `!f a b x. FUNPOW f (a+b) x = FUNPOW f a (FUNPOW f b x)`,
  Induct_on `b` \\ ASM_REWRITE_TAC [ADD_CLAUSES,FUNPOW]);

(*---------------------------------------------------------------------------
  - Iterated Maps -----------------------------------------------------------
  ---------------------------------------------------------------------------*)

val IMAP_def = Define `
  IMAP f init next <=>
    (!a. (f 0 a = init a)) /\
    (!t a. (f (SUC t) a = next (f t a)))`;

val IS_IMAP_INIT_def = Define`
  IS_IMAP_INIT f init = ?next. IMAP f init next`;

val IS_IMAP_def = Define`
  IS_IMAP f = ?init next. IMAP f init next`;

(*---------------------------------------------------------------------------
  - Data Abstraction Criterion ----------------------------------------------
  ---------------------------------------------------------------------------*)

val RANGE_def = Define`RANGE f = IMAGE f UNIV`;

val DATA_ABSTRACTION_def = Define `
  DATA_ABSTRACTION abs initi inits =
  SURJ abs (RANGE initi) (RANGE inits)`;

(*---------------------------------------------------------------------------
  - Immersions : General, Uniform and Adjunct -------------------------------
  ---------------------------------------------------------------------------*)

val FREE_IMMERSION_def = Define`
  FREE_IMMERSION imm =
    ((imm 0 = 0) /\
    (!t1 t2. t1 < t2 ==> imm t1 < imm t2))`;

val IMMERSION_def = Define `
  IMMERSION imm = !a. FREE_IMMERSION (imm a)`;

val IMMERSION = REWRITE_RULE [FREE_IMMERSION_def] IMMERSION_def;

(*
val IMMERSION =
  (CONV_RULE (DEPTH_CONV FORALL_AND_CONV) o
   REWRITE_RULE [FREE_IMMERSION_def]) IMMERSION_def;
*)

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

(*---------------------------------------------------------------------------
  - Correctness Definitions -------------------------------------------------
  ---------------------------------------------------------------------------*)

val CORRECT_def = Define `
  CORRECT spec impl imm abs <=>
    IMMERSION imm /\ DATA_ABSTRACTION abs (impl 0) (spec 0) /\
    (!t a. spec t (abs a) = abs (impl (imm a t) a))`;

val CORRECT_SUP_def = Define `
  CORRECT_SUP spec impl imm1 imm2 abs <=>
    IMMERSION imm1 /\ IMMERSION imm2 /\
    DATA_ABSTRACTION abs (impl 0) (spec 0) /\
    (!r a. spec (imm1 a r) (abs a) = abs (impl (imm2 a r) a))`;

val IS_CORRECT_def = Define`
  IS_CORRECT spec impl = ?imm abs. CORRECT spec impl imm abs`;

val IS_CORRECT_SUP_def = Define`
  IS_CORRECT_SUP spec impl =
    ?imm1 imm2 abs. CORRECT_SUP spec impl imm1 imm2 abs`;

(*---------------------------------------------------------------------------
  - Time-Consistent State Functions -----------------------------------------
  ---------------------------------------------------------------------------*)

val TCON_def = Define `
  TCON f = !t1 t2 a. f (t1 + t2) a = f t1 (f t2 a)`;

val TCON_IMMERSION_def = Define `
  TCON_IMMERSION f imm =
    !t1 t2 a.
      f (imm (f (imm a t2) a) t1 + imm a t2) a =
      f (imm (f (imm a t2) a) t1) (f (imm a t2) a)`;

(*---------------------------------------------------------------------------
  - Data Abstraction Id -----------------------------------------------------
  ---------------------------------------------------------------------------*)

val DATA_ABSTRACTION_I = store_thm("DATA_ABSTRACTION_I",
  `!abs initi. DATA_ABSTRACTION abs initi I = (!a. ?b. abs (initi b) = a)`,
  RW_TAC std_ss [DATA_ABSTRACTION_def,RANGE_def,IMAGE_DEF,SURJ_DEF,
    IN_UNIV,GSPECIFICATION] \\ PROVE_TAC []);

(*---------------------------------------------------------------------------
  - Uniform Immersions are Immersions ---------------------------------------
  ---------------------------------------------------------------------------*)

val SUC_COMM_LEMMA = prove(
  `!t p. t + (SUC p + 1) = SUC (t + (p + 1))`, ARITH_TAC);

val UIMMERSION_MONO_LEMMA = prove(
  `!imm f dur a t. UIMMERSION imm f dur ==> imm a t < imm a (SUC t)`,
  RW_TAC bool_ss [UIMMERSION_def,ADD_COMM,LESS_NOT_EQ,LESS_ADD_NONZERO]);

val UIMMERSION_MONO_LEMMA2 = prove(
  `!imm f dur a t p. UIMMERSION imm f dur ==> imm a t < imm a (t + (p + 1))`,
  REPEAT STRIP_TAC
   \\ IMP_RES_TAC UIMMERSION_MONO_LEMMA
   \\ Induct_on `p`
   >- ASM_REWRITE_TAC [SYM ONE,GSYM ADD1,UIMMERSION_MONO_LEMMA]
   \\ FULL_SIMP_TAC bool_ss
        [SUC_COMM_LEMMA,LESS_IMP_LESS_ADD,ADD_COMM,UIMMERSION_def]);

val UIMMERSION_IS_IMMERSION_LEMMA = store_thm("UIMMERSION_IS_IMMERSION_LEMMA",
  `!imm f dur. UIMMERSION imm f dur ==> IMMERSION imm`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC UIMMERSION_MONO_LEMMA2
    \\ FULL_SIMP_TAC bool_ss [UIMMERSION_def]
    \\ RW_TAC bool_ss [IMMERSION]
    \\ IMP_RES_TAC LESS_ADD_1
    \\ ASM_REWRITE_TAC [UIMMERSION_MONO_LEMMA2]);

val UNIFORM_IMP_IMMERSION = store_thm("UNIFORM_IMP_IMMERSION",
  `!imm f. UNIFORM imm f ==> IMMERSION imm`,
  PROVE_TAC [UNIFORM_def,UIMMERSION_IS_IMMERSION_LEMMA]);

(*---------------------------------------------------------------------------
  - Uniform Adjunct Immersions are Immersions -------------------------------
  ---------------------------------------------------------------------------*)

val AUIMMERSION_MONO_LEMMA = prove(
  `!f imm1 imm2 dur1 dur2 a t.
     AUIMMERSION imm1 imm2 f dur1 dur2 ==> imm1 a t < imm1 a (SUC t)`,
  RW_TAC bool_ss [AUIMMERSION_def,ADD_COMM,LESS_NOT_EQ,LESS_ADD_NONZERO]);

val AUIMMERSION_MONO_LEMMA2 = prove(
  `!f imm1 imm2 dur1 dur2 a t p.
     AUIMMERSION imm1 imm2 f dur1 dur2 ==>imm1 a t < imm1 a (t + (p + 1))`,
  REPEAT STRIP_TAC
   \\ IMP_RES_TAC AUIMMERSION_MONO_LEMMA
   \\ Induct_on `p`
   >- ASM_REWRITE_TAC [SYM ONE,GSYM ADD1,AUIMMERSION_MONO_LEMMA]
   \\ FULL_SIMP_TAC bool_ss
        [SUC_COMM_LEMMA,LESS_IMP_LESS_ADD,ADD_COMM,AUIMMERSION_def]);

val AUIMMERSION_IS_IMMERSION_LEMMA = store_thm("AUIMMERSION_IS_IMMERSION_LEMMA",
  `!f imm1 imm2 dur1 dur2.
      AUIMMERSION imm1 imm2 f dur1 dur2 ==> IMMERSION imm1 /\ IMMERSION imm2`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC AUIMMERSION_MONO_LEMMA2
    \\ FULL_SIMP_TAC bool_ss [AUIMMERSION_def]
    \\ IMP_RES_TAC UIMMERSION_IS_IMMERSION_LEMMA
    \\ RW_TAC bool_ss [IMMERSION]
    \\ IMP_RES_TAC LESS_ADD_1
    \\ ASM_REWRITE_TAC [AUIMMERSION_MONO_LEMMA2]);

val ADJUNCT_IMP_IMMERSIONS = store_thm("ADJUNCT_IMP_IMMERSIONS",
  `!imm1 imm2 f. ADJUNCT imm1 imm2 f ==> IMMERSION imm1 /\ IMMERSION imm2`,
  PROVE_TAC [ADJUNCT_def,AUIMMERSION_IS_IMMERSION_LEMMA]);

val ADJUNCT_IMP_UNIFORM = store_thm("ADJUNCT_IMP__UNIFORM",
  `!imm1 imm2 f. ADJUNCT imm1 imm2 f ==> UNIFORM imm2 f`,
  PROVE_TAC [ADJUNCT_def,UNIFORM_def,AUIMMERSION_def]);

(*---------------------------------------------------------------------------
  - Correct then Super Correct ----------------------------------------------
  ---------------------------------------------------------------------------*)

val CORRECT_IMP_CORRECT_SUP = store_thm("CORRECT_IMP_CORRECT_SUP",
  `!spec impl. IS_CORRECT spec impl ==> IS_CORRECT_SUP spec impl`,
  RW_TAC bool_ss [IS_CORRECT_def,IS_CORRECT_SUP_def]
    \\ EXISTS_TAC `\a t. t`
    \\ EXISTS_TAC `imm`
    \\ EXISTS_TAC `abs`
    \\ FULL_SIMP_TAC arith_ss [CORRECT_def,CORRECT_SUP_def,IMMERSION]);

(*---------------------------------------------------------------------------
  - Iterated Maps Unique  ---------------------------------------------------
  ---------------------------------------------------------------------------*)

val IMAP_UNIQUE1 = store_thm("IMAP_UNIQUE1",
  `!f g init next. IMAP f init next /\ IMAP g init next ==> (f = g)`,
  RW_TAC bool_ss [IMAP_def]
    \\ ONCE_REWRITE_TAC [FUN_EQ_THM]
    \\ Induct
    \\ ONCE_REWRITE_TAC [FUN_EQ_THM]
    \\ ASM_REWRITE_TAC []);

(*---------------------------------------------------------------------------
  - Time-Consistency Results ------------------------------------------------
  ---------------------------------------------------------------------------*)

val TC_IMP_IMAP = store_thm("TC_IMP_IMAP",
  `!f. TCON f ==> IS_IMAP f`,
  RW_TAC bool_ss [TCON_def,IMAP_def,IS_IMAP_def]
    \\ EXISTS_TAC `f 0`
    \\ EXISTS_TAC `f (SUC 0)`
    \\ POP_ASSUM (fn th => ASSUME_TAC
         (GEN_ALL (ONCE_REWRITE_RULE [ADD_COMM] (SPECL [`1`,`t`] th))))
    \\ ASM_REWRITE_TAC [ADD1,SYM ONE]);

val TC_THM = store_thm("TC_THM",
  `!f. TCON f <=> IS_IMAP f /\ (!t a. f 0 (f t a) = f t a)`,
  STRIP_TAC \\ EQ_TAC
    \\ REPEAT STRIP_TAC
    THENL [
      PROVE_TAC [TC_IMP_IMAP],
      FULL_SIMP_TAC bool_ss [TCON_def]
        \\ POP_ASSUM (fn th => REWRITE_TAC
             [GSYM (REDUCE_RULE (SPECL [`0`,`t`] th))]),
      FULL_SIMP_TAC bool_ss [TCON_def,IS_IMAP_def,IMAP_def]
        \\ Induct_on `t1` \\ ASM_REWRITE_TAC [ADD_CLAUSES]]);

val TC_I_THM = store_thm("TC_I_THM",
  `!f. IS_IMAP_INIT f I ==> TCON f`,
  PROVE_TAC [TC_THM,IS_IMAP_def,IS_IMAP_INIT_def,IMAP_def,I_THM]);

val TC_IMP_TC_IMMERSION = store_thm("TC_IMP_TC_IMMERSION",
  `!f. TCON f ==> !imm. TCON_IMMERSION f imm`,
  RW_TAC bool_ss [TCON_def,TCON_IMMERSION_def]);

val TC_IMMERSION_TC = store_thm("TC_IMMERSION_TC",
  `!f. TCON_IMMERSION f (\a t. t) = TCON f`,
  STRIP_TAC \\ EQ_TAC \\
    SIMP_TAC bool_ss [TC_IMP_TC_IMMERSION,TCON_def,TCON_IMMERSION_def]);

val IMAP_INIT = store_thm("IMAP_INIT",
  `!f init. IS_IMAP_INIT f init ==> (f 0 = init)`,
   RW_TAC bool_ss [IS_IMAP_INIT_def,IMAP_def,FUN_EQ_THM]);

val STATE_FUNPOW_ADD = store_thm("STATE_FUNPOW_ADD",
  `!f init next. IMAP f init next ==>
      (!x y a. f (x + y) a = FUNPOW next x (f y a))`,
  RW_TAC bool_ss [IMAP_def]
   \\ Induct_on `x`
   \\ ASM_REWRITE_TAC [ADD,FUNPOW,FUNPOW_THM]);

val STATE_FUNPOW_ZERO = store_thm("STATE_FUNPOW_ZERO",
  `!f init next. IMAP f init next ==> (!t a. f t a = FUNPOW next t (f 0 a))`,
  PROVE_TAC [ADD_0,STATE_FUNPOW_ADD]);

val STATE_FUNPOW_INIT = store_thm("STATE_FUNPOW_INIT",
  `!f init next. IMAP f init next ==> (!t a. f t a = FUNPOW next t (init a))`,
  PROVE_TAC [STATE_FUNPOW_ZERO,IMAP_def]);

val TC_IMMERSION_LEMMA = store_thm("TC_IMMERSION_LEMMA",
  `!f imm. IMMERSION imm /\ TCON_IMMERSION f imm ==>
       (!t a. f 0 (f (imm a t) a) = f (imm a t) a)`,
  RW_TAC bool_ss [TCON_IMMERSION_def,IMMERSION]
    \\ POP_ASSUM (fn th => ASSUME_TAC (SPECL [`0`,`t`,`a`] th))
    \\ PAT_ASSUM `!a. P` (fn th => RULE_ASSUM_TAC (SIMP_RULE arith_ss [th]))
    \\ POP_ASSUM (fn th => REWRITE_TAC [SYM th]));

val TC_IMMERSION_LEMMA2 = store_thm("TC_IMMERSION_LEMMA2",
  `!f imm. IMMERSION imm /\ IS_IMAP f ==>
     (TCON_IMMERSION f imm = !t a. f 0 (f (imm a t) a) = f (imm a t) a)`,
  RW_TAC bool_ss [IS_IMAP_def,IMMERSION,TCON_IMMERSION_def]
   \\ EQ_TAC
   \\ REPEAT STRIP_TAC THENL [
     POP_ASSUM (fn th => ASSUME_TAC (SPECL [`0`,`t`] th))
       \\ PAT_ASSUM `!a. x /\ y`
            (fn th => RULE_ASSUM_TAC (SIMP_RULE arith_ss [th]))
       \\ PROVE_TAC [],
     `IS_IMAP_INIT f init` by PROVE_TAC [IS_IMAP_INIT_def]
       \\ IMP_RES_TAC IMAP_INIT
       \\ POP_ASSUM (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]))
       \\ IMP_RES_TAC STATE_FUNPOW_INIT
       \\ ASSUME_TAC FUNPOW_COMP
       \\ ASM_REWRITE_TAC []]);

(* ------------------------------------------------------------------------- *)

val TC_IMM_LEM = store_thm("TC_IMM_LEM",
  `!f g imm dur.
     TCON_IMMERSION f imm /\ UIMMERSION imm f dur /\
     IMAP g (f 0) (\a. f (dur a) a) ==>
     !t a. g t a = f (imm a t) a`,
  NTAC 5 STRIP_TAC
    \\ FULL_SIMP_TAC bool_ss [UIMMERSION_def,IMAP_def,TCON_IMMERSION_def]
    \\ Induct \\ STRIP_TAC
    \\ ASM_REWRITE_TAC []
    \\ PAT_ASSUM `!t1 t2 a.
            f (imm (f (imm a t2) a) t1 + imm a t2) a =
            f (imm (f (imm a t2) a) t1) (f (imm a t2) a)`
         (fn th => ASSUME_TAC (SPECL [`1`,`t`,`a`] th)
              \\ ASSUME_TAC (SPECL [`0`,`t`] th))
    \\ PAT_ASSUM `!a t. imm a (SUC t) = dur (f (imm a t) a) + imm a t`
         (fn th => ASSUME_TAC (REDUCE_RULE (GEN_ALL (SPECL [`a`,`0`] th))))
    \\ PAT_ASSUM `!a. imm a 0 = 0` (fn th => FULL_SIMP_TAC arith_ss [th])
    \\ PAT_ASSUM `!a. f (imm a t) a = f 0 (f (imm a t) a)`
         (fn th => FULL_SIMP_TAC bool_ss [GSYM th]));

val TC_IMMERSION_THM = store_thm("TC_IMMERSION_THM",
  `!f g imm dur.
           UIMMERSION imm f dur /\
           IMAP g (f 0) (\a. f (dur a) a) ==>
           (TCON_IMMERSION f imm ==> TCON g)`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC UIMMERSION_IS_IMMERSION_LEMMA
    \\ IMP_RES_TAC TC_IMMERSION_LEMMA
    \\ FULL_SIMP_TAC bool_ss [IS_IMAP_def,TC_THM]
    \\ STRIP_TAC >- PROVE_TAC []
    \\ IMP_RES_TAC TC_IMM_LEM \\ FULL_SIMP_TAC bool_ss [IMAP_def]);

(*---------------------------------------------------------------------------
  - Time-Consistency One-Step Theorems --------------------------------------
  ---------------------------------------------------------------------------*)

val SPLIT_ITER_LEMMA = prove(
  `!f init next imm dur. IMAP f init next /\ UIMMERSION imm f dur ==>
    (!t a. f (dur (f 0 (f (imm a t) a)) + imm a t) a =
           FUNPOW next (imm (f (imm a t) a) 1) (f (imm a t) a))`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC STATE_FUNPOW_INIT
    \\ FULL_SIMP_TAC bool_ss
         [FUNPOW_COMP,UIMMERSION_def,ONE,ADD_CLAUSES,FUNPOW,FUNPOW_THM]);

val TC_IMMERSION_ONE_STEP_THM = store_thm("TC_IMMERSION_ONE_STEP_THM",
  `!f imm . IS_IMAP f /\ UNIFORM imm f ==>
    (TCON_IMMERSION f imm <=>
       (!a. f 0 (f (imm a 0) a) = f (imm a 0) a) /\
       (!a. f 0 (f (imm a 1) a) = f (imm a 1) a))`,
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC UNIFORM_IMP_IMMERSION
    \\ EQ_TAC \\ STRIP_TAC
    \\ ASM_SIMP_TAC bool_ss [TC_IMMERSION_LEMMA,TC_IMMERSION_LEMMA2]
    \\ Induct >- ASM_REWRITE_TAC []
    \\ GEN_TAC \\ FULL_SIMP_TAC bool_ss [UNIFORM_def,IS_IMAP_def]
    \\ PAT_ASSUM `UIMMERSION imm f dur` (fn th =>
          REWRITE_TAC [REWRITE_RULE [UIMMERSION_def] th] \\ ASSUME_TAC th)
    \\ PAT_ASSUM `!a. f 0 (f (imm a t) a) = f (imm a t) a`
         (fn th => (ONCE_REWRITE_TAC [GSYM th] \\ ASSUME_TAC th))
    \\ IMP_RES_TAC SPLIT_ITER_LEMMA
    \\ POP_ASSUM (fn th => REWRITE_TAC [th])
    \\ POP_ASSUM (fn th => (ONCE_REWRITE_TAC [GSYM th] \\ ASSUME_TAC th))
    \\ IMP_RES_TAC STATE_FUNPOW_ZERO
    \\ POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
    \\ ASM_REWRITE_TAC []);

val UNIFORM_ID = prove(
  `!f. UNIFORM (\a t. t) f`,
  RW_TAC bool_ss [UNIFORM_def] \\ EXISTS_TAC `\a. 1`
    \\ REWRITE_TAC [UIMMERSION_def] \\ SIMP_TAC arith_ss []);

Theorem TC_ONE_STEP_THM:
  !f. TCON f <=>
        IS_IMAP f /\ (!a. f 0 (f 0 a) = f 0 a) /\ (!a. f 0 (f 1 a) = f 1 a)
Proof
  PROVE_TAC [TC_IMP_IMAP,
    (SIMP_RULE std_ss [UNIFORM_ID,TC_IMMERSION_TC] o
     SPECL [`f`,`\a t. t`]) TC_IMMERSION_ONE_STEP_THM]
QED

val TCON_IMMERSION_COR = store_thm("TCON_IMMERSION_COR",
  `!f imm.
     UNIFORM imm f /\ TCON_IMMERSION f imm ==>
       !t1 t2 a. imm a (t1 + t2) = imm (f (imm a t1) a) t2 + imm a t1`,
  RW_TAC bool_ss [UNIFORM_def,UIMMERSION_def,TCON_IMMERSION_def]
    \\ Induct_on `t2` \\ ASM_REWRITE_TAC [ADD_CLAUSES]
    \\ numLib.ARITH_TAC);

(*---------------------------------------------------------------------------
  - Correctnes One-Step Theorems --------------------------------------------
  ---------------------------------------------------------------------------*)

val ONE_STEP_LEMMA = prove(
  `!f imm dur.
     UNIFORM imm f /\ TCON_IMMERSION f imm ==>
     (!t a. imm a (SUC t) = (imm (f (imm a t) a) 1 + imm a t))`,
  REPEAT STRIP_TAC
   \\ IMP_RES_TAC UNIFORM_IMP_IMMERSION
   \\ IMP_RES_TAC TC_IMMERSION_LEMMA
   \\ FULL_SIMP_TAC bool_ss [UNIFORM_def,UIMMERSION_def,ONE,ADD_CLAUSES]);

Theorem ONE_STEP_THM:
  !spec impl imm abs.
       UNIFORM imm impl /\
       TCON spec /\
       TCON_IMMERSION impl imm /\
       DATA_ABSTRACTION abs (impl 0) (spec 0) ==>
      (CORRECT spec impl imm abs <=>
        (!a. spec 0 (abs a) = abs (impl (imm a 0) a)) /\
         !a. spec 1 (abs a) = abs (impl (imm a 1) a))
Proof
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC ONE_STEP_LEMMA
    \\ EQ_TAC
    \\ RW_TAC bool_ss [CORRECT_def]
    >- IMP_RES_TAC UNIFORM_IMP_IMMERSION
    \\ Induct_on `t` >- ASM_REWRITE_TAC []
    \\ PAT_ASSUM `!t a. imm a (SUC t) = imm (impl (imm a t) a) 1 + imm a t`
         (fn th => REWRITE_TAC [th])
    \\ PAT_ASSUM `TCON_IMMERSION impl imm`
         (fn th => REWRITE_TAC [REWRITE_RULE [TCON_IMMERSION_def] th])
    \\ PAT_ASSUM `!a. spec 1 (abs a) = abs (impl (imm a 1) a)`
         (fn th => REWRITE_TAC [ONE,GSYM th])
    \\ POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
    \\ RULE_ASSUM_TAC (REWRITE_RULE [TCON_def])
    \\ PAT_ASSUM `!t1 t2 a. spec (t1 + t2) a = spec t1 (spec t2 a)`
         (fn th => REWRITE_TAC [SYM ONE,GSYM (SPECL [`SUC 0`,`t`] th)])
    \\ SIMP_TAC arith_ss [ADD1]
QED

(* ------------------------------------------------------------------------- *)

val ONE_STEP_SUP_LEMMA = prove(
  `!f imm1 imm2.  ADJUNCT imm1 imm2 f /\ TCON_IMMERSION f imm2 ==>
      (!r a. imm1 a (SUC r) = (imm1 (f (imm2 a r) a) 1 + imm1 a r))`,
  REPEAT STRIP_TAC
   \\ IMP_RES_TAC ADJUNCT_IMP_IMMERSIONS
   \\ IMP_RES_TAC TC_IMMERSION_LEMMA
   \\ FULL_SIMP_TAC bool_ss
        [ADJUNCT_def,UIMMERSION_def,AUIMMERSION_def,ONE,ADD_CLAUSES]);

Theorem ONE_STEP_SUP_THM:
  !spec impl imm1 imm2 abs.
      (ADJUNCT imm1 imm2 impl /\
       TCON spec /\
       TCON_IMMERSION impl imm2) ==>
      (CORRECT_SUP spec impl imm1 imm2 abs <=>
        DATA_ABSTRACTION abs (impl 0) (spec 0) /\
        (!a. spec (imm1 a 0) (abs a) = abs (impl (imm2 a 0) a)) /\
         !a. spec (imm1 a 1) (abs a) = abs (impl (imm2 a 1) a))
Proof
  REPEAT STRIP_TAC
    \\ IMP_RES_TAC ADJUNCT_IMP_UNIFORM
    \\ EQ_TAC
    \\ RW_TAC bool_ss [CORRECT_SUP_def]
    THENL [
       IMP_RES_TAC ADJUNCT_IMP_IMMERSIONS,
       IMP_RES_TAC ADJUNCT_IMP_IMMERSIONS,
       Induct_on `r` >- ASM_REWRITE_TAC []
         \\ IMP_RES_TAC ONE_STEP_SUP_LEMMA
         \\ POP_ASSUM (fn th => REWRITE_TAC [th])
         \\ IMP_RES_TAC ONE_STEP_LEMMA
         \\ REWRITE_TAC [ONE]
         \\ POP_ASSUM (fn th => REWRITE_TAC [th])
         \\ PAT_ASSUM `TCON_IMMERSION impl imm2`
              (fn th => REWRITE_TAC [REWRITE_RULE [TCON_IMMERSION_def] th])
         \\ PAT_ASSUM `!a. spec (imm1 a 1) (abs a) = abs (impl (imm2 a 1) a)`
              (fn th => REWRITE_TAC [ONE,GSYM th])
         \\ RULE_ASSUM_TAC (REWRITE_RULE [TCON_def])
         \\ POP_ASSUM (fn th => ASM_REWRITE_TAC [GSYM th])]
QED

(* ------------------------------------------------------------------------- *)

val CORRECT_TRANS = store_thm("CORRECT_TRANS",
  `!f1 f2 f3 imm1 imm2 abs1 abs2.
     CORRECT f1 f2 imm1 abs1 /\ CORRECT f2 f3 imm2 abs2 ==>
     CORRECT f1 f3 (\x. imm2 x o imm1 (abs2 x)) (abs1 o abs2)`,
  RW_TAC bool_ss [CORRECT_def,IMMERSION,DATA_ABSTRACTION_def,o_THM,
                  SURJ_DEF,RANGE_def,IMAGE_DEF,IN_UNIV,GSPECIFICATION]
    \\ PROVE_TAC []);

(* ------------------------------------------------------------------------- *)

val IMAP_COMP = store_thm("IMAP_COMP",
  `!f init next. IMAP f init next ==>
     (!t a. f t a = if t = 0 then init a else next (f (t-1) a))`,
   REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [IMAP_def]
    \\ RW_TAC bool_ss []
    \\ RULE_ASSUM_TAC (REWRITE_RULE [NOT_ZERO_LT_ZERO])
    \\ IMP_RES_TAC LESS_ADD_1
    \\ RW_TAC arith_ss [GSYM ADD1]);

val UIMMERSION_COMP = prove(
  `!imm f dur. UIMMERSION imm f dur ==>
     (!t a. imm a t =
         if t = 0 then 0
         else dur (f (imm a (t-1)) a) + imm a (t-1))`,
   REPEAT STRIP_TAC \\ FULL_SIMP_TAC bool_ss [UIMMERSION_def]
    \\ RW_TAC bool_ss [UIMMERSION_def]
    \\ RULE_ASSUM_TAC (REWRITE_RULE [NOT_ZERO_LT_ZERO])
    \\ IMP_RES_TAC LESS_ADD_1
    \\ RW_TAC arith_ss [GSYM ADD1]);

val UIMMERSION_ONE = store_thm("UIMMERSION_ONE",
  `!f init next imm dur.
     IS_IMAP_INIT f init /\ UIMMERSION imm f dur ==>
     !a. imm a 1 = dur (init a)`,
  RW_TAC bool_ss [UIMMERSION_def,IS_IMAP_INIT_def,IMAP_def,ONE,ADD_0]
    \\ ASM_REWRITE_TAC []);

val IMAP_NEXT = store_thm("IMAP_NEXT",
  `!f init next. IMAP f init next ==>
      (f t a = b) /\ (next b = c) ==>
      (f (t + 1) a = c)`,
  RW_TAC std_ss [IMAP_def,ADD1]
);

(* ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ *)

val _ = export_theory();
