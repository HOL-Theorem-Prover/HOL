open HolKernel boolLib Parse bossLib


open ltlTheory full_ltlTheory prop_logicTheory
open Temporal_LogicTheory Past_Temporal_LogicTheory

val _ = new_theory "ltl_translations"

(************************************************************)
(* Translation examples/logic/ltl -> examples/temporal_deep *)
(************************************************************)

val LOGIC_TO_TEMPORAL_DEEP_def = Define `
  (LOGIC_TO_TEMPORAL_DEEP (F_VAR v) = (LTL_PROP (P_PROP v))) /\
  (LOGIC_TO_TEMPORAL_DEEP (F_CONJ l1 l2) = (LTL_AND (LOGIC_TO_TEMPORAL_DEEP l1, LOGIC_TO_TEMPORAL_DEEP l2))) /\
  (LOGIC_TO_TEMPORAL_DEEP (F_NEG l) = (LTL_NOT (LOGIC_TO_TEMPORAL_DEEP l))) /\
  (LOGIC_TO_TEMPORAL_DEEP (F_X l) = (LTL_NEXT (LOGIC_TO_TEMPORAL_DEEP l))) /\
  (LOGIC_TO_TEMPORAL_DEEP (F_U l1 l2) = (LTL_SUNTIL (LOGIC_TO_TEMPORAL_DEEP l1, LOGIC_TO_TEMPORAL_DEEP l2)))`;


val IS_FUTURE_LTL___LOGIC_TO_TEMPORAL_DEEP = store_thm("IS_FUTURE_LTL___LOGIC_TO_TEMPORAL_DEEP",
  ``!l. IS_FUTURE_LTL (LOGIC_TO_TEMPORAL_DEEP l)``,

Induct_on `l` >> (
  ASM_SIMP_TAC std_ss [LOGIC_TO_TEMPORAL_DEEP_def, IS_FUTURE_LTL_def]
));


val LOGIC_TO_TEMPORAL_DEEP___SEM_TIME = store_thm ("LOGIC_TO_TEMPORAL_DEEP___SEM_TIME",
``!l t w. LTL_SEM_TIME t w (LOGIC_TO_TEMPORAL_DEEP l) = FLTL_MODELS (suff (WORD w) t) l``,

Induct_on `l` >> (
  FULL_SIMP_TAC std_ss [LOGIC_TO_TEMPORAL_DEEP_def, FLTL_MODELS_def, LTL_SEM_THM,
    P_SEM_def, wordTheory.at_def, wordTheory.AT_SUFF_LEMM]
) >- (
  (* NEXT *)
  SIMP_TAC arith_ss [wordTheory.SUFF_SUFF_LEMM, arithmeticTheory.ADD1]
) >- (
  (* SUNTIL *)
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
    Q.EXISTS_TAC `k - t` THEN
    FULL_SIMP_TAC arith_ss [wordTheory.SUFF_SUFF_LEMM],

    rename1 `suff (suff _ _) k` THEN
    Q.EXISTS_TAC `k + t` THEN
    FULL_SIMP_TAC arith_ss [wordTheory.SUFF_SUFF_LEMM] THEN
    REPEAT STRIP_TAC THEN
    Q.PAT_X_ASSUM `!j. _` (MP_TAC o Q.SPEC `j-t`) THEN
    FULL_SIMP_TAC arith_ss []
  ]
));


val LOGIC_TO_TEMPORAL_DEEP___SEM = store_thm ("LOGIC_TO_TEMPORAL_DEEP___SEM",
``!l w. LTL_SEM w (LOGIC_TO_TEMPORAL_DEEP l) = FLTL_MODELS (WORD w) l``,

SIMP_TAC std_ss [LTL_SEM_def, LOGIC_TO_TEMPORAL_DEEP___SEM_TIME, wordTheory.SUFF_0_LEMM]);


(************************************************************)
(* Translation examples/logic/ltl -> examples/temporal_deep *)
(************************************************************)

val TEMPORAL_DEEP_PROP_TO_LOGIC_def = Define `
  (TEMPORAL_DEEP_PROP_TO_LOGIC (P_PROP v) = (F_VAR v)) /\
  (TEMPORAL_DEEP_PROP_TO_LOGIC P_TRUE = ltl$LTL_TRUE ARB) /\
  (TEMPORAL_DEEP_PROP_TO_LOGIC (P_NOT p) = (F_NEG (TEMPORAL_DEEP_PROP_TO_LOGIC p))) /\
  (TEMPORAL_DEEP_PROP_TO_LOGIC (P_AND (p1,p2)) =
     (F_CONJ (TEMPORAL_DEEP_PROP_TO_LOGIC p1) (TEMPORAL_DEEP_PROP_TO_LOGIC p2)))`;


val TEMPORAL_DEEP_TO_LOGIC_def = Define `
  (TEMPORAL_DEEP_TO_LOGIC (LTL_PROP p) = TEMPORAL_DEEP_PROP_TO_LOGIC p) /\

  (TEMPORAL_DEEP_TO_LOGIC (LTL_AND (l1, l2)) = (F_CONJ (TEMPORAL_DEEP_TO_LOGIC l1) (TEMPORAL_DEEP_TO_LOGIC l2))) /\

  (TEMPORAL_DEEP_TO_LOGIC (LTL_NOT l) = (F_NEG (TEMPORAL_DEEP_TO_LOGIC l))) /\
  (TEMPORAL_DEEP_TO_LOGIC (LTL_NEXT l) = (F_X (TEMPORAL_DEEP_TO_LOGIC l))) /\
  (TEMPORAL_DEEP_TO_LOGIC (LTL_SUNTIL (l1, l2)) = (F_U (TEMPORAL_DEEP_TO_LOGIC l1) (TEMPORAL_DEEP_TO_LOGIC l2)))`;


val TEMPROAL_DEEP_TO_LOGIC_LOGIC_TO_TEMPORAL_DEEP = store_thm (
  "TEMPROAL_DEEP_TO_LOGIC_LOGIC_TO_TEMPORAL_DEEP",
  ``!l. TEMPORAL_DEEP_TO_LOGIC (LOGIC_TO_TEMPORAL_DEEP l) = l``,
Induct_on `l` >> (
  ASM_SIMP_TAC std_ss [TEMPORAL_DEEP_TO_LOGIC_def,
    LOGIC_TO_TEMPORAL_DEEP_def, TEMPORAL_DEEP_PROP_TO_LOGIC_def]
));


val TEMPORAL_DEEP_PROP_TO_LOGIC___SEM_TIME = store_thm ("TEMPORAL_DEEP_PROP_TO_LOGIC___SEM_TIME",
``!p t w. FLTL_MODELS (suff (WORD w) t) (TEMPORAL_DEEP_PROP_TO_LOGIC p) = P_SEM (w t) p``,

INDUCT_THEN prop_logic_induct ASSUME_TAC >> (
  ASM_SIMP_TAC std_ss [TEMPORAL_DEEP_PROP_TO_LOGIC_def, FLTL_MODELS_def,
    wordTheory.at_def, P_SEM_def, ltlTheory.LTL_TRUE_def, ltlTheory.LTL_FALSE_def,
    wordTheory.AT_SUFF_LEMM]
));

val TEMPORAL_DEEP_PROP_TO_LOGIC___SEM = store_thm ("TEMPORAL_DEEP_PROP_TO_LOGIC___SEM",
``!p w. FLTL_MODELS (WORD w) (TEMPORAL_DEEP_PROP_TO_LOGIC p) = P_SEM (w 0) p``,

REPEAT GEN_TAC THEN
Q.SUBGOAL_THEN `WORD w = suff (WORD w) 0` SUBST1_TAC >- (
  REWRITE_TAC[wordTheory.SUFF_0_LEMM]
) >>
SIMP_TAC std_ss [TEMPORAL_DEEP_PROP_TO_LOGIC___SEM_TIME]);



val TEMPORAL_DEEP_TO_LOGIC___SEM_TIME = store_thm ("TEMPORAL_DEEP_TO_LOGIC___SEM_TIME",
``!l t w. IS_FUTURE_LTL l ==> (FLTL_MODELS (suff (WORD w) t) (TEMPORAL_DEEP_TO_LOGIC l) = LTL_SEM_TIME t w l)``,

INDUCT_THEN ltl_induct ASSUME_TAC >> (
  ASM_SIMP_TAC std_ss [IS_FUTURE_LTL_def, TEMPORAL_DEEP_TO_LOGIC_def,
    TEMPORAL_DEEP_PROP_TO_LOGIC___SEM_TIME, LTL_SEM_def, LTL_SEM_TIME_def,
    FLTL_MODELS_def, wordTheory.SUFF_SUFF_LEMM, arithmeticTheory.ADD1]
) >>
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
  rename1 `LTL_SEM_TIME (t+k)` >>
  Q.EXISTS_TAC `k + t` >>
  FULL_SIMP_TAC arith_ss [] THEN
  REPEAT STRIP_TAC THEN
  Q.PAT_X_ASSUM `!j. _` (MP_TAC o Q.SPEC `j-t`) THEN
  FULL_SIMP_TAC arith_ss [],

  Q.EXISTS_TAC `k - t` THEN
  FULL_SIMP_TAC arith_ss []
]);


val TEMPORAL_DEEP_TO_LOGIC___SEM = store_thm ("TEMPORAL_DEEP_TO_LOGIC___SEM",
``!l w. IS_FUTURE_LTL l ==> (FLTL_MODELS (WORD w) (TEMPORAL_DEEP_TO_LOGIC l) = LTL_SEM w l)``,

REPEAT GEN_TAC THEN
Q.SUBGOAL_THEN `WORD w = suff (WORD w) 0` SUBST1_TAC >- (
  REWRITE_TAC[wordTheory.SUFF_0_LEMM]
) >>
SIMP_TAC std_ss [TEMPORAL_DEEP_TO_LOGIC___SEM_TIME, LTL_SEM_def]);



(************************************************************)
(* Translation examples/temporal_deep -> src/temporal       *)
(************************************************************)

val TEMPORAL_DEEP_TO_TEMPORAL_def = Define `
  (TEMPORAL_DEEP_TO_TEMPORAL (LTL_PROP p) w = (\t. P_SEM (w t) p)) /\

  (TEMPORAL_DEEP_TO_TEMPORAL (LTL_AND (l1, l2)) w =
     (\a b t. (a t) /\ (b t)) (TEMPORAL_DEEP_TO_TEMPORAL l1 w)
                              (TEMPORAL_DEEP_TO_TEMPORAL l2 w)) /\

  (TEMPORAL_DEEP_TO_TEMPORAL (LTL_NOT l) w = (\a t. ~(a t)) (TEMPORAL_DEEP_TO_TEMPORAL l w)) /\
  (TEMPORAL_DEEP_TO_TEMPORAL (LTL_NEXT l) w = (NEXT (TEMPORAL_DEEP_TO_TEMPORAL l w))) /\
  (TEMPORAL_DEEP_TO_TEMPORAL (LTL_SUNTIL (l1, l2)) w =
    (TEMPORAL_DEEP_TO_TEMPORAL l1 w) SUNTIL (TEMPORAL_DEEP_TO_TEMPORAL l2 w)) /\
  (TEMPORAL_DEEP_TO_TEMPORAL (LTL_PSNEXT l) w = (PSNEXT (TEMPORAL_DEEP_TO_TEMPORAL l w))) /\
  (TEMPORAL_DEEP_TO_TEMPORAL (LTL_PSUNTIL (l1, l2)) w =
    (TEMPORAL_DEEP_TO_TEMPORAL l1 w) PSUNTIL (TEMPORAL_DEEP_TO_TEMPORAL l2 w))`;


val TEMPORAL_DEEP_TO_TEMPORAL_THM = store_thm ("TEMPORAL_DEEP_TO_TEMPORAL_THM",
  ``!l. TEMPORAL_DEEP_TO_TEMPORAL l = \w t. LTL_SEM_TIME t w l``,

SIMP_TAC std_ss [FUN_EQ_THM] THEN
INDUCT_THEN ltl_induct ASSUME_TAC >> (
  ASM_SIMP_TAC std_ss [TEMPORAL_DEEP_TO_TEMPORAL_def,
    LTL_SEM_TIME_def]
) >- (
  (* NEXT *)
  ASM_SIMP_TAC std_ss [NEXT]
) >- (
  (* SUNTIL *)
  ASM_SIMP_TAC std_ss [SUNTIL_LINORD, UPTO, arithmeticTheory.GREATER_EQ]
) >- (
  (* PSNEXT *)
  ASM_SIMP_TAC arith_ss [PSNEXT, arithmeticTheory.GREATER_DEF]
) >- (
  (* PSUNTIL *)
  ASM_SIMP_TAC std_ss [PSUNTIL] >>
  REPEAT STRIP_TAC >> EQ_TAC >> REPEAT STRIP_TAC >- (
    METIS_TAC[]
  ) >>
  Q.ABBREV_TAC `P = \k. k <= t /\ LTL_SEM_TIME k w l'` >>
  `(P k) /\ !k. k > t ==> ~(P k)` by (
    Q.UNABBREV_TAC `P` >>
    ASM_SIMP_TAC arith_ss []
  ) >>
  `?delta. P delta /\ (!t. t > delta ==> ~(P t))` by
    METIS_TAC[numLib.EXISTS_GREATEST_CONV ``(?k. P k) /\ (?k. !t. t > k ==> ~(P t))``] >>
  Q.UNABBREV_TAC `P` >>
  Q.EXISTS_TAC `delta` >>
  FULL_SIMP_TAC arith_ss [arithmeticTheory.GREATER_DEF] >>
  REPEAT GEN_TAC >> STRIP_TAC >>
  `~(delta < k)` by METIS_TAC[] >>
  `k < t'` by DECIDE_TAC >>
  METIS_TAC[]
))



(************************************************************)
(* Translation examples/logic/ltl -> src/temporal           *)
(************************************************************)

val LOGIC_TO_TEMPORAL_def = Define `
  LOGIC_TO_TEMPORAL l = (TEMPORAL_DEEP_TO_TEMPORAL (LOGIC_TO_TEMPORAL_DEEP l))`;


val LOGIC_TO_TEMPORAL_THM = store_thm ("LOGIC_TO_TEMPORAL_THM",
  ``!l. LOGIC_TO_TEMPORAL l = \w t. FLTL_MODELS (suff (WORD w) t) l``,

SIMP_TAC std_ss [LOGIC_TO_TEMPORAL_def, TEMPORAL_DEEP_TO_TEMPORAL_THM,
  LOGIC_TO_TEMPORAL_DEEP___SEM_TIME]);


val LOGIC_TO_TEMPORAL_ALT_DEF = store_thm ("LOGIC_TO_TEMPORAL_ALT_DEF",
``(!v. LOGIC_TO_TEMPORAL (F_VAR v) = (\w t. v IN w t)) /\
  (!l1 l2. LOGIC_TO_TEMPORAL (F_CONJ l1 l2) =
     (\w t. (LOGIC_TO_TEMPORAL l1 w t) /\ (LOGIC_TO_TEMPORAL l2 w t))) /\
  (!l. LOGIC_TO_TEMPORAL (F_NEG l) = (\w t. ~(LOGIC_TO_TEMPORAL l w t))) /\
  (!l. LOGIC_TO_TEMPORAL (F_X l) = \w. (NEXT (LOGIC_TO_TEMPORAL l w))) /\
  (!l1 l2. LOGIC_TO_TEMPORAL (F_U l1 l2) = \w. ((LOGIC_TO_TEMPORAL l1 w) SUNTIL (LOGIC_TO_TEMPORAL l2 w)))``,

SIMP_TAC std_ss [LOGIC_TO_TEMPORAL_def, LOGIC_TO_TEMPORAL_DEEP_def,
  TEMPORAL_DEEP_TO_TEMPORAL_def, FUN_EQ_THM, P_SEM_def]);

val _ = export_theory ();
