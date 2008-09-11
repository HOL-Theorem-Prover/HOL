open HolKernel Parse boolLib

infix THEN THENL |->
infix 8 by

open Datatype integerTheory bossLib int_arithTheory simpLib pred_setTheory

val _ = new_theory "DeepSyntax";

val _ = Hol_datatype `deep_form = Conjn of deep_form => deep_form
                                | Disjn of deep_form => deep_form
                                | Negn of deep_form
                                | UnrelatedBool of bool
                                | xLT of int | LTx of int
                                | xEQ of int
                                | xDivided of int => int`;

val eval_form_def = Define
  `(eval_form (Conjn f1 f2) x = eval_form f1 x /\ eval_form f2 x) /\
   (eval_form (Disjn f1 f2) x = eval_form f1 x \/ eval_form f2 x) /\
   (eval_form (Negn f) x = ~eval_form f x) /\
   (eval_form (UnrelatedBool b) x = b) /\
   (eval_form (xLT i) x = x < i) /\
   (eval_form (LTx i) x = i < x) /\
   (eval_form (xEQ i) x = (x = i)) /\
   (eval_form (xDivided i1 i2) x = i1 int_divides x + i2)`;

val neginf_def = Define
  `(neginf (Conjn f1 f2) = Conjn (neginf f1) (neginf f2)) /\
   (neginf (Disjn f1 f2) = Disjn (neginf f1) (neginf f2)) /\
   (neginf (Negn f) = Negn (neginf f)) /\
   (neginf (UnrelatedBool b) = UnrelatedBool b) /\
   (neginf (xLT i) = UnrelatedBool T) /\
   (neginf (LTx i) = UnrelatedBool F) /\
   (neginf (xEQ i) = UnrelatedBool F) /\
   (neginf (xDivided i1 i2) = xDivided i1 i2)`;

val posinf_def = Define
  `(posinf (Conjn f1 f2) = Conjn (posinf f1) (posinf f2)) /\
   (posinf (Disjn f1 f2) = Disjn (posinf f1) (posinf f2)) /\
   (posinf (Negn f) = Negn (posinf f)) /\
   (posinf (UnrelatedBool b) = UnrelatedBool b) /\
   (posinf (xLT i) = UnrelatedBool F) /\
   (posinf (LTx i) = UnrelatedBool T) /\
   (posinf (xEQ i) = UnrelatedBool F) /\
   (posinf (xDivided i1 i2) = xDivided i1 i2)`;

val neginf_ok = store_thm(
  "neginf_ok",
  ``!f. ?y. !x. x < y ==> (eval_form f x = eval_form (neginf f) x)``,
  Induct THEN SRW_TAC [][eval_form_def, neginf_def] THENL [
    Q.EXISTS_TAC `int_min y y'` THEN PROVE_TAC [INT_MIN_LT],
    Q.EXISTS_TAC `int_min y y'` THEN PROVE_TAC [INT_MIN_LT],
    PROVE_TAC [],
    PROVE_TAC [INT_LT_GT],
    PROVE_TAC [INT_LT_REFL]
  ]);

val posinf_ok = store_thm(
  "posinf_ok",
  ``!f. ?y. !x. y < x ==> (eval_form f x = eval_form (posinf f) x)``,
  Induct THEN SRW_TAC [][eval_form_def, posinf_def] THENL [
    Q.EXISTS_TAC `int_max y y'` THEN PROVE_TAC [INT_MAX_LT],
    Q.EXISTS_TAC `int_max y y'` THEN PROVE_TAC [INT_MAX_LT],
    PROVE_TAC [INT_LT_GT],
    PROVE_TAC [],
    PROVE_TAC [INT_LT_REFL]
  ]);

val alldivide_def = Define
  `(alldivide (Conjn f1 f2) d = alldivide f1 d /\ alldivide f2 d) /\
   (alldivide (Disjn f1 f2) d = alldivide f1 d /\ alldivide f2 d) /\
   (alldivide (Negn f) d = alldivide f d) /\
   (alldivide (UnrelatedBool b) d = T) /\
   (alldivide (xLT i) d = T) /\
   (alldivide (LTx i) d = T) /\
   (alldivide (xEQ i) d = T) /\
   (alldivide (xDivided i1 i2) d = i1 int_divides d)`;

val add_d_neginf = store_thm(
  "add_d_neginf",
  ``!f x y d. alldivide f d ==>
              (eval_form (neginf f) x = eval_form (neginf f) (x + y * d))``,
  Induct THEN SRW_TAC [][eval_form_def, neginf_def, alldivide_def] THENL [
    PROVE_TAC [],
    PROVE_TAC [],
    `i int_divides y * d` by PROVE_TAC [INT_DIVIDES_RMUL] THEN
    `x + y * d + i0 = y * d + (x + i0)` by
        CONV_TAC (AC_CONV(INT_ADD_ASSOC, INT_ADD_COMM)) THEN
    PROVE_TAC [INT_DIVIDES_LADD]
  ]);

val add_d_posinf = store_thm(
  "add_d_posinf",
  ``!f x y d. alldivide f d ==>
              (eval_form (posinf f) x = eval_form (posinf f) (x + y * d))``,
  Induct THEN SRW_TAC [][eval_form_def, posinf_def, alldivide_def] THENL [
    PROVE_TAC [],
    PROVE_TAC [],
    `i int_divides y * d` by PROVE_TAC [INT_DIVIDES_RMUL] THEN
    `x + y * d + i0 = y * d + (x + i0)` by
        CONV_TAC (AC_CONV(INT_ADD_ASSOC, INT_ADD_COMM)) THEN
    PROVE_TAC [INT_DIVIDES_LADD]
  ]);

val neginf_disj1_implies_exoriginal = store_thm(
  "neginf_disj1_implies_exoriginal",
  ``!f d i.
      alldivide f d ==> 0 < i /\ i <= d /\ eval_form (neginf f) i ==>
      ?x. eval_form f x``,
  SRW_TAC [][] THEN
  STRIP_ASSUME_TAC (Q.SPEC `f` neginf_ok) THEN
  `0 < d` by PROVE_TAC [INT_LTE_TRANS] THEN
  `?c. i - c * d < y` by PROVE_TAC [can_get_small] THEN
  FULL_SIMP_TAC std_ss [int_sub, INT_NEG_LMUL] THEN
  PROVE_TAC [add_d_neginf]);

val posinf_disj1_implies_exoriginal = store_thm(
  "posinf_disj1_implies_exoriginal",
  ``!f d i.
      alldivide f d ==> 0 < i /\ i <= d /\ eval_form (posinf f) i ==>
      ?x. eval_form f x``,
  SRW_TAC [][] THEN
  STRIP_ASSUME_TAC (Q.SPEC `f` posinf_ok) THEN
  `0 < d` by PROVE_TAC [INT_LTE_TRANS] THEN
  `?c. y < i + c * d` by PROVE_TAC [can_get_big] THEN
  PROVE_TAC [add_d_posinf]);

val Aset_def = Define
  `(Aset pos (Conjn f1 f2) = Aset pos f1 UNION Aset pos f2) /\
   (Aset pos (Disjn f1 f2) = Aset pos f1 UNION Aset pos f2) /\
   (Aset pos (Negn f) = Aset (~pos) f) /\
   (Aset pos (UnrelatedBool b) = {}) /\
   (Aset pos (xLT i) = if pos then {i} else {}) /\
   (Aset pos (LTx i) = if pos then {} else {i + 1}) /\
   (Aset pos (xEQ i) = if pos then {i + 1} else {i}) /\
   (Aset pos (xDivided i1 i2) = {})`;

val Bset_def = Define
  `(Bset pos (Conjn f1 f2) = Bset pos f1 UNION Bset pos f2) /\
   (Bset pos (Disjn f1 f2) = Bset pos f1 UNION Bset pos f2) /\
   (Bset pos (Negn f) = Bset (~pos) f) /\
   (Bset pos (UnrelatedBool b) = {}) /\
   (Bset pos (xLT i) = if pos then {} else {i + ~1}) /\
   (Bset pos (LTx i) = if pos then {i} else {}) /\
   (Bset pos (xEQ i) = if pos then {i + ~1} else {i}) /\
   (Bset pos (xDivided i1 i2) = {})`;

val predset_lemma = prove(
  ``!P Q R. P UNION Q SUBSET R = P SUBSET R /\ Q SUBSET R``,
  SRW_TAC [][SUBSET_DEF, IN_UNION] THEN PROVE_TAC []);

val neginf_inductive_case = prove(
  ``!g x d f pos.
        alldivide f d /\ 0 < d /\ eval_form g x /\
        (!j b. 0 < j /\ j <= d /\ b IN Bset pos f ==> ~eval_form g (b + j)) /\
        Bset pos f SUBSET Bset T g ==>
        if pos then eval_form f x ==> eval_form f (x - d)
        else eval_form f (x - d) ==> eval_form f x``,
  NTAC 3 GEN_TAC THEN Induct THENL [
    GEN_TAC THEN RULE_ASSUM_TAC (Q.SPEC `pos`) THEN
    REPEAT STRIP_TAC THEN
    FULL_SIMP_TAC std_ss [IN_UNION, predset_lemma, Bset_def,
                          eval_form_def, alldivide_def] THEN PROVE_TAC [],
    GEN_TAC THEN RULE_ASSUM_TAC (Q.SPEC `pos`) THEN
    REPEAT STRIP_TAC THEN
    FULL_SIMP_TAC std_ss [IN_UNION, predset_lemma, Bset_def, alldivide_def,
                          eval_form_def] THEN PROVE_TAC [],
    GEN_TAC THEN SIMP_TAC std_ss [Bset_def, eval_form_def] THEN
    RULE_ASSUM_TAC (Q.SPEC `~pos`) THEN
    REPEAT STRIP_TAC THEN FULL_SIMP_TAC std_ss [alldivide_def] THEN
    PROVE_TAC [],
    SIMP_TAC std_ss [eval_form_def],
    SRW_TAC [] [eval_form_def, Bset_def] THENL [
      (* easy case: x < i ==> x - d < i  *)
      `x < i + d` by PROVE_TAC [INT_LT_ADD2, INT_ADD_RID] THEN
      PROVE_TAC [INT_LT_SUB_RADD],
      (* harder case: x - d < i ==> x < i *)
      SPOSE_NOT_THEN ASSUME_TAC THEN
      FULL_SIMP_TAC std_ss [not_less, GSYM INT_LT_ADDNEG2, IN_SING] THEN
      `x - d <= i + ~1` by PROVE_TAC [less_to_leq_samel] THEN
      FULL_SIMP_TAC std_ss [INT_LE_SUB_RADD] THEN
      `?k. (x = (i + ~1) + k) /\ 0 < k /\ k <= d` by
         PROVE_TAC [in_additive_range] THEN PROVE_TAC []
    ],
    SRW_TAC [][eval_form_def, Bset_def] THENL [
      (* harder case: i < x ==> i < x - d *)
      SPOSE_NOT_THEN ASSUME_TAC THEN
      FULL_SIMP_TAC std_ss [INT_NOT_LT, INT_LE_SUB_RADD, IN_SING] THEN
      `?k. (x = i + k) /\ 0 < k /\ k <= d` by
         PROVE_TAC [in_additive_range] THEN
      PROVE_TAC [],
      FULL_SIMP_TAC std_ss [GSYM INT_NEG_LT0, INT_LT_SUB_LADD] THEN
      `i + d + ~d < x` by PROVE_TAC [INT_LT_ADD2, INT_ADD_RID] THEN
      FULL_SIMP_TAC std_ss [GSYM INT_ADD_ASSOC, INT_ADD_RINV, INT_ADD_RID]
    ],
    SRW_TAC [][eval_form_def, Bset_def, IN_SING] THENL [
      FIRST_X_ASSUM (MP_TAC o Q.SPEC `1`) THEN
      ASM_SIMP_TAC std_ss [GSYM INT_ADD_ASSOC, INT_ADD_LINV, INT_ADD_RID,
                           INT_NOT_LE] THEN
      CONV_TAC intReduce.REDUCE_CONV THEN PROVE_TAC [INT_DISCRETE, INT_ADD_LID],
      FIRST_X_ASSUM (MP_TAC o Q.SPEC `d`) THEN
      ASM_SIMP_TAC std_ss [GSYM INT_ADD_ASSOC, int_sub, INT_ADD_RID,
                           INT_LE_REFL, INT_ADD_LINV]
    ],
    SRW_TAC [][eval_form_def, Bset_def, IN_SING, alldivide_def,
               int_sub] THEN
    `x + ~d + i0 = x + i0 + ~d`
       by CONV_TAC(AC_CONV(INT_ADD_ASSOC, INT_ADD_COMM)) THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    `i int_divides ~d` by PROVE_TAC [INT_DIVIDES_NEG] THEN
    PROVE_TAC [INT_DIVIDES_LADD, INT_DIVIDES_RADD]
  ]);

val neginf_lemma =
  GEN_ALL (SIMP_RULE std_ss [SUBSET_REFL]
           (Q.INST [`g` |-> `f`, `pos` |-> `T`]
                   (SPEC_ALL neginf_inductive_case)))

val posinf_inductive_case = prove(
  ``!g x d f pos.
       alldivide f d /\ 0 < d /\ eval_form g x /\
       (!j b. 0 < j /\ j <= d /\ b IN Aset pos f ==> ~eval_form g (b + ~j)) /\
       Aset pos f SUBSET Aset T g ==>
       if pos then eval_form f x ==> eval_form f (x + d)
       else eval_form f (x + d) ==> eval_form f x``,
  NTAC 3 GEN_TAC THEN Induct THENL [
    GEN_TAC THEN RULE_ASSUM_TAC (Q.SPEC `pos`) THEN
    ASM_SIMP_TAC std_ss [alldivide_def, eval_form_def, Aset_def,
                         predset_lemma, IN_UNION] THEN REPEAT STRIP_TAC THEN
    FULL_SIMP_TAC std_ss [] THEN PROVE_TAC [],
    GEN_TAC THEN RULE_ASSUM_TAC (Q.SPEC `pos`) THEN
    ASM_SIMP_TAC std_ss [alldivide_def, eval_form_def, Aset_def,
                         predset_lemma, IN_UNION] THEN REPEAT STRIP_TAC THEN
    FULL_SIMP_TAC std_ss [] THEN PROVE_TAC [],
    GEN_TAC THEN RULE_ASSUM_TAC (Q.SPEC `~pos`) THEN
    ASM_SIMP_TAC std_ss [alldivide_def, eval_form_def, Aset_def,
                         predset_lemma, IN_UNION] THEN REPEAT STRIP_TAC THEN
    FULL_SIMP_TAC std_ss [] THEN PROVE_TAC [],
    SIMP_TAC std_ss [eval_form_def],
    SRW_TAC [][Aset_def, eval_form_def, IN_SING, alldivide_def] THENL [
      SPOSE_NOT_THEN (MP_TAC o
                      REWRITE_RULE [INT_NOT_LT, GSYM INT_LE_SUB_RADD]) THEN
      STRIP_TAC THEN
      `?k. (x = i - k) /\ 0 < k /\ k <= d` by
          PROVE_TAC [in_subtractive_range] THEN
      PROVE_TAC [int_sub],
      FULL_SIMP_TAC std_ss [GSYM INT_NEG_LT0] THEN
      PROVE_TAC [INT_ADD_ASSOC, INT_ADD_RINV, INT_ADD_RID, INT_LT_ADD2]
    ],
    SRW_TAC [][Aset_def, eval_form_def, IN_SING, alldivide_def] THENL [
      PROVE_TAC [INT_ADD_RID, INT_LT_ADD2],
      SPOSE_NOT_THEN (ASSUME_TAC o REWRITE_RULE [not_less]) THEN
      `i + 1 <= x + d` by PROVE_TAC [less_to_leq_samer] THEN
      POP_ASSUM (ASSUME_TAC o REWRITE_RULE [GSYM INT_LE_SUB_RADD]) THEN
      `?k. (x = i + 1 - k) /\ 0 < k /\ k <= d` by
          PROVE_TAC [in_subtractive_range] THEN
      PROVE_TAC [int_sub]
    ],
    SRW_TAC [][Aset_def, eval_form_def, IN_SING, alldivide_def] THENL [
      FIRST_X_ASSUM (MP_TAC o Q.SPEC `1`) THEN
      ASM_SIMP_TAC std_ss [GSYM INT_ADD_ASSOC, INT_ADD_RINV, INT_ADD_RID] THEN
      CONV_TAC intReduce.REDUCE_CONV THEN PROVE_TAC [INT_DISCRETE, INT_ADD_LID,
                                                    INT_NOT_LE],
      FIRST_X_ASSUM (MP_TAC o Q.SPEC `d`) THEN
      ASM_SIMP_TAC std_ss [GSYM INT_ADD_ASSOC, INT_LE_REFL, INT_ADD_RID,
                           INT_ADD_RINV]
    ],
    SRW_TAC [][Aset_def, eval_form_def, IN_SING, alldivide_def] THEN
    `x + d + i0 = x + i0 + d` by
       CONV_TAC (AC_CONV(INT_ADD_ASSOC, INT_ADD_COMM)) THEN
    PROVE_TAC [INT_DIVIDES_LADD, INT_DIVIDES_RADD]
  ]);

val posinf_lemma =
  GEN_ALL (SIMP_RULE std_ss [SUBSET_REFL]
           (Q.INST [`g` |-> `f`, `pos` |-> `T`]
                   (SPEC_ALL posinf_inductive_case)))

val neginf_exoriginal_implies_rhs = store_thm(
  "neginf_exoriginal_implies_rhs",
  ``!f d x.
       alldivide f d /\ 0 < d ==>
       eval_form f x ==>
       (?i. 0 < i /\ i <= d /\ eval_form (neginf f) i) \/
       (?j b. 0 < j /\ j <= d /\ b IN Bset T f /\ eval_form f (b + j))``,
  REPEAT STRIP_TAC THEN
  Cases_on
    `?j b. 0 < j /\ j <= d /\ b IN Bset T f /\ eval_form f (b + j)`
  THENL [
    ASM_REWRITE_TAC [],
    DISJ1_TAC THEN
    POP_ASSUM (fn th =>
      `!j b. 0 < j /\ j <= d /\ b IN Bset T f ==> ~eval_form f (b + j)`
         by PROVE_TAC [th]) THEN
    Q.SUBGOAL_THEN `!x. eval_form f x ==> eval_form f (x - d)`
    ASSUME_TAC THENL [
      PROVE_TAC [neginf_lemma],
      STRIP_ASSUME_TAC (Q.SPEC `f` neginf_ok) THEN
      `!c. 0 < c ==> eval_form f (x - c * d)`
         by PROVE_TAC [top_and_lessers] THEN
      `?e. 0 < e /\ x - e * d < y` by PROVE_TAC [can_get_small] THEN
      `eval_form f (x - e * d)` by PROVE_TAC [] THEN
      `eval_form (neginf f) (x - e * d)` by PROVE_TAC [] THEN
      `?k. 0 < x - e * d - k * d /\ x - e * d - k * d <= d` by
         PROVE_TAC [subtract_to_small] THEN
      FULL_SIMP_TAC std_ss [int_sub, INT_NEG_LMUL] THEN
      PROVE_TAC [add_d_neginf]
    ]
  ]);

val posinf_exoriginal_implies_rhs = store_thm(
  "posinf_exoriginal_implies_rhs",
  ``!f d x.
       alldivide f d /\ 0 < d ==>
       eval_form f x ==>
       (?i. 0 < i /\ i <= d /\ eval_form (posinf f) i) \/
       (?j b. 0 < j /\ j <= d /\ b IN Aset T f /\ eval_form f (b + ~j))``,
  REPEAT STRIP_TAC THEN
  Cases_on
    `?j b. 0 < j /\ j <= d /\ b IN Aset T f /\ eval_form f (b + ~j)`
  THENL [
    ASM_REWRITE_TAC [],
    DISJ1_TAC THEN
    POP_ASSUM (fn th =>
      `!j b. 0 < j /\ j <= d /\ b IN Aset T f ==> ~eval_form f (b + ~j)`
         by PROVE_TAC [th]) THEN
    Q.SUBGOAL_THEN `!x. eval_form f x ==> eval_form f (x + d)`
    ASSUME_TAC THENL [
      PROVE_TAC [posinf_lemma],
      STRIP_ASSUME_TAC (Q.SPEC `f` posinf_ok) THEN
      `!c. 0 < c ==> eval_form f (x + c * d)`
         by PROVE_TAC [bot_and_greaters] THEN
      `?e. 0 < e /\ y < x + e * d` by PROVE_TAC [can_get_big] THEN
      `eval_form f (x + e * d)` by PROVE_TAC [] THEN
      `eval_form (posinf f) (x + e * d)` by PROVE_TAC [] THEN
      `?k. 0 < x + e * d - k * d /\ x + e * d - k * d <= d` by
         PROVE_TAC [subtract_to_small] THEN
      FULL_SIMP_TAC std_ss [int_sub, INT_NEG_LMUL] THEN
      PROVE_TAC [add_d_posinf]
    ]
  ]);



val neginf_exoriginal_eq_rhs = store_thm(
  "neginf_exoriginal_eq_rhs",
  ``!f d.
       alldivide f d /\ 0 < d ==>
       ((?x. eval_form f x) =
           (?i. K (0 < i /\ i <= d) i /\ eval_form (neginf f) i) \/
           (?b j. (b IN Bset T f /\ K (0 < j /\ j <= d) j)  /\
                  eval_form f (b + j)))``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC [combinTheory.K_THM, GSYM INT_NEG_MINUS1] THEN
  REPEAT STRIP_TAC THENL [
    IMP_RES_TAC neginf_exoriginal_implies_rhs THEN PROVE_TAC [],
    PROVE_TAC [neginf_disj1_implies_exoriginal],
    PROVE_TAC []
  ]);

val posinf_exoriginal_eq_rhs = store_thm(
  "posinf_exoriginal_eq_rhs",
  ``!f d.
       alldivide f d /\ 0 < d ==>
       ((?x. eval_form f x) =
           (?i. K (0 < i /\ i <= d) i /\ eval_form (posinf f) i) \/
           (?b j. (b IN Aset T f /\ K (0 < j /\ j <= d) j) /\
                  eval_form f (b + ~1 * j)))``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  REWRITE_TAC [combinTheory.K_THM, GSYM INT_NEG_MINUS1] THEN
  REPEAT STRIP_TAC THENL [
    IMP_RES_TAC posinf_exoriginal_implies_rhs THEN PROVE_TAC [],
    PROVE_TAC [posinf_disj1_implies_exoriginal],
    PROVE_TAC []
  ]);

(* useful additional rewrites for the d.p. *)
val in_bset = store_thm(
  "in_bset",
  ``((?b. b IN Bset pos (Conjn f1 f2) /\ P b) =
          (?b. b IN Bset pos f1 /\ P b) \/ (?b. b IN Bset pos f2 /\ P b)) /\
    ((?b. b IN Bset pos (Disjn f1 f2) /\ P b) =
          (?b. b IN Bset pos f1 /\ P b) \/ (?b. b IN Bset pos f2 /\ P b)) /\
    ((?b. b IN Bset T (Negn f) /\ P b) = (?b. b IN Bset F f /\ P b)) /\
    ((?b. b IN Bset F (Negn f) /\ P b) = (?b. b IN Bset T f /\ P b)) /\
    ((?b. b IN Bset pos (UnrelatedBool b0) /\ P b) = F) /\
    ((?b. b IN Bset T (xLT i) /\ P b) = F) /\
    ((?b. b IN Bset F (xLT i) /\ P b) = P (i + ~1)) /\
    ((?b. b IN Bset T (LTx i) /\ P b) = P i) /\
    ((?b. b IN Bset F (LTx i) /\ P b) = F) /\
    ((?b. b IN Bset T (xEQ i) /\ P b) = P (i + ~1)) /\
    ((?b. b IN Bset F (xEQ i) /\ P b) = P i) /\
    ((?b. b IN Bset pos (xDivided i1 i2) /\ P b) = F)``,
  SIMP_TAC std_ss [IN_UNION, NOT_IN_EMPTY, IN_SING, Bset_def] THEN
  PROVE_TAC []);

val in_aset = store_thm(
  "in_aset",
  ``((?a. a IN Aset pos (Conjn f1 f2) /\ P a) =
          (?a. a IN Aset pos f1 /\ P a) \/ (?a. a IN Aset pos f2 /\ P a)) /\
    ((?a. a IN Aset pos (Disjn f1 f2) /\ P a) =
          (?a. a IN Aset pos f1 /\ P a) \/ (?a. a IN Aset pos f2 /\ P a)) /\
    ((?a. a IN Aset T (Negn f) /\ P a) = (?a. a IN Aset F f /\ P a)) /\
    ((?a. a IN Aset F (Negn f) /\ P a) = (?a. a IN Aset T f /\ P a)) /\
    ((?a. a IN Aset pos (UnrelatedBool a0) /\ P a) = F) /\
    ((?a. a IN Aset T (xLT i) /\ P a) = P i) /\
    ((?a. a IN Aset F (xLT i) /\ P a) = F) /\
    ((?a. a IN Aset T (LTx i) /\ P a) = F) /\
    ((?a. a IN Aset F (LTx i) /\ P a) = P (i + 1)) /\
    ((?a. a IN Aset T (xEQ i) /\ P a) = P (i + 1)) /\
    ((?a. a IN Aset F (xEQ i) /\ P a) = P i) /\
    ((?a. a IN Aset pos (xDivided i1 i2) /\ P a) = F)``,
  SIMP_TAC std_ss [IN_UNION, NOT_IN_EMPTY, IN_SING, Aset_def] THEN
  PROVE_TAC []);



val _ = export_theory();
