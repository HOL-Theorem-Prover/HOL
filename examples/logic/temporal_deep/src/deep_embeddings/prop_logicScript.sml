open HolKernel Parse boolLib bossLib;

open pred_setTheory pairTheory arithmeticTheory tuerk_tacticsLib
     containerTheory listTheory temporal_deep_mixedTheory set_lemmataTheory;

open Sanity;

val _ = hide "S";
val _ = hide "I";

val _ = new_theory "prop_logic";
val _ = ParseExtras.temp_loose_equality();

val _ = Datatype `
    prop_logic = P_PROP 'a                       (* atomic proposition *)
               | P_TRUE                          (* true               *)
               | P_NOT  prop_logic               (* negation           *)
               | P_AND (prop_logic # prop_logic) (* conjunction        *)
`;

val prop_logic_11 = DB.fetch "-" "prop_logic_11";

Theorem prop_logic_induct = Q.GEN `P`
   (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2)) ==> (A ==> B1)``)
     (SIMP_RULE
       std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P x ==> Q(x,y)) = !x. P x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P y ==> Q(x,y)) = !y. P y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P`,`\(f1,f2). P f1 /\ P f2`]
         (TypeBase.induction_of ``:'a prop_logic``))));

val P_SEM_def = Define
  `(P_SEM s (P_TRUE) = T) /\
   (P_SEM s (P_PROP p) = p IN s) /\
   (P_SEM s (P_NOT b) = ~(P_SEM s b)) /\
   (P_SEM s (P_AND(b1,b2)) = (P_SEM s b1 /\ P_SEM s b2))`;

(******************************************************************************
* Syntactic Sugar for Propositional logic
******************************************************************************)

val P_FALSE_def = Define
   `P_FALSE = P_NOT (P_TRUE)`;

val P_OR_def = Define
   `P_OR (b1, b2) = P_NOT (P_AND (P_NOT b1, P_NOT b2))`;

val P_IMPL_def = Define
   `P_IMPL (b1, b2) = P_OR (P_NOT b1, b2)`;

val P_COND_def = Define
   `P_COND (c, b1, b2) = P_AND (P_IMPL (c, b1), P_IMPL (P_NOT c, b2))`;

val P_EQUIV_def = Define
   `P_EQUIV (b1, b2) = P_AND (P_IMPL (b1, b2), P_IMPL (b2, b1))`;

val PROP_LOGIC_EQUIVALENT_def = Define
   `PROP_LOGIC_EQUIVALENT b1 b2 = (!s. (P_SEM s b1) = (P_SEM s b2))`;

val P_USED_VARS_def = Define
  `(P_USED_VARS (P_TRUE) = EMPTY) /\
   (P_USED_VARS (P_PROP p) = {p}) /\
   (P_USED_VARS (P_NOT b) = P_USED_VARS b) /\
   (P_USED_VARS (P_AND(b1,b2)) = ((P_USED_VARS b1) UNION (P_USED_VARS b2)))`;

val IS_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_def = Define
  `(IS_POSITIVE_PROP_FORMULA_SUBSET S P_TRUE = T) /\
   (IS_POSITIVE_PROP_FORMULA_SUBSET S (P_PROP a) = T) /\
   (IS_POSITIVE_PROP_FORMULA_SUBSET S (P_NOT p') =
    IS_NEGATIVE_PROP_FORMULA_SUBSET S p') /\
   (IS_POSITIVE_PROP_FORMULA_SUBSET S (P_AND(p', p'')) = (
    IS_POSITIVE_PROP_FORMULA_SUBSET S p' /\
    IS_POSITIVE_PROP_FORMULA_SUBSET S p'')) /\
   (IS_NEGATIVE_PROP_FORMULA_SUBSET S P_TRUE = T) /\
   (IS_NEGATIVE_PROP_FORMULA_SUBSET S (P_PROP a) = (~(a IN S))) /\
   (IS_NEGATIVE_PROP_FORMULA_SUBSET S (P_NOT p') =
    IS_POSITIVE_PROP_FORMULA_SUBSET S p') /\
   (IS_NEGATIVE_PROP_FORMULA_SUBSET S (P_AND(p', p'')) = (
    IS_NEGATIVE_PROP_FORMULA_SUBSET S p' /\
    IS_NEGATIVE_PROP_FORMULA_SUBSET S p''))`;

val IS_POSITIVE_PROP_FORMULA_def = Define
   `IS_POSITIVE_PROP_FORMULA p = IS_POSITIVE_PROP_FORMULA_SUBSET UNIV p`;

val IS_NEGATIVE_PROP_FORMULA_def = Define
   `IS_NEGATIVE_PROP_FORMULA p = IS_NEGATIVE_PROP_FORMULA_SUBSET UNIV p`;

val P_BIGOR_def = Define
  `(P_BIGOR [] = P_FALSE) /\
   (P_BIGOR (s::S) = P_OR (s, P_BIGOR S))`;

val P_BIGAND_def = Define
  `(P_BIGAND [] = P_TRUE) /\
   (P_BIGAND (s::S) = P_AND (s, P_BIGAND S))`;

val P_BIGCOND_def = Define
  `(P_BIGCOND [] = P_FALSE) /\
   (P_BIGCOND ((c,b)::l) = P_COND (c, b, P_BIGCOND l))`;

val P_SEM_MIN_def = Define
   `P_SEM_MIN S p = (P_SEM S p /\ !S'. (S' PSUBSET S) ==> ~(P_SEM S' p))`;

val P_PROP_DISJUNCTION_def = Define
  `(P_PROP_DISJUNCTION [] = P_FALSE) /\
   (P_PROP_DISJUNCTION (s::S) = P_OR (P_PROP s, P_PROP_DISJUNCTION S))`;

val P_PROP_CONJUNCTION_def = Define
  `(P_PROP_CONJUNCTION [] = P_TRUE) /\
   (P_PROP_CONJUNCTION (s::S) = P_AND (P_PROP s, P_PROP_CONJUNCTION S))`;

val IS_PROP_DISJUNCTION_def = Define
  `(IS_PROP_DISJUNCTION p = (?S. p = P_PROP_DISJUNCTION S))`;

val IS_PROP_CONJUNCTION_def = Define
  `(IS_PROP_CONJUNCTION p = (?S. p = P_PROP_CONJUNCTION S))`;

val P_MODEL_DISJUNCTION_def = Define
   `P_MODEL_DISJUNCTION S p =
    P_PROP_DISJUNCTION (SET_TO_LIST ({S' | P_SEM S' p} INTER (POW S)))`;

val P_MIN_MODEL_DISJUNCTION_def = Define
   `P_MIN_MODEL_DISJUNCTION S p =
    P_PROP_DISJUNCTION (SET_TO_LIST ({S' | P_SEM_MIN S' p} INTER (POW S)))`;

val P_PROP_SET_MODEL_def = Define
  `(P_PROP_SET_MODEL S S' =
      P_AND (P_PROP_CONJUNCTION (SET_TO_LIST (S INTER S')),
             P_NOT (P_PROP_DISJUNCTION (SET_TO_LIST (S' DIFF S)))))`;

val P_NEGATE_VARS_def = Define
  `(P_NEGATE_VARS (P_TRUE) = P_TRUE) /\
   (P_NEGATE_VARS (P_PROP p) = (P_NOT (P_PROP p))) /\
   (P_NEGATE_VARS (P_NOT b) = (P_NOT(P_NEGATE_VARS b))) /\
   (P_NEGATE_VARS (P_AND(b1,b2)) = P_AND(P_NEGATE_VARS b1, P_NEGATE_VARS b2))`;

Theorem P_NEGATE_VARS_SEM :
    !p s. (P_SEM s (P_NEGATE_VARS p)) = (P_SEM (UNIV DIFF s) p)
Proof
    INDUCT_THEN prop_logic_induct ASSUME_TAC THEN
    ASM_SIMP_TAC std_ss [P_SEM_def, P_NEGATE_VARS_def, IN_DIFF, IN_UNIV]
QED

val P_DUAL_def = Define
   `P_DUAL p = P_NOT (P_NEGATE_VARS p)`;

val P_IS_CONTRADICTION_def = Define
   `P_IS_CONTRADICTION p = (!P. ~(P_SEM P p))`;

val P_IS_TAUTOLOGY_def = Define
   `P_IS_TAUTOLOGY p = (!P. P_SEM P p)`;

val P_ASSIGN_TRUE_def = Define
  `(P_ASSIGN_TRUE V (P_PROP p) = (if p IN V then P_TRUE else P_PROP p)) /\
   (P_ASSIGN_TRUE V P_TRUE = P_TRUE) /\
   (P_ASSIGN_TRUE V (P_NOT b) = P_NOT(P_ASSIGN_TRUE V b)) /\
   (P_ASSIGN_TRUE V (P_AND(b1,b2)) =
      P_AND (P_ASSIGN_TRUE V b1, P_ASSIGN_TRUE V b2))`;

val P_ASSIGN_FALSE_def = Define
  `(P_ASSIGN_FALSE V (P_PROP p) = (if p IN V then P_FALSE else P_PROP p)) /\
   (P_ASSIGN_FALSE V P_TRUE = P_TRUE) /\
   (P_ASSIGN_FALSE V (P_NOT b) = P_NOT(P_ASSIGN_FALSE V b)) /\
   (P_ASSIGN_FALSE V (P_AND(b1,b2)) =
      P_AND (P_ASSIGN_FALSE V b1, P_ASSIGN_FALSE V b2))`;

val P_SUBSTITUTION_def = Define
  `(P_SUBSTITUTION f (P_PROP p) = f p) /\
   (P_SUBSTITUTION f P_TRUE = P_TRUE) /\
   (P_SUBSTITUTION f (P_NOT b) = P_NOT(P_SUBSTITUTION f b)) /\
   (P_SUBSTITUTION f (P_AND(b1,b2)) =
      P_AND (P_SUBSTITUTION f b1, P_SUBSTITUTION f b2))`;

Definition P_EXISTS_def:
  (P_EXISTS [] p = p) /\
  (P_EXISTS (v::l) p =
   P_EXISTS l (P_OR(P_ASSIGN_TRUE {v} p, P_ASSIGN_FALSE {v} p)))
End

val P_FORALL_def = Define
  `(P_FORALL l p = P_NOT (P_EXISTS l (P_NOT p)))`;

Definition VAR_RENAMING_HASHTABLE_def:
  VAR_RENAMING_HASHTABLE S f =
  P_BIGOR (SET_TO_LIST
           (IMAGE (\s. P_AND(P_PROP_SET_MODEL s S, P_PROP(f s))) (POW S)))
End

(******************************************************************************
* Fundamental lemmata about prop logic
******************************************************************************)

Theorem P_SEM_THM:
  !s b1 b2 c b p.
    (P_SEM s (P_TRUE)) /\ ~(P_SEM s (P_FALSE)) /\
    (P_SEM s (P_PROP p) = p IN s) /\
    (P_SEM s (P_NOT b) = ~(P_SEM s b)) /\
    (P_SEM s (P_AND(b1,b2)) = (P_SEM s b1 /\ P_SEM s b2)) /\
    (P_SEM s (P_OR(b1,b2)) = (P_SEM s b1 \/ P_SEM s b2)) /\
    (P_SEM s (P_IMPL(b1,b2)) = (P_SEM s b1 ==> P_SEM s b2)) /\
    (P_SEM s (P_COND(c, b1,b2)) =
     (P_SEM s c /\ P_SEM s b1) \/ (~P_SEM s c /\ P_SEM s b2)) /\
    (P_SEM s (P_EQUIV(b1,b2)) = (P_SEM s b1 = P_SEM s b2))
Proof
    REPEAT GEN_TAC THEN
    EVAL_TAC THEN
    PROVE_TAC[IN_DEF]
QED


Theorem P_USED_VARS_INTER_SUBSET_THM:
  !s p S. (P_USED_VARS p) SUBSET S ==> (P_SEM s p = P_SEM (s INTER S) p)
Proof
   GEN_TAC THEN
   INDUCT_THEN prop_logic_induct ASSUME_TAC THENL [
      SIMP_TAC arith_ss [P_SEM_def, P_USED_VARS_def, INTER_DEF, SUBSET_DEF,
                         IN_SING] THEN
      REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC arith_ss [GSPECIFICATION],

      REWRITE_TAC[P_SEM_THM],

      REWRITE_TAC[P_SEM_THM, P_USED_VARS_def] THEN
      PROVE_TAC[],

      REWRITE_TAC[P_SEM_THM, P_USED_VARS_def, UNION_SUBSET] THEN
      REPEAT STRIP_TAC THEN
      RES_TAC THEN
      ASM_REWRITE_TAC []
   ]
QED


val P_USED_VARS_INTER_THM =
 store_thm
  ("P_USED_VARS_INTER_THM",
   ``!s p. (P_SEM s p = P_SEM (s INTER (P_USED_VARS p)) p)``,

   METIS_TAC  [P_USED_VARS_INTER_SUBSET_THM, SUBSET_REFL]);



val P_USED_VARS_EVAL =
 store_thm
  ("P_USED_VARS_EVAL",
   ``!p b b1 b2. (
    (P_USED_VARS (P_TRUE) = {}) /\
    (P_USED_VARS (P_FALSE) = {}) /\
    (P_USED_VARS (P_PROP p) = {p}) /\
    (P_USED_VARS (P_NOT b) = P_USED_VARS b) /\
    (P_USED_VARS (P_AND(b1, b2)) = P_USED_VARS b1 UNION P_USED_VARS b2) /\
    (P_USED_VARS (P_OR(b1, b2)) = P_USED_VARS b1 UNION P_USED_VARS b2) /\
    (P_USED_VARS (P_IMPL(b1, b2)) = P_USED_VARS b1 UNION P_USED_VARS b2) /\
    (P_USED_VARS (P_EQUIV(b1, b2)) = P_USED_VARS b1 UNION P_USED_VARS b2)
   )``,

  REWRITE_TAC[P_USED_VARS_def, P_FALSE_def, P_OR_def, P_IMPL_def, P_EQUIV_def]>>
  SIMP_TAC std_ss [EXTENSION, IN_UNION] THEN PROVE_TAC[]);





Definition P_VAR_RENAMING_def:
  (P_VAR_RENAMING (f:'a->'b) (P_TRUE) = P_TRUE) /\
  (P_VAR_RENAMING f (P_PROP p) = P_PROP (f p)) /\
  (P_VAR_RENAMING f (P_NOT b) = P_NOT (P_VAR_RENAMING f b)) /\
  (P_VAR_RENAMING f (P_AND(b1,b2)) =
   P_AND(P_VAR_RENAMING f b1, P_VAR_RENAMING f b2))
End


val P_VAR_RENAMING___USED_VARS =
 store_thm
  ("P_VAR_RENAMING___USED_VARS",

   ``!a f. (P_USED_VARS (P_VAR_RENAMING f a) =
       (IMAGE f (P_USED_VARS a)))``,

   INDUCT_THEN prop_logic_induct ASSUME_TAC THENL [

      SIMP_TAC std_ss [P_USED_VARS_def,
                  P_VAR_RENAMING_def,
                  IMAGE_DEF,
                  EXTENSION,
                  GSPECIFICATION,
                  IN_SING,
                  EXISTS_PROD],


      REWRITE_TAC [P_USED_VARS_def, P_VAR_RENAMING_def, IMAGE_EMPTY],
      ASM_REWRITE_TAC [P_USED_VARS_def, P_VAR_RENAMING_def],
      ASM_REWRITE_TAC [P_USED_VARS_def, P_VAR_RENAMING_def, IMAGE_UNION]
   ]);


Theorem P_VAR_RENAMING_EVAL:
  !p f b b1 b2.
    (P_VAR_RENAMING f (P_TRUE) = P_TRUE) /\
    (P_VAR_RENAMING f (P_FALSE) = P_FALSE) /\
    (P_VAR_RENAMING f (P_PROP p) = (P_PROP (f p))) /\
    (P_VAR_RENAMING f (P_NOT b) = P_NOT(P_VAR_RENAMING f b)) /\
    (P_VAR_RENAMING f (P_AND(b1, b2)) =
     P_AND(P_VAR_RENAMING f b1, P_VAR_RENAMING f b2)) /\
    (P_VAR_RENAMING f (P_OR(b1, b2)) =
     P_OR(P_VAR_RENAMING f b1, P_VAR_RENAMING f b2)) /\
    (P_VAR_RENAMING f (P_IMPL(b1, b2)) =
     P_IMPL(P_VAR_RENAMING f b1, P_VAR_RENAMING f b2)) /\
    (P_VAR_RENAMING f (P_EQUIV(b1, b2)) =
     P_EQUIV(P_VAR_RENAMING f b1, P_VAR_RENAMING f  b2))
Proof
  REWRITE_TAC[P_VAR_RENAMING_def,P_FALSE_def,P_OR_def,P_IMPL_def,P_EQUIV_def]
QED

val FINITE___P_USED_VARS =
 store_thm
  ("FINITE___P_USED_VARS",

  ``!p. FINITE(P_USED_VARS p)``,

  INDUCT_THEN prop_logic_induct ASSUME_TAC THENL [
      REWRITE_TAC[P_USED_VARS_def, FINITE_SING],

      REWRITE_TAC[P_USED_VARS_def, FINITE_EMPTY],

      ASM_REWRITE_TAC[P_USED_VARS_def],

      ASM_REWRITE_TAC[P_USED_VARS_def, FINITE_UNION]
  ]);



Theorem IS_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_SEM:
  !p V V' S.
    (IS_POSITIVE_PROP_FORMULA_SUBSET V p /\ P_SEM S p /\ V' SUBSET V ==>
     P_SEM (S UNION V') p) /\
    (IS_NEGATIVE_PROP_FORMULA_SUBSET V p /\ P_SEM (S UNION V') p /\
     V' SUBSET V ==>
     P_SEM S p)
Proof
    INDUCT_THEN prop_logic_induct ASSUME_TAC THEN
    REWRITE_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_def,
        P_SEM_def, IN_UNION] THENL [
        PROVE_TAC[SUBSET_DEF],
        PROVE_TAC[],
        PROVE_TAC[]
    ]
QED


val IS_POSITIVE_NEGATIVE_PROP_FORMULA_SEM =
 store_thm
  ("IS_POSITIVE_NEGATIVE_PROP_FORMULA_SEM",
   ``!p S S'. ((IS_POSITIVE_PROP_FORMULA p /\ P_SEM S p /\ S SUBSET S') ==>
        (P_SEM S' p)) /\
      ((IS_NEGATIVE_PROP_FORMULA p /\ P_SEM S' p /\ S SUBSET S') ==>
        (P_SEM S p))``,

    REWRITE_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_def,
        IS_POSITIVE_PROP_FORMULA_def,
        IS_NEGATIVE_PROP_FORMULA_def] THEN
    REPEAT GEN_TAC THEN
    Cases_on `S SUBSET S'` THEN ASM_REWRITE_TAC[] THEN
    `?V'. V' = S' DIFF S` by PROVE_TAC[] THEN
    `S' = S UNION V'` by (ASM_SIMP_TAC std_ss [UNION_DEF, DIFF_DEF,
        GSPECIFICATION, EXTENSION] THEN PROVE_TAC[SUBSET_DEF]) THEN
    PROVE_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_SEM,
        SUBSET_UNIV]);


val P_PROP_MIN_SEM =
 store_thm
  ("P_PROP_MIN_SEM",
    ``!S1 p. P_SEM_MIN S1 (P_PROP p) = (S1 = {p})``,

    SIMP_TAC std_ss [P_SEM_MIN_def, P_SEM_def, PSUBSET_MEMBER,
        SUBSET_DEF, EXTENSION, IN_SING] THEN
    METIS_TAC[IN_SING]);


val P_PROP_DISJUNCTION_SEM =
 store_thm
  ("P_PROP_DISJUNCTION_SEM",
    ``!S1 S2. P_SEM S1 (P_PROP_DISJUNCTION S2) = (EXISTS (\s. s IN S1) S2)``,

    Induct_on `S2` THENL [
        SIMP_TAC list_ss [P_PROP_DISJUNCTION_def, P_SEM_THM],
        ASM_SIMP_TAC list_ss [P_PROP_DISJUNCTION_def, P_SEM_THM]
    ]);


Theorem P_PROP_DISJUNCTION_MIN_SEM:
  !S1:'a set S2. P_SEM_MIN S1 (P_PROP_DISJUNCTION S2) = EXISTS (\s. S1 = {s}) S2
Proof
    SIMP_TAC std_ss [P_PROP_DISJUNCTION_SEM, P_SEM_MIN_def] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
        FULL_SIMP_TAC std_ss [EXISTS_MEM] THEN
        `~(?S'. S' PSUBSET S1 /\ s IN S')` by PROVE_TAC[] THEN
        FULL_SIMP_TAC std_ss [PSUBSET_DEF] THEN
        `{s} SUBSET S1` by PROVE_TAC[SUBSET_DEF, IN_SING] THEN
        `s IN {s}` by PROVE_TAC[IN_SING] THEN
        PROVE_TAC[],

        `?P. (\s. S1 = {s}) = P` by METIS_TAC[] THEN
        `?Q. (\s. s IN S1) = Q` by METIS_TAC[] THEN
        FULL_SIMP_TAC std_ss [] THEN
        `!e. P e ==>  Q e` by METIS_TAC [IN_SING] THEN
        PROVE_TAC[LIST_EXISTS_MONO],

        FULL_SIMP_TAC std_ss [EXISTS_MEM, PSUBSET_DEF] THEN
        `s' IN S1` by PROVE_TAC[SUBSET_DEF] THEN
        `s' = s` by PROVE_TAC[IN_SING] THEN
        `~(S1 SUBSET S')` by PROVE_TAC[SET_EQ_SUBSET] THEN
        PROVE_TAC[SUBSET_DEF, IN_SING]
    ]
QED


val P_PROP_CONJUNCTION_SEM =
 store_thm
  ("P_PROP_CONJUNCTION_SEM",
    ``!S1 S2. P_SEM S1 (P_PROP_CONJUNCTION S2) = (EVERY (\s. s IN S1) S2)``,

    Induct_on `S2` THEN
    ASM_SIMP_TAC list_ss [P_PROP_CONJUNCTION_def, P_SEM_THM]);


val P_PROP_CONJUNCTION_MIN_SEM =
 store_thm
  ("P_PROP_CONJUNCTION_MIN_SEM",
    ``!S1 S2. P_SEM_MIN S1 (P_PROP_CONJUNCTION S2) = (S1 = LIST_TO_SET S2)``,

    SIMP_TAC list_ss [P_SEM_MIN_def, P_PROP_CONJUNCTION_SEM, EXTENSION,
        LIST_TO_SET] THEN
    Induct_on `S2` THENL [
        SIMP_TAC list_ss [] THEN
        REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
            PROVE_TAC[REST_PSUBSET, MEMBER_NOT_EMPTY],
            PROVE_TAC[PSUBSET_MEMBER]
        ],

        SIMP_TAC list_ss [] THEN
        REPEAT STRIP_TAC THEN
        Cases_on `~(h IN S1)` THEN1 METIS_TAC[] THEN
        FULL_SIMP_TAC std_ss [] THEN
        Cases_on `MEM h S2` THENL [
           `!S'. (~(h IN S')) ==> EXISTS ($~ o (\s. s IN S')) S2` by
                (SIMP_TAC std_ss [EXISTS_MEM] THEN PROVE_TAC[]) THEN
           METIS_TAC[],

           `?S1'. S1' = S1 DELETE h` by PROVE_TAC[] THEN
           `EVERY (\s. s IN S1) S2 = EVERY (\s. s IN S1') S2` by
                (ASM_SIMP_TAC std_ss [EVERY_MEM, IN_DELETE] THEN
                PROVE_TAC[]) THEN
            `S1' PSUBSET S1` by (ASM_SIMP_TAC std_ss [PSUBSET_DEF,
                DELETE_SUBSET, EXTENSION, IN_DELETE] THEN PROVE_TAC[]) THEN
            SUBGOAL_THEN ``
                (!S'. S' PSUBSET S1 ==> ~(h IN S') \/ EXISTS ($~ o (\s. s IN S')) S2) =
                (!S'. S' PSUBSET S1' ==> EXISTS ($~ o (\s. s IN S')) S2)`` ASSUME_TAC THEN1 (

                EQ_TAC THEN REPEAT STRIP_TAC THENL [
                    `(h INSERT S') PSUBSET S1` by (
                        FULL_SIMP_TAC std_ss [PSUBSET_DEF, SUBSET_DEF, IN_INSERT,
                            EXTENSION] THEN
                        METIS_TAC[]) THEN
                    `EXISTS ($~ o (\s. s IN (h INSERT S'))) S2` by METIS_TAC[IN_INSERT] THEN
                    FULL_SIMP_TAC std_ss [EXISTS_MEM, IN_INSERT] THEN
                    PROVE_TAC[],

                    Cases_on `h IN S'` THEN ASM_REWRITE_TAC[] THEN
                    `(S' DELETE h) PSUBSET S1'` by
                        (FULL_SIMP_TAC std_ss [PSUBSET_DEF, SUBSET_DEF, IN_DELETE, EXTENSION] THEN
                        METIS_TAC[]) THEN
                    `EXISTS ($~ o (\s. s IN (S' DELETE h))) S2` by METIS_TAC[] THEN
                    FULL_SIMP_TAC std_ss [EXISTS_MEM, IN_DELETE] THEN
                    PROVE_TAC[]
                ]) THEN
            FULL_SIMP_TAC std_ss [] THEN
            SIMP_TAC std_ss [IN_DELETE] THEN
            METIS_TAC[]
        ]
    ]);




val IS_POSITIVE_PROP_FORMULA___PROP_DISJUNCTION =
 store_thm
  ("IS_POSITIVE_PROP_FORMULA___PROP_DISJUNCTION",
    ``!l. IS_POSITIVE_PROP_FORMULA (P_PROP_DISJUNCTION l)``,

    Induct_on `l` THEN
    FULL_SIMP_TAC std_ss [IS_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_def,
        IS_POSITIVE_PROP_FORMULA_def, P_PROP_DISJUNCTION_def,
        P_FALSE_def, P_OR_def]);


val IS_POSITIVE_PROP_FORMULA___PROP_CONJUNCTION =
 store_thm
  ("IS_POSITIVE_PROP_FORMULA___PROP_CONJUNCTION",
    ``!l. IS_POSITIVE_PROP_FORMULA (P_PROP_CONJUNCTION l)``,

    Induct_on `l` THEN
    FULL_SIMP_TAC std_ss [
        IS_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_def,
        IS_POSITIVE_PROP_FORMULA_def, P_PROP_CONJUNCTION_def]);


val P_USED_VARS___P_PROP_DISJUNCTION =
 store_thm
  ("P_USED_VARS___P_PROP_DISJUNCTION",
    ``!l. P_USED_VARS (P_PROP_DISJUNCTION l) = (LIST_TO_SET l)``,

    Induct_on `l` THEN
    ASM_SIMP_TAC std_ss [P_PROP_DISJUNCTION_def, LIST_TO_SET_THM, P_FALSE_def,
            P_USED_VARS_def, P_OR_def, GSYM INSERT_SING_UNION]);


val P_USED_VARS___P_PROP_CONJUNCTION =
 store_thm
  ("P_USED_VARS___P_PROP_CONJUNCTION",
    ``!l. P_USED_VARS (P_PROP_CONJUNCTION l) = (LIST_TO_SET l)``,

    Induct_on `l` THEN
    ASM_SIMP_TAC std_ss [P_PROP_CONJUNCTION_def, LIST_TO_SET_THM,
            P_USED_VARS_def, GSYM INSERT_SING_UNION]);


val P_BIGAND_SEM =
 store_thm
  ("P_BIGAND_SEM",

    ``!l S. (P_SEM S (P_BIGAND l)) = (!e. (IS_EL e l) ==> P_SEM S e)``,

    Induct_on `l` THEN
    SIMP_TAC list_ss [P_SEM_THM, P_BIGAND_def] THEN
    PROVE_TAC[]);


val P_BIGAND___P_USED_VARS =
 store_thm
  ("P_BIGAND___P_USED_VARS",

  ``!l. (P_USED_VARS (P_BIGAND l) =
        LIST_BIGUNION (MAP (\p. P_USED_VARS p) l))``,

  Induct_on `l` THENL [
    SIMP_TAC std_ss [P_USED_VARS_def, P_BIGAND_def, MAP, LIST_BIGUNION_def],
    ASM_SIMP_TAC std_ss [P_USED_VARS_def, P_BIGAND_def, MAP, LIST_BIGUNION_def]
  ]);



val P_BIGOR_SEM =
 store_thm
  ("P_BIGOR_SEM",

    ``!l S. (P_SEM S (P_BIGOR l)) = (?e. (IS_EL e l) /\ P_SEM S e)``,

    Induct_on `l` THEN
    SIMP_TAC list_ss [P_SEM_THM, P_BIGOR_def] THEN
    PROVE_TAC[]);


val P_BIGOR___P_USED_VARS =
 store_thm
  ("P_BIGOR___P_USED_VARS",

  ``!l. (P_USED_VARS (P_BIGOR l) =
        LIST_BIGUNION (MAP (\p. P_USED_VARS p) l))``,

  Induct_on `l` THENL [
    SIMP_TAC std_ss [P_USED_VARS_def, P_BIGOR_def, MAP, LIST_BIGUNION_def, P_FALSE_def],
    ASM_SIMP_TAC std_ss [P_USED_VARS_def, P_OR_def, P_BIGOR_def, MAP, LIST_BIGUNION_def]
  ]);


Theorem P_SEM_MIN_MODEL_EXISTS_FINITE[local]:
  !n p S. FINITE S /\ CARD S < n ==> P_SEM S p ==>
          ?S'. S' SUBSET S /\ P_SEM_MIN S' p
Proof
    Induct_on `n` THENL [
        SIMP_TAC arith_ss [],

        REPEAT STRIP_TAC THEN
        Cases_on `P_SEM_MIN S p` THENL [
            PROVE_TAC[SUBSET_REFL],

            FULL_SIMP_TAC std_ss [P_SEM_MIN_def] THEN1
            PROVE_TAC[] THEN
            `FINITE S'` by PROVE_TAC[PSUBSET_FINITE] THEN
            `CARD S' < CARD S` by PROVE_TAC[CARD_PSUBSET] THEN
            `CARD S' < n` by DECIDE_TAC THEN
            RES_TAC THEN
            EXISTS_TAC ``S'':'a set`` THEN
            ASM_REWRITE_TAC[] THEN
            PROVE_TAC[SUBSET_TRANS, PSUBSET_DEF]
        ]
    ]
QED


val P_SEM_MIN_MODEL_EXISTS =
 store_thm
  ("P_SEM_MIN_MODEL_EXISTS",

    ``!p S. (P_SEM S p ==> (?S'. FINITE S' /\ S' SUBSET S /\ P_SEM_MIN S' p))``,

    REPEAT STRIP_TAC THEN
    `?T'. P_USED_VARS p = T'` by PROVE_TAC[] THEN
    `P_SEM (S INTER T') p` by PROVE_TAC[P_USED_VARS_INTER_THM] THEN
    `FINITE (S INTER T')` by PROVE_TAC[FINITE___P_USED_VARS,
        INTER_FINITE, INTER_COMM] THEN
    `(S INTER T') SUBSET S` by PROVE_TAC[INTER_SUBSET] THEN
    `CARD (S INTER T') < SUC (CARD (S INTER T'))` by DECIDE_TAC THEN
    PROVE_TAC[SUBSET_TRANS, SUBSET_FINITE,
        P_SEM_MIN_MODEL_EXISTS_FINITE]);


val P_PROP_SET_MODEL_SEM =
 store_thm
  ("P_PROP_SET_MODEL_SEM",
    ``!S S' S''. FINITE S' ==> (P_SEM S'' (P_PROP_SET_MODEL S S') = (S'' INTER S' = S INTER S'))``,

    REWRITE_TAC[P_PROP_SET_MODEL_def, P_SEM_THM, P_PROP_DISJUNCTION_SEM,
    P_PROP_CONJUNCTION_SEM, EXISTS_MEM, EVERY_MEM] THEN

    REPEAT STRIP_TAC THEN
    `FINITE (S INTER S')` by PROVE_TAC[INTER_FINITE, INTER_COMM] THEN
    `FINITE (S' DIFF S)` by PROVE_TAC[FINITE_DIFF] THEN
    FULL_SIMP_TAC std_ss [MEM_SET_TO_LIST, IN_INTER, IN_DIFF, EXTENSION] THEN
    PROVE_TAC[]);


val P_ASSIGN_TRUE_SEM =
 store_thm
  ("P_ASSIGN_TRUE_SEM",

    ``!p s V. P_SEM s (P_ASSIGN_TRUE V p) =
        P_SEM (s UNION V) p``,

    INDUCT_THEN prop_logic_induct ASSUME_TAC THEN
    ASM_REWRITE_TAC[P_ASSIGN_TRUE_def, P_SEM_def] THEN

    REWRITE_TAC[IN_UNION] THEN
    Cases_on `a IN V` THEN
    REWRITE_TAC[P_SEM_def]);


val P_ASSIGN_FALSE_SEM =
 store_thm
  ("P_ASSIGN_FALSE_SEM",

    ``!p s V. P_SEM s (P_ASSIGN_FALSE V p) =
        P_SEM (s DIFF V) p``,

    INDUCT_THEN prop_logic_induct ASSUME_TAC THEN
    ASM_REWRITE_TAC[P_ASSIGN_FALSE_def, P_SEM_def] THEN

    REWRITE_TAC[IN_DIFF] THEN
    Cases_on `a IN V` THEN
    REWRITE_TAC[P_SEM_THM]);



val P_SUBSTITUTION_SEM =
 store_thm
  ("P_SUBSTITUTION_SEM",

    ``!p s f. P_SEM s (P_SUBSTITUTION f p) =
        P_SEM {v | P_SEM s (f v)} p``,

    INDUCT_THEN prop_logic_induct ASSUME_TAC THEN
    ASM_SIMP_TAC std_ss [P_SUBSTITUTION_def, P_SEM_def, GSPECIFICATION]);



val P_EXISTS_SEM =
 store_thm
  ("P_EXISTS_SEM",

    ``!s l p. (P_SEM s (P_EXISTS l p) =
        (?l'. (l' SUBSET (LIST_TO_SET l)) /\ (P_SEM ((s DIFF (LIST_TO_SET l)) UNION l') p)))``,

    Induct_on `l` THENL [
        SIMP_TAC list_ss [LIST_TO_SET_THM, SUBSET_EMPTY, P_EXISTS_def, UNION_EMPTY,
            DIFF_EMPTY],

        ASM_SIMP_TAC list_ss [P_EXISTS_def, LIST_TO_SET_THM, P_SEM_THM, P_ASSIGN_TRUE_SEM,
            P_ASSIGN_FALSE_SEM] THEN
        REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
            EXISTS_TAC ``h INSERT l'`` THEN
            REPEAT STRIP_TAC THENL [
                FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT] THEN PROVE_TAC[],

                `s DIFF (h INSERT LIST_TO_SET l) UNION (h INSERT l') =
                s DIFF LIST_TO_SET l UNION l' UNION {h}` by
                    (SIMP_TAC std_ss [INSERT_DEF, UNION_DEF, DIFF_DEF, GSPECIFICATION, EXTENSION,
                        NOT_IN_EMPTY] THEN
                    PROVE_TAC[]) THEN
                ASM_REWRITE_TAC[]
            ],

            EXISTS_TAC ``l' DELETE h`` THEN
            REPEAT STRIP_TAC THENL [
                FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT, IN_DELETE],

                `s DIFF (h INSERT LIST_TO_SET l) UNION (l' DELETE h) =
                s DIFF LIST_TO_SET l UNION l' DIFF {h}` by
                    (SIMP_TAC std_ss [INSERT_DEF, UNION_DEF, DIFF_DEF, GSPECIFICATION, EXTENSION,
                        NOT_IN_EMPTY, DELETE_DEF] THEN
                    PROVE_TAC[]) THEN
                ASM_REWRITE_TAC[]
            ],

            EXISTS_TAC ``l' DELETE h`` THEN
            REPEAT STRIP_TAC THENL [
                FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_INSERT, IN_DELETE] THEN PROVE_TAC[],

                `(s DIFF LIST_TO_SET l UNION (l' DELETE h) UNION {h} =
                s DIFF (h INSERT LIST_TO_SET l) UNION l') \/
                (s DIFF LIST_TO_SET l UNION (l' DELETE h) DIFF {h} =
                s DIFF (h INSERT LIST_TO_SET l) UNION l')` by
                    (SIMP_TAC std_ss [INSERT_DEF, UNION_DEF, DIFF_DEF, GSPECIFICATION, EXTENSION,
                        NOT_IN_EMPTY, DELETE_DEF] THEN
                    METIS_TAC[]) THEN
                ASM_REWRITE_TAC[]
            ]
        ]
    ]);


val P_FORALL_SEM =
 store_thm
  ("P_FORALL_SEM",

    ``!s l p. (P_SEM s (P_FORALL l p) =
        (!l'. (l' SUBSET (LIST_TO_SET l)) ==> (P_SEM ((s DIFF (LIST_TO_SET l)) UNION l') p)))``,

    REWRITE_TAC[P_FORALL_def, P_SEM_THM, P_EXISTS_SEM] THEN
    PROVE_TAC[]);




val P_SEM___VAR_RENAMING___NOT_INJ =
  store_thm (
    "P_SEM___VAR_RENAMING___NOT_INJ",
      ``!p f s. P_SEM s (P_VAR_RENAMING f p) = P_SEM (\x. f x IN s) p``,

    INDUCT_THEN prop_logic_induct ASSUME_TAC THEN (
      ASM_SIMP_TAC std_ss [P_VAR_RENAMING_def, P_SEM_def, IN_ABS]
    ));



val P_SEM___VAR_RENAMING =
 store_thm
  ("P_SEM___VAR_RENAMING",
   ``!p f s. (INJ f (s UNION P_USED_VARS p) UNIV) ==> ((P_SEM s p) = (P_SEM (IMAGE f s) (P_VAR_RENAMING f p)))``,

   SIMP_TAC std_ss [INJ_DEF, IN_UNIV, IN_UNION] THEN
   INDUCT_THEN prop_logic_induct ASSUME_TAC THENL [
      SIMP_TAC std_ss [P_USED_VARS_def, P_SEM_def, P_VAR_RENAMING_def,
        IN_SING, IN_IMAGE] THEN
      PROVE_TAC[],

      SIMP_TAC std_ss [P_SEM_def, P_VAR_RENAMING_def],

      SIMP_TAC std_ss [P_SEM_def, P_VAR_RENAMING_def, P_USED_VARS_def] THEN
      ASM_REWRITE_TAC[],

      SIMP_TAC std_ss [P_SEM_def, P_VAR_RENAMING_def, P_USED_VARS_def, IN_UNION] THEN
      METIS_TAC[]
   ]);




val P_MIN_MODEL_DISJUNCTION_SEM =
 store_thm
  ("P_MIN_MODEL_DISJUNCTION_SEM",

    ``!S1 S2 p. FINITE S2 ==> ((P_SEM S1 (P_MIN_MODEL_DISJUNCTION S2 p)) = (?s. s IN S1 /\ s SUBSET S2 /\ P_SEM_MIN s p))``,

    REPEAT STRIP_TAC THEN
    REWRITE_TAC[P_MIN_MODEL_DISJUNCTION_def, P_PROP_DISJUNCTION_SEM, EXISTS_MEM] THEN
    `FINITE (POW S2)` by PROVE_TAC[FINITE_POW_IFF] THEN
    `?M. M = ({S' | P_SEM_MIN S' p} INTER POW S2)` by PROVE_TAC[] THEN
    `M SUBSET (POW S2)` by PROVE_TAC[INTER_SUBSET] THEN
    `FINITE M` by PROVE_TAC[SUBSET_FINITE] THEN
    FULL_SIMP_TAC list_ss [MEM_SET_TO_LIST] THEN
    `!e. (IS_EL e (SET_TO_LIST ({S' | P_SEM_MIN S' p} INTER POW S2))) =
        (e IN  ({S' | P_SEM_MIN S' p} INTER POW S2))` by PROVE_TAC[MEM_SET_TO_LIST] THEN
    ASM_SIMP_TAC std_ss [IN_POW, IN_INTER, GSPECIFICATION] THEN
    PROVE_TAC[]);


val P_MODEL_DISJUNCTION_SEM =
 store_thm
  ("P_MODEL_DISJUNCTION_SEM",

    ``!S1 S2 p. FINITE S2 ==> ((P_SEM S1 (P_MODEL_DISJUNCTION S2 p)) = (?s. s IN S1 /\ s SUBSET S2 /\ P_SEM s p))``,

    REPEAT STRIP_TAC THEN
    REWRITE_TAC[P_MODEL_DISJUNCTION_def, P_PROP_DISJUNCTION_SEM, EXISTS_MEM] THEN
    `FINITE (POW S2)` by PROVE_TAC[FINITE_POW_IFF] THEN
    `?M. M = ({S' | P_SEM S' p} INTER POW S2)` by PROVE_TAC[] THEN
    `M SUBSET (POW S2)` by PROVE_TAC[INTER_SUBSET] THEN
    `FINITE M` by PROVE_TAC[SUBSET_FINITE] THEN
    FULL_SIMP_TAC list_ss [MEM_SET_TO_LIST] THEN
    `!e. (IS_EL e (SET_TO_LIST ({S' | P_SEM S' p} INTER POW S2))) =
        (e IN  ({S' | P_SEM S' p} INTER POW S2))` by PROVE_TAC[MEM_SET_TO_LIST] THEN
    ASM_SIMP_TAC std_ss [IN_POW, IN_INTER, GSPECIFICATION] THEN
    PROVE_TAC[]);


val P_MIN_MODEL_DISJUNCTION_MIN_SEM =
 store_thm
  ("P_MIN_MODEL_DISJUNCTION_MIN_SEM",

    ``!S1 S2 p. FINITE S2 ==> ((P_SEM_MIN S1 (P_MIN_MODEL_DISJUNCTION S2 p)) = (?s. (S1 = {s}) /\ s SUBSET S2 /\ P_SEM_MIN s p))``,

    REPEAT STRIP_TAC THEN
    REWRITE_TAC[P_MIN_MODEL_DISJUNCTION_def, P_PROP_DISJUNCTION_MIN_SEM, EXISTS_MEM] THEN
    `FINITE (POW S2)` by PROVE_TAC[FINITE_POW_IFF] THEN
    `?M. M = ({S' | P_SEM_MIN S' p} INTER POW S2)` by PROVE_TAC[] THEN
    `M SUBSET (POW S2)` by PROVE_TAC[INTER_SUBSET] THEN
    `FINITE M` by PROVE_TAC[SUBSET_FINITE] THEN
    FULL_SIMP_TAC list_ss [MEM_SET_TO_LIST] THEN
    `!e. (IS_EL e (SET_TO_LIST ({S' | P_SEM_MIN S' p} INTER POW S2))) =
        (e IN  ({S' | P_SEM_MIN S' p} INTER POW S2))` by PROVE_TAC[MEM_SET_TO_LIST] THEN
    ASM_SIMP_TAC std_ss [IN_POW, IN_INTER, GSPECIFICATION] THEN
    PROVE_TAC[]);


val P_MODEL_DISJUNCTION_MIN_SEM =
 store_thm
  ("P_MODEL_DISJUNCTION_MIN_SEM",

    ``!S1 S2 p. FINITE S2 ==> ((P_SEM_MIN S1 (P_MODEL_DISJUNCTION S2 p)) = (?s. (S1 = {s}) /\ s SUBSET S2 /\ P_SEM s p))``,

    REPEAT STRIP_TAC THEN
    REWRITE_TAC[P_MODEL_DISJUNCTION_def, P_PROP_DISJUNCTION_MIN_SEM, EXISTS_MEM] THEN
    `FINITE (POW S2)` by PROVE_TAC[FINITE_POW_IFF] THEN
    `?M. M = ({S' | P_SEM S' p} INTER POW S2)` by PROVE_TAC[] THEN
    `M SUBSET (POW S2)` by PROVE_TAC[INTER_SUBSET] THEN
    `FINITE M` by PROVE_TAC[SUBSET_FINITE] THEN
    FULL_SIMP_TAC list_ss [MEM_SET_TO_LIST] THEN
    `!e. (IS_EL e (SET_TO_LIST ({S' | P_SEM S' p} INTER POW S2))) =
        (e IN  ({S' | P_SEM S' p} INTER POW S2))` by PROVE_TAC[MEM_SET_TO_LIST] THEN
    ASM_SIMP_TAC std_ss [IN_POW, IN_INTER, GSPECIFICATION] THEN
    PROVE_TAC[]);


val P_DUAL_MODELS_THM =
 store_thm
  ("P_DUAL_MODELS_THM",
    ``!p. (IS_POSITIVE_PROP_FORMULA p ==> (!S. (P_SEM S (P_DUAL p)) =
        (!S'. (P_SEM S' p) ==> (~(DISJOINT S S'))))) /\
        (IS_NEGATIVE_PROP_FORMULA p ==> (!S. ~(P_SEM S (P_DUAL p)) =
        (!S'. (~P_SEM S' p) ==> (~(DISJOINT S S')))))``,

    SIMP_TAC std_ss  [IS_POSITIVE_PROP_FORMULA_def, P_DUAL_def,  P_SEM_def, NOT_IN_EMPTY, GSPECIFICATION,
    IS_NEGATIVE_PROP_FORMULA_def, P_NEGATE_VARS_SEM, DISJOINT_DEF, INTER_DEF, EXTENSION, P_SEM_MIN_def] THEN
    INDUCT_THEN prop_logic_induct ASSUME_TAC THEN
    SIMP_TAC std_ss [IS_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_def, P_SEM_def, IN_DIFF, IN_UNIV] THENL [
        PROVE_TAC[IN_SING],
        PROVE_TAC[NOT_IN_EMPTY],
        PROVE_TAC[],

        REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC std_ss [] THEN
        EQ_TAC THEN REPEAT STRIP_TAC THENL [
            METIS_TAC[],
            METIS_TAC[],

            Cases_on `!S'. P_SEM S' p' ==> ?x. x IN S /\ x IN S'` THEN ASM_REWRITE_TAC[] THEN
            REPEAT STRIP_TAC THEN
            FULL_SIMP_TAC std_ss [GSYM IS_POSITIVE_PROP_FORMULA_def] THEN
            `?T'. T' = S' UNION S''` by PROVE_TAC[] THEN
            `P_SEM T' p /\ P_SEM T' p'` by METIS_TAC[IS_POSITIVE_NEGATIVE_PROP_FORMULA_SEM,
                SUBSET_UNION] THEN
            `?x. x IN S /\ x IN T'` by PROVE_TAC[] THEN
            `x IN S'` by PROVE_TAC[IN_UNION] THEN
            PROVE_TAC[],

            METIS_TAC[],
            METIS_TAC[],
            METIS_TAC[],
            METIS_TAC[]
        ]
    ]);


val P_DUAL_MIN_MODELS_THM =
 store_thm
  ("P_DUAL_MIN_MODELS_THM",
    ``!p. IS_POSITIVE_PROP_FORMULA p ==> (!S. (P_SEM S (P_DUAL p)) =
        (!S'. (P_SEM_MIN S' p) ==> (~(DISJOINT S S'))))``,

    REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
        PROVE_TAC[P_DUAL_MODELS_THM, P_SEM_MIN_def],

        Tactical.REVERSE (SUBGOAL_THEN ``!S'. P_SEM S' p ==> ~DISJOINT S S'`` ASSUME_TAC) THEN1 (
            PROVE_TAC[P_DUAL_MODELS_THM]
        ) THEN
        REPEAT STRIP_TAC THEN
        `?S''. S'' SUBSET S' /\ P_SEM_MIN S'' p` by PROVE_TAC[P_SEM_MIN_MODEL_EXISTS] THEN
        `~(DISJOINT S S'')` by PROVE_TAC[] THEN
        PROVE_TAC[DISJOINT_SUBSET]
    ]);



val P_NEGATE_VARS___IS_POSITIVE_NEGATIVE_PROP_FORMULA =
 store_thm
  ("P_NEGATE_VARS___IS_POSITIVE_NEGATIVE_PROP_FORMULA",
    ``!p. (IS_POSITIVE_PROP_FORMULA p ==> IS_NEGATIVE_PROP_FORMULA (P_NEGATE_VARS p)) /\
             (IS_NEGATIVE_PROP_FORMULA p ==> IS_POSITIVE_PROP_FORMULA (P_NEGATE_VARS p))``,

    REWRITE_TAC[IS_POSITIVE_PROP_FORMULA_def, IS_NEGATIVE_PROP_FORMULA_def] THEN
    INDUCT_THEN prop_logic_induct ASSUME_TAC THEN
    ASM_SIMP_TAC std_ss [IS_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_def, P_NEGATE_VARS_def]);


val P_DUAL___IS_POSITIVE_NEGATIVE_PROP_FORMULA =
 store_thm
  ("P_DUAL___IS_POSITIVE_NEGATIVE_PROP_FORMULA",
    ``!p. (IS_POSITIVE_PROP_FORMULA p ==> IS_POSITIVE_PROP_FORMULA (P_DUAL p)) /\
            (IS_NEGATIVE_PROP_FORMULA p ==> IS_NEGATIVE_PROP_FORMULA (P_DUAL p))``,

    REWRITE_TAC[IS_POSITIVE_PROP_FORMULA_def, IS_NEGATIVE_PROP_FORMULA_def, P_DUAL_def,
        IS_POSITIVE_NEGATIVE_PROP_FORMULA_SUBSET_def] THEN
    REWRITE_TAC [GSYM IS_POSITIVE_PROP_FORMULA_def, GSYM IS_NEGATIVE_PROP_FORMULA_def,
        P_NEGATE_VARS___IS_POSITIVE_NEGATIVE_PROP_FORMULA]);



val VAR_RENAMING_HASHTABLE_SEM =
 store_thm
  ("VAR_RENAMING_HASHTABLE_SEM",

    ``!s S f. (FINITE S) ==> ((P_SEM s (VAR_RENAMING_HASHTABLE S f)) =
                  (f (s INTER S) IN s))``,

    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [VAR_RENAMING_HASHTABLE_def, P_BIGOR_SEM,
        FINITE_POW_IFF, IMAGE_FINITE, MEM_SET_TO_LIST, IN_IMAGE,
        GSYM LEFT_EXISTS_AND_THM, IN_POW, P_SEM_THM,
        P_PROP_SET_MODEL_SEM] THEN
    EQ_TAC THEN REPEAT STRIP_TAC THENL [
        PROVE_TAC[SUBSET_INTER_ABSORPTION],

        EXISTS_TAC ``s INTER S`` THEN
        ASM_REWRITE_TAC[INTER_SUBSET, INTER_INTER_ABSORPTION]
    ]);


val P_BIGAND___APPEND =
 store_thm
  ("P_BIGAND___APPEND",

``!C1 C2. PROP_LOGIC_EQUIVALENT (P_BIGAND (C1++C2)) (P_AND(P_BIGAND C1, P_BIGAND C2))``,

  SIMP_TAC std_ss [PROP_LOGIC_EQUIVALENT_def] THEN
  REPEAT STRIP_TAC THEN
  Induct_on `C1` THENL [
    SIMP_TAC list_ss [P_BIGAND_def, P_SEM_THM],

    ASM_SIMP_TAC list_ss [P_BIGAND_def, P_SEM_THM] THEN
    PROVE_TAC[]
  ]);


val P_ASSIGN_TRUE_FALSE___P_USED_VARS =
  store_thm ("P_ASSIGN_TRUE_FALSE___P_USED_VARS",
    ``!p v.
    (P_USED_VARS (P_ASSIGN_TRUE v p) =
    P_USED_VARS p DIFF v) /\
    (P_USED_VARS (P_ASSIGN_FALSE v p) =
    P_USED_VARS p DIFF v)``,

    INDUCT_THEN prop_logic_induct ASSUME_TAC THENL [
      REWRITE_TAC [P_ASSIGN_TRUE_def, P_ASSIGN_FALSE_def] THEN
      REPEAT GEN_TAC THEN
      Cases_on `a IN v` THEN (
        ASM_SIMP_TAC std_ss [P_USED_VARS_EVAL, EXTENSION, IN_DIFF,
          IN_SING, NOT_IN_EMPTY] THEN
        PROVE_TAC[]
      ),

      SIMP_TAC std_ss [P_ASSIGN_TRUE_def, P_USED_VARS_EVAL, EMPTY_DIFF,
                      P_ASSIGN_FALSE_def],

      ASM_SIMP_TAC std_ss [P_ASSIGN_TRUE_def, P_ASSIGN_FALSE_def, P_USED_VARS_EVAL],

      ASM_SIMP_TAC std_ss [P_ASSIGN_TRUE_def, P_ASSIGN_FALSE_def, P_USED_VARS_EVAL, UNION_OVER_DIFF]
    ]);


val P_ASSIGN_TRUE_FALSE___EVAL =
  store_thm ("P_ASSIGN_TRUE_FALSE___EVAL",
    ``(P_ASSIGN_TRUE V (P_PROP p) = (if p IN V then P_TRUE else P_PROP p)) /\
      (P_ASSIGN_TRUE V P_TRUE = P_TRUE) /\
      (P_ASSIGN_TRUE V P_FALSE = P_FALSE) /\
      (P_ASSIGN_TRUE V (P_NOT b) = P_NOT(P_ASSIGN_TRUE V b)) /\
      (P_ASSIGN_TRUE V (P_AND(b1,b2)) = P_AND (P_ASSIGN_TRUE V b1, P_ASSIGN_TRUE V b2)) /\
      (P_ASSIGN_TRUE V (P_OR(b1,b2)) = P_OR (P_ASSIGN_TRUE V b1, P_ASSIGN_TRUE V b2)) /\
      (P_ASSIGN_TRUE V (P_IMPL(b1,b2)) = P_IMPL (P_ASSIGN_TRUE V b1, P_ASSIGN_TRUE V b2)) /\
      (P_ASSIGN_TRUE V (P_COND(c, b1,b2)) = P_COND (P_ASSIGN_TRUE V c, P_ASSIGN_TRUE V b1, P_ASSIGN_TRUE V b2)) /\
      (P_ASSIGN_TRUE V (P_EQUIV(b1,b2)) = P_EQUIV (P_ASSIGN_TRUE V b1, P_ASSIGN_TRUE V b2)) /\

      (P_ASSIGN_FALSE V (P_PROP p) = (if p IN V then P_FALSE else P_PROP p)) /\
      (P_ASSIGN_FALSE V P_TRUE = P_TRUE) /\
      (P_ASSIGN_FALSE V P_FALSE = P_FALSE) /\
      (P_ASSIGN_FALSE V (P_NOT b) = P_NOT(P_ASSIGN_FALSE V b)) /\
      (P_ASSIGN_FALSE V (P_AND(b1,b2)) = P_AND (P_ASSIGN_FALSE V b1, P_ASSIGN_FALSE V b2)) /\
      (P_ASSIGN_FALSE V (P_OR(b1,b2)) = P_OR (P_ASSIGN_FALSE V b1, P_ASSIGN_FALSE V b2)) /\
      (P_ASSIGN_FALSE V (P_IMPL(b1,b2)) = P_IMPL (P_ASSIGN_FALSE V b1, P_ASSIGN_FALSE V b2)) /\
      (P_ASSIGN_FALSE V (P_COND(c, b1,b2)) = P_COND (P_ASSIGN_FALSE V c, P_ASSIGN_FALSE V b1, P_ASSIGN_FALSE V b2)) /\
      (P_ASSIGN_FALSE V (P_EQUIV(b1,b2)) = P_EQUIV (P_ASSIGN_FALSE V b1, P_ASSIGN_FALSE V b2))``,

  SIMP_TAC std_ss [P_ASSIGN_TRUE_def, P_ASSIGN_FALSE_def, P_FALSE_def, P_EQUIV_def, P_IMPL_def, P_OR_def, P_COND_def]);



val P_EXISTS___P_USED_VARS =
  store_thm ("P_EXISTS___P_USED_VARS",
    ``!l p.
      P_USED_VARS (P_EXISTS l p) =
      P_USED_VARS p DIFF (LIST_TO_SET l)``,

  Induct_on `l` THENL [
    SIMP_TAC std_ss [P_EXISTS_def, LIST_TO_SET_THM, DIFF_EMPTY],

    ASM_SIMP_TAC std_ss [P_EXISTS_def, LIST_TO_SET_THM, DIFF_EMPTY,
      P_USED_VARS_EVAL, P_ASSIGN_TRUE_FALSE___P_USED_VARS] THEN
    SIMP_TAC std_ss [EXTENSION, IN_UNION, IN_DIFF, IN_SING, IN_INSERT] THEN
    PROVE_TAC[]
  ])


val P_FORALL___P_USED_VARS =
  store_thm ("P_FORALL___P_USED_VARS",
    ``!l p.
      P_USED_VARS (P_FORALL l p) =
      P_USED_VARS p DIFF (LIST_TO_SET l)``,

  REWRITE_TAC[P_FORALL_def, P_USED_VARS_def, P_EXISTS___P_USED_VARS]);


val P_PROP_SET_MODEL___P_USED_VARS =
  store_thm ("P_PROP_SET_MODEL___P_USED_VARS",
    ``!S1 S2. FINITE S2 ==>
      (P_USED_VARS (P_PROP_SET_MODEL S1 S2) = S2)``,

  SIMP_TAC std_ss [P_PROP_SET_MODEL_def, P_USED_VARS_EVAL,
    P_USED_VARS___P_PROP_DISJUNCTION, P_USED_VARS___P_PROP_CONJUNCTION] THEN
  REPEAT STRIP_TAC THEN
  `FINITE (S1 INTER S2)` by PROVE_TAC[INTER_FINITE, INTER_COMM] THEN
  `FINITE (S2 DIFF S1)` by PROVE_TAC[FINITE_DIFF] THEN
  ASM_SIMP_TAC std_ss [SET_TO_LIST_INV] THEN
  SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF] THEN
  PROVE_TAC[]
);



val VAR_RENAMING_HASHTABLE_LIST_def =
Define
  `(VAR_RENAMING_HASHTABLE_LIST [] S f = P_PROP (f S)) /\
   (VAR_RENAMING_HASHTABLE_LIST (e::l) S f =
      P_OR (P_AND (P_PROP e, VAR_RENAMING_HASHTABLE_LIST l (e INSERT S) f),
            P_AND (P_NOT (P_PROP e), VAR_RENAMING_HASHTABLE_LIST l S f)))`


val VAR_RENAMING_HASHTABLE_LIST___CLEAN_VAR_SET =
  store_thm ("VAR_RENAMING_HASHTABLE_LIST___CLEAN_VAR_SET",
    ``!l f S.
(VAR_RENAMING_HASHTABLE_LIST l S f) =
(VAR_RENAMING_HASHTABLE_LIST l EMPTY (\x. f (x UNION S)))``,

Induct_on `l` THENL [
  SIMP_TAC std_ss [VAR_RENAMING_HASHTABLE_LIST_def, UNION_EMPTY],

  SIMP_TAC std_ss [VAR_RENAMING_HASHTABLE_LIST_def] THEN
  ONCE_ASM_REWRITE_TAC[] THEN
  SIMP_TAC std_ss [UNION_EMPTY, UNION_INSERT]
]);



val VAR_RENAMING_HASHTABLE_LIST___FUN_RESTRICT =
  store_thm ("VAR_RENAMING_HASHTABLE_LIST___FUN_RESTRICT",
    ``!l S f f'. (!s. s SUBSET (S UNION LIST_TO_SET l) ==> (f s = f' s)) ==>
    (VAR_RENAMING_HASHTABLE_LIST l S f =
    VAR_RENAMING_HASHTABLE_LIST l S f')``,

Induct_on `l` THENL [
  SIMP_TAC std_ss [VAR_RENAMING_HASHTABLE_LIST_def] THEN
  PROVE_TAC[SUBSET_REFL, SUBSET_TRANS, SUBSET_UNION],

  SIMP_TAC std_ss [VAR_RENAMING_HASHTABLE_LIST_def, prop_logic_11,
    P_OR_def] THEN
  REPEAT STRIP_TAC THENL [
    Q_SPECL_NO_ASSUM 1 [`h INSERT S`, `f`, `f'`] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 (
      SIMP_ALL_TAC list_ss [SUBSET_DEF, IN_UNION, IN_INSERT,
        LIST_TO_SET] THEN
      PROVE_TAC[]
    ) THEN
    ASM_REWRITE_TAC[],

    Q_SPECL_NO_ASSUM 1 [`S`, `f`, `f'`] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 (
      SIMP_ALL_TAC list_ss [SUBSET_DEF, IN_UNION, IN_INSERT,
        LIST_TO_SET] THEN
      PROVE_TAC[]
    ) THEN
    ASM_REWRITE_TAC[]
  ]
]);



val VAR_RENAMING_HASHTABLE_LIST___EQUIVALENT_HASHTABLE_SET =
  store_thm ("VAR_RENAMING_HASHTABLE_LIST___EQUIVALENT_HASHTABLE_SET",
  ``!l f.
  (PROP_LOGIC_EQUIVALENT (VAR_RENAMING_HASHTABLE (LIST_TO_SET l) f)
                        (VAR_RENAMING_HASHTABLE_LIST l EMPTY f))``,

REWRITE_TAC[PROP_LOGIC_EQUIVALENT_def] THEN
Induct_on `l` THENL [
  SIMP_TAC std_ss [LIST_TO_SET_THM,  VAR_RENAMING_HASHTABLE_def,
                   VAR_RENAMING_HASHTABLE_LIST_def, P_SEM_def,
  P_BIGOR_SEM, POW_EQNS, IMAGE_SING, MEM_SET_TO_LIST,
  FINITE_SING, IN_SING, P_PROP_SET_MODEL_SEM, FINITE_EMPTY,
  INTER_EMPTY],

  POP_ASSUM (ASSUME_TAC o GSYM) THEN
  REWRITE_TAC [VAR_RENAMING_HASHTABLE_LIST_def] THEN
  ONCE_REWRITE_TAC[VAR_RENAMING_HASHTABLE_LIST___CLEAN_VAR_SET] THEN
  ASM_SIMP_TAC std_ss [LIST_TO_SET_THM, P_SEM_THM,
    VAR_RENAMING_HASHTABLE_def, P_BIGOR_SEM, MEM_SET_TO_LIST,
    FINITE_LIST_TO_SET, FINITE_POW_IFF, FINITE_INSERT, IMAGE_FINITE,
    IN_IMAGE, UNION_EMPTY, GSYM LEFT_EXISTS_AND_THM,
    P_PROP_SET_MODEL_SEM] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
    Cases_on `h IN s` THEN ASM_REWRITE_TAC [] THENL [
      Cases_on `MEM h l` THENL [
        Q_TAC EXISTS_TAC `s'` THEN
        SUBGOAL_TAC `h INSERT LIST_TO_SET l = LIST_TO_SET l` THEN1 (
          SIMP_TAC std_ss [EXTENSION, IN_INSERT,
            LIST_TO_SET] THEN
          PROVE_TAC[]
        ) THEN
        SUBGOAL_TAC `s' UNION {h} = s'` THEN1 (
          SIMP_ALL_TAC std_ss [EXTENSION, IN_INSERT, IN_INTER, IN_UNION,
            IN_SING] THEN
          PROVE_TAC[]
        ) THEN
        PROVE_TAC[],

        Q_TAC EXISTS_TAC `s' DELETE h` THEN
        SUBGOAL_TAC `h IN s'` THEN1 (
          SIMP_ALL_TAC std_ss [EXTENSION, IN_INTER, IN_INSERT] THEN
          PROVE_TAC[]
        ) THEN
        ASM_SIMP_TAC std_ss [UNION_SING, INSERT_DELETE] THEN
        REPEAT STRIP_TAC THEN (
          SIMP_ALL_TAC std_ss [IN_POW, SUBSET_DEF, IN_INSERT, IN_DELETE,
                               LIST_TO_SET, EXTENSION, IN_INTER] THEN
          METIS_TAC[]
        )
      ],


      Q_TAC EXISTS_TAC `s'` THEN
      SIMP_ALL_TAC std_ss [IN_POW, SUBSET_DEF, IN_INSERT, IN_DELETE,
                           LIST_TO_SET, EXTENSION, IN_INTER] THEN
      METIS_TAC[]
    ],


    Q_TAC EXISTS_TAC `h INSERT x` THEN
    SIMP_ALL_TAC std_ss [IN_POW, SUBSET_DEF, IN_INSERT, IN_DELETE, LIST_TO_SET,
                         EXTENSION, IN_INTER,
    UNION_SING] THEN
    METIS_TAC[],


    Q_TAC EXISTS_TAC `x` THEN
    SIMP_ALL_TAC std_ss [IN_POW, SUBSET_DEF, IN_INSERT, IN_DELETE, LIST_TO_SET,
                         EXTENSION, IN_INTER] THEN
    METIS_TAC[]
  ]
]);


Theorem VAR_RENAMING_HASHTABLE_LIST___P_USED_VARS:
  !l S f. P_USED_VARS (VAR_RENAMING_HASHTABLE_LIST l S f) =
          LIST_TO_SET l UNION IMAGE (\x. f (x UNION S)) (POW (LIST_TO_SET l))
Proof
  Induct_on `l` THENL [
    SIMP_TAC std_ss [VAR_RENAMING_HASHTABLE_LIST_def, LIST_TO_SET_THM,
                     UNION_EMPTY, SUBSET_EMPTY, GSPEC_EQ, IMAGE_SING,
                     P_USED_VARS_def, POW_EQNS],

    ASM_SIMP_TAC std_ss [VAR_RENAMING_HASHTABLE_LIST_def, P_USED_VARS_EVAL,
                         EXTENSION, IN_UNION, IN_SING, LIST_TO_SET_THM,
                         IN_INSERT, POW_EQNS, IMAGE_UNION, LET_THM] THEN
    REPEAT STRIP_TAC THEN
    REPEAT BOOL_EQ_STRIP_TAC THEN
    SIMP_TAC std_ss [GSYM IMAGE_COMPOSE, combinTheory.o_DEF, UNION_INSERT]
  ]
QED

val _ = export_theory();
