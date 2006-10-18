open HolKernel Parse boolLib bossLib;

(*
quietdec := true;

val home_dir = (concat Globals.HOLDIR "/examples/temporal_deep/");
loadPath := (concat home_dir "src/deep_embeddings") :: 
            (concat home_dir "src/tools") :: 
            !loadPath;

map load
 ["symbolic_semi_automatonTheory", "prop_logicTheory", "xprop_logicTheory", "set_lemmataTheory", "pred_setTheory", "listTheory", "pairTheory",
   "containerTheory", "infinite_pathTheory", "tuerk_tacticsLib",
   "symbolic_kripke_structureTheory", "temporal_deep_mixedTheory"];
*)
open symbolic_semi_automatonTheory prop_logicTheory xprop_logicTheory set_lemmataTheory pred_setTheory listTheory pairTheory containerTheory infinite_pathTheory symbolic_kripke_structureTheory tuerk_tacticsLib
temporal_deep_mixedTheory;

val _ = hide "S";
val _ = hide "I";

(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)


val _ = new_theory "automaton_formula";



(*****************************************************************************
 * Acceptance conditions
 *****************************************************************************)
val acceptance_condition =
 Hol_datatype
  `acceptance_condition =
    ACCEPT_PROP of 'a prop_logic
        | ACCEPT_TRUE
        | ACCEPT_NOT  of acceptance_condition
        | ACCEPT_AND  of acceptance_condition # acceptance_condition
        | ACCEPT_G    of acceptance_condition`;


val acceptance_condition_induct =
 save_thm
  ("acceptance_condition_induct",
   Q.GEN
    `P`
    (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2)) ==> (A ==> B1)``)
     (SIMP_RULE
       std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P x ==> Q(x,y)) = !x. P x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P y ==> Q(x,y)) = !y. P y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P`,`\(f1,f2). P f1 /\ P f2`]
         (TypeBase.induction_of ``:'a acceptance_condition``)))));


val ACCEPT_COND_USED_VARS_def=
 Define
   `(ACCEPT_COND_USED_VARS (ACCEPT_PROP p) = P_USED_VARS p) /\
    (ACCEPT_COND_USED_VARS ACCEPT_TRUE = EMPTY) /\
    (ACCEPT_COND_USED_VARS (ACCEPT_NOT a) = ACCEPT_COND_USED_VARS a) /\
    (ACCEPT_COND_USED_VARS (ACCEPT_G a) = ACCEPT_COND_USED_VARS a) /\
    (ACCEPT_COND_USED_VARS (ACCEPT_AND(a, b)) = (ACCEPT_COND_USED_VARS a) UNION (ACCEPT_COND_USED_VARS b))`;

(*****************************************************************************
 * Automaton formulas
 *****************************************************************************)
val automaton_formula =
 Hol_datatype
  `automaton_formula =
          ACCEPT_COND of 'a acceptance_condition
          | A_NDET   of 'a symbolic_semi_automaton # automaton_formula
        | A_NOT       of automaton_formula
        | A_AND       of automaton_formula # automaton_formula
        | A_TRUE`;


val automaton_formula_induct =
 save_thm
  ("automaton_formula_induct",
   Q.GEN `P0` (
    (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2)) ==> (A ==> B1)``)
     (SIMP_RULE
       std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P0 x ==> Q(x,y)) = !x. P0 x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P0 y ==> Q(x,y)) = !y. P0 y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P0`,`\(A, f). P0 f`,`\(f1,f2). P0 f1 /\ P0 f2`]
         (TypeBase.induction_of ``:'a automaton_formula``))))));


val A_USED_INPUT_VARS_def=
 Define
   `(A_USED_INPUT_VARS (ACCEPT_COND p) = ACCEPT_COND_USED_VARS p) /\
    (A_USED_INPUT_VARS A_TRUE = EMPTY) /\
    (A_USED_INPUT_VARS (A_NDET(A, f)) = (SEMI_AUTOMATON_USED_INPUT_VARS A UNION
       (A_USED_INPUT_VARS f DIFF A.S))) /\
    (A_USED_INPUT_VARS (A_NOT a) = (A_USED_INPUT_VARS a)) /\
    (A_USED_INPUT_VARS (A_AND(a, b)) = (A_USED_INPUT_VARS a) UNION (A_USED_INPUT_VARS b))`;


val A_USED_STATE_VARS_def=
 Define
   `(A_USED_STATE_VARS (ACCEPT_COND p) = EMPTY) /\
    (A_USED_STATE_VARS A_TRUE = EMPTY) /\
    (A_USED_STATE_VARS (A_NDET(A, f)) = A.S UNION (A_USED_STATE_VARS f)) /\
    (A_USED_STATE_VARS (A_NOT a) = A_USED_STATE_VARS a) /\
    (A_USED_STATE_VARS (A_AND(a, b)) = (A_USED_STATE_VARS a) UNION (A_USED_STATE_VARS b))`;


val A_USED_VARS_def =
 Define
   `A_USED_VARS a = (A_USED_INPUT_VARS a) UNION (A_USED_STATE_VARS a)`;


val A_USED_VARS___DIRECT_DEF =
 store_thm (
   "A_USED_VARS___DIRECT_DEF",
   ``(A_USED_VARS (ACCEPT_COND p) = ACCEPT_COND_USED_VARS p) /\
     (A_USED_VARS A_TRUE = EMPTY) /\
     (A_USED_VARS (A_NDET(A, f)) = (SEMI_AUTOMATON_USED_VARS A UNION
       (A_USED_VARS f))) /\
     (A_USED_VARS (A_NOT a) = (A_USED_VARS a)) /\
     (A_USED_VARS (A_AND(a, b)) = (A_USED_VARS a) UNION (A_USED_VARS b))``,

    SIMP_TAC std_ss [A_USED_VARS_def, A_USED_INPUT_VARS_def,
                     A_USED_STATE_VARS_def, UNION_EMPTY] THEN
    REPEAT STRIP_TAC THENL [
      SIMP_TAC std_ss [EXTENSION, IN_UNION,
        SEMI_AUTOMATON_USED_VARS_def, IN_DIFF] THEN
      PROVE_TAC[],

      SIMP_TAC std_ss [EXTENSION, IN_UNION] THEN
      PROVE_TAC[]
    ]);


val STATE_VARDISJOINT_AUTOMATON_FORMULA_def=
 Define
   `(STATE_VARDISJOINT_AUTOMATON_FORMULA (ACCEPT_COND p) = T) /\
    (STATE_VARDISJOINT_AUTOMATON_FORMULA A_TRUE = T) /\
    (STATE_VARDISJOINT_AUTOMATON_FORMULA (A_NDET(A, f)) = ((DISJOINT A.S (A_USED_STATE_VARS f)) /\ (STATE_VARDISJOINT_AUTOMATON_FORMULA f))) /\
    (STATE_VARDISJOINT_AUTOMATON_FORMULA (A_NOT a) = STATE_VARDISJOINT_AUTOMATON_FORMULA a) /\
    (STATE_VARDISJOINT_AUTOMATON_FORMULA (A_AND(a, b)) = (DISJOINT (A_USED_STATE_VARS a) (A_USED_STATE_VARS b)) /\ (STATE_VARDISJOINT_AUTOMATON_FORMULA a) /\ (STATE_VARDISJOINT_AUTOMATON_FORMULA b))`;


val VARDISJOINT_AUTOMATON_FORMULA_def=
 Define
   `(VARDISJOINT_AUTOMATON_FORMULA f =
      (STATE_VARDISJOINT_AUTOMATON_FORMULA f) /\ DISJOINT (A_USED_STATE_VARS f) (A_USED_INPUT_VARS f))`;



(*****************************************************************************
 * Varibal renamings
 *****************************************************************************)
val ACCEPT_VAR_RENAMING_def =
 Define
   `(ACCEPT_VAR_RENAMING (f:'a->'b) (ACCEPT_TRUE) = ACCEPT_TRUE) /\
    (ACCEPT_VAR_RENAMING f (ACCEPT_PROP p) = (ACCEPT_PROP (P_VAR_RENAMING f p))) /\
    (ACCEPT_VAR_RENAMING f (ACCEPT_NOT b) = ACCEPT_NOT (ACCEPT_VAR_RENAMING f b)) /\
    (ACCEPT_VAR_RENAMING f (ACCEPT_G b) = ACCEPT_G (ACCEPT_VAR_RENAMING f b)) /\
    (ACCEPT_VAR_RENAMING f (ACCEPT_AND(b1,b2)) = (ACCEPT_AND(ACCEPT_VAR_RENAMING f b1, ACCEPT_VAR_RENAMING f b2)))`;


val A_VAR_RENAMING_def=
 Define
   `((A_VAR_RENAMING (f:'a -> 'b) (ACCEPT_COND p)) = ACCEPT_COND (ACCEPT_VAR_RENAMING f p)) /\
    ((A_VAR_RENAMING f A_TRUE) = A_TRUE) /\
    ((A_VAR_RENAMING f (A_NDET(A:'a symbolic_semi_automaton, f'))) = A_NDET(
       SEMI_AUTOMATON_VAR_RENAMING f A, A_VAR_RENAMING f f')) /\
    ((A_VAR_RENAMING f (A_NOT a)) = A_NOT(A_VAR_RENAMING f a)) /\
    (A_VAR_RENAMING f (A_AND(a, b)) = (A_AND (A_VAR_RENAMING f a, A_VAR_RENAMING f b)))`;



(*=============================================================================
= Semantic
=============================================================================*)


(*****************************************************************************
 * Acceptance conditions
 *****************************************************************************)
val ACCEPT_COND_SEM_TIME_def=
 Define
   `(ACCEPT_COND_SEM_TIME t v (ACCEPT_PROP p) = P_SEM (v t) p) /\
    (ACCEPT_COND_SEM_TIME t v ACCEPT_TRUE = T) /\
    (ACCEPT_COND_SEM_TIME t v (ACCEPT_NOT a) = ~(ACCEPT_COND_SEM_TIME t v a)) /\
    (ACCEPT_COND_SEM_TIME t v (ACCEPT_G a) = (!t':num. (t' >= t) ==> (ACCEPT_COND_SEM_TIME t' v a))) /\
    (ACCEPT_COND_SEM_TIME t v (ACCEPT_AND(a, b)) = ((ACCEPT_COND_SEM_TIME t v a) /\ ACCEPT_COND_SEM_TIME t v b))`;


val ACCEPT_COND_SEM_def=
 Define
   `(ACCEPT_COND_SEM v f = ACCEPT_COND_SEM_TIME 0 v f)`;


(*****************************************************************************
 * Automaton formulas
 *****************************************************************************)
val A_SEM_def=
 Define
   `((A_SEM i (ACCEPT_COND p)) = (ACCEPT_COND_SEM i p)) /\
    ((A_SEM i (A_TRUE)) = T) /\
    ((A_SEM i (A_NDET(A, f))) = (?w. (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w) /\ (A_SEM (INPUT_RUN_PATH_UNION A i w) f))) /\
    ((A_SEM i (A_NOT a)) = ~(A_SEM i a)) /\
    ((A_SEM i (A_AND(a, b))) = ((A_SEM i a) /\ A_SEM i b))`;


val A_KS_SEM_def =
 Define
   `A_KS_SEM M A = 
      !i. IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M i ==> A_SEM i A`;




(*=============================================================================
= Syntactic Sugar and elementary lemmata
=============================================================================*)

(*****************************************************************************
 * Acceptance conditions
*****************************************************************************)
val ACCEPT_F_def =
 Define
   `ACCEPT_F b = ACCEPT_NOT(ACCEPT_G (ACCEPT_NOT b))`;


val ACCEPT_FALSE_def =
 Define
   `ACCEPT_FALSE = ACCEPT_NOT(ACCEPT_TRUE)`;


val ACCEPT_OR_def =
 Define
   `ACCEPT_OR(b1, b2) = ACCEPT_NOT(ACCEPT_AND(ACCEPT_NOT b1, ACCEPT_NOT b2))`;


val ACCEPT_IMPL_def =
 Define
   `ACCEPT_IMPL(b1, b2) = ACCEPT_OR(ACCEPT_NOT b1, b2)`;


val ACCEPT_EQUIV_def =
 Define
   `ACCEPT_EQUIV(b1, b2) = ACCEPT_AND(ACCEPT_IMPL(b1, b2),ACCEPT_IMPL(b2, b1))`;

val ACCEPT_BIGAND_def =
 Define
   `(ACCEPT_BIGAND [] = ACCEPT_TRUE) /\
    (ACCEPT_BIGAND (e::C) = ACCEPT_AND(e, ACCEPT_BIGAND C))`;



(*****************************************************************************
 * Automaton formulas
 *****************************************************************************)
val A_BIGAND_def =
 Define
   `(A_BIGAND ([]:'a automaton_formula list) = (A_TRUE:'a automaton_formula)) /\
    (A_BIGAND (e::C) = A_AND(e, A_BIGAND C))`;


val A_UNIV_def =
 Define
   `A_UNIV(A, f) = A_NOT(A_NDET(A, A_NOT f))`;


val A_FALSE_def =
 Define
   `A_FALSE = A_NOT(A_TRUE)`;


val A_OR_def =
 Define
   `A_OR(b1, b2) = A_NOT(A_AND(A_NOT b1, A_NOT b2))`;


val A_IMPL_def =
 Define
   `A_IMPL(b1, b2) = A_OR(A_NOT b1, b2)`;


val A_EQUIV_def =
 Define
   `A_EQUIV(b1, b2) = A_AND(A_IMPL(b1, b2),A_IMPL(b2, b1))`;


val A_NDET_CONSTRAINED_def =
 Define
   `A_NDET_CONSTRAINED(A, C, f) = A_NDET(A, A_AND(f, A_BIGAND C))`;


val A_UNIV_CONSTRAINED_def =
 Define
   `A_UNIV_CONSTRAINED(A, C, f) = A_UNIV(A, A_IMPL(A_BIGAND C, f))`;


val A_SEM_THM =
 store_thm
  ("A_SEM_THM",
     ``!A f v p a b. (((A_SEM v (ACCEPT_COND p)) = (ACCEPT_COND_SEM v p)) /\
     ((A_SEM v (A_UNIV(A, f))) = (!w. (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A v w) ==> (A_SEM (INPUT_RUN_PATH_UNION A v w) f))) /\
     ((A_SEM v (A_NDET(A, f))) = (?w. (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A v w) /\ (A_SEM (INPUT_RUN_PATH_UNION A v w) f))) /\
     (A_SEM v (A_TRUE)) /\ ~(A_SEM v (A_FALSE)) /\
     ((A_SEM v (A_NOT a)) = ~(A_SEM v a)) /\
     ((A_SEM v (A_AND(a, b))) = ((A_SEM v a) /\ A_SEM v b)) /\
     ((A_SEM v (A_OR(a, b))) = ((A_SEM v a) \/ A_SEM v b)) /\
     ((A_SEM v (A_IMPL(a, b))) = ((A_SEM v a) ==> A_SEM v b)) /\
     ((A_SEM v (A_EQUIV(a, b))) = ((A_SEM v a) = A_SEM v b)))``,

   SIMP_TAC arith_ss [A_UNIV_def, A_FALSE_def, A_OR_def, A_IMPL_def, A_EQUIV_def, A_SEM_def] THEN
   REPEAT STRIP_TAC THEN PROVE_TAC[]
);


val A_USED_STATE_VARS_COMPATIBLE_def =
 Define
   `A_USED_STATE_VARS_COMPATIBLE a1 a2 =
       DISJOINT (A_USED_INPUT_VARS a1) (A_USED_STATE_VARS a2) /\
       DISJOINT (A_USED_INPUT_VARS a2) (A_USED_STATE_VARS a1) /\
       DISJOINT (A_USED_STATE_VARS a1) (A_USED_STATE_VARS a2)`;


val VARDISJOINT_AUTOMATON_FORMULA___A_USED_STATE_VARS_COMPATIBLE =
 store_thm
  ("VARDISJOINT_AUTOMATON_FORMULA___A_USED_STATE_VARS_COMPATIBLE",

   ``(VARDISJOINT_AUTOMATON_FORMULA (A_AND(a1, a2))) ==>
      A_USED_STATE_VARS_COMPATIBLE a1 a2``,

   REWRITE_TAC[VARDISJOINT_AUTOMATON_FORMULA_def,
               A_USED_STATE_VARS_COMPATIBLE_def,
               A_USED_STATE_VARS_def,
               A_USED_INPUT_VARS_def,
               STATE_VARDISJOINT_AUTOMATON_FORMULA_def,
               DISJOINT_UNION_BOTH] THEN
   PROVE_TAC[]);


val AUTOMATON_EQUIV_def =
 Define
   `AUTOMATON_EQUIV a1 a2 = !v. (A_SEM v a1) = (A_SEM v a2)`;


val AUTOMATON_EQUIV_THM =
 store_thm
  ("AUTOMATON_EQUIV_THM",
    ``(!A f. AUTOMATON_EQUIV (A_NDET(A, f)) (A_NOT (A_UNIV(A, A_NOT f)))) /\
      (!A f. AUTOMATON_EQUIV (A_UNIV(A, f)) (A_NOT (A_NDET(A, A_NOT f)))) /\
      (!a1 a2.  (AUTOMATON_EQUIV (A_NOT a1) (A_NOT a2)) = AUTOMATON_EQUIV a1 a2) /\
      (!a1 a2. (AUTOMATON_EQUIV (A_AND (a1,a2)) (A_AND (a2,a1)))) /\
      (!a1 a2 b. (AUTOMATON_EQUIV a1 a2) ==> (AUTOMATON_EQUIV (A_AND (a1,b)) (A_AND (a2,b)))) /\
      (!a1 a2. (!v. (A_SEM v (A_EQUIV(a1, a2)))) = (AUTOMATON_EQUIV a1 a2)) /\
      (!a1 a2. (AUTOMATON_EQUIV (A_OR (a1,a2)) (A_OR (a2,a1)))) /\
      (!a1 a2 b. (AUTOMATON_EQUIV a1 a2) ==> (AUTOMATON_EQUIV (A_OR (a1,b)) (A_OR (a2,b)))) /\
      (!a1 a2 b. (AUTOMATON_EQUIV a1 a2) ==> (AUTOMATON_EQUIV (A_IMPL (a1,b)) (A_IMPL (a2,b)))) /\
      (!a1 a2 b. (AUTOMATON_EQUIV a1 a2) ==> (AUTOMATON_EQUIV (A_IMPL (b,a1)) (A_IMPL (b,a2)))) /\
      (!A a1 a2. (AUTOMATON_EQUIV a1 a2) ==> AUTOMATON_EQUIV (A_NDET(A, a1)) (A_NDET(A, a2))) /\
      (!A a1 a2. (AUTOMATON_EQUIV a1 a2) ==> AUTOMATON_EQUIV (A_UNIV(A, a1)) (A_UNIV(A, a2))) /\
      (!a1 a2. (AUTOMATON_EQUIV a1 a2) = (AUTOMATON_EQUIV a2 a1)) /\
      (!a1. (AUTOMATON_EQUIV a1 a1)) /\
      (!a1. ((AUTOMATON_EQUIV a1 a2) /\ (AUTOMATON_EQUIV a2 a3)) ==> (AUTOMATON_EQUIV a1 a3))``,

   REWRITE_TAC[AUTOMATON_EQUIV_def, A_SEM_THM] THEN
   REPEAT STRIP_TAC THEN
   PROVE_TAC []);


val A_BIGAND___A_USED_INPUT_VARS =
 store_thm
  ("A_BIGAND___A_USED_INPUT_VARS",
   ``!C1 C2. A_USED_INPUT_VARS (A_BIGAND (APPEND C1 C2)) = A_USED_INPUT_VARS (A_AND (A_BIGAND C1,
 A_BIGAND C2))``,

   REWRITE_TAC[A_USED_INPUT_VARS_def] THEN
   Induct_on `C1` THENL [
      SIMP_TAC arith_ss [A_BIGAND_def, APPEND, A_USED_INPUT_VARS_def, UNION_EMPTY],

      SIMP_TAC arith_ss [A_BIGAND_def, APPEND, A_USED_INPUT_VARS_def, UNION_EMPTY] THEN
      PROVE_TAC [UNION_ASSOC]
   ]);


val A_BIGAND___A_USED_STATE_VARS =
 store_thm
  ("A_BIGAND___A_USED_STATE_VARS",
   ``!C1 C2. A_USED_STATE_VARS (A_BIGAND (APPEND C1 C2)) = A_USED_STATE_VARS (A_AND (A_BIGAND C1,
 A_BIGAND C2))``,

   REWRITE_TAC[A_USED_STATE_VARS_def] THEN
   Induct_on `C1` THENL [
      SIMP_TAC arith_ss [A_BIGAND_def, APPEND, A_USED_STATE_VARS_def, UNION_EMPTY],

      SIMP_TAC arith_ss [A_BIGAND_def, APPEND, A_USED_STATE_VARS_def, UNION_EMPTY] THEN
      PROVE_TAC [UNION_ASSOC]
   ]);


val A_BIGAND___A_SEM =
 store_thm
  ("A_BIGAND___A_SEM",
   ``!C1 C2 v. A_SEM v (A_BIGAND (APPEND C1 C2)) = ((A_SEM v (A_BIGAND C1)) /\ (A_SEM v (A_BIGAND C2)))``,

   Induct_on `C1` THENL [
      SIMP_TAC arith_ss [A_BIGAND_def, APPEND, A_SEM_def],

      SIMP_TAC arith_ss [A_BIGAND_def, APPEND, A_SEM_def, UNION_EMPTY] THEN
      PROVE_TAC []
   ]);


val A_BIGAND_SEM =
 store_thm
  ("A_BIGAND_SEM",
   ``!w C. A_SEM w (A_BIGAND C) = !e. MEM e C ==> A_SEM w e``,

Induct_on `C` THENL [
  SIMP_TAC list_ss [A_BIGAND_def, A_SEM_def],

  ASM_SIMP_TAC list_ss [A_BIGAND_def, A_SEM_def] THEN
  PROVE_TAC[]
])


val ACCEPT_BIGAND_SEM =
 store_thm
  ("ACCEPT_BIGAND_SEM",
   ``!t w C. ACCEPT_COND_SEM_TIME t w (ACCEPT_BIGAND C) = !e. MEM e C ==> ACCEPT_COND_SEM_TIME t w e``,

Induct_on `C` THENL [
  SIMP_TAC list_ss [ACCEPT_BIGAND_def, ACCEPT_COND_SEM_TIME_def],

  ASM_SIMP_TAC list_ss [ACCEPT_BIGAND_def, ACCEPT_COND_SEM_TIME_def] THEN
  METIS_TAC[]
])


val ACCEPT_BIGAND___VAR_RENAMING =
 store_thm
  ("ACCEPT_BIGAND___VAR_RENAMING",

   ``!f C.
    ACCEPT_VAR_RENAMING f (ACCEPT_BIGAND C) = 
    (ACCEPT_BIGAND (MAP (ACCEPT_VAR_RENAMING f) C))``,

    Induct_on `C` THENL [
      SIMP_TAC list_ss [ACCEPT_BIGAND_def, ACCEPT_VAR_RENAMING_def],
      ASM_SIMP_TAC list_ss [ACCEPT_BIGAND_def, ACCEPT_VAR_RENAMING_def]
    ]);


val A_BIGAND___AUTOMATON_EQUIV =
 store_thm
  ("A_BIGAND___AUTOMATON_EQUIV",
   ``!C1 C2. AUTOMATON_EQUIV (A_BIGAND (APPEND C1 C2)) (A_AND(A_BIGAND C1, A_BIGAND C2))``,

   REWRITE_TAC[AUTOMATON_EQUIV_def, A_SEM_def, A_BIGAND___A_SEM]);


val A_BIGAND___STATE_VARDISJOINT_AUTOMATON_FORMULA =
 store_thm
  ("A_BIGAND___STATE_VARDISJOINT_AUTOMATON_FORMULA",
   ``!C1 C2. STATE_VARDISJOINT_AUTOMATON_FORMULA (A_BIGAND (APPEND C1 C2)) = STATE_VARDISJOINT_AUTOMATON_FORMULA (A_AND (A_BIGAND C1,  A_BIGAND C2))``,

   REWRITE_TAC[STATE_VARDISJOINT_AUTOMATON_FORMULA_def] THEN
   Induct_on `C1` THENL [
      SIMP_TAC arith_ss [A_BIGAND_def,
                         APPEND,
                         DISJOINT_EMPTY,
                         STATE_VARDISJOINT_AUTOMATON_FORMULA_def,
                         A_USED_STATE_VARS_def],

      SIMP_TAC arith_ss [A_BIGAND_def,
                         APPEND,
                         DISJOINT_EMPTY,
                         STATE_VARDISJOINT_AUTOMATON_FORMULA_def,
                         A_USED_STATE_VARS_def,
                         DISJOINT_UNION_BOTH,
                         A_BIGAND___A_USED_STATE_VARS] THEN
      REPEAT STRIP_TAC THEN
      EQ_TAC THEN REPEAT STRIP_TAC THEN
      PROVE_TAC [DISJOINT_SYM]
   ]);


val A_BIGAND___VARDISJOINT_AUTOMATON_FORMULA =
 store_thm
  ("A_BIGAND___VARDISJOINT_AUTOMATON_FORMULA",
   ``!C1 C2. VARDISJOINT_AUTOMATON_FORMULA (A_BIGAND (APPEND C1 C2)) = VARDISJOINT_AUTOMATON_FORMULA (A_AND (A_BIGAND C1,  A_BIGAND C2))``,

   REWRITE_TAC[VARDISJOINT_AUTOMATON_FORMULA_def,
               A_BIGAND___A_USED_STATE_VARS,
               A_BIGAND___A_USED_INPUT_VARS,
               A_BIGAND___STATE_VARDISJOINT_AUTOMATON_FORMULA]);


val A_BIGAND_EMPTY =
 store_thm
  ("A_BIGAND_EMPTY",

  ``!C. (A_BIGAND C = A_TRUE) = (C = [])``,

  Cases_on `C` THEN EVAL_TAC);


val A_BIGAND_11 =
 store_thm
  ("A_BIGAND_11",

  ``!C D. (A_BIGAND C = A_BIGAND D) = (C = D)``,

   Induct_on `C` THEN
   Cases_on `D` THEN
   EVAL_TAC THEN PROVE_TAC[]);


val EXISTS_RUN_WITH_PROPERTIES_def =
 Define
   `EXISTS_RUN_WITH_PROPERTIES A C = (!i. ?w. (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w) /\ (A_SEM (INPUT_RUN_PATH_UNION A i w) (A_BIGAND C)))`;


val UNIQUE_RUN_WITH_PROPERTIES_def =
 Define
   `UNIQUE_RUN_WITH_PROPERTIES A C = (!i. ?!w. (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w) /\ (A_SEM (INPUT_RUN_PATH_UNION A i w) (A_BIGAND C)))`;


val UNIQUE_RUN_WITH_PROPERTIES___IMPLIES_EXISTENCE =
 store_thm (
   "UNIQUE_RUN_WITH_PROPERTIES___IMPLIES_EXISTENCE",
   ``!A C. UNIQUE_RUN_WITH_PROPERTIES A C ==> EXISTS_RUN_WITH_PROPERTIES A C``,

   REWRITE_TAC[UNIQUE_RUN_WITH_PROPERTIES_def, EXISTS_RUN_WITH_PROPERTIES_def] THEN METIS_TAC[]);


val A_NDET_CONSTRAINED_11 =
 store_thm
  ("A_NDET_CONSTRAINED_11",

   ``!A B C D p q.
   ((A_NDET_CONSTRAINED(A, C, p)) =
   (A_NDET_CONSTRAINED(B, D, q))) =
   ((A = B) /\ (C = D) /\ (p = q))``,

   EVAL_TAC THEN
   Induct_on `C` THEN
   Cases_on `D` THEN
   EVAL_TAC THEN PROVE_TAC[]);


(*Automaton Classes*)
val ACCEPT_COND_PROP_def =
 Define
   `ACCEPT_COND_PROP b = ACCEPT_COND (ACCEPT_PROP b)`;


val ACCEPT_COND_PROP_11 =
 store_thm
  ("ACCEPT_COND_PROP_11",

  ``!p1 p2. (ACCEPT_COND_PROP p1 = ACCEPT_COND_PROP p2) = (p1 = p2)``,

   EVAL_TAC THEN PROVE_TAC[]);


val ACCEPT_COND_GF_def =
 Define
   `ACCEPT_COND_GF b = ACCEPT_COND (ACCEPT_G(ACCEPT_F (ACCEPT_PROP b)))`;


val ACCEPT_COND_FG_def =
 Define
   `ACCEPT_COND_FG b = ACCEPT_COND (ACCEPT_F(ACCEPT_G (ACCEPT_PROP b)))`;


val ACCEPT_COND_F_def =
 Define
   `ACCEPT_COND_F b = ACCEPT_COND (ACCEPT_F (ACCEPT_PROP b))`;


val ACCEPT_COND_G_def =
 Define
   `ACCEPT_COND_G b = ACCEPT_COND (ACCEPT_G (ACCEPT_PROP b))`;


val IS_EX_AUTOMATON_def =
 Define
  `IS_EX_AUTOMATON af =
      ?A f. af = A_NDET(A, f)`;


val IS_ALL_AUTOMATON_def =
 Define
  `IS_ALL_AUTOMATON af =
      ?A f. af = A_UNIV(A, f)`;


val IS_AUTOMATON_def =
 Define
  `IS_AUTOMATON af = (IS_EX_AUTOMATON af \/ IS_ALL_AUTOMATON af)`;


val IS_DET_EX_AUTOMATON_def =
 Define
  `IS_DET_EX_AUTOMATON af = ?A f. ((af = A_NDET(A, f)) /\ IS_DET_SYMBOLIC_SEMI_AUTOMATON A)`;


val IS_DET_ALL_AUTOMATON_def =
 Define
  `IS_DET_ALL_AUTOMATON af = ?A f. ((af = A_UNIV(A, f)) /\ IS_DET_SYMBOLIC_SEMI_AUTOMATON A)`;


val IS_DET_AUTOMATON_def =
 Define
  `IS_DET_AUTOMATON af = (IS_DET_EX_AUTOMATON af \/ IS_DET_ALL_AUTOMATON af)`;


val IS_NDET_GF_AUTOMATON_def =
 Define
  `IS_NDET_GF_AUTOMATON af = ?A b. ((af = A_NDET(A, ACCEPT_COND_GF b)))`;


val IS_NDET_FG_AUTOMATON_def =
 Define
  `IS_NDET_FG_AUTOMATON af = ?A b. ((af = A_NDET(A, ACCEPT_COND_FG b)))`;


val IS_NDET_F_AUTOMATON_def =
 Define
  `IS_NDET_F_AUTOMATON af = ?A b. ((af = A_NDET(A, ACCEPT_COND_F b)))`;


val IS_NDET_G_AUTOMATON_def =
 Define
  `IS_NDET_G_AUTOMATON af = ?A b. ((af = A_NDET(A, ACCEPT_COND_G b)))`;


val IS_DET_EX_GF_AUTOMATON_def=
 Define
   `IS_DET_EX_GF_AUTOMATON af = (?A b. (af = A_NDET (A,ACCEPT_COND_GF b)) /\ IS_DET_SYMBOLIC_SEMI_AUTOMATON A)`;


val IS_DET_EX_FG_AUTOMATON_def=
 Define
   `IS_DET_EX_FG_AUTOMATON af = (?A b. (af = A_NDET (A,ACCEPT_COND_FG b)) /\ IS_DET_SYMBOLIC_SEMI_AUTOMATON A)`;


val IS_DET_EX_G_AUTOMATON_def=
 Define
   `IS_DET_EX_G_AUTOMATON af = (?A b. (af = A_NDET (A,ACCEPT_COND_G b)) /\ IS_DET_SYMBOLIC_SEMI_AUTOMATON A)`;


val IS_DET_EX_F_AUTOMATON_def=
 Define
   `IS_DET_EX_F_AUTOMATON af = (?A b. (af = A_NDET (A,ACCEPT_COND_F b)) /\ IS_DET_SYMBOLIC_SEMI_AUTOMATON A)`;


val IS_UNIV_GF_AUTOMATON_def =
 Define
  `IS_UNIV_GF_AUTOMATON af = ?A b. ((af = A_UNIV(A, ACCEPT_COND_GF b)))`;


val IS_UNIV_FG_AUTOMATON_def =
 Define
  `IS_UNIV_FG_AUTOMATON af = ?A b. ((af = A_UNIV(A, ACCEPT_COND_FG b)))`;


val IS_UNIV_F_AUTOMATON_def =
 Define
  `IS_UNIV_F_AUTOMATON af = ?A b. ((af = A_UNIV(A, ACCEPT_COND_F b)))`;


val IS_UNIV_G_AUTOMATON_def =
 Define
  `IS_UNIV_G_AUTOMATON af = ?A b. ((af = A_UNIV(A, ACCEPT_COND_G b)))`;


val A_NDET_GEN_GF_def =
 Define
   `A_NDET_GEN_GF(A, C) = A_NDET(A, A_BIGAND (MAP (\p. ACCEPT_COND_GF p) C))`;





val A_IS_EMPTY_def =
 Define
   `A_IS_EMPTY A = ~(?i. A_SEM i A)`;

val A_IS_CONTRADICTION_def =
 Define
   `A_IS_CONTRADICTION A = A_IS_EMPTY A`;

val A_IS_TAUTOLOGY_def =
 Define
   `A_IS_TAUTOLOGY A = (!i. A_SEM i A)`;


val A_TAUTOLOGY_CONTRADICTION_DUAL =
 store_thm
  ("A_TAUTOLOGY_CONTRADICTION_DUAL",

  ``(!A. A_IS_CONTRADICTION (A_NOT A) = A_IS_TAUTOLOGY A) /\
    (!A. A_IS_TAUTOLOGY (A_NOT A) = A_IS_CONTRADICTION A)``,

    SIMP_TAC std_ss [A_IS_TAUTOLOGY_def, A_IS_CONTRADICTION_def, A_SEM_def,
      A_IS_EMPTY_def]);


val A_TAUTOLOGY_CONTRADICTION___TO___EQUIVALENT =
 store_thm
  ("A_TAUTOLOGY_CONTRADICTION___TO___EQUIVALENT",

  ``(!A. A_IS_CONTRADICTION A = AUTOMATON_EQUIV A A_FALSE) /\
    (!A. A_IS_TAUTOLOGY A = AUTOMATON_EQUIV A A_TRUE)``,

    SIMP_TAC std_ss [A_IS_TAUTOLOGY_def, A_IS_CONTRADICTION_def, A_IS_EMPTY_def, AUTOMATON_EQUIV_def, A_SEM_THM]);



(*****************************************************************************
 * Variable renamings
 *****************************************************************************)


val FINITE___ACCEPT_COND_USED_VARS =
 store_thm
  ("FINITE___ACCEPT_COND_USED_VARS",

  ``!a. FINITE(ACCEPT_COND_USED_VARS a)``,

  INDUCT_THEN acceptance_condition_induct ASSUME_TAC THENL [
      REWRITE_TAC[ACCEPT_COND_USED_VARS_def, FINITE___P_USED_VARS],
      REWRITE_TAC[ACCEPT_COND_USED_VARS_def, FINITE_EMPTY],
      ASM_REWRITE_TAC[ACCEPT_COND_USED_VARS_def],
      ASM_REWRITE_TAC[ACCEPT_COND_USED_VARS_def, FINITE_UNION],
      ASM_REWRITE_TAC[ACCEPT_COND_USED_VARS_def]
  ]);

val ACCEPT_VAR_RENAMING___USED_VARS =
 store_thm
  ("ACCEPT_VAR_RENAMING___USED_VARS",

   ``!a f. (ACCEPT_COND_USED_VARS (ACCEPT_VAR_RENAMING f a) =
       (IMAGE f (ACCEPT_COND_USED_VARS a)))``,

   INDUCT_THEN acceptance_condition_induct ASSUME_TAC THENL [
      REWRITE_TAC [ACCEPT_COND_USED_VARS_def, ACCEPT_VAR_RENAMING_def, P_VAR_RENAMING___USED_VARS],
      REWRITE_TAC [ACCEPT_COND_USED_VARS_def, ACCEPT_VAR_RENAMING_def, IMAGE_EMPTY],
      ASM_REWRITE_TAC [ACCEPT_COND_USED_VARS_def, ACCEPT_VAR_RENAMING_def],
      ASM_REWRITE_TAC [ACCEPT_COND_USED_VARS_def, ACCEPT_VAR_RENAMING_def, IMAGE_UNION],
      ASM_REWRITE_TAC[ACCEPT_COND_USED_VARS_def, ACCEPT_VAR_RENAMING_def]
   ]);



val FINITE___A_USED_INPUT_VARS =
 store_thm
  ("FINITE___A_USED_INPUT_VARS",

  ``!a. FINITE(A_USED_INPUT_VARS a)``,

   INDUCT_THEN automaton_formula_induct ASSUME_TAC THENL [
      REWRITE_TAC[A_USED_INPUT_VARS_def, FINITE___ACCEPT_COND_USED_VARS],

      REWRITE_TAC[A_USED_INPUT_VARS_def, FINITE_UNION, FINITE___SEMI_AUTOMATON_USED_INPUT_VARS] THEN
      METIS_TAC[FINITE_DIFF],

      ASM_REWRITE_TAC[A_USED_INPUT_VARS_def],
      ASM_REWRITE_TAC[A_USED_INPUT_VARS_def, FINITE_UNION],
      ASM_REWRITE_TAC[A_USED_INPUT_VARS_def, FINITE_EMPTY]
   ]);


val A_VAR_RENAMING___USED_STATE_VARS =
 store_thm
  ("A_VAR_RENAMING___USED_STATE_VARS",

   ``!a f.
       (A_USED_STATE_VARS (A_VAR_RENAMING f a) =
       (IMAGE f (A_USED_STATE_VARS a)))``,


   INDUCT_THEN automaton_formula_induct ASSUME_TAC THENL [

         REWRITE_TAC [A_USED_STATE_VARS_def, A_VAR_RENAMING_def, IMAGE_EMPTY],

         Cases_on `p_1` THEN
         ASM_REWRITE_TAC [A_USED_STATE_VARS_def,
                        A_VAR_RENAMING_def,
                        SEMI_AUTOMATON_VAR_RENAMING_def,
                        symbolic_semi_automaton_REWRITES,
                        IMAGE_UNION],

         ASM_REWRITE_TAC [A_USED_STATE_VARS_def, A_VAR_RENAMING_def],
         ASM_REWRITE_TAC [A_USED_STATE_VARS_def, A_VAR_RENAMING_def, IMAGE_UNION],
         REWRITE_TAC [A_USED_STATE_VARS_def, A_VAR_RENAMING_def, IMAGE_EMPTY]
   ]);


val A_VAR_RENAMING___USED_INPUT_VARS =
 store_thm
  ("A_VAR_RENAMING___USED_INPUT_VARS",

   ``!a f. (INJ f (A_USED_VARS a) UNIV) ==>

       (A_USED_INPUT_VARS (A_VAR_RENAMING f a) =
       (IMAGE f (A_USED_INPUT_VARS a)))``,

   INDUCT_THEN automaton_formula_induct ASSUME_TAC THENL [

      REWRITE_TAC [A_USED_INPUT_VARS_def, A_VAR_RENAMING_def, ACCEPT_VAR_RENAMING___USED_VARS],


      Cases_on `p_1` THEN
      ASM_SIMP_TAC std_ss [A_USED_VARS_def,
                           A_USED_INPUT_VARS_def,
                           A_USED_STATE_VARS_def,
                           A_VAR_RENAMING_def,
                           SEMI_AUTOMATON_USED_INPUT_VARS_def,
                           SEMI_AUTOMATON_VAR_RENAMING_def,
                           SEMI_AUTOMATON_USED_VARS_def,
                           DIFF_UNION,
                           symbolic_semi_automaton_REWRITES,
                           P_VAR_RENAMING___USED_VARS, XP_VAR_RENAMING___USED_VARS,
                           IMAGE_UNION] THEN
      REPEAT STRIP_TAC THEN
      `?INJ_SET. INJ_SET = (P_USED_VARS p UNION XP_USED_VARS x DIFF f UNION
             (A_USED_INPUT_VARS a DIFF f) UNION
             (f UNION A_USED_STATE_VARS a))` by METIS_TAC[] THEN

      `((P_USED_VARS p UNION XP_USED_VARS x UNION f) SUBSET INJ_SET) /\
       ((A_USED_INPUT_VARS a UNION f) SUBSET INJ_SET) /\
       ((A_USED_VARS a SUBSET INJ_SET))` by
         (ASM_SIMP_TAC std_ss [UNION_DEF, SUBSET_DEF, GSPECIFICATION, DIFF_DEF, A_USED_VARS_def] THEN
         METIS_TAC[]) THEN
      METIS_TAC[INJ_SUBSET, IMAGE_DIFF, IMAGE_UNION],



      FULL_SIMP_TAC std_ss [A_USED_VARS_def, A_USED_STATE_VARS_def, A_USED_INPUT_VARS_def, A_VAR_RENAMING_def],

      FULL_SIMP_TAC std_ss [A_USED_VARS_def, A_USED_STATE_VARS_def, A_USED_INPUT_VARS_def, A_VAR_RENAMING_def,  IMAGE_UNION] THEN
      REPEAT STRIP_TAC THEN
      `(A_USED_INPUT_VARS a UNION A_USED_STATE_VARS a) SUBSET
       (A_USED_INPUT_VARS a UNION A_USED_INPUT_VARS a' UNION
         (A_USED_STATE_VARS a UNION A_USED_STATE_VARS a'))` by
         METIS_TAC[SUBSET_UNION, UNION_COMM, UNION_ASSOC] THEN

      `(A_USED_INPUT_VARS a' UNION A_USED_STATE_VARS a') SUBSET
       (A_USED_INPUT_VARS a UNION A_USED_INPUT_VARS a' UNION
         (A_USED_STATE_VARS a UNION A_USED_STATE_VARS a'))` by
         METIS_TAC[SUBSET_UNION, UNION_COMM, UNION_ASSOC] THEN

      METIS_TAC[INJ_SUBSET],



      REWRITE_TAC [A_USED_INPUT_VARS_def, A_VAR_RENAMING_def, ACCEPT_VAR_RENAMING___USED_VARS, IMAGE_EMPTY]
   ]);


val A_VAR_RENAMING___USED_VARS =
 store_thm
  ("A_VAR_RENAMING___USED_VARS",

   ``!a f. (INJ f (A_USED_VARS a) UNIV) ==>

       (A_USED_VARS (A_VAR_RENAMING f a) =
       (IMAGE f (A_USED_VARS a)))``,

   REPEAT STRIP_TAC THEN
   REWRITE_TAC [A_USED_VARS_def, IMAGE_UNION, A_VAR_RENAMING___USED_STATE_VARS] THEN
   METIS_TAC[A_VAR_RENAMING___USED_INPUT_VARS]);


val A_VAR_RENAMING___A_BIGAND =
 store_thm
  ("A_VAR_RENAMING___A_BIGAND",

   ``!f C. (A_VAR_RENAMING f (A_BIGAND C) = A_BIGAND (MAP (A_VAR_RENAMING f) C))``,

   Induct_on `C` THENL [
      REWRITE_TAC [MAP, A_BIGAND_def, A_VAR_RENAMING_def],
      ASM_REWRITE_TAC [MAP, A_BIGAND_def, A_VAR_RENAMING_def]
   ]);


val ACCEPT_COND_USED_VARS_INTER_SUBSET_THM =
 store_thm
  ("ACCEPT_COND_USED_VARS_INTER_SUBSET_THM",
   ``!a S t. ((ACCEPT_COND_USED_VARS a) SUBSET S) ==> (ACCEPT_COND_SEM_TIME t v a = ACCEPT_COND_SEM_TIME t (PATH_RESTRICT v S) a)``,

   INDUCT_THEN acceptance_condition_induct ASSUME_TAC THENL [
      SIMP_TAC std_ss [ACCEPT_COND_USED_VARS_def, ACCEPT_COND_SEM_TIME_def, PATH_RESTRICT_def, PATH_MAP_def] THEN
      PROVE_TAC [P_USED_VARS_INTER_SUBSET_THM],

      REWRITE_TAC[ACCEPT_COND_SEM_TIME_def],

      REWRITE_TAC[ACCEPT_COND_SEM_TIME_def, ACCEPT_COND_USED_VARS_def] THEN
      PROVE_TAC[],

      REWRITE_TAC[ACCEPT_COND_SEM_TIME_def, ACCEPT_COND_USED_VARS_def, UNION_SUBSET] THEN
      PROVE_TAC[],

      REWRITE_TAC[ACCEPT_COND_SEM_TIME_def, ACCEPT_COND_USED_VARS_def] THEN
      PROVE_TAC[]
   ]);


val ACCEPT_COND_USED_VARS_INTER_THM =
 store_thm
  ("ACCEPT_COND_USED_VARS_INTER_THM",
   ``!a t. (ACCEPT_COND_SEM_TIME t v a = ACCEPT_COND_SEM_TIME t (PATH_RESTRICT v (ACCEPT_COND_USED_VARS a)) a)``,

   METIS_TAC [ACCEPT_COND_USED_VARS_INTER_SUBSET_THM, SUBSET_REFL]);


val A_USED_INPUT_VARS_INTER_SUBSET_THM =
 store_thm
  ("A_USED_INPUT_VARS_INTER_SUBSET_THM",
   ``!a S. ((A_USED_INPUT_VARS a) SUBSET S) ==>
      (!i. (A_SEM i a = A_SEM (PATH_RESTRICT i S) a))``,

   INDUCT_THEN automaton_formula_induct STRIP_ASSUME_TAC THENL [
      FULL_SIMP_TAC std_ss [A_SEM_def, A_USED_INPUT_VARS_def, ACCEPT_COND_SEM_def] THEN
      PROVE_TAC [ACCEPT_COND_USED_VARS_INTER_SUBSET_THM],

      FULL_SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, A_SEM_def, IS_TRANSITION_def, INPUT_RUN_PATH_UNION_def,
        A_USED_INPUT_VARS_def, UNION_SUBSET, DIFF_SUBSET_ELIM, SEMI_AUTOMATON_USED_INPUT_VARS_def] THEN
      REPEAT STRIP_TAC THEN
      EXISTS_EQ_STRIP_TAC THEN
      BINOP_TAC THENL [
         SUBGOAL_TAC `!n. ((INPUT_RUN_STATE_UNION p_1 (i n) (w n)) INTER (S UNION p_1.S)) =
            ((INPUT_RUN_STATE_UNION p_1 (PATH_RESTRICT i S n) (w n)) INTER (S UNION p_1.S))` THEN1 (

            SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, INPUT_RUN_STATE_UNION_def, IN_DIFF, PATH_RESTRICT_def,
              PATH_MAP_def] THEN
            REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN
            FULL_SIMP_TAC std_ss []
         ) THEN
         PROVE_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM, P_USED_VARS_INTER_SUBSET_THM],


         REMAINS_TAC `(PATH_RESTRICT (\n. INPUT_RUN_STATE_UNION p_1 (i n) (w n)) (S UNION p_1.S)) =
                      (PATH_RESTRICT (\n. INPUT_RUN_STATE_UNION p_1 (PATH_RESTRICT i S n) (w n)) (S UNION p_1.S))` THEN1 (
           METIS_TAC[]
         ) THEN
         SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, INPUT_RUN_STATE_UNION_def] THEN
         ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
         SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF] THEN
         REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN
         FULL_SIMP_TAC std_ss []
      ],

      REWRITE_TAC [A_USED_INPUT_VARS_def,  A_SEM_def] THEN
      PROVE_TAC[],

      REWRITE_TAC [UNION_SUBSET, A_USED_INPUT_VARS_def, A_SEM_def] THEN
      PROVE_TAC[],

      REWRITE_TAC [A_SEM_def]
   ]);


val A_USED_INPUT_VARS_INTER_THM =
 store_thm
  ("A_USED_INPUT_VARS_INTER_THM",
   ``!a S i. (A_SEM i a = A_SEM (PATH_RESTRICT i (A_USED_INPUT_VARS a)) a)``,

   METIS_TAC[A_USED_INPUT_VARS_INTER_SUBSET_THM, SUBSET_REFL]);


val A_USED_INPUT_VARS_DIFF_DISJOINT_THM =
 store_thm
  ("A_USED_INPUT_VARS_DIFF_DISJOINT_THM",
   ``!a S. (DISJOINT (A_USED_INPUT_VARS a) S) ==>
      (!i. (A_SEM i a = A_SEM (PATH_DIFF i S) a))``,

   REPEAT STRIP_TAC THEN
   `A_USED_INPUT_VARS a SUBSET COMPL S` by PROVE_TAC[SUBSET_COMPL_DISJOINT] THEN
   PROVE_TAC[A_USED_INPUT_VARS_INTER_SUBSET_THM, PATH_DIFF_PATH_RESTRICT]);



val A_AND___A_NDET =
 store_thm
  ("A_AND___A_NDET",

   ``!A1 f1 A2 f2. (A_USED_STATE_VARS_COMPATIBLE (A_NDET(A1, f1)) (A_NDET(A2, f2))) ==>
      ((AUTOMATON_EQUIV (A_AND(A_NDET(A1, f1), A_NDET(A2, f2))) (A_NDET((PRODUCT_SEMI_AUTOMATON A1 A2), A_AND(f1,f2)))))``,

   SIMP_TAC std_ss [A_USED_STATE_VARS_COMPATIBLE_def,
                    A_USED_INPUT_VARS_def,
                    A_USED_STATE_VARS_def,
                    STATE_VARDISJOINT_AUTOMATON_FORMULA_def,
                    DISJOINT_UNION_BOTH,
                    AUTOMATON_EQUIV_def,
                    DISJOINT_DIFF_ELIM_SYM,
                    A_SEM_def
                    ] THEN

   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [

      EXISTS_TAC ``PATH_UNION w w'`` THEN
      REPEAT STRIP_TAC THENL [
         METIS_TAC [PRODUCT_SEMI_AUTOMATON_RUN, DISJOINT_SYM],


         SUBGOAL_TAC `(DISJOINT (A_USED_INPUT_VARS f1) A2.S) /\
                      ((PATH_DIFF (INPUT_RUN_PATH_UNION (PRODUCT_SEMI_AUTOMATON A1 A2) v (PATH_UNION w w')) A2.S) = 
                          (PATH_DIFF (INPUT_RUN_PATH_UNION A1 v w) A2.S))` THEN1 (
           ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
           SIMP_ALL_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL, PATH_DIFF_def, IN_UNION, IN_DIFF,
             INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, PATH_UNION_def, EXTENSION, PRODUCT_SEMI_AUTOMATON_REWRITES,
             IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, PATH_SUBSET_def] THEN
           REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN PROVE_TAC[]
         ) THEN
         PROVE_TAC[A_USED_INPUT_VARS_DIFF_DISJOINT_THM],



         SUBGOAL_TAC `(DISJOINT (A_USED_INPUT_VARS f2) A1.S) /\
                      ((PATH_DIFF (INPUT_RUN_PATH_UNION (PRODUCT_SEMI_AUTOMATON A1 A2) v (PATH_UNION w w')) A1.S) = 
                          (PATH_DIFF (INPUT_RUN_PATH_UNION A2 v w') A1.S))` THEN1 (
           ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
           SIMP_ALL_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL, PATH_DIFF_def, IN_UNION, IN_DIFF,
             INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, PATH_UNION_def, EXTENSION, PRODUCT_SEMI_AUTOMATON_REWRITES,
             IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, PATH_SUBSET_def] THEN
           REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN PROVE_TAC[]
         ) THEN
         PROVE_TAC[A_USED_INPUT_VARS_DIFF_DISJOINT_THM]
      ],


      EXISTS_TAC ``(PATH_RESTRICT w A1.S)`` THEN
      REPEAT STRIP_TAC THENL [
         PROVE_TAC [PRODUCT_SEMI_AUTOMATON_RUN2___FIRST, DISJOINT_SYM],


         SUBGOAL_TAC `(DISJOINT (A_USED_INPUT_VARS f1) A2.S) /\
                      ((PATH_DIFF (INPUT_RUN_PATH_UNION A1 v (PATH_RESTRICT w A1.S)) A2.S) =
                      (PATH_DIFF (INPUT_RUN_PATH_UNION (PRODUCT_SEMI_AUTOMATON A1 A2) v w) A2.S))` THEN1 (
           ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
           SIMP_ALL_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL, PATH_DIFF_def, IN_UNION, IN_DIFF,
             INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, PATH_UNION_def, EXTENSION, PRODUCT_SEMI_AUTOMATON_REWRITES,
             IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, PATH_SUBSET_def, PATH_RESTRICT_def, PATH_MAP_def, IN_INTER] THEN
           REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN PROVE_TAC[]
         ) THEN
         PROVE_TAC[A_USED_INPUT_VARS_DIFF_DISJOINT_THM]
      ],


      EXISTS_TAC ``(PATH_RESTRICT w A2.S)`` THEN
      REPEAT STRIP_TAC THENL [
         PROVE_TAC [PRODUCT_SEMI_AUTOMATON_RUN2___SECOND, DISJOINT_SYM],


         SUBGOAL_TAC `(DISJOINT (A_USED_INPUT_VARS f2) A1.S) /\
                      ((PATH_DIFF (INPUT_RUN_PATH_UNION A2 v (PATH_RESTRICT w A2.S)) A1.S) =
                      (PATH_DIFF (INPUT_RUN_PATH_UNION (PRODUCT_SEMI_AUTOMATON A1 A2) v w) A1.S))` THEN1 (
           ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
           SIMP_ALL_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL, PATH_DIFF_def, IN_UNION, IN_DIFF,
             INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, PATH_UNION_def, EXTENSION, PRODUCT_SEMI_AUTOMATON_REWRITES,
             IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, PATH_SUBSET_def, PATH_RESTRICT_def, PATH_MAP_def, IN_INTER] THEN
           REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN PROVE_TAC[]
         ) THEN
         PROVE_TAC[A_USED_INPUT_VARS_DIFF_DISJOINT_THM]
      ]
   ]);




val PRODUCT_SEMI_AUTOMATON___EXISTS_RUN_WITH_PROPERTIES =
 store_thm
  ("PRODUCT_SEMI_AUTOMATON___EXISTS_RUN_WITH_PROPERTIES",

   ``!A1 C1 A2 C2. (A_USED_STATE_VARS_COMPATIBLE (A_NDET(A1, A_BIGAND C1)) (A_NDET(A2, A_BIGAND C2))) ==>
      (((EXISTS_RUN_WITH_PROPERTIES A1 C1) /\ (EXISTS_RUN_WITH_PROPERTIES A2 C2)) ==>
      (EXISTS_RUN_WITH_PROPERTIES (PRODUCT_SEMI_AUTOMATON A1 A2) (C1++C2)))``,



   REPEAT STRIP_TAC THEN
   SIMP_ALL_TAC std_ss [EXISTS_RUN_WITH_PROPERTIES_def, EXISTS_UNIQUE_DEF, A_BIGAND___A_SEM, A_SEM_def] THEN
   SUBGOAL_TAC `AUTOMATON_EQUIV (A_AND (A_NDET (A1, A_BIGAND C1),A_NDET (A2, A_BIGAND C2))) 
                                (A_NDET (PRODUCT_SEMI_AUTOMATON A1 A2,A_AND (A_BIGAND C1,A_BIGAND C2)))` THEN1 (
      PROVE_TAC[A_AND___A_NDET]
   ) THEN
   SIMP_ALL_TAC std_ss [A_BIGAND_def, A_BIGAND___A_SEM, AUTOMATON_EQUIV_def, A_SEM_def] THEN
   PROVE_TAC[]);


val PRODUCT_SEMI_AUTOMATON___UNIQUE_RUN_WITH_PROPERTIES =
 store_thm
  ("PRODUCT_SEMI_AUTOMATON___UNIQUE_RUN_WITH_PROPERTIES",

   ``!A1 C1 A2 C2. (A_USED_STATE_VARS_COMPATIBLE (A_NDET(A1, A_BIGAND C1)) (A_NDET(A2, A_BIGAND C2))) ==>
      (((UNIQUE_RUN_WITH_PROPERTIES A1 C1) /\ (UNIQUE_RUN_WITH_PROPERTIES A2 C2)) ==>
      (UNIQUE_RUN_WITH_PROPERTIES (PRODUCT_SEMI_AUTOMATON A1 A2) (C1++C2)))``,

   REPEAT STRIP_TAC THEN
   SIMP_ALL_TAC std_ss [UNIQUE_RUN_WITH_PROPERTIES_def, EXISTS_UNIQUE_DEF, A_BIGAND___A_SEM, A_SEM_def] THEN
   REPEAT STRIP_TAC THENL [
      `AUTOMATON_EQUIV (A_AND (A_NDET (A1, A_BIGAND C1),A_NDET (A2, A_BIGAND C2))) (A_NDET (PRODUCT_SEMI_AUTOMATON A1 A2,A_AND (A_BIGAND C1,A_BIGAND C2)))` by PROVE_TAC[A_AND___A_NDET] THEN
      SIMP_ALL_TAC std_ss [A_BIGAND_def, A_BIGAND___A_SEM, AUTOMATON_EQUIV_def, A_SEM_def] THEN
      PROVE_TAC[],


      REMAINS_TAC `(PATH_RESTRICT x A1.S = PATH_RESTRICT y A1.S) /\
                   (PATH_RESTRICT x A2.S = PATH_RESTRICT y A2.S)` THEN1 (

        `(x = PATH_UNION (PATH_RESTRICT x A1.S) (PATH_RESTRICT x A2.S)) /\
         (y = PATH_UNION (PATH_RESTRICT y A1.S) (PATH_RESTRICT y A2.S))`
            by METIS_TAC[IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, PATH_PARTITION, PRODUCT_SEMI_AUTOMATON_REWRITES] THEN
        PROVE_TAC[]
      ) THEN

      REMAINS_TAC `(IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A1 i (PATH_RESTRICT x A1.S) /\ IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A2 i (PATH_RESTRICT x A2.S) /\
                   IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A1 i (PATH_RESTRICT y A1.S) /\ IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A2 i (PATH_RESTRICT y A2.S)) /\
                  (A_SEM (INPUT_RUN_PATH_UNION A1 i (PATH_RESTRICT x A1.S)) (A_BIGAND C1) /\
                   A_SEM (INPUT_RUN_PATH_UNION A1 i (PATH_RESTRICT y A1.S)) (A_BIGAND C1) /\
                   A_SEM (INPUT_RUN_PATH_UNION A2 i (PATH_RESTRICT x A2.S)) (A_BIGAND C2) /\
                   A_SEM (INPUT_RUN_PATH_UNION A2 i (PATH_RESTRICT y A2.S)) (A_BIGAND C2))` THEN1 (
        METIS_TAC[]
      ) THEN


      SUBGOAL_TAC `DISJOINT A1.S A2.S /\
                   DISJOINT A2.S (SEMI_AUTOMATON_USED_INPUT_VARS A1) /\
                   DISJOINT A1.S (SEMI_AUTOMATON_USED_INPUT_VARS A2) /\
                   DISJOINT (A_USED_INPUT_VARS (A_BIGAND C2)) A1.S /\
                   DISJOINT (A_USED_INPUT_VARS (A_BIGAND C1)) A2.S` THEN1 (
        SIMP_ALL_TAC std_ss [A_USED_STATE_VARS_COMPATIBLE_def, A_USED_STATE_VARS_def,
          A_USED_INPUT_VARS_def, DISJOINT_UNION_BOTH] THEN
        PROVE_TAC[DISJOINT_SYM, DISJOINT_DIFF_ELIM_SYM]
      ) THEN
      SUBGOAL_TAC `((PATH_DIFF (INPUT_RUN_PATH_UNION (PRODUCT_SEMI_AUTOMATON A1 A2) i x) A1.S) =
                    (PATH_DIFF (INPUT_RUN_PATH_UNION A2 i (PATH_RESTRICT x A2.S)) A1.S)) /\

                    ((PATH_DIFF (INPUT_RUN_PATH_UNION (PRODUCT_SEMI_AUTOMATON A1 A2) i x) A2.S) =
                    (PATH_DIFF (INPUT_RUN_PATH_UNION A1 i (PATH_RESTRICT x A1.S)) A2.S)) /\
            
                    ((PATH_DIFF (INPUT_RUN_PATH_UNION (PRODUCT_SEMI_AUTOMATON A1 A2) i y) A1.S) =
                    (PATH_DIFF (INPUT_RUN_PATH_UNION A2 i (PATH_RESTRICT y A2.S)) A1.S)) /\
            
                    ((PATH_DIFF (INPUT_RUN_PATH_UNION (PRODUCT_SEMI_AUTOMATON A1 A2) i y) A2.S) =
                    (PATH_DIFF (INPUT_RUN_PATH_UNION A1 i (PATH_RESTRICT y A1.S)) A2.S))` THEN1 (
    
        UNDISCH_NO_TAC 7 THEN UNDISCH_NO_TAC 9 THEN REPEAT WEAKEN_HD_TAC THEN
        ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
        SIMP_TAC std_ss [PATH_DIFF_def, INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, EXTENSION, 
          PATH_RESTRICT_def, PRODUCT_SEMI_AUTOMATON_REWRITES, IN_UNION, IN_DIFF, PATH_MAP_def, IN_INTER, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
          PATH_SUBSET_def, SUBSET_DEF] THEN
        REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN
        PROVE_TAC[]
      ) THEN
      PROVE_TAC[PRODUCT_SEMI_AUTOMATON_RUN2___FIRST, PRODUCT_SEMI_AUTOMATON_RUN2___SECOND, A_USED_INPUT_VARS_DIFF_DISJOINT_THM]
   ]);



val A_NDET___FLATTENING =
 store_thm
  ("A_NDET___FLATTENING",

   ``!A1 A2 f. ( A_USED_STATE_VARS_COMPATIBLE (A_NDET(A1, A_TRUE)) (A_NDET(A2, f))) ==>
      ((AUTOMATON_EQUIV (A_NDET(A1, A_NDET(A2, f))) (A_NDET((PRODUCT_SEMI_AUTOMATON A1 A2), f))))``,


   SIMP_TAC std_ss [AUTOMATON_EQUIV_def, A_SEM_def, A_USED_STATE_VARS_COMPATIBLE_def, DISJOINT_UNION_BOTH, 
     A_USED_INPUT_VARS_def, SEMI_AUTOMATON_USED_INPUT_VARS_def, EMPTY_DIFF, UNION_EMPTY, A_USED_STATE_VARS_def] THEN
   REPEAT STRIP_TAC THEN 
   FULL_SIMP_TAC std_ss [DISJOINT_UNION_BOTH, DISJOINT_DIFF_ELIM_SYM] THEN
   SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, INPUT_RUN_PATH_UNION_def, PRODUCT_SEMI_AUTOMATON_REWRITES, PATH_SUBSET_def, SUBSET_DEF, IN_UNION,
      P_SEM_THM, INPUT_RUN_STATE_UNION_def, IS_TRANSITION_def, XP_SEM_def] THEN
   EQ_TAC THEN REPEAT STRIP_TAC THENL [
      EXISTS_TAC ``PATH_UNION w w'`` THEN
      SIMP_TAC std_ss [PATH_UNION_def, IN_UNION] THEN
      
      SUBGOAL_TAC `!n. (((w n UNION w' n UNION (v n DIFF (A1.S UNION A2.S)))) =
                        ((w' n UNION (w n UNION (v n DIFF A1.S) DIFF A2.S)))) /\
                       (((w n UNION w' n UNION (v n DIFF (A1.S UNION A2.S))) INTER (COMPL A2.S)) =
                        ((w n UNION (v n DIFF A1.S)) INTER (COMPL A2.S)))` THEN1 (
        SIMP_ALL_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF, IN_COMPL, GSYM SUBSET_COMPL_DISJOINT,
          SUBSET_DEF, IN_COMPL] THEN
        REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN PROVE_TAC[]
      ) THEN
      SUBGOAL_TAC `P_USED_VARS A1.S0 SUBSET (COMPL A2.S) /\
                   P_USED_VARS A2.S0 SUBSET (COMPL A1.S) /\
                   XP_USED_VARS A1.R SUBSET (COMPL A2.S) /\
                   XP_USED_VARS A2.R SUBSET (COMPL A1.S)` THEN1 (
        PROVE_TAC[SUBSET_COMPL_DISJOINT]
      ) THEN
      REPEAT STRIP_TAC THENL [
        PROVE_TAC[],
        PROVE_TAC[],
        PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM],
        PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM],
        PROVE_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM],
        PROVE_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM],
        ASM_SIMP_TAC std_ss []
      ],


      EXISTS_TAC ``(PATH_RESTRICT w A1.S)`` THEN
      SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, IN_INTER] THEN
      SUBGOAL_TAC `!n. (((w n UNION (v n DIFF (A1.S UNION A2.S))) INTER (COMPL A2.S)) =
                        ((w n INTER A1.S) UNION (v n DIFF A1.S)) INTER (COMPL A2.S))` THEN1 (
        SIMP_ALL_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF, IN_COMPL, GSYM SUBSET_COMPL_DISJOINT,
          SUBSET_DEF, IN_COMPL] THEN
        REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN PROVE_TAC[]
      ) THEN
      SUBGOAL_TAC `P_USED_VARS A1.S0 SUBSET (COMPL A2.S) /\
                   XP_USED_VARS A1.R SUBSET (COMPL A2.S)` THEN1 (
        PROVE_TAC[SUBSET_COMPL_DISJOINT]
      ) THEN
      REPEAT STRIP_TAC THENL [
        PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM],
        PROVE_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM],

        EXISTS_TAC ``(PATH_RESTRICT w A2.S)`` THEN
        SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, IN_INTER] THEN
        SUBGOAL_TAC `!n. (w n INTER A2.S UNION (w n INTER A1.S UNION (v n DIFF A1.S) DIFF A2.S)) =
                         (w n UNION (v n DIFF (A1.S UNION A2.S)))` THEN1 (
          SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF] THEN
          REPEAT STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC THEN METIS_TAC[]
        ) THEN
        ASM_SIMP_TAC std_ss []
      ]
   ]);








val TOTAL_DET_AUTOMATON_EX_ALL_EQUIV =
 store_thm
  ("TOTAL_DET_AUTOMATON_EX_ALL_EQUIV",
   ``!A. IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON A ==> (!f. AUTOMATON_EQUIV (A_NDET(A,f)) (A_UNIV(A,f)))``,

   REPEAT STRIP_TAC THEN
   REWRITE_TAC [AUTOMATON_EQUIV_def, A_SEM_THM] THEN
   METIS_TAC[TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_UNIQUE_RUN]);


val UNIQUE_RUN_WITH_PROPERTIES___CONSTRAINED_AUTOMATON_EX_ALL_EQUIV =
 store_thm
  ("UNIQUE_RUN_WITH_PROPERTIES___CONSTRAINED_AUTOMATON_EX_ALL_EQUIV",
   ``!A C. (UNIQUE_RUN_WITH_PROPERTIES A C) ==> (!f. AUTOMATON_EQUIV (A_NDET_CONSTRAINED (A,C,f)) (A_UNIV_CONSTRAINED (A,C,f)))``,

   REWRITE_TAC [AUTOMATON_EQUIV_def,
                A_NDET_CONSTRAINED_def,
                A_UNIV_CONSTRAINED_def,
                A_SEM_THM,
                UNIQUE_RUN_WITH_PROPERTIES_def] THEN
   METIS_TAC[]);


val NEG_ACCEPTANCE_CONDITION =
 store_thm
  ("NEG_ACCEPTANCE_CONDITION",
   ``!A f. AUTOMATON_EQUIV (A_NOT(A_NDET(A,f))) (A_UNIV(A, A_NOT f))``,

   REPEAT STRIP_TAC THEN
   REWRITE_TAC [AUTOMATON_EQUIV_def, A_SEM_THM] THEN
   METIS_TAC[]);


val NEG_ACCEPTANCE_CONDITION_DET =
 store_thm
  ("NEG_ACCEPTANCE_CONDITION_DET",
   ``!A f. IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON A ==> (AUTOMATON_EQUIV (A_NOT(A_NDET(A,f))) (A_NDET(A, A_NOT f)))``,

   REPEAT STRIP_TAC THEN
   REWRITE_TAC [AUTOMATON_EQUIV_def, A_SEM_THM] THEN
   METIS_TAC[TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_UNIQUE_RUN]);



val ACCEPT_COND___VAR_RENAMING___NOT_INJ =
 store_thm
  ("ACCEPT_COND___VAR_RENAMING___NOT_INJ",
   ``!ac t i f. 
      (ACCEPT_COND_SEM_TIME t i (ACCEPT_VAR_RENAMING f ac)) =
      (ACCEPT_COND_SEM_TIME t (\n x. f x IN i n) ac)``,

   INDUCT_THEN acceptance_condition_induct ASSUME_TAC THEN (
     FULL_SIMP_TAC std_ss [ACCEPT_VAR_RENAMING_def, ACCEPT_COND_SEM_TIME_def,
        P_SEM___VAR_RENAMING___NOT_INJ]
   ));


val ACCEPT_COND___VAR_RENAMING =
 store_thm
  ("ACCEPT_COND___VAR_RENAMING",
   ``!a t i f. (INJ f (PATH_USED_VARS i UNION ACCEPT_COND_USED_VARS a) UNIV) ==>
      ((ACCEPT_COND_SEM_TIME t i a) = (ACCEPT_COND_SEM_TIME t (PATH_VAR_RENAMING f i) (ACCEPT_VAR_RENAMING f a)))``,


   INDUCT_THEN acceptance_condition_induct ASSUME_TAC THENL [
      REPEAT STRIP_TAC THEN
      SIMP_ALL_TAC std_ss [ACCEPT_COND_SEM_TIME_def, ACCEPT_VAR_RENAMING_def,
        PATH_VAR_RENAMING_def, PATH_MAP_def, ACCEPT_COND_USED_VARS_def] THEN
      SUBGOAL_TAC `(i t UNION  P_USED_VARS p) SUBSET (PATH_USED_VARS i UNION P_USED_VARS p)` THEN1 (
         SIMP_TAC std_ss [PATH_USED_VARS_def, SUBSET_DEF, IN_UNION, IN_BIGUNION, GSPECIFICATION] THEN
         PROVE_TAC[]
      ) THEN
      PROVE_TAC[P_SEM___VAR_RENAMING, INJ_SUBSET],

      SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def, ACCEPT_VAR_RENAMING_def],

      ASM_SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def, ACCEPT_VAR_RENAMING_def, ACCEPT_COND_USED_VARS_def],

      SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def, ACCEPT_VAR_RENAMING_def, ACCEPT_COND_USED_VARS_def] THEN
      PROVE_TAC[INJ_SUBSET, SUBSET_UNION, UNION_COMM, UNION_ASSOC],

      SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def, ACCEPT_VAR_RENAMING_def, ACCEPT_COND_USED_VARS_def] THEN
      PROVE_TAC[]
   ]);




val AUTOMATON_FORMULA___VAR_RENAMING =
 store_thm
  ("AUTOMATON_FORMULA___VAR_RENAMING",
   ``!a i (f:'a->'b). (INJ f (PATH_USED_VARS i UNION A_USED_VARS a) UNIV) ==>
      ((A_SEM i a) = (A_SEM (PATH_VAR_RENAMING f i) (A_VAR_RENAMING f a)))``,

   INDUCT_THEN automaton_formula_induct ASSUME_TAC THENL [      
      REPEAT STRIP_TAC THEN
      REWRITE_TAC [A_SEM_def, A_VAR_RENAMING_def, ACCEPT_COND_SEM_def] THEN
      SIMP_ALL_TAC std_ss [A_USED_VARS___DIRECT_DEF] THEN
      PROVE_TAC[ACCEPT_COND___VAR_RENAMING, A_USED_VARS_def],

      REPEAT STRIP_TAC THEN
      SIMP_TAC std_ss [A_SEM_def, A_VAR_RENAMING_def] THEN
      EQ_TAC THEN REPEAT STRIP_TAC THENL [
         Q_TAC EXISTS_TAC `PATH_VAR_RENAMING f w` THEN
         REPEAT STRIP_TAC THENL [
            UNDISCH_KEEP_NO_TAC 1 THEN
            IMP_TO_EQ_TAC THEN
            MATCH_MP_TAC SEMI_AUTOMATON___VAR_RENAMING THEN
            UNDISCH_NO_TAC 2 THEN
            MATCH_MP_TAC INJ_SUBSET THEN
            SIMP_ALL_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
              PATH_SUBSET_def, SUBSET_DEF] THEN
            SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, A_USED_VARS___DIRECT_DEF,
              SEMI_AUTOMATON_USED_VARS_def, GSYM PATH_USED_VARS_THM] THEN
            PROVE_TAC[],


            SUBGOAL_TAC `(INPUT_RUN_PATH_UNION (SEMI_AUTOMATON_VAR_RENAMING f p_1) (PATH_VAR_RENAMING f i) (PATH_VAR_RENAMING f w)) = 
                         (PATH_VAR_RENAMING f ((INPUT_RUN_PATH_UNION p_1 i w)))` THEN1 (
              ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
              Cases_on `p_1` THEN
              SIMP_ALL_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, EXTENSION, PATH_VAR_RENAMING_def, IN_UNION,
                PATH_MAP_def, IN_IMAGE, IN_DIFF, SEMI_AUTOMATON_VAR_RENAMING_def, symbolic_semi_automaton_REWRITES, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, PATH_SUBSET_def, SUBSET_DEF,
                INJ_DEF, IN_UNIV,
                GSYM PATH_USED_VARS_THM,
                A_USED_VARS___DIRECT_DEF,
                SEMI_AUTOMATON_USED_VARS___DIRECT_DEF] THEN
              METIS_TAC[]
            ) THEN
            ASM_REWRITE_TAC[] THEN
            REMAINS_TAC `INJ f (PATH_USED_VARS (INPUT_RUN_PATH_UNION p_1 i w) UNION A_USED_VARS a) UNIV` THEN1 (
              PROVE_TAC[]
            ) THEN
            UNDISCH_NO_TAC 3 THEN
            MATCH_MP_TAC INJ_SUBSET THEN
            SIMP_ALL_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
              PATH_SUBSET_def, SUBSET_DEF] THEN
            SIMP_TAC std_ss [EXTENSION, IN_UNION, A_USED_VARS___DIRECT_DEF,
              SUBSET_DEF, GSYM PATH_USED_VARS_THM, IN_DIFF,
              INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
              SEMI_AUTOMATON_USED_VARS___DIRECT_DEF] THEN
            PROVE_TAC[]
         ],

         SUBGOAL_TAC `?w'. PATH_SUBSET w' p_1.S /\ (w = PATH_VAR_RENAMING f w')` THEN1 (
            MATCH_MP_TAC PATH_VAR_RENAMING___ORIG_PATH_EXISTS THEN
            Cases_on `p_1` THEN
            FULL_SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
              SEMI_AUTOMATON_VAR_RENAMING_def, symbolic_semi_automaton_REWRITES]
         ) THEN
         Q_TAC EXISTS_TAC `w'` THEN
         REPEAT STRIP_TAC THENL [
            UNDISCH_NO_TAC 3 THEN
            IMP_TO_EQ_TAC THEN
            ASM_REWRITE_TAC [] THEN
            MATCH_MP_TAC (GSYM SEMI_AUTOMATON___VAR_RENAMING) THEN
            UNDISCH_NO_TAC 3 THEN
            MATCH_MP_TAC INJ_SUBSET THEN
            SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, A_USED_VARS___DIRECT_DEF,
              SEMI_AUTOMATON_USED_VARS_def, GSYM PATH_USED_VARS_THM] THEN
            SIMP_ALL_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF] THEN
            PROVE_TAC[],



            SUBGOAL_TAC `(INPUT_RUN_PATH_UNION (SEMI_AUTOMATON_VAR_RENAMING f p_1) (PATH_VAR_RENAMING f i) (PATH_VAR_RENAMING f w')) = 
                         (PATH_VAR_RENAMING f ((INPUT_RUN_PATH_UNION p_1 i w')))` THEN1 (
              ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
              Cases_on `p_1` THEN
              SIMP_ALL_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, EXTENSION, PATH_VAR_RENAMING_def, IN_UNION,
                PATH_MAP_def, IN_IMAGE, IN_DIFF, SEMI_AUTOMATON_VAR_RENAMING_def, symbolic_semi_automaton_REWRITES, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, PATH_SUBSET_def, SUBSET_DEF,
                INJ_DEF, IN_UNIV,
                GSYM PATH_USED_VARS_THM,
                A_USED_VARS___DIRECT_DEF,
                SEMI_AUTOMATON_USED_VARS___DIRECT_DEF] THEN
              METIS_TAC[]
            ) THEN
            REMAINS_TAC `INJ f (PATH_USED_VARS (INPUT_RUN_PATH_UNION p_1 i w') UNION A_USED_VARS a) UNIV` THEN1 (
              PROVE_TAC[]
            ) THEN
            UNDISCH_NO_TAC 5 THEN
            MATCH_MP_TAC INJ_SUBSET THEN
            SIMP_ALL_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF] THEN
            SIMP_TAC std_ss [EXTENSION, IN_UNION, A_USED_VARS___DIRECT_DEF,
              SUBSET_DEF, GSYM PATH_USED_VARS_THM, IN_DIFF,
              INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
              SEMI_AUTOMATON_USED_VARS___DIRECT_DEF] THEN
            PROVE_TAC[]
         ]
      ],

      

      ASM_SIMP_TAC std_ss [A_USED_VARS___DIRECT_DEF, A_VAR_RENAMING_def, A_SEM_def],



      ASM_SIMP_TAC std_ss [A_USED_VARS___DIRECT_DEF, A_VAR_RENAMING_def, A_SEM_def] THEN
      REPEAT STRIP_TAC THEN
      REMAINS_TAC `INJ f (PATH_USED_VARS i UNION A_USED_VARS a) UNIV /\
                   INJ f (PATH_USED_VARS i UNION A_USED_VARS a') UNIV` THEN1 (
        PROVE_TAC[]
      ) THEN
      STRIP_TAC THEN
      UNDISCH_HD_TAC THEN
      MATCH_MP_TAC INJ_SUBSET THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
      PROVE_TAC[],



      REWRITE_TAC[A_SEM_def, A_VAR_RENAMING_def] 
   ]);
      
      

val AUTOMATON_FORMULA___STATE_VAR_RENAMING =
 store_thm
  ("AUTOMATON_FORMULA___STATE_VAR_RENAMING",
   ``!a i f. ((INJ f (PATH_USED_VARS i UNION A_USED_VARS a) UNIV) /\ (!x. x IN (A_USED_INPUT_VARS a) ==> (f x = x))) ==>
      ((A_SEM i a) = (A_SEM i (A_VAR_RENAMING f a)))``,

   REPEAT STRIP_TAC THEN
   REMAINS_TAC `(PATH_RESTRICT (PATH_VAR_RENAMING f i) (A_USED_INPUT_VARS (A_VAR_RENAMING f a))) =
                (PATH_RESTRICT i (A_USED_INPUT_VARS (A_VAR_RENAMING f a)))` THEN1 (
      PROVE_TAC[AUTOMATON_FORMULA___VAR_RENAMING, A_USED_INPUT_VARS_INTER_THM]
   ) THEN

   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_VAR_RENAMING_def, PATH_MAP_def, EXTENSION, IN_INTER] THEN
   REPEAT STRIP_TAC THEN CONJ_EQ_STRIP_TAC THEN
   SUBGOAL_TAC `x' IN IMAGE f (A_USED_INPUT_VARS a)` THEN1 (  
      `INJ f (A_USED_VARS a) UNIV` by METIS_TAC[INJ_SUBSET, SUBSET_UNION] THEN
      FULL_SIMP_TAC std_ss [A_VAR_RENAMING___USED_INPUT_VARS]
   ) THEN
   SIMP_ALL_TAC std_ss [IN_IMAGE, INJ_DEF, IN_UNIV, IN_UNION, GSYM PATH_USED_VARS_THM, A_USED_VARS_def] THEN
   METIS_TAC[]);


val A_SEM_AUTOMATON_RUN___STATE_VAR_RENAMING =
 store_thm
  ("A_SEM_AUTOMATON_RUN___STATE_VAR_RENAMING",
   ``!A a f. ((INJ f UNIV UNIV) /\ (!x. x IN (SEMI_AUTOMATON_USED_INPUT_VARS A UNION (A_USED_INPUT_VARS a DIFF A.S)) ==> (f x = x))) ==>
     !i w. (A_SEM (INPUT_RUN_PATH_UNION A i w) a = A_SEM (INPUT_RUN_PATH_UNION (SEMI_AUTOMATON_VAR_RENAMING f A) i (PATH_VAR_RENAMING f w)) (A_VAR_RENAMING f a))``,


   REPEAT STRIP_TAC THEN
   REMAINS_TAC `(PATH_RESTRICT (PATH_VAR_RENAMING f (INPUT_RUN_PATH_UNION A i w)) (A_USED_INPUT_VARS (A_VAR_RENAMING f a))) =
                (PATH_RESTRICT (INPUT_RUN_PATH_UNION (SEMI_AUTOMATON_VAR_RENAMING f A) i (PATH_VAR_RENAMING f w)) (A_USED_INPUT_VARS (A_VAR_RENAMING f a)))` THEN1 (
      PROVE_TAC[AUTOMATON_FORMULA___VAR_RENAMING, A_USED_INPUT_VARS_INTER_THM,
        INJ_SUBSET, SUBSET_UNIV]
   ) THEN

   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   Cases_on `A` THEN
   SIMP_ALL_TAC std_ss [PATH_RESTRICT_def, PATH_VAR_RENAMING_def, PATH_MAP_def, EXTENSION, IN_INTER, IN_UNION, IN_DIFF,
     INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, IN_IMAGE, SEMI_AUTOMATON_VAR_RENAMING_def, symbolic_semi_automaton_REWRITES] THEN
   REPEAT STRIP_TAC THEN CONJ_EQ_STRIP_TAC THEN
   `x'' IN IMAGE f (A_USED_INPUT_VARS a)` by PROVE_TAC[INJ_SUBSET, SUBSET_UNIV, A_VAR_RENAMING___USED_INPUT_VARS] THEN
   SIMP_ALL_TAC std_ss [IN_IMAGE, INJ_DEF, IN_UNIV] THEN
   METIS_TAC[]);





val STATE_VARDISJOINT_AUTOMATON_FORMULA___VAR_RENAMING =
 store_thm
  ("STATE_VARDISJOINT_AUTOMATON_FORMULA___VAR_RENAMING",

   ``!a f. ((INJ f (A_USED_STATE_VARS a) UNIV)) ==>
      (STATE_VARDISJOINT_AUTOMATON_FORMULA (A_VAR_RENAMING f a) = STATE_VARDISJOINT_AUTOMATON_FORMULA a)``,

   INDUCT_THEN automaton_formula_induct STRIP_ASSUME_TAC THENL [

      SIMP_TAC std_ss [A_USED_STATE_VARS_def, STATE_VARDISJOINT_AUTOMATON_FORMULA_def,
        A_VAR_RENAMING_def],

      Cases_on `p_1` THEN
      SIMP_ALL_TAC std_ss [A_USED_STATE_VARS_def, STATE_VARDISJOINT_AUTOMATON_FORMULA_def,
        A_VAR_RENAMING_def, symbolic_semi_automaton_REWRITES, SEMI_AUTOMATON_VAR_RENAMING_def,
        A_VAR_RENAMING___USED_STATE_VARS] THEN
      REPEAT STRIP_TAC THEN 
      BINOP_TAC THENL [
         SIMP_ALL_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL, INJ_DEF, IN_UNIV, IN_UNION, IN_IMAGE] THEN
         PROVE_TAC[],

         PROVE_TAC[SUBSET_UNION, INJ_SUBSET]
      ],

      ASM_SIMP_TAC std_ss [A_USED_STATE_VARS_def, STATE_VARDISJOINT_AUTOMATON_FORMULA_def, A_VAR_RENAMING_def],

      ASM_SIMP_TAC std_ss [A_USED_STATE_VARS_def, STATE_VARDISJOINT_AUTOMATON_FORMULA_def, A_VAR_RENAMING_def, 
        A_VAR_RENAMING___USED_STATE_VARS] THEN
      REPEAT STRIP_TAC THEN
      BINOP_TAC THENL [
         SIMP_ALL_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL, INJ_DEF, IN_UNIV, IN_UNION, IN_IMAGE] THEN
         PROVE_TAC[],

         PROVE_TAC[SUBSET_UNION, INJ_SUBSET]
      ],

      SIMP_TAC std_ss [A_VAR_RENAMING_def, STATE_VARDISJOINT_AUTOMATON_FORMULA_def]
   ]);





val VARDISJOINT_AUTOMATON_FORMULA___VAR_RENAMING =
 store_thm
  ("VARDISJOINT_AUTOMATON_FORMULA___VAR_RENAMING",

   ``!a f. ((INJ f (A_USED_VARS a) UNIV)) ==>
      (VARDISJOINT_AUTOMATON_FORMULA (A_VAR_RENAMING f a) = VARDISJOINT_AUTOMATON_FORMULA a)``,

   REWRITE_TAC[VARDISJOINT_AUTOMATON_FORMULA_def, A_USED_VARS_def] THEN
   REPEAT GEN_TAC THEN DISCH_TAC THEN BINOP_TAC THENL[
      PROVE_TAC[STATE_VARDISJOINT_AUTOMATON_FORMULA___VAR_RENAMING, INJ_SUBSET, SUBSET_UNION],

      `A_USED_INPUT_VARS (A_VAR_RENAMING f a) = IMAGE f (A_USED_INPUT_VARS a)` by 
        PROVE_TAC[A_VAR_RENAMING___USED_INPUT_VARS, A_USED_VARS_def] THEN
      ASM_SIMP_TAC std_ss [A_VAR_RENAMING___USED_STATE_VARS, A_VAR_RENAMING___USED_INPUT_VARS, A_USED_VARS_def,
        GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL, IN_IMAGE] THEN
      SIMP_ASSUMPTIONS_TAC std_ss [INJ_DEF, IN_UNION, IN_UNIV] THEN
      PROVE_TAC[]
   ]);







val EXISTS_RUN_WITH_PROPERTIES___A_SEM_REWRITE =
 store_thm
  ("EXISTS_RUN_WITH_PROPERTIES___A_SEM_REWRITE",
   ``!A C. EXISTS_RUN_WITH_PROPERTIES A C =
     (!i. A_SEM i (A_NDET (A, A_BIGAND C)))``,

  SIMP_TAC std_ss [EXISTS_RUN_WITH_PROPERTIES_def, A_SEM_def]);





val EXISTS_RUN_WITH_PROPERTIES___STATE_VAR_RENAMING =
 store_thm
  ("EXISTS_RUN_WITH_PROPERTIES___STATE_VAR_RENAMING",
   ``!A C f. ((INJ f UNIV UNIV) /\ (!x. x IN (SEMI_AUTOMATON_USED_INPUT_VARS A
         UNION ((A_USED_INPUT_VARS (A_BIGAND C)) DIFF A.S)) ==> (f x = x))) ==>
      ((EXISTS_RUN_WITH_PROPERTIES (SEMI_AUTOMATON_VAR_RENAMING f A) (MAP (A_VAR_RENAMING f) C)) = (EXISTS_RUN_WITH_PROPERTIES A C))``,


   REPEAT STRIP_TAC THEN
   SIMP_TAC std_ss [EXISTS_RUN_WITH_PROPERTIES___A_SEM_REWRITE, GSYM A_VAR_RENAMING___A_BIGAND,
      GSYM A_VAR_RENAMING_def] THEN
   `SEMI_AUTOMATON_USED_INPUT_VARS A UNION (A_USED_INPUT_VARS (A_BIGAND C) DIFF A.S) =
    A_USED_INPUT_VARS  (A_NDET (A,A_BIGAND C))` by SIMP_TAC std_ss [A_USED_INPUT_VARS_def] THEN
   PROVE_TAC[AUTOMATON_FORMULA___STATE_VAR_RENAMING, INJ_SUBSET, SUBSET_UNIV]);


val UNIQUE_RUN_WITH_PROPERTIES___STATE_VAR_RENAMING =
 store_thm
  ("UNIQUE_RUN_WITH_PROPERTIES___STATE_VAR_RENAMING",
   ``!A C f. ((INJ f UNIV UNIV) /\ (!x. x IN (SEMI_AUTOMATON_USED_INPUT_VARS A
         UNION ((A_USED_INPUT_VARS (A_BIGAND C)) DIFF A.S)) ==> (f x = x))) ==>
      ((UNIQUE_RUN_WITH_PROPERTIES (SEMI_AUTOMATON_VAR_RENAMING f A) (MAP (A_VAR_RENAMING f) C)) = (UNIQUE_RUN_WITH_PROPERTIES A C))``,


   SIMP_TAC std_ss [UNIQUE_RUN_WITH_PROPERTIES_def, EXISTS_UNIQUE_DEF] THEN
   REPEAT STRIP_TAC THEN SIMP_TAC std_ss [FORALL_AND_THM] THEN
   BINOP_TAC THEN1 METIS_TAC[EXISTS_RUN_WITH_PROPERTIES___STATE_VAR_RENAMING, EXISTS_RUN_WITH_PROPERTIES_def] THEN
   
   REWRITE_TAC [GSYM A_VAR_RENAMING___A_BIGAND] THEN
   FORALL_EQ_STRIP_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THENL [
     REMAINS_TAC `PATH_VAR_RENAMING f x = PATH_VAR_RENAMING f y` THEN1 (
       UNDISCH_HD_TAC THEN
       ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
       SIMP_ALL_TAC std_ss [PATH_VAR_RENAMING_def, PATH_MAP_def, EXTENSION, IN_IMAGE, INJ_DEF, IN_UNIV] THEN
       METIS_TAC[]
     ) THEN
     Q_SPECL_NO_ASSUM 4 [`PATH_VAR_RENAMING f x`, `PATH_VAR_RENAMING f y`] THEN
     METIS_TAC[A_SEM_AUTOMATON_RUN___STATE_VAR_RENAMING, SEMI_AUTOMATON___STATE_VAR_RENAMING, IN_UNION, SUBSET_UNIV, INJ_SUBSET],

     
     SUBGOAL_TAC `(?x'. x = PATH_VAR_RENAMING f x') /\ (?y'. y = PATH_VAR_RENAMING f y')` THEN1 (
       SIMP_ASSUMPTIONS_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, SEMI_AUTOMATON_VAR_RENAMING_REWRITES] THEN
       METIS_TAC[PATH_VAR_RENAMING___ORIG_PATH_EXISTS]
     ) THEN
     METIS_TAC[A_SEM_AUTOMATON_RUN___STATE_VAR_RENAMING, SEMI_AUTOMATON___STATE_VAR_RENAMING, IN_UNION]
   ]
);



val EXISTS_RUN_WITH_PROPERTIES___PROPERTIES_SPLIT =
 store_thm(
   "EXISTS_RUN_WITH_PROPERTIES___PROPERTIES_SPLIT",

   ``(!A C1 C2. EXISTS_RUN_WITH_PROPERTIES A (C1++C2) ==>
      (EXISTS_RUN_WITH_PROPERTIES A C1 /\ EXISTS_RUN_WITH_PROPERTIES A C2)) /\
     (!A c C. EXISTS_RUN_WITH_PROPERTIES A (c::C) ==>
      (EXISTS_RUN_WITH_PROPERTIES A [c] /\ EXISTS_RUN_WITH_PROPERTIES A C))``,

   REWRITE_TAC[EXISTS_RUN_WITH_PROPERTIES_def, A_BIGAND___A_SEM, A_BIGAND_def, A_SEM_def] THEN
   METIS_TAC[]);



val A_NDET___INITIAL_ACCEPTANCE_SYM =
 store_thm
  ("A_NDET___INITIAL_ACCEPTANCE_SYM",
   ``!S S0 R p C. AUTOMATON_EQUIV
   (A_NDET (symbolic_semi_automaton S S0 R,A_AND (ACCEPT_COND_PROP p,A_BIGAND C)))
   (A_NDET (symbolic_semi_automaton S (P_AND(p, S0)) R,A_BIGAND C))``,
   
   SIMP_TAC std_ss [AUTOMATON_EQUIV_def, A_SEM_def, ACCEPT_COND_PROP_def, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, symbolic_semi_automaton_REWRITES,
     IS_TRANSITION_def, INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, ACCEPT_COND_SEM_def,
     ACCEPT_COND_SEM_TIME_def, P_SEM_def] THEN
   REPEAT GEN_TAC THEN EXISTS_EQ_STRIP_TAC THEN REPEAT BOOL_EQ_STRIP_TAC);



val A_UNIV___INITIAL_ACCEPTANCE_SYM =
 store_thm
  ("A_UNIV___INITIAL_ACCEPTANCE_SYM",
   ``!S S0 R p C. AUTOMATON_EQUIV
   (A_UNIV (symbolic_semi_automaton S S0 R,A_IMPL (ACCEPT_COND_PROP p,A_BIGAND C)))
   (A_UNIV (symbolic_semi_automaton S (P_AND(p, S0)) R,A_BIGAND C))``,

   SIMP_TAC std_ss [AUTOMATON_EQUIV_def, A_SEM_def, ACCEPT_COND_PROP_def, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, symbolic_semi_automaton_REWRITES,
     IS_TRANSITION_def, INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def, ACCEPT_COND_SEM_def,
     ACCEPT_COND_SEM_TIME_def, P_SEM_def, A_UNIV_def, A_IMPL_def, A_OR_def] THEN
   METIS_TAC[]);



val ACCEPT_COND_RESTN_SEM =
 store_thm
  ("ACCEPT_COND_RESTN_SEM",
   ``!f v t1 t2. ((ACCEPT_COND_SEM_TIME (t1+t2) v f) = (ACCEPT_COND_SEM_TIME t1 (PATH_RESTN v t2) f))``,

   INDUCT_THEN acceptance_condition_induct ASSUME_TAC THENL [
      SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def, PATH_RESTN_def],
      SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def],
      ASM_SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def],
      ASM_SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def],

      ASM_SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def] THEN
      REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
         `t' + t2 >= t1 + t2` by DECIDE_TAC THEN
         PROVE_TAC[],

         `?t. t = (t' - t2)` by METIS_TAC[] THEN
         `(t' = t + t2) /\ (t >= t1)` by DECIDE_TAC THEN
         PROVE_TAC[]
      ]
   ])


val ID_AUTOMATON_SEM =
 store_thm(
   "ID_AUTOMATON_SEM",
   ``!a. AUTOMATON_EQUIV a (A_NDET(ID_SEMI_AUTOMATON, a))``,

   SIMP_TAC std_ss [AUTOMATON_EQUIV_def, EMPTY_PATH_def, A_SEM_def,
      ID_SEMI_AUTOMATON_RUN, INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
      ID_SEMI_AUTOMATON_REWRITES, UNION_EMPTY, DIFF_EMPTY] THEN
   METIS_TAC[]);






val A_NDET___SIMPLIFIED_SEMI_AUTOMATON_THM =
  store_thm (
    "A_NDET___SIMPLIFIED_SEMI_AUTOMATON_THM",

``!A A' f ac. IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON A' A f /\
            (DISJOINT (IMAGE f (SEMI_AUTOMATON_USED_INPUT_VARS A)) (ACCEPT_COND_USED_VARS ac)) ==>
            (!i. A_SEM i (A_NDET (A, ACCEPT_COND ac)) =
                 A_SEM i (A_NDET (A', ACCEPT_COND (ACCEPT_VAR_RENAMING
                    (\x. (if x IN SEMI_AUTOMATON_USED_INPUT_VARS A then f x else x)) ac))))``,


SIMP_TAC std_ss [A_SEM_THM] THEN
REPEAT STRIP_TAC THEN 
ASSUME_TAC IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON___RUNS2 THEN
Q_SPECL_NO_ASSUM 0 [`A'`, `A`, `f`] THEN
PROVE_CONDITION_NO_ASSUM 0 THEN1 ASM_REWRITE_TAC[] THEN
ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN
EQ_TAC THEN REPEAT STRIP_TAC THENL [

  Q_TAC EXISTS_TAC `\n. w n UNION (IMAGE f (i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A))` THEN
  `PATH_SUBSET w A.S` by FULL_SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def] THEN
  REPEAT STRIP_TAC THENL [    
    SIMP_ALL_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF, IN_UNION, IN_IMAGE, IN_INTER] THEN
    METIS_TAC[],

    REMAINS_TAC `PATH_RESTRICT (\n.
                  w n UNION IMAGE f (i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A))
                  A.S = w` THEN1 (
      ASM_REWRITE_TAC[]
    ) THEN

    ONCE_REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    ONCE_REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN
    SIMP_ALL_TAC std_ss [IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON_def, IN_UNION, 
      IN_IMAGE, IN_DIFF, IN_SING, PATH_RESTRICT_def, PATH_MAP_def,
      IN_INTER, PATH_SUBSET_def, SUBSET_DEF] THEN
    METIS_TAC[],
    
    SIMP_ALL_TAC std_ss [IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON_def, IN_UNION, 
      IN_IMAGE, IN_DIFF, IN_SING, PATH_RESTRICT_def, PATH_MAP_def,
      IN_INTER, PATH_SUBSET_def, SUBSET_DEF] THEN
    METIS_TAC[],


    SIMP_ALL_TAC std_ss [ACCEPT_COND___VAR_RENAMING___NOT_INJ,
      ACCEPT_COND_SEM_def] THEN
    UNDISCH_NO_TAC 1 THEN
    ONCE_REWRITE_TAC[ACCEPT_COND_USED_VARS_INTER_THM] THEN
    IMP_TO_EQ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    ONCE_REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN
    SIMP_ALL_TAC std_ss [IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON_def, 
      PATH_SUBSET_def, SUBSET_DEF, DISJOINT_DISJ_THM] THEN
    FULL_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
      IN_UNION, IN_DIFF, IN_BETA_THM, IN_IMAGE, 
      symbolic_semi_automaton_REWRITES, IN_INTER, IN_SING,
      PATH_RESTRICT_def, PATH_MAP_def, SEMI_AUTOMATON_USED_INPUT_VARS_def] THEN
    METIS_TAC[]
  ],


  Q_TAC EXISTS_TAC `PATH_RESTRICT w A.S` THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_ALL_TAC std_ss [ACCEPT_COND___VAR_RENAMING___NOT_INJ,
    ACCEPT_COND_SEM_def] THEN
  UNDISCH_NO_TAC 0 THEN
  ONCE_REWRITE_TAC[ACCEPT_COND_USED_VARS_INTER_THM] THEN
  IMP_TO_EQ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN
  SIMP_ALL_TAC std_ss [IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON_def, 
    PATH_SUBSET_def, SUBSET_DEF, DISJOINT_DISJ_THM] THEN
  FULL_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
    IN_UNION, IN_DIFF, IN_BETA_THM, IN_IMAGE, 
    symbolic_semi_automaton_REWRITES, IN_INTER, IN_SING,
    PATH_RESTRICT_def, PATH_MAP_def, SEMI_AUTOMATON_USED_INPUT_VARS_def] THEN
  METIS_TAC[]
])
  



val A_UNIV___SIMPLIFIED_SEMI_AUTOMATON_THM =
  store_thm (
    "A_UNIV___SIMPLIFIED_SEMI_AUTOMATON_THM",

``!A A' f ac. IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON A' A f /\
            (DISJOINT (IMAGE f (SEMI_AUTOMATON_USED_INPUT_VARS A)) (ACCEPT_COND_USED_VARS ac)) ==>
            (!i. A_SEM i (A_UNIV (A, ACCEPT_COND ac)) =
                 A_SEM i (A_UNIV (A', ACCEPT_COND (ACCEPT_VAR_RENAMING
                    (\x. (if x IN SEMI_AUTOMATON_USED_INPUT_VARS A then f x else x)) ac))))``,

  REPEAT STRIP_TAC THEN
  REWRITE_TAC[A_UNIV_def] THEN
  ONCE_REWRITE_TAC[A_SEM_def] THEN
  SIMP_TAC std_ss [] THEN
  SUBGOAL_TAC `!A ac i. A_SEM i (A_NDET (A, A_NOT (ACCEPT_COND ac))) =
                        A_SEM i (A_NDET (A, ACCEPT_COND (ACCEPT_NOT ac)))` THEN1 (
    SIMP_TAC std_ss [A_SEM_def, ACCEPT_COND_SEM_def, ACCEPT_COND_SEM_TIME_def]
  ) THEN
  ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

  ASSUME_TAC A_NDET___SIMPLIFIED_SEMI_AUTOMATON_THM THEN
  Q_SPECL_NO_ASSUM 0 [`A`, `A'`, `f`, `ACCEPT_NOT ac`] THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 (
    ASM_SIMP_TAC std_ss [ACCEPT_COND_USED_VARS_def]
  ) THEN
  ASM_SIMP_TAC std_ss [ACCEPT_VAR_RENAMING_def]);



val _ = export_theory();


