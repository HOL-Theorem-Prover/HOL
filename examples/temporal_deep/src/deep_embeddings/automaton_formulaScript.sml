(* -*- Mode: holscript; -*- ***************************************************)
(*                                                                            *)
(*     Automaton formula (symbolic semi-automaton + acceptance_condition)     *)
(*                                                                            *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open symbolic_semi_automatonTheory prop_logicTheory xprop_logicTheory
     set_lemmataTheory pred_setTheory listTheory pairTheory
     containerTheory infinite_pathTheory symbolic_kripke_structureTheory
     tuerk_tacticsLib temporal_deep_mixedTheory;

open Sanity;

val _ = hide "S";
val _ = hide "I";

val _ = new_theory "automaton_formula";
val _ = ParseExtras.temp_loose_equality()

(******************************************************************************)
(*                                                                            *)
(*     Acceptance conditions (a limited form of LTL with only G operator)     *)
(*                                                                            *)
(******************************************************************************)

(* see omega_automaton_translationTheory.ACCEPT_COND_TO_LTL_def for a direct
   translation to LTL, where ACCEPT_G is translated to LTL_ALWAYS
 *)
Datatype :
    acceptance_condition =
          ACCEPT_PROP ('a prop_logic)
        | ACCEPT_TRUE
        | ACCEPT_NOT   acceptance_condition
        | ACCEPT_AND  (acceptance_condition # acceptance_condition)
        | ACCEPT_G     acceptance_condition
End

Theorem acceptance_condition_induct = Q.GEN `P`
   (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2)) ==> (A ==> B1)``)
     (SIMP_RULE
       std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P x ==> Q(x,y)) = !x. P x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P y ==> Q(x,y)) = !y. P y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P`,`\(f1,f2). P f1 /\ P f2`]
         (TypeBase.induction_of ``:'a acceptance_condition``))));

val ACCEPT_COND_USED_VARS_def = Define
  `(ACCEPT_COND_USED_VARS (ACCEPT_PROP p) = P_USED_VARS p) /\
   (ACCEPT_COND_USED_VARS ACCEPT_TRUE = EMPTY) /\
   (ACCEPT_COND_USED_VARS (ACCEPT_NOT a) = ACCEPT_COND_USED_VARS a) /\
   (ACCEPT_COND_USED_VARS (ACCEPT_G a) = ACCEPT_COND_USED_VARS a) /\
   (ACCEPT_COND_USED_VARS (ACCEPT_AND(a, b)) =
     (ACCEPT_COND_USED_VARS a) UNION (ACCEPT_COND_USED_VARS b))`;

(*****************************************************************************
 * Automaton formulas
 *****************************************************************************)
Datatype : (* see [1, p.8] *)
    automaton_formula =
          ACCEPT_COND ('a acceptance_condition)
        | A_NDET      ('a symbolic_semi_automaton # automaton_formula)
        | A_NOT        automaton_formula
        | A_AND       (automaton_formula # automaton_formula)
        | A_TRUE
End

Theorem automaton_formula_induct = Q.GEN `P0`
   (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2)) ==> (A ==> B1)``)
     (SIMP_RULE std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P0 x ==> Q(x,y)) = !x. P0 x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P0 y ==> Q(x,y)) = !y. P0 y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P0`,`\(A, f). P0 f`,`\(f1,f2). P0 f1 /\ P0 f2`]
         (TypeBase.induction_of ``:'a automaton_formula``))));

val A_USED_INPUT_VARS_def = Define
  `(A_USED_INPUT_VARS (ACCEPT_COND p) = ACCEPT_COND_USED_VARS p) /\
   (A_USED_INPUT_VARS A_TRUE = EMPTY) /\
   (A_USED_INPUT_VARS (A_NDET(A, f)) =
     (SEMI_AUTOMATON_USED_INPUT_VARS A) UNION
     (A_USED_INPUT_VARS f DIFF A.S)) /\
   (A_USED_INPUT_VARS (A_NOT a) = A_USED_INPUT_VARS a) /\
   (A_USED_INPUT_VARS (A_AND(a, b)) = (A_USED_INPUT_VARS a) UNION (A_USED_INPUT_VARS b))`;

val A_USED_STATE_VARS_def = Define
  `(A_USED_STATE_VARS (ACCEPT_COND p) = EMPTY) /\
   (A_USED_STATE_VARS A_TRUE = EMPTY) /\
   (A_USED_STATE_VARS (A_NDET(A, f)) = A.S UNION (A_USED_STATE_VARS f)) /\
   (A_USED_STATE_VARS (A_NOT a) = A_USED_STATE_VARS a) /\
   (A_USED_STATE_VARS (A_AND(a, b)) = (A_USED_STATE_VARS a) UNION (A_USED_STATE_VARS b))`;

val A_USED_VARS_def = Define
   `A_USED_VARS a = (A_USED_INPUT_VARS a) UNION (A_USED_STATE_VARS a)`;

(* added toplevel quantifiers *)
Theorem A_USED_VARS___DIRECT_DEF :
   !A f p a b.
   (A_USED_VARS (ACCEPT_COND p) = ACCEPT_COND_USED_VARS p) /\
   (A_USED_VARS A_TRUE = EMPTY) /\
   (A_USED_VARS (A_NDET(A, f)) = (SEMI_AUTOMATON_USED_VARS A UNION (A_USED_VARS f))) /\
   (A_USED_VARS (A_NOT a) = (A_USED_VARS a)) /\
   (A_USED_VARS (A_AND(a, b)) = (A_USED_VARS a) UNION (A_USED_VARS b))
Proof
    SIMP_TAC std_ss [A_USED_VARS_def, A_USED_INPUT_VARS_def,
                     A_USED_STATE_VARS_def, UNION_EMPTY]
 >> rpt STRIP_TAC
 >| [ SIMP_TAC std_ss [EXTENSION, IN_UNION,
                       SEMI_AUTOMATON_USED_VARS_def, IN_DIFF] \\
      PROVE_TAC [],
      SIMP_TAC std_ss [EXTENSION, IN_UNION] >> PROVE_TAC [] ]
QED

val STATE_VARDISJOINT_AUTOMATON_FORMULA_def = Define
  `(STATE_VARDISJOINT_AUTOMATON_FORMULA (ACCEPT_COND p) = T) /\
   (STATE_VARDISJOINT_AUTOMATON_FORMULA A_TRUE = T) /\
   (STATE_VARDISJOINT_AUTOMATON_FORMULA (A_NDET(A, f)) =
     (DISJOINT A.S (A_USED_STATE_VARS f) /\ STATE_VARDISJOINT_AUTOMATON_FORMULA f)) /\
   (STATE_VARDISJOINT_AUTOMATON_FORMULA (A_NOT a) = STATE_VARDISJOINT_AUTOMATON_FORMULA a) /\
   (STATE_VARDISJOINT_AUTOMATON_FORMULA (A_AND(a, b)) =
     (DISJOINT (A_USED_STATE_VARS a) (A_USED_STATE_VARS b) /\
      STATE_VARDISJOINT_AUTOMATON_FORMULA a /\ STATE_VARDISJOINT_AUTOMATON_FORMULA b))`;

(* also disjoint with input variables *)
val VARDISJOINT_AUTOMATON_FORMULA_def = Define
   `VARDISJOINT_AUTOMATON_FORMULA f =
     (STATE_VARDISJOINT_AUTOMATON_FORMULA f /\
      DISJOINT (A_USED_STATE_VARS f) (A_USED_INPUT_VARS f))`;

(*****************************************************************************
 * Variable renamings
 *****************************************************************************)
val ACCEPT_VAR_RENAMING_def = Define
  `(ACCEPT_VAR_RENAMING (f:'a->'b) (ACCEPT_TRUE) = ACCEPT_TRUE) /\
   (ACCEPT_VAR_RENAMING f (ACCEPT_PROP p) = (ACCEPT_PROP (P_VAR_RENAMING f p))) /\
   (ACCEPT_VAR_RENAMING f (ACCEPT_NOT b) = ACCEPT_NOT (ACCEPT_VAR_RENAMING f b)) /\
   (ACCEPT_VAR_RENAMING f (ACCEPT_G b) = ACCEPT_G (ACCEPT_VAR_RENAMING f b)) /\
   (ACCEPT_VAR_RENAMING f (ACCEPT_AND(b1,b2)) =
      ACCEPT_AND(ACCEPT_VAR_RENAMING f b1, ACCEPT_VAR_RENAMING f b2))`;

val A_VAR_RENAMING_def = Define
  `(A_VAR_RENAMING (f:'a -> 'b) (ACCEPT_COND p) = ACCEPT_COND (ACCEPT_VAR_RENAMING f p)) /\
   (A_VAR_RENAMING f A_TRUE = A_TRUE) /\
   (A_VAR_RENAMING f (A_NDET(A:'a symbolic_semi_automaton, f')) =
      A_NDET(SEMI_AUTOMATON_VAR_RENAMING f A, A_VAR_RENAMING f f')) /\
   (A_VAR_RENAMING f (A_NOT a) = A_NOT(A_VAR_RENAMING f a)) /\
   (A_VAR_RENAMING f (A_AND(a, b)) = (A_AND (A_VAR_RENAMING f a, A_VAR_RENAMING f b)))`;

(*=============================================================================
= Semantics
=============================================================================*)

(*****************************************************************************
 * Acceptance conditions
 *****************************************************************************)
val ACCEPT_COND_SEM_TIME_def = Define
  `(ACCEPT_COND_SEM_TIME t v (ACCEPT_PROP p) = P_SEM (v t) p) /\
   (ACCEPT_COND_SEM_TIME t v ACCEPT_TRUE = T) /\
   (ACCEPT_COND_SEM_TIME t v (ACCEPT_NOT a) = ~(ACCEPT_COND_SEM_TIME t v a)) /\
   (ACCEPT_COND_SEM_TIME t v (ACCEPT_G a) =
     !t':num. t' >= t ==> ACCEPT_COND_SEM_TIME t' v a) /\
   (ACCEPT_COND_SEM_TIME t v (ACCEPT_AND(a, b)) =
     (ACCEPT_COND_SEM_TIME t v a /\ ACCEPT_COND_SEM_TIME t v b))`;

val ACCEPT_COND_SEM_def = Define
   `ACCEPT_COND_SEM v f = ACCEPT_COND_SEM_TIME 0 v f`;

(*****************************************************************************
 * Automaton formulas
 *****************************************************************************)
val A_SEM_def = Define
  `(A_SEM i (ACCEPT_COND p) = ACCEPT_COND_SEM i p) /\
   (A_SEM i (A_TRUE) = T) /\
   (A_SEM i (A_NDET(A, f)) =
      ?w. (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w) /\
          (A_SEM (INPUT_RUN_PATH_UNION A i w) f)) /\
   (A_SEM i (A_NOT a) = ~(A_SEM i a)) /\
   (A_SEM i (A_AND(a, b)) = ((A_SEM i a) /\ A_SEM i b))`;

val A_KS_SEM_def = Define
   `A_KS_SEM M A =
      !i. IS_INITIAL_PATH_THROUGH_SYMBOLIC_KRIPKE_STRUCTURE M i ==> A_SEM i A`;

(*=============================================================================
= Syntactic Sugar and elementary lemmata
=============================================================================*)

(*****************************************************************************
 * Acceptance conditions
*****************************************************************************)
val ACCEPT_F_def = Define
   `ACCEPT_F b = ACCEPT_NOT(ACCEPT_G (ACCEPT_NOT b))`;

val ACCEPT_FALSE_def = Define
   `ACCEPT_FALSE = ACCEPT_NOT(ACCEPT_TRUE)`;

val ACCEPT_OR_def = Define
   `ACCEPT_OR(b1, b2) = ACCEPT_NOT(ACCEPT_AND(ACCEPT_NOT b1, ACCEPT_NOT b2))`;

val ACCEPT_IMPL_def = Define
   `ACCEPT_IMPL(b1, b2) = ACCEPT_OR(ACCEPT_NOT b1, b2)`;

val ACCEPT_EQUIV_def = Define
   `ACCEPT_EQUIV(b1, b2) = ACCEPT_AND(ACCEPT_IMPL(b1, b2),ACCEPT_IMPL(b2, b1))`;

val ACCEPT_BIGAND_def = Define
  `(ACCEPT_BIGAND [] = ACCEPT_TRUE) /\
   (ACCEPT_BIGAND (e::C) = ACCEPT_AND(e, ACCEPT_BIGAND C))`;

(*****************************************************************************
 * Automaton formulas
 *****************************************************************************)
val A_BIGAND_def = Define
  `(A_BIGAND ([] :'a automaton_formula list) = (A_TRUE :'a automaton_formula)) /\
   (A_BIGAND (e::C) = A_AND(e, A_BIGAND C))`;

val A_UNIV_def = Define
   `A_UNIV(A, f) = A_NOT(A_NDET(A, A_NOT f))`;

val A_FALSE_def = Define
   `A_FALSE = A_NOT(A_TRUE)`;

val A_OR_def = Define
   `A_OR(b1, b2) = A_NOT(A_AND(A_NOT b1, A_NOT b2))`;

val A_IMPL_def = Define
   `A_IMPL(b1, b2) = A_OR(A_NOT b1, b2)`;

val A_EQUIV_def = Define
   `A_EQUIV(b1, b2) = A_AND(A_IMPL(b1, b2),A_IMPL(b2, b1))`;

val A_NDET_CONSTRAINED_def = Define
   `A_NDET_CONSTRAINED(A, C, f) = A_NDET(A, A_AND(f, A_BIGAND C))`;

val A_UNIV_CONSTRAINED_def = Define
   `A_UNIV_CONSTRAINED(A, C, f) = A_UNIV(A, A_IMPL(A_BIGAND C, f))`;

(* semantics of automata formula, `v` is input trace *)
Theorem A_SEM_THM :
    !A f v p a b.
      (A_SEM v (ACCEPT_COND p) = ACCEPT_COND_SEM v p) /\
      (A_SEM v (A_UNIV(A, f)) =
        !w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A v w ==> A_SEM (INPUT_RUN_PATH_UNION A v w) f) /\
      (A_SEM v (A_NDET(A, f)) =
        ?w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A v w /\ A_SEM (INPUT_RUN_PATH_UNION A v w) f) /\
      (A_SEM v A_TRUE) /\
     ~(A_SEM v A_FALSE) /\
      (A_SEM v (A_NOT a) = ~(A_SEM v a)) /\
      (A_SEM v (A_AND(a, b)) = (A_SEM v a /\ A_SEM v b)) /\
      (A_SEM v (A_OR(a, b)) = (A_SEM v a \/ A_SEM v b)) /\
      (A_SEM v (A_IMPL(a, b)) = (A_SEM v a ==> A_SEM v b)) /\
      (A_SEM v (A_EQUIV(a, b)) = (A_SEM v a <=> A_SEM v b))
Proof
    SIMP_TAC arith_ss [A_UNIV_def, A_FALSE_def, A_OR_def, A_IMPL_def, A_EQUIV_def, A_SEM_def]
 >> rpt STRIP_TAC >> PROVE_TAC []
QED

val A_USED_STATE_VARS_COMPATIBLE_def = Define
   `A_USED_STATE_VARS_COMPATIBLE a1 a2 =
     (DISJOINT (A_USED_INPUT_VARS a1) (A_USED_STATE_VARS a2) /\
      DISJOINT (A_USED_INPUT_VARS a2) (A_USED_STATE_VARS a1) /\
      DISJOINT (A_USED_STATE_VARS a1) (A_USED_STATE_VARS a2))`;

(* added toplevel quantifiers *)
Theorem VARDISJOINT_AUTOMATON_FORMULA___A_USED_STATE_VARS_COMPATIBLE :
    !a1 a2. VARDISJOINT_AUTOMATON_FORMULA (A_AND(a1, a2)) ==>
            A_USED_STATE_VARS_COMPATIBLE a1 a2
Proof
    rpt GEN_TAC
 >> REWRITE_TAC [VARDISJOINT_AUTOMATON_FORMULA_def,
                 A_USED_STATE_VARS_COMPATIBLE_def,
                 A_USED_STATE_VARS_def, A_USED_INPUT_VARS_def,
                 STATE_VARDISJOINT_AUTOMATON_FORMULA_def, DISJOINT_UNION_BOTH]
 >> PROVE_TAC []
QED

(* two automata are equivalent if they accept the same set of input traces *)
val AUTOMATON_EQUIV_def = Define
   `AUTOMATON_EQUIV a1 a2 = !v. A_SEM v a1 <=> A_SEM v a2`;

Theorem AUTOMATON_EQUIV_THM :
      (!A f. AUTOMATON_EQUIV (A_NDET(A, f)) (A_NOT (A_UNIV(A, A_NOT f)))) /\
      (!A f. AUTOMATON_EQUIV (A_UNIV(A, f)) (A_NOT (A_NDET(A, A_NOT f)))) /\
      (!a1 a2. AUTOMATON_EQUIV (A_NOT a1) (A_NOT a2) <=> AUTOMATON_EQUIV a1 a2) /\
      (!a1 a2. AUTOMATON_EQUIV (A_AND (a1,a2)) (A_AND (a2,a1))) /\
      (!a1 a2 b. AUTOMATON_EQUIV a1 a2 ==> AUTOMATON_EQUIV (A_AND (a1,b)) (A_AND (a2,b))) /\
      (!a1 a2. (!v. A_SEM v (A_EQUIV(a1, a2))) <=> AUTOMATON_EQUIV a1 a2) /\
      (!a1 a2. AUTOMATON_EQUIV (A_OR (a1,a2)) (A_OR (a2,a1))) /\
      (!a1 a2 b. AUTOMATON_EQUIV a1 a2 ==> AUTOMATON_EQUIV (A_OR (a1,b)) (A_OR (a2,b))) /\
      (!a1 a2 b. AUTOMATON_EQUIV a1 a2 ==> AUTOMATON_EQUIV (A_IMPL (a1,b)) (A_IMPL (a2,b))) /\
      (!a1 a2 b. AUTOMATON_EQUIV a1 a2 ==> AUTOMATON_EQUIV (A_IMPL (b,a1)) (A_IMPL (b,a2))) /\
      (!A a1 a2. AUTOMATON_EQUIV a1 a2 ==> AUTOMATON_EQUIV (A_NDET(A, a1)) (A_NDET(A, a2))) /\
      (!A a1 a2. AUTOMATON_EQUIV a1 a2 ==> AUTOMATON_EQUIV (A_UNIV(A, a1)) (A_UNIV(A, a2))) /\
      (!a1 a2. AUTOMATON_EQUIV a1 a2 <=> AUTOMATON_EQUIV a2 a1) /\
      (!a1. AUTOMATON_EQUIV a1 a1) /\
      (!a1 a2 a3. AUTOMATON_EQUIV a1 a2 /\ AUTOMATON_EQUIV a2 a3 ==> AUTOMATON_EQUIV a1 a3)
Proof
    REWRITE_TAC [AUTOMATON_EQUIV_def, A_SEM_THM]
 >> rpt STRIP_TAC
 >> PROVE_TAC []
QED

Theorem A_BIGAND___A_USED_INPUT_VARS :
    !C1 C2. A_USED_INPUT_VARS (A_BIGAND (APPEND C1 C2)) =
            A_USED_INPUT_VARS (A_AND (A_BIGAND C1, A_BIGAND C2))
Proof
    REWRITE_TAC [A_USED_INPUT_VARS_def]
 >> Induct_on `C1`
 >> SIMP_TAC arith_ss [A_BIGAND_def, APPEND, A_USED_INPUT_VARS_def, UNION_EMPTY]
 >> PROVE_TAC [UNION_ASSOC]
QED

Theorem A_BIGAND___A_USED_STATE_VARS :
    !C1 C2. A_USED_STATE_VARS (A_BIGAND (APPEND C1 C2)) =
            A_USED_STATE_VARS (A_AND (A_BIGAND C1, A_BIGAND C2))
Proof
    REWRITE_TAC [A_USED_STATE_VARS_def]
 >> Induct_on `C1`
 >> SIMP_TAC arith_ss [A_BIGAND_def, APPEND, A_USED_STATE_VARS_def, UNION_EMPTY]
 >> PROVE_TAC [UNION_ASSOC]
QED

Theorem A_BIGAND___A_SEM :
    !C1 C2 v. A_SEM v (A_BIGAND (APPEND C1 C2)) <=>
              A_SEM v (A_BIGAND C1) /\ A_SEM v (A_BIGAND C2)
Proof
    Induct_on `C1`
 >> SIMP_TAC arith_ss [A_BIGAND_def, APPEND, A_SEM_def, UNION_EMPTY]
 >> PROVE_TAC []
QED

Theorem A_BIGAND_SEM :
    !w C. A_SEM w (A_BIGAND C) <=> !e. MEM e C ==> A_SEM w e
Proof
    Induct_on `C`
 >> ASM_SIMP_TAC list_ss [A_BIGAND_def, A_SEM_def]
 >> PROVE_TAC []
QED

Theorem ACCEPT_BIGAND_SEM :
    !t w C. ACCEPT_COND_SEM_TIME t w (ACCEPT_BIGAND C) <=>
            !e. MEM e C ==> ACCEPT_COND_SEM_TIME t w e
Proof
    Induct_on `C`
 >> ASM_SIMP_TAC list_ss [ACCEPT_BIGAND_def, ACCEPT_COND_SEM_TIME_def]
 >> METIS_TAC []
QED

Theorem ACCEPT_BIGAND___VAR_RENAMING :
    !f C. ACCEPT_VAR_RENAMING f (ACCEPT_BIGAND C) =
          ACCEPT_BIGAND (MAP (ACCEPT_VAR_RENAMING f) C)
Proof
    Induct_on `C`
 >> ASM_SIMP_TAC list_ss [ACCEPT_BIGAND_def, ACCEPT_VAR_RENAMING_def]
QED

Theorem A_BIGAND___AUTOMATON_EQUIV :
    !C1 C2. AUTOMATON_EQUIV (A_BIGAND (APPEND C1 C2))
                            (A_AND(A_BIGAND C1, A_BIGAND C2))
Proof
    REWRITE_TAC [AUTOMATON_EQUIV_def, A_SEM_def, A_BIGAND___A_SEM]
QED

Theorem A_BIGAND___STATE_VARDISJOINT_AUTOMATON_FORMULA :
    !C1 C2. STATE_VARDISJOINT_AUTOMATON_FORMULA (A_BIGAND (APPEND C1 C2)) =
            STATE_VARDISJOINT_AUTOMATON_FORMULA (A_AND (A_BIGAND C1,  A_BIGAND C2))
Proof
    REWRITE_TAC [STATE_VARDISJOINT_AUTOMATON_FORMULA_def]
 >> Induct_on `C1`
 >- SIMP_TAC arith_ss [A_BIGAND_def,
                       APPEND,
                       DISJOINT_EMPTY,
                       STATE_VARDISJOINT_AUTOMATON_FORMULA_def,
                       A_USED_STATE_VARS_def]
 >> SIMP_TAC arith_ss [A_BIGAND_def,
                       APPEND,
                       DISJOINT_EMPTY,
                       STATE_VARDISJOINT_AUTOMATON_FORMULA_def,
                       A_USED_STATE_VARS_def,
                       DISJOINT_UNION_BOTH,
                       A_BIGAND___A_USED_STATE_VARS]
 >> rpt STRIP_TAC
 >> EQ_TAC >> rpt STRIP_TAC
 >> PROVE_TAC [DISJOINT_SYM]
QED

Theorem A_BIGAND___VARDISJOINT_AUTOMATON_FORMULA :
    !C1 C2. VARDISJOINT_AUTOMATON_FORMULA (A_BIGAND (APPEND C1 C2)) =
            VARDISJOINT_AUTOMATON_FORMULA (A_AND (A_BIGAND C1, A_BIGAND C2))
Proof
    REWRITE_TAC [VARDISJOINT_AUTOMATON_FORMULA_def,
                 A_BIGAND___A_USED_STATE_VARS,
                 A_BIGAND___A_USED_INPUT_VARS,
                 A_BIGAND___STATE_VARDISJOINT_AUTOMATON_FORMULA]
QED

Theorem A_BIGAND_EMPTY :
    !C. (A_BIGAND C = A_TRUE) <=> (C = [])
Proof
    Cases_on `C` >> EVAL_TAC
QED

Theorem A_BIGAND_11 :
    !C D. (A_BIGAND C = A_BIGAND D) <=> (C = D)
Proof
    Induct_on `C`
 >> Cases_on `D`
 >> EVAL_TAC >> PROVE_TAC []
QED

(* for any input trace i there exists a run (i,w) with property C *)
val EXISTS_RUN_WITH_PROPERTIES_def = Define
   `EXISTS_RUN_WITH_PROPERTIES A C =
      !i. ?w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w /\
              A_SEM (INPUT_RUN_PATH_UNION A i w) (A_BIGAND C)`;

val UNIQUE_RUN_WITH_PROPERTIES_def = Define
   `UNIQUE_RUN_WITH_PROPERTIES A C =
      !i. ?!w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w /\
               A_SEM (INPUT_RUN_PATH_UNION A i w) (A_BIGAND C)`;

Theorem UNIQUE_RUN_WITH_PROPERTIES___IMPLIES_EXISTENCE :
    !A C. UNIQUE_RUN_WITH_PROPERTIES A C ==> EXISTS_RUN_WITH_PROPERTIES A C
Proof
    REWRITE_TAC [UNIQUE_RUN_WITH_PROPERTIES_def, EXISTS_RUN_WITH_PROPERTIES_def]
 >> METIS_TAC []
QED

Theorem A_NDET_CONSTRAINED_11 :
    !A B C D p q.
      (A_NDET_CONSTRAINED(A, C, p) = A_NDET_CONSTRAINED(B, D, q)) <=>
      (A = B) /\ (C = D) /\ (p = q)
Proof
    EVAL_TAC
 >> Induct_on `C`
 >> Cases_on `D` >> EVAL_TAC >> PROVE_TAC []
QED

(******************************************************************************)
(*                                                                            *)
(*    Automaton classes (hierarchy) [2,3]                                     *)
(*                                                                            *)
(******************************************************************************)

val ACCEPT_COND_PROP_def = Define
   `ACCEPT_COND_PROP b = ACCEPT_COND (ACCEPT_PROP b)`;

Theorem ACCEPT_COND_PROP_11 :
    !p1 p2. (ACCEPT_COND_PROP p1 = ACCEPT_COND_PROP p2) <=> (p1 = p2)
Proof
    EVAL_TAC >> PROVE_TAC []
QED

(* Buechi acceptance condition (infinitely often) [4] *)
val ACCEPT_COND_GF_def = Define
   `ACCEPT_COND_GF b = ACCEPT_COND (ACCEPT_G(ACCEPT_F (ACCEPT_PROP b)))`;

val ACCEPT_COND_FG_def = Define
   `ACCEPT_COND_FG b = ACCEPT_COND (ACCEPT_F(ACCEPT_G (ACCEPT_PROP b)))`;

val ACCEPT_COND_F_def = Define
   `ACCEPT_COND_F b = ACCEPT_COND (ACCEPT_F (ACCEPT_PROP b))`;

val ACCEPT_COND_G_def = Define
   `ACCEPT_COND_G b = ACCEPT_COND (ACCEPT_G (ACCEPT_PROP b))`;

val IS_EX_AUTOMATON_def = Define
   `IS_EX_AUTOMATON af = ?A f. af = A_NDET(A, f)`;

val IS_ALL_AUTOMATON_def = Define
   `IS_ALL_AUTOMATON af = ?A f. af = A_UNIV(A, f)`;

(* when automaton formula is an automaton *)
val IS_AUTOMATON_def = Define
   `IS_AUTOMATON af = (IS_EX_AUTOMATON af \/ IS_ALL_AUTOMATON af)`;

val IS_DET_EX_AUTOMATON_def = Define
   `IS_DET_EX_AUTOMATON af = ?A f. ((af = A_NDET(A, f)) /\ IS_DET_SYMBOLIC_SEMI_AUTOMATON A)`;

val IS_DET_ALL_AUTOMATON_def = Define
   `IS_DET_ALL_AUTOMATON af = ?A f. ((af = A_UNIV(A, f)) /\ IS_DET_SYMBOLIC_SEMI_AUTOMATON A)`;

val IS_DET_AUTOMATON_def = Define
   `IS_DET_AUTOMATON af = (IS_DET_EX_AUTOMATON af \/ IS_DET_ALL_AUTOMATON af)`;

val IS_NDET_GF_AUTOMATON_def = Define
   `IS_NDET_GF_AUTOMATON af = ?A b. ((af = A_NDET(A, ACCEPT_COND_GF b)))`;

val IS_NDET_FG_AUTOMATON_def = Define
   `IS_NDET_FG_AUTOMATON af = ?A b. ((af = A_NDET(A, ACCEPT_COND_FG b)))`;

val IS_NDET_F_AUTOMATON_def = Define
   `IS_NDET_F_AUTOMATON af = ?A b. ((af = A_NDET(A, ACCEPT_COND_F b)))`;

val IS_NDET_G_AUTOMATON_def = Define
   `IS_NDET_G_AUTOMATON af = ?A b. ((af = A_NDET(A, ACCEPT_COND_G b)))`;

val IS_DET_EX_GF_AUTOMATON_def = Define
   `IS_DET_EX_GF_AUTOMATON af =
      ?A b. (af = A_NDET (A,ACCEPT_COND_GF b)) /\ IS_DET_SYMBOLIC_SEMI_AUTOMATON A`;

val IS_DET_EX_FG_AUTOMATON_def = Define
   `IS_DET_EX_FG_AUTOMATON af =
      ?A b. (af = A_NDET (A,ACCEPT_COND_FG b)) /\ IS_DET_SYMBOLIC_SEMI_AUTOMATON A`;

val IS_DET_EX_G_AUTOMATON_def = Define
   `IS_DET_EX_G_AUTOMATON af =
      ?A b. (af = A_NDET (A,ACCEPT_COND_G b)) /\ IS_DET_SYMBOLIC_SEMI_AUTOMATON A`;

val IS_DET_EX_F_AUTOMATON_def = Define
   `IS_DET_EX_F_AUTOMATON af =
      ?A b. (af = A_NDET (A,ACCEPT_COND_F b)) /\ IS_DET_SYMBOLIC_SEMI_AUTOMATON A`;

val IS_UNIV_GF_AUTOMATON_def = Define
   `IS_UNIV_GF_AUTOMATON af = ?A b. ((af = A_UNIV(A, ACCEPT_COND_GF b)))`;

val IS_UNIV_FG_AUTOMATON_def = Define
   `IS_UNIV_FG_AUTOMATON af = ?A b. ((af = A_UNIV(A, ACCEPT_COND_FG b)))`;

val IS_UNIV_F_AUTOMATON_def = Define
   `IS_UNIV_F_AUTOMATON af = ?A b. ((af = A_UNIV(A, ACCEPT_COND_F b)))`;

val IS_UNIV_G_AUTOMATON_def = Define
   `IS_UNIV_G_AUTOMATON af = ?A b. ((af = A_UNIV(A, ACCEPT_COND_G b)))`;

val A_NDET_GEN_GF_def = Define
   `A_NDET_GEN_GF(A, C) = A_NDET(A, A_BIGAND (MAP (\p. ACCEPT_COND_GF p) C))`;

val A_IS_EMPTY_def = Define
   `A_IS_EMPTY A = ~(?i. A_SEM i A)`;

val A_IS_CONTRADICTION_def = Define
   `A_IS_CONTRADICTION A = A_IS_EMPTY A`;

val A_IS_TAUTOLOGY_def = Define
   `A_IS_TAUTOLOGY A = (!i. A_SEM i A)`;

Theorem A_TAUTOLOGY_CONTRADICTION_DUAL :
    (!A. A_IS_CONTRADICTION (A_NOT A) = A_IS_TAUTOLOGY A) /\
    (!A. A_IS_TAUTOLOGY (A_NOT A) = A_IS_CONTRADICTION A)
Proof
    SIMP_TAC std_ss [A_IS_TAUTOLOGY_def, A_IS_CONTRADICTION_def, A_SEM_def,
                     A_IS_EMPTY_def]
QED

Theorem A_TAUTOLOGY_CONTRADICTION___TO___EQUIVALENT :
    (!A. A_IS_CONTRADICTION A = AUTOMATON_EQUIV A A_FALSE) /\
    (!A. A_IS_TAUTOLOGY A = AUTOMATON_EQUIV A A_TRUE)
Proof
    SIMP_TAC std_ss [A_IS_TAUTOLOGY_def, A_IS_CONTRADICTION_def, A_IS_EMPTY_def,
                     AUTOMATON_EQUIV_def, A_SEM_THM]
QED

(*****************************************************************************
 * Variable renamings
 *****************************************************************************)

Theorem FINITE___ACCEPT_COND_USED_VARS :
    !a. FINITE (ACCEPT_COND_USED_VARS a)
Proof
  INDUCT_THEN acceptance_condition_induct ASSUME_TAC THENL [
      REWRITE_TAC[ACCEPT_COND_USED_VARS_def, FINITE___P_USED_VARS],
      REWRITE_TAC[ACCEPT_COND_USED_VARS_def, FINITE_EMPTY],
      ASM_REWRITE_TAC[ACCEPT_COND_USED_VARS_def],
      ASM_REWRITE_TAC[ACCEPT_COND_USED_VARS_def, FINITE_UNION],
      ASM_REWRITE_TAC[ACCEPT_COND_USED_VARS_def]
  ]
QED

Theorem ACCEPT_VAR_RENAMING___USED_VARS :
    !a f. ACCEPT_COND_USED_VARS (ACCEPT_VAR_RENAMING f a) =
          IMAGE f (ACCEPT_COND_USED_VARS a)
Proof
   INDUCT_THEN acceptance_condition_induct ASSUME_TAC THENL [
      REWRITE_TAC [ACCEPT_COND_USED_VARS_def, ACCEPT_VAR_RENAMING_def, P_VAR_RENAMING___USED_VARS],
      REWRITE_TAC [ACCEPT_COND_USED_VARS_def, ACCEPT_VAR_RENAMING_def, IMAGE_EMPTY],
      ASM_REWRITE_TAC [ACCEPT_COND_USED_VARS_def, ACCEPT_VAR_RENAMING_def],
      ASM_REWRITE_TAC [ACCEPT_COND_USED_VARS_def, ACCEPT_VAR_RENAMING_def, IMAGE_UNION],
      ASM_REWRITE_TAC[ACCEPT_COND_USED_VARS_def, ACCEPT_VAR_RENAMING_def]
   ]
QED

Theorem FINITE___A_USED_INPUT_VARS :
    !a. FINITE (A_USED_INPUT_VARS a)
Proof
    INDUCT_THEN automaton_formula_induct ASSUME_TAC
 >| [ REWRITE_TAC [A_USED_INPUT_VARS_def, FINITE___ACCEPT_COND_USED_VARS],
      REWRITE_TAC [A_USED_INPUT_VARS_def, FINITE_UNION, FINITE___SEMI_AUTOMATON_USED_INPUT_VARS] \\
      METIS_TAC [FINITE_DIFF],
      ASM_REWRITE_TAC [A_USED_INPUT_VARS_def],
      ASM_REWRITE_TAC [A_USED_INPUT_VARS_def, FINITE_UNION],
      ASM_REWRITE_TAC [A_USED_INPUT_VARS_def, FINITE_EMPTY] ]
QED

Theorem A_VAR_RENAMING___USED_STATE_VARS :
    !a f. A_USED_STATE_VARS (A_VAR_RENAMING f a) = IMAGE f (A_USED_STATE_VARS a)
Proof
    INDUCT_THEN automaton_formula_induct ASSUME_TAC
 >| [ REWRITE_TAC [A_USED_STATE_VARS_def, A_VAR_RENAMING_def, IMAGE_EMPTY],
      Cases_on `p_1` \\
      ASM_REWRITE_TAC [A_USED_STATE_VARS_def,
                       A_VAR_RENAMING_def,
                       SEMI_AUTOMATON_VAR_RENAMING_def,
                       symbolic_semi_automaton_REWRITES,
                       IMAGE_UNION],
      ASM_REWRITE_TAC [A_USED_STATE_VARS_def, A_VAR_RENAMING_def],
      ASM_REWRITE_TAC [A_USED_STATE_VARS_def, A_VAR_RENAMING_def, IMAGE_UNION],
      REWRITE_TAC [A_USED_STATE_VARS_def, A_VAR_RENAMING_def, IMAGE_EMPTY] ]
QED

Theorem A_VAR_RENAMING___USED_INPUT_VARS :
    !a f. INJ f (A_USED_VARS a) UNIV ==>
         (A_USED_INPUT_VARS (A_VAR_RENAMING f a) = IMAGE f (A_USED_INPUT_VARS a))
Proof
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
      rpt STRIP_TAC THEN
      Q.ABBREV_TAC `INJ_SET = (P_USED_VARS p UNION XP_USED_VARS x DIFF f UNION
             (A_USED_INPUT_VARS a DIFF f) UNION
             (f UNION A_USED_STATE_VARS a))` THEN

      `((P_USED_VARS p UNION XP_USED_VARS x UNION f) SUBSET INJ_SET) /\
       ((XP_USED_VARS x UNION f) SUBSET INJ_SET) /\
       ((A_USED_INPUT_VARS a UNION f) SUBSET INJ_SET) /\
       ((A_USED_VARS a SUBSET INJ_SET))` by (
         Q.UNABBREV_TAC `INJ_SET` THEN
         ASM_SIMP_TAC std_ss [UNION_DEF, SUBSET_DEF, GSPECIFICATION, DIFF_DEF, A_USED_VARS_def] THEN
         METIS_TAC []) THEN

      METIS_TAC[INJ_SUBSET_DOMAIN, IMAGE_DIFF, IMAGE_UNION],

      FULL_SIMP_TAC std_ss [A_USED_VARS_def, A_USED_STATE_VARS_def,
                            A_USED_INPUT_VARS_def, A_VAR_RENAMING_def],

      FULL_SIMP_TAC std_ss [A_USED_VARS_def, A_USED_STATE_VARS_def,
                            A_USED_INPUT_VARS_def, A_VAR_RENAMING_def,  IMAGE_UNION] THEN
      rpt STRIP_TAC THEN
      `(A_USED_INPUT_VARS a UNION A_USED_STATE_VARS a) SUBSET
       (A_USED_INPUT_VARS a UNION A_USED_INPUT_VARS a' UNION
         (A_USED_STATE_VARS a UNION A_USED_STATE_VARS a'))` by
         METIS_TAC [SUBSET_UNION, UNION_COMM, UNION_ASSOC] THEN

      `(A_USED_INPUT_VARS a' UNION A_USED_STATE_VARS a') SUBSET
       (A_USED_INPUT_VARS a UNION A_USED_INPUT_VARS a' UNION
         (A_USED_STATE_VARS a UNION A_USED_STATE_VARS a'))` by
         METIS_TAC [SUBSET_UNION, UNION_COMM, UNION_ASSOC] THEN
      METIS_TAC [INJ_SUBSET_DOMAIN],

      REWRITE_TAC [A_USED_INPUT_VARS_def, A_VAR_RENAMING_def,
                   ACCEPT_VAR_RENAMING___USED_VARS, IMAGE_EMPTY]
   ]
QED

Theorem A_VAR_RENAMING___USED_VARS :
    !a f. INJ f (A_USED_VARS a) UNIV ==>
         (A_USED_VARS (A_VAR_RENAMING f a) = IMAGE f (A_USED_VARS a))
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [A_USED_VARS_def, IMAGE_UNION, A_VAR_RENAMING___USED_STATE_VARS]
 >> METIS_TAC [A_VAR_RENAMING___USED_INPUT_VARS]
QED

Theorem A_VAR_RENAMING___A_BIGAND :
    !f C. A_VAR_RENAMING f (A_BIGAND C) = A_BIGAND (MAP (A_VAR_RENAMING f) C)
Proof
    Induct_on `C`
 >| [ REWRITE_TAC [MAP, A_BIGAND_def, A_VAR_RENAMING_def],
      ASM_REWRITE_TAC [MAP, A_BIGAND_def, A_VAR_RENAMING_def] ]
QED

Theorem ACCEPT_COND_USED_VARS_INTER_SUBSET_THM :
    !a S t v. (ACCEPT_COND_USED_VARS a) SUBSET S ==>
              (ACCEPT_COND_SEM_TIME t v a = ACCEPT_COND_SEM_TIME t (PATH_RESTRICT v S) a)
Proof
    INDUCT_THEN acceptance_condition_induct ASSUME_TAC
 >| [ SIMP_TAC std_ss [ACCEPT_COND_USED_VARS_def, ACCEPT_COND_SEM_TIME_def,
                       PATH_RESTRICT_def, PATH_MAP_def] \\
      PROVE_TAC [P_USED_VARS_INTER_SUBSET_THM],

      REWRITE_TAC [ACCEPT_COND_SEM_TIME_def],

      REWRITE_TAC [ACCEPT_COND_SEM_TIME_def, ACCEPT_COND_USED_VARS_def] \\
      PROVE_TAC [],

      REWRITE_TAC [ACCEPT_COND_SEM_TIME_def, ACCEPT_COND_USED_VARS_def, UNION_SUBSET] \\
      PROVE_TAC [],

      REWRITE_TAC [ACCEPT_COND_SEM_TIME_def, ACCEPT_COND_USED_VARS_def] \\
      PROVE_TAC [] ]
QED

Theorem ACCEPT_COND_USED_VARS_INTER_THM :
    !a t v. ACCEPT_COND_SEM_TIME t v a =
            ACCEPT_COND_SEM_TIME t (PATH_RESTRICT v (ACCEPT_COND_USED_VARS a)) a
Proof
    METIS_TAC [ACCEPT_COND_USED_VARS_INTER_SUBSET_THM, SUBSET_REFL]
QED

Theorem A_USED_INPUT_VARS_INTER_SUBSET_THM :
    !a S. (A_USED_INPUT_VARS a) SUBSET S ==>
          !i. A_SEM i a = A_SEM (PATH_RESTRICT i S) a
Proof
    INDUCT_THEN automaton_formula_induct STRIP_ASSUME_TAC
 >| [ FULL_SIMP_TAC std_ss [A_SEM_def, A_USED_INPUT_VARS_def, ACCEPT_COND_SEM_def] \\
      PROVE_TAC [ACCEPT_COND_USED_VARS_INTER_SUBSET_THM],

      FULL_SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                            A_SEM_def, IS_TRANSITION_def, INPUT_RUN_PATH_UNION_def,
                            A_USED_INPUT_VARS_def, UNION_SUBSET, DIFF_SUBSET_ELIM,
                            SEMI_AUTOMATON_USED_INPUT_VARS_def] \\
      rpt STRIP_TAC \\
      EXISTS_EQ_STRIP_TAC \\
      BINOP_TAC >|
      [ SUBGOAL_TAC `!n. ((INPUT_RUN_STATE_UNION p_1 (i n) (w n)) INTER (S UNION p_1.S)) =
            ((INPUT_RUN_STATE_UNION p_1 (PATH_RESTRICT i S n) (w n)) INTER (S UNION p_1.S))`
        >- (SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, INPUT_RUN_STATE_UNION_def,
                             IN_DIFF, PATH_RESTRICT_def, PATH_MAP_def] \\
            rpt STRIP_TAC >> rpt BOOL_EQ_STRIP_TAC \\
            FULL_SIMP_TAC std_ss []) \\
        PROVE_TAC [XP_USED_VARS_INTER_SUBSET_BOTH_THM, P_USED_VARS_INTER_SUBSET_THM],

        REMAINS_TAC `(PATH_RESTRICT (\n. INPUT_RUN_STATE_UNION p_1 (i n) (w n)) (S UNION p_1.S)) =
                     (PATH_RESTRICT (\n. INPUT_RUN_STATE_UNION p_1
                                           (PATH_RESTRICT i S n) (w n)) (S UNION p_1.S))`
        >- (METIS_TAC []) \\
        SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, INPUT_RUN_STATE_UNION_def] \\
        ONCE_REWRITE_TAC [FUN_EQ_THM] \\
        SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF] \\
        rpt STRIP_TAC >> rpt BOOL_EQ_STRIP_TAC \\
        FULL_SIMP_TAC std_ss [] ],

      REWRITE_TAC [A_USED_INPUT_VARS_def,  A_SEM_def] \\
      PROVE_TAC [],

      REWRITE_TAC [UNION_SUBSET, A_USED_INPUT_VARS_def, A_SEM_def] \\
      PROVE_TAC [],

      REWRITE_TAC [A_SEM_def] ]
QED

Theorem A_USED_INPUT_VARS_INTER_THM :
    !a i. A_SEM i a = A_SEM (PATH_RESTRICT i (A_USED_INPUT_VARS a)) a
Proof
    METIS_TAC [A_USED_INPUT_VARS_INTER_SUBSET_THM, SUBSET_REFL]
QED

Theorem A_USED_INPUT_VARS_DIFF_DISJOINT_THM :
    !a S. DISJOINT (A_USED_INPUT_VARS a) S ==> !i. A_SEM i a = A_SEM (PATH_DIFF i S) a
Proof
    rpt STRIP_TAC
 >> `A_USED_INPUT_VARS a SUBSET COMPL S` by PROVE_TAC [SUBSET_COMPL_DISJOINT]
 >> PROVE_TAC [A_USED_INPUT_VARS_INTER_SUBSET_THM, PATH_DIFF_PATH_RESTRICT]
QED

Theorem A_AND___A_NDET :
    !A1 f1 A2 f2. A_USED_STATE_VARS_COMPATIBLE (A_NDET(A1, f1)) (A_NDET(A2, f2)) ==>
                  AUTOMATON_EQUIV (A_AND(A_NDET(A1, f1), A_NDET(A2, f2)))
                                  (A_NDET((PRODUCT_SEMI_AUTOMATON A1 A2), A_AND(f1,f2)))
Proof
    SIMP_TAC std_ss [A_USED_STATE_VARS_COMPATIBLE_def,
                     A_USED_INPUT_VARS_def, A_USED_STATE_VARS_def,
                     STATE_VARDISJOINT_AUTOMATON_FORMULA_def,
                     DISJOINT_UNION_BOTH, AUTOMATON_EQUIV_def,
                     DISJOINT_DIFF_ELIM_SYM, A_SEM_def]
 >> rpt STRIP_TAC
 >> EQ_TAC >> rpt STRIP_TAC
 >| [ EXISTS_TAC ``PATH_UNION w w'`` \\
      rpt STRIP_TAC >|
      [ METIS_TAC [PRODUCT_SEMI_AUTOMATON_RUN, DISJOINT_SYM],

        SUBGOAL_TAC `DISJOINT (A_USED_INPUT_VARS f1) A2.S /\
                     (PATH_DIFF (INPUT_RUN_PATH_UNION
                                   (PRODUCT_SEMI_AUTOMATON A1 A2) v (PATH_UNION w w')) A2.S =
                      PATH_DIFF (INPUT_RUN_PATH_UNION A1 v w) A2.S)`
        >- (ONCE_REWRITE_TAC [FUN_EQ_THM] \\
            SIMP_ALL_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
                                 PATH_DIFF_def, IN_UNION, IN_DIFF,
                                 INPUT_RUN_PATH_UNION_def,
                                 INPUT_RUN_STATE_UNION_def,
                                 PATH_UNION_def, EXTENSION,
                                 PRODUCT_SEMI_AUTOMATON_REWRITES,
                                 IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, PATH_SUBSET_def] \\
           rpt STRIP_TAC >> rpt BOOL_EQ_STRIP_TAC >> PROVE_TAC []) \\
        PROVE_TAC [A_USED_INPUT_VARS_DIFF_DISJOINT_THM],

        SUBGOAL_TAC `DISJOINT (A_USED_INPUT_VARS f2) A1.S /\
                     (PATH_DIFF (INPUT_RUN_PATH_UNION
                                   (PRODUCT_SEMI_AUTOMATON A1 A2) v (PATH_UNION w w')) A1.S =
                      PATH_DIFF (INPUT_RUN_PATH_UNION A2 v w') A1.S)`
        >- (ONCE_REWRITE_TAC [FUN_EQ_THM] \\
            SIMP_ALL_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
                                 PATH_DIFF_def, IN_UNION, IN_DIFF,
                                 INPUT_RUN_PATH_UNION_def,
                                 INPUT_RUN_STATE_UNION_def,
                                 PATH_UNION_def, EXTENSION, PRODUCT_SEMI_AUTOMATON_REWRITES,
                                 IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, PATH_SUBSET_def] \\
            rpt STRIP_TAC >> rpt BOOL_EQ_STRIP_TAC >> PROVE_TAC []) \\
        PROVE_TAC [A_USED_INPUT_VARS_DIFF_DISJOINT_THM] ],

      EXISTS_TAC ``(PATH_RESTRICT w A1.S)`` \\
      rpt STRIP_TAC >|
      [ PROVE_TAC [PRODUCT_SEMI_AUTOMATON_RUN2___FIRST, DISJOINT_SYM],

        SUBGOAL_TAC `DISJOINT (A_USED_INPUT_VARS f1) A2.S /\
                     (PATH_DIFF (INPUT_RUN_PATH_UNION A1 v (PATH_RESTRICT w A1.S)) A2.S =
                      PATH_DIFF (INPUT_RUN_PATH_UNION (PRODUCT_SEMI_AUTOMATON A1 A2) v w) A2.S)`
        >- (ONCE_REWRITE_TAC [FUN_EQ_THM] \\
            SIMP_ALL_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
                                 PATH_DIFF_def, IN_UNION, IN_DIFF,
                                 INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
                                 PATH_UNION_def, EXTENSION, PRODUCT_SEMI_AUTOMATON_REWRITES,
                                 IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                                 PATH_SUBSET_def, PATH_RESTRICT_def, PATH_MAP_def, IN_INTER] \\
            rpt STRIP_TAC >> rpt BOOL_EQ_STRIP_TAC >> PROVE_TAC []) \\
        PROVE_TAC [A_USED_INPUT_VARS_DIFF_DISJOINT_THM] ],

      EXISTS_TAC ``(PATH_RESTRICT w A2.S)`` \\
      rpt STRIP_TAC >|
      [ PROVE_TAC [PRODUCT_SEMI_AUTOMATON_RUN2___SECOND, DISJOINT_SYM],

        SUBGOAL_TAC `DISJOINT (A_USED_INPUT_VARS f2) A1.S /\
                     (PATH_DIFF (INPUT_RUN_PATH_UNION A2 v (PATH_RESTRICT w A2.S)) A1.S =
                      PATH_DIFF (INPUT_RUN_PATH_UNION (PRODUCT_SEMI_AUTOMATON A1 A2) v w) A1.S)`
        >- (ONCE_REWRITE_TAC [FUN_EQ_THM] \\
            SIMP_ALL_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
                                 PATH_DIFF_def, IN_UNION, IN_DIFF,
                                 INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
                                 PATH_UNION_def, EXTENSION, PRODUCT_SEMI_AUTOMATON_REWRITES,
                                 IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                                 PATH_SUBSET_def, PATH_RESTRICT_def, PATH_MAP_def, IN_INTER] \\
           rpt STRIP_TAC >> rpt BOOL_EQ_STRIP_TAC >> PROVE_TAC []) \\
        PROVE_TAC [A_USED_INPUT_VARS_DIFF_DISJOINT_THM] ] ]
QED

Theorem PRODUCT_SEMI_AUTOMATON___EXISTS_RUN_WITH_PROPERTIES :
    !A1 C1 A2 C2.
        A_USED_STATE_VARS_COMPATIBLE (A_NDET(A1, A_BIGAND C1)) (A_NDET(A2, A_BIGAND C2)) ==>
        EXISTS_RUN_WITH_PROPERTIES A1 C1 /\ EXISTS_RUN_WITH_PROPERTIES A2 C2 ==>
        EXISTS_RUN_WITH_PROPERTIES (PRODUCT_SEMI_AUTOMATON A1 A2) (C1++C2)
Proof
    rpt STRIP_TAC
 >> SIMP_ALL_TAC std_ss [EXISTS_RUN_WITH_PROPERTIES_def, EXISTS_UNIQUE_DEF,
                         A_BIGAND___A_SEM, A_SEM_def]
 >> SUBGOAL_TAC `AUTOMATON_EQUIV (A_AND (A_NDET (A1, A_BIGAND C1),A_NDET (A2, A_BIGAND C2)))
                                 (A_NDET (PRODUCT_SEMI_AUTOMATON A1 A2,A_AND (A_BIGAND C1,A_BIGAND C2)))`
 >- PROVE_TAC[A_AND___A_NDET]
 >> SIMP_ALL_TAC std_ss [A_BIGAND_def, A_BIGAND___A_SEM, AUTOMATON_EQUIV_def, A_SEM_def]
 >> PROVE_TAC []
QED

Theorem PRODUCT_SEMI_AUTOMATON___UNIQUE_RUN_WITH_PROPERTIES :
    !A1 C1 A2 C2.
        A_USED_STATE_VARS_COMPATIBLE (A_NDET(A1, A_BIGAND C1)) (A_NDET(A2, A_BIGAND C2)) ==>
        UNIQUE_RUN_WITH_PROPERTIES A1 C1 /\ UNIQUE_RUN_WITH_PROPERTIES A2 C2 ==>
        UNIQUE_RUN_WITH_PROPERTIES (PRODUCT_SEMI_AUTOMATON A1 A2) (C1++C2)
Proof
    rpt STRIP_TAC
 >> SIMP_ALL_TAC std_ss [UNIQUE_RUN_WITH_PROPERTIES_def, EXISTS_UNIQUE_DEF,
                         A_BIGAND___A_SEM, A_SEM_def]
 >> rpt STRIP_TAC
 >| [ `AUTOMATON_EQUIV (A_AND (A_NDET (A1, A_BIGAND C1),A_NDET (A2, A_BIGAND C2)))
                       (A_NDET (PRODUCT_SEMI_AUTOMATON A1 A2,A_AND (A_BIGAND C1,A_BIGAND C2)))`
         by PROVE_TAC [A_AND___A_NDET] \\
      SIMP_ALL_TAC std_ss [A_BIGAND_def, A_BIGAND___A_SEM, AUTOMATON_EQUIV_def, A_SEM_def] \\
      PROVE_TAC [],

      REMAINS_TAC `(PATH_RESTRICT x A1.S = PATH_RESTRICT y A1.S) /\
                   (PATH_RESTRICT x A2.S = PATH_RESTRICT y A2.S)`
      >- (`(x = PATH_UNION (PATH_RESTRICT x A1.S) (PATH_RESTRICT x A2.S)) /\
           (y = PATH_UNION (PATH_RESTRICT y A1.S) (PATH_RESTRICT y A2.S))`
              by METIS_TAC [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                            PATH_PARTITION, PRODUCT_SEMI_AUTOMATON_REWRITES] \\
          PROVE_TAC []) \\
      REMAINS_TAC `(IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A1 i (PATH_RESTRICT x A1.S) /\
                    IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A2 i (PATH_RESTRICT x A2.S) /\
                    IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A1 i (PATH_RESTRICT y A1.S) /\
                    IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A2 i (PATH_RESTRICT y A2.S)) /\
                   (A_SEM (INPUT_RUN_PATH_UNION A1 i (PATH_RESTRICT x A1.S)) (A_BIGAND C1) /\
                    A_SEM (INPUT_RUN_PATH_UNION A1 i (PATH_RESTRICT y A1.S)) (A_BIGAND C1) /\
                    A_SEM (INPUT_RUN_PATH_UNION A2 i (PATH_RESTRICT x A2.S)) (A_BIGAND C2) /\
                    A_SEM (INPUT_RUN_PATH_UNION A2 i (PATH_RESTRICT y A2.S)) (A_BIGAND C2))`
      >- METIS_TAC [] \\
      SUBGOAL_TAC `DISJOINT A1.S A2.S /\
                   DISJOINT A2.S (SEMI_AUTOMATON_USED_INPUT_VARS A1) /\
                   DISJOINT A1.S (SEMI_AUTOMATON_USED_INPUT_VARS A2) /\
                   DISJOINT (A_USED_INPUT_VARS (A_BIGAND C2)) A1.S /\
                   DISJOINT (A_USED_INPUT_VARS (A_BIGAND C1)) A2.S`
      >- (SIMP_ALL_TAC std_ss [A_USED_STATE_VARS_COMPATIBLE_def, A_USED_STATE_VARS_def,
                               A_USED_INPUT_VARS_def, DISJOINT_UNION_BOTH] \\
          PROVE_TAC [DISJOINT_SYM, DISJOINT_DIFF_ELIM_SYM]) \\
      SUBGOAL_TAC `(PATH_DIFF (INPUT_RUN_PATH_UNION (PRODUCT_SEMI_AUTOMATON A1 A2) i x) A1.S =
                    PATH_DIFF (INPUT_RUN_PATH_UNION A2 i (PATH_RESTRICT x A2.S)) A1.S) /\
                   (PATH_DIFF (INPUT_RUN_PATH_UNION (PRODUCT_SEMI_AUTOMATON A1 A2) i x) A2.S =
                    PATH_DIFF (INPUT_RUN_PATH_UNION A1 i (PATH_RESTRICT x A1.S)) A2.S) /\
                   (PATH_DIFF (INPUT_RUN_PATH_UNION (PRODUCT_SEMI_AUTOMATON A1 A2) i y) A1.S =
                    PATH_DIFF (INPUT_RUN_PATH_UNION A2 i (PATH_RESTRICT y A2.S)) A1.S) /\
                   (PATH_DIFF (INPUT_RUN_PATH_UNION (PRODUCT_SEMI_AUTOMATON A1 A2) i y) A2.S =
                    PATH_DIFF (INPUT_RUN_PATH_UNION A1 i (PATH_RESTRICT y A1.S)) A2.S)`
      >- (UNDISCH_NO_TAC 7 THEN UNDISCH_NO_TAC 9 THEN rpt WEAKEN_HD_TAC \\
          ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
          SIMP_TAC std_ss [PATH_DIFF_def, INPUT_RUN_PATH_UNION_def,
                           INPUT_RUN_STATE_UNION_def, EXTENSION,
                           PATH_RESTRICT_def,
                           PRODUCT_SEMI_AUTOMATON_REWRITES,
                           IN_UNION, IN_DIFF, PATH_MAP_def, IN_INTER,
                           IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                           PATH_SUBSET_def, SUBSET_DEF] \\
          rpt STRIP_TAC THEN rpt BOOL_EQ_STRIP_TAC \\
          PROVE_TAC []) \\
      PROVE_TAC [PRODUCT_SEMI_AUTOMATON_RUN2___FIRST,
                 PRODUCT_SEMI_AUTOMATON_RUN2___SECOND, A_USED_INPUT_VARS_DIFF_DISJOINT_THM] ]
QED

Theorem A_NDET___FLATTENING :
    !A1 A2 f. A_USED_STATE_VARS_COMPATIBLE (A_NDET(A1, A_TRUE)) (A_NDET(A2, f)) ==>
              AUTOMATON_EQUIV (A_NDET(A1, A_NDET(A2, f)))
                              (A_NDET(PRODUCT_SEMI_AUTOMATON A1 A2, f))
Proof
    SIMP_TAC std_ss [AUTOMATON_EQUIV_def, A_SEM_def,
                     A_USED_STATE_VARS_COMPATIBLE_def, DISJOINT_UNION_BOTH,
                     A_USED_INPUT_VARS_def, SEMI_AUTOMATON_USED_INPUT_VARS_def,
                     EMPTY_DIFF, UNION_EMPTY, A_USED_STATE_VARS_def]
 >> rpt STRIP_TAC
 >> FULL_SIMP_TAC std_ss [DISJOINT_UNION_BOTH, DISJOINT_DIFF_ELIM_SYM]
 >> SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     INPUT_RUN_PATH_UNION_def, PRODUCT_SEMI_AUTOMATON_REWRITES,
                     PATH_SUBSET_def, SUBSET_DEF, IN_UNION,
                     P_SEM_THM, INPUT_RUN_STATE_UNION_def, IS_TRANSITION_def, XP_SEM_def]
 >> EQ_TAC >> rpt STRIP_TAC
 >| [ EXISTS_TAC ``PATH_UNION w w'`` THEN
      SIMP_TAC std_ss [PATH_UNION_def, IN_UNION] THEN

      SUBGOAL_TAC `!n. (((w n UNION w' n UNION (v n DIFF (A1.S UNION A2.S)))) =
                        ((w' n UNION (w n UNION (v n DIFF A1.S) DIFF A2.S)))) /\
                       (((w n UNION w' n UNION (v n DIFF (A1.S UNION A2.S))) INTER (COMPL A2.S)) =
                        ((w n UNION (v n DIFF A1.S)) INTER (COMPL A2.S)))` THEN1 (
        SIMP_ALL_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF, IN_COMPL, GSYM SUBSET_COMPL_DISJOINT,
          SUBSET_DEF, IN_COMPL] THEN
        rpt STRIP_TAC THEN rpt BOOL_EQ_STRIP_TAC THEN PROVE_TAC[]
      ) THEN
      SUBGOAL_TAC `P_USED_VARS A1.S0 SUBSET (COMPL A2.S) /\
                   P_USED_VARS A2.S0 SUBSET (COMPL A1.S) /\
                   XP_USED_VARS A1.R SUBSET (COMPL A2.S) /\
                   XP_USED_VARS A2.R SUBSET (COMPL A1.S)` THEN1 (
        PROVE_TAC[SUBSET_COMPL_DISJOINT]
      ) THEN
      rpt STRIP_TAC THENL [
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
        rpt STRIP_TAC THEN rpt BOOL_EQ_STRIP_TAC THEN PROVE_TAC[]
      ) THEN
      SUBGOAL_TAC `P_USED_VARS A1.S0 SUBSET (COMPL A2.S) /\
                   XP_USED_VARS A1.R SUBSET (COMPL A2.S)` THEN1 (
        PROVE_TAC[SUBSET_COMPL_DISJOINT]
      ) THEN
      rpt STRIP_TAC THENL [
        PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM],
        PROVE_TAC[XP_USED_VARS_INTER_SUBSET_BOTH_THM],

        EXISTS_TAC ``(PATH_RESTRICT w A2.S)`` THEN
        SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, IN_INTER] THEN
        SUBGOAL_TAC `!n. (w n INTER A2.S UNION (w n INTER A1.S UNION (v n DIFF A1.S) DIFF A2.S)) =
                         (w n UNION (v n DIFF (A1.S UNION A2.S)))` THEN1 (
          SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF] THEN
          rpt STRIP_TAC THEN rpt BOOL_EQ_STRIP_TAC THEN METIS_TAC[]
        ) THEN
        ASM_SIMP_TAC std_ss []
      ] ]
QED

(* key result: for total and deterministic semi-automata, A_NDET (existential)
   and A_UNIV (universal) acceptance conditions are the same thing.
 *)
Theorem TOTAL_DET_AUTOMATON_EX_ALL_EQUIV :
    !A. IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON A ==>
        !f. AUTOMATON_EQUIV (A_NDET(A,f)) (A_UNIV(A,f))
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [AUTOMATON_EQUIV_def, A_SEM_THM]
 >> METIS_TAC [TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_UNIQUE_RUN]
QED

Theorem UNIQUE_RUN_WITH_PROPERTIES___CONSTRAINED_AUTOMATON_EX_ALL_EQUIV :
    !A C. UNIQUE_RUN_WITH_PROPERTIES A C ==>
          !f. AUTOMATON_EQUIV (A_NDET_CONSTRAINED (A,C,f)) (A_UNIV_CONSTRAINED (A,C,f))
Proof
    REWRITE_TAC [AUTOMATON_EQUIV_def,
                 A_NDET_CONSTRAINED_def,
                 A_UNIV_CONSTRAINED_def,
                 A_SEM_THM,
                 UNIQUE_RUN_WITH_PROPERTIES_def]
 >> METIS_TAC []
QED

Theorem NEG_ACCEPTANCE_CONDITION :
    !A f. AUTOMATON_EQUIV (A_NOT(A_NDET(A,f))) (A_UNIV(A, A_NOT f))
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [AUTOMATON_EQUIV_def, A_SEM_THM]
 >> METIS_TAC []
QED

Theorem NEG_ACCEPTANCE_CONDITION_DET :
    !A f. IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON A ==>
          AUTOMATON_EQUIV (A_NOT(A_NDET(A,f))) (A_NDET(A, A_NOT f))
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [AUTOMATON_EQUIV_def, A_SEM_THM]
 >> METIS_TAC [TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_UNIQUE_RUN]
QED

Theorem ACCEPT_COND___VAR_RENAMING___NOT_INJ :
    !ac t i f.
       ACCEPT_COND_SEM_TIME t i (ACCEPT_VAR_RENAMING f ac) =
       ACCEPT_COND_SEM_TIME t (\n x. f x IN i n) ac
Proof
    INDUCT_THEN acceptance_condition_induct ASSUME_TAC
 >> FULL_SIMP_TAC std_ss [ACCEPT_VAR_RENAMING_def, ACCEPT_COND_SEM_TIME_def,
                          P_SEM___VAR_RENAMING___NOT_INJ]
QED

Theorem ACCEPT_COND___VAR_RENAMING :
    !a t i f. INJ f (PATH_USED_VARS i UNION ACCEPT_COND_USED_VARS a) UNIV ==>
                    (ACCEPT_COND_SEM_TIME t i a =
                     ACCEPT_COND_SEM_TIME t (PATH_VAR_RENAMING f i) (ACCEPT_VAR_RENAMING f a))
Proof
    INDUCT_THEN acceptance_condition_induct ASSUME_TAC
 >| [ rpt STRIP_TAC \\
      SIMP_ALL_TAC std_ss [ACCEPT_COND_SEM_TIME_def, ACCEPT_VAR_RENAMING_def,
                           PATH_VAR_RENAMING_def, PATH_MAP_def, ACCEPT_COND_USED_VARS_def] \\
      `(i t UNION  P_USED_VARS p) SUBSET (PATH_USED_VARS i UNION P_USED_VARS p)`
          by (SIMP_TAC std_ss [PATH_USED_VARS_def, SUBSET_DEF, IN_UNION,
                               IN_BIGUNION, GSPECIFICATION] \\
              PROVE_TAC []) \\
      PROVE_TAC [P_SEM___VAR_RENAMING, INJ_SUBSET_DOMAIN],

      SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def, ACCEPT_VAR_RENAMING_def],

      ASM_SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def, ACCEPT_VAR_RENAMING_def,
                           ACCEPT_COND_USED_VARS_def],

      SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def, ACCEPT_VAR_RENAMING_def,
                       ACCEPT_COND_USED_VARS_def] \\
      PROVE_TAC [INJ_SUBSET_DOMAIN, SUBSET_UNION, UNION_COMM, UNION_ASSOC],

      SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def, ACCEPT_VAR_RENAMING_def,
                       ACCEPT_COND_USED_VARS_def] \\
      PROVE_TAC [] ]
QED

Theorem AUTOMATON_FORMULA___VAR_RENAMING :
    !a i (f:'a->'b). INJ f (PATH_USED_VARS i UNION A_USED_VARS a) UNIV ==>
                    (A_SEM i a = A_SEM (PATH_VAR_RENAMING f i) (A_VAR_RENAMING f a))
Proof
    INDUCT_THEN automaton_formula_induct ASSUME_TAC THENL [
      rpt STRIP_TAC THEN
      REWRITE_TAC [A_SEM_def, A_VAR_RENAMING_def, ACCEPT_COND_SEM_def] THEN
      SIMP_ALL_TAC std_ss [A_USED_VARS___DIRECT_DEF] THEN
      PROVE_TAC[ACCEPT_COND___VAR_RENAMING, A_USED_VARS_def],

      rpt STRIP_TAC THEN
      SIMP_TAC std_ss [A_SEM_def, A_VAR_RENAMING_def] THEN
      EQ_TAC THEN rpt STRIP_TAC THENL [
         Q.EXISTS_TAC `PATH_VAR_RENAMING f w` THEN
         rpt STRIP_TAC THENL [
            UNDISCH_KEEP_NO_TAC 1 THEN
            IMP_TO_EQ_TAC THEN
            MATCH_MP_TAC SEMI_AUTOMATON___VAR_RENAMING THEN
            UNDISCH_NO_TAC 2 THEN
            MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
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
            MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
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
         Q.EXISTS_TAC `w'` THEN
         rpt STRIP_TAC THENL [
            UNDISCH_NO_TAC 3 THEN
            IMP_TO_EQ_TAC THEN
            ASM_REWRITE_TAC [] THEN
            MATCH_MP_TAC (GSYM SEMI_AUTOMATON___VAR_RENAMING) THEN
            UNDISCH_NO_TAC 3 THEN
            MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
            SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, A_USED_VARS___DIRECT_DEF,
              SEMI_AUTOMATON_USED_VARS_def, GSYM PATH_USED_VARS_THM] THEN
            SIMP_ALL_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF] THEN
            PROVE_TAC [],

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
            MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
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
      rpt STRIP_TAC THEN
      REMAINS_TAC `INJ f (PATH_USED_VARS i UNION A_USED_VARS a) UNIV /\
                   INJ f (PATH_USED_VARS i UNION A_USED_VARS a') UNIV` THEN1 (
        PROVE_TAC[]
      ) THEN
      STRIP_TAC THEN
      UNDISCH_HD_TAC THEN
      MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
      PROVE_TAC[],

      REWRITE_TAC[A_SEM_def, A_VAR_RENAMING_def]
   ]
QED

Theorem AUTOMATON_FORMULA___STATE_VAR_RENAMING :
    !a i f. INJ f (PATH_USED_VARS i UNION A_USED_VARS a) UNIV /\
           (!x. x IN (A_USED_INPUT_VARS a) ==> (f x = x)) ==>
           (A_SEM i a = A_SEM i (A_VAR_RENAMING f a))
Proof
    rpt STRIP_TAC
 >> REMAINS_TAC `PATH_RESTRICT (PATH_VAR_RENAMING f i) (A_USED_INPUT_VARS (A_VAR_RENAMING f a)) =
                 PATH_RESTRICT i (A_USED_INPUT_VARS (A_VAR_RENAMING f a))`
 >- PROVE_TAC [AUTOMATON_FORMULA___VAR_RENAMING, A_USED_INPUT_VARS_INTER_THM]
 >> ONCE_REWRITE_TAC [FUN_EQ_THM]
 >> SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_VAR_RENAMING_def, PATH_MAP_def,
                     EXTENSION, IN_INTER]
 >> rpt STRIP_TAC >> CONJ_EQ_STRIP_TAC
 >> SUBGOAL_TAC `x' IN IMAGE f (A_USED_INPUT_VARS a)`
 >- (`INJ f (A_USED_VARS a) UNIV` by METIS_TAC[INJ_SUBSET_DOMAIN, SUBSET_UNION] \\
     FULL_SIMP_TAC std_ss [A_VAR_RENAMING___USED_INPUT_VARS])
 >> SIMP_ALL_TAC std_ss [IN_IMAGE, INJ_DEF, IN_UNIV, IN_UNION,
                         GSYM PATH_USED_VARS_THM, A_USED_VARS_def]
 >> METIS_TAC []
QED

Theorem A_SEM_AUTOMATON_RUN___STATE_VAR_RENAMING :
    !A a f. INJ f UNIV UNIV /\
            (!x. x IN (SEMI_AUTOMATON_USED_INPUT_VARS A UNION
                       (A_USED_INPUT_VARS a DIFF A.S)) ==> (f x = x)) ==>
      !i w. (A_SEM (INPUT_RUN_PATH_UNION A i w) a =
             A_SEM (INPUT_RUN_PATH_UNION (SEMI_AUTOMATON_VAR_RENAMING f A) i (PATH_VAR_RENAMING f w))
                   (A_VAR_RENAMING f a))
Proof
    rpt STRIP_TAC
 >> REMAINS_TAC `(PATH_RESTRICT (PATH_VAR_RENAMING f (INPUT_RUN_PATH_UNION A i w))
                                (A_USED_INPUT_VARS (A_VAR_RENAMING f a))) =
                 (PATH_RESTRICT (INPUT_RUN_PATH_UNION
                                  (SEMI_AUTOMATON_VAR_RENAMING f A) i
                                  (PATH_VAR_RENAMING f w))
                                (A_USED_INPUT_VARS (A_VAR_RENAMING f a)))`
 >- PROVE_TAC [AUTOMATON_FORMULA___VAR_RENAMING, A_USED_INPUT_VARS_INTER_THM,
               INJ_SUBSET_DOMAIN, SUBSET_UNIV]
 >> ONCE_REWRITE_TAC [FUN_EQ_THM]
 >> Cases_on `A`
 >> SIMP_ALL_TAC std_ss [PATH_RESTRICT_def, PATH_VAR_RENAMING_def, PATH_MAP_def,
                         EXTENSION, IN_INTER, IN_UNION, IN_DIFF,
                         INPUT_RUN_PATH_UNION_def,
                         INPUT_RUN_STATE_UNION_def, IN_IMAGE,
                         SEMI_AUTOMATON_VAR_RENAMING_def, symbolic_semi_automaton_REWRITES]
 >> rpt STRIP_TAC >> CONJ_EQ_STRIP_TAC
 >> `x'' IN IMAGE f (A_USED_INPUT_VARS a)`
       by PROVE_TAC [INJ_SUBSET_DOMAIN, SUBSET_UNIV, A_VAR_RENAMING___USED_INPUT_VARS]
 >> SIMP_ALL_TAC std_ss [IN_IMAGE, INJ_DEF, IN_UNIV]
 >> METIS_TAC []
QED

Theorem STATE_VARDISJOINT_AUTOMATON_FORMULA___VAR_RENAMING :
    !a f. INJ f (A_USED_STATE_VARS a) UNIV ==>
         (STATE_VARDISJOINT_AUTOMATON_FORMULA (A_VAR_RENAMING f a) =
          STATE_VARDISJOINT_AUTOMATON_FORMULA a)
Proof
    INDUCT_THEN automaton_formula_induct STRIP_ASSUME_TAC
 >| [ SIMP_TAC std_ss [A_USED_STATE_VARS_def, STATE_VARDISJOINT_AUTOMATON_FORMULA_def,
                       A_VAR_RENAMING_def],
      Cases_on `p_1` \\
      SIMP_ALL_TAC std_ss [A_USED_STATE_VARS_def, STATE_VARDISJOINT_AUTOMATON_FORMULA_def,
                           A_VAR_RENAMING_def,
                           symbolic_semi_automaton_REWRITES,
                           SEMI_AUTOMATON_VAR_RENAMING_def,
                           A_VAR_RENAMING___USED_STATE_VARS] \\
      rpt STRIP_TAC \\
      BINOP_TAC >|
      [ SIMP_ALL_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
                             INJ_DEF, IN_UNIV, IN_UNION, IN_IMAGE] \\
        PROVE_TAC [],
        PROVE_TAC [SUBSET_UNION, INJ_SUBSET_DOMAIN, SUBSET_REFL] ],
      ASM_SIMP_TAC std_ss [A_USED_STATE_VARS_def, STATE_VARDISJOINT_AUTOMATON_FORMULA_def,
                           A_VAR_RENAMING_def],
      ASM_SIMP_TAC std_ss [A_USED_STATE_VARS_def, STATE_VARDISJOINT_AUTOMATON_FORMULA_def,
                           A_VAR_RENAMING_def, A_VAR_RENAMING___USED_STATE_VARS] \\
      rpt STRIP_TAC \\
      BINOP_TAC >|
      [ SIMP_ALL_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
                             INJ_DEF, IN_UNIV, IN_UNION, IN_IMAGE] \\
        PROVE_TAC [],
        PROVE_TAC [SUBSET_UNION, INJ_SUBSET_DOMAIN, SUBSET_REFL] ],
      SIMP_TAC std_ss [A_VAR_RENAMING_def, STATE_VARDISJOINT_AUTOMATON_FORMULA_def] ]
QED

Theorem VARDISJOINT_AUTOMATON_FORMULA___VAR_RENAMING :
    !a f. INJ f (A_USED_VARS a) UNIV ==>
         (VARDISJOINT_AUTOMATON_FORMULA (A_VAR_RENAMING f a) = VARDISJOINT_AUTOMATON_FORMULA a)
Proof
    REWRITE_TAC [VARDISJOINT_AUTOMATON_FORMULA_def, A_USED_VARS_def]
 >> rpt GEN_TAC >> DISCH_TAC >> BINOP_TAC
 >| [ PROVE_TAC [STATE_VARDISJOINT_AUTOMATON_FORMULA___VAR_RENAMING,
                 INJ_SUBSET_DOMAIN, SUBSET_UNION, SUBSET_REFL],
     `A_USED_INPUT_VARS (A_VAR_RENAMING f a) = IMAGE f (A_USED_INPUT_VARS a)`
        by PROVE_TAC [A_VAR_RENAMING___USED_INPUT_VARS, A_USED_VARS_def] \\
      ASM_SIMP_TAC std_ss [A_VAR_RENAMING___USED_STATE_VARS,
                           A_VAR_RENAMING___USED_INPUT_VARS, A_USED_VARS_def,
                           GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL, IN_IMAGE] \\
      SIMP_ASSUMPTIONS_TAC std_ss [INJ_DEF, IN_UNION, IN_UNIV] \\
      PROVE_TAC [SUBSET_REFL] ]
QED

Theorem EXISTS_RUN_WITH_PROPERTIES___A_SEM_REWRITE :
    !A C. EXISTS_RUN_WITH_PROPERTIES A C = !i. A_SEM i (A_NDET (A, A_BIGAND C))
Proof
    SIMP_TAC std_ss [EXISTS_RUN_WITH_PROPERTIES_def, A_SEM_def]
QED

Theorem EXISTS_RUN_WITH_PROPERTIES___STATE_VAR_RENAMING :
    !A C f. INJ f UNIV UNIV /\
           (!x. x IN (SEMI_AUTOMATON_USED_INPUT_VARS A
                      UNION ((A_USED_INPUT_VARS (A_BIGAND C)) DIFF A.S)) ==> (f x = x)) ==>
      (EXISTS_RUN_WITH_PROPERTIES (SEMI_AUTOMATON_VAR_RENAMING f A) (MAP (A_VAR_RENAMING f) C) =
       EXISTS_RUN_WITH_PROPERTIES A C)
Proof
    rpt STRIP_TAC
 >> SIMP_TAC std_ss [EXISTS_RUN_WITH_PROPERTIES___A_SEM_REWRITE,
                     GSYM A_VAR_RENAMING___A_BIGAND,
                     GSYM A_VAR_RENAMING_def]
 >> `(SEMI_AUTOMATON_USED_INPUT_VARS A) UNION (A_USED_INPUT_VARS (A_BIGAND C) DIFF A.S) =
     A_USED_INPUT_VARS (A_NDET (A,A_BIGAND C))`
       by SIMP_TAC std_ss [A_USED_INPUT_VARS_def]
 >> PROVE_TAC [AUTOMATON_FORMULA___STATE_VAR_RENAMING, INJ_SUBSET_DOMAIN,
               SUBSET_UNIV, SUBSET_REFL]
QED

Theorem UNIQUE_RUN_WITH_PROPERTIES___STATE_VAR_RENAMING :
    !A C f. INJ f UNIV UNIV /\
           (!x. x IN (SEMI_AUTOMATON_USED_INPUT_VARS A
                      UNION ((A_USED_INPUT_VARS (A_BIGAND C)) DIFF A.S)) ==> (f x = x)) ==>
      (UNIQUE_RUN_WITH_PROPERTIES (SEMI_AUTOMATON_VAR_RENAMING f A) (MAP (A_VAR_RENAMING f) C) =
       UNIQUE_RUN_WITH_PROPERTIES A C)
Proof
    SIMP_TAC std_ss [UNIQUE_RUN_WITH_PROPERTIES_def, EXISTS_UNIQUE_DEF]
 >> rpt STRIP_TAC >> SIMP_TAC std_ss [FORALL_AND_THM]
 >> BINOP_TAC
 >- METIS_TAC [EXISTS_RUN_WITH_PROPERTIES___STATE_VAR_RENAMING,
               EXISTS_RUN_WITH_PROPERTIES_def]
 >> REWRITE_TAC [GSYM A_VAR_RENAMING___A_BIGAND]
 >> FORALL_EQ_STRIP_TAC
 >> EQ_TAC >> rpt STRIP_TAC
 >| [ REMAINS_TAC `PATH_VAR_RENAMING f x = PATH_VAR_RENAMING f y`
      >- (UNDISCH_HD_TAC \\
          ONCE_REWRITE_TAC [FUN_EQ_THM] \\
          SIMP_ALL_TAC std_ss [PATH_VAR_RENAMING_def, PATH_MAP_def, EXTENSION, IN_IMAGE,
                               INJ_DEF, IN_UNIV] \\
          METIS_TAC []) \\
      Q_SPECL_NO_ASSUM 4 [`PATH_VAR_RENAMING f x`, `PATH_VAR_RENAMING f y`] \\
      METIS_TAC [A_SEM_AUTOMATON_RUN___STATE_VAR_RENAMING,
                 SEMI_AUTOMATON___STATE_VAR_RENAMING, IN_UNION,
                 SUBSET_UNIV, INJ_SUBSET_DOMAIN, SUBSET_REFL],
      SUBGOAL_TAC `(?x'. x = PATH_VAR_RENAMING f x') /\ ?y'. y = PATH_VAR_RENAMING f y'`
      >- (SIMP_ASSUMPTIONS_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                                       SEMI_AUTOMATON_VAR_RENAMING_REWRITES] \\
          METIS_TAC [PATH_VAR_RENAMING___ORIG_PATH_EXISTS]) \\
      METIS_TAC [A_SEM_AUTOMATON_RUN___STATE_VAR_RENAMING,
                 SEMI_AUTOMATON___STATE_VAR_RENAMING, IN_UNION] ]
QED

Theorem EXISTS_RUN_WITH_PROPERTIES___PROPERTIES_SPLIT :
    (!A C1 C2. EXISTS_RUN_WITH_PROPERTIES A (C1++C2) ==>
               EXISTS_RUN_WITH_PROPERTIES A C1 /\ EXISTS_RUN_WITH_PROPERTIES A C2) /\
    (!A c C. EXISTS_RUN_WITH_PROPERTIES A (c::C) ==>
             EXISTS_RUN_WITH_PROPERTIES A [c] /\ EXISTS_RUN_WITH_PROPERTIES A C)
Proof
    REWRITE_TAC [EXISTS_RUN_WITH_PROPERTIES_def, A_BIGAND___A_SEM, A_BIGAND_def, A_SEM_def]
 >> METIS_TAC []
QED

Theorem A_NDET___INITIAL_ACCEPTANCE_SYM :
    !S S0 R p C. AUTOMATON_EQUIV
                  (A_NDET (symbolic_semi_automaton S S0 R,A_AND (ACCEPT_COND_PROP p,A_BIGAND C)))
                  (A_NDET (symbolic_semi_automaton S (P_AND(p, S0)) R,A_BIGAND C))
Proof
    SIMP_TAC std_ss [AUTOMATON_EQUIV_def, A_SEM_def, ACCEPT_COND_PROP_def,
                     IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     symbolic_semi_automaton_REWRITES,
                     IS_TRANSITION_def, INPUT_RUN_PATH_UNION_def,
                     INPUT_RUN_STATE_UNION_def,
                     ACCEPT_COND_SEM_def, ACCEPT_COND_SEM_TIME_def, P_SEM_def]
 >> rpt GEN_TAC
 >> EXISTS_EQ_STRIP_TAC >> rpt BOOL_EQ_STRIP_TAC
QED

Theorem A_UNIV___INITIAL_ACCEPTANCE_SYM :
    !S S0 R p C. AUTOMATON_EQUIV
                  (A_UNIV (symbolic_semi_automaton S S0 R,A_IMPL (ACCEPT_COND_PROP p,A_BIGAND C)))
                  (A_UNIV (symbolic_semi_automaton S (P_AND(p, S0)) R,A_BIGAND C))
Proof
    SIMP_TAC std_ss [AUTOMATON_EQUIV_def, A_SEM_def, ACCEPT_COND_PROP_def,
                     IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     symbolic_semi_automaton_REWRITES,
                     IS_TRANSITION_def, INPUT_RUN_PATH_UNION_def,
                     INPUT_RUN_STATE_UNION_def, ACCEPT_COND_SEM_def,
                     ACCEPT_COND_SEM_TIME_def, P_SEM_def, A_UNIV_def, A_IMPL_def, A_OR_def]
 >> METIS_TAC []
QED

Theorem ACCEPT_COND_RESTN_SEM :
    !f v t1 t2. (ACCEPT_COND_SEM_TIME (t1+t2) v f =
                 ACCEPT_COND_SEM_TIME t1 (PATH_RESTN v t2) f)
Proof
    INDUCT_THEN acceptance_condition_induct ASSUME_TAC
 >| [ SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def, PATH_RESTN_def],
      SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def],
      ASM_SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def],
      ASM_SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def],
      ASM_SIMP_TAC std_ss [ACCEPT_COND_SEM_TIME_def] \\
      rpt STRIP_TAC >> EQ_TAC >> rpt STRIP_TAC >| (* 2 subgoals *)
      [ rename1 `t3 >= t1` \\
       `t3 + t2 >= t1 + t2` by DECIDE_TAC \\
        PROVE_TAC [],
        rename1 `t3 >= t1 + t2` \\
       `?t. t = (t3 - t2)` by METIS_TAC [] \\
       `(t3 = t + t2) /\ (t >= t1)` by DECIDE_TAC \\
        PROVE_TAC [] ] ]
QED

Theorem ID_AUTOMATON_SEM :
    !a. AUTOMATON_EQUIV a (A_NDET(ID_SEMI_AUTOMATON, a))
Proof
    SIMP_TAC std_ss [AUTOMATON_EQUIV_def, EMPTY_PATH_def, A_SEM_def,
                     ID_SEMI_AUTOMATON_RUN, INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
                     ID_SEMI_AUTOMATON_REWRITES, UNION_EMPTY, DIFF_EMPTY]
 >> METIS_TAC []
QED

Theorem A_NDET___SIMPLIFIED_SEMI_AUTOMATON_THM :
    !A A' f ac.
       IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON A' A f /\
       DISJOINT (IMAGE f (SEMI_AUTOMATON_USED_INPUT_VARS A)) (ACCEPT_COND_USED_VARS ac) ==>
       !i. A_SEM i (A_NDET (A, ACCEPT_COND ac)) =
           A_SEM i (A_NDET (A', ACCEPT_COND
                                 (ACCEPT_VAR_RENAMING
                                   (\x. (if x IN SEMI_AUTOMATON_USED_INPUT_VARS A then f x else x)) ac)))
Proof
    SIMP_TAC std_ss [A_SEM_THM]
 >> rpt STRIP_TAC
 >> ASSUME_TAC IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON___RUNS2
 >> Q_SPECL_NO_ASSUM 0 [`A'`, `A`, `f`]
 >> PROVE_CONDITION_NO_ASSUM 0 >- ASM_REWRITE_TAC []
 >> ASM_SIMP_TAC std_ss [] >> WEAKEN_HD_TAC
 >> EQ_TAC >> rpt STRIP_TAC
 >| [ (* goal 1 (of 2) *)
      Q.EXISTS_TAC `\n. w n UNION (IMAGE f (i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A))` \\
     `PATH_SUBSET w A.S` by FULL_SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def] \\
      rpt STRIP_TAC >|
      [ SIMP_ALL_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF, IN_UNION, IN_IMAGE,
                             IN_INTER, SUBSET_REFL] \\
        METIS_TAC [],

        REMAINS_TAC `PATH_RESTRICT
                       (\n. w n UNION IMAGE f (i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A))
                       A.S = w` >- ASM_REWRITE_TAC [] \\
        ONCE_REWRITE_TAC [FUN_EQ_THM] >> GEN_TAC \\
        ONCE_REWRITE_TAC [EXTENSION] >> GEN_TAC \\
        SIMP_ALL_TAC std_ss [IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON_def, IN_UNION,
                             IN_IMAGE, IN_DIFF, IN_SING, PATH_RESTRICT_def, PATH_MAP_def,
                             IN_INTER, PATH_SUBSET_def, SUBSET_DEF, SUBSET_REFL] \\
        METIS_TAC [],

        SIMP_ALL_TAC std_ss [IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON_def, IN_UNION,
                             IN_IMAGE, IN_DIFF, IN_SING, PATH_RESTRICT_def, PATH_MAP_def,
                             IN_INTER, PATH_SUBSET_def, SUBSET_DEF, SUBSET_REFL] \\
        METIS_TAC [],

        SIMP_ALL_TAC std_ss [ACCEPT_COND___VAR_RENAMING___NOT_INJ,
                             ACCEPT_COND_SEM_def] \\
        UNDISCH_NO_TAC 1 \\
        ONCE_REWRITE_TAC[ACCEPT_COND_USED_VARS_INTER_THM] THEN
        IMP_TO_EQ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        ONCE_REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
        ONCE_REWRITE_TAC [EXTENSION] THEN GEN_TAC THEN
        SIMP_ALL_TAC std_ss [IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON_def,
                             PATH_SUBSET_def, SUBSET_DEF, SUBSET_REFL, DISJOINT_DISJ_THM] \\
        FULL_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
                              IN_UNION, IN_DIFF, IN_ABS, IN_IMAGE,
                              symbolic_semi_automaton_REWRITES, IN_INTER, IN_SING,
                              PATH_RESTRICT_def, PATH_MAP_def, SEMI_AUTOMATON_USED_INPUT_VARS_def] \\
        METIS_TAC [] ],
      (* goal 2 (of 2) *)
      Q.EXISTS_TAC `PATH_RESTRICT w A.S` \\
      ASM_REWRITE_TAC [] \\
      SIMP_ALL_TAC std_ss [ACCEPT_COND___VAR_RENAMING___NOT_INJ,
                           ACCEPT_COND_SEM_def] \\
      UNDISCH_NO_TAC 0 \\
      ONCE_REWRITE_TAC[ACCEPT_COND_USED_VARS_INTER_THM] \\
      IMP_TO_EQ_TAC >> AP_THM_TAC >> AP_TERM_TAC \\
      ONCE_REWRITE_TAC [FUN_EQ_THM] >> GEN_TAC \\
      ONCE_REWRITE_TAC [EXTENSION] >> GEN_TAC \\
      SIMP_ALL_TAC std_ss [IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON_def,
                           PATH_SUBSET_def, SUBSET_DEF, DISJOINT_DISJ_THM] \\
      FULL_SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
                            IN_UNION, IN_DIFF, IN_ABS, IN_IMAGE,
                            symbolic_semi_automaton_REWRITES, IN_INTER, IN_SING,
                            PATH_RESTRICT_def, PATH_MAP_def, SEMI_AUTOMATON_USED_INPUT_VARS_def] \\
      METIS_TAC [] ]
QED

Theorem A_UNIV___SIMPLIFIED_SEMI_AUTOMATON_THM :
    !A A' f ac.
       IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON A' A f /\
       DISJOINT (IMAGE f (SEMI_AUTOMATON_USED_INPUT_VARS A)) (ACCEPT_COND_USED_VARS ac) ==>
       !i. A_SEM i (A_UNIV (A, ACCEPT_COND ac)) =
           A_SEM i (A_UNIV (A', ACCEPT_COND
                                 (ACCEPT_VAR_RENAMING
                                   (\x. (if x IN SEMI_AUTOMATON_USED_INPUT_VARS A then f x else x)) ac)))
Proof
    rpt STRIP_TAC
 >> REWRITE_TAC [A_UNIV_def]
 >> ONCE_REWRITE_TAC [A_SEM_def]
 >> SIMP_TAC std_ss []
 >> SUBGOAL_TAC `!A ac i. A_SEM i (A_NDET (A, A_NOT (ACCEPT_COND ac))) =
                          A_SEM i (A_NDET (A, ACCEPT_COND (ACCEPT_NOT ac)))`
 >- SIMP_TAC std_ss [A_SEM_def, ACCEPT_COND_SEM_def, ACCEPT_COND_SEM_TIME_def]
 >> ASM_REWRITE_TAC []
 >> WEAKEN_HD_TAC
 >> ASSUME_TAC A_NDET___SIMPLIFIED_SEMI_AUTOMATON_THM
 >> Q_SPECL_NO_ASSUM 0 [`A`, `A'`, `f`, `ACCEPT_NOT ac`]
 >> PROVE_CONDITION_NO_ASSUM 0
 >- ASM_SIMP_TAC std_ss [ACCEPT_COND_USED_VARS_def]
 >> ASM_SIMP_TAC std_ss [ACCEPT_VAR_RENAMING_def]
QED

val _ = export_theory();

(* References:

 [1] Tuerk, T., Schneider, K., Gordon, M.: Model Checking PSL Using HOL and SMV.
     In: Bin, E., Ziv, A., and Ur, S. (eds.) LNCS 4383 - Hardware and Software:
     Verification and Testing (HVC 2006). pp. 1-15. Springer, Berlin, Heidelberg (2007).

 [2] Tuerk, T., Schneider, K.: A hierarchy for Accellera's property specification
     language, Thesis, University of Kaiserslautern (2005).

 [3] Schneider, K.: Improving Automata Generation for Linear Temporal Logic by
     Considering the Automaton Hierarchy. In: Nieuwenhuis, R. and Voronkov, A. (eds.)
     LNAI 2250 - Logic for Programming, Artificial Intelligence, and Reasoning (LPAR 2001).
     pp. 39–54. Springer, Berlin, Heidelberg (2001).

 [4] Schneider, K., Hoffmann, D.W.: A HOL Conversion for Translating Linear Time
     Temporal Logic to omega-Automata. In: LNCS 1690 - Theorem Proving in Higher Order
     Logics (TPHOLs 1999). pp. 255–272. Springer, Berlin, Heidelberg (1999).
*)
