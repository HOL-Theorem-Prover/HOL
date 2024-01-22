(* -*- Mode: holscript; -*- ***************************************************)
(*                                                                            *)
(*       Symbolic representation of non-deterministic semi-automata           *)
(*                                                                            *)
(******************************************************************************)

open HolKernel Parse boolLib bossLib;

open infinite_pathTheory pred_setTheory listTheory pairTheory xprop_logicTheory
     containerTheory prop_logicTheory set_lemmataTheory prim_recTheory;

open term_grammar tuerk_tacticsLib temporal_deep_mixedTheory;

open Sanity;

val _ = hide "S";
val _ = hide "K";
val _ = hide "I";

val _ = new_theory "symbolic_semi_automaton";
val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj"]
val _ = ParseExtras.temp_loose_equality()

(* Different with symbolic_kripke_structure, which does not have concepts of
   input and state variables, i.e. there's no "S" component (state variables).

  `symbolic_semi_automaton` is used in LTL to Omega automata translation, where
   variables used in LTL formula are treated as input variables. (ltl2omega.sml)

  It's "semi" because there's no final states or fair states specified (yet).
 *)
Datatype :
    symbolic_semi_automaton =
    <| S:  'var set;        (* set of all (used) state variables *)
       S0: 'var prop_logic; (* initial states *)
       R:  'var xprop_logic (* transition relation, current state # input # next state *)
     |>
End

(* used input vars = all used vars in (S0,R) - all state vars (S) *)
val SEMI_AUTOMATON_USED_INPUT_VARS_def = Define
   `SEMI_AUTOMATON_USED_INPUT_VARS A = (P_USED_VARS A.S0 UNION XP_USED_VARS A.R) DIFF A.S`;

val SEMI_AUTOMATON_USED_VARS_def = Define
   `SEMI_AUTOMATON_USED_VARS A = (SEMI_AUTOMATON_USED_INPUT_VARS A) UNION A.S`;

(* all used vars = all used vars in (S0,R) + all state vars (S) *)
Theorem SEMI_AUTOMATON_USED_VARS___DIRECT_DEF :
    !A. SEMI_AUTOMATON_USED_VARS A = P_USED_VARS A.S0 UNION XP_USED_VARS A.R UNION A.S
Proof
    SIMP_TAC std_ss [SEMI_AUTOMATON_USED_VARS_def, EXTENSION, IN_UNION,
                     IN_DIFF, SEMI_AUTOMATON_USED_INPUT_VARS_def]
 >> PROVE_TAC []
QED

val SEMI_AUTOMATON_VAR_RENAMING_def = Define
   `SEMI_AUTOMATON_VAR_RENAMING (f:'a->'b) (symbolic_semi_automaton S S0 R) =
      (symbolic_semi_automaton (IMAGE f S) (P_VAR_RENAMING f S0) (XP_VAR_RENAMING f R))`;

Theorem SEMI_AUTOMATON_VAR_RENAMING_REWRITES :
    !A f. ((SEMI_AUTOMATON_VAR_RENAMING f A).S = IMAGE f A.S) /\
          ((SEMI_AUTOMATON_VAR_RENAMING f A).S0 = P_VAR_RENAMING f A.S0) /\
          ((SEMI_AUTOMATON_VAR_RENAMING f A).R = XP_VAR_RENAMING f A.R)
Proof
    Cases_on `A` >> EVAL_TAC >> PROVE_TAC []
QED

Theorem symbolic_semi_automaton_REWRITES =
        LIST_CONJ
        (TypeBase.one_one_of “:α symbolic_semi_automaton” ::
         TypeBase.accessors_of “:α symbolic_semi_automaton”)

(*=============================================================================
= Semantics
=============================================================================*)

(*****************************************************************************)
(* symbolic representation of non deterministic semi automata                *)
(*****************************************************************************)

(* `A` is used only to filter out all state variables in `i` *)
val INPUT_RUN_STATE_UNION_def = Define
   `INPUT_RUN_STATE_UNION A i s = s UNION (i DIFF A.S)`;

val INPUT_RUN_PATH_UNION_def = Define
   `INPUT_RUN_PATH_UNION A i w = \n. INPUT_RUN_STATE_UNION A (i n) (w n)`;

(* (s1,i1) is the current state, (s2,i2) is the next state *)
val IS_TRANSITION_def = Define
   `IS_TRANSITION A s1 i1 s2 i2 =
       XP_SEM A.R (INPUT_RUN_STATE_UNION A i1 s1, INPUT_RUN_STATE_UNION A i2 s2)`;

(*****************************************************************************)
(* RUN A i w is true iff w is a run of i through A                           *)
(*****************************************************************************)
val IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def = Define
   `IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w =
      (PATH_SUBSET w A.S /\
       P_SEM (INPUT_RUN_PATH_UNION A i w 0) A.S0 /\
       !n. IS_TRANSITION A (w n) (i n) (w (SUC n)) (i (SUC n)))`;

(*=============================================================================
= Syntactic Sugar and elementary lemmata
=============================================================================*)

(* cf. boolTheory.EXISTS_DEF (at least one), EXISTS_UNIQUE_DEF (exactly one) *)
val EXISTS_AT_MOST_ONE_def = Define
   `EXISTS_AT_MOST_ONE = \P:'a->bool. !x y. P x /\ P y ==> (x=y)`;
val _ = set_fixity "EXISTS_AT_MOST_ONE" Binder;

(* Deterministric: for each input trace there's at most one "compatible" trace
   satisfying initial state and transition relation.
 *)
val IS_DET_SYMBOLIC_SEMI_AUTOMATON_def = Define
   `IS_DET_SYMBOLIC_SEMI_AUTOMATON A =
      (!i. EXISTS_AT_MOST_ONE s. ((s SUBSET A.S) /\ (P_SEM (INPUT_RUN_STATE_UNION A i s) A.S0))) /\
      (!s1 i1 i2. EXISTS_AT_MOST_ONE s2. ((s2 SUBSET A.S) /\ IS_TRANSITION A s1 i1 s2 i2))`;

(* Total: for each input trace there's at least one "compatible" trace, i.e.
   no deadlock for whatever inputs.
 *)
val IS_TOTAL_SYMBOLIC_SEMI_AUTOMATON_def = Define
   `IS_TOTAL_SYMBOLIC_SEMI_AUTOMATON A =
      (!i. ?s. ((s SUBSET A.S) /\ (P_SEM (INPUT_RUN_STATE_UNION A i s) A.S0))) /\
      (!s1 i1 i2. ?s2. ((s2 SUBSET A.S) /\ IS_TRANSITION A s1 i1 s2 i2))`;

val IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_def = Define
   `IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON A =
    IS_TOTAL_SYMBOLIC_SEMI_AUTOMATON A /\ IS_DET_SYMBOLIC_SEMI_AUTOMATON A`;

(* Total+deterministric: for each input trace there's exactly one "compatible" trace
   satisfying initial state and transition relation.
 *)
Theorem IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_THM :
    !A. IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON A =
       (!i. ?!s. ((s SUBSET A.S) /\ (P_SEM (INPUT_RUN_STATE_UNION A i s) A.S0))) /\
       (!s1 i1 i2. ?!s2. ((s2 SUBSET A.S) /\ IS_TRANSITION A s1 i1 s2 i2))
Proof
    GEN_TAC
 >> SIMP_TAC std_ss [IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_def,
                     IS_TOTAL_SYMBOLIC_SEMI_AUTOMATON_def,
                     IS_DET_SYMBOLIC_SEMI_AUTOMATON_def, EXISTS_AT_MOST_ONE_def]
 >> PROVE_TAC []
QED

(* A semi-automaton without some syntactic sugar, i.e. w/o input variables *)
val IS_SIMPLE_SYMBOLIC_SEMI_AUTOMATON_def = Define
   `IS_SIMPLE_SYMBOLIC_SEMI_AUTOMATON A =
      (P_USED_VARS A.S0 SUBSET A.S /\ XP_USED_X_VARS A.R SUBSET A.S)`;

(* In "simple" symbolic runs of semi-automaton, the input state (i n) is only
   used in the current part of relation.
 *)
val IS_SYMBOLIC_RUN_THROUGH_SIMPLE_SEMI_AUTOMATON_def = Define
   `IS_SYMBOLIC_RUN_THROUGH_SIMPLE_SEMI_AUTOMATON A i w =
      (PATH_SUBSET w A.S /\ P_SEM (w 0) A.S0 /\
       !n. XP_SEM A.R ((w n) UNION (i n DIFF A.S), (w (SUC n))))`;

(* In case of simple symbolic semi-automaton, the normal symbolic run is
   also the "simple" symbolic run.
 *)
Theorem IS_SYMBOLIC_RUN_THROUGH_SIMPLE_SEMI_AUTOMATON_THM :
    !A. IS_SIMPLE_SYMBOLIC_SEMI_AUTOMATON A ==>
        !i w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w =
              IS_SYMBOLIC_RUN_THROUGH_SIMPLE_SEMI_AUTOMATON A i w
Proof
    SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     IS_SYMBOLIC_RUN_THROUGH_SIMPLE_SEMI_AUTOMATON_def,
                     IS_SIMPLE_SYMBOLIC_SEMI_AUTOMATON_def,
                     IS_TRANSITION_def,
                     INPUT_RUN_PATH_UNION_def,
                     INPUT_RUN_STATE_UNION_def,
                     PATH_SUBSET_def]
 >> rpt STRIP_TAC
 >> BOOL_EQ_STRIP_TAC
 >> SUBGOAL_TAC `!n. (w n UNION (i n DIFF A.S)) INTER A.S = w n`
 >- (SIMP_ALL_TAC std_ss [EXTENSION, IN_UNION, IN_INTER, IN_DIFF, SUBSET_DEF] \\
     METIS_TAC [])
 >> PROVE_TAC [P_USED_VARS_INTER_SUBSET_THM, XP_USED_VARS_INTER_SUBSET_THM]
QED

(* A = f(A'), a simplification of A' (mostly the input variables) *)
val IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON_def = Define
   `IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON A A' f =
     (!i. i IN SEMI_AUTOMATON_USED_INPUT_VARS A' ==>
          f i NOTIN (A'.S UNION SEMI_AUTOMATON_USED_INPUT_VARS A' UNION
                     IMAGE f (SEMI_AUTOMATON_USED_INPUT_VARS A' DIFF {i}))) /\
     (A = symbolic_semi_automaton
            (A'.S UNION (IMAGE f (SEMI_AUTOMATON_USED_INPUT_VARS A')))
            (P_VAR_RENAMING (\x. if (x IN A'.S) then x else f x) A'.S0)
            (XP_AND((XP_VAR_RENAMING (\x. if (x IN A'.S) then x else f x) A'.R),
                    XP_BIGAND (SET_TO_LIST (IMAGE (\i. XP_EQUIV(XP_PROP (f i), XP_PROP i))
                                            (SEMI_AUTOMATON_USED_INPUT_VARS A'))))))`;
(* product = synchoronous composition *)
val PRODUCT_SEMI_AUTOMATON_def = Define
   `PRODUCT_SEMI_AUTOMATON (symbolic_semi_automaton S_1 S0_1 R_1)
                           (symbolic_semi_automaton S_2 S0_2 R_2) =
      symbolic_semi_automaton (S_1 UNION S_2) (P_AND(S0_1, S0_2)) (XP_AND(R_1, R_2))`;

Theorem PRODUCT_SEMI_AUTOMATON_THM :
    !A B C. (PRODUCT_SEMI_AUTOMATON A B = C) <=> (C.S  = (A.S UNION B.S)) /\
                                                 (C.S0 = (P_AND(A.S0, B.S0))) /\
                                                 (C.R  = (XP_AND(A.R, B.R)))
Proof
    Cases_on `A` >> Cases_on `B` >> Cases_on `C`
 >> EVAL_TAC >> PROVE_TAC []
QED

Theorem PRODUCT_SEMI_AUTOMATON_REWRITES :
    !A B. ((PRODUCT_SEMI_AUTOMATON A B).S  = (A.S UNION B.S)) /\
          ((PRODUCT_SEMI_AUTOMATON A B).S0 = (P_AND(A.S0,B.S0))) /\
          ((PRODUCT_SEMI_AUTOMATON A B).R  = (XP_AND(A.R, B.R)))
Proof
    PROVE_TAC [PRODUCT_SEMI_AUTOMATON_THM]
QED

(* empty semi automaton (accepting all input traces) *)
val ID_SEMI_AUTOMATON_def = Define
   `ID_SEMI_AUTOMATON = symbolic_semi_automaton EMPTY P_TRUE XP_TRUE`;

Theorem ID_SEMI_AUTOMATON_RUN :
    !i w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON ID_SEMI_AUTOMATON i w <=> (w = EMPTY_PATH)
Proof
    EVAL_TAC >> PROVE_TAC [SUBSET_EMPTY]
QED

Theorem ID_SEMI_AUTOMATON_REWRITES :
    (ID_SEMI_AUTOMATON.S  = EMPTY) /\
    (ID_SEMI_AUTOMATON.S0 = P_TRUE) /\
    (ID_SEMI_AUTOMATON.R  = XP_TRUE)
Proof
    EVAL_TAC
QED

Theorem SYMBOLIC_SEMI_AUTOMATON___REWRITE :
    !A. symbolic_semi_automaton A.S A.S0 A.R = A
Proof
    Cases_on `A` >> EVAL_TAC
QED

Theorem FINITE___SEMI_AUTOMATON_USED_INPUT_VARS :
    !A. FINITE (SEMI_AUTOMATON_USED_INPUT_VARS A)
Proof
    Cases_on `A`
 >> REWRITE_TAC [SEMI_AUTOMATON_USED_INPUT_VARS_def]
 >> METIS_TAC [FINITE___P_USED_VARS, FINITE___XP_USED_VARS, FINITE_UNION, FINITE_DIFF]
QED

Theorem SEMI_AUTOMATON_VAR_RENAMING___USED_VARS :
    !A f. SEMI_AUTOMATON_USED_VARS (SEMI_AUTOMATON_VAR_RENAMING f A) =
          IMAGE f (SEMI_AUTOMATON_USED_VARS A)
Proof
    Cases_on `A`
 >> REWRITE_TAC [SEMI_AUTOMATON_USED_VARS_def, SEMI_AUTOMATON_USED_INPUT_VARS_def,
                 SEMI_AUTOMATON_VAR_RENAMING_def,
                 symbolic_semi_automaton_REWRITES]
 >> SIMP_TAC std_ss [DIFF_UNION_ELIM]
 >> REWRITE_TAC [IMAGE_UNION, P_VAR_RENAMING___USED_VARS, XP_VAR_RENAMING___USED_VARS]
QED

Theorem SEMI_AUTOMATON_VAR_RENAMING___USED_INPUT_VARS :
    !A f. INJ f (SEMI_AUTOMATON_USED_VARS A) UNIV ==>
         (SEMI_AUTOMATON_USED_INPUT_VARS (SEMI_AUTOMATON_VAR_RENAMING f A) =
         (IMAGE f (SEMI_AUTOMATON_USED_INPUT_VARS A)))
Proof
    Cases_on `A`
 >> REWRITE_TAC [SEMI_AUTOMATON_USED_INPUT_VARS_def, SEMI_AUTOMATON_VAR_RENAMING_def,
                 SEMI_AUTOMATON_USED_VARS_def, DIFF_UNION_ELIM,
                 symbolic_semi_automaton_REWRITES,
                 P_VAR_RENAMING___USED_VARS, XP_VAR_RENAMING___USED_VARS]
 >> METIS_TAC [IMAGE_UNION, IMAGE_DIFF]
QED

(* for total automata (at least one next state), there exist a transition function
   which picks one next state given the last state and inputs.
 *)
Theorem TOTAL_SYMBOLIC_SEMI_AUTOMATON_TRANS_FUNC :
    !A. IS_TOTAL_SYMBOLIC_SEMI_AUTOMATON A ==>
        ?R_FUNC. !s1 s2 i1 i2. (R_FUNC s1 i1 i2 = s2) ==>
                               s2 SUBSET A.S /\ IS_TRANSITION A s1 i1 s2 i2
Proof
    SIMP_TAC std_ss [IS_TOTAL_SYMBOLIC_SEMI_AUTOMATON_def]
 >> rpt STRIP_TAC
 >> ASSUME_TAC
      (SKOLEM_CONV ``!s1 i1 i2. ?s2. s2 SUBSET A.S /\ IS_TRANSITION A s1 i1 s2 i2``)
 >> PROVE_TAC []
QED

(* for deterministic automata (at most one next state), there exists a transition
   function such that, if a transition exists, it picks that exact next state.
 *)
Theorem DET_SYMBOLIC_SEMI_AUTOMATON_TRANS_FUNC :
    !A. IS_DET_SYMBOLIC_SEMI_AUTOMATON A ==>
        ?R_FUNC. !s1 s2 i1 i2. s2 SUBSET A.S /\ IS_TRANSITION A s1 i1 s2 i2 ==>
                               (R_FUNC s1 i1 i2 = s2)
Proof
    SIMP_TAC std_ss [IS_DET_SYMBOLIC_SEMI_AUTOMATON_def, EXISTS_AT_MOST_ONE_def]
 >> rpt STRIP_TAC
 >> EXISTS_TAC ``\s1 i1 i2. @s2. (s2 SUBSET A.S /\ IS_TRANSITION A s1 i1 s2 i2)``
 >> SIMP_TAC std_ss []
 >> rpt STRIP_TAC
 >> SELECT_ELIM_TAC
 >> METIS_TAC []
QED

(* `==>` becomes `<=>` if the deterministic automata is also total *)
Theorem TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_TRANS_FUNC :
    !A. IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON A ==>
        ?R_FUNC. !s1 s2 i1 i2. s2 SUBSET A.S /\ IS_TRANSITION A s1 i1 s2 i2 <=>
                               (R_FUNC s1 i1 i2 = s2)
Proof
    SIMP_TAC std_ss [IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_THM]
 >> rpt STRIP_TAC
 >> ASSUME_TAC
      (SKOLEM_CONV ``!s1 i1 i2. ?s2. s2 SUBSET A.S /\ IS_TRANSITION A s1 i1 s2 i2``)
 >> `?f. !s1 i1 i2. (f s1 i1 i2) SUBSET A.S /\
                    IS_TRANSITION A s1 i1 (f s1 i1 i2) i2` by PROVE_TAC []
 >> EXISTS_TAC ``f:'a set -> 'a set -> 'a set -> 'a set``
 >> METIS_TAC []
QED

Theorem DET_SYMBOLIC_SEMI_AUTOMATON_EXISTS_AT_MOST_ONE_RUN :
    !A i. IS_DET_SYMBOLIC_SEMI_AUTOMATON A ==>
          EXISTS_AT_MOST_ONE w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w
Proof
    SIMP_TAC std_ss [IS_DET_SYMBOLIC_SEMI_AUTOMATON_def, EXISTS_AT_MOST_ONE_def,
                     IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     PATH_SUBSET_def, INPUT_RUN_PATH_UNION_def]
 >> rpt STRIP_TAC
 >> ONCE_REWRITE_TAC [FUN_EQ_THM]
 >> Induct_on `x'`
 >> PROVE_TAC []
QED

Theorem TOTAL_SYMBOLIC_SEMI_AUTOMATON_EXISTS_RUN :
    !A i. IS_TOTAL_SYMBOLIC_SEMI_AUTOMATON A ==>
          ?w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w
Proof
    SIMP_TAC std_ss [IS_TOTAL_SYMBOLIC_SEMI_AUTOMATON_def, EXISTS_AT_MOST_ONE_def,
                     IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     PATH_SUBSET_def, INPUT_RUN_PATH_UNION_def]
 >> rpt STRIP_TAC
 >> `?R_FUNC. !s1 s2 i1 i2. (s2 = R_FUNC s1 i1 i2) ==>
                            s2 SUBSET A.S /\ IS_TRANSITION A s1 i1 s2 i2`
       by METIS_TAC [DET_SYMBOLIC_SEMI_AUTOMATON_TRANS_FUNC]
 >> `?s. s SUBSET A.S /\ P_SEM (INPUT_RUN_STATE_UNION A (i 0) s) A.S0` by PROVE_TAC []
 >> `?f:num -> 'a set -> 'a set. f= (\n s. R_FUNC s (i n) (i (SUC n)))` by METIS_TAC []
 >> `?t. (t 0 = s) /\ !n. t (SUC n) = f n (t n)` by METIS_TAC [num_Axiom]
 >> EXISTS_TAC ``t:num->'a set``
 >> rpt STRIP_TAC
 >| [ Cases_on `n` >> PROVE_TAC [],
      ASM_SIMP_TAC std_ss [],
      METIS_TAC[] ]
QED

Theorem TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_UNIQUE_RUN :
    !A i. IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON A ==>
          ?!w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w
Proof
    SIMP_TAC std_ss [IS_TOTAL_DET_SYMBOLIC_SEMI_AUTOMATON_def, EXISTS_UNIQUE_DEF]
 >> rpt STRIP_TAC
 >| [ PROVE_TAC [TOTAL_SYMBOLIC_SEMI_AUTOMATON_EXISTS_RUN],
      METIS_TAC [DET_SYMBOLIC_SEMI_AUTOMATON_EXISTS_AT_MOST_ONE_RUN,
                 EXISTS_AT_MOST_ONE_def] ]
QED

Theorem PRODUCT_SEMI_AUTOMATON_COMM_RUN :
    !A B v w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (PRODUCT_SEMI_AUTOMATON A B) v w =
              IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (PRODUCT_SEMI_AUTOMATON B A) v w
Proof
    Cases_on `A` >> Cases_on `B`
 >> SIMP_TAC std_ss [PRODUCT_SEMI_AUTOMATON_def,
                     IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, PATH_SUBSET_def,
                     INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
                     symbolic_semi_automaton_REWRITES,
                     UNION_COMM, P_SEM_def, IS_TRANSITION_def, XP_SEM_def]
 >> PROVE_TAC []
QED

(* symbolic run of product semi-automaton requires disjointness of all vars *)
Theorem PRODUCT_SEMI_AUTOMATON_RUN :
    !A1 A2. DISJOINT A1.S A2.S /\
            DISJOINT A1.S (SEMI_AUTOMATON_USED_INPUT_VARS A2) /\
            DISJOINT A2.S (SEMI_AUTOMATON_USED_INPUT_VARS A1) ==>
           !i w1 w2. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A1 i w1 /\
                     IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A2 i w2 ==>
                     IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON
                       (PRODUCT_SEMI_AUTOMATON A1 A2) i (PATH_UNION w1 w2)
Proof
    SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     SEMI_AUTOMATON_USED_INPUT_VARS_def,
                     INPUT_RUN_PATH_UNION_def, PATH_UNION_def,
                     INPUT_RUN_STATE_UNION_def, PRODUCT_SEMI_AUTOMATON_REWRITES]
 >> rpt (rpt GEN_TAC >> DISCH_THEN STRIP_ASSUME_TAC)
 >> SUBGOAL_TAC
      `!n. ((w1 n UNION w2 n UNION (i n DIFF (A1.S UNION A2.S))) INTER (COMPL A2.S) =
            (w1 n UNION (i n DIFF A1.S)) INTER (COMPL A2.S)) /\
           ((w1 n UNION w2 n UNION (i n DIFF (A1.S UNION A2.S))) INTER (COMPL A1.S) =
            (w2 n UNION (i n DIFF A2.S)) INTER (COMPL A1.S))`
 >- (SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF] \\
     FULL_SIMP_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
                           IN_UNION, IN_DIFF, PATH_SUBSET_def] \\
     rpt STRIP_TAC >> rpt BOOL_EQ_STRIP_TAC >> PROVE_TAC [])
 >> rpt STRIP_TAC
 >| [ (* goal 1 (of 3) *)
      FULL_SIMP_TAC std_ss [PATH_SUBSET_def, PRODUCT_SEMI_AUTOMATON_REWRITES,
                            UNION_SUBSET] \\
      PROVE_TAC [SUBSET_UNION, SUBSET_TRANS],
      (* goal 2 (of 3) *)
      SIMP_TAC std_ss [P_SEM_def] THEN
      SUBGOAL_TAC `(P_USED_VARS A1.S0) SUBSET (COMPL A2.S) /\
                   (P_USED_VARS A2.S0) SUBSET (COMPL A1.S)`
      >- (FULL_SIMP_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT,
                                SUBSET_DEF, IN_COMPL, IN_UNION, IN_DIFF] \\
          PROVE_TAC []) \\
      PROVE_TAC[P_USED_VARS_INTER_SUBSET_THM],
      (* goal 3 (of 3) *)
      FULL_SIMP_TAC std_ss [IS_TRANSITION_def, PRODUCT_SEMI_AUTOMATON_REWRITES, XP_SEM_def,
                            INPUT_RUN_STATE_UNION_def] \\
      SUBGOAL_TAC `(XP_USED_VARS A1.R SUBSET COMPL A2.S) /\
                   (XP_USED_VARS A2.R SUBSET COMPL A1.S)`
      >- (FULL_SIMP_TAC std_ss [GSYM SUBSET_COMPL_DISJOINT, SUBSET_DEF, IN_COMPL,
                                IN_UNION, IN_DIFF, XP_USED_VARS_def] \\
          PROVE_TAC []) \\
      PROVE_TAC [XP_USED_VARS_INTER_SUBSET_BOTH_THM] ]
QED

(* symbolic run of product semi-automaton implies run of the 1st semi-automaton *)
Theorem PRODUCT_SEMI_AUTOMATON_RUN2___FIRST :
    !A1 A2. DISJOINT A1.S A2.S /\
            DISJOINT A2.S (SEMI_AUTOMATON_USED_INPUT_VARS A1) ==>
           !i w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (PRODUCT_SEMI_AUTOMATON A1 A2) i w ==>
                 IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A1 i (PATH_RESTRICT w A1.S)
Proof
    SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     IS_TRANSITION_def, FORALL_AND_THM,
                     PRODUCT_SEMI_AUTOMATON_REWRITES, P_SEM_def, XP_SEM_def]
 >> rpt ((rpt GEN_TAC) THEN (DISCH_THEN STRIP_ASSUME_TAC))
 >> SUBGOAL_TAC
      `!n. (INPUT_RUN_STATE_UNION A1 (i n) (PATH_RESTRICT w A1.S n)) INTER (COMPL A2.S) =
           (INPUT_RUN_STATE_UNION (PRODUCT_SEMI_AUTOMATON A1 A2) (i n) (w n)) INTER (COMPL A2.S)`
 >- (SIMP_TAC std_ss [INPUT_RUN_STATE_UNION_def, EXTENSION, IN_INTER, IN_COMPL, IN_UNION,
                      PRODUCT_SEMI_AUTOMATON_REWRITES, IN_DIFF, PATH_RESTRICT_def, PATH_MAP_def] \\
     rpt GEN_TAC >> rpt BOOL_EQ_STRIP_TAC \\
     FULL_SIMP_TAC std_ss [PATH_SUBSET_def, GSYM SUBSET_COMPL_DISJOINT,
                           SUBSET_DEF, IN_UNION, IN_COMPL] \\
     PROVE_TAC [])
 >> rpt STRIP_TAC
 >| [ SIMP_TAC std_ss [PATH_SUBSET_def, PATH_RESTRICT_def, PATH_MAP_def, INTER_SUBSET],
      SUBGOAL_TAC `P_USED_VARS A1.S0 SUBSET COMPL A2.S`
      >- (FULL_SIMP_TAC std_ss [PATH_SUBSET_def, GSYM SUBSET_COMPL_DISJOINT,
                                SUBSET_DEF, IN_UNION, IN_COMPL,
                                SEMI_AUTOMATON_USED_INPUT_VARS_def, IN_UNION, IN_DIFF] \\
          PROVE_TAC []) \\
      PROVE_TAC [P_USED_VARS_INTER_SUBSET_THM],
      SUBGOAL_TAC `XP_USED_VARS A1.R SUBSET COMPL A2.S`
      >- (FULL_SIMP_TAC std_ss [PATH_SUBSET_def, GSYM SUBSET_COMPL_DISJOINT,
                                SUBSET_DEF, IN_UNION, IN_COMPL,
                                SEMI_AUTOMATON_USED_INPUT_VARS_def,
                                IN_UNION, IN_DIFF, XP_USED_VARS_def] \\
          PROVE_TAC []) \\
      PROVE_TAC [XP_USED_VARS_INTER_SUBSET_BOTH_THM] ]
QED

(* symbolic run of product semi-automaton implies run of the 2nd semi-automaton *)
Theorem PRODUCT_SEMI_AUTOMATON_RUN2___SECOND :
    !A1 A2. DISJOINT A1.S A2.S /\
            DISJOINT A1.S (SEMI_AUTOMATON_USED_INPUT_VARS A2) ==>
           !i w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (PRODUCT_SEMI_AUTOMATON A1 A2) i w ==>
                 IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A2 i (PATH_RESTRICT w A2.S)
Proof
    PROVE_TAC [PRODUCT_SEMI_AUTOMATON_RUN2___FIRST, DISJOINT_SYM,
               PRODUCT_SEMI_AUTOMATON_COMM_RUN]
QED

(* symbolic run restricted to a superset of input vars is still a symbolic run *)
Theorem SEMI_AUTOMATON_USED_INPUT_VARS_INTER_SUBSET_THM :
    !A S. (SEMI_AUTOMATON_USED_INPUT_VARS A) SUBSET S ==>
          !i w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w =
                IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A (PATH_RESTRICT i S) w
Proof
    SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     IS_TRANSITION_def, INPUT_RUN_PATH_UNION_def,
                     SEMI_AUTOMATON_USED_INPUT_VARS_def, DIFF_SUBSET_ELIM, UNION_SUBSET]
 >> rpt STRIP_TAC
 >> rpt CONJ_EQ_STRIP_TAC
 >> SUBGOAL_TAC
      `!n. (INPUT_RUN_STATE_UNION A (i n) (w n)) INTER (S UNION A.S) =
           (INPUT_RUN_STATE_UNION A (PATH_RESTRICT i S n) (w n)) INTER (S UNION A.S)`
 >- (SIMP_TAC std_ss [INPUT_RUN_STATE_UNION_def, EXTENSION, IN_INTER,
                      IN_UNION, IN_DIFF, PATH_RESTRICT_def, PATH_MAP_def] \\
     rpt GEN_TAC \\
     rpt BOOL_EQ_STRIP_TAC >> PROVE_TAC [])
 >> BINOP_TAC
 >| [ PROVE_TAC [P_USED_VARS_INTER_SUBSET_THM],
      PROVE_TAC [XP_USED_VARS_INTER_SUBSET_BOTH_THM] ]
QED

(* special case: symbolic run restricted to input vars is still a symbolic run *)
Theorem SEMI_AUTOMATON_USED_INPUT_VARS_INTER_THM :
    !A i w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w =
            IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A
              (PATH_RESTRICT i (SEMI_AUTOMATON_USED_INPUT_VARS A)) w
Proof
    METIS_TAC [SEMI_AUTOMATON_USED_INPUT_VARS_INTER_SUBSET_THM, SUBSET_REFL]
QED

(* A = f(A') *)
Theorem IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON___RUN_INPUT_VARS :
    !A A' f w i. IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON A A' f /\
                 IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w ==>
       !i'. i' IN SEMI_AUTOMATON_USED_INPUT_VARS A' ==> !n. i' IN i n <=> f i' IN w n
Proof
    SIMP_TAC std_ss [IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON_def,
                     IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     IS_TRANSITION_def, INPUT_RUN_STATE_UNION_def,
                     INPUT_RUN_PATH_UNION_def,
                     symbolic_semi_automaton_REWRITES,
                     XP_SEM_THM, FORALL_AND_THM,
                     XP_BIGAND_SEM, IMAGE_FINITE,
                     FINITE___SEMI_AUTOMATON_USED_INPUT_VARS,
                     MEM_SET_TO_LIST, IN_IMAGE, IN_UNION,
                     GSYM LEFT_FORALL_IMP_THM, IN_DIFF, IN_SING]
 >> rpt STRIP_TAC
 >> SPECL_NO_ASSUM 1 [``n:num``, ``i':'a``]
 >> UNDISCH_HD_TAC
 >> ASM_SIMP_TAC std_ss []
 >> SUBGOAL_TAC `~(f i' IN i n /\
                   !x. f i' <> f x \/ x NOTIN SEMI_AUTOMATON_USED_INPUT_VARS A')`
 >- METIS_TAC []
 >> SUBGOAL_TAC `~(i' IN w n) /\
                 (i' NOTIN A'.S /\
                  !x. i' <> f x \/ x NOTIN SEMI_AUTOMATON_USED_INPUT_VARS A')`
 >- (WEAKEN_HD_TAC \\
     FULL_SIMP_TAC std_ss [SEMI_AUTOMATON_USED_INPUT_VARS_def, IN_DIFF,
                           PATH_SUBSET_def, SUBSET_DEF, IN_UNION, IN_IMAGE] \\
     METIS_TAC [])
 >> ASM_SIMP_TAC std_ss []
QED

Theorem IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON___RUNS :
    !A A' f. IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON A A' f ==>
             IS_SIMPLE_SYMBOLIC_SEMI_AUTOMATON A /\
             !w i. PATH_SUBSET w A'.S ==>
                  (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i
                    (\n. w n UNION
                         IMAGE f (i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A')) =
                   IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A' i w)
Proof
    rpt GEN_TAC >> DISCH_TAC
 >> LEFT_CONJ_TAC
 >| [ FULL_SIMP_TAC std_ss
                       [IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON_def,
                        IS_SIMPLE_SYMBOLIC_SEMI_AUTOMATON_def,
                        IN_UNION, IN_IMAGE,
                        symbolic_semi_automaton_REWRITES,
                        P_VAR_RENAMING___USED_VARS, SUBSET_DEF,
                        XP_VAR_RENAMING___USED_X_VARS,
                        XP_BIGAND___XP_USED_VARS,
                        XP_USED_VARS_EVAL, MEM_MAP,
                        IN_LIST_BIGUNION,
                        IMAGE_FINITE,
                        FINITE___SEMI_AUTOMATON_USED_INPUT_VARS,
                        MEM_SET_TO_LIST,
                        GSYM LEFT_EXISTS_AND_THM, GSYM EXISTS_OR_THM,
                        GSYM LEFT_FORALL_IMP_THM,
                        NOT_IN_EMPTY] \\
      rpt STRIP_TAC >| (* 2 subgoals *)
      [ Cases_on `x' IN A'.S` THEN
        ASM_SIMP_TAC std_ss [SEMI_AUTOMATON_USED_INPUT_VARS_def,
                             IN_UNION, IN_DIFF] THEN
        PROVE_TAC [],

        Cases_on `i IN A'.S` \\
        FULL_SIMP_TAC std_ss [SEMI_AUTOMATON_USED_INPUT_VARS_def,
                              IN_UNION, IN_DIFF, XP_USED_VARS_def] \\
        PROVE_TAC [] ],

    ASM_SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SIMPLE_SEMI_AUTOMATON_THM] THEN
    SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                    IS_SYMBOLIC_RUN_THROUGH_SIMPLE_SEMI_AUTOMATON_def] THEN
    rpt STRIP_TAC THEN
    FULL_SIMP_TAC std_ss [IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON_def,
                          symbolic_semi_automaton_REWRITES, XP_SEM_THM,
                          FORALL_AND_THM] THEN
    MATCH_MP_TAC (prove(``!A A' B B' C. ((C /\ D) /\ ((A /\ B) = (A'/\ B'))) ==>
                          ((C /\ A /\ B /\ D) = (A' /\ B'))``, METIS_TAC[])) THEN
    rpt STRIP_TAC THENL [
      FULL_SIMP_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF, IN_UNION] THEN
      rpt STRIP_TAC THENL [
        METIS_TAC[],
        METIS_TAC[IMAGE_INTER, SUBSET_DEF, IN_INTER]
      ],

      FULL_SIMP_TAC std_ss [XP_BIGAND_SEM,
                            FINITE___SEMI_AUTOMATON_USED_INPUT_VARS,
                            MEM_SET_TO_LIST, IMAGE_FINITE, IN_IMAGE,
                            GSYM LEFT_FORALL_IMP_THM, XP_SEM_THM,
                            IN_UNION, IN_INTER, IN_DIFF, IN_SING,
                            PATH_SUBSET_def, SUBSET_DEF,
                            SEMI_AUTOMATON_USED_INPUT_VARS_def
                          ] THEN
      METIS_TAC[],

    SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def,
                      INPUT_RUN_STATE_UNION_def,
                      IS_TRANSITION_def] THEN
    `?f'. (\x. (if x IN A'.S then x else f x)) = f'` by METIS_TAC[] THEN
    SUBGOAL_TAC `!n. (w n UNION IMAGE f (i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A')) =
                      IMAGE f' (w n UNION (i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A'))` THEN1 (
      ASM_SIMP_TAC std_ss [EXTENSION, IN_UNION, IMAGE_UNION] THEN
      rpt STRIP_TAC THEN
      BINOP_TAC THENL [
        GSYM_NO_TAC 1 (*Def f'*) THEN
        FULL_SIMP_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF, IN_IMAGE] THEN
        METIS_TAC[],

        SIMP_TAC std_ss [IN_IMAGE, IN_INTER,
            SEMI_AUTOMATON_USED_INPUT_VARS_def, IN_UNION, IN_DIFF] THEN
        EXISTS_EQ_STRIP_TAC THEN
        rpt BOOL_EQ_STRIP_TAC THEN
        METIS_TAC[]
      ]
    ) THEN
    SUBGOAL_TAC `INJ f' (SEMI_AUTOMATON_USED_VARS A') UNIV` THEN1 (
      SIMP_ALL_TAC std_ss [INJ_DEF, IN_UNIV, SEMI_AUTOMATON_USED_VARS_def,
        SEMI_AUTOMATON_USED_INPUT_VARS_def, IN_UNION, IN_DIFF, IN_IMAGE, IN_SING] THEN
      METIS_TAC[]
    ) THEN

    SIMP_ALL_TAC std_ss [PATH_SUBSET_def, SUBSET_DEF] THEN
    BINOP_TAC THENL [
        SUBGOAL_TAC `P_SEM (IMAGE f' (w 0 UNION i 0 INTER SEMI_AUTOMATON_USED_INPUT_VARS A'))
            (P_VAR_RENAMING f' A'.S0) = P_SEM (w 0 UNION i 0 INTER SEMI_AUTOMATON_USED_INPUT_VARS A') A'.S0` THEN1 (
            SUBGOAL_TAC `(w 0 UNION i 0 INTER SEMI_AUTOMATON_USED_INPUT_VARS A') UNION (P_USED_VARS A'.S0) SUBSET
                          (SEMI_AUTOMATON_USED_VARS A')` THEN1 (
              FULL_SIMP_TAC std_ss [SEMI_AUTOMATON_USED_VARS_def, SUBSET_DEF, IN_UNION,
                                    IN_INTER, SEMI_AUTOMATON_USED_INPUT_VARS_def,
                                    IN_DIFF, PATH_SUBSET_def] THEN
              METIS_TAC[]
            ) THEN
            METIS_TAC[INJ_SUBSET_DOMAIN, P_SEM___VAR_RENAMING]
        ) THEN
        FULL_SIMP_TAC std_ss [] THEN
        ONCE_REWRITE_TAC [P_USED_VARS_INTER_THM] THEN
        MK_COMB_TAC THEN SIMP_TAC std_ss [] THEN
        MK_COMB_TAC THEN SIMP_TAC std_ss [] THEN
        SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF,
                        SEMI_AUTOMATON_USED_INPUT_VARS_def] THEN
        METIS_TAC[],

        ASM_SIMP_TAC std_ss [] THEN
        FORALL_EQ_STRIP_TAC THEN
        SUBGOAL_TAC `XP_SEM (XP_VAR_RENAMING f' A'.R)
                      (IMAGE f'
                        (w n UNION i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A') UNION
                      (i n DIFF (A'.S UNION IMAGE f (SEMI_AUTOMATON_USED_INPUT_VARS A'))),
                      IMAGE f'
                        (w (SUC n) UNION
                          i (SUC n) INTER SEMI_AUTOMATON_USED_INPUT_VARS A')) =
                    XP_SEM (XP_VAR_RENAMING f' A'.R)
                      (IMAGE f'
                        (w n UNION i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A'),
                      IMAGE f'
                        (w (SUC n) UNION
                          i (SUC n) INTER SEMI_AUTOMATON_USED_INPUT_VARS A'))` THEN1 (
          SUBGOAL_TAC `XP_USED_CURRENT_VARS (XP_VAR_RENAMING f' A'.R) SUBSET
                      (A'.S UNION IMAGE f (SEMI_AUTOMATON_USED_INPUT_VARS A'))` THEN1 (
            SIMP_TAC std_ss [XP_VAR_RENAMING___USED_CURRENT_VARS,
                            SUBSET_DEF, IN_UNION,
                            SEMI_AUTOMATON_USED_INPUT_VARS_def,
                            IN_IMAGE, IN_DIFF, IN_UNION,
                            XP_USED_VARS_def] THEN
            METIS_TAC[]
          ) THEN
          SUBGOAL_TAC `!S1 S2 S3 S4. (S1 UNION (S2 DIFF S3)) INTER S3 =
                                  (S1 INTER S3)` THEN1 (
            SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF] THEN
            PROVE_TAC[]
          ) THEN
          METIS_TAC[XP_USED_VARS_INTER_SUBSET_THM]
        ) THEN
        ASM_SIMP_TAC std_ss [] THEN WEAKEN_HD_TAC THEN

        SUBGOAL_TAC ` XP_SEM (XP_VAR_RENAMING f' A'.R)
                        (IMAGE f' (w n UNION i n INTER  SEMI_AUTOMATON_USED_INPUT_VARS A'),
                        IMAGE f' (w (SUC n) UNION i (SUC n) INTER SEMI_AUTOMATON_USED_INPUT_VARS A')) =
                      XP_SEM A'.R
                        (w n UNION i n INTER  SEMI_AUTOMATON_USED_INPUT_VARS A',
                        w (SUC n) UNION i (SUC n) INTER SEMI_AUTOMATON_USED_INPUT_VARS A')` THEN1 (
          MATCH_MP_TAC (GSYM XP_SEM___VAR_RENAMING) THEN
          UNDISCH_HD_TAC (*INJ f'*) THEN
          SIMP_TAC std_ss [] THEN
          MATCH_MP_TAC (REWRITE_RULE [
            prove (``!t1 t2 t3. (t1 /\ t2 ==> t3) = (t2 ==> t1 ==> t3)``, PROVE_TAC[])] INJ_SUBSET_DOMAIN) THEN
          FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, IN_INTER, SEMI_AUTOMATON_USED_VARS_def,
            PATH_SUBSET_def, SEMI_AUTOMATON_USED_INPUT_VARS_def, IN_DIFF] THEN
          METIS_TAC[]
        ) THEN

        FULL_SIMP_TAC std_ss [] THEN
        ONCE_REWRITE_TAC[XP_USED_VARS_INTER_THM] THEN
        MK_COMB_TAC THEN SIMP_TAC std_ss [PAIR_EQ] THEN
        SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF,
                        SEMI_AUTOMATON_USED_INPUT_VARS_def,
                        XP_USED_VARS_def] THEN
        METIS_TAC[]
      ]
    ]
  ]
QED

val IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON___RUNS2 =
 store_thm
  ("IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON___RUNS2",

    ``!A A' f. IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON A A' f ==>
        !w i. ((IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w) =
               (PATH_SUBSET w (A'.S UNION IMAGE f (SEMI_AUTOMATON_USED_INPUT_VARS A')) /\
                IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A' i (PATH_RESTRICT w A'.S) /\
                (!i'. (i' IN SEMI_AUTOMATON_USED_INPUT_VARS A') ==>
                      (!n. (i' IN i n) = (f i' IN w n)))))``,

    rpt STRIP_TAC THEN EQ_TAC THENL [
      STRIP_TAC THEN LEFT_CONJ_TAC THENL [
        SIMP_ALL_TAC std_ss [IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON_def,
          IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def] THEN
        UNDISCH_HD_TAC (*PATH_SUBSET w A.S*) THEN
        ASM_SIMP_TAC std_ss [symbolic_semi_automaton_REWRITES],


        REVERSE RIGHT_CONJ_TAC THEN1 (
          METIS_TAC[IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON___RUN_INPUT_VARS]
        ) THEN

        MP_TAC (Q.SPECL [`A`, `A'`, `f`] (GSYM IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON___RUNS)) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        Q.PAT_X_ASSUM `!w i. _` (MP_TAC o Q.SPECL [`PATH_RESTRICT w A'.S`, `i`]) THEN
        ASM_SIMP_TAC std_ss [PATH_SUBSET_RESTRICT] THEN
        DISCH_THEN (K ALL_TAC) THEN


        `(\n. PATH_RESTRICT w A'.S n UNION
              IMAGE f (i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A')) = w` suffices_by
           (DISCH_TAC >> ASM_REWRITE_TAC[]) THEN

        ONCE_REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
        ONCE_REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN

        SIMP_ALL_TAC std_ss [PATH_SUBSET_def, PATH_RESTRICT_def, IN_UNION, IN_IMAGE,
          SUBSET_DEF, PATH_MAP_def, IN_INTER] THEN
        METIS_TAC[]
      ],


      STRIP_TAC THEN
      ASSUME_TAC (GSYM IS_SIMPLIFIED_SYMBOLIC_SEMI_AUTOMATON___RUNS) THEN
      Q_SPECL_NO_ASSUM 0 [`A`, `A'`, `f`] THEN
      PROVE_CONDITION_NO_ASSUM 0 THEN1 ASM_REWRITE_TAC[] THEN
      CLEAN_ASSUMPTIONS_TAC THEN
      Q_SPECL_NO_ASSUM 1 [`PATH_RESTRICT w A'.S`, `i`] THEN
      PROVE_CONDITION_NO_ASSUM 0 THEN1 ASM_SIMP_TAC std_ss [PATH_RESTRICT_def, PATH_MAP_def, INTER_SUBSET, PATH_SUBSET_def] THEN

      REMAINS_TAC `(\n.
        PATH_RESTRICT w A'.S n UNION
        IMAGE f (i n INTER SEMI_AUTOMATON_USED_INPUT_VARS A')) = w` THEN1 (
        FULL_SIMP_TAC std_ss []
      ) THEN

      ONCE_REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      ONCE_REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN

      SIMP_ALL_TAC std_ss [PATH_SUBSET_def, PATH_RESTRICT_def, IN_UNION, IN_IMAGE,
        SUBSET_DEF, PATH_MAP_def, IN_INTER] THEN
      METIS_TAC[]
  ]);

Theorem INPUT_RUN_PATH_UNION___SPLIT :
    !A p. INPUT_RUN_PATH_UNION A p (PATH_RESTRICT p A.S) = p
Proof
    rpt GEN_TAC
 >> ONCE_REWRITE_TAC [FUN_EQ_THM]
 >> SIMP_TAC std_ss [INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
                     PATH_RESTRICT_def, EXTENSION, IN_UNION, PATH_MAP_def,
                     IN_INTER, IN_DIFF]
 >> PROVE_TAC []
QED

Theorem INPUT_RUN_STATE_UNION___SPLIT :
    !A s. INPUT_RUN_STATE_UNION A s (s INTER A.S) = s
Proof
    rpt GEN_TAC
 >> SIMP_TAC std_ss [INPUT_RUN_STATE_UNION_def, PATH_RESTRICT_def, EXTENSION,
                     IN_UNION, PATH_MAP_def, IN_INTER, IN_DIFF]
 >> PROVE_TAC []
QED

Theorem IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON___SPLIT :
    !S S0 R i w.
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S S0 R) i w <=>
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S S0 XP_TRUE) i w /\
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S P_TRUE R) i w
Proof
    SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     symbolic_semi_automaton_REWRITES, P_SEM_def,
                     IS_TRANSITION_def, XP_SEM_def,
                     INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def]
 >> PROVE_TAC []
QED

Theorem IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON___R_AND_SPLIT :
    !S S0 R1 R2 i w.
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S S0 (XP_AND(R1, R2))) i w <=>
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S S0 R1) i w /\
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S S0 R2) i w
Proof
    SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     symbolic_semi_automaton_REWRITES, P_SEM_def, IS_TRANSITION_def,
                     XP_SEM_def, INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def]
 >> PROVE_TAC []
QED

Theorem IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON___R_AND_SPLIT_MINIMAL :
    !S S0 R1 R2 i w.
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S S0 (XP_AND(R1, R2))) i w <=>
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S S0 XP_TRUE) i w /\
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S P_TRUE R1) i w /\
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S P_TRUE R2) i w
Proof
    METIS_TAC [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON___R_AND_SPLIT,
               IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON___SPLIT]
QED

Theorem IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON___S0_AND_SPLIT :
    !S S0_1 S0_2 R i w.
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S (P_AND(S0_1, S0_2)) R) i w
       <=>
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S S0_1 R) i w /\
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S S0_2 R) i w
Proof
    SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     symbolic_semi_automaton_REWRITES, P_SEM_def, IS_TRANSITION_def,
                     XP_SEM_def, INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def]
 >> METIS_TAC []
QED

Theorem IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON___S0_AND_SPLIT_MINIMAL :
    !S S0_1 S0_2 R i w.
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S (P_AND(S0_1, S0_2)) R) i w
       <=>
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S P_TRUE R) i w /\
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S S0_1 XP_TRUE) i w /\
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S S0_2 XP_TRUE) i w
Proof
    SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     symbolic_semi_automaton_REWRITES, P_SEM_def, IS_TRANSITION_def,
                     XP_SEM_def, INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def]
 >> METIS_TAC []
QED

Theorem IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON___S_EXTENSION :
    !S1 S2 S' S0 R i w.
       (S2 = S1 UNION S') /\ DISJOINT S' (P_USED_VARS S0 UNION XP_USED_VARS R) /\
        PATH_SUBSET w S2 ==>
       (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S2 S0 R) i w <=>
        IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (symbolic_semi_automaton S1 S0 R) i
          (PATH_RESTRICT w S1))
Proof
    SIMP_TAC std_ss [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def,
                     symbolic_semi_automaton_REWRITES, IS_TRANSITION_def,
                     INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
                     PATH_SUBSET_def, PATH_RESTRICT_def, PATH_MAP_def, INTER_SUBSET,
                     DISJOINT_UNION_BOTH, GSYM SUBSET_COMPL_DISJOINT, UNION_SUBSET]
 >> rpt STRIP_TAC
 >> SUBGOAL_TAC `!n. (w n UNION (i n DIFF (S1 UNION S'))) INTER COMPL S' =
                     (w n INTER S1 UNION (i n DIFF S1)) INTER COMPL S'`
 >- (FULL_SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_COMPL, IN_UNION, IN_DIFF, SUBSET_DEF] \\
     rpt STRIP_TAC \\
     rpt BOOL_EQ_STRIP_TAC >> PROVE_TAC [])
 >> PROVE_TAC [P_USED_VARS_INTER_SUBSET_THM, XP_USED_VARS_INTER_SUBSET_BOTH_THM]
QED

Theorem SEMI_AUTOMATON___VAR_RENAMING :
    !A v f w. INJ f ((PATH_USED_VARS v) UNION (PATH_USED_VARS w) UNION (SEMI_AUTOMATON_USED_VARS A))
                    UNIV ==>
      (IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A v w =
       IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON
         (SEMI_AUTOMATON_VAR_RENAMING f A) (PATH_VAR_RENAMING f v) (PATH_VAR_RENAMING f w))
Proof
    Cases_on `A`
 >> FULL_SIMP_TAC std_ss
      [IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON_def, IS_TRANSITION_def,
       INPUT_RUN_PATH_UNION_def, PATH_VAR_RENAMING_def, PATH_MAP_def,
       symbolic_semi_automaton_REWRITES,
       SEMI_AUTOMATON_VAR_RENAMING_def, INPUT_RUN_STATE_UNION_def,
       PATH_SUBSET_def, PATH_USED_VARS_def, SEMI_AUTOMATON_USED_VARS_def,
       INJ_DEF, IN_UNIV, IN_UNION, IN_BIGUNION, GSPECIFICATION,
       SEMI_AUTOMATON_USED_INPUT_VARS_def, IN_DIFF, GSYM RIGHT_EXISTS_AND_THM,
       GSYM EXISTS_OR_THM]
 >> rpt STRIP_TAC
 >> BINOP_TAC >| [ ALL_TAC, BINOP_TAC ]
 >| [ (* goal 1 (of 3) *)
      FORALL_EQ_STRIP_TAC THEN
      SIMP_TAC std_ss [IMAGE_DEF, SUBSET_DEF, GSPECIFICATION] THEN
      METIS_TAC[],
      (* goal 2 (of 3) *)
      SUBGOAL_TAC `INJ f' (v 0 UNION f) UNIV /\
                   INJ f' ((w 0 UNION (v 0 DIFF f)) UNION (P_USED_VARS p)) UNIV`
      >- (SIMP_TAC std_ss [INJ_DEF, IN_UNIV, IN_UNION, IN_DIFF] \\
          METIS_TAC []) \\
      FULL_SIMP_TAC std_ss [GSYM IMAGE_DIFF, GSYM IMAGE_UNION] \\
      PROVE_TAC[P_SEM___VAR_RENAMING],
      (* goal 3 (of 3) *)
      FORALL_EQ_STRIP_TAC \\
      SUBGOAL_TAC `!n. INJ f' (v n UNION f) UNIV /\
                       INJ f' ((w n UNION (v n DIFF f)) UNION
                               (w (SUC n) UNION (v (SUC n) DIFF f)) UNION
                               (XP_USED_VARS x)) UNIV`
      >- (SIMP_TAC std_ss [INJ_DEF, IN_UNIV, IN_UNION, IN_DIFF] \\
          METIS_TAC []) \\
      FULL_SIMP_TAC std_ss [GSYM IMAGE_DIFF, GSYM IMAGE_UNION] \\
      METIS_TAC [XP_SEM___VAR_RENAMING] ]
QED

Theorem SEMI_AUTOMATON___STATE_VAR_RENAMING :
    !A f. (INJ f UNIV UNIV) /\ (!x. x IN (SEMI_AUTOMATON_USED_INPUT_VARS A) ==> (f x = x)) ==>
          !i w. IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON A i w =
                IS_SYMBOLIC_RUN_THROUGH_SEMI_AUTOMATON (SEMI_AUTOMATON_VAR_RENAMING f A)
                  i (PATH_VAR_RENAMING f w)
Proof
    rpt STRIP_TAC
 >> SUBGOAL_TAC
      `((PATH_RESTRICT i (SEMI_AUTOMATON_USED_INPUT_VARS A)) =
        (PATH_RESTRICT (PATH_VAR_RENAMING f i) (SEMI_AUTOMATON_USED_INPUT_VARS A))) /\
       (SEMI_AUTOMATON_USED_INPUT_VARS (SEMI_AUTOMATON_VAR_RENAMING f A) =
        SEMI_AUTOMATON_USED_INPUT_VARS A)`
 >- (Cases_on `A` THEN
     SIMP_ALL_TAC std_ss
       [PATH_RESTRICT_def, PATH_MAP_def, SEMI_AUTOMATON_USED_INPUT_VARS_def,
        SEMI_AUTOMATON_VAR_RENAMING_def,
        symbolic_semi_automaton_REWRITES,
        P_VAR_RENAMING___USED_VARS, EXTENSION, IN_UNION, IN_DIFF,
        IN_IMAGE, XP_VAR_RENAMING___USED_VARS, INJ_DEF, IN_UNIV] \\
     rpt STRIP_TAC >|
     [ ONCE_REWRITE_TAC [FUN_EQ_THM] \\
       SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF, PATH_VAR_RENAMING_def,
                        PATH_MAP_def, IN_IMAGE] \\
       rpt GEN_TAC >> rpt BOOL_EQ_STRIP_TAC >> PROVE_TAC [],
       PROVE_TAC [] ])
 >> METIS_TAC [SEMI_AUTOMATON___VAR_RENAMING, INJ_SUBSET_DOMAIN, SUBSET_UNIV,
               SEMI_AUTOMATON_USED_INPUT_VARS_INTER_THM]
QED

Theorem P_SEM_AUTOMATON_RUN___STATE_VAR_RENAMING :
    !A p f. INJ f UNIV UNIV /\
            (!x. x IN (SEMI_AUTOMATON_USED_INPUT_VARS A UNION (P_USED_VARS p DIFF A.S)) ==> (f x = x)) ==>
      !i w t. (P_SEM (INPUT_RUN_PATH_UNION A i w t) p =
               P_SEM (INPUT_RUN_PATH_UNION (SEMI_AUTOMATON_VAR_RENAMING f A) i
                                           (PATH_VAR_RENAMING f w) t)
                     (P_VAR_RENAMING f p))
Proof
    rpt STRIP_TAC
 >> SIMP_ASSUMPTIONS_TAC std_ss [IN_UNION, IN_DIFF]
 >> `P_SEM (INPUT_RUN_PATH_UNION A i w t) p =
     P_SEM (IMAGE f (INPUT_RUN_PATH_UNION A i w t)) (P_VAR_RENAMING f p)`
      by METIS_TAC [P_SEM___VAR_RENAMING, INJ_SUBSET_DOMAIN, SUBSET_UNIV]
 >> ASM_REWRITE_TAC []
 >> `P_USED_VARS (P_VAR_RENAMING f p) = IMAGE f (P_USED_VARS p)`
      by METIS_TAC [P_VAR_RENAMING___USED_VARS]
 >> SUBGOAL_TAC `(IMAGE f (INPUT_RUN_PATH_UNION A i w t)) INTER (P_USED_VARS (P_VAR_RENAMING f p)) =
                 (INPUT_RUN_PATH_UNION (SEMI_AUTOMATON_VAR_RENAMING f A) i
                                          (PATH_VAR_RENAMING f w) t) INTER
                 (P_USED_VARS (P_VAR_RENAMING f p))`
 >- (ASM_SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_IMAGE] \\
     GEN_TAC >> CONJ_EQ_STRIP_TAC \\
     Cases_on `A` \\
     SIMP_ALL_TAC std_ss [IN_IMAGE, SEMI_AUTOMATON_VAR_RENAMING_def,
                          INPUT_RUN_PATH_UNION_def, INPUT_RUN_STATE_UNION_def,
                          PATH_VAR_RENAMING_def, symbolic_semi_automaton_REWRITES,
                          PATH_MAP_def, IN_UNION, IN_DIFF, INJ_DEF, IN_UNIV] \\
     METIS_TAC [])
 >> PROVE_TAC [P_USED_VARS_INTER_THM]
QED

Theorem TRANSITION_CURRENT_STATE_CLEANING :
    !A s1 i1 s2 i2. IS_TRANSITION A s1 i1 s2 i2 =
                    IS_TRANSITION A (s1 INTER A.S) (i1 UNION s1) s2 i2
Proof
    SIMP_TAC std_ss [IS_TRANSITION_def, INPUT_RUN_STATE_UNION_def]
 >> rpt STRIP_TAC
 >> REMAINS_TAC `s1 UNION (i1 DIFF A.S) = s1 INTER A.S UNION (i1 UNION s1 DIFF A.S)`
 >- ASM_REWRITE_TAC []
 >> SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF]
 >> PROVE_TAC []
QED

Theorem TRANSITION_NEXT_STATE_CLEANING :
    !A s1 i1 s2 i2. IS_TRANSITION A s1 i1 s2 i2 =
                    IS_TRANSITION A s1 i1 (s2 INTER A.S) (i2 UNION s2)
Proof
    SIMP_TAC std_ss [IS_TRANSITION_def, INPUT_RUN_STATE_UNION_def]
 >> rpt STRIP_TAC
 >> REMAINS_TAC `s2 UNION (i2 DIFF A.S) = s2 INTER A.S UNION (i2 UNION s2 DIFF A.S)`
 >- ASM_REWRITE_TAC []
 >> SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_UNION, IN_DIFF]
 >> PROVE_TAC []
QED

Theorem TRANSITION_STATE_CLEANING :
    !A s1 i1 s2 i2. IS_TRANSITION A s1 i1 s2 i2 =
                    IS_TRANSITION A (s1 INTER A.S) (i1 UNION s1) (s2 INTER A.S) (i2 UNION s2)
Proof
    PROVE_TAC [TRANSITION_CURRENT_STATE_CLEANING,
               TRANSITION_NEXT_STATE_CLEANING]
QED

val _ = export_theory ();
