

(*****************************************************************************)
(* Create "ModelTheory" containing definition of models for OBE semantics.   *)
(* PSL version 1.1                                                           *)
(*****************************************************************************)

(******************************************************************************
* A model is a quintuple (S,S0,R,P,L), represented as a record, where
* 
*  - S  : 'state                    is a set of states
*  - S0 : 'state -> bool            is a subset of S, the initial states
*  - R  : 'state # 'state -> bool   is a transition relation 
*  - P  : 'prop                     is a set of atomic proposition
*  - L  : 'state -> ('prop -> bool) maps each state to the 
*                                   set of propositions true in that state
* 
* N.B. terms that follow are not contrained to use type variables 'state and 
*      'prop, but may use 'a, 'b etc or whatever typechecking assigns.
******************************************************************************)

(******************************************************************************
* Load theory of syntax, paths and models
* (commented out for compilation)
******************************************************************************)
(*
quietdec := true;                         (* Switch off output               *)
loadPath                                  (* Add official-semantics to path  *)
 :=
 "../../path" :: !loadPath;
map load 
 ["pred_setLib","res_quanTools", "rich_listTheory", "pairLib",
  "FinitePathTheory", "PathTheory"];
open pred_setLib res_quanTools rich_listTheory pred_setTheory
     FinitePathTheory PathTheory pairLib;
quietdec := false;                        (* Restore output                  *)
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib pred_setLib 
     res_quanTools rich_listTheory pred_setTheory pairLib
     FinitePathTheory PathTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Start a new theory called ModelTheory
******************************************************************************)
val _ = new_theory "Model";

(******************************************************************************
* A simpset fragment to rewrite away quantifiers restricted with :: LESS
******************************************************************************)
val resq_SS =
 simpLib.merge_ss
  [res_quanTools.resq_SS,
   rewrites
    [LESS_def,LENGTH_def,IN_LESS,IN_LESSX]];

(******************************************************************************
* Stop ``S`` parsing to the S-combinator
******************************************************************************)
val _ = hide "S";

(******************************************************************************
* ``: ('state,'prop)model``
******************************************************************************)
val model_def =
 Hol_datatype
  `model = 
    <| S: 'state -> bool;
       S0:'state -> bool;
       R: 'state # 'state -> bool;
       P: 'prop -> bool;
       L: 'state -> ('prop -> bool) |>`;

val MODEL_def =
 Define
  `MODEL M =
    M.S0 SUBSET M.S /\
    (!s s'. (s,s') IN M.R ==> s IN M.S /\ s' IN M.S) /\
    (!s. s IN M.S ==> M.L s SUBSET M.P)`;

(******************************************************************************
* A useful special case (possibly the only one we'll need) is to identify 
* propositions with predicates on states, then we just need to specify the 
* set of initial states B:'state->bool and 
* transition relation R:'state#'state->bool, then:
* SIMPLE_MODEL B R : :('a, 'a -> bool) model
*******************************************************************************)
val SIMPLE_MODEL_def =
 Define
  `SIMPLE_MODEL (B:'state -> bool) (R:'state#'state->bool) = 
    <| S  := {s | T};
       S0 := B;
       R  := R; 
       P  := {p | T}; 
       L  := (\(s:'state). {p:'state -> bool | s IN p}) |>`;

val MODEL_SIMPLE_MODEL =
 store_thm
  ("MODEL_SIMPLE_MODEL",
   ``MODEL(SIMPLE_MODEL B R)``,
   RW_TAC list_ss [MODEL_def,SIMPLE_MODEL_def]
    THEN RW_TAC (srw_ss()) [SUBSET_UNIV]);

(******************************************************************************
* Product of two models
*   
*    (S1,S01,R1,P1,L1) || (S2,S02,R2,P2,L2)
*    =
*    (S1  x S2,     -- Cartesian product
*     S01 x S02,    -- Cartesian product
*     {((s1,s2),(s1,s2)) | R1(s1,s1') and R2(s2,s2')},
*     P1 U P2,      -- disjoint union
*     lambda (s1,s2) 
*       {p in (P1 U P2) | if (p in P1) then (p in L1 s1) else (p in L2 s2)}
*    )
******************************************************************************)
val MODEL_PROD_def =
 Define 
  `MODEL_PROD (M1:('state1, 'prop1) model) (M2:('state2, 'prop2) model) =
    <| S  := {(s1,s2) | s1 IN M1.S  /\ s2 IN M2.S};
       S0 := {(s1,s2) | s1 IN M1.S0 /\ s2 IN M2.S0};
       R  := {((s1,s2),(s1',s2')) | (s1,s1') IN M1.R /\ (s2,s2') IN M2.R};
       P  := {p | if ISL p then OUTL p IN M1.P else OUTR p IN M2.P};
       L  := \(s1,s2). 
              {p | if ISL p then OUTL p IN M1.L s1 else OUTR p IN M2.L s2} |>`;

val _ = set_fixity "||" (Infixl 650);
val _ = overload_on ("||", ``MODEL_PROD``);

val MODEL_MODEL_PROD =
 store_thm
  ("MODEL_MODEL_PROD",
   ``!M1 M2. MODEL M1 /\ MODEL M2 ==> MODEL(M1 || M2)``,
   RW_TAC list_ss [MODEL_def,MODEL_PROD_def]
    THEN FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF]
    THEN RW_TAC list_ss []
    THEN RES_TAC
    THEN FULL_SIMP_TAC list_ss []
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(GEN_BETA_RULE(el 4 thl)))
    THEN FULL_SIMP_TAC (srw_ss()) []
    THEN PROVE_TAC[]);

(******************************************************************************
* A letter is either TOP, or BOTTOM
* or a set of atomic propositions repersenting a state
******************************************************************************)
val letter_def =
 Hol_datatype
  `letter = TOP | BOTTOM | STATE of ('prop -> bool)`;

(*****************************************************************************)
(* ``L_SEM l p`` means proposition p is true with respect to letter l        *)
(*****************************************************************************)
val L_SEM_def =
 Define
  `(L_SEM TOP (p:'prop) = T)
   /\
   (L_SEM BOTTOM p = F)
   /\
   (L_SEM(STATE s) p = p IN s)`;

(*****************************************************************************)
(* FINITE_LETTER_IN p l iff p occurs in an element of l                      *)
(*****************************************************************************)
val FINITE_LETTER_IN_def =
 Define
  `FINITE_LETTER_IN p l = 
    ?i. i < LENGTH l /\ ?s. (EL i l = STATE s) /\ p IN s` ;

(*****************************************************************************)
(* INFINITE_LETTER_IN p f iff p occurs in an element of f                    *)
(*****************************************************************************)
val INFINITE_LETTER_IN_def =
 Define
  `INFINITE_LETTER_IN p f = 
    ?i s. (f i = STATE s) /\ p IN s` ;

(*****************************************************************************)
(* Conversion of a path to a model (Kripke structure)                        *)
(*****************************************************************************)
val PATH_TO_MODEL_def =
 Define
  `(PATH_TO_MODEL(FINITE l) = 
    <| S  := {n | n < LENGTH l};
       S0 := {0};
       R  := {(n,n') | n < LENGTH l /\ n' < LENGTH l /\ (n' = n+1)};
       P  := {p:'prop | FINITE_LETTER_IN p l};
       L  := \n. {p | n < LENGTH l /\ FINITE_LETTER_IN p l /\ L_SEM (EL n l) p} |>)
   /\
   (PATH_TO_MODEL(INFINITE f) = 
    <| S  := {n | T};
       S0 := {0};
       R  := {(n,n') | n' = n+1};
       P  := {p:'prop | INFINITE_LETTER_IN p f};
       L  := \n. {p | INFINITE_LETTER_IN p f /\ L_SEM (f n) p} |>)`;

val MODEL_PATH_TO_MODEL =
 store_thm
  ("MODEL_PATH_TO_MODEL",
   ``!p. 0 < LENGTH p ==>  MODEL(PATH_TO_MODEL p)``,
   GEN_TAC
    THEN Cases_on `p`
    THEN RW_TAC list_ss [SUBSET_DEF,MODEL_def,PATH_TO_MODEL_def]   
    THEN FULL_SIMP_TAC (srw_ss()) [SUBSET_UNIV,LENGTH_def,LS]);

(*****************************************************************************)
(* Definition of an automaton: ``: ('label,'state)automaton``                *)
(* (e.g. Clarke/Grumberg/Peled "Model Checking" Chapter 9)                   *)
(*****************************************************************************)
val automaton_def =
 Hol_datatype
  `automaton = 
    <| Sigma: 'label -> bool;
       Q:     'state -> bool;
       Delta: 'state # 'label # 'state -> bool;
       Q0:    'state -> bool;
       F:     'state -> bool |>`;

val AUTOMATON_def =
 Define
  `AUTOMATON A =
    A.Q0 SUBSET A.Q /\
    (!s a s'. (s,a,s') IN A.Delta ==> s IN A.Q /\ a IN A.Sigma /\ s' IN A.Q) /\
    A.F SUBSET A.Q`;

(*****************************************************************************)
(* Convert a model to an automaton                                           *)
(* (Clarke/Grumberg/Peled "Model Checking" 9.2)                              *)
(*****************************************************************************)
val MODEL_TO_AUTOMATON_def =
 Define
  `MODEL_TO_AUTOMATON (M:('state,'prop)model) =
    <| Sigma := {a | a SUBSET M.P};
       Q     := {SOME s : ('state)option | s IN M.S} UNION {NONE};
       Delta := {(SOME s, a, SOME s') | (s,s') IN M.R /\ (a = M.L s')}
                UNION
                {(NONE, a, SOME s) | s IN M.S0 /\ (a = M.L s)};
       Q0    := {NONE :  ('state)option};
       F     := {SOME s : ('state)option | s IN M.S} UNION {NONE} |>`;

val AUTOMATON_MODEL_TO_AUTOMATON =
 store_thm
  ("AUTOMATON_MODEL_TO_AUTOMATON",
   ``!M. MODEL M ==> AUTOMATON(MODEL_TO_AUTOMATON M)``,
   RW_TAC list_ss [MODEL_def,AUTOMATON_def,MODEL_TO_AUTOMATON_def]
    THEN FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF]
    THEN RW_TAC list_ss []
    THEN PROVE_TAC[]);

(*****************************************************************************)
(* Product of a model with an automaton                                      *)
(*                                                                           *)
(*  S is the cross product of the states of M with the states of A. That     *)
(*  is, the set of states (s,t) such that s is a state in M and t a state    *)
(*  in A. So is the set of states (s,t) such that s is in the initial        *)
(*  states of M and t is in the initial states of A. R((s,t),(s',t')) iff    *)
(*  (s,s') is in the relation of M, and (t,a,t') is in the relation of A,    *)
(*  where a is the labeling of s. P are the propositions of M and            *)
(*  L(s,t) = L(s).                                                           *)
(*****************************************************************************) 
val AUTOMATON_MODEL_PROD_def =
 Define 
  `AUTOMATON_MODEL_PROD 
    (A:('prop -> bool, 'state1) automaton) (M:('state2, 'prop) model) =
    <| S  := {(s,t) | s IN M.S  /\ t IN A.Q};
       S0 := {(s,t) | s IN M.S0 /\ t IN A.Q0};
       R  := {((s,t),(s',t')) | 
              ?a. (a = M.L s) /\ (s,s') IN M.R /\ (t,a,t') IN A.Delta};
       P  := M.P;
       L  := \(s,t). M.L s |>`;

val _ = overload_on ("||", ``AUTOMATON_MODEL_PROD``);

val MODEL_AUTOMATON_MODEL_PROD =
 store_thm
  ("MODEL_AUTOMATON_MODEL_PROD",
   ``!A M. AUTOMATON A /\ MODEL M ==> MODEL(A || M)``,
   RW_TAC list_ss [MODEL_def,AUTOMATON_def,AUTOMATON_MODEL_PROD_def]
    THEN FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF]
    THEN RW_TAC list_ss []
    THEN RES_TAC
    THEN FULL_SIMP_TAC list_ss []);

(*****************************************************************************)
(* Product of automata                                                       *)
(*****************************************************************************)
val AUTOMATON_PROD_def =
 Define
  `AUTOMATON_PROD
   (A1:('label1,'state1)automaton) (A2:('label2,'state2)automaton) =
    <| Sigma := {(a1,a2) | a1 IN A1.Sigma  /\ a2 IN A2.Sigma };
       Q     := {(q1,q2) | q1 IN A1.Q  /\ q2 IN A2.Q};
       Delta := {((q1,q2),(a1,a2),(q1',q2')) | 
                 (q1,a1,q1') IN A1.Delta /\ (q2,a2,q2') IN A2.Delta};
       Q0    := {(q1,q2) | q1 IN A1.Q0  /\ q2 IN A2.Q0};
       F     := {(q1,q2) | q1 IN A1.F  /\ q2 IN A2.F} |>`;

val _ = overload_on ("||", ``AUTOMATON_PROD``);

val AUTOMATON_AUTOMATON_PROD =
 store_thm
  ("AUTOMATON_AUTOMATON_PROD",
   ``!A1 A2. AUTOMATON A1 /\ AUTOMATON A2 ==> AUTOMATON(A1 || A2)``,
   RW_TAC list_ss [AUTOMATON_def,AUTOMATON_PROD_def]
    THEN FULL_SIMP_TAC (srw_ss()) [SUBSET_DEF]
    THEN RW_TAC list_ss []
    THEN PROVE_TAC[]);

(* Examples

SIMP_CONV (srw_ss()) [MODEL_TO_AUTOMATON_def,PATH_TO_MODEL_def]
``PATH_TO_MODEL(FINITE l)``;

SIMP_CONV (srw_ss()) [MODEL_TO_AUTOMATON_def,PATH_TO_MODEL_def]
``MODEL_TO_AUTOMATON(PATH_TO_MODEL(FINITE l))``;

SIMP_CONV (srw_ss()) 
  [MODEL_TO_AUTOMATON_def,PATH_TO_MODEL_def,MODEL_PROD_def]
  ``(PATH_TO_MODEL(FINITE l) || 
     <| S  := states;
        S0 := initial_states;
        R  := trans;
        P  := props;
        L  := val_fn |>)``;

SIMP_CONV (srw_ss()) 
  [MODEL_TO_AUTOMATON_def,PATH_TO_MODEL_def,MODEL_PROD_def]
  ``MODEL_TO_AUTOMATON
    (PATH_TO_MODEL(FINITE l) || 
     <| S  := states;
        S0 := initial_states;
        R  := trans;
        P  := props;
        L  := val_fn |>)``;

SIMP_CONV (srw_ss()) 
  [AUTOMATON_MODEL_PROD_def,SIMPLE_MODEL_def]
  ``<| Sigma := alphabet;
       Q     := states;
       Delta := delta;
       Q0    := initial_states;
       F     := final_states |>
    ||
    SIMPLE_MODEL initial_states (\(s,s'). ?a. delta(s,a,s'))``;

SIMP_CONV (srw_ss()) 
  [AUTOMATON_MODEL_PROD_def,SIMPLE_MODEL_def,MODEL_TO_AUTOMATON_def]
  ``MODEL_TO_AUTOMATON
     (<| Sigma := alphabet;
        Q     := states;
        Delta := delta;
        Q0    := initial_states;
        F     := final_states |>
     ||
     SIMPLE_MODEL initial_states (\(s,s'). ?a. delta(s,a,s')))``;

*)

(******************************************************************************
* PATH M s is true of path p iff p is a computation path of model M
******************************************************************************)
val PATH_def = 
 Define 
  `(PATH M s (FINITE l) = 
    (LENGTH l > 0) /\ (s = HD l) /\ s IN M.S /\
    (!n :: (LESS(LENGTH l - 1)). 
      EL n l IN M.S /\ EL (SUC n) l IN M.S /\ (EL n l, EL (SUC n) l) IN M.R) /\
    !s. ~((EL (LENGTH l - 1) l, s) IN M.R))
   /\
   (PATH M s (INFINITE f) = 
     (s = f 0) /\ !n. f n IN M.S /\ (f n, f(SUC n)) IN M.R)`;

(******************************************************************************
* LANGUAGE A p is true of path p iff p is a computation path of model M
******************************************************************************)
val LANGUAGE_def = 
 Define 
  `(LANGUAGE A (FINITE l) = 
    (LENGTH l > 0)                                                         /\
    EL 0 l IN A.Q0                                                         /\
    (!n :: (LESS(LENGTH l - 1)). ?a. (EL n l, a, EL (SUC n) l) IN A.Delta) /\
    !a s. ~((EL (LENGTH l - 1) l, a, s) IN A.Delta))
   /\
   (LANGUAGE A (INFINITE f) = 
     f 0 IN A.Q0 /\ !n. ?a. (f n, a, f(SUC n)) IN A.Delta)`;

(*****************************************************************************)
(* MODEL_TO_AUTOMATON adds a value -- "iota" in Clarke/Grumberg/Peled -- to  *)
(* the states of M.  STRIP_IOTA removes iotas.                               *)
(* Not sure if this is needed.                                               *)
(*****************************************************************************)
val STRIP_IOTA_def =
 Define `STRIP_IOTA(SOME x) = x`;

val PATH_STRIP_IOTA_def =
 Define
  `(PATH_STRIP_IOTA(FINITE l) = FINITE(MAP STRIP_IOTA l))
   /\
   (PATH_STRIP_IOTA(INFINITE f) = INFINITE(STRIP_IOTA o f))`;

(*****************************************************************************)
(* Add iotas to a path                                                       *)
(*****************************************************************************)
val PATH_ADD_IOTA_def =
 Define
  `(PATH_ADD_IOTA(FINITE l) = FINITE(MAP SOME l))
   /\
   (PATH_ADD_IOTA(INFINITE f) = INFINITE(SOME o f))`;

(*****************************************************************************)
(* Should have proved FINITE_PATH_LANGUAGE directly, but now too lazy to     *)
(* tweak the rather tedious proof.                                           *)
(*****************************************************************************)
val FINITE_PATH_LANGUAGE_LEMMA = 
 store_thm
  ("FINITE_PATH_LANGUAGE_LEMMA",
   ``!M s l.
      MODEL M /\ s IN M.S0 /\ (s = HD l)
      ==>
      (PATH M s (FINITE l) = 
        LANGUAGE 
         (MODEL_TO_AUTOMATON M) 
         (CONS(NONE, (PATH_ADD_IOTA (FINITE l)))))``,
   REPEAT GEN_TAC
    THEN SIMP_TAC (list_ss++resq_SS) 
          [MODEL_def,PATH_def,LANGUAGE_def,MODEL_TO_AUTOMATON_def,
           PATH_ADD_IOTA_def,CONS_def]
    THEN RW_TAC (srw_ss()) []
    THEN EQ_TAC
    THEN RW_TAC list_ss []
    THENL
     [Cases_on `n`
       THEN RW_TAC list_ss []
       THENL
        [Q.EXISTS_TAC `HD l`
          THEN RW_TAC list_ss []
          THEN Cases_on `l`
          THEN RW_TAC list_ss []
          THEN FULL_SIMP_TAC list_ss [],
         Q.EXISTS_TAC `M.L(EL (SUC n') l)` 
          THEN DISJ1_TAC
          THEN Q.EXISTS_TAC `EL n' l` 
          THEN Q.EXISTS_TAC `EL (SUC n') l`
          THEN `n' < LENGTH l` by DECIDE_TAC
          THEN RW_TAC list_ss [EL_MAP]
          THEN Cases_on `l`
          THEN RW_TAC list_ss []
          THEN FULL_SIMP_TAC list_ss []
          THEN `n' < LENGTH t` by DECIDE_TAC
          THEN RW_TAC list_ss [EL_MAP]],
      Cases_on `(~(EL (LENGTH l) (NONE::MAP SOME l) = SOME s') \/ ~(a = M.L s'') \/
                ~(s = SOME s'')) \/ ~((s',s'') IN M.R)`
       THEN FULL_SIMP_TAC list_ss []
       THEN RW_TAC list_ss []
       THEN `LENGTH l = SUC(LENGTH l - 1)` by DECIDE_TAC
       THEN `EL (LENGTH l - 1) (MAP SOME l) = SOME s'` by PROVE_TAC[TL,EL]
       THEN `LENGTH l - 1  < LENGTH l` by DECIDE_TAC
       THEN `SOME(EL (LENGTH l - 1) l) = SOME s'` by PROVE_TAC[EL_MAP]
       THEN FULL_SIMP_TAC list_ss []
       THEN PROVE_TAC[],
      Cases_on `(~(EL (LENGTH l) (NONE::MAP SOME l) = NONE) \/ ~(a = M.L s') \/
                ~(s = SOME s')) \/ ~(s' IN M.S0)`
       THEN FULL_SIMP_TAC list_ss []
       THEN RW_TAC list_ss []
       THEN `LENGTH l = SUC(LENGTH l - 1)` by DECIDE_TAC
       THEN `EL (LENGTH l - 1) (MAP SOME l) = NONE` by PROVE_TAC[TL,EL]
       THEN `LENGTH l - 1  < LENGTH l` by DECIDE_TAC
       THEN `SOME(EL (LENGTH l - 1) l) = NONE` by PROVE_TAC[EL_MAP]
       THEN FULL_SIMP_TAC list_ss [],
      Cases_on `LENGTH l = 0`
       THEN RW_TAC list_ss []
       THEN POP_ASSUM(fn th => FULL_SIMP_TAC list_ss [th]),
      FULL_SIMP_TAC list_ss [SUBSET_DEF],
      `SUC n < LENGTH l` by DECIDE_TAC
       THEN RES_TAC
       THEN `n < LENGTH l` by DECIDE_TAC
       THEN FULL_SIMP_TAC list_ss [EL_MAP]
       THEN PROVE_TAC[],
      `SUC n < LENGTH l` by DECIDE_TAC
       THEN RES_TAC
       THEN `n < LENGTH l` by DECIDE_TAC
       THEN FULL_SIMP_TAC list_ss [EL_MAP]
       THEN Cases_on `l`
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss []
       THEN `EL n (MAP SOME t) = SOME (EL n t)` by PROVE_TAC[EL_MAP]
               (* Above needed, I think, for mysterious type variable reasons *)
       THEN `SOME(EL n t) = SOME s''` by PROVE_TAC[]
       THEN FULL_SIMP_TAC list_ss []
       THEN PROVE_TAC[],
      `SUC n < LENGTH l` by DECIDE_TAC
       THEN RES_TAC
       THEN FULL_SIMP_TAC list_ss [EL_MAP]
       THEN `n < LENGTH l` by DECIDE_TAC
       THEN `EL n (MAP SOME l) = SOME (EL n l)` by PROVE_TAC[EL_MAP] 
       THENL
        [`SOME(EL n l) = SOME s'` by PROVE_TAC[]
          THEN FULL_SIMP_TAC list_ss []
          THEN Cases_on `l`
          THEN RW_TAC list_ss []
          THEN FULL_SIMP_TAC list_ss []
          THEN `EL n (MAP SOME t) = SOME (EL n t)` by PROVE_TAC[EL_MAP] 
               (* Above needed, I think, for mysterious type variable reasons *)
          THEN `SOME(EL n t) = SOME s''` by PROVE_TAC[]
          THEN FULL_SIMP_TAC list_ss [],
         `SOME(EL n l) = NONE` by PROVE_TAC[]
          THEN FULL_SIMP_TAC list_ss []],
      Cases_on `LENGTH l = 0`
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss []
       THEN `LENGTH l - 1 < LENGTH l` by DECIDE_TAC
       THEN RES_TAC
       THENL
        [`!a s.
            (!s' s''.
               (~(EL (LENGTH l) (NONE::MAP SOME l) = SOME s') \/
                ~(a = M.L s'') \/ ~(s = SOME s'')) \/ ~((s',s'') IN M.R))` 
           by PROVE_TAC[]
          THEN POP_ASSUM
                (fn th => 
                  ASSUME_TAC(Q.SPECL[`M.L s`,`SOME s`,`EL (LENGTH l - 1) l`,`s`]th))
          THEN FULL_SIMP_TAC list_ss []
          THEN `LENGTH l = SUC(LENGTH l - 1)` by DECIDE_TAC
          THEN `LENGTH l - 1 < LENGTH l` by DECIDE_TAC
          THEN PROVE_TAC[EL,TL,EL_MAP],
         `!a s.
            (!s' s''.
               (~(EL (LENGTH l) (NONE::MAP SOME l) = SOME s') \/
                ~(a = M.L s'') \/ ~(s = SOME s'')) \/ ~((s',s'') IN M.R))` 
           by PROVE_TAC[]
          THEN POP_ASSUM
                (fn th => 
                  ASSUME_TAC(Q.SPECL[`M.L s`,`SOME s`,`EL (LENGTH l - 1) l`,`s`]th))
          THEN FULL_SIMP_TAC list_ss []
          THEN `LENGTH l = SUC(LENGTH l - 1)` by DECIDE_TAC
          THEN `LENGTH l - 1 < LENGTH l` by DECIDE_TAC
          THEN PROVE_TAC[EL,TL,EL_MAP]]]);

(*****************************************************************************)
(*     |- !M l.                                                              *)
(*          MODEL M /\ HD l IN M.S0 ==>                                      *)
(*          (PATH M (HD l) (FINITE l) =                                      *)
(*           LANGUAGE (MODEL_TO_AUTOMATON M)                                 *)
(*             (CONS (NONE,PATH_ADD_IOTA (FINITE l))))                       *)
(*****************************************************************************)
val FINITE_PATH_LANGUAGE =
 save_thm
  ("FINITE_PATH_LANGUAGE",
   ((Q.GEN `M` o Q.GEN `l`)
    (SIMP_RULE list_ss []
     (Q.SPECL[`M`,`HD l`,`l`]FINITE_PATH_LANGUAGE_LEMMA))));
 
val INFINITE_PATH_LANGUAGE =
 store_thm
  ("INFINITE_PATH_LANGUAGE",
   ``!M f.
      MODEL M /\ f 0 IN M.S0
      ==>
      (PATH M (f 0) (INFINITE f) = 
        LANGUAGE 
         (MODEL_TO_AUTOMATON M) 
         (CONS(NONE, (PATH_ADD_IOTA (INFINITE f)))))``,
   REPEAT GEN_TAC
    THEN SIMP_TAC (list_ss++resq_SS) 
          [MODEL_def,PATH_def,LANGUAGE_def,MODEL_TO_AUTOMATON_def,
           PATH_ADD_IOTA_def,CONS_def]
    THEN RW_TAC (srw_ss()) []
    THEN EQ_TAC
    THEN RW_TAC list_ss []
    THENL
     [Cases_on `n`
       THEN RW_TAC list_ss [],
      Cases_on `n`
       THEN ZAP_TAC list_ss [SUBSET_DEF],
      POP_ASSUM(STRIP_ASSUME_TAC o Q.SPEC `SUC n`)
       THEN FULL_SIMP_TAC list_ss []]);

val PATH_LANGUAGE =
 store_thm
  ("PATH_LANGUAGE",
   ``!M w.
      MODEL M /\ (ELEM w 0) IN M.S0
      ==>
      (PATH M (ELEM w 0) w = 
        LANGUAGE (MODEL_TO_AUTOMATON M) (CONS(NONE, (PATH_ADD_IOTA w))))``,
   REPEAT GEN_TAC
    THEN Cases_on `w`
    THEN SIMP_TAC (list_ss++resq_SS) 
          [ELEM_def,HEAD_def,REST_def,RESTN_def,
           FINITE_PATH_LANGUAGE,INFINITE_PATH_LANGUAGE]);

val _ = export_theory();


