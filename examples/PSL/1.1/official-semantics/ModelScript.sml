
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
 ["pred_setLib",
  "FinitePathTheory", "PathTheory"];
open pred_setLib 
     FinitePathTheory PathTheory;
quietdec := false;                        (* Restore output                  *)
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib pred_setLib FinitePathTheory PathTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Start a new theory called ModelTheory
******************************************************************************)
val _ = new_theory "Model";

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

(******************************************************************************
* A useful special case (possibly the only one we'll need) is to identify 
* propositions with predicates on states, then we just need to specify the 
* set of initial states B:'state->bool and 
* transition relation R:'state#'state->bool, then:
* MAKE_SIMPLE_MODEL B R : :('a, 'a -> bool) model
*******************************************************************************)
val MAKE_SIMPLE_MODEL =
 Define
  `MAKE_SIMPLE_MODEL (B:'state -> bool) (R:'state#'state->bool) = 
    <| S  := {s | T};
       S0 := B;
       R  := R; 
       P  := {p | T}; 
       L  := (\(s:'state). {f:'state -> bool | f s}) |>`;

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
val PROD_def =
 Define 
  `PROD (M1:('state1, 'prop1) model) (M2:('state2, 'prop2) model) =
    <| S  := {(s1,s2) | M1.S  s1 /\ M2.S  s2};
       S0 := {(s1,s2) | M1.S0 s1 /\ M2.S0 s2};
       R  := {((s1,s2),(s1',s2')) | M1.R(s1,s1') /\ M2.R(s2,s2')};
       P  := {p | if ISL p then M1.P(OUTL p) else M2.P(OUTR p)};
       L  := \(s1,s2). {p | if ISL p then M1.L s1 (OUTL p) else M2.L s2 (OUTR p)} |>`;

val _ = set_fixity "||" (Infixl 650);
val _ = overload_on ("||", ``PROD``);


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
(* Conversion of a path to a machine (Kripke structure)                      *)
(*****************************************************************************)
val PATH_TO_MODEL_def =
 Define
  `(PATH_TO_MODEL(FINITE l) = 
    <| S  := {n | n < LENGTH l};
       S0 := {0};
       R  := {(n,n') | n' = n+1};
       P  := {p:'prop | FINITE_LETTER_IN p l};
       L  := \n. {p | L_SEM (EL n l) p} |>)
   /\
   (PATH_TO_MODEL(INFINITE f) = 
    <| S  := {n | T};
       S0 := {0};
       R  := {(n,n') | n' = n+1};
       P  := {p:'prop | INFINITE_LETTER_IN p f};
       L  := \n. {p | L_SEM (f n) p} |>)`;

(*****************************************************************************)
(* Definition of an automation                                               *)
(* (e.g. Clarke/Grumberg/Peled "Model Checking" Chapter 9)                   *)
(*****************************************************************************)
val automaton_def =
 Hol_datatype
  `automaton = 
    <| Sigma: 'alphabet -> bool;
       Q:     'state -> bool;
       Delta: 'state # ('alphabet -> bool) # 'state -> bool;
       Q0:    'state -> bool;
       F:     'state -> bool |>`;

(*****************************************************************************)
(* Convert a model to an automaton                                           *)
(* (Clarke/Grumberg/Peled "Model Checking" 9.2)                              *)
(*****************************************************************************)
val MODEL_TO_AUTOMATON_def =
 Define
  `MODEL_TO_AUTOMATON (M:('state,'prop)model) =
    <| Sigma := {p : 'prop | T};
       Q     := {s : ('state)option | T};
       Delta := {(SOME s, a, SOME s') | M.R(s,s') /\ (a = M.L s')}
                UNION
                {(NONE, a, SOME s) | s IN M.S0 /\ (a = M.L s)};
       Q0    := {NONE :  ('state)option};
       F     := {s : ('state)option | T} |>`;

(* This looks like rubbish!

(*****************************************************************************)
(* Convert an automation to a model.                                         *)
(*****************************************************************************)
val AUTOMATON_TO_MODEL_def =
 Define
  `AUTOMATON_TO_MODEL (A : ('prop, 'state option)automaton) =
    <| S  := {s | ?q. q IN A.Q /\ (q = SOME s)};
       S0 := {s | ?q a. (q = SOME s) /\ (NONE, a, q) IN A.Delta};
       R  := {(s,s') | ?q a q'. (q = SOME s) /\ (q' = SOME s') 
                                /\ (q,a,q') IN A.Delta};
       P  := {p:'prop | T};
       L  := \s. {p:'prop | T}  |>`;

val MODEL_AUTOMATON_MODEL =
 store_thm
  ("MODEL_AUTOMATON_MODEL",
   ``MODEL_TO_AUTOMATON
      (AUTOMATON_TO_MODEL 
        <| Sigma:=sig; Q:=q; Delta:=del; Q0:=q0; F:=f |>) = 
      <| Sigma:=sig; Q:=q; Delta:=del; Q0:=q0; F:=f |>``,
   RW_TAC list_ss [MODEL_TO_AUTOMATON_def,AUTOMATON_TO_MODEL_def]

*)

val _ = export_theory();


