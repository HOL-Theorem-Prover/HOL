
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

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;

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
    <| S  := \s.T;
       S0 := B;
       R  := R; 
       P  := \p.T; 
       L  := (\(s:'state) (f:'state -> bool). f s) |>`;

val _ = export_theory();

