
(*****************************************************************************)
(* Create "KripkeTheory" containing definition of Kripke structure and some  *)
(* related definitions, including computation paths.                         *)
(*                                                                           *)
(* Created  Wed Dec 25 23:02:12 GMT 2002                                     *)
(* Modified Wed Jan 29 09:46:40 GMT 2003                                     *)
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
* Load theory of finite and infinite sequences and additional definitions of
functions on lists (commented out for compilation)
******************************************************************************)
(*
quietdec := true;
map load ["PSLPathTheory", "rich_listTheory", "intLib"];
open PSLPathTheory listTheory rich_listTheory;
quietdec := false;
*)

Theory Kripke
Ancestors
  PSLPath list rich_list

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Stop ``S`` parsing to the S-combinator
******************************************************************************)
val _ = hide "S";

(******************************************************************************
* ``: ('state,'prop)kripke_structure``
******************************************************************************)
Datatype:
   kripke_structure =
    <| S: 'state -> bool;
       S0:'state -> bool;
       R: 'state # 'state -> bool;
       P: 'prop -> bool;
       L: 'state -> ('prop -> bool) |>
End

(******************************************************************************
* A useful special case (possibly the only one we'll need) is to identify
* propositions with predicates on states, then we just need to specify the
* set of initial states B:'state->bool and
* transition relation R:'state#'state->bool, then:
* MAKE_SIMPLE_KRIPKE_STRUCTURE B R : :('a, 'a -> bool) kripke_structure
*******************************************************************************)
Definition MAKE_SIMPLE_KRIPKE_STRUCTURE_def:
   MAKE_SIMPLE_KRIPKE_STRUCTURE (B:'state -> bool) (R:'state#'state->bool) =
    <| S  := \s.T;
       S0 := B;
       R  := R;
       P  := \p.T;
       L  := (\(s:'state) (f:'state -> bool). f s) |>
End
