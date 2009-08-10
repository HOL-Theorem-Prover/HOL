

(*****************************************************************************)
(* Create "ModelTheory" containing definition of models for OBE semantics.   *)
(* PSL version 1.1                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* A model is a quintuple (S,S0,R,P,L), represented as a record, where       *)
(*                                                                           *)
(*  - S  : 'state -> bool            is a set of states                      *)
(*  - S0 : 'state -> bool            is a subset of S, the initial states    *)
(*  - R  : 'state # 'state -> bool   is a transition relation                *)
(*  - P  : 'prop -> bool             is a set of atomic proposition          *)
(*  - L  : 'state -> ('prop -> bool) maps each state to the                  *)
(*                                   set of propositions true in that state  *)
(*                                                                           *)
(* The type parameters are: ``: ('state,'prop)model``                        *)
(* N.B. terms that follow are not contrained to use type variables 'state    *)
(* and 'prop, but may use 'a, 'b etc or whatever typechecking assigns.       *)
(*****************************************************************************)

(*****************************************************************************)
(* Load theory of syntax, paths and models                                   *)
(* (commented out for compilation)                                           *)
(*****************************************************************************)

(*
quietdec := true;                         (* Switch off output               *)
loadPath                                  (* Add path to loadPath            *)
 :=
 "../../path" :: !loadPath;
map load ["pred_setLib","PathTheory"];
open ped_setTheory PathTheory;
quietdec := false;                        (* Restore output                  *)
*)

(*****************************************************************************)
(* Boilerplate needed for compilation                                        *)
(*****************************************************************************)

open HolKernel Parse boolLib bossLib pred_setTheory PathTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Start a new theory called ModelTheory                                     *)
(*****************************************************************************)

val _ = new_theory "Model";

(*****************************************************************************)
(* Stop ``S`` parsing to the S-combinator                                    *)
(*****************************************************************************)
val _ = hide "S";

(*****************************************************************************)
(* ``: ('prop,'state)model``                                                 *)
(*****************************************************************************)
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

(*****************************************************************************)
(* A letter is either TOP, or BOTTOM                                         *)
(* or a set of atomic propositions repersenting a state                      *)
(*****************************************************************************)
val letter_def =
 Hol_datatype
  `letter = TOP | BOTTOM | STATE of ('prop -> bool)`;

(*****************************************************************************)
(* PATH M s is true of path p iff p is a computation path of model M         *)
(*****************************************************************************)
val PATH_def =
 Define
  `PATH M s w =
    (LENGTH w > 0) /\ (s = ELEM w 0) /\ s IN M.S /\
    (!n :: (LESS(LENGTH w - 1)).
      ELEM w n IN M.S /\ ELEM w (SUC n) IN M.S /\
      (ELEM w n, ELEM w (SUC n)) IN M.R) /\
    (!l. (w = FINITE l)
         ==> !s. s IN M.S ==> ~((ELEM w (LENGTH l - 1), s) IN M.R))`;


(*****************************************************************************)
(* A computation of M is a path of M starting from an initial state          *)
(*****************************************************************************)
val COMPUTATION_def =
 Define
  `COMPUTATION M w = ?s. s IN M.S0 /\ PATH M s w`;

val _ = export_theory();


