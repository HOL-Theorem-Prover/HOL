

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
map load ["pred_setLib","PSLPathTheory"];
open ped_setTheory PSLPathTheory;
quietdec := false;                        (* Restore output                  *)
*)

Theory Model
Ancestors
  pred_set PSLPath


(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

val _ = ParseExtras.temp_loose_equality()

(*****************************************************************************)
(* Stop ``S`` parsing to the S-combinator                                    *)
(*****************************************************************************)
val _ = hide "S";

(*****************************************************************************)
(* ``: ('prop,'state)model``                                                 *)
(*****************************************************************************)
Datatype:
   model =
    <| S: 'state -> bool;
       S0:'state -> bool;
       R: 'state # 'state -> bool;
       P: 'prop -> bool;
       L: 'state -> ('prop -> bool) |>
End

Definition MODEL_def:
   MODEL M =
    M.S0 SUBSET M.S /\
    (!s s'. (s,s') IN M.R ==> s IN M.S /\ s' IN M.S) /\
    (!s. s IN M.S ==> M.L s SUBSET M.P)
End

(*****************************************************************************)
(* A letter is either TOP, or BOTTOM                                         *)
(* or a set of atomic propositions repersenting a state                      *)
(*****************************************************************************)
Datatype:
   letter = TOP | BOTTOM | STATE of ('prop -> bool)
End

(*****************************************************************************)
(* PATH M s is true of path p iff p is a computation path of model M         *)
(*****************************************************************************)
Definition PATH_def:
   PATH M s w =
    (LENGTH w > 0) /\ (s = ELEM w 0) /\ s IN M.S /\
    (!n :: (LESS(LENGTH w - 1)).
      ELEM w n IN M.S /\ ELEM w (SUC n) IN M.S /\
      (ELEM w n, ELEM w (SUC n)) IN M.R) /\
    (!l. (w = FINITE l)
         ==> !s. s IN M.S ==> ~((ELEM w (LENGTH l - 1), s) IN M.R))
End


(*****************************************************************************)
(* A computation of M is a path of M starting from an initial state          *)
(*****************************************************************************)
Definition COMPUTATION_def:
   COMPUTATION M w = ?s. s IN M.S0 /\ PATH M s w
End
