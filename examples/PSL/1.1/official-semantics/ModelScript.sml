

(*****************************************************************************)
(* Create "ModelTheory" containing definition of models for OBE semantics.   *)
(* PSL version 1.1                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* A model is a quintuple (S,S0,R,P,L), represented as a record, where       *)
(*                                                                           *)
(*  - S  : 'state                    is a set of states                      *)
(*  - S0 : 'state -> bool            is a subset of S, the initial states    *)
(*  - R  : 'state # 'state -> bool   is a transition relation                *)
(*  - P  : 'prop                     is a set of atomic proposition          *)
(*  - L  : 'state -> ('prop -> bool) maps each state to the                  *)
(*                                   set of propositions true in that state  *)
(*                                                                           *)
(* N.B. terms that follow are not contrained to use type variables 'state    *)
(* and 'prop, but may use 'a, 'b etc or whatever typechecking assigns.       *)
(*****************************************************************************)

(*****************************************************************************)
(* Load theory of syntax, paths and models                                   *)
(* (commented out for compilation)                                           *)
(*****************************************************************************)

(*
quietdec := true;                         (* Switch off output               *)
loadPath                                  (* Add official-semantics to path  *)
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
(* ``: ('state,'prop)model``                                                 *)
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
  `(PATH M s (FINITE l) = 
    (LENGTH l > 0) /\ (s = HD l) /\ s IN M.S /\
    (!n :: (LESS(LENGTH l - 1)). 
      EL n l IN M.S /\ EL (SUC n) l IN M.S /\ (EL n l, EL (SUC n) l) IN M.R) /\
    !s. ~((EL (LENGTH l - 1) l, s) IN M.R))
   /\
   (PATH M s (INFINITE f) = 
     (s = f 0) /\ !n. f n IN M.S /\ (f n, f(SUC n)) IN M.R)`;

val _ = export_theory();


