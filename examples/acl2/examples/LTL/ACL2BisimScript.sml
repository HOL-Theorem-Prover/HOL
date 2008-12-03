(*****************************************************************************)
(* Create "ACL2BisimTheory"                                                  *)
(*                                                                           *)
(* Link general bisumulation in HOL to ACL2 version in the paper:            *)
(* Sandip Ray, John Matthews, Mark Tuttle, "Certifying Compositional Model   *)
(* Checking Algorithms in ACL2".                                             *)
(*                                                                           *)
(*****************************************************************************)

(*  Commands when run interactively:
quietdec := true;                                    (* Switch off output    *)
loadPath := "../../ml" :: (!loadPath);
map load 
 ["pred_setLib","stringLib","finite_mapTheory","LTLTheory","sexpTheory"];
open
 pred_setTheory stringLib finite_mapTheory LTLTheory sexpTheory;
quietdec := false;                                   (* Restore output       *)
*)

(*****************************************************************************)
(* Boilerplate needed for compilation                                        *)
(*****************************************************************************)

open HolKernel Parse boolLib bossLib pred_setTheory LTLTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)


(******************************************************************************
* Start a new theory called ACL2Bisim
******************************************************************************)

val _ = new_theory "ACL2Bisim";


(* 
Instantiate general Kripke structure to have states as sexp and
propositions as strings
*)

val _ = type_abbrev("kripke", ``:(sexp,sexp)model``);

(* Variables in a formula *)
val VARS_def =
 Define
  `(VARS TRUE = {})
   /\
   (VARS FALSE = {})
   /\
   (VARS (ATOMIC a) = {a})
   /\
   (VARS (NOT f) = VARS f)
   /\
   (VARS (AND f1 f2) = VARS f1 UNION VARS f2)
   /\
   (VARS (OR f1 f2) = VARS f1 UNION VARS f2)
   /\
   (VARS (SOMETIMES f) = VARS f)
   /\
   (VARS (ALWAYS f) = VARS f)
   /\
   (VARS (NEXT f) = VARS f)
   /\
   (VARS (UNTIL f1 f2) = VARS f1 UNION VARS f2)
   /\
   (VARS (WEAK_UNTIL f1 f2) = VARS f1 UNION VARS f2)`;


val _ = export_theory();
