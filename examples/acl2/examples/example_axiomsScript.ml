(*****************************************************************************)
(* HOL proof of the translation of the example axioms in example_axioms.lisp *)
(* created by                                                                *)
(*                                                                           *)
(*  ../lisp/a2ml.csh example_axioms.lisp example_axioms.lisp.ml              *)
(*                                                                           *)
(* This is not a compilable file. It must be loaded interactively with       *)
(* the ML function use (this is because it uses example_axioms.lisp.ml).     *)
(*                                                                           *)
(* NOTE                                                                      *)
(* This is a first example. I expect to implement some tools that will       *)
(* make it nicer. I also need to add documentation on various functions      *)
(* to the paper.                                                             *)
(*                                                                           *)
(*****************************************************************************)
quietdec := true;                             (* suppress printing of output *)
loadPath := "../ml" :: !loadPath;             (* add acl2/ml to load path    *)
map                                           (* load infrastructure         *)
 load 
 ["sexp",
  "sexpTheory",
  "basic_defaxiomsTheory"];
open sexp sexpTheory;                         (* open in current session     *)
Globals.checking_const_names := false;        (* suppress odd names warnings *)
quietdec := false;                            (* restore printing of output  *)

(*****************************************************************************)
(* Start new theory "example-axioms"                                         *)
(*****************************************************************************)
new_theory "example_axioms";

(*****************************************************************************)
(* Load ML file created from example_axioms.lisp with a2ml.csh               *)
(*****************************************************************************)
use "example_axioms.lisp.ml";

(*****************************************************************************)
(* Bind each of the ML terms corresponding to the five defaxioms in          *)
(* example_axioms.lisp to ML friendly names based on the ACL2 names          *)
(* (replace "-" by "_") and then turn variables like ACL2::FOO to foo.       *)
(*****************************************************************************)
val [CAR_CDR_ELIM,CAR_CONS,CDR_CONS,CONS_EQUAL,BOOLEAN_CHARACTERP] = 
 map 
  (clean_acl2_term o #3 o def_to_term) 
  (!sexp.acl2_list_ref);

val CAR_CDR_ELIM_AX =
 time store_thm
  ("CAR_CDR_ELIM_AX",
   ``~(^CAR_CDR_ELIM = nil)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[]);

val CAR_CONS_AX =
 time store_thm
  ("CAR_CONS_AX",
   ``~(^CAR_CONS = nil)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[]);

val CDR_CONS_AX =
 time store_thm
  ("CDR_CONS_AX",
   ``~(^CDR_CONS = nil)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[]);

val CONS_EQUAL_AX =
 time store_thm  (* brute force proof below takes a few minutes *)
  ("CONS_EQUAL_AX",
   ``~(^CONS_EQUAL = nil)``,
   Cases_on `x1` THEN Cases_on `x2` THEN Cases_on `y1` THEN Cases_on `y2`
    THEN ACL2_SIMP_TAC[]
    THEN PROVE_TAC[]);

val BOOLEAN_CHARACTERP_AX =
 time store_thm
  ("BOOLEAN_CHARACTERP_AX",
   ``~(^BOOLEAN_CHARACTERP = nil)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[]);

export_theory();
