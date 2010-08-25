(*****************************************************************************)
(* This file defines a type of s-expressions and various constants and       *)
(* functions on this type (t, nil, car, cdr, cons etc).                      *)
(*                                                                           *)
(* One goal is to construct a model of ACL2 by proving the axioms in         *)
(* axioms.lisp.                                                              *)
(*                                                                           *)
(* File written by Mike Gordon and Matt Kaufmann; maintained by Mike Gordon. *)
(*                                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Ignore everything up to "END BOILERPLATE"                                 *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE NEEDED FOR COMPILATION                                  *)
(*****************************************************************************)

(******************************************************************************
* Load theories
******************************************************************************)
(* The commented out stuff below should be loaded in interactive sessions
quietdec := true;
app 
 load  
 ["complex_rationalTheory", "sexp","acl2_packageTheory"];
open complex_rationalTheory sexp acl2_packageTheory stringLib;
Globals.checking_const_names := false;
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation: open HOL4 systems modules.
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories (including ratTheory from Jens Brandt).
******************************************************************************)

open stringLib fracTheory ratTheory sexp complex_rationalTheory sexpTheory 
     hol_defaxiomsTheory acl2_packageTheory sexp;

open problem_set_1_answers m1_story;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Start new theory "imported_acl2"                                          *)
(*****************************************************************************)

(* Previously: use "imported_acl2_books.ml"; *)

val _ = new_theory "imported_acl2";

val current_package = ref "UnspecifiedPackage";

val acl2_simp =
 SIMP_RULE
  list_ss
  ([let_simp,andl_fold,itel_fold,itel_append,
    forall2_thm,exists2_thm,forall_fold,exists_fold,
    implies,andl_simp,not_simp,t_nil]
   @
   (map GSYM [int_def,nat_def,List_def,asym_def,csym_def,ksym_def,osym_def]));

val install_fn = (I ## acl2_simp) o install o mk_acl2def;

val _ = map install_fn (discard_duplicate_events problem_set_1_answers);
val _ = map install_fn (discard_duplicate_events m1_story);

val _ = export_theory();




