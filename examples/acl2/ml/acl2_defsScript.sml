(*****************************************************************************)
(* Some manual definitions needed for translateScript                        *)
(* (eventually these may be generated automatically from defaxioms)          *)
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
map 
 load  
 ["stringLib","complex_rationalTheory","gcdTheory","sexp","sexpTheory"];
open stringLib complex_rationalTheory gcdTheory sexp sexpTheory;
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
open stringLib complex_rationalTheory gcdTheory sexp sexpTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

val _ = new_theory "acl2_defs";

val booleanp_def =
 acl2Define "ACL2::BOOLEANP"
  `booleanp x = ite (equal x t) t (equal x nil)`;

val not_def =
 acl2Define "COMMON-LISP::NOT"
  `not p = ite p nil t`;

val zp_def = 
 acl2Define "ACL2::ZP"
  `zp x = ite (integerp x) (not (less (cpx 0 1 0 1) x)) t`;

val zip_def = 
 acl2Define "ACL2::ZIP"
  `zip x = ite (integerp x) (equal x (cpx 0 1 0 1)) t`;

val fix_def =
 acl2Define "ACL2::FIX"
  `fix x = ite (acl2_numberp x) x (cpx 0 1 0 1)`;

val atom_def =
 acl2Define "COMMON-LISP::ATOM"
  `atom x = not (consp x)`;

val eq_def =
 acl2Define  "COMMON-LISP::EQ"
  `eq x y = equal x y`;

val common_lisp_equal_def =
 acl2Define "DEFUN COMMON-LISP::="
  `common_lisp_equal x y = equal x y`;

val _ = export_acl2_theory();

