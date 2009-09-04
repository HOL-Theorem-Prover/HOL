
(*****************************************************************************) 
(* Run hol in this directory, then use "make_hol_acl2_defaxioms.ml" will     *)
(* create a file hol_acl2_defaxioms.lisp containing a Lisp format            *)
(* printout of the definitions in hol_defaxiomsTheory.                       *)
(* (Written in a hurry by MJCG with only a partial understanding of what     *)
(* I was doing, so possibly untrustworthy!)                                  *)
(*****************************************************************************)

quietdec :=true;

load "hol_defaxiomsTheory";

open sexp sexpTheory hol_defaxiomsTheory;

(* Eliminate som HOL abbreviations *)
val simp =
 SIMP_RULE
  std_ss
  [List_def,itel_def,andl_def,csym_def];

(* Grab theorems from hol_defaxiomsTheory *)
val thms = 
 map 
  (defun o snd o dest_thm o SPEC_ALL o simp o snd) 
  (theorems "hol_defaxioms");

(* Function for filtering out definitions - fails on non-definitions *)
fun clean (defun tm) = 
    if can deftm_to_mlsexp_defun (spec_all tm) then defun tm else fail()
 |  clean _ = fail();

(* Remove non-definition theorems *)
val defs = mapfilter clean thms;

(* Create and print file *)
print_lisp_file 
 "hol_acl2_defaxioms"
 (fn out => mapfilter (print_acl2def out) defs);

print "File \n\n\nhol_acl2_defaxioms.lisp created.\n\n\n";

quietdec := false;




