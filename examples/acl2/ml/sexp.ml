map load ["sexp","sexpTheory"];
open fracTheory ratTheory complex_rationalTheory sexp sexpTheory;

(*****************************************************************************)
(* Print an ACL2 DEFUN (entered as a preterm) to a file defun.tmp.lisp,      *)
(* then run a2ml, then read in generated mlsexp, convert to a term and       *)
(* turn into an ACL2_DEFUN tagged definition and overload a hol name.        *)
(*****************************************************************************)
fun new_defun nam q =
 let val _  = print_defuns_to_mlsexps [q]
     val _  = use "defun-tmp.ml"
     val th = case mk_def(hd(tl(!acl2_list_ref)))
               of  defun(_,defth) => defth
               |   _              => err "new_defun" "not a defun"
     val (opr,_) = strip_comb(lhs(concl(SPEC_ALL th)))
     val _ = overload_on(nam,opr)
 in
  th
 end;


