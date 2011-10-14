(*****************************************************************************)
(* Defines the list of triples ACL2_PACKAGE_ALIST representing the           *)
(* initial ACL2 package structure.                                           *)
(*                                                                           *)
(* Also defines a predicate VALID_PKG_TRIPLES from Matt Kaufmann that        *)
(* abstracts key properties of the package structure and verifies:           *)
(*                                                                           *)
(*  |- VALID_PKG_TRIPLES  ACL2_PACKAGE_ALIST                                 *)
(*                                                                           *)
(* Modified again to split into 4 equal length lists, hence O(n. log n)      *)
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
map load ["stringLib","pairSyntax","listSyntax","PKGS"];
open stringLib pairSyntax listSyntax;
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

open listSyntax pairSyntax stringLib listTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Start new theory "acl2_package"                                           *)
(*****************************************************************************)
val _ = new_theory "acl2_package";

(*****************************************************************************)
(* ACL2_PACKAGE_ALIST contains a list of triples                             *)
(*                                                                           *)
(*   (symbol-name , known-pkg-name , actual-pkg-name)                        *)
(*                                                                           *)
(* The idea is that when symbol-name is interned into known-pkg-name, the    *)
(* resulting symbol's package name is actual-pkg-name.  That is, the         *)
(* symbol with name symbol-name and package-name actual-pkg-name is          *)
(* imported into package known-pkg-name.                                     *)
(*****************************************************************************)


(*****************************************************************************)
(* Building a term directly out of a slurped in ACL2 package structure       *)
(* (e.g. kpa-v2-9-3.ml) breaks the HOL compiler. We therefore fold in the    *)
(* abbreviations below (this idea due to Konrad). It is strange that         *)
(* rewriting the big term is no problem, but compiling it breaks.            *)
(*****************************************************************************)
val ACL2_CL_def     = Define `ACL2_CL      = ("ACL2", "COMMON-LISP")`;
val ACL2_USER_def   = Define `ACL2_USER    = ("ACL2-USER" , "ACL2")`;
val ACL_USER_CL_def = Define `ACL2_USER_CL = ("ACL2-USER" , "COMMON-LISP")`;

(*****************************************************************************)
(* Convert imported ACL2 package structure:                                  *)
(*                                                                           *)
(*  [                                                                        *)
(*  ("&", "ACL2-USER", "ACL2"),                                              *)
(*  ("*ACL2-EXPORTS*", "ACL2-USER", "ACL2"),                                 *)
(*  ...                                                                      *)
(*  ("VALUES", "ACL2", "COMMON-LISP"),                                       *)
(*  ("ZEROP", "ACL2", "COMMON-LISP")                                         *)
(*  ]                                                                        *)
(*                                                                           *)
(* to corresponding term, then fold in ACL2_CL_def, ACL2_USER_def and        *)
(* ACL_USER_CL_def using REWRITE_CONV, then extract the simplified term.     *)
(* Used to define ACL2_PACKAGE_ALIST                                         *)
(*****************************************************************************)

fun make_package_structure_term l =
 rhs
  (concl
    (REWRITE_CONV
      (map GSYM [ACL2_CL_def,ACL2_USER_def,ACL_USER_CL_def])
      (mk_list
       (map
         (fn (s1,s2,s3) =>
           mk_pair(fromMLstring s1, mk_pair(fromMLstring s2, fromMLstring s3)))
        l,
        ``:string # string # string``))));

(*****************************************************************************)
(* The actual triples specifying the initial ACL2 package                    *)
(*****************************************************************************)
val ACL2_PACKAGE_ALIST_def =
 time
  Define
  `ACL2_PACKAGE_ALIST =
    ^(make_package_structure_term PKGS.ACL2_PACKAGE_ALIST)`;

val ACL2_KNOWN_PACKAGES_def =
 time
  Define
  `ACL2_KNOWN_PACKAGES =
    ^(listSyntax.mk_list
       (map fromMLstring PKGS.ACL2_KNOWN_PACKAGES,
        ``:string``))`;

(*****************************************************************************)
(* (defun lookup (pkg-name triples sym-name)                                 *)
(*                                                                           *)
(* ; Triples is a list of "package triples" of the form (sym-name            *)
(* ; pkg-name orig-pkg-name) representing that the symbol-package-name of    *)
(* ; pkg-name::sym-anme is orig-pkg-name.  Lookup returns the                *)
(* ; symbol-package-name of pkg-name::sym-name.                              *)
(*                                                                           *)
(*   (cond ((endp triples)                                                   *)
(*          pkg-name)                                                        *)
(*         ((and (equal pkg-name (nth 1 (car triples)))                      *)
(*               (equal sym-name (nth 0 (car triples))))                     *)
(*          (nth 2 (car triples)))                                           *)
(*         (t (lookup pkg-name (cdr triples) sym-name))))                    *)
(*                                                                           *)
(* LOOKUP pkg_name [(x1,y1,z1);...;(xn,yn,zn)] sym_name  =  zi               *)
(*    if for some i: sym_name=xi and pkg_name=yi (scanning from left)        *)
(*                                                                           *)
(* LOOKUP pkg_name [(x1,y1,z1);...;(xn,yn,zn)] sym_name  =  pkg_name         *)
(*    if for all i: ~(sym_name=xi and pkg_name=yi)                           *)
(*                                                                           *)
(*****************************************************************************)
val LOOKUP_def =
 Define
  `(LOOKUP pkg_name [] _ = pkg_name)
   /\
   (LOOKUP pkg_name ((x1,y1,z1)::a) sym_name =
     if (sym_name=x1) /\ (pkg_name=y1)
       then z1
       else LOOKUP pkg_name a sym_name)`;

(*****************************************************************************)
(* (defun valid-pkg-triples-aux (tail triples)                               *)
(*                                                                           *)
(* ; We recognize whether tail, a tail of triples, is a legal list of        *)
(* ; package triples with respect to the full list, triples.  The idea is    *)
(* ; that for any symbol s imported from package p1 to package p2, s         *)
(* ; cannot be imported from some other package p0 into p1.  That is,        *)
(* ; lookup is idempotent.                                                   *)
(*                                                                           *)
(*   (if (endp tail)                                                         *)
(*       t                                                                   *)
(*     (let* ((trip (car tail))                                              *)
(*            (sym-name (nth 0 trip))                                        *)
(*            (p2 (nth 2 trip)))                                             *)
(*         (and (equal (lookup p2 triples sym-name)                          *)
(*                     p2)                                                   *)
(*              (not (equal sym-name "ACL2-PKG-WITNESS"))                    *)
(*              (not (equal p2 ""))                                          *)
(*              (valid-pkg-triples-aux (cdr tail) triples)))))               *)
(*****************************************************************************)
val VALID_PKG_TRIPLES_AUX_def =
 Define
  `(VALID_PKG_TRIPLES_AUX [] triples = T)
   /\
   (VALID_PKG_TRIPLES_AUX ((sym_name,_,p2)::tail) triples =
     (LOOKUP p2 triples sym_name = p2) /\
     ~(sym_name = "ACL2-PKG-WITNESS")  /\
     ~(p2 = "")                        /\
     (VALID_PKG_TRIPLES_AUX tail triples))`;

val VALID_PKG_TRIPLES_def =
 Define
  `VALID_PKG_TRIPLES triples = VALID_PKG_TRIPLES_AUX triples triples`;


(*

val VALID_ACL2_PACKAGE_ALIST =
 save_thm
  ("VALID_ACL2_PACKAGE_ALIST",
   Count.apply (time EVAL) ``VALID_PKG_TRIPLES ACL2_PACKAGE_ALIST``);

This causes an overflow:

  OverflowUncaught exception:
  Overflow

*)

val _ = export_theory();
