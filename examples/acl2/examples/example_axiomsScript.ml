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
(* From axioms.lisp                                                          *)
(*                                                                           *)
(* ; Convention:  when a term p is used as a formula it means                *)
(* ; (not (equal p nil))   [MJCG changed "t" to "p" here]                    *)
(*                                                                           *)
(* |= p is defined below to mean "p is true in the HOL model of ACL2"        *)
(*                                                                           *)
(*****************************************************************************)
set_fixity "|=" (Prefix 11);                (* Give "|=" weak precedence *)
val ACL2_THM_def =
 xDefine "ACL2_THM"
  `(|= p) = (not(equal p nil) = t)`;

(*****************************************************************************)
(* Sanity checking theorem                                                   *)
(*****************************************************************************)
val ACL2_THM =
 store_thm
  ("ACL2_THM",
   ``!p. (|= p) = ~(p = nil)``,
   Induct
    THEN ACL2_SIMP_TAC [ACL2_THM_def]
    THEN PROVE_TAC[T_NIL,sexp_11]);

add_acl2_simps[ACL2_THM];

(*****************************************************************************)
(* Load ML file created from example_axioms.lisp with a2ml.csh               *)
(*****************************************************************************)
use "example_axioms.lisp.ml";

(*****************************************************************************)
(* Bind each of the ML terms corresponding to the five defaxioms in          *)
(* example_axioms.lisp to ML friendly names based on the ACL2 names          *)
(* (replace "-" by "_") and then turn variables like ACL2::FOO to foo.       *)
(*****************************************************************************)
val [CAR_CDR_ELIM,CAR_CONS,CDR_CONS,CONS_EQUAL,BOOLEAN_CHARACTERP,
     ZERO,COMMUTATIVITY_OF_BINARY_ADD,DISTRIBUTIVITY,TRICHOTOMY,
     RATIONAL_IMPLIES2,LOWEST_TERMS,
     COMPLETION_OF_SYMBOL_NAME, DEFAULT_SYMBOL_NAME, 
     COMPLETION_OF_SYMBOL_PACKAGE_NAME,
     INTERN_IN_PACKAGE_OF_SYMBOL_SYMBOL_NAME,
     SYMBOL_PACKAGE_NAME_PKG_WITNESS_NAME,NIL_IS_NOT_CIRCULAR,
     COMPLETION_OF_BINARY_MULT] = 
 map 
  (clean_acl2_term o #3 o def_to_term) 
  (!sexp.acl2_list_ref);

(*
 map 
  ((fn(x,y,z) => (x,y,clean_acl2_term z)) o def_to_term) 
  (!sexp.acl2_list_ref);

 map mk_def (!sexp.acl2_list_ref);
*)

val CAR_CDR_ELIM_AX =
 time store_thm
  ("CAR_CDR_ELIM_AX",
   ``|= ^CAR_CDR_ELIM``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[]);

val CAR_CONS_AX =
 time store_thm
  ("CAR_CONS_AX",
   ``|= ^CAR_CONS``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[]);

val CDR_CONS_AX =
 time store_thm
  ("CDR_CONS_AX",
   ``|= ^CDR_CONS``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[]);

val CONS_EQUAL_AX =
 time store_thm  (* brute force proof below takes a few minutes *)
  ("CONS_EQUAL_AX",
   ``|= ^CONS_EQUAL``,
   Cases_on `x1` THEN Cases_on `x2` THEN Cases_on `y1` THEN Cases_on `y2`
    THEN ACL2_SIMP_TAC[]
    THEN PROVE_TAC[]);

val BOOLEAN_CHARACTERP_AX =
 time store_thm
  ("BOOLEAN_CHARACTERP_AX",
   ``|= ^BOOLEAN_CHARACTERP``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC[]);

val ZERO_AX =
 time store_thm
  ("ZERO_AX",
   ``|= ^ZERO``,
   ACL2_SIMP_TAC[less_def,cpx_def,ratTheory.RAT_LES_REF]);

val COMMUTATIVITY_OF_BINARY_ADD_AX =
 time store_thm
  ("COMMUTATIVITY_OF_BINARY_ADD_AX",
   ``|= ^COMMUTATIVITY_OF_BINARY_ADD``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC[]
    THEN Cases_on `c` THEN Cases_on `c'`
    THEN PROVE_TAC
          [complex_rationalTheory.COMPLEX_ADD_def,ratTheory.RAT_ADD_COMM]);

val rat_0 =
 store_thm
  ("rat_0",
   ``rat 0 1 = rat_0``,
   PROVE_TAC[rat_def,ratTheory.rat_0_def,fracTheory.frac_0_def]);

(* runtime: 260.682s,    gctime: 6.265s,     systime: 0.393s. *)
val DISTRIBUTIVITY_AX =
 time store_thm
  ("DISTRIBUTIVITY_AX",
   ``|= ^DISTRIBUTIVITY``,
   Cases_on `x` THEN Cases_on `y` THEN Cases_on `z`
    THEN ACL2_SIMP_TAC
          [rat_0,int_def,cpx_def,complex_rationalTheory.COMPLEX_ADD_def,
           ratTheory.RAT_0,ratTheory.RAT_ADD_LID]
    THEN Cases_on `c` THEN TRY(Cases_on `c'`) THEN TRY(Cases_on `c''` )
    THEN FULL_SIMP_TAC arith_ss
          [complex_rationalTheory.COMPLEX_ADD_def,
           complex_rationalTheory.COMPLEX_MULT_def,
           ratTheory.RAT_MUL_LZERO, ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,
           ratTheory.RAT_SUB_LID,ratTheory.RAT_SUB_RID,ratTheory.RAT_AINV_0,
           ratTheory.RAT_SUB_LDISTRIB, ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_LDISTRIB, ratTheory.RAT_RDISTRIB,
           complex_rationalTheory.complex_rational_11]
    THEN METIS_TAC 
          [ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_ADD_COMM,
           ratTheory.RAT_RSUB_EQ,ratTheory.RAT_LSUB_EQ,
           ratTheory.RAT_MUL_LZERO, ratTheory.RAT_MUL_RZERO]);
(*
val TRICHOTOMY_AX =
 time store_thm
  ("TRICHOTOMY_AX",
   ``|= ^TRICHOTOMY``,
   Cases_on `x` 
    THEN ACL2_SIMP_TAC
          [rat_0,int_def,cpx_def,ratTheory.RAT_0,ratTheory.RAT_LES_REF]
    THEN Cases_on `c` 
    THEN FULL_SIMP_TAC arith_ss (!acl2_simps)

    THEN FULL_SIMP_TAC arith_ss
          [complex_rationalTheory.COMPLEX_ADD_def,
           complex_rationalTheory.COMPLEX_MULT_def,
           ratTheory.RAT_MUL_LZERO, ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,
           ratTheory.RAT_SUB_LID,ratTheory.RAT_SUB_RID,ratTheory.RAT_AINV_0,
           ratTheory.RAT_SUB_LDISTRIB, ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_LDISTRIB, ratTheory.RAT_RDISTRIB,
           complex_rationalTheory.complex_rational_11]
    THEN METIS_TAC 
          [ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_ADD_COMM,
           ratTheory.RAT_RSUB_EQ,ratTheory.RAT_LSUB_EQ,
           ratTheory.RAT_MUL_LZERO, ratTheory.RAT_MUL_RZERO]);

val RATIONAL_IMPLIES2_AX =
 time store_thm
  ("RATIONAL_IMPLIES2_AX",
   ``|= ^RATIONAL_IMPLIES2``,
   Cases_on `x` 
    THEN ACL2_SIMP_TAC[]
    THEN Cases_on `c` 
    THEN FULL_SIMP_TAC arith_ss (!acl2_simps)
    THEN Cases_on `r0 = rat_0`
    THEN RW_TAC arith_ss []
    THENL
     [FULL_SIMP_TAC arith_ss
      [
       PROVE_TAC[]]);
*)

val COMPLETION_OF_SYMBOL_NAME =
 time store_thm
  ("COMPLETION_OF_SYMBOL_NAME",
   ``|= ^COMPLETION_OF_SYMBOL_NAME``,
   Cases_on `x` 
    THEN ACL2_SIMP_TAC[]);

val implies =
 store_thm
  ("implies",
   ``!x y. (|= implies x y) = (|= x) ==> (|= y)``,
   REPEAT GEN_TAC
    THEN Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC []
    THEN PROVE_TAC[]);

val not =
 store_thm
  ("not",
   ``!x. (|= not x) = ~(|= x)``,
   REPEAT GEN_TAC
    THEN Cases_on `x`
    THEN ACL2_SIMP_TAC []
    THEN PROVE_TAC[]);

(*
val DEFAULT_SYMBOL_NAME =
 time store_thm
  ("DEFAULT_SYMBOL_NAME",
   ``|= ^DEFAULT_SYMBOL_NAME``,
   RW_TAC std_ss [implies,not]
   Cases_on `x` 
    THEN ACL2_SIMP_TAC[]
    THEN Cases_on `s = ""`
    THEN ACL2_SIMP_TAC[]
*)

val COMPLETION_OF_SYMBOL_PACKAGE_NAME =
 time store_thm
  ("COMPLETION_OF_SYMBOL_PACKAGE_NAME",
   ``|= ^COMPLETION_OF_SYMBOL_PACKAGE_NAME``,
   Cases_on `x` 
    THEN SIMP_TAC std_ss [symbol_name_def,symbolp_def]
    THEN SIMP_TAC std_ss [GSYM symbolp_def]

(*
   Should I try to prove:

    (implies
      (and (symbolp x)
           (equal (symbol-package-name x) (symbol-package-name y)))
      (symbolp y))

... sure, you could try to prove that implication.  Here's a hand
proof:

From (symbolp x) and the assumption about the package system,
(symbol-package-name x) != nil.  On the other hand, if (not (symbolp y)), then
by the axiom completion-of-symbol-package-name, (symbol-package-name y) = nil.
So we have contradicted the second hypothesis.
*)


(* Proof outline from Matt:
First, the comment inside the axiom itself (in source file axioms.lisp)
explains how we can prove (symbolp y) from the other hypotheses.

(defaxiom intern-in-package-of-symbol-symbol-name

; This axiom assumes a model of packages in which "" is not the name of any
; package, but is instead used as a default value when symbol-package-name is
; applied to a non-symbol.  So, the following hypotheses imply (symbolp y).
; Perhaps we should just add (symbolp y) or else add an axiom that (symbolp y)
; if and only if (symbol-package-name y) is not "".  (Or is this provable
; already?)  See also chk-acceptable-defpkg for a related comment, in which a
; proof of nil is shown using this axiom when "" is not disallowed as a package
; name.

  (implies (and (symbolp x)
                (equal (symbol-package-name x) (symbol-package-name y)))
           (equal (intern-in-package-of-symbol (symbol-name x) y) x)))

So, I'll assume that x and y are both symbolps.  I'm assuming that we can find
HOL terms px, py, nx, and ny such that we can prove the following in HOL
(from the definition of symbolp, though I don't know how to do this).

  x = sym px nx
  y = sym py ny

Then from (equal (symbol-package-name x) (symbol-package-name y)) we know

  px = py

Then:

  intern-in-package-of-symbol (symbol-name x) y
= intern-in-package-of-symbol (symbol-name (sym px nx)) (sym py ny)
= {since py=px, as shown above}
  intern-in-package-of-symbol (symbol-name (sym px nx)) (sym px ny)
= {by definition of symbol-name}
  intern-in-package-of-symbol (str nx) (sym px ny)
= {by definition of intern-in-package-of-symbol}
  BASIC_INTERN nx px
= {by symbolp(x), hence symbolp(sym px nx)}
  sym px nx
= x
*)

val INTERN_IN_PACKAGE_OF_SYMBOL_SYMBOL_NAME_AX =
 time store_thm
  ("INTERN_IN_PACKAGE_OF_SYMBOL_SYMBOL_NAME_AX",
   ``|= ^INTERN_IN_PACKAGE_OF_SYMBOL_SYMBOL_NAME ``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC[]
    THEN Cases_on `BASIC_INTERN s0 s = sym s s0` 
    THEN RW_TAC std_ss []
    THENL
     [POP_ASSUM(fn th => FULL_SIMP_TAC std_ss [th,sexp_11,T_NIL])
       THEN Cases_on `y`
       THEN FULL_SIMP_TAC arith_ss (sexp_11::(!acl2_simps))

*)

(*
val _ = export_acl2_theory();
*)

