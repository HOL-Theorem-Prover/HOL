
(*****************************************************************************)
(* HOL proofs of the ACL2 axioms and theorems in defaxioms.lisp.trans.       *)
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
 ["intLib","stringLib","complex_rationalTheory","gcdTheory",
  "sexp","sexpTheory","hol_defaxiomsTheory","translateTheory"];
open stringLib complex_rationalTheory gcdTheory 
     sexp sexpTheory hol_defaxiomsTheory translateTheory;
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
open stringLib complex_rationalTheory gcdTheory sexp sexpTheory
     hol_defaxiomsTheory translateTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

val _ = new_theory "hol_defaxioms_proofs";

(*****************************************************************************)
(* Proof of ACL2 axioms                                                      *)
(*****************************************************************************)

(*****************************************************************************)
(* Add some theorems from translateTheory to theorems used by ACL2_SIMP_TAC  *)
(*****************************************************************************)
val _ = add_acl2_simps (CONJUNCTS translateTheory.JUDGEMENT_THMS);

(*
     [oracles: DEFAXIOM ACL2::CLOSURE, DISK_THM] [axioms: ] []
     |- |= andl
             [acl2_numberp (add x y); acl2_numberp (mult x y);
              acl2_numberp (unary_minus x); acl2_numberp (reciprocal x)],
*)

val closure_defaxiom =
 store_thm
  ("closure_defaxiom",
   ``|= andl
         [acl2_numberp (add x y); acl2_numberp (mult x y);
          acl2_numberp (unary_minus x); acl2_numberp (reciprocal x)]``,
   ACL2_SIMP_TAC []);

(*
     [oracles: DEFAXIOM ACL2::ASSOCIATIVITY-OF-+] [axioms: ] []
     |- |= equal (add (add x y) z) (add x (add y z)),
*)

val associativity_of_plus_defaxiom =
 store_thm
  ("associativity_of_plus_defaxiom",
   ``|= equal (add (add x y) z) (add x (add y z))``,
   Cases_on `x` THEN Cases_on `y` THEN Cases_on `z`
    THEN ACL2_SIMP_TAC [int_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN TRY(Cases_on `c'`)
    THEN TRY(Cases_on `c''`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,complex_rational_11,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_LID,
           ratTheory.RAT_ADD_RID,ratTheory.RAT_0,
           ratTheory.RAT_ADD_ASSOC]);

(*
     [oracles: DEFAXIOM ACL2::COMMUTATIVITY-OF-+] [axioms: ] []
     |- |= equal (add x y) (add y x),
*)

val commutativity_of_plus_defaxiom =
 store_thm
  ("commutativity_of_plus_defaxiom",
   ``|= equal (add x y) (add y x)``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC [int_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN TRY(Cases_on `c'`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,complex_rational_11,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_LID,
           ratTheory.RAT_ADD_RID,ratTheory.RAT_0,ratTheory.RAT_ADD_COMM]);

(*
     [oracles: DEFAXIOM ACL2::UNICITY-OF-0, DISK_THM] [axioms: ] []
     |- |= equal (add (nat 0) x) (fix x),
*)

val unicity_of_0_defaxiom =
 store_thm
  ("unicity_of_0_defaxiom",
   ``|= equal (add (nat 0) x) (fix x)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC [int_def,nat_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,complex_rational_11,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,com_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_LID,
           ratTheory.RAT_SUB_LID,ratTheory.RAT_ADD_RINV,
           ratTheory.RAT_ADD_RID,ratTheory.RAT_0,ratTheory.RAT_ADD_COMM]);

(*
     [oracles: DEFAXIOM ACL2::INVERSE-OF-+, DISK_THM] [axioms: ] []
     |- |= equal (add x (unary_minus x)) (nat 0),
*)

val inverse_of_plus_defaxiom =
 store_thm
  ("inverse_of_plus_defaxiom",
   ``|= equal (add x (unary_minus x)) (nat 0)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC [int_def,nat_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,complex_rational_11,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,com_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_LID,
           ratTheory.RAT_SUB_LID,ratTheory.RAT_ADD_RINV,
           ratTheory.RAT_ADD_RID,ratTheory.RAT_0,ratTheory.RAT_ADD_COMM]);

(*
     [oracles: DEFAXIOM ACL2::ASSOCIATIVITY-OF-*] [axioms: ] []
     |- |= equal (mult (mult x y) z) (mult x (mult y z)),
*)

val associativity_of_star_defaxiom =
 store_thm
  ("associativity_of_star_defaxiom",
   ``|= equal (mult (mult x y) z) (mult x (mult y z))``,
   Cases_on `x` THEN Cases_on `y` THEN Cases_on `z`
    THEN ACL2_SIMP_TAC [int_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN TRY(Cases_on `c'`)
    THEN TRY(Cases_on `c''`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_MULT_def,complex_rational_11,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL]
    THEN METIS_TAC[ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_ADD_COMM]);

(*
     [oracles: DEFAXIOM ACL2::COMMUTATIVITY-OF-*] [axioms: ] []
     |- |= equal (mult x y) (mult y x),
*)

val commutativity_of_star_defaxiom =
 store_thm
  ("commutativity_of_star_defaxiom",
   ``|= equal (mult x y) (mult y x)``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC [int_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN TRY(Cases_on `c'`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_MULT_def,complex_rational_11,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_1,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,ratTheory.RAT_SUB_ID,
           ratTheory.RAT_LDISTRIB,ratTheory.RAT_RDISTRIB,
           ratTheory.RAT_SUB_LDISTRIB,ratTheory.RAT_SUB_RDISTRIB,
           ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_0,
           ratTheory.RAT_AINV_ADD,
           ratTheory.RAT_ADD_ASSOC,ratTheory.RAT_MUL_ASSOC,
           GSYM ratTheory.RAT_AINV_LMUL,GSYM ratTheory.RAT_AINV_RMUL]
    THEN METIS_TAC[ratTheory.RAT_MUL_COMM,ratTheory.RAT_ADD_COMM]);

(*
     [oracles: DEFAXIOM ACL2::UNICITY-OF-1, DISK_THM] [axioms: ] []
     |- |= equal (mult (nat 1) x) (fix x),
*)

val unicity_of_1_defaxiom =
 store_thm
  ("unicity_of_1_defaxiom",
   ``|= equal (mult (nat 1) x) (fix x)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC [int_def,nat_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN FULL_SIMP_TAC arith_ss 
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_MULT_def,
           complex_rational_11,sexpTheory.rat_def,
           GSYM fracTheory.frac_1_def,com_1_def,
           GSYM ratTheory.rat_1,ratTheory.RAT_ADD_LID,
           GSYM fracTheory.frac_0_def,GSYM ratTheory.rat_0,
           ratTheory.RAT_MUL_LZERO,ratTheory.RAT_SUB_RID,
           ratTheory.RAT_SUB_LID,ratTheory.RAT_ADD_RINV,ratTheory.RAT_MUL_LID,
           ratTheory.RAT_ADD_RID,ratTheory.RAT_1,ratTheory.RAT_ADD_COMM]);

(*
     [oracles: DEFAXIOM ACL2::INVERSE-OF-*, DISK_THM] [axioms: ] []
     |- |= implies (andl [acl2_numberp x; not (equal x (nat 0))])
             (equal (mult x (reciprocal x)) (nat 1)),
*)

val RAT_SQ_SGN =
 store_thm
  ("RAT_SQ_SGN",
   ``!(r:rat). 0 <= rat_sgn(r*r)``,
   RW_TAC arith_ss [ratTheory.RAT_SGN_MUL,integerTheory.INT_LE_SQUARE]);

val RAT_SQ_NONNEG =
 store_thm
  ("RAT_SQ_NONNEG",
   ``!(r:rat). 0 <= r*r``,
   GEN_TAC
    THEN Cases_on `r*r = 0`
    THEN RW_TAC arith_ss [ratTheory.RAT_MUL_LZERO,ratTheory.RAT_LEQ_REF]
    THEN `0 <= rat_sgn(r*r)` by PROVE_TAC[RAT_SQ_SGN]
    THEN DISJ_CASES_TAC(ISPEC ``(r:rat) * r`` ratTheory.RAT_SGN_TOTAL)
    THENL
     [PROVE_TAC[Cooper.COOPER_PROVE ``~(0 <= (n:int) /\ (n = ~1))``],
      POP_ASSUM DISJ_CASES_TAC
       THEN FULL_SIMP_TAC arith_ss 
             [ratTheory.RAT_SGN_MUL,ratTheory.RAT_SGN_CLAUSES,
              ratTheory.RAT_LES_IMP_LEQ,ratTheory.rat_gre_def,
              integerTheory.INT_ENTIRE]]);

val RAT_SQ_POS =
 store_thm
  ("RAT_SQ_POS",
   ``!(r:rat). ~(r = 0) ==> 0 < r*r``,
   GEN_TAC
    THEN `0 <= r*r` by PROVE_TAC[RAT_SQ_NONNEG]
    THEN FULL_SIMP_TAC arith_ss [ratTheory.rat_leq_def]
    THEN POP_ASSUM(ASSUME_TAC o GSYM)
    THEN FULL_SIMP_TAC arith_ss [GSYM ratTheory.RAT_NO_ZERODIV]);

val RAT_SUM_SQ_POS =
 store_thm
  ("RAT_SUM_SQ_POS",
   ``~(r1 = 0) /\ ~(r2 = 0) ==> 0 < r1*r1 + r2*r2``,
   RW_TAC std_ss []
    THEN IMP_RES_TAC RAT_SQ_POS
    THEN RW_TAC std_ss [ratTheory.RAT_0LES_0LES_ADD]);

val inverse_of_star_defaxiom = 
 (* Would expect to be able to improve on this proof *)
 store_thm
  ("inverse_of_star_defaxiom",
   ``|= implies (andl [acl2_numberp x; not (equal x (nat 0))])
             (equal (mult x (reciprocal x)) (nat 1))``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC [int_def,nat_def,cpx_def]
    THEN TRY(Cases_on `c`)
    THEN ACL2_FULL_SIMP_TAC
          [COMPLEX_ADD_def,COMPLEX_SUB_def,COMPLEX_RECIPROCAL_def,
           complex_rational_11,
           sexpTheory.rat_def,
           GSYM fracTheory.frac_0_def,com_0_def,
           GSYM ratTheory.rat_0,ratTheory.RAT_ADD_LID,
           ratTheory.RAT_SUB_LID,ratTheory.RAT_ADD_RINV,
           ratTheory.RAT_ADD_RID,ratTheory.RAT_0,ratTheory.RAT_ADD_COMM]
    THEN Cases_on `r = 0` THEN Cases_on `r0 = 0`
    THEN ACL2_SIMP_TAC[]
    THENL
     [ASSUM_LIST(fn thl => ACL2_FULL_SIMP_TAC[el 3 thl] THEN ASSUME_TAC (el 3 thl)),
      ASSUM_LIST(fn thl => ACL2_FULL_SIMP_TAC[el 3 thl] THEN ASSUME_TAC (el 3 thl)),
      ASSUM_LIST(fn thl => ACL2_FULL_SIMP_TAC[el 1 thl,el 2 thl] 
                            THEN ASSUME_TAC (el 1 thl) THEN ASSUME_TAC (el 2 thl))]
    THEN ACL2_FULL_SIMP_TAC
          [ratTheory.RAT_MUL_LZERO,ratTheory.RAT_MUL_RZERO,
           ratTheory.RAT_ADD_LID,ratTheory.RAT_ADD_RID,
           ratTheory.RAT_DIV_MULMINV,COMPLEX_MULT_def,
           GSYM fracTheory.frac_1_def,GSYM ratTheory.rat_1,
           complex_rational_11,ratTheory.RAT_AINV_0,
           ratTheory.RAT_MUL_ASSOC,GSYM ratTheory.RAT_AINV_LMUL,
           GSYM ratTheory.RAT_AINV_RMUL]
    THEN IMP_RES_TAC
          (PROVE[ratTheory.RAT_NO_ZERODIV_NEG]``~(r=0) ==> ~((r*r) = 0)``)
    THEN ACL2_FULL_SIMP_TAC
          [ratTheory.RAT_MUL_RINV,ratTheory.RAT_SUB_LID,
           ratTheory.RAT_AINV_AINV,ratTheory.RAT_SUB_RID]
    THEN `(r0 * r * rat_minv (r * r + r0 * r0) +
            ~(r * r0 * rat_minv (r * r + r0 * r0)) = 0)`
          by PROVE_TAC[ratTheory.RAT_ADD_RINV,ratTheory.RAT_MUL_COMM]
    THEN POP_ASSUM(fn th => FULL_SIMP_TAC std_ss [th])
    THEN ACL2_FULL_SIMP_TAC
          [ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_AINV,
           GSYM ratTheory.RAT_RDISTRIB,ratTheory.RAT_MUL_RINV]
    THEN Cases_on `r * r + r0 * r0 = 0`
    THEN ACL2_FULL_SIMP_TAC
          [ratTheory.RAT_SUB_ADDAINV,ratTheory.RAT_AINV_AINV,
           GSYM ratTheory.RAT_RDISTRIB,ratTheory.RAT_MUL_RINV]
    THEN `0 < r * r + r0 * r0` by PROVE_TAC[RAT_SUM_SQ_POS]
    THEN PROVE_TAC[ratTheory.RAT_LES_REF]);

(*
     [oracles: DEFAXIOM ACL2::DISTRIBUTIVITY] [axioms: ] []
     |- |= equal (mult x (add y z)) (add (mult x y) (mult x z)),
*)

(*
     [oracles: DEFAXIOM ACL2::<-ON-OTHERS, DISK_THM] [axioms: ] []
     |- |= equal (less x y) (less (add x (unary_minus y)) (nat 0)),
*)

(*
     [oracles: DEFAXIOM ACL2::ZERO, DISK_THM] [axioms: ] []
     |- |= not (less (nat 0) (nat 0)),
*)

(*
     [oracles: DEFAXIOM ACL2::TRICHOTOMY, DISK_THM] [axioms: ] []
     |- |= andl
             [implies (acl2_numberp x)
                (itel
                   [(less (nat 0) x,less (nat 0) x);
                    (equal x (nat 0),equal x (nat 0))]
                   (less (nat 0) (unary_minus x)));
              ite (not (less (nat 0) x)) (not (less (nat 0) x))
                (not (less (nat 0) (unary_minus x)))],
*)

(*
     [oracles: DEFAXIOM ACL2::POSITIVE, DISK_THM] [axioms: ] []
     |- |= andl
             [implies (andl [less (nat 0) x; less (nat 0) y])
                (less (nat 0) (add x y));
              implies
                (andl
                   [rationalp x; rationalp y; less (nat 0) x;
                    less (nat 0) y]) (less (nat 0) (mult x y))],
*)

(*
     [oracles: DEFAXIOM ACL2::RATIONAL-IMPLIES1, DISK_THM] [axioms: ] []
     |- |= implies (rationalp x)
             (andl
                [integerp (denominator x); integerp (numerator x);
                 less (nat 0) (denominator x)]),
*)

(*
     [oracles: DEFAXIOM ACL2::RATIONAL-IMPLIES2] [axioms: ] []
     |- |= implies (rationalp x)
             (equal (mult (reciprocal (denominator x)) (numerator x)) x),
*)

(*
     [oracles: DEFAXIOM ACL2::INTEGER-IMPLIES-RATIONAL] [axioms: ] []
     |- |= implies (integerp x) (rationalp x),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLEX-IMPLIES1, DISK_THM] [axioms: ] []
     |- |= andl [rationalp (realpart x); rationalp (imagpart x)],
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLEX-DEFINITION, DISK_THM] [axioms: ] []
     |- |= implies (andl [rationalp x; rationalp y])
             (equal (complex x y) (add x (mult (cpx 0 1 1 1) y))),
*)

(*
     [oracles: DEFAXIOM ACL2::NONZERO-IMAGPART, DISK_THM] [axioms: ] []
     |- |= implies (complex_rationalp x) (not (equal (nat 0) (imagpart x))),
*)

(*
     [oracles: DEFAXIOM ACL2::REALPART-IMAGPART-ELIM] [axioms: ] []
     |- |= implies (acl2_numberp x)
             (equal (complex (realpart x) (imagpart x)) x),
*)

(*
     [oracles: DEFAXIOM ACL2::REALPART-COMPLEX, DISK_THM] [axioms: ] []
     |- |= implies (andl [rationalp x; rationalp y])
             (equal (realpart (complex x y)) x),
*)

(*
     [oracles: DEFAXIOM ACL2::IMAGPART-COMPLEX, DISK_THM] [axioms: ] []
     |- |= implies (andl [rationalp x; rationalp y])
             (equal (imagpart (complex x y)) y),
*)

(*
     [oracles: DEFAXIOM ACL2::NONNEGATIVE-PRODUCT, DISK_THM] [axioms: ] []
     |- |= implies (rationalp x)
             (andl [rationalp (mult x x); not (less (mult x x) (nat 0))]),
*)

(*
     [oracles: DEFAXIOM ACL2::INTEGER-0, DISK_THM] [axioms: ] []
     |- |= integerp (nat 0),
*)

(*
     [oracles: DEFAXIOM ACL2::INTEGER-1, DISK_THM] [axioms: ] []
     |- |= integerp (nat 1),
*)

(*
     [oracles: DEFAXIOM ACL2::INTEGER-STEP, DISK_THM] [axioms: ] []
     |- |= implies (integerp x)
             (andl [integerp (add x (nat 1)); integerp (add x (int ~1))]),
*)

(*
     [oracles: DEFAXIOM ACL2::LOWEST-TERMS, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [integerp n; rationalp x; integerp r; integerp q;
                 less (nat 0) n; equal (numerator x) (mult n r);
                 equal (denominator x) (mult n q)]) (equal n (nat 1)),
*)

(*
     [oracles: DEFAXIOM ACL2::CAR-CDR-ELIM] [axioms: ] []
     |- |= implies (consp x) (equal (cons (car x) (cdr x)) x),
*)

(*
     [oracles: DEFAXIOM ACL2::CAR-CONS] [axioms: ] []
     |- |= equal (car (cons x y)) x,
*)

val car_cons_defaxiom =
 store_thm
  ("car_cons_defaxiom",
   ``|= equal (car (cons x y)) x``,
   ACL2_SIMP_TAC []);

(*
     [oracles: DEFAXIOM ACL2::CDR-CONS] [axioms: ] []
     |- |= equal (cdr (cons x y)) y,
*)

val cdr_cons_defaxiom =
 store_thm
  ("cdr_cons_defaxiom",
   ``|= equal (cdr (cons x y)) y``,
   ACL2_SIMP_TAC []);

(*
     [oracles: DEFAXIOM ACL2::CONS-EQUAL, DISK_THM] [axioms: ] []
     |- |= equal (equal (cons x1 y1) (cons x2 y2))
             (andl [equal x1 x2; equal y1 y2]),
*)

val cons_equal_defaxiom =
 store_thm
  ("cons_equal_defaxiom",
   ``|= equal (equal (cons x1 y1) (cons x2 y2))
              (andl [equal x1 x2; equal y1 y2])``,
   ACL2_SIMP_TAC []
    THEN PROVE_TAC[sexp_11,T_NIL]);

(*
     [oracles: DEFAXIOM ACL2::BOOLEANP-CHARACTERP] [axioms: ] []
     |- |= booleanp (characterp x),
*)

val booleanp_characterp_defaxiom =
 store_thm
  ("booleanp_characterp_defaxiom",
   ``|= booleanp (characterp x)``,
   ACL2_SIMP_TAC []
    THEN Cases_on `x`
    THEN ACL2_FULL_SIMP_TAC[]);

(*
     [oracles: DEFAXIOM ACL2::CHARACTERP-PAGE] [axioms: ] []
     |- |= characterp (chr #"\f"),
*)

(* Old version
val characterp_page_defaxiom =
 store_thm
  ("characterp_page_defaxiom",
   ``|= characterp (chr ^(fromMLchar #"\f"))``,
   (* Does HOL needs to be fixed to avoid antiquotation? *)
   ACL2_SIMP_TAC []);
*)

val characterp_page_defaxiom =
 store_thm
  ("characterp_page_defaxiom",
   ``|= characterp (chr #"\f")``,
   (* Does HOL needs to be fixed to avoid antiquotation? *)
   ACL2_SIMP_TAC []);

(*
     [oracles: DEFAXIOM ACL2::CHARACTERP-TAB] [axioms: ] []
     |- |= characterp (chr #"\t"),
*)

(* Old version
val characterp_tab_defaxiom =
 store_thm
  ("characterp_tab_defaxiom",
   ``|= characterp (chr ^(fromMLchar #"\t"))``,  
   (* Does HOL needs to be fixed to avoid antiquotation? *)
   ACL2_SIMP_TAC []);
*)

val characterp_tab_defaxiom =
 store_thm
  ("characterp_tab_defaxiom",
   ``|= characterp (chr #"\t")``,  
   (* Does HOL needs to be fixed to avoid antiquotation? *)
   ACL2_SIMP_TAC []);

(*
     [oracles: DEFAXIOM ACL2::CHARACTERP-RUBOUT] [axioms: ] []
     |- |= characterp (chr #"\127"),
*)

(* Old version
val characterp_rubout_defaxiom =
 store_thm
  ("characterp_rubout_defaxiom",
   ``|= characterp (chr ^(fromMLchar #"\127"))``,  
   (* Does HOL needs to be fixed to avoid antiquotation? *)
   ACL2_SIMP_TAC []);
*)

val characterp_rubout_defaxiom =
 store_thm
  ("characterp_rubout_defaxiom",
   ``|= characterp (chr #"\127")``,  
   (* Does HOL needs to be fixed to avoid antiquotation? *)
   ACL2_SIMP_TAC []);

(*
     [oracles: DEFAXIOM ACL2::COERCE-INVERSE-1, DISK_THM] [axioms: ] []
     |- |= implies (character_listp x)
             (equal (coerce (coerce x (csym "STRING")) (csym "LIST")) x),
*)

val list_EXPLODE_coerce =
 store_thm
  ("list_EXPLODE_coerce",
   ``!s. (|= character_listp s)
         ==>
         (list_to_sexp 
           chr
           (EXPLODE(coerce_list_to_string(make_character_list s))) = s)``,
   Induct
    THEN ACL2_SIMP_TAC
          [csym_def,COMMON_LISP_def,coerce_string_to_list_def,
           coerce_list_to_string_def,list_to_sexp_def,
           EVAL ``EXPLODE ""``,make_character_list_def]
    THEN FULL_SIMP_TAC std_ss [GSYM nil_def, GSYM ACL2_TRUE]
    THEN Cases_on `s`
    THEN ACL2_FULL_SIMP_TAC
          [make_character_list_def,coerce_list_to_string_def,
           stringTheory.EXPLODE_EQNS,list_to_sexp_def]);

val coerce_inverse_1_defaxiom =
 store_thm
  ("coerce_inverse_1_defaxiom",
   ``|= implies
          (character_listp x)
          (equal (coerce (coerce x (csym "STRING")) (csym "LIST")) x)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC
          [csym_def,COMMON_LISP_def,coerce_string_to_list_def,
           list_to_sexp_def,EVAL ``EXPLODE ""``]
    THENL
     [PROVE_TAC[sexp_11],
      Cases_on `characterp s = sym "COMMON-LISP" "NIL"`
       THEN ACL2_FULL_SIMP_TAC[make_character_list_def]
       THEN Cases_on `s`
       THEN ACL2_FULL_SIMP_TAC
             [make_character_list_def,coerce_list_to_string_def,
              stringTheory.EXPLODE_EQNS,list_to_sexp_def]
       THEN PROVE_TAC[T_NIL,sexp_11,ACL2_TRUE,list_EXPLODE_coerce,nil_def]]);

(*
     [oracles: DEFAXIOM ACL2::COERCE-INVERSE-2, DISK_THM] [axioms: ] []
     |- |= implies (stringp x)
             (equal (coerce (coerce x (csym "LIST")) (csym "STRING")) x),
*)

val true_listp_list_to_sexp = (* This is not used *)
 store_thm
  ("true_listp_list_to_sexp",
   ``!l. |= true_listp(list_to_sexp f l)``,
   Induct
    THEN ACL2_SIMP_TAC[list_to_sexp_def]
    THEN ONCE_REWRITE_TAC[true_listp_def]
    THEN ACL2_FULL_SIMP_TAC[ACL2_TRUE]);

val coerce_list_EXPLODE =
 store_thm
  ("coerce_list_EXPLODE",
   ``!s. coerce 
          (list_to_sexp chr (EXPLODE s))
          (sym "COMMON-LISP" "STRING") =
         str s``,
   Induct
    THEN ACL2_SIMP_TAC
          [csym_def,COMMON_LISP_def,coerce_string_to_list_def,
           coerce_list_to_string_def,list_to_sexp_def,
           EVAL ``EXPLODE ""``,stringTheory.EXPLODE_EQNS,
           make_character_list_def]
    THEN Cases_on `EXPLODE s`
    THEN ACL2_FULL_SIMP_TAC
          [make_character_list_def,coerce_list_to_string_def,
           stringTheory.EXPLODE_EQNS,list_to_sexp_def,
           stringTheory.EXPLODE_EQ_NIL,EVAL ``"STRING" = "LIST"``]);

val coerce_inverse_2_defaxiom =
 store_thm
  ("coerce_inverse_2_defaxiom",
   ``|= implies
         (stringp x)
         (equal (coerce (coerce x (csym "LIST")) (csym "STRING")) x)``,
   Cases_on `x`
    THEN ACL2_SIMP_TAC
          [csym_def,COMMON_LISP_def,coerce_string_to_list_def,
           list_to_sexp_def,EVAL ``EXPLODE ""``]
    THEN PROVE_TAC[coerce_list_EXPLODE,sexp_11,T_NIL]);

(*
     [oracles: DEFAXIOM ACL2::CHARACTER-LISTP-COERCE, DISK_THM] [axioms: ] []
     |- |= character_listp (coerce acl2_str (csym "LIST")),
*)

val character_listp_list_to_sexp = 
 store_thm
  ("character_listp_list_to_sexp",
   ``!l. |= character_listp(list_to_sexp chr l)``,
   Induct
    THEN ACL2_SIMP_TAC[list_to_sexp_def]
    THEN ACL2_FULL_SIMP_TAC[ACL2_TRUE,nil_def]);

val character_listp_coerce_defaxiom =
 store_thm
  ("character_listp_coerce_defaxiom",
   ``|= character_listp (coerce acl2_str (csym "LIST"))``,
   Cases_on `acl2_str`
    THEN ACL2_SIMP_TAC
          [csym_def,COMMON_LISP_def,coerce_string_to_list_def,
           coerce_list_to_string_def,list_to_sexp_def,
           EVAL ``EXPLODE ""``,stringTheory.EXPLODE_EQNS,
           make_character_list_def]
    THEN PROVE_TAC[character_listp_list_to_sexp,nil_def,ACL2_TRUE]);

val assoc_nil =
 store_thm
  ("assoc_nil",
   ``assoc x nil = nil``,
   CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[assoc_def]))
    THEN ACL2_SIMP_TAC[itel_def]);

val assoc_cons =
 store_thm
  ("assoc_cons",
   ``assoc x (cons (cons x' y) l) = 
      if |= equal x x' then cons x' y else assoc x l``,
   CONV_TAC(LHS_CONV(ONCE_REWRITE_CONV[assoc_def]))
    THEN ACL2_SIMP_TAC[itel_def]);

(*     
val lower_case_p_char_downcase_defaxiom =
 store_thm
  ("lower_case_p_char_downcase_defaxiom",
   ``|= implies (andl [upper_case_p x; characterp x])
                (lower_case_p (char_downcase x))``,
   REWRITE_TAC[implies]
    THEN STRIP_TAC
    THEN SIMP_TAC std_ss [char_downcase_def,assoc_cons,List_def]
    THEN CONV_TAC(DEPTH_CONV(pairLib.let_CONV))
    THEN SIMP_TAC std_ss [itel_def,ite_def]
    THEN ACL2_FULL_SIMP_TAC[assoc_cons,assoc_nil]
    THEN REWRITE_TAC[COND_RAND]
*)

(*
     [oracles: DEFAXIOM ACL2::STRINGP-SYMBOL-PACKAGE-NAME] [axioms: ] []
     |- |= stringp (symbol_package_name x),
*)

(*
     [oracles: DEFAXIOM ACL2::SYMBOLP-INTERN-IN-PACKAGE-OF-SYMBOL] [axioms: ]
     [] |- |= symbolp (intern_in_package_of_symbol x y),
*)

(*
     [oracles: DEFAXIOM ACL2::SYMBOLP-PKG-WITNESS] [axioms: ] []
     |- |= symbolp (pkg_witness x),
*)

(*
     [oracles: DEFAXIOM ACL2::INTERN-IN-PACKAGE-OF-SYMBOL-SYMBOL-NAME,
                DISK_THM]
     [axioms: ] []
     |- |= implies
             (andl
                [symbolp x;
                 equal (symbol_package_name x) (symbol_package_name y)])
             (equal (intern_in_package_of_symbol (symbol_name x) y) x),
*)

(*
     [oracles: DEFAXIOM ACL2::SYMBOL-NAME-PKG-WITNESS] [axioms: ] []
     |- |= equal (symbol_name (pkg_witness pkg_name))
             (str "ACL2-PKG-WITNESS"),
*)

(*
     [oracles: DEFAXIOM ACL2::SYMBOL-PACKAGE-NAME-PKG-WITNESS-NAME, DISK_THM]
     [axioms: ] []
     |- |= equal (symbol_package_name (pkg_witness pkg_name))
             (ite (stringp pkg_name) pkg_name (str ACL2)),
*)

(*
     [oracles: DEFAXIOM ACL2::SYMBOL-NAME-INTERN-IN-PACKAGE-OF-SYMBOL,
                DISK_THM]
     [axioms: ] []
     |- |= implies (andl [stringp s; symbolp any_symbol])
             (equal (symbol_name (intern_in_package_of_symbol s any_symbol))
                s),
*)

(*
     [oracles: DEFAXIOM ACL2::ACL2-INPUT-CHANNEL-PACKAGE, DISK_THM]
     [axioms: ] []
     |- |= implies
             (andl
                [stringp x; symbolp y;
                 equal (symbol_package_name y) (str "ACL2-INPUT-CHANNEL")])
             (equal (symbol_package_name (intern_in_package_of_symbol x y))
                (str "ACL2-INPUT-CHANNEL")),
*)

(*
     [oracles: DEFAXIOM ACL2::ACL2-OUTPUT-CHANNEL-PACKAGE, DISK_THM]
     [axioms: ] []
     |- |= implies
             (andl
                [stringp x; symbolp y;
                 equal (symbol_package_name y) (str ACL2_OUTPUT_CHANNEL)])
             (equal (symbol_package_name (intern_in_package_of_symbol x y))
                (str ACL2_OUTPUT_CHANNEL)),
*)

(*
     [oracles: DEFAXIOM ACL2::ACL2-PACKAGE, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [stringp x;
                 not
                   (member_symbol_name x
                      (List
                         [csym "&ALLOW-OTHER-KEYS";
                          csym "*PRINT-MISER-WIDTH*"; csym "&AUX";
                          csym "*PRINT-PPRINT-DISPATCH*"; csym "&BODY";
                          csym "*PRINT-PRETTY*"; csym "&ENVIRONMENT";
                          csym "*PRINT-RADIX*"; csym "&KEY";
                          csym "*PRINT-READABLY*"; csym "&OPTIONAL";
                          csym "*PRINT-RIGHT-MARGIN*"; csym "&REST";
                          csym "*QUERY-IO*"; csym "&WHOLE";
                          csym "*RANDOM-STATE*"; csym "*";
                          csym "*READ-BASE*"; csym "**";
                          csym "*READ-DEFAULT-FLOAT-FORMAT*"; csym "***";
                          csym "*READ-EVAL*"; csym "*BREAK-ON-SIGNALS*";
                          csym "*READ-SUPPRESS*";
                          csym "*COMPILE-FILE-PATHNAME*"; csym "*READTABLE*";
                          csym "*COMPILE-FILE-TRUENAME*";
                          csym "*STANDARD-INPUT*"; csym "*COMPILE-PRINT*";
                          csym "*STANDARD-OUTPUT*"; csym "*COMPILE-VERBOSE*";
                          csym "*TERMINAL-IO*"; csym "*DEBUG-IO*";
                          csym "*TRACE-OUTPUT*"; csym "*DEBUGGER-HOOK*";
                          csym "+"; csym "*DEFAULT-PATHNAME-DEFAULTS*";
                          csym "++"; csym "*ERROR-OUTPUT*"; csym "+++";
                          csym "*FEATURES*"; csym "-";
                          csym "*GENSYM-COUNTER*"; csym "/";
                          csym "*LOAD-PATHNAME*"; csym "//";
                          csym "*LOAD-PRINT*"; csym "///";
                          csym "*LOAD-TRUENAME*"; csym "/=";
                          csym "*LOAD-VERBOSE*"; csym "1+";
                          csym "*MACROEXPAND-HOOK*"; csym "1-";
                          csym "*MODULES*"; csym "<"; csym "*PACKAGE*";
                          csym "<="; csym "*PRINT-ARRAY*"; csym "=";
                          csym "*PRINT-BASE*"; csym ">"; csym "*PRINT-CASE*";
                          csym ">="; csym "*PRINT-CIRCLE*"; csym "ABORT";
                          csym "*PRINT-ESCAPE*"; csym "ABS";
                          csym "*PRINT-GENSYM*"; csym "ACONS";
                          csym "*PRINT-LENGTH*"; csym "ACOS";
                          csym "*PRINT-LEVEL*"; csym "ACOSH";
                          csym "*PRINT-LINES*"; csym "ADD-METHOD";
                          csym "ADJOIN"; csym "ATOM"; csym "BOUNDP";
                          csym "ADJUST-ARRAY"; csym "BASE-CHAR";
                          csym "BREAK"; csym "ADJUSTABLE-ARRAY-P";
                          csym "BASE-STRING"; csym "BROADCAST-STREAM";
                          csym "ALLOCATE-INSTANCE"; csym "BIGNUM";
                          csym "BROADCAST-STREAM-STREAMS";
                          csym "ALPHA-CHAR-P"; csym "BIT";
                          csym "BUILT-IN-CLASS"; csym "ALPHANUMERICP";
                          csym "BIT-AND"; csym "BUTLAST"; csym "AND";
                          csym "BIT-ANDC1"; csym "BYTE"; csym "APPEND";
                          csym "BIT-ANDC2"; csym "BYTE-POSITION";
                          csym "APPLY"; csym "BIT-EQV"; csym "BYTE-SIZE";
                          csym "APROPOS"; csym "BIT-IOR"; csym "CAAAAR";
                          csym "APROPOS-LIST"; csym "BIT-NAND";
                          csym "CAAADR"; csym "AREF"; csym "BIT-NOR";
                          csym "CAAAR"; csym "ARITHMETIC-ERROR";
                          csym "BIT-NOT"; csym "CAADAR";
                          csym "ARITHMETIC-ERROR-OPERANDS"; csym "BIT-ORC1";
                          csym "CAADDR"; csym "ARITHMETIC-ERROR-OPERATION";
                          csym "BIT-ORC2"; csym "CAADR"; csym "ARRAY";
                          csym "BIT-VECTOR"; csym "CAAR";
                          csym "ARRAY-DIMENSION"; csym "BIT-VECTOR-P";
                          csym "CADAAR"; csym "ARRAY-DIMENSION-LIMIT";
                          csym "BIT-XOR"; csym "CADADR";
                          csym "ARRAY-DIMENSIONS"; csym "BLOCK";
                          csym "CADAR"; csym "ARRAY-DISPLACEMENT";
                          csym "BOOLE"; csym "CADDAR";
                          csym "ARRAY-ELEMENT-TYPE"; csym "BOOLE-1";
                          csym "CADDDR"; csym "ARRAY-HAS-FILL-POINTER-P";
                          csym "BOOLE-2"; csym "CADDR";
                          csym "ARRAY-IN-BOUNDS-P"; csym "BOOLE-AND";
                          csym "CADR"; csym "ARRAY-RANK"; csym "BOOLE-ANDC1";
                          csym "CALL-ARGUMENTS-LIMIT";
                          csym "ARRAY-RANK-LIMIT"; csym "BOOLE-ANDC2";
                          csym "CALL-METHOD"; csym "ARRAY-ROW-MAJOR-INDEX";
                          csym "BOOLE-C1"; csym "CALL-NEXT-METHOD";
                          csym "ARRAY-TOTAL-SIZE"; csym "BOOLE-C2";
                          csym "CAR"; csym "ARRAY-TOTAL-SIZE-LIMIT";
                          csym "BOOLE-CLR"; csym "CASE"; csym "ARRAYP";
                          csym "BOOLE-EQV"; csym "CATCH"; csym "ASH";
                          csym "BOOLE-IOR"; csym "CCASE"; csym "ASIN";
                          csym "BOOLE-NAND"; csym "CDAAAR"; csym "ASINH";
                          csym "BOOLE-NOR"; csym "CDAADR"; csym "ASSERT";
                          csym "BOOLE-ORC1"; csym "CDAAR"; csym "ASSOC";
                          csym "BOOLE-ORC2"; csym "CDADAR"; csym "ASSOC-IF";
                          csym "BOOLE-SET"; csym "CDADDR";
                          csym "ASSOC-IF-NOT"; csym "BOOLE-XOR";
                          csym "CDADR"; csym "ATAN"; csym "BOOLEAN";
                          csym "CDAR"; csym "ATANH"; csym "BOTH-CASE-P";
                          csym "CDDAAR"; csym "CDDADR"; csym "CLEAR-INPUT";
                          csym "COPY-TREE"; csym "CDDAR";
                          csym "CLEAR-OUTPUT"; csym "COS"; csym "CDDDAR";
                          csym "CLOSE"; csym "COSH"; csym "CDDDDR";
                          csym "CLRHASH"; csym "COUNT"; csym "CDDDR";
                          csym "CODE-CHAR"; csym "COUNT-IF"; csym "CDDR";
                          csym "COERCE"; csym "COUNT-IF-NOT"; csym "CDR";
                          csym "COMPILATION-SPEED"; csym "CTYPECASE";
                          csym "CEILING"; csym "COMPILE"; csym "DEBUG";
                          csym "CELL-ERROR"; csym "COMPILE-FILE";
                          csym "DECF"; csym "CELL-ERROR-NAME";
                          csym "COMPILE-FILE-PATHNAME"; csym "DECLAIM";
                          csym "CERROR"; csym "COMPILED-FUNCTION";
                          csym "DECLARATION"; csym "CHANGE-CLASS";
                          csym "COMPILED-FUNCTION-P"; csym "DECLARE";
                          csym "CHAR"; csym "COMPILER-MACRO";
                          csym "DECODE-FLOAT"; csym "CHAR-CODE";
                          csym "COMPILER-MACRO-FUNCTION";
                          csym "DECODE-UNIVERSAL-TIME";
                          csym "CHAR-CODE-LIMIT"; csym "COMPLEMENT";
                          csym "DEFCLASS"; csym "CHAR-DOWNCASE";
                          csym "COMPLEX"; csym "DEFCONSTANT";
                          csym "CHAR-EQUAL"; csym "COMPLEXP";
                          csym "DEFGENERIC"; csym "CHAR-GREATERP";
                          csym "COMPUTE-APPLICABLE-METHODS";
                          csym "DEFINE-COMPILER-MACRO"; csym "CHAR-INT";
                          csym "COMPUTE-RESTARTS"; csym "DEFINE-CONDITION";
                          csym "CHAR-LESSP"; csym "CONCATENATE";
                          csym "DEFINE-METHOD-COMBINATION"; csym "CHAR-NAME";
                          csym "CONCATENATED-STREAM";
                          csym "DEFINE-MODIFY-MACRO"; csym "CHAR-NOT-EQUAL";
                          csym "CONCATENATED-STREAM-STREAMS";
                          csym "DEFINE-SETF-EXPANDER";
                          csym "CHAR-NOT-GREATERP"; csym "COND";
                          csym "DEFINE-SYMBOL-MACRO"; csym "CHAR-NOT-LESSP";
                          csym "CONDITION"; csym "DEFMACRO";
                          csym "CHAR-UPCASE"; csym "CONJUGATE";
                          csym "DEFMETHOD"; csym "CHAR/="; csym "CONS";
                          csym "DEFPACKAGE"; csym "CHAR<"; csym "CONSP";
                          csym "DEFPARAMETER"; csym "CHAR<=";
                          csym "CONSTANTLY"; csym "DEFSETF"; csym "CHAR=";
                          csym "CONSTANTP"; csym "DEFSTRUCT"; csym "CHAR>";
                          csym "CONTINUE"; csym "DEFTYPE"; csym "CHAR>=";
                          csym "CONTROL-ERROR"; csym "DEFUN";
                          csym "CHARACTER"; csym "COPY-ALIST"; csym "DEFVAR";
                          csym "CHARACTERP"; csym "COPY-LIST"; csym "DELETE";
                          csym "CHECK-TYPE"; csym "COPY-PPRINT-DISPATCH";
                          csym "DELETE-DUPLICATES"; csym "CIS";
                          csym "COPY-READTABLE"; csym "DELETE-FILE";
                          csym "CLASS"; csym "COPY-SEQ"; csym "DELETE-IF";
                          csym "CLASS-NAME"; csym "COPY-STRUCTURE";
                          csym "DELETE-IF-NOT"; csym "CLASS-OF";
                          csym "COPY-SYMBOL"; csym "DELETE-PACKAGE";
                          csym "DENOMINATOR"; csym "EQ";
                          csym "DEPOSIT-FIELD"; csym "EQL"; csym "DESCRIBE";
                          csym "EQUAL"; csym "DESCRIBE-OBJECT";
                          csym "EQUALP"; csym "DESTRUCTURING-BIND";
                          csym "ERROR"; csym "DIGIT-CHAR"; csym "ETYPECASE";
                          csym "DIGIT-CHAR-P"; csym "EVAL"; csym "DIRECTORY";
                          csym "EVAL-WHEN"; csym "DIRECTORY-NAMESTRING";
                          csym "EVENP"; csym "DISASSEMBLE"; csym "EVERY";
                          csym "DIVISION-BY-ZERO"; csym "EXP"; csym "DO";
                          csym "EXPORT"; csym "DO*"; csym "EXPT";
                          csym "DO-ALL-SYMBOLS"; csym "EXTENDED-CHAR";
                          csym "DO-EXTERNAL-SYMBOLS"; csym "FBOUNDP";
                          csym "DO-SYMBOLS"; csym "FCEILING";
                          csym "DOCUMENTATION"; csym "FDEFINITION";
                          csym "DOLIST"; csym "FFLOOR"; csym "DOTIMES";
                          csym "FIFTH"; csym "DOUBLE-FLOAT";
                          csym "FILE-AUTHOR"; csym "DOUBLE-FLOAT-EPSILON";
                          csym "FILE-ERROR";
                          csym "DOUBLE-FLOAT-NEGATIVE-EPSILON";
                          csym "FILE-ERROR-PATHNAME"; csym "DPB";
                          csym "FILE-LENGTH"; csym "DRIBBLE";
                          csym "FILE-NAMESTRING"; csym "DYNAMIC-EXTENT";
                          csym "FILE-POSITION"; csym "ECASE";
                          csym "FILE-STREAM"; csym "ECHO-STREAM";
                          csym "FILE-STRING-LENGTH";
                          csym "ECHO-STREAM-INPUT-STREAM";
                          csym "FILE-WRITE-DATE";
                          csym "ECHO-STREAM-OUTPUT-STREAM"; csym "FILL";
                          csym "ED"; csym "FILL-POINTER"; csym "EIGHTH";
                          csym "FIND"; csym "ELT"; csym "FIND-ALL-SYMBOLS";
                          csym "ENCODE-UNIVERSAL-TIME"; csym "FIND-CLASS";
                          csym "END-OF-FILE"; csym "FIND-IF"; csym "ENDP";
                          csym "FIND-IF-NOT"; csym "ENOUGH-NAMESTRING";
                          csym "FIND-METHOD";
                          csym "ENSURE-DIRECTORIES-EXIST";
                          csym "FIND-PACKAGE";
                          csym "ENSURE-GENERIC-FUNCTION";
                          csym "FIND-RESTART"; csym "FIND-SYMBOL";
                          csym "GET-INTERNAL-RUN-TIME"; csym "FINISH-OUTPUT";
                          csym "GET-MACRO-CHARACTER"; csym "FIRST";
                          csym "GET-OUTPUT-STREAM-STRING"; csym "FIXNUM";
                          csym "GET-PROPERTIES"; csym "FLET";
                          csym "GET-SETF-EXPANSION"; csym "FLOAT";
                          csym "GET-UNIVERSAL-TIME"; csym "FLOAT-DIGITS";
                          csym "GETF"; csym "FLOAT-PRECISION";
                          csym "GETHASH"; csym "FLOAT-RADIX"; csym "GO";
                          csym "FLOAT-SIGN"; csym "GRAPHIC-CHAR-P";
                          csym "FLOATING-POINT-INEXACT"; csym "HANDLER-BIND";
                          csym "FLOATING-POINT-INVALID-OPERATION";
                          csym "HANDLER-CASE";
                          csym "FLOATING-POINT-OVERFLOW"; csym "HASH-TABLE";
                          csym "FLOATING-POINT-UNDERFLOW";
                          csym "HASH-TABLE-COUNT"; csym "FLOATP";
                          csym "HASH-TABLE-P"; csym "FLOOR";
                          csym "HASH-TABLE-REHASH-SIZE"; csym "FMAKUNBOUND";
                          csym "HASH-TABLE-REHASH-THRESHOLD";
                          csym "FORCE-OUTPUT"; csym "HASH-TABLE-SIZE";
                          csym "FORMAT"; csym "HASH-TABLE-TEST";
                          csym "FORMATTER"; csym "HOST-NAMESTRING";
                          csym "FOURTH"; csym "IDENTITY"; csym "FRESH-LINE";
                          csym "IF"; csym "FROUND"; csym "IGNORABLE";
                          csym "FTRUNCATE"; csym "IGNORE"; csym "FTYPE";
                          csym "IGNORE-ERRORS"; csym "FUNCALL";
                          csym "IMAGPART"; csym "FUNCTION"; csym "IMPORT";
                          csym "FUNCTION-KEYWORDS"; csym "IN-PACKAGE";
                          csym "FUNCTION-LAMBDA-EXPRESSION"; csym "INCF";
                          csym "FUNCTIONP"; csym "INITIALIZE-INSTANCE";
                          csym "GCD"; csym "INLINE"; csym "GENERIC-FUNCTION";
                          csym "INPUT-STREAM-P"; csym "GENSYM";
                          csym "INSPECT"; csym "GENTEMP"; csym "INTEGER";
                          csym "GET"; csym "INTEGER-DECODE-FLOAT";
                          csym "GET-DECODED-TIME"; csym "INTEGER-LENGTH";
                          csym "GET-DISPATCH-MACRO-CHARACTER";
                          csym "INTEGERP"; csym "GET-INTERNAL-REAL-TIME";
                          csym "INTERACTIVE-STREAM-P"; csym "INTERN";
                          csym "LISP-IMPLEMENTATION-TYPE";
                          csym "INTERNAL-TIME-UNITS-PER-SECOND";
                          csym "LISP-IMPLEMENTATION-VERSION";
                          csym "INTERSECTION"; csym "LIST";
                          csym "INVALID-METHOD-ERROR"; csym "LIST*";
                          csym "INVOKE-DEBUGGER"; csym "LIST-ALL-PACKAGES";
                          csym "INVOKE-RESTART"; csym "LIST-LENGTH";
                          csym "INVOKE-RESTART-INTERACTIVELY"; csym "LISTEN";
                          csym "ISQRT"; csym "LISTP"; csym KEYWORD;
                          csym "LOAD"; csym "KEYWORDP";
                          csym "LOAD-LOGICAL-PATHNAME-TRANSLATIONS";
                          csym "LABELS"; csym "LOAD-TIME-VALUE";
                          csym "LAMBDA"; csym "LOCALLY";
                          csym "LAMBDA-LIST-KEYWORDS"; csym "LOG";
                          csym "LAMBDA-PARAMETERS-LIMIT"; csym "LOGAND";
                          csym "LAST"; csym "LOGANDC1"; csym "LCM";
                          csym "LOGANDC2"; csym "LDB"; csym "LOGBITP";
                          csym "LDB-TEST"; csym "LOGCOUNT"; csym "LDIFF";
                          csym "LOGEQV"; csym "LEAST-NEGATIVE-DOUBLE-FLOAT";
                          csym "LOGICAL-PATHNAME";
                          csym "LEAST-NEGATIVE-LONG-FLOAT";
                          csym "LOGICAL-PATHNAME-TRANSLATIONS";
                          csym "LEAST-NEGATIVE-NORMALIZED-DOUBLE-FLOAT";
                          csym "LOGIOR";
                          csym "LEAST-NEGATIVE-NORMALIZED-LONG-FLOAT";
                          csym "LOGNAND";
                          csym "LEAST-NEGATIVE-NORMALIZED-SHORT-FLOAT";
                          csym "LOGNOR";
                          csym "LEAST-NEGATIVE-NORMALIZED-SINGLE-FLOAT";
                          csym "LOGNOT"; csym "LEAST-NEGATIVE-SHORT-FLOAT";
                          csym "LOGORC1"; csym "LEAST-NEGATIVE-SINGLE-FLOAT";
                          csym "LOGORC2"; csym "LEAST-POSITIVE-DOUBLE-FLOAT";
                          csym "LOGTEST"; csym "LEAST-POSITIVE-LONG-FLOAT";
                          csym "LOGXOR";
                          csym "LEAST-POSITIVE-NORMALIZED-DOUBLE-FLOAT";
                          csym "LONG-FLOAT";
                          csym "LEAST-POSITIVE-NORMALIZED-LONG-FLOAT";
                          csym "LONG-FLOAT-EPSILON";
                          csym "LEAST-POSITIVE-NORMALIZED-SHORT-FLOAT";
                          csym "LONG-FLOAT-NEGATIVE-EPSILON";
                          csym "LEAST-POSITIVE-NORMALIZED-SINGLE-FLOAT";
                          csym "LONG-SITE-NAME";
                          csym "LEAST-POSITIVE-SHORT-FLOAT"; csym "LOOP";
                          csym "LEAST-POSITIVE-SINGLE-FLOAT";
                          csym "LOOP-FINISH"; csym "LENGTH";
                          csym "LOWER-CASE-P"; csym "LET";
                          csym "MACHINE-INSTANCE"; csym "LET*";
                          csym "MACHINE-TYPE"; csym "MACHINE-VERSION";
                          csym "MASK-FIELD"; csym "MACRO-FUNCTION";
                          csym "MAX"; csym "MACROEXPAND"; csym "MEMBER";
                          csym "MACROEXPAND-1"; csym "MEMBER-IF";
                          csym "MACROLET"; csym "MEMBER-IF-NOT";
                          csym "MAKE-ARRAY"; csym "MERGE";
                          csym "MAKE-BROADCAST-STREAM";
                          csym "MERGE-PATHNAMES";
                          csym "MAKE-CONCATENATED-STREAM"; csym "METHOD";
                          csym "MAKE-CONDITION"; csym "METHOD-COMBINATION";
                          csym "MAKE-DISPATCH-MACRO-CHARACTER";
                          csym "METHOD-COMBINATION-ERROR";
                          csym "MAKE-ECHO-STREAM"; csym "METHOD-QUALIFIERS";
                          csym "MAKE-HASH-TABLE"; csym "MIN";
                          csym "MAKE-INSTANCE"; csym "MINUSP";
                          csym "MAKE-INSTANCES-OBSOLETE"; csym "MISMATCH";
                          csym "MAKE-LIST"; csym "MOD";
                          csym "MAKE-LOAD-FORM";
                          csym "MOST-NEGATIVE-DOUBLE-FLOAT";
                          csym "MAKE-LOAD-FORM-SAVING-SLOTS";
                          csym "MOST-NEGATIVE-FIXNUM"; csym "MAKE-METHOD";
                          csym "MOST-NEGATIVE-LONG-FLOAT";
                          csym "MAKE-PACKAGE";
                          csym "MOST-NEGATIVE-SHORT-FLOAT";
                          csym "MAKE-PATHNAME";
                          csym "MOST-NEGATIVE-SINGLE-FLOAT";
                          csym "MAKE-RANDOM-STATE";
                          csym "MOST-POSITIVE-DOUBLE-FLOAT";
                          csym "MAKE-SEQUENCE"; csym "MOST-POSITIVE-FIXNUM";
                          csym "MAKE-STRING";
                          csym "MOST-POSITIVE-LONG-FLOAT";
                          csym "MAKE-STRING-INPUT-STREAM";
                          csym "MOST-POSITIVE-SHORT-FLOAT";
                          csym "MAKE-STRING-OUTPUT-STREAM";
                          csym "MOST-POSITIVE-SINGLE-FLOAT";
                          csym "MAKE-SYMBOL"; csym "MUFFLE-WARNING";
                          csym "MAKE-SYNONYM-STREAM";
                          csym "MULTIPLE-VALUE-BIND";
                          csym "MAKE-TWO-WAY-STREAM";
                          csym "MULTIPLE-VALUE-CALL"; csym "MAKUNBOUND";
                          csym "MULTIPLE-VALUE-LIST"; csym "MAP";
                          csym "MULTIPLE-VALUE-PROG1"; csym "MAP-INTO";
                          csym "MULTIPLE-VALUE-SETQ"; csym "MAPC";
                          csym "MULTIPLE-VALUES-LIMIT"; csym "MAPCAN";
                          csym "NAME-CHAR"; csym "MAPCAR"; csym "NAMESTRING";
                          csym "MAPCON"; csym "NBUTLAST"; csym "MAPHASH";
                          csym "NCONC"; csym "MAPL"; csym "NEXT-METHOD-P";
                          csym "MAPLIST"; nil; csym "NINTERSECTION";
                          csym "PACKAGE-ERROR"; csym "NINTH";
                          csym "PACKAGE-ERROR-PACKAGE";
                          csym "NO-APPLICABLE-METHOD"; csym "PACKAGE-NAME";
                          csym "NO-NEXT-METHOD"; csym "PACKAGE-NICKNAMES";
                          csym "NOT"; csym "PACKAGE-SHADOWING-SYMBOLS";
                          csym "NOTANY"; csym "PACKAGE-USE-LIST";
                          csym "NOTEVERY"; csym "PACKAGE-USED-BY-LIST";
                          csym "NOTINLINE"; csym "PACKAGEP"; csym "NRECONC";
                          csym "PAIRLIS"; csym "NREVERSE";
                          csym "PARSE-ERROR"; csym "NSET-DIFFERENCE";
                          csym "PARSE-INTEGER"; csym "NSET-EXCLUSIVE-OR";
                          csym "PARSE-NAMESTRING"; csym "NSTRING-CAPITALIZE";
                          csym "PATHNAME"; csym "NSTRING-DOWNCASE";
                          csym "PATHNAME-DEVICE"; csym "NSTRING-UPCASE";
                          csym "PATHNAME-DIRECTORY"; csym "NSUBLIS";
                          csym "PATHNAME-HOST"; csym "NSUBST";
                          csym "PATHNAME-MATCH-P"; csym "NSUBST-IF";
                          csym "PATHNAME-NAME"; csym "NSUBST-IF-NOT";
                          csym "PATHNAME-TYPE"; csym "NSUBSTITUTE";
                          csym "PATHNAME-VERSION"; csym "NSUBSTITUTE-IF";
                          csym "PATHNAMEP"; csym "NSUBSTITUTE-IF-NOT";
                          csym "PEEK-CHAR"; csym "NTH"; csym "PHASE";
                          csym "NTH-VALUE"; csym "PI"; csym "NTHCDR";
                          csym "PLUSP"; csym "NULL"; csym "POP";
                          csym "NUMBER"; csym "POSITION"; csym "NUMBERP";
                          csym "POSITION-IF"; csym "NUMERATOR";
                          csym "POSITION-IF-NOT"; csym "NUNION";
                          csym "PPRINT"; csym "ODDP"; csym "PPRINT-DISPATCH";
                          csym "OPEN"; csym "PPRINT-EXIT-IF-LIST-EXHAUSTED";
                          csym "OPEN-STREAM-P"; csym "PPRINT-FILL";
                          csym "OPTIMIZE"; csym "PPRINT-INDENT"; csym "OR";
                          csym "PPRINT-LINEAR"; csym "OTHERWISE";
                          csym "PPRINT-LOGICAL-BLOCK";
                          csym "OUTPUT-STREAM-P"; csym "PPRINT-NEWLINE";
                          csym "PACKAGE"; csym "PPRINT-POP";
                          csym "PPRINT-TAB"; csym "READ-CHAR";
                          csym "PPRINT-TABULAR"; csym "READ-CHAR-NO-HANG";
                          csym "PRIN1"; csym "READ-DELIMITED-LIST";
                          csym "PRIN1-TO-STRING"; csym "READ-FROM-STRING";
                          csym "PRINC"; csym "READ-LINE";
                          csym "PRINC-TO-STRING";
                          csym "READ-PRESERVING-WHITESPACE"; csym "PRINT";
                          csym "READ-SEQUENCE"; csym "PRINT-NOT-READABLE";
                          csym "READER-ERROR";
                          csym "PRINT-NOT-READABLE-OBJECT"; csym "READTABLE";
                          csym "PRINT-OBJECT"; csym "READTABLE-CASE";
                          csym "PRINT-UNREADABLE-OBJECT"; csym "READTABLEP";
                          csym "PROBE-FILE"; csym "REAL"; csym "PROCLAIM";
                          csym "REALP"; csym "PROG"; csym "REALPART";
                          csym "PROG*"; csym "REDUCE"; csym "PROG1";
                          csym "REINITIALIZE-INSTANCE"; csym "PROG2";
                          csym "REM"; csym "PROGN"; csym "REMF";
                          csym "PROGRAM-ERROR"; csym "REMHASH"; csym "PROGV";
                          csym "REMOVE"; csym "PROVIDE";
                          csym "REMOVE-DUPLICATES"; csym "PSETF";
                          csym "REMOVE-IF"; csym "PSETQ";
                          csym "REMOVE-IF-NOT"; csym "PUSH";
                          csym "REMOVE-METHOD"; csym "PUSHNEW";
                          csym "REMPROP"; csym "QUOTE"; csym "RENAME-FILE";
                          csym "RANDOM"; csym "RENAME-PACKAGE";
                          csym "RANDOM-STATE"; csym "REPLACE";
                          csym "RANDOM-STATE-P"; csym "REQUIRE";
                          csym "RASSOC"; csym "REST"; csym "RASSOC-IF";
                          csym "RESTART"; csym "RASSOC-IF-NOT";
                          csym "RESTART-BIND"; csym "RATIO";
                          csym "RESTART-CASE"; csym "RATIONAL";
                          csym "RESTART-NAME"; csym "RATIONALIZE";
                          csym "RETURN"; csym "RATIONALP";
                          csym "RETURN-FROM"; csym "READ"; csym "REVAPPEND";
                          csym "READ-BYTE"; csym "REVERSE"; csym "ROOM";
                          csym "SIMPLE-BIT-VECTOR"; csym "ROTATEF";
                          csym "SIMPLE-BIT-VECTOR-P"; csym "ROUND";
                          csym "SIMPLE-CONDITION"; csym "ROW-MAJOR-AREF";
                          csym "SIMPLE-CONDITION-FORMAT-ARGUMENTS";
                          csym "RPLACA";
                          csym "SIMPLE-CONDITION-FORMAT-CONTROL";
                          csym "RPLACD"; csym "SIMPLE-ERROR"; csym "SAFETY";
                          csym "SIMPLE-STRING"; csym "SATISFIES";
                          csym "SIMPLE-STRING-P"; csym "SBIT";
                          csym "SIMPLE-TYPE-ERROR"; csym "SCALE-FLOAT";
                          csym "SIMPLE-VECTOR"; csym "SCHAR";
                          csym "SIMPLE-VECTOR-P"; csym "SEARCH";
                          csym "SIMPLE-WARNING"; csym "SECOND"; csym "SIN";
                          csym "SEQUENCE"; csym "SINGLE-FLOAT";
                          csym "SERIOUS-CONDITION";
                          csym "SINGLE-FLOAT-EPSILON"; csym "SET";
                          csym "SINGLE-FLOAT-NEGATIVE-EPSILON";
                          csym "SET-DIFFERENCE"; csym "SINH";
                          csym "SET-DISPATCH-MACRO-CHARACTER"; csym "SIXTH";
                          csym "SET-EXCLUSIVE-OR"; csym "SLEEP";
                          csym "SET-MACRO-CHARACTER"; csym "SLOT-BOUNDP";
                          csym "SET-PPRINT-DISPATCH"; csym "SLOT-EXISTS-P";
                          csym "SET-SYNTAX-FROM-CHAR";
                          csym "SLOT-MAKUNBOUND"; csym "SETF";
                          csym "SLOT-MISSING"; csym "SETQ";
                          csym "SLOT-UNBOUND"; csym "SEVENTH";
                          csym "SLOT-VALUE"; csym "SHADOW";
                          csym "SOFTWARE-TYPE"; csym "SHADOWING-IMPORT";
                          csym "SOFTWARE-VERSION"; csym "SHARED-INITIALIZE";
                          csym "SOME"; csym "SHIFTF"; csym "SORT";
                          csym "SHORT-FLOAT"; csym "SPACE";
                          csym "SHORT-FLOAT-EPSILON"; csym "SPECIAL";
                          csym "SHORT-FLOAT-NEGATIVE-EPSILON";
                          csym "SPECIAL-OPERATOR-P"; csym "SHORT-SITE-NAME";
                          csym "SPEED"; csym "SIGNAL"; csym "SQRT";
                          csym "SIGNED-BYTE"; csym "STABLE-SORT";
                          csym "SIGNUM"; csym "STANDARD";
                          csym "SIMPLE-ARRAY"; csym "STANDARD-CHAR";
                          csym "SIMPLE-BASE-STRING"; csym "STANDARD-CHAR-P";
                          csym "STANDARD-CLASS"; csym "SUBLIS";
                          csym "STANDARD-GENERIC-FUNCTION"; csym "SUBSEQ";
                          csym "STANDARD-METHOD"; csym "SUBSETP";
                          csym "STANDARD-OBJECT"; csym "SUBST"; csym "STEP";
                          csym "SUBST-IF"; csym "STORAGE-CONDITION";
                          csym "SUBST-IF-NOT"; csym "STORE-VALUE";
                          csym "SUBSTITUTE"; csym "STREAM";
                          csym "SUBSTITUTE-IF"; csym "STREAM-ELEMENT-TYPE";
                          csym "SUBSTITUTE-IF-NOT"; csym "STREAM-ERROR";
                          csym "SUBTYPEP"; csym "STREAM-ERROR-STREAM";
                          csym "SVREF"; csym "STREAM-EXTERNAL-FORMAT";
                          csym "SXHASH"; csym "STREAMP"; csym "SYMBOL";
                          csym "STRING"; csym "SYMBOL-FUNCTION";
                          csym "STRING-CAPITALIZE"; csym "SYMBOL-MACROLET";
                          csym "STRING-DOWNCASE"; csym "SYMBOL-NAME";
                          csym "STRING-EQUAL"; csym "SYMBOL-PACKAGE";
                          csym "STRING-GREATERP"; csym "SYMBOL-PLIST";
                          csym "STRING-LEFT-TRIM"; csym "SYMBOL-VALUE";
                          csym "STRING-LESSP"; csym "SYMBOLP";
                          csym "STRING-NOT-EQUAL"; csym "SYNONYM-STREAM";
                          csym "STRING-NOT-GREATERP";
                          csym "SYNONYM-STREAM-SYMBOL";
                          csym "STRING-NOT-LESSP"; t;
                          csym "STRING-RIGHT-TRIM"; csym "TAGBODY";
                          csym "STRING-STREAM"; csym "TAILP";
                          csym "STRING-TRIM"; csym "TAN";
                          csym "STRING-UPCASE"; csym "TANH"; csym "STRING/=";
                          csym "TENTH"; csym "STRING<"; csym "TERPRI";
                          csym "STRING<="; csym "THE"; csym "STRING=";
                          csym "THIRD"; csym "STRING>"; csym "THROW";
                          csym "STRING>="; csym "TIME"; csym "STRINGP";
                          csym "TRACE"; csym "STRUCTURE";
                          csym "TRANSLATE-LOGICAL-PATHNAME";
                          csym "STRUCTURE-CLASS"; csym "TRANSLATE-PATHNAME";
                          csym "STRUCTURE-OBJECT"; csym "TREE-EQUAL";
                          csym "STYLE-WARNING"; csym "TRUENAME";
                          csym "TRUNCATE"; csym "VALUES-LIST";
                          csym "TWO-WAY-STREAM"; csym "VARIABLE";
                          csym "TWO-WAY-STREAM-INPUT-STREAM"; csym "VECTOR";
                          csym "TWO-WAY-STREAM-OUTPUT-STREAM";
                          csym "VECTOR-POP"; csym "TYPE"; csym "VECTOR-PUSH";
                          csym "TYPE-ERROR"; csym "VECTOR-PUSH-EXTEND";
                          csym "TYPE-ERROR-DATUM"; csym "VECTORP";
                          csym "TYPE-ERROR-EXPECTED-TYPE"; csym "WARN";
                          csym "TYPE-OF"; csym "WARNING"; csym "TYPECASE";
                          csym "WHEN"; csym "TYPEP"; csym "WILD-PATHNAME-P";
                          csym "UNBOUND-SLOT"; csym "WITH-ACCESSORS";
                          csym "UNBOUND-SLOT-INSTANCE";
                          csym "WITH-COMPILATION-UNIT";
                          csym "UNBOUND-VARIABLE";
                          csym "WITH-CONDITION-RESTARTS";
                          csym "UNDEFINED-FUNCTION";
                          csym "WITH-HASH-TABLE-ITERATOR"; csym "UNEXPORT";
                          csym "WITH-INPUT-FROM-STRING"; csym "UNINTERN";
                          csym "WITH-OPEN-FILE"; csym "UNION";
                          csym "WITH-OPEN-STREAM"; csym "UNLESS";
                          csym "WITH-OUTPUT-TO-STRING"; csym "UNREAD-CHAR";
                          csym "WITH-PACKAGE-ITERATOR"; csym "UNSIGNED-BYTE";
                          csym "WITH-SIMPLE-RESTART"; csym "UNTRACE";
                          csym "WITH-SLOTS"; csym "UNUSE-PACKAGE";
                          csym "WITH-STANDARD-IO-SYNTAX";
                          csym "UNWIND-PROTECT"; csym "WRITE";
                          csym "UPDATE-INSTANCE-FOR-DIFFERENT-CLASS";
                          csym "WRITE-BYTE";
                          csym "UPDATE-INSTANCE-FOR-REDEFINED-CLASS";
                          csym "WRITE-CHAR";
                          csym "UPGRADED-ARRAY-ELEMENT-TYPE";
                          csym "WRITE-LINE";
                          csym "UPGRADED-COMPLEX-PART-TYPE";
                          csym "WRITE-SEQUENCE"; csym "UPPER-CASE-P";
                          csym "WRITE-STRING"; csym "USE-PACKAGE";
                          csym "WRITE-TO-STRING"; csym "USE-VALUE";
                          csym "Y-OR-N-P"; csym "USER-HOMEDIR-PATHNAME";
                          csym "YES-OR-NO-P"; csym "VALUES"; csym "ZEROP"]));
                 symbolp y; equal (symbol_package_name y) (str ACL2)])
             (equal (symbol_package_name (intern_in_package_of_symbol x y))
                (str ACL2)),
*)

(*
     [oracles: DEFAXIOM ACL2::KEYWORD-PACKAGE, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [stringp x; symbolp y;
                 equal (symbol_package_name y) (str KEYWORD)])
             (equal (symbol_package_name (intern_in_package_of_symbol x y))
                (str KEYWORD)),
*)

(*
     [oracles: DEFAXIOM ACL2::STRING-IS-NOT-CIRCULAR, DISK_THM] [axioms: ] []
     |- |= equal (csym "STRING")
             (intern_in_package_of_symbol
                (coerce
                   (cons (chr #"S")
                      (cons (chr #"T")
                         (cons (chr #"R")
                            (cons (chr #"I")
                               (cons (chr #"N")
                                  (cons (chr #"G") (nat 0)))))))
                   (cons (chr #"S")
                      (cons (chr #"T")
                         (cons (chr #"R")
                            (cons (chr #"I")
                               (cons (chr #"N")
                                  (cons (chr #"G") (nat 0))))))))
                (intern_in_package_of_symbol (nat 0) (nat 0))),
*)

(*
     [oracles: DEFAXIOM ACL2::NIL-IS-NOT-CIRCULAR, DISK_THM] [axioms: ] []
     |- |= equal nil
             (intern_in_package_of_symbol
                (coerce
                   (cons (chr #"N")
                      (cons (chr #"I") (cons (chr #"L") (nat 0))))
                   (csym "STRING")) (csym "STRING")),
*)

(*
     [oracles: DEFAXIOM ACL2::CHAR-CODE-LINEAR, DISK_THM] [axioms: ] []
     |- |= less (char_code x) (nat 256),
*)

(*
     [oracles: DEFAXIOM ACL2::CODE-CHAR-TYPE] [axioms: ] []
     |- |= characterp (code_char n),
*)

(*
     [oracles: DEFAXIOM ACL2::CODE-CHAR-CHAR-CODE-IS-IDENTITY] [axioms: ] []
     |- |= implies (force (characterp c)) (equal (code_char (char_code c)) c),
*)

(*
     [oracles: DEFAXIOM ACL2::CHAR-CODE-CODE-CHAR-IS-IDENTITY, DISK_THM]
     [axioms: ] []
     |- |= implies
             (andl
                [force (integerp n); force (not (less n (nat 0)));
                 force (less n (nat 256))])
             (equal (char_code (code_char n)) n),
*)


(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-+, DISK_THM] [axioms: ] []
     |- |= equal (add x y)
             (itel
                [(acl2_numberp x,ite (acl2_numberp y) (add x y) x);
                 (acl2_numberp y,y)] (nat 0)),
*)

val completion_of_plus_defaxiom =
 store_thm
  ("completion_of_plus_defaxiom",
   ``|= equal (add x y)
              (itel
                [(acl2_numberp x,ite (acl2_numberp y) (add x y) x);
                 (acl2_numberp y,y)] (nat 0))``,
   Cases_on `x` THEN Cases_on `y`
    THEN ACL2_SIMP_TAC [itel_def,int_def,cpx_def,nat_def]);

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-*, DISK_THM] [axioms: ] []
     |- |= equal (mult x y)
             (ite (acl2_numberp x) (ite (acl2_numberp y) (mult x y) (nat 0))
                (nat 0)),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-UNARY-MINUS, DISK_THM] [axioms: ]
     []
     |- |= equal (unary_minus x)
             (ite (acl2_numberp x) (unary_minus x) (nat 0)),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-UNARY-/, DISK_THM] [axioms: ] []
     |- |= equal (reciprocal x)
             (ite (andl [acl2_numberp x; not (equal x (nat 0))])
                (reciprocal x) (nat 0)),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-<, DISK_THM] [axioms: ] []
     |- |= equal (less x y)
             (itel
                [(andl [rationalp x; rationalp y],less x y);
                 (less (realpart (ite (acl2_numberp x) x (nat 0)))
                    (realpart (ite (acl2_numberp y) y (nat 0))),
                  less (realpart (ite (acl2_numberp x) x (nat 0)))
                    (realpart (ite (acl2_numberp y) y (nat 0))))]
                (andl
                   [equal (realpart (ite (acl2_numberp x) x (nat 0)))
                      (realpart (ite (acl2_numberp y) y (nat 0)));
                    less (imagpart (ite (acl2_numberp x) x (nat 0)))
                      (imagpart (ite (acl2_numberp y) y (nat 0)))])),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-CAR, DISK_THM] [axioms: ] []
     |- |= equal (car x) (andl [consp x; car x]),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-CDR, DISK_THM] [axioms: ] []
     |- |= equal (cdr x) (andl [consp x; cdr x]),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-CHAR-CODE, DISK_THM] [axioms: ]
     [] |- |= equal (char_code x) (ite (characterp x) (char_code x) (nat 0)),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-CODE-CHAR, DISK_THM] [axioms: ]
     []
     |- |= equal (code_char x)
             (ite (andl [integerp x; not (less x (nat 0)); less x (nat 256)])
                (code_char x) (code_char (nat 0))),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-COMPLEX, DISK_THM] [axioms: ] []
     |- |= equal (complex x y)
             (complex (ite (rationalp x) x (nat 0))
                (ite (rationalp y) y (nat 0))),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-COERCE, DISK_THM] [axioms: ] []
     |- |= equal (coerce x y)
             (ite (equal y (csym "LIST"))
                (andl [stringp x; coerce x (csym "LIST")])
                (coerce (acl2_make_character_list x) (csym "STRING"))),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-DENOMINATOR, DISK_THM] [axioms: ]
     []
     |- |= equal (denominator x) (ite (rationalp x) (denominator x) (nat 1)),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-IMAGPART, DISK_THM] [axioms: ] []
     |- |= equal (imagpart x) (ite (acl2_numberp x) (imagpart x) (nat 0)),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-INTERN-IN-PACKAGE-OF-SYMBOL,
                DISK_THM]
     [axioms: ] []
     |- |= equal (intern_in_package_of_symbol x y)
             (andl [stringp x; symbolp y; intern_in_package_of_symbol x y]),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-NUMERATOR, DISK_THM] [axioms: ]
     [] |- |= equal (numerator x) (ite (rationalp x) (numerator x) (nat 0)),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-REALPART, DISK_THM] [axioms: ] []
     |- |= equal (realpart x) (ite (acl2_numberp x) (realpart x) (nat 0)),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-SYMBOL-NAME, DISK_THM] [axioms: ]
     []
     |- |= equal (symbol_name x) (ite (symbolp x) (symbol_name x) (str "")),
*)


(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-SYMBOL-PACKAGE-NAME, DISK_THM]
     [axioms: ] []
     |- |= equal (symbol_package_name x)
             (ite (symbolp x) (symbol_package_name x) (str "")),
*)

(*
     [oracles: DEFAXIOM ACL2::BOOLEANP-BAD-ATOM<=, DISK_THM] [axioms: ] []
     |- |= ite (equal (bad_atom_less_equal x y) t)
             (equal (bad_atom_less_equal x y) t)
             (equal (bad_atom_less_equal x y) nil),
*)

(*
     [oracles: DEFAXIOM ACL2::BAD-ATOM<=-ANTISYMMETRIC, DISK_THM] [axioms: ]
     []
     |- |= implies
             (andl
                [bad_atom x; bad_atom y; bad_atom_less_equal x y;
                 bad_atom_less_equal y x]) (equal x y),
*)

(*
     [oracles: DEFAXIOM ACL2::BAD-ATOM<=-TRANSITIVE, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [bad_atom_less_equal x y; bad_atom_less_equal y z;
                 bad_atom x; bad_atom y; bad_atom z])
             (bad_atom_less_equal x z),
*)

(*
     [oracles: DEFAXIOM ACL2::BAD-ATOM<=-TOTAL, DISK_THM] [axioms: ] []
     |- |= implies (andl [bad_atom x; bad_atom y])
             (ite (bad_atom_less_equal x y) (bad_atom_less_equal x y)
                (bad_atom_less_equal y x)),
*)

val _ = export_acl2_theory();
