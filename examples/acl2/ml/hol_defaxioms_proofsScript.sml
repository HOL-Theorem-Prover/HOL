
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
 ["stringLib","complex_rationalTheory","gcdTheory",
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
   ``!x y z. |= equal (add (add x y) z) (add x (add y z))``,
   Cases THEN Cases THEN Cases
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
   ``!x y. |= equal (add x y) (add y x)``,
   Cases THEN Cases
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

(*
     [oracles: DEFAXIOM ACL2::INVERSE-OF-+, DISK_THM] [axioms: ] []
     |- |= equal (add x (unary_minus x)) (nat 0),
*)

(*
     [oracles: DEFAXIOM ACL2::ASSOCIATIVITY-OF-*] [axioms: ] []
     |- |= equal (mult (mult x y) z) (mult x (mult y z)),
*)

val associativity_of_star_defaxiom =
 store_thm
  ("associativity_of_star_defaxiom",
   ``!x y z. |= equal (mult (mult x y) z) (mult x (mult y z))``,
   Cases THEN Cases THEN Cases
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
   ``!x y. |= equal (mult x y) (mult y x)``,
   Cases THEN Cases
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

(*
     [oracles: DEFAXIOM ACL2::INVERSE-OF-*, DISK_THM] [axioms: ] []
     |- |= implies (andl [acl2_numberp x; not (equal x (nat 0))])
             (equal (mult x (reciprocal x)) (nat 1)),
*)

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
     [oracles: DEFTHM ACL2::COMPLEX-EQUAL, DISK_THM] [axioms: ] []
     |- |= implies
             (andl [rationalp x1; rationalp y1; rationalp x2; rationalp y2])
             (equal (equal (complex x1 y1) (complex x2 y2))
                (andl [equal x1 x2; equal y1 y2])),
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

val characterp_page_defaxiom =
 store_thm
  ("characterp_page_defaxiom",
   ``|= characterp (chr ^(fromMLchar #"\f"))``,
   (* Does HOL needs to be fixed to avoid antiquotation? *)
   ACL2_SIMP_TAC []);

(*
     [oracles: DEFAXIOM ACL2::CHARACTERP-TAB] [axioms: ] []
     |- |= characterp (chr #"\t"),
*)

val characterp_tab_defaxiom =
 store_thm
  ("characterp_tab_defaxiom",
   ``|= characterp (chr ^(fromMLchar #"\t"))``,  
   (* Does HOL needs to be fixed to avoid antiquotation? *)
   ACL2_SIMP_TAC []);

(*
     [oracles: DEFAXIOM ACL2::CHARACTERP-RUBOUT] [axioms: ] []
     |- |= characterp (chr #"\127"),
*)

val characterp_rubout_defaxiom =
 store_thm
  ("characterp_rubout_defaxiom",
   ``|= characterp (chr ^(fromMLchar #"\127"))``,  
   (* Does HOL needs to be fixed to avoid antiquotation? *)
   ACL2_SIMP_TAC []);

(*
     [oracles: DEFTHM ACL2::CHARACTER-LISTP-FORWARD-TO-EQLABLE-LISTP]
     [axioms: ] [] |- |= implies (character_listp x) (eqlable_listp x),
*)

(* Still need to show:

> val it =
    F
    ------------------------------------
      2.  ~(character_listp s0 = sym "COMMON-LISP" "NIL")
      1.  eqlable_listp s0 = sym "COMMON-LISP" "NIL"

val character_listp_forward_to_eqlable_listp_defthm =
 store_thm
  ("character_listp_forward_to_eqlable_listp",
   ``|= implies (character_listp x) (eqlable_listp x)``,
   REWRITE_TAC[implies]
    THEN Induct_on `x`
    THEN ACL2_FULL_SIMP_TAC [itel_def]
    THEN Cases_on `s`
    THEN ACL2_FULL_SIMP_TAC [itel_def]

    THEN Cases_on `s0`
    THEN ACL2_FULL_SIMP_TAC [itel_def]

   ONCE_REWRITE_TAC[eqlable_listp_def,character_listp_def]
    THEN ACL2_SIMP_TAC []
    THEN Cases_on `x`
    THEN ACL2_FULL_SIMP_TAC []
    THEN Cases_on `s`
    THEN ACL2_FULL_SIMP_TAC [itel_def]

*)

(*
     [oracles: DEFTHM ACL2::STANDARD-CHAR-LISTP-FORWARD-TO-CHARACTER-LISTP]
     [axioms: ] [] |- |= implies (standard_char_listp x) (character_listp x),
*)

(*
     [oracles: DEFAXIOM ACL2::COERCE-INVERSE-1, DISK_THM] [axioms: ] []
     |- |= implies (character_listp x)
             (equal (coerce (coerce x (csym "STRING")) (csym "LIST")) x),
*)

(*
     [oracles: DEFAXIOM ACL2::COERCE-INVERSE-2, DISK_THM] [axioms: ] []
     |- |= implies (stringp x)
             (equal (coerce (coerce x (csym "LIST")) (csym "STRING")) x),
*)

(*
     [oracles: DEFAXIOM ACL2::CHARACTER-LISTP-COERCE, DISK_THM] [axioms: ] []
     |- |= character_listp (coerce acl2_str (csym "LIST")),
*)

(*
     [oracles: DEFTHM ACL2::LOWER-CASE-P-CHAR-DOWNCASE, DISK_THM] [axioms: ]
     []
     |- |= implies (andl [upper_case_p x; characterp x])
             (lower_case_p (char_downcase x)),
*)

(*
     [oracles: DEFTHM ACL2::UPPER-CASE-P-CHAR-UPCASE, DISK_THM] [axioms: ] []
     |- |= implies (andl [lower_case_p x; characterp x])
             (upper_case_p (char_upcase x)),
*)

(*
     [oracles: DEFTHM ACL2::LOWER-CASE-P-FORWARD-TO-ALPHA-CHAR-P, DISK_THM]
     [axioms: ] []
     |- |= implies (andl [lower_case_p x; characterp x]) (alpha_char_p x),
*)

(*
     [oracles: DEFTHM ACL2::UPPER-CASE-P-FORWARD-TO-ALPHA-CHAR-P, DISK_THM]
     [axioms: ] []
     |- |= implies (andl [upper_case_p x; characterp x]) (alpha_char_p x),
*)

(*
     [oracles: DEFTHM ACL2::ALPHA-CHAR-P-FORWARD-TO-CHARACTERP] [axioms: ] []
     |- |= implies (alpha_char_p x) (characterp x),
*)

(*
     [oracles: DEFTHM ACL2::CHARACTERP-CHAR-DOWNCASE] [axioms: ] []
     |- |= characterp (char_downcase x),
*)

(*
     [oracles: DEFTHM ACL2::CHARACTERP-CHAR-UPCASE] [axioms: ] []
     |- |= characterp (char_upcase x),
*)

(*
     [oracles: DEFTHM ACL2::CHARACTER-LISTP-STRING-DOWNCASE-1] [axioms: ] []
     |- |= character_listp (string_downcase1 x),
*)

(*
     [oracles: DEFTHM ACL2::CHARACTER-LISTP-STRING-UPCASE1-1] [axioms: ] []
     |- |= character_listp (string_upcase1 x),
*)

(*
     [oracles: DEFTHM ACL2::ATOM-LISTP-FORWARD-TO-TRUE-LISTP] [axioms: ] []
     |- |= implies (atom_listp x) (true_listp x),
*)

(*
     [oracles: DEFTHM ACL2::EQLABLE-LISTP-FORWARD-TO-ATOM-LISTP] [axioms: ]
     [] |- |= implies (eqlable_listp x) (atom_listp x),
*)

(*
     [oracles: DEFTHM ACL2::CHARACTERP-NTH, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [character_listp x; integerp i; not (less i (nat 0));
                 less i (len x)]) (characterp (nth i x)),
*)

(*
     [oracles: DEFTHM ACL2::STANDARD-STRING-ALISTP-FORWARD-TO-ALISTP]
     [axioms: ] [] |- |= implies (standard_string_alistp x) (alistp x),
*)

(*
     [oracles: DEFTHM ACL2::NATP-COMPOUND-RECOGNIZER, DISK_THM] [axioms: ] []
     |- |= equal (natp x) (andl [integerp x; not (less x (nat 0))]),
*)

(*
     [oracles: DEFTHM ACL2::POSP-COMPOUND-RECOGNIZER, DISK_THM] [axioms: ] []
     |- |= equal (posp x) (andl [integerp x; less (nat 0) x]),
*)

(*
     [oracles: DEFTHM ACL2::O-P-IMPLIES-O<G] [axioms: ] []
     |- |= implies (o_p a) (o_less_g a),
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
     [oracles: DEFTHM ACL2::KEYWORDP-FORWARD-TO-SYMBOLP] [axioms: ] []
     |- |= implies (keywordp x) (symbolp x),
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
     [oracles: DEFTHM ACL2::SYMBOL-EQUALITY, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [symbolp s1; symbolp s2;
                 equal (symbol_name s1) (symbol_name s2);
                 equal (symbol_package_name s1) (symbol_package_name s2)])
             (equal s1 s2),
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
     [oracles: DEFTHM ACL2::STANDARD-CHAR-LISTP-APPEND, DISK_THM] [axioms: ]
     []
     |- |= implies (true_listp x)
             (equal (standard_char_listp (binary_append x y))
                (andl [standard_char_listp x; standard_char_listp y])),
*)

(*
     [oracles: DEFTHM ACL2::CHARACTER-LISTP-APPEND, DISK_THM] [axioms: ] []
     |- |= implies (true_listp x)
             (equal (character_listp (binary_append x y))
                (andl [character_listp x; character_listp y])),
*)

(*
     [oracles: DEFTHM ACL2::CHARACTER-LISTP-REMOVE-DUPLICATES-EQL] [axioms: ]
     []
     |- |= implies (character_listp x)
             (character_listp (remove_duplicates_eql x)),
*)

(*
     [oracles: DEFTHM ACL2::CHARACTER-LISTP-REVAPPEND, DISK_THM] [axioms: ]
     []
     |- |= implies (true_listp x)
             (equal (character_listp (revappend x y))
                (andl [character_listp x; character_listp y])),
*)

(*
     [oracles: DEFTHM ACL2::PSEUDO-TERM-LISTP-FORWARD-TO-TRUE-LISTP]
     [axioms: ] [] |- |= implies (pseudo_term_listp x) (true_listp x),
*)

(*
     [oracles: DEFTHM ACL2::STANDARD-CHAR-P-NTH, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [standard_char_listp chars; not (less i (nat 0));
                 less i (len chars)]) (standard_char_p (nth i chars)),
*)

(*
     [oracles: DEFTHM ACL2::EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE, DISK_THM]
     [axioms: ] []
     |- |= implies (andl [acl2_numberp r; not (equal r (nat 0))])
             (not (equal (expt r i) (nat 0))),
*)

(*
     [oracles: DEFTHM ACL2::RATIONALP-EXPT-TYPE-PRESCRIPTION] [axioms: ] []
     |- |= implies (rationalp r) (rationalp (expt r i)),
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
     [oracles: DEFTHM ACL2::STRING<-L-IRREFLEXIVE] [axioms: ] []
     |- |= not (string_less_l x x i),
*)

(*
     [oracles: DEFTHM ACL2::STRING<-IRREFLEXIVE] [axioms: ] []
     |- |= not (string_less s s),
*)

(*
     [oracles: DEFTHM ACL2::WORLDP-FORWARD-TO-ASSOC-EQ-EQUAL-ALISTP]
     [axioms: ] [] |- |= implies (worldp x) (assoc_eq_equal_alistp x),
*)

(*
     [oracles: DEFTHM ACL2::ORDERED-SYMBOL-ALISTP-FORWARD-TO-SYMBOL-ALISTP]
     [axioms: ] [] |- |= implies (ordered_symbol_alistp x) (symbol_alistp x),
*)

(*
     [oracles: DEFTHM ACL2::TRUE-LIST-LISTP-FORWARD-TO-TRUE-LISTP] [axioms: ]
     [] |- |= implies (true_list_listp x) (true_listp x),
*)

(*
     [oracles: DEFTHM ACL2::EQUAL-CHAR-CODE, DISK_THM] [axioms: ] []
     |- |= implies (andl [characterp x; characterp y])
             (implies (equal (char_code x) (char_code y)) (equal x y)),
*)

(*
     [oracles: DEFTHM ACL2::BOUNDED-INTEGER-ALISTP-FORWARD-TO-EQLABLE-ALISTP]
     [axioms: ] []
     |- |= implies (bounded_integer_alistp x n) (eqlable_alistp x),
*)

(*
     [oracles: DEFTHM ACL2::KEYWORD-VALUE-LISTP-FORWARD-TO-TRUE-LISTP]
     [axioms: ] [] |- |= implies (keyword_value_listp x) (true_listp x),
*)

(*
     [oracles: DEFTHM ACL2::KEYWORD-VALUE-LISTP-ASSOC-KEYWORD] [axioms: ] []
     |- |= implies (keyword_value_listp l)
             (keyword_value_listp (assoc_keyword key l)),
*)

(*
     [oracles: DEFTHM ACL2::CONSP-ASSOC-EQ, DISK_THM] [axioms: ] []
     |- |= implies (alistp l)
             (ite (consp (assoc_eq name l)) (consp (assoc_eq name l))
                (equal (assoc_eq name l) nil)),
*)

(*
     [oracles: DEFTHM ACL2::ARRAY1P-FORWARD, DISK_THM] [axioms: ] []
     |- |= implies (array1p name l)
             (andl
                [symbolp name; alistp l;
                 keyword_value_listp (cdr (assoc_eq (ksym "HEADER") l));
                 true_listp
                   (cadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 equal
                   (length
                      (cadr
                         (assoc_keyword (ksym "DIMENSIONS")
                            (cdr (assoc_eq (ksym "HEADER") l))))) (nat 1);
                 integerp
                   (caadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 integerp
                   (cadr
                      (assoc_keyword (ksym "MAXIMUM-LENGTH")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 less (nat 0)
                   (caadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 less
                   (caadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))))
                   (cadr
                      (assoc_keyword (ksym "MAXIMUM-LENGTH")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 not
                   (less (nat 2147483647)
                      (cadr
                         (assoc_keyword (ksym "MAXIMUM-LENGTH")
                            (cdr (assoc_eq (ksym "HEADER") l)))));
                 bounded_integer_alistp l
                   (caadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))))]),
*)

(*
     [oracles: DEFTHM ACL2::ARRAY1P-LINEAR, DISK_THM] [axioms: ] []
     |- |= implies (array1p name l)
             (andl
                [less (nat 0)
                   (caadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 less
                   (caadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))))
                   (cadr
                      (assoc_keyword (ksym "MAXIMUM-LENGTH")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 not
                   (less (nat 2147483647)
                      (cadr
                         (assoc_keyword (ksym "MAXIMUM-LENGTH")
                            (cdr (assoc_eq (ksym "HEADER") l)))))]),
*)

(*
     [oracles: DEFTHM ACL2::ARRAY2P-FORWARD, DISK_THM] [axioms: ] []
     |- |= implies (array2p name l)
             (andl
                [symbolp name; alistp l;
                 keyword_value_listp (cdr (assoc_eq (ksym "HEADER") l));
                 true_listp
                   (cadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 equal
                   (length
                      (cadr
                         (assoc_keyword (ksym "DIMENSIONS")
                            (cdr (assoc_eq (ksym "HEADER") l))))) (nat 2);
                 integerp
                   (caadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 integerp
                   (cadadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 integerp
                   (cadr
                      (assoc_keyword (ksym "MAXIMUM-LENGTH")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 less (nat 0)
                   (caadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 less (nat 0)
                   (cadadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 less
                   (mult
                      (caadr
                         (assoc_keyword (ksym "DIMENSIONS")
                            (cdr (assoc_eq (ksym "HEADER") l))))
                      (cadadr
                         (assoc_keyword (ksym "DIMENSIONS")
                            (cdr (assoc_eq (ksym "HEADER") l)))))
                   (cadr
                      (assoc_keyword (ksym "MAXIMUM-LENGTH")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 not
                   (less (nat 2147483647)
                      (cadr
                         (assoc_keyword (ksym "MAXIMUM-LENGTH")
                            (cdr (assoc_eq (ksym "HEADER") l)))));
                 bounded_integer_alistp2 l
                   (caadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))))
                   (cadadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))))]),
*)

(*
     [oracles: DEFTHM ACL2::ARRAY2P-LINEAR, DISK_THM] [axioms: ] []
     |- |= implies (array2p name l)
             (andl
                [less (nat 0)
                   (caadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 less (nat 0)
                   (cadadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 less
                   (mult
                      (caadr
                         (assoc_keyword (ksym "DIMENSIONS")
                            (cdr (assoc_eq (ksym "HEADER") l))))
                      (cadadr
                         (assoc_keyword (ksym "DIMENSIONS")
                            (cdr (assoc_eq (ksym "HEADER") l)))))
                   (cadr
                      (assoc_keyword (ksym "MAXIMUM-LENGTH")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 not
                   (less (nat 2147483647)
                      (cadr
                         (assoc_keyword (ksym "MAXIMUM-LENGTH")
                            (cdr (assoc_eq (ksym "HEADER") l)))))]),
*)

(*
     [oracles: DEFTHM ACL2::CONSP-ASSOC, DISK_THM] [axioms: ] []
     |- |= implies (alistp l)
             (ite (consp (assoc name l)) (consp (assoc name l))
                (equal (assoc name l) nil)),
*)

(*
     [oracles: DEFTHM ACL2::ARRAY1P-CONS, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [less n
                   (caadr
                      (assoc_keyword (ksym "DIMENSIONS")
                         (cdr (assoc_eq (ksym "HEADER") l))));
                 not (less n (nat 0)); integerp n; array1p name l])
             (array1p name (cons (cons n val) l)),
*)

(*
     [oracles: DEFTHM ACL2::ARRAY2P-CONS, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [less j (cadr (dimensions name l)); not (less j (nat 0));
                 integerp j; less i (car (dimensions name l));
                 not (less i (nat 0)); integerp i; array2p name l])
             (array2p name (cons (cons (cons i j) val) l)),
*)

(*
     [oracles: DEFTHM ACL2::32-BIT-INTEGERP-FORWARD-TO-INTEGERP] [axioms: ]
     [] |- |= implies (acl2_32_bit_integerp x) (integerp x),
*)

(*
     [oracles: DEFTHM ACL2::RATIONAL-LISTP-FORWARD-TO-TRUE-LISTP] [axioms: ]
     [] |- |= implies (rational_listp x) (true_listp x),
*)

(*
     [oracles: DEFTHM ACL2::INTEGER-LISTP-FORWARD-TO-RATIONAL-LISTP]
     [axioms: ] [] |- |= implies (integer_listp x) (rational_listp x),
*)

(*
     [oracles: DEFTHM ACL2::32-BIT-INTEGER-LISTP-FORWARD-TO-INTEGER-LISTP]
     [axioms: ] []
     |- |= implies (acl2_32_bit_integer_listp x) (integer_listp x),
*)

(*
     [oracles: DEFTHM ACL2::KNOWN-PACKAGE-ALISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-ALISTP,
                DISK_THM]
     [axioms: ] []
     |- |= implies (known_package_alistp x)
             (andl [true_list_listp x; alistp x]),
*)

(*
     [oracles: DEFTHM ACL2::TIMER-ALISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-SYMBOL-ALISTP,
                DISK_THM]
     [axioms: ] []
     |- |= implies (timer_alistp x)
             (andl [true_list_listp x; symbol_alistp x]),
*)

(*
     [oracles: DEFTHM ACL2::TYPED-IO-LISTP-FORWARD-TO-TRUE-LISTP] [axioms: ]
     [] |- |= implies (typed_io_listp x typ) (true_listp x),
*)

(*
     [oracles: DEFTHM ACL2::OPEN-CHANNEL1-FORWARD-TO-TRUE-LISTP-AND-CONSP,
                DISK_THM]
     [axioms: ] []
     |- |= implies (open_channel1 x) (andl [true_listp x; consp x]),
*)

(*
     [oracles: DEFTHM ACL2::OPEN-CHANNELS-P-FORWARD, DISK_THM] [axioms: ] []
     |- |= implies (open_channels_p x)
             (andl [ordered_symbol_alistp x; true_list_listp x]),
*)

(*
     [oracles: DEFTHM ACL2::FILE-CLOCK-P-FORWARD-TO-INTEGERP] [axioms: ] []
     |- |= implies (file_clock_p x) (natp x),
*)

(*
     [oracles: DEFTHM ACL2::READABLE-FILE-FORWARD-TO-TRUE-LISTP-AND-CONSP,
                DISK_THM]
     [axioms: ] []
     |- |= implies (readable_file x) (andl [true_listp x; consp x]),
*)

(*
     [oracles: DEFTHM ACL2::READABLE-FILES-LISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-ALISTP,
                DISK_THM]
     [axioms: ] []
     |- |= implies (readable_files_listp x)
             (andl [true_list_listp x; alistp x]),
*)

(*
     [oracles: DEFTHM ACL2::READABLE-FILES-P-FORWARD-TO-READABLE-FILES-LISTP]
     [axioms: ] []
     |- |= implies (readable_files_p x) (readable_files_listp x),
*)

(*
     [oracles: DEFTHM ACL2::WRITTEN-FILE-FORWARD-TO-TRUE-LISTP-AND-CONSP,
                DISK_THM]
     [axioms: ] []
     |- |= implies (written_file x) (andl [true_listp x; consp x]),
*)

(*
     [oracles: DEFTHM ACL2::WRITTEN-FILE-LISTP-FORWARD-TO-TRUE-LIST-LISTP-AND-ALISTP,
                DISK_THM]
     [axioms: ] []
     |- |= implies (written_file_listp x)
             (andl [true_list_listp x; alistp x]),
*)

(*
     [oracles: DEFTHM ACL2::WRITTEN-FILES-P-FORWARD-TO-WRITTEN-FILE-LISTP]
     [axioms: ] [] |- |= implies (written_files_p x) (written_file_listp x),
*)

(*
     [oracles: DEFTHM ACL2::READ-FILE-LISTP1-FORWARD-TO-TRUE-LISTP-AND-CONSP,
                DISK_THM]
     [axioms: ] []
     |- |= implies (read_file_listp1 x) (andl [true_listp x; consp x]),
*)

(*
     [oracles: DEFTHM ACL2::READ-FILE-LISTP-FORWARD-TO-TRUE-LIST-LISTP]
     [axioms: ] [] |- |= implies (read_file_listp x) (true_list_listp x),
*)

(*
     [oracles: DEFTHM ACL2::READ-FILES-P-FORWARD-TO-READ-FILE-LISTP]
     [axioms: ] [] |- |= implies (read_files_p x) (read_file_listp x),
*)

(*
     [oracles: DEFTHM ACL2::WRITABLE-FILE-LISTP1-FORWARD-TO-TRUE-LISTP-AND-CONSP,
                DISK_THM]
     [axioms: ] []
     |- |= implies (writable_file_listp1 x) (andl [true_listp x; consp x]),
*)

(*
     [oracles: DEFTHM ACL2::WRITABLE-FILE-LISTP-FORWARD-TO-TRUE-LIST-LISTP]
     [axioms: ] [] |- |= implies (writable_file_listp x) (true_list_listp x),
*)

(*
     [oracles: DEFTHM ACL2::WRITEABLE-FILES-P-FORWARD-TO-WRITABLE-FILE-LISTP]
     [axioms: ] []
     |- |= implies (writeable_files_p x) (writable_file_listp x),
*)

(*
     [oracles: DEFTHM ACL2::STATE-P1-FORWARD, DISK_THM] [axioms: ] []
     |- |= implies (state_p1 x)
             (andl
                [true_listp x; equal (length x) (nat 15);
                 open_channels_p (nth (nat 0) x);
                 open_channels_p (nth (nat 1) x);
                 ordered_symbol_alistp (nth (nat 2) x);
                 all_boundp
                   (List
                      [List [asym "ACCUMULATED-TTREE"];
                       List [asym "ACCUMULATED-WARNINGS"];
                       cons (asym "ACL2-VERSION") (str "ACL2 Version 2.9.3");
                       List [asym "AXIOMSP"]; List [asym "BDDNOTES"];
                       List [asym "CERTIFY-BOOK-FILE"];
                       List [asym "CONNECTED-BOOK-DIRECTORY"];
                       List [asym "CURRENT-ACL2-WORLD"];
                       cons (asym "CURRENT-PACKAGE") (str ACL2);
                       cons (asym "DEFAXIOMS-OKP-CERT") t;
                       List [asym "ERROR-TRACE-STACK"];
                       List [asym "EVISCERATE-HIDE-TERMS"];
                       cons (asym "FMT-HARD-RIGHT-MARGIN") (nat 77);
                       cons (asym "FMT-SOFT-RIGHT-MARGIN") (nat 65);
                       List [asym "GSTACKP"];
                       cons (asym "GUARD-CHECKING-ON") t;
                       List [asym "IN-CERTIFY-BOOK-FLG"];
                       List [asym "IN-LOCAL-FLG"];
                       List [asym "IN-PROVE-FLG"];
                       List [asym "INCLUDE-BOOK-ALIST-STATE"];
                       List [asym "INFIXP"];
                       List [asym "INHIBIT-OUTPUT-LST"; asym "SUMMARY"];
                       cons (asym "LD-LEVEL") (nat 0);
                       List [asym "LD-REDEFINITION-ACTION"];
                       List [asym "LD-SKIP-PROOFSP"];
                       List [asym "MATCH-FREE-ERROR"];
                       cons (asym "MORE-DOC-MAX-LINES") (nat 45);
                       cons (asym "MORE-DOC-MIN-LINES") (nat 35);
                       List [asym "MORE-DOC-STATE"];
                       List [asym "PACKAGES-CREATED-BY-DEFPKG"];
                       cons (asym "PRINT-BASE") (nat 10);
                       cons (asym "PRINT-CASE") (ksym "UPCASE");
                       List [asym "PRINT-CLAUSE-IDS"];
                       cons (asym "PRINT-DOC-START-COLUMN") (nat 15);
                       cons (asym "PROMPT-FUNCTION")
                         (asym "DEFAULT-PRINT-PROMPT");
                       List [asym "PROOF-TREE-CTX"];
                       cons (asym "PROOFS-CO")
                         (osym "STANDARD-CHARACTER-OUTPUT-0");
                       List
                         [asym "RAW-ARITY-ALIST";
                          cons (asym "ER-PROGN") (csym "LAST");
                          cons (csym "EVAL-WHEN") (ksym "LAST");
                          cons (csym "LET") (ksym "LAST");
                          cons (csym "LET*") (ksym "LAST");
                          cons (asym "MV-LET") (ksym "LAST");
                          cons (asym "PROG2$") (ksym "LAST");
                          cons (csym "PROGN") (ksym "LAST");
                          cons (csym "THE") (ksym "LAST");
                          cons (csym "TIME") (ksym "LAST");
                          cons (csym "TRACE") (nat 1);
                          cons (csym "UNTRACE") (nat 1)];
                       List [asym "SAFE-MODE"];
                       List [asym "SAVED-OUTPUT-REVERSED"];
                       List [asym "SAVED-OUTPUT-TOKEN-LST"];
                       List [asym "SAVED-OUTPUT-P"];
                       cons (asym "SKIP-PROOFS-OKP-CERT") t;
                       List [asym "SKIPPED-PROOFSP"];
                       cons (asym "STANDARD-CO")
                         (osym "STANDARD-CHARACTER-OUTPUT-0");
                       cons (asym "STANDARD-OI")
                         (osym "STANDARD-OBJECT-INPUT-0");
                       List [asym "TAINTED-OKP"]; List [asym "TIMER-ALIST"];
                       cons (asym "TRACE-CO")
                         (osym "STANDARD-CHARACTER-OUTPUT-0");
                       cons (asym "TRANSLATE-ERROR-DEPTH") (int ~1);
                       cons (asym "TRIPLE-PRINT-PREFIX") (str " ");
                       List [asym "UNDONE-WORLDS-KILL-RING"; nil; nil; nil];
                       List [asym "WINDOW-INTERFACEP"];
                       List [asym "WORMHOLE-NAME"];
                       List [asym "WORMHOLE-OUTPUT"]]) (nth (nat 2) x);
                 worldp
                   (cdr (assoc (asym "CURRENT-ACL2-WORLD") (nth (nat 2) x)));
                 symbol_alistp
                   (fgetprop (asym "ACL2-DEFAULTS-TABLE")
                      (asym "TABLE-ALIST") nil
                      (cdr
                         (assoc (asym "CURRENT-ACL2-WORLD")
                            (nth (nat 2) x))));
                 timer_alistp
                   (cdr (assoc (asym "TIMER-ALIST") (nth (nat 2) x)));
                 known_package_alistp
                   (fgetprop (asym "KNOWN-PACKAGE-ALIST")
                      (asym "GLOBAL-VALUE") nil
                      (cdr
                         (assoc (asym "CURRENT-ACL2-WORLD")
                            (nth (nat 2) x)))); true_listp (nth (nat 3) x);
                 acl2_32_bit_integer_listp (nth (nat 4) x);
                 integerp (nth (nat 5) x); integer_listp (nth (nat 6) x);
                 rational_listp (nth (nat 7) x);
                 file_clock_p (nth (nat 8) x);
                 readable_files_p (nth (nat 9) x);
                 written_files_p (nth (nat 10) x);
                 read_files_p (nth (nat 11) x);
                 writeable_files_p (nth (nat 12) x);
                 true_list_listp (nth (nat 13) x);
                 symbol_alistp (nth (nat 14) x)]),
*)

(*
     [oracles: DEFTHM ACL2::STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1]
     [axioms: ] [] |- |= implies (state_p state_state) (state_p1 state_state),
*)

(*
     [oracles: DEFTHM ACL2::INTEGER-RANGE-P-FORWARD, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [integer_range_p lower (add (nat 1) upper_1) x;
                 integerp upper_1])
             (andl [integerp x; not (less x lower); not (less upper_1 x)]),
*)

(*
     [oracles: DEFTHM ACL2::SIGNED-BYTE-P-FORWARD-TO-INTEGERP] [axioms: ] []
     |- |= implies (signed_byte_p n x) (integerp x),
*)

(*
     [oracles: DEFTHM ACL2::UNSIGNED-BYTE-P-FORWARD-TO-NONNEGATIVE-INTEGERP,
                DISK_THM]
     [axioms: ] []
     |- |= implies (unsigned_byte_p n x)
             (andl [integerp x; not (less x (nat 0))]),
*)

(*
     [oracles: DEFTHM ACL2::STRING<-L-ASYMMETRIC, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [eqlable_listp x1; eqlable_listp x2; integerp i;
                 string_less_l x1 x2 i]) (not (string_less_l x2 x1 i)),
*)

(*
     [oracles: DEFTHM ACL2::SYMBOL-<-ASYMMETRIC, DISK_THM] [axioms: ] []
     |- |= implies
             (andl [symbolp sym1; symbolp sym2; symbol_less sym1 sym2])
             (not (symbol_less sym2 sym1)),
*)

(*
     [oracles: DEFTHM ACL2::STRING<-L-TRANSITIVE, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [string_less_l x y i; string_less_l y z j; integerp i;
                 integerp j; integerp k; character_listp x;
                 character_listp y; character_listp z])
             (string_less_l x z k),
*)

(*
     [oracles: DEFTHM ACL2::SYMBOL-<-TRANSITIVE, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [symbol_less x y; symbol_less y z; symbolp x; symbolp y;
                 symbolp z]) (symbol_less x z),
*)

(*
     [oracles: DEFTHM ACL2::STRING<-L-TRICHOTOMY, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [not (string_less_l x y i); integerp i; integerp j;
                 character_listp x; character_listp y])
             (iff (string_less_l y x j) (not (equal x y))),
*)

(*
     [oracles: DEFTHM ACL2::SYMBOL-<-TRICHOTOMY, DISK_THM] [axioms: ] []
     |- |= implies (andl [symbolp x; symbolp y; not (symbol_less x y)])
             (iff (symbol_less y x) (not (equal x y))),
*)

(*
     [oracles: DEFTHM ACL2::ORDERED-SYMBOL-ALISTP-REMOVE-FIRST-PAIR,
                DISK_THM]
     [axioms: ] []
     |- |= implies
             (andl [ordered_symbol_alistp l; symbolp key; assoc_eq key l])
             (ordered_symbol_alistp (remove_first_pair key l)),
*)

(*
     [oracles: DEFTHM ACL2::SYMBOL-<-IRREFLEXIVE] [axioms: ] []
     |- |= implies (symbolp x) (not (symbol_less x x)),
*)

(*
     [oracles: DEFTHM ACL2::ORDERED-SYMBOL-ALISTP-ADD-PAIR, DISK_THM]
     [axioms: ] []
     |- |= implies (andl [ordered_symbol_alistp gs; symbolp w5])
             (ordered_symbol_alistp (add_pair w5 w6 gs)),
*)

(*
     [oracles: DEFTHM ACL2::ORDERED-SYMBOL-ALISTP-GETPROPS, DISK_THM]
     [axioms: ] []
     |- |= implies (andl [worldp w; symbolp world_name; symbolp key])
             (ordered_symbol_alistp (getprops key world_name w)),
*)

(*
     [oracles: DEFTHM ACL2::TRUE-LIST-LISTP-FORWARD-TO-TRUE-LISTP-ASSOC-EQ]
     [axioms: ] []
     |- |= implies (true_list_listp l) (true_listp (assoc_eq key l)),
*)

(*
     [oracles: DEFTHM ACL2::TRUE-LISTP-CADR-ASSOC-EQ-FOR-OPEN-CHANNELS-P,
                DISK_THM]
     [axioms: ] []
     |- |= implies (open_channels_p alist)
             (true_listp (cadr (assoc_eq key alist))),
*)

(*
     [oracles: DEFTHM ACL2::NTH-UPDATE-NTH, DISK_THM] [axioms: ] []
     |- |= equal (nth m (update_nth n val l))
             (ite (equal (nfix m) (nfix n)) val (nth m l)),
*)

(*
     [oracles: DEFTHM ACL2::TRUE-LISTP-UPDATE-NTH] [axioms: ] []
     |- |= implies (true_listp l) (true_listp (update_nth key val l)),
*)

(*
     [oracles: DEFTHM ACL2::NTH-UPDATE-NTH-ARRAY, DISK_THM] [axioms: ] []
     |- |= equal (nth m (update_nth_array n i val l))
             (ite (equal (nfix m) (nfix n)) (update_nth i val (nth m l))
                (nth m l)),
*)

(*
     [oracles: DEFTHM ACL2::LEN-UPDATE-NTH, DISK_THM] [axioms: ] []
     |- |= equal (len (update_nth n val x))
             (max (add (nat 1) (nfix n)) (len x)),
*)

(*
     [oracles: DEFTHM ACL2::UPDATE-RUN-TIMES-PRESERVES-STATE-P1, DISK_THM]
     [axioms: ] []
     |- |= implies (andl [state_p1 state; rational_listp times])
             (state_p1 (update_run_times times state)),
*)

(*
     [oracles: DEFTHM ACL2::READ-RUN-TIME-PRESERVES-STATE-P1, DISK_THM]
     [axioms: ] []
     |- |= implies (state_p1 state)
             (state_p1 (nth (nat 1) (read_run_time state))),
*)

(*
     [oracles: DEFTHM ACL2::NTH-0-READ-RUN-TIME-TYPE-PRESCRIPTION, DISK_THM]
     [axioms: ] []
     |- |= implies (state_p1 state)
             (rationalp (nth (nat 0) (read_run_time state))),
*)

(*
     [oracles: DEFTHM ACL2::RATIONALP-+, DISK_THM] [axioms: ] []
     |- |= implies (andl [rationalp x; rationalp y]) (rationalp (add x y)),
*)

(*
     [oracles: DEFTHM ACL2::RATIONALP-*, DISK_THM] [axioms: ] []
     |- |= implies (andl [rationalp x; rationalp y]) (rationalp (mult x y)),
*)

(*
     [oracles: DEFTHM ACL2::RATIONALP-UNARY--] [axioms: ] []
     |- |= implies (rationalp x) (rationalp (unary_minus x)),
*)

(*
     [oracles: DEFTHM ACL2::RATIONALP-UNARY-/] [axioms: ] []
     |- |= implies (rationalp x) (rationalp (reciprocal x)),
*)

(*
     [oracles: DEFTHM ACL2::RATIONALP-IMPLIES-ACL2-NUMBERP] [axioms: ] []
     |- |= implies (rationalp x) (acl2_numberp x),
*)

(*
     [oracles: DEFTHM ACL2::NTH-0-CONS, DISK_THM] [axioms: ] []
     |- |= equal (nth (nat 0) (cons a l)) a,
*)

(*
     [oracles: DEFTHM ACL2::NTH-ADD1, DISK_THM] [axioms: ] []
     |- |= implies (andl [integerp n; not (less n (nat 0))])
             (equal (nth (add (nat 1) n) (cons a l)) (nth n l)),
*)

(*
     [oracles: DEFTHM ACL2::MAIN-TIMER-TYPE-PRESCRIPTION, DISK_THM]
     [axioms: ] []
     |- |= implies (state_p1 state)
             (andl [consp (main_timer state); true_listp (main_timer state)]),
*)

(*
     [oracles: DEFTHM ACL2::ORDERED-SYMBOL-ALISTP-ADD-PAIR-FORWARD, DISK_THM]
     [axioms: ] []
     |- |= implies (andl [symbolp key; ordered_symbol_alistp l])
             (ordered_symbol_alistp (add_pair key value l)),
*)

(*
     [oracles: DEFTHM ACL2::ASSOC-ADD-PAIR, DISK_THM] [axioms: ] []
     |- |= implies (andl [symbolp sym2; ordered_symbol_alistp alist])
             (equal (assoc sym1 (add_pair sym2 val alist))
                (ite (equal sym1 sym2) (cons sym1 val) (assoc sym1 alist))),
*)

(*
     [oracles: DEFTHM ACL2::ADD-PAIR-PRESERVES-ALL-BOUNDP, DISK_THM]
     [axioms: ] []
     |- |= implies
             (andl
                [eqlable_alistp alist1; ordered_symbol_alistp alist2;
                 all_boundp alist1 alist2; symbolp acl2_sym])
             (all_boundp alist1 (add_pair acl2_sym val alist2)),
*)

(*
     [oracles: DEFTHM ACL2::STATE-P1-UPDATE-MAIN-TIMER, DISK_THM] [axioms: ]
     []
     |- |= implies (state_p1 state)
             (state_p1
                (update_nth (nat 2)
                   (add_pair (asym "MAIN-TIMER") val (nth (nat 2) state))
                   state)),
*)

(*
     [oracles: DEFTHM ACL2::ALL-BOUNDP-PRESERVES-ASSOC, DISK_THM] [axioms: ]
     []
     |- |= implies
             (andl
                [eqlable_alistp tbl1; eqlable_alistp tbl2;
                 all_boundp tbl1 tbl2; symbolp x; assoc_eq x tbl1])
             (assoc x tbl2),
*)

(*
     [oracles: DEFTHM ACL2::STATE-P1-UPDATE-NTH-2-WORLD, DISK_THM] [axioms: ]
     []
     |- |= implies
             (andl
                [state_p1 state; worldp wrld;
                 known_package_alistp
                   (fgetprop (asym "KNOWN-PACKAGE-ALIST")
                      (asym "GLOBAL-VALUE") nil wrld);
                 symbol_alistp
                   (fgetprop (asym "ACL2-DEFAULTS-TABLE")
                      (asym "TABLE-ALIST") nil wrld)])
             (state_p1
                (update_nth (nat 2)
                   (add_pair (asym "CURRENT-ACL2-WORLD") wrld
                      (nth (nat 2) state)) state)),
*)

(*
     [oracles: DEFTHM ACL2::TRUE-LIST-LISTP-FORWARD-TO-TRUE-LISTP-ASSOC-EQUAL]
     [axioms: ] []
     |- |= implies (true_list_listp l) (true_listp (assoc_equal key l)),
*)

(*
     [oracles: DEFTHM ACL2::NATP-POSITION-AC, DISK_THM] [axioms: ] []
     |- |= implies (andl [integerp acc; not (less acc (nat 0))])
             (ite (equal (position_ac item lst acc) nil)
                (equal (position_ac item lst acc) nil)
                (andl
                   [integerp (position_ac item lst acc);
                    not (less (position_ac item lst acc) (nat 0))])),
*)

(*
     [oracles: DEFTHM ACL2::BOOLEAN-LISTP-CONS, DISK_THM] [axioms: ] []
     |- |= equal (boolean_listp (cons x y))
             (andl [booleanp x; boolean_listp y]),
*)

(*
     [oracles: DEFTHM ACL2::BOOLEAN-LISTP-FORWARD, DISK_THM] [axioms: ] []
     |- |= implies (boolean_listp (cons a lst))
             (andl [booleanp a; boolean_listp lst]),
*)

(*
     [oracles: DEFTHM ACL2::BOOLEAN-LISTP-FORWARD-TO-SYMBOL-LISTP] [axioms: ]
     [] |- |= implies (boolean_listp x) (symbol_listp x),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-+, DISK_THM] [axioms: ] []
     |- |= equal (add x y)
             (itel
                [(acl2_numberp x,ite (acl2_numberp y) (add x y) x);
                 (acl2_numberp y,y)] (nat 0)),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-+-1] [axioms: ] []
     |- |= implies (not (acl2_numberp x)) (equal (add x y) (fix y)),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-+-2] [axioms: ] []
     |- |= implies (not (acl2_numberp y)) (equal (add x y) (fix x)),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-*, DISK_THM] [axioms: ] []
     |- |= equal (mult x y)
             (ite (acl2_numberp x) (ite (acl2_numberp y) (mult x y) (nat 0))
                (nat 0)),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-*-1, DISK_THM] [axioms: ] []
     |- |= implies (not (acl2_numberp x)) (equal (mult x y) (nat 0)),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-*-2, DISK_THM] [axioms: ] []
     |- |= implies (not (acl2_numberp y)) (equal (mult x y) (nat 0)),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-UNARY-MINUS, DISK_THM] [axioms: ]
     []
     |- |= equal (unary_minus x)
             (ite (acl2_numberp x) (unary_minus x) (nat 0)),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-UNARY-MINUS, DISK_THM] [axioms: ] []
     |- |= implies (not (acl2_numberp x)) (equal (unary_minus x) (nat 0)),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-UNARY-/, DISK_THM] [axioms: ] []
     |- |= equal (reciprocal x)
             (ite (andl [acl2_numberp x; not (equal x (nat 0))])
                (reciprocal x) (nat 0)),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-UNARY-/, DISK_THM] [axioms: ] []
     |- |= implies
             (ite (not (acl2_numberp x)) (not (acl2_numberp x))
                (equal x (nat 0))) (equal (reciprocal x) (nat 0)),
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
     [oracles: DEFTHM ACL2::DEFAULT-<-1, DISK_THM] [axioms: ] []
     |- |= implies (not (acl2_numberp x)) (equal (less x y) (less (nat 0) y)),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-<-2, DISK_THM] [axioms: ] []
     |- |= implies (not (acl2_numberp y)) (equal (less x y) (less x (nat 0))),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-CAR, DISK_THM] [axioms: ] []
     |- |= equal (car x) (andl [consp x; car x]),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-CAR] [axioms: ] []
     |- |= implies (not (consp x)) (equal (car x) nil),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-CDR, DISK_THM] [axioms: ] []
     |- |= equal (cdr x) (andl [consp x; cdr x]),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-CDR] [axioms: ] []
     |- |= implies (not (consp x)) (equal (cdr x) nil),
*)

(*
     [oracles: DEFTHM ACL2::CONS-CAR-CDR, DISK_THM] [axioms: ] []
     |- |= equal (cons (car x) (cdr x)) (ite (consp x) x (List [nil])),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-CHAR-CODE, DISK_THM] [axioms: ]
     [] |- |= equal (char_code x) (ite (characterp x) (char_code x) (nat 0)),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-CHAR-CODE, DISK_THM] [axioms: ] []
     |- |= implies (not (characterp x)) (equal (char_code x) (nat 0)),
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
     [oracles: DEFTHM ACL2::DEFAULT-COMPLEX-1, DISK_THM] [axioms: ] []
     |- |= implies (not (rationalp x))
             (equal (complex x y) (complex (nat 0) y)),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-COMPLEX-2, DISK_THM] [axioms: ] []
     |- |= implies (not (rationalp y))
             (equal (complex x y) (ite (rationalp x) x (nat 0))),
*)

(*
     [oracles: DEFTHM ACL2::COMPLEX-0, DISK_THM] [axioms: ] []
     |- |= equal (complex x (nat 0)) (rfix x),
*)

(*
     [oracles: DEFTHM ACL2::ADD-DEF-COMPLEX] [axioms: ] []
     |- |= equal (add x y)
             (complex (add (realpart x) (realpart y))
                (add (imagpart x) (imagpart y))),
*)

(*
     [oracles: DEFTHM ACL2::REALPART-+] [axioms: ] []
     |- |= equal (realpart (add x y)) (add (realpart x) (realpart y)),
*)

(*
     [oracles: DEFTHM ACL2::IMAGPART-+] [axioms: ] []
     |- |= equal (imagpart (add x y)) (add (imagpart x) (imagpart y)),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-COERCE, DISK_THM] [axioms: ] []
     |- |= equal (coerce x y)
             (ite (equal y (csym "LIST"))
                (andl [stringp x; coerce x (csym "LIST")])
                (coerce (acl2_make_character_list x) (csym "STRING"))),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-COERCE-1, DISK_THM] [axioms: ] []
     |- |= implies (not (stringp x)) (equal (coerce x (csym "LIST")) nil),
*)

(*
     [oracles: DEFTHM ACL2::MAKE-CHARACTER-LIST-MAKE-CHARACTER-LIST]
     [axioms: ] []
     |- |= equal (acl2_make_character_list (acl2_make_character_list x))
             (acl2_make_character_list x),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-COERCE-2, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [synp nil
                   (List
                      [asym "SYNTAXP";
                       List
                         [csym "NOT";
                          List
                            [csym "EQUAL"; asym "Y";
                             List
                               [csym "QUOTE";
                                List [csym "QUOTE"; csym "STRING"]]]]])
                   (List
                      [csym "IF";
                       List
                         [csym "NOT";
                          List
                            [csym "EQUAL"; asym "Y";
                             List
                               [csym "QUOTE";
                                List [csym "QUOTE"; csym "STRING"]]]];
                       List [csym "QUOTE"; t]; List [csym "QUOTE"; nil]]);
                 not (equal y (csym "LIST"))])
             (equal (coerce x y) (coerce x (csym "STRING"))),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-COERCE-3, DISK_THM] [axioms: ] []
     |- |= implies (not (consp x))
             (equal (coerce x (csym "STRING")) (str "")),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-DENOMINATOR, DISK_THM] [axioms: ]
     []
     |- |= equal (denominator x) (ite (rationalp x) (denominator x) (nat 1)),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-DENOMINATOR, DISK_THM] [axioms: ] []
     |- |= implies (not (rationalp x)) (equal (denominator x) (nat 1)),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-IMAGPART, DISK_THM] [axioms: ] []
     |- |= equal (imagpart x) (ite (acl2_numberp x) (imagpart x) (nat 0)),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-IMAGPART, DISK_THM] [axioms: ] []
     |- |= implies (not (acl2_numberp x)) (equal (imagpart x) (nat 0)),
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
     [oracles: DEFTHM ACL2::DEFAULT-NUMERATOR, DISK_THM] [axioms: ] []
     |- |= implies (not (rationalp x)) (equal (numerator x) (nat 0)),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-REALPART, DISK_THM] [axioms: ] []
     |- |= equal (realpart x) (ite (acl2_numberp x) (realpart x) (nat 0)),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-REALPART, DISK_THM] [axioms: ] []
     |- |= implies (not (acl2_numberp x)) (equal (realpart x) (nat 0)),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-SYMBOL-NAME, DISK_THM] [axioms: ]
     []
     |- |= equal (symbol_name x) (ite (symbolp x) (symbol_name x) (str "")),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-SYMBOL-NAME] [axioms: ] []
     |- |= implies (not (symbolp x)) (equal (symbol_name x) (str "")),
*)

(*
     [oracles: DEFAXIOM ACL2::COMPLETION-OF-SYMBOL-PACKAGE-NAME, DISK_THM]
     [axioms: ] []
     |- |= equal (symbol_package_name x)
             (ite (symbolp x) (symbol_package_name x) (str "")),
*)

(*
     [oracles: DEFTHM ACL2::DEFAULT-SYMBOL-PACKAGE-NAME] [axioms: ] []
     |- |= implies (not (symbolp x)) (equal (symbol_package_name x) (str "")),
*)

(*
     [oracles: DEFTHM ACL2::PSEUDO-TERM-LISTP-MFC-CLAUSE] [axioms: ] []
     |- |= pseudo_term_listp (mfc_clause mfc),
*)

(*
     [oracles: DEFTHM ACL2::TYPE-ALISTP-MFC-TYPE-ALIST] [axioms: ] []
     |- |= type_alistp (mfc_type_alist mfc),
*)

(*
     [oracles: DEFTHM ACL2::BAD-ATOM-COMPOUND-RECOGNIZER, DISK_THM]
     [axioms: ] []
     |- |= iff (bad_atom x)
             (not
                (itel
                   [(consp x,consp x); (acl2_numberp x,acl2_numberp x);
                    (symbolp x,symbolp x); (characterp x,characterp x)]
                   (stringp x))),
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

(*
     [oracles: DEFTHM ACL2::ALPHORDER-REFLEXIVE] [axioms: ] []
     |- |= implies (not (consp x)) (alphorder x x),
*)

(*
     [oracles: DEFTHM ACL2::ALPHORDER-TRANSITIVE, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [alphorder x y; alphorder y z; not (consp x); not (consp y);
                 not (consp z)]) (alphorder x z),
*)

(*
     [oracles: DEFTHM ACL2::ALPHORDER-ANTI-SYMMETRIC, DISK_THM] [axioms: ] []
     |- |= implies
             (andl
                [not (consp x); not (consp y); alphorder x y; alphorder y x])
             (equal x y),
*)

(*
     [oracles: DEFTHM ACL2::ALPHORDER-TOTAL, DISK_THM] [axioms: ] []
     |- |= implies (andl [not (consp x); not (consp y)])
             (ite (alphorder x y) (alphorder x y) (alphorder y x)),
*)

(*
     [oracles: DEFTHM ACL2::LEXORDER-REFLEXIVE] [axioms: ] []
     |- |= lexorder x x,
*)

(*
     [oracles: DEFTHM ACL2::LEXORDER-ANTI-SYMMETRIC, DISK_THM] [axioms: ] []
     |- |= implies (andl [lexorder x y; lexorder y x]) (equal x y),
*)

(*
     [oracles: DEFTHM ACL2::LEXORDER-TRANSITIVE, DISK_THM] [axioms: ] []
     |- |= implies (andl [lexorder x y; lexorder y z]) (lexorder x z),
*)

(*
     [oracles: DEFTHM ACL2::LEXORDER-TOTAL, DISK_THM] [axioms: ] []
     |- |= ite (lexorder x y) (lexorder x y) (lexorder y x)]
*)

val _ = export_acl2_theory();
