(*****************************************************************************)
(* Define complex rationals                                                  *)
(*****************************************************************************)

(* The commented out stuff below should be loaded in interactive sessions
quietdec := true;
map
 load
 ["intLib","gcdTheory", "fracLib", "ratLib"];
open intLib gcdTheory fracLib ratLib ratTheory;
quietdec := false;
*)

Theory complex_rational
Ancestors
  gcd rat
Libs
  fracLib ratLib

(*****************************************************************************)
(* A complex rational x+yi is a pair of rational numbers.                    *)
(* The type ``:complex_rational`` is a datatype isomorphic to                *)
(* ``:rat # rat``, with curried constructor ``COMPLEX_RATIONAL``.            *)
(*****************************************************************************)
Datatype: complex_rational = COMPLEX_RATIONAL of rat => rat
End

(*****************************************************************************)
(* Abbreviation for the complex rational constructor                         *)
(*****************************************************************************)
val _ = overload_on("com", ``COMPLEX_RATIONAL``);

(*****************************************************************************)
(* Complex rationals representing 0 and 1                                    *)
(*****************************************************************************)
val com_0_def = Define `com_0 = com rat_0 rat_0`
and com_1_def = Define `com_1 = com rat_1 rat_0`;

(*****************************************************************************)
(* Define complex addition                                                   *)
(*****************************************************************************)
Definition COMPLEX_ADD_def:
   COMPLEX_ADD (com a1 b1) (com a2 b2) =
    com (a1+a2) (b1+b2)
End

(*****************************************************************************)
(* Overload "+" onto complex addition                                        *)
(*****************************************************************************)
val _ = overload_on("+", ``COMPLEX_ADD``);

(*****************************************************************************)
(* Define complex subtraction                                                *)
(*****************************************************************************)
Definition COMPLEX_SUB_def:
   COMPLEX_SUB (com a1 b1) (com a2 b2) =
    com (a1-a2) (b1-b2)
End

(*****************************************************************************)
(* Overload "-" onto complex subtraction                                     *)
(*****************************************************************************)
val _ = overload_on("-", ``COMPLEX_SUB``);

(*****************************************************************************)
(* Complex multiplication                                                    *)
(*****************************************************************************)
Definition COMPLEX_MULT_def:
   COMPLEX_MULT (com a1 b1) (com a2 b2) =
    com ((a1*a2)-(b1*b2)) ((b1*a2)+(a1*b2))
End

(*****************************************************************************)
(* Overload "*" onto complex multiplication                                  *)
(*****************************************************************************)
val _ = overload_on("*", ``COMPLEX_MULT``);

(*****************************************************************************)
(* Complex reciprocal (1/x)                                                  *)
(*****************************************************************************)
Definition COMPLEX_RECIPROCAL_def:
   COMPLEX_RECIPROCAL (com a b) = com (a/(a*a + b*b)) ((~b)/(a*a + b*b))
End

(*****************************************************************************)
(* Complex comparisions                                                      *)
(*****************************************************************************)

Definition COMPLEX_LT_def:
   COMPLEX_LT (com ra ia) (com rb ib) =
    (ra < rb) \/ ((ra = rb) /\ (ia < ib))
End

Definition COMPLEX_LE_def:
   COMPLEX_LE (com ra ia) (com rb ib) =
    (ra < rb) \/ ((ra = rb) /\ (ia <= ib))
End

Definition COMPLEX_GT_def:
   COMPLEX_GT (com ra ia) (com rb ib) =
    (ra > rb) \/ ((ra = rb) /\ (ia > ib))
End

Definition COMPLEX_GE_def:
   COMPLEX_GE (com ra ia) (com rb ib) =
    (ra > rb) \/ ((ra = rb) /\ (ia >= ib))
End

(*****************************************************************************)
(* Overload "<", ">", "<=",">=" onto complex comparisons                     *)
(*****************************************************************************)

val _ = overload_on("<",``COMPLEX_LT``);
val _ = overload_on("<=",``COMPLEX_LE``);
val _ = overload_on(">",``COMPLEX_GT``);
val _ = overload_on(">=",``COMPLEX_GE``);

(*****************************************************************************)
(* Complex negation                                                          *)
(*****************************************************************************)

Definition COMPLEX_NEG_def:   COMPLEX_NEG a = com_0 - a
End

(*****************************************************************************)
(* Overload "~" onto complex negation                                        *)
(*****************************************************************************)

val _ = overload_on("~",``COMPLEX_NEG``);

(*****************************************************************************)
(* Complex division                                                          *)
(*****************************************************************************)

Definition COMPLEX_DIV_def:   COMPLEX_DIV a b = a * (COMPLEX_RECIPROCAL b)
End

(*****************************************************************************)
(* Overload "/" onto complex division                                        *)
(*****************************************************************************)

val _ = overload_on("/",``COMPLEX_DIV``);

(*****************************************************************************)
(* DIVIDES : int->int->bool  tests if first argument divides second argument *)
(*                                                                           *)
(* Uses:                                                                     *)
(*  ABS     : int -> int          get absolute value                         *)
(*  Num     : int -> num          convert non-negative integer to a natural  *)
(*  MOD     : num -> num -> num   compute remainder (curried infix)          *)
(*                                                                           *)
(*****************************************************************************)
Definition DIVIDES_def:   DIVIDES m n = (Num(ABS n) MOD Num(ABS m) = 0)
End

(*****************************************************************************)
(* Test if a complex rational is an integer                                  *)
(*                                                                           *)
(* Uses following auxiliary functions:                                       *)
(*                                                                           *)
(*  rat_nmr : rat->int          get numerator                                *)
(*  rat_dnm : rat->int          get denominator                              *)
(*                                                                           *)
(*****************************************************************************)
Definition IS_INT_def:
   IS_INT(com a b) = DIVIDES (rat_dnm a) (rat_nmr a) /\ (b = rat_0)
End

(*****************************************************************************)
(* Need GCD to put a fraction in lowest terms for computing numerator and    *)
(* denominator                                                               *)
(*                                                                           *)
(*    numerator(m/n) = m/(gcd m n)                                           *)
(*  denominator(m/n) = n/(gcd m n)                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Divide each component of a pair of integers by their gcd and return       *)
(* the reduced pair: (x,y) |--> (x/(gcd x y), y/(gcd x y))                   *)
(*****************************************************************************)
Definition reduce_def:
   reduce(x,y) =
    let n = &(gcd (Num(ABS x)) (Num(ABS y))) in (x/n, y/n)
End

(*****************************************************************************)
(* Reduce a rational to lowest terms and return numerator as an integer      *)
(*****************************************************************************)
Definition reduced_nmr_def:
   reduced_nmr r = FST(reduce(rep_frac(rep_rat r)))
End

(*****************************************************************************)
(* Reduce a rational to lowest terms and return denominator as an integer    *)
(*****************************************************************************)
Definition reduced_dnm_def:
   reduced_dnm r = SND(reduce(rep_frac(rep_rat r)))
End

(*****************************************************************************)
(* Multiplication theorems for use in translation                            *)
(*****************************************************************************)

val COMPLEX_MULT_COMM =
 store_thm
   ("COMPLEX_MULT_COMM",
    ``a * b = b * a:complex_rational``,
    Cases_on `a` THEN Cases_on `b`
     THEN RW_TAC std_ss [COMPLEX_MULT_def]
     THEN METIS_TAC [RAT_MUL_COMM,RAT_ADD_COMM]);

val COMPLEX_MULT_ASSOC =
 store_thm
  ("COMPLEX_MULT_ASSOC",
   ``a * (b * c) = a * b * c:complex_rational``,
   Cases_on `a` THEN Cases_on `b` THEN Cases_on `c`
    THEN RW_TAC std_ss
          [COMPLEX_MULT_def,RAT_LDISTRIB,RAT_RDISTRIB,
           RAT_SUB_ADDAINV,GSYM RAT_AINV_LMUL,GSYM RAT_AINV_RMUL,
           RAT_ADD_ASSOC,RAT_MUL_ASSOC,RAT_AINV_ADD]
    THEN METIS_TAC
          [RAT_MUL_COMM,RAT_MUL_ASSOC,RAT_ADD_COMM,RAT_ADD_ASSOC]);

val COMPLEX_MULT_RID =
 store_thm
  ("COMPLEX_MULT_RID",
   ``a * com_1 = a``,
   Cases_on `a`
    THEN RW_TAC std_ss
          [com_1_def,COMPLEX_MULT_def,GSYM rat_0,rat_0_def,
           GSYM rat_1,rat_1_def,RAT_MUL_RID,RAT_MUL_RZERO,
           RAT_ADD_RID,RAT_SUB_RID]);
