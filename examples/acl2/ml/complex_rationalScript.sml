(*****************************************************************************)
(* Define complex rationals                                                  *)
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
 ["intLib","gcdTheory", "fracLib", "ratLib"];
open intLib gcdTheory fracLib ratLib ratTheory;
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation: open HOL4 systems modules
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories (including ratTheory from Jens Brandt)
******************************************************************************)
open gcdTheory fracLib ratLib;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Start new theory "complex_rational"                                       *)
(*****************************************************************************)
val _ = new_theory "complex_rational";

(*****************************************************************************)
(* A complex rational x+yi is a pair of rational numbers.                    *)
(* The type ``:complex_rational`` is a datatype isomorphic to                *)
(* ``:rat # rat``, with curried constructor ``COMPLEX_RATIONAL``.            *)
(*****************************************************************************)
val _ = Hol_datatype `complex_rational = COMPLEX_RATIONAL of rat => rat`;

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
val COMPLEX_ADD_def =
 Define
  `COMPLEX_ADD (com a1 b1) (com a2 b2) =
    com (a1+a2) (b1+b2)`;

(*****************************************************************************)
(* Overload "+" onto complex addition                                        *)
(*****************************************************************************)
val _ = overload_on("+", ``COMPLEX_ADD``);

(*****************************************************************************)
(* Define complex subtraction                                                *)
(*****************************************************************************)
val COMPLEX_SUB_def =
 Define
  `COMPLEX_SUB (com a1 b1) (com a2 b2) =
    com (a1-a2) (b1-b2)`;

(*****************************************************************************)
(* Overload "-" onto complex subtraction                                     *)
(*****************************************************************************)
val _ = overload_on("-", ``COMPLEX_SUB``);

(*****************************************************************************)
(* Complex multiplication                                                    *)
(*****************************************************************************)
val COMPLEX_MULT_def =
 Define
  `COMPLEX_MULT (com a1 b1) (com a2 b2) =
    com ((a1*a2)-(b1*b2)) ((b1*a2)+(a1*b2))`;

(*****************************************************************************)
(* Overload "*" onto complex multiplication                                  *)
(*****************************************************************************)
val _ = overload_on("*", ``COMPLEX_MULT``);

(*****************************************************************************)
(* Complex reciprocal (1/x)                                                  *)
(*****************************************************************************)
val COMPLEX_RECIPROCAL_def =
 Define
  `COMPLEX_RECIPROCAL (com a b) = com (a/(a*a + b*b)) ((~b)/(a*a + b*b))`;

(*****************************************************************************)
(* DIVIDES : int->int->bool  tests if first argument divides second argument *)
(*                                                                           *)
(* Uses:                                                                     *)
(*  ABS     : int -> int          get absolute value                         *)
(*  Num     : int -> num          convert non-negative integer to a natural  *)
(*  MOD     : num -> num -> num   compute remainder (curried infix)          *)
(*                                                                           *)
(*****************************************************************************)
val DIVIDES_def = Define `DIVIDES m n = (Num(ABS n) MOD Num(ABS m) = 0)`;

(*****************************************************************************)
(* Test if a complex rational is an integer                                  *)
(*                                                                           *)
(* Uses following auxiliary functions:                                       *)
(*                                                                           *)
(*  rat_nmr : rat->int          get numerator                                *)
(*  rat_dnm : rat->int          get denominator                              *)
(*                                                                           *)
(*****************************************************************************)
val IS_INT_def =
 Define 
  `IS_INT(com a b) = DIVIDES (rat_dnm a) (rat_nmr a) /\ (b = rat_0)`;

(*****************************************************************************)
(* Need GCD to put a fraction in lowest terms for computing numerator and    *)
(* denominator                                                               *)
(*                                                                           *)
(*    numerator(m/n) = m/(gcd m n)                                           *)
(*  denominator(m/n) = n/(gcd m n)                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Divide each component of a pair of integers by their GCD and return       *)
(* the reduced pair: (x,y) |--> (x/GCD(x,y), y/GCD(x,y))                     *)
(*****************************************************************************)
val reduce_def =
 Define
  `reduce(x,y) = let n = &(gcd (Num(ABS x)) (Num(ABS y))) in (x/n, y/n)`;

(*****************************************************************************)
(* Reduce a rational to lowest terms and return numerator as an integer      *)
(*****************************************************************************)
val reduced_nmr_def =
 Define
  `reduced_nmr r = FST(reduce(rep_frac(rep_rat r)))`;

(*****************************************************************************)
(* Reduce a rational to lowest terms and return denominator as an integer    *)
(*****************************************************************************)
val reduced_dnm_def =
 Define
  `reduced_dnm r = SND(reduce(rep_frac(rep_rat r)))`;

val _ = export_theory();
