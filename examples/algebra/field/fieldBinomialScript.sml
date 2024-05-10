(* ------------------------------------------------------------------------- *)
(* Binomial coefficients and expansion, for Field                            *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "fieldBinomial";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory listTheory arithmeticTheory numberTheory combinatoricsTheory
     dividesTheory;

open fieldTheory;
open ringTheory;
open groupTheory;
open monoidTheory;

open groupMapTheory ringMapTheory fieldMapTheory;

(* val _ = load "ringBinomialTheory"; *)
open ringBinomialTheory;

(* ------------------------------------------------------------------------- *)
(* Field Binomial Documentation                                              *)
(* ------------------------------------------------------------------------- *)
(*
   Overloading:
*)
(* Definitions and Theorems (# are exported):

   Field Binomial Theorems:
   field_binomial_property       |- !r. Field r ==> !k. 0 < k /\ k < char r ==> (##(binomial (char r) k) = #0)
   finite_field_freshman_thm     |- !r. FiniteField r ==> !x y. x IN R /\ y IN R ==>
                                        ((x + y) ** char r = x ** char r + y ** char r)
   finite_field_freshman_all     |- !r. FiniteField r ==> !x y. x IN R /\ y IN R ==>
                                    !k. (x + y) ** char r ** k = x ** char r ** k + y ** char r ** k
   finite_field_freshman_all_sub |- !r. FiniteField r ==> !x y. x IN R /\ y IN R ==>
                                    !k. (x - y) ** char r ** k = x ** char r ** k - y ** char r ** k
   finite_field_num_fermat_thm   |- !r. FiniteField r ==> !n. ##n ** char r = ##n
   finite_field_num_fermat_all   |- !r. FiniteField r ==> !n k. ##n ** char r ** k = ##n
   finite_field_map_endo         |- !r. FiniteField r ==> FieldEndo (\x. x ** char r) r
   finite_field_map_auto         |- !r. FiniteField r /\ (CARD R = char r) ==> FieldAuto (\x. x ** char r) r
*)

(* ------------------------------------------------------------------------- *)
(* Field Binomial Theorems                                                   *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> 1 < char r /\ ##(binomial (char r) k) = #0   for  0 < k < (char r) *)
(* Proof:
   Field r ==> prime (char r) or char r = 0     by field_char
   If char r = 0, no k in range 0 ... char.
   Otherwise, true                              by ring_char_prime
*)
val field_binomial_property = store_thm(
  "field_binomial_property",
  ``!r:'a field. Field r ==> !k. 0 < k /\ k < char r ==> (##(binomial (char r) k) = #0)``,
  rpt strip_tac >>
  `(char r = 0) \/ prime (char r)` by rw[field_char] >-
  metis_tac[DECIDE ``!k. 0 < k /\ k < 0 <=> F``] >>
  metis_tac[ring_char_prime, field_is_ring]);

(* Theorem: [Freshman's Theorem] FiniteField r ==> (x + y)^(char r) = x^(char r) + y^(char r) *)
(* Proof:
   FiniteField r ==> prime (char r)     by finite_field_char
   FiniteField r ==> Ring r             by FiniteField_def, field_is_ring
   Hence true                           by ring_freshman_thm
*)
val finite_field_freshman_thm = store_thm(
  "finite_field_freshman_thm",
  ``!r:'a field. FiniteField r ==> !x y. x IN R /\ y IN R ==> ((x + y) ** (char r) = x ** (char r) + y ** (char r))``,
  rw[ring_freshman_thm, finite_field_char, FiniteField_def]);

(* Theorem: [Freshman's Theorem Generalized]
             FiniteField r ==> 1 < char r /\ !k. (x + y)^(char r)^k = x^(char r)^k + y^(char r)^k
             Note: a^b^c = a^(b^c)   *)
(* Proof:
   FiniteField r ==> prime (char r)     by finite_field_char
   FiniteField r ==> Ring r             by FiniteField_def, field_is_ring
   Hence true                           by ring_freshman_all
*)
val finite_field_freshman_all = store_thm(
  "finite_field_freshman_all",
  ``!r:'a field. FiniteField r ==>
      !x y. x IN R /\ y IN R ==> !k. (x + y) ** (char r) ** k = x ** (char r) ** k + y ** (char r) ** k``,
  rw[ring_freshman_all, finite_field_char, FiniteField_def]);

(* Theorem: FiniteField r ==> !x y. x IN R /\ y IN R ==>
            !k. (x - y) ** char r ** k = x ** char r ** k - y ** char r ** k *)
(* Proof:
   Note prime (char r)         by finite_field_char
   Hence the result follows    by ring_freshman_all_sub
*)
val finite_field_freshman_all_sub = store_thm(
  "finite_field_freshman_all_sub",
  ``!r:'a field. FiniteField r ==> !x y. x IN R /\ y IN R ==>
   !k. (x - y) ** char r ** k = x ** char r ** k - y ** char r ** k``,
  metis_tac[finite_field_char, ring_freshman_all_sub, finite_field_is_field, field_is_ring]);

(* Theorem: [Fermat's Little Theorem] FiniteField r ==> (##n) ** (char r) = (##n)  *)
(* Proof:
   FiniteField r ==> prime (char r)     by finite_field_char
   FiniteField r ==> Ring r             by FiniteField_def, field_is_ring
   Hence true                           by ring_fermat_thm
*)
val finite_field_num_fermat_thm = store_thm(
  "finite_field_num_fermat_thm",
  ``!r:'a field. FiniteField r ==> !n. (##n) ** (char r) = (##n)``,
  rw[ring_fermat_thm, finite_field_char, FiniteField_def]);

(* Theorem: [Fermat's Little Theorem Generalized] FiniteField r ==> !k. (##n) ** (char r) ** k = (##n)  *)
(* Proof:
   FiniteField r ==> prime (char r)     by finite_field_char
   FiniteField r ==> Ring r             by FiniteField_def, field_is_ring
   Hence true                           by ring_fermat_all
*)
val finite_field_num_fermat_all = store_thm(
  "finite_field_num_fermat_all",
  ``!r:'a field. FiniteField r ==> !n k. (##n) ** (char r) ** k = (##n)``,
  rw[ring_fermat_all, finite_field_char, FiniteField_def]);

(* Theorem: [Frobenius Theorem]
            For a FiniteField r, x IN R,
            the map x --> x^p  is a ring homomorphism to itself (endomorphism)
         or FiniteField r ==> RingEndo (\x. x ** (char r)) r  *)
(* Proof:
   Let p = char r.
   First, x IN R ==> x ** p IN R           by field_exp_element.
   So we need to verify F(x) = x ** p is a ring homomorphism, meaning:
   (1) FiniteField r ==> GroupHomo (\x. x ** p) (ring_sum r) (ring_sum r)
       Expanding by GroupHomo_def, this is to show:
       FiniteField r /\ x IN R /\ x' IN R ==> (x + x') ** p = x ** p + x' ** p
       which is true by finite_field_freshman_thm.
   (2) FiniteField r ==> MonoidHomo (\x. x ** p) r.prod r.prod
       Expanding by MonoidHomo_def, this is to show:
       FiniteField r /\ x IN R /\ x' IN r ==> (x * x') ** p = x ** p * x' ** p
       which is true by field_mult_exp.
*)
val finite_field_map_endo = store_thm(
  "finite_field_map_endo",
  ``!r:'a ring. FiniteField r ==> FieldEndo (\x. x ** (char r)) r``,
  rpt strip_tac >>
  `Field r /\ FINITE R` by metis_tac[FiniteField_def] >>
  qabbrev_tac `p = char r` >>
  rw[FieldEndo_def, FieldHomo_def, RingHomo_def] >| [
    rw[GroupHomo_def] >>
    rw[finite_field_freshman_thm, Abbr`p`],
    rw[MonoidHomo_def]
  ]);

(* Theorem: FiniteField r /\ (CARD R = char r) ==> FieldAuto (\x. x ** char r) r *)
(* Proof:
   By FieldAuto_def, FieldIso_def, this is to show:
   (1) FieldHomo (\x. x ** char r) r r
       Since FieldEndo (\x. x ** char r) r        by finite_field_map_endo
          so FieldHomo (\x. x ** char r) r r      by FieldEndo_def
   (2) (\x. x ** char r) PERMUTES R
       Note !x. x IN R ==> (x ** char r = x)      by finite_field_fermat_thm, CARD R = char r
       Expand by BIJ_DEF, INJ_DEF, SURJ_DEF, this is to show:
       (1) x IN R ==> x ** char r IN R, true  by field_exp_element
       (2) x IN R /\ x' IN R /\ x ** char r = x' ** char r ==> x = x'
           Since x ** char r = x                  by above, finite_field_fermat_thm
             and x' ** char r = x'                by above, finite_field_fermat_thm
           This is trivially true.
       (3) same as (1)
       (4) x IN R ==> ?x'. x' IN R /\ (x' ** char r = x), true by taking x' = x.
*)
val finite_field_map_auto = store_thm(
  "finite_field_map_auto",
  ``!r:'a field. FiniteField r /\ (CARD R = char r) ==> FieldAuto (\x. x ** char r) r``,
  rpt (stripDup[FiniteField_def]) >>
  rw_tac std_ss[FieldAuto_def, FieldIso_def] >-
  metis_tac[finite_field_map_endo, FieldEndo_def] >>
  `!x. x IN R ==> (x ** char r = x)` by metis_tac[finite_field_fermat_thm] >>
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  metis_tac[]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
