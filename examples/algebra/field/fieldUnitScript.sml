(* ------------------------------------------------------------------------- *)
(* Units in a Field                                                          *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "fieldUnit";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

(* open dependent theories *)
open pred_setTheory;

(* Get dependent theories local *)
(* val _ = load "fieldTheory"; *)
(* val _ = load "ringUnitTheory"; *)
open ringTheory fieldTheory;
open ringDividesTheory ringUnitTheory;

(* ------------------------------------------------------------------------- *)
(* Field Units Documentation                                                 *)
(* ------------------------------------------------------------------------- *)
(* Overloading:
*)
(* Definitions and Theorems (# are exported):

   Field Unit Equivalence:
   field_eq_unit_eq       |- !r. Field r ==> !x y. x IN R /\ y IN R /\ (x = y) ==> x =~ y
   field_divides_antisym  |- !r. Field r ==> !x y. x IN R /\ y IN R /\ x rdivides y /\ y rdivides x ==> x =~ y
*)

(* ------------------------------------------------------------------------- *)
(* Field Unit Equivalence                                                    *)
(* ------------------------------------------------------------------------- *)

(* Theorem: Field r ==> !x y. x IN R /\ y IN R /\ (x = y) ==> x =~ y*)
(* Proof: by ring_eq_unit_eq, field_is_ring *)
Theorem field_eq_unit_eq:
  !r:'a field. Field r ==> !x y. x IN R /\ y IN R /\ (x = y) ==> x =~ y
Proof
  rw[ring_eq_unit_eq]
QED

(* Theorem: Field r ==> !x y. x IN R /\ y IN R /\ x rdivides y /\ y rdivides x ==> x =~ y *)
(* Proof:
   If x = #0,
      then y = #0                                by field_zero_divides
        so x =~ y                                by field_eq_unit_eq
   If x <> #0,
      x IN R+                                    by field_nonzero_eq
   x rdivides y ==> ?u. u IN R /\ (y = u * x)    by ring_divides_def
   y rdivides x ==> ?v. v IN R /\ (x = v * y)    by ring_divides_def
   Hence  x = v * (u * x) = (v * u) * x          by field_mult_assoc
      or  v * u = #1                             by field_nonzero_mult_eq_self
      or  unit v                                 by ring_unit_property
    Thus  x =~ y                                 by unit_eq_def
*)
Theorem field_divides_antisym:
  !r:'a field. Field r ==> !x y. x IN R /\ y IN R /\ x rdivides y /\ y rdivides x ==> x =~ y
Proof
  rpt strip_tac >>
  Cases_on `x = #0` >-
  metis_tac[field_zero_divides, field_eq_unit_eq] >>
  `x IN R+` by rw[field_nonzero_eq] >>
  `?u. u IN R /\ (y = u * x)` by rw[GSYM ring_divides_def] >>
  `?v. v IN R /\ (x = v * y)` by rw[GSYM ring_divides_def] >>
  `x = (v * u) * x` by metis_tac[field_mult_assoc] >>
  `v * u = #1` by metis_tac[field_nonzero_mult_eq_self, field_mult_element] >>
  metis_tac[ring_unit_property, unit_eq_def, field_is_ring]
QED

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
