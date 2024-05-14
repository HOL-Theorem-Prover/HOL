(* ------------------------------------------------------------------------- *)
(* Ideals in Field                                                           *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "fieldIdeal";

(* ------------------------------------------------------------------------- *)

(* val _ = load "jcLib"; *)
open jcLib;

open pred_setTheory arithmeticTheory gcdsetTheory numberTheory
     combinatoricsTheory;

open monoidTheory groupTheory ringTheory fieldTheory;

(* ------------------------------------------------------------------------- *)
(* Ideals in Field Documentation                                             *)
(* ------------------------------------------------------------------------- *)
(* Overloads:
*)
(* Definitions and Theorems (# are exported):

   Ideals in Field:
   field_ideals                       |- !r i. Field r /\ i << r ==> (i = <#0>) \/ (i = r)
   quotient_field_by_maximal_ideal    |- !r i. Ring r /\ i <> r /\ maxi i ==> Field (r / i)
   quotient_field_ideal_ne_ring       |- !r i. Ring r /\ Field (r / i) ==> i <> r
   quotient_field_imp_maximal_ideal   |- !r i. Ring r /\ i << r /\ Field (r / i) ==> i <> r /\ maxi i
   quotient_field_iff_maximal_ideal   |- !r. Ring r ==> !i. i << r /\ Field (r / i) <=> i <> r /\ maxi i
*)

(* ------------------------------------------------------------------------- *)
(* Ideals in Field                                                           *)
(* ------------------------------------------------------------------------- *)

(* The carrier of Ideal = carrier of group i.sum *)
val _ = temp_overload_on ("I", ``i.carrier``);
(* The carrier of Ideal = carrier of group j.sum *)
val _ = temp_overload_on ("J", ``j.carrier``);

(* Theorem: A Field has only two ideals:
            Field r ==> i << r ==> (i = <#0>) \/ (i = r)  *)
(* Proof:
   Consider the carrier of the ideal.
   If it is {#0},
   i = <#0>                         by ideal_carrier_sing
   If it is not {#0},
   Since #0 IN I                    by ideal_has_zero
   there is x <> #0 IN I            by ONE_ELEMENT_SING
   But x IN I ==> x IN R            by ideal_element_property
   And x <> #0 IN R ==> |/x IN R    by field_inv_element
   Hence x * |/x IN I               by ideal_def
   or         #1 IN I               by field_mult_rinv
   Hence i = r                      by ideal_with_one
*)
val field_ideals = store_thm(
  "field_ideals",
  ``!r i:'a ring. Field r /\ i << r ==> (i = <#0>) \/ (i = r)``,
  rpt strip_tac >>
  Cases_on `I = {#0}` >| [
    rw[GSYM ideal_carrier_sing],
    `<#0> << r` by rw[zero_ideal_ideal] >>
    `Ring r` by rw[field_is_ring] >>
    `i <> <#0>` by metis_tac[ideal_eq_ideal, zero_ideal_sing] >>
    rw[] >>
    `#0 IN I` by rw[ideal_has_zero] >>
    `?x. x IN I /\ x <> #0` by metis_tac[ONE_ELEMENT_SING, MEMBER_NOT_EMPTY] >>
    `x IN R` by metis_tac[ideal_element_property] >>
    `x IN R+` by rw[ring_nonzero_eq] >>
    metis_tac[field_inv_element, field_mult_rinv, ideal_def, ideal_with_one]
  ]);

(* Theorem: i <> r /\ maxi i ==> Field (r/i) *)
(* Proof: by definitions, this is to show:
   (1) i << r ==> Ring (r / i), true by quotient_ring_ring.
   (2) (r / i).prod.id <> (r / i).sum.id
       which is to show: IMAGE (\z. #1 + z) I <> I
       Assume IMAGE (\z. #1 + z) I = I
       then since #0 IN I      by ideal_has_zero
        #1 + #0 = #1 IN I      by ring_add_rzero
       ==> i = r               by ideal_with_one
       But this contradicts i <> r.
   (3) x IN (r / i).carrier /\ x <> (r / i).sum.id ==> ?y. y IN (r / i).carrier /\ ((r / i).prod.op x y = (r / i).prod.id)
       or x IN R/I /\ x <> I ==> ?y. y IN R/I /\ ((gen x * gen y) o I = #1 o I)
       Let p = gen x,
       then p IN R /\ p o I = x      by ideal_cogen_property
       If p IN I, then p o I = I     by ideal_coset_of_element
       which contradicts x <> I, hence
       p NOTIN I                     by ideal_coset_of_element

       Construct the ideal: <p>.
       <p> << r                by principal_ideal_ideal
       i << (<p> + i) << r     by ideal_sum_has_ideal_comm, ideal_sum_ideal
       But i <> (<p> + i)      by principal_ideal_sum_equal_ideal, since p NOTIN I
       Thus (<p> + i) = r              by maxi condition
       or  #1 IN (<p> + i).carrier     by ideal_with one
       So there are q IN R, z IN I such that:
       #1 = p * q + z                  by ideal_sum_element, principal_ideal_element
       or #1 === p * q                 by ideal_congruence_def
       or p * q === #1                 by ideal_congruence_sym

       Let y = q o I, the goal becomes:
          q o I IN R/I /\ ((p * gen (q o I)) o I = #1 o I)
       i.e. to show: p * gen (q o I) === #1    by ideal_coset_eq, ideal_congruence_def
       By ideal_coset_property,
       q o I IN R/I /\ (gen (q o I) o I = q o I
       or     gen (q o I) === q       by above, and ideal_congruence_def
       so p * gen (q o I) === p * q   by ideal_congruence_mult
       Thus goal is true by ideal_congruence_trans.
*)
val quotient_field_by_maximal_ideal = store_thm(
  "quotient_field_by_maximal_ideal",
  ``!r i:'a ring. Ring r /\ i <> r /\ maxi i ==> Field (r/i)``,
  rw[ideal_maximal_def, field_def_by_inv] >| [
    rw[quotient_ring_ring],
    rw[quotient_ring_def, quotient_ring_add_def, quotient_ring_mult_def, coset_def] >>
    spose_not_then strip_assume_tac >>
    `#0 IN I` by rw[ideal_has_zero] >>
    `#1 + #0 = #1` by rw[] >>
    `#1 + #0 IN IMAGE (\z. #1 + z) I` by rw[] >>
    `#1 IN I` by metis_tac[] >>
    metis_tac[ideal_with_one],
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    rw[quotient_ring_def, quotient_ring_add_def, quotient_ring_mult_def] >>
    `gen x IN R /\ (gen x o I = x)` by rw[ideal_cogen_property] >>
    `gen x NOTIN I` by metis_tac[ideal_coset_of_element] >>
    qabbrev_tac `p = gen x` >>
    `<p> << r` by rw[principal_ideal_ideal] >>
    `i << (<p> + i)` by rw[ideal_sum_has_ideal_comm] >>
    `(<p> + i) << r` by rw[ideal_sum_ideal] >>
    `(<p> + i) = r` by metis_tac[principal_ideal_sum_equal_ideal] >>
    `#1 IN (<p> + i).carrier` by rw[ideal_with_one] >>
    `?y z. y IN <p>.carrier /\ z IN I /\ (#1 = y + z)` by rw[GSYM ideal_sum_element] >>
    `?q. q IN R /\ (#1 = p * q + z)` by metis_tac[principal_ideal_element] >>
    qexists_tac `q o I` >>
    `q o I IN R/I /\ (gen (q o I) o I = q o I)` by rw[ideal_coset_property] >>
    `gen (q o I) IN R` by rw[ideal_cogen_property] >>
    `p * gen (q o I) === #1` suffices_by rw[ideal_coset_eq, ideal_congruence_def] >>
    `gen (q o I) === q` by rw[GSYM ideal_coset_eq, ideal_congruence_def] >>
    `p * gen (q o I) === p * q` by rw[ideal_congruence_mult] >>
    `#1 - p * q = z` by metis_tac[ring_sub_eq_add, ring_one_element, ring_mult_element, ideal_element_property] >>
    `#1 === p * q` by rw[ideal_congruence_def] >>
    `p * q === #1` by rw[ideal_congruence_sym] >>
    metis_tac[ideal_congruence_trans, ring_one_element, ring_mult_element]
  ]);

(* Theorem: The ideal of a quotient field cannot be the ring itself.
            Ring r /\ Field (r / i) ==> r <> i *)
(* Proof:
   i.e. to show: Ring r /\ Field (r / i) /\ r = i ==> F
   Since (r/r).carrier = {R}    by quotient_ring_ring_sing
   (r/r).sum.id = R             by field_zero_element, IN_SING
   (r/r).prod.id = R            by field_one_element, IN_SING
   which contradicts field_one_ne_zero.
*)
val quotient_field_ideal_ne_ring = store_thm(
  "quotient_field_ideal_ne_ring",
  ``!r i:'a ring. Ring r /\ Field (r/i) ==> i <> r``,
  rpt strip_tac >>
  `(r/r).carrier = {R}` by rw[quotient_ring_ring_sing] >>
  `(r/r).sum.id IN (r/r).carrier /\ (r/r).prod.id IN (r/r).carrier` by rw[] >>
  metis_tac[field_one_ne_zero, IN_SING]);

(* Theorem: Ring r /\ i << r /\ Field (r/i) ==> i <> r /\ maxi i  *)
(* Proof: by definitions, this is to show:
   (1) Field (r / i) ==> r <> i
       Suppose r = i,
       Since (r/r).carrier = {R}    by quotient_ring_ring_sing
       (r/r).sum.id = R             by field_zero_element, IN_SING
       (r/r).prod.id = R            by field_one_element, IN_SING
       which contradicts field_one_ne_zero.
   (2) i << r /\ Field (r / i) /\ i <> r ==> maxi i
       By ideal_maximal_def, this is to show:
       i << r /\ Field (r / i) /\ i <> r /\ i << j /\ j << r ==> (i = j) \/ (j = r)
*)
val quotient_field_imp_maximal_ideal = store_thm(
  "quotient_field_imp_maximal_ideal",
  ``!r i:'a ring. Ring r /\ i << r /\ Field (r/i) ==> i <> r /\ maxi i``,
  ntac 3 strip_tac >>
  CONJ_ASM1_TAC >| [
    rw[quotient_field_ideal_ne_ring],
    rw[ideal_maximal_def] >>
    `RingHomo (\x. x o I) r (r/i)` by rw[quotient_ring_homo] >>
    `SURJ (\x. x o I) R (R/I)` by rw[quotient_ring_homo_surj] >>
    `(r/i).carrier = R/I` by rw[quotient_ring_def] >>
    `Ring (r/i)` by rw[quotient_ring_ring] >>
    `homo_ideal (\x. x o I) r (r/i) j << (r/i)` by rw[ring_homo_ideal_ideal] >>
    `(homo_ideal (\x. x o I) r (r / i) j).carrier = IMAGE (\x. x o I) J` by rw_tac std_ss[homo_ideal_def] >>
    `(homo_ideal (\x. x o I) r (r/i) j = principal_ideal (r / i) (r / i).sum.id) \/
    (homo_ideal (\x. x o I) r (r/i) j = (r/i))` by metis_tac[field_ideals] >| [
      `(principal_ideal (r / i) (r / i).sum.id).carrier = {(r / i).sum.id}` by rw[zero_ideal_sing] >>
      `(r / i).sum.id = I` by rw[quotient_ring_def, quotient_ring_add_def] >>
      `IMAGE (\x. x o I) J = {I}` by metis_tac[] >>
      (`!x. x IN J ==> x o I IN IMAGE (\x. x o I) J` by (rw[] >> metis_tac[])) >>
      `!x. x IN J ==> (x o I = I)` by metis_tac[IN_SING] >>
      `!x. x IN J ==> x IN I` by metis_tac[ideal_coset_eq_carrier, ideal_element_property] >>
      `J SUBSET I` by rw[SUBSET_DEF] >>
      `I SUBSET J` by metis_tac[ideal_def, Subgroup_def] >>
      `I = J` by rw[SUBSET_ANTISYM] >>
      metis_tac[ideal_eq_ideal],
      `r.sum.carrier = R` by rw[] >>
      `j.sum.carrier = J` by metis_tac[ideal_def] >>
      `!x. x IN R ==> x o I IN R/I` by rw[ideal_coset_property] >>
      `!x. x IN R ==> x o I IN IMAGE (\x. x o I) J` by metis_tac[] >>
      `!z. z IN IMAGE (\x. x o I) J ==> ?u. (z = u o I) /\ u IN J` by rw[] >>
      `!x. x IN R ==> ?y. (x o I = y o I) /\ y IN J` by metis_tac[] >>
      `!x. x IN R ==> ?y. (x - y IN I) /\ y IN J` by metis_tac[ideal_coset_eq, ideal_element_property] >>
      `!x. x IN R ==> ?y. (x - y IN J) /\ y IN J` by metis_tac[ideal_element] >>
      `!x. x IN R ==> ?y. (x - y IN J) /\ y IN J /\ (x - y + y) IN J` by metis_tac[ideal_property] >>
      `!x. x IN R ==> ?y. (x - y IN J) /\ y IN J /\ x IN J` by metis_tac[ring_sub_add, ideal_element_property] >>
      `R SUBSET J` by metis_tac[SUBSET_DEF] >>
      `J SUBSET R` by metis_tac[ideal_element, SUBSET_DEF] >>
      `J = R` by rw[SUBSET_ANTISYM] >>
      metis_tac[ideal_eq_ideal, ideal_refl]
    ]
  ]);

(* Theorem: Ring r /\ i << r /\ Field (r/i) <=> i <> r /\ maxi i  *)
(* Proof:
   If part: Ring r /\ i << r /\ Field (r/i) ==> i <> r /\ maxi i
     True by quotient_field_imp_maximal_ideal.
   Only-if part: i <> r /\ maxi i ==> i << r /\ Field (r / i)
     the part: i << r           true by ideal_maximal_def
     the part: Field (r / i)    true by quotient_field_by_maximal_ideal.
*)
val quotient_field_iff_maximal_ideal = store_thm(
  "quotient_field_iff_maximal_ideal",
  ``!r:'a ring. Ring r ==> !i:'a ring. i << r /\ Field (r/i) <=> i <> r /\ maxi i``,
  rw[quotient_field_imp_maximal_ideal, EQ_IMP_THM] >-
  metis_tac[ideal_maximal_def] >>
  rw[quotient_field_by_maximal_ideal]);

(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
