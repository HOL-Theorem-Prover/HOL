(* ------------------------------------------------------------------------- *)
(* Scalars, Rational Torsion and Generated Curve Subgroups                    *)
(* ------------------------------------------------------------------------- *)
(*
   Documentation

   Scalar multiplication is the existing group exponent (sw_group r a b).exp.
   sw_torsion_group_def is the kernel of multiplication by n on the rational
   curve group over r; it is not torsion over an algebraic closure.

   Scalars:
     sw_scalar_zero, sw_scalar_one, sw_scalar_closed, sw_scalar_add,
       sw_scalar_mult, sw_scalar_distrib, sw_scalar_neg, sw_scalar_endo.
   Torsion:
     sw_torsion_carrier, sw_torsion_member, sw_torsion_subgroup,
       sw_torsion_group, sw_torsion_normal, sw_torsion_finite_group.
     sw_torsion_zero             n = 0 gives the whole curve group.
     sw_torsion_one_carrier      n = 1 gives only infinity.
     sw_torsion_order, sw_torsion_infinite_order
                                Membership iff point order divides n;
                                HOL represents infinite order by 0.
   Generated subgroups and cofactors:
     sw_generated_member, sw_generated_subset, sw_generated_subgroup,
       sw_generated_cyclic, sw_generator_card, sw_point_order_divides_card.
     sw_cofactor_one_generated, sw_cofactor_clearing,
       sw_cofactor_clearing_order.

   Retain the curve, membership and finiteness hypotheses of each theorem.
   Cofactor clearing proves n-torsion membership; it does not by itself
   identify a particular generated subgroup or prove a nonzero result.
*)

Theory ellipticTorsion
Ancestors
  shortWeierstrass shortWeierstrassGroup

open groupTheory monoidTheory pred_setTheory arithmeticTheory dividesTheory

Theorem sw_scalar_zero[simp]:
  (sw_group (r:'a field) a b).exp P 0 = ECInfinity
Proof
  simp[group_exp_0]
QED

Theorem sw_scalar_one:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b ==>
  (sw_group r a b).exp P 1 = P
Proof
  metis_tac[short_weierstrass_group, sw_group_carrier, group_exp_1]
QED

Theorem sw_scalar_closed:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b ==>
  (sw_group r a b).exp P n IN sw_points r a b
Proof
  metis_tac[short_weierstrass_group, sw_group_carrier, group_exp_element]
QED

Theorem sw_scalar_add:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b ==>
  (sw_group r a b).exp P (m + n) =
  sw_add r a b ((sw_group r a b).exp P m) ((sw_group r a b).exp P n)
Proof
  metis_tac[short_weierstrass_group, sw_group_carrier, sw_group_op,
            group_exp_add]
QED

Theorem sw_scalar_mult:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b ==>
  (sw_group r a b).exp P (m * n) =
  (sw_group r a b).exp ((sw_group r a b).exp P m) n
Proof
  metis_tac[short_weierstrass_group, sw_group_carrier, group_exp_mult]
QED

Theorem sw_scalar_distrib:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b /\ Q IN sw_points r a b ==>
  (sw_group r a b).exp (sw_add r a b P Q) n =
  sw_add r a b ((sw_group r a b).exp P n) ((sw_group r a b).exp Q n)
Proof
  strip_tac >>
  `AbelianGroup (sw_group r a b)` by
    metis_tac[short_weierstrass_abelian_group] >>
  metis_tac[AbelianGroup_def, group_comm_op_exp,
            sw_group_carrier, sw_group_op]
QED

Theorem sw_scalar_neg:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b ==>
  (sw_group r a b).exp (sw_neg r P) n =
  sw_neg r ((sw_group r a b).exp P n)
Proof
  strip_tac >>
  `Group (sw_group r a b) /\
   P IN (sw_group r a b).carrier` by
    metis_tac[short_weierstrass_group, sw_group_carrier] >>
  metis_tac[group_inv_exp, sw_group_inv, sw_scalar_closed]
QED

Theorem sw_scalar_endo:
  ShortWeierstrassCurve (r:'a field) a b ==>
  GroupEndo (\P. (sw_group r a b).exp P n) (sw_group r a b)
Proof
  strip_tac >>
  SIMP_TAC bool_ss [GroupEndo_def, GroupHomo_def, sw_group_carrier, sw_group_op] >>
  conj_tac >- metis_tac[sw_scalar_closed] >>
  metis_tac[sw_scalar_distrib]
QED

Definition sw_torsion_group_def:
  sw_torsion_group (r:'a field) a b n =
    kernel_group (\P. (sw_group r a b).exp P n)
      (sw_group r a b) (sw_group r a b)
End

Theorem sw_torsion_carrier:
  (sw_torsion_group (r:'a field) a b n).carrier =
    {P | P IN sw_points r a b /\
         (sw_group r a b).exp P n = ECInfinity}
Proof
  rw[sw_torsion_group_def, kernel_group_def, EXTENSION]
QED

Theorem sw_torsion_member:
  P IN (sw_torsion_group (r:'a field) a b n).carrier <=>
  P IN sw_points r a b /\ (sw_group r a b).exp P n = ECInfinity
Proof
  simp[sw_torsion_carrier]
QED

Theorem sw_torsion_id[simp]:
  (sw_torsion_group (r:'a field) a b n).id = ECInfinity
Proof
  simp[sw_torsion_group_def, kernel_group_def]
QED

Theorem sw_torsion_op[simp]:
  (sw_torsion_group (r:'a field) a b n).op = sw_add r a b
Proof
  simp[sw_torsion_group_def, kernel_group_def]
QED

Theorem sw_torsion_subgroup:
  ShortWeierstrassCurve (r:'a field) a b ==>
  Subgroup (sw_torsion_group r a b n) (sw_group r a b)
Proof
  rw[sw_torsion_group_def] >>
  irule kernel_group_subgroup >>
  metis_tac[short_weierstrass_group, sw_scalar_endo, GroupEndo_def]
QED

Theorem sw_torsion_group:
  ShortWeierstrassCurve (r:'a field) a b ==>
  Group (sw_torsion_group r a b n)
Proof
  metis_tac[sw_torsion_subgroup, Subgroup_def]
QED

Theorem sw_torsion_normal:
  ShortWeierstrassCurve (r:'a field) a b ==>
  normal_subgroup (sw_torsion_group r a b n) (sw_group r a b)
Proof
  rw[sw_torsion_group_def] >>
  irule kernel_group_normal >>
  metis_tac[short_weierstrass_group, sw_scalar_endo, GroupEndo_def]
QED

Theorem sw_torsion_zero:
  ShortWeierstrassCurve (r:'a field) a b ==>
  sw_torsion_group r a b 0 = sw_group r a b
Proof
  strip_tac >> irule subgroup_eq_carrier >>
  simp[sw_torsion_subgroup, sw_torsion_carrier, EXTENSION]
QED

Theorem sw_torsion_one_carrier:
  ShortWeierstrassCurve (r:'a field) a b ==>
  (sw_torsion_group r a b 1).carrier = {ECInfinity}
Proof
  rw[EXTENSION, sw_torsion_member] >>
  metis_tac[sw_scalar_one, sw_points_member, sw_on_curve_ECInfinity]
QED

Theorem sw_torsion_order:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b ==>
  (P IN (sw_torsion_group r a b n).carrier <=>
   order (sw_group r a b) P divides n)
Proof
  strip_tac >> SIMP_TAC bool_ss [sw_torsion_member] >>
  metis_tac[short_weierstrass_group, sw_group_carrier, sw_group_id,
            group_order_divides_exp]
QED

Theorem sw_torsion_infinite_order:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b /\ order (sw_group r a b) P = 0 ==>
  (P IN (sw_torsion_group r a b n).carrier <=> n = 0)
Proof
  metis_tac[sw_torsion_order, ZERO_DIVIDES]
QED

Theorem sw_torsion_finite_group:
  FiniteField (r:'a field) /\ ShortWeierstrassCurve r a b ==>
  FiniteGroup (sw_torsion_group r a b n)
Proof
  strip_tac >> irule finite_subgroup_finite_group >>
  qexists_tac `sw_group r a b` >>
  metis_tac[sw_torsion_subgroup, short_weierstrass_finite_group,
            FiniteAbelianGroup_def_alt]
QED

Theorem sw_generated_member:
  P IN (Generated (sw_group (r:'a field) a b) Q).carrier <=>
  ?n. P = (sw_group r a b).exp Q n
Proof
  simp[generated_element]
QED

Theorem sw_generated_subset:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b ==>
  (Generated (sw_group r a b) P).carrier SUBSET sw_points r a b
Proof
  metis_tac[generated_subset, short_weierstrass_group, sw_group_carrier]
QED

Theorem sw_generated_subgroup:
  FiniteField (r:'a field) /\ ShortWeierstrassCurve r a b /\
  P IN sw_points r a b ==>
  Subgroup (Generated (sw_group r a b) P) (sw_group r a b)
Proof
  metis_tac[generated_subgroup, short_weierstrass_finite_group,
            FiniteAbelianGroup_def_alt, sw_group_carrier]
QED

Theorem sw_generated_cyclic:
  FiniteField (r:'a field) /\ ShortWeierstrassCurve r a b /\
  P IN sw_points r a b ==>
  cyclic (Generated (sw_group r a b) P)
Proof
  metis_tac[cyclic_generated_group, short_weierstrass_finite_group,
            FiniteAbelianGroup_def_alt, sw_group_carrier]
QED

Theorem sw_generator_card:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b /\ 0 < order (sw_group r a b) P ==>
  CARD (Generated (sw_group r a b) P).carrier = order (sw_group r a b) P
Proof
  metis_tac[generated_group_card, short_weierstrass_group, sw_group_carrier]
QED

Theorem sw_point_order_divides_card:
  FiniteField (r:'a field) /\ ShortWeierstrassCurve r a b /\
  P IN sw_points r a b ==>
  order (sw_group r a b) P divides CARD (sw_points r a b)
Proof
  metis_tac[group_order_divides, short_weierstrass_finite_group,
            FiniteAbelianGroup_def_alt, sw_group_carrier]
QED

Theorem sw_cofactor_one_generated:
  FiniteField (r:'a field) /\ ShortWeierstrassCurve r a b /\
  P IN sw_points r a b /\
  order (sw_group r a b) P = CARD (sw_points r a b) ==>
  Generated (sw_group r a b) P = sw_group r a b
Proof
  strip_tac >>
  `FiniteGroup (sw_group r a b)` by
    metis_tac[short_weierstrass_finite_group, FiniteAbelianGroup_def_alt] >>
  `0 < order (sw_group r a b) P` by
    metis_tac[group_order_pos, sw_group_carrier] >>
  irule subgroup_eq_carrier >>
  reverse conj_tac >- metis_tac[sw_generated_subgroup] >>
  simp[sw_group_carrier] >>
  irule SUBSET_EQ_CARD >>
  metis_tac[FiniteGroup_def, sw_group_carrier, sw_generated_subset,
            sw_generator_card, SUBSET_FINITE]
QED

Theorem sw_cofactor_clearing:
  FiniteField (r:'a field) /\ ShortWeierstrassCurve r a b /\
  P IN sw_points r a b /\ CARD (sw_points r a b) = h * n ==>
  (sw_group r a b).exp P h IN (sw_torsion_group r a b n).carrier
Proof
  strip_tac >> SIMP_TAC bool_ss [sw_torsion_member] >>
  conj_tac >- metis_tac[sw_scalar_closed] >>
  `FiniteGroup (sw_group r a b)` by
    metis_tac[short_weierstrass_finite_group, FiniteAbelianGroup_def_alt] >>
  metis_tac[finite_group_Fermat, sw_group_carrier, sw_group_id,
            sw_scalar_mult]
QED

Theorem sw_cofactor_clearing_order:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b /\ 0 < h /\ 0 < n /\
  order (sw_group r a b) P = h * n ==>
  order (sw_group r a b) ((sw_group r a b).exp P h) = n
Proof
  strip_tac >>
  `0 < order (sw_group r a b) P` by simp[] >>
  `n divides order (sw_group r a b) P` by
    metis_tac[divides_def, MULT_COMM] >>
  `order (sw_group r a b) P DIV n = h` by simp[MULT_DIV] >>
  metis_tac[group_order_exp_cofactor, short_weierstrass_group,
            sw_group_carrier]
QED
