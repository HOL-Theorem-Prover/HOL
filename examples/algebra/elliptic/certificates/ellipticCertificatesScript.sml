(* -------------------------------------------------------------------------
   Elliptic-curve arithmetic and order certificate rules

   Documentation
   Support checked inverse witnesses and binary evaluation of the existing
   short-Weierstrass group exponent. Points use ECAffine x y or ECInfinity;
   curve validity and point membership remain explicit hypotheses.

   Public interface
   - sw_field_sum_inv_witness, sw_field_prod_inv_witness and
     sw_GF_prod_inv_witness justify proposed inverses by checked operations.
   - sw_scalar_double and sw_scalar_double_add provide binary scalar steps.
   - sw_prime_generator_order deduces exact prime order from a nonidentity
     point annihilated by that prime, with curve/membership hypotheses.
   - sw_GF_prod_exp relates numeric field powers to modular powers;
     finite_field_cube_nonresidue supplies a checked cubic obstruction.

   The ML scalar libraries propose coordinates and inverse values; these
   rules require proofs and do not introduce a new scalar operation.
   ------------------------------------------------------------------------- *)

Theory ellipticCertificates
Ancestors
  shortWeierstrass shortWeierstrassGroup ellipticTorsion fieldInstances

open fieldTheory fieldInstancesTheory groupTheory ringTheory

Theorem sw_field_sum_inv_witness:
  !(r:'a field) x y.
    Field r /\ x IN r.carrier /\ y IN r.carrier /\
    r.sum.op x y = r.sum.id ==>
    r.sum.inv x = y
Proof
  metis_tac[field_add_eq_zero]
QED

Theorem sw_field_prod_inv_witness:
  !(r:'a field) x y.
    Field r /\ x IN r.carrier /\ x <> r.sum.id /\
    y IN r.carrier /\ r.prod.op x y = r.prod.id ==>
    r.prod.inv x = y
Proof
  rpt strip_tac >>
  `r.prod.inv x = (Invertibles r.prod).inv x` by
    metis_tac[sw_field_prod_inv_eq] >>
  asm_rewrite_tac[] >>
  CONV_TAC SYM_CONV >>
  irule ring_unit_rinv_unique >>
  simp[GSYM field_nonzero_unit, field_nonzero_eq, field_is_ring]
QED

(* A proposed numerical inverse is checked by multiplication in GF p. *)
Theorem sw_GF_prod_inv_witness:
  !p x y.
    prime p /\ x < p /\ x <> 0 /\ y < p /\ (x * y) MOD p = 1 ==>
    (GF p).prod.inv x = y
Proof
  rpt strip_tac >>
  irule sw_field_prod_inv_witness >>
  simp[GF_field, GF_eval]
QED

(* Binary certificates concern the existing group exponent, not a new scalar. *)
Theorem sw_scalar_double:
  !(r:'a field) a b P n.
    ShortWeierstrassCurve r a b /\ P IN sw_points r a b ==>
    (sw_group r a b).exp P (2 * n) =
      sw_add r a b ((sw_group r a b).exp P n)
                   ((sw_group r a b).exp P n)
Proof
  rpt strip_tac >>
  `2 * n = n + n` by decide_tac >>
  asm_simp_tac bool_ss [sw_scalar_add]
QED

Theorem sw_scalar_double_add:
  !(r:'a field) a b P n.
    ShortWeierstrassCurve r a b /\ P IN sw_points r a b ==>
    (sw_group r a b).exp P (2 * n + 1) =
      sw_add r a b P
        (sw_add r a b ((sw_group r a b).exp P n)
                      ((sw_group r a b).exp P n))
Proof
  rpt strip_tac >>
  `2 * n + 1 = 1 + (n + n)` by decide_tac >>
  metis_tac[sw_scalar_add, sw_scalar_one]
QED

Theorem sw_prime_generator_order:
  ShortWeierstrassCurve (r:'a field) a b /\
  P IN sw_points r a b /\ P <> ECInfinity /\ prime n /\
  (sw_group r a b).exp P n = ECInfinity ==>
  order (sw_group r a b) P = n
Proof
  strip_tac >>
  `Group (sw_group r a b) /\ P IN (sw_group r a b).carrier` by
    metis_tac[short_weierstrass_group, sw_group_carrier] >>
  `order (sw_group r a b) P divides n` by
    metis_tac[group_order_divides_exp, sw_group_id] >>
  metis_tac[dividesTheory.prime_def, group_order_eq_1, sw_group_id]
QED

Theorem sw_GF_prod_exp:
  !p x n. 1 < p ==>
    (GF p).prod.exp x n = x ** n MOD p
Proof
  gen_tac >> gen_tac >> Induct >>
  simp[monoidTheory.monoid_exp_0, GF_eval] >>
  strip_tac >>
  simp[monoidTheory.monoid_exp_SUC, GF_eval, arithmeticTheory.EXP] >>
  metis_tac[arithmeticTheory.MOD_TIMES2, arithmeticTheory.MOD_MOD]
QED

Theorem finite_field_cube_nonresidue:
  !(r:'a field) c k.
    FiniteField r /\ c IN r.carrier /\ c <> r.sum.id /\
    CARD r.carrier - 1 = 3 * k /\ r.prod.exp c k <> r.prod.id ==>
    !x. x IN r.carrier ==> r.prod.exp x 3 <> c
Proof
  rpt strip_tac >>
  `Field r` by metis_tac[FiniteField_def] >>
  `x <> r.sum.id` by
    metis_tac[field_zero_exp, DECIDE ``(3:num) <> 0``] >>
  `x IN ring_nonzero r` by simp[field_nonzero_eq] >>
  `r.prod.exp x (CARD r.carrier - 1) = r.prod.id` by
    metis_tac[finite_field_Fermat, finite_field_nonzero_carrier_card] >>
  metis_tac[field_exp_mult]
QED

