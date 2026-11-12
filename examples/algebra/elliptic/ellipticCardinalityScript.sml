(* ------------------------------------------------------------------------- *)
(* Elementary Curve Cardinality and Exact-Order Certificates                  *)
(* ------------------------------------------------------------------------- *)
(*
   Documentation

   Finite short-Weierstrass curves have at most two affine points per
   x-coordinate and one point at infinity. This is an elementary bound,
   not Hasse's theorem. Curve results retain ShortWeierstrassCurve and
   FiniteField hypotheses where needed.

   Cardinality:
     sw_x_fiber_card, sw_points_card_bound    CARD points <= 2*CARD field + 1.
     sw_no_two_torsion_odd_card              No nonidentity 2-torsion implies
                                            odd cardinality.
     sw_cardinality_from_odd_divisor,
       sw_cardinality_from_odd_subgroup,
       sw_cardinality_from_odd_point_order   Identify the full cardinality
                                            using the bound and torsion test.
     sw_root_free_no_two_torsion             Root-free cubic gives that test.

   Exact order:
     group_exact_order_certificate, sw_exact_order_certificate.
   To establish order N > 0, check [N]P = O and [N/q]P <> O for every prime
   divisor q of N. An annihilation equation alone does not prove exact order.
*)

Theory ellipticCardinality
Ancestors
  shortWeierstrass shortWeierstrassGroup ellipticTorsion cardinal prime

open arithmeticTheory pred_setTheory cardinalTheory dividesTheory
     groupTheory monoidTheory fieldTheory ringTheory primeTheory

Theorem finite_involution_even_card:
  !s:'a set. FINITE s ==>
  !f. (!x. x IN s ==> f x IN s /\ f (f x) = x /\ f x <> x) ==>
      EVEN (CARD s)
Proof
  ho_match_mp_tac FINITE_COMPLETE_INDUCTION >>
  rpt strip_tac >>
  Cases_on `s = {}` >- simp[] >>
  `?x. x IN s` by metis_tac[MEMBER_NOT_EMPTY] >>
  `f x IN s /\ f x <> x /\ f (f x) = x` by metis_tac[] >>
  `s DELETE x DELETE f x PSUBSET s` by
    (rw[PSUBSET_DEF, SUBSET_DEF, EXTENSION] >> metis_tac[]) >>
  `EVEN (CARD (s DELETE x DELETE f x))` by
    (qpat_x_assum `!y. y PSUBSET s ==> _`
       (qspec_then `s DELETE x DELETE f x` mp_tac) >>
     simp[] >> disch_then (qspec_then `f` irule) >>
     rw[IN_DELETE] >> metis_tac[]) >>
  `s = x INSERT (f x INSERT (s DELETE x DELETE f x))` by
    (rw[EXTENSION] >> metis_tac[]) >>
  `CARD s = SUC (SUC (CARD (s DELETE x DELETE f x)))` by
    (pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[CARD_INSERT]) >>
  qpat_x_assum `CARD s = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  qpat_x_assum `EVEN (CARD (s DELETE x DELETE f x))`
    (fn th => REWRITE_TAC [EVEN, th])
QED

Theorem sw_x_fiber_card:
  ShortWeierstrassCurve (r:'a field) a b /\ FiniteField r ==>
  CARD {P | ?y. P = ECAffine x y /\ P IN sw_points r a b} <= 2
Proof
  strip_tac >>
  qabbrev_tac `s = {P | ?y. P = ECAffine x y /\ P IN sw_points r a b}` >>
  Cases_on `s = {}` >- simp[] >>
  `?P. P IN s` by metis_tac[MEMBER_NOT_EMPTY] >>
  `?y. P = ECAffine x y /\ P IN sw_points r a b` by
    fs[Abbr`s`] >>
  `s SUBSET {ECAffine x y; ECAffine x (r.sum.inv y)}` by
    (rw[Abbr`s`, SUBSET_DEF] >>
     metis_tac[sw_same_x_on_curve, sw_points_member]) >>
  `CARD s <= CARD {ECAffine x y; ECAffine x (r.sum.inv y)}` by
    metis_tac[CARD_SUBSET, FINITE_INSERT, FINITE_EMPTY] >>
  `CARD {ECAffine x y; ECAffine x (r.sum.inv y)} <= 2` by
    (Cases_on `y = r.sum.inv y` >> simp[CARD_INSERT]) >>
  decide_tac
QED

Theorem sw_points_card_bound:
  ShortWeierstrassCurve (r:'a field) a b /\ FiniteField r ==>
  CARD (sw_points r a b) <= 2 * CARD r.carrier + 1
Proof
  strip_tac >>
  qabbrev_tac `fiber = \x. {P | ?y. P = ECAffine x y /\ P IN sw_points r a b}` >>
  `FINITE r.carrier` by metis_tac[FiniteField_def] >>
  `!x. FINITE (fiber x)` by
    (gen_tac >> irule SUBSET_FINITE >>
     qexists_tac `sw_points r a b` >>
     simp[sw_points_finite, Abbr`fiber`, SUBSET_DEF] >> metis_tac[]) >>
  `CARD (BIGUNION {fiber x | x IN r.carrier}) <= CARD r.carrier * 2` by
    (irule CARD_BIGUNION_LE >>
     asm_simp_tac bool_ss [HAS_SIZE, sw_x_fiber_card, Abbr`fiber`]) >>
  `FINITE (BIGUNION {fiber x | x IN r.carrier})` by
    (simp[SET_RULE ``{fiber x | x IN s} = IMAGE fiber s``, FINITE_BIGUNION] >>
     metis_tac[]) >>
  `sw_points r a b = {ECInfinity} UNION BIGUNION {fiber x | x IN r.carrier}` by
    (REWRITE_TAC [SET_RULE ``{f x | x IN s} = IMAGE f s``] >>
     ONCE_REWRITE_TAC [EXTENSION] >>
     gen_tac >> Cases_on `x` >>
     simp[IN_BIGUNION_IMAGE, Abbr`fiber`, sw_affine_mem] >> metis_tac[]) >>
  `CARD (sw_points r a b) <=
   1 + CARD (BIGUNION {fiber x | x IN r.carrier})` by
    metis_tac[CARD_UNION_LE, FINITE_SING, CARD_SING] >>
  decide_tac
QED

Theorem sw_points_card_positive:
  FiniteField (r:'a field) ==>
  0 < CARD (sw_points r a b)
Proof
  strip_tac >>
  metis_tac[sw_points_finite, sw_infinity_mem, CARD_EQ_0,
            NOT_IN_EMPTY, NOT_ZERO_LT_ZERO]
QED

Theorem sw_double_eq_infinity:
  ShortWeierstrassCurve (r:'a field) a b /\ P IN sw_points r a b ==>
  ((sw_group r a b).exp P 2 = ECInfinity <=> sw_neg r P = P)
Proof
  strip_tac >>
  `Group (sw_group r a b)` by metis_tac[short_weierstrass_group] >>
  `P IN (sw_group r a b).carrier` by simp[] >>
  `(sw_group r a b).exp P 2 = sw_add r a b P P` by
    (ONCE_REWRITE_TAC [DECIDE ``2 = SUC 1``] >>
     simp[group_exp_SUC, group_exp_1]) >>
  metis_tac[group_linv_unique, sw_group_inv, sw_group_id, sw_group_op,
            sw_add_neg_l]
QED

Theorem sw_no_two_torsion_odd_card:
  ShortWeierstrassCurve (r:'a field) a b /\ FiniteField r /\
  (!P. P IN sw_points r a b /\ (sw_group r a b).exp P 2 = ECInfinity ==>
       P = ECInfinity) ==>
  ODD (CARD (sw_points r a b))
Proof
  strip_tac >>
  `EVEN (CARD (sw_points r a b DELETE ECInfinity))` by
    (irule finite_involution_even_card >>
     asm_simp_tac bool_ss [FINITE_DELETE, sw_points_finite] >>
     qexists_tac `sw_neg r` >>
     PURE_REWRITE_TAC [IN_DELETE] >> rpt strip_tac >>
     metis_tac[sw_neg_mem, sw_neg_involutive, sw_neg_infinity,
               sw_double_eq_infinity]) >>
  `sw_points r a b = ECInfinity INSERT (sw_points r a b DELETE ECInfinity)` by
    metis_tac[INSERT_DELETE, sw_infinity_mem] >>
  `CARD (sw_points r a b) = SUC (CARD (sw_points r a b DELETE ECInfinity))` by
    (pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[CARD_INSERT, sw_points_finite]) >>
  qpat_x_assum `CARD (sw_points r a b) = _`
    (fn th => ONCE_REWRITE_TAC [th]) >>
  qpat_x_assum `EVEN (CARD (sw_points r a b DELETE ECInfinity))`
    (fn th => REWRITE_TAC [ODD, GSYM EVEN_ODD, th])
QED

Theorem sw_cardinality_from_odd_divisor:
  ShortWeierstrassCurve (r:'a field) a b /\ FiniteField r /\
  0 < N /\ ODD N /\ N divides CARD (sw_points r a b) /\
  2 * CARD r.carrier + 1 < 3 * N /\
  (!P. P IN sw_points r a b /\ (sw_group r a b).exp P 2 = ECInfinity ==>
       P = ECInfinity) ==>
  CARD (sw_points r a b) = N
Proof
  strip_tac >>
  `ODD (CARD (sw_points r a b))` by
    metis_tac[sw_no_two_torsion_odd_card] >>
  `0 < CARD (sw_points r a b)` by metis_tac[sw_points_card_positive] >>
  `CARD (sw_points r a b) <= 2 * CARD r.carrier + 1` by
    metis_tac[sw_points_card_bound] >>
  `?k. CARD (sw_points r a b) = k * N` by
    metis_tac[divides_def] >>
  `ODD k` by metis_tac[ODD_MULT] >>
  `k < 3` by
    (spose_not_then strip_assume_tac >>
     `3 <= k` by decide_tac >>
     `3 * N <= k * N` by simp[LE_MULT_RCANCEL] >>
     decide_tac) >>
  `k = 0 \/ k = 1 \/ k = 2` by decide_tac >> fs[]
QED

Theorem sw_cardinality_from_odd_subgroup:
  ShortWeierstrassCurve (r:'a field) a b /\ FiniteField r /\
  Subgroup h (sw_group r a b) /\ CARD h.carrier = N /\
  0 < N /\ ODD N /\ 2 * CARD r.carrier + 1 < 3 * N /\
  (!P. P IN sw_points r a b /\ (sw_group r a b).exp P 2 = ECInfinity ==>
       P = ECInfinity) ==>
  CARD (sw_points r a b) = N
Proof
  strip_tac >> irule sw_cardinality_from_odd_divisor >>
  simp[] >>
  metis_tac[Lagrange_thm, short_weierstrass_group,
            sw_group_carrier, sw_points_finite]
QED

Theorem sw_cardinality_from_odd_point_order:
  ShortWeierstrassCurve (r:'a field) a b /\ FiniteField r /\
  P IN sw_points r a b /\ order (sw_group r a b) P = N /\
  0 < N /\ ODD N /\ 2 * CARD r.carrier + 1 < 3 * N /\
  (!Q. Q IN sw_points r a b /\ (sw_group r a b).exp Q 2 = ECInfinity ==>
       Q = ECInfinity) ==>
  CARD (sw_points r a b) = N
Proof
  strip_tac >> irule sw_cardinality_from_odd_divisor >>
  metis_tac[sw_point_order_divides_card]
QED

Theorem sw_root_free_no_two_torsion:
  ShortWeierstrassCurve (r:'a field) a b /\
  (!x. x IN r.carrier ==> sw_curve_rhs r a b x <> r.sum.id) ==>
  !P. P IN sw_points r a b /\ (sw_group r a b).exp P 2 = ECInfinity ==>
      P = ECInfinity
Proof
  rpt strip_tac >>
  `sw_neg r P = P` by metis_tac[sw_double_eq_infinity] >>
  Cases_on `P` >- simp[] >>
  rename1 `ECAffine x y IN sw_points r a b` >>
  fs[sw_neg_def, sw_affine_mem] >>
  `Field r /\ char r <> 2` by fs[ShortWeierstrassCurve_def] >>
  `y = r.sum.id` by
    (spose_not_then strip_assume_tac >>
     `y IN R+` by simp[field_nonzero_eq] >>
     `r.prod.op (r.sum.inv r.prod.id) y = r.prod.op r.prod.id y` by
       metis_tac[field_mult_lneg, field_mult_lone, field_one_element] >>
     metis_tac[field_mult_rcancel, field_one_element, field_neg_element,
               field_neg_one_eq_one]) >>
  fs[field_zero_exp] >> metis_tac[]
QED

Theorem group_exact_order_certificate:
  Group (g:'a group) /\ P IN g.carrier /\ 0 < N /\
  g.exp P N = g.id /\
  (!q. prime q /\ q divides N ==> g.exp P (N DIV q) <> g.id) ==>
  order g P = N
Proof
  strip_tac >>
  `order g P divides N` by metis_tac[group_order_condition] >>
  `?k. N = k * order g P` by metis_tac[divides_def] >>
  `0 < k /\ 0 < order g P` by
    (Cases_on `k = 0` >> Cases_on `order g P = 0` >> fs[] >> decide_tac) >>
  Cases_on `k = 1` >- fs[] >>
  `1 < k` by decide_tac >>
  `?q. prime q /\ q divides k` by
    metis_tac[prime_divisors_nonempty, MEMBER_NOT_EMPTY, prime_divisors_element] >>
  `?t. k = t * q` by metis_tac[divides_def] >>
  `q divides N` by metis_tac[DIVIDES_TRANS, divides_def, MULT_COMM] >>
  `0 < q` by metis_tac[PRIME_POS] >>
  `N DIV q = t * order g P` by
    ( `N = (t * order g P) * q` by metis_tac[MULT_ASSOC, MULT_COMM] >>
      metis_tac[MULT_DIV]) >>
  `order g P divides (N DIV q)` by metis_tac[divides_def] >>
  metis_tac[group_order_condition]
QED

Theorem sw_exact_order_certificate:
  ShortWeierstrassCurve (r:'a field) a b /\ P IN sw_points r a b /\
  0 < N /\ (sw_group r a b).exp P N = ECInfinity /\
  (!q. prime q /\ q divides N ==>
       (sw_group r a b).exp P (N DIV q) <> ECInfinity) ==>
  order (sw_group r a b) P = N
Proof
  metis_tac[group_exact_order_certificate, short_weierstrass_group,
            sw_group_carrier, sw_group_id]
QED
