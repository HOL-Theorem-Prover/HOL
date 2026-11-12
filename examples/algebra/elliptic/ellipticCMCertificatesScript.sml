(* -------------------------------------------------------------------------
   Order-three endomorphism certificates for independent generators

   Documentation
   Abstract finite-group results supporting complex-multiplication curve
   certificates. No curve or endomorphism is assumed valid by its name:
   callers supply GroupEndo, f^3 = identity, exact point order, divisibility,
   and the required prime-order eigenvalue exclusions.

   Public interface
   - cm_cube_root_coprime restricts cubic roots modulo a prime;
     cm_cyclic_order_line identifies a cyclic subgroup of a specified order.
   - cm_order_three_automorphism and cm_order_three_eigenvalue describe
     endomorphisms whose third iterate is identity.
   - cm_independent establishes independence of P and
     Q = g.exp (f P) (M DIV d), under the stated exclusion hypotheses.
   - cm_independent_product_card and cm_independent_card_bound yield the
     subgroup-product size M*d and the corresponding ambient lower bound.

   The independence argument does not require coprimality of d and M DIV d.
   ------------------------------------------------------------------------- *)

Theory ellipticCMCertificates
Ancestors
  group number cardinal prime ring

open arithmeticTheory pred_setTheory cardinalTheory dividesTheory
     numberTheory groupTheory monoidTheory primeTheory ringTheory gcdTheory

Theorem cm_cube_root_coprime:
  prime q /\ coprime 3 (q - 1) /\ t < q /\ t ** 3 MOD q = 1 ==>
  t = 1
Proof
  strip_tac >>
  `1 < q /\ 0 < q` by metis_tac[ONE_LT_PRIME, PRIME_POS] >>
  `ordz q t divides 3` by
    metis_tac[ZN_order_divides_exp, DECIDE ``(0:num) < 3``] >>
  `0 < ordz q t` by
    metis_tac[ZERO_DIVIDES, NOT_ZERO_LT_ZERO, DECIDE ``(3:num) <> 0``] >>
  `ordz q t divides (q - 1)` by
    metis_tac[ZN_order_divides_phi, phi_prime] >>
  `ordz q t = 1` by metis_tac[coprime_common_factor] >>
  metis_tac[ZN_order_eq_1_alt, LESS_MOD]
QED

Theorem cm_generated_member_subset[local]:
  Group (g:'a group) /\ a IN g.carrier /\
  x IN (Generated g a).carrier ==>
  (Generated g x).carrier SUBSET (Generated g a).carrier
Proof
  rw[SUBSET_DEF, generated_element] >>
  metis_tac[group_exp_mult]
QED

Theorem cm_generated_member_order_divides[local]:
  FiniteGroup (g:'a group) /\ a IN g.carrier /\
  x IN (Generated g a).carrier ==>
  order g x divides order g a
Proof
  strip_tac >>
  `Generated g a <= g` by metis_tac[generated_subgroup] >>
  `FiniteGroup (Generated g a)` by metis_tac[generated_finite_group] >>
  `order (Generated g a) x divides CARD (Generated g a).carrier` by
    metis_tac[group_order_divides] >>
  metis_tac[subgroup_order, generated_group_card, group_order_pos,
            FiniteGroup_def]
QED

Theorem cm_generated_equal_order[local]:
  FiniteGroup (g:'a group) /\ a IN g.carrier /\ x IN g.carrier /\
  x IN (Generated g a).carrier /\ order g x = order g a ==>
  (Generated g x).carrier = (Generated g a).carrier
Proof
  strip_tac >>
  `Group g` by metis_tac[FiniteGroup_def] >>
  `(Generated g x).carrier SUBSET (Generated g a).carrier` by
    metis_tac[cm_generated_member_subset] >>
  `FINITE (Generated g x).carrier /\ FINITE (Generated g a).carrier` by
    metis_tac[generated_group_finite] >>
  `CARD (Generated g x).carrier = CARD (Generated g a).carrier` by
    metis_tac[generated_group_card, group_order_pos] >>
  metis_tac[SUBSET_EQ_CARD]
QED

(* The unique subgroup of a given order inside a finite cyclic group.
   In particular this does not require the order and cofactor to be coprime. *)
Theorem cm_cyclic_order_line:
  FiniteGroup (g:'a group) /\ a IN g.carrier /\
  0 < k /\ k divides order g a /\
  x IN (Generated g a).carrier /\ order g x = k ==>
  (Generated g x).carrier =
  (Generated g (g.exp a (order g a DIV k))).carrier
Proof
  strip_tac >>
  `Group g /\ 0 < order g a` by
    metis_tac[FiniteGroup_def, group_order_pos] >>
  `x IN g.carrier` by metis_tac[generated_subset, SUBSET_DEF] >>
  `?n. x = g.exp a n` by metis_tac[generated_element] >>
  `g.exp x k = g.id` by metis_tac[group_order_property] >>
  `g.exp a (n * k) = g.id` by metis_tac[group_exp_mult] >>
  `order g a divides (n * k)` by metis_tac[group_order_divides_exp] >>
  `(order g a DIV k) divides n` by
    metis_tac[dividend_divides_divisor_multiple] >>
  `?j. n = j * (order g a DIV k)` by metis_tac[divides_def] >>
  `x IN (Generated g (g.exp a (order g a DIV k))).carrier` by
    (simp[generated_element] >> qexists_tac `j` >>
     metis_tac[group_exp_mult, MULT_COMM]) >>
  `g.exp a (order g a DIV k) IN g.carrier` by
    metis_tac[group_exp_element] >>
  `order g (g.exp a (order g a DIV k)) = k` by
    metis_tac[group_order_exp_cofactor] >>
  metis_tac[cm_generated_equal_order]
QED

Theorem cm_order_three_automorphism:
  GroupEndo f (g:'a group) /\
  (!x. x IN g.carrier ==> f (f (f x)) = x) ==>
  GroupIso f g g
Proof
  strip_tac >> fs[GroupEndo_def] >>
  rw[GroupIso_def, BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  metis_tac[group_homo_element]
QED

Theorem cm_order_three_eigenvalue:
  Group (g:'a group) /\ GroupEndo f g /\
  (!x. x IN g.carrier ==> f (f (f x)) = x) /\
  u IN g.carrier /\ order g u = q /\ 1 < q /\
  f u = g.exp u t ==>
  t ** 3 MOD q = 1
Proof
  strip_tac >>
  `GroupHomo f g g` by metis_tac[GroupEndo_def] >>
  `f (f u) = g.exp u (t * t)` by
    metis_tac[group_homo_exp, group_exp_mult] >>
  `f (f (f u)) = g.exp u ((t * t) * t)` by
    ( imp_res_tac group_homo_exp >> metis_tac [group_exp_mult, MULT_ASSOC, MULT_COMM] )>>
  `g.exp u ((t * t) * t) = u` by metis_tac[] >>
  `t ** 3 = (t * t) * t` by
    (PURE_ONCE_REWRITE_TAC [DECIDE ``(3:num) = 2 + 1``] >>
     PURE_REWRITE_TAC
       [arithmeticTheory.EXP_ADD, arithmeticTheory.EXP_2,
        arithmeticTheory.EXP_1] >> REFL_TAC) >>
  `g.exp u (t ** 3) = g.exp u 1` by metis_tac[group_exp_1] >>
  `0 < order g u` by decide_tac >>
  `t ** 3 MOD order g u = 1 MOD order g u` by
    metis_tac[group_exp_eq_condition] >>
  metis_tac[ONE_MOD]
QED

(* A nontrivial intersection would supply a common prime-order line.
   Applying f to its generator then gives a forbidden cubic eigenvalue. *)
Theorem cm_independent:
  FiniteGroup (g:'a group) /\ P IN g.carrier /\
  order g P = M /\ 0 < M /\ 0 < d /\ d divides M /\
  GroupEndo f g /\
  (!x. x IN g.carrier ==> f (f (f x)) = x) /\
  Q = g.exp (f P) (M DIV d) /\
  (!q t. prime q /\ q divides d /\ t < q /\ t ** 3 MOD q = 1 ==>
     f (g.exp P (M DIV q)) <>
       g.exp (g.exp P (M DIV q)) t) ==>
  independent g P Q
Proof
  strip_tac >>
  `Group g` by metis_tac[FiniteGroup_def] >>
  `GroupHomo f g g` by metis_tac[GroupEndo_def] >>
  `GroupIso f g g` by metis_tac[cm_order_three_automorphism] >>
  `f P IN g.carrier /\ order g (f P) = M` by
    metis_tac[group_homo_element, group_iso_order] >>
  `Q IN g.carrier /\ order g Q = d` by
    metis_tac[group_exp_element, group_order_exp_cofactor] >>
  simp[EXTENSION, IN_INTER, IN_SING] >> gen_tac >>
  eq_tac >| [
    strip_tac >> CCONTR_TAC >>
    `x IN g.carrier` by metis_tac[generated_subset, SUBSET_DEF] >>
    `0 < order g x /\ order g x <> 1` by
      metis_tac[group_order_pos, group_order_eq_1] >>
    `?q. prime q /\ q divides order g x` by metis_tac[PRIME_FACTOR] >>
    `0 < q /\ q <> 1` by metis_tac[PRIME_POS, prime_def] >>
    `1 < q` by decide_tac >>
    `order g x divides d` by
      metis_tac[cm_generated_member_order_divides] >>
    `q divides d /\ q divides M` by metis_tac[DIVIDES_TRANS] >>
    qabbrev_tac `y = g.exp x (order g x DIV q)` >>
    `y = g.exp x (order g x DIV q)` by simp[Abbr`y`] >>
    `y IN g.carrier /\ order g y = q` by
      metis_tac[group_exp_element, group_order_exp_cofactor] >>
    `y IN (Generated g x).carrier` by
      metis_tac[generated_element] >>
    `y IN (Generated g P).carrier /\ y IN (Generated g Q).carrier` by
      metis_tac[cm_generated_member_subset, SUBSET_DEF] >>
    `Q IN (Generated g (f P)).carrier` by
      metis_tac[generated_element] >>
    `y IN (Generated g (f P)).carrier` by
      metis_tac[cm_generated_member_subset, SUBSET_DEF] >>
    qabbrev_tac `u = g.exp P (M DIV q)` >>
    `u = g.exp P (M DIV q)` by simp[Abbr`u`] >>
    `u IN g.carrier /\ order g u = q` by
      metis_tac[group_exp_element, group_order_exp_cofactor] >>
    `f u = g.exp (f P) (M DIV q)` by
      metis_tac[group_homo_exp] >>
    `(Generated g y).carrier = (Generated g u).carrier` by
      metis_tac[cm_cyclic_order_line] >>
    `(Generated g y).carrier = (Generated g (f u)).carrier` by
      metis_tac[cm_cyclic_order_line] >>
    `f u IN g.carrier` by metis_tac[group_homo_element] >>
    `f u IN (Generated g u).carrier` by
      metis_tac[generated_gen_element] >>
    `?t. t < q /\ f u = g.exp u t` by
      (`(Generated g u).carrier = IMAGE (g.exp u) (count q)` by
         metis_tac[generated_carrier_as_image] >>
       qpat_x_assum
         `(Generated g u).carrier = IMAGE (g.exp u) (count q)`
         (fn eq => qpat_x_assum `f u IN (Generated g u).carrier`
           (mp_tac o PURE_REWRITE_RULE [eq, IN_IMAGE, IN_COUNT])) >>
       metis_tac[]) >>
    `t ** 3 MOD q = 1` by metis_tac[cm_order_three_eigenvalue] >>
    metis_tac[],
    rw[generated_carrier_has_id]
  ]
QED

Theorem cm_independent_product_card:
  FiniteGroup (g:'a group) /\ P IN g.carrier /\
  order g P = M /\ 0 < M /\ 0 < d /\ d divides M /\
  GroupEndo f g /\
  (!x. x IN g.carrier ==> f (f (f x)) = x) /\
  Q = g.exp (f P) (M DIV d) /\
  (!q t. prime q /\ q divides d /\ t < q /\ t ** 3 MOD q = 1 ==>
     f (g.exp P (M DIV q)) <>
       g.exp (g.exp P (M DIV q)) t) ==>
  CARD (subgroup_cross g (Generated g P) (Generated g Q)).carrier = M * d
Proof
  strip_tac >>
  `Group g` by metis_tac[FiniteGroup_def] >>
  `GroupHomo f g g` by metis_tac[GroupEndo_def] >>
  `GroupIso f g g` by metis_tac[cm_order_three_automorphism] >>
  `f P IN g.carrier /\ order g (f P) = M` by
    metis_tac[group_homo_element, group_iso_order] >>
  `Q IN g.carrier /\ order g Q = d` by
    metis_tac[group_exp_element, group_order_exp_cofactor] >>
  metis_tac[cm_independent, independent_generator_2_card]
QED

Theorem cm_independent_card_bound:
  FiniteGroup (g:'a group) /\ P IN g.carrier /\
  order g P = M /\ 0 < M /\ 0 < d /\ d divides M /\
  GroupEndo f g /\
  (!x. x IN g.carrier ==> f (f (f x)) = x) /\
  Q = g.exp (f P) (M DIV d) /\
  (!q t. prime q /\ q divides d /\ t < q /\ t ** 3 MOD q = 1 ==>
     f (g.exp P (M DIV q)) <>
       g.exp (g.exp P (M DIV q)) t) ==>
  M * d <= CARD g.carrier
Proof
  strip_tac >>
  `Group g /\ FINITE g.carrier` by metis_tac[FiniteGroup_def] >>
  `f P IN g.carrier` by
    metis_tac[GroupEndo_def, group_homo_element] >>
  `Q IN g.carrier` by metis_tac[group_exp_element] >>
  `(Generated g P).carrier SUBSET g.carrier /\
   (Generated g Q).carrier SUBSET g.carrier` by
    metis_tac[generated_subset] >>
  `(subgroup_cross g (Generated g P) (Generated g Q)).carrier
     SUBSET g.carrier` by
    metis_tac[subgroup_cross_property, subset_cross_subset] >>
  `CARD (subgroup_cross g (Generated g P) (Generated g Q)).carrier = M * d` by
    metis_tac[cm_independent_product_card] >>
  metis_tac[CARD_SUBSET]
QED
