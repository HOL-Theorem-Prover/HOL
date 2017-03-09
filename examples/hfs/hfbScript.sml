open HolKernel Parse boolLib bossLib;

val _ = new_theory "hfb";

val _ = Datatype`hfb0 = HF_E | HF_I hfb0 hfb0`

val (hfb0_equiv_rules, hfb0_equiv_ind, hfb0_equiv_cases) = Hol_reln`
  hfb0_equiv HF_E HF_E ∧
  (∀x y b. hfb0_equiv (HF_I x (HF_I y b)) (HF_I y (HF_I x b))) ∧
  (∀x1 x2 b1 b2.
    hfb0_equiv x1 x2 ∧ hfb0_equiv b1 b2 ⇒
    hfb0_equiv (HF_I x1 b1) (HF_I x2 b2)) ∧
  (∀h1 h2 h3. hfb0_equiv h1 h2 ∧ hfb0_equiv h2 h3 ⇒ hfb0_equiv h1 h3)
`;

val hfb0_refl = Q.store_thm(
  "hfb0_refl",
  `∀h. hfb0_equiv h h`,
  Induct >> simp[hfb0_equiv_rules]);

val hfb0_sym = Q.store_thm(
  "hfb0_sym",
  `∀h1 h2. hfb0_equiv h1 h2 ⇒ hfb0_equiv h2 h1`,
  Induct_on `hfb0_equiv` >> metis_tac[hfb0_equiv_rules]);

val hfb0_trans = save_thm(
  "hfb0_trans",
  last (CONJUNCTS hfb0_equiv_rules))



val _ = export_theory();
