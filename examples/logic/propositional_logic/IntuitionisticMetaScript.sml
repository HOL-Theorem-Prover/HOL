Theory IntuitionisticMeta
Ancestors
  ipropSyntax IntuitionisticHilbert IntuitionisticSemantics

Theorem soundness:
  ∅ ⊢ⁱ ϕ ⇒ valid ϕ
Proof
  Induct_on‘ded’ >> rw[] >>
  gvs[valid_def, models_def] >>
  metis_tac[isModel_def, models_monotone]
QED

(* exercise: show ¬ded {a → b} (¬p ∨ q)
two element model, first world has nothing true; second has a and b.
first world has a ⇒ b, but has neither b, nor ¬a, as former effectively
means that no future world has a.*)
Theorem example:
  ¬({IVar p ⇒ⁱ IVar q} ⊢ⁱ ineg (IVar p) ∨ⁱ  IVar q)
Proof
  simp[GSYM deduction_iff] >> strip_tac >>
  drule soundness >> simp[valid_def] >>
  qexists ‘<| worlds := {1;2}; valn := \w v. w = 2 ∧ (v = p ∨ v = q);
              rel := \m n. m = n ∨ n = 2 |>’ >>
  qexists ‘1’ >> simp[isModel_def, models_def]
QED

Theorem nonLEM:
  ¬(∅ ⊢ⁱ IVar p ∨ⁱ ineg (IVar p))
Proof
  strip_tac >> drule soundness >> simp[valid_def] >>
  simp[models_def, SF CONJ_ss, PULL_EXISTS] >>
  qexists ‘<| worlds := {1;2}; valn := λw v. w = 2 ∧ v = p;
              rel := λm n. m = n ∨ n = 2 |>’ >>
  simp[isModel_def]
QED
