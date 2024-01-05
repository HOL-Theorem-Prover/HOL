open HolKernel Parse boolLib bossLib stringTheory;

val _ = new_theory "SlaneyRL";


Datatype: s_prop = s_VAR string
          | s_IMP s_prop s_prop
          | s_AND s_prop s_prop
          | s_OR s_prop s_prop
          | s_ICONJ s_prop s_prop
          | s_NOT s_prop
          | s_tt
End


val _ = set_fixity "-->ₛ" (Infixr 490);
val _ = overload_on ("-->ₛ", “s_IMP”);

val _ = set_fixity "&ₛ" (Infixl 600);
val _ = overload_on ("&ₛ", “s_AND”);

val _ = set_fixity "Vₛ" (Infixl 500);
val _ = overload_on ("Vₛ", “s_OR”);

val _ = overload_on ("~ₛ", “s_NOT”);

val _ = overload_on ("τₛ", “s_tt”);

Definition s_DIMP_def:
  s_DIMP A B = (A -->ₛ B) &ₛ (B -->ₛ A)
End


val _ = set_fixity "<->ₛ" (Infix (NONASSOC, 491)); (* Infix (NONASSOC, 491)*)
val _ = overload_on ("<->ₛ", “s_DIMP”);

val _ = set_fixity "ioₛ" (Infixl 600);
val _ = overload_on ("ioₛ", “s_ICONJ”);

Inductive slaney_provable:
[s_identity:]
  ∀A. slaney_provable (A -->ₛ A)
[s_permutation:]
  ∀A B C. slaney_provable ((A -->ₛ (B -->ₛ C)) -->ₛ (B -->ₛ (A -->ₛ C)))
[s_transitivity:]
  ∀A B C. slaney_provable ((A -->ₛ B) -->ₛ ((B -->ₛ C) -->ₛ (A -->ₛ C)))
[s_contraction:] (∀A B. slaney_provable ((A -->ₛ (A -->ₛ B)) -->ₛ (A -->ₛ B)))
[s_conjunction_l:] (∀A B. slaney_provable ((A &ₛ B) -->ₛ A))
[s_conjunction_r:] (∀A B. slaney_provable ((A &ₛ B) -->ₛ B))
[s_conj_introduction:]
  ∀A B C. slaney_provable (((A -->ₛ B) &ₛ (A -->ₛ C)) -->ₛ (A -->ₛ (B &ₛ C)))
[s_disjunction_l:] (∀A B. slaney_provable (A -->ₛ (A Vₛ B)))
[s_disjunction_r:] (∀A B. slaney_provable (B -->ₛ (A Vₛ B)))
[s_disjunction_elim:]
  ∀A B C. slaney_provable (((A -->ₛ C) &ₛ (B -->ₛ C)) -->ₛ ((A Vₛ B) -->ₛ C))
[s_distribution:]
  ∀A B C. slaney_provable ((A &ₛ (B Vₛ C)) -->ₛ ((A &ₛ B) Vₛ (A &ₛ C)))
[s_contrapositive:] ∀A B. slaney_provable ((A -->ₛ (~ₛB)) -->ₛ (B -->ₛ (~ₛA)))
[s_double_negation:] (∀A. slaney_provable ((~ₛ(~ₛA)) -->ₛ A ))
[s_adjunction_rule:]
  (∀A B. slaney_provable A ∧ slaney_provable B ⇒ slaney_provable (A &ₛ B))
[s_modus_ponens:]
  (∀A B. slaney_provable A ∧ slaney_provable (A -->ₛ B) ⇒ slaney_provable B)
[s_intensional_conj_lr:]
  (∀A B C. slaney_provable ((A ioₛ B) -->ₛ C) ⇒ slaney_provable (A -->ₛ (B -->ₛ C)))
[s_intensional_conj_rl:]
  ∀A B C. slaney_provable (A -->ₛ (B -->ₛ C)) ⇒
          slaney_provable ((A ioₛ B) -->ₛ C)
[s_tt_rl:] (∀A. slaney_provable A ⇒ slaney_provable (τₛ -->ₛ A))
[s_tt_lr:] (∀A. slaney_provable (τₛ -->ₛ A) ⇒ slaney_provable A)
End

Theorem s_assertion:
  ∀A B. slaney_provable (A -->ₛ ((A -->ₛ B) -->ₛ B))
Proof
  rpt strip_tac >> irule s_modus_ponens >> qexists_tac ‘(A -->ₛ B) -->ₛ (A -->ₛ B)’ >>
  simp [s_identity, s_permutation]
QED

Theorem s_prefixing:
  ∀A B C. slaney_provable ((A -->ₛ B) -->ₛ ((C -->ₛ A) -->ₛ (C -->ₛ B)))
Proof
  metis_tac[slaney_provable_rules]
QED

Theorem s_equiv_identity:
  ∀A. slaney_provable (A <->ₛ A)
Proof
  simp [s_DIMP_def, slaney_provable_rules]
QED

Theorem s_equiv_symmetry:
  ∀A B. slaney_provable (A <->ₛ B) ⇔ slaney_provable (B <->ₛ A)
Proof
  metis_tac [slaney_provable_rules, s_DIMP_def]
QED

Theorem s_equiv_transitivity:
  ∀ A B C. slaney_provable (A <->ₛ B) ∧ slaney_provable (B <->ₛ C) ⇒
           slaney_provable (A <->ₛ C)
Proof
  metis_tac[s_adjunction_rule, s_transitivity, s_conjunction_l, s_conjunction_r, s_conj_introduction, s_DIMP_def, s_modus_ponens]
QED

Theorem s_conj_intro_rule:
  ∀A B C. slaney_provable (A -->ₛ B) ∧
          slaney_provable (A -->ₛ C) ⇒
          slaney_provable (A -->ₛ (B &ₛ C))
Proof
  metis_tac[slaney_provable_rules]
QED

Theorem s_equiv_replacement:
  ∀A B C. slaney_provable (A <->ₛ B) ⇒
          (slaney_provable ((A -->ₛ C) <->ₛ (B -->ₛ C))) ∧
          (slaney_provable ((C -->ₛ A) <->ₛ (C -->ₛ B))) ∧
          slaney_provable (~ₛ A <->ₛ ~ₛ B) ∧
          (slaney_provable ((A &ₛ C) <->ₛ (B &ₛ C))) ∧
          (slaney_provable ((C &ₛ A) <->ₛ (C &ₛ A))) ∧
          (slaney_provable ((A Vₛ C) <->ₛ (B Vₛ C))) ∧
          (slaney_provable ((C Vₛ A) <->ₛ (C Vₛ A))) ∧
          (slaney_provable ((A ioₛ C) <->ₛ (B ioₛ C))) ∧
          (slaney_provable ((C ioₛ A) <->ₛ (C ioₛ A))) ∧
          (slaney_provable ((A <->ₛ C) <->ₛ (B <->ₛ C))) ∧
          (slaney_provable ((C <->ₛ A) <->ₛ (C <->ₛ A))) ∧
          (slaney_provable (A) ⇔ slaney_provable (B))
Proof
  rpt strip_tac >> gs[s_DIMP_def]
  >- metis_tac[slaney_provable_rules]
  >- metis_tac [s_conjunction_r, s_conjunction_l, s_transitivity, s_modus_ponens, s_adjunction_rule, s_permutation, s_adjunction_rule]
  >- metis_tac[s_transitivity, s_modus_ponens, s_conjunction_r, s_conjunction_l, s_double_negation, s_contrapositive, s_adjunction_rule]
  >- metis_tac [s_conj_introduction, s_conjunction_r, s_conjunction_l, s_transitivity, s_modus_ponens, s_adjunction_rule, s_permutation, s_adjunction_rule]
  >- metis_tac [s_conj_introduction, s_conjunction_r, s_conjunction_l, s_transitivity, s_modus_ponens, s_adjunction_rule, s_permutation, s_adjunction_rule]
  >- metis_tac [s_conjunction_r, s_conjunction_l, s_transitivity, s_modus_ponens, s_adjunction_rule,
                s_adjunction_rule, s_disjunction_elim, s_disjunction_l, s_disjunction_r]
  >- metis_tac [s_conjunction_r, s_conjunction_l, s_transitivity, s_modus_ponens, s_adjunction_rule,
                s_adjunction_rule, s_disjunction_elim, s_disjunction_l, s_disjunction_r]
  >- metis_tac [s_conjunction_r, s_conjunction_l, s_transitivity, s_permutation, s_modus_ponens, s_adjunction_rule,
                s_adjunction_rule, s_intensional_conj_lr, s_intensional_conj_rl, s_identity]
  >- metis_tac [s_conjunction_r, s_conjunction_l, s_transitivity, s_permutation, s_modus_ponens, s_adjunction_rule,
                s_adjunction_rule, s_intensional_conj_lr, s_intensional_conj_rl, s_identity]
  >- (irule s_adjunction_rule >> rw[] >> irule s_conj_intro_rule >>
      metis_tac [s_conj_introduction, s_conjunction_r, s_conjunction_l, s_transitivity, s_modus_ponens, s_adjunction_rule, s_permutation, s_adjunction_rule]
     )
  >- (irule s_adjunction_rule >> rw[] >> irule s_conj_intro_rule >>
      metis_tac [s_conj_introduction, s_conjunction_r, s_conjunction_l, s_transitivity, s_modus_ponens, s_adjunction_rule, s_permutation, s_adjunction_rule]
     )
  >- metis_tac[slaney_provable_rules]
QED

Theorem s_double_negative_equiv:
  ∀A. slaney_provable (A <->ₛ ~ₛ (~ₛ A))
Proof
  metis_tac[s_DIMP_def, slaney_provable_rules]
QED

Theorem s_double_negative_implication_equiv:
 ∀A B. slaney_provable((A -->ₛ B) <->ₛ (A -->ₛ ~ₛ (~ₛ B)))
Proof
  rw[s_DIMP_def] >> irule s_adjunction_rule >> strip_tac
  >- (irule s_modus_ponens >> qexists_tac ‘B -->ₛ ~ₛ(~ₛ B)’ >> strip_tac
       >- metis_tac[s_DIMP_def, s_double_negative_equiv, slaney_provable_rules]
       >- metis_tac[slaney_provable_rules, s_permutation]
     )
  >- (irule s_modus_ponens >> qexists_tac ‘~ₛ(~ₛ B)-->ₛ B’ >> strip_tac
       >- metis_tac[s_DIMP_def, s_double_negative_equiv, slaney_provable_rules]
       >- metis_tac[slaney_provable_rules, s_permutation]
     )
QED


Theorem s_contrapositive_2:
  ∀A B. slaney_provable ((A -->ₛ B) <->ₛ (~ₛ B -->ₛ ~ₛ A))
Proof
  rw [s_DIMP_def] >> irule s_adjunction_rule >> strip_tac
  >- (assume_tac s_double_negative_implication_equiv >> last_x_assum $ qspecl_then [‘A’, ‘B’] strip_assume_tac >>
      gs[s_DIMP_def] >> assume_tac s_contrapositive >>
      last_x_assum $ qspecl_then [‘A’, ‘~ₛ B’] strip_assume_tac >>
       metis_tac[s_transitivity, s_conjunction_l, s_modus_ponens]
     )
  >- (assume_tac s_contrapositive >>
      last_x_assum $ qspecl_then [‘~ₛ B’, ‘A’] strip_assume_tac >>
      assume_tac s_double_negative_implication_equiv >> last_x_assum $ qspecl_then [‘A’, ‘B’] strip_assume_tac >>
      gs [s_DIMP_def] >> metis_tac[s_transitivity, s_conjunction_r, s_modus_ponens]
      )
QED

Theorem s_double_dimp_equiv:
  ∀A B C D. slaney_provable (A <->ₛ B) ∧ slaney_provable (C <->ₛ D) ⇒
          slaney_provable ((A -->ₛ C) <->ₛ (B -->ₛ D)) ∧
          slaney_provable ((A &ₛ C) <->ₛ (B &ₛ D)) ∧
          slaney_provable ((A Vₛ C) <->ₛ (B Vₛ D)) ∧
          slaney_provable ((A ioₛ C) <->ₛ (B ioₛ D))
Proof
  rpt strip_tac >> gs[s_DIMP_def] >> irule s_adjunction_rule
  >- metis_tac [s_modus_ponens, s_conjunction_l, s_conjunction_r, s_transitivity, s_prefixing, s_permutation]
  >- metis_tac [s_conj_introduction, s_transitivity, s_conjunction_r, s_conjunction_l, s_adjunction_rule, s_modus_ponens]
  >- metis_tac[s_disjunction_elim, s_disjunction_l, s_disjunction_r, s_transitivity, s_adjunction_rule, s_conjunction_l, s_conjunction_r, s_modus_ponens]
  >- metis_tac[s_modus_ponens, s_identity, s_conjunction_r, s_conjunction_l,  s_intensional_conj_rl,  s_intensional_conj_lr, s_transitivity]
QED

Theorem s_OR_definable:
  ∀A B. slaney_provable ((A Vₛ B) <->ₛ (~ₛ (~ₛ A &ₛ ~ₛ B)))
Proof
  rw[s_DIMP_def] >> irule s_adjunction_rule >> rw[]
  >- (irule s_modus_ponens >> qexists_tac ‘((A -->ₛ ~ₛ (~ₛ A &ₛ ~ₛ B)) &ₛ (B -->ₛ ~ₛ (~ₛ A &ₛ ~ₛ B)))’ >>
      assume_tac s_disjunction_elim >>
      last_x_assum $ qspecl_then [‘A’, ‘B’, ‘~ₛ (~ₛ A &ₛ ~ₛ B)’] strip_assume_tac >> rw[] >>
      irule s_adjunction_rule >>  metis_tac[slaney_provable_rules])
  >- (‘slaney_provable (~ₛ (~ₛ A &ₛ ~ₛ B) -->ₛ ~ₛ (~ₛ(A Vₛ B)))’ suffices_by
        metis_tac [s_double_negative_equiv, s_equiv_replacement] >>
      irule s_modus_ponens >> qexists_tac ‘~ₛ (A Vₛ B) -->ₛ ~ₛ (~ₛ(~ₛ A &ₛ ~ₛ B))’ >>
      simp[s_contrapositive] >>
      ‘slaney_provable (~ₛ (A Vₛ B) -->ₛ (~ₛ A &ₛ ~ₛ B))’ suffices_by
        metis_tac [s_double_negative_equiv, s_equiv_replacement] >>
      assume_tac s_conj_introduction >>
      last_x_assum $ qspecl_then [‘~ₛ (A Vₛ B)’, ‘~ₛ A’, ‘~ₛ B’] strip_assume_tac >>
      ‘slaney_provable (((~ₛ (A Vₛ B) -->ₛ ~ₛ A) &ₛ (~ₛ (A Vₛ B) -->ₛ ~ₛ B)))’ suffices_by
        metis_tac[s_modus_ponens] >>
      metis_tac[slaney_provable_rules, s_double_negative_equiv, s_equiv_replacement])
QED

Theorem s_IO_definable:
  ∀A B. slaney_provable ((A ioₛ B) <->ₛ (~ₛ (A -->ₛ ~ₛ B)))
Proof
  rw[s_DIMP_def] >> irule s_adjunction_rule >> rw[]
  >-(irule s_intensional_conj_rl >>
     metis_tac[s_assertion, s_contrapositive, s_transitivity, s_modus_ponens])
  >- (‘slaney_provable (A -->ₛ B -->ₛ (A ioₛ B))’ by metis_tac [slaney_provable_rules] >>
      metis_tac[s_contrapositive, s_contrapositive_2, s_equiv_replacement, s_permutation, s_modus_ponens])
QED


Theorem s_disjunction_OR_def:
  ∀A B C. slaney_provable (( A &ₛ ~ₛ (~ₛ B &ₛ ~ₛ C)) -->ₛ
                           ~ₛ(~ₛ ( A &ₛ B) &ₛ ~ₛ ( A &ₛ C)))
Proof
  rpt strip_tac >> assume_tac s_distribution >>
  last_x_assum $ qspecl_then [‘A’, ‘B’, ‘C’] strip_assume_tac >>
  ‘slaney_provable ((A &ₛ ~ₛ (~ₛ B &ₛ ~ₛ C)) -->ₛ ((A &ₛ B) Vₛ (A &ₛ C)))’ suffices_by metis_tac[s_OR_definable, s_equiv_replacement] >>
  ‘slaney_provable ((A &ₛ ~ₛ (~ₛ B &ₛ ~ₛ C)) <->ₛ (A &ₛ (B Vₛ C)))’ suffices_by metis_tac[s_equiv_replacement] >>
  rw [s_DIMP_def] >> irule s_adjunction_rule >> strip_tac
  >- (irule s_modus_ponens >> qexists_tac ‘((A &ₛ ~ₛ (~ₛ B &ₛ ~ₛ C)) -->ₛ A) &ₛ ((A &ₛ ~ₛ (~ₛ B &ₛ ~ₛ C)) -->ₛ (B Vₛ C))’ >>
      assume_tac s_conj_introduction >>
      last_x_assum $ qspecl_then [‘(A &ₛ ~ₛ (~ₛ B &ₛ ~ₛ C))’, ‘A’, ‘B Vₛ C’] strip_assume_tac >> rw[] >>
      irule s_adjunction_rule >> strip_tac >> metis_tac[slaney_provable_rules, s_OR_definable, s_equiv_replacement]
     )
  >- (irule s_modus_ponens >> qexists_tac ‘((A &ₛ (B Vₛ C)) -->ₛ A) &ₛ ((A &ₛ (B Vₛ C)) -->ₛ ~ₛ (~ₛ B &ₛ ~ₛ C))’ >>
      assume_tac s_conj_introduction >>
      last_x_assum $ qspecl_then [‘(A &ₛ (B Vₛ C))’, ‘A’, ‘~ₛ (~ₛ B &ₛ ~ₛ C)’] strip_assume_tac >> rw[] >>
      irule s_adjunction_rule >> strip_tac >> metis_tac[slaney_provable_rules, s_OR_definable, s_equiv_replacement]
     )
QED

val _ = export_theory();
