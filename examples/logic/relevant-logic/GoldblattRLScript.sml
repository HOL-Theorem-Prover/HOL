open HolKernel Parse boolLib bossLib stringTheory;

val _ = new_theory "GoldblattRL";

Datatype: g_prop = g_VAR string
          | g_IMP g_prop g_prop
          | g_AND g_prop g_prop
          | g_NOT g_prop
          | g_tt
End

val _ = set_fixity "-->ₐ" (Infixr 490);
val _ = overload_on ("-->ₐ", “g_IMP”);

val _ = set_fixity "&ₐ" (Infixl 600);
val _ = overload_on ("&ₐ", “g_AND”);

val _ = overload_on ("~ₐ", “g_NOT”);

val _ = overload_on ("τₐ", “g_tt”);

Definition g_OR_def:
  g_OR A B = ~ₐ(~ₐA &ₐ ~ₐB)
End

Definition g_DIMP_def:
  g_DIMP A B = (A -->ₐ B) &ₐ (B -->ₐ A)
End

Definition g_ICONJ_def:
  g_ICONJ A B = ~ₐ(A -->ₐ ~ₐB)
End


val _ = set_fixity "Vₐ" (Infixl 500);
val _ = overload_on ("Vₐ", “g_OR”);

val _ = set_fixity "<->ₐ" (Infix (NONASSOC, 491));
val _ = overload_on ("<->ₐ", “g_DIMP”);

val _ = set_fixity "ioₐ" (Infixl 600);
val _ = overload_on ("ioₐ", “g_ICONJ”);


Inductive goldblatt_provable:
[g_identity:] (∀A. goldblatt_provable (A -->ₐ A))
[g_suffixing:]
  (∀ A B C. goldblatt_provable ((A -->ₐ B) -->ₐ ((B -->ₐ C) -->ₐ (A -->ₐ C))))
[g_assertion:]
  (∀A B. goldblatt_provable (A -->ₐ ((A -->ₐ B) -->ₐ B)))
[g_contraction:]
  (∀A B. goldblatt_provable ((A -->ₐ (A -->ₐ B)) -->ₐ (A -->ₐ B)))
[g_conjunction_l:] (∀A B. goldblatt_provable((A &ₐ B) -->ₐ A))
[g_conjunction_r:] (∀A B. goldblatt_provable ((A &ₐ B) -->ₐ B))
[g_conj_introduction:]
  ∀A B C.
    goldblatt_provable (((A -->ₐ B) &ₐ (A -->ₐ C)) -->ₐ (A -->ₐ (B &ₐ C)))
[g_disjunction_l:] (∀A B. goldblatt_provable (A -->ₐ (A Vₐ B)))
[g_disjunction_r:] (∀A B. goldblatt_provable (B -->ₐ (A Vₐ B)))
[g_disjunction_elim:]
  ∀A B C.
    goldblatt_provable (((A -->ₐ C) &ₐ (B -->ₐ C)) -->ₐ ((A Vₐ B) -->ₐ C))
[g_distribution:]
  (∀A B C. goldblatt_provable ((A &ₐ (B Vₐ C)) -->ₐ ((A &ₐ B) Vₐ (A &ₐ C))))
[g_contrapositive:]
  ∀A B. goldblatt_provable ((A -->ₐ (~ₐB)) -->ₐ (B -->ₐ (~ₐA)))
[g_double_negation:] (∀A. goldblatt_provable ((~ₐ(~ₐA)) -->ₐ A ))
[g_adjunction_rule:]
  ∀A B. goldblatt_provable A ∧ goldblatt_provable B ⇒
        goldblatt_provable (A &ₐ B)
[g_modus_ponens:]
  ∀A B. goldblatt_provable A ∧ goldblatt_provable (A -->ₐ B) ⇒
        goldblatt_provable B
[g_tt_rl:] (∀A. goldblatt_provable A ⇒ goldblatt_provable (τₐ -->ₐ A))
[g_tt_lr:] (∀A. goldblatt_provable (τₐ -->ₐ A) ⇒ goldblatt_provable A)
End

Theorem g_permutation:
  ∀A B C. goldblatt_provable ((A -->ₐ (B -->ₐ C)) -->ₐ (B -->ₐ (A -->ₐ C)))
Proof
  metis_tac[g_suffixing, g_assertion, g_modus_ponens]
QED

Theorem g_double_neg:
  ∀A. goldblatt_provable (A -->ₐ ~ₐ (~ₐ A))
Proof
  metis_tac[g_DIMP_def, goldblatt_provable_rules]
QED

Theorem g_double_negative_equiv:
  ∀A. goldblatt_provable (A <->ₐ ~ₐ (~ₐ A))
Proof
  metis_tac[g_DIMP_def, g_double_negation, g_double_neg, g_adjunction_rule]
QED

Theorem g_double_negative_implication_equiv:
 ∀A B. goldblatt_provable((A -->ₐ B) <->ₐ (A -->ₐ ~ₐ (~ₐ B)))
Proof
  metis_tac [g_permutation, goldblatt_provable_rules, g_DIMP_def, g_double_negative_equiv]
QED

Theorem g_conj_intro_rule:
  ∀A B C. goldblatt_provable (A -->ₐ B) ∧
          goldblatt_provable (A -->ₐ C) ⇒
          goldblatt_provable (A -->ₐ (B &ₐ C))
Proof
  metis_tac[goldblatt_provable_rules]
QED

Theorem g_equiv_replacement:
  ∀A B C. goldblatt_provable (A <->ₐ B) ⇒
          (goldblatt_provable ((A -->ₐ C) <->ₐ (B -->ₐ C))) ∧
          (goldblatt_provable ((C -->ₐ A) <->ₐ (C -->ₐ B))) ∧
          (goldblatt_provable ((A &ₐ C) <->ₐ (B &ₐ C))) ∧
          (goldblatt_provable ((C &ₐ A) <->ₐ (C &ₐ B))) ∧
          (goldblatt_provable ((~ₐ A) <->ₐ ~ₐ B)) ∧
          (goldblatt_provable ((A <->ₐ C) <->ₐ (B <->ₐ C))) ∧
          (goldblatt_provable ((C <->ₐ A) <->ₐ (C <->ₐ B))) ∧
          (goldblatt_provable A ⇔ goldblatt_provable B)
Proof
  rw[]
  >- metis_tac[goldblatt_provable_rules, g_permutation, g_DIMP_def]
  >- metis_tac[goldblatt_provable_rules, g_permutation, g_DIMP_def]
  >- metis_tac[goldblatt_provable_rules, g_permutation, g_DIMP_def]
  >- metis_tac[goldblatt_provable_rules, g_permutation, g_DIMP_def]
  >- metis_tac[goldblatt_provable_rules, g_permutation, g_DIMP_def]
  >- (gs[g_DIMP_def] >> irule g_adjunction_rule >> rw[] >>
      irule g_conj_intro_rule >>
      metis_tac[goldblatt_provable_rules, g_permutation])
  >- (gs[g_DIMP_def] >> irule g_adjunction_rule >> rw[] >>
      irule g_conj_intro_rule >>
      metis_tac[goldblatt_provable_rules, g_permutation])
 >- metis_tac[goldblatt_provable_rules, g_permutation, g_DIMP_def]
QED


Theorem g_contrapositive_alt:
 ∀ A B. goldblatt_provable ((A -->ₐ B) <->ₐ (~ₐ B -->ₐ ~ₐ A))
Proof
  rw [g_DIMP_def] >> irule g_adjunction_rule >> strip_tac
  >- metis_tac[g_DIMP_def, g_double_negative_implication_equiv, g_suffixing,
                g_conjunction_l, g_modus_ponens, g_contrapositive]
  >- metis_tac[g_DIMP_def, g_double_negative_implication_equiv, g_suffixing,
                g_conjunction_r, g_modus_ponens, g_contrapositive]
QED

Theorem g_io_rule:
  ∀A B C. goldblatt_provable ((A ioₐ B) -->ₐ C) ⇔ goldblatt_provable (A -->ₐ (B -->ₐ C))
Proof
  rw[g_ICONJ_def, EQ_IMP_THM]
  >- (‘goldblatt_provable (~ₐ C -->ₐ (A -->ₐ ~ₐB))’ suffices_by
        metis_tac[g_permutation, g_modus_ponens, g_contrapositive_alt, g_equiv_replacement] >>
     metis_tac [g_equiv_replacement, g_contrapositive_alt, g_DIMP_def, goldblatt_provable_rules])
  >- (‘goldblatt_provable (~ₐ C -->ₐ (A -->ₐ ~ₐB))’ suffices_by
        metis_tac [g_equiv_replacement, g_contrapositive_alt, g_DIMP_def, goldblatt_provable_rules] >>
      metis_tac[g_permutation, g_modus_ponens, g_contrapositive_alt, g_equiv_replacement])
QED

val _ = export_theory();
