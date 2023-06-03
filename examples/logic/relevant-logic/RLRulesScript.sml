open HolKernel Parse boolLib bossLib stringTheory;

open GoldblattRLTheory;

val _ = new_theory "RLRules";

val _ = set_fixity "-->" (Infixr 490);
val _ = overload_on ("-->", “g_IMP”);

val _ = set_fixity "&" (Infixl 600);
val _ = overload_on ("&", “g_AND”);

val _ = overload_on ("~", “g_NOT”);

val _ = overload_on ("τ", “g_tt”);

val _ = set_fixity "V" (Infixl 500);
val _ = overload_on ("V", “g_OR”);

val _ = set_fixity "<->" (Infix (NONASSOC, 491));
val _ = overload_on ("<->", “g_DIMP”);

val _ = set_fixity "∘ᵣ" (Infixl 49600);
val _ = overload_on ("∘ᵣ", “g_ICONJ”);

val _ = overload_on ("|-", “goldblatt_provable”);


Theorem g_io_commutative:
  ∀A B. |- ((A ∘ᵣ B) <-> (B ∘ᵣ A))
Proof
  rpt strip_tac >> rw[g_ICONJ_def, g_DIMP_def] >>
  irule g_adjunction_rule >> rw[] >>
  metis_tac [g_contrapositive_alt, g_equiv_replacement, goldblatt_provable_rules]
QED

Theorem g_io_commutative_lr:
  ∀A B. |- ((A ∘ᵣ B) --> (B ∘ᵣ A))
Proof
  metis_tac[goldblatt_provable_rules, g_io_commutative, g_DIMP_def]
QED

Theorem g_strong_equiv_replacement:
  ∀A B C. |- (A <-> B) ⇒
          |- ((A --> C) <-> (B --> C)) ∧
          |- ((C --> A) <-> (C --> B)) ∧
          |- (~A <-> ~B) ∧
          |- ((A & C) <-> (B & C)) ∧
          |- ((C & A) <-> (C & B))
Proof
  rw[g_DIMP_def] >> irule g_adjunction_rule >> rw[]
  >- metis_tac[g_modus_ponens, g_conjunction_r, g_conjunction_l, g_suffixing,
               g_permutation, g_contrapositive_alt, g_DIMP_def]
  >- metis_tac[g_modus_ponens, g_conjunction_r, g_conjunction_l, g_suffixing,
               g_permutation, g_contrapositive_alt, g_DIMP_def]
  >- metis_tac[g_modus_ponens, g_conjunction_r, g_conjunction_l, g_suffixing,
               g_permutation, g_contrapositive_alt, g_DIMP_def]
  >- metis_tac[g_modus_ponens, g_conjunction_r, g_conjunction_l, g_suffixing,
               g_permutation, g_contrapositive_alt, g_DIMP_def]
  >- metis_tac[g_modus_ponens, g_conjunction_r, g_conjunction_l, g_suffixing,
               g_permutation, g_contrapositive_alt, g_DIMP_def]
  >- metis_tac[g_modus_ponens, g_conjunction_r, g_conjunction_l, g_suffixing,
               g_permutation, g_contrapositive_alt, g_DIMP_def]
  >> metis_tac[g_conj_introduction, g_conjunction_l, g_conjunction_r, g_adjunction_rule, g_modus_ponens, g_suffixing]
QED

Theorem g_equiv_commutative:
  ∀ A B. |- (A <-> B) ⇔ |- (B <-> A)
Proof
  rw[g_DIMP_def] >> metis_tac[goldblatt_provable_rules]
QED

Theorem g_equiv_associaive:
  ∀ A B C. |- (A <-> B) ∧ |- (B <-> C) ⇒ |- (A <-> C)
Proof
  rw[g_DIMP_def] >> metis_tac[g_conjunction_r, g_conjunction_l, g_suffixing, g_modus_ponens, g_adjunction_rule]
QED

Theorem g_equiv_AND:
  ∀A B C D. |- (A <-> B) ∧ |- (C <-> D) ⇒
            |- ((A & C) <-> (B & D))
Proof
  rw[g_DIMP_def] >> irule g_adjunction_rule >> rw[] >>
  metis_tac[g_conj_introduction, g_conjunction_l, g_conjunction_r, g_adjunction_rule, g_modus_ponens, g_suffixing]
QED

Theorem g_strong_io_rule:
  ∀A B C. |- (((A ∘ᵣ B) --> C ) <-> (A --> B --> C))
Proof
  rw[g_ICONJ_def] >>
  ‘|- ((~(A --> ~B) --> C) <-> (~C --> ~~(A --> ~B)))’ by
    metis_tac[g_contrapositive_alt, g_strong_equiv_replacement] >>
  ‘|- ((~C --> ~~(A --> ~B)) <-> (~C --> (A --> ~B)))’ by
    metis_tac[g_double_negative_equiv, g_strong_equiv_replacement, g_equiv_commutative] >>
  ‘|-((~C --> (A --> ~B)) <-> (A --> ~C --> ~B))’ by (
    rw[g_DIMP_def] >> irule g_adjunction_rule >>
    metis_tac[g_permutation, goldblatt_provable_rules]
    ) >>
  ‘|- ((A --> ~C --> ~B) <-> (A --> B --> C))’ by
    metis_tac[g_contrapositive_alt, g_strong_equiv_replacement, g_equiv_commutative] >>
   metis_tac[g_equiv_associaive]
QED

Theorem g_io_associative:
 ∀A B C. |- ((A ∘ᵣ (B ∘ᵣ C)) <-> ((A ∘ᵣ B) ∘ᵣ C))
Proof
  rw[g_ICONJ_def] >>
  ‘|- ((B --> ~C) <-> ~~(B --> ~C))’ by
     metis_tac[g_double_negative_equiv] >>
  ‘|- (~(A --> ~~(B --> ~C)) <-> ~(A --> (B --> ~C)))’ by
      metis_tac[g_equiv_replacement, g_strong_equiv_replacement] >>
  ‘|- (~(A --> B --> ~C) <-> ~((A ∘ᵣ B) --> ~C))’ suffices_by
    metis_tac[g_equiv_replacement, g_strong_equiv_replacement, g_ICONJ_def] >>
  metis_tac[g_strong_io_rule, g_equiv_commutative, g_strong_equiv_replacement]
QED

Theorem g_io_associative_rl:
 ∀A B C. |- ((A ∘ᵣ (B ∘ᵣ C)) --> ((A ∘ᵣ B) ∘ᵣ C))
Proof
  metis_tac[g_io_associative, g_DIMP_def, goldblatt_provable_rules]
QED

Theorem g_AND_commutative:
  ∀A B. goldblatt_provable ((A &ₐ B) <->ₐ B &ₐ A)
Proof
  metis_tac[g_DIMP_def, goldblatt_provable_rules]
QED

Theorem g_AND_associative_lr:
  ∀A B C. |- ((A & (B & C)) --> ((A & B) & C))
Proof
  rpt strip_tac >>
  ‘|- ((A & (B & C)) --> A)’ by metis_tac[goldblatt_provable_rules] >>
  ‘|- ((A & (B & C)) --> B)’ by metis_tac[goldblatt_provable_rules] >>
  ‘|- ((A & (B & C)) --> C)’ by metis_tac[goldblatt_provable_rules] >>
  ‘|- ((A & (B & C)) --> (A & B))’ by metis_tac[goldblatt_provable_rules] >>
  metis_tac[goldblatt_provable_rules]
QED

Theorem g_AND_associative_rl:
  ∀A B C. |- (((A & B) & C) --> (A & (B & C)))
Proof
  rpt strip_tac >> metis_tac[goldblatt_provable_rules]
QED

Theorem g_distribution_equiv:
  ∀A B C. |- (((A & B) V (A & C)) <-> (A & (B V C)))
Proof
  rw [g_DIMP_def] >> irule g_adjunction_rule >> rw[]
  >- (‘|- ((A & B) --> (A & (B V C)))’ by (
       ‘|- ((A & B) --> B V C)’ by
          metis_tac[g_suffixing, g_disjunction_l, g_conjunction_r, g_modus_ponens] >>
       ‘|- ((A & B) --> A)’ by metis_tac[goldblatt_provable_rules] >>
       metis_tac[g_adjunction_rule,  g_conj_introduction, g_modus_ponens]
       ) >>
      ‘|- ((A & C) --> (A & (B V C)))’ by (
        ‘|- ((A & C) --> B V C)’ by
           metis_tac[g_suffixing, g_disjunction_r, g_conjunction_r, g_modus_ponens] >>
        ‘|- ((A & C) --> A)’ by metis_tac[goldblatt_provable_rules] >>
        metis_tac[g_adjunction_rule,  g_conj_introduction, g_modus_ponens]
        ) >>
      metis_tac [g_disjunction_elim, g_adjunction_rule, g_modus_ponens])
  >- metis_tac[goldblatt_provable_rules]
QED

Theorem g_conj_elim_l:
  ∀A B C. |- ((A --> (B & C)) --> A --> B)
Proof
  metis_tac[g_suffixing, g_permutation, g_conjunction_l, g_modus_ponens]
QED

Theorem g_conj_elim_r:
  ∀A B C. |- ((A --> (B & C)) --> A --> C)
Proof
  metis_tac[g_suffixing, g_permutation, g_conjunction_r, g_modus_ponens]
QED

Theorem yeet_lemma:
  ∀A B C. |- (B --> C) ⇒ |- ((A ∘ᵣ B) --> (A ∘ᵣ C))
Proof
  rpt strip_tac >> simp [g_io_rule] >> simp[g_ICONJ_def] >>
  assume_tac g_suffixing >>
  last_x_assum $ qspecl_then [‘A’, ‘~C’, ‘~B’] strip_assume_tac >>
  ‘|- ((A --> ~C) --> (A --> ~B))’ by
    metis_tac[g_modus_ponens, g_permutation, g_contrapositive_alt, g_equiv_replacement] >>
  metis_tac[g_permutation, g_contrapositive, g_suffixing, g_modus_ponens]
QED

Theorem yeet:
  ∀A B C D. |- (A --> C) ∧ |- (B --> D) ⇒ |- ((A ∘ᵣ B) --> C ∘ᵣ D)
Proof
  rpt strip_tac >>
  ‘|- ((A ∘ᵣ B) --> A ∘ᵣ D)’ by metis_tac [yeet_lemma] >>
  ‘|- ((A ∘ᵣ D) --> C ∘ᵣ D)’ by metis_tac[yeet_lemma, g_io_commutative, g_equiv_replacement] >>
  metis_tac[goldblatt_provable_rules]
QED

Theorem g_io_distribution_equiv:
  ∀A B C. |- ((A ∘ᵣ (B V C)) <-> ((A ∘ᵣ B) V (A ∘ᵣ C)))
Proof
  rw[g_DIMP_def] >> irule g_adjunction_rule >> rw[g_ICONJ_def, g_OR_def] >>
  ‘|- (( A --> ~~(~B & ~C)) <-> (A --> (~B & ~C)))’ by
    metis_tac[g_double_negative_implication_equiv, g_equiv_replacement] >>
  ‘|- ((~~(A --> ~B) & ~~(A --> ~C)) <->  ((A --> ~B) & (A --> ~C)))’ by (
    simp[g_DIMP_def] >> irule g_adjunction_rule >> rw[]
    >- (‘|- ((~~(A --> ~B) & ~~(A --> ~C)) --> (A --> ~B))’
          by metis_tac[g_conjunction_l, g_equiv_replacement, g_double_negative_equiv] >>
        ‘|- ((~~(A --> ~B) & ~~(A --> ~C)) --> (A --> ~C))’
          by metis_tac[g_conjunction_r, g_equiv_replacement, g_double_negative_equiv] >>
        metis_tac[goldblatt_provable_rules]
       )
    >-(‘|- (((A --> ~B) & (A --> ~C)) --> ~~(A --> ~B))’
         by metis_tac[g_conjunction_l, g_equiv_replacement, g_double_negative_equiv] >>
       ‘|- (((A --> ~B) & (A --> ~C)) --> ~~(A --> ~C))’
         by metis_tac[g_conjunction_r, g_equiv_replacement, g_double_negative_equiv] >>
       metis_tac[goldblatt_provable_rules]
      )
    )
  >- (‘|- ((~~(A --> ~B) & ~~(A --> ~C)) --> (A --> ~~(~B & ~C)))’
        suffices_by metis_tac[g_contrapositive_alt, g_equiv_replacement] >>
      ‘ |- (((A --> ~B) & (A --> ~C)) --> A --> (~B & ~C))’ suffices_by
        metis_tac[g_equiv_replacement] >>
      metis_tac[goldblatt_provable_rules]
     )
  >- (‘|- ((A --> ~~(~B & ~C)) --> (~~(A --> ~B) & ~~(A --> ~C)))’
        suffices_by metis_tac[g_contrapositive_alt, g_equiv_replacement] >>
      ‘|- ((A --> (~B & ~C)) --> ((A --> ~B) & (A --> ~C)))’ suffices_by
        metis_tac[g_equiv_replacement] >>
      ‘|- ((A --> ~B & ~C) --> (A --> ~B))’ by metis_tac[g_conj_elim_l] >>
      ‘|- ((A --> ~B & ~C) --> (A --> ~C))’ by metis_tac[g_conj_elim_r] >>
      metis_tac[goldblatt_provable_rules]
     )
QED

Theorem  g_io_distribution_lr:
  ∀A B C. |- ((A ∘ᵣ (B V C)) --> ((A ∘ᵣ B) V (A ∘ᵣ C)))
Proof
  metis_tac[goldblatt_provable_rules, g_DIMP_def, g_io_distribution_equiv]
QED

Theorem g_io_true:
  ∀A. |- ((τ ∘ᵣ A) <-> A)
Proof
  rw[g_DIMP_def] >> irule g_adjunction_rule >> rw[]
  >- metis_tac[g_io_rule, goldblatt_provable_rules]
  >- (simp[g_ICONJ_def] >> metis_tac[goldblatt_provable_rules])
QED

Theorem g_anti_truth_imp:
  ∀A. |- (A --> ~τ) ⇔ |- (~A)
Proof
  metis_tac[goldblatt_provable_rules]
QED

Theorem g_io_imp:
  ∀A. |- (A --> (A ∘ᵣ A))
Proof
  rw[g_ICONJ_def] >>
  ‘|- (A --> (A --> ~A) --> ~A)’ by
    metis_tac[goldblatt_provable_rules] >>
  ‘|- (A --> A --> ~(A --> ~A))’ by
    metis_tac[g_modus_ponens, g_contrapositive, g_suffixing] >>
  metis_tac[goldblatt_provable_rules]
QED

Theorem g_reductio:
  ∀A. |-((A --> ~A) --> ~A)
Proof
  metis_tac[g_ICONJ_def, g_modus_ponens, g_contrapositive, g_io_imp]
QED

Theorem g_AND_MP:
  ∀A B. |- ((A & (A --> B)) --> B)
Proof
  rpt strip_tac >>
  ‘|- ((A & (A --> B)) --> A)’ by simp[g_conjunction_l] >>
  ‘|- ((A & (A --> B)) --> (A --> B))’ by simp[g_conjunction_r] >>
  ‘|- ((A & (A --> B)) --> (A & (A --> B)) --> B)’ by
    metis_tac[g_suffixing, g_modus_ponens, g_permutation] >>
  metis_tac[g_modus_ponens, g_contraction]
QED

Theorem g_AND_STRENGTHEN:
  ∀A B C. |- ((A --> C) --> ((A & B) --> C)) ∧
          |- ((B --> C) --> ((A & B) --> C))
Proof
  metis_tac[goldblatt_provable_rules]
QED

Theorem g_imp_conj_introduction:
  ∀ A B C D. |-  (A --> B --> C) ∧ |-  (A --> B --> D) ⇒
             |- (A --> B --> (C & D))
Proof
  rpt strip_tac >>
  ‘|- ((A ∘ᵣ B) --> C)’ by metis_tac[g_io_rule] >>
  ‘|- ((A ∘ᵣ B) --> D)’  by metis_tac[g_io_rule] >>
  ‘|- ((A ∘ᵣ B) --> C & D)’  suffices_by metis_tac[g_io_rule] >>
  metis_tac[goldblatt_provable_rules]
QED

val _ = export_theory();
