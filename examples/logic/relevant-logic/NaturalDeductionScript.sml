open HolKernel Parse boolLib bossLib stringTheory;

open GoldblattRLTheory RLRulesTheory;

val _ = new_theory "NaturalDeduction";

val _ = set_fixity "-->" (Infixr 490);
val _ = overload_on ("-->", “g_IMP”);

val _ = set_fixity "&" (Infixl 600);
val _ = overload_on ("&", “g_AND”);

val _ = overload_on ("~", “g_NOT”);

val _ = overload_on ("τ", “g_tt”);

val _ = set_fixity "V" (Infixl 500);
val _ = overload_on ("V", “g_OR”);

val _ = set_fixity "<->" (Infixr 490);
val _ = overload_on ("<->", “g_DIMP”);

val _ = set_fixity "∘ᵣ" (Infixl 600);
val _ = overload_on ("∘ᵣ", “g_ICONJ”);

Datatype: Bunch = PROP g_prop
          | COMMA Bunch Bunch
          | SEMICOLON Bunch Bunch
End

val _ = set_fixity "，" (Infixr 490);
Overload "，" = “λp q. COMMA (PROP p) (PROP q)”
Overload "，" = “λp q. COMMA p (PROP q)”
Overload "，" = “λp q. COMMA (PROP p) q”
Overload "，" = “COMMA”

val _ = set_fixity "；" (Infixr 490);

Overload "；" = “λp q. SEMICOLON (PROP p) (PROP q)”
Overload "；" = “λp q. SEMICOLON p (PROP q)”
Overload "；" = “λp q. SEMICOLON (PROP p) q”
Overload "；" = “SEMICOLON”

Datatype: B_Context = HOLE
          | LCOMMA B_Context Bunch
          | RCOMMA Bunch B_Context
          | LSEMI B_Context Bunch
          | RSEMI Bunch B_Context
End

Definition REPLACE_def:
  (REPLACE HOLE X = X) ∧
  (REPLACE (LCOMMA Γ b) X = COMMA (REPLACE Γ X) b) ∧
  (REPLACE (RCOMMA b Γ) X = COMMA b (REPLACE Γ X)) ∧
  (REPLACE (LSEMI Γ b) X  = SEMICOLON (REPLACE Γ X) b) ∧
  (REPLACE (RSEMI b Γ) X  = SEMICOLON b (REPLACE Γ X))
End

val _ = overload_on ("，", “RCOMMA”);
val _ = overload_on ("，", “LCOMMA”);

val _ = overload_on ("；", “RSEMI”);
val _ = overload_on ("；", “LSEMI”);

Inductive R_sequent:
(* Classical Rules *)
[Assumption:] (∀A. R_sequent (PROP A) A)
[AND_Elimination_l:] (∀X A B. R_sequent X (A & B) ⇒ R_sequent X A)
[AND_Elimination_r:] (∀X A B. R_sequent X (A & B) ⇒ R_sequent X B)
[OR_Introduction_l:] (∀X A B. R_sequent X A ⇒ R_sequent X (A V B))
[OR_Introduction_r:] (∀X A B. R_sequent X B ⇒ R_sequent X (A V B))
[NOT_NOT_Introduction:] (∀X A. R_sequent X A ⇒ R_sequent X (~~A))
[NOT_NOT_Elimination:] (∀X A. R_sequent X (~~A) ⇒ R_sequent X A)

(* Non-Classical Rules *)
[AND_Introduction:]
  ∀X Y A B. (R_sequent X A ∧ R_sequent Y B ⇒ R_sequent (X， Y) (A & B))
[IMP_Introduction:]
  ∀X A B. R_sequent (X ； (PROP A)) B ⇒ R_sequent X (A --> B)
[IMP_Elimination:]
  ∀X Y A B. R_sequent X (A --> B) ∧ R_sequent Y A ⇒ R_sequent (X ； Y) B
[RAA:]
  ∀X Y A B. R_sequent (X ； (PROP A)) B ∧ R_sequent Y (~B) ⇒
            R_sequent (X ； Y) (~A)
[OR_Elimination:]
  ∀Γ X A B C. R_sequent X (A V B) ∧ R_sequent(REPLACE Γ (PROP  A)) C ∧
              R_sequent (REPLACE Γ (PROP  B)) C
              ⇒
              R_sequent (REPLACE Γ X) C
(* Structural Rules *)
[COMMA_commutative:]
  (∀Γ X Y A. R_sequent (REPLACE Γ (X ， Y)) A ⇒ R_sequent (REPLACE Γ (Y ， X)) A)
[COMMA_associative_lr:]
  (∀Γ X Y Z A. R_sequent (REPLACE Γ ((X ， Y) ， Z)) A ⇒
               R_sequent (REPLACE Γ (X ， (Y ， Z))) A)
[COMMA_associative_rl:]
  (∀Γ X Y Z A. R_sequent (REPLACE Γ (X ， (Y ， Z))) A ⇒ R_sequent (REPLACE Γ ((X ， Y) ， Z)) A) (* delete*)
[COMMA_idempotent_lr:]
  (∀Γ X A. R_sequent (REPLACE Γ (X ， X)) A ⇒ R_sequent (REPLACE Γ X) A)
[COMMA_idempotent_rl:]
  (∀Γ X A. R_sequent (REPLACE Γ X) A ⇒ R_sequent (REPLACE Γ (X ， X)) A)
[weakening:]
  (∀Γ X Y A. R_sequent (REPLACE Γ X) A ⇒ R_sequent (REPLACE Γ (X ， Y)) A)
[identity_lr:]
  (∀Γ X A. R_sequent (REPLACE Γ ((PROP τ) ； X) ) A ⇒ R_sequent (REPLACE Γ X) A)
[identity_rl:]
  (∀Γ X A. R_sequent (REPLACE Γ X) A ⇒ R_sequent (REPLACE Γ ((PROP τ) ； X) ) A)
(* system R *)
[SEMICOLON_commutative:]
  (∀Γ X Y A. R_sequent (REPLACE Γ (X ； Y)) A ⇒ R_sequent (REPLACE Γ (Y；X)) A)
[SEMICOLON_associative_lr:]
  (∀Γ X Y Z A. R_sequent (REPLACE Γ ((X ； Y) ； Z)) A ⇒
               R_sequent (REPLACE Γ (X ； (Y ； Z))) A)
[SEMICOLON_idempotent_lr:]
  (∀Γ X A. R_sequent (REPLACE Γ (X ； X)) A ⇒ R_sequent (REPLACE Γ X) A)
End

val _ = overload_on ("|-", “goldblatt_provable”);

val _ = set_fixity "||-" (Infixr 460);
val _ = overload_on ("||-", “R_sequent”);

Theorem SEMICOLON_associative_rl:
  ∀Γ X Y Z A. R_sequent (REPLACE Γ (X； (Y； Z))) A ⇒ R_sequent (REPLACE Γ ((X； Y)； Z)) A
Proof
  metis_tac [SEMICOLON_associative_lr, SEMICOLON_commutative]
QED

Theorem R_Contrapositive:
  ∀ A B. (PROP (A-->B)) ||- (~B --> ~A)
Proof
  metis_tac[RAA, IMP_Elimination, IMP_Introduction, Assumption]
QED

Theorem AND_Elimination_l_alt:
  ∀A B. R_sequent (PROP (A & B)) A
Proof
   metis_tac[R_sequent_rules]
QED

Theorem AND_Elimination_r_alt:
  ∀A B. R_sequent (PROP (A & B)) B
Proof
  metis_tac[R_sequent_rules]
QED

Theorem OR_Introduction_l_alt:
  ∀A B. R_sequent (PROP A) (A V B)
Proof
  metis_tac[R_sequent_rules]
QED

Theorem OR_Introduction_r_alt:
  ∀A B. R_sequent (PROP B) (A V B)
Proof
  metis_tac[R_sequent_rules]
QED

Theorem NOT_NOT_Introduction_alt:
  ∀A. R_sequent (PROP A) (~~A)
Proof
  metis_tac[R_sequent_rules]
QED

Theorem NOT_NOT_Elimination_alt:
  ∀A. R_sequent (PROP (~~A)) (A)
Proof
  metis_tac[R_sequent_rules]
QED

Theorem hilbert_to_natural_deduction:
  ∀A. |- A
      ⇒ (PROP  τ) ||- A
Proof
  Induct_on ‘|-’ >> rpt strip_tac
  >- metis_tac [Assumption, identity_rl, IMP_Introduction, REPLACE_def]
  >- (‘(((PROP (A --> B)) ； (PROP (B --> C))) ； PROP A) ||- C’ suffices_by
        metis_tac [identity_rl, IMP_Introduction, REPLACE_def] >>
      assume_tac Assumption >>
      last_assum $ qspec_then ‘A --> B’ strip_assume_tac >>
      last_assum $ qspec_then ‘B --> C’ strip_assume_tac >>
      last_x_assum $ qspec_then ‘A’ strip_assume_tac >>
      ‘(PROP (A-->B) ； PROP A) ||- B’ by metis_tac[IMP_Elimination] >>
      ‘(PROP (B --> C) ； PROP (A-->B) ； PROP A) ||- C’ by metis_tac[IMP_Elimination] >>
      assume_tac SEMICOLON_associative_rl >>
      last_x_assum $ qspecl_then [‘HOLE’,‘PROP  (B --> C)’, ‘PROP  (A --> B)’,
                                  ‘PROP A’, ‘C’] strip_assume_tac >>
      gs[REPLACE_def] >>
      assume_tac SEMICOLON_commutative >>
      last_x_assum $ qspecl_then [‘LSEMI HOLE (PROP A)’,‘PROP  (B --> C)’, ‘PROP  (A --> B)’, ‘C’] strip_assume_tac >>
      gs[REPLACE_def]
     )
  >- (‘((PROP  A) ； (PROP (A-->B))) ||- B’ suffices_by
        metis_tac [identity_rl, IMP_Introduction, REPLACE_def] >>
      assume_tac Assumption >>
      last_assum $ qspec_then ‘A --> B’ strip_assume_tac >>
      last_x_assum $ qspec_then ‘A’ strip_assume_tac >>
      assume_tac SEMICOLON_commutative >>
      last_x_assum $ qspecl_then [‘HOLE’,‘PROP  (A --> B)’, ‘PROP A’, ‘B’] strip_assume_tac >>
      metis_tac [REPLACE_def, IMP_Elimination]
     )
  >- (‘(PROP (A-->A-->B) ； PROP A) ||- B ’ suffices_by
        metis_tac [identity_rl, IMP_Introduction, REPLACE_def] >>
      ‘((PROP (A-->A-->B) ； PROP A) ； PROP A)  ||- B ’ by
        metis_tac [Assumption, IMP_Elimination] >>
      metis_tac [REPLACE_def, SEMICOLON_associative_lr, SEMICOLON_idempotent_lr]
     )
  >- metis_tac[AND_Elimination_l_alt, Assumption, IMP_Introduction, identity_rl, REPLACE_def]
  >- metis_tac[AND_Elimination_r_alt, Assumption, IMP_Introduction, identity_rl, REPLACE_def]
  >- (‘(PROP  ((A --> B) & (A --> C)) ； PROP A) ||- (B & C)’ suffices_by
        metis_tac [identity_rl, IMP_Introduction, REPLACE_def] >>
      ‘(PROP  ((A --> B) & (A --> C)) ； PROP A) ||- B’ by
        metis_tac[IMP_Elimination, Assumption, AND_Elimination_l_alt] >>
      ‘(PROP  ((A --> B) & (A --> C)) ； PROP A) ||- C’ by
        metis_tac[IMP_Elimination, Assumption, AND_Elimination_r_alt] >>
      metis_tac[AND_Introduction, COMMA_idempotent_lr, REPLACE_def]
     )
  >- metis_tac[OR_Introduction_l_alt, Assumption, IMP_Introduction, identity_rl, REPLACE_def]
  >- metis_tac[OR_Introduction_r_alt, Assumption, IMP_Introduction, identity_rl, REPLACE_def]
  >- (‘(PROP  ((A --> C) & (B --> C)) ； PROP (A V B)) ||- C’ suffices_by
        metis_tac [identity_rl, IMP_Introduction, REPLACE_def] >>
      ‘(PROP  ((A --> C) & (B --> C)) ； PROP A) ||- C’ by
        metis_tac[IMP_Elimination, Assumption, AND_Elimination_l_alt] >>
      ‘(PROP  ((A --> C) & (B --> C)) ； PROP B) ||- C’ by
        metis_tac[IMP_Elimination, Assumption, AND_Elimination_r_alt] >>
      assume_tac OR_Elimination >>
      last_x_assum $ qspecl_then [‘RSEMI (PROP  ((A --> C) & (B --> C))) HOLE’,
                                  ‘PROP  (A V B)’, ‘A’, ‘B’, ‘C’] strip_assume_tac >>
      metis_tac [Assumption, REPLACE_def]
     )
  >- (‘(PROP  (A & (B V C))) ||- ((A & B) V (A & C))’ suffices_by
        metis_tac [identity_rl, IMP_Introduction, REPLACE_def] >>
      ‘(PROP  (A & (B V C))) ||- A’ by metis_tac[Assumption, AND_Elimination_l_alt] >>
      ‘(PROP  (A & (B V C))) ||- (B V C)’ by metis_tac[Assumption, AND_Elimination_r_alt] >>
      ‘(PROP  (A & (B V C)) ， PROP B ) ||- ((A & B) V (A & C))’ by
        metis_tac [Assumption, AND_Introduction, OR_Introduction_l, OR_Introduction_r] >>
      ‘(PROP  (A & (B V C)) ， PROP C ) ||- ((A & B) V (A & C))’ by
        metis_tac [Assumption, AND_Introduction,  OR_Introduction_l, OR_Introduction_r] >>
      assume_tac OR_Elimination >>
      last_x_assum $ qspecl_then [‘RCOMMA (PROP (A & (B V C))) HOLE’,
                                  ‘PROP (A & (B V C))’, ‘B’, ‘C’,
                                  ‘((A & B) V (A & C))’] strip_assume_tac >>
      metis_tac [COMMA_idempotent_lr, REPLACE_def]
     )
  >- (‘((PROP (A --> ~B)) ； PROP (B)) ||- (~A)’ suffices_by
        metis_tac [identity_rl, IMP_Introduction, REPLACE_def] >>
      irule RAA >> metis_tac [NOT_NOT_Introduction_alt, Assumption, IMP_Elimination]
     )
  >- metis_tac [identity_rl, IMP_Introduction, REPLACE_def, NOT_NOT_Elimination_alt]
  >- metis_tac[AND_Introduction, REPLACE_def, COMMA_idempotent_lr]
  >- metis_tac[IMP_Elimination, identity_lr, REPLACE_def]
  >- metis_tac[IMP_Introduction, identity_rl, REPLACE_def]
  >- metis_tac[Assumption, IMP_Elimination, identity_lr, REPLACE_def]
QED

Definition bg_translation_def[simp]:
  (bg_translation (PROP A) = A) ∧
  (bg_translation (X ， Y) = (bg_translation X) & (bg_translation Y)) ∧
  (bg_translation (X； Y) = (bg_translation X) ∘ᵣ (bg_translation Y))
End

val _ = overload_on ("bg", “bg_translation”);

Theorem g_id[simp] = g_identity;

Theorem g_suffixing_rule:
  |- (A --> B) ∧ |- (B --> C) ⇒ |- (A --> C)
Proof
  metis_tac[goldblatt_provable_rules]
QED

Theorem OR_Bunch_rule:
  |- (bg (REPLACE Γ (PROP (A V B))) --> (bg (REPLACE Γ (PROP A)) V bg (REPLACE Γ (PROP B))))
Proof
  Induct_on ‘Γ’ >> gs[REPLACE_def] >> strip_tac
  >- ( qabbrev_tac ‘AA = bg (REPLACE Γ (PROP A))’ >>
       qabbrev_tac ‘BB = bg (REPLACE Γ (PROP B))’ >>
       qabbrev_tac ‘AORB = bg (REPLACE Γ (PROP (A V B)))’ >>
       qabbrev_tac ‘CC = bg B0’ >>
       ‘|- (AORB & CC --> (AA V BB) & CC)’ by metis_tac[goldblatt_provable_rules] >>
       irule g_suffixing_rule >> first_assum $ irule_at Any >>
       ‘|- (CC & (AA V BB) --> AA & CC V BB & CC)’ suffices_by
         metis_tac[g_AND_commutative, g_equiv_replacement] >>
       ‘|- (CC & AA  --> AA & CC V BB & CC)’ by
         metis_tac[g_AND_commutative, g_equiv_replacement, goldblatt_provable_rules] >>
       ‘|- (CC & BB  --> AA & CC V BB & CC)’ by
         metis_tac[g_AND_commutative, g_equiv_replacement, goldblatt_provable_rules] >>
       ‘|- (CC & AA V CC & BB --> AA & CC V BB & CC)’ by
         metis_tac[goldblatt_provable_rules] >>
       metis_tac[g_distribution, g_suffixing, g_modus_ponens]
     )
  >- ( qabbrev_tac ‘AA = bg (REPLACE Γ (PROP A))’ >>
       qabbrev_tac ‘BB = bg (REPLACE Γ (PROP B))’ >>
       qabbrev_tac ‘AORB = bg (REPLACE Γ (PROP (A V B)))’ >>
       qabbrev_tac ‘CC = bg B0’ >>
       ‘|- (CC & AORB --> CC & (AA V BB))’ by metis_tac[goldblatt_provable_rules] >>
       irule g_suffixing_rule >> first_assum $ irule_at Any >>
       metis_tac[g_distribution, g_suffixing, g_modus_ponens]
     )
  >- ( qabbrev_tac ‘AA = bg (REPLACE Γ (PROP A))’ >>
       qabbrev_tac ‘BB = bg (REPLACE Γ (PROP B))’ >>
       qabbrev_tac ‘AORB = bg (REPLACE Γ (PROP (A V B)))’ >>
       qabbrev_tac ‘CC = bg B0’ >>
       ‘|- (AORB ∘ᵣ CC --> (AA V BB) ∘ᵣ CC)’ by metis_tac[goldblatt_provable_rules, yeet] >>
       irule g_suffixing_rule >> first_assum $ irule_at Any >>
       ‘|- (CC ∘ᵣ (AA V BB) --> AA ∘ᵣ CC V BB ∘ᵣ CC)’ suffices_by
         metis_tac[g_io_commutative, g_equiv_replacement] >>
       ‘|- (CC ∘ᵣ AA  --> AA ∘ᵣ CC V BB ∘ᵣ CC)’ by
         metis_tac[g_io_commutative, g_equiv_replacement, goldblatt_provable_rules] >>
       ‘|- (CC ∘ᵣ BB  --> AA ∘ᵣ CC V BB ∘ᵣ CC)’ by
         metis_tac[g_io_commutative, g_equiv_replacement, goldblatt_provable_rules] >>
       ‘|- (CC ∘ᵣ AA V CC ∘ᵣ BB --> AA ∘ᵣ CC V BB ∘ᵣ CC)’ by
         metis_tac[goldblatt_provable_rules] >>
       metis_tac[g_io_distribution_lr, g_suffixing, g_modus_ponens]
     )
  >- ( qabbrev_tac ‘AA = bg (REPLACE Γ (PROP A))’ >>
       qabbrev_tac ‘BB = bg (REPLACE Γ (PROP B))’ >>
       qabbrev_tac ‘AORB = bg (REPLACE Γ (PROP (A V B)))’ >>
       qabbrev_tac ‘CC = bg B0’ >>
       ‘|- (CC ∘ᵣ AORB --> CC ∘ᵣ (AA V BB))’ by metis_tac[goldblatt_provable_rules, yeet] >>
       irule g_suffixing_rule >> first_assum $ irule_at Any >>
       metis_tac[g_io_distribution_lr, g_suffixing, g_modus_ponens]
     )
QED

Theorem CONTEXT_IMP:
  ∀X Y. |- (bg(X) --> bg(Y)) ⇒ ∀Γ. |- (bg(REPLACE Γ X) --> bg(REPLACE Γ (Y)))
Proof
  rpt strip_tac >> Induct_on ‘Γ’ >> rw[REPLACE_def]
  >- metis_tac[goldblatt_provable_rules]
  >- metis_tac[goldblatt_provable_rules]
  >- (simp[g_ICONJ_def] >> metis_tac[goldblatt_provable_rules, g_contrapositive_alt, g_DIMP_def])
  >- (‘|-((bg (REPLACE Γ X) ∘ᵣ bg B0) --> (bg (REPLACE Γ (Y)) ∘ᵣ bg B0))’ suffices_by
        metis_tac[g_io_commutative, g_equiv_replacement] >> simp[g_ICONJ_def] >>
      metis_tac[goldblatt_provable_rules, g_contrapositive_alt, g_DIMP_def])
QED

Theorem natural_deduction_to_hilbert:
  ∀X A. X ||- A ⇒ |- ((bg X) --> A)
Proof
  Induct_on ‘X ||- A’ >> rw[] (* 22 *)
  >- metis_tac[goldblatt_provable_rules]
  >- metis_tac[goldblatt_provable_rules]
  >- metis_tac[goldblatt_provable_rules]
  >- metis_tac[goldblatt_provable_rules]
  >- metis_tac[goldblatt_provable_rules]
  >- metis_tac[goldblatt_provable_rules]
  >- metis_tac[goldblatt_provable_rules]
  >- metis_tac[g_io_rule]
  >- (‘|- (bg X' --> bg X --> A')’ suffices_by
        metis_tac[g_io_rule, g_permutation, g_modus_ponens] >>
      metis_tac[g_permutation, g_suffixing, g_modus_ponens]
     )
  >- (‘|- (bg X --> bg X' --> ~A)’ suffices_by
        simp[g_io_rule] >>
      ‘|- (bg X --> ~A' --> ~A)’ by
        metis_tac[g_io_rule, g_contrapositive_alt, g_equiv_replacement] >>
      metis_tac [g_permutation, g_suffixing, g_modus_ponens]
     )
  >- (‘|- (bg (REPLACE Γ (PROP  A)) V bg (REPLACE Γ (PROP  B)) --> A')’ by
        metis_tac[goldblatt_provable_rules] >>
      ‘|- (bg (REPLACE Γ X) --> bg (REPLACE Γ (PROP  A)) V bg (REPLACE Γ (PROP  B)))’
        suffices_by metis_tac[goldblatt_provable_rules] >>
      assume_tac CONTEXT_IMP >> last_x_assum $ qspecl_then [‘X’, ‘PROP  (A V B)’] strip_assume_tac >>
      gs[] >> last_x_assum $ qspec_then ‘Γ’ strip_assume_tac >>
      metis_tac [OR_Bunch_rule, g_suffixing, g_modus_ponens]
     )
  >- (‘|- (bg (Y ， X) --> bg(X ， Y))’ by
        (simp[] >> metis_tac[goldblatt_provable_rules, g_DIMP_def, g_AND_commutative]) >>
      metis_tac[CONTEXT_IMP, g_suffixing, g_modus_ponens]
     )
  >- (‘|- (bg ((X ， Y ， Z)) --> bg((X ， Y) ， Z))’ by
        (simp[] >> metis_tac[goldblatt_provable_rules, g_AND_associative_lr]) >>
      metis_tac[CONTEXT_IMP, g_suffixing, g_modus_ponens]
     )
  >- (‘|- (bg (((X ， Y) ， Z)) --> bg(X ， (Y ， Z)))’ by
        (simp[] >> metis_tac[goldblatt_provable_rules, g_AND_associative_rl]) >>
      metis_tac[CONTEXT_IMP, g_suffixing, g_modus_ponens]
     )
  >- (‘|- (bg (X) --> bg (X ， X))’ by
        (simp[] >> metis_tac[goldblatt_provable_rules]) >>
      metis_tac[CONTEXT_IMP, g_suffixing, g_modus_ponens]
     )
  >- (‘|- (bg (X ， X) --> bg (X))’ by
        (simp[] >> metis_tac[goldblatt_provable_rules]) >>
      metis_tac[CONTEXT_IMP, g_suffixing, g_modus_ponens]
     )
  >- (‘|- (bg (X ， Y) --> bg (X))’ by
        (simp[] >> metis_tac[goldblatt_provable_rules]) >>
      metis_tac[CONTEXT_IMP, g_suffixing, g_modus_ponens]
     )
  >- (‘|- (bg (X) --> bg (PROP τ ； X))’ by
        (simp[] >> metis_tac[goldblatt_provable_rules, g_DIMP_def, g_io_true]) >>
      metis_tac[CONTEXT_IMP, g_suffixing, g_modus_ponens]
     )
  >- (‘|- (bg (PROP τ ； X) --> bg (X))’ by
        (simp[] >> metis_tac[goldblatt_provable_rules, g_DIMP_def, g_io_true]) >>
      metis_tac[CONTEXT_IMP, g_suffixing, g_modus_ponens]
     )
  >- (‘|- (bg (Y ； X) --> bg (X ； Y))’ by
        (simp[] >> metis_tac[goldblatt_provable_rules, g_io_commutative_lr]) >>
      metis_tac[CONTEXT_IMP, g_suffixing, g_modus_ponens]
     )
  >- (‘|- (bg (X ； (Y ； Z)) --> bg ((X ； Y) ； Z))’ by
        (simp[] >> metis_tac[goldblatt_provable_rules, g_io_associative_rl]) >>
      metis_tac[CONTEXT_IMP, g_suffixing, g_modus_ponens]
     )
  >- (‘|- (bg (X) --> bg(X ； X))’ by
        (simp[] >> metis_tac[goldblatt_provable_rules, g_io_imp]) >>
      metis_tac[CONTEXT_IMP, g_suffixing, g_modus_ponens]
     )
QED

Theorem X_derive_bg_X:
  ∀X. X ||- bg(X)
Proof
  Induct >> gs[]
  >- metis_tac[R_sequent_rules]
  >- metis_tac[R_sequent_rules]
  >- (rename[‘X ； Y ||- _’] >>
      simp[g_ICONJ_def] >> assume_tac RAA >>
      last_x_assum irule >> qexists_tac ‘~(bg Y)’ >> rw[]
      >- metis_tac[NOT_NOT_Introduction]
      >- (‘((PROP τ) ； X)||- (bg X --> ~bg Y) --> ~bg Y’ suffices_by
            metis_tac[IMP_Elimination, Assumption, REPLACE_def, identity_lr] >>
          ‘(PROP τ)||- bg X --> (bg X --> ~bg Y) --> ~bg Y’ suffices_by
            metis_tac[IMP_Elimination] >>
          metis_tac[goldblatt_provable_rules, hilbert_to_natural_deduction]
         )
     )
QED

Theorem bg_trans_reconstuction:
  ∀X A. |- (bg(X) --> A) ⇒ X ||- A
Proof
  Induct >> gs[] >> rw[] >>
  drule_then strip_assume_tac hilbert_to_natural_deduction
  >- (assume_tac identity_lr >> last_x_assum $ qspec_then ‘HOLE’ strip_assume_tac >>
      gs[REPLACE_def] >> last_x_assum irule >>
      irule IMP_Elimination >> metis_tac[Assumption])
  >- (rename[‘X ， Y ||- A’] >>
      ‘X ， Y ||- bg X & bg Y’ by
        (assume_tac X_derive_bg_X >>
         pop_assum $ qspec_then ‘X ， Y’ strip_assume_tac >>
         gs[]) >>
      metis_tac[IMP_Elimination, identity_lr, REPLACE_def])
  >- (rename[‘X ； Y ||- A’] >>
      ‘X ； Y ||- (bg X ∘ᵣ bg Y)’ by
      (assume_tac X_derive_bg_X >>
       pop_assum $ qspec_then ‘X ； Y’ strip_assume_tac >>
       gs[]) >>
      metis_tac[IMP_Elimination, identity_lr, REPLACE_def])
QED

val _ = export_theory();
