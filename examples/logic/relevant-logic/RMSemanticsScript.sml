
open HolKernel Parse boolLib bossLib;

open GoldblattRLTheory RLRulesTheory;
open listTheory;
open pred_setTheory;
open numpairTheory string_numTheory;

val _ = new_theory "RMSemantics";

Theorem NOT_MEM_FILTER_LEMMA:
  ∀ a γ. ¬ MEM a (FILTER (λx. x ≠ a) γ)
Proof
  strip_tac >> Induct >> gs[] >> rw[]
QED

Theorem MEM_FILTER_LEMMA:
  ∀ a x γ. MEM x (FILTER (λx. x ≠ a) γ) ⇒ MEM x γ
Proof
  Induct_on ‘γ’ >> gs[] >> rw[]
  >> metis_tac[]
QED

Theorem EMPTY_FILTER_LEMMA:
  ∀a γ. FILTER (λx. x ≠ a) γ = [] ⇔ set γ ⊆ {a}
Proof
  rw[EQ_IMP_THM, SUBSET_DEF] >>
  Induct_on ‘γ’ >> rw[] >> gs[]
QED

Theorem FILTER_NON_MEM_EQUAL:
  ∀ γ A. ¬MEM A γ ⇒ FILTER (λx. x ≠ A) γ = γ
Proof
  Induct_on ‘γ’ >> rw[] >> gs[] >>
  Cases_on ‘γ = []’ >> gs[] >>
  Cases_on ‘FILTER (λx. x ≠ A) γ = []’ >> gs[] >>
  ‘∃B. MEM B γ’ by (Cases_on ‘γ’ >> gs[]) >>
  Induct_on ‘γ’ >> gs[]
QED

Theorem FINITE_EXISTS_LIST:
  ∀x. FINITE x ⇒ ∃l. set l = x
Proof
  Induct_on ‘FINITE’ >>
  rw[] >> qexists_tac ‘e :: l’ >>
  gs[]
QED

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

val _ = overload_on ("|-", “goldblatt_provable”);

Datatype: FRAME = <| W: α set; Z: α; R:α -> α -> α -> bool; STAR: α -> α |>
End

Datatype: MODEL = <| RF: α FRAME; VF: string -> α set|>
End

Definition R_Frame_def:
  R_Frame RF  ⇔
    (RF.Z ∈ RF.W) ∧

    (∀x. x ∈ RF.W ⇒ (RF.STAR x) ∈ RF.W) ∧

    (∀x. x ∈ RF.W ⇒ RF.R RF.Z x x) ∧
    (∀x x' y y' z z'.
        x ∈ RF.W ∧ y ∈ RF.W ∧  z ∈ RF.W ∧
        x' ∈ RF.W ∧ y' ∈ RF.W ∧  z' ∈ RF.W ∧
        RF.R RF.Z x' x ∧ RF.R RF.Z y' y ∧ RF.R RF.Z z z' ∧
        RF.R x y z ⇒ RF.R x' y' z')  ∧

    (∀x. x ∈ RF.W ⇒ RF.STAR (RF.STAR x) = x) ∧
    (∀ w x y. RF.R w x y ∧ x ∈ RF.W ∧ y ∈ RF.W ∧ w ∈ RF.W ⇒ RF.R w (RF.STAR y) (RF.STAR x)) ∧
    (* RF.R Conditions *)
    (∀x. x ∈ RF.W ⇒ RF.R x x x) ∧
    (∀x y z.
        x ∈ RF.W ∧ y ∈ RF.W ∧  z ∈ RF.W ∧
        RF.R x y z ⇒ RF.R y x z) ∧
    (∀w x y z a.
       x ∈ RF.W ∧ y ∈ RF.W ∧  z ∈ RF.W ∧ w ∈ RF.W ∧  a ∈ RF.W ∧
        RF.R w x a ∧ RF.R a y z ⇒
       (∃ b. RF.R x y b ∧ RF.R w b z ∧ b ∈ RF.W))
End

Theorem R_ZERO_EXISTS[simp] = R_Frame_def |> iffLR |> cj 1
Theorem R_STAR_CLOSURE      = R_Frame_def |> iffLR |> cj 2

Theorem R_R_ZERO_REFLEX     = R_Frame_def |> iffLR |> cj 3
Theorem R_R_MONOTONE        = R_Frame_def |> iffLR |> cj 4
Theorem R_STAR_INVERSE      = R_Frame_def |> iffLR |> cj 5
Theorem R_STAR_DUAL         = R_Frame_def |> iffLR |> cj 6

Theorem R_R_SELF_REFLEX     = R_Frame_def |> iffLR |> cj 7
Theorem R_R_COMM            = R_Frame_def |> iffLR |> cj 8
Theorem R_INTER_WORLD       = R_Frame_def |> iffLR |> cj 9

Definition Hereditary_def:
  Hereditary RM ⇔
    ∀x y s. RM.RF.R RM.RF.Z x y ∧ x ∈ RM.VF s ⇒ y ∈ RM.VF s
End

Definition R_Model_def:
  R_Model RM ⇔ R_Frame RM.RF ∧ Hereditary RM
End

Definition Holds_def:
  (Holds RM w (g_VAR s) ⇔ w ∈ RM.RF.W ∧ w ∈ RM.VF s) ∧
  (Holds RM w (a & b) ⇔  w ∈ RM.RF.W ∧ Holds RM w a ∧ Holds RM w b) ∧
  (Holds RM w (~a) ⇔  w ∈ RM.RF.W ∧ ¬ Holds RM (RM.RF.STAR w) a) ∧
  (Holds RM w (a --> b) ⇔  w ∈ RM.RF.W ∧ ∀x y. x ∈ RM.RF.W ∧ y ∈ RM.RF.W ∧ RM.RF.R w x y ∧ Holds RM x a ⇒ Holds RM y b) ∧
  (Holds RM w τ ⇔  w ∈ RM.RF.W ∧ RM.RF.R RM.RF.Z RM.RF.Z w)
End

Theorem OR_Holds:
  ∀ RM w A B. R_Model RM ∧ w ∈ RM.RF.W ⇒ (Holds RM w (A V B) ⇔ Holds RM w A ∨ Holds RM w B)
Proof
  rw[R_Model_def, g_OR_def, Holds_def, EQ_IMP_THM] >> metis_tac[R_STAR_INVERSE, R_STAR_CLOSURE]
QED

Theorem Hereditary_Lemma:
  ∀ RM x y p.
    R_Model RM ∧ x ∈ RM.RF.W ∧ y ∈ RM.RF.W ∧ Holds RM x p ∧ RM.RF.R RM.RF.Z x y ⇒
    Holds RM y p
Proof
  gen_tac >>
  simp[R_Model_def, Hereditary_def] >> Induct_on ‘p’ >>
  simp[Holds_def]
  >- metis_tac[]
  >- (rpt strip_tac >> gs[] >>
      rename [‘RM.RF.R y a b’, ‘Holds _ a A’, ‘Holds _ b B’] >>
      ‘RM.RF.R x a b’ suffices_by metis_tac[] >>
      drule_then irule R_R_MONOTONE >> simp[] >>
      qexistsl_tac [‘y’, ‘a’, ‘b’] >> simp[] >>
      metis_tac[R_R_ZERO_REFLEX])
  >- metis_tac[]
  >- (rw[] >> rename[‘RM.RF.R RM.RF.Z x y’, ‘¬Holds RM (RM.RF.STAR y) A’] >>
      ‘RM.RF.R RM.RF.Z (RM.RF.STAR y) (RM.RF.STAR x)’ by (irule R_STAR_DUAL >> simp[]) >>
      metis_tac[R_STAR_CLOSURE])
  >- (rw[] >>
      irule R_R_MONOTONE >> simp[] >>
      qexistsl_tac [‘RM.RF.Z’, ‘x’, ‘y’] >> simp[] >>
      simp[R_R_ZERO_REFLEX, R_R_SELF_REFLEX])
QED

Theorem R_INTER_WORLD_CONVERSE:
∀RF. R_Frame RF ⇒
     ∀w x y z b. RF.R x y b ∧ RF.R w b z ∧ x ∈ RF.W ∧ y ∈ RF.W ∧ z ∈ RF.W ∧ w ∈ RF.W ∧ b ∈ RF.W
                 ⇒ ∃a. RF.R w x a ∧ RF.R a y z ∧ a ∈ RF.W
Proof
  metis_tac[R_R_COMM, R_INTER_WORLD]
QED

Theorem Contraction_Lemma:
  R_Frame RF ∧ RF.R w x y ∧ w ∈ RF.W ∧ x ∈ RF.W ∧ y ∈ RF.W ⇒ ∃x'. x' ∈ RF.W ∧ RF.R w x x' ∧ RF.R x' x y
Proof
  metis_tac[R_R_SELF_REFLEX, R_INTER_WORLD_CONVERSE]
QED

Theorem Soundness:
  ∀p RM. |- p ∧ R_Model RM ⇒ Holds RM RM.RF.Z p
Proof
  rpt gen_tac >>
  Induct_on ‘goldblatt_provable’ >> simp[Holds_def, R_Model_def] >>
  rpt strip_tac >> gs[R_STAR_CLOSURE]
  >- metis_tac[Hereditary_Lemma, R_R_ZERO_REFLEX, R_Model_def]
  >- (rename [‘RM.RF.R RM.RF.Z ab bc_ac’, ‘RM.RF.R bc_ac bc ac’, ‘RM.RF.R ac a c’] >>
      ‘RM.RF.R bc ab ac’ by
        (irule R_R_MONOTONE >>
         metis_tac[R_R_ZERO_REFLEX, R_R_COMM]) >>
      metis_tac[R_INTER_WORLD])
  >- (rename[‘RM.RF.R RM.RF.Z a ab_b’, ‘RM.RF.R ab_b ab b’] >>
      ‘RM.RF.R a ab b’ by
        (irule R_R_MONOTONE >>
         metis_tac[R_R_ZERO_REFLEX]) >>
      metis_tac[R_R_COMM])
  >- (rename [‘RM.RF.R RM.RF.Z aab ab’, ‘RM.RF.R ab a b’] (* contraction *) >>
      last_x_assum irule >> simp[] >> qexistsl_tac [‘a’, ‘a’] >> simp[] >>
      irule Contraction_Lemma >> simp[] >>
      irule R_R_MONOTONE >>
      metis_tac[R_R_ZERO_REFLEX, R_R_COMM])
  >- metis_tac[Hereditary_Lemma, R_Model_def]
  >- metis_tac[Hereditary_Lemma, R_Model_def]
  >- (rename [‘RM.RF.R RM.RF.Z x y’, ‘RM.RF.R y a b’] >>
      last_x_assum irule >> simp[] >> qexists_tac ‘a’ >> gs[] >>
      irule R_R_MONOTONE >> metis_tac[R_R_ZERO_REFLEX])
  >- (rename [‘RM.RF.R RM.RF.Z x y’, ‘RM.RF.R y a c’] >>
      last_x_assum irule >> simp[] >> qexists_tac ‘a’ >> gs[] >>
      irule R_R_MONOTONE >> metis_tac[R_R_ZERO_REFLEX])
  >- metis_tac[OR_Holds, Hereditary_Lemma, R_Model_def]
  >- metis_tac[OR_Holds, Hereditary_Lemma, R_Model_def]
  >- (rename [‘RM.RF.R RM.RF.Z x y’, ‘RM.RF.R y avb c’] >>
      ‘RM.RF.R x avb c’ by
        (irule R_R_MONOTONE >> metis_tac[R_R_ZERO_REFLEX]) >>
      metis_tac[OR_Holds, R_Model_def])
  >- metis_tac[OR_Holds, Holds_def, Hereditary_Lemma, R_Model_def]
  >- (rename [‘RM.RF.R RM.RF.Z x y’, ‘RM.RF.R y b a’] (*Contradiction*) >>
      ‘RM.RF.R x (RM.RF.STAR a) (RM.RF.STAR b)’ by
        (irule R_R_MONOTONE >>  metis_tac[R_R_ZERO_REFLEX, R_STAR_DUAL, R_STAR_CLOSURE]) >>
      last_x_assum $ qspecl_then [‘RM.RF.STAR a’, ‘RM.RF.STAR b’] strip_assume_tac >> gs[R_STAR_CLOSURE] >>
      metis_tac [R_STAR_INVERSE])
  >- metis_tac[R_STAR_INVERSE, Hereditary_Lemma, R_Model_def]
  >- (last_x_assum irule >> metis_tac[R_R_SELF_REFLEX, R_ZERO_EXISTS])
  >- (‘Holds RM x p’ by
        (irule Hereditary_Lemma >> simp[R_Model_def] >>
         qexists_tac ‘RM.RF.Z’ >> simp[]) >>
      irule Hereditary_Lemma >> simp[R_Model_def] >>
      qexists_tac ‘x’ >> simp[])
  >- (last_x_assum irule >> metis_tac[R_R_SELF_REFLEX, R_ZERO_EXISTS])
QED

Definition CONJl_def:
  (CONJl [] = τ) ∧
  (CONJl [p] = p) ∧
  (CONJl (p::(q::lp)) = p & CONJl (q::lp))
End

Definition pENTAIL_def:
  pENTAIL Γ p ⇔
    ∃ γ. γ ≠ [] ∧ (set γ) ⊆ Γ ∧ |- ((CONJl γ) --> p)
End

val _ = set_fixity "|-^" (Infixr 490);
Overload "|-^" = “pENTAIL”

Definition R_Theory_def:
  R_Theory θ ⇔
    (∀p. θ |-^ p ⇒ p ∈ θ)
End

Definition Regular_def:
  Regular θ ⇔
    R_Theory θ ∧ (∀p. |- p ⇒ p ∈ θ)
End

Definition Prime_def:
  Prime θ ⇔
    R_Theory θ ∧ (∀A B. (A V B) ∈ θ ⇒ (A ∈ θ ∨ B ∈ θ))
End

Definition Ordinary_def:
  Ordinary θ ⇔ Prime θ ∧ Regular θ
End


Theorem LIST_SUBSET_ADJUNCTION:
  ∀γ. set γ ⊆ {p | |- p} ⇒ |- (CONJl γ)
Proof
  rpt strip_tac >> gs[SUBSET_DEF] >>
  Induct_on ‘γ’
  >- metis_tac[goldblatt_provable_rules, CONJl_def]
  >> Cases_on ‘γ’ >> gs[CONJl_def] >>
  rpt strip_tac >> rename[‘|- (k & CONJl (h::t))’] >>
  metis_tac[goldblatt_provable_rules]
QED

Theorem g_A_CONJl_A:
  ∀A γ. set γ ⊆ {A} ∧ γ ≠ []  ⇒
        |- (A --> CONJl γ)
Proof
  rw[] >> Induct_on ‘γ’ >> rw[] >>
  Cases_on ‘γ = []’ >> gs[CONJl_def, g_identity] >>
  ‘CONJl (A::γ) = A & CONJl γ’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
  metis_tac [goldblatt_provable_rules]
QED

Theorem CONJl_weaken_r:
  γ ≠ [] ⇒ |- (CONJl (δ ++ γ) --> CONJl γ)
Proof
  Induct_on ‘δ’
  >- simp[g_identity]
  >- (Cases_on ‘δ’
      >- (Cases_on ‘γ’ >> gs[] >>
          simp[CONJl_def, g_conjunction_r]
         )
      >- (gs[CONJl_def] >> rpt strip_tac
          >> metis_tac[goldblatt_provable_rules]
         )
     )
QED

Theorem CONJl_weaken_l:
  ∀δ. δ ≠ [] ⇒ |- (CONJl (δ ++ γ) --> CONJl δ)
Proof
  Induct_on ‘δ’
  >- simp[]
  >- (Cases_on ‘δ’
      >- (Cases_on ‘γ’ >> gs[] >>
          simp[CONJl_def, g_identity, g_conjunction_l]
         )
      >- (gs[CONJl_def] >> rpt strip_tac
          >> metis_tac[goldblatt_provable_rules]
         )
     )
QED

Theorem CONJl_split:
  ∀ α β. α ≠ [] ∧ β ≠ [] ⇒
         |- (CONJl α & CONJl β --> CONJl (α ++ β)) ∧
         |- (CONJl (α ++ β) --> CONJl α & CONJl β)
Proof
  rw[]
  >- (Induct_on ‘α’ >> rw[] >>
      Cases_on ‘α = []’ >> rw[CONJl_def]
      >- (‘CONJl (h::β) = h & CONJl β’ by (Cases_on ‘β’ >> metis_tac[CONJl_def]) >>
          gs[g_identity]
         )
      >- (‘CONJl (h::α) = h & CONJl α’ by (Cases_on ‘α’ >> metis_tac[CONJl_def]) >>
          ‘CONJl (h::(α ⧺ β)) = h & CONJl (α ++ β)’ by (Cases_on ‘α ++ β’ >> gs[] >> metis_tac[CONJl_def]) >>
          gs[] >>
          ‘|- (h & CONJl α & CONJl β --> CONJl α & CONJl β)’ by
            metis_tac[g_suffixing, g_modus_ponens, g_conj_introduction, g_conjunction_l, g_conjunction_r, g_adjunction_rule] >>
          ‘|- (h & CONJl α & CONJl β --> h)’ by
            metis_tac[g_suffixing, g_modus_ponens, g_conjunction_l] >>
          metis_tac[g_adjunction_rule, g_conj_introduction, g_modus_ponens, g_suffixing]
         )
     )
  >- (irule g_conj_intro_rule >> rw[CONJl_weaken_l, CONJl_weaken_r])
QED

Theorem CONJl_MEM_IMP:
  MEM p γ ⇒ |- (CONJl γ --> p)
Proof
  Induct_on ‘γ’ >> rw[]
  >- (Cases_on ‘γ = []’ >> gs[CONJl_def, g_identity] >>
      ‘CONJl (h::γ) = h & CONJl γ’ by
        (Cases_on ‘γ’ >> gs[CONJl_def]) >> simp[g_conjunction_l]
     )
  >- (gs[] >>
      ‘CONJl (h::γ) = h & CONJl γ’ by
        (Cases_on ‘γ’ >> gs[CONJl_def]) >> simp[] >> metis_tac[goldblatt_provable_rules]
     )
QED

Theorem IMP_MEM_IMP_CONJl:
  ∀q γ. (γ ≠ [] ∧ ∀p. (MEM p γ ⇒ |- (q --> p))) ⇒ |-(q --> CONJl γ)
Proof
  rpt strip_tac >>
  Induct_on ‘γ’ >> rw[] >> Cases_on ‘γ = []’
  >- gs[CONJl_def]
  >- (gs[] >>
      ‘CONJl (h::γ) = h & CONJl γ’ by
        (Cases_on ‘γ’ >> gs[CONJl_def]) >> simp[] >>
      irule g_conj_intro_rule >> gs[]
     )
QED

Theorem FILTER_AND_FILTERED_IMP_CONJl :
  ∀A γ.γ ≠ [] ∧ MEM A γ ∧ FILTER (λx. x ≠ A) γ ≠ [] ⇒
          |- ((CONJl (FILTER (λx. x ≠ A) γ) & A) --> CONJl γ)
Proof
  rw[] >>
  Induct_on ‘γ’ >> rw[] (* 3 *)
  >- (Cases_on ‘FILTER (λx. x ≠ A) γ = []’ >> gs[CONJl_def] (* 2 *)
      >- (‘set γ ⊆ {A}’ by metis_tac[EMPTY_FILTER_LEMMA] >>
          Cases_on ‘γ = []’
          >- metis_tac[goldblatt_provable_rules, CONJl_def]
          >- (‘CONJl (h::γ) = h & CONJl γ’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
              gs[] >> metis_tac[goldblatt_provable_rules, g_A_CONJl_A]
             )
         )
      >- (Cases_on ‘γ = []’ >> rw[CONJl_def] (* 2 *)
          >- metis_tac[goldblatt_provable_rules]
          >- (‘CONJl (h::FILTER (λx. x ≠ A) γ) = h & CONJl (FILTER (λx. x ≠ A) γ)’ by
                (Cases_on ‘FILTER (λx. x ≠ A) γ’ >> gs[CONJl_def]
                ) >>
              ‘CONJl (h::γ) = h & CONJl γ’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
              gs[] >>
              ‘|- (h & CONJl (FILTER (λx. x ≠ A) γ) & A --> h & (CONJl (FILTER (λx. x ≠ A) γ) & A))’ by
                gs[g_AND_associative_rl] >>
              ‘|- (h & (CONJl (FILTER (λx. x ≠ A) γ) & A) --> h & CONJl γ)’ by
                metis_tac[goldblatt_provable_rules] >>
              metis_tac[g_suffixing, g_modus_ponens]
             )
         )
     )
  >- (Cases_on ‘γ = []’ >>
      Cases_on ‘MEM A γ’ >> gs[]
      >- (‘CONJl (A::γ) = A & CONJl γ’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
          gs[] >> metis_tac[goldblatt_provable_rules]
         )
      >- (‘FILTER (λx. x ≠ A) γ = γ’ by
            (Induct_on ‘γ’ >> rw[] >> gs[] >>
             Cases_on ‘γ = []’ >> gs[] >>
             Cases_on ‘FILTER (λx. x ≠ A) γ = []’ >> gs[] >>
             ‘∃B. MEM B γ’ by (Cases_on ‘γ’ >> gs[]) >>
             Induct_on ‘γ’ >> gs[]
            ) >>
          ‘CONJl (A::γ) = A & CONJl γ’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
          gs[] >> metis_tac[goldblatt_provable_rules]
         )
     )
  >- (Cases_on ‘γ = []’ >> gs[] >>
      ‘CONJl (A::γ) = A & CONJl γ’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
      gs[] >> metis_tac[goldblatt_provable_rules]
     )
QED

Theorem Trans_pENTAILS:
  ∀ A p q. A |-^ p ∧ (A ∪ {p}) |-^ q  ⇒ A |-^ q
Proof
  rpt strip_tac >>
  Cases_on ‘p ∈ A’ (* 2 *)
  >- (‘(A ∪ {p}) = A’ by (simp[EXTENSION] >> metis_tac[]) >>
      metis_tac[]
     )
  >- (gs[pENTAIL_def] >> rename [‘|- (CONJl δ --> q)’] >>
      reverse $ Cases_on ‘MEM p δ’ (* 2 *)
      >- (qexists_tac ‘δ’ >> gs[SUBSET_DEF] >> rpt strip_tac >>
          ‘x ≠ p’ by metis_tac[] >>
          qpat_x_assum ‘∀x. MEM x δ ⇒ x ∈ A ∨ x = p’ (qspec_then ‘x’ strip_assume_tac) >>
          metis_tac[]
         )
      >- (qexists_tac ‘(FILTER (λ x. x ≠ p) δ) ++ γ’ >> strip_tac (* 2 *)
          >- (gs[SUBSET_DEF, MEM_FILTER, DISJ_IMP_THM] >> metis_tac[]
             )
          >- (‘|- (CONJl (FILTER (λx. x ≠ p) δ ⧺ γ) --> CONJl δ)’ suffices_by
                (rpt strip_tac
                 >- (gs[SUBSET_DEF] >> rw[] >> gs[] >>
                     Cases_on ‘x = p’ >> gs[NOT_MEM_FILTER_LEMMA] >>
                     metis_tac[MEM_FILTER_LEMMA]
                    )
                 >- (metis_tac[g_suffixing, g_modus_ponens]
                    )
                ) >> Cases_on ‘γ = []’ >> gvs[CONJl_def] >>
              qpat_x_assum ‘MEM p δ’ mp_tac >>
              qpat_x_assum ‘set δ ⊆ A ∪ {p}’ mp_tac >>
              qid_spec_tac ‘δ’ >> Induct >>
              gs[] >> rw[] >> rename[‘_ --> CONJl (h::Δ)’] >> gs[] (* 3 *)
              >- (‘CONJl (h :: Δ) = h & CONJl Δ’ by (
                   Cases_on ‘Δ’ >> gs[CONJl_def]
                   ) >> simp[] >> irule g_conj_intro_rule >>
                  simp[CONJl_MEM_IMP] >> (* here *)
                  ‘CONJl (h :: (FILTER (λx. x ≠ p) Δ ⧺ γ)) = h & (CONJl (FILTER (λx. x ≠ p) Δ ⧺ γ))’ by
                    (Cases_on ‘FILTER (λx. x ≠ p) Δ ⧺ γ’ >> gs[CONJl_def]
                    ) >> gs[] >>
                  metis_tac[g_conjunction_r, g_suffixing, g_modus_ponens]
                 )
              >- (Cases_on ‘MEM h Δ’ >> gvs[]
                  >- (‘CONJl (h :: Δ) = h & CONJl Δ’ by (
                       Cases_on ‘Δ’ >> gs[CONJl_def]
                       ) >> simp[] >> irule g_conj_intro_rule >>
                      metis_tac[CONJl_weaken_r, g_suffixing, g_modus_ponens]
                     )
                  >- (‘FILTER (λx. x ≠ h) Δ = Δ’ by (
                       Induct_on ‘Δ’ >> rw[]
                       ) >> simp[] >> Cases_on ‘Δ = []’ >> gs[CONJl_def] >>
                      ‘CONJl (h :: Δ) = h & CONJl Δ’ by (
                        Cases_on ‘Δ’ >> gs[CONJl_def]
                        ) >> simp[] >> irule g_conj_intro_rule >> strip_tac
                      >- metis_tac[CONJl_weaken_r, g_suffixing, g_modus_ponens]
                      >- simp[CONJl_weaken_l]
                     )
                 )
              >- (‘CONJl (h :: Δ) = h & CONJl Δ’ by (
                   Cases_on ‘Δ’ >> gs[CONJl_def]
                   ) >> simp[] >> irule g_conj_intro_rule >>
                  metis_tac[CONJl_weaken_r, g_suffixing, g_modus_ponens]
                 )
             )
         )
     )
QED

Theorem CONJl_IN_R_Theory_IMP:
  ∀ A γ. R_Theory A ∧ γ ≠ []  ⇒ (CONJl γ ∈ A ⇔ set γ ⊆ A)
Proof
  gs[R_Theory_def, EQ_IMP_THM, SUBSET_DEF] >> rpt strip_tac >> last_x_assum $ irule >> gs[pENTAIL_def] (* 2 *)
  >- (qexists_tac ‘[CONJl γ]’ >> gs[CONJl_def, CONJl_MEM_IMP])
  >- (qexists_tac ‘γ’ >> gs[g_identity, SUBSET_DEF])
QED

Theorem IMP_CONJl_R_THEORY:
  ∀ A γ θ. γ ≠ [] ∧ R_Theory θ ∧ (∀ B. B ∈ set γ ⇒ A --> B ∈ θ) ⇒
           A --> CONJl γ ∈ θ
Proof
  rw[] >> Induct_on ‘γ’ >> rw[] >>
  Cases_on ‘γ = []’
  >- gs[CONJl_def]
  >- (‘CONJl (h::γ) = h & CONJl γ’ by
        (Cases_on ‘γ’ >> gs[CONJl_def]) >>
      gs[R_Theory_def, pENTAIL_def] >> last_x_assum irule >>
      qexists_tac ‘[A --> h; A --> CONJl γ]’ >>
      gs[CONJl_def, g_conj_introduction]
     )
QED

Theorem CONJl_NOTIN_PRIME:
  ∀A γ. Prime A ∧ ~CONJl γ ∈ A ∧ γ ≠ [] ⇒
        ∃x. MEM x γ ∧ ~x ∈ A
Proof
  strip_tac >> Induct >> rw[] >>
  Cases_on ‘γ = []’
  >- (qexists_tac ‘h’ >> gs[CONJl_def])
  >- (‘CONJl (h::γ) = h & CONJl (γ)’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
      gs[] >>
      ‘(~h V ~CONJl γ) ∈ A’ by (
        gs[Prime_def, R_Theory_def] >> last_x_assum irule >>
        simp[pENTAIL_def] >> qexists_tac ‘[~(h & CONJl γ)]’ >> gs[CONJl_def, g_OR_def] >>
        ‘|- ((~(~~h & ~~CONJl γ)) <-> (~(h & CONJl γ)))’ by (
          ‘|- (h <-> ~~h)’ by simp[g_double_negative_equiv] >>
          ‘|- (CONJl γ <-> ~~CONJl γ)’ by simp[g_double_negative_equiv] >>
          metis_tac[g_equiv_AND, g_equiv_replacement, g_equiv_commutative]
          ) >> metis_tac[g_DIMP_def, g_modus_ponens, g_conjunction_r, g_conjunction_l]
        ) >>
        gs[Prime_def] >> last_x_assum $ qspecl_then [‘~h’, ‘~ CONJl γ’] strip_assume_tac >>
        gs[] >>  metis_tac[]
     )
QED

Definition R_gn:
  R_gn (g_VAR s) = 4*(s2n s + 1) ∧
  R_gn (A --> B) = 4*(R_gn A ⊗ R_gn B) + 1 ∧
  R_gn (A & B) = 4*(R_gn A ⊗ R_gn B) + 2 ∧
  R_gn (~A) = 4*(R_gn A) + 3 ∧
  R_gn τ = 0
End

Theorem R_gn_INJ[simp]:
  ∀A B. R_gn A = R_gn B ⇔ A = B
Proof
  simp[EQ_IMP_THM] >> Induct >>
  Cases_on ‘B’ >> simp[R_gn] >> rpt strip_tac >>
  pop_assum (mp_tac o AP_TERM “flip (MOD) 4”) >> simp[]
QED

Theorem countable_g_props:
  countable 𝕌(:g_prop)
Proof
  simp[countable_def, INJ_DEF] >> metis_tac[R_gn_INJ]
QED
 (*
Definition Theta_i_def:
  Theta_i 0 A = {p | |- p} ∧
  Theta_i (SUC n) A =
  let p = LINV R_gn UNIV n;
      θ = Theta_i n A
  in if θ ∪ {p} |-^ A
     then θ
     else θ ∪ {p}
End

Definition Theta_def:
  Theta A = BIGUNION {Theta_i n A | n ∈ UNIV}
End
*)
Definition Theta_i_def:
  Theta_i 0 A = {p | |- p} ∧
  Theta_i (SUC n) A =
  if Theta_i n A ∪ {LINV R_gn UNIV n} |-^ A
     then Theta_i n A
     else Theta_i n A ∪ {LINV R_gn UNIV n}
End

Definition Theta_def:
  Theta A = BIGUNION {Theta_i n A | n ∈ UNIV}
End

Theorem Theta_i_grows:
  e ∈ Theta_i n A ∧ n ≤ m ⇒ e ∈ Theta_i m A
Proof
  rpt strip_tac >> Induct_on ‘m’
  >- (rpt strip_tac >> gs[Theta_i_def])
  >> Cases_on ‘n = SUC m’ >> strip_tac
  >- gs[]
  >> ‘n ≤ m’ by decide_tac >> gs[Theta_i_def] >>
  Cases_on ‘Theta_i m A ∪ {LINV R_gn 𝕌(:g_prop) m} |-^ A’ >> gs[]
QED

Theorem FINITE_SUBSET_THETA:
  ∀s. FINITE s ⇒ (s ⊆ Theta A ⇔ ∃n. s ⊆ Theta_i n A)
Proof
  Induct_on ‘FINITE’ >> simp[] >>
  rpt strip_tac >> simp[Theta_def, PULL_EXISTS] >> reverse eq_tac
  >- metis_tac[]
  >> rpt strip_tac >> rename [‘ p ∈ Theta_i m A’, ‘s ⊆ Theta_i n A’] >>
  Cases_on ‘m ≤ n’
  >- metis_tac[Theta_i_grows]
  >> ‘n < m’ by decide_tac >>
  qexists_tac ‘m’ >> simp[SUBSET_DEF] >> rpt strip_tac
  >> irule Theta_i_grows >> qexists_tac ‘n’ >> gs[] >>
  metis_tac[SUBSET_DEF]
QED

Theorem Theta_Maximal_Rejection:
  ∀A. ¬ |- A ⇒
      ¬((Theta A) |-^ A) ∧ ∀q. q ∉ (Theta A) ⇒ (Theta A ∪ {q}) |-^ A
Proof
  rpt strip_tac
  >- (gs[pENTAIL_def, FINITE_DEF, FINITE_SUBSET_THETA] >>
      Induct_on ‘n’ >>
      metis_tac[LIST_SUBSET_ADJUNCTION, goldblatt_provable_rules,
                pENTAIL_def, Theta_i_def])
  >- (CCONTR_TAC >>
      qpat_x_assum ‘q ∉ Theta A’ mp_tac >> gs[] >>
      assume_tac FINITE_SUBSET_THETA >>
      last_x_assum $ qspec_then ‘{q}’ strip_assume_tac >> gs[] >>
      qexists_tac ‘SUC (R_gn q)’ >> gs[Theta_i_def] >>
      ‘q = LINV R_gn 𝕌(:g_prop) (R_gn q)’ by (
        ‘q ∈ 𝕌(:g_prop)’ by simp[] >>
        ‘INJ R_gn 𝕌(:g_prop)  𝕌(:num)’ by simp[INJ_DEF] >>
        metis_tac [LINV_DEF]
        ) >>
      ‘¬ (Theta_i (R_gn q) A ∪ {q} |-^ A)’ suffices_by (
        rw[] >> metis_tac[]) >>
      gs[pENTAIL_def] >> rpt strip_tac >>
      last_x_assum $ qspec_then ‘γ’ strip_assume_tac >> gs[] >>
      ‘¬(set γ ⊆ Theta_i (R_gn q) A ∪ {q})’ suffices_by metis_tac[] >>
      gs[SUBSET_DEF] >> qexists_tac ‘x’ >> simp[] >>
      assume_tac FINITE_SUBSET_THETA >>
      last_x_assum $ qspec_then ‘{x}’ strip_assume_tac >> gs[])
QED

Theorem R_SUBSET_THETA:
 {p | |- p} ⊆ Theta A
Proof
  simp[Theta_def, BIGUNION, PULL_EXISTS] >>
  rw[SUBSET_DEF] >> qexists_tac ‘0’ >> simp[SUBSET_DEF, Theta_i_def]
QED

Theorem Theta_R_Theory:
  ∀A. ¬ |- A ⇒ R_Theory (Theta A)
Proof
  metis_tac[R_SUBSET_THETA, Trans_pENTAILS, Theta_Maximal_Rejection, R_Theory_def]
QED

Theorem Exists_Theta_prop:
  ∀A a. ¬( |- A ) ∧ a ∉ Theta A ⇒
         ∃ c. |- ((c & a) --> A) ∧ c ∈ Theta A
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac Theta_Maximal_Rejection >>
  last_x_assum $ qspec_then ‘a’ strip_assume_tac >> gs[pENTAIL_def] >>
  qexists_tac ‘CONJl (FILTER (λx. x ≠ a) γ)’ >> rw[] (* 2 *)
  >- (‘|- (CONJl (FILTER (λx. x ≠ a) γ) & a --> CONJl γ)’ suffices_by
        metis_tac[goldblatt_provable_rules] >>
      reverse $ Cases_on ‘MEM a γ’ (* 2 *)
      >- (‘set γ ⊆ Theta A’ by (
           gs[SUBSET_DEF] >> metis_tac[]
           ) >> metis_tac[]
         )
      >- (‘|- (CONJl (FILTER (λx. x ≠ a) γ) & a --> CONJl γ)’ suffices_by
            metis_tac[goldblatt_provable_rules] >>
          Cases_on ‘FILTER (λx. x ≠ a) γ = []’ (* 2 *)
          >- (Induct_on ‘γ’ >> rw[CONJl_def]
              >> gs[] >> Cases_on ‘γ = []’ >> gs[CONJl_def] (* 3 *)
              >- metis_tac[goldblatt_provable_rules]
              >- (‘CONJl (a::γ) = a & CONJl γ’ by
                    (Cases_on ‘γ’ >> gs[CONJl_def]) >> simp[] >>
                  irule g_conj_intro_rule >> simp[g_conjunction_r] >>
                  last_x_assum irule >> strip_tac >>
                  ‘MEM a γ’ by
                    (Induct_on ‘γ’ >> rw[]) >> simp[] >>
                  ‘|- (CONJl γ --> CONJl (a::γ))’ suffices_by
                    metis_tac[goldblatt_provable_rules] >>
                  simp[] >> irule g_conj_intro_rule >> simp[g_identity, CONJl_MEM_IMP]
                 )
              >- (‘CONJl (a::γ) = a & CONJl γ’ by
                    (Cases_on ‘γ’ >> gs[CONJl_def]) >> simp[] >>
                  irule g_conj_intro_rule >> simp[g_conjunction_r] >>
                  last_x_assum irule >>
                  ‘|- (CONJl γ --> CONJl (a::γ))’ suffices_by
                    metis_tac[goldblatt_provable_rules] >>
                  simp[] >> irule g_conj_intro_rule >> simp[g_identity, CONJl_MEM_IMP]
                 )
             )
          >- (irule IMP_MEM_IMP_CONJl >> reverse $ strip_tac >> gs[] >>
              rpt strip_tac >> Cases_on ‘p = a’
              >- metis_tac [goldblatt_provable_rules]
              >- (‘MEM p (FILTER (λx. x ≠ a) γ)’ suffices_by
                    metis_tac[goldblatt_provable_rules, CONJl_MEM_IMP] >>
                  qpat_x_assum ‘MEM p γ’ $ mp_tac >>
                  qid_spec_tac ‘γ’ >> Induct >> gs[] >>
                  rename [‘MEM p δ ⇒ MEM p (FILTER (λx. x ≠ a) δ)’] >>
                  reverse $ rw[] >> gs[]
                 )
             )
         )
     )
  >- (‘set (FILTER (λx. x ≠ a) γ) ⊆ Theta A’ suffices_by (
       rw[] >> ‘R_Theory (Theta A)’ by simp[Theta_R_Theory] >>
       assume_tac CONJl_IN_R_Theory_IMP >>
       pop_assum $ qspecl_then [‘Theta A’, ‘FILTER (λx. x ≠ a) γ’] strip_assume_tac >>
       Cases_on ‘FILTER (λx. x ≠ a) γ = []’ >> gs[CONJl_def] >>
       ‘|- τ’ by metis_tac[goldblatt_provable_rules] >>
       assume_tac R_SUBSET_THETA >> gs[ SUBSET_DEF]
       ) >>
      gs[SUBSET_DEF] >> rw[] >>
      Cases_on ‘x = a’ >> metis_tac[NOT_MEM_FILTER_LEMMA, MEM_FILTER_LEMMA]
     )
QED

Theorem Theta_Prime:
  ∀A. ¬ |- A ⇒ Prime (Theta A)
Proof
  rw[Prime_def, Theta_R_Theory] >>
  rename[‘a V b ∈ Theta A’] >> CCONTR_TAC >> qpat_x_assum ‘a V b ∈ Theta A’ mp_tac >> gs[] >>
  drule_all_then strip_assume_tac Exists_Theta_prop >>
  rev_drule_all_then strip_assume_tac Exists_Theta_prop >>
  rename [‘|- (c & a --> A)’, ‘|- (d & b --> A)’, ‘a V b ∉ Theta A’] >>
  ‘|- ((c & d) & a --> A)’ by (
    ‘|- (((c & d) & a) --> (c & a))’ by
       (assume_tac g_conj_introduction >>
        last_x_assum $ qspecl_then [‘((c & d) & a)’, ‘c’,‘a’] strip_assume_tac >>
        metis_tac [g_conjunction_l, g_conjunction_r, g_modus_ponens,
                   g_conj_introduction, g_suffixing, g_adjunction_rule]
       ) >>
    metis_tac[g_suffixing, g_modus_ponens]
    ) >>
  ‘|- ((c & d) & b --> A)’ by (
    ‘|- (((c & d) & b) --> (d & b))’ by
       (assume_tac g_conj_introduction >>
        last_x_assum $ qspecl_then [‘((c & d) & b)’, ‘c’, ‘b’] strip_assume_tac >>
        metis_tac [g_conjunction_l, g_conjunction_r, g_modus_ponens,
                   g_conj_introduction, g_suffixing, g_adjunction_rule]
       ) >>
    metis_tac[g_suffixing, g_modus_ponens]
    ) >>
  ‘|- (((c & d) & (a V b)) --> A)’ by
    metis_tac [g_suffixing, g_modus_ponens, g_adjunction_rule, g_distribution, g_disjunction_elim] >>
  ‘(c & d) ∈ Theta A’ by (
    ‘R_Theory (Theta A)’ by simp [Theta_R_Theory] >>
    gs[R_Theory_def] >> last_x_assum irule >>
    simp[pENTAIL_def] >> qexists_tac ‘[c; d]’ >> gs[CONJl_def] >> simp[g_identity]
    ) >>
  CCONTR_TAC >> gs[] >>
  ‘(Theta A) |-^ A’ by
    (simp[pENTAIL_def] >>
     qexists_tac ‘[(c & d); (a V b)]’ >> simp[CONJl_def]
    ) >>
  metis_tac[Theta_Maximal_Rejection]
QED

Theorem Theta_Ordinary:
  ∀A. ¬ |- A ⇒ Ordinary (Theta A)
Proof
  rw[Ordinary_def, Theta_Prime, Regular_def, Theta_R_Theory] >>
  assume_tac R_SUBSET_THETA >> gs[SUBSET_DEF]
QED

Definition sENTAILS_def:
  sENTAILS S Γ p ⇔
    ∃ γ. γ ≠ [] ∧ (set γ) ⊆ Γ ∧ (CONJl γ) --> p ∈ S
End

Definition S_Theory_def:
  S_Theory S Θ ⇔
    Ordinary S ∧ ∀p. (sENTAILS S Θ p ⇒ p ∈ Θ)
End

Theorem Theta_S_theory_cor:
  ¬ |- p ⇒ ((S_Theory (Theta p) Γ) ⇔ ∀q. (sENTAILS (Theta p) Γ q ⇒ q ∈ Γ))
Proof
  rw[S_Theory_def, Theta_Ordinary]
QED

Definition APPLYING_def:
  APPLYING X Y = {p | ∃γ. γ ≠ [] ∧ (CONJl γ --> p) ∈ X ∧ set γ ⊆ Y}
End

Definition Canonical_Frame_def:
  Canonical_Frame A =
    <|W := {w | Prime w ∧ S_Theory (Theta A) w};
      Z := (Theta A);
      R := λ x y z. APPLYING x y ⊆ z ∧ x ∈ {w | Prime w ∧ S_Theory (Theta A) w} ∧
                    y ∈ {w | Prime w ∧ S_Theory (Theta A) w} ∧
                    z ∈ {w | Prime w ∧ S_Theory (Theta A) w};
      STAR := λ x. {A | ~A ∉ x} |>
End

Theorem Theta_Theta_theory:
  ∀A. ¬ |- A ⇒  S_Theory (Theta A) (Theta A)
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac Theta_Ordinary >>
  rw[Theta_S_theory_cor, sENTAILS_def] >>
  drule_then strip_assume_tac Theta_R_Theory >>
  ‘CONJl γ ∈ Theta A’ by gs[CONJl_IN_R_Theory_IMP] >> gs[R_Theory_def] >>
  last_x_assum irule >> simp[pENTAIL_def] >> qexists_tac ‘[CONJl γ; CONJl γ --> q]’ >>
  simp[CONJl_def] >> simp[g_AND_MP]
QED

Theorem Canonical_Frame_STAR_STAR:
  ∀ A x.
      x ∈ (Canonical_Frame A).W ⇒
      (Canonical_Frame A).STAR ((Canonical_Frame A).STAR x) = x
Proof
  simp [Canonical_Frame_def] >>
  rpt strip_tac >> gs[EXTENSION] >> rw[EQ_IMP_THM] >>
  rename[‘~~a ∈ x’] >> gs[Prime_def, R_Theory_def] >> last_x_assum $ irule >>
  simp[pENTAIL_def] (* 2 *)
  >- (qexists_tac ‘[~~a]’ >> simp[SUBSET_DEF, g_double_negation, CONJl_def])
  >- (qexists_tac ‘[a]’ >> simp[SUBSET_DEF, g_double_neg, CONJl_def])
QED

Theorem Prime_STAR_R_Theory:
  ∀x. Prime x ⇒ R_Theory {A | ~A ∉ x}
Proof
  simp[R_Theory_def, pENTAIL_def] >> rpt strip_tac >>
  CCONTR_TAC >>
  qpat_x_assum ‘|- (CONJl γ --> p)’ mp_tac >> gs[] >>
  Induct_on ‘γ’
  >- gs[]
  >- (Cases_on ‘γ = []’
      >- (gs[CONJl_def] >> rpt strip_tac >>
          ‘|- (~p --> ~h)’ by metis_tac[g_contrapositive_alt, g_equiv_replacement] >>
          gs[Prime_def, R_Theory_def, pENTAIL_def] >> qpat_x_assum ‘~h ∉ x’ mp_tac >> gs[] >>
          last_x_assum irule >> qexists_tac ‘[~p]’ >>
          simp[CONJl_def, SUBSET_DEF]
         )
      >- (rpt strip_tac >>
          ‘CONJl (h::γ) = h & CONJl γ’ by (Cases_on ‘γ’ >> gs[CONJl_def]) >>
          gs[] >>
          ‘|- (~p --> ~(h & CONJl γ))’ by
            metis_tac[goldblatt_provable_rules, g_contrapositive_alt, g_DIMP_def] >>
          ‘~h V ~CONJl γ ∈ x’ by
            (gs[R_Theory_def, Prime_def] >> last_x_assum irule >> simp[pENTAIL_def] >>
             qexists_tac ‘[~p]’ >> simp[SUBSET_DEF, CONJl_def] >>
             simp[g_OR_def] >>
             ‘|- ((~(~~h & ~~CONJl γ)) <-> (~(h & CONJl γ)))’ by (
               ‘|- (h <-> ~~h)’ by simp[g_double_negative_equiv] >>
               ‘|- (CONJl γ <-> ~~CONJl γ)’ by simp[g_double_negative_equiv] >>
               metis_tac[g_equiv_AND, g_equiv_replacement, g_equiv_commutative]
               ) >> metis_tac[g_equiv_replacement, g_equiv_commutative]
            ) >>
          assume_tac CONJl_NOTIN_PRIME >> pop_assum $ qspecl_then [‘x’, ‘γ’] strip_assume_tac >> gs[Prime_def] >>
          qpat_x_assum ‘∀A B. A V B ∈ x ⇒ A ∈ x ∨ B ∈ x’ $ qspecl_then [‘~h’, ‘~ CONJl γ’] strip_assume_tac >>
          gs[SUBSET_DEF]
         )
     )
QED

Theorem STAR_IN_CANONICAL_FRAME:
  ∀A x.
      x ∈ (Canonical_Frame A).W ∧ ¬ |- A ⇒
      (Canonical_Frame A).STAR x ∈ (Canonical_Frame A).W
Proof
  rpt strip_tac >> gs[Canonical_Frame_def] >> rpt strip_tac
  >- (simp[Prime_def] >> reverse $ rw[] (* 2 *)
      >- (rename [‘~(a V b) ∉ x’] >> CCONTR_TAC >> gs[g_OR_def] >>
          ‘let C = Canonical_Frame A in
             C.STAR (C.STAR x) = x’ by
            (assume_tac Canonical_Frame_STAR_STAR >> gs[] >>
             pop_assum irule >> simp[Canonical_Frame_def]
             ) >> gs[S_Theory_def] >>
          ‘(~a & ~b) ∈ x’ by
            (last_x_assum $ irule >> gs[sENTAILS_def] >>
             qexists_tac ‘[~a; ~b]’ >> rw[CONJl_def] >>
             gs[Regular_def, Ordinary_def] >> last_x_assum irule >>
             simp[g_identity]
            ) >>
          gs[EXTENSION, Canonical_Frame_def]
         )
      >- simp[Prime_STAR_R_Theory]
     )
  >- (gs[S_Theory_def, sENTAILS_def] >> rw[] >> CCONTR_TAC >>
      gs[] >> ‘S_Theory (Theta A) (Theta A)’ by gs[Theta_Theta_theory] >> gs[S_Theory_def] >>
      ‘~p --> ~CONJl γ ∈ Theta A’ by
        (last_x_assum irule >> simp[sENTAILS_def] >>
         qexists_tac ‘[CONJl γ --> p]’ >> simp[CONJl_def] >>
         ‘|- ((CONJl γ --> p) --> ~p --> ~CONJl γ)’ by
           metis_tac[goldblatt_provable_rules, g_contrapositive_alt, g_DIMP_def] >>
         gs[Ordinary_def, Regular_def]
        ) >>
      qpat_x_assum ‘set γ ⊆ {A | ~A ∉ x}’ mp_tac >> simp[SUBSET_DEF] >>
      ‘~CONJl γ ∈ x’ by
        (last_x_assum irule >> simp[sENTAILS_def] >>
         qexists_tac ‘[~p]’ >> gs[SUBSET_DEF, CONJl_def]
        ) >>
        gs[CONJl_NOTIN_PRIME]
     )
QED

Definition B_WORLD_i_def:
  B_WORLD_i 0 Θ S R = S ∧
  B_WORLD_i (SUC n) Θ S R =
  if (∃A. A ∈ R ∧ sENTAILS Θ (B_WORLD_i n Θ S R ∪ {LINV R_gn UNIV n}) A)
  then B_WORLD_i n Θ S R
  else B_WORLD_i n Θ S R ∪ {LINV R_gn UNIV n}
End

Definition B_WORLD_def:
  B_WORLD Θ S R = BIGUNION {B_WORLD_i n Θ S R | n ∈ UNIV}
End

Theorem B_WORLD_i_grows:
  ∀ e n m Θ A R. e ∈ B_WORLD_i n Θ A R ∧ n ≤ m ⇒
                 e ∈ B_WORLD_i m Θ A R
Proof
  rpt strip_tac >> Induct_on ‘m’
  >- (rpt strip_tac >> gs[B_WORLD_i_def])
  >> Cases_on ‘n = SUC m’ >> strip_tac
  >- gs[]
  >> ‘n ≤ m’ by decide_tac >> gs[B_WORLD_i_def] >> rw[]
QED

Theorem FINITE_SUBSET_B_WORLD:
    ∀ s Θ A R. FINITE s ⇒ (s ⊆ B_WORLD Θ A R ⇔ ∃n. s ⊆ B_WORLD_i n Θ A R)
Proof
  Induct_on ‘FINITE’ >> simp[] >>
  rpt strip_tac >> simp[B_WORLD_def, PULL_EXISTS] >> reverse eq_tac
  >- metis_tac[]
  >> rpt strip_tac >>
  rename [‘e ∈ B_WORLD_i m Θ I' R’,
          ‘s ⊆ B_WORLD_i n Θ I' R’] >>
  Cases_on ‘m ≤ n’
  >- metis_tac[B_WORLD_i_grows]
  >> ‘n < m’ by decide_tac >>
  qexists_tac ‘m’ >> simp[SUBSET_DEF] >> rpt strip_tac >>
  irule B_WORLD_i_grows >> qexists_tac ‘n’ >> gs[] >>
  metis_tac[SUBSET_DEF]
QED

Theorem S_Theory_imp_R_Theory:
  ∀ θ x. S_Theory θ x ⇒ R_Theory x
Proof
  rpt strip_tac >>
  gs[R_Theory_def, S_Theory_def, pENTAIL_def, sENTAILS_def] >>
  rpt strip_tac >> last_x_assum irule >>
  qexists_tac ‘γ’ >>
  gs[Ordinary_def, Regular_def]
QED

Theorem CONJl_IN_APPLIED:
  ∀ θ w x γ. S_Theory θ w ∧
             set γ ⊆ APPLYING w x ∧ γ ≠ [] ⇒
             CONJl γ ∈ APPLYING w x
Proof
  rw[] >> Induct_on ‘γ’ >> rw[] >>
  Cases_on ‘γ = []’
  >- metis_tac[CONJl_def]
  >- (gs[] >>
      ‘CONJl (h::γ) = h & CONJl γ’ by
        (Cases_on ‘γ’ >> metis_tac[CONJl_def]
        ) >> gs[APPLYING_def] >>
      rename[‘CONJl α --> CONJl γ ∈ w’, ‘CONJl β --> h’, ‘CONJl (h::γ) = h & CONJl γ’] >>
      qexists_tac ‘α ++ β’ >> simp[CONJl_def] >>
      ‘(CONJl α & CONJl β) --> h ∈ w ∧ (CONJl α & CONJl β) --> CONJl γ ∈ w’ by
        (‘R_Theory w’ by metis_tac[S_Theory_imp_R_Theory] >> gs[R_Theory_def, pENTAIL_def] >>
         strip_tac (* 2 *)
         >- (last_x_assum irule >> qexists_tac ‘[CONJl β --> h]’ >> simp[CONJl_def, g_AND_STRENGTHEN])
         >- (last_x_assum irule >> qexists_tac ‘[CONJl α --> CONJl γ]’ >> simp[CONJl_def, g_AND_STRENGTHEN])
        ) >>
      gs[S_Theory_def, sENTAILS_def] >> last_x_assum irule >>
      qexists_tac ‘[CONJl α & CONJl β --> h; CONJl α & CONJl β --> CONJl γ]’ >> rw[CONJl_def] >>
      gs[Ordinary_def, Regular_def] >> last_x_assum irule >>
      ‘|- ((CONJl α & CONJl β --> h) & (CONJl α & CONJl β --> CONJl γ) -->
           CONJl α & CONJl β --> h & CONJl γ)’ by simp[g_conj_introduction] >>
      ‘|- (CONJl α & CONJl β --> (CONJl α & CONJl β --> h) & (CONJl α & CONJl β --> CONJl γ) -->
            h & CONJl γ)’ by metis_tac[g_permutation, g_modus_ponens] >>
      ‘|- (CONJl (α ++ β) --> CONJl α & CONJl β)’ by simp[CONJl_split] >>
      metis_tac[g_suffixing, g_modus_ponens, g_permutation]
     )
QED


Theorem S_Theory_B_WORLD:
  ∀A w x y z. ¬ |- A ∧
            S_Theory (Theta A) w ∧
            APPLYING w (B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)}) ⊆ z
            ⇒
            S_Theory (Theta A) (B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)})
Proof
  rpt strip_tac >>
  rw[S_Theory_def, sENTAILS_def, Theta_Ordinary] >> simp[B_WORLD_def, PULL_EXISTS] >>
  qexists_tac ‘SUC (R_gn p)’ >> simp[B_WORLD_i_def] >>
  ‘LINV R_gn 𝕌(:g_prop) (R_gn p) = p’ by (
    ‘p ∈ 𝕌(:g_prop)’ by simp[] >>
    ‘INJ R_gn 𝕌(:g_prop)  𝕌(:num)’ by simp[INJ_DEF] >>
    metis_tac [LINV_DEF]
    ) >> simp[PULL_EXISTS] >>
  ‘¬∃A' q.
      (A' --> q ∈ w ∧ q ∉ z) ∧
      sENTAILS (Theta A)
               (B_WORLD_i (R_gn p) (Theta A) (APPLYING x y)
                {p | (∃q. p --> q ∈ w ∧ q ∉ z)} ∪
                {p}) A'’ suffices_by
    (rw[] >> metis_tac[]) >>
  CCONTR_TAC >> gs[sENTAILS_def] >>
  rename [‘CONJl δ --> B ∈ Theta A’] >>
  ‘(B --> q) --> CONJl δ --> q ∈ Theta A’ by
    (drule_then mp_tac Theta_Ordinary >>
     rw[Ordinary_def, Prime_def, R_Theory_def, pENTAIL_def] >>
     last_x_assum irule >> qexists_tac ‘[CONJl δ --> B]’ >>
     simp[CONJl_def, g_suffixing]
    ) >>
  ‘q ∈ APPLYING w
   (B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)})’ suffices_by
    metis_tac[SUBSET_DEF] >>
  simp[APPLYING_def] >>
  qexists_tac ‘(FILTER (λx. x ≠ p) δ) ++ γ’ >> reverse $ rw[]
  >- gs[APPLYING_def]
  >- (‘∀δ. set δ ⊆
               B_WORLD_i (R_gn p) (Theta A) (APPLYING x y)
               {p | (∃q. p --> q ∈ w ∧ q ∉ z)} ∪ {p} ⇒
           set (FILTER (λx. x ≠ p) δ) ⊆
               B_WORLD (Theta A) {p | (∃γ. γ ≠ [] ∧ CONJl γ --> p ∈ x ∧ set γ ⊆ y)}
               {p | (∃q. p --> q ∈ w ∧ q ∉ z)}’ by
        (Induct >> rw[] >> assume_tac FINITE_SUBSET_B_WORLD >>
         pop_assum $ qspec_then ‘{h}’ strip_assume_tac >>
         gs[] >> qexists_tac ‘R_gn p’ >> gs[APPLYING_def]
        ) >>
      gs[]
     )
  >- (qpat_x_assum ‘S_Theory (Theta A) w’ mp_tac >> rw[S_Theory_def, sENTAILS_def] >>
      last_assum irule >> qexists_tac ‘[CONJl δ --> q]’ >> rw[CONJl_def]
      >- (last_x_assum irule >> qexists_tac ‘[B --> q]’ >> gs[CONJl_def]
         )
      >- (drule Theta_R_Theory >> rw[R_Theory_def, pENTAIL_def] >>
          last_x_assum irule >>
          qexists_tac ‘[CONJl (FILTER (λx. x ≠ p) δ ⧺ γ) --> CONJl δ]’ >>
          reverse $ rw[CONJl_def]
          >- simp[g_suffixing]
          >- (irule IMP_CONJl_R_THEORY >> gs[Theta_R_Theory] >>
              rw[] >> rename [‘MEM b δ’] >> Cases_on ‘b = p’
              >- (simp[] >>
                  Cases_on ‘FILTER (λx. x ≠ p) δ = []’ >> simp[] >>
                  assume_tac Theta_R_Theory >>
                  pop_assum $ qspec_then ‘A’ strip_assume_tac >>
                  gs[R_Theory_def, pENTAIL_def] >> pop_assum irule >>
                  qexists_tac ‘[CONJl γ --> p]’ >> simp[CONJl_def] >>
                  irule g_modus_ponens >> qexists_tac ‘CONJl (FILTER (λx. x ≠ p) δ) & CONJl γ --> CONJl γ’ >>
                  simp[g_conjunction_r] >>
                  metis_tac[g_modus_ponens, g_suffixing, g_permutation, CONJl_split]
                 )
              >- (‘MEM b (FILTER (λx. x ≠ p) δ)’ by
                    (pop_assum mp_tac >>
                     pop_assum mp_tac >>
                     qid_spec_tac ‘δ’ >>
                     qid_spec_tac ‘b’ >>
                     qid_spec_tac ‘p’ >>
                     gen_tac >> gen_tac >>
                     Induct >> rw[] >> CCONTR_TAC >>
                     gs[]
                    ) >>
                  gs[Ordinary_def, Regular_def] >> last_x_assum irule >>
                  irule CONJl_MEM_IMP >> simp[]
                 )
             )
         )
     )
QED

Theorem B_WORLD_prop_exists:
 ∀ p x w z C. ¬ |- p ∧ Prime z ∧ S_Theory (Theta p) w ∧
              S_Theory (Theta p) (B_WORLD (Theta p) x {p | ∃q. p --> q ∈ w ∧ q ∉ z}) ∧
              C ∉ B_WORLD (Theta p) x {p | ∃q. p --> q ∈ w ∧ q ∉ z} ∧ B_WORLD (Theta p) x {p | ∃q. p --> q ∈ w ∧ q ∉ z} ≠ ∅ ⇒
              ∃D d. D ∉ z ∧ d ∈ B_WORLD (Theta p) x {p | ∃q. p --> q ∈ w ∧ q ∉ z} ∧
                    d & C --> D ∈ w
Proof
  rw[] >> CCONTR_TAC >> gs[] >>
  qpat_x_assum ‘C ∉ B_WORLD (Theta p) x {p | (∃q. p --> q ∈ w ∧ q ∉ z)}’ mp_tac >> gs[] >>
  ‘{C} ⊆ B_WORLD (Theta p) x {p | (∃q. p --> q ∈ w ∧ q ∉ z)}’ suffices_by simp[] >>
  irule (iffRL FINITE_SUBSET_B_WORLD) >> simp[] >>
  qexists_tac ‘SUC (R_gn C)’ >> simp[B_WORLD_i_def] >>
  ‘¬ ∃A. (∃q. A --> q ∈ w ∧ q ∉ z) ∧
         sENTAILS (Theta p)
                  (B_WORLD_i (R_gn C) (Theta p) x {p | (∃q. p --> q ∈ w ∧ q ∉ z)} ∪
                   {C}) A’ suffices_by
    (‘LINV R_gn 𝕌(:g_prop) (R_gn C) = C’ by
       (‘C ∈ 𝕌(:g_prop)’ by simp[] >>
        ‘INJ R_gn 𝕌(:g_prop)  𝕌(:num)’ by simp[INJ_DEF] >>
        metis_tac [LINV_DEF]
       ) >> strip_tac >> simp[]
    ) >>
  rw[] >>
  Cases_on ‘sENTAILS (Theta p) (B_WORLD_i (R_gn C) (Theta p) x {p | (∃q. p --> q ∈ w ∧ q ∉ z)} ∪ {C}) A’ >> simp[] >>
  CCONTR_TAC >> gs[] >>
  qpat_x_assum ‘∀D d.
          D ∈ z ∨ d ∉ B_WORLD (Theta p) x {p | (∃q. p --> q ∈ w ∧ q ∉ z)} ∨
          d & C --> D ∉ w’ mp_tac >> rw[] >>
  gs[sENTAILS_def] >>
  ‘∃α. α ∈ B_WORLD (Theta p) x {p | ∃q. p --> q ∈ w ∧ q ∉ z}’ by metis_tac[MEMBER_NOT_EMPTY] >>
  qexistsl_tac [‘q’, ‘CONJl (α::(FILTER (λx. x ≠ C) γ))’] >> rw[] (* 2 *)
  >- (‘set (α::(FILTER (λx. x ≠ C) γ)) ⊆ B_WORLD (Theta p) x {p | (∃q. p --> q ∈ w ∧ q ∉ z)}’ by
        (gs[SUBSET_DEF] >> rpt strip_tac >> simp[] >>
         last_x_assum $ qspec_then ‘x'’ strip_assume_tac >>
         ‘MEM x' γ’ by metis_tac[MEM_FILTER_LEMMA] >> gs[NOT_MEM_FILTER_LEMMA] >>
         simp[B_WORLD_def] >> metis_tac[]
        ) >> irule (iffRL CONJl_IN_R_Theory_IMP) >> simp[] >>
      metis_tac[S_Theory_imp_R_Theory]
     )
  >- (‘CONJl (α::FILTER (λx. x ≠ C) γ) & C --> A ∈ (Theta p)’ suffices_by
        (rw[] >> gs[S_Theory_def] >> last_x_assum irule >> simp[sENTAILS_def] >>
         qexists_tac ‘[A --> q]’ >> simp[CONJl_def] >>
         gs[Ordinary_def, Regular_def, R_Theory_def] >>
         qpat_x_assum ‘∀p._ |-^ _ ⇒ _’ irule >> simp[pENTAIL_def] >>
         qexists_tac ‘[CONJl (α::FILTER (λx. x ≠ C) γ) & C --> A]’ >>
         simp[CONJl_def, g_suffixing]) >>
      Cases_on ‘FILTER (λx. x ≠ C) γ = []’ >> gs[CONJl_def]
      >- (‘set γ ⊆ {C}’ by gs[EMPTY_FILTER_LEMMA] >>
          gs[S_Theory_def, Ordinary_def, Regular_def, R_Theory_def] >>
          qpat_x_assum ‘∀p._ |-^ _ ⇒ _’ irule >> rw[pENTAIL_def] >>
          qexists_tac ‘[CONJl γ --> A]’ >> rw[CONJl_def] >>
          metis_tac[goldblatt_provable_rules, g_A_CONJl_A]
         )
      >- (‘CONJl (α::FILTER (λx. x ≠ C) γ) = α & CONJl (FILTER (λx. x ≠ C) γ)’ by
            (Cases_on ‘FILTER (λx. x ≠ C) γ’ >> gs[CONJl_def]) >>
          gs[S_Theory_def, Ordinary_def, Regular_def, R_Theory_def] >>
          qpat_assum ‘∀p._ |-^ _ ⇒ _’ irule >> rw[pENTAIL_def] >>
          qexists_tac ‘[CONJl (FILTER (λx. x ≠ C) γ) & C --> A]’ >>
          rw[CONJl_def]
          >- (qpat_assum ‘∀p._ |-^ _ ⇒ _’ irule >> rw[pENTAIL_def] >>
              qexists_tac ‘[CONJl γ --> A]’ >> simp[CONJl_def] >>
              irule g_modus_ponens >>
              qexists_tac ‘CONJl (FILTER (λx. x ≠ C) γ) & C --> CONJl γ’ >>
              simp[g_suffixing] >> Cases_on ‘MEM C γ’
              >- gs[FILTER_AND_FILTERED_IMP_CONJl]
              >- metis_tac[goldblatt_provable_rules, FILTER_NON_MEM_EQUAL]
             )
          >- (irule g_modus_ponens >>
              qexists_tac
              ‘(α & (CONJl (FILTER (λx. x ≠ C) γ) & C) --> A) -->
               (α & CONJl (FILTER (λx. x ≠ C) γ) & C --> A)’ >>
              reverse $ strip_tac >> metis_tac[goldblatt_provable_rules, g_AND_associative_rl]
             )
         )
     )
QED

Theorem Prime_B_WORLD:
  ∀A w x y z.¬ |- A ∧
           Prime z ∧ S_Theory (Theta A) w ∧
           APPLYING w (B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)}) ⊆ z
           ⇒
           Prime (B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)})
Proof
  rpt strip_tac >> assume_tac S_Theory_B_WORLD >>
  last_x_assum $ qspecl_then [‘A’, ‘w’, ‘x’, ‘y’, ‘z’] strip_assume_tac >>
  gs[] >> rw[Prime_def]
  >- metis_tac[S_Theory_imp_R_Theory]
  >- (CCONTR_TAC >> gs[] >>
      rename[‘C V D ∈ B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)}’] >>
      ‘B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)} ≠ ∅’ by metis_tac[MEMBER_NOT_EMPTY] >>
      assume_tac B_WORLD_prop_exists >>
      last_assum $ qspecl_then [‘A’, ‘APPLYING x y’, ‘w’, ‘z’, ‘C’] strip_assume_tac >>
      last_x_assum $ qspecl_then [‘A’, ‘APPLYING x y’, ‘w’, ‘z’, ‘D’] strip_assume_tac >> gs[] >>
      rename[‘C V D ∈ B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)}’,
             ‘c & C --> α ∈ w’, ‘d & D --> β ∈ w’] >>
      ‘c & d & (C V D) --> α V β ∈ w’ suffices_by
        (CCONTR_TAC >> gs[] >>
         ‘α V β ∈ z’ by
           (qpat_x_assum ‘_ ⊆ z’ mp_tac >> rw[Once SUBSET_DEF, Once APPLYING_def] >>
            last_x_assum irule >> qexists_tac ‘[c & d; C V D]’ >>
            simp[CONJl_def] >> qpat_x_assum ‘S_Theory _ (B_WORLD _ _ _)’ mp_tac >>
            rw[S_Theory_def, sENTAILS_def] >> last_x_assum irule >>
            qexists_tac ‘[c; d]’ >> simp[CONJl_def] >> metis_tac[Ordinary_def, Regular_def, g_identity]
           ) >> metis_tac[Prime_def]
        ) >>
      qpat_x_assum ‘ S_Theory (Theta A) w’ mp_tac >>
      rw[S_Theory_def, sENTAILS_def] >>
      ‘c & C --> α V β ∈ w’ by
        (last_assum irule >> qexists_tac ‘[c & C --> α]’ >>
         simp[CONJl_def] >> gs[Ordinary_def, Regular_def] >>
         last_x_assum irule >> metis_tac[goldblatt_provable_rules, g_permutation]
        ) >>
      ‘c & d & C --> α V β ∈ w’ by
        (last_assum irule >> qexists_tac ‘[c & C --> α V β]’ >>
         simp[CONJl_def] >> gs[Ordinary_def, Regular_def] >>
         last_x_assum irule >>
         metis_tac[goldblatt_provable_rules, g_permutation, g_AND_associative_rl, g_AND_associative_lr, g_AND_STRENGTHEN]
        ) >>
      ‘d & D --> α V β ∈ w’ by
        (last_assum irule >> qexists_tac ‘[d & D --> β]’ >>
         simp[CONJl_def] >> gs[Ordinary_def, Regular_def] >>
         last_x_assum irule >> metis_tac[goldblatt_provable_rules, g_permutation]
        ) >>
      ‘c & d & D --> α V β ∈ w’ by
        (last_assum irule >> qexists_tac ‘[d & D --> α V β]’ >>
         simp[CONJl_def] >> gs[Ordinary_def, Regular_def] >>
         last_x_assum irule >>
         metis_tac[goldblatt_provable_rules, g_permutation, g_AND_associative_rl, g_AND_associative_lr, g_AND_STRENGTHEN]
        ) >>
      last_x_assum irule >> qexists_tac ‘[ c & d & C --> α V β; c & d & D --> α V β]’ >>
      simp[CONJl_def] >> gs[Ordinary_def, Regular_def] >> last_x_assum irule >>
      metis_tac [g_suffixing, g_modus_ponens, g_adjunction_rule, g_distribution, g_disjunction_elim]
     )
QED

Theorem Canonical_Frame_is_R_Frame:
  ∀A. ¬|- A ⇒ R_Frame (Canonical_Frame A)
Proof
  simp[R_Frame_def] >> rpt strip_tac >>
  gs[Canonical_Frame_def] >>
  ‘Ordinary (Theta A)’ by simp[Theta_Ordinary] (* 9 *)
  >- gs[Ordinary_def, Theta_Theta_theory]
  >- (assume_tac STAR_IN_CANONICAL_FRAME >> gs[Canonical_Frame_def] >> metis_tac[])
  >- (gs[Theta_Theta_theory, Ordinary_def] >> rw[APPLYING_def, SUBSET_DEF] >>
      rename [‘q ∈ x’] >> gs[S_Theory_def, sENTAILS_def] >> last_x_assum irule >>
      qexists_tac ‘γ’ >> simp [SUBSET_DEF]
     )
  >- (‘x' ⊆ x’ by
        (gs[APPLYING_def, SUBSET_DEF] >> rw[] >> last_x_assum irule >>
         rename [‘B ∈ t’] >> qexists_tac ‘[B]’ >> gs[CONJl_def, Ordinary_def, Regular_def, g_identity]
        ) >>
      ‘y' ⊆ y’ by
        (gs[APPLYING_def, SUBSET_DEF] >> rw[] >> last_x_assum irule >>
         rename [‘B ∈ t’] >> qexists_tac ‘[B]’ >> gs[CONJl_def, Ordinary_def, Regular_def, g_identity]
        ) >>
      ‘z ⊆ z'’ by
        (gs[APPLYING_def, SUBSET_DEF] >> rw[] >> last_x_assum irule >>
         rename [‘B ∈ t’] >> qexists_tac ‘[B]’ >> gs[CONJl_def, Ordinary_def, Regular_def, g_identity]
        ) >>
      ‘APPLYING x' y' ⊆ z’ suffices_by gs[SUBSET_DEF] >>
      rw[APPLYING_def, SUBSET_DEF] >>
      rename [‘B ∈ z’] >> qpat_x_assum ‘APPLYING x y ⊆ z’ mp_tac >>
      rw[APPLYING_def, SUBSET_DEF] >> pop_assum irule >> qexists_tac ‘γ’ >>
      gs[SUBSET_DEF]
     )
  >- (assume_tac Canonical_Frame_STAR_STAR >> gs[Canonical_Frame_def] >>
      metis_tac[]
     )
  >- (‘(Canonical_Frame A).STAR x ∈ (Canonical_Frame A).W’ by
        simp[STAR_IN_CANONICAL_FRAME, Canonical_Frame_def] >>
      ‘(Canonical_Frame A).STAR y ∈ (Canonical_Frame A).W’ by
        simp[STAR_IN_CANONICAL_FRAME, Canonical_Frame_def] >>
      gs[Canonical_Frame_def] >> simp[APPLYING_def, SUBSET_DEF] >>
      rpt strip_tac >> rename [‘~a ∈ x’] >>
      qpat_x_assum ‘∀x. MEM x γ ⇒ ~x ∉ y’ mp_tac >> gs[] >>
      ‘~a --> ~CONJl γ ∈ w’ by (
        qpat_x_assum ‘S_Theory (Theta A) w’ mp_tac >>
        rw[S_Theory_def, sENTAILS_def] >> pop_assum irule >>
        qexists_tac ‘[CONJl γ --> a]’ >> simp [CONJl_def, SUBSET_DEF] >>
        ‘|- ((CONJl γ --> a) --> ~a --> ~CONJl γ)’ suffices_by gs[Ordinary_def, Regular_def] >>
        metis_tac[g_contrapositive_alt, g_DIMP_def, goldblatt_provable_rules]
        ) >>
      ‘~CONJl γ ∈ y’ by
        (gs[APPLYING_def, SUBSET_DEF] >> last_x_assum irule >>
         qexists_tac ‘[~a]’ >> simp[CONJl_def]
        ) >> irule CONJl_NOTIN_PRIME >> gs[]
     )
  >- (rw[APPLYING_def, SUBSET_DEF] >> rename[‘a ∈ x’] >>
      gs[S_Theory_def, sENTAILS_def] >> last_x_assum irule >>
      qexists_tac ‘[CONJl γ; (CONJl γ --> a)]’ >> gs[CONJl_def] >>
      gs[CONJl_IN_R_Theory_IMP, Prime_def, g_AND_MP, Ordinary_def, Regular_def, SUBSET_DEF]
     )
  >- (rw[APPLYING_def, SUBSET_DEF] >> rename[‘a ∈ z’] >>
      qpat_x_assum ‘APPLYING x y ⊆ z’ mp_tac >> rw[APPLYING_def, SUBSET_DEF] >>
      pop_assum irule >> qexists_tac ‘[CONJl γ --> a]’ >> simp[CONJl_def] >>
      gs[S_Theory_def] >> last_x_assum irule >> simp[sENTAILS_def] >>
      qexists_tac ‘γ’ >> gs[SUBSET_DEF, Ordinary_def, Regular_def, g_assertion]
     )
  >- (qexists_tac ‘B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)}’ >>
      ‘APPLYING x y ⊆
       B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)}’ by
        (rw[B_WORLD_def, BIGUNION, PULL_EXISTS, SUBSET_DEF] >> qexists_tac ‘0’ >>
         gs[B_WORLD_i_def]
        ) >>
      ‘APPLYING w
       (B_WORLD (Theta A) (APPLYING x y) {p | (∃q. p --> q ∈ w ∧ q ∉ z)}) ⊆ z’ by (
        rw[Once SUBSET_DEF, Once APPLYING_def] >>
        rename[‘β ∈ z’] >> assume_tac FINITE_SUBSET_B_WORLD >>
        pop_assum $ qspecl_then [‘set γ’, ‘Theta A’, ‘APPLYING x y’,
                                 ‘{p | (∃q. p --> q ∈ w ∧ q ∉ z)}’]
                  strip_assume_tac >> gs[] >>
        Induct_on ‘n’ >> simp[B_WORLD_i_def]
        >- (rw[] >> ‘CONJl γ ∈ APPLYING x y’ by metis_tac[CONJl_IN_APPLIED] >>
            pop_assum mp_tac >>
            qpat_x_assum ‘APPLYING w x ⊆ a’ mp_tac >>
            qpat_x_assum ‘APPLYING a y ⊆ z’ mp_tac >>
            rw[APPLYING_def, SUBSET_DEF] >>
            rename[‘∀x. MEM x δ ⇒ x ∈ y’] >>
            last_x_assum irule >> qexists_tac ‘δ’ >>
            simp[] >> last_x_assum irule >>
            qexists_tac ‘[CONJl δ --> CONJl γ]’ >> simp[CONJl_def] >>
            ‘|- ((CONJl γ --> β)  --> (CONJl δ --> CONJl γ) --> CONJl δ --> β)’ by
              metis_tac [goldblatt_provable_rules, g_permutation] >>
            gs[S_Theory_def] >> last_x_assum irule >> simp[sENTAILS_def] >>
            qexists_tac ‘[CONJl γ --> β]’ >> gs[CONJl_def, Ordinary_def, Regular_def]
           )
        >- (rw[] >>
            CCONTR_TAC >>
            qpat_x_assum
            ‘¬∃A'.
                (∃q. A' --> q ∈ w ∧ q ∉ z) ∧
                sENTAILS (Theta A)
                         (B_WORLD_i n (Theta A) (APPLYING x y)
                          {p | (∃q. p --> q ∈ w ∧ q ∉ z)} ∪ {LINV R_gn 𝕌(:g_prop) n}) A'’ mp_tac >>
            simp[] >> qexists_tac ‘CONJl γ’ >> rw[]
            >- metis_tac[]
            >- (simp[sENTAILS_def] >> qexists_tac ‘γ’ >> gs[Ordinary_def, Regular_def, g_identity, CONJl_def]
               )
           )
        ) >>
      drule_then strip_assume_tac S_Theory_B_WORLD >>
      last_x_assum $ qspecl_then [‘w’, ‘x’, ‘y’, ‘z’] strip_assume_tac >>
      gs[] >> irule Prime_B_WORLD >> gs[])
QED

Definition Canonical_Model_def:
  Canonical_Model A =
    <|RF := Canonical_Frame A;
      VF := λx. {w | g_VAR x ∈ w}|>
End

Theorem Canonical_Model_is_R_Model:
  ∀A. ¬|-A ⇒ R_Model (Canonical_Model A)
Proof
  rw[R_Model_def, Canonical_Frame_is_R_Frame, Canonical_Model_def, Hereditary_def] >>
  gs[Canonical_Frame_def, SUBSET_DEF] >> last_x_assum irule >> simp[APPLYING_def] >>
  qexists_tac ‘[g_VAR s]’ >> simp[CONJl_def] >>
  gs[S_Theory_def, Ordinary_def, Regular_def, g_identity]
QED




Definition X_WORLD_i_def:
  X_WORLD_i 0 Θ S R w = S ∧
  X_WORLD_i (SUC n) Θ S R w =
  if (∃A. A ∈ R ∧ sENTAILS Θ (APPLYING w (X_WORLD_i n Θ S R w ∪ {LINV R_gn UNIV n})) A)
  then X_WORLD_i n Θ S R w
  else X_WORLD_i n Θ S R w ∪ {LINV R_gn UNIV n}
End

Definition X_WORLD_def:
  X_WORLD Θ S R w = BIGUNION {X_WORLD_i n Θ S R w | n ∈ UNIV}
End

Definition Y_WORLD_i_def:
  Y_WORLD_i 0 Θ S R = S ∧
  Y_WORLD_i (SUC n) Θ S R =
  if (∃A. A ∈ R ∧ sENTAILS Θ (Y_WORLD_i n Θ S R ∪ {LINV R_gn UNIV n}) A)
  then Y_WORLD_i n Θ S R
  else Y_WORLD_i n Θ S R ∪ {LINV R_gn UNIV n}
End

Definition Y_WORLD_def:
  Y_WORLD Θ S R = BIGUNION {Y_WORLD_i n Θ S R | n ∈ UNIV}
End

Theorem X_WORLD_i_grows:
  ∀ e n m Θ A R w. e ∈ X_WORLD_i n Θ A R w ∧ n ≤ m ⇒
                   e ∈ X_WORLD_i m Θ A R w
Proof
  rpt strip_tac >> Induct_on ‘m’
  >- (rpt strip_tac >> gs[X_WORLD_i_def])
  >> Cases_on ‘n = SUC m’ >> strip_tac
  >- gs[]
  >> ‘n ≤ m’ by decide_tac >> gs[X_WORLD_i_def] >> rw[]
QED

Theorem FINITE_SUBSET_X_WORLD:
  ∀s Θ A R w. FINITE s ⇒ (s ⊆ X_WORLD Θ A R w ⇔ ∃n. s ⊆ X_WORLD_i n Θ A R w)
Proof
  Induct_on ‘FINITE’ >> simp[] >>
  rpt strip_tac >> simp[X_WORLD_def, PULL_EXISTS] >> reverse eq_tac
  >- metis_tac[]
  >> rpt strip_tac >>
  rename [‘e ∈ X_WORLD_i m Θ I' R w’,
          ‘s ⊆ X_WORLD_i n Θ I' R w’] >>
  Cases_on ‘m ≤ n’
  >- metis_tac[X_WORLD_i_grows]
  >> ‘n < m’ by decide_tac >>
  qexists_tac ‘m’ >> simp[SUBSET_DEF] >> rpt strip_tac >>
  irule X_WORLD_i_grows >> qexists_tac ‘n’ >> gs[] >>
  metis_tac[SUBSET_DEF]
QED

Theorem X_WORLD_condition:
  ∀p w A B. ¬|- p ∧ B ∈ APPLYING w (X_WORLD (Theta p) {A} {B} w) ⇒
  ∃γ. CONJl γ --> B ∈ w ∧ set γ ⊆ {A} ∧ γ ≠ []
Proof
  rw[APPLYING_def] >> qexists_tac ‘γ’ >>
  simp[] >> CCONTR_TAC >> qpat_x_assum ‘CONJl γ --> B ∈ w’ mp_tac >> gs[] >>
  assume_tac FINITE_SUBSET_X_WORLD >>
  last_x_assum $ qspecl_then [‘set γ’, ‘Theta p’, ‘{A}’, ‘{B}’, ‘w’] strip_assume_tac >> gs[] >>
  Induct_on ‘n’
  >- (rw[X_WORLD_i_def])
  >- (rw[X_WORLD_i_def] >> CCONTR_TAC >>
      qpat_x_assum ‘¬sENTAILS (Theta p)
                    (APPLYING w
                     (X_WORLD_i n (Theta p) {A} {B} w ∪ {LINV R_gn 𝕌(:g_prop) n})) B’ mp_tac >>
      gs[sENTAILS_def] >> qexists_tac ‘[B]’ >> rw[]
      >- (simp[APPLYING_def] >> metis_tac[])
      >- (simp[CONJl_def] >> metis_tac[Theta_Ordinary, Ordinary_def, Regular_def, g_identity])
     )
QED

Theorem APPLIED_X_WORLD_i_GROWS:
  ∀ x n m. n ≤ m ∧ x ∈ APPLYING w (X_WORLD_i n (Theta p) {A} {B} w) ⇒
       x ∈ APPLYING w (X_WORLD_i m (Theta p) {A} {B} w)
Proof
  rw[APPLYING_def] >>
  qexists_tac ‘γ’ >> gs[SUBSET_DEF] >> rw[] >>
  irule X_WORLD_i_grows >> qexists_tac ‘n’ >> gs[]
QED

Theorem FINITE_APPLIED_SUBSET:
  ∀ γ. FINITE γ ⇒ (γ ⊆ APPLYING w (X_WORLD (Theta p) {A} {B} w) ⇔
                     ∃n. γ ⊆ APPLYING w (X_WORLD_i n (Theta p) {A} {B} w)
                  )
Proof
  Induct_on ‘FINITE’ >> rw[EQ_IMP_THM] (* 3 *)
  >- (‘∃m. e ∈ APPLYING w (X_WORLD_i m (Theta p) {A} {B} w)’ by
        (gs[APPLYING_def] >> assume_tac FINITE_SUBSET_X_WORLD >>
         pop_assum $ qspec_then ‘set γ'’ strip_assume_tac >> gs[] >>
         qexistsl_tac [‘n'’, ‘γ'’] >> gs[]
        ) >> gs[] >>
      Cases_on ‘n ≤ m’
      >- (qexists_tac ‘m’ >> gs[SUBSET_DEF] >> rw[] >>
          last_x_assum $ qspec_then ‘x’ strip_assume_tac >> gs[] >>
          metis_tac[APPLIED_X_WORLD_i_GROWS]
         )
      >- (‘m ≤ n’ by decide_tac >> qexists_tac ‘n’ >> rw[] >>
          metis_tac [APPLIED_X_WORLD_i_GROWS]
       )
     )
  >- (gs[X_WORLD_def, BIGUNION, PULL_EXISTS, APPLYING_def] >> qexists_tac ‘γ'’ >>
      gs[SUBSET_DEF] >> rw[] >> qexists_tac ‘n’ >> simp[]
     )
  >- (gs[X_WORLD_def, BIGUNION, PULL_EXISTS, APPLYING_def, SUBSET_DEF] >>
      rw[] >> first_x_assum $ qspec_then ‘x’ strip_assume_tac >> gs[] >>
      qexists_tac ‘γ''’ >> rw[] >> qexists_tac ‘n’ >> simp[]
     )
QED

Theorem FINITE_X_WORLD_i:
  ∀n θ a b w. FINITE (X_WORLD_i n θ {a} {b} w)
Proof
  Induct >> rw[X_WORLD_i_def]
QED

Theorem NOT_EMPTY_X_WORLD_i:
  ∀n θ a b w. X_WORLD_i n θ {a} {b} w ≠ ∅
Proof
  Induct >> rw[X_WORLD_i_def]
QED

Theorem APPLYING_TO_FINITE:
  ∀ w θ x γ p. FINITE x ∧ set γ = x ∧ S_Theory θ w ∧ p ∈ APPLYING w x ⇒
             CONJl γ --> p ∈ w
Proof
  rw[APPLYING_def] >>
  drule_then strip_assume_tac S_Theory_imp_R_Theory >>
  gs[R_Theory_def, pENTAIL_def] >> last_assum irule >>
  qexists_tac ‘[CONJl γ' --> p]’ >> gs[CONJl_def] >>
  irule g_modus_ponens >> qexists_tac ‘CONJl γ --> CONJl γ'’ >>
  gs[g_suffixing] >> irule IMP_MEM_IMP_CONJl >>
  metis_tac[CONJl_MEM_IMP, SUBSET_DEF]
QED


Theorem APPLIED_S_THEORY_alt:
  ∀θ w x. S_Theory θ w ⇒
  S_Theory θ (APPLYING w x)
Proof
  rpt strip_tac >> rw[S_Theory_def]
  >- gs[S_Theory_def]
  >- (gs[sENTAILS_def] >>
      drule_all_then strip_assume_tac CONJl_IN_APPLIED >>
      gs[APPLYING_def] >> rename[‘CONJl δ --> CONJl γ ∈ w’] >>
      qexists_tac ‘δ’ >> gs[S_Theory_def] >> last_x_assum irule >>
      simp[sENTAILS_def] >> qexists_tac ‘[CONJl δ --> CONJl γ]’ >>
      simp[CONJl_def] >> gs[Ordinary_def, Prime_def,
                            R_Theory_def, pENTAIL_def] >>
      last_x_assum irule >>
      qexists_tac ‘[CONJl γ --> p]’ >> simp[CONJl_def] >>
      metis_tac[g_suffixing, g_permutation, g_modus_ponens])
QED

Theorem APPLIED_S_THEORY:
  ∀p w x. ¬ |- p ∧ S_Theory (Theta p) w ⇒
  S_Theory (Theta p) (APPLYING w x)
Proof
  rpt strip_tac >> rw[S_Theory_def]
  >- metis_tac[Theta_Ordinary]
  >- (gs[sENTAILS_def] >>
      drule_all_then strip_assume_tac CONJl_IN_APPLIED >>
      gs[APPLYING_def] >> rename[‘CONJl δ --> CONJl γ ∈ w’] >>
      qexists_tac ‘δ’ >> gs[S_Theory_def] >> last_x_assum irule >>
      simp[sENTAILS_def] >> qexists_tac ‘[CONJl δ --> CONJl γ]’ >>
      simp[CONJl_def] >> drule_then strip_assume_tac Theta_R_Theory >>
      gs[R_Theory_def, pENTAIL_def] >> last_x_assum irule >>
      qexists_tac ‘[CONJl γ --> p']’ >> simp[CONJl_def] >>
      metis_tac[g_suffixing, g_permutation, g_modus_ponens])
QED

Theorem Y_WORLD_i_grows:
  ∀ e n m Θ A R. e ∈ Y_WORLD_i n Θ A R ∧ n ≤ m ⇒
                   e ∈ Y_WORLD_i m Θ A R
Proof
  rpt strip_tac >> Induct_on ‘m’
  >- (rpt strip_tac >> gs[Y_WORLD_i_def])
  >> Cases_on ‘n = SUC m’ >> strip_tac
  >- gs[]
  >> ‘n ≤ m’ by decide_tac >> gs[Y_WORLD_i_def] >> rw[]
QED

Theorem FINITE_SUBSET_Y_WORLD:
    ∀s Θ A R. FINITE s ⇒ (s ⊆ Y_WORLD Θ A R ⇔ ∃n. s ⊆ Y_WORLD_i n Θ A R)
Proof
  Induct_on ‘FINITE’ >> simp[] >>
  rpt strip_tac >> simp[Y_WORLD_def, PULL_EXISTS] >> reverse eq_tac
  >- metis_tac[]
  >> rpt strip_tac >>
  rename [‘e ∈ Y_WORLD_i m Θ I' R’,
          ‘s ⊆ Y_WORLD_i n Θ I' R’] >>
  Cases_on ‘m ≤ n’
  >- metis_tac[Y_WORLD_i_grows]
  >> ‘n < m’ by decide_tac >>
  qexists_tac ‘m’ >> simp[SUBSET_DEF] >> rpt strip_tac >>
  irule Y_WORLD_i_grows >> qexists_tac ‘n’ >> gs[] >>
  metis_tac[SUBSET_DEF]
QED

Theorem X_WORLD_THETA_THEORY:
  ¬ |- p ∧ S_Theory (Theta p) w ∧ A --> B ∉ w ⇒
  S_Theory (Theta p) (X_WORLD (Theta p) {A} {B} w)
Proof
  rpt strip_tac >>
  rw[S_Theory_def, sENTAILS_def, Theta_Ordinary] >>
  rename[‘CONJl γ --> D ∈ Theta p’] >>
  simp[X_WORLD_def, PULL_EXISTS] >>
  qexists_tac ‘SUC (R_gn D)’ >>
  simp[X_WORLD_i_def] >>
  ‘LINV R_gn 𝕌(:g_prop) (R_gn D) = D’ by (
    ‘D ∈ 𝕌(:g_prop)’ by simp[] >>
    ‘INJ R_gn 𝕌(:g_prop)  𝕌(:num)’ by simp[INJ_DEF] >>
    metis_tac [LINV_DEF]
    ) >> simp[] >>
  ‘¬ sENTAILS (Theta p) (APPLYING w (X_WORLD_i (R_gn D) (Theta p) {A} {B} w ∪ {D})) B’
  suffices_by rw[] >>
  CCONTR_TAC >> gs[sENTAILS_def] >>
  rename [‘CONJl δ --> B ∈ Theta p’] >>
  drule_all_then strip_assume_tac CONJl_IN_APPLIED >>
  ‘∃l. set l = X_WORLD_i (R_gn D) (Theta p) {A} {B} w’ by
    (irule FINITE_EXISTS_LIST >> simp[FINITE_X_WORLD_i]
    ) >>
  ‘l ++ γ ≠ [] ∧ set (l ++ γ) ⊆ X_WORLD (Theta p) {A} {B} w ∧ CONJl (l ++ γ) --> D ∈ Theta p’ by
    (rw[] (* 2 *)
     >- (rw[X_WORLD_def, BIGUNION, SUBSET_DEF, PULL_EXISTS] >> metis_tac[])
     >- (‘Ordinary (Theta p)’ by gs[Theta_Ordinary] >>
         gs[Ordinary_def, Prime_def, R_Theory_def, pENTAIL_def] >>
         last_x_assum irule >> qexists_tac ‘[CONJl γ --> D]’ >>
         gs[CONJl_def] >>
         irule g_modus_ponens >>
         qexists_tac ‘(CONJl l & CONJl γ) --> CONJl γ’ >>
         gs[g_conjunction_r] >>
         irule g_modus_ponens >>
         qexists_tac ‘CONJl (l ++ γ) --> (CONJl l & CONJl γ)’ >> rw[]
         >- (‘l ≠ []’ by
               (CCONTR_TAC >>
                gs[NOT_EMPTY_X_WORLD_i]
               ) >>
             assume_tac CONJl_split >>
             pop_assum $ qspecl_then [‘l’, ‘γ’] strip_assume_tac >>
             metis_tac [goldblatt_provable_rules]
            )
         >- metis_tac[g_suffixing, g_permutation, g_modus_ponens]
        )
    ) >>
  ‘(CONJl (l ⧺ γ) & D --> CONJl δ) ∈ w’ by
    (‘CONJl l & D --> CONJl δ ∈ w’ by (
      ‘CONJl (l ++ [D]) --> CONJl δ ∈ w’ suffices_by (
        rw[] >>
        ‘R_Theory w’ by (gs[Canonical_Frame_def] >> metis_tac[S_Theory_imp_R_Theory]) >>
        gs[R_Theory_def, pENTAIL_def] >> last_x_assum irule >>
        qexists_tac ‘[CONJl (l ⧺ [D]) --> CONJl δ]’ >> gs[CONJl_def] >>
        irule g_modus_ponens >> qexists_tac ‘CONJl l & CONJl [D] --> CONJl (l ⧺ [D])’ >> rw[]
        >- (‘l ≠ []’ by
              (CCONTR_TAC >>
               gs[NOT_EMPTY_X_WORLD_i]
              ) >> gs[CONJl_split]
           )
        >- gs[CONJl_def, g_suffixing]
        ) >>
      irule APPLYING_TO_FINITE >> gs[PULL_EXISTS, Canonical_Frame_def] >>
      metis_tac[]
      ) >>
     ‘R_Theory w’ by metis_tac[S_Theory_imp_R_Theory] >>
     gs[R_Theory_def, pENTAIL_def] >> last_x_assum irule >>
     qexists_tac ‘[CONJl l & D --> CONJl δ]’ >> gs[CONJl_def] >>
     irule g_modus_ponens >> qexists_tac ‘(CONJl (l ⧺ γ) & D) --> CONJl l & D’ >>
     gs[g_suffixing] >>
     ‘l ≠ []’ by
       (CCONTR_TAC >>
        gs[NOT_EMPTY_X_WORLD_i]
       ) >>
     ‘|- (CONJl (l ⧺ γ) --> CONJl l & CONJl γ)’ by metis_tac[CONJl_split] >>
     metis_tac[goldblatt_provable_rules]
    ) >>
  ‘(CONJl (l ++ γ) & D --> CONJl δ) --> CONJl (l ++ γ) --> CONJl δ ∈ Theta p’ by
    (drule_then strip_assume_tac Theta_Ordinary >>
     gs[Ordinary_def, Regular_def] >>
     ‘CONJl (l ++ γ) --> CONJl (l ++ γ) ∈ Theta p’ by simp[g_identity] >>
     ‘CONJl (l ++ γ) --> (CONJl (l ++ γ) & D) ∈ Theta p’ by
       (gs[R_Theory_def, pENTAIL_def] >> last_x_assum irule >>
        qexists_tac ‘[CONJl (l ++ γ) --> CONJl (l ++ γ); CONJl (l ++ γ) --> D]’ >>
        gs[CONJl_def, g_conj_introduction]
       ) >>
     gs[R_Theory_def, pENTAIL_def] >> last_x_assum irule >>
     qexists_tac ‘[CONJl (l ⧺ γ) --> CONJl (l ⧺ γ) & D]’ >>
     gs[CONJl_def, g_suffixing]
    ) >>
  ‘CONJl (l ⧺ γ) --> CONJl δ ∈ w’ by
    (‘S_Theory (Theta p) w’ by gs[Canonical_Frame_def] >>
     gs[S_Theory_def, sENTAILS_def] >> last_x_assum irule >>
     qexists_tac ‘[CONJl (l ⧺ γ) & D --> CONJl δ]’ >>
     gs[CONJl_def]
    ) >>
  ‘¬sENTAILS (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w)) B’ by
    (rw[sENTAILS_def] >>
     rename [‘α = [] ∨ ¬(set α ⊆ APPLYING w (X_WORLD (Theta p) {A} {B} w)) ∨
              CONJl α --> B ∉ Theta p’] >>
     Cases_on ‘α = []’ >> gs[] >>
     Cases_on ‘CONJl α --> B ∉ Theta p’ >> gs[] >>
     assume_tac FINITE_APPLIED_SUBSET >> gs[] >>
     Induct
     >- (gs[X_WORLD_i_def] >> CCONTR_TAC >>
         gs[] >>
         ‘CONJl α ∈ APPLYING w {A}’ by
           metis_tac[CONJl_IN_APPLIED] >>
         pop_assum mp_tac >> simp[APPLYING_def] >> CCONTR_TAC >> gs[] >>
         qpat_x_assum ‘A --> B ∉ w’ mp_tac >> gs[S_Theory_def] >>
         last_x_assum irule >> simp[sENTAILS_def] >> qexists_tac ‘[CONJl γ' --> CONJl α]’ >>
         simp[CONJl_def] >> gs[Ordinary_def, Prime_def, R_Theory_def, pENTAIL_def] >>
         last_x_assum irule >>
         qexists_tac ‘[CONJl α --> B]’ >> gs[CONJl_def] >>
         metis_tac[g_modus_ponens, g_suffixing, g_permutation, g_A_CONJl_A]
        )
     >- (rw[X_WORLD_i_def] >>
         CCONTR_TAC >>
         qpat_x_assum ‘¬sENTAILS _ _ _’ mp_tac >>
         gs[] >> simp[sENTAILS_def] >> metis_tac[]
        )
    ) >>
  pop_assum mp_tac >> rw[sENTAILS_def] >>
  qexists_tac ‘[CONJl δ]’ >> rw[CONJl_def, APPLYING_def] >>
  metis_tac[]
QED

Theorem X_WORLD_prop_exists:
  ∀w p A B a. ¬ |- p ∧ S_Theory (Theta p) w ∧ Prime w ∧
              A --> B ∉ w ∧ a ∉ X_WORLD (Theta p) {A} {B} w ⇒
              ∃c γ. c ∈ X_WORLD (Theta p) {A} {B} w ∧
                    c & a --> CONJl γ ∈ w ∧ CONJl γ --> B ∈ (Theta p)
Proof
  rpt strip_tac >> CCONTR_TAC >>
  qpat_x_assum ‘a ∉ X_WORLD (Theta p) {A} {B} w’ mp_tac >> gs[] >>
  ‘{a} ⊆ X_WORLD (Theta p) {A} {B} w’ suffices_by gs[] >>
  irule (iffRL FINITE_SUBSET_X_WORLD) >> simp[] >>
  qexists_tac ‘SUC (R_gn a)’ >> simp[X_WORLD_i_def] >>
  ‘¬ sENTAILS (Theta p)
   (APPLYING w
    (X_WORLD_i (R_gn a) (Theta p) {A} {B} w ∪
     {a})) B’ suffices_by
    (‘LINV R_gn 𝕌(:g_prop) (R_gn a) = a’ by (
      ‘a ∈ 𝕌(:g_prop)’ by simp[] >>
      ‘INJ R_gn 𝕌(:g_prop)  𝕌(:num)’ by simp[INJ_DEF] >>
      metis_tac [LINV_DEF]
      ) >> gs[]
    ) >> rw[sENTAILS_def] >>
  CCONTR_TAC >> gs[] >>
  drule_all_then mp_tac CONJl_IN_APPLIED >>
  simp[APPLYING_def] >> CCONTR_TAC >> gs[] >>
  qpat_x_assum ‘∀ c γ. _’ mp_tac >> simp[] >>
  rename [‘CONJl δ --> CONJl γ ∈ w’] >>
  qexistsl_tac [‘CONJl (A::(FILTER (λx. x ≠ a) δ))’, ‘γ’] >> rw[] (* 2 *)
  >- (‘set (A::FILTER (λx. x ≠ a) δ) ⊆ X_WORLD (Theta p) {A} {B} w’ suffices_by (
       rw[] >>
       ‘R_Theory (X_WORLD (Theta p) {A} {B} w)’ by
         metis_tac[S_Theory_imp_R_Theory, X_WORLD_THETA_THEORY] >>
       assume_tac CONJl_IN_R_Theory_IMP >>
       pop_assum $ qspecl_then [‘X_WORLD (Theta p) {A} {B} w’, ‘A::FILTER (λx. x ≠ a) δ’] strip_assume_tac >>
       Cases_on ‘FILTER (λx. x ≠ a) δ = []’ >> gs[CONJl_def]
       ) >>
      gs[SUBSET_DEF] >> rw[]
      >- (simp[X_WORLD_def, PULL_EXISTS] >> qexists_tac ‘0’ >> simp[X_WORLD_i_def])
      >- (Cases_on ‘x = a’
          >- metis_tac[NOT_MEM_FILTER_LEMMA, MEM_FILTER_LEMMA]
          >- (simp[X_WORLD_def, PULL_EXISTS] >> qexists_tac ‘R_gn a’ >>
               metis_tac[NOT_MEM_FILTER_LEMMA, MEM_FILTER_LEMMA])
         )
     )
  >- (‘CONJl (FILTER (λx. x ≠ a) δ) & a --> CONJl γ ∈ w’ suffices_by
        (rw[] >> Cases_on ‘FILTER (λx. x ≠ a) δ = []’ >> gs[CONJl_def] (* 2 *)
         >- (‘set δ ⊆ {a}’ by gs[EMPTY_FILTER_LEMMA] >>
             gs[S_Theory_def, sENTAILS_def] >> last_x_assum irule >>
             qexists_tac ‘[CONJl δ --> CONJl γ]’ >> rw[CONJl_def] >>
             qpat_x_assum ‘Ordinary θ’ mp_tac >>
             rw[Ordinary_def, Regular_def, SUBSET_DEF] >> last_x_assum irule >>
             metis_tac[goldblatt_provable_rules, g_A_CONJl_A]
            )
         >- (‘CONJl (A::FILTER (λx. x ≠ a) δ) = A & CONJl (FILTER (λx. x ≠ a) δ)’ by
               (Cases_on ‘FILTER (λx. x ≠ a) δ’ >> gs[CONJl_def]) >>
             ‘R_Theory w’ by metis_tac [S_Theory_imp_R_Theory] >>
             gs[R_Theory_def, pENTAIL_def] >> last_assum irule >>
             qexists_tac ‘[CONJl (FILTER (λx. x ≠ a) δ) & a --> CONJl γ]’ >>
             rw[CONJl_def, g_AND_STRENGTHEN] >> irule g_modus_ponens >>
             qexists_tac
             ‘(A & (CONJl (FILTER (λx. x ≠ a) δ) & a) --> CONJl γ) -->
              (A & CONJl (FILTER (λx. x ≠ a) δ) & a --> CONJl γ)’ >>
             reverse $ strip_tac >> metis_tac[goldblatt_provable_rules, g_AND_associative_rl]
            )
        ) >>
      Cases_on ‘FILTER (λx. x ≠ a) δ = []’ (* 2 *)
      >- (‘set δ ⊆ {a}’ by gs[EMPTY_FILTER_LEMMA] >>
          ‘R_Theory w’ by metis_tac[S_Theory_imp_R_Theory] >>
          gs[R_Theory_def, pENTAIL_def] >> last_assum irule >>
          qexists_tac ‘[a --> CONJl γ]’ >> gs[g_AND_STRENGTHEN, CONJl_def] >>
          last_assum irule >> qexists_tac ‘[CONJl δ --> CONJl γ]’ >> gs[CONJl_def] >>
          metis_tac[goldblatt_provable_rules, g_A_CONJl_A]
         )
      >- (‘R_Theory w’ by metis_tac[S_Theory_imp_R_Theory] >>
          gs[R_Theory_def, pENTAIL_def] >>
          pop_assum irule >> qexists_tac ‘[CONJl δ --> CONJl γ]’ >>
          gs[CONJl_def] >> irule g_modus_ponens >>
          qexists_tac ‘(CONJl (FILTER (λx. x ≠ a) δ) & a) --> CONJl δ’ >>
          gs[g_suffixing] >> Cases_on ‘MEM a δ’ (* 2 *)
          >- gs[FILTER_AND_FILTERED_IMP_CONJl]
          >- (‘FILTER (λx. x ≠ a) δ = δ’ by simp[FILTER_NON_MEM_EQUAL] >>
              gs[g_conjunction_l]
             )
         )
     )
QED

Theorem X_WORLD_Prime:
  ∀p θ w A B.
    ¬ |- p ∧ S_Theory (Theta p) w ∧ Prime w ∧ A --> B ∉ w ⇒
    Prime (X_WORLD (Theta p) {A} {B} w)
Proof
  rpt strip_tac >> rw[Prime_def]
  >- (irule S_Theory_imp_R_Theory >> qexists_tac ‘Theta p’ >> gs[X_WORLD_THETA_THEORY])
  >- (rename[‘C V D ∈ X_WORLD (Theta p) {A} {B} w’] >> CCONTR_TAC >>
      gs[] >> assume_tac X_WORLD_prop_exists >>
      last_x_assum $ qspecl_then [‘w’, ‘p’, ‘A’, ‘B’] strip_assume_tac >>
      gs[] >>
      first_assum $ qspec_then ‘C’ strip_assume_tac >>
      first_x_assum $ qspec_then ‘D’ strip_assume_tac >>
      gs[] >>
      ‘CONJl γ V CONJl γ' --> B ∈ Theta p’ by
        (gs[S_Theory_def, Ordinary_def, R_Theory_def, Prime_def, pENTAIL_def] >>
         last_x_assum irule >>
         qexists_tac ‘[CONJl γ --> B; CONJl γ' --> B]’ >>
         gs[CONJl_def, g_disjunction_elim]
        ) >>
      rename[‘CONJl γ V CONJl δ --> B ∈ Theta p’, ‘d & D --> CONJl δ ∈ w’] >>
      ‘¬sENTAILS (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w)) B’ suffices_by
        (simp[sENTAILS_def] >> qexists_tac ‘[CONJl γ V CONJl δ]’ >> simp[CONJl_def] >>
         simp[APPLYING_def] >> qexists_tac ‘[c & d; C V D]’ >> simp[CONJl_def] >>
         ‘R_Theory w’ by metis_tac[S_Theory_imp_R_Theory] >> gs[R_Theory_def, pENTAIL_def] >>
         ‘((c & d) & C) --> (CONJl γ V CONJl δ) ∈ w’ by
           (last_x_assum irule >>
            qexists_tac ‘[c & C --> CONJl γ]’ >> gs[CONJl_def] >>
            irule g_modus_ponens >>
            qexists_tac ‘c & d & C --> c & C’ >> rw[]
            >- metis_tac[goldblatt_provable_rules]
            >- (irule g_modus_ponens >>
                qexists_tac ‘CONJl γ --> CONJl γ V CONJl δ’ >> rw[]
                >- metis_tac[goldblatt_provable_rules]
                >- metis_tac[g_modus_ponens, g_permutation, g_suffixing]
               )
           ) >>
         ‘((c & d) & D) --> (CONJl γ V CONJl δ) ∈ w’ by
           (last_x_assum irule >>
            qexists_tac ‘[d & D --> CONJl δ]’ >> gs[CONJl_def] >>
            irule g_modus_ponens >>
            qexists_tac ‘c & d & D --> d & D’ >> rw[]
            >- metis_tac[goldblatt_provable_rules]
            >- (irule g_modus_ponens >>
                qexists_tac ‘CONJl δ --> CONJl γ V CONJl δ’ >> rw[]
                >- metis_tac[goldblatt_provable_rules]
                >- metis_tac[g_modus_ponens, g_permutation, g_suffixing]
               )
           ) >>
         ‘((c & d) & (C V D)) --> (CONJl γ V CONJl δ) ∈ w’ by
           (last_x_assum irule >>
            qexists_tac ‘[((c & d) & C) --> (CONJl γ V CONJl δ);
                          ((c & d) & D) --> (CONJl γ V CONJl δ)]’ >>
            gs[CONJl_def] >>
            metis_tac [g_suffixing, g_modus_ponens, g_adjunction_rule, g_distribution, g_disjunction_elim]
           ) >> rw[] >>
         ‘R_Theory (X_WORLD (Theta p) {A} {B} w)’ by
           metis_tac[S_Theory_imp_R_Theory, X_WORLD_THETA_THEORY] >>
         gs[R_Theory_def, pENTAIL_def] >> last_x_assum irule >>
         qexists_tac ‘[c; d]’ >> gs[CONJl_def] >> simp[g_identity]
        ) >> CCONTR_TAC >> gs[sENTAILS_def] >>
      ‘FINITE (set γ')’ by gs[] >>
      drule_all (iffLR FINITE_APPLIED_SUBSET) >> gs[] >>
      Induct
      >- (simp[X_WORLD_i_def] >> CCONTR_TAC >> gs[] >>
          drule_all_then strip_assume_tac CONJl_IN_APPLIED >>
          qpat_x_assum ‘A --> B ∉ w’ mp_tac >> simp[] >>
          gs[S_Theory_def] >> last_assum irule >> gs[APPLYING_def] >>
          simp[sENTAILS_def] >> qexists_tac ‘[CONJl γ'' --> CONJl γ']’ >>
          simp[CONJl_def] >> gs[Ordinary_def, Prime_def, R_Theory_def] >>
          last_x_assum irule >> simp[pENTAIL_def] >>
          qexists_tac ‘[CONJl γ' --> B]’ >> simp[CONJl_def] >>
          irule g_modus_ponens >> qexists_tac ‘A --> CONJl γ''’ >>
          rw[g_A_CONJl_A] >>
          metis_tac[g_modus_ponens, g_suffixing, g_permutation])
      >- (simp[X_WORLD_i_def] >>
          rw[] >> gs[sENTAILS_def] >> CCONTR_TAC >>
          gs[] >> qpat_x_assum ‘∀γ''. _’ mp_tac >> simp[] >>
          qexists_tac ‘γ'’ >> gs[])
     )
QED

Theorem Y_WORLD_THETA_THEORY:
  ∀p B x.  ¬ |- p ∧ B ∉ x ∧ S_Theory (Theta p) x ⇒
  S_Theory (Theta p) (Y_WORLD (Theta p) x {B})
Proof
  rpt strip_tac >>
  rw[S_Theory_def, sENTAILS_def, Theta_Ordinary] >>
  rename[‘CONJl γ --> D ∈ Theta p’] >>
  simp[Y_WORLD_def, PULL_EXISTS] >>
  qexists_tac ‘SUC (R_gn D)’ >>
  simp[Y_WORLD_i_def] >>
  ‘LINV R_gn 𝕌(:g_prop) (R_gn D) = D’ by (
    ‘D ∈ 𝕌(:g_prop)’ by simp[] >>
    ‘INJ R_gn 𝕌(:g_prop)  𝕌(:num)’ by simp[INJ_DEF] >>
    metis_tac [LINV_DEF]
    ) >> simp[] >>
  ‘¬sENTAILS (Theta p) (Y_WORLD_i (R_gn D) (Theta p) x {B} ∪ {D}) B’
  suffices_by rw[] >>
  CCONTR_TAC >> gs[sENTAILS_def] >>
  rename [‘CONJl δ --> B ∈ Theta p’] >>
  ‘sENTAILS (Theta p) (Y_WORLD (Theta p) x {B}) B’ by
    (simp[sENTAILS_def] >> qexists_tac ‘γ ++ (FILTER (λx. x ≠ D) δ)’ >> rw[] (* 2 *)
     >- (irule (iffRL FINITE_SUBSET_Y_WORLD) >>
         simp[] >> qexists_tac ‘R_gn D’ >> gs[SUBSET_DEF] >> rw[] >>
         drule_all_then strip_assume_tac MEM_FILTER_LEMMA >>
         first_x_assum $ qspec_then ‘x'’ strip_assume_tac >>
         gs[] >> metis_tac[NOT_MEM_FILTER_LEMMA])
     >- (drule_then strip_assume_tac Theta_Theta_theory >>
         gs[S_Theory_def] >> last_x_assum irule >>
         simp[sENTAILS_def] >> qexists_tac ‘[CONJl δ --> B]’ >>
         simp[CONJl_def] >> drule_then strip_assume_tac Theta_R_Theory >>
         gs[R_Theory_def] >> last_assum irule >> simp[pENTAIL_def] >>
         qexists_tac ‘[CONJl (γ ⧺ FILTER (λx. x ≠ D) δ) --> CONJl δ]’ >>
         simp[g_suffixing, CONJl_def] >>
         Cases_on ‘FILTER (λx. x ≠ D) δ = []’ >> gs[]
         >- (last_assum irule >> simp[pENTAIL_def] >>
             qexists_tac ‘[CONJl γ --> D]’ >> simp[CONJl_def] >>
             metis_tac[iffLR EMPTY_FILTER_LEMMA, g_A_CONJl_A, CONJl_def, g_suffixing, g_permutation, g_modus_ponens])
         >- (reverse $ Cases_on ‘MEM D δ’
             >- (gs[FILTER_NON_MEM_EQUAL] >> drule_then strip_assume_tac Theta_Ordinary >>
                 gs[Ordinary_def, Regular_def] >> last_x_assum irule >>
                 metis_tac[goldblatt_provable_rules, CONJl_split])
             >- (last_x_assum irule >> simp[pENTAIL_def] >>
                 qexists_tac ‘[CONJl (γ ++ (FILTER (λx. x ≠ D) δ) ) --> (CONJl (FILTER (λx. x ≠ D) δ) & D)]’ >> simp[CONJl_def] >>
                 rw[CONJl_def]
                 >- (drule_then strip_assume_tac Theta_R_Theory >>
                     gs[R_Theory_def, pENTAIL_def] >> last_assum irule >>
                     qexists_tac ‘[CONJl (γ ⧺ FILTER (λx. x ≠ D) δ) --> CONJl (FILTER (λx. x ≠ D) δ) ;
                                   CONJl (γ ⧺ FILTER (λx. x ≠ D) δ) --> D]’ >>
                     rw[CONJl_def, g_conj_introduction]
                     >-(drule_then strip_assume_tac Theta_Ordinary >>
                        gs[Ordinary_def, Regular_def] >> last_x_assum irule >>
                        assume_tac (CONJl_split |> cj 2) >>
                        last_x_assum $ qspecl_then [‘γ’, ‘ FILTER (λx. x ≠ D) δ’] strip_assume_tac >>
                        metis_tac[g_modus_ponens, g_suffixing, g_permutation, g_conjunction_l, g_conjunction_r])
                     >- (last_x_assum irule >> qexists_tac ‘[CONJl γ --> D]’ >> simp[CONJl_def] >>
                         assume_tac (CONJl_split |> cj 2) >>
                         last_x_assum $ qspecl_then [‘γ’, ‘ FILTER (λx. x ≠ D) δ’] strip_assume_tac >>
                         metis_tac[g_modus_ponens, g_suffixing, g_permutation, g_conjunction_l, g_conjunction_r])
                    )
                 >- (assume_tac FILTER_AND_FILTERED_IMP_CONJl >>
                     last_x_assum $ qspecl_then [‘D’, ‘δ’] strip_assume_tac >> gs[] >>
                     metis_tac[g_suffixing, g_permutation, g_modus_ponens])
                )
            )
        )
    ) >>
  pop_assum mp_tac >> rw[sENTAILS_def] >>
  Cases_on ‘γ' = [] ∨ CONJl γ' --> B ∉ Theta p’ >> gs[] >>
  CCONTR_TAC >> gs[] >>
  ‘FINITE (set γ')’ by gs[] >>
  drule_all_then strip_assume_tac FINITE_SUBSET_Y_WORLD >>
  gs[] >> qpat_x_assum ‘set γ' ⊆ Y_WORLD_i n (Theta p) x {B}’ mp_tac >>
  simp[] >> Induct_on ‘n’ >> simp[Y_WORLD_i_def]
  >- (CCONTR_TAC >> qpat_x_assum ‘B ∉ x’ mp_tac >> gs[S_Theory_def] >>
      last_x_assum irule >> metis_tac[sENTAILS_def])
  >- (rw[] >> rename [‘¬sENTAILS (Theta p) (Y_WORLD_i n (Theta p) x {B} ∪ {q}) B’] >>
      CCONTR_TAC >> gs[] >>
      qpat_x_assum ‘¬sENTAILS (Theta p) (Y_WORLD_i n (Theta p) x {B} ∪ {q}) B’ mp_tac >>
      simp[sENTAILS_def] >> qexists_tac ‘γ'’ >> simp[])
QED

Theorem Y_WORLD_prop_exists:
  ∀x p B a. ¬ |- p ∧  B ∉ x ∧ S_Theory (Theta p) x ∧ a ∉ Y_WORLD (Theta p) x {B} ∧ Y_WORLD (Theta p) x {B} ≠ ∅ ⇒
            ∃c. c ∈ Y_WORLD (Theta p) x {B} ∧ c & a --> B ∈ (Theta p)
Proof
  rpt strip_tac >> CCONTR_TAC >>
  qpat_x_assum ‘a ∉ Y_WORLD (Theta p) x {B}’ mp_tac >> gs[] >>
  ‘{a} ⊆ Y_WORLD (Theta p) x {B}’ suffices_by gs[] >>
  irule (iffRL FINITE_SUBSET_Y_WORLD) >> simp[] >>
  qexists_tac ‘SUC (R_gn a)’ >> simp[Y_WORLD_i_def] >>
  ‘¬sENTAILS (Theta p)
   (Y_WORLD_i (R_gn a) (Theta p) x {B} ∪
    {a}) B’ suffices_by
    (‘LINV R_gn 𝕌(:g_prop) (R_gn a) = a’ by (
      ‘a ∈ 𝕌(:g_prop)’ by simp[] >>
      ‘INJ R_gn 𝕌(:g_prop)  𝕌(:num)’ by simp[INJ_DEF] >>
      metis_tac [LINV_DEF]
      ) >> gs[]
    ) >> rw[sENTAILS_def] >>
  CCONTR_TAC >> gs[] >>
  qpat_x_assum ‘∀ c. _’ mp_tac >> simp[] >>
  drule_then strip_assume_tac (iffRL MEMBER_NOT_EMPTY) >>
  rename [‘A ∈ Y_WORLD (Theta p) x {B}’] >>
  qexists_tac ‘CONJl (A::(FILTER (λx. x ≠ a) γ))’ >> rw[] (* 2 *)
  >- (drule_all_then strip_assume_tac Y_WORLD_THETA_THEORY >>
      drule_all_then strip_assume_tac S_Theory_imp_R_Theory >>
      drule_then irule (iffRL CONJl_IN_R_Theory_IMP) >> rw[] >>
      gs[Y_WORLD_def, PULL_EXISTS, SUBSET_DEF] >>
      rw[] >> qexists_tac ‘R_gn a’ >>
      last_x_assum $ qspec_then ‘x'’ strip_assume_tac >>
      drule_then strip_assume_tac MEM_FILTER_LEMMA >>
      gs[] >> metis_tac[NOT_MEM_FILTER_LEMMA])
  >- (‘CONJl (FILTER (λx. x ≠ a) γ) & a --> B ∈ Theta p’ suffices_by
        (rw[] >> Cases_on ‘FILTER (λx. x ≠ a) γ = []’ >> gs[CONJl_def] (* 2 *)
         >- (‘set γ ⊆ {a}’ by gs[EMPTY_FILTER_LEMMA] >>
             drule_then strip_assume_tac Theta_Ordinary >>
             gs[Ordinary_def, Prime_def, R_Theory_def, pENTAIL_def] >>
             last_assum irule >> qexists_tac ‘[a --> B]’ >> simp[CONJl_def] >>
             simp[g_AND_STRENGTHEN] >> last_x_assum irule >>
             qexists_tac ‘[CONJl γ --> B]’ >> simp[CONJl_def] >>
             metis_tac[goldblatt_provable_rules, g_A_CONJl_A]
            )
         >- (‘CONJl (A::FILTER (λx. x ≠ a) γ) = A & CONJl (FILTER (λx. x ≠ a) γ)’ by
               (Cases_on ‘FILTER (λx. x ≠ a) γ’ >> gs[CONJl_def]) >>
             ‘R_Theory (Theta p)’ by metis_tac [Theta_R_Theory] >>
             gs[R_Theory_def, pENTAIL_def] >> last_assum irule >>
             qexists_tac ‘[CONJl (FILTER (λx. x ≠ a) γ) & a --> B]’ >>
             reverse $ rw[CONJl_def, g_AND_STRENGTHEN] >> irule g_modus_ponens >>
             qexists_tac
             ‘(A & (CONJl (FILTER (λx. x ≠ a) γ) & a) --> B) -->
              (A & CONJl (FILTER (λx. x ≠ a) γ) & a --> B)’ >>
             reverse $ strip_tac >> metis_tac[goldblatt_provable_rules, g_AND_associative_rl])
        ) >>
      Cases_on ‘FILTER (λx. x ≠ a) γ = []’ (* 2 *)
      >- (‘set γ ⊆ {a}’ by gs[EMPTY_FILTER_LEMMA] >>
          ‘R_Theory (Theta p)’ by metis_tac[Theta_R_Theory] >>
          gs[R_Theory_def, pENTAIL_def] >> last_assum irule >>
          qexists_tac ‘[CONJl γ --> B]’ >> gs[g_AND_STRENGTHEN, CONJl_def] >> rw[] >>
          metis_tac[goldblatt_provable_rules, g_A_CONJl_A])
      >- (‘R_Theory (Theta p)’ by metis_tac[Theta_R_Theory] >>
          gs[R_Theory_def, pENTAIL_def] >>
          pop_assum irule >> qexists_tac ‘[CONJl γ --> B]’ >>
          gs[CONJl_def] >> irule g_modus_ponens >>
          qexists_tac ‘(CONJl (FILTER (λx. x ≠ a) γ) & a) --> CONJl γ’ >>
          gs[g_suffixing] >> Cases_on ‘MEM a γ’ (* 2 *)
          >- gs[FILTER_AND_FILTERED_IMP_CONJl]
          >- (‘FILTER (λx. x ≠ a) γ = γ’ by simp[FILTER_NON_MEM_EQUAL] >>
              gs[g_conjunction_l])
         )
     )
QED

Theorem Y_WORLD_Prime:
  ∀p θ x A B.
    ¬ |- p ∧ S_Theory (Theta p) x ∧ B ∉ x ⇒
    Prime (Y_WORLD (Theta p) x {B})
Proof
  rpt strip_tac >> rw[Prime_def]
  >- (irule S_Theory_imp_R_Theory >> qexists_tac ‘Theta p’ >> gs[Y_WORLD_THETA_THEORY])
  >- (rename[‘C V D ∈ Y_WORLD (Theta p) x {B}’] >> CCONTR_TAC >>
      gs[] >> assume_tac Y_WORLD_prop_exists >>
      last_x_assum $ qspecl_then [‘x’, ‘p’, ‘B’] strip_assume_tac >>
      ‘Y_WORLD (Theta p) x {B} ≠ ∅’ by metis_tac[MEMBER_NOT_EMPTY] >>
      gs[] >>
      first_assum $ qspec_then ‘C’ strip_assume_tac >>
      first_x_assum $ qspec_then ‘D’ strip_assume_tac >>
      gs[] >>
      rename[‘c & C --> B ∈ Theta p’, ‘d & D --> B ∈ Theta p’, ‘C V D ∈ Y_WORLD (Theta p) x {B}’] >>
      ‘¬sENTAILS (Theta p) (Y_WORLD (Theta p) x {B}) B’ suffices_by
        (simp[sENTAILS_def] >> qexists_tac ‘[c & d; C V D]’ >> simp[CONJl_def] >>
         rw[]
         >- (assume_tac Y_WORLD_THETA_THEORY >>
             last_x_assum $ qspecl_then [‘p’, ‘B’, ‘x’] strip_assume_tac >> gs[] >>
             drule_then strip_assume_tac S_Theory_imp_R_Theory >>
             gs[R_Theory_def, pENTAIL_def] >> last_x_assum irule >>
             qexists_tac ‘[c; d]’ >> simp[CONJl_def, g_identity])
         >- (‘(c & d) & C --> B ∈ Theta p’ by (
              ‘|- (((c & d) & C) --> (c & C))’ by
                 (assume_tac g_conj_introduction >>
                  last_x_assum $ qspecl_then [‘((c & d) & C)’, ‘c’,‘C’] strip_assume_tac >>
                  metis_tac [g_conjunction_l, g_conjunction_r, g_modus_ponens,
                             g_conj_introduction, g_suffixing, g_adjunction_rule]
                 ) >> drule_then strip_assume_tac Theta_R_Theory >>
              gs[R_Theory_def] >>
              qpat_x_assum ‘∀p'. Theta p |-^ p' ⇒ p' ∈ Theta p’ irule >>
              simp[pENTAIL_def] >> qexists_tac ‘[c & C --> B]’ >> simp[CONJl_def] >>
              metis_tac[g_suffixing, g_modus_ponens]
              ) >>
             ‘(c & d) & D --> B ∈ Theta p’ by (
               ‘|- (((c & d) & D) --> (d & D))’ by
                  (assume_tac g_conj_introduction >>
                   last_x_assum $ qspecl_then [‘((c & d) & D)’, ‘d’,‘D’] strip_assume_tac >>
                   ‘|- (c & d & D --> D)’ by metis_tac[goldblatt_provable_rules] >>
                   ‘|- (c & d & D --> d)’ by metis_tac[goldblatt_provable_rules] >>
                   metis_tac[goldblatt_provable_rules]
                   ) >> drule_then strip_assume_tac Theta_R_Theory >>
               gs[R_Theory_def] >>
               qpat_x_assum ‘∀p'. Theta p |-^ p' ⇒ p' ∈ Theta p’ irule >>
               simp[pENTAIL_def] >> qexists_tac ‘[d & D --> B]’ >> simp[CONJl_def] >>
               metis_tac[g_suffixing, g_modus_ponens]
               ) >> drule_then strip_assume_tac Theta_R_Theory >>
               gs[R_Theory_def] >> last_x_assum irule >> simp[pENTAIL_def] >>
             qexists_tac ‘[c & d & C --> B; c & d & D --> B]’ >> simp[CONJl_def] >>
            metis_tac [g_suffixing, g_modus_ponens, g_adjunction_rule, g_distribution, g_disjunction_elim]
            )
        ) >>
      CCONTR_TAC >> gs[sENTAILS_def] >>
      ‘FINITE (set γ)’ by gs[] >>
      drule_all (iffLR FINITE_SUBSET_Y_WORLD) >>
      gs[] >>
      Induct
      >- (simp[Y_WORLD_i_def] >> CCONTR_TAC >> gs[] >>
          qpat_x_assum ‘B ∉ w’ mp_tac >> simp[] >>
          gs[S_Theory_def] >> last_assum irule >>
          simp[sENTAILS_def] >> qexists_tac ‘γ’ >> simp[])
      >- (simp[Y_WORLD_i_def] >>
          rw[] >> gs[sENTAILS_def] >> CCONTR_TAC >>
          gs[] >> qpat_x_assum ‘∀γ'. _’ mp_tac >> simp[] >>
          qexists_tac ‘γ’ >> gs[])
     )
QED

Theorem Truth_Lemma:
  ∀p. ¬ |- p ⇒  (∀A w. w ∈ (Canonical_Model p).RF.W ⇒
      (Holds (Canonical_Model p) w A ⇔ A ∈ w))
Proof
  strip_tac >> strip_tac >>
  Induct >> gs[Holds_def, Canonical_Model_def] >> rw[](* 4 *)
  >- (reverse $ rw[EQ_IMP_THM] >> rename [‘A --> B ∈ w’]
      >- (qpat_x_assum ‘(Canonical_Frame p).R w x y’ mp_tac >>
          rw[Canonical_Frame_def, APPLYING_def, SUBSET_DEF, sENTAILS_def] >>
          last_x_assum irule >> qexists_tac ‘[A]’ >>
          gs[CONJl_def]
         )
      >- (CCONTR_TAC >>
          qpat_x_assum
          ‘∀x y.
             x ∈ (Canonical_Frame p).W ∧ y ∈ (Canonical_Frame p).W ∧
             (Canonical_Frame p).R w x y ∧
             Holds <|RF := Canonical_Frame p; VF := (λx. {w | g_VAR x ∈ w})|> x A ⇒
             B ∈ y’ mp_tac >> gs[] >>
          qexistsl_tac [‘X_WORLD (Theta p) {A} {B} w’,
                        ‘Y_WORLD (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w)) {B}’] >>
          ‘X_WORLD (Theta p) {A} {B} w ∈ (Canonical_Frame p).W’ by
            (reverse $ rw[Canonical_Frame_def]
             >- (irule X_WORLD_THETA_THEORY >> gs[Canonical_Frame_def])
             >- (irule X_WORLD_Prime >> gs[Canonical_Frame_def])
            ) >>
          ‘Y_WORLD (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w)) {B} ∈ (Canonical_Frame p).W’ by
            (‘B ∉ APPLYING w (X_WORLD (Theta p) {A} {B} w)’ by
               (CCONTR_TAC >> qpat_x_assum ‘A --> B ∉ w’ mp_tac >> gs[] >>
                qpat_x_assum ‘w ∈ _’ mp_tac >> rw[Canonical_Frame_def] >> gs[S_Theory_def] >>
                last_x_assum irule >> drule_all_then strip_assume_tac X_WORLD_condition >>
                simp[sENTAILS_def] >> qexists_tac ‘[CONJl γ --> B]’ >> simp[CONJl_def] >>
                drule_then strip_assume_tac Theta_R_Theory >> gs[R_Theory_def] >>
                last_x_assum irule >> simp[pENTAIL_def] >>
                qexists_tac ‘[A --> CONJl γ]’ >> simp[CONJl_def, g_suffixing] >>
                gs[Ordinary_def, Regular_def] >> last_x_assum irule >>
                metis_tac[g_A_CONJl_A]) >>
             ‘S_Theory (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w))’ by
               (irule APPLIED_S_THEORY >> gs[Canonical_Frame_def]) >>
             reverse $ rw[Canonical_Frame_def]
             >- (irule Y_WORLD_THETA_THEORY >> gs[])
             >- (irule Y_WORLD_Prime >> rw[])
            ) >> gs[] >> rw[] (* 3 *)
          >- (gs[Canonical_Frame_def] >>
              rw[Y_WORLD_def, BIGUNION, SUBSET_DEF, PULL_EXISTS] >>
              qexists_tac ‘0’ >> gs[Y_WORLD_i_def]
             )
          >- (rw[X_WORLD_def, BIGUNION, PULL_EXISTS] >>
              qexists_tac ‘0’ >> gs[X_WORLD_i_def]
             )
          >- (rw[Y_WORLD_def] >> CCONTR_TAC >> gs[] >>
              qpat_x_assum
              ‘B ∈ Y_WORLD_i n (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w)) {B}’ mp_tac >>
              simp[] >> Induct_on ‘n’ >> rw[Y_WORLD_i_def] (* 3 *)
              >- (simp[APPLYING_def] >> CCONTR_TAC >> gs[] >>
                  pop_assum mp_tac >> assume_tac FINITE_SUBSET_X_WORLD >>
                  pop_assum $ qspec_then ‘set γ’ strip_assume_tac >> gs[] >>
                  Induct_on ‘n’ >> rw[X_WORLD_i_def]
                  >- (CCONTR_TAC >> gs[] >>
                      qpat_x_assum ‘A --> B ∉ w’ mp_tac >> simp[] >>
                      qpat_x_assum ‘w ∈ (Canonical_Frame p).W’ mp_tac >>
                      rw[Canonical_Frame_def, Prime_def, R_Theory_def] >>
                      last_x_assum irule >> simp[pENTAIL_def] >>
                      qexists_tac ‘[CONJl γ --> B]’ >> simp[CONJl_def] >>
                      irule g_modus_ponens >> qexists_tac ‘A --> CONJl γ’ >>
                      simp[g_suffixing, g_A_CONJl_A]
                     )
                  >- (CCONTR_TAC >> gs[] >>
                      qpat_x_assum
                      ‘¬sENTAILS (Theta p)
                       (APPLYING w
                        (X_WORLD_i n (Theta p) {A} {B} w ∪ {LINV R_gn 𝕌(:g_prop) n})) B’
                      mp_tac >> simp[sENTAILS_def] >> qexists_tac ‘[B]’ >>
                      gs[APPLYING_def, CONJl_def] >> rw[] (* 2 *)
                      >- (qexists_tac ‘γ’ >> gs[])
                      >- (‘Ordinary (Theta p)’ by gs[Theta_Ordinary] >>
                          gs[Ordinary_def, Regular_def, g_identity]
                         )
                     )
                 )
              >- (CCONTR_TAC >>
                  qpat_x_assum
                  ‘¬sENTAILS (Theta p)
                   (Y_WORLD_i n (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w))
                    {B} ∪ {LINV R_gn 𝕌(:g_prop) n}) B’ mp_tac >>
                  gs[sENTAILS_def] >> qexists_tac ‘[B]’ >>
                  gs[CONJl_def] >> ‘Ordinary (Theta p)’ by gs[Theta_Ordinary] >>
                  gs[Ordinary_def, Regular_def, g_identity]
                 )
              >- (CCONTR_TAC >>
                  qpat_x_assum
                  ‘¬sENTAILS (Theta p)
                   (Y_WORLD_i n (Theta p) (APPLYING w (X_WORLD (Theta p) {A} {B} w))
                    {B} ∪ {LINV R_gn 𝕌(:g_prop) n}) B’ mp_tac >>
                  gs[] >> rename[‘B = B'’] >>
                  simp[sENTAILS_def] >> qexists_tac ‘[B']’ >>
                  gs[CONJl_def] >> ‘Ordinary (Theta p)’ by gs[Theta_Ordinary] >>
                  gs[Ordinary_def, Regular_def, g_identity]
                 )
             )
         )
     )
  >- (rw[EQ_IMP_THM] >> rename[‘A & B ∈ w’] >>
      qpat_x_assum ‘w ∈ (Canonical_Frame p).W’ mp_tac >>
      simp[Canonical_Frame_def, S_Theory_def, sENTAILS_def] >> rw[]  (* 3 *)
      >- (last_x_assum irule >> qexists_tac ‘[A; B]’ >>
          gs[CONJl_def, Ordinary_def, Regular_def, g_identity]
         )
      >- (last_x_assum irule >>
          qexists_tac ‘[A & B]’ >>
          gs[CONJl_def, Ordinary_def, Regular_def, g_conjunction_l]
         )
      >- (last_x_assum irule >>
          qexists_tac ‘[A & B]’ >>
          gs[CONJl_def, Ordinary_def, Regular_def, g_conjunction_r]
         )
     )
  >- (‘(Canonical_Frame p).STAR w ∈ (Canonical_Frame p).W’ by
        (‘R_Frame (Canonical_Frame p)’ by
           (assume_tac Canonical_Frame_is_R_Frame >>
            pop_assum $ qspec_then ‘p’ strip_assume_tac >> gs[]
           ) >> gs[R_STAR_CLOSURE]
        ) >> rw[EQ_IMP_THM] >> gs[Canonical_Frame_def]
     )
  >- (rw[EQ_IMP_THM] (* 2 *)
      >- (pop_assum mp_tac >> simp[Canonical_Frame_def] >> rw[] >>
          gs[SUBSET_DEF, APPLYING_def] >> last_x_assum irule >>
          qexists_tac ‘[τ]’ >>
          gs[CONJl_def, g_identity, S_Theory_def, Ordinary_def, Regular_def] >>
          qpat_x_assum ‘∀p'. |- p' ⇒ p' ∈ Theta p’ irule >>
          metis_tac[goldblatt_provable_rules]
         )
      >- (‘(Canonical_Frame p).R w (Canonical_Frame p).Z w’ by
            (‘R_Frame (Canonical_Frame p)’ by
               (assume_tac Canonical_Frame_is_R_Frame >>
                pop_assum $ qspec_then ‘p’ strip_assume_tac >> gs[]
               ) >>
             ‘(Canonical_Frame p).R (Canonical_Frame p).Z w w’ by
               gs[R_R_ZERO_REFLEX] >>
             gs[R_R_COMM]
            ) >>
          simp[Canonical_Frame_def] >>
          assume_tac Theta_Ordinary >> pop_assum $ qspec_then ‘p’ strip_assume_tac >> gs[Ordinary_def] >>
          assume_tac Theta_Theta_theory >> pop_assum $ qspec_then ‘p’ strip_assume_tac >>
          gs[Canonical_Frame_def] >>
          qpat_x_assum ‘APPLYING w (Theta p) ⊆ w’ mp_tac >> rw[APPLYING_def,SUBSET_DEF] >>
          last_x_assum irule >> qexists_tac ‘[x]’ >> rw[CONJl_def] (* 2 *)
          >- (gs[S_Theory_def] >> last_x_assum irule >>
              simp[sENTAILS_def] >> qexists_tac ‘[τ]’ >> gs[CONJl_def, Regular_def] >>
              qpat_x_assum ‘∀p'. |- p' ⇒ p' ∈ Theta p’ irule >>
              metis_tac[goldblatt_provable_rules])
          >- (gs[S_Theory_def] >> last_x_assum irule >> simp[sENTAILS_def] >>
              qexists_tac ‘γ’ >> gs[SUBSET_DEF]
             )
         )
     )
QED

Theorem Completeness:
  (∀ (RM : (g_prop set) MODEL) . R_Model RM ⇒ Holds RM RM.RF.Z p) ⇒ |- p
Proof
  rw[] >> CCONTR_TAC >> qpat_x_assum ‘∀RM. R_Model RM ⇒ Holds RM RM.RF.Z p’ mp_tac >> simp[] >>
  qexists_tac ‘Canonical_Model p’ >> simp[Canonical_Model_is_R_Model]  >>
  drule_then strip_assume_tac Truth_Lemma >>
  last_x_assum $ qspecl_then [‘p’, ‘(Canonical_Frame p).Z’] strip_assume_tac >>
  ‘p ∉ (Canonical_Frame p).Z’ suffices_by
    gs[Canonical_Frame_is_R_Frame, Canonical_Model_def] >>
  gs[Canonical_Frame_def] >> drule Theta_Maximal_Rejection >>
  CCONTR_TAC >> gs[pENTAIL_def] >>
  last_x_assum $ qspec_then ‘[p]’ strip_assume_tac >>
  gs[CONJl_def, g_identity]
QED

val _ = export_theory();
