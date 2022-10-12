open HolKernel Parse boolLib bossLib pred_setTheory;
open relationTheory;
open GoldblattRLTheory RLRulesTheory;


val _ = new_theory "CoverSemantics";

Datatype:
  COVER_SYSTEM = <| W: α set; REF: α -> α -> bool; COVER: α set -> α -> bool |>
End

Definition Upset_def:
  Upset CS X ⇔ X ⊆ CS.W ∧ ∀d e. d ∈ X ∧ e ∈ CS.W ∧ CS.REF d e ⇒ e ∈ X
End

Definition Up_def:
  Up CS x = {u | u ∈ CS.W ∧ ∃w. w ∈ x ∧ CS.REF w u}
End

Definition PREORDER_def:
  PREORDER R X ⇔
    (∀x. x ∈ X ⇒ R x x) ∧
    (∀x y z. x ∈ X ∧ y ∈ X ∧ z ∈ X ∧ R x y ∧ R y z ⇒
             R x z)
End

Definition Is_Cover_System_def:
  Is_Cover_System CS ⇔ PREORDER CS.REF CS.W ∧
                       (∀x y. CS.REF x y ⇒ x ∈ CS.W ∧ y ∈ CS.W) ∧
                       (∀x. x ∈ CS.W ⇒ ∃Z. CS.COVER Z x) ∧
                       (∀x Z. x ∈ CS.W ∧ CS.COVER Z x ⇒ Z ⊆ Up CS {x})
End

Theorem Upset_up:
  Is_Cover_System CS ⇒
  (Upset CS X ⇔ Up CS X = X)
Proof
  rw[Up_def, Upset_def, EXTENSION, EQ_IMP_THM]
  >- metis_tac[SUBSET_DEF]
  >- (qexists_tac ‘x’ >> metis_tac[Is_Cover_System_def, PREORDER_def, SUBSET_DEF])
  >- gs[SUBSET_DEF]
  >- metis_tac[Is_Cover_System_def]
QED


Theorem Upset_UNION:
  ∀CS A B. Upset CS A ∧ Upset CS B ⇒ Upset CS (A ∪ B)
Proof
  rw[Upset_def] >> metis_tac[]
QED


Theorem Upset_INTER:
  ∀CS A B. Upset CS A ∧ Upset CS B ⇒ Upset CS (A ∩ B)
Proof
  rw[Upset_def, SUBSET_DEF] >> metis_tac[]
QED


Definition j_def:
  j CS X = {w | w ∈ CS.W ∧ ∃Z. CS.COVER Z w ∧ Z ⊆ X}
End

Definition Localized_def:
  Localized CS X ⇔ j CS X ⊆ X
End

Theorem lemma6_3_1:
  ∀CS X. Is_Cover_System CS ∧ Upset CS X ⇒ X ⊆ j CS X
Proof
  rw[j_def, SUBSET_DEF]
  >- gs[Upset_def, SUBSET_DEF]
  >> ‘Up CS {x} ⊆ X’ by
    (gs[Upset_def] >> rw[SUBSET_DEF, Up_def] >>
     last_x_assum irule >> simp[] >>
     metis_tac[]
    ) >>
  gs[Is_Cover_System_def] >>
  qpat_x_assum ‘∀x. x ∈ CS.W ⇒ ∃Z. CS.COVER Z x’ $ qspec_then ‘x’ strip_assume_tac >>
  gs[Upset_def, SUBSET_DEF] >> qexists_tac ‘Z’ >> simp[] >>
  last_x_assum $ qspecl_then [‘x’, ‘Z’] strip_assume_tac >> gs[]
QED

Datatype:
  R_COVER_SYSTEM = <| W: α set; REF: α -> α -> bool; COVER: α set -> α -> bool; FUSE: α -> α -> α; E: α; ORTH: α -> α -> bool |>
End

Definition rel_Lift_1:
   rel_Lift_1 R X y ⇔ ∀x. x ∈ X ⇒ R x y
End

Definition rel_Lift_2:
   rel_Lift_2 R x Y ⇔ ∀y. y ∈ Y ⇒ R x y
End


Definition op_Lift_1:
   op_Lift_1 R X y = {R x y | x ∈ X}
End

Definition op_Lift_2:
   op_Lift_2 R x Y = {R x y | y ∈ Y}
End

Definition to_CS_def:
  (to_CS: α R_COVER_SYSTEM -> α COVER_SYSTEM) RCS = <|W := RCS.W; REF := RCS.REF; COVER := RCS.COVER |>
End

val _= set_mapped_fixity {term_name = "rcsBOT", fixity = Infix (NONASSOC, 450), tok="⊥ₐ"};
Overload "rcsBOT" = “λ x y. rel_Lift_1 RCS.ORTH (x: α set) y”
Overload "rcsBOT" = “λ x y. rel_Lift_2 RCS.ORTH (x: α) y”
Overload "rcsBOT" = “λ x y. RCS.ORTH (x: α) y”

val _= set_mapped_fixity {term_name = "rcsFUSE", fixity = Infix (NONASSOC, 450), tok="⬝ₐ"};
Overload "rcsFUSE" = “λ x y. op_Lift_1 RCS.FUSE (x: α set) y”
Overload "rcsFUSE" = “λ x y. op_Lift_2 RCS.FUSE (x: α) y”
Overload "rcsFUSE" = “λ x y. RCS.FUSE (x: α) y”

val _= set_mapped_fixity {term_name = "rcsREF", fixity = Infix (NONASSOC, 450), tok="≼ₐ"};
Overload "rcsREF" = “λ x y. RCS.REF (x: α) y”


val _= set_mapped_fixity {term_name = "rcsCOVER", fixity = Infix (NONASSOC, 450), tok="▹ₐ"};
Overload "rcsCOVER" = “λ (x : α set) y. RCS.COVER x y”


Overload "j" = “λ (X: α set). j (to_CS RCS) X”
Overload "Upset" = “λ (X: α set). Upset (to_CS RCS) X”
Overload "Localized" = “λ (X: α set). Localized (to_CS RCS) X”


Definition Is_Relevant_Cover_System_def:
  Is_Relevant_Cover_System RCS ⇔
    RCS.E ∈ RCS.W ∧
    (∀x y. x ≼ₐ y ⇒ x ∈ RCS.W ∧ y ∈ RCS.W) ∧
    (∀x Z. Z ▹ₐ x ⇒ x ∈ RCS.W ∧ Z ⊆ RCS.W) ∧
    (∀x y. x ∈ RCS.W ∧ y ∈ RCS.W ⇒ x ⬝ₐ y ∈ RCS.W) ∧
    (∀x y. x ⊥ₐ y ⇒ x ∈ RCS.W ∧ y ∈ RCS.W) ∧
    Is_Cover_System (to_CS RCS) ∧

    (* SQUARE-DECREASING COMMUNITIVE ORDERED MONOID *)
    (∀x. x ∈ RCS.W ⇒ (x ⬝ₐ RCS.E) = x) ∧
    (∀x. x ∈ RCS.W ⇒ (RCS.E ⬝ₐ x) = x) ∧
    (∀x y. x ∈ RCS.W ∧ y ∈ RCS.W ⇒ (x ⬝ₐ y) = (y ⬝ₐ x)) ∧
    (∀x y z. x ∈ RCS.W ∧ y ∈ RCS.W ∧ z ∈ RCS.W ⇒ (x ⬝ₐ (y ⬝ₐ z)) = ((x ⬝ₐ y) ⬝ₐ z)) ∧
    (∀x x' y y'. x ≼ₐ x' ∧ y ≼ₐ y' ⇒ (x ⬝ₐ y) ≼ₐ (x' ⬝ₐ y')) ∧
    (∀x. x ∈ RCS.W ⇒ (x ⬝ₐ x) ≼ₐ x) ∧

    (* OTHER *)
    (∀x y Z. Z ▹ₐ x ∧ y ∈ RCS.W ⇒ (Z ⬝ₐ y) ▹ₐ (x ⬝ₐ y)) ∧
    (∀x x' y y'. x ≼ₐ x' ∧ y ≼ₐ y' ∧ x ⊥ₐ y ⇒ x' ⊥ₐ y') ∧
    (∀x Z. Z ▹ₐ x ∧ Z ⊥ₐ RCS.E ⇒ x ⊥ₐ RCS.E) ∧
    (∀x y z. x ∈ RCS.W ∧ y ∈ RCS.W ∧ z ∈ RCS.W ∧ (x ⬝ₐ y) ⊥ₐ z ⇒ (x ⬝ₐ z) ⊥ₐ y)
End

Theorem RCS_IDENTITY               = Is_Relevant_Cover_System_def |> iffLR |> cj 1
Theorem RCS_REFINEMENT_CLOSURE     = Is_Relevant_Cover_System_def |> iffLR |> cj 2
Theorem RCS_COVER_CLOSURE          = Is_Relevant_Cover_System_def |> iffLR |> cj 3
Theorem RCS_FUSION_CLOSURE         = Is_Relevant_Cover_System_def |> iffLR |> cj 4
Theorem RCS_ORTHOGONAL_CLOSURE     = Is_Relevant_Cover_System_def |> iffLR |> cj 5
Theorem RCS_COVER_SYSTEM           = Is_Relevant_Cover_System_def |> iffLR |> cj 6

Theorem RCS_FUSION_RIGHT_IDENTITY  = Is_Relevant_Cover_System_def |> iffLR |> cj 7
Theorem RCS_FUSION_LEFT_IDENTITY   = Is_Relevant_Cover_System_def |> iffLR |> cj 8
Theorem RCS_FUSION_COMM            = Is_Relevant_Cover_System_def |> iffLR |> cj 9
Theorem RCS_FUSION_ASSOC_LR        = Is_Relevant_Cover_System_def |> iffLR |> cj 10
Theorem RCS_FUSION_MONO_REFINEMENT = Is_Relevant_Cover_System_def |> iffLR |> cj 11
Theorem RCS_FUSION_SQUARE_DECREASE = Is_Relevant_Cover_System_def |> iffLR |> cj 12

Theorem RCS_FUSION_COVERING        = Is_Relevant_Cover_System_def |> iffLR |> cj 13
Theorem RCS_REFINEMENT_ORTHOGONAL  = Is_Relevant_Cover_System_def |> iffLR |> cj 14
Theorem RCS_IDENTITY_ORTH_IS_LOCAL = Is_Relevant_Cover_System_def |> iffLR |> cj 15
Theorem RCS_CONTRAPOSITION         = Is_Relevant_Cover_System_def |> iffLR |> cj 16

Theorem RCS_PREORDER:
  Is_Relevant_Cover_System RCS ⇒
  PREORDER RCS.REF RCS.W
Proof
  rw[] >> drule RCS_COVER_SYSTEM >> simp[to_CS_def] >>
  rw[Is_Cover_System_def]
QED

Definition Perp_def:
  Perp RCS (X: α set) = {y | y ∈ RCS.W ∧ ∀x. x ∈ X ⇒ y ⊥ₐ x}
End

Overload "Perp" = “λ (X: α set). Perp RCS X”

Theorem to_CS_IS_COVER:
  ∀RCS. Is_Relevant_Cover_System RCS ⇒
        Is_Cover_System (to_CS RCS)
Proof
  rw[to_CS_def, RCS_COVER_SYSTEM]
QED

Definition Is_Prop_def:
  Is_Prop RCS X ⇔ (Localized (to_CS RCS) X ∧ Upset (to_CS RCS) X)
End

Definition IMP_def:
  IMP RCS X Y = {w | w ∈ RCS.W ∧ {w ⬝ₐ x | x ∈ X} ⊆ Y}
End

val _= set_mapped_fixity {term_name = "IMPP", fixity = Infix (NONASSOC, 450), tok="⟹ₐ"};
Overload "IMPP" = “λ (x : α set) y. IMP RCS x y”

Theorem lemma6_4_1_1:
  ∀RCS x y. Is_Relevant_Cover_System RCS ∧ x ∈ RCS.W ∧ y ∈ RCS.W ⇒
            (x ⊥ₐ y ⇔ (x ⬝ₐ y) ⊥ₐ RCS.E)
Proof
  rw[EQ_IMP_THM]
  >- (irule RCS_CONTRAPOSITION >> simp[RCS_IDENTITY] >>
      metis_tac[RCS_FUSION_RIGHT_IDENTITY]
     )
  >- (drule_then strip_assume_tac RCS_CONTRAPOSITION >>
      pop_assum $ qspecl_then [‘x’, ‘y’, ‘RCS.E’]  strip_assume_tac >>
      metis_tac[RCS_FUSION_RIGHT_IDENTITY, RCS_IDENTITY]
     )
QED

Theorem lemma6_4_1_2:
  ∀RCS X. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ⇒
          Is_Prop RCS (Perp RCS X)
Proof
  reverse $ rw[Is_Prop_def, Localized_def, Perp_def]
  >- (rw[Upset_def, SUBSET_DEF, to_CS_def] >> irule RCS_REFINEMENT_ORTHOGONAL >>
      simp[] >> metis_tac[PREORDER_def, RCS_PREORDER, SUBSET_DEF]
     )
  >- (rw[j_def, Once SUBSET_DEF, to_CS_def] >> rename[‘x ⊥ₐ y’] >>
      irule (iffRL lemma6_4_1_1) >> rw[]
      >- gs[SUBSET_DEF]
      >> ‘∀z. z ∈ Z ⇒ z ⊥ₐ y’ by gs[SUBSET_DEF] >>
      ‘∀z. z ∈ Z ⇒ (z ⬝ₐ y) ⊥ₐ RCS.E’ by
        (rw[] >> irule (iffLR lemma6_4_1_1) >>
         gs[SUBSET_DEF]) >>
      drule_then strip_assume_tac RCS_FUSION_COVERING >>
      pop_assum $ qspecl_then [‘x’, ‘y’, ‘Z’] strip_assume_tac >>
      gs[] >> irule RCS_IDENTITY_ORTH_IS_LOCAL >> simp[] >>
      qexists_tac ‘Z ⬝ₐ y’ >> gs[op_Lift_1, rel_Lift_1, SUBSET_DEF] >>
      metis_tac[SUBSET_DEF])
QED

Theorem lemma6_4_1_3:
  ∀RCS X Y. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ∧
            Y ⊆ RCS.W ∧ Upset Y ⇒
            Upset (X ⟹ₐ Y)
Proof
  rw[Upset_def, to_CS_def]
  >- simp[IMP_def, Once SUBSET_DEF]
  >- (rw[IMP_def, SUBSET_DEF] >> rename [‘x ∈ X’, ‘d ∈ X ⟹ₐ Y’] >>
      last_x_assum irule >> rw[]
      >- gs[SUBSET_DEF, RCS_REFINEMENT_CLOSURE, RCS_FUSION_CLOSURE]
      >- (qexists_tac ‘d ⬝ₐ x’ >> rw[]
          >- (gs[IMP_def, SUBSET_DEF] >> metis_tac[])
          >- (irule RCS_FUSION_MONO_REFINEMENT >>
              simp[] >> metis_tac[PREORDER_def, RCS_PREORDER, SUBSET_DEF]
             )
         )
     )
QED

Theorem lemma6_4_1_4:
  ∀RCS X Y. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ∧
            Y ⊆ RCS.W ∧ Localized Y ⇒
            Localized (X ⟹ₐ Y)
Proof
  rw[SUBSET_DEF, Localized_def, IMP_def, j_def, to_CS_def] >>
  rename[‘x ⬝ₐ y ∈ Y’] >> first_x_assum irule >>
  simp[RCS_FUSION_CLOSURE] >> qexists_tac ‘Z ⬝ₐ y’ >>
  rw[RCS_FUSION_COVERING, op_Lift_1] >>
  metis_tac[]
QED

Theorem lemma6_4_1_5:
  ∀RCS (x: α) X. Is_Relevant_Cover_System RCS ∧ x ∈ RCS.W ∧ X ⊆ RCS.W ∧
                 x ⊥ₐ X ⇒
                 x ⊥ₐ j X
Proof
  rw[j_def, rel_Lift_2, to_CS_def] >> irule (iffRL lemma6_4_1_1) >> simp[] >>
  irule RCS_IDENTITY_ORTH_IS_LOCAL >> simp[] >>
  qexists_tac ‘Z ⬝ₐ x’ >> rw[]
  >- metis_tac[RCS_FUSION_COVERING, RCS_FUSION_COMM]
  >- (pop_assum mp_tac >> rw[SUBSET_DEF, op_Lift_1, rel_Lift_1] >>
      metis_tac[lemma6_4_1_1, RCS_FUSION_COMM, SUBSET_DEF]
     )
QED

Theorem lemma6_4_1_5_alt:
  ∀RCS (x: α) X. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ⇒
                 Perp X ⊆ Perp (j X)
Proof
  rw[SUBSET_DEF, Perp_def] >> rename[‘x ⊥ₐ y’] >>
  assume_tac lemma6_4_1_5 >> gs[rel_Lift_2] >> first_x_assum irule >>
  simp[] >> qexists_tac ‘X’ >> gs[SUBSET_DEF]
QED

Theorem lemma6_4_1_6:
  ∀RCS X. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ⇒
          j X ⊆ Perp (Perp (j X)) ∧ Perp (Perp (j X)) ⊆ Perp (Perp X)
Proof
  rw[]
  >- (rw[SUBSET_DEF, j_def, to_CS_def, Perp_def] >>
      rename [‘x ⊥ₐ y’] >>
      ‘y ⊥ₐ x’ suffices_by
        metis_tac[lemma6_4_1_1, RCS_FUSION_COMM] >>
      last_x_assum irule >> metis_tac[]
     )
  >- (‘Perp X ⊆ Perp (j X)’ suffices_by
        rw[Perp_def, SUBSET_DEF] >>
      rw[Perp_def, SUBSET_DEF] >>
      rename [‘x ⊥ₐ y’] >>
      assume_tac lemma6_4_1_5 >>
      pop_assum $ qspecl_then [‘RCS’, ‘x’, ‘X’] strip_assume_tac >>
      gs[rel_Lift_2]
     )
QED

Theorem lemma6_4_1_7:
  ∀(RCS : α R_COVER_SYSTEM) X x. Is_Relevant_Cover_System RCS ∧ Upset X ∧ X ⊆ RCS.W ∧ x ∈ RCS.W ⇒
            (x ⊥ₐ X ⇔ x ⊥ₐ j X)
Proof
  rw[] >>
  EQ_TAC >> strip_tac
  >- gs[lemma6_4_1_5]
  >- (gs[rel_Lift_2] >> rw[] >>
      metis_tac[lemma6_3_1, RCS_COVER_SYSTEM, SUBSET_DEF])
QED

Theorem lemma6_4_1_7_alt:
  ∀RCS (x: α) X. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ∧ Upset X ⇒
                 Perp X = Perp (j X)
Proof
  rw[Perp_def, EXTENSION] >> metis_tac[lemma6_4_1_7, rel_Lift_2]
QED

Theorem lemma6_4_1_8:
  ∀RCS (x: α) X. Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ∧ Upset X ⇒
                 X ⊆ j X ∧ j X ⊆ Perp (Perp (j X)) ∧ Perp (Perp (j X)) = Perp (Perp X)
Proof
  rw[lemma6_4_1_7_alt, lemma6_4_1_6, lemma6_3_1, RCS_COVER_SYSTEM]
QED

Theorem corollary6_4_2:
  ∀RCS (X: α set). Is_Relevant_Cover_System RCS ∧ X ⊆ RCS.W ∧ Upset X ∧ X = Perp (Perp X) ⇒
                   Is_Prop RCS X
Proof
  rw[Is_Prop_def, Localized_def] >>
  metis_tac[SUBSET_DEF, lemma6_4_1_8]
QED

Definition Orthojoin_def:
  Orthojoin RCS X Y = Perp RCS (Perp RCS (X ∪ Y))
End

Overload "Orthojoin" = “λ (X: α set). Orthojoin RCS X”

Definition R_MODEL_SYSTEM_def:
  R_MODEL_SYSTEM RCS Ps ⇔ Is_Relevant_Cover_System RCS ∧
                          ((Up (to_CS RCS) {RCS.E}) ∈ Ps) ∧
                          (∀X. X ∈ Ps ⇒ Upset X) ∧
                          (∀X. X ∈ Ps ⇒ X = Perp (Perp X)) ∧
                          (∀X. X ∈ Ps ⇒ Perp X ∈ Ps) ∧
                          (∀X Y. X ∈ Ps ∧ Y ∈ Ps ⇒ X ∩ Y ∈ Ps) ∧
                          (∀X Y. X ∈ Ps ∧ Y ∈ Ps ⇒ X ⟹ₐ Y ∈ Ps) ∧
                          (∀X Y. X ∈ Ps ∧ Y ∈ Ps ⇒ Orthojoin X Y = j (X ∪ Y))
End

Theorem R_MODEL_SYSTEM_R_COVER_SYSTEM    = R_MODEL_SYSTEM_def |> iffLR |> cj 1
Theorem R_MODEL_SYSTEM_E_CONE_PS         = R_MODEL_SYSTEM_def |> iffLR |> cj 2
Theorem R_MODEL_SYSTEM_PS_UPSET          = R_MODEL_SYSTEM_def |> iffLR |> cj 3
Theorem R_MODEL_SYSTEM_PS_ORTHOCLOSED    = R_MODEL_SYSTEM_def |> iffLR |> cj 4
Theorem R_MODEL_SYSTEM_PERP_PS           = R_MODEL_SYSTEM_def |> iffLR |> cj 5
Theorem R_MODEL_SYSTEM_INTER_PS          = R_MODEL_SYSTEM_def |> iffLR |> cj 6
Theorem R_MODEL_SYSTEM_IMP_PS            = R_MODEL_SYSTEM_def |> iffLR |> cj 7
Theorem R_MODEL_SYSTEM_ORTHOJOIN_J_UNION = R_MODEL_SYSTEM_def |> iffLR |> cj 8

Theorem Ps_membership:
  ∀RCS Ps X. R_MODEL_SYSTEM RCS Ps ∧ X ∈ Ps ⇒
             X ⊆ RCS.W
Proof
  rw[SUBSET_DEF] >>
  ‘Upset X’ by metis_tac[R_MODEL_SYSTEM_PS_UPSET] >>
  gs[Upset_def] >> gs[SUBSET_DEF, to_CS_def]
QED

val _= set_mapped_fixity {term_name = "gBOT", fixity = Infix (NONASSOC, 450), tok="⊥"};
val _= set_mapped_fixity {term_name = "gFUSE", fixity = Infix (NONASSOC, 450), tok="⬝"};
val _= set_mapped_fixity {term_name = "gREF", fixity = Infix (NONASSOC, 450), tok="≼"};
val _= set_mapped_fixity {term_name = "gCOVER", fixity = Infix (NONASSOC, 450), tok="▹"};
val _= set_mapped_fixity {term_name = "gIMPP", fixity = Infix (NONASSOC, 450), tok="⟹"};

Overload "gBOT" = “λ x y. RCS.ORTH (x: g_prop set) y”
Overload "gBOT" = “λ x y. rel_Lift_1 RCS.ORTH (x: (g_prop set) set) y”
Overload "gBOT" = “λ x y. rel_Lift_2 RCS.ORTH (x: g_prop set) y”

Overload "gFUSE" = “λ x y. RCS.FUSE (x: g_prop set) y”
Overload "gFUSE" = “λ x y. op_Lift_1 RCS.FUSE (x: (g_prop set) set) y”
Overload "gFUSE" = “λ x y. op_Lift_2 RCS.FUSE (x: g_prop set) y”

Overload "gREF" = “λ x y. RCS.REF (x: g_prop set) y”

Overload "gCOVER" = “λ (x : (g_prop set) set) y. RCS.COVER x y”

Overload "j" = “λ (X: (g_prop set) set). j (to_CS RCS) X”
Overload "Upset" = “λ (X: (g_prop set) set). Upset (to_CS RCS) X”
Overload "Localized" = “λ (X: (g_prop set) set). Localized (to_CS RCS) X”
Overload "Perp" = “λ (X: (g_prop set) set). Perp RCS X”
Overload "gIMPP" = “λ (x : (g_prop set) set) y. IMP RCS x y”
Overload "Orthojoin" = “λ (X: (g_prop set) set). Orthojoin RCS X”

Definition Model_Function_def:
  Model_Function (RCS: (g_prop set) R_COVER_SYSTEM) Ps M ⇔
    (∀a A. M (g_VAR a) = A ⇒ A ∈ Ps) ∧
    (M τ = Up (to_CS RCS) {RCS.E}) ∧
    (∀A B. M (A & B) = M A ∩ M B) ∧
    (∀A B. M (A --> B) = (M A ⟹ M B)) ∧
    (∀A. M (~A) = Perp (M A))
End

Theorem Model_Function_var = Model_Function_def |> iffLR |> cj 1
Theorem Model_Function_t   = Model_Function_def |> iffLR |> cj 2
Theorem Model_Function_and = Model_Function_def |> iffLR |> cj 3
Theorem Model_Function_imp = Model_Function_def |> iffLR |> cj 4
Theorem Model_Function_not = Model_Function_def |> iffLR |> cj 5

Theorem M_SUBSET_RCS_W:
  ∀RCS Ps M A. Model_Function RCS Ps M ∧ R_MODEL_SYSTEM RCS Ps ⇒
          M A ⊆ RCS.W
Proof
  rpt strip_tac >> Induct_on ‘A’ >> gs[Model_Function_def, SUBSET_DEF] >> rw[]
  >- metis_tac[Ps_membership, SUBSET_DEF]
  >- gs[IMP_def]
  >- gs[Perp_def]
  >- gs[R_MODEL_SYSTEM_def, Up_def, to_CS_def]
QED

Theorem M_IN_Ps_W:
  ∀RCS Ps M A. Model_Function RCS Ps M ∧ R_MODEL_SYSTEM RCS Ps ⇒
          M A ∈ Ps
Proof
  rpt strip_tac >> Induct_on ‘A’ >> gs[Model_Function_def, SUBSET_DEF] >> rw[]
  >- metis_tac[Ps_membership, SUBSET_DEF, R_MODEL_SYSTEM_IMP_PS, R_MODEL_SYSTEM_INTER_PS,
               R_MODEL_SYSTEM_PERP_PS, R_MODEL_SYSTEM_E_CONE_PS, to_CS_def, Up_def]
  >- metis_tac[Ps_membership, SUBSET_DEF, R_MODEL_SYSTEM_IMP_PS, R_MODEL_SYSTEM_INTER_PS,
               R_MODEL_SYSTEM_PERP_PS, R_MODEL_SYSTEM_E_CONE_PS, to_CS_def, Up_def]
  >- metis_tac[Ps_membership, SUBSET_DEF, R_MODEL_SYSTEM_IMP_PS, R_MODEL_SYSTEM_INTER_PS,
               R_MODEL_SYSTEM_PERP_PS]
  >- (drule_then strip_assume_tac R_MODEL_SYSTEM_E_CONE_PS >>
      ‘Up (to_CS RCS) {RCS.E} = {w | RCS.E ≼ w ∧ w ∈ RCS.W}’ suffices_by
        metis_tac[] >> rw[Once EXTENSION, Up_def, to_CS_def, EQ_IMP_THM])
QED

Theorem Model_Function_or:
  ∀RCS Ps M. Model_Function RCS Ps M ⇒
             ∀A B. M(A V B) = Orthojoin (M A) (M B)
Proof
  rw[Orthojoin_def, g_OR_def] >>
  drule_then strip_assume_tac Model_Function_and >>
  drule_then strip_assume_tac Model_Function_not >> gs[] >>
  ‘Perp (M A) ∩ Perp (M B) = Perp (M A ∪ M B)’ suffices_by metis_tac[] >>
  rw[EXTENSION, Perp_def, EQ_IMP_THM] >> metis_tac[]
QED

Definition C_Holds_def:
  C_Holds RCS Ps M w A ⇔ w ∈ M A ∧ Model_Function RCS Ps M ∧ R_MODEL_SYSTEM RCS Ps
End

Theorem C_Holds_conditions:
  ∀RCS Ps M w. R_MODEL_SYSTEM RCS Ps ∧ Model_Function RCS Ps M ∧ w ∈ RCS.W ⇒
             (∀s. C_Holds RCS Ps M w (g_VAR s) ⇔ w ∈ M (g_VAR s)) ∧
             (C_Holds RCS Ps M w τ ⇔ RCS.E ≼ w) ∧
             (∀A. C_Holds RCS Ps M w (~A) ⇔ ∀u. C_Holds RCS Ps M u A ⇒ w ⊥ u) ∧
             (∀A B. C_Holds RCS Ps M w (A & B) ⇔ C_Holds RCS Ps M w A ∧ C_Holds RCS Ps M w B) ∧
             (∀A B. C_Holds RCS Ps M w (A --> B) ⇔ ∀u. C_Holds RCS Ps M u A ⇒ C_Holds RCS Ps M (w ⬝ u) B)
Proof
  rw[C_Holds_def, SUBSET_DEF, EQ_IMP_THM] >>
  gs[Model_Function_def, Perp_def, IMP_def, SUBSET_DEF, Up_def, to_CS_def] >>
  metis_tac[RCS_ORTHOGONAL_CLOSURE, RCS_FUSION_CLOSURE, M_SUBSET_RCS_W, SUBSET_DEF]
QED

Theorem Semantic_Entailment:
  ∀ RCS Ps M A B. R_MODEL_SYSTEM RCS Ps ∧ Model_Function RCS Ps M ⇒
        (C_Holds RCS Ps M RCS.E (A --> B) ⇔ M A ⊆ M B)
Proof
  rw[EQ_IMP_THM, C_Holds_def]
  >- (drule Model_Function_imp >> rw[SUBSET_DEF, IMP_def] >>
      gs[] >> last_x_assum irule >>
      qexists_tac ‘x’ >> simp[] >>
      irule (GSYM RCS_FUSION_LEFT_IDENTITY) >>
      metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, M_SUBSET_RCS_W, SUBSET_DEF, Model_Function_def]
     )
  >- (drule Model_Function_imp >> rw[SUBSET_DEF, IMP_def]
      >- metis_tac[RCS_IDENTITY, R_MODEL_SYSTEM_R_COVER_SYSTEM] >~
      [‘RCS.E ⬝ y ∈ M B’, ‘y ∈ M A’, ‘M A ⊆ M B’]
      >- (‘(RCS.E ⬝ y) = y’ suffices_by metis_tac[SUBSET_DEF] >>
          metis_tac[RCS_FUSION_LEFT_IDENTITY, R_MODEL_SYSTEM_R_COVER_SYSTEM,
                    M_SUBSET_RCS_W, SUBSET_DEF])
     )
QED

Theorem C_Holds_at_E:
  ∀RCS Ps M A. R_MODEL_SYSTEM RCS Ps ∧ Model_Function RCS Ps M ⇒
             (C_Holds RCS Ps M RCS.E A ⇔ RCS.E ∈ M A)
Proof
  rw[C_Holds_def]
QED

Theorem E_x_is_x:
  ∀RCS Ps M x. R_MODEL_SYSTEM RCS Ps ∧ Model_Function RCS Ps M ∧ x ∈ RCS.W ⇒
               (RCS.E ⬝ x) = x
Proof
  metis_tac[M_SUBSET_RCS_W, SUBSET_DEF, R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_LEFT_IDENTITY]
QED

Theorem soundness:
  ∀p RCS Ps M. |- p ∧ R_MODEL_SYSTEM RCS Ps ∧ Model_Function RCS Ps M ⇒
               C_Holds RCS Ps M RCS.E p
Proof
  Induct_on ‘goldblatt_provable’ >>
  rw[] >> irule (iffRL C_Holds_at_E) >> simp[]
  >- (drule Model_Function_imp >> rw[IMP_def]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rw[SUBSET_DEF] >> metis_tac[M_SUBSET_RCS_W, E_x_is_x, SUBSET_DEF])
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      rw[IMP_def, SUBSET_DEF]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename [‘RCS.E ⬝ x ∈ RCS.W’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >>
          gs[])
      >- (rename[‘(RCS.E ⬝ x) ⬝ y ∈ RCS.W’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >>
          gs[] >> metis_tac[M_SUBSET_RCS_W, SUBSET_DEF, RCS_FUSION_CLOSURE, R_MODEL_SYSTEM_R_COVER_SYSTEM]
         )
      >- (rename[‘((RCS.E ⬝ x) ⬝ y) ⬝ z ∈ M C’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >>
          last_x_assum irule >>
          qexists_tac ‘(x ⬝ z)’ >> rw[]
          >- (‘((y ⬝ x) ⬝ z) = (y ⬝ (x ⬝ z))’ suffices_by
                metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_COMM, RCS_FUSION_ASSOC_LR] >>
              ‘z ∈ RCS.W’ by metis_tac[M_SUBSET_RCS_W, SUBSET_DEF] >>
              irule (GSYM RCS_FUSION_ASSOC_LR) >> metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM])
          >- metis_tac[]
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      rw[IMP_def, SUBSET_DEF]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename [‘RCS.E ⬝ x ∈ RCS.W’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x, M_SUBSET_RCS_W, SUBSET_DEF] >>
          gs[] >> metis_tac[M_SUBSET_RCS_W, SUBSET_DEF]
         )
      >- (rename[‘(RCS.E ⬝ x) ⬝ y ∈ M B’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x, M_SUBSET_RCS_W, SUBSET_DEF] >>
          gs[] >> last_x_assum irule >> qexists_tac ‘x’ >> simp[] >>
          metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_COMM, M_SUBSET_RCS_W, SUBSET_DEF])
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      rw[IMP_def, SUBSET_DEF]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘RCS.E ⬝ x ∈ RCS.W’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >>
          gs[])
      >- (rename[‘(RCS.E ⬝ x) ⬝ y ∈ M B’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >>
          gs[PULL_EXISTS] >>
          ‘Upset (M B)’ by
            metis_tac[R_MODEL_SYSTEM_PS_UPSET, M_IN_Ps_W] >>
          gs[Upset_def] >> pop_assum irule >> rw[]
          >- (‘x ⬝ y ∈ RCS.W’ suffices_by rw[to_CS_def] >>
              metis_tac[M_SUBSET_RCS_W, SUBSET_DEF, RCS_FUSION_CLOSURE])
          >- (qexists_tac ‘(x ⬝ y) ⬝ y’ >> reverse $ rw[] >>
              ‘((x ⬝ y) ⬝ y) ≼ (x ⬝ y)’ suffices_by rw[to_CS_def] >>
              ‘((x ⬝ y) ⬝ y) = (x ⬝ (y ⬝ y))’ by
                (irule (GSYM RCS_FUSION_ASSOC_LR) >>
                 metis_tac [M_SUBSET_RCS_W, SUBSET_DEF, R_MODEL_SYSTEM_R_COVER_SYSTEM]) >>
              gs[] >> irule RCS_FUSION_MONO_REFINEMENT >> rw[] >>
              metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_SQUARE_DECREASE,
                        M_SUBSET_RCS_W, SUBSET_DEF, RCS_PREORDER, PREORDER_def]
             )
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_and >>
      rw[IMP_def, SUBSET_DEF]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘(RCS.E ⬝ x) ∈ M A’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x, M_SUBSET_RCS_W, SUBSET_DEF] >>
          gs[])
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_and >>
      rw[IMP_def, SUBSET_DEF]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘(RCS.E ⬝ x) ∈ M B’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x, M_SUBSET_RCS_W, SUBSET_DEF] >>
          gs[])
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_and >>
      rw[IMP_def, SUBSET_DEF]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘(RCS.E ⬝ x) ∈ RCS.W’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >>
          gs[])
      >- (rename[‘(RCS.E ⬝ x) ⬝ y ∈ M B’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >>
          gs[] >> metis_tac[]
         )
      >- (rename[‘(RCS.E ⬝ x) ⬝ y ∈ M C’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >>
          gs[] >> metis_tac[]
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_or >>
      rw[IMP_def, SUBSET_DEF]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘(RCS.E ⬝ x) ∈ Orthojoin (M A) (M B)’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x, M_SUBSET_RCS_W, SUBSET_DEF] >>
          ‘Orthojoin (M A) (M B) = j (M A ∪ M B)’ by metis_tac [R_MODEL_SYSTEM_ORTHOJOIN_J_UNION, M_IN_Ps_W] >>
          gs[] >> ‘M A ⊆ j (M A ∪ M B)’ suffices_by metis_tac[SUBSET_DEF] >>
          irule SUBSET_TRANS >> qexists_tac ‘M A ∪ M B’ >> strip_tac
          >- simp[SUBSET_UNION]
          >- (irule lemma6_3_1 >> rw[]
              >- metis_tac[to_CS_IS_COVER, R_MODEL_SYSTEM_R_COVER_SYSTEM]
              >- (irule Upset_UNION >> metis_tac[R_MODEL_SYSTEM_PS_UPSET, M_IN_Ps_W])
             )
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_or >>
      rw[IMP_def, SUBSET_DEF]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘(RCS.E ⬝ x) ∈ Orthojoin (M A) (M B)’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x, M_SUBSET_RCS_W, SUBSET_DEF] >>
          ‘Orthojoin (M A) (M B) = j (M A ∪ M B)’ by metis_tac [R_MODEL_SYSTEM_ORTHOJOIN_J_UNION, M_IN_Ps_W] >>
          gs[] >> ‘M B ⊆ j (M A ∪ M B)’ suffices_by metis_tac[SUBSET_DEF] >>
          irule SUBSET_TRANS >> qexists_tac ‘M A ∪ M B’ >> strip_tac
          >- simp[SUBSET_UNION]
          >- (irule lemma6_3_1 >> rw[]
              >- metis_tac[to_CS_IS_COVER, R_MODEL_SYSTEM_R_COVER_SYSTEM]
              >- (irule Upset_UNION >> metis_tac[R_MODEL_SYSTEM_PS_UPSET, M_IN_Ps_W])
             )
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_and >>
      drule_then strip_assume_tac Model_Function_or >>
      rw[IMP_def, SUBSET_DEF]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘(RCS.E ⬝ x) ∈ RCS.W’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >>
          gs[])
      >- (rename[‘(RCS.E ⬝ x) ⬝ y ∈ M C’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >>
          ‘Orthojoin (M A) (M B) = j (M A ∪ M B)’ by metis_tac [R_MODEL_SYSTEM_ORTHOJOIN_J_UNION, M_IN_Ps_W] >>
          gs[] >> qpat_x_assum ‘_ ∈ j _’ mp_tac >> rw[j_def] >>
          ‘Z ▹ y’ by gs[to_CS_def] >>
          ‘Localized (M C)’ by
            metis_tac [Is_Prop_def, corollary6_4_2, M_IN_Ps_W, M_SUBSET_RCS_W, R_MODEL_SYSTEM_PS_UPSET,
                       R_MODEL_SYSTEM_PS_ORTHOCLOSED, R_MODEL_SYSTEM_R_COVER_SYSTEM] >>
          gs[Localized_def] >> pop_assum mp_tac >> rw[SUBSET_DEF, j_def] >>
          pop_assum irule >> simp[PULL_EXISTS] >> qexists_tac ‘Z ⬝ x’ >> rw[]
          >- (‘(Z ⬝ x) ▹ (x ⬝ y)’ suffices_by simp[to_CS_def] >>
              ‘y ∈ RCS.W’ by gs[to_CS_def] >>
              ‘(Z ⬝ x) ▹ (y ⬝ x)’ suffices_by
                metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_COMM] >>
              irule RCS_FUSION_COVERING >> metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM]
             )
          >- (gs[op_Lift_1, SUBSET_DEF] >> rename[‘z ⬝ x ∈ M C’] >>
              first_x_assum $ qspec_then ‘z’ strip_assume_tac >> gs[] >>
              metis_tac[RCS_FUSION_COMM, M_SUBSET_RCS_W, SUBSET_DEF, R_MODEL_SYSTEM_R_COVER_SYSTEM]
             )
          >- (‘x ⬝ y ∈ RCS.W’ suffices_by simp[to_CS_def] >>
              ‘y ∈ RCS.W’ by gs[to_CS_def] >>
              metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_CLOSURE]
             )
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_and >>
      drule_then strip_assume_tac Model_Function_or >>
      rw[IMP_def, SUBSET_DEF]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘RCS.E ⬝ x ∈ Orthojoin (M A ∩ M B) (M A ∩ M C)’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x, M_SUBSET_RCS_W, SUBSET_DEF] >>
          ‘Orthojoin (M B) (M C) = j (M B ∪ M C)’ by metis_tac [R_MODEL_SYSTEM_ORTHOJOIN_J_UNION, M_IN_Ps_W] >>
          ‘Orthojoin (M A ∩ M B) (M A ∩ M C) = j ((M A ∩ M B) ∪ (M A ∩ M C))’ by
            metis_tac [R_MODEL_SYSTEM_ORTHOJOIN_J_UNION, M_IN_Ps_W] >>
          gs[] >> qpat_x_assum ‘x ∈ j (M B ∪ M C)’ mp_tac >> rw[j_def] >>
          qexists_tac ‘Z’ >>
          ‘Z ⊆ M A’ suffices_by
            metis_tac[SUBSET_DEF, UNION_OVER_INTER, SUBSET_INTER] >>
          irule SUBSET_TRANS >> qexists_tac ‘{w | x ≼ w ∧ w ∈ RCS.W}’ >> reverse $ rw[]
          >- (‘Upset (M A)’ by metis_tac[M_IN_Ps_W, R_MODEL_SYSTEM_PS_UPSET] >>
              gs[Upset_def] >> rw[SUBSET_DEF] >> last_x_assum irule >> rw[to_CS_def] >>
              metis_tac[]
             )
          >- (‘{w | x ≼ w ∧ w ∈ RCS.W} = Up (to_CS RCS) {x}’ by
                (rw[Up_def, Once EXTENSION, to_CS_def] >> metis_tac[]) >>
              gs[] >> irule (Is_Cover_System_def |> iffLR |> cj 4) >>
              metis_tac[to_CS_IS_COVER, R_MODEL_SYSTEM_R_COVER_SYSTEM, to_CS_def]
             )
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_not >>
      rw[IMP_def, SUBSET_DEF]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘RCS.E ⬝ x ∈ RCS.W’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >>
          gs[])
      >- (rename[‘(RCS.E ⬝ x) ⬝ y ∈ Perp (M A)’] >>
          ‘(RCS.E ⬝ x) = x’ by metis_tac[E_x_is_x] >> simp[] >>
          gs[Perp_def, PULL_EXISTS] >> rpt strip_tac
          >- metis_tac[M_SUBSET_RCS_W, SUBSET_DEF, R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_FUSION_CLOSURE]
          >- (rename[‘(x ⬝ y) ⊥ z’] >> last_x_assum $ qspec_then ‘z’ strip_assume_tac >>
              ‘∀x'. x' ∈ M B ⇒ (x ⬝ z) ⊥ x'’ by metis_tac[M_SUBSET_RCS_W, SUBSET_DEF] >>
              irule RCS_CONTRAPOSITION >>
              metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, M_SUBSET_RCS_W, SUBSET_DEF]
             )
         )
     )
  >- (drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_not >>
      rw[IMP_def, SUBSET_DEF]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (rename[‘RCS.E ⬝ x ∈ M A’] >>
          ‘(RCS.E ⬝ x) = x’ by (gs[Perp_def] >> metis_tac[E_x_is_x]) >>
          gs[] >> ‘M A = Perp (Perp (M A))’ suffices_by metis_tac[] >>
          metis_tac[M_IN_Ps_W, R_MODEL_SYSTEM_PS_ORTHOCLOSED]
         )
     )
  >- (‘C_Holds RCS Ps M RCS.E p’ by gs[] >>
      ‘C_Holds RCS Ps M RCS.E p'’ by gs[] >>
      drule_then strip_assume_tac Model_Function_and >>
      gs[C_Holds_def]
     )
  >- (‘C_Holds RCS Ps M RCS.E p’ by gs[] >>
      ‘C_Holds RCS Ps M RCS.E (p --> p')’ by gs[] >>
      drule_then strip_assume_tac Model_Function_imp >>
      gs[C_Holds_def, IMP_def, SUBSET_DEF] >> last_x_assum irule >>
      qexists_tac ‘RCS.E’ >> simp[] >>
      metis_tac[RCS_FUSION_RIGHT_IDENTITY, R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
     )
  >- (‘C_Holds RCS Ps M RCS.E p’ by gs[] >>
      drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_t >>
      gs[C_Holds_def, IMP_def, SUBSET_DEF] >> rw[]
      >- metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_IDENTITY]
      >- (‘Upset (M p)’ by metis_tac[M_IN_Ps_W, R_MODEL_SYSTEM_PS_UPSET] >>
          gs[Upset_def] >> last_x_assum irule >> rw[] >~
          [‘RCS.E ⬝ y ∈ (to_CS RCS).W’]
          >- (‘RCS.E ⬝ y ∈ RCS.W’ suffices_by rw[to_CS_def] >>
              gs[Up_def, to_CS_def] >>
              metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM,
                        RCS_FUSION_LEFT_IDENTITY]) >~
          [‘y ∈ Up (to_CS RCS) {RCS.E}’]
          >- (qexists_tac ‘RCS.E’ >> simp[] >>
              ‘RCS.E ≼ (RCS.E ⬝ y)’ suffices_by rw[to_CS_def] >>
              ‘(RCS.E ⬝ RCS.E) ≼ (RCS.E ⬝ y)’
                suffices_by (gs[Up_def, to_CS_def] >>
                             metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM,
                                       RCS_FUSION_LEFT_IDENTITY]) >>
              irule RCS_FUSION_MONO_REFINEMENT >> simp[] >>
              gs[Up_def, to_CS_def] >>
              metis_tac[R_MODEL_SYSTEM_R_COVER_SYSTEM, RCS_PREORDER,
                        PREORDER_def, SUBSET_DEF, RCS_IDENTITY])
         )
     )
  >- (‘C_Holds RCS Ps M RCS.E (τ --> p)’ by gs[] >>
      drule_then strip_assume_tac Model_Function_imp >>
      drule_then strip_assume_tac Model_Function_t >>
      gs[C_Holds_def, IMP_def, SUBSET_DEF] >>
      last_x_assum irule >>
      qexists_tac ‘RCS.E’ >> gs[Up_def, to_CS_def] >>
      metis_tac[RCS_FUSION_RIGHT_IDENTITY, R_MODEL_SYSTEM_R_COVER_SYSTEM,
                RCS_PREORDER, PREORDER_def, SUBSET_DEF, RCS_IDENTITY])
QED

Definition ENTAILS_def:
  ENTAILS A B ⇔
    |- (A --> B)
End

val _ = set_fixity "|-^" (Infixr 490);

Overload "|-^" = “ENTAILS”

Theorem ENTAILS_PREORDER:
  PREORDER ENTAILS (𝕌(:g_prop))
Proof
  rw[PREORDER_def, ENTAILS_def] >>
  metis_tac[goldblatt_provable_rules]
QED

Theorem ENTAILS_REFL:
  ∀A. A |-^ A
Proof
  rw[ENTAILS_def] >>
  metis_tac[goldblatt_provable_rules]
QED

Theorem ENTAILS_TRANS:
  ∀A B C. A |-^ B ∧ B |-^ C ⇒
      A |-^ C
Proof
  rw[ENTAILS_def] >>
  metis_tac[goldblatt_provable_rules]
QED

Theorem ENTAILS_AND:
  ∀ A B C. A |-^ (B & C) ⇔ (A |-^ B ∧ A |-^ C)
Proof
  rw[EQ_IMP_THM, ENTAILS_def] >>
  metis_tac[goldblatt_provable_rules]
QED

Theorem OR_ENTAILS:
  ∀ A B C. A |-^ C ∧ B |-^ C ⇒ (A V B) |-^ C
Proof
  rw[EQ_IMP_THM, ENTAILS_def] >>
  metis_tac[goldblatt_provable_rules]
QED

Theorem ENTAILS_CONTRAPOS:
  ∀A B. A |-^ (~B) ⇒ B |-^ (~A)
Proof
  rw[EQ_IMP_THM, ENTAILS_def] >>
  metis_tac[goldblatt_provable_rules]
QED

Theorem ENTAILS_DOUBLE_NEG:
  ∀A. A |-^ (~~A) ∧ (~~A) |-^ A
Proof
  rw[ENTAILS_def] >>
  metis_tac[goldblatt_provable_rules]
QED

Theorem ENTAILS_CONTRAPOS_alt:
  ∀A B. A |-^ B ⇒ (~B) |-^ (~A)
Proof
  rw[] >>
  metis_tac[ENTAILS_CONTRAPOS, ENTAILS_DOUBLE_NEG, ENTAILS_TRANS]
QED

Theorem ENTAILS_ICONJ_COMM:
  ∀A B. (A ∘ᵣ B) |-^ (B ∘ᵣ A)
Proof
  rw[ENTAILS_def] >>
  metis_tac[goldblatt_provable_rules, g_io_commutative_lr]
QED

Theorem ENTAILS_ICONJ_MONOTONE:
  ∀A B C. A |-^ B ⇒
          (A ∘ᵣ C) |-^ (B ∘ᵣ C) ∧ (C ∘ᵣ A) |-^ (C ∘ᵣ B)
Proof
   metis_tac[yeet, ENTAILS_REFL, ENTAILS_def]
QED

Theorem ENTAILS_ICONJ_MONOTONE_alt:
  ∀A B C D. A |-^ B ∧ C |-^ D ⇒
          (A ∘ᵣ C) |-^ (B ∘ᵣ D) ∧ (C ∘ᵣ A) |-^ (D ∘ᵣ B)
Proof
   metis_tac[yeet, ENTAILS_REFL, ENTAILS_def]
QED

Theorem ENTAILS_ICONJ_RULE:
  ∀A B C. (A ∘ᵣ B) |-^ C ⇔
          A |-^ (B --> C)
Proof
  metis_tac[EQ_IMP_THM, g_io_rule, ENTAILS_def]
QED

Theorem ENTAILS_ICONJ_ASSOC:
  ∀A B C. ((A ∘ᵣ B)∘ᵣ C) |-^ (A ∘ᵣ ( B ∘ᵣ C)) ∧
          (A ∘ᵣ ( B ∘ᵣ C)) |-^ ((A ∘ᵣ B)∘ᵣ C)
Proof
  metis_tac[g_io_associative_rl, ENTAILS_def, ENTAILS_TRANS, ENTAILS_ICONJ_COMM]
QED

Theorem ENTAILS_ICONJ_T:
  ∀A. (τ ∘ᵣ A) |-^ A ∧ A |-^ (τ ∘ᵣ A)
Proof
  metis_tac[ENTAILS_def, g_DIMP_def, goldblatt_provable_rules, g_io_true]
QED

Theorem ENTAILS_ICONJ_SELF:
  ∀A. A |-^ (A ∘ᵣ A)
Proof
  metis_tac[g_io_imp, ENTAILS_def]
QED

Definition Theory_def:
  Theory A = {B | A |-^ B}
End

Theorem Theory_closed_ENTAILS:
  ∀ A B C. B ∈ Theory A ∧ B |-^ C ⇒
           C ∈ Theory A
Proof
  rw[Theory_def] >>
  metis_tac[ENTAILS_TRANS]
QED

Theorem Theory_closed_CONJ:
  ∀A B C. B ∈ Theory A ∧ C ∈ Theory A ⇒
          B & C ∈ Theory A
Proof
  rw[Theory_def, ENTAILS_AND]
QED

Theorem Theory_SUBSET:
  ∀A B. A |-^ B ⇔ Theory B ⊆ Theory A
Proof
  rw[SUBSET_DEF, ENTAILS_def, Theory_def, EQ_IMP_THM]
  >> metis_tac[goldblatt_provable_rules]
QED

Theorem Theory_EQ:
  ∀A B. A |-^ B ∧ B |-^ A ⇔ Theory A = Theory B
Proof
  metis_tac[Theory_SUBSET, SUBSET_ANTISYM_EQ]
QED

Definition gens_def:
  gens X = {A | Theory A = X}
End

Definition EQUIV_def:
  EQUIV A = {B | B |-^ A ∧ A |-^ B}
End

Definition is_EQUIV_def:
  is_EQUIV X ⇔ ∃A. X = EQUIV A ∨ X = ∅
End

Definition Theory_union_def:
  Theory_union X = BIGUNION {Theory A | A ∈ X}
End

Theorem gens_is_EQUIV:
  ∀X. is_EQUIV (gens X)
Proof
  rw[] >> Cases_on ‘gens X = ∅’
  >- rw[is_EQUIV_def]
  >- (‘∃x. x ∈ gens X’ by metis_tac[MEMBER_NOT_EMPTY] >>
      gs[gens_def] >> rw[is_EQUIV_def, EQUIV_def] >>
      qexists_tac ‘x’ >> simp[EXTENSION] >>
      rw[Once EQ_IMP_THM]
      >- gs[Theory_def, g_identity, ENTAILS_def]
      >- (last_x_assum $ qspec_then ‘x'’ strip_assume_tac >>
          gs[Theory_def, g_identity, ENTAILS_def])
      >- (rw[Theory_def, EQ_IMP_THM] >>
           metis_tac[ENTAILS_TRANS])
     )
QED

Theorem Theorem_EQUIV:
  ∀A. Theory_union (EQUIV A) = Theory A
Proof
  rw[EQUIV_def, EQ_IMP_THM] >>
  irule SUBSET_ANTISYM >> reverse $ rw[]
  >- (rw[Theory_union_def, BIGUNION, PULL_EXISTS, SUBSET_DEF] >>
      qexists_tac ‘A’ >> metis_tac[ENTAILS_REFL]
     )
  >- (rw[Theory_union_def, BIGUNION, PULL_EXISTS, SUBSET_DEF, Theory_EQ] >>
     gs[])
QED


Definition CAN_FUSION_def:
  CAN_FUSION X Y = Theory_union {x ∘ᵣ y | x ∈ gens X ∧ y ∈ gens Y}
End

Definition CAN_ORTH_def:
  CAN_ORTH X Y = ∃A B. A ∈ gens X ∧ B ∈ gens Y ∧ A |-^ (~B)
End

Definition Canonical_System_def:
  Canonical_System = <|W := {Theory A | A ∈ 𝕌(:g_prop)};
                       REF := (λx y. x ⊆ y ∧ x ∈ {Theory A | A ∈ 𝕌(:g_prop)} ∧ y ∈ {Theory A | A ∈ 𝕌(:g_prop)});
                       COVER := (λZ x. BIGINTER Z = x ∧ x ∈ {Theory A | A ∈ 𝕌(:g_prop)} ∧ Z ⊆ {Theory A | A ∈ 𝕌(:g_prop)});
                       E := Theory τ;
                       FUSE := CAN_FUSION; ORTH := CAN_ORTH |>
End

Definition EQUIV_W_def:
  EQUIV_W A = {w | A ∈ w ∧ w ∈ Canonical_System.W}
End

Definition Canonical_System_Ps_def:
  Canonical_System_Ps = {EQUIV_W A | A ∈ 𝕌(:g_prop)}
End


val _= set_mapped_fixity {term_name = "gBOTc", fixity = Infix (NONASSOC, 450), tok="⊥ₘ"};
val _= set_mapped_fixity {term_name = "gFUSEc", fixity = Infix (NONASSOC, 450), tok="⬝ₘ"};
val _= set_mapped_fixity {term_name = "gREFc", fixity = Infix (NONASSOC, 450), tok="≼ₘ"};
val _= set_mapped_fixity {term_name = "gCOVERc", fixity = Infix (NONASSOC, 450), tok="▹ₘ"};
val _= set_mapped_fixity {term_name = "gIMPPc", fixity = Infix (NONASSOC, 450), tok="⟹ₘ"};

Overload "gBOTc" = “λ x y. Canonical_System.ORTH (x: g_prop set) y”
Overload "gBOTc" = “λ x y. rel_Lift_1 Canonical_System.ORTH (x: (g_prop set) set) y”
Overload "gBOTc" = “λ x y. rel_Lift_2 Canonical_System.ORTH (x: g_prop set) y”

Overload "gFUSEc" = “λ x y. Canonical_System.FUSE (x: g_prop set) y”
Overload "gFUSEc" = “λ x y. op_Lift_1 Canonical_System.FUSE (x: (g_prop set) set) y”
Overload "gFUSEc" = “λ x y. op_Lift_2 Canonical_System.FUSE (x: g_prop set) y”

Overload "gREFc" = “λ x y. Canonical_System.REF (x: g_prop set) y”

Overload "gCOVERc" = “λ (x : (g_prop set) set) y. Canonical_System.COVER x y”


Overload "j" = “λ (X: (g_prop set) set). j (to_CS Canonical_System) X”
Overload "Upset" = “λ (X: (g_prop set) set). Upset (to_CS Canonical_System) X”
Overload "Localized" = “λ (X: (g_prop set) set). Localized (to_CS Canonical_System) X”
Overload "Perp" = “λ (X: (g_prop set) set). Perp Canonical_System X”
Overload "gIMPPc" = “λ (x : (g_prop set) set) y. IMP Canonical_System x y”
Overload "Orthojoin" = “λ (X: (g_prop set) set). Orthojoin Canonical_System X”

Theorem CAN_FUSION_alt:
  ∀A B. CAN_FUSION (Theory A) (Theory B) = Theory (A ∘ᵣ B)
Proof
  reverse $ rw[CAN_FUSION_def] >> irule SUBSET_ANTISYM >> reverse $ rw[]
  >- (rw[Theory_union_def, BIGUNION, PULL_EXISTS, SUBSET_DEF] >>
      qexistsl_tac [‘A’, ‘B’] >> simp[gens_def])
  >- (rw[Theory_union_def, BIGUNION, PULL_EXISTS, SUBSET_DEF] >>
      gs[gens_def, GSYM Theory_EQ] >> gs[Theory_def] >>
      metis_tac[ENTAILS_TRANS, ENTAILS_ICONJ_MONOTONE_alt])
QED

Theorem CAN_ORTH_alt:
  ∀A B. CAN_ORTH (Theory A) (Theory B) ⇔ A |-^ (~B)
Proof
  rw[CAN_ORTH_def, EQ_IMP_THM, gens_def]
  >- (gs[GSYM Theory_EQ] >>
      metis_tac[ENTAILS_TRANS, ENTAILS_CONTRAPOS_alt])
  >- metis_tac[]
QED

Theorem Canonical_System_is_RCS:
  Is_Relevant_Cover_System Canonical_System
Proof
  rw[Is_Relevant_Cover_System_def]
  >- (gs[Canonical_System_def] >> metis_tac[])
  >- (gs[Canonical_System_def] >> metis_tac[])
  >- (gs[Canonical_System_def] >> metis_tac[])
  >- (gs[Canonical_System_def] >> metis_tac[])
  >- (gs[Canonical_System_def] >> metis_tac[])
  >- (gs[Canonical_System_def] >> metis_tac[CAN_FUSION_alt])
  >- (gs[Canonical_System_def] >> gs[CAN_ORTH_def, gens_def] >> metis_tac[])
  >- (gs[Canonical_System_def] >> gs[CAN_ORTH_def, gens_def] >> metis_tac[])
  >- (rw[Canonical_System_def, to_CS_def, Is_Cover_System_def]
      >- (rw[PREORDER_def] >> metis_tac[SUBSET_TRANS])
      >- (qexists_tac ‘{Theory A}’ >> simp[BIGINTER] >> metis_tac[])
      >- (rw[Up_def, SUBSET_DEF] >> gs[SUBSET_DEF, BIGINTER, EXTENSION] >>
          metis_tac[])
     )
  >- (gs[Canonical_System_def, CAN_FUSION_alt, GSYM Theory_EQ] >>
      metis_tac[ENTAILS_ICONJ_T, ENTAILS_ICONJ_COMM, ENTAILS_TRANS])
  >- gs[Canonical_System_def, CAN_FUSION_alt, GSYM Theory_EQ, ENTAILS_ICONJ_T]
  >- gs[Canonical_System_def, CAN_FUSION_alt, GSYM Theory_EQ, ENTAILS_ICONJ_COMM]
  >- gs[Canonical_System_def, CAN_FUSION_alt, GSYM Theory_EQ, ENTAILS_ICONJ_ASSOC]
  >- (gs[Canonical_System_def] >> rw[]
      >- gs[CAN_FUSION_alt, GSYM Theory_SUBSET, ENTAILS_ICONJ_MONOTONE_alt]
      >- metis_tac[CAN_FUSION_alt, GSYM Theory_EQ]
      >- metis_tac[CAN_FUSION_alt, GSYM Theory_EQ]
     )
  >- (gs[Canonical_System_def] >> rw[]
      >- gs[CAN_FUSION_alt, GSYM Theory_SUBSET, ENTAILS_ICONJ_SELF]
      >- metis_tac[CAN_FUSION_alt, GSYM Theory_EQ]
      >- metis_tac[]
     )
  >- (gs[Canonical_System_def] >> rw[]
      >- (irule SUBSET_ANTISYM >> reverse $ rw[]
          >- (rw[op_Lift_1, BIGINTER, PULL_EXISTS, SUBSET_DEF] >>
              gs[SUBSET_DEF] >>
              last_x_assum $ qspec_then ‘x'’ strip_assume_tac >>
              gs[] >>
              rename [‘BIGINTER Z = Theory A’,
                      ‘x ∈ CAN_FUSION (Theory A) (Theory B)’,
                      ‘x' = Theory C’] >> gs[CAN_FUSION_alt] >>
              qpat_x_assum ‘x ∈ Theory (A ∘ᵣ B)’ mp_tac >> rw[Theory_def] >>
              ‘C |-^ A’ suffices_by
                metis_tac[ENTAILS_ICONJ_MONOTONE, ENTAILS_TRANS] >>
              gs[BIGINTER, Theory_def, EXTENSION] >>
              last_x_assum $ qspec_then ‘A’ strip_assume_tac >>
              gs[ENTAILS_REFL] >> last_x_assum $ qspec_then ‘{B | C |-^ B}’ strip_assume_tac >>
              gs[])
          >- (rw[SUBSET_DEF, op_Lift_1] >>
              rename[‘D ∈ CAN_FUSION (Theory A) (Theory B)’] >>
              gs[CAN_FUSION_alt, PULL_EXISTS, SUBSET_DEF] >>
              ‘∀C. Theory C ∈ Z ⇒ B --> D ∈ Theory C’ by
                (rw[] >> first_x_assum $ qspec_then ‘Theory C’ strip_assume_tac >>
                 gs[CAN_FUSION_alt, Theory_def, ENTAILS_ICONJ_RULE]) >>
              ‘B --> D ∈ Theory A’ suffices_by
                gs[Theory_def, GSYM ENTAILS_ICONJ_RULE] >>
              gs[BIGINTER, EXTENSION] >> last_x_assum $ qspec_then ‘B --> D’ strip_assume_tac >>
              pop_assum mp_tac >> rw[EQ_IMP_THM] >> qpat_x_assum ‘_ ⇒ B --> D ∈ Theory A’ irule >>
              rw[] >> last_x_assum $ qspec_then ‘P’ strip_assume_tac >> gs[] >>
              metis_tac[EXTENSION])
         )
      >- (gs[] >> metis_tac[CAN_FUSION_alt])
      >- (simp[op_Lift_1] >> gs[SUBSET_DEF] >> rw[] >>
          metis_tac[CAN_FUSION_alt])
     )
  >- (gs[Canonical_System_def] >> rw[] >>
      rename[‘Theory A ⊆ Theory A'’,
             ‘Theory B ⊆ Theory B'’] >>
      gs[CAN_ORTH_alt, GSYM Theory_SUBSET] >>
      metis_tac[ENTAILS_TRANS, ENTAILS_CONTRAPOS_alt]
     )
  >- (gs[Canonical_System_def, rel_Lift_1] >> rw[] >>
      ‘∀C. Theory C ∈ Z ⇒ CAN_ORTH (Theory C) (Theory τ)’ by gs[] >>
      gs[CAN_ORTH_alt] >>
      ‘~τ ∈ BIGINTER Z’ suffices_by
        (strip_tac >> gs[Theory_def, EXTENSION]) >>
      gs[SUBSET_DEF] >> rw[] >>
      last_x_assum $ qspec_then ‘P’ strip_assume_tac >> gs[] >>
      simp[Theory_def]
     )
  >- (gs[Canonical_System_def, CAN_ORTH_alt, CAN_FUSION_alt] >>
      pop_assum mp_tac >>
      rename[‘(A ∘ᵣ B) |-^ ~C ⇒ (A ∘ᵣ C) |-^ ~B’] >> rw[] >>
      gs[ENTAILS_ICONJ_RULE] >> metis_tac[ENTAILS_TRANS, ENTAILS_def, g_contrapositive]
     )
QED

Theorem lemma6_5_3_1:
 ∀A. Up (to_CS Canonical_System) {Theory A} = EQUIV_W A
Proof
  rw[Up_def, Once EXTENSION, Once EQ_IMP_THM, to_CS_def, Canonical_System_def, EQUIV_W_def]
  >- (gs[SUBSET_DEF, Theory_def] >> last_x_assum irule >>
      gs[EXTENSION] >> metis_tac[ENTAILS_REFL])
  >- (gs[SUBSET_DEF, Theory_def] >> metis_tac[ENTAILS_TRANS])
  >- metis_tac[]
QED

Theorem lemma6_5_3_2:
  ∀A B. EQUIV_W A ∩ EQUIV_W B = EQUIV_W (A & B)
Proof
  rw[EQUIV_W_def, Canonical_System_def, Once EXTENSION, EQ_IMP_THM] >>
  gs[Theory_def] >> metis_tac[ENTAILS_AND]
QED

Theorem lemma6_5_3_3:
  ∀A. Perp (EQUIV_W A) = EQUIV_W (~A)
Proof
  rw[] >> irule SUBSET_ANTISYM >> rw[]
  >- (rw[Once SUBSET_DEF, EQUIV_W_def] >> gs[Perp_def] >>
      last_x_assum $ qspec_then ‘Theory A’ strip_assume_tac >>
      gs[Canonical_System_def] >>
      ‘CAN_ORTH (Theory A') (Theory A)’ by (gs[Theory_def, ENTAILS_REFL] >> metis_tac[]) >>
      gs[CAN_ORTH_alt, Theory_def])
  >- (rw[Once SUBSET_DEF, EQUIV_W_def, Perp_def, Canonical_System_def] >>
      gs[CAN_ORTH_alt, Theory_def] >> metis_tac[ENTAILS_TRANS, ENTAILS_CONTRAPOS])
QED

Theorem lemma6_5_3_4:
  ∀A B. (EQUIV_W A ⟹ₘ EQUIV_W B) = EQUIV_W (A --> B)
Proof
  rw[] >> irule SUBSET_ANTISYM >> rw[]
  >- (rw[Once SUBSET_DEF, EQUIV_W_def]
      >- (gs[IMP_def, Canonical_System_def] >>
          rename[‘x = Theory C’] >> gs[SUBSET_DEF, PULL_EXISTS, CAN_FUSION_alt] >>
          last_x_assum $ qspec_then ‘A’ strip_assume_tac >>
          gs[Theory_def, ENTAILS_REFL, ENTAILS_ICONJ_RULE])
      >- gs[IMP_def]
     )
  >- (rw[Once SUBSET_DEF, EQUIV_W_def, IMP_def, Canonical_System_def] >>
      rename[‘A --> B ∈ Theory C’] >> rw[SUBSET_DEF, PULL_EXISTS, CAN_FUSION_alt] >>
      qexists_tac ‘C ∘ᵣ A'’ >> gs[Theory_def] >>
      metis_tac[ENTAILS_ICONJ_RULE, ENTAILS_ICONJ_MONOTONE, ENTAILS_TRANS])
QED

Theorem lemma6_5_3_5:
   ∀A B. Orthojoin (EQUIV_W A) (EQUIV_W B) = EQUIV_W (A V B)
Proof
  rw[Orthojoin_def, g_OR_def] >> simp[GSYM lemma6_5_3_2, GSYM lemma6_5_3_3] >>
  ‘Perp (EQUIV_W A ∪ EQUIV_W B) = Perp (EQUIV_W A) ∩ Perp (EQUIV_W B)’ suffices_by
    metis_tac[] >>
  simp[Perp_def, EXTENSION] >> metis_tac[]
QED

Theorem Canonical_System_is_R_Model_system:
  R_MODEL_SYSTEM Canonical_System Canonical_System_Ps
Proof
  rw[R_MODEL_SYSTEM_def, Canonical_System_is_RCS]
  >- (simp[Canonical_System_Ps_def, GSYM lemma6_5_3_1] >>
      qexists_tac ‘τ’ >> simp[Canonical_System_def])
  >- gs[Canonical_System_Ps_def, Upset_def, to_CS_def,
        EQUIV_W_def, Canonical_System_def, SUBSET_DEF]
  >- (gs[Canonical_System_Ps_def, lemma6_5_3_3] >>
      rw[EQUIV_W_def, Canonical_System_def, Once EXTENSION, EQ_IMP_THM, Theory_def] >>
      gs[] >> metis_tac[ENTAILS_DOUBLE_NEG, ENTAILS_TRANS])
  >- (gs[Canonical_System_Ps_def] >> metis_tac[lemma6_5_3_3])
  >- (gs[Canonical_System_Ps_def] >> metis_tac[lemma6_5_3_2])
  >- (gs[Canonical_System_Ps_def] >> metis_tac[lemma6_5_3_4])
  >- (gs[Canonical_System_Ps_def] >>
      rename[‘Orthojoin (EQUIV_W A) (EQUIV_W B) = j (EQUIV_W A ∪ EQUIV_W B)’] >>
      irule SUBSET_ANTISYM >> reverse $ rw[]
      >- (simp[Orthojoin_def] >> assume_tac Canonical_System_is_RCS >>
          drule_then strip_assume_tac lemma6_4_1_6 >>
          pop_assum $ qspec_then ‘EQUIV_W A ∪ EQUIV_W B’ strip_assume_tac >>
          ‘EQUIV_W A ∪ EQUIV_W B ⊆ Canonical_System.W’ by
            simp[SUBSET_DEF, EQUIV_W_def] >>
          metis_tac[SUBSET_TRANS])
      >- (rw[lemma6_5_3_5, SUBSET_DEF] >>
          ‘∃C. x = Theory C’ by
            (gs[EQUIV_W_def, Canonical_System_def] >> metis_tac[]) >> gs[] >>
          ‘Up (to_CS Canonical_System) {x} = EQUIV_W C’ by gs[lemma6_5_3_1] >>
          rpt strip_tac >> simp[j_def, to_CS_def, PULL_EXISTS] >>
          qexists_tac ‘(EQUIV_W C ∩ EQUIV_W A) ∪ (EQUIV_W C ∩ EQUIV_W B)’ >> rw[SUBSET_DEF]
          >- (simp[Canonical_System_def] >> metis_tac[])
          >- (qabbrev_tac ‘Z = EQUIV_W C ∩ EQUIV_W A ∪ EQUIV_W C ∩ EQUIV_W B’ >>
              reverse $ rw[Canonical_System_def]
              >- simp[EQUIV_W_def, SUBSET_DEF, Canonical_System_def, Abbr‘Z’]
              >- metis_tac[]
              >- (irule SUBSET_ANTISYM >> reverse $ rw[]
                  >- (‘Z ⊆ EQUIV_W C’ by simp[Abbr‘Z’] >>
                      rw[SUBSET_DEF] >> gs[EQUIV_W_def, SUBSET_DEF] >>
                      last_x_assum $ qspec_then ‘P’ strip_assume_tac >> gs[] >>
                      ‘∃D. P = Theory D’ by
                        (gs[Canonical_System_def] >> metis_tac[]) >> gs[Theory_def] >>
                      metis_tac[ENTAILS_TRANS])
                  >- (gs[lemma6_5_3_2] >> rw[SUBSET_DEF, Abbr‘Z’] >>
                      ‘x ∈ Theory (C & A)’ by
                        (last_x_assum irule >>
                         simp[EQUIV_W_def, Canonical_System_def, Theory_def] >>
                         metis_tac[ENTAILS_REFL]) >>
                      ‘x ∈ Theory (C & B)’ by
                         (last_x_assum irule >>
                         simp[EQUIV_W_def, Canonical_System_def, Theory_def] >>
                          metis_tac[ENTAILS_REFL]) >>
                      gs[Theory_def, EQUIV_W_def] >>
                      ‘(C & (A V B)) |-^ ((C & A) V C & B)’ by metis_tac[ENTAILS_def, g_distribution] >>
                      ‘C |-^ (C & A) V C & B’ by
                        metis_tac[OR_ENTAILS, ENTAILS_TRANS, ENTAILS_AND, ENTAILS_REFL] >>
                      metis_tac[OR_ENTAILS, ENTAILS_TRANS]
                     )
                 )
             )
         )
     )
QED


Theorem Model_System_Characterisation_1_2:
  ∀p. |- p ⇒ (∀RCS Ps M. R_MODEL_SYSTEM RCS Ps ∧ Model_Function RCS Ps M ⇒ C_Holds RCS Ps M RCS.E p)
Proof
  gs[soundness]
QED

Theorem Model_System_Characterisation_2_3:
  ∀p. (∀RCS Ps M. R_MODEL_SYSTEM RCS Ps ∧ Model_Function RCS Ps M ⇒ C_Holds RCS Ps M RCS.E p) ⇒
      ∀M. Model_Function Canonical_System Canonical_System_Ps M ⇒
          C_Holds Canonical_System Canonical_System_Ps M Canonical_System.E p
Proof
  rw[] >> last_x_assum irule >> gs[Canonical_System_is_R_Model_system]
QED

Theorem Model_System_Characterisation_3_1:
  ∀p. (∀M. Model_Function Canonical_System Canonical_System_Ps M ⇒
            C_Holds Canonical_System Canonical_System_Ps M Canonical_System.E p)
      ⇒ |- p
Proof
  rw[] >> last_x_assum $ qspec_then ‘λx. EQUIV_W x’ strip_assume_tac >>
  ‘Model_Function Canonical_System Canonical_System_Ps (λx. EQUIV_W x)’ by
    (rw[Model_Function_def]
     >- (rw[Canonical_System_Ps_def] >> metis_tac[])
     >- (rw[GSYM lemma6_5_3_1, Up_def, Theory_def, to_CS_def, EXTENSION, Once EQ_IMP_THM]
         >- (qexists_tac ‘w’ >> simp[] >>
             gs[Canonical_System_def, to_CS_def, Theory_def])
         >- (qexists_tac ‘Canonical_System.E’ >>
             gs[Canonical_System_def, Theory_def] >> metis_tac[])
        )
     >- gs[GSYM lemma6_5_3_2]
     >- gs[GSYM lemma6_5_3_4]
     >- gs[GSYM lemma6_5_3_3]
    ) >>
  gs[C_Holds_def, EQUIV_W_def, Canonical_System_def, Theory_def] >>
  metis_tac[goldblatt_provable_rules, ENTAILS_def]
QED

Theorem completeness:
  (∀RCS Ps M. R_MODEL_SYSTEM RCS Ps ∧ Model_Function RCS Ps M ⇒ C_Holds RCS Ps M RCS.E p) ⇒
  |- p
Proof
  rw[] >> drule_then strip_assume_tac Model_System_Characterisation_2_3 >>
  rw[] >> irule Model_System_Characterisation_3_1 >> gs[]
QED

val _ = export_theory();
