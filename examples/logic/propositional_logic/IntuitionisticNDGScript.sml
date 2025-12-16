
(* ========================================================================== *)
(* Equivalence of Sequent Calculus and Natural Deduction                      *)
(* Working from Troelstra and Schwichtenburg - Basic Proof Theory 2nd Edition *)
(* Written by Alexander Cox, ANU, u6060697@anu.edu.au                         *)
(* Supervised by Michael Norrish, ANU; Data61                                 *)
(* ========================================================================== *)
Theory IntuitionisticNDG
Ancestors
  bag pred_set ipropSyntax


(* Natural Deduction for intuitionistic logic                      *)
(* N is the 'deduciblility' relation for this system               *)
(* A, B and C are used to represent formulae                       *)
(* D, D1, D2, D3 are used to represent the set of open assumptions *)
(* I'm representing the deductions simply with unlabeled sets of   *)
(*   open assumptions, as in T&S 2.1.8-2.1.9 (p.41--44)            *)

Inductive N:
[~ax:]
  ∀ A. N {A} A
[~andi:]
  ∀A B D1 D2.
    N D1 A ∧ N D2 B ==> N (D1 ∪ D2) (A ∧ⁱ B)
[~andel:]
  ∀A B D. N D (A ∧ⁱ B) ==> N D A
[~ander:]
  ∀A B D. N D (A ∧ⁱ B) ==> N D B
[~impi:]
  ∀A B D. N (A INSERT D) B ==> N D (A ⇒ⁱ B)
[~impe:]
  ∀A B D1 D2.
    N D1 (A ⇒ⁱ B) ∧ N D2 A
    ==> N (D1 ∪ D2) B
[~oril:]
  ∀A B D. N D A ==> N D (A ∨ⁱ B)
[~orir:]
  ∀A B D. N D B ==> N D (A ∨ⁱ B)
[~ore:]
  ∀A B C D D1 D2.
    N D (A ∨ⁱ B) ∧ N (A INSERT D1) C ∧ N (B INSERT D2) C ==>
    N (D ∪ D1 ∪ D2) C
[~bot:]
  ∀A D. N D ⊥ⁱ ==> N D A
End

Theorem N_FINITE:
  ∀D A. N D A ==> FINITE D
Proof Induct_on ‘N’ >> rw[]
QED

(* Natural deduction with a slightly different ∨-elimination rule *)
Inductive Nd:
[~ax:]
  ∀ A. Nd {A} A
[~andi:]
  ∀A B D1 D2. Nd D1 A ∧ Nd D2 B
              ==> Nd (D1 UNION D2) (A ∧ⁱ B)
[~andel:]
  ∀A B D. (Nd D (A ∧ⁱ B)) ==> Nd D A
[~ander:]
  ∀A B D. (Nd D (A ∧ⁱ B)) ==> Nd D B
[~impi:]
  ∀A B D. (Nd D B) ==> Nd (D DELETE A) (A ⇒ⁱ B)
[~impe:]
  ∀A B D1 D2. (Nd D1 (A ⇒ⁱ B)) ∧ (Nd D2 A)
              ==> Nd (D1 UNION D2) B
[~oril:]
  ∀A B D. Nd D A ==> Nd D (A ∨ⁱ B)
[~orir:]
  ∀A B D. Nd D B ==> Nd D (A ∨ⁱ B)
[~ore:]
  ∀A B C D D1 D2.
    Nd D (A ∨ⁱ B) ∧ Nd D1 C ∧ Nd D2 C
    ==> Nd (D ∪ (D1 DELETE A) ∪ (D2 DELETE B)) C
[~bot:]
  ∀A D. (Nd D ⊥ⁱ) ==> (Nd D A)
End

Theorem N_lw:
  ∀D A. N D A ==> ∀B. N (B INSERT D) A
Proof
  rw[] >>
  ‘N {B} B’ by metis_tac[N_ax] >>
  ‘N ({B} ∪ D) (B ∧ⁱ A)’ by metis_tac[N_andi] >>
  ‘N ({B} ∪ D) A’ by metis_tac[N_ander] >>
  metis_tac[INSERT_SING_UNION]
QED

Theorem Nd_lw:
∀D A. Nd D A ==> ∀B. Nd (B INSERT D) A
Proof
  rw[] >>
  ‘Nd {B} B’ by metis_tac[Nd_ax] >>
  ‘Nd ({B} ∪ D) (B ∧ⁱ A)’ by metis_tac[Nd_andi] >>
  ‘Nd ({B} ∪ D) A’ by metis_tac[Nd_ander] >>
  metis_tac[INSERT_SING_UNION]
QED

Theorem N_lw_SUBSET:
  ∀D'. FINITE D' ==> ∀D A. N D A  ∧ D ⊆ D' ==> N D' A
Proof
  GEN_TAC >>
  Induct_on ‘CARD D'’
  >- (rw[] >>
      metis_tac[CARD_EQ_0,SUBSET_EMPTY])
  >- (rw[] >>
      Cases_on ‘D=D'’
      >- metis_tac[]
      >- (‘∃D₀ e. (D' = e INSERT D₀) ∧ D ⊆ D₀ ∧ e NOTIN D₀’
            by (‘∃e. e ∈ D' ∧ e NOTIN D’
            by metis_tac[PSUBSET_DEF,PSUBSET_MEMBER] >>
            qexists_tac ‘D' DELETE e’ >>
            qexists_tac ‘e’ >>
            simp[] >>
            fs[SUBSET_DEF]) >>
          rw[] >>
          fs[] >>
          metis_tac[N_lw]))
QED

Theorem Nd_lw_SUBSET:
∀D'. FINITE D' ==> ∀D A. Nd D A  ∧ D ⊆ D' ==> Nd D' A
Proof
  GEN_TAC >>
  Induct_on ‘CARD D'’
  >- (rw[] >> metis_tac[CARD_EQ_0,SUBSET_EMPTY])
  >- (rw[] >> Cases_on ‘D=D'’ >- metis_tac[] >>
      ‘∃D₀ e. (D' = e INSERT D₀) ∧ D ⊆ D₀ ∧ e NOTIN D₀’
        by (‘∃e. e ∈ D' ∧ e NOTIN D’
              by metis_tac[PSUBSET_DEF,PSUBSET_MEMBER] >>
            qexists_tac ‘D' DELETE e’ >>
            qexists_tac ‘e’ >>
            simp[] >>
            fs[SUBSET_DEF]) >>
      rw[] >>
      fs[] >>
      metis_tac[Nd_lw])
QED

Theorem N_ax':
  FINITE D ∧ A ∈ D ⇒ N D A
Proof
  strip_tac >> irule N_lw_SUBSET >> simp[] >>
  irule_at Any N_ax >> simp[]
QED

Theorem N_impi_DELETE:
  ∀D A B. N D A ==> N (D DELETE B) (B ⇒ⁱ A)
Proof
  rw[] >>
  ‘N (B INSERT D) A’ by metis_tac[N_lw] >>
  Cases_on ‘B ∈ D’
    >- (‘∃D'. (D = B INSERT D') ∧ B NOTIN D'’
          by metis_tac[DECOMPOSITION] >>
        fs[] >>
        ‘(B INSERT D') DELETE B = D'’
          by (dsimp[EXTENSION] >>
              metis_tac[]) >>
        simp[N_impi])
    >- simp[DELETE_NON_ELEMENT_RWT,N_impi]
QED

Theorem N_Nd:
  ∀D A. N D A <=> Nd D A
Proof
 ‘(∀D A. N D A ==> Nd D A) ∧
  (∀D A. Nd D A ==> N D A)’
    suffices_by metis_tac[] >>
  conj_tac
  >- (Induct_on ‘N’ >>
      rw[Nd_rules]
        >- metis_tac[Nd_andel]
        >- metis_tac[Nd_ander]
        >- (‘Nd ((A INSERT D) DELETE A) (A ⇒ⁱ B)’
              by metis_tac[Nd_impi] >>
            fs[DELETE_DEF] >>
            irule Nd_lw_SUBSET >>
            conj_tac >- metis_tac[N_FINITE,FINITE_INSERT] >>
            qexists_tac ‘D DIFF {A}’ >>
            simp[])
        >- metis_tac[Nd_impe]
        >- (‘Nd (D ∪ ((A INSERT D1) DELETE A) ∪ ((B INSERT D2) DELETE B)) C’
              by metis_tac[Nd_ore] >>
            fs[DELETE_DEF] >>
            irule Nd_lw_SUBSET >>
            conj_tac >- metis_tac[N_FINITE,FINITE_UNION,FINITE_INSERT] >>
            qexists_tac ‘D ∪ (D1 DIFF {A}) ∪ (D2 DIFF {B})’ >>
            rw[SUBSET_DEF]))
  >- (Induct_on ‘Nd’ >>
      rw[N_rules]
        >- metis_tac[N_andel]
        >- metis_tac[N_ander]
        >- metis_tac[N_impi_DELETE]
        >- metis_tac[N_impe]
        >- (‘N (A INSERT (D1 DELETE A)) C’
              by (irule N_lw_SUBSET >>
                  rw[] >- metis_tac[N_FINITE] >>
                  qexists_tac ‘D1’ >>
                  rw[DELETE_DEF,SUBSET_DEF]) >>
            ‘N (B INSERT (D2 DELETE B)) C’
              by (irule N_lw_SUBSET >>
                  rw[] >- metis_tac[N_FINITE] >>
                  qexists_tac ‘D2’ >>
                  rw[DELETE_DEF,SUBSET_DEF]) >>
            metis_tac[N_ore]))
QED

Definition NThm:   NThm A = N EMPTY A
End

(* Example deductions *)
Theorem N_example1: NThm (A ⇒ⁱ (B ⇒ⁱ A))
Proof
  ‘N {A} A’ by rw[N_ax] >>
  ‘N {B} B’ by rw[N_ax] >>
  ‘{A} UNION {B} = {A;B}’ by simp[UNION_DEF,INSERT_DEF] >>
  ‘N {A;B} (A ∧ⁱ B)’ by metis_tac[N_andi] >>
  ‘N {A;B} (A)’ by metis_tac[N_andel] >>
  ‘N {A} (B ⇒ⁱ A)’ by (irule N_impi >> simp[INSERT_COMM]) >>
  ‘N {} (A ⇒ⁱ (B ⇒ⁱ A))’ by metis_tac[N_impi] >>
  rw[NThm]
QED

Theorem N_example2:
  NThm (⊥ⁱ ⇒ⁱ A)
Proof
  ‘N {⊥ⁱ} ⊥ⁱ’ by rw[N_rules] >>
  ‘N {⊥ⁱ} A’ by rw[N_rules] >>
  ‘{} = ({⊥ⁱ} DIFF {⊥ⁱ})’ by rw[DIFF_DEF] >>
  ‘N EMPTY (⊥ⁱ ⇒ⁱ A)’ by metis_tac[N_rules] >>
  rw[NThm]
QED


(* Sequent Calculus (Gentzen System) for intuitionistic logic        *)
(* G is the 'deduciblility' relation for this system                 *)
(* A, B and C are used to represent formulae                         *)
(* Γ is used to represent the multiset of the antecedents            *)
(* The consequent is always a single formula in intuitionistic logic *)
Inductive G:
[~ax:]
  ∀A Γ. (A <: Γ) ∧ FINITE_BAG Γ ==> G Γ A
[~bot:]
  ∀ A Γ. (⊥ⁱ <: Γ) ∧ FINITE_BAG Γ ==> G Γ A
[~lc:] (* Left Contraction *)
  ∀A Γ C.
    G ({|A;A|} ⊎ Γ) C
   ==>
   G ({|A|} ⊎ Γ) C
[~landl:]
  ∀A B Γ C.
    G (BAG_INSERT A Γ) C ==>
    G (BAG_INSERT (A ∧ⁱ B) Γ) C
[~landr:]
  ∀A B Γ C.
    G (BAG_INSERT B Γ) C
    ==>
    G (BAG_INSERT (A ∧ⁱ B) Γ) C
[~rand:]
  ∀A B Γ. G Γ A ∧ G Γ B ==> G Γ (A ∧ⁱ B)
[~lor:]
  ∀A B Γ C.
    G (BAG_INSERT A Γ) C ∧ G (BAG_INSERT B Γ) C
   ==>
   G (BAG_INSERT (A ∨ⁱ B) Γ) C
[~rorl:]
  ∀A B Γ. G Γ A ==> G Γ (A ∨ⁱ B)
[~rorr:]
  ∀A B Γ. G Γ B ==> G Γ (A ∨ⁱ B)
[~limp:]
  ∀A B Γ C.
    G Γ A ∧ G (BAG_INSERT B Γ) C
    ==>
    G (BAG_INSERT (A ⇒ⁱ B) Γ) C
[~rimp:]
  ∀A B Γ. G (BAG_INSERT A Γ) B ==> G Γ (A ⇒ⁱ B)
[~cut:]
  ∀A B Γ Δ. G Γ A ∧ G (BAG_INSERT A Δ) B ==> G (Γ ⊎ Δ) B
End

Definition GThm:   GThm A = G EMPTY_BAG A
End

Theorem G_example1:
  GThm ((A ∧ⁱ B) ⇒ⁱ (B ∧ⁱ A))
Proof rw[GThm,G_rules]
QED

Theorem G_example2: GThm ((A ⇒ⁱ (A ⇒ⁱ B)) ⇒ⁱ (A ⇒ⁱ B))
Proof
  rw[GThm] >>
  ‘G {|(A ⇒ⁱ A ⇒ⁱ B)|} (A ⇒ⁱ B)’ suffices_by metis_tac[G_rules] >>
  ‘G {|A;(A ⇒ⁱ A ⇒ⁱ B)|} (B)’ suffices_by metis_tac[G_rules] >>
  ‘G {|A|} (A)’ by metis_tac[G_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
  ‘G {|B;A|} (B)’ by metis_tac[G_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
  (* `G {|A;B|} (B)` by simp[G_lw] >> *)
  (* `G {|B;A|} (B)` by simp[BAG_INSERT_commutes] >> *)
  ‘G {|(A ⇒ⁱ B);A|} (B)’ by metis_tac[G_rules] >>
  ‘G {|(A ⇒ⁱ A ⇒ⁱ B);A|} (B)’ suffices_by metis_tac[BAG_INSERT_commutes] >>
  metis_tac[G_rules]
QED

Theorem G_land_commutes:
  G {| A ∧ⁱ B |} Δ ==> G {| B ∧ⁱ A |} Δ
Proof
  rw[] >>
  ‘G {|B|} B’ by metis_tac[G_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
  ‘G {|B ∧ⁱ A|} B’ by metis_tac[G_landl] >>
  ‘G {|A|} A’ by metis_tac[G_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
  ‘G {|B ∧ⁱ A|} A’ by metis_tac[G_landr] >>
  ‘G {|B ∧ⁱ A|} (A ∧ⁱ B)’ by metis_tac[G_rand] >>
  ‘G ({|B ∧ⁱ A|} ⊎ {||}) Δ’ by metis_tac[G_cut] >>
  metis_tac[BAG_UNION_EMPTY]
QED

Theorem G_FINITE:
  ∀Γ A. G Γ A ==> FINITE_BAG Γ
Proof Induct_on ‘G’ >> rw[]
QED

(* Thanks for your help with this theorem Michael *)
Theorem G_lw:
  ∀Γ A. G Γ A ⇒ ∀Γ'. Γ ≤ Γ' ∧ FINITE_BAG Γ' ⇒ G Γ' A
Proof
  Induct_on ‘G’ >> rw[]
  >- (irule G_ax >> fs[SUB_BAG, BAG_IN])
  >- (irule G_bot >> fs[SUB_BAG,BAG_IN])
  >- (‘∃Γ₂. Γ' = {|A|} ⊎ Γ₂’
        by (qexists_tac ‘Γ' - {|A|}’ >> irule SUB_BAG_DIFF_EQ >>
            metis_tac[SUB_BAG_UNION_down]) >>
      rw[] >> irule G_lc >> first_x_assum irule >> simp[] >> fs[])
  >- (‘∃Γ₂. Γ' = BAG_INSERT (A ∧ⁱ B) Γ₂’
        by (qexists_tac ‘Γ' - {|A ∧ⁱ B|}’ >> fs[BAG_INSERT_UNION] >>
            irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
      rw[] >> irule G_landl >> first_x_assum irule >> fs[SUB_BAG_INSERT])
  >- (‘∃Γ₂. Γ' = BAG_INSERT (A ∧ⁱ B) Γ₂’
        by (qexists_tac ‘Γ' - {|A ∧ⁱ B|}’ >> fs[BAG_INSERT_UNION] >>
            irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
      rw[] >> irule G_landr >> first_x_assum irule >> fs[SUB_BAG_INSERT])
  >- (irule G_rand >> simp[])
  >- (‘∃Γ₂. Γ' = BAG_INSERT (A ∨ⁱ B) Γ₂’
        by (qexists_tac ‘Γ' - {|A ∨ⁱ B|}’ >> fs[BAG_INSERT_UNION] >>
            irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
      rw[] >> fs[SUB_BAG_INSERT] >> irule G_lor >> conj_tac >>
      first_x_assum (fn th => irule th >> fs[SUB_BAG_INSERT] >> NO_TAC))
  >- simp[G_rorl]
  >- simp[G_rorr]
  >- (‘∃Γ₂. Γ' = BAG_INSERT (A ⇒ⁱ B) Γ₂’
        by (qexists_tac ‘Γ' - {|A ⇒ⁱ B|}’ >> fs[BAG_INSERT_UNION] >>
            irule SUB_BAG_DIFF_EQ >> metis_tac[SUB_BAG_UNION_down]) >>
      rw[] >> irule G_limp >> fs[SUB_BAG_INSERT])
  >- simp[SUB_BAG_INSERT, G_rimp]
  >- (rename [‘Γ₁ ⊎ Γ₂ ≤ Γ₃’] >>
      ‘∃Γ₀. Γ₃ = Γ₀ ⊎ Γ₁ ⊎ Γ₂’
        by metis_tac[SUB_BAG_EXISTS, COMM_BAG_UNION, ASSOC_BAG_UNION] >>
      rw[] >> irule G_cut >>
      rename [‘G (BAG_INSERT A _) B’] >> qexists_tac ‘A’ >>
      conj_tac >> first_x_assum irule >> fs[SUB_BAG_INSERT])
QED

Theorem G_lw_BAG_MERGE:
  ∀Γ A. G Γ A ==> ∀Γ'. FINITE_BAG Γ' ==> G (BAG_MERGE Γ' Γ) A
Proof
  rw[] >>
  irule G_lw >>
  ‘FINITE_BAG Γ’ by metis_tac[G_FINITE] >>
  simp[FINITE_BAG_MERGE] >>
  qexists_tac ‘Γ’ >>
  simp[SUB_BAG,BAG_INN_BAG_MERGE]
QED

Theorem G_lw_BAG_UNION:
  ∀Γ A. G Γ A ==> ∀Γ'. FINITE_BAG Γ' ==> G (Γ ⊎ Γ') A
Proof
  rw[] >>
  irule G_lw >>
  ‘FINITE_BAG Γ’ by metis_tac[G_FINITE] >>
  simp[FINITE_BAG_UNION] >>
  qexists_tac ‘Γ’ >>
  simp[]
QED

Theorem G_lw_BAG_INSERT:
  ∀Γ A. G Γ A ==> ∀B Γ'. G (BAG_INSERT B Γ) A
Proof
  rw[] >>
  irule G_lw >>
  ‘FINITE_BAG Γ’ by metis_tac[G_FINITE] >>
  simp[FINITE_BAG_THM] >>
  qexists_tac ‘Γ’ >>
  simp[SUB_BAG_INSERT_I]
QED

Theorem G_lc_AeA[local]:
  ∀A e Γ'. G (BAG_INSERT A (BAG_INSERT e (BAG_INSERT A Γ'))) B
           ==> G (BAG_INSERT e (BAG_INSERT A Γ')) B
Proof
  rw[] >>
  ‘G ({|A;A|} ⊎ ({|e|} ⊎ Γ')) B’
    by (fs[BAG_UNION_INSERT,ASSOC_BAG_UNION,BAG_INSERT_UNION] >>
        simp[COMM_BAG_UNION] >>
        fs[EL_BAG,BAG_UNION]) >>
  ‘G ({|A|} ⊎ ({|e|} ⊎ Γ')) B’
    by metis_tac[G_lc] >>
  ‘G (({|A|} ⊎ {|e|}) ⊎ Γ') B’
    by fs[ASSOC_BAG_UNION] >>
  ‘G (({|e|} ⊎ {|A|}) ⊎ Γ') B’
    by fs[COMM_BAG_UNION] >>
  fs[BAG_INSERT_UNION] >>
  fs[EL_BAG] >>
  simp[ASSOC_BAG_UNION]
QED

Theorem unibag_AA_A[local]: unibag ({|A;A|} ⊎ Γ) = unibag ({|A|} ⊎ Γ)
Proof simp[unibag_thm]
QED

Theorem G_unibag:
  ∀Γ A. G Γ A <=> G (unibag Γ) A
Proof
  rw[] >> EQ_TAC
  >- (‘∀Γ. FINITE_BAG Γ ==> ∀A. G Γ A ==> G (unibag Γ) A’
        suffices_by metis_tac[G_FINITE] >>
      gen_tac >>
      Induct_on ‘BAG_CARD Γ’ >>
      rw[]
        >- (‘Γ = {||}’ by metis_tac[BCARD_0] >>
            fs[])
        >- (Cases_on ‘unibag Γ = Γ’ >- fs[] >>
            drule_then strip_assume_tac unibag_DECOMPOSE >>
            rename [‘Γ = {|B;B|} ⊎ Γ0’,‘SUC n = BAG_CARD Γ’] >>
            ‘G ({|B|} ⊎ Γ0) A’ by metis_tac[G_lc] >>
            ‘BAG_CARD ({|B|} ⊎ Γ0) = n’ by fs[BAG_CARD_THM] >>
            ‘FINITE_BAG ({|B|} ⊎ Γ0)’ by fs[] >>
            metis_tac[unibag_AA_A]))
   >- metis_tac[unibag_SUB_BAG,G_lw,G_FINITE,unibag_FINITE]
QED

Theorem N_G:
  ∀D A. N D A ==> G (BAG_OF_SET D) A
Proof
 Induct_on ‘N’ >>
 rw[G_rules]
 >- (irule G_rand >> conj_tac
     >- (‘G (BAG_OF_SET (D' ∪ D)) A’ suffices_by metis_tac[UNION_COMM] >>
         simp[BAG_OF_SET_UNION] >>
         metis_tac[G_lw_BAG_MERGE,G_FINITE])
     >- (simp[BAG_OF_SET_UNION] >>
         metis_tac[G_lw_BAG_MERGE,G_FINITE]))
 >- (‘G {|A|} A’ by metis_tac[G_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
     ‘G {|A ∧ⁱ B|} A’ by metis_tac[G_landl] >>
     ‘G ((BAG_OF_SET D) ⊎ {||}) A’ by metis_tac[G_cut] >>
     metis_tac[BAG_UNION_EMPTY])
 >- (‘G {|A'|} A'’ by metis_tac[G_ax,BAG_IN_BAG_INSERT,FINITE_BAG] >>
     ‘G {|A ∧ⁱ A'|} A'’ by metis_tac[G_landr] >>
     ‘G ((BAG_OF_SET D) ⊎ {||}) A'’ by metis_tac[G_cut] >>
     metis_tac[BAG_UNION_EMPTY])
 >- (irule G_rimp >>
     fs[BAG_OF_SET_INSERT] >>
     irule G_lw >>
     simp[] >>
     drule G_FINITE >>
     rw[] >>
     qexists_tac ‘BAG_MERGE {|A|} (BAG_OF_SET D)’ >>
     simp[BAG_MERGE_ELBAG_SUB_BAG_INSERT])
 >- (rename[‘N D (A ⇒ⁱ B)’] >>
     simp[BAG_OF_SET_UNION] >>
    ‘FINITE_BAG (BAG_OF_SET D')’ by metis_tac[N_FINITE,FINITE_BAG_OF_SET] >>
    ‘G (BAG_INSERT B (BAG_OF_SET D')) B’
      by simp[G_ax,BAG_IN_BAG_INSERT] >>
    ‘G (BAG_INSERT (A ⇒ⁱ B) (BAG_OF_SET D')) B’
      by metis_tac[G_limp] >>
    ‘G ((BAG_OF_SET D) ⊎ (BAG_OF_SET D')) B’
      by metis_tac[G_cut] >>
    ‘G (unibag (BAG_OF_SET D ⊎ BAG_OF_SET D')) B’ by metis_tac[G_unibag] >>
    fs[unibag_UNION])
 >- (rename [‘N (_ INSERT _) C’] >>
     fs[BAG_OF_SET_UNION,BAG_OF_SET_INSERT] >>
     qabbrev_tac ‘Δ = ((BAG_OF_SET D) ⊎ (BAG_OF_SET D1) ⊎ (BAG_OF_SET D2))’ >>
     ‘FINITE_BAG (BAG_INSERT A Δ)’
       by (simp[Abbr‘Δ’,FINITE_BAG_THM] >>
           metis_tac[FINITE_BAG_OF_SET,N_FINITE,FINITE_INSERT]) >>
      ‘G (BAG_INSERT A Δ) C’
        by (‘G (BAG_MERGE {|A|} Δ) C’
              suffices_by metis_tac[BAG_MERGE_ELBAG_SUB_BAG_INSERT,G_lw] >>
            simp[Abbr‘Δ’] >>
            irule G_lw >>
            conj_tac >- fs[FINITE_BAG_MERGE,FINITE_BAG_THM] >>
            qexists_tac ‘BAG_MERGE {|A|} (BAG_OF_SET D1)’ >>
            simp[] >>
            fs[BAG_MERGE,BAG_INSERT,EMPTY_BAG,
               BAG_OF_SET,BAG_UNION,SUB_BAG,BAG_INN,IN_DEF] >>
            rw[] >>
            fs[]) >>
      ‘FINITE_BAG (BAG_INSERT B Δ)’
      by (simp[Abbr‘Δ’,FINITE_BAG_THM] >>
          metis_tac[FINITE_BAG_OF_SET,N_FINITE,FINITE_INSERT]) >>
      ‘G (BAG_INSERT B Δ) C’
        by (‘G (BAG_MERGE {|B|} Δ) C’
              suffices_by metis_tac[BAG_MERGE_ELBAG_SUB_BAG_INSERT,G_lw] >>
            simp[Abbr‘Δ’] >>
            irule G_lw >>
            conj_tac >- fs[FINITE_BAG_MERGE,FINITE_BAG_THM] >>
            qexists_tac ‘BAG_MERGE {|B|} (BAG_OF_SET D2)’ >>
            simp[] >>
            fs[BAG_MERGE,BAG_INSERT,EMPTY_BAG,
               BAG_OF_SET,BAG_UNION,SUB_BAG,BAG_INN,IN_DEF] >>
            rw[] >>
            fs[]) >>
      ‘G Δ (A ∨ⁱ B)’
        by (simp[Abbr‘Δ’] >>
            irule G_lw_BAG_UNION >>
            conj_tac >- metis_tac[FINITE_INSERT,N_FINITE,FINITE_BAG_OF_SET] >>
            irule G_lw_BAG_UNION >>
            conj_tac >- metis_tac[FINITE_INSERT,N_FINITE,FINITE_BAG_OF_SET] >>
            metis_tac[]) >>
      ‘G (BAG_INSERT (A ∨ⁱ B) Δ) C’ by metis_tac[G_lor] >>
      ‘G ((BAG_OF_SET D) ⊎ Δ) C’ by metis_tac[G_cut] >>
      ‘G (unibag (BAG_OF_SET D ⊎ Δ)) C’ by metis_tac[G_unibag] >>
      ‘(unibag (BAG_OF_SET D ⊎ Δ))
        = BAG_MERGE (BAG_MERGE (BAG_OF_SET D) (BAG_OF_SET D1)) (BAG_OF_SET D2)’
         suffices_by metis_tac[] >>
      rw[Abbr‘Δ’,unibag_UNION,BAG_MERGE,FUN_EQ_THM])
 >- (‘G {| ⊥ⁱ |} A’ by metis_tac[G_bot,BAG_IN_BAG_INSERT,FINITE_BAG] >>
     metis_tac[G_cut,BAG_UNION_EMPTY])
QED

Theorem G_N:
  ∀Γ A. G Γ A ==> N (SET_OF_BAG Γ) A
Proof
  Induct_on ‘G’ >> rw[N_rules]
    >- (‘∃b. Γ = BAG_INSERT A b’ by metis_tac[BAG_DECOMPOSE] >>
        fs[] >>
        simp[SET_OF_BAG_INSERT, Once INSERT_SING_UNION] >>
        ‘N {A} A’ by metis_tac[N_ax] >>
        simp[UNION_COMM] >>
        irule N_lw_SUBSET >>
        conj_tac >- metis_tac[FINITE_UNION,FINITE_SET_OF_BAG,FINITE_DEF] >>
        metis_tac[SUBSET_UNION])
    >- (‘∃b. Γ = BAG_INSERT ⊥ⁱ b’ by metis_tac[BAG_DECOMPOSE] >>
        fs[] >>
        simp[SET_OF_BAG_INSERT, Once INSERT_SING_UNION] >>
        ‘N {⊥ⁱ} ⊥ⁱ’ by metis_tac[N_ax] >>
        ‘N {⊥ⁱ} A’ by metis_tac[N_bot] >>
        irule N_lw_SUBSET >>
        conj_tac >- metis_tac[FINITE_UNION,FINITE_SET_OF_BAG,FINITE_DEF] >>
        metis_tac[SUBSET_UNION])
    >- fs[SET_OF_BAG,BAG_UNION,BAG_INSERT]
    >- (rename [‘N _ C’] >>
        fs[SET_OF_BAG_INSERT] >>
        ‘N {A ∧ⁱ B} (A ∧ⁱ B)’ by metis_tac[N_ax] >>
        ‘N {A ∧ⁱ B} A’ by metis_tac[N_andel] >>
        ‘N ((A INSERT (SET_OF_BAG Γ)) DELETE A) (A ⇒ⁱ C)’
          by metis_tac[N_impi_DELETE] >>
        fs[DELETE_DEF] >>
        ‘N (((SET_OF_BAG Γ) DIFF {A}) ∪ {A ∧ⁱ B}) C’ by metis_tac[N_impe] >>
        ‘N ((A ∧ⁱ B) INSERT ((SET_OF_BAG Γ) DIFF {A})) C’
          by metis_tac[UNION_COMM,INSERT_SING_UNION] >>
        irule N_lw_SUBSET >>
        conj_tac >- metis_tac[N_FINITE,FINITE_INSERT] >>
        qexists_tac ‘(A ∧ⁱ B) INSERT SET_OF_BAG Γ DIFF {A}’ >>
        rw[SUBSET_DEF])
    >- (rename [‘N _ C’] >>
        ‘N {A ∧ⁱ B} (A ∧ⁱ B)’ by metis_tac[N_ax] >>
        ‘N {A ∧ⁱ B} B’ by metis_tac[N_ander] >>
        qabbrev_tac ‘Γ'= SET_OF_BAG (BAG_INSERT B Γ)’ >>
        ‘N (B INSERT Γ') C’ by metis_tac[N_lw] >>
        ‘N (Γ' DELETE B) (B ⇒ⁱ C)’
          by (Cases_on ‘B ∈ Γ'’
              >- (‘∃Γ0. (Γ' = B INSERT Γ0) ∧ B NOTIN Γ0’
                    by metis_tac[DECOMPOSITION] >>
                  fs[] >>
                  ‘(B INSERT Γ0) DELETE B = Γ0’
                    by (dsimp[EXTENSION] >>
                        metis_tac[]) >>
                  simp[N_impi])
              >- (simp[DELETE_NON_ELEMENT_RWT,N_impi])) >>
        ‘N ((Γ' DELETE B) ∪ {A ∧ⁱ B}) C’ by metis_tac[N_impe] >>
        ‘N ((A ∧ⁱ B) INSERT (Γ' DELETE B)) C’
          by metis_tac[UNION_COMM,INSERT_SING_UNION] >>
        fs[Abbr‘Γ'’,SET_OF_BAG_INSERT] >>
        irule N_lw_SUBSET >>
        conj_tac >- metis_tac[N_FINITE,FINITE_INSERT] >>
        fs[DELETE_DEF] >>
        qexists_tac ‘(A ∧ⁱ B) INSERT SET_OF_BAG Γ DIFF {B}’ >>
        rw[SUBSET_DEF])
    >- (rename [‘N _ (A ∧ⁱ B)’] >> metis_tac[N_andi,UNION_IDEMPOT])
    >- (rename [‘N _ C’] >>
        qabbrev_tac ‘Δ = (A ∨ⁱ B) INSERT (SET_OF_BAG Γ)’ >>
        qabbrev_tac ‘Γ' = A INSERT (SET_OF_BAG Γ)’ >>
        qabbrev_tac ‘Γ'' = B INSERT (SET_OF_BAG Γ)’ >>
        fs[SET_OF_BAG_INSERT] >>
        ‘FINITE_BAG Γ’ by metis_tac[G_FINITE,FINITE_BAG_THM] >>
        ‘N (A INSERT Δ) C’
          by (irule N_lw_SUBSET >>
              simp[Abbr‘Δ’] >>
              qexists_tac ‘Γ'’ >>
              simp[Abbr‘Γ'’,SUBSET_INSERT_RIGHT]) >>
        ‘N (B INSERT Δ) C’
          by (irule N_lw_SUBSET >>
              simp[Abbr‘Δ’] >>
              qexists_tac ‘Γ''’ >>
              simp[Abbr‘Γ''’,SUBSET_INSERT_RIGHT]) >>
        ‘N {(A ∨ⁱ B)} (A ∨ⁱ B)’ by metis_tac[N_ax] >>
        ‘FINITE ({A ∨ⁱ B} ∪ (SET_OF_BAG Γ))’
          by (‘FINITE (SET_OF_BAG Γ)’
                by metis_tac[FINITE_SET_OF_BAG] >>
              metis_tac[FINITE_UNION,FINITE_DEF]) >>
        ‘N ({A ∨ⁱ B} ∪ (SET_OF_BAG Γ)) (A ∨ⁱ B)’
          by metis_tac[SUBSET_UNION,N_lw_SUBSET] >>
        ‘N Δ (A ∨ⁱ B)’
          by (simp[Abbr‘Δ’,Abbr‘Γ'’,Abbr‘Γ''’] >>
              irule N_lw_SUBSET >>
              rw[] >>
              qexists_tac ‘{A ∨ⁱ B}’ >>
              simp[]) >>
        ‘N (Δ ∪ Δ ∪ Δ) C’ by metis_tac[N_ore] >>
        metis_tac[UNION_IDEMPOT])
    >- (rename [‘N _ C’] >>
        fs[SET_OF_BAG_INSERT] >>
        ‘FINITE_BAG Γ’ by metis_tac[G_FINITE,FINITE_BAG_THM] >>
        ‘FINITE (SET_OF_BAG Γ)’ by metis_tac[FINITE_SET_OF_BAG] >>
        ‘N {A ⇒ⁱ B} (A ⇒ⁱ B)’ by metis_tac[N_ax] >>
        ‘N ((A ⇒ⁱ B) INSERT (SET_OF_BAG Γ)) B’
          by metis_tac[INSERT_SING_UNION,N_impe] >>
        irule N_lw_SUBSET >>
        rw[] >>
        ‘N (B INSERT (SET_OF_BAG Γ)) C’
          by metis_tac[N_lw_SUBSET,FINITE_INSERT] >>
        ‘N (SET_OF_BAG Γ) (B ⇒ⁱ C)’ by metis_tac[N_impi] >>
        ‘N ((SET_OF_BAG Γ) ∪ ((A ⇒ⁱ B) INSERT SET_OF_BAG Γ)) C’
          by metis_tac[N_impe] >>
        ‘N ((A ⇒ⁱ B) INSERT SET_OF_BAG Γ) C’
          by metis_tac[UNION_COMM,UNION_ASSOC,UNION_IDEMPOT,INSERT_SING_UNION]>>
        qexists_tac ‘(A ⇒ⁱ B) INSERT (SET_OF_BAG Γ)’ >>
        rw[] >>
        fs[SUBSET_INSERT_RIGHT])
    >- (rename [‘N _ (A ⇒ⁱ B)’] >>
        fs[SET_OF_BAG_INSERT] >>
        metis_tac[N_impi])
    >- (rename [‘G (BAG_INSERT A Δ) B’] >>
        fs[SET_OF_BAG_INSERT] >>
        ‘N ((A INSERT SET_OF_BAG Δ) DELETE A) (A ⇒ⁱ B)’
          by metis_tac[N_impi_DELETE] >>
        fs[DELETE_DEF] >>
        ‘N ((SET_OF_BAG Δ DIFF {A}) ∪ (SET_OF_BAG Γ)) B’ by metis_tac[N_impe] >>
        irule N_lw_SUBSET >>
        reverse(rw[])
          >- (qexists_tac ‘SET_OF_BAG Δ DIFF {A} ∪ SET_OF_BAG Γ’ >>
              rw[]
              >- (irule SUBSET_TRANS >>
                  qexists_tac ‘(SET_OF_BAG Δ)’ >>
                  fs[SET_OF_BAG_INSERT,SET_OF_BAG_UNION])
              >- fs[SET_OF_BAG_UNION])
          >> metis_tac[G_FINITE,FINITE_BAG_THM])
QED

Theorem G_iff_N:
∀Γ A. G Γ A <=> N (SET_OF_BAG Γ) A
Proof
  rw[G_N] >>
  EQ_TAC >- rw[G_N] >>
  rw[] >>
  ‘G (unibag Γ) A’ by metis_tac[N_G] >>
  metis_tac[G_unibag]
QED
