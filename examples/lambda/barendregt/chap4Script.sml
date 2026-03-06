(* ========================================================================== *)
(* FILE    : chap4Script.sml                                                  *)
(* TITLE   : Lambda Theories (general setup)                                  *)
(* ========================================================================== *)
Theory chap4
Ancestors
  pred_set relation term horeduction chap2 chap3
Libs
  hurdUtils binderLib


val _ = hide "B"

(* definition 4.1.1(i) is already in chap2, given name asmlam

   NOTE: “lambdathy {}” is false, use “lambdathy (UNCURRY (==)” for the base theory.
 *)
Definition lambdathy_def:
  lambdathy A ⇔ consistent (asmlam A) ∧ UNCURRY (asmlam A) = A
End

Theorem asmlam_lameq_absorb :
    asmlam (UNCURRY (==)) = (==)
Proof
    simp [FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM]
 >> CONJ_TAC
 >- (HO_MATCH_MP_TAC asmlam_ind >> simp [] \\
     METIS_TAC [lameq_rules])
 >> HO_MATCH_MP_TAC lameq_ind
 >> METIS_TAC [asmlam_rules]
QED

Theorem asmlam_lameta_absorb :
    asmlam (UNCURRY lameta) = lameta
Proof
    simp [FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM]
 >> CONJ_TAC
 >- (HO_MATCH_MP_TAC asmlam_ind >> simp [] \\
     METIS_TAC [lameta_rules])
 >> HO_MATCH_MP_TAC lameta_ind
 >> REWRITE_TAC [CONJ_ASSOC]
 >> CONJ_TAC >- METIS_TAC [asmlam_rules]
 >> qx_genl_tac [‘t’, ‘y’] >> STRIP_TAC
 >> MATCH_MP_TAC asmlam_eqn >> simp []
 >> MATCH_MP_TAC lameta_ETA >> art []
QED

(* not used *)
Theorem asmlam_conversion_absorb :
    asmlam (UNCURRY (conversion R)) = asmlam (UNCURRY R)
Proof
    simp [FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM]
 >> reverse CONJ_TAC
 >- (HO_MATCH_MP_TAC asmlam_ind >> simp [] \\
     reverse CONJ_TAC >- METIS_TAC [asmlam_rules] \\
     rpt STRIP_TAC \\
     MATCH_MP_TAC asmlam_eqn >> rw [] \\
     rw [conversion_rules])
 >> HO_MATCH_MP_TAC asmlam_ind >> simp []
 >> reverse CONJ_TAC >- METIS_TAC [asmlam_rules]
 >> HO_MATCH_MP_TAC EQC_INDUCTION
 >> reverse CONJ_TAC >- METIS_TAC [asmlam_rules]
 >> HO_MATCH_MP_TAC compat_closure_ind
 >> reverse CONJ_TAC >- METIS_TAC [asmlam_rules]
 >> rpt STRIP_TAC
 >> MATCH_MP_TAC asmlam_eqn >> rw []
QED

Theorem lambdathy_lameq :
    lambdathy (UNCURRY (==))
Proof
    rw [lambdathy_def, asmlam_lameq_absorb, lameq_consistent]
QED

Theorem lambdathy_lameta :
    lambdathy (UNCURRY lameta)
Proof
    rw [lambdathy_def, asmlam_lameta_absorb, lameta_consistent]
QED

Definition church1_def:
  church1 = LAM "x" (LAM "y" (VAR "x" @@ VAR "y"))
End

Overload "𝟙" = “church1”

Overload "TC" = “asmlam”

Overload "eta_extend" = “λA. asmlam (UNCURRY eta ∪ A)”
val _ = set_mapped_fixity {tok = UTF8.chr 0x1D73C, fixity = Suffix 2100,
                           term_name = "eta_extend"}

Theorem lameta_subset_eta_extend:
  ∀M N. lameta M N ⇒ 𝒯 𝜼 M N
Proof
  Induct_on ‘lameta’ >>
  rw[asmlam_refl, asmlam_beta, asmlam_lcong, asmlam_rcong, asmlam_abscong] >~
  [‘_ 𝜼 M N’, ‘_ 𝜼 N M’] >- metis_tac[asmlam_sym] >~
  [‘_ 𝜼 (LAM v (M @@ VAR v)) M’]
  >- (irule asmlam_eqn >> simp[eta_def] >> metis_tac[]) >>
  metis_tac[asmlam_trans]
QED

Theorem asmlam_equality:
  asmlam A = asmlam B ⇔
    (∀a1 a2. (a1,a2) ∈ A ⇒ asmlam B a1 a2) ∧
    (∀b1 b2. (b1,b2) ∈ B ⇒ asmlam A b1 b2)
Proof
  iff_tac
  >- (simp[] >> rw[] >~
      [‘A⁺ = B⁺’, ‘(a1,a2) ∈ A’]
      >- (‘A⁺ a1 a2’ suffices_by simp[] >> simp[asmlam_eqn]) >>
      simp[asmlam_eqn]) >>
  strip_tac >> simp[FUN_EQ_THM, EQ_IMP_THM, FORALL_AND_THM] >> conj_tac >>
  Induct_on ‘asmlam’ >>
  rw[asmlam_beta, asmlam_refl, asmlam_lcong, asmlam_rcong, asmlam_abscong] >>
  metis_tac[asmlam_sym, asmlam_trans]
QED

Theorem eta_alt:
  FINITE X ⇒ (η M N ⇔ ∃v. v ∉ X ∧ v # N ∧ M = LAM v (N @@ VAR v))
Proof
  simp[EQ_IMP_THM, eta_def] >> rw[]
  >- (simp[LAM_eq_thm, SF DNF_ss, SF CONJ_ss, tpm_fresh] >>
      Q_TAC (NEW_TAC "z") ‘{v} ∪ FV N ∪ X’ >> metis_tac[]) >>
  simp[LAM_eq_thm, SF CONJ_ss, tpm_fresh, SF SFY_ss]
QED

Theorem lemma4_1_5:
  ((I,𝟙) INSERT 𝒯)⁺ = 𝒯 𝜼
Proof
  simp[asmlam_equality] >> rw[]
  >- (irule lameta_subset_eta_extend >>
      simp[church1_def, I_def] >> irule lameta_SYM >>
      irule lameta_ABS >> irule lameta_ETA >> simp[]) >>
  simp[asmlam_eqn] >>
  ‘FINITE {"x"; "y"}’ by simp[] >>
  dxrule_then assume_tac eta_alt >> gvs[] >>
  rename [‘_⁺ (LAM v (M @@ VAR v)) M’] >>
  qmatch_abbrev_tac ‘A⁺ _ _’ >>
  ‘A⁺ (LAM v (M @@ VAR v)) (𝟙 @@ M)’
    by (‘A⁺ (𝟙 @@ M) ([M/"x"] (LAM "y" (VAR "x" @@ VAR "y")))’
          by simp[asmlam_beta, church1_def] >>
        Q_TAC (NEW_TAC "z") ‘FV M ∪ {"x"; "y"}’ >>
        ‘LAM "y" (VAR "x" @@ VAR "y") = LAM z ([VAR z/"y"](VAR "x" @@ VAR "y"))’
          by simp[SIMPLE_ALPHA] >>
        gs[SUB_THM] >>
        ‘LAM z (M @@ VAR z) = LAM v (M @@ VAR v)’
          suffices_by metis_tac[asmlam_sym] >>
        simp[LAM_eq_thm, SF CONJ_ss, tpm_fresh]) >>
  ‘A⁺ (𝟙 @@ M) (I @@ M)’
    by (irule asmlam_lcong  >> simp[Abbr‘A’] >>
        metis_tac[asmlam_sym, asmlam_eqn, IN_INSERT]) >>
  dxrule_all_then assume_tac asmlam_trans >>
  ‘A⁺ (I @@ M) M’ suffices_by metis_tac[asmlam_trans] >>
  simp[lameq_asmlam, lameq_I]
QED

(* Barendregt def'n 4.1.6(i) *)
Definition K0_def:
  K0 = { (M,N) | unsolvable M ∧ unsolvable N ∧ closed M ∧ closed N }
End

Overload "𝒦₀" = “K0”

Definition Kthy_def:
  Kthy = { (M,N) | asmlam K0 M N }
End
Overload "𝒦" = “Kthy”

(* Barendregt def'n 4.1.7(ii) *)
Definition sensible_def:
  sensible 𝒯 ⇔ lambdathy 𝒯 ∧ 𝒦 ⊆ 𝒯
End

(* Barendregt def'n 4.1.7(iii) *)
Definition semisensible_def:
  semisensible 𝒯 ⇔ ∀M N. 𝒯⁺ M N ⇒ ¬(unsolvable M ∧ solvable N)
End

val Kfp_def =
  new_specification ("Kfp_def", ["Kfp"], SPEC “K:term” fixed_point_thm);

Overload "K∞" = “Kfp”

Theorem FV_Kfp[simp]:
  FV Kfp = {}
Proof
  simp[Kfp_def]
QED

Theorem Kfp_thm:
  Kfp @@ x == Kfp
Proof
  strip_assume_tac Kfp_def >>
  dxrule_then (qspec_then ‘x’ assume_tac) lameq_APPL >>
  dxrule_then assume_tac lameq_SYM >> irule lameq_TRANS >>
  first_x_assum $ irule_at Any >> simp[lameq_K]
QED

Theorem KfpI:
  𝒯⁺ I Kfp ⇒ inconsistent 𝒯⁺
Proof
  strip_tac >> simp[inconsistent_def] >>
  qx_genl_tac [‘M’, ‘N’] >>
  qmatch_abbrev_tac ‘A M N’ >>
  ‘∀P. A P Kfp’
    suffices_by (strip_tac >> simp[Abbr‘A’] >>
                 metis_tac[asmlam_trans, asmlam_sym]) >>
  qx_gen_tac ‘P’ >>
  ‘A P (I @@ P)’
    by (simp[Abbr‘A’] >> metis_tac[asmlam_sym, lameq_asmlam, lameq_I]) >>
  ‘A (I @@ P) (Kfp @@ P)’
    by (simp[Abbr‘A’] >> metis_tac[asmlam_lcong, IN_INSERT, asmlam_eqn]) >>
  ‘∀x y z. A x y ∧ A y z ⇒ A x z’ by metis_tac[asmlam_trans] >>
  first_assum $ dxrule_all_then assume_tac >>
  first_x_assum irule >> pop_assum $ irule_at Any >>
  simp[Abbr‘A’, lameq_asmlam, Kfp_thm]
QED

Theorem asmlam_EMPTY:
  asmlam {} = $==
Proof
  simp[FUN_EQ_THM, EQ_IMP_THM, lameq_asmlam] >>
  Induct_on ‘asmlam’ >> metis_tac[lameq_rules, NOT_IN_EMPTY]
QED

Theorem Kfp_unsolvable[simp]:
  unsolvable Kfp
Proof
  simp[solvable_alt_closed, closed_def] >>
  Induct >> simp[]
  >- (strip_tac >> gvs[GSYM asmlam_EMPTY] >>
      dxrule_then assume_tac asmlam_sym >> drule KfpI >>
      simp[asmlam_EMPTY, lameq_consistent]) >>
  rpt strip_tac >>
  resolve_then Any assume_tac Kfp_thm lameq_appstar_cong >>
  metis_tac[lameq_SYM, lameq_TRANS]
QED

Theorem lemma4_1_8i:
  I # Kfp
Proof
  simp[incompatible_def, KfpI, asmlam_eqn]
QED

(* argument seems to rely on solvable (LAM v t) ⇔ solvable t, which is proved
   in chapter 8, suggesting all of this stuff should move to a mechanisation of
   chapter 16
Theorem corollary4_1_19:
  sensible 𝒯 ⇒ semisensible 𝒯
Proof
  simp[sensible_def, semisensible_def] >> CCONTR_TAC >> gvs[] >>
  rename [‘solvable M’, ‘unsolvable N’, ‘𝒯⁺ N M’] >>
  wlog_tac ‘closed M ∧ closed N’ [‘M’,‘N’]
  >- (gvs[]
      >- (first_x_assum $ qspecl_then [‘closure M’, ‘closure N’] mp_tac >>
          simp[]
  qpat_x_assum ‘solvable M’ mp_tac >> simp[solvable_def] >>
  qx_genl_tac [‘M'’, ‘Ps’] >> Cases_on ‘M' ·· Ps == I’ >> simp[] >>
  simp[closures_def] >> qx_gen_tac ‘vs’ >> rpt strip_tac >>
QED
*)

Theorem eta_extend_alt_conversion :
    !M N. conversion (RINSERT (beta RUNION eta) M N) = eta_extend {(M,N)}
Proof
    rw [FUN_EQ_THM]
 >> EQ_TAC >> STRIP_TAC
 >- (rename1 ‘eta_extend {(M,N)} x y’ \\
     POP_ASSUM MP_TAC \\
     qid_spec_tac ‘y’ \\
     qid_spec_tac ‘x’ \\
     HO_MATCH_MP_TAC EQC_INDUCTION \\
     simp [CONJ_ASSOC] >> reverse CONJ_TAC
     >- (qx_genl_tac [‘x’, ‘y’, ‘z’] >> STRIP_TAC \\
         MATCH_MP_TAC asmlam_trans \\
         Q.EXISTS_TAC ‘y’ >> art []) \\
     reverse CONJ_TAC
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC asmlam_sym >> art []) \\
     simp [asmlam_refl] \\
     MATCH_MP_TAC compat_closure_ind \\
     simp [CONJ_ASSOC] >> reverse CONJ_TAC
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC asmlam_abscong >> art []) \\
     reverse CONJ_TAC
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC asmlam_lcong >> art []) \\
     reverse CONJ_TAC
     >- (rpt STRIP_TAC \\
         MATCH_MP_TAC asmlam_rcong >> art []) \\
     rw [RINSERT, RUNION] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       MATCH_MP_TAC lameq_asmlam \\
       MATCH_MP_TAC ccbeta_lameq \\
       MATCH_MP_TAC compat_closure_R >> art [],
       (* goal 2 (of 3) *)
       MATCH_MP_TAC asmlam_eqn >> rw [],
       (* goal 3 (of 3) *)
       MATCH_MP_TAC asmlam_eqn >> rw [] ])
 >> rename1 ‘eta_extend {(M,N)} x y’
 >> POP_ASSUM MP_TAC
 >> qid_spec_tac ‘y’
 >> qid_spec_tac ‘x’
 >> HO_MATCH_MP_TAC asmlam_ind >> rw [] (* 8 subgoals *)
 >| [ (* goal 1 (of 8) *)
      MATCH_MP_TAC EQC_R \\
      MATCH_MP_TAC compat_closure_R \\
      rw [RINSERT, RUNION],
      (* goal 2 (of 8) *)
      MATCH_MP_TAC EQC_R \\
      MATCH_MP_TAC compat_closure_R \\
      rw [RINSERT, RUNION],
      (* goal 3 (of 8) *)
      MATCH_MP_TAC EQC_R \\
      MATCH_MP_TAC compat_closure_R \\
      rw [RINSERT, RUNION, beta_def] \\
      DISJ1_TAC >> DISJ1_TAC \\
      qexistsl_tac [‘x’, ‘M'’] >> art [],
      (* goal 4 (of 8) *)
      rw [conversion_rules],
      (* goal 5 (of 8) *)
      METIS_TAC [conversion_rules],
      (* goal 6 (of 8) *)
      PROVE_TAC [conversion_compatible, compatible_def, rightctxt, rightctxt_thm],
      (* goal 7 (of 8) *)
      PROVE_TAC [conversion_compatible, compatible_def, leftctxt],
      (* goal 8 (of 8) *)
      PROVE_TAC [conversion_compatible, compatible_def, absctxt] ]
QED

(* Definition 4.1.22 [1, p.83] (Hilbert-Post-completeness)

   NOTE: An extra predicate ‘P’ is needed to support [lameta_complete_final],
   which requires ‘has_benf M /\ has_benf N’.

  "HP-complete theories correspond to maximally consistent theories in first order
   model theory." (same page of [1])

   NOTE: In particular, asmlam ((UNCURRY eta) UNION {(M,N)}) := eta_extend {(M,N)}
 *)
Definition HP_complete_def :
    HP_complete thy P <=>
      !M N. P M /\ P N ==>
            asmlam thy M N \/ inconsistent (asmlam (thy UNION {(M,N)}))
End

(* NOTE: This is the unconditional version of HP-completeness.

  "It will be proved in Chapter 16 that “Kthy” has a quite natural unique HP-complete
   extension “Kthy_star” such that “|- HP_complete' Kthy_star” holds.
 *)
Overload HP_complete' = “\thy. HP_complete thy (K T)”

val _ = html_theory "chap4";

(* References:

 [1] Barendregt, H.P.: The lambda calculus, its syntax and semantics.
     College Publications, London (1984).
 *)
