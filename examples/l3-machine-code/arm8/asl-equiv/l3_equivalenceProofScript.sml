open HolKernel boolLib bossLib Parse BasicProvers dep_rewrite
open armv86aTheory armv86a_terminationTheory armv86a_typesTheory
open arm8Theory arm8Lib arm8_stepTheory arm8_stepLib
open wordsTheory bitstringTheory finite_mapTheory listTheory
     arithmeticTheory integerTheory realTheory intrealTheory
open l3_equivalenceTheory l3_equivalence_miscTheory l3_equivalence_lemmasTheory
open wordsLib intLib l3_equivalenceLib

val _ = new_theory "l3_equivalenceProof";

Type res = ``:('a, exception) result # regstate sequential_state``;

(****************************************)

Theorem HaveEL_T[simp]:
  ∀el. HaveEL el = returnS T
Proof
  rw[FUN_EQ_THM, HaveEL_def, returnS] >>
  Cases_on_word_value `el` >> gvs[]
QED

Theorem HaveVirtHostExt_T[simp]:
  HaveVirtHostExt () = T
Proof
  rw[HaveVirtHostExt_def]
QED

Theorem HavePACExt_T[simp]:
  HavePACExt () = T
Proof
  rw[HavePACExt_def]
QED

Theorem HaveAnyAArch32_T[simp]:
  HaveAnyAArch32 () = T
Proof
  rw[HaveAnyAArch32_def]
QED

Theorem HighestELUsingAArch32_F:
  ∀asl.  ¬ asl.regstate.bool_reg "__highest_el_aarch32"
  ⇒ HighestELUsingAArch32 () asl = returnS F asl
Proof
  simp[HighestELUsingAArch32_def, asl_reg_rws, highest_el_aarch32_ref_def]
QED

Theorem UsingAArch32_F:
  ∀asl.
    (asl.regstate.ProcState_reg "PSTATE").ProcState_nRW = 0b0w ∧
    ¬ asl.regstate.bool_reg "__highest_el_aarch32"
  ⇒ UsingAArch32 () asl = returnS F asl
Proof
  rw[UsingAArch32_def] >>
  simp[Once bindS, asl_reg_rws, returnS] >>
  simp[HighestELUsingAArch32_def, asl_reg_rws, highest_el_aarch32_ref_def] >>
  simp[bindS, returnS]
QED

Theorem HighestEL_EL3[simp]:
  HighestEL () = returnS EL3
Proof
  rw[HighestEL_def]
QED

Theorem HaveSecureEL2Ext_T[simp]:
  HaveSecureEL2Ext () = T
Proof
  rw[HaveSecureEL2Ext_def]
QED

Theorem HaveNV2Ext_T[simp]:
  HaveNV2Ext () = returnS T
Proof
  rw[FUN_EQ_THM, HaveNV2Ext_def, HaveNVExt_def,
     IMPDEF_boolean_def, IMPDEF_boolean_map_def]
QED

Theorem HaveEMPAMExt[simp]:
  HaveEMPAMExt () = returnS F
Proof
  rw[FUN_EQ_THM] >> EVAL_TAC
QED

Theorem HaveMPAMExt[simp]:
  HaveMPAMExt () = returnS F
Proof
  rw[FUN_EQ_THM] >> EVAL_TAC
QED

Theorem HaveMTEExt[simp]:
  HaveMTEExt () = returnS T
Proof
  rw[FUN_EQ_THM] >> EVAL_TAC
QED

Theorem HaveAArch32EL:
  ∀asl el. ¬ asl.regstate.bool_reg "__highest_el_aarch32"
  ⇒ HaveAArch32EL el asl = returnS (el ≠ EL3) asl
Proof
  rpt gen_tac >> strip_tac >> simp[HaveAArch32EL_def] >>
  drule HighestELUsingAArch32_F >> strip_tac >>
  drule $ INST_TYPE [gamma |-> bool] returnS_bindS >> simp[] >>
  disch_then kall_tac >>
  Cases_on_word_value `el` >> simp[returnS]
QED

Theorem IsSecureBelowEL3:
  ∀asl. ¬ asl.regstate.bool_reg "__highest_el_aarch32"
  ⇒ IsSecureBelowEL3 () asl =
    returnS (¬ word_bit 0 (asl.regstate.bitvector_64_dec_reg "SCR_EL3")) asl
Proof
  rw[IsSecureBelowEL3_def, SCR_GEN_read_def, SCR_read_def] >>
  drule HighestELUsingAArch32_F >> strip_tac >>
  drule $ INST_TYPE [gamma |-> bool] returnS_bindS >> simp[] >>
  disch_then kall_tac >> simp[asl_reg_rws, returnS, bindS, asl_word_rws] >>
  simp[EL_MAP, sail2_valuesTheory.just_list_def] >>
  DEP_REWRITE_TAC[el_w2v] >> simp[] >> blastLib.BBLAST_TAC >> simp[SCR_EL3_ref_def]
QED

Theorem IsSecure:
  ∀asl.
    (asl.regstate.ProcState_reg "PSTATE").ProcState_nRW = 0b0w ∧
    ¬asl.regstate.bool_reg "__highest_el_aarch32" ∧
    word_bit 0 (asl.regstate.bitvector_64_dec_reg "SCR_EL3")
  ⇒ IsSecure () asl =
    returnS ((asl.regstate.ProcState_reg "PSTATE").ProcState_EL = EL3) asl
Proof
  rw[IsSecure_def] >>
  drule_all UsingAArch32_F >> strip_tac >>
  drule $ INST_TYPE [gamma |-> bool] returnS_bindS >> simp[] >> strip_tac >>
  simp[asl_reg_rws, Once bindS, Once returnS] >>
  IF_CASES_TAC >> gvs[] >> simp[Once bindS, Once returnS, IsSecureBelowEL3]
QED

Theorem IsSecure_returnS:
  ∀asl.  ¬asl.regstate.bool_reg "__highest_el_aarch32" ⇒
  ∃w. IsSecure () asl = returnS w asl
Proof
  rw[IsSecure_def, UsingAArch32_def, IsSecureBelowEL3_def,
     HighestELUsingAArch32_def, SCR_GEN_read_def, SCR_read_def] >>
  simp[asl_word_rws, asl_reg_rws, highest_el_aarch32_ref_def] >>
  simp[EL_MAP, sail2_valuesTheory.just_list_def, el_w2v] >>
  simp[returnS, bindS, seqS] >>
  EVERY_CASE_TAC >> gvs[returnS, bindS, seqS] >>
  EVERY_CASE_TAC >> gvs[returnS, bindS, seqS]
QED

(*
  Alternatively:
  ¬ word_bit 31 HCR_EL2 ⇒
    word_bit 31 HCR_EL3 ∧ ¬ word_bit 27 HCR_EL2
*)
Theorem ELUsingAArch32_F:
  ∀asl el.
    ¬ asl.regstate.bool_reg "__highest_el_aarch32" ∧
    (let SCR_EL3 = asl.regstate.bitvector_64_dec_reg "SCR_EL3" in
      word_bit 0 SCR_EL3 (* ELs below 3 are non-secure *) ∧
      word_bit 10 SCR_EL3 (* RW bit - ELs below 3 are not AArch32 *)) ∧
    (let HCR_EL2 = asl.regstate.bitvector_64_dec_reg "HCR_EL2" in
      word_bit 31 HCR_EL2 (* RW bit - EL1 is AArch64 *)) ∧
    (asl.regstate.ProcState_reg "PSTATE").ProcState_nRW = 0b0w ∧
    (el = EL0 ⇒ (asl.regstate.ProcState_reg "PSTATE").ProcState_EL = EL0)
  ⇒ ELUsingAArch32 el asl = returnS F asl
Proof
  rw[] >> simp[ELUsingAArch32_def] >>
  drule IsSecureBelowEL3 >> strip_tac >>
  drule $ INST_TYPE [gamma |-> bool] returnS_bindS >> simp[] >>
  disch_then kall_tac >> pop_assum kall_tac >>
  simp[ELStateUsingAArch32_def, sail2_state_monadTheory.undefined_boolS_def] >>
  simp[ELStateUsingAArch32K_def] >>
  drule HaveAArch32EL >> disch_then $ qspec_then `el` assume_tac >>
  drule $ INST_TYPE [gamma |-> bool] returnS_bindS >> simp[] >> strip_tac >>
  IF_CASES_TAC >> simp[] >>
  drule HighestELUsingAArch32_F >> strip_tac >>
  drule $ INST_TYPE [gamma |-> bool] returnS_bindS >> simp[] >>
  rw[sail2_state_monadTheory.undefined_boolS_def] >>
  simp[pairTheory.LAMBDA_PROD] >>
  simp[asl_reg_rws, asl_word_rws, SCR_EL3_ref_def, HCR_EL2_ref_def] >>
  simp[sail2_operators_mwordsTheory.slice_def] >>
  simp[extract_bit_64, v2w_word1_eq] >>
  ntac 3 $ simp[Once bindS, Once returnS] >>
  IF_CASES_TAC >> simp[] >>
  ntac 2 $ simp[Once bindS, Once returnS]
QED

Theorem IsSecureEL2Enabled_F:
  ∀asl.
    ¬ asl.regstate.bool_reg "__highest_el_aarch32" ∧
    (let SCR_EL3 = asl.regstate.bitvector_64_dec_reg "SCR_EL3" in
     word_bit 0 SCR_EL3 (* ELs below 3 are non-secure *) ∧
     word_bit 10 SCR_EL3 (* RW bit - ELs below 3 are not AArch32 *) ∧
     ¬ word_bit 18 SCR_EL3 (* Secure EL2 disabled *)) ∧
    (let HCR_EL2 = asl.regstate.bitvector_64_dec_reg "HCR_EL2" in
      word_bit 31 HCR_EL2 (* RW bit - EL1 is AArch64 *)) ∧
    (asl.regstate.ProcState_reg "PSTATE").ProcState_nRW = 0b0w
  ⇒ IsSecureEL2Enabled () asl = returnS F asl
Proof
  rw[] >> simp[IsSecureEL2Enabled_def] >>
  qspecl_then [`asl`,`EL3`] mp_tac ELUsingAArch32_F >> rw[] >>
  drule $ INST_TYPE [gamma |-> bool] returnS_bindS >> rw[] >>
  simp[asl_reg_rws, SCR_EL3_ref_def, returnS, bindS, extract_bit_64]
QED

Theorem ELIsInHost_F:
  ∀asl el.
    ¬ asl.regstate.bool_reg "__highest_el_aarch32" ∧
    (let SCR_EL3 = asl.regstate.bitvector_64_dec_reg "SCR_EL3" in
     word_bit 0 SCR_EL3 (* ELs below 3 are non-secure *) ∧
     word_bit 10 SCR_EL3 (* RW bit - ELs below 3 are not AArch32 *) ∧
     ¬ word_bit 18 SCR_EL3 (* Secure EL2 disabled *)) ∧
    (let HCR_EL2 = asl.regstate.bitvector_64_dec_reg "HCR_EL2" in
      word_bit 31 HCR_EL2 (* RW bit - EL1 is AArch64 *) ∧
      ¬ word_bit 34 HCR_EL2 (* Virtualization Host Extension (FEAT_VHE) disabled *)) ∧
    (asl.regstate.ProcState_reg "PSTATE").ProcState_nRW = 0b0w
  ⇒ ELIsInHost el asl = returnS F asl
Proof
  rw[] >> simp[ELIsInHost_def] >>
  qspec_then `asl` mp_tac IsSecureEL2Enabled_F >> simp[] >> strip_tac >>
  drule $ INST_TYPE [gamma |-> bool] returnS_bindS >> simp[] >> disch_then kall_tac >>
  drule IsSecureBelowEL3 >> strip_tac >>
  drule $ INST_TYPE [gamma |-> bool] returnS_bindS >> simp[] >> disch_then kall_tac >>
  qspecl_then [`asl`,`EL2`] mp_tac ELUsingAArch32_F >> simp[] >> strip_tac >>
  drule $ INST_TYPE [gamma |-> bool] returnS_bindS >> simp[] >> disch_then kall_tac >>
  simp[asl_reg_rws, HCR_EL2_ref_def, returnS, bindS, COND_RATOR, extract_bit_64]
QED

Theorem S1TranslationRegime:
  ∀asl el.
    ¬ asl.regstate.bool_reg "__highest_el_aarch32" ∧
    (let SCR_EL3 = asl.regstate.bitvector_64_dec_reg "SCR_EL3" in
     word_bit 0 SCR_EL3 (* ELs below 3 are non-secure *) ∧
     word_bit 10 SCR_EL3 (* RW bit - ELs below 3 are not AArch32 *) ∧
     ¬ word_bit 18 SCR_EL3 (* Secure EL2 disabled *)) ∧
    (let HCR_EL2 = asl.regstate.bitvector_64_dec_reg "HCR_EL2" in
      word_bit 31 HCR_EL2 (* RW bit - EL1 is AArch64 *) ∧
      ¬ word_bit 34 HCR_EL2 (* Virtualization Host Extension (FEAT_VHE) disabled *)) ∧
    (asl.regstate.ProcState_reg "PSTATE").ProcState_nRW = 0b0w
  ⇒ S1TranslationRegime el asl = returnS (if el = 0w then 1w else el) asl
Proof
  rw[] >> simp[S1TranslationRegime_def] >>
  qspecl_then [`asl`,`3w`] mp_tac ELUsingAArch32_F >> simp[] >> strip_tac >>
  drule $ INST_TYPE [gamma |-> ``:word2``] returnS_bindS >> simp[] >> strip_tac >>
  qspecl_then [`asl`,`0w`] mp_tac ELIsInHost_F >> simp[] >> strip_tac >>
  drule $ INST_TYPE [gamma |-> ``:word2``] returnS_bindS >> simp[] >> strip_tac
QED

Theorem AArch64_SetLSInstructionSyndrome:
  ∀size sgn r b1 b2 asl.
    (size = 1 ∨ size = 2 ∨ size = 4 ∨ size = 8) ∧
    0 ≤ r ∧ r < 32
  ⇒ ∃v.
    AArch64_SetLSInstructionSyndrome size sgn r b1 b2 asl =
    write_regS LSISyndrome_ref v asl
Proof
  rpt gen_tac >> qmatch_goalsub_abbrev_tac `sizeP ∧ _` >> strip_tac >>
  simp[AArch64_SetLSInstructionSyndrome_def, MakeLSInstructionSyndrome_def] >>
  simp[asl_reg_rws, returnS, bindS, Once COND_RATOR] >>
  simp[Once COND_RAND, COND_RATOR] >> simp[in_range_def] >>
  `r ≤ 31` by (ntac 2 $ last_x_assum kall_tac >> ARITH_TAC) >> simp[] >>
  IF_CASES_TAC >> simp[] >- irule_at Any EQ_REFL >>
  IF_CASES_TAC >> simp[] >- irule_at Any EQ_REFL >>
  simp[returnS, LSISyndrome_ref_def] >>
  qexists_tac `asl.regstate.bitvector_11_dec_reg "__LSISyndrome"` >>
  simp[sail2_state_monadTheory.sequential_state_component_equality,
       regstate_component_equality] >>
  rw[FUN_EQ_THM] >> IF_CASES_TAC >> simp[]
QED

Theorem HasS2Translation:
  ∀asl. asl_sys_regs_ok asl ⇒
    HasS2Translation () asl =
    returnS ((asl.regstate.ProcState_reg "PSTATE").ProcState_EL ∈ {EL0;EL1}) asl
Proof
  rw[HasS2Translation_def, EL2Enabled_def, IsInHost_def] >>
  gvs[asl_sys_regs_ok_def, asl_reg_rws] >>
  simp[Once bindS, Once returnS] >>
  DEP_REWRITE_TAC[extract_bit_64] >> simp[SCR_EL3_ref_def] >>
  simp[Once bindS, Once returnS] >>
  qmatch_goalsub_abbrev_tac `ELIsInHost el` >>
  qspecl_then [`asl`,`el`] mp_tac ELIsInHost_F >> rw[] >>
  drule $ INST_TYPE [gamma |-> bool] returnS_bindS >>
  simp[] >> disch_then kall_tac >>
  simp[COND_RATOR, bindS, returnS] >> IF_CASES_TAC >> simp[]
QED

Theorem DoubleLockStatus[simp]:
  DoubleLockStatus () = returnS F
Proof
  rw[FUN_EQ_THM] >> EVAL_TAC
QED

Theorem AArch64_AccessIsTagChecked:
  ∀vaddr acctype asl.
    word_bit 4 ((asl.regstate.ProcState_reg "PSTATE").ProcState_M) ⇒
    AArch64_AccessIsTagChecked vaddr acctype asl = returnS F asl
Proof
  rw[] >> simp[AArch64_AccessIsTagChecked_def] >>
  simp[asl_word_rws, asl_reg_rws, Once bindS, Once returnS] >>
  DEP_REWRITE_TAC[HD_MAP] >> simp[w2v_not_NIL] >>
  simp[sail2_valuesTheory.just_list_def] >>
  once_rewrite_tac[GSYM EL] >>
  DEP_REWRITE_TAC[el_w2v] >> simp[] >> gvs[word_bit_def]
QED

Theorem GenMPAMcurEL:
  ∀b asl. ¬asl.regstate.bool_reg "__highest_el_aarch32" ⇒
  GenMPAMcurEL b asl = do
    s <- IsSecure ();
    returnS <|
      MPAMinfo_mpam_ns := v2w [¬s];
      MPAMinfo_partid := 0w;
      MPAMinfo_pmg := 0w |>
    od asl
Proof
  rw[GenMPAMcurEL_def, sail2_state_monadTheory.undefined_boolS_def] >>
  drule IsSecure_returnS >> strip_tac >>
  simp[
    sail2_state_monadTheory.liftRS_def,
    sail2_state_monadTheory.catch_early_returnS_def,
    sail2_state_monadTheory.try_catchS_def,
    returnS, bindS
    ] >>
  EVAL_TAC >> IF_CASES_TAC >> gvs[]
QED

Theorem CreateAccessDescriptor:
  ∀acctype asl. ¬asl.regstate.bool_reg "__highest_el_aarch32" ⇒
  CreateAccessDescriptor acctype asl = do
    s <- IsSecure();
    returnS
      <|
        AccessDescriptor_acctype := acctype;
        AccessDescriptor_mpam := <|
          MPAMinfo_mpam_ns := v2w [¬s];
          MPAMinfo_partid := 0w;
          MPAMinfo_pmg := 0w |>;
        AccessDescriptor_page_table_walk := F;
        AccessDescriptor_secondstage := @x. T;
        AccessDescriptor_s2fs1walk := @x. T;
        AccessDescriptor_level := ARB
      |>
    od asl
Proof
  rw[CreateAccessDescriptor_def, undefined_AccessDescriptor_def,
     undefined_AccType_def, undefined_MPAMinfo_def,
     sail2_state_monadTheory.undefined_boolS_def, preludeTheory.undefined_int_def] >>
  drule GenMPAMcurEL >> rw[] >>
  simp[bindS, returnS] >>
  drule IsSecure_returnS >> rw[] >> simp[returnS]
QED

Theorem Halted_F:
  ((5 >< 0) (asl.regstate.bitvector_32_dec_reg "EDSCR") = 0b1w ∨
  (5 >< 0) (asl.regstate.bitvector_32_dec_reg "EDSCR") = 0b10w)
  ⇒ Halted () asl = returnS F asl
Proof
  rw[Halted_def, asl_reg_rws, EDSCR_ref_def] >>
  ntac 2 $ simp[Once bindS, Once returnS]
QED


(****************************************)

Theorem l3_asl_SetTheFlags:
  ∀l3 asl1. state_rel l3 asl1 ⇒
  ∀n z c v f. ∃asl2.
    do
      p1 <- read_regS PSTATE_ref;
      write_regS PSTATE_ref (p1 with ProcState_N := n);
      p2 <- read_regS PSTATE_ref;
      write_regS PSTATE_ref (p2 with ProcState_Z := z);
      p3 <- read_regS PSTATE_ref;
      write_regS PSTATE_ref (p3 with ProcState_C := c);
      p4 <- read_regS PSTATE_ref;
      write_regS PSTATE_ref (p4 with ProcState_V := v);
      f
    od asl1 =
    f asl2 : unit res ∧
    state_rel (SetTheFlags (T,HD (w2v n),HD (w2v z),HD (w2v c),HD (w2v v)) l3) asl2
Proof
  rw[returnS, seqS, bindS, asl_reg_rws, COND_RATOR, SetTheFlags_def] >>
  irule_at Any EQ_REFL >>
  state_rel_tac[] >> rpt $ pop_assum kall_tac >>
  rename1 `foo = _` >> Cases_on_word_value `foo` >> gvs[]
QED

Theorem l3_asl_SetTheFlags_alt:
  ∀l3 asl1. state_rel l3 asl1 ⇒
  ∀n z c v. ∃asl2.
    do
      p1 <- read_regS PSTATE_ref;
      write_regS PSTATE_ref (p1 with ProcState_N := n);
      p2 <- read_regS PSTATE_ref;
      write_regS PSTATE_ref (p2 with ProcState_Z := z);
      p3 <- read_regS PSTATE_ref;
      write_regS PSTATE_ref (p3 with ProcState_C := c);
      p4 <- read_regS PSTATE_ref;
      write_regS PSTATE_ref (p4 with ProcState_V := v);
    od asl1 =
    returnS () asl2 : unit res ∧
    state_rel (SetTheFlags (T,HD (w2v n),HD (w2v z),HD (w2v c),HD (w2v v)) l3) asl2
Proof
  rw[returnS, seqS, bindS, asl_reg_rws, COND_RATOR, SetTheFlags_def] >>
  state_rel_tac[] >> rpt $ pop_assum kall_tac >>
  rename1 `foo = _` >> Cases_on_word_value `foo` >> gvs[]
QED

Theorem X_set_31:
  width = 32 ∨ width = 64 ⇒
  X_set width 31 v = returnS ()
Proof
  simp[X_set_def]
QED

Theorem X_set_not_31:
  ∀l3 asl1. state_rel l3 asl1 ⇒
  ∀width i v. (width = 32 ∨ width = 64) ∧ i ≥ 0 ∧ i < 31 ⇒
  ∃asl2.
    X_set width i v asl1 = returnS () asl2 ∧
    state_rel (write'X (v, n2w (nat_of_int i)) l3) asl2
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[X_set_def] >> IF_CASES_TAC >> gvs[returnS] >>
  simp[asl_reg_rws] >>
  IF_CASES_TAC >> gvs[] >- (strip_tac >> irule FALSITY >> ARITH_TAC) >>
  simp[bindS, returnS, write'X_def] >>
  reverse IF_CASES_TAC >> gvs[] >- (strip_tac >> irule FALSITY >> ARITH_TAC) >>
  rw[] >> state_rel_tac[] >> irule FALSITY >> ARITH_TAC
QED

Theorem X_set_asl_sys_regs_ok:
  ∀asl asl' width r v.
    asl_sys_regs_ok asl ∧ X_set width r v asl = returnS () asl'
  ⇒ asl_sys_regs_ok asl'
Proof
  rw[] >> gvs[X_set_def, returnS, bindS, seqS, failS, COND_RATOR, asl_reg_rws] >>
  every_case_tac >> gvs[asl_sys_regs_ok_def]
QED

Theorem X_read:
  ∀l3 asl. state_rel l3 asl ⇒
  ∀i. i ≥ 0 ∧ i ≤ 31 ⇒
  X_read 64 i asl = returnS (X (n2w (nat_of_int i)) l3 : 64 word) asl
Proof
  rw[] >> simp[X_read_def] >> IF_CASES_TAC >> gvs[] >>
  simp[asl_reg_rws, bindS, X_def, returnS] >>
  IF_CASES_TAC >> gvs[] >- (irule FALSITY >> ARITH_TAC) >>
  IF_CASES_TAC >> gvs[] >- (irule FALSITY >> ARITH_TAC) >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  state_rel_tac[] >> first_x_assum $ irule o GSYM >> ARITH_TAC
QED

Theorem X_read32:
  ∀l3 asl. state_rel l3 asl ⇒
  ∀i. i ≥ 0 ∧ i ≤ 31 ⇒
  X_read 32 i asl = returnS (X (n2w (nat_of_int i)) l3 : word32) asl
Proof
  rw[] >> simp[X_read_def] >> IF_CASES_TAC >> gvs[] >>
  simp[asl_reg_rws, bindS, X_def, returnS] >>
  IF_CASES_TAC >> gvs[] >- (irule FALSITY >> ARITH_TAC) >>
  IF_CASES_TAC >> gvs[] >- (irule FALSITY >> ARITH_TAC) >>
  `reg_rel l3.REG asl.regstate` by state_rel_tac[] >> gvs[reg_rel_def] >>
  first_x_assum $ qspec_then `Num i` $ mp_tac o GSYM >> impl_tac >- ARITH_TAC >>
  rw[R_ref_def] >> blastLib.BBLAST_TAC
QED

Theorem X_read_8:
  ∀l3 asl. state_rel l3 asl ⇒
  ∀i. i ≥ 0 ∧ i ≤ 31 ⇒
  X_read 8 i asl = returnS (X (n2w (nat_of_int i)) l3 : word8) asl
Proof
  rw[] >> simp[X_read_def] >> IF_CASES_TAC >> gvs[] >>
  simp[asl_reg_rws, bindS, X_def, returnS] >>
  IF_CASES_TAC >> gvs[] >- (irule FALSITY >> ARITH_TAC) >>
  IF_CASES_TAC >> gvs[] >- (irule FALSITY >> ARITH_TAC) >>
  `reg_rel l3.REG asl.regstate` by state_rel_tac[] >> gvs[reg_rel_def] >>
  first_x_assum $ qspec_then `Num i` $ mp_tac o GSYM >> impl_tac >- ARITH_TAC >>
  rw[R_ref_def] >> blastLib.BBLAST_TAC
QED

Theorem SP_read:
  ∀l3 asl. state_rel l3 asl ⇒
  SP_read 64 asl = returnS (SP l3 : 64 word) asl
Proof
  rw[] >> simp[SP_read_def, SP_def] >>
  state_rel_tac[] >> simp[bindS, returnS] >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[]
QED

Theorem SP_set:
  ∀l3 asl. state_rel l3 asl ⇒
  ∀v. ∃asl2.
    SP_set 64 v asl = returnS () asl2 ∧
    state_rel (write'SP v l3) asl2
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[SP_set_def, asl_reg_rws, returnS, bindS, write'SP_def] >>
  IF_CASES_TAC >> gvs[] >- state_rel_tac[] >>
  IF_CASES_TAC >> gvs[] >- state_rel_tac[] >>
  simp[bindS, COND_RATOR, returnS] >>
  Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >> state_rel_tac[]
QED

Theorem SP_set_asl_sys_regs_ok:
  ∀asl asl' width v.
    asl_sys_regs_ok asl ∧ SP_set width v asl = returnS () asl'
  ⇒ asl_sys_regs_ok asl'
Proof
  rw[] >> gvs[SP_set_def, returnS, bindS, seqS, failS, COND_RATOR, asl_reg_rws] >>
  every_case_tac >> gvs[asl_sys_regs_ok_def]
QED

Theorem PC_read:
  ∀l3 asl. state_rel l3 asl ⇒
    PC_read () asl = returnS l3.PC asl
Proof
  rw[] >> simp[PC_read_def] >> state_rel_tac[]
QED

Theorem PSTATE_read:
  ∀asl.
    read_regS PSTATE_ref asl =
    returnS (asl.regstate.ProcState_reg "PSTATE") asl : ProcState res
Proof
  rw[asl_reg_rws]
QED

Theorem TCR_EL1_read:
  ∀l3 asl. state_rel l3 asl ⇒
    read_regS TCR_EL1_ref asl =
    returnS (reg'TCR_EL1 l3.TCR_EL1) asl : word64 res
Proof
  rw[asl_reg_rws] >> state_rel_tac[]
QED

(* TODO: should we require upper bits of TCR_EL2 to be clear? *)
Theorem TCR_EL2_read:
  ∀l3 asl. state_rel l3 asl ⇒
    read_regS TCR_EL2_ref asl =
    returnS ((63 >< 32) (asl.regstate.bitvector_64_dec_reg "TCR_EL2") @@
              reg'TCR_EL2_EL3 l3.TCR_EL2) asl : word64 res
Proof
  rw[asl_reg_rws] >> state_rel_tac[] >>
  simp[returnS] >> blastLib.BBLAST_TAC
QED

Theorem TCR_EL3_read:
  ∀l3 asl. state_rel l3 asl ⇒
    read_regS TCR_EL3_ref asl =
    returnS (reg'TCR_EL2_EL3 l3.TCR_EL3) asl : word32 res
Proof
  rw[asl_reg_rws] >> state_rel_tac[] >>
  simp[returnS] >> blastLib.BBLAST_TAC
QED

Theorem SCTLR_read:
  ∀l3 asl. state_rel l3 asl ⇒
    ∀el. el ≠ 0w ⇒
    SCTLR_read el asl =
    returnS
    (case el of
    | 1w =>
        (63 >< 32) (asl.regstate.bitvector_64_dec_reg "SCTLR_EL1") @@
        reg'SCTLRType l3.SCTLR_EL1
    | 2w =>
        (63 >< 32) (asl.regstate.bitvector_64_dec_reg "SCTLR_EL2") @@
        reg'SCTLRType l3.SCTLR_EL2
    | 3w =>
        (63 >< 32) (asl.regstate.bitvector_64_dec_reg "SCTLR_EL3") @@
        reg'SCTLRType l3.SCTLR_EL3)
    asl
Proof
  rw[asl_reg_rws, SCTLR_read_def] >>
  Cases_on_word_value `el` >> gvs[returnS] >>
  state_rel_tac[] >> blastLib.BBLAST_TAC
QED

Definition aslSCTLR_def:
  aslSCTLR el asl =
  case el of
  | 0w => asl.regstate.bitvector_64_dec_reg "SCTLR_EL1"
  | 1w => asl.regstate.bitvector_64_dec_reg "SCTLR_EL1"
  | 2w => asl.regstate.bitvector_64_dec_reg "SCTLR_EL2"
  | 3w => asl.regstate.bitvector_64_dec_reg "SCTLR_EL3"
End

Theorem SCTLR_read__1:
  ∀l3 asl. state_rel l3 asl ∧ asl_sys_regs_ok asl ⇒
    SCTLR_read__1 () asl =
    returnS ((63 >< 32) (aslSCTLR l3.PSTATE.EL asl) @@ (reg'SCTLRType $ SCTLR l3)) asl
Proof
  rw[SCTLR_read__1_def, S1TranslationRegime__1_def] >>
  qspec_then `asl` assume_tac PSTATE_read >>
  drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >>
  simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `foo.ProcState_EL` >>
  `foo.ProcState_EL = l3.PSTATE.EL` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[] >>
  qspecl_then [`asl`,`l3.PSTATE.EL`] mp_tac S1TranslationRegime >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
  drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >>
  simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `SCTLR_read el'` >>
  drule SCTLR_read >> disch_then $ qspec_then `el'` mp_tac >>
  impl_tac >- (unabbrev_all_tac >> IF_CASES_TAC >> gvs[]) >>
  simp[returnS] >> disch_then kall_tac >> unabbrev_all_tac >>
  simp[aslSCTLR_def, SCTLR_def, TranslationRegime_def] >>
  Cases_on_word_value `l3.PSTATE.EL` >> gvs[]
QED


(****************************************)

Theorem l3_models_asl_NoOperation:
  l3_models_asl_instr NoOperation
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >>
  l3_decode_tac >> l3_run_tac >>
  asl_execute_tac >> gvs[] >>
  state_rel_tac []
QED

Theorem l3_models_asl_MoveWideOp_Z:
  ∀b hw imm16 r.
    l3_models_asl_instr (Data (MoveWide@64 (b, MoveWideOp_Z, hw, imm16, r)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >>
  asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
  simp[decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  simp[undefined_MoveWideOp_def] >>
  simp[execute_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  reverse IF_CASES_TAC >> gvs[] >- (Cases_on_word_value `hw` >> gvs[]) >>
  Cases_on `r = 31w` >> gvs[INT_ADD_CALCULATE]
  >- (DEP_REWRITE_TAC[X_set_31] >> simp[returnS] >> state_rel_tac[]) >>
  qmatch_goalsub_abbrev_tac `X_set _ reg v asl1` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel _ asl` kall_tac >>
  dxrule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`reg`,`v`] mp_tac >> simp[Abbr `reg`, int_ge] >>
  impl_tac >- WORD_DECIDE_TAC >> strip_tac >> simp[] >> gvs[write'X_def, returnS] >>
  irule $ b64 alpha X_set_asl_sys_regs_ok >> simp[returnS] >> rpt $ goal_assum drule
QED

Theorem l3_models_asl_MoveWideOp_N:
  ∀b hw imm16 r.
    l3_models_asl_instr (Data (MoveWide@64 (b, MoveWideOp_N, hw, imm16, r)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >>
  asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
  gvs[decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[undefined_MoveWideOp_def] >>
  gvs[execute_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  reverse IF_CASES_TAC >> gvs[] >- (Cases_on_word_value `hw` >> gvs[]) >>
  Cases_on `r = 31w` >> gvs[INT_ADD_CALCULATE]
  >- (DEP_REWRITE_TAC[X_set_31] >> simp[returnS] >> state_rel_tac[]) >>
  qmatch_goalsub_abbrev_tac `X_set _ reg v asl1` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel _ asl` kall_tac >>
  dxrule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`reg`,`v`] mp_tac >> simp[Abbr `reg`, int_ge] >>
  impl_tac >- WORD_DECIDE_TAC >> strip_tac >> simp[] >> gvs[write'X_def, returnS] >>
  irule $ b64 alpha X_set_asl_sys_regs_ok >> simp[returnS] >> rpt $ goal_assum drule
QED

Theorem l3_models_asl_MoveWideOp_K:
  ∀b hw r.
    l3_models_asl_instr (Data (MoveWide@64 (b, MoveWideOp_K, hw, i, r)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >>
  asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
  gvs[decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[undefined_MoveWideOp_def] >>
  gvs[execute_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  reverse IF_CASES_TAC >> gvs[] >- (Cases_on_word_value `hw` >> gvs[]) >>
  qmatch_goalsub_abbrev_tac `bindS x f asl1` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel _ asl` kall_tac >>
  drule X_read >> disch_then $ qspec_then `&w2n r` mp_tac >> impl_tac
  >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  qspec_then `f` drule returnS_bindS  >> simp[Abbr `f`] >> strip_tac >>
  Cases_on `r = 31w` >> gvs[]
  >- (DEP_REWRITE_TAC[X_set_31] >> simp[returnS]) >>
  simp[INT_ADD_CALCULATE, X_def] >>
  qmatch_goalsub_abbrev_tac `X_set _ reg v _` >>
  dxrule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`reg`,`v`] mp_tac >> simp[Abbr `reg`, int_ge] >>
  impl_tac >- WORD_DECIDE_TAC >> strip_tac >> simp[] >> gvs[write'X_def, returnS] >>
  irule $ b64 alpha X_set_asl_sys_regs_ok >> simp[returnS] >> rpt $ goal_assum drule
QED

Theorem l3_asl_AddWithCarry:
  ∀x y carry_b carry_v.
    flag_rel carry_b carry_v
  ⇒ armv86a$AddWithCarry x y carry_v =
     (I ## (λ(a,b,c,d).v2w [a;b;c;d])) (arm8$AddWithCarry (x, y, carry_b))
Proof
  rw[flag_rel_def] >> gvs[armv86aTheory.AddWithCarry_def, AddWithCarry_def] >>
  simp[integer_subrange_def, asl_word_rws] >> conj_asm1_tac >>
  simp[lemTheory.w2ui_def, INT_ADD] >>
  simp[w2n_v2w, v2n, bitTheory.MOD_2EXP_def] >>
  qmatch_goalsub_abbrev_tac `b MOD 2` >>
  `b MOD 2 = b` by (unabbrev_all_tac >> rw[]) >> simp[]
  >- (
    map_every qmatch_goalsub_abbrev_tac [`n2w n`, `TAKE l`] >>
    qspec_then `fixwidth l (n2v n)` mp_tac TAKE_LENGTH_ID >>
    rewrite_tac[length_fixwidth] >> disch_then SUBST_ALL_TAC >>
    unabbrev_all_tac >> simp[v2w_fixwidth]
    ) >>
  simp[] >> qmatch_goalsub_abbrev_tac `n2w stuff` >>
  DEP_REWRITE_TAC[HD_MAP] >> conj_asm1_tac
  >- (
    qsuff_tac `LENGTH (w2v (n2w stuff)) ≠ 0` >- rw[] >>
    rewrite_tac[length_w2v] >> assume_tac EXISTS_HB >> gvs[]
    ) >>
  simp[sail2_valuesTheory.just_list_def] >>
  unabbrev_all_tac >> blastLib.BBLAST_TAC >> rw[] >> gvs[] >>
  qmatch_goalsub_abbrev_tac `w2v stuff` >>
  qspecl_then [`stuff`,`0`] mp_tac el_w2v >> simp[]
QED

(* TODO this proof has two very similar halves - perhaps these could be combined *)
Theorem l3_models_asl_AddSubImmediate:
  ∀b b1 b2 i r2 r1.
    (i && ¬0b111111111111w ≠ 0b0w ⇒ i && ¬0b111111111111000000000000w = 0b0w)
  ⇒ l3_models_asl_instr
      (Data (AddSubImmediate@64 (b, b1, b2, i, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >> simp[encode_rws] >>
  IF_CASES_TAC >> gvs[]
  >- (
    `i = (0w : 52 word) @@ ((11 >< 0) i : 12 word)` by
      blastLib.FULL_BBLAST_TAC >> gvs[] >>
    last_x_assum kall_tac >> rename1 `_ @@ _ @@ _ @@ _ @@ j @@ _ @@ _` >>
    qmatch_goalsub_abbrev_tac `Decode instr` >>
    `Decode instr =  Data (AddSubImmediate@64 (0b1w,b1,b2,w2w j,r2,r1))` by (
      unabbrev_all_tac >> Cases_on `b1` >> Cases_on `b2` >> l3_decode_tac) >>
    unabbrev_all_tac >> gvs[] >> rw[] >>
    qmatch_asmsub_abbrev_tac `Run (Data (addsubimm instr))` >>
    `Run (Data (addsubimm instr)) = dfn'AddSubImmediate instr` by (
      unabbrev_all_tac >> Cases_on `b1` >> Cases_on `b2` >>
      l3_run_tac >> rw[FUN_EQ_THM]) >>
    unabbrev_all_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac `seqS (wr i) ex` >>
    `∃i'. (do wr i; ex od asl) = (do wr i';
      execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
        (&w2n r1) 64 (w2w j : 64 word) (&w2n r2) b2 b1 od asl)` by (
      unabbrev_all_tac >>
      Cases_on `b1` >> Cases_on `b2` >> gvs[] >>
      asl_cexecute_tac >> simp[] >>
      gvs[
        decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
        decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
        decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
        decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def
        ] >>
      simp[asl_reg_rws, seqS, returnS] >> irule_at Any EQ_REFL) >>
    simp[] >> pop_assum kall_tac >> unabbrev_all_tac >>
    simp[asl_reg_rws, seqS, Once returnS] >>
    qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
    `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    qpat_x_assum `state_rel l3 asl` kall_tac >>
    simp[execute_aarch64_instrs_integer_arithmetic_add_sub_immediate_def] >>
    simp[dfn'AddSubImmediate_def] >>
    `(w2n r1 = 31 ⇔ r1 = 0b11111w) ∧ (w2n r2 = 31 ⇔ r2 = 0b11111w)` by WORD_DECIDE_TAC >>
    simp[] >>
    qpat_abbrev_tac `branch_asl = if b1 then _ else _` >>
    qpat_abbrev_tac `branch_l3 = if b1 then _ else _` >>
    `branch_asl = (λ(a,b). (v2w [b], a)) branch_l3` by (
      unabbrev_all_tac >> IF_CASES_TAC >> gvs[]) >>
    simp[] >>
    PairCases_on `branch_l3` >> gvs[] >>
    qpat_abbrev_tac `read_asl = if r2 = _ then _ else _` >>
    qpat_abbrev_tac `read_l3 = if r2 = _ then _ else _` >>
    `read_asl asl1 = returnS read_l3 asl1` by (
      unabbrev_all_tac >> IF_CASES_TAC >> gvs[]
      >- (irule SP_read >> simp[])
      >- (DEP_REWRITE_TAC[X_read] >> simp[int_ge] >> WORD_DECIDE_TAC)) >>
    simp[] >>
    qmatch_goalsub_abbrev_tac `bindS _ rest` >>
    drule returnS_bindS_unit >> simp[] >> strip_tac >> simp[Abbr `rest`] >>
    qspecl_then [`read_l3`,`branch_l30`,`branch_l31`] mp_tac l3_asl_AddWithCarry >>
    simp[flag_rel_def] >> strip_tac >>
    qmatch_goalsub_abbrev_tac `(_ ## _) add_res` >>
    PairCases_on `add_res` >> gvs[] >>
    reverse IF_CASES_TAC >> gvs[] >> simp[COND_RATOR]
    >- (
      drule $ b64 alpha SP_set >> drule $ b64 alpha X_set_not_31 >>
      disch_then $ qspecl_then [`64`,`&w2n r1`,`add_res0`] assume_tac >>
      disch_then $ qspec_then `add_res0` assume_tac >> gvs[int_ge] >>
      drule_all $ b64 alpha SP_set_asl_sys_regs_ok >> strip_tac >>
      IF_CASES_TAC >> gvs[returnS] >>
      qpat_x_assum `w2n _ < _ ⇒ _` mp_tac >> impl_tac >- WORD_DECIDE_TAC >>
      strip_tac >> simp[] >>
      irule $ b64 alpha X_set_asl_sys_regs_ok >> simp[returnS] >>
      goal_assum $ drule_at $ Pos last >>
      unabbrev_all_tac >> gvs[asl_sys_regs_ok_def]
      )
    >- (
      dxrule l3_asl_SetTheFlags >>
      disch_then $ qspecl_then
        [`v2w [add_res1]`,`v2w [add_res2]`,
         `v2w [add_res3]`,`v2w [add_res4]`,`X_set 64 (&w2n r1) add_res0`] mp_tac >>
      strip_tac >> simp[] >>
      drule $ b64 alpha X_set_not_31 >>
      disch_then $ qspecl_then [`64`,`&w2n r1`,`add_res0`] mp_tac >> simp[int_ge] >>
      `asl_sys_regs_ok asl2` by (
        qpat_x_assum `_ = _ asl2` $ mp_tac o GSYM >>
        simp[bindS, seqS, returnS, failS, asl_reg_rws, X_set_def, COND_RATOR] >>
        rpt CASE_TAC >> rw[] >>
        gvs[sail2_state_monadTheory.sequential_state_component_equality,
           armv86a_typesTheory.ProcState_component_equality,
           regstate_component_equality, FUN_EQ_THM, FORALL_AND_THM] >>
        gvs[asl_sys_regs_ok_def]) >>
      Cases_on `r1 = 31w` >> gvs[]
      >- (gvs[X_set_31, returnS, write'X_def, w2v_v2w]) >>
      impl_tac >- WORD_DECIDE_TAC >>
      strip_tac >> simp[returnS] >> gvs[w2v_v2w] >>
      irule $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule
      )
    )
  >- (
    `i = (0w : 40 word) @@ ((23 >< 12) i : 12 word) @@ (0w : 12 word)` by
      blastLib.FULL_BBLAST_TAC >> gvs[] >>
    qpat_x_assum `_ && i = _` kall_tac >>
    rename1 `_ @@ _ @@ _ @@ _ @@ j @@ _ @@ _` >>
    qmatch_goalsub_abbrev_tac `Decode instr` >>
    `Decode instr =  Data (AddSubImmediate@64 (0b1w,b1,b2,w2w j << 12,r2,r1))` by (
      unabbrev_all_tac >> Cases_on `b1` >> Cases_on `b2` >> l3_decode_tac) >>
    unabbrev_all_tac >> gvs[] >> rw[] >>
    qmatch_asmsub_abbrev_tac `Run (Data (addsubimm instr))` >>
    `Run (Data (addsubimm instr)) = dfn'AddSubImmediate instr` by (
      unabbrev_all_tac >> Cases_on `b1` >> Cases_on `b2` >>
      l3_run_tac >> rw[FUN_EQ_THM]) >>
    unabbrev_all_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac `seqS (wr i) ex` >>
    `∃i'. (do wr i; ex od asl) = (do wr i';
      execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
        (&w2n r1) 64 ((w2w j << 12) : 64 word) (&w2n r2) b2 b1 od asl)` by (
      unabbrev_all_tac >> Cases_on `b1` >> Cases_on `b2` >> gvs[] >>
      asl_cexecute_tac >> simp[] >>
      gvs[
        decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
        decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
        decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
        decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def
        ] >>
      simp[asl_reg_rws, seqS, returnS]
      >- (
        qexists_tac `13` >> simp[] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
        EVAL_TAC >> simp[]
        )
      >- (
        qexists_tac `14` >> simp[] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
        EVAL_TAC >> simp[]
        )
      >- (
        qexists_tac `11` >> simp[] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
        EVAL_TAC >> simp[]
        )
      >- (
        qexists_tac `12` >> simp[] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
        EVAL_TAC >> simp[]
        )) >>
    simp[] >> pop_assum kall_tac >> unabbrev_all_tac >>
    simp[asl_reg_rws, seqS, Once returnS] >>
    qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
    `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    qpat_x_assum `state_rel l3 asl` kall_tac >>
    simp[execute_aarch64_instrs_integer_arithmetic_add_sub_immediate_def] >>
    simp[dfn'AddSubImmediate_def] >>
    `(w2n r1 = 31 ⇔ r1 = 0b11111w) ∧ (w2n r2 = 31 ⇔ r2 = 0b11111w)` by WORD_DECIDE_TAC >>
    simp[] >>
    qpat_abbrev_tac `branch_asl = if b1 then _ else _` >>
    qpat_abbrev_tac `branch_l3 = if b1 then _ else _` >>
    `branch_asl = (λ(a,b). (v2w [b], a)) branch_l3` by (
      unabbrev_all_tac >> IF_CASES_TAC >> gvs[]) >>
    simp[] >>
    PairCases_on `branch_l3` >> gvs[] >>
    qpat_abbrev_tac `read_asl = if r2 = _ then _ else _` >>
    qpat_abbrev_tac `read_l3 = if r2 = _ then _ else _` >>
    `read_asl asl1 = returnS read_l3 asl1` by (
      unabbrev_all_tac >> IF_CASES_TAC >> gvs[]
      >- (irule SP_read >> simp[])
      >- (DEP_REWRITE_TAC[X_read] >> simp[int_ge] >> WORD_DECIDE_TAC)) >>
    simp[] >>
    qmatch_goalsub_abbrev_tac `bindS _ rest` >>
    drule returnS_bindS_unit >> simp[] >> strip_tac >> simp[Abbr `rest`] >>
    qspecl_then [`read_l3`,`branch_l30`,`branch_l31`] mp_tac l3_asl_AddWithCarry >>
    simp[flag_rel_def] >> strip_tac >>
    qmatch_goalsub_abbrev_tac `(_ ## _) add_res` >>
    PairCases_on `add_res` >> gvs[] >>
    reverse IF_CASES_TAC >> gvs[] >> simp[COND_RATOR]
    >- (
      drule $ b64 alpha SP_set >> drule $ b64 alpha X_set_not_31 >>
      disch_then $ qspecl_then [`64`,`&w2n r1`,`add_res0`] assume_tac >>
      disch_then $ qspec_then `add_res0` assume_tac >> gvs[int_ge] >>
      drule_all $ b64 alpha SP_set_asl_sys_regs_ok >> strip_tac >>
      IF_CASES_TAC >> gvs[returnS] >>
      qpat_x_assum `w2n _ < _ ⇒ _` mp_tac >> impl_tac >- WORD_DECIDE_TAC >>
      strip_tac >> simp[] >>
      irule $ b64 alpha X_set_asl_sys_regs_ok >> simp[returnS] >>
      goal_assum $ drule_at $ Pos last >>
      unabbrev_all_tac >> gvs[asl_sys_regs_ok_def]
      )
    >- (
      dxrule l3_asl_SetTheFlags >>
      disch_then $ qspecl_then
        [`v2w [add_res1]`,`v2w [add_res2]`,
         `v2w [add_res3]`,`v2w [add_res4]`,`X_set 64 (&w2n r1) add_res0`] mp_tac >>
      strip_tac >> simp[] >>
      drule $ b64 alpha X_set_not_31 >>
      disch_then $ qspecl_then [`64`,`&w2n r1`,`add_res0`] mp_tac >> simp[int_ge] >>
      `asl_sys_regs_ok asl2` by (
        qpat_x_assum `_ = _ asl2` $ mp_tac o GSYM >>
        simp[bindS, seqS, returnS, failS, asl_reg_rws, X_set_def, COND_RATOR] >>
        rpt CASE_TAC >> rw[] >>
        gvs[sail2_state_monadTheory.sequential_state_component_equality,
           armv86a_typesTheory.ProcState_component_equality,
           regstate_component_equality, FUN_EQ_THM, FORALL_AND_THM] >>
        gvs[asl_sys_regs_ok_def]) >>
      Cases_on `r1 = 31w` >> gvs[]
      >- (gvs[X_set_31, returnS, write'X_def, w2v_v2w]) >>
      impl_tac >- WORD_DECIDE_TAC >>
      strip_tac >> simp[returnS] >> gvs[w2v_v2w] >>
      irule $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule
      )
    )
QED

Theorem l3_models_asl_LogicalImmediate_T:
  ∀b i r2 r1.
    IS_SOME (EncodeBitMask i)
  ⇒ l3_models_asl_instr
      (Data (LogicalImmediate@64 (b, LogicalOp_AND, T, i, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  Cases_on `EncodeBitMask i` >> gvs[] >> rename1 `EncodeBitMask _ = SOME enc` >>
  PairCases_on `enc` >> simp[encode_rws] >>
  qmatch_goalsub_abbrev_tac `Decode opc` >>
  `Decode opc = Data (LogicalImmediate@64 (1w, LogicalOp_AND, T, i, r2, r1))` by (
    unabbrev_all_tac >>
    simp[Decode_def, boolify32_def] >> blastLib.BBLAST_TAC >>
    drule Decode_T_EncodeBitMask >> strip_tac >>
    map_every qcollapse_tac [`enc0`,`enc1`,`enc2`,`r1`,`r2`] >>
    simp[DecodeLogicalOp_def]) >>
  unabbrev_all_tac >> simp[] >> rw[] >>
  l3_run_tac >>
  qmatch_goalsub_abbrev_tac `seqS (wr s) ex` >>
  `∃s'. (do wr s; ex od asl) = (do wr s';
    execute_aarch64_instrs_integer_logical_immediate
      (&w2n r1) 64 i (&w2n r2) LogicalOp_AND T od asl)` by (
    unabbrev_all_tac >> asl_cexecute_tac >> simp[] >> pop_assum kall_tac >>
    simp[decode_ands_log_imm_aarch64_instrs_integer_logical_immediate_def] >>
    simp[sail2_state_monadTheory.undefined_boolS_def,
         armv86aTheory.undefined_LogicalOp_def] >>
    imp_res_tac Decode_T_EncodeBitMask >>
    imp_res_tac l3_asl_DecodeBitMasks >> simp[] >>
    simp[asl_reg_rws, seqS, Once returnS] >> irule_at Any EQ_REFL) >>
  simp[] >> pop_assum kall_tac >> unabbrev_all_tac >>
  simp[asl_reg_rws, seqS, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel l3 asl` kall_tac >>
  simp[execute_aarch64_instrs_integer_logical_immediate_def] >>
  drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >> impl_tac
  >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >> simp[asl_word_rws] >>
  DEP_REWRITE_TAC[HD_MAP] >> simp[sail2_valuesTheory.just_list_def, w2v_not_NIL] >>
  qmatch_goalsub_abbrev_tac `(_ >< _) flag` >>
  qmatch_goalsub_abbrev_tac `X_set _ a b` >>
  dxrule l3_asl_SetTheFlags >>
  disch_then $ qspecl_then
    [`(3 >< 3) flag`,`(2 >< 2) flag`,
     `(1 >< 1) flag`,`(0 >< 0) flag`,`X_set 64 a b`] mp_tac >>
  strip_tac >> simp[Abbr `a`, Abbr `b`] >>
  `asl_sys_regs_ok asl2` by (
    qpat_x_assum `_ = _ asl2` $ mp_tac o GSYM >>
    simp[bindS, seqS, returnS, failS, asl_reg_rws, X_set_def, COND_RATOR] >>
    rpt CASE_TAC >> rw[] >>
    gvs[sail2_state_monadTheory.sequential_state_component_equality,
       armv86a_typesTheory.ProcState_component_equality,
       regstate_component_equality, FUN_EQ_THM, FORALL_AND_THM] >>
    gvs[asl_sys_regs_ok_def]) >>
  Cases_on `r1 = 31w` >> gvs[X_set_31]
  >- (
    unabbrev_all_tac >> simp[returnS] >> gvs[SetTheFlags_def] >>
    ntac 2 $ pop_assum mp_tac >> rpt $ pop_assum kall_tac >> rpt strip_tac >>
    state_rel_tac[] >> gvs[X_def] >> rpt $ pop_assum kall_tac >>
    rename1 `v2w [HD (w2v foo)] @@ _` >> Cases_on `HD (w2v foo)` >> simp[] >>
    pop_assum mp_tac >>
    rewrite_tac[GSYM EL] >> DEP_REWRITE_TAC[el_w2v] >> simp[word_msb_def]
    ) >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`i && X r2 l3`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >> simp[returnS] >>
  gvs[SetTheFlags_def, write'X_def, X_def, Abbr `flag`] >> reverse $ rw[]
  >- (irule $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule) >>
  state_rel_tac[] >> rpt $ pop_assum kall_tac >>
  rename1 `v2w [HD (w2v foo)] @@ _` >> Cases_on `HD (w2v foo)` >> simp[] >>
  pop_assum mp_tac >>
  rewrite_tac[GSYM EL] >> DEP_REWRITE_TAC[el_w2v] >> simp[word_msb_def]
QED

Definition l3_to_asl_LogicalOp_def:
  l3_to_asl_LogicalOp (arm8$LogicalOp_AND) = armv86a_types$LogicalOp_AND ∧
  l3_to_asl_LogicalOp (LogicalOp_ORR) = LogicalOp_ORR ∧
  l3_to_asl_LogicalOp (LogicalOp_EOR) = LogicalOp_EOR
End

Theorem l3_models_asl_LogicalImmediate_F:
  ∀b op i r2 r1.
    IS_SOME (EncodeBitMask i)
  ⇒ l3_models_asl_instr (Data (LogicalImmediate@64 (b, op, F, i, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  Cases_on `EncodeBitMask i` >> gvs[] >> rename1 `EncodeBitMask _ = SOME enc` >>
  PairCases_on `enc` >> simp[] >>
  `∃lop. EncodeLogicalOp (op, F) = SOME lop` by (
    Cases_on `op` >> gvs[encode_rws]) >>
  simp[encode_rws] >>
  qmatch_goalsub_abbrev_tac `Decode opc` >>
  `Decode opc = Data (LogicalImmediate@64 (1w, op, F, i, r2, r1))` by (
    unabbrev_all_tac >>
    simp[Decode_def, boolify32_def] >> blastLib.BBLAST_TAC >>
    drule Decode_T_EncodeBitMask >> strip_tac >>
    map_every qcollapse_tac [`enc0`,`enc1`,`enc2`,`r1`,`r2`,`lop`] >> simp[] >>
    Cases_on `op` >> gvs[encode_rws, DecodeLogicalOp_def]) >>
  unabbrev_all_tac >> simp[] >> rw[] >>
  l3_run_tac >> pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `seqS (wr s) ex` >>
  `∃s'. (do wr s; ex od asl) = (do wr s';
    execute_aarch64_instrs_integer_logical_immediate
      (&w2n r1) 64 i (&w2n r2) (l3_to_asl_LogicalOp op) F od asl)` by (
    unabbrev_all_tac >>
    Cases_on `op` >> gvs[EncodeLogicalOp_def, LogicalOp_of_num_def] >>
    asl_cexecute_tac >> simp[] >> pop_assum kall_tac >>
    simp[
      decode_and_log_imm_aarch64_instrs_integer_logical_immediate_def,
      decode_orr_log_imm_aarch64_instrs_integer_logical_immediate_def,
      decode_eor_log_imm_aarch64_instrs_integer_logical_immediate_def
      ] >>
    simp[sail2_state_monadTheory.undefined_boolS_def,
         armv86aTheory.undefined_LogicalOp_def] >>
    imp_res_tac Decode_T_EncodeBitMask >>
    imp_res_tac l3_asl_DecodeBitMasks >> simp[] >>
    simp[asl_reg_rws, seqS, Once returnS, l3_to_asl_LogicalOp_def] >>
    irule_at Any EQ_REFL) >>
  simp[] >> pop_assum kall_tac >> unabbrev_all_tac >>
  simp[asl_reg_rws, seqS, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel l3 asl` kall_tac >>
  simp[execute_aarch64_instrs_integer_logical_immediate_def] >>
  simp[dfn'LogicalImmediate_def] >>
  `(w2n r1 = 31 ⇔ r1 = 0b11111w) ∧ (w2n r2 = 31 ⇔ r2 = 0b11111w)` by WORD_DECIDE_TAC >>
  drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >> impl_tac
  >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `SP_set _ aslw` >>
  qmatch_goalsub_abbrev_tac `write'SP l3w` >>
  `aslw = l3w` by (
    unabbrev_all_tac >> Cases_on `op` >> simp[l3_to_asl_LogicalOp_def]) >>
  simp[] >> ntac 3 $ pop_assum kall_tac >>
  IF_CASES_TAC >> simp[]
  >- (
    drule $ b64 alpha SP_set >>
    disch_then $ qspec_then `l3w` assume_tac >> gvs[returnS] >>
    irule $ b64 alpha SP_set_asl_sys_regs_ok >> simp[returnS] >>
    rpt $ goal_assum drule
    )
  >- (
    drule $ b64 alpha X_set_not_31 >>
    disch_then $ qspecl_then [`64`,`&w2n r1`,`l3w`] mp_tac >> simp[] >>
    impl_tac >- ( simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> simp[returnS] >>
    irule $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule
    )
QED

Theorem l3_models_asl_LogicalImmediate:
  ∀bb op b i r2 r1.
    IS_SOME (EncodeBitMask i) ∧
    IS_SOME (EncodeLogicalOp (op, b))
  ⇒ l3_models_asl_instr (Data (LogicalImmediate@64 (bb, op, b, i, r2, r1)))
Proof
  gen_tac >> Cases >> Cases >> gvs[EncodeLogicalOp_def] >>
  simp[l3_models_asl_LogicalImmediate_T, l3_models_asl_LogicalImmediate_F]
QED

Definition l3_to_asl_ShiftType_def:
  l3_to_asl_ShiftType (arm8$ShiftType_LSL) = armv86a_types$ShiftType_LSL ∧
  l3_to_asl_ShiftType (ShiftType_LSR) = ShiftType_LSR ∧
  l3_to_asl_ShiftType (ShiftType_ASR) = ShiftType_ASR ∧
  l3_to_asl_ShiftType (ShiftType_ROR) = ShiftType_ROR
End

Theorem l3_asl_ShiftReg:
  ∀l3 asl. state_rel l3 asl ⇒
    ∀r asl_shift_type amount l3_shift_type.
      0 ≤ r ∧ r ≤ 31 ∧
      l3_to_asl_ShiftType l3_shift_type = asl_shift_type ∧
      l3_shift_type ≠ ShiftType_ROR
    ⇒ armv86a$ShiftReg 64 r asl_shift_type amount asl : word64 res =
      returnS (arm8$ShiftReg (n2w (Num r), l3_shift_type, nat_of_int amount) l3) asl
Proof
  rw[armv86aTheory.ShiftReg_def, ShiftReg_def, ShiftValue_def] >>
  drule X_read >> disch_then $ drule_at Any >> simp[int_ge] >> strip_tac >>
  drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >> simp[] >>
  disch_then kall_tac >> simp[returnS] >>
  `¬ (r < 0)` by ARITH_TAC >> gvs[] >>
  Cases_on `l3_shift_type` >> gvs[l3_to_asl_ShiftType_def]
QED

Theorem l3_asl_ShiftReg_ROR:
  ∀l3 asl. state_rel l3 asl ⇒
    ∀r amount. 0 ≤ r ∧ r ≤ 31
    ⇒ armv86a$ShiftReg 64 r ShiftType_ROR amount asl : word64 res =
      returnS (arm8$ShiftReg (n2w (Num r), ShiftType_ROR, Num (amount % 64)) l3) asl
Proof
  rw[armv86aTheory.ShiftReg_def, ShiftReg_def, ShiftValue_def] >>
  drule X_read >> disch_then $ drule_at Any >> simp[int_ge] >> strip_tac >>
  drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >> simp[]
QED

Theorem l3_models_asl_AddSubShiftedRegister:
  ∀b shift_type b1 b2 r3 w r2 r1.
    l3_models_asl_instr
      (Data (AddSubShiftedRegister@64 (b, b1, b2, shift_type, r3, w, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >> simp[encode_rws] >>
  qmatch_goalsub_abbrev_tac `Decode opc` >>
  `shift_type = ShiftType_ROR ⇒ Decode opc = Reserved` by (
    unabbrev_all_tac >> rw[] >>
    Cases_on `b1` >> Cases_on `b2` >> l3_decode_tac) >>
  `shift_type ≠ ShiftType_ROR ⇒
    Decode opc =
    Data (AddSubShiftedRegister@64 (1w, b1, b2, shift_type, r3, w, r2, r1))` by (
      unabbrev_all_tac >> rw[] >>
      Cases_on `b1` >> Cases_on `b2` >> Cases_on `shift_type` >> simp[] >>
      l3_decode_tac >> gvs[DecodeShift_def]) >>
  Cases_on `shift_type = ShiftType_ROR` >> rw[] >> gvs[]
  (* TODO why is l3_run_tac not working here? *)
  >- (
    gvs[Run_def, dfn'Reserved_def, raise'exception_def] >>
    IF_CASES_TAC >> gvs[]
    ) >>
  unabbrev_all_tac >> rw[Run_def] >>
  qmatch_goalsub_abbrev_tac `seqS (wr s) ex` >>
  `∃s'. (do wr s; ex od asl) = (do wr s';
    execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
      (&w2n r1) (:64) (&w2n r3) (&w2n r2)
      b2 (&w2n w) (l3_to_asl_ShiftType shift_type) b1 od asl)` by (
    unabbrev_all_tac >>
    Cases_on `shift_type` >> gvs[l3_to_asl_ShiftType_def] >>
    Cases_on `b1` >> Cases_on `b2` >>
    asl_cexecute_tac >> simp[] >> pop_assum kall_tac >>
    simp[
      decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_def,
      decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_def,
      decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_def,
      decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_def
      ] >>
    simp[armv86aTheory.DecodeShift_def] >>
    simp[asl_reg_rws, seqS, Once returnS] >>
    irule_at Any EQ_REFL) >>
  simp[] >> pop_assum kall_tac >> unabbrev_all_tac >>
  simp[asl_reg_rws, seqS, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel l3 asl` kall_tac >>
  simp[execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg_def] >>
  simp[dfn'AddSubShiftedRegister_def] >>
  drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >> impl_tac
  >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule l3_asl_ShiftReg >>
  disch_then $ qspecl_then
    [`&w2n r3`,`l3_to_asl_ShiftType shift_type`,`&w2n w`,`shift_type`] mp_tac >>
  simp[] >> impl_tac >- WORD_DECIDE_TAC >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qpat_abbrev_tac `asl_cond = if b1 then _ else _` >>
  qpat_abbrev_tac `l3_cond = if b1 then _ else _` >>
  `asl_cond = (λ(a,b). (v2w [b], a)) l3_cond` by (
    unabbrev_all_tac >> IF_CASES_TAC >> simp[]) >>
  simp[] >> pop_assum kall_tac >> simp[Abbr `asl_cond`] >>
  PairCases_on `l3_cond` >> gvs[] >>
  qspecl_then [`X r2 l3`,`l3_cond0`,`l3_cond1`] mp_tac l3_asl_AddWithCarry >>
  simp[flag_rel_def] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `(_ ## _) add_res` >>
  PairCases_on `add_res` >> gvs[] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    Cases_on `r1 = 31w` >> gvs[X_set_31]
    >- (simp[returnS, write'X_def]) >>
    drule $ b64 alpha X_set_not_31 >>
    disch_then $ qspecl_then [`64`,`&w2n r1`,`add_res0`] mp_tac >> simp[] >>
    impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> simp[returnS] >>
    irule $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule
    ) >>
  dxrule l3_asl_SetTheFlags >>
  disch_then $ qspecl_then
    [`v2w [add_res1]`,`v2w [add_res2]`,
      `v2w [add_res3]`,`v2w [add_res4]`,`X_set 64 (&w2n r1) add_res0`] mp_tac >>
  strip_tac >> simp[] >> gvs[SetTheFlags_def, w2v_v2w] >>
  `asl_sys_regs_ok asl2` by (
    qpat_x_assum `_ = _ asl2` $ mp_tac o GSYM >>
    simp[bindS, seqS, returnS, failS, asl_reg_rws, X_set_def, COND_RATOR] >>
    rpt CASE_TAC >> rw[] >>
    gvs[sail2_state_monadTheory.sequential_state_component_equality,
       armv86a_typesTheory.ProcState_component_equality,
       regstate_component_equality, FUN_EQ_THM, FORALL_AND_THM] >>
    gvs[asl_sys_regs_ok_def]) >>
  Cases_on `r1 = 31w` >> gvs[X_set_31]
  >- (simp[returnS, write'X_def]) >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`add_res0`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> simp[returnS] >>
  irule $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule
QED

Theorem l3_models_asl_LogicalShiftedRegister_T:
  ∀b b1 shift_type i r3 r2 r1. i < 64 ⇒
  l3_models_asl_instr
      (Data (LogicalShiftedRegister@64
        (b, LogicalOp_AND, b1, T, shift_type, i, r3, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >> simp[encode_rws] >>
  qmatch_goalsub_abbrev_tac `Decode opc` >>
  `Decode opc = Data (LogicalShiftedRegister@64
    (1w, LogicalOp_AND, b1, T, shift_type, i, r3, r2, r1))` by (
    unabbrev_all_tac >> l3_decode_tac >>
    qcollapse_tac `n2w i : 6 word` >> simp[] >>
    Cases_on `shift_type` >> gvs[DecodeShift_def]) >>
  unabbrev_all_tac >> simp[] >> rw[] >>
  l3_run_tac >>
  gvs[GSYM $ b64 ``:'N`` X_def |> SIMP_RULE (srw_ss()) [FUN_EQ_THM]] >>
  gvs[GSYM $ ShiftReg_def |> SIMP_RULE std_ss [FUN_EQ_THM]] >>
  gvs[PULL_FORALL] >> ntac 2 $ first_x_assum $ qspec_then `l3` assume_tac >>
  qmatch_asmsub_abbrev_tac `word_msb shift_res` >>
  qmatch_goalsub_abbrev_tac `seqS (wr s) ex` >>
  `∃s'. (do wr s; ex od asl) = (do wr s';
    execute_aarch64_instrs_integer_logical_shiftedreg
      (&w2n r1) (:64) b1 (&w2n r3) (&w2n r2) LogicalOp_AND T (&i)
      (l3_to_asl_ShiftType shift_type) od asl)` by (
    unabbrev_all_tac >> Cases_on `b1` >> asl_cexecute_tac >> gvs[] >>
    map_every qcollapse_tac
      [`n2w i : 6 word`,`n2w (ShiftType2num shift_type) : 2 word`] >>
    simp[
      decode_bics_aarch64_instrs_integer_logical_shiftedreg_def,
      decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg_def
      ] >>
    simp[sail2_state_monadTheory.undefined_boolS_def,
         armv86aTheory.undefined_LogicalOp_def] >>
    Cases_on `shift_type` >> gvs[armv86aTheory.DecodeShift_def] >>
    simp[asl_reg_rws, returnS, seqS, l3_to_asl_ShiftType_def] >>
    irule_at Any EQ_REFL) >>
  simp[] >> pop_assum kall_tac >> simp[Abbr `wr`, Abbr `s`, Abbr `ex`] >>
  simp[asl_reg_rws, seqS, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel l3 asl` kall_tac >>
  simp[execute_aarch64_instrs_integer_logical_shiftedreg_def] >>
  drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >> impl_tac
  >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >> simp[asl_word_rws] >>
  `ShiftReg 64 (&w2n r3) (l3_to_asl_ShiftType shift_type) (&i) asl1 =
    returnS (ShiftReg (r3,shift_type,i) l3) asl1 : word64 res` by (
      Cases_on `shift_type = ShiftType_ROR` >> gvs[l3_to_asl_ShiftType_def] >> (
      gvs[ShiftReg_def, ShiftValue_def, armv86aTheory.ShiftReg_def] >>
      drule X_read >> disch_then $ qspec_then `&w2n r3` mp_tac >> impl_tac
      >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
      drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >> simp[returnS] >>
      disch_then kall_tac >>
      Cases_on `shift_type` >> gvs[l3_to_asl_ShiftType_def])) >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[HD_MAP] >> simp[sail2_valuesTheory.just_list_def, w2v_not_NIL] >>
  qmatch_goalsub_abbrev_tac `(_ >< _) flag` >>
  `flag = v2w [word_msb shift_res; (shift_res = 0w); F; F]` by (
    gvs[Abbr `flag`] >> blastLib.BBLAST_TAC >> simp[] >>
    rewrite_tac[GSYM EL] >> DEP_REWRITE_TAC[el_w2v] >> simp[word_msb_def]) >>
  simp[] >>
  dxrule l3_asl_SetTheFlags >>
  disch_then $ qspecl_then
    [`(3 >< 3) flag`,`(2 >< 2) flag`,
     `(1 >< 1) flag`,`(0 >< 0) flag`,`X_set 64 (&w2n r1) shift_res`] mp_tac >>
  strip_tac >> gvs[Abbr `flag`] >>
  `asl_sys_regs_ok asl2` by (
    qpat_x_assum `_ = _ asl2` $ mp_tac o GSYM >>
    simp[bindS, seqS, returnS, failS, asl_reg_rws, X_set_def, COND_RATOR] >>
    rpt CASE_TAC >> rw[] >>
    gvs[sail2_state_monadTheory.sequential_state_component_equality,
       armv86a_typesTheory.ProcState_component_equality,
       regstate_component_equality, FUN_EQ_THM, FORALL_AND_THM] >>
    gvs[asl_sys_regs_ok_def]) >>
  Cases_on `r1 = 31w` >> gvs[X_set_31]
  >- (simp[returnS] >> gvs[SetTheFlags_def, w2v_v2w]) >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`shift_res`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >> simp[returnS] >>
  gvs[SetTheFlags_def, write'X_def, X_def, w2v_v2w] >>
  irule $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule
QED

Theorem l3_models_asl_LogicalShiftedRegister_F:
  ∀b lop b1 shift_type i r3 r2 r1. i < 64 ⇒
  l3_models_asl_instr
      (Data (LogicalShiftedRegister@64
        (b, lop, b1, F, shift_type, i, r3, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  `∃wlop. EncodeLogicalOp (lop, F) = SOME wlop` by (
    Cases_on `lop` >> gvs[encode_rws]) >>
  simp[encode_rws] >>
  qmatch_goalsub_abbrev_tac `Decode opc` >>
  `Decode opc = Data (LogicalShiftedRegister@64
    (1w, lop, b1, F, shift_type, i, r3, r2, r1))` by (
    unabbrev_all_tac >> l3_decode_tac >>
    qcollapse_tac `n2w i : 6 word` >> simp[] >>
    Cases_on `lop` >> gvs[EncodeLogicalOp_def] >>
    Cases_on `shift_type` >> gvs[DecodeShift_def]) >>
  unabbrev_all_tac >> simp[] >> rw[] >>
  l3_run_tac >>
  gvs[GSYM $ b64 ``:'N`` X_def |> SIMP_RULE (srw_ss()) [FUN_EQ_THM]] >>
  gvs[GSYM $ ShiftReg_def |> SIMP_RULE std_ss [FUN_EQ_THM]] >>
  gvs[PULL_FORALL] >> ntac 2 $ first_x_assum $ qspec_then `l3` assume_tac >>
  pop_assum mp_tac >> qpat_abbrev_tac `shift_res = _ && b` >> strip_tac >>
  qmatch_goalsub_abbrev_tac `seqS (wr s) ex` >>
  `∃s'. (do wr s; ex od asl) = (do wr s';
    execute_aarch64_instrs_integer_logical_shiftedreg
      (&w2n r1) (:64) b1 (&w2n r3) (&w2n r2) (l3_to_asl_LogicalOp lop) F (&i)
      (l3_to_asl_ShiftType shift_type) od asl)` by (
    unabbrev_all_tac >>
    Cases_on `b1` >> Cases_on `lop` >> gvs[EncodeLogicalOp_def, LogicalOp_of_num_def] >>
    asl_cexecute_tac >> gvs[] >>
    map_every qcollapse_tac
      [`n2w i : 6 word`,`n2w (ShiftType2num shift_type) : 2 word`] >>
    simp[
      decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg_def,
      decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg_def,
      decode_eon_aarch64_instrs_integer_logical_shiftedreg_def,
      decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg_def,
      decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg_def,
      decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg_def
      ] >>
    simp[sail2_state_monadTheory.undefined_boolS_def,
         armv86aTheory.undefined_LogicalOp_def] >>
    Cases_on `shift_type` >> gvs[armv86aTheory.DecodeShift_def] >>
    simp[asl_reg_rws, returnS, seqS, l3_to_asl_LogicalOp_def, l3_to_asl_ShiftType_def] >>
    irule_at Any EQ_REFL
    ) >>
  simp[] >> pop_assum kall_tac >> simp[Abbr `wr`, Abbr `s`, Abbr `ex`] >>
  simp[asl_reg_rws, seqS, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel l3 asl` kall_tac >>
  simp[execute_aarch64_instrs_integer_logical_shiftedreg_def] >>
  drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >> impl_tac
  >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >> simp[asl_word_rws] >>
  `ShiftReg 64 (&w2n r3) (l3_to_asl_ShiftType shift_type) (&i) asl1 =
    returnS (ShiftReg (r3,shift_type,i) l3) asl1 : word64 res` by (
      Cases_on `shift_type = ShiftType_ROR` >> gvs[l3_to_asl_ShiftType_def] >> (
      gvs[ShiftReg_def, ShiftValue_def, armv86aTheory.ShiftReg_def] >>
      drule X_read >> disch_then $ qspec_then `&w2n r3` mp_tac >> impl_tac
      >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
      drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >> simp[returnS] >>
      disch_then kall_tac >>
      Cases_on `shift_type` >> gvs[l3_to_asl_ShiftType_def])) >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  Cases_on `r1 = 31w` >> gvs[X_set_31]
  >- (simp[returnS] >> gvs[SetTheFlags_def, w2v_v2w]) >>
  drule $ b64 alpha X_set_not_31 >>
  qmatch_goalsub_abbrev_tac `X_set _ _ shift` >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`shift`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  simp[Abbr `shift`, returnS] >>
  Cases_on `lop` >> gvs[write'X_def, l3_to_asl_LogicalOp_def] >>
  irule $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule
QED

Theorem l3_models_asl_LogicalShiftedRegister:
  ∀b lop b1 b2 shift_type i r3 r2 r1. i < 64 ⇒
    IS_SOME (EncodeLogicalOp (lop, b2))
  ⇒ l3_models_asl_instr
      (Data (LogicalShiftedRegister@64
        (b, lop, b1, b2, shift_type, i, r3, r2, r1)))
Proof
  gen_tac >> Cases >> Cases >> Cases >> gvs[EncodeLogicalOp_def] >>
  simp[l3_models_asl_LogicalShiftedRegister_T,
       l3_models_asl_LogicalShiftedRegister_F]
QED

Theorem l3_models_asl_BitfieldMove:
  ∀bb b1 b2 w t r s r2 r1.
    r < 64 ∧ s < 64 ∧ (b2 ⇒ b1) ∧
    arm8$DecodeBitMasks (1w, n2w s, n2w r, F) = SOME (w, t)
  ⇒ l3_models_asl_instr
      (Data (BitfieldMove@64 (bb, b1, b2, w, t, r, s, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >> simp[encode_rws] >>
  qmatch_goalsub_abbrev_tac `if c then e1 else e2` >>
  `∃b. (if c then e1 else e2) = SOME b` by (
    unabbrev_all_tac >> every_case_tac >> gvs[]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `Decode opc` >>
  `Decode opc = Data (BitfieldMove@64 (1w, b1, b2, w, t, r, s, r2, r1))` by (
    unabbrev_all_tac >>
    simp[Decode_def, boolify32_def] >> blastLib.BBLAST_TAC >>
    map_every qcollapse_tac [`n2w r : 6 word`,`n2w s : 6 word`,`r2`,`r1`] >>
    simp[] >> Cases_on_word_value `b` >> gvs[] >> every_case_tac >> gvs[]) >>
  unabbrev_all_tac >> simp[] >> rw[] >>
  l3_run_tac >>
  gvs[GSYM $ b64 ``:'N`` X_def |> SIMP_RULE (srw_ss()) [FUN_EQ_THM]] >>
  gvs[PULL_FORALL] >> ntac 2 $ first_x_assum $ qspec_then `l3` assume_tac >>
  qmatch_goalsub_abbrev_tac `seqS (wr s1) ex` >>
  `∃s'. (do wr s1; ex od asl) = (do wr s';
    execute_aarch64_instrs_integer_bitfield
      (&r) (&s) (&w2n r1) 64 b2 b1 (&w2n r2) t w od asl)` by (
    unabbrev_all_tac >>
    qpat_x_assum `_ = SOME b` mp_tac >> rpt IF_CASES_TAC >> rw[] >> gvs[] >>
    asl_cexecute_tac >> simp[] >>
    map_every qcollapse_tac [`n2w s : 6 word`,`n2w r : 6 word`] >>
    simp[
      decode_sbfm_aarch64_instrs_integer_bitfield_def,
      decode_ubfm_aarch64_instrs_integer_bitfield_def,
      decode_bfm_aarch64_instrs_integer_bitfield_def
      ] >>
    simp[sail2_state_monadTheory.undefined_boolS_def] >>
    drule l3_asl_DecodeBitMasks >> simp[] >> disch_then kall_tac >>
    simp[asl_reg_rws, seqS, returnS] >> irule_at Any EQ_REFL) >>
  simp[] >> pop_assum kall_tac >> unabbrev_all_tac >>
  simp[asl_reg_rws, seqS, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel l3 asl` kall_tac >>
  simp[execute_aarch64_instrs_integer_bitfield_def] >>
  qmatch_goalsub_abbrev_tac `bindS br1 _` >>
  `br1 asl1 = returnS (if b1 then 0b0w else X r1 l3) asl1` by (
    simp[Abbr `br1`] >> IF_CASES_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r1` mp_tac >> simp[] >>
    disch_then irule >> simp[int_ge] >> WORD_DECIDE_TAC) >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  simp[asl_word_rws] >>
  DEP_REWRITE_TAC[EL_MAP, el_w2v] >> simp[sail2_valuesTheory.just_list_def] >>
  `¬(63i - &s < 0) ∧ Num (63 - &s) < 64 ∧ 63 - Num (63 - &s) = s` by (
    ntac 2 $ last_x_assum mp_tac >> rpt $ pop_assum kall_tac >> ARITH_TAC) >>
  simp[w2v_v2w] >>
  Cases_on `r1 = 31w` >> gvs[] >- (simp[X_set_31, returnS]) >>
  qmatch_goalsub_abbrev_tac `X_set _ _ v` >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`v`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
  simp[returnS] >> gvs[write'X_def] >>
  irule_at Any $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule >>
  qmatch_goalsub_abbrev_tac `_⦇r1 ↦ vl⦈` >>
  qsuff_tac `v = vl` >- (rw[] >> simp[]) >>
  unabbrev_all_tac >>
  simp[X_def] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  IF_CASES_TAC >> gvs[]
  >- (
    qspec_then `s` assume_tac $ b64 alpha word_bit_0 >>
    pop_assum mp_tac >> rewrite_tac[word_bit_def] >> simp[] >> EVAL_TAC
    )
  >- (
    simp[word_bit_def] >>
    Cases_on_word `l3.REG r2 ' s` >> gvs[] >> EVAL_TAC
    )
QED

Theorem l3_models_asl_Division:
  ∀bb b r3 r2 r1.
    l3_models_asl_instr (Data (Division@64 (bb, b, r3, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >> simp[encode_rws] >>
  l3_decode_tac >> l3_run_tac >> rw[] >>
  gvs[GSYM $ b64 ``:'N`` X_def |> SIMP_RULE (srw_ss()) [FUN_EQ_THM]] >>
  qmatch_goalsub_abbrev_tac `seqS (wr s) ex` >>
  `∃s'. (do wr s; ex od asl) = (do wr s';
    execute_aarch64_instrs_integer_arithmetic_div
      (&w2n r1) (:64) (&w2n r3) (&w2n r2) b od asl)` by (
    unabbrev_all_tac >> Cases_on `b` >> gvs[] >> asl_cexecute_tac >> simp[] >>
    simp[
      decode_udiv_aarch64_instrs_integer_arithmetic_div_def,
      decode_sdiv_aarch64_instrs_integer_arithmetic_div_def
      ] >>
    simp[asl_reg_rws, seqS, returnS] >> irule_at Any EQ_REFL) >>
  simp[] >> pop_assum kall_tac >> unabbrev_all_tac >>
  simp[asl_reg_rws, seqS, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel l3 asl` kall_tac >>
  simp[execute_aarch64_instrs_integer_arithmetic_div_def] >>
  drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read >> disch_then $ qspec_then `&w2n r3` mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  simp[preludeTheory.undefined_int_def] >>
  Cases_on `r1 = 31w` >> gvs[] >- (simp[X_set_31, returnS]) >>
  qmatch_goalsub_abbrev_tac `X_set _ _ v` >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`v`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
  simp[returnS] >> gvs[write'X_def] >>
  irule_at Any $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule >>
  qmatch_goalsub_abbrev_tac `_⦇r1 ↦ vl⦈` >>
  qsuff_tac `v = vl` >- (rw[] >> simp[]) >>
  unabbrev_all_tac >>
  map_every qabbrev_tac [`x3 = X r3 l3 : 64 word`,`x2 = X r2 l3 : 64 word`] >>
  IF_CASES_TAC >> gvs[] >- EVAL_TAC >>
  simp[
    armv86aTheory.asl_Int_def,
    armv86aTheory.RoundTowardsZero_def
    ] >>
  ntac 11 $ last_x_assum kall_tac >>
  Cases_on `b` >> gvs[]
  >- (
    `¬ (&w2n x2 / &w2n x3 < 0 : real)` by (
      simp[realTheory.REAL_NOT_LT] >> irule realTheory.REAL_LE_DIV >> simp[]) >>
    simp[] >>
    DEP_REWRITE_TAC[intrealTheory.INT_FLOOR_EQNS] >> conj_tac >- WORD_DECIDE_TAC >>
    simp[integer_subrange_def, asl_word_rws, TAKE_LENGTH_ID_rwt] >>
    assume_tac $ b64 alpha v2w_fixwidth >> gvs[] >> simp[word_div_def]
    ) >>
  gvs[w2i_alt_def] >>
  ntac 2 $ once_rewrite_tac[COND_RAND] >> simp[] >>
  once_rewrite_tac[word_quot_alt_def] >>
  rewrite_tac[LET_DEF] >> BETA_TAC >>
  qabbrev_tac `n2 = w2n $ word_abs x2` >>
  qabbrev_tac `n3 = w2n $ word_abs x3` >>
  `n3 ≠ 0` by (
    unabbrev_all_tac >> rw[w2n_11] >>
    rewrite_tac[word_abs_def] >> IF_CASES_TAC >> simp[]) >>
  qabbrev_tac `posve = n2w (n2 DIV n3) : word64` >>
  qabbrev_tac `negve = -posve` >> gvs[] >>
  `-&n2 / -&n3 = &n2 / &n3 : real` by (
    qspecl_then [`-1`,`-&n3`] mp_tac REAL_DIV_MUL2 >> gvs[] >>
    disch_then $ qspec_then `-&n2` mp_tac >> simp[REAL_NEG_MUL2]) >>
  Cases_on `word_msb x2` >> Cases_on `word_msb x3` >> gvs[]
  >- (
    simp[lt_ratl, INT_FLOOR_EQNS] >>
    simp[Abbr `posve`] >>
    simp[integer_subrange_def, asl_word_rws] >>
    DEP_REWRITE_TAC[TAKE_LENGTH_ID_rwt] >> simp[] >>
    qspec_then `n2v (n2 DIV n3)` assume_tac $ b64 alpha v2w_fixwidth >> gvs[]
    )
  >- (
    simp[lt_ratl] >> gvs[INT_CEILING_NEG_DIV, INT_FLOOR_EQNS] >>
    reverse IF_CASES_TAC >> gvs[]
    >- (gvs[ZERO_DIV] >> simp[integer_subrange_def, asl_word_rws]) >>
    simp[Abbr `posve`, Abbr `negve`, Abbr `n2`, Abbr `n3`] >>
    once_rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-(x : word64)``]
    \\ Cases_on ‘word_abs x2’
    \\ Cases_on ‘word_abs x3’
    \\ asm_simp_tac std_ss [LET_THM,w2n_n2w]
    \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM bitstringTheory.v2n_n2v]))
    \\ qabbrev_tac ‘xs = n2v (n DIV n')’
    \\ rewrite_tac [neg_v2n_lemma]
    \\ fs [integer_subrange_neg]
    \\ ‘n DIV n' < 18446744073709551616’ by fs [DIV_LT_X]
    \\ fs [] \\ fs [DIV_EQ_X]
    \\ IF_CASES_TAC
    \\ TRY (
        ‘n DIV n' = 0’ by fs [DIV_EQ_X] \\ fs [GSYM neg_v2n_lemma,Abbr‘xs’] \\ NO_TAC)
    \\ fs [field_def, shiftr_def]
    \\ fs[b64 alpha v2w_fixwidth |> SIMP_RULE (srw_ss()) []]
    \\ rw [] \\ unabbrev_all_tac
    \\ gvs [v2n_fixwidth,DIV_EQ_X]
    \\ EVAL_TAC
    )
  >- (
    simp[neg_rat, lt_ratl, INT_CEILING_NEG_DIV, INT_FLOOR_EQNS] >>
    reverse IF_CASES_TAC >> gvs[]
    >- (gvs[ZERO_DIV] >> simp[integer_subrange_def, asl_word_rws]) >>
    simp[Abbr `posve`, Abbr `negve`, Abbr `n2`, Abbr `n3`] >>
    once_rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-(x : word64)``]
    \\ Cases_on ‘word_abs x2’
    \\ Cases_on ‘word_abs x3’
    \\ asm_simp_tac std_ss [LET_THM,w2n_n2w]
    \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM bitstringTheory.v2n_n2v]))
    \\ qabbrev_tac ‘xs = n2v (n DIV n')’
    \\ rewrite_tac [neg_v2n_lemma]
    \\ fs [integer_subrange_neg]
    \\ ‘n DIV n' < 18446744073709551616’ by fs [DIV_LT_X]
    \\ fs [] \\ fs [DIV_EQ_X]
    \\ IF_CASES_TAC
    \\ TRY (
        ‘n DIV n' = 0’ by fs [DIV_EQ_X] \\ fs [GSYM neg_v2n_lemma,Abbr‘xs’] \\ NO_TAC)
    \\ fs [field_def, shiftr_def]
    \\ fs[b64 alpha v2w_fixwidth |> SIMP_RULE (srw_ss()) []]
    \\ rw [] \\ unabbrev_all_tac
    \\ gvs [v2n_fixwidth,DIV_EQ_X]
    \\ EVAL_TAC
    )
  >- (
    simp[lt_ratl, INT_FLOOR_EQNS] >>
    simp[Abbr `posve`] >>
    simp[integer_subrange_def, asl_word_rws] >>
    DEP_REWRITE_TAC[TAKE_LENGTH_ID_rwt] >> simp[] >>
    qspec_then `n2v (n2 DIV n3)` assume_tac $ b64 alpha v2w_fixwidth >> gvs[]
    )
QED

Theorem l3_models_asl_MultiplyHigh:
  ∀b r3 r2 r1.
    l3_models_asl_instr (Data (MultiplyHigh (b, r3, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >> simp[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >>
  gvs[GSYM $ b64 ``:'N`` X_def |> SIMP_RULE (srw_ss()) [FUN_EQ_THM]] >>
  qmatch_goalsub_abbrev_tac `seqS (wr s) ex` >>
  `∃s'. (do wr s; ex od asl) = (do wr s';
    execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi
      (&w2n r1) 64 (&w2n r3) (&w2n r2) ¬b od) asl` by (
    unabbrev_all_tac >> Cases_on `b` >> gvs[] >> asl_cexecute_tac >> simp[] >>
    simp[sail2_valuesTheory.just_list_def] >>
    simp[
      decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi_def,
      decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi_def
      ] >>
    simp[asl_reg_rws, seqS, returnS] >> irule_at Any EQ_REFL) >>
  simp[Abbr `wr`, Abbr `s`, asl_reg_rws, seqS, returnS] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel l3 asl` kall_tac >>
  simp[execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi_def] >>
  drule X_read >> disch_then $ qspec_then `(&w2n r2)` mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule $ returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read >> disch_then $ qspec_then `(&w2n r3)` mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule $ returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  Cases_on `r1 = 31w` >> gvs[] >- (simp[X_set_31, returnS]) >>
  qmatch_goalsub_abbrev_tac `X_set _ _ res` >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`res`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >>
  strip_tac >> simp[returnS] >>
  irule_at Any $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule >>
  qmatch_goalsub_abbrev_tac `_⦇ r1 ↦ l3_res ⦈` >>
  qsuff_tac `res = l3_res` >> rw[] >> gvs[write'X_def] >>
  unabbrev_all_tac >>
  map_every qabbrev_tac [`x2 = X r2 l3 : 64 word`,`x3 = X r3 l3 : 64 word`] >>
  rpt $ pop_assum kall_tac >>
  simp[asl_Int_def, ExtendWord_def] >> IF_CASES_TAC >> gvs[]
  >- (
    DEP_REWRITE_TAC[integer_subrange_pos] >> simp[] >>
    `w2w x2 : word128 * w2w x3 = n2w (w2n x2 * w2n x3)` by rw[word_mul_def, w2n_w2w] >>
    pop_assum SUBST_ALL_TAC >> qmatch_goalsub_abbrev_tac `n2w n` >>
    DEP_REWRITE_TAC[GSYM extract_v2w |>
      INST_TYPE [alpha |-> ``:128``, beta |-> ``:64``]] >> simp[] >>
    DEP_REWRITE_TAC[v2w_fixwidth_dimindex] >> simp[]
    ) >>
  rename [‘integer_subrange (w2i x2 * w2i x3) 127 64 = (127 >< 64) (sw2sw x2 * sw2sw x3)’]
  \\ Cases_on `x2` using integer_wordTheory.ranged_int_word_nchotomy
  \\ Cases_on `x3` using integer_wordTheory.ranged_int_word_nchotomy
  \\ fs [integer_wordTheory.sw2sw_i2w,integer_wordTheory.word_i2w_mul,
         integer_wordTheory.w2i_i2w]
  \\ reverse (Cases_on ‘i’) \\ fs []
  THEN1 EVAL_TAC
  \\ (reverse (Cases_on ‘i'’) THEN1 EVAL_TAC) \\ fs []
  \\ ‘n * n' ≤ 9223372036854775808 * 9223372036854775808’ by
       (irule LESS_MONO_MULT2 \\ fs [])
  \\ gvs [INT_MUL_REDUCE |> REWRITE_RULE[NUMERAL_DEF]]
  \\ rewrite_tac [integer_wordTheory.i2w_def]
  \\ IF_CASES_TAC \\ TRY (gvs [] \\ NO_TAC)
  \\ rewrite_tac [INT_NEGNEG,NUM_OF_INT]
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM bitstringTheory.v2n_n2v]))
  \\ qabbrev_tac ‘xs = n2v (n * n')’
  \\ rewrite_tac [neg_v2n_lemma,bitstringTheory.v2n_n2v]
  \\ TRY (
      gvs [integer_subrange_pos,v2w_TAKE_64_fixwidth_128,field_def,shiftr_def]
      \\ NO_TAC)
  \\ fs [integer_subrange_neg]
  \\ qid_spec_tac ‘xs’
  \\ ho_match_mp_tac $ Q.SPEC `128` forall_fixwidth
  \\ strip_tac
  \\ rename [‘v2n ys’]
  \\ Cases_on ‘v2n ys = 0’ \\ fs []
  \\ TRY (pop_assum mp_tac \\ rename [‘v2n ys = 0 ⇒ _’] \\ strip_tac
          \\ strip_tac \\ gvs [LENGTH_eq_128,v2n_0] \\ EVAL_TAC \\ NO_TAC)
  \\ simp_tac std_ss [fcpTheory.CART_EQ]
  \\ once_rewrite_tac [bitstringTheory.word_index_v2w]
  \\ fs [word_extract_def,w2w,word_bits_def,fcpTheory.FCP_BETA]
  \\ once_rewrite_tac [bitstringTheory.word_index_v2w] \\ fs []
  \\ qsuff_tac `∀xs i. i < 64 ⇒ (testbit i (field 127 64 xs) ⇔ testbit (i + 64) xs)`
  \\ rw[] \\ gvs[]
  \\ fs [field_def,shiftr_def]
  \\ fs [testbit,bitstringTheory.el_fixwidth] \\ rw []
  \\ fs [EL_TAKE]
  \\ Cases_on ‘i + 64 < LENGTH xs'’ \\ gvs [] \\ fs [EL_TAKE]
QED

Theorem l3_models_asl_MultiplyAddSub:
  ∀bb b r4 r3 r2 r1.
    l3_models_asl_instr (Data (MultiplyAddSub@64 (bb, b, r4, r3, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >> simp[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >>
  gvs[GSYM $ b64 ``:'N`` X_def |> SIMP_RULE (srw_ss()) [FUN_EQ_THM]] >>
  qmatch_goalsub_abbrev_tac `seqS (wr s) ex` >>
  `∃s'. (do wr s; ex od asl) = (do wr s';
    execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub
      (&w2n r3) (&w2n r1) (:64) (:64) (&w2n r4) (&w2n r2) b od) asl` by (
    unabbrev_all_tac >> Cases_on `b` >> gvs[] >> asl_cexecute_tac >> simp[] >>
    simp[
      decode_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub_def,
      decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub_def
      ] >>
    simp[asl_reg_rws, seqS, returnS] >> irule_at Any EQ_REFL) >>
  simp[Abbr `wr`, Abbr `s`, asl_reg_rws, seqS, returnS] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel l3 asl` kall_tac >>
  simp[execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub_def] >>
  drule X_read >> disch_then $ qspec_then `(&w2n r2)` mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule $ returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read >> disch_then $ qspec_then `(&w2n r4)` mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule $ returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read >> disch_then $ qspec_then `(&w2n r3)` mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule $ returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  simp[preludeTheory.undefined_int_def] >>
  Cases_on `r1 = 31w` >> gvs[] >- (simp[X_set_31, returnS]) >>
  qmatch_goalsub_abbrev_tac `X_set _ _ res` >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`res`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >>
  strip_tac >> simp[returnS] >>
  irule_at Any $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule >>
  qmatch_goalsub_abbrev_tac `_⦇ r1 ↦ l3_res ⦈` >>
  qsuff_tac `res = l3_res` >> rw[] >> gvs[write'X_def] >>
  unabbrev_all_tac >>
  map_every qabbrev_tac [
    `x2 = X r2 l3 : 64 word`,`x3 = X r3 l3 : 64 word`, `x4 = X r4 l3 : 64 word`] >>
  rpt $ pop_assum kall_tac >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    simp[INT_ADD_CALCULATE, integer_subrange_def, asl_word_rws] >>
    DEP_REWRITE_TAC[TAKE_LENGTH_ID_rwt] >> simp[] >>
    assume_tac $ b64 alpha v2w_fixwidth >> gvs[] >> pop_assum kall_tac >>
    simp[word_mul_def, word_add_def]
    ) >>
  simp[INT_SUB_CALCULATE, INT_ADD_CALCULATE] >> IF_CASES_TAC >> gvs[]
  >- (
    simp[integer_subrange_def, asl_word_rws] >>
    DEP_REWRITE_TAC[TAKE_LENGTH_ID_rwt] >> simp[] >>
    assume_tac $ b64 alpha v2w_fixwidth >> gvs[] >> pop_assum kall_tac >>
    simp[word_mul_def, word_sub_def, word_add_def] >> ARITH_TAC
    ) >>
  once_rewrite_tac[GSYM $ SIMP_CONV (srw_ss()) [] ``-(x : word64)``] >>
  Cases_on ‘x2’ \\ Cases_on ‘x3’ \\ Cases_on ‘x4’
  \\ rewrite_tac [word_mul_n2w,GSYM word_sub_def,word_arith_lemma2]
  \\ reverse IF_CASES_TAC THEN1 gvs []
  \\ rename [‘a < b * c:num’]
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM bitstringTheory.v2n_n2v]))
  \\ qabbrev_tac ‘xs = n2v (b * c − a)’
  \\ rewrite_tac [neg_v2n_lemma]
  \\ asm_rewrite_tac []
  \\ gvs[integer_subrange_def, asl_word_rws]
  \\ qid_spec_tac ‘xs’
  \\ ho_match_mp_tac $ Q.SPEC `64` forall_fixwidth
  \\ strip_tac
  \\ rename [‘v2n ys’]
  \\ Cases_on ‘v2n ys = 0’ \\ fs []
  \\ fs [LENGTH_add]
  \\ CASE_TAC \\ fs []
  \\ strip_tac
  \\ gvs [LENGTH_eq_64]
QED

Theorem l3_asl_ConditionHolds:
  ∀l3 asl. state_rel l3 asl ⇒
    ∀w. ConditionHolds w asl = returnS (ConditionHolds w l3) asl
Proof
  rw[arm8Theory.ConditionHolds_def, armv86aTheory.ConditionHolds_def,
     ConditionTest_def] >>
  simp[asl_word_rws, EL_MAP] >>
  simp[sail2_valuesTheory.just_list_def] >>
  Cases_on_word_value `(3 >< 1) w` >> gvs[el_w2v, word_bit_def] >>
  simp[sail2_state_monadTheory.undefined_boolS_def] >>
  qspec_then `asl` assume_tac PSTATE_read >>
  drule $ INST_TYPE [gamma |-> bool] returnS_bindS >> simp[] >> strip_tac >>
  qabbrev_tac `pst = asl.regstate.ProcState_reg "PSTATE"` >>
  `pst.ProcState_N = v2w [l3.PSTATE.N] ∧
   pst.ProcState_Z = v2w [l3.PSTATE.Z] ∧
   pst.ProcState_C = v2w [l3.PSTATE.C] ∧
   pst.ProcState_V = v2w [l3.PSTATE.V]` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[] >>
  map_every Cases_on [`l3.PSTATE.N`,`l3.PSTATE.Z`,`l3.PSTATE.C`,`l3.PSTATE.V`] >>
  gvs[returnS]
QED

Theorem l3_models_asl_ConditionalCompareImmediate:
  ∀bb b w1 w2 flgs r. w2n w1 < 32 ∧ w2 ≠ 31w ⇒
    l3_models_asl_instr
      (Data (ConditionalCompareImmediate@64 (bb, b, w1, w2, flgs, r)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >> simp[encode_rws] >>
  PairCases_on `flgs` >> simp[w2w_def] >>
  qabbrev_tac `ww1 = n2w (w2n w1) : 5 word` >>
  l3_decode_tac >> rw[] >>
  qmatch_goalsub_abbrev_tac `seqS (wr s) ex` >>
  `∃s'. (do wr s; ex od asl) = (do wr s';
    execute_aarch64_instrs_integer_conditional_compare_immediate
      w2 64 (v2w [flgs0;flgs1;flgs2;flgs3]) w1 (&w2n r) b od) asl` by (
    unabbrev_all_tac >>
    Cases_on `b` >> gvs[] >> Cases_on_word_value `w2` >> gvs[] >>
    asl_cexecute_tac >> simp[] >>
    simp[
      decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate_def,
      decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate_def
      ] >>
    qcollapse_tac `n2w (w2n w1) : 5 word` >>
    simp[asl_reg_rws, seqS, returnS] >>
    simp[w2w_n2w, n2w_BITS, WORD_BITS_EXTRACT] >>
    DEP_REWRITE_TAC[WORD_EXTRACT_ID] >> simp[] >>
    irule_at Any EQ_REFL) >>
  simp[Abbr `wr`, Abbr `s`, asl_reg_rws, seqS, returnS] >>
  ntac 2 $ pop_assum kall_tac >> qpat_x_assum `Decode _ = _` kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel l3 asl` kall_tac >>
  simp[Run_def, dfn'ConditionalCompareImmediate_def] >>
  simp[execute_aarch64_instrs_integer_conditional_compare_immediate_def] >>
  `w2w ww1 : 64 word = w1` by (unabbrev_all_tac >> gvs[w2w_def]) >> simp[] >>
  qpat_abbrev_tac `asl_cnd = if b then _ else _` >>
  qpat_abbrev_tac `cnd = if b then _ else _` >>
  `asl_cnd = (λ(w,b). (v2w [b],w)) cnd` by (
    unabbrev_all_tac >> IF_CASES_TAC >> gvs[]) >>
  simp[] >> PairCases_on `cnd` >> gvs[] >>
  drule X_read >> disch_then $ qspec_then `(&w2n r)` mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule $ returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`X r l3`,`cnd0`,`cnd1`] mp_tac l3_asl_AddWithCarry >>
  simp[flag_rel_def] >> disch_then kall_tac >>
  qpat_abbrev_tac `res = arm8$AddWithCarry _` >>
  PairCases_on `res` >> simp[] >>
  drule l3_asl_ConditionHolds >> disch_then $ qspec_then `w2` assume_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `(_ >< _) flgs` >>
  drule l3_asl_SetTheFlags_alt >>
  disch_then $ qspecl_then [
    `(3 >< 3) flgs`,`(2 >< 2) flgs`,`(1 >< 1) flgs`,`(0 >< 0) flgs`] assume_tac >>
  gvs[] >> simp[returnS] >>
  `asl_sys_regs_ok asl2` by (
    qpat_x_assum `_ = _ asl2` $ mp_tac o GSYM >>
    simp[bindS, seqS, returnS, failS, asl_reg_rws, X_set_def, COND_RATOR] >>
    rpt CASE_TAC >> rw[] >>
    gvs[sail2_state_monadTheory.sequential_state_component_equality,
       armv86a_typesTheory.ProcState_component_equality,
       regstate_component_equality, FUN_EQ_THM, FORALL_AND_THM] >>
    gvs[asl_sys_regs_ok_def]) >>
  qpat_x_assum `state_rel _ _` mp_tac >> gvs[Abbr `flgs`] >>
  rewrite_tac[GSYM EL] >> DEP_REWRITE_TAC[el_w2v] >> simp[] >>
  IF_CASES_TAC >> gvs[] >> EVAL_TAC
QED

Theorem l3_models_asl_ConditionalSelect:
  ∀bb b1 b2 w r3 r2 r1. w ≠ 31w ⇒
    l3_models_asl_instr
      (Data (ConditionalSelect@64 (bb, b1, b2, w, r3, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >> simp[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >>
  gvs[GSYM $ b64 ``:'N`` X_def |> SIMP_RULE (srw_ss()) [FUN_EQ_THM]] >>
  gvs[GSYM ConditionHolds_def |> SIMP_RULE (srw_ss()) [FUN_EQ_THM]] >>
  qmatch_goalsub_abbrev_tac `seqS (wr s) ex` >>
  `∃s'. (do wr s; ex od asl) = (do wr s';
    execute_aarch64_instrs_integer_conditional_select
      w (&w2n r1) (:64) b2 b1 (&w2n r3) (&w2n r2) od) asl` by (
    unabbrev_all_tac >>
    Cases_on `b1` >> Cases_on `b2` >> gvs[] >> Cases_on_word_value `w` >> gvs[] >>
    asl_cexecute_tac >> simp[] >>
    simp[
      decode_csneg_aarch64_instrs_integer_conditional_select_def,
      decode_csinv_aarch64_instrs_integer_conditional_select_def,
      decode_csinc_aarch64_instrs_integer_conditional_select_def,
      decode_csel_aarch64_instrs_integer_conditional_select_def
      ] >>
    simp[asl_reg_rws, seqS, returnS] >> irule_at Any EQ_REFL) >>
  simp[Abbr `wr`, Abbr `s`, asl_reg_rws, seqS, returnS] >>
  ntac 2 $ pop_assum kall_tac >> qpat_x_assum `Decode _ = _` kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel l3 asl` kall_tac >>
  simp[execute_aarch64_instrs_integer_conditional_select_def] >>
  drule X_read >> disch_then $ qspec_then `(&w2n r2)` mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule $ returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read >> disch_then $ qspec_then `(&w2n r3)` mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule $ returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule l3_asl_ConditionHolds >> disch_then $ qspec_then `w` assume_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  Cases_on `r1 = 31w` >> gvs[] >- gvs[X_set_31, returnS] >>
  simp[asl_word_rws, INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, n2w_w2n] >>
  qmatch_goalsub_abbrev_tac `X_set _ _ res` >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`res`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
  simp[returnS] >>
  irule_at Any $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule >>
  qmatch_goalsub_abbrev_tac `_⦇ r1 ↦ l3_res ⦈` >>
  qsuff_tac `res = l3_res` >> rw[] >> gvs[write'X_def] >>
  unabbrev_all_tac >> rpt (IF_CASES_TAC >> gvs[]) >> simp[word_add_def]
QED

Theorem l3_models_asl_AddSubCarry:
  ∀bb b1 b2 r3 r2 r1.
    l3_models_asl_instr
      (Data (AddSubCarry@64 (bb, b1, b2, r3, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >> simp[encode_rws] >>
  l3_decode_tac >> rw[] >>
  qmatch_goalsub_abbrev_tac `seqS (wr s) ex` >>
  `∃s'. (do wr s; ex od asl) = (do wr s';
    execute_aarch64_instrs_integer_arithmetic_add_sub_carry
      (&w2n r1) (:64) (&w2n r3) (&w2n r2) b2 b1 od) asl` by (
    unabbrev_all_tac >>
    Cases_on `b1` >> Cases_on `b2` >> gvs[] >> asl_cexecute_tac >> simp[] >>
    simp[
      decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry_def,
      decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry_def,
      decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry_def,
      decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry_def
      ] >>
    simp[asl_reg_rws, seqS, returnS] >> irule_at Any EQ_REFL) >>
  simp[Abbr `wr`, Abbr `s`, asl_reg_rws, seqS, returnS] >>
  ntac 2 $ pop_assum kall_tac >> qpat_x_assum `Decode _ = _` kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel l3 asl` kall_tac >>
  simp[Run_def, dfn'AddSubCarry_def] >>
  simp[execute_aarch64_instrs_integer_arithmetic_add_sub_carry_def] >>
  drule X_read >> disch_then $ qspec_then `(&w2n r2)` mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule $ returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read >> disch_then $ qspec_then `(&w2n r3)` mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule $ returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `AddWithCarry _ x3` >>
  qspec_then `asl1` assume_tac PSTATE_read >>
  drule returnS_bindS_unit >> simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `pst.ProcState_C` >>
  `pst.ProcState_C = v2w [l3.PSTATE.C]` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[] >>
  qspecl_then [`X r2 l3`,`x3`,`l3.PSTATE.C`] mp_tac l3_asl_AddWithCarry >>
  simp[flag_rel_def] >> disch_then kall_tac >>
  qpat_abbrev_tac `res = arm8$AddWithCarry _` >>
  PairCases_on `res` >> gvs[] >> reverse IF_CASES_TAC >> gvs[]
  >- (
    Cases_on `r1 = 31w` >> gvs[X_set_31, returnS, write'X_def] >>
    drule $ b64 alpha X_set_not_31 >>
    disch_then $ qspecl_then [`64`,`&w2n r1`,`res0`] mp_tac >> simp[] >>
    impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
    simp[returnS] >> gvs[write'X_def] >>
    irule $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule
    ) >>
  drule l3_asl_SetTheFlags >>
  disch_then $ qspecl_then [
    `v2w [res1]`,`v2w [res2]`,`v2w [res3]`,`v2w [res4]`,
    `X_set 64 (&w2n r1) res0`] assume_tac >> gvs[] >>
  gvs[w2v_v2w] >>
  `asl_sys_regs_ok asl2` by (
    qpat_x_assum `_ = _ asl2` $ mp_tac o GSYM >>
    simp[bindS, seqS, returnS, failS, asl_reg_rws, X_set_def, COND_RATOR] >>
    rpt CASE_TAC >> rw[] >>
    gvs[sail2_state_monadTheory.sequential_state_component_equality,
       armv86a_typesTheory.ProcState_component_equality,
       regstate_component_equality, FUN_EQ_THM, FORALL_AND_THM] >>
    gvs[asl_sys_regs_ok_def]) >>
  Cases_on `r1 = 31w` >> gvs[X_set_31, returnS, write'X_def] >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`res0`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
  simp[returnS] >> gvs[write'X_def] >>
  irule $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule
QED

Theorem l3_asl_AddrTop:
  ∀l3 asl.
    state_rel l3 asl ∧ asl_sys_regs_ok asl
  ⇒ ∀target.
      AddrTop target T l3.PSTATE.EL asl = returnS
        (case l3.PSTATE.EL of
        | 2w =>
          if l3.TCR_EL2.TBI ∧ ¬word_bit 29 (reg'TCR_EL2_EL3 l3.TCR_EL2) then 55 else 63
        | 3w =>
          if l3.TCR_EL3.TBI ∧ ¬word_bit 29 (reg'TCR_EL2_EL3 l3.TCR_EL3) then 55 else 63
        | _ =>
          if word_bit 55 target then
            if l3.TCR_EL1.TBI1 ∧ ¬word_bit 52 (reg'TCR_EL1 l3.TCR_EL1) then 55 else 63
          else if l3.TCR_EL1.TBI0 ∧ ¬word_bit 51 (reg'TCR_EL1 l3.TCR_EL1) then 55 else 63
        ) asl
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> simp[AddrTop_def] >>
  qspecl_then [`asl`,`l3.PSTATE.EL`] mp_tac S1TranslationRegime >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
  drule $ INST_TYPE [gamma |-> ``:int``] returnS_bindS >> simp[] >>
  disch_then kall_tac >> qmatch_goalsub_abbrev_tac `ELUsingAArch32 el` >>
  qspecl_then [`asl`,`el`] mp_tac ELUsingAArch32_F >> simp[] >> impl_tac
  >- (unabbrev_all_tac >> rw[] >> gvs[asl_sys_regs_ok_def]) >> strip_tac >>
  drule $ INST_TYPE [gamma |-> ``:int``] returnS_bindS >> simp[] >>
  disch_then kall_tac >>
  `el = 1w ∨ el = 2w ∨ el = 3w` by (
    rw[Abbr `el`] >> Cases_on_word_value `l3.PSTATE.EL` >> gvs[]) >>
  simp[asl_word_rws, EL_MAP, el_w2v]
  >- (
    ntac 4 $ simp[Once sail2_valuesTheory.just_list_def] >>
    `target ' 55 = word_bit 55 target` by WORD_DECIDE_TAC >> simp[] >>
    IF_CASES_TAC >> simp[] >>
    drule TCR_EL1_read >> strip_tac >>
    drule $ INST_TYPE [gamma |-> ``:int``] returnS_bindS >> simp[] >>
    disch_then kall_tac >>
    qpat_x_assum `ELUsingAArch32 _ _ = _` assume_tac >>
    drule $ INST_TYPE [gamma |-> ``:int``] returnS_bindS >> simp[] >>
    disch_then kall_tac >> simp[extract_bit_64] >>
    simp[returnS] >>
    `word_bit 37 (reg'TCR_EL1 l3.TCR_EL1) = l3.TCR_EL1.TBI0` by (
      simp[reg'TCR_EL1_def] >> CASE_TAC >> simp[] >> blastLib.BBLAST_TAC) >>
    `word_bit 38 (reg'TCR_EL1 l3.TCR_EL1) = l3.TCR_EL1.TBI1` by (
      simp[reg'TCR_EL1_def] >> CASE_TAC >> simp[] >> blastLib.BBLAST_TAC) >>
    simp[] >> Cases_on_word_value `l3.PSTATE.EL` >> gvs[]
    )
  >- (
    `l3.PSTATE.EL = 2w` by (
      unabbrev_all_tac >> Cases_on_word_value `l3.PSTATE.EL` >> gvs[]) >>
    rpt var_eq_tac >> gvs[] >>
    ntac 4 $ simp[Once sail2_valuesTheory.just_list_def] >>
    qspecl_then [`asl`,`l3.PSTATE.EL`] mp_tac ELIsInHost_F >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >>
    strip_tac >>
    drule $ INST_TYPE [gamma |-> ``:int``] returnS_bindS >> simp[] >>
    disch_then kall_tac >>
    drule TCR_EL2_read >> strip_tac >>
    drule $ INST_TYPE [gamma |-> ``:int``] returnS_bindS >> simp[] >>
    disch_then kall_tac >>
    qpat_x_assum `ELUsingAArch32 _ _ = _` assume_tac >>
    drule $ INST_TYPE [gamma |-> ``:int``] returnS_bindS >> simp[] >>
    disch_then kall_tac >> simp[extract_bit_64] >>
    qmatch_goalsub_abbrev_tac `word_bit _ tcr_el2` >>
    `word_bit 20 tcr_el2 = l3.TCR_EL2.TBI` by (
      unabbrev_all_tac >> simp[reg'TCR_EL2_EL3_def] >>
      CASE_TAC >> simp[] >> blastLib.BBLAST_TAC) >>
    `word_bit 29 tcr_el2 = word_bit 29 (reg'TCR_EL2_EL3 l3.TCR_EL2)` by (
      unabbrev_all_tac >> simp[reg'TCR_EL2_EL3_def] >>
      CASE_TAC >> simp[] >> blastLib.BBLAST_TAC) >>
    simp[returnS]
    )
  >- (
    `l3.PSTATE.EL = 3w` by (
      unabbrev_all_tac >> Cases_on_word_value `l3.PSTATE.EL` >> gvs[]) >>
    rpt var_eq_tac >> gvs[] >>
    drule TCR_EL3_read >> strip_tac >>
    drule $ INST_TYPE [gamma |-> ``:int``] returnS_bindS >> simp[] >>
    disch_then kall_tac >>
    qpat_x_assum `ELUsingAArch32 _ _ = _` assume_tac >>
    drule $ INST_TYPE [gamma |-> ``:int``] returnS_bindS >> simp[] >>
    disch_then kall_tac >> DEP_REWRITE_TAC[extract_bit] >> simp[] >>
    qmatch_goalsub_abbrev_tac `word_bit _ tcr_el3` >>
    `word_bit 20 tcr_el3 = l3.TCR_EL3.TBI` by (
      unabbrev_all_tac >> simp[reg'TCR_EL2_EL3_def] >>
      CASE_TAC >> simp[] >> blastLib.BBLAST_TAC) >>
    `word_bit 29 tcr_el3 = word_bit 29 (reg'TCR_EL2_EL3 l3.TCR_EL3)` by (
      unabbrev_all_tac >> simp[reg'TCR_EL2_EL3_def] >>
      CASE_TAC >> simp[] >> blastLib.BBLAST_TAC) >>
    ntac 2 $ pop_assum $ SUBST_ALL_TAC >> rpt $ pop_assum kall_tac >> simp[]
    )
QED

Theorem l3_asl_AArch64_BranchAddr:
  ∀l3 asl.
    state_rel l3 asl ∧ asl_sys_regs_ok asl
  ⇒ ∀target.
      AArch64_BranchAddr target asl = returnS
      (case l3.PSTATE.EL of
      | 2w =>
        if l3.TCR_EL2.TBI ∧ ¬word_bit 29 (reg'TCR_EL2_EL3 l3.TCR_EL2)
        then (55 >< 0) target else target
      | 3w =>
        if l3.TCR_EL3.TBI ∧ ¬word_bit 29 (reg'TCR_EL2_EL3 l3.TCR_EL3)
        then (55 >< 0) target else target
      | _ =>
        if word_bit 55 target then
          if l3.TCR_EL1.TBI1 ∧ ¬word_bit 52 (reg'TCR_EL1 l3.TCR_EL1)
          then (55 --- 0) target else target
        else if l3.TCR_EL1.TBI0 ∧ ¬word_bit 51 (reg'TCR_EL1 l3.TCR_EL1)
             then (55 >< 0) target else target
      ) asl
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  simp[AArch64_BranchAddr_def] >>
  qspec_then `asl` mp_tac UsingAArch32_F >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
  drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >> simp[] >>
  disch_then kall_tac >>
  qspec_then `asl` assume_tac PSTATE_read >>
  drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >> simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `AddrTop _ _ el` >>
  `el = l3.PSTATE.EL` by (unabbrev_all_tac >> state_rel_tac[]) >> gvs[] >>
  drule_all l3_asl_AddrTop >> disch_then $ qspec_then `target` assume_tac >>
  qmatch_asmsub_abbrev_tac `_ = returnS addrtop _` >>
  drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >> simp[] >>
  disch_then kall_tac >> qpat_x_assum `AddrTop _ _ _ _ = _` kall_tac >>
  IF_CASES_TAC >> simp[]
  >- (unabbrev_all_tac >> gvs[COND_RATOR] >> rpt (IF_CASES_TAC >> gvs[returnS])) >>
  `addrtop = 55` by (unabbrev_all_tac >> rpt (CASE_TAC >> gvs[])) >>
  simp[asl_word_rws, EL_MAP] >> ntac 2 $ simp[sail2_valuesTheory.just_list_def] >>
  simp[el_w2v] >> `target ' 55 = word_bit 55 target` by WORD_DECIDE_TAC >> simp[] >>
  simp[IsInHost_def] >>
  qspec_then `asl` mp_tac ELIsInHost_F >> impl_tac >- gvs[asl_sys_regs_ok_def] >>
  disch_then $ qspec_then `l3.PSTATE.EL` assume_tac >>
  drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >> simp[] >> strip_tac >>
  Cases_on_word_value `l3.PSTATE.EL` >> simp[] >> unabbrev_all_tac >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  simp[returnS, EVAL ``i2w 72057594037927935 : word64``] >> blastLib.BBLAST_TAC
QED

Theorem l3_models_asl_BranchImmediate_CALL:
  ∀a. a = sw2sw ((27 >< 2) a @@ (0b0w : word2)) ⇒
    l3_models_asl_instr (Branch (BranchImmediate (a, BranchType_CALL)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >> pop_assum kall_tac >>
  asl_cexecute_tac >> simp[] >> pop_assum kall_tac >>
  qcollapse_tac `(27 >< 2) a : 26 word` >>
  qcollapse_tac `(((27 >< 2) a : 26 word) @@ (0w : 2 word)) : 28 word` >>
  simp[dfn'BranchImmediate_def] >>
  simp[
    decode_bl_aarch64_instrs_branch_unconditional_immediate_def,
    execute_aarch64_instrs_branch_unconditional_immediate_def
    ] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule PC_read >> strip_tac >> drule returnS_bindS_unit >> rw[] >>
  ntac 2 $ pop_assum kall_tac >>
  drule $ b64 alpha X_set_not_31 >> simp[asl_word_rws] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos] >>
  `n2w (w2n l3.PC + 4) = l3.PC + 4w` by simp[word_add_def] >> simp[] >>
  disch_then $ qspecl_then [`64`,`30`,`l3.PC + 0b100w`] mp_tac >> rw[] >>
  simp[Once seqS, returnS] >>
  `asl_sys_regs_ok asl2` by
    gvs[X_set_def, asl_reg_rws, returnS, bindS, asl_sys_regs_ok_def] >>
  drule PC_read >> strip_tac >>
  drule returnS_bindS_unit >> rw[] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[armv86aTheory.BranchTo_def] >>
  qspec_then `asl2` mp_tac $ GEN_ALL UsingAArch32_F >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  qmatch_goalsub_abbrev_tac `AArch64_BranchAddr addr` >>
  drule l3_asl_AArch64_BranchAddr >> simp[] >>
  disch_then $ qspecl_then [`addr`] strip_assume_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  pop_assum kall_tac >> simp[returnS, bindS, seqS] >>
  ntac 10 $ last_x_assum kall_tac >>
  gvs[asl_reg_rws, returnS, BranchTaken_ref_def] >>
  gvs[BranchTo_def, write'X_def, Hint_Branch_def] >>
  reverse conj_tac >- gvs[asl_sys_regs_ok_def] >>
  Cases_on_word_value `l3.PSTATE.EL` >> simp[]
  >- (
    `¬word_bit 29 (reg'TCR_EL2_EL3 l3.TCR_EL3)` by (
      state_rel_tac[] >> gvs[asl_sys_regs_ok_def] >>
      qmatch_goalsub_abbrev_tac `_ (_ (_ tcr_el3))` >>
      qpat_x_assum `¬word_bit 29 tcr_el3` mp_tac >>
      blastLib.BBLAST_TAC >> gvs[]) >>
    simp[] >> IF_CASES_TAC >> simp[] >>
    state_rel_tac[] >> blastLib.BBLAST_TAC
    )
  >- (
    `¬word_bit 29 (reg'TCR_EL2_EL3 l3.TCR_EL2)` by (
      state_rel_tac[] >> gvs[asl_sys_regs_ok_def] >>
      qmatch_goalsub_abbrev_tac `_ (_ (_ tcr_el2))` >>
      qpat_x_assum `¬word_bit 29 tcr_el2` mp_tac >>
      blastLib.BBLAST_TAC >> gvs[]) >>
    simp[] >> IF_CASES_TAC >> simp[] >>
    state_rel_tac[] >> blastLib.BBLAST_TAC
    ) >>
  `¬word_bit 51 (reg'TCR_EL1 l3.TCR_EL1) ∧
   ¬word_bit 52 (reg'TCR_EL1 l3.TCR_EL1)` by (
    state_rel_tac[] >> gvs[asl_sys_regs_ok_def]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `word_bit 55 foo` >>
  `word_bit 55 foo = word_bit 55 addr` by (
    simp[Abbr `foo`] >> IF_CASES_TAC >> simp[] >>
    pop_assum mp_tac >> blastLib.BBLAST_TAC) >>
  simp[Abbr `foo`] >>
  (
    Cases_on `word_bit 55 addr` >> simp[]
    >- (
      Cases_on `l3.TCR_EL1.TBI1` >> simp[] >> state_rel_tac[] >>
      qpat_x_assum `word_bit _ _` mp_tac >> blastLib.BBLAST_TAC
      )
    >- (
      Cases_on `l3.TCR_EL1.TBI0` >> simp[] >> state_rel_tac[] >>
      qpat_x_assum `word_bit _ _` mp_tac >> blastLib.BBLAST_TAC
      )
  )
QED

Theorem l3_models_asl_BranchImmediate_JMP:
  ∀a. a = sw2sw ((27 >< 2) a @@ (0b0w : word2)) ⇒
    l3_models_asl_instr (Branch (BranchImmediate (a, BranchType_JMP)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >> pop_assum kall_tac >>
  asl_cexecute_tac >> simp[] >> pop_assum kall_tac >>
  qcollapse_tac `(27 >< 2) a : 26 word` >>
  qcollapse_tac `(((27 >< 2) a : 26 word) @@ (0w : 2 word)) : 28 word` >>
  simp[dfn'BranchImmediate_def] >>
  simp[
    decode_b_uncond_aarch64_instrs_branch_unconditional_immediate_def,
    execute_aarch64_instrs_branch_unconditional_immediate_def
    ] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule PC_read >> strip_tac >> drule returnS_bindS_unit >> rw[] >>
  ntac 2 $ pop_assum kall_tac >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  qmatch_goalsub_abbrev_tac `BranchTo (addr, _)` >>
  simp[armv86aTheory.BranchTo_def] >>
  qspec_then `asl1` mp_tac $ GEN_ALL UsingAArch32_F >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  drule l3_asl_AArch64_BranchAddr >> simp[] >>
  disch_then $ qspecl_then [`addr`] strip_assume_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  pop_assum kall_tac >> simp[returnS, bindS, seqS] >>
  gvs[asl_reg_rws, returnS, BranchTaken_ref_def] >>
  gvs[BranchTo_def, Hint_Branch_def] >>
  reverse conj_tac >- gvs[asl_sys_regs_ok_def] >>
  Cases_on_word_value `l3.PSTATE.EL` >> simp[]
  >- (
    `¬word_bit 29 (reg'TCR_EL2_EL3 l3.TCR_EL3)` by (
      state_rel_tac[] >> gvs[asl_sys_regs_ok_def] >>
      qmatch_goalsub_abbrev_tac `_ (_ (_ tcr_el3))` >>
      qpat_x_assum `¬word_bit 29 tcr_el3` mp_tac >>
      blastLib.BBLAST_TAC >> gvs[]) >>
    simp[] >> IF_CASES_TAC >> simp[] >>
    state_rel_tac[] >> blastLib.BBLAST_TAC
    )
  >- (
    `¬word_bit 29 (reg'TCR_EL2_EL3 l3.TCR_EL2)` by (
      state_rel_tac[] >> gvs[asl_sys_regs_ok_def] >>
      qmatch_goalsub_abbrev_tac `_ (_ (_ tcr_el2))` >>
      qpat_x_assum `¬word_bit 29 tcr_el2` mp_tac >>
      blastLib.BBLAST_TAC >> gvs[]) >>
    simp[] >> IF_CASES_TAC >> simp[] >>
    state_rel_tac[] >> blastLib.BBLAST_TAC
    ) >>
  `¬word_bit 51 (reg'TCR_EL1 l3.TCR_EL1) ∧
   ¬word_bit 52 (reg'TCR_EL1 l3.TCR_EL1)` by (
    state_rel_tac[] >> gvs[asl_sys_regs_ok_def]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `word_bit 55 foo` >>
  `word_bit 55 foo = word_bit 55 addr` by (
    simp[Abbr `foo`] >> IF_CASES_TAC >> simp[] >>
    pop_assum mp_tac >> blastLib.BBLAST_TAC) >>
  simp[Abbr `foo`] >>
  (
    Cases_on `word_bit 55 addr` >> simp[]
    >- (
      Cases_on `l3.TCR_EL1.TBI1` >> simp[] >> state_rel_tac[] >>
      qpat_x_assum `word_bit _ _` mp_tac >> blastLib.BBLAST_TAC
      )
    >- (
      Cases_on `l3.TCR_EL1.TBI0` >> simp[] >> state_rel_tac[] >>
      qpat_x_assum `word_bit _ _` mp_tac >> blastLib.BBLAST_TAC
      )
  )
QED

Theorem l3_models_asl_BranchConditional:
  ∀a i. a = sw2sw ((20 >< 2) a @@ (0b0w : word2)) ∧ i ≠ 0b1111w ⇒
    l3_models_asl_instr (Branch (BranchConditional (a, i)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >> pop_assum kall_tac >>
  asl_cexecute_tac >> simp[] >> pop_assum kall_tac >>
  qcollapse_tac `(20 >< 2) a : 19 word` >>
  qcollapse_tac `(((20 >< 2) a : 19 word) @@ (0w : 2 word)) : 21 word` >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[dfn'BranchConditional_def] >>
  simp[
    decode_b_cond_aarch64_instrs_branch_conditional_cond_def,
    execute_aarch64_instrs_branch_conditional_cond_def
    ] >>
  drule l3_asl_ConditionHolds >> disch_then $ qspec_then `i` assume_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  reverse IF_CASES_TAC >> gvs[] >- simp[returnS] >>
  drule PC_read >> strip_tac >> drule returnS_bindS_unit >> rw[] >>
  ntac 2 $ pop_assum kall_tac >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  qmatch_goalsub_abbrev_tac `BranchTo (addr, _)` >>
  simp[armv86aTheory.BranchTo_def] >>
  qspec_then `asl1` mp_tac $ GEN_ALL UsingAArch32_F >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  drule l3_asl_AArch64_BranchAddr >> simp[] >>
  disch_then $ qspecl_then [`addr`] strip_assume_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  pop_assum kall_tac >> simp[returnS, bindS, seqS] >>
  gvs[asl_reg_rws, returnS, BranchTaken_ref_def] >>
  gvs[BranchTo_def, Hint_Branch_def] >>
  reverse conj_tac >- gvs[asl_sys_regs_ok_def] >>
  Cases_on_word_value `l3.PSTATE.EL` >> simp[]
  >- (
    `¬word_bit 29 (reg'TCR_EL2_EL3 l3.TCR_EL3)` by (
      state_rel_tac[] >> gvs[asl_sys_regs_ok_def] >>
      qmatch_goalsub_abbrev_tac `_ (_ (_ tcr_el3))` >>
      qpat_x_assum `¬word_bit 29 tcr_el3` mp_tac >>
      blastLib.BBLAST_TAC >> gvs[]) >>
    simp[] >> IF_CASES_TAC >> simp[] >>
    state_rel_tac[] >> blastLib.BBLAST_TAC
    )
  >- (
    `¬word_bit 29 (reg'TCR_EL2_EL3 l3.TCR_EL2)` by (
      state_rel_tac[] >> gvs[asl_sys_regs_ok_def] >>
      qmatch_goalsub_abbrev_tac `_ (_ (_ tcr_el2))` >>
      qpat_x_assum `¬word_bit 29 tcr_el2` mp_tac >>
      blastLib.BBLAST_TAC >> gvs[]) >>
    simp[] >> IF_CASES_TAC >> simp[] >>
    state_rel_tac[] >> blastLib.BBLAST_TAC
    ) >>
  `¬word_bit 51 (reg'TCR_EL1 l3.TCR_EL1) ∧
   ¬word_bit 52 (reg'TCR_EL1 l3.TCR_EL1)` by (
    state_rel_tac[] >> gvs[asl_sys_regs_ok_def]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `word_bit 55 foo` >>
  `word_bit 55 foo = word_bit 55 addr` by (
    simp[Abbr `foo`] >> IF_CASES_TAC >> simp[] >>
    pop_assum mp_tac >> blastLib.BBLAST_TAC) >>
  simp[Abbr `foo`] >>
  (
    Cases_on `word_bit 55 addr` >> simp[]
    >- (
      Cases_on `l3.TCR_EL1.TBI1` >> simp[] >> state_rel_tac[] >>
      qpat_x_assum `word_bit _ _` mp_tac >> blastLib.BBLAST_TAC
      )
    >- (
      Cases_on `l3.TCR_EL1.TBI0` >> simp[] >> state_rel_tac[] >>
      qpat_x_assum `word_bit _ _` mp_tac >> blastLib.BBLAST_TAC
      )
  )
QED

Theorem l3_models_asl_BranchRegister_JMP:
  ∀r.
    l3_models_asl_instr (Branch (BranchRegister (r, BranchType_JMP)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >> pop_assum kall_tac >>
  asl_cexecute_tac >> simp[] >> pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[dfn'BranchRegister_def] >>
  simp[
    decode_br_aarch64_instrs_branch_unconditional_register_def,
    execute_aarch64_instrs_branch_unconditional_register_def
    ] >>
  simp[undefined_BranchType_def] >>
  drule X_read >> disch_then $ qspec_then `&w2n r` mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  `∃b. read_regS InGuardedPage_ref asl1 = returnS b asl1 : bool res` by
    simp[asl_reg_rws, returnS] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `seqS left right` >>
  `∃w2. left = write_regS BTypeNext_ref w2` by (
    unabbrev_all_tac >> rpt IF_CASES_TAC >> gvs[] >> irule_at Any EQ_REFL) >>
  simp[Abbr `left`, Abbr `right`, asl_reg_rws, returnS, seqS] >>
  simp[BTypeNext_ref_def] >> qmatch_goalsub_abbrev_tac `_ asl2 : unit res` >>
  `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[armv86aTheory.BranchTo_def] >>
  qspec_then `asl2` mp_tac $ GEN_ALL UsingAArch32_F >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  drule l3_asl_AArch64_BranchAddr >> simp[] >>
  disch_then $ qspecl_then [`X r l3`] strip_assume_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  pop_assum kall_tac >> simp[returnS, bindS, seqS] >>
  gvs[asl_reg_rws, returnS, BranchTaken_ref_def] >>
  gvs[BranchTo_def, Hint_Branch_def] >>
  reverse conj_tac >- gvs[asl_sys_regs_ok_def] >>
  Cases_on_word_value `l3.PSTATE.EL` >> simp[]
  >- (
    `¬word_bit 29 (reg'TCR_EL2_EL3 l3.TCR_EL3)` by (
      state_rel_tac[] >> gvs[asl_sys_regs_ok_def] >>
      qmatch_goalsub_abbrev_tac `_ (_ (_ tcr_el3))` >>
      qpat_x_assum `¬word_bit 29 tcr_el3` mp_tac >>
      blastLib.BBLAST_TAC >> gvs[]) >>
    simp[] >> IF_CASES_TAC >> simp[] >>
    state_rel_tac[] >> blastLib.BBLAST_TAC
    )
  >- (
    `¬word_bit 29 (reg'TCR_EL2_EL3 l3.TCR_EL2)` by (
      state_rel_tac[] >> gvs[asl_sys_regs_ok_def] >>
      qmatch_goalsub_abbrev_tac `_ (_ (_ tcr_el2))` >>
      qpat_x_assum `¬word_bit 29 tcr_el2` mp_tac >>
      blastLib.BBLAST_TAC >> gvs[]) >>
    simp[] >> IF_CASES_TAC >> simp[] >>
    state_rel_tac[] >> blastLib.BBLAST_TAC
    ) >>
  `¬word_bit 51 (reg'TCR_EL1 l3.TCR_EL1) ∧
   ¬word_bit 52 (reg'TCR_EL1 l3.TCR_EL1)` by (
    state_rel_tac[] >> gvs[asl_sys_regs_ok_def]) >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `bit_field_insert _ _ _ xx` >>
  qmatch_goalsub_abbrev_tac `word_bit 55 foo` >>
  `word_bit 55 foo = word_bit 55 xx` by (
    simp[Abbr `foo`] >> IF_CASES_TAC >> simp[] >>
    pop_assum mp_tac >> blastLib.BBLAST_TAC) >>
  simp[Abbr `foo`] >>
  (
    Cases_on `word_bit 55 addr` >> simp[]
    >- (
      Cases_on `l3.TCR_EL1.TBI1` >> simp[] >> state_rel_tac[] >>
      qpat_x_assum `word_bit _ _` mp_tac >> blastLib.BBLAST_TAC
      )
    >- (
      Cases_on `l3.TCR_EL1.TBI0` >> simp[] >> state_rel_tac[] >>
      qpat_x_assum `word_bit _ _` mp_tac >> blastLib.BBLAST_TAC
      )
  )
QED

Theorem l3_models_asl_ExtractRegister:
  ∀b w r3 r2 r1.
    l3_models_asl_instr (Data (ExtractRegister@64 (b, w, r3, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >>
  asl_cexecute_tac >> simp[] >> pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[
    decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate_def,
    execute_aarch64_instrs_integer_ins_ext_extract_immediate_def
    ] >>
  simp[INT_ADD_CALCULATE, INT_SUB_CALCULATE] >>
  drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >> pop_assum kall_tac >>
  drule X_read >> disch_then $ qspec_then `&w2n r3` mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >> pop_assum kall_tac >>
  reverse IF_CASES_TAC >> gvs[]
  >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> WORD_DECIDE_TAC) >>
  Cases_on `r1 = 31w` >> gvs[] >- simp[X_set_31, returnS] >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,
    `(w2n w + 63 >< w2n w) (((X r2 l3 :word64) @@ (X r3 l3 :word64)) :word128)`]
    mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> simp[returnS] >>
  drule_all X_set_asl_sys_regs_ok >> strip_tac >>
  qpat_x_assum `_ = returnS _ _` kall_tac >>
  qpat_x_assum `state_rel _ _` mp_tac >> simp[write'X_def] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    irule FALSITY >> pop_assum mp_tac >> simp[] >>
    DEP_REWRITE_TAC[LESS_MOD] >> simp[] >> WORD_DECIDE_TAC
    ) >>
  qmatch_goalsub_abbrev_tac `_⦇r1 ↦ asl_val⦈` >>
  qmatch_goalsub_abbrev_tac `_⦇r1 ↦ v2w l3_val⦈` >>
  qsuff_tac `asl_val = v2w l3_val` >> rw[] >> unabbrev_all_tac >>
  gvs[GSYM $ b64 ``:'N`` X_def |> SIMP_RULE (srw_ss()) [FUN_EQ_THM]] >>
  qmatch_goalsub_abbrev_tac `x2 @@ x3` >>
  `w2v x2 ++ w2v x3 = w2v ((x2 @@ x3) : word128)` by (
    bitstringLib.Cases_on_v2w `x2` >> bitstringLib.Cases_on_v2w `x3` >>
    once_rewrite_tac[word_concat_v2w_rwt] >> gvs[w2v_v2w]) >>
  simp[] >> qmatch_goalsub_abbrev_tac `shiftr (w2v x23)` >>
  qmatch_goalsub_abbrev_tac `lo + 63` >>
  qspec_then `w` assume_tac w2n_lt >> gvs[] >>
  blastLib.BBLAST_TAC >> `lo + 63 < 127` by gvs[] >>
  simp[MIN_DEF, shiftr_def, testbit_el, EL_TAKE, el_w2v]
QED

Theorem l3_models_asl_Address_F:
  ∀i r. sw2sw ((20 >< 0) i : 21 word) = i ⇒
    l3_models_asl_instr (Address (F, i, r))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >> simp[encode_rws] >>
  `((20 >< 2) i : 19 word) @@ ((1 >< 0) i : 2 word) = (20 >< 0) i` by WORD_DECIDE_TAC >>
  simp[] >> l3_decode_tac >> rw[] >> qcollapse_tac `(20 >< 0) i` >>
  simp[Run_def, dfn'Address_def] >>
  asl_cexecute_tac >> simp[] >> pop_assum kall_tac >>
  map_every qcollapse_tac [`(20 >< 2) i`,`(1 >< 0) i`] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[
    decode_adr_aarch64_instrs_integer_arithmetic_address_pc_rel_def,
    execute_aarch64_instrs_integer_arithmetic_address_pc_rel_def
    ] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  drule PC_read >> rw[Once bindS, returnS] >>
  Cases_on `r = 31w` >> gvs[] >- simp[write'X_def, X_set_31, returnS] >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r`,`i + l3.PC`] mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[returnS] >>
  irule $ b64 alpha X_set_asl_sys_regs_ok >> simp[returnS] >>
  rpt $ goal_assum drule
QED

Theorem l3_models_asl_Address_T:
  ∀(j : 52 word) r. sw2sw ((20 >< 0) j @@ (0w : word12)) = j @@ (0w : word12) ⇒
    l3_models_asl_instr (Address (T, j @@ (0w : word12), r))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >> simp[encode_rws] >>
  `(13 >< 12) (j @@ (0w : word12)) = (1 >< 0) j` by blastLib.BBLAST_TAC >>
  `(32 >< 14) (j @@ (0w : word12)) = (20 >< 2) j` by blastLib.BBLAST_TAC >>
  `(20 >< 2) j @@ (1 >< 0) j @@ (0w : word12) = (20 >< 0) j @@ (0w : word12)`
    by blastLib.BBLAST_TAC >>
  gvs[] >>
  l3_decode_tac >> rw[] >> qcollapse_tac `(20 >< 0) j @@ (0w : word12)` >>
  simp[Run_def, dfn'Address_def] >>
  simp[] >> asl_cexecute_tac >> simp[] >> pop_assum kall_tac >>
  map_every qcollapse_tac [`(20 >< 2) j`,`(1 >< 0) j`] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[
    decode_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel_def,
    execute_aarch64_instrs_integer_arithmetic_address_pc_rel_def
    ] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  drule PC_read >> rw[Once bindS, returnS] >>
  Cases_on `r = 31w` >> gvs[] >- simp[write'X_def, X_set_31, returnS] >>
  DEP_REWRITE_TAC[word_concat_assoc |> INST_TYPE [``:ε`` |-> ``:14``]] >> simp[] >>
  qmatch_goalsub_abbrev_tac `X_set _ _ asl_val` >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r`,`asl_val`] mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> simp[returnS] >>
  qmatch_goalsub_abbrev_tac `write'X (l3_val,_)` >> gvs[] >>
  irule_at Any $ b64 alpha X_set_asl_sys_regs_ok >> rpt $ goal_assum drule >>
  qsuff_tac `asl_val = l3_val` >> rw[] >> gvs[] >> unabbrev_all_tac >>
  simp[set_subrange_zeros_def, set_slice_zeros_def, EVAL ``i2w 4095``] >>
  blastLib.BBLAST_TAC
QED

Theorem l3_models_asl_Address:
  ∀b i r.
    let instr = Address (b, i, r) in
    (∀s. Encode instr ≠ BadCode s) ⇒ l3_models_asl_instr instr
Proof
  reverse $ rw[encode_rws]
  >- (
    `((20 >< 2) i : 19 word) @@ ((1 >< 0) i : 2 word) = (20 >< 0) i` by
      WORD_DECIDE_TAC >>
    gvs[l3_models_asl_Address_F]
    ) >>
  `∃j : 52 word. i = j @@ (0w : word12)` by (
    qexists_tac `(63 >< 12) i` >> pop_assum mp_tac >> blastLib.BBLAST_TAC) >>
  gvs[] >>
  irule l3_models_asl_Address_T >> pop_assum mp_tac >> blastLib.BBLAST_TAC
QED

(******************** Loads/store ********************)

(********** Misc lemmas **********)

Triviality APPLY_UPDATE_ALT_THM:
  ∀f a b c. f⦇a ↦ b⦈ c = if c = a then b else f c
Proof
  rw[combinTheory.APPLY_UPDATE_THM]
QED

Triviality FLOOKUP_UPDATE_ALT:
  ∀fm k1 v k2. FLOOKUP (fm |+ (k1,v)) k2 = if k2 = k1 then SOME v else FLOOKUP fm k2
Proof
  rw[FLOOKUP_UPDATE]
QED

Triviality load_store_encode_lemma:
  (w : word64 = w2w ((11 >< 0) (w ⋙ 3)) ≪ 3 ⇔
    ∃j : word12. w = (0w : 49 word) @@ j @@ (0w : word3)) ∧
  (w : word64 = w2w ((11 >< 0) (w ⋙ 2)) ≪ 2 ⇔
    ∃j : word12. w = (0w : 50 word) @@ j @@ (0w : word2)) ∧
  (w : word64 = sw2sw ((8 >< 0) w) ⇔
    (word_bit 8 w ⇔ w = (-1w : 56 word) @@ (7 >< 0) w) ∧
    (¬word_bit 8 w ⇔ w = (7 >< 0) w)) ∧
  (w : word64 = w2w ((11 >< 0) w : word12) ⇔
    ∃j : word12. w = (0w : 52 word) @@ j)
Proof
  rpt conj_tac
  >- (
    reverse eq_tac >> rw[] >- blastLib.BBLAST_TAC >>
    qexists_tac `(14 >< 3) w` >> pop_assum mp_tac >> blastLib.BBLAST_TAC
    )
  >- (
    reverse eq_tac >> rw[] >- blastLib.BBLAST_TAC >>
    qexists_tac `(13 >< 2) w` >> pop_assum mp_tac >> blastLib.BBLAST_TAC
    )
  >- blastLib.BBLAST_TAC
  >- (
    reverse eq_tac >> rw[] >- blastLib.BBLAST_TAC >>
    qexists_tac `(11 >< 0) w` >> pop_assum mp_tac >> blastLib.BBLAST_TAC
    )
QED

(********** Relational lemmas **********)

Theorem AArch64_TranslateAddress:
  ∀vaddr acctype iswrite aligned size asl.
    ∃addrdesc.
      AArch64_TranslateAddress vaddr acctype iswrite aligned size asl =
      returnS addrdesc asl ∧
      addrdesc.AddressDescriptor_paddress.FullAddress_address = vaddr ∧
      ¬IsFault addrdesc
Proof
  rw[AArch64_TranslateAddress_def, bindS, returnS] >>
  simp[
    undefined_AddressDescriptor_def,
    undefined_FaultRecord_def,
    undefined_MemoryAttributes_def,
    undefined_FullAddress_def,
    undefined_Fault_def,
    undefined_AccType_def,
    undefined_MemType_def,
    undefined_DeviceType_def,
    undefined_MemAttrHints_def,
    preludeTheory.undefined_int_def,
    sail2_state_monadTheory.undefined_boolS_def
    ] >>
  simp[returnS, IsFault_def]
QED

Theorem l3_asl_Align:
  Align w (&i) = Align (w,i)
Proof
  simp[armv86aTheory.Align_def, arm8Theory.Align_def, Align__1_def] >>
  Cases_on `i = 0` >> gvs[] >>
  simp[integer_subrange_def, INT_MUL_CALCULATE, INT_DIV_CALCULATE, asl_word_rws] >>
  DEP_REWRITE_TAC[TAKE_LENGTH_ID_rwt] >> simp[] >>
  DEP_REWRITE_TAC[v2w_fixwidth_dimindex] >> simp[]
QED

Theorem l3_asl_BigEndian:
  ∀l3 asl. state_rel l3 asl ∧ asl_sys_regs_ok asl
  ⇒ BigEndian () asl = returnS (BigEndian l3) asl
Proof
  rw[] >> simp[armv86aTheory.BigEndian_def, arm8Theory.BigEndian_def] >>
  simp[sail2_state_monadTheory.undefined_boolS_def] >>
  qspec_then `asl` mp_tac UsingAArch32_F >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
  drule $ INST_TYPE [gamma |-> bool] returnS_bindS >>
  simp[] >> disch_then kall_tac >>
  simp[asl_reg_rws, asl_word_rws] >>
  simp[Once bindS, Once returnS] >>
  qmatch_goalsub_abbrev_tac `el = 0w` >>
  `el = l3.PSTATE.EL` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule_all SCTLR_read__1 >> strip_tac >>
  drule $ INST_TYPE [gamma |-> bool] returnS_bindS >>
  simp[COND_RATOR] >> disch_then kall_tac >>
  simp[EL_MAP, el_w2v, sail2_valuesTheory.just_list_def] >>
  qmatch_goalsub_abbrev_tac `foo ' 24` >>
  `foo ' 24 = (SCTLR l3).E0E` by (
    unabbrev_all_tac >> simp[reg'SCTLRType_def] >> CASE_TAC >> simp[] >>
    Cases_on_word_value `l3.PSTATE.EL` >>
    gvs[SCTLR_def, TranslationRegime_def, aslSCTLR_def] >> blastLib.BBLAST_TAC) >>
  qmatch_goalsub_abbrev_tac `bar ' 25` >>
  `bar ' 25 = (SCTLR l3).EE` by (
    unabbrev_all_tac >> simp[reg'SCTLRType_def] >> CASE_TAC >> simp[] >>
    Cases_on_word_value `l3.PSTATE.EL` >>
    gvs[SCTLR_def, TranslationRegime_def, aslSCTLR_def] >> blastLib.BBLAST_TAC) >>
  simp[] >> rw[SCTLR_def, TranslationRegime_def]
QED

Theorem l3_asl_CheckSPAlignment:
  ∀l3 asl. state_rel l3 asl ∧ asl_sys_regs_ok asl ⇒
    ∀l3'. CheckSPAlignment l3 = l3' ∧ l3'.exception = NoException
    ⇒ l3 = l3' ∧ CheckSPAlignment () asl = returnS () asl
Proof
  rw[CheckSPAlignment_def, raise'exception_def] >>
  rw[armv86aTheory.CheckSPAlignment_def] >>
  simp[sail2_state_monadTheory.undefined_boolS_def] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspec_then `asl` assume_tac PSTATE_read >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  `(asl.regstate.ProcState_reg "PSTATE").ProcState_EL = l3.PSTATE.EL` by
      state_rel_tac[] >>
  simp[asl_word_rws, EL_MAP] >> simp[sail2_valuesTheory.just_list_def, el_w2v] >>
  drule_all SCTLR_read__1 >> strip_tac >> drule returnS_bindS_unit >>
  IF_CASES_TAC >> simp[] >> disch_then kall_tac
  >- (
    simp[aslSCTLR_def, SCTLR_def, TranslationRegime_def] >>
    qmatch_goalsub_abbrev_tac `(foo @@ bar) ' 4` >>
    `(foo @@ bar) ' 4 = l3.SCTLR_EL1.SA0` by (
      unabbrev_all_tac >> simp[reg'SCTLRType_def] >>
      CASE_TAC >> simp[] >> blastLib.BBLAST_TAC) >>
    simp[l3_asl_Align] >> gvs[Aligned_def]
    ) >>
  qmatch_goalsub_abbrev_tac `foo ' 3` >>
  `foo ' 3 = (SCTLR l3).SA` by (
    unabbrev_all_tac >> simp[reg'SCTLRType_def] >> CASE_TAC >> simp[] >>
    simp[aslSCTLR_def, SCTLR_def, TranslationRegime_def] >>
    Cases_on_word_value `l3.PSTATE.EL` >>
    gvs[SCTLR_def, TranslationRegime_def] >> blastLib.BBLAST_TAC) >>
  simp[] >> gvs[Aligned_def, l3_asl_Align]
QED

(********** Memory reads/writes **********)

Theorem l3_asl_Mem_read_1:
  ∀l3 asl addrdesc accdesc.
    mem_rel l3 asl.memstate asl.tagstate ∧
    asl.regstate.bitvector_64_dec_reg "__CNTControlBase" = 0w
  ⇒ let p = addrdesc.AddressDescriptor_paddress.FullAddress_address in
    Mem_read addrdesc 1 accdesc asl = returnS (l3 p) asl
Proof
  LET_ELIM_TAC >> rw[Mem_read_def] >>
  simp[
    sail2_state_monadTheory.undefined_boolS_def, undefined_FaultRecord_def,
    undefined_MemoryAttributes_def, undefined_FullAddress_def,
    undefined_Fault_def, undefined_AccType_def,
    preludeTheory.undefined_int_def
    ] >>
  simp[asl_sys_reg_rws] >>
  simp[Once returnS, Once bindS] >>
  simp[
    preludeTheory.ReadMemory_def,
    sail2_state_monadTheory.read_memS_def,
    sail2_state_monadTheory.read_memtS_def,
    asl_word_rws, w2n_w2w
    ] >>
  simp[
    sail2_state_monadTheory.read_memt_bytesS_def,
    sail2_state_monadTheory.read_memt_bytesS_def,
    sail2_state_monadTheory.readS_def,
    bindS, returnS
    ] >>
  simp[sail2_state_monadTheory.get_mem_bytes_def] >>
  qspec_then `p` assume_tac w2n_lt >> gvs[] >>
  gvs[mem_rel_def] >> last_x_assum $ qspec_then `p` assume_tac >> gvs[] >>
  gvs[] >> simp[sail2_valuesTheory.and_bit_def] >>
  ntac 2 $ simp[Once sail2_valuesTheory.just_list_def] >>
  simp[returnS] >>
  simp[sail2_valuesTheory.bits_of_mem_bytes_def,
       sail2_valuesTheory.bits_of_bytes_def] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  DEP_REWRITE_TAC[OPTION_MAP_just_list] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss, EVERY_MAP] >>
  simp[returnS]
QED

Theorem l3_asl_Mem_read_4:
  ∀l3 asl addrdesc accdesc.
    mem_rel l3 asl.memstate asl.tagstate ∧
    asl.regstate.bitvector_64_dec_reg "__CNTControlBase" = 0w
  ⇒ let p = addrdesc.AddressDescriptor_paddress.FullAddress_address in
    Mem_read addrdesc 4 accdesc asl =
    returnS (l3 (p + 3w) @@ l3 (p + 2w) @@ l3 (p + 1w) @@ l3 p) asl
Proof
  LET_ELIM_TAC >> rw[Mem_read_def] >>
  simp[
    sail2_state_monadTheory.undefined_boolS_def, undefined_FaultRecord_def,
    undefined_MemoryAttributes_def, undefined_FullAddress_def,
    undefined_Fault_def, undefined_AccType_def,
    preludeTheory.undefined_int_def
    ] >>
  simp[asl_sys_reg_rws] >>
  simp[Once returnS, Once bindS] >>
  simp[
    preludeTheory.ReadMemory_def,
    sail2_state_monadTheory.read_memS_def,
    sail2_state_monadTheory.read_memtS_def,
    asl_word_rws, w2n_w2w
    ] >>
  simp[
    sail2_state_monadTheory.read_memt_bytesS_def,
    sail2_state_monadTheory.readS_def,
    bindS, returnS
    ] >>
  simp[sail2_state_monadTheory.get_mem_bytes_def] >>
  gvs[mem_rel_def] >>
  qspec_then `p` assume_tac w2n_lt >> gvs[] >>
  map_every (fn qt => last_assum $ qspec_then qt assume_tac)
    [`p`,`p+1w`,`p+2w`,`p+3w`] >>
  last_x_assum kall_tac >> gvs[word_add_def] >>
  simp[sail2_valuesTheory.and_bit_def] >>
  ntac 5 $ simp[Once sail2_valuesTheory.just_list_def] >>
  simp[returnS] >>
  simp[sail2_valuesTheory.bits_of_mem_bytes_def,
       sail2_valuesTheory.bits_of_bytes_def] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  DEP_REWRITE_TAC[OPTION_MAP_just_list] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss, EVERY_MAP] >>
  simp[returnS] >> DEP_REWRITE_TAC[word_concat_v2w] >> simp[]
QED

Theorem l3_asl_Mem_read_8:
  ∀l3 asl addrdesc accdesc.
    mem_rel l3 asl.memstate asl.tagstate ∧
    asl.regstate.bitvector_64_dec_reg "__CNTControlBase" = 0w
  ⇒ let p = addrdesc.AddressDescriptor_paddress.FullAddress_address in
    Mem_read addrdesc 8 accdesc asl = returnS (mem_dword l3 (w2w p)) asl
Proof
  LET_ELIM_TAC >> rw[Mem_read_def] >>
  simp[
    sail2_state_monadTheory.undefined_boolS_def, undefined_FaultRecord_def,
    undefined_MemoryAttributes_def, undefined_FullAddress_def,
    undefined_Fault_def, undefined_AccType_def,
    preludeTheory.undefined_int_def
    ] >>
  simp[asl_sys_reg_rws] >>
  simp[Once returnS, Once bindS] >>
  simp[
    preludeTheory.ReadMemory_def,
    sail2_state_monadTheory.read_memS_def,
    sail2_state_monadTheory.read_memtS_def,
    asl_word_rws, w2n_w2w
    ] >>
  simp[
    sail2_state_monadTheory.read_memt_bytesS_def,
    sail2_state_monadTheory.readS_def,
    bindS, returnS
    ] >>
  simp[sail2_state_monadTheory.get_mem_bytes_def] >>
  gvs[mem_rel_def] >>
  qspec_then `p` assume_tac w2n_lt >> gvs[] >>
  map_every (fn qt => last_assum $ qspec_then qt assume_tac)
    [`p`,`p+1w`,`p+2w`,`p+3w`,`p+4w`,`p+5w`,`p+6w`,`p+7w`] >>
  last_x_assum kall_tac >> gvs[word_add_def] >>
  simp[sail2_valuesTheory.and_bit_def] >>
  ntac 9 $ simp[Once sail2_valuesTheory.just_list_def] >>
  simp[returnS] >>
  simp[sail2_valuesTheory.bits_of_mem_bytes_def,
       sail2_valuesTheory.bits_of_bytes_def] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  DEP_REWRITE_TAC[OPTION_MAP_just_list] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss, EVERY_MAP] >>
  simp[returnS, mem_dword_def] >>
  gvs[GSYM word_add_n2w] >>
  gvs[LENGTH_EQ_NUM_compute] >> blastLib.BBLAST_TAC
QED

Theorem l3_asl_Mem_read0_1_AccType_NORMAL:
  ∀l3 asl addr. state_rel l3 asl ∧ asl_sys_regs_ok asl ⇒
  Mem_read0 addr 1 AccType_NORMAL asl =
  returnS (FST (Mem (addr,1,AccType_NORMAL) l3)) asl : word8 res
Proof
  rw[] >> simp[Mem_read0_def, AArch64_CheckAlignment_def] >>
  simp[sail2_state_monadTheory.undefined_boolS_def, undefined_Constraint_def,
       ConstrainUnpredictable_def] >>
  simp[l3_asl_Align, asl_word_rws, Align_def] >>
  simp[EL_MAP, sail2_valuesTheory.just_list_def, el_w2v] >>
  drule_all SCTLR_read__1 >> strip_tac >>
  drule $ INST_TYPE [gamma |-> ``:word8``] returnS_bindS >>
  simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `foo ' 1` >>
  `foo ' 1 = (SCTLR l3).A` by (
    unabbrev_all_tac >> simp[reg'SCTLRType_def] >> CASE_TAC >> simp[] >>
    gvs[SCTLR_def, TranslationRegime_def] >>
    Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >> blastLib.BBLAST_TAC) >>
  simp[Once $ GSYM COND_RAND] >> ntac 2 $ pop_assum kall_tac >>
  simp[AArch64_MemSingle_read_def, l3_asl_Align, Align_def] >>
  qspecl_then [`addr`,`AccType_NORMAL`,`F`,`T`,`1`,`asl`]
    assume_tac AArch64_TranslateAddress >> gvs[] >>
  drule $ INST_TYPE [gamma |-> ``:word8``] returnS_bindS >>
  simp[] >> disch_then kall_tac >>
  qspecl_then [`AccType_NORMAL`,`asl`] mp_tac CreateAccessDescriptor >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
  qspec_then `asl` mp_tac IsSecure >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
  ntac 2 $ simp[Once returnS] >> simp[] >>
  qpat_abbrev_tac `addr = _.FullAddress_address` >>
  qspecl_then [`addr`,`AccType_NORMAL`,`asl`] mp_tac AArch64_AccessIsTagChecked >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
  drule $ INST_TYPE [gamma |-> ``:word8``] returnS_bindS >>
  simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `Mem_read _ _ accdesc` >>
  qspecl_then [`l3.MEM`,`asl`,`addrdesc`,`accdesc`] mp_tac l3_asl_Mem_read_1 >>
  impl_tac >- state_rel_tac[] >> rw[] >>
  drule $ INST_TYPE [gamma |-> ``:word8``] returnS_bindS >>
  simp[] >> disch_then kall_tac >>
  drule_all l3_asl_BigEndian >> strip_tac >>
  drule $ INST_TYPE [gamma |-> ``:word8``] returnS_bindS >>
  simp[] >> disch_then kall_tac >>
  simp[Mem_def, CheckAlignment_def, Aligned_def] >>
  ntac 3 $ simp[Once state_transformerTheory.FOR_def] >>
  simp[reverse_endianness0_def, Align_def, BigEndianReverse_def]
QED

Theorem l3_asl_Mem_read0_4_AccType_NORMAL:
  ∀l3 asl addr. state_rel l3 asl ∧ asl_sys_regs_ok asl ∧
    ((SCTLR l3).A ⇒ Aligned (addr, 4)) ⇒
  Mem_read0 addr 4 AccType_NORMAL asl =
  returnS (FST (Mem (addr,4,AccType_NORMAL) l3)) asl : word32 res
Proof
  rw[] >> simp[Mem_read0_def, AArch64_CheckAlignment_def] >>
  simp[sail2_state_monadTheory.undefined_boolS_def, undefined_Constraint_def,
       ConstrainUnpredictable_def] >>
  simp[l3_asl_Align, asl_word_rws] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[EL_MAP, sail2_valuesTheory.just_list_def, el_w2v] >>
  drule_all SCTLR_read__1 >> strip_tac >>
  drule $ INST_TYPE [gamma |-> ``:word32``] returnS_bindS >>
  simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `foo ' 1` >>
  `foo ' 1 = (SCTLR l3).A` by (
    unabbrev_all_tac >> simp[reg'SCTLRType_def] >> CASE_TAC >> simp[] >>
    gvs[SCTLR_def, TranslationRegime_def] >>
    Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >> blastLib.BBLAST_TAC) >>
  simp[Once $ GSYM COND_RAND] >> ntac 2 $ pop_assum kall_tac >>
  IF_CASES_TAC >- gvs[Aligned_def] >>
  pop_assum mp_tac >> simp[DISJ_EQ_IMP] >> strip_tac >> gvs[] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    simp[AArch64_MemSingle_read_def, l3_asl_Align] >>
    qspecl_then [`addr`,`AccType_NORMAL`,`F`,`T`,`4`,`asl`]
      assume_tac AArch64_TranslateAddress >> gvs[] >>
    drule $ INST_TYPE [gamma |-> ``:word32``] returnS_bindS >>
    simp[] >> disch_then kall_tac >>
    qspecl_then [`AccType_NORMAL`,`asl`] mp_tac CreateAccessDescriptor >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
    qspec_then `asl` mp_tac IsSecure >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
    ntac 2 $ simp[Once returnS] >> simp[HaveMTEExt] >>
    qpat_abbrev_tac `addr = _.FullAddress_address` >>
    qspecl_then [`addr`,`AccType_NORMAL`,`asl`] mp_tac AArch64_AccessIsTagChecked >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
    drule $ INST_TYPE [gamma |-> ``:word32``] returnS_bindS >>
    simp[] >> disch_then kall_tac >>
    qmatch_goalsub_abbrev_tac `Mem_read _ _ accdesc` >>
    qspecl_then [`l3.MEM`,`asl`,`addrdesc`,`accdesc`] mp_tac l3_asl_Mem_read_4 >>
    impl_tac >- state_rel_tac[] >> rw[] >>
    drule $ INST_TYPE [gamma |-> ``:word32``] returnS_bindS >>
    simp[] >> disch_then kall_tac >>
    drule_all l3_asl_BigEndian >> strip_tac >>
    drule $ INST_TYPE [gamma |-> ``:word32``] returnS_bindS >>
    simp[] >> disch_then kall_tac >>
    simp[Mem_def, CheckAlignment_def, Aligned_def] >>
    ntac 3 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    simp[BigEndianReverse_def] >>
    rewrite_tac[GSYM APPEND_ASSOC] >>
    DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
    map_every (rewrite_tac o single) [
      GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
    simp[reverse_endianness0_def, mem_dword_def] >>
    IF_CASES_TAC >> gvs[] >> simp[returnS] >>
    WORD_DECIDE_TAC
    ) >>
  simp[AArch64_MemSingle_read_def, l3_asl_Align, Align_def] >>
  qspecl_then [`addr`,`AccType_NORMAL`,`F`,`F`,`1`,`asl`]
    assume_tac AArch64_TranslateAddress >> gvs[] >>
  drule $ INST_TYPE [gamma |-> ``:word32``] returnS_bindS >>
  simp[] >> disch_then kall_tac >>
  qspecl_then [`AccType_NORMAL`,`asl`] mp_tac CreateAccessDescriptor >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
  qspec_then `asl` mp_tac IsSecure >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
  ntac 2 $ simp[Once returnS] >> simp[HaveMTEExt] >>
  `∀addr. AArch64_AccessIsTagChecked addr AccType_NORMAL asl = returnS F asl` by (
    rw[] >> irule AArch64_AccessIsTagChecked >> gvs[asl_sys_regs_ok_def]) >>
  simp[Once bindS, Once returnS] >>
  qspecl_then [`l3.MEM`,`asl`] mp_tac l3_asl_Mem_read_1 >>
  impl_tac >- state_rel_tac[] >> rw[] >>
  simp[Once bindS, Once returnS] >>
  ntac 8 $ simp[Once sail2_valuesAuxiliaryTheory.index_list_rw] >>
  ntac 8 $ simp[Once sail2_stateAuxiliaryTheory.foreachS_rw] >>
  simp[GSYM bit_field_insert_def] >>
  qpat_abbrev_tac `addr = _.FullAddress_address` >>
  qmatch_goalsub_abbrev_tac `word_modify bar _` >>
  `word_modify bar : word64 -> word64 = bit_field_insert 7 0 (l3.MEM addr)` by (
      simp[Abbr `bar`, bit_field_insert_def]) >>
  simp[Abbr `bar`] >>
  map_every (fn qt =>
    qspecl_then [qt,`AccType_NORMAL`,`F`,`F`,`1`,`asl`]
      strip_assume_tac AArch64_TranslateAddress)
  [`addr + i2w 1`,`addr + i2w 2`,`addr + i2w 3`,`addr + i2w 4`,
   `addr + i2w 5`,`addr + i2w 6`,`addr + i2w 7`] >>
  gvs $ map (EVAL o Term) [`i2w 1`,`i2w 2`,`i2w 3`,`i2w 4`,`i2w 5`,`i2w 6`,`i2w 7`] >>
  ntac 7 (
    simp[Once returnS, Once bindS] >>
    simp[Once returnS, Once bindS] >>
    simp[Once returnS, Once bindS] >>
    simp[Once returnS] >>
    simp[Once returnS, Once bindS] >>
    simp[Once returnS, Once bindS]
    ) >>
  drule_all l3_asl_BigEndian >> strip_tac >> simp[bindS, returnS] >>
  qmatch_goalsub_abbrev_tac `if _ then _ else mem` >>
  simp[Mem_def, CheckAlignment_def, Aligned_def] >>
  ntac 3 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
  simp[state_transformerTheory.BIND_DEF] >>
  simp[BigEndianReverse_def] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
  map_every (rewrite_tac o single) [
    GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
  simp[reverse_endianness0_def] >>
  unabbrev_all_tac >> IF_CASES_TAC >> gvs[] >> blastLib.BBLAST_TAC
QED

Theorem l3_asl_Mem_read0_8_AccType_NORMAL:
  ∀l3 asl addr. state_rel l3 asl ∧ asl_sys_regs_ok asl ∧
    ((SCTLR l3).A ⇒ Aligned (addr, 8)) ⇒
  Mem_read0 addr 8 AccType_NORMAL asl =
  returnS (FST (Mem (addr,8,AccType_NORMAL) l3)) asl : word64 res
Proof
  rw[] >> simp[Mem_read0_def, AArch64_CheckAlignment_def] >>
  simp[sail2_state_monadTheory.undefined_boolS_def, undefined_Constraint_def,
       ConstrainUnpredictable_def] >>
  simp[l3_asl_Align, asl_word_rws] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[EL_MAP, sail2_valuesTheory.just_list_def, el_w2v] >>
  drule_all SCTLR_read__1 >> strip_tac >>
  drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >>
  simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `foo ' 1` >>
  `foo ' 1 = (SCTLR l3).A` by (
    unabbrev_all_tac >> simp[reg'SCTLRType_def] >> CASE_TAC >> simp[] >>
    gvs[SCTLR_def, TranslationRegime_def] >>
    Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >> blastLib.BBLAST_TAC) >>
  simp[Once $ GSYM COND_RAND] >> ntac 2 $ pop_assum kall_tac >>
  IF_CASES_TAC >- gvs[Aligned_def] >>
  pop_assum mp_tac >> simp[DISJ_EQ_IMP] >> strip_tac >> gvs[] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    simp[AArch64_MemSingle_read_def, l3_asl_Align] >>
    qspecl_then [`addr`,`AccType_NORMAL`,`F`,`T`,`8`,`asl`]
      assume_tac AArch64_TranslateAddress >> gvs[] >>
    drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >>
    simp[] >> disch_then kall_tac >>
    qspecl_then [`AccType_NORMAL`,`asl`] mp_tac CreateAccessDescriptor >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
    qspec_then `asl` mp_tac IsSecure >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
    ntac 2 $ simp[Once returnS] >> simp[HaveMTEExt] >>
    qpat_abbrev_tac `addr = _.FullAddress_address` >>
    qspecl_then [`addr`,`AccType_NORMAL`,`asl`] mp_tac AArch64_AccessIsTagChecked >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
    drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >>
    simp[] >> disch_then kall_tac >>
    qmatch_goalsub_abbrev_tac `Mem_read _ _ accdesc` >>
    qspecl_then [`l3.MEM`,`asl`,`addrdesc`,`accdesc`] mp_tac l3_asl_Mem_read_8 >>
    impl_tac >- state_rel_tac[] >> rw[] >>
    drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >>
    simp[] >> disch_then kall_tac >>
    drule_all l3_asl_BigEndian >> strip_tac >>
    drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >>
    simp[] >> disch_then kall_tac >>
    simp[Mem_def, CheckAlignment_def, Aligned_def] >>
    ntac 3 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    simp[BigEndianReverse_def] >>
    rewrite_tac[GSYM APPEND_ASSOC] >>
    DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
    map_every (rewrite_tac o single) [
      GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
    simp[reverse_endianness0_def, mem_dword_def] >>
    IF_CASES_TAC >> gvs[] >> simp[returnS] >>
    WORD_DECIDE_TAC
    ) >>
  simp[AArch64_MemSingle_read_def, l3_asl_Align, Align_def] >>
  qspecl_then [`addr`,`AccType_NORMAL`,`F`,`F`,`1`,`asl`]
    assume_tac AArch64_TranslateAddress >> gvs[] >>
  drule $ INST_TYPE [gamma |-> ``:word64``] returnS_bindS >>
  simp[] >> disch_then kall_tac >>
  qspecl_then [`AccType_NORMAL`,`asl`] mp_tac CreateAccessDescriptor >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
  qspec_then `asl` mp_tac IsSecure >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
  ntac 2 $ simp[Once returnS] >> simp[HaveMTEExt] >>
  `∀addr. AArch64_AccessIsTagChecked addr AccType_NORMAL asl = returnS F asl` by (
    rw[] >> irule AArch64_AccessIsTagChecked >> gvs[asl_sys_regs_ok_def]) >>
  simp[Once bindS, Once returnS] >>
  qspecl_then [`l3.MEM`,`asl`] mp_tac l3_asl_Mem_read_1 >>
  impl_tac >- state_rel_tac[] >> rw[] >>
  simp[Once bindS, Once returnS] >>
  ntac 8 $ simp[Once sail2_valuesAuxiliaryTheory.index_list_rw] >>
  ntac 8 $ simp[Once sail2_stateAuxiliaryTheory.foreachS_rw] >>
  simp[GSYM bit_field_insert_def] >>
  qpat_abbrev_tac `addr = _.FullAddress_address` >>
  qmatch_goalsub_abbrev_tac `word_modify bar _` >>
  `word_modify bar : word64 -> word64 = bit_field_insert 7 0 (l3.MEM addr)` by (
      simp[Abbr `bar`, bit_field_insert_def]) >>
  simp[Abbr `bar`] >>
  map_every (fn qt =>
    qspecl_then [qt,`AccType_NORMAL`,`F`,`F`,`1`,`asl`]
      strip_assume_tac AArch64_TranslateAddress)
  [`addr + i2w 1`,`addr + i2w 2`,`addr + i2w 3`,`addr + i2w 4`,
   `addr + i2w 5`,`addr + i2w 6`,`addr + i2w 7`] >>
  gvs $ map (EVAL o Term) [`i2w 1`,`i2w 2`,`i2w 3`,`i2w 4`,`i2w 5`,`i2w 6`,`i2w 7`] >>
  ntac 7 (
    simp[Once returnS, Once bindS] >>
    simp[Once returnS, Once bindS] >>
    simp[Once returnS, Once bindS] >>
    simp[Once returnS] >>
    simp[Once returnS, Once bindS] >>
    simp[Once returnS, Once bindS]
    ) >>
  drule_all l3_asl_BigEndian >> strip_tac >> simp[bindS, returnS] >>
  qmatch_goalsub_abbrev_tac `if _ then _ else mem` >>
  simp[Mem_def, CheckAlignment_def, Aligned_def] >>
  ntac 3 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
  simp[state_transformerTheory.BIND_DEF] >>
  simp[BigEndianReverse_def] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
  map_every (rewrite_tac o single) [
    GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
  simp[reverse_endianness0_def] >>
  `mem = mem_dword l3.MEM addr` by (
    unabbrev_all_tac >> simp[mem_dword_def] >> blastLib.BBLAST_TAC) >>
  simp[mem_dword_def] >> IF_CASES_TAC >> gvs[] >> blastLib.BBLAST_TAC
QED

Theorem l3_asl_Mem_read0_4_AccType_IFETCH:
  ∀l3 asl addr. state_rel l3 asl ∧ asl_sys_regs_ok asl ∧
    ((SCTLR l3).A ⇒ Aligned (addr, 4)) ⇒
  Mem_read0 addr 4 AccType_IFETCH asl =
  returnS (FST (Mem (addr,4,AccType_IFETCH) l3)) asl : word32 res
Proof
  rw[] >> simp[Mem_read0_def, AArch64_CheckAlignment_def] >>
  simp[sail2_state_monadTheory.undefined_boolS_def, undefined_Constraint_def,
       ConstrainUnpredictable_def] >>
  simp[l3_asl_Align, asl_word_rws] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[EL_MAP, sail2_valuesTheory.just_list_def, el_w2v] >>
  drule_all SCTLR_read__1 >> strip_tac >>
  drule $ INST_TYPE [gamma |-> ``:word32``] returnS_bindS >>
  simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `foo ' 1` >>
  `foo ' 1 = (SCTLR l3).A` by (
    unabbrev_all_tac >> simp[reg'SCTLRType_def] >> CASE_TAC >> simp[] >>
    gvs[SCTLR_def, TranslationRegime_def] >>
    Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >> blastLib.BBLAST_TAC) >>
  simp[Once $ GSYM COND_RAND] >> ntac 2 $ pop_assum kall_tac >>
  IF_CASES_TAC >- gvs[Aligned_def] >>
  pop_assum mp_tac >> simp[DISJ_EQ_IMP] >> strip_tac >> gvs[] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    simp[AArch64_MemSingle_read_def, l3_asl_Align] >>
    qspecl_then [`addr`,`AccType_IFETCH`,`F`,`T`,`4`,`asl`]
      assume_tac AArch64_TranslateAddress >> gvs[] >>
    drule $ INST_TYPE [gamma |-> ``:word32``] returnS_bindS >>
    simp[] >> disch_then kall_tac >>
    qspecl_then [`AccType_IFETCH`,`asl`] mp_tac CreateAccessDescriptor >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
    qspec_then `asl` mp_tac IsSecure >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
    ntac 2 $ simp[Once returnS] >> simp[HaveMTEExt] >>
    qpat_abbrev_tac `addr = _.FullAddress_address` >>
    qspecl_then [`addr`,`AccType_IFETCH`,`asl`] mp_tac AArch64_AccessIsTagChecked >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
    drule $ INST_TYPE [gamma |-> ``:word32``] returnS_bindS >>
    simp[] >> disch_then kall_tac >>
    qmatch_goalsub_abbrev_tac `Mem_read _ _ accdesc` >>
    qspecl_then [`l3.MEM`,`asl`,`addrdesc`,`accdesc`] mp_tac l3_asl_Mem_read_4 >>
    impl_tac >- state_rel_tac[] >> rw[] >>
    drule $ INST_TYPE [gamma |-> ``:word32``] returnS_bindS >>
    simp[] >> disch_then kall_tac >>
    drule_all l3_asl_BigEndian >> strip_tac >>
    drule $ INST_TYPE [gamma |-> ``:word32``] returnS_bindS >>
    simp[] >> disch_then kall_tac >>
    simp[Mem_def, CheckAlignment_def, Aligned_def] >>
    ntac 3 (ntac 4 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    simp[BigEndianReverse_def] >>
    rewrite_tac[GSYM APPEND_ASSOC] >>
    DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
    map_every (rewrite_tac o single) [
      GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
    simp[reverse_endianness0_def] >>
    IF_CASES_TAC >> gvs[] >> simp[returnS] >>
    WORD_DECIDE_TAC
    ) >>
  simp[AArch64_MemSingle_read_def, l3_asl_Align, Align_def] >>
  qspecl_then [`addr`,`AccType_IFETCH`,`F`,`F`,`1`,`asl`]
    assume_tac AArch64_TranslateAddress >> gvs[] >>
  drule $ INST_TYPE [gamma |-> ``:word32``] returnS_bindS >>
  simp[] >> disch_then kall_tac >>
  qspecl_then [`AccType_IFETCH`,`asl`] mp_tac CreateAccessDescriptor >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
  qspec_then `asl` mp_tac IsSecure >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
  ntac 2 $ simp[Once returnS] >> simp[HaveMTEExt] >>
  `∀addr. AArch64_AccessIsTagChecked addr AccType_IFETCH asl = returnS F asl` by (
    rw[] >> irule AArch64_AccessIsTagChecked >> gvs[asl_sys_regs_ok_def]) >>
  simp[Once bindS, Once returnS] >>
  qspecl_then [`l3.MEM`,`asl`] mp_tac l3_asl_Mem_read_1 >>
  impl_tac >- state_rel_tac[] >> rw[] >>
  simp[Once bindS, Once returnS] >>
  ntac 4 $ simp[Once sail2_valuesAuxiliaryTheory.index_list_rw] >>
  ntac 4 $ simp[Once sail2_stateAuxiliaryTheory.foreachS_rw] >>
  simp[GSYM bit_field_insert_def] >>
  qpat_abbrev_tac `addr = _.FullAddress_address` >>
  qmatch_goalsub_abbrev_tac `word_modify bar _` >>
  `word_modify bar : word64 -> word64 = bit_field_insert 7 0 (l3.MEM addr)` by (
      simp[Abbr `bar`, bit_field_insert_def]) >>
  simp[Abbr `bar`] >>
  map_every (fn qt =>
    qspecl_then [qt,`AccType_IFETCH`,`F`,`F`,`1`,`asl`]
      strip_assume_tac AArch64_TranslateAddress)
  [`addr + i2w 1`,`addr + i2w 2`,`addr + i2w 3`] >>
  gvs $ map (EVAL o Term) [`i2w 1`,`i2w 2`,`i2w 3`,`i2w 4`,`i2w 5`,`i2w 6`,`i2w 7`] >>
  ntac 3 (
    simp[Once returnS, Once bindS] >>
    simp[Once returnS, Once bindS] >>
    simp[Once returnS, Once bindS] >>
    simp[Once returnS] >>
    simp[Once returnS, Once bindS] >>
    simp[Once returnS, Once bindS]
    ) >>
  drule_all l3_asl_BigEndian >> strip_tac >> simp[bindS, returnS] >>
  qmatch_goalsub_abbrev_tac `if _ then _ else mem` >>
  simp[Mem_def, CheckAlignment_def, Aligned_def] >>
  ntac 3 (ntac 4 $ simp[Once state_transformerTheory.FOR_def]) >>
  simp[state_transformerTheory.BIND_DEF] >>
  simp[BigEndianReverse_def] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
  map_every (rewrite_tac o single) [
    GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
  simp[reverse_endianness0_def] >>
  `mem = l3.MEM (addr + 3w) @@ l3.MEM (addr + 2w) @@
          l3.MEM (addr + 1w) @@ l3.MEM addr` by (
    unabbrev_all_tac >> blastLib.BBLAST_TAC) >>
  simp[] >> IF_CASES_TAC >> simp[] >> blastLib.BBLAST_TAC
QED

(**)

Theorem Mem_set_1:
  ∀asl addrdesc a w:word8. asl_sys_regs_ok asl ⇒
    Mem_set addrdesc 1 a w asl = returnS () $ asl with
    <|memstate :=
            asl.memstate |+
            (w2n addrdesc.AddressDescriptor_paddress.FullAddress_address
              MOD dimword(:64), MAP bitU_of_bool $ w2v w);
      tagstate :=
        asl.tagstate |+
        (w2n addrdesc.AddressDescriptor_paddress.FullAddress_address
          MOD dimword(:64),B0) |>
Proof
  rw[Mem_set_def] >>
  simp[
    sail2_state_monadTheory.undefined_boolS_def, undefined_FaultRecord_def,
    undefined_MemoryAttributes_def, undefined_FullAddress_def,
    undefined_Fault_def, undefined_AccType_def,
    preludeTheory.undefined_int_def, preludeTheory.undefined_unit_def
    ] >>
  simp[asl_sys_reg_rws] >>
  simp[Once returnS, Once bindS] >> IF_CASES_TAC >> gvs[]
  >- (irule FALSITY >> gvs[asl_sys_regs_ok_def]) >>
  simp[
    preludeTheory.WriteMemory_def,
    sail2_state_monadTheory.write_memS_def,
    sail2_state_monadTheory.write_memtS_def,
    sail2_valuesTheory.mem_bytes_of_bits_def,
    sail2_valuesTheory.bytes_of_bits_def,
    asl_word_rws, w2n_w2w
    ] >>
  simp[byte_chunks_MAP, optionTheory.OPTION_MAP_COMPOSE] >>
  DEP_REWRITE_TAC[byte_chunks_ByteList] >> simp[] >>
  simp[
    sail2_state_monadTheory.write_memt_bytesS_def,
    sail2_state_monadTheory.updateS_def,
    bindS, returnS, seqS
    ] >>
  simp[sail2_state_monadTheory.put_mem_bytes_def, list_combine]
QED

Theorem AArch64_MemSingle_set_1:
  ∀asl addr flag val:word8. asl_sys_regs_ok asl ⇒
    ∃v. AArch64_MemSingle_set addr 1 AccType_NORMAL flag val asl =
      (write_regS exclusive_block_address_ref v (asl with
        <|memstate :=
            asl.memstate |+
              (w2n addr MOD dimword(:64),MAP bitU_of_bool (w2v val));
          tagstate :=
            asl.tagstate |+ (w2n addr MOD dimword(:64),B0)|>))
Proof
  rw[AArch64_MemSingle_set_def, l3_asl_Align, Align_def] >>
  qspecl_then [`addr`,`AccType_NORMAL`,`T`,`flag`,`1`,`asl`]
    assume_tac AArch64_TranslateAddress >> gvs[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `seqS a b` >>
  `∃v. a asl = write_regS exclusive_block_address_ref v asl` by (
    unabbrev_all_tac >> simp[COND_RATOR] >>
    simp[ProcessorID_def, asl_reg_rws, MPIDR_EL1_ref_def, bindS, returnS] >>
    simp[ClearExclusiveByAddress_def, asl_reg_rws, bindS, returnS] >>
    simp[GetExclusiveBlockAddress_def, exclusive_block_address_ref_def] >>
    simp[COND_RATOR] >> rw[returnS]
    >- irule_at Any EQ_REFL
    >- (
      simp[sail2_state_monadTheory.sequential_state_component_equality] >>
      simp[regstate_component_equality, FUN_EQ_THM] >>
      qexists_tac `asl.regstate.bitvector_64_dec_reg "__exclusive_block_address"` >>
      rw[]
      )
    >- (
      simp[sail2_state_monadTheory.sequential_state_component_equality] >>
      simp[regstate_component_equality, FUN_EQ_THM] >>
      qexists_tac `asl.regstate.bitvector_64_dec_reg "__exclusive_block_address"` >>
      rw[]
      )
    ) >>
  simp[Abbr `b`, Once seqS, Once returnS, asl_reg_rws] >>
  simp[exclusive_block_address_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl0 : regstate sequential_state` >>
  `asl_sys_regs_ok asl0` by (unabbrev_all_tac >> gvs[asl_sys_regs_ok_def]) >>
  qspecl_then [`AccType_NORMAL`,`asl0`] mp_tac CreateAccessDescriptor >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >> simp[Once bindS] >>
  qspec_then `asl0` mp_tac IsSecure >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >> simp[Once bindS] >>
  ntac 2 $ simp[Once returnS] >>
  `∀addr. AArch64_AccessIsTagChecked addr AccType_NORMAL asl0 = returnS F asl0` by (
    rw[] >> irule AArch64_AccessIsTagChecked >> gvs[asl_sys_regs_ok_def]) >>
  simp[Once bindS, Once returnS] >>
  qmatch_goalsub_abbrev_tac `Mem_set _ _ accdesc _` >>
  drule Mem_set_1 >> disch_then $ qspecl_then [`addrdesc`,`accdesc`,`val`] assume_tac >>
  simp[returnS] >> unabbrev_all_tac >> simp[] >> irule_at Any EQ_REFL
QED

Theorem l3_asl_Mem_set0_1_AccType_NORMAL:
  ∀l3 asl addr (val : word8) l3'.
    state_rel l3 asl ∧ asl_sys_regs_ok asl ∧
    write'Mem (val, addr, 1, AccType_NORMAL) l3 = l3' ∧
    l3'.exception = NoException
  ⇒ ∃asl'.
      Mem_set0 addr 1 AccType_NORMAL val asl = returnS () asl' ∧
      state_rel l3' asl' ∧
      asl_sys_regs_ok asl'
Proof
  rw[] >> simp[Mem_set0_def, AArch64_CheckAlignment_def] >>
  simp[sail2_state_monadTheory.undefined_boolS_def, undefined_Constraint_def,
       ConstrainUnpredictable_def] >>
  simp[l3_asl_Align, asl_word_rws] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[EL_MAP, sail2_valuesTheory.just_list_def, el_w2v] >>
  drule_all l3_asl_BigEndian >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule_all SCTLR_read__1 >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `foo ' 1` >>
  `foo ' 1 = (SCTLR l3).A` by (
    unabbrev_all_tac >> simp[reg'SCTLRType_def] >> CASE_TAC >> simp[] >>
    gvs[SCTLR_def, TranslationRegime_def] >>
    Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >> blastLib.BBLAST_TAC) >>
  simp[Once $ GSYM COND_RAND] >> ntac 2 $ pop_assum kall_tac >>
  simp[Align_def, reverse_endianness0_def] >>
  drule AArch64_MemSingle_set_1 >>
  disch_then $ qspecl_then [`addr`,`T`,`val`] assume_tac >> gvs[] >>
  simp[asl_reg_rws, exclusive_block_address_ref_def, returnS] >>
  reverse conj_tac >- gvs[asl_sys_regs_ok_def] >>
  simp[write'Mem_def] >>
  simp[Once state_transformerTheory.FOR_def] >>
  simp[CheckAlignment_def, Aligned_def, Align_def, BigEndianReverse_def, fields] >>
  gvs[state_rel_def] >> rewrite_tac[CONJ_ASSOC] >> conj_tac >- state_rel_tac[] >>
  gvs[mem_rel_def, FLOOKUP_UPDATE_ALT, APPLY_UPDATE_ALT_THM] >> gen_tac >>
  last_x_assum $ qspec_then `w` assume_tac >> gvs[] >> rw[]
  >- (irule_at Any EQ_REFL >> simp[])
  >- (irule FALSITY >> pop_assum mp_tac >> WORD_DECIDE_TAC)
  >- (irule FALSITY >> pop_assum mp_tac >> WORD_DECIDE_TAC)
  >- (irule_at Any EQ_REFL >> simp[])
QED

Theorem l3_asl_Mem_set0_4_AccType_NORMAL:
  ∀l3 asl addr (val : word32) l3'.
    state_rel l3 asl ∧ asl_sys_regs_ok asl ∧
    write'Mem (val, addr, 4, AccType_NORMAL) l3 = l3' ∧
    l3'.exception = NoException
  ⇒ ∃asl'.
      Mem_set0 addr 4 AccType_NORMAL val asl = returnS () asl' ∧
      state_rel l3' asl' ∧
      asl_sys_regs_ok asl'
Proof
  rw[] >> simp[Mem_set0_def, AArch64_CheckAlignment_def] >>
  simp[sail2_state_monadTheory.undefined_boolS_def, undefined_Constraint_def,
       ConstrainUnpredictable_def] >>
  simp[l3_asl_Align, asl_word_rws] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[EL_MAP, sail2_valuesTheory.just_list_def, el_w2v] >>
  drule_all l3_asl_BigEndian >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule_all SCTLR_read__1 >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `foo ' 1` >>
  `foo ' 1 = (SCTLR l3).A` by (
    unabbrev_all_tac >> simp[reg'SCTLRType_def] >> CASE_TAC >> simp[] >>
    gvs[SCTLR_def, TranslationRegime_def] >>
    Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >> blastLib.BBLAST_TAC) >>
  simp[Once $ GSYM COND_RAND] >> ntac 2 $ pop_assum kall_tac >>
  `(SCTLR l3).A ⇒ addr = Align (addr, 4)` by (
    CCONTR_TAC >> gvs[] >>
    qpat_x_assum `_.exception = NoException` mp_tac >> simp[write'Mem_def] >>
    ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    simp[CheckAlignment_def, Aligned_def, raise'exception_def] >>
    IF_CASES_TAC >> gvs[]) >>
  IF_CASES_TAC >- gvs[] >> pop_assum kall_tac >> simp[] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    simp[AArch64_MemSingle_set_def, l3_asl_Align] >>
    qspecl_then [`addr`,`AccType_NORMAL`,`T`,`T`,`4`,`asl`]
      assume_tac AArch64_TranslateAddress >> gvs[] >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qmatch_goalsub_abbrev_tac `seqS x _` >>
    `∃asl1. x asl = returnS () asl1 ∧ state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (
      simp[Abbr `x`] >> reverse $ rw[] >- simp[returnS] >>
      simp[ProcessorID_def, asl_reg_rws, bindS, returnS] >>
      simp[ClearExclusiveByAddress_def, asl_reg_rws, bindS, returnS] >>
      simp[GetExclusiveBlockAddress_def, COND_RATOR, returnS] >>
      IF_CASES_TAC >> simp[exclusive_block_address_ref_def] >>
      state_rel_tac[]) >>
    simp[Once seqS, Once returnS] >>
    qpat_x_assum `x _ = _` kall_tac >> gvs[Abbr `x`] >>
    qspecl_then [`AccType_NORMAL`,`asl1`] mp_tac CreateAccessDescriptor >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >> simp[Once bindS] >>
    qspec_then `asl1` mp_tac IsSecure >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >> simp[Once bindS] >>
    ntac 2 $ simp[Once returnS] >>
    qpat_abbrev_tac `addr = _.FullAddress_address` >>
    qspecl_then [`addr`,`AccType_NORMAL`,`asl1`] mp_tac AArch64_AccessIsTagChecked >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qmatch_goalsub_abbrev_tac `Mem_set _ _ accdesc` >>
    simp[Mem_set_def] >>
    simp[
      sail2_state_monadTheory.undefined_boolS_def, undefined_FaultRecord_def,
      undefined_MemoryAttributes_def, undefined_FullAddress_def,
      undefined_Fault_def, undefined_AccType_def,
      preludeTheory.undefined_int_def, preludeTheory.undefined_unit_def
      ] >>
    simp[asl_sys_reg_rws] >>
    simp[Once returnS, Once bindS] >> IF_CASES_TAC >> gvs[]
    >- (irule FALSITY >> gvs[asl_sys_regs_ok_def]) >>
    simp[
      preludeTheory.WriteMemory_def,
      sail2_state_monadTheory.write_memS_def,
      sail2_state_monadTheory.write_memtS_def,
      sail2_valuesTheory.mem_bytes_of_bits_def,
      sail2_valuesTheory.bytes_of_bits_def,
      asl_word_rws, w2n_w2w
      ] >>
    simp[byte_chunks_MAP, optionTheory.OPTION_MAP_COMPOSE] >>
    DEP_REWRITE_TAC[byte_chunks_ByteList] >> simp[] >>
    simp[
      sail2_state_monadTheory.write_memt_bytesS_def,
      sail2_state_monadTheory.updateS_def,
      bindS, returnS, seqS
      ] >>
    simp[sail2_state_monadTheory.put_mem_bytes_def] >>
    reverse conj_tac >- gvs[asl_sys_regs_ok_def] >>
    `∃mem. write'Mem (val,addr,4,AccType_NORMAL) l3 = l3 with MEM := mem` by (
      simp[write'Mem_def] >>
      ntac 8 $ simp[Once state_transformerTheory.FOR_def] >>
      simp[state_transformerTheory.BIND_DEF] >>
      simp[CheckAlignment_def, Aligned_def] >> irule_at Any EQ_REFL) >>
    simp[] >> gvs[state_rel_def] >>
    simp[list_combine, LENGTH_ByteList] >>
    pop_assum mp_tac >> simp[write'Mem_def] >>
    ntac 8 $ simp[Once state_transformerTheory.FOR_def] >>
    simp[state_transformerTheory.BIND_DEF] >>
    simp[CheckAlignment_def, Aligned_def] >>
    simp[arm8_state_component_equality] >> strip_tac >> gvs[] >>
    qpat_x_assum `mem_rel _ _ _` mp_tac >> rpt $ pop_assum kall_tac >>
    simp[word_add_def] >> reverse $ rw[]
    >- (
      `w2v val =
        w2v ((31 >< 24) val) ++ w2v ((23 >< 16) val) ++
        w2v ((15 >< 8) val) ++ w2v ((7 >< 0) val)` by (
        rewrite_tac[GSYM APPEND_ASSOC] >>
        map_every (rewrite_tac o single) [
          GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
        AP_TERM_TAC >> blastLib.BBLAST_TAC) >>
      pop_assum SUBST_ALL_TAC >>
      rewrite_tac[GSYM APPEND_ASSOC] >>
      DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
      simp[field_concat_left, field_concat_right] >> rw[mem_rel_def]
      >- (simp[FLOOKUP_UPDATE] >> rpt IF_CASES_TAC >> simp[] >> gvs[mem_rel_def]) >>
      simp[FLOOKUP_UPDATE_ALT, APPLY_UPDATE_ALT_THM] >> simp[Once CONJ_SYM] >>
      ntac 3 (
        IF_CASES_TAC >> simp[] >> gvs[]
        >- (
          rpt (IF_CASES_TAC >> gvs[]) >>
          irule_at Any EQ_REFL >> simp[] >> rpt AP_TERM_TAC >>
          SUBST_ALL_TAC $ GSYM $ mk_blast_thm ``val : word32`` >> EVAL_TAC
          )
        ) >>
      IF_CASES_TAC >> gvs[]
      >- (
        reverse $ rpt IF_CASES_TAC >> gvs[]
        >- (
          irule FALSITY >> pop_assum mp_tac >> simp[] >>
          qspec_then `addr` mp_tac w2n_lt >> simp[]
          )
        >- (Q.REFINE_EXISTS_TAC `w2v (_ : word8)` >> simp[]) >>
        irule FALSITY >> ARITH_TAC
        )
      >- (
        reverse $ rpt IF_CASES_TAC >> gvs[]
        >- (
          gvs[mem_rel_def] >> first_x_assum $ qspec_then `w` mp_tac >> rw[] >>
          goal_assum $ drule_at Any >> simp[]
          )
        >- (irule FALSITY >> qspec_then `addr` assume_tac w2n_lt >> gvs[]) >>
        irule FALSITY >>
        qmatch_asmsub_abbrev_tac `w2n _ = (w2n _ + offset) MOD _` >>
        qpat_x_assum `_ ≠ _ (_ + offset)` mp_tac >> simp[] >>
        once_rewrite_tac[GSYM w2n_11] >> unabbrev_all_tac >>
        first_assum SUBST1_TAC >> simp[]
        )
      )
    >- (
      simp[w2v_reverse_endianness0_32] >>
      `w2v val =
        w2v ((31 >< 24) val) ++ w2v ((23 >< 16) val) ++
        w2v ((15 >< 8) val) ++ w2v ((7 >< 0) val)` by (
        rewrite_tac[GSYM APPEND_ASSOC] >>
        map_every (rewrite_tac o single) [
          GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
        AP_TERM_TAC >> blastLib.BBLAST_TAC) >>
      pop_assum SUBST_ALL_TAC >>
      simp[BigEndianReverse_def] >>
      rewrite_tac[GSYM APPEND_ASSOC] >>
      DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
      rewrite_tac[GSYM APPEND_ASSOC] >>
      DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
      simp[field_concat_left, field_concat_right] >> rw[mem_rel_def]
      >- (simp[FLOOKUP_UPDATE] >> rpt IF_CASES_TAC >> simp[] >> gvs[mem_rel_def]) >>
      simp[FLOOKUP_UPDATE_ALT, APPLY_UPDATE_ALT_THM] >> simp[Once CONJ_SYM] >>
      ntac 3 (
        IF_CASES_TAC >> simp[] >> gvs[]
        >- (
          rpt (IF_CASES_TAC >> gvs[]) >>
          irule_at Any EQ_REFL >> simp[] >> rpt AP_TERM_TAC >>
          SUBST_ALL_TAC $ GSYM $ mk_blast_thm ``val : word32`` >> EVAL_TAC
          )
        ) >>
      IF_CASES_TAC >> gvs[]
      >- (
        reverse $ rpt IF_CASES_TAC >> gvs[]
        >- (
          irule FALSITY >> pop_assum mp_tac >> simp[] >>
          qspec_then `addr` mp_tac w2n_lt >> simp[]
          )
        >- (Q.REFINE_EXISTS_TAC `w2v (_ : word8)` >> simp[]) >>
        irule FALSITY >> ARITH_TAC
        )
      >- (
        reverse $ rpt IF_CASES_TAC >> gvs[]
        >- (
          gvs[mem_rel_def] >> first_x_assum $ qspec_then `w` mp_tac >> rw[] >>
          goal_assum $ drule_at Any >> simp[]
          )
        >- (irule FALSITY >> qspec_then `addr` assume_tac w2n_lt >> gvs[]) >>
        irule FALSITY >>
        qmatch_asmsub_abbrev_tac `w2n _ = (w2n _ + offset) MOD _` >>
        qpat_x_assum `_ ≠ _ (_ + offset)` mp_tac >> simp[] >>
        once_rewrite_tac[GSYM w2n_11] >> unabbrev_all_tac >>
        first_assum SUBST1_TAC >> simp[]
        )
      )
    ) >>
  ntac 8 $ simp[Once sail2_valuesAuxiliaryTheory.index_list_rw] >>
  ntac 8 $ simp[Once sail2_stateAuxiliaryTheory.foreachS_rw] >>
  map_every (simp o single o EVAL o Term)
    [`i2w 1`,`i2w 2`,`i2w 3`,`i2w 4`,`i2w 5`,`i2w 6`,`i2w 7`] >>
  qmatch_goalsub_abbrev_tac `(_ >< _) rv` >>
  drule AArch64_MemSingle_set_1 >>
  disch_then $ qspecl_then [`addr`,`F`,`(7 >< 0) rv`] assume_tac >> gvs[] >>
  simp[Once seqS, asl_reg_rws, exclusive_block_address_ref_def, Once returnS] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `asl_sys_regs_ok asl1` by (
    qpat_x_assum `asl_sys_regs_ok _` mp_tac >> simp[Abbr `asl1`, asl_sys_regs_ok_def]) >>
  drule AArch64_MemSingle_set_1 >>
  disch_then $ qspecl_then [`addr + 1w`,`F`,`(15 >< 8) rv`] assume_tac >> gvs[] >>
  simp[Once bindS, asl_reg_rws, exclusive_block_address_ref_def, Once returnS] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `asl_sys_regs_ok asl2` by (
    qpat_x_assum `asl_sys_regs_ok _` mp_tac >> simp[Abbr `asl2`, asl_sys_regs_ok_def]) >>
  drule AArch64_MemSingle_set_1 >>
  disch_then $ qspecl_then [`addr + 2w`,`F`,`(23 >< 16) rv`] assume_tac >> gvs[] >>
  simp[Once bindS, asl_reg_rws, exclusive_block_address_ref_def, Once returnS] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `asl_sys_regs_ok asl3` by (
    qpat_x_assum `asl_sys_regs_ok _` mp_tac >> simp[Abbr `asl3`, asl_sys_regs_ok_def]) >>
  drule AArch64_MemSingle_set_1 >>
  disch_then $ qspecl_then [`addr + 3w`,`F`,`(31 >< 24) rv`] assume_tac >> gvs[] >>
  simp[Once bindS, asl_reg_rws, exclusive_block_address_ref_def, Once returnS] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl4 : regstate sequential_state` >>
  `asl_sys_regs_ok asl4` by (
    qpat_x_assum `asl_sys_regs_ok _` mp_tac >> simp[Abbr `asl4`, asl_sys_regs_ok_def]) >>
  simp[returnS] >>
  `CheckAlignment (addr,4,AccType_NORMAL,T) l3 = l3` by (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    simp[write'Mem_def] >>
    ntac 8 $ simp[Once state_transformerTheory.FOR_def] >>
    simp[state_transformerTheory.BIND_DEF] >>
    gvs[CheckAlignment_def] >> IF_CASES_TAC >> gvs[] >>
    simp[raise'exception_def] >> rw[]) >>
  qpat_x_assum `asl_sys_regs_ok asl` mp_tac >>
  rpt $ qpat_x_assum `asl_sys_regs_ok _` kall_tac >>
  rpt $ qpat_x_assum `AArch64_MemSingle_set _ _ _ _ _ _ = _` kall_tac >>
  unabbrev_all_tac >> simp[] >> strip_tac >>
  simp[write'Mem_def] >>
  ntac 8 $ simp[Once state_transformerTheory.FOR_def] >>
  simp[state_transformerTheory.BIND_DEF] >> simp[word_add_def] >>
  reverse $ IF_CASES_TAC >> simp[]
  >- (
    `w2v val =
      w2v ((31 >< 24) val) ++ w2v ((23 >< 16) val) ++
      w2v ((15 >< 8) val) ++ w2v ((7 >< 0) val)` by (
      rewrite_tac[GSYM APPEND_ASSOC] >>
      map_every (rewrite_tac o single) [
        GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
      AP_TERM_TAC >> blastLib.BBLAST_TAC) >>
    pop_assum SUBST_ALL_TAC >>
    rewrite_tac[GSYM APPEND_ASSOC] >>
    DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
    simp[field_concat_left, field_concat_right] >>
    `v2w (field 7 0 (w2v ((31 >< 24) val : word8))) : word8 = (31 >< 24) val` by (
      SUBST1_TAC $ GSYM $ mk_blast_thm ``val : word32`` >> EVAL_TAC) >>
    simp[] >> pop_assum kall_tac >> gvs[state_rel_def] >>
    simp[CONJ_ASSOC] >> conj_tac >- state_rel_tac[] >>
    rw[mem_rel_def]
    >- (simp[FLOOKUP_UPDATE] >> rpt IF_CASES_TAC >> simp[] >> gvs[mem_rel_def]) >>
    simp[FLOOKUP_UPDATE_ALT, APPLY_UPDATE_ALT_THM] >> simp[Once CONJ_SYM] >>
    ntac 3 (
      IF_CASES_TAC >> simp[] >> gvs[]
      >- (
        rpt (IF_CASES_TAC >> gvs[]) >>
        irule_at Any EQ_REFL >> simp[] >> rpt AP_TERM_TAC >>
        SUBST_ALL_TAC $ GSYM $ mk_blast_thm ``val : word32`` >> EVAL_TAC
        )
      ) >>
    IF_CASES_TAC >> gvs[]
    >- (
      reverse $ rpt IF_CASES_TAC >> gvs[]
      >- (
        irule FALSITY >> pop_assum mp_tac >> simp[] >>
        qspec_then `addr` mp_tac w2n_lt >> simp[]
        )
      >- (Q.REFINE_EXISTS_TAC `w2v (_ : word8)` >> simp[]) >>
      irule FALSITY >> ARITH_TAC
      )
    >- (
      reverse $ rpt IF_CASES_TAC >> gvs[]
      >- (
        gvs[mem_rel_def] >> first_x_assum $ qspec_then `w` mp_tac >> rw[] >>
        goal_assum $ drule_at Any >> simp[]
        )
      >- (irule FALSITY >> qspec_then `addr` assume_tac w2n_lt >> gvs[]) >>
      irule FALSITY >>
      qmatch_asmsub_abbrev_tac `w2n _ = (w2n _ + offset) MOD _` >>
      qpat_x_assum `_ ≠ _ (_ + offset)` mp_tac >> simp[] >>
      once_rewrite_tac[GSYM w2n_11] >> unabbrev_all_tac >>
      first_assum SUBST1_TAC >> simp[]
      )
    )
  >- (
    simp[extract_bits_reverse_endianness0_32] >>
    `w2v val =
      w2v ((31 >< 24) val) ++ w2v ((23 >< 16) val) ++
      w2v ((15 >< 8) val) ++ w2v ((7 >< 0) val)` by (
      rewrite_tac[GSYM APPEND_ASSOC] >>
      map_every (rewrite_tac o single) [
        GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
      AP_TERM_TAC >> blastLib.BBLAST_TAC) >>
    pop_assum SUBST_ALL_TAC >>
    simp[BigEndianReverse_def] >>
    rewrite_tac[GSYM APPEND_ASSOC] >>
    DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
    rewrite_tac[GSYM APPEND_ASSOC] >>
    DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
    simp[field_concat_left, field_concat_right] >>
    `v2w (field 7 0 (w2v ((31 >< 24) val : word8))) : word8 = (31 >< 24) val` by (
      SUBST1_TAC $ GSYM $ mk_blast_thm ``val : word32`` >> EVAL_TAC) >>
    simp[] >> pop_assum kall_tac >> gvs[state_rel_def] >>
    simp[CONJ_ASSOC] >> conj_tac >- state_rel_tac[] >>
    rw[mem_rel_def]
    >- (simp[FLOOKUP_UPDATE] >> rpt IF_CASES_TAC >> simp[] >> gvs[mem_rel_def]) >>
    simp[FLOOKUP_UPDATE_ALT, APPLY_UPDATE_ALT_THM] >> simp[Once CONJ_SYM] >>
    ntac 3 (
      IF_CASES_TAC >> simp[] >> gvs[]
      >- (
        rpt (IF_CASES_TAC >> gvs[]) >>
        irule_at Any EQ_REFL >> simp[] >> rpt AP_TERM_TAC >>
        SUBST_ALL_TAC $ GSYM $ mk_blast_thm ``val : word64`` >> EVAL_TAC
        )
      ) >>
    IF_CASES_TAC >> gvs[]
    >- (
      reverse $ rpt IF_CASES_TAC >> gvs[]
      >- (
        irule FALSITY >> pop_assum mp_tac >> simp[] >>
        qspec_then `addr` mp_tac w2n_lt >> simp[]
        )
      >- (Q.REFINE_EXISTS_TAC `w2v (_ : word8)` >> simp[]) >>
      irule FALSITY >> ARITH_TAC
      )
    >- (
      reverse $ rpt IF_CASES_TAC >> gvs[]
      >- (
        gvs[mem_rel_def] >> first_x_assum $ qspec_then `w` mp_tac >> rw[] >>
        goal_assum $ drule_at Any >> simp[]
        )
      >- (irule FALSITY >> qspec_then `addr` assume_tac w2n_lt >> gvs[]) >>
      irule FALSITY >>
      qmatch_asmsub_abbrev_tac `w2n _ = (w2n _ + offset) MOD _` >>
      qpat_x_assum `_ ≠ _ (_ + offset)` mp_tac >> simp[] >>
      once_rewrite_tac[GSYM w2n_11] >> unabbrev_all_tac >>
      first_assum SUBST1_TAC >> simp[]
      )
    )
QED

Theorem l3_asl_Mem_set0_8_AccType_NORMAL:
  ∀l3 asl addr (val : word64) l3'.
    state_rel l3 asl ∧ asl_sys_regs_ok asl ∧
    write'Mem (val, addr, 8, AccType_NORMAL) l3 = l3' ∧
    l3'.exception = NoException
  ⇒ ∃asl'.
      Mem_set0 addr 8 AccType_NORMAL val asl = returnS () asl' ∧
      state_rel l3' asl' ∧
      asl_sys_regs_ok asl'
Proof
  rw[] >> simp[Mem_set0_def, AArch64_CheckAlignment_def] >>
  simp[sail2_state_monadTheory.undefined_boolS_def, undefined_Constraint_def,
       ConstrainUnpredictable_def] >>
  simp[l3_asl_Align, asl_word_rws] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[EL_MAP, sail2_valuesTheory.just_list_def, el_w2v] >>
  drule_all l3_asl_BigEndian >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule_all SCTLR_read__1 >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `foo ' 1` >>
  `foo ' 1 = (SCTLR l3).A` by (
    unabbrev_all_tac >> simp[reg'SCTLRType_def] >> CASE_TAC >> simp[] >>
    gvs[SCTLR_def, TranslationRegime_def] >>
    Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >> blastLib.BBLAST_TAC) >>
  simp[Once $ GSYM COND_RAND] >> ntac 2 $ pop_assum kall_tac >>
  `(SCTLR l3).A ⇒ addr = Align (addr, 8)` by (
    CCONTR_TAC >> gvs[] >>
    qpat_x_assum `_.exception = NoException` mp_tac >> simp[write'Mem_def] >>
    ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    simp[CheckAlignment_def, Aligned_def, raise'exception_def] >>
    IF_CASES_TAC >> gvs[]) >>
  IF_CASES_TAC >- gvs[] >> pop_assum kall_tac >> simp[] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (
    simp[AArch64_MemSingle_set_def, l3_asl_Align] >>
    qspecl_then [`addr`,`AccType_NORMAL`,`T`,`T`,`8`,`asl`]
      assume_tac AArch64_TranslateAddress >> gvs[] >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qmatch_goalsub_abbrev_tac `seqS x _` >>
    `∃asl1. x asl = returnS () asl1 ∧ state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (
      simp[Abbr `x`] >> reverse $ rw[] >- simp[returnS] >>
      simp[ProcessorID_def, asl_reg_rws, bindS, returnS] >>
      simp[ClearExclusiveByAddress_def, asl_reg_rws, bindS, returnS] >>
      simp[GetExclusiveBlockAddress_def, COND_RATOR, returnS] >>
      IF_CASES_TAC >> simp[exclusive_block_address_ref_def] >>
      state_rel_tac[]) >>
    simp[Once seqS, Once returnS] >>
    qpat_x_assum `x _ = _` kall_tac >> gvs[Abbr `x`] >>
    qspecl_then [`AccType_NORMAL`,`asl1`] mp_tac CreateAccessDescriptor >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >> simp[Once bindS] >>
    qspec_then `asl1` mp_tac IsSecure >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >> simp[Once bindS] >>
    ntac 2 $ simp[Once returnS] >>
    qpat_abbrev_tac `addr = _.FullAddress_address` >>
    qspecl_then [`addr`,`AccType_NORMAL`,`asl1`] mp_tac AArch64_AccessIsTagChecked >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qmatch_goalsub_abbrev_tac `Mem_set _ _ accdesc` >>
    simp[Mem_set_def] >>
    simp[
      sail2_state_monadTheory.undefined_boolS_def, undefined_FaultRecord_def,
      undefined_MemoryAttributes_def, undefined_FullAddress_def,
      undefined_Fault_def, undefined_AccType_def,
      preludeTheory.undefined_int_def, preludeTheory.undefined_unit_def
      ] >>
    simp[asl_sys_reg_rws] >>
    simp[Once returnS, Once bindS] >> IF_CASES_TAC >> gvs[]
    >- (irule FALSITY >> gvs[asl_sys_regs_ok_def]) >>
    simp[
      preludeTheory.WriteMemory_def,
      sail2_state_monadTheory.write_memS_def,
      sail2_state_monadTheory.write_memtS_def,
      sail2_valuesTheory.mem_bytes_of_bits_def,
      sail2_valuesTheory.bytes_of_bits_def,
      asl_word_rws, w2n_w2w
      ] >>
    simp[byte_chunks_MAP, optionTheory.OPTION_MAP_COMPOSE] >>
    DEP_REWRITE_TAC[byte_chunks_ByteList] >> simp[] >>
    simp[
      sail2_state_monadTheory.write_memt_bytesS_def,
      sail2_state_monadTheory.updateS_def,
      bindS, returnS, seqS
      ] >>
    simp[sail2_state_monadTheory.put_mem_bytes_def] >>
    reverse conj_tac >- gvs[asl_sys_regs_ok_def] >>
    `∃mem. write'Mem (val,addr,8,AccType_NORMAL) l3 = l3 with MEM := mem` by (
      simp[write'Mem_def] >>
      ntac 8 $ simp[Once state_transformerTheory.FOR_def] >>
      simp[state_transformerTheory.BIND_DEF] >>
      simp[CheckAlignment_def, Aligned_def] >> irule_at Any EQ_REFL) >>
    simp[] >> gvs[state_rel_def] >>
    simp[list_combine, LENGTH_ByteList] >>
    pop_assum mp_tac >> simp[write'Mem_def] >>
    ntac 8 $ simp[Once state_transformerTheory.FOR_def] >>
    simp[state_transformerTheory.BIND_DEF] >>
    simp[CheckAlignment_def, Aligned_def] >>
    simp[arm8_state_component_equality] >> strip_tac >> gvs[] >>
    qpat_x_assum `mem_rel _ _ _` mp_tac >> rpt $ pop_assum kall_tac >>
    simp[word_add_def] >> reverse $ rw[]
    >- (
      `w2v val =
        w2v ((63 >< 56) val) ++ w2v ((55 >< 48) val) ++ w2v ((47 >< 40) val) ++
        w2v ((39 >< 32) val) ++ w2v ((31 >< 24) val) ++ w2v ((23 >< 16) val) ++
        w2v ((15 >< 8) val) ++ w2v ((7 >< 0) val)` by (
        rewrite_tac[GSYM APPEND_ASSOC] >>
        map_every (rewrite_tac o single) [
          GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
        AP_TERM_TAC >> blastLib.BBLAST_TAC) >>
      pop_assum SUBST_ALL_TAC >>
      rewrite_tac[GSYM APPEND_ASSOC] >>
      DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
      simp[field_concat_left, field_concat_right] >> rw[mem_rel_def]
      >- (simp[FLOOKUP_UPDATE] >> rpt IF_CASES_TAC >> simp[] >> gvs[mem_rel_def]) >>
      simp[FLOOKUP_UPDATE_ALT, APPLY_UPDATE_ALT_THM] >> simp[Once CONJ_SYM] >>
      ntac 7 (
        IF_CASES_TAC >> simp[] >> gvs[]
        >- (
          rpt (IF_CASES_TAC >> gvs[]) >>
          irule_at Any EQ_REFL >> simp[] >> rpt AP_TERM_TAC >>
          SUBST_ALL_TAC $ GSYM $ mk_blast_thm ``val : word64`` >> EVAL_TAC
          )
        ) >>
      IF_CASES_TAC >> gvs[]
      >- (
        reverse $ rpt IF_CASES_TAC >> gvs[]
        >- (
          irule FALSITY >> pop_assum mp_tac >> simp[] >>
          qspec_then `addr` mp_tac w2n_lt >> simp[]
          )
        >- (Q.REFINE_EXISTS_TAC `w2v (_ : word8)` >> simp[]) >>
        irule FALSITY >> ARITH_TAC
        )
      >- (
        reverse $ rpt IF_CASES_TAC >> gvs[]
        >- (
          gvs[mem_rel_def] >> first_x_assum $ qspec_then `w` mp_tac >> rw[] >>
          goal_assum $ drule_at Any >> simp[]
          )
        >- (irule FALSITY >> qspec_then `addr` assume_tac w2n_lt >> gvs[]) >>
        irule FALSITY >>
        qmatch_asmsub_abbrev_tac `w2n _ = (w2n _ + offset) MOD _` >>
        qpat_x_assum `_ ≠ _ (_ + offset)` mp_tac >> simp[] >>
        once_rewrite_tac[GSYM w2n_11] >> unabbrev_all_tac >>
        first_assum SUBST1_TAC >> simp[]
        )
      )
    >- (
      simp[w2v_reverse_endianness0_64] >>
      `w2v val =
        w2v ((63 >< 56) val) ++ w2v ((55 >< 48) val) ++ w2v ((47 >< 40) val) ++
        w2v ((39 >< 32) val) ++ w2v ((31 >< 24) val) ++ w2v ((23 >< 16) val) ++
        w2v ((15 >< 8) val) ++ w2v ((7 >< 0) val)` by (
        rewrite_tac[GSYM APPEND_ASSOC] >>
        map_every (rewrite_tac o single) [
          GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
        AP_TERM_TAC >> blastLib.BBLAST_TAC) >>
      pop_assum SUBST_ALL_TAC >>
      simp[BigEndianReverse_def] >>
      rewrite_tac[GSYM APPEND_ASSOC] >>
      DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
      rewrite_tac[GSYM APPEND_ASSOC] >>
      DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
      simp[field_concat_left, field_concat_right] >> rw[mem_rel_def]
      >- (simp[FLOOKUP_UPDATE] >> rpt IF_CASES_TAC >> simp[] >> gvs[mem_rel_def]) >>
      simp[FLOOKUP_UPDATE_ALT, APPLY_UPDATE_ALT_THM] >> simp[Once CONJ_SYM] >>
      ntac 7 (
        IF_CASES_TAC >> simp[] >> gvs[]
        >- (
          rpt (IF_CASES_TAC >> gvs[]) >>
          irule_at Any EQ_REFL >> simp[] >> rpt AP_TERM_TAC >>
          SUBST_ALL_TAC $ GSYM $ mk_blast_thm ``val : word64`` >> EVAL_TAC
          )
        ) >>
      IF_CASES_TAC >> gvs[]
      >- (
        reverse $ rpt IF_CASES_TAC >> gvs[]
        >- (
          irule FALSITY >> pop_assum mp_tac >> simp[] >>
          qspec_then `addr` mp_tac w2n_lt >> simp[]
          )
        >- (Q.REFINE_EXISTS_TAC `w2v (_ : word8)` >> simp[]) >>
        irule FALSITY >> ARITH_TAC
        )
      >- (
        reverse $ rpt IF_CASES_TAC >> gvs[]
        >- (
          gvs[mem_rel_def] >> first_x_assum $ qspec_then `w` mp_tac >> rw[] >>
          goal_assum $ drule_at Any >> simp[]
          )
        >- (irule FALSITY >> qspec_then `addr` assume_tac w2n_lt >> gvs[]) >>
        irule FALSITY >>
        qmatch_asmsub_abbrev_tac `w2n _ = (w2n _ + offset) MOD _` >>
        qpat_x_assum `_ ≠ _ (_ + offset)` mp_tac >> simp[] >>
        once_rewrite_tac[GSYM w2n_11] >> unabbrev_all_tac >>
        first_assum SUBST1_TAC >> simp[]
        )
      )
    ) >>
  ntac 8 $ simp[Once sail2_valuesAuxiliaryTheory.index_list_rw] >>
  ntac 8 $ simp[Once sail2_stateAuxiliaryTheory.foreachS_rw] >>
  map_every (simp o single o EVAL o Term)
    [`i2w 1`,`i2w 2`,`i2w 3`,`i2w 4`,`i2w 5`,`i2w 6`,`i2w 7`] >>
  qmatch_goalsub_abbrev_tac `(_ >< _) rv` >>
  drule AArch64_MemSingle_set_1 >>
  disch_then $ qspecl_then [`addr`,`F`,`(7 >< 0) rv`] assume_tac >> gvs[] >>
  simp[Once seqS, asl_reg_rws, exclusive_block_address_ref_def, Once returnS] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `asl_sys_regs_ok asl1` by (
    qpat_x_assum `asl_sys_regs_ok _` mp_tac >> simp[Abbr `asl1`, asl_sys_regs_ok_def]) >>
  drule AArch64_MemSingle_set_1 >>
  disch_then $ qspecl_then [`addr + 1w`,`F`,`(15 >< 8) rv`] assume_tac >> gvs[] >>
  simp[Once bindS, asl_reg_rws, exclusive_block_address_ref_def, Once returnS] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `asl_sys_regs_ok asl2` by (
    qpat_x_assum `asl_sys_regs_ok _` mp_tac >> simp[Abbr `asl2`, asl_sys_regs_ok_def]) >>
  drule AArch64_MemSingle_set_1 >>
  disch_then $ qspecl_then [`addr + 2w`,`F`,`(23 >< 16) rv`] assume_tac >> gvs[] >>
  simp[Once bindS, asl_reg_rws, exclusive_block_address_ref_def, Once returnS] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `asl_sys_regs_ok asl3` by (
    qpat_x_assum `asl_sys_regs_ok _` mp_tac >> simp[Abbr `asl3`, asl_sys_regs_ok_def]) >>
  drule AArch64_MemSingle_set_1 >>
  disch_then $ qspecl_then [`addr + 3w`,`F`,`(31 >< 24) rv`] assume_tac >> gvs[] >>
  simp[Once bindS, asl_reg_rws, exclusive_block_address_ref_def, Once returnS] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl4 : regstate sequential_state` >>
  `asl_sys_regs_ok asl4` by (
    qpat_x_assum `asl_sys_regs_ok _` mp_tac >> simp[Abbr `asl4`, asl_sys_regs_ok_def]) >>
  drule AArch64_MemSingle_set_1 >>
  disch_then $ qspecl_then [`addr + 4w`,`F`,`(39 >< 32) rv`] assume_tac >> gvs[] >>
  simp[Once bindS, asl_reg_rws, exclusive_block_address_ref_def, Once returnS] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl5 : regstate sequential_state` >>
  `asl_sys_regs_ok asl5` by (
    qpat_x_assum `asl_sys_regs_ok _` mp_tac >> simp[Abbr `asl5`, asl_sys_regs_ok_def]) >>
  drule AArch64_MemSingle_set_1 >>
  disch_then $ qspecl_then [`addr + 5w`,`F`,`(47 >< 40) rv`] assume_tac >> gvs[] >>
  simp[Once bindS, asl_reg_rws, exclusive_block_address_ref_def, Once returnS] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl6 : regstate sequential_state` >>
  `asl_sys_regs_ok asl6` by (
    qpat_x_assum `asl_sys_regs_ok _` mp_tac >> simp[Abbr `asl6`, asl_sys_regs_ok_def]) >>
  drule AArch64_MemSingle_set_1 >>
  disch_then $ qspecl_then [`addr + 6w`,`F`,`(55 >< 48) rv`] assume_tac >> gvs[] >>
  simp[Once bindS, asl_reg_rws, exclusive_block_address_ref_def, Once returnS] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl7 : regstate sequential_state` >>
  `asl_sys_regs_ok asl7` by (
    qpat_x_assum `asl_sys_regs_ok _` mp_tac >> simp[Abbr `asl7`, asl_sys_regs_ok_def]) >>
  drule AArch64_MemSingle_set_1 >>
  disch_then $ qspecl_then [`addr + 7w`,`F`,`(63 >< 56) rv`] assume_tac >> gvs[] >>
  simp[Once bindS, asl_reg_rws, exclusive_block_address_ref_def, Once returnS] >>
  pop_assum kall_tac >> simp[returnS] >> reverse conj_tac
  >- (pop_assum mp_tac >> rpt $ pop_assum kall_tac >> simp[asl_sys_regs_ok_def]) >>
  `CheckAlignment (addr,8,AccType_NORMAL,T) l3 = l3` by (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    simp[write'Mem_def] >>
    ntac 8 $ simp[Once state_transformerTheory.FOR_def] >>
    simp[state_transformerTheory.BIND_DEF] >>
    gvs[CheckAlignment_def] >> IF_CASES_TAC >> gvs[] >>
    simp[raise'exception_def] >> rw[]) >>
  qpat_x_assum `asl_sys_regs_ok asl` mp_tac >>
  rpt $ qpat_x_assum `asl_sys_regs_ok _` kall_tac >>
  rpt $ qpat_x_assum `AArch64_MemSingle_set _ _ _ _ _ _ = _` kall_tac >>
  unabbrev_all_tac >> simp[] >> strip_tac >>
  simp[write'Mem_def] >>
  ntac 8 $ simp[Once state_transformerTheory.FOR_def] >>
  simp[state_transformerTheory.BIND_DEF] >> simp[word_add_def] >>
  reverse $ IF_CASES_TAC >> simp[]
  >- (
    `w2v val =
      w2v ((63 >< 56) val) ++ w2v ((55 >< 48) val) ++ w2v ((47 >< 40) val) ++
      w2v ((39 >< 32) val) ++ w2v ((31 >< 24) val) ++ w2v ((23 >< 16) val) ++
      w2v ((15 >< 8) val) ++ w2v ((7 >< 0) val)` by (
      rewrite_tac[GSYM APPEND_ASSOC] >>
      map_every (rewrite_tac o single) [
        GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
      AP_TERM_TAC >> blastLib.BBLAST_TAC) >>
    pop_assum SUBST_ALL_TAC >>
    rewrite_tac[GSYM APPEND_ASSOC] >>
    DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
    simp[field_concat_left, field_concat_right] >>
    `v2w (field 7 0 (w2v ((63 >< 56) val : word8))) : word8 = (63 >< 56) val` by (
      SUBST1_TAC $ GSYM $ mk_blast_thm ``val : word64`` >> EVAL_TAC) >>
    simp[] >> pop_assum kall_tac >> gvs[state_rel_def] >>
    simp[CONJ_ASSOC] >> conj_tac >- state_rel_tac[] >>
    rw[mem_rel_def]
    >- (simp[FLOOKUP_UPDATE] >> rpt IF_CASES_TAC >> simp[] >> gvs[mem_rel_def]) >>
    simp[FLOOKUP_UPDATE_ALT, APPLY_UPDATE_ALT_THM] >> simp[Once CONJ_SYM] >>
    ntac 7 (
      IF_CASES_TAC >> simp[] >> gvs[]
      >- (
        rpt (IF_CASES_TAC >> gvs[]) >>
        irule_at Any EQ_REFL >> simp[] >> rpt AP_TERM_TAC >>
        SUBST_ALL_TAC $ GSYM $ mk_blast_thm ``val : word64`` >> EVAL_TAC
        )
      ) >>
    IF_CASES_TAC >> gvs[]
    >- (
      reverse $ rpt IF_CASES_TAC >> gvs[]
      >- (
        irule FALSITY >> pop_assum mp_tac >> simp[] >>
        qspec_then `addr` mp_tac w2n_lt >> simp[]
        )
      >- (Q.REFINE_EXISTS_TAC `w2v (_ : word8)` >> simp[]) >>
      irule FALSITY >> ARITH_TAC
      )
    >- (
      reverse $ rpt IF_CASES_TAC >> gvs[]
      >- (
        gvs[mem_rel_def] >> first_x_assum $ qspec_then `w` mp_tac >> rw[] >>
        goal_assum $ drule_at Any >> simp[]
        )
      >- (irule FALSITY >> qspec_then `addr` assume_tac w2n_lt >> gvs[]) >>
      irule FALSITY >>
      qmatch_asmsub_abbrev_tac `w2n _ = (w2n _ + offset) MOD _` >>
      qpat_x_assum `_ ≠ _ (_ + offset)` mp_tac >> simp[] >>
      once_rewrite_tac[GSYM w2n_11] >> unabbrev_all_tac >>
      first_assum SUBST1_TAC >> simp[]
      )
    )
  >- (
    simp[extract_bits_reverse_endianness0_64] >>
    `w2v val =
      w2v ((63 >< 56) val) ++ w2v ((55 >< 48) val) ++ w2v ((47 >< 40) val) ++
      w2v ((39 >< 32) val) ++ w2v ((31 >< 24) val) ++ w2v ((23 >< 16) val) ++
      w2v ((15 >< 8) val) ++ w2v ((7 >< 0) val)` by (
      rewrite_tac[GSYM APPEND_ASSOC] >>
      map_every (rewrite_tac o single) [
        GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
      AP_TERM_TAC >> blastLib.BBLAST_TAC) >>
    pop_assum SUBST_ALL_TAC >>
    simp[BigEndianReverse_def] >>
    rewrite_tac[GSYM APPEND_ASSOC] >>
    DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
    rewrite_tac[GSYM APPEND_ASSOC] >>
    DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
    simp[field_concat_left, field_concat_right] >>
    `v2w (field 7 0 (w2v ((63 >< 56) val : word8))) : word8 = (63 >< 56) val` by (
      SUBST1_TAC $ GSYM $ mk_blast_thm ``val : word64`` >> EVAL_TAC) >>
    simp[] >> pop_assum kall_tac >> gvs[state_rel_def] >>
    simp[CONJ_ASSOC] >> conj_tac >- state_rel_tac[] >>
    rw[mem_rel_def]
    >- (simp[FLOOKUP_UPDATE] >> rpt IF_CASES_TAC >> simp[] >> gvs[mem_rel_def]) >>
    simp[FLOOKUP_UPDATE_ALT, APPLY_UPDATE_ALT_THM] >> simp[Once CONJ_SYM] >>
    ntac 7 (
      IF_CASES_TAC >> simp[] >> gvs[]
      >- (
        rpt (IF_CASES_TAC >> gvs[]) >>
        irule_at Any EQ_REFL >> simp[] >> rpt AP_TERM_TAC >>
        SUBST_ALL_TAC $ GSYM $ mk_blast_thm ``val : word64`` >> EVAL_TAC
        )
      ) >>
    IF_CASES_TAC >> gvs[]
    >- (
      reverse $ rpt IF_CASES_TAC >> gvs[]
      >- (
        irule FALSITY >> pop_assum mp_tac >> simp[] >>
        qspec_then `addr` mp_tac w2n_lt >> simp[]
        )
      >- (Q.REFINE_EXISTS_TAC `w2v (_ : word8)` >> simp[]) >>
      irule FALSITY >> ARITH_TAC
      )
    >- (
      reverse $ rpt IF_CASES_TAC >> gvs[]
      >- (
        gvs[mem_rel_def] >> first_x_assum $ qspec_then `w` mp_tac >> rw[] >>
        goal_assum $ drule_at Any >> simp[]
        )
      >- (irule FALSITY >> qspec_then `addr` assume_tac w2n_lt >> gvs[]) >>
      irule FALSITY >>
      qmatch_asmsub_abbrev_tac `w2n _ = (w2n _ + offset) MOD _` >>
      qpat_x_assum `_ ≠ _ (_ + offset)` mp_tac >> simp[] >>
      once_rewrite_tac[GSYM w2n_11] >> unabbrev_all_tac >>
      first_assum SUBST1_TAC >> simp[]
      )
    )
QED


(* TODO a lot of the proofs below are very similar - perhaps they could be combined *)

(********** 64-bit loads **********)

Theorem l3_models_asl_LoadStoreImmediate_NORMAL_LOAD_FFFFF_1:
  ∀b (j : word12) r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@64
        (3w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, T,
         (0w :49 word) @@ j @@ (0w :word3), r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >>
  `(11 >< 0) ((0w :49 word) @@ j @@ (0w :word3) ⋙ 3) = j` by WORD_DECIDE_TAC >>
  simp[] >> pop_assum kall_tac >>
  reverse IF_CASES_TAC >> gvs[]
  >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> WORD_DECIDE_TAC) >>
  l3_decode_tac >> simp[] >> l3_run_tac >>
  asl_cexecute_tac >>
  simp[
    decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def
    ] >>
  ntac 2 $ pop_assum kall_tac >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[
    HaveMTEExt_def, IMPDEF_boolean_def, IMPDEF_boolean_map_def,
    mte_implemented_def,
    SetNotTagCheckedInstruction_def
    ] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`8`,`F`,`&w2n r1`,`T`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos,
         GSYM word_add_def, n2w_w2n, ExtendWord_def] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_read0_8_AccType_NORMAL >> simp[] >>
    disch_then $ qspec_then `X r2 l3 + w2w j ≪ 3` mp_tac >> impl_keep_tac
    >- (
      CCONTR_TAC >> gvs[] >>
      qpat_x_assum `_.exception = NoException` mp_tac >>
      simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'X_def] >>
      pairarg_tac >> simp[] >> qsuff_tac `s.exception ≠ NoException` >> rw[] >>
      qpat_x_assum `Mem _ _ = _` mp_tac >>
      simp[Mem_def, CheckAlignment_def, raise'exception_def] >>
      ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
      simp[state_transformerTheory.BIND_DEF] >>
      Cases_on `l3.exception = NoException` >> gvs[] >>
      strip_tac >> simp[] >> gvs[arm8_state_component_equality]
      ) >>
    strip_tac >> drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    pairarg_tac >> gvs[] >>
    `s = l3` by (
      pop_assum mp_tac >> simp[Mem_def, CheckAlignment_def] >>
      ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
      simp[state_transformerTheory.BIND_DEF] >> Cases_on `(SCTLR l3).A` >> gvs[]) >>
    gvs[] >> simp[write'X_def] >> reverse IF_CASES_TAC >> gvs[]
    >- simp[X_set_31, returnS] >>
    drule $ b64 alpha X_set_not_31 >>
    disch_then $ qspecl_then [`64`,`&w2n r1`,`v'`] mp_tac >> simp[] >>
    impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
    simp[seqS, returnS] >> gvs[write'X_def] >>
    qpat_x_assum `X_set _ _ _ _ = _` mp_tac >>
    simp[X_set_def, int_ge] >>
    every_case_tac >> gvs[returnS, bindS, asl_reg_rws] >>
    rw[] >> gvs[asl_sys_regs_ok_def] >>
    irule FALSITY >> pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
    WORD_DECIDE_TAC
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
    simp[write'X_def] >> pairarg_tac >> simp[] >>
    qsuff_tac `s.exception ≠ NoException` >> rw[] >>
    qmatch_asmsub_abbrev_tac `Mem (foo,_,_) bar` >>
    gvs[Mem_def, CheckAlignment_def, raise'exception_def] >>
    rpt $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`8`,`F`,`&w2n r1`,`T`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos,
       GSYM word_add_def, n2w_w2n] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_read0_8_AccType_NORMAL >> simp[] >>
  disch_then $ qspec_then `SP l3 + w2w j ≪ 3` mp_tac >> impl_keep_tac
  >- (
    CCONTR_TAC >> gvs[] >>
    qpat_x_assum `(_ _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'X_def] >>
    pairarg_tac >> simp[] >> qsuff_tac `s.exception ≠ NoException` >> rw[] >>
    qpat_x_assum `Mem _ _ = _` mp_tac >>
    simp[Mem_def, CheckAlignment_def, raise'exception_def] >>
    ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    Cases_on `l3.exception = NoException` >> gvs[] >>
    strip_tac >> simp[] >> gvs[arm8_state_component_equality]
    ) >>
  strip_tac >> drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  pairarg_tac >> gvs[] >>
  `s = l3` by (
    pop_assum mp_tac >> simp[Mem_def, CheckAlignment_def] >>
    ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    Cases_on `(SCTLR l3).A` >> gvs[]) >>
  gvs[] >> simp[write'X_def] >> reverse IF_CASES_TAC >> gvs[]
  >- simp[X_set_31, returnS] >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`v'`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
  simp[seqS, returnS] >> gvs[write'X_def] >> simp[ExtendWord_def] >>
  qpat_x_assum `X_set _ _ _ _ = _` mp_tac >>
  simp[X_set_def, int_ge] >>
  every_case_tac >> gvs[returnS, bindS, asl_reg_rws] >>
  rw[] >> gvs[asl_sys_regs_ok_def] >>
  irule FALSITY >> pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
  WORD_DECIDE_TAC
QED

Theorem l3_models_asl_LoadStoreImmediate_NORMAL_LOAD_FFFFF_2:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@64
        (3w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, unsigned,
         w2w j, r2, r1)))
Proof
  rw[] >>
  Cases_on `
    ∃i :word12. unsigned ∧ w2w j : word64 = (0w : 49 word) @@ i @@ (0w : word3)` >>
  gvs[l3_models_asl_LoadStoreImmediate_NORMAL_LOAD_FFFFF_1] >>
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >> IF_CASES_TAC >> gvs[] >- gvs[load_store_encode_lemma] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  ntac 3 $ pop_assum kall_tac >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >> rw[] >>
  asl_cexecute_tac >>
  simp[
    decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def
    ] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qcollapse_tac `0w : word1 @@ j` >> gvs[sw2sw_w2w] >>
  `¬word_msb (0w : word1 @@ j)` by blastLib.BBLAST_TAC >> simp[] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`8`,`F`,`&w2n r1`,`T`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[ExtendWord_def, LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_read0_8_AccType_NORMAL >> simp[] >>
    disch_then $ qspec_then `w2w (0w :word1 @@ j) + X r2 l3` mp_tac >> impl_keep_tac
    >- (
      CCONTR_TAC >> gvs[] >>
      qpat_x_assum `_.exception = NoException` mp_tac >>
      simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'X_def] >>
      pairarg_tac >> simp[] >> qsuff_tac `s.exception ≠ NoException` >> rw[] >>
      qpat_x_assum `Mem _ _ = _` mp_tac >>
      simp[Mem_def, CheckAlignment_def, raise'exception_def] >>
      ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
      simp[state_transformerTheory.BIND_DEF] >>
      Cases_on `l3.exception = NoException` >> gvs[] >>
      strip_tac >> simp[] >> gvs[arm8_state_component_equality]
      ) >>
    strip_tac >> drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    pairarg_tac >> gvs[] >>
    `s = l3` by (
      pop_assum mp_tac >> simp[Mem_def, CheckAlignment_def] >>
      ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
      simp[state_transformerTheory.BIND_DEF] >> Cases_on `(SCTLR l3).A` >> gvs[]) >>
    gvs[] >> simp[write'X_def] >> reverse IF_CASES_TAC >> gvs[]
    >- simp[X_set_31, returnS] >>
    drule $ b64 alpha X_set_not_31 >>
    disch_then $ qspecl_then [`64`,`&w2n r1`,`v'`] mp_tac >> simp[] >>
    impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
    simp[seqS, returnS] >> gvs[write'X_def] >>
    qpat_x_assum `X_set _ _ _ _ = _` mp_tac >>
    simp[X_set_def, int_ge] >>
    every_case_tac >> gvs[returnS, bindS, asl_reg_rws] >>
    rw[] >> gvs[asl_sys_regs_ok_def] >>
    irule FALSITY >> pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
    WORD_DECIDE_TAC
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  `asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> gvs[sp_rel_access_pc_ref_def] >> state_rel_tac[]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
    simp[write'X_def] >> pairarg_tac >> simp[] >>
    qsuff_tac `s.exception ≠ NoException` >> rw[] >>
    qmatch_asmsub_abbrev_tac `Mem (foo,_,_) bar` >>
    gvs[Mem_def, CheckAlignment_def, raise'exception_def] >>
    rpt $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`8`,`F`,`&w2n r1`,`T`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos,
       GSYM word_add_def, n2w_w2n] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_read0_8_AccType_NORMAL >> simp[] >>
  disch_then $ qspec_then `SP l3 + w2w (0w : word1 @@ j)` mp_tac >> impl_keep_tac
  >- (
    CCONTR_TAC >> gvs[] >>
    qpat_x_assum `(_ _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'X_def] >>
    pairarg_tac >> simp[] >> qsuff_tac `s.exception ≠ NoException` >> rw[] >>
    qpat_x_assum `Mem _ _ = _` mp_tac >>
    simp[Mem_def, CheckAlignment_def, raise'exception_def] >>
    ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    Cases_on `l3.exception = NoException` >> gvs[] >>
    strip_tac >> simp[] >> gvs[arm8_state_component_equality]
    ) >>
  strip_tac >> drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  pairarg_tac >> gvs[] >>
  `s = l3` by (
    pop_assum mp_tac >> simp[Mem_def, CheckAlignment_def] >>
    ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    Cases_on `(SCTLR l3).A` >> gvs[]) >>
  gvs[] >> simp[write'X_def] >> reverse IF_CASES_TAC >> gvs[]
  >- simp[X_set_31, returnS] >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`v'`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
  simp[seqS, returnS] >> gvs[write'X_def] >> simp[ExtendWord_def] >>
  qpat_x_assum `X_set _ _ _ _ = _` mp_tac >>
  simp[X_set_def, int_ge] >>
  every_case_tac >> gvs[returnS, bindS, asl_reg_rws] >>
  rw[] >> gvs[asl_sys_regs_ok_def] >>
  irule FALSITY >> pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
  WORD_DECIDE_TAC
QED

Theorem l3_models_asl_LoadStoreImmediate_NORMAL_LOAD_FFFFF_3:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@64
        (3w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, unsigned,
         (-1w : 56 word) @@ j, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >> IF_CASES_TAC >> gvs[]
  >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  reverse IF_CASES_TAC >> gvs[]
  >- (pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  ntac 2 $ pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `(_ >< _) (w @@ _)` >>
  `(8 >< 0) (w @@ j) : 9 word = (0b1w : 1 word) @@ j` by (
    unabbrev_all_tac >> blastLib.BBLAST_TAC) >>
  simp[] >> ntac 2 $ pop_assum kall_tac >>
  DEP_REWRITE_TAC[word_concat_assoc |> INST_TYPE [``:ε`` |-> ``:20``]] >> simp[] >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >>
  rw[] >> asl_cexecute_tac >>
  simp[
    decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def
    ] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  `asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qcollapse_tac `1w : word1 @@ j` >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`8`,`F`,`&w2n r1`,`T`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[ExtendWord_def, LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_read0_8_AccType_NORMAL >> simp[] >>
    disch_then $ qspec_then `sw2sw (1w :word1 @@ j) + X r2 l3` mp_tac >> impl_keep_tac
    >- (
      CCONTR_TAC >> gvs[] >>
      qpat_x_assum `_.exception = NoException` mp_tac >>
      simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'X_def] >>
      pairarg_tac >> simp[] >> qsuff_tac `s.exception ≠ NoException` >> rw[] >>
      qpat_x_assum `Mem _ _ = _` mp_tac >>
      simp[Mem_def, CheckAlignment_def, raise'exception_def] >>
      ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
      simp[state_transformerTheory.BIND_DEF] >>
      Cases_on `l3.exception = NoException` >> gvs[] >>
      strip_tac >> simp[] >> gvs[arm8_state_component_equality]
      ) >>
    strip_tac >> drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    pairarg_tac >> gvs[] >>
    `s = l3` by (
      pop_assum mp_tac >> simp[Mem_def, CheckAlignment_def] >>
      ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
      simp[state_transformerTheory.BIND_DEF] >> Cases_on `(SCTLR l3).A` >> gvs[]) >>
    gvs[] >> simp[write'X_def] >> reverse IF_CASES_TAC >> gvs[]
    >- simp[X_set_31, returnS] >>
    drule $ b64 alpha X_set_not_31 >>
    disch_then $ qspecl_then [`64`,`&w2n r1`,`v'`] mp_tac >> simp[] >>
    impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
    simp[seqS, returnS] >> gvs[write'X_def] >>
    qpat_x_assum `X_set _ _ _ _ = _` mp_tac >>
    simp[X_set_def, int_ge] >>
    every_case_tac >> gvs[returnS, bindS, asl_reg_rws] >>
    rw[] >> gvs[asl_sys_regs_ok_def] >>
    irule FALSITY >> pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
    WORD_DECIDE_TAC
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  `asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> gvs[sp_rel_access_pc_ref_def] >> state_rel_tac[]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
    simp[write'X_def] >> pairarg_tac >> simp[] >>
    qsuff_tac `s.exception ≠ NoException` >> rw[] >>
    qmatch_asmsub_abbrev_tac `Mem (foo,_,_) bar` >>
    gvs[Mem_def, CheckAlignment_def, raise'exception_def] >>
    rpt $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`8`,`F`,`&w2n r1`,`T`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos,
       GSYM word_add_def, n2w_w2n] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_read0_8_AccType_NORMAL >> simp[] >>
  disch_then $ qspec_then `SP l3 + sw2sw (1w : word1 @@ j)` mp_tac >> impl_keep_tac
  >- (
    CCONTR_TAC >> gvs[] >>
    qpat_x_assum `(_ _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'X_def] >>
    pairarg_tac >> simp[] >> qsuff_tac `s.exception ≠ NoException` >> rw[] >>
    qpat_x_assum `Mem _ _ = _` mp_tac >>
    simp[Mem_def, CheckAlignment_def, raise'exception_def] >>
    ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    Cases_on `l3.exception = NoException` >> gvs[] >>
    strip_tac >> simp[] >> gvs[arm8_state_component_equality]
    ) >>
  strip_tac >> drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  pairarg_tac >> gvs[] >>
  `s = l3` by (
    pop_assum mp_tac >> simp[Mem_def, CheckAlignment_def] >>
    ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    Cases_on `(SCTLR l3).A` >> gvs[]) >>
  gvs[] >> simp[write'X_def] >> reverse IF_CASES_TAC >> gvs[]
  >- simp[X_set_31, returnS] >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`v'`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
  simp[seqS, returnS] >> gvs[write'X_def] >> simp[ExtendWord_def] >>
  qpat_x_assum `X_set _ _ _ _ = _` mp_tac >>
  simp[X_set_def, int_ge] >>
  every_case_tac >> gvs[returnS, bindS, asl_reg_rws] >>
  rw[] >> gvs[asl_sys_regs_ok_def] >>
  irule FALSITY >> pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
  WORD_DECIDE_TAC
QED

Theorem l3_models_asl_LoadStoreImmediate_NORMAL_LOAD_FFFFF:
  ∀b w unsigned r2 r1.
    let instr =
      LoadStore (LoadStoreImmediate@64
        (3w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, unsigned, w, r2, r1))
    in (∀s. Encode instr ≠ BadCode s) ⇒ l3_models_asl_instr instr
Proof
  rw[encode_rws] >> gvs[load_store_encode_lemma]
  >- simp[l3_models_asl_LoadStoreImmediate_NORMAL_LOAD_FFFFF_1] >>
  Cases_on `word_bit 8 w` >> gvs[] >> qpat_x_assum `w = _` SUBST_ALL_TAC
  >- (
    assume_tac l3_models_asl_LoadStoreImmediate_NORMAL_LOAD_FFFFF_3 >>
    gvs[]
    )
  >- (
    `∃j : word8. (7 >< 0) w : word64 = w2w j` by (
      qexists_tac `(7 >< 0) w` >> blastLib.BBLAST_TAC) >>
    pop_assum SUBST_ALL_TAC >>
    simp[l3_models_asl_LoadStoreImmediate_NORMAL_LOAD_FFFFF_2]
    )
QED

(********** 64-bit stores **********)

Theorem l3_models_asl_LoadStoreImmediate_NORMAL_STORE_FFFFF_1:
  ∀b (j : word12) r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@64
        (3w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, T,
         (0w :49 word) @@ j @@ (0w :word3), r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >>
  `(11 >< 0) ((0w :49 word) @@ j @@ (0w :word3) ⋙ 3) = j` by WORD_DECIDE_TAC >>
  simp[] >> pop_assum kall_tac >>
  reverse IF_CASES_TAC >> gvs[]
  >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> WORD_DECIDE_TAC) >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >> rw[] >>
  asl_cexecute_tac >>
  simp[
    decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def
    ] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    drule X_read >> disch_then $ qspec_then `&w2n r1` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`8`,`F`,`&w2n r1`,`T`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2` by (unabbrev_all_tac >> state_rel_tac[]) >>
    `asl_sys_regs_ok asl2` by (unabbrev_all_tac >> gvs[asl_sys_regs_ok_def]) >>
    drule l3_asl_Mem_set0_8_AccType_NORMAL >> simp[] >>
    disch_then $ qspecl_then [`X r2 l3 + w2w j ≪ 3`,`X r1 l3`] mp_tac >> impl_keep_tac
    >- gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
    simp[Once returnS] >> strip_tac >> simp[seqS, returnS]
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  `asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> gvs[sp_rel_access_pc_ref_def] >> state_rel_tac[]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'Mem_def] >>
    gvs[CheckAlignment_def, raise'exception_def] >>
    rpt $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read >> disch_then $ qspec_then `&w2n r1` mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`8`,`F`,`&w2n r1`,`T`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_set0_8_AccType_NORMAL >> simp[] >>
  disch_then $ qspecl_then [`SP l3 + w2w j ≪ 3`,`X r1 l3`] mp_tac >> impl_tac
  >- (
    qpat_x_assum `(_ (_,_) _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
    ) >>
  simp[returnS] >> strip_tac >> simp[seqS, returnS]
QED

Theorem l3_models_asl_LoadStoreImmediate_NORMAL_STORE_FFFFF_2:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@64
        (3w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, unsigned,
         w2w j, r2, r1)))
Proof
  rw[] >>
  Cases_on `
    ∃i :word12. unsigned ∧ w2w j : word64 = (0w : 49 word) @@ i @@ (0w : word3)` >>
  gvs[l3_models_asl_LoadStoreImmediate_NORMAL_STORE_FFFFF_1] >>
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >> IF_CASES_TAC >> gvs[] >- gvs[load_store_encode_lemma] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  ntac 3 $ pop_assum kall_tac >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >> rw[] >>
  asl_cexecute_tac >>
  simp[
    decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def
    ] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  `asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qcollapse_tac `0w : word1 @@ j` >> gvs[sw2sw_w2w] >>
  `¬word_msb (0w : word1 @@ j)` by blastLib.BBLAST_TAC >> simp[] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    drule X_read >> disch_then $ qspec_then `&w2n r1` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`8`,`F`,`&w2n r1`,`T`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_set0_8_AccType_NORMAL >> simp[] >>
    disch_then $ qspecl_then [`w2w (0w :word1 @@ j) + X r2 l3`,`X r1 l3`] mp_tac >>
    impl_tac
    >- (
      qpat_x_assum `_.exception = NoException` mp_tac >>
      simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
      ) >>
    simp[returnS] >> strip_tac >> simp[seqS, returnS]
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'Mem_def] >>
    gvs[CheckAlignment_def, raise'exception_def] >>
    rpt $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read >> disch_then $ qspec_then `&w2n r1` mp_tac >>
  impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`8`,`F`,`&w2n r1`,`T`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_set0_8_AccType_NORMAL >> simp[] >>
  disch_then $ qspecl_then [`SP l3 + w2w (0w : word1 @@ j)`,`X r1 l3`] mp_tac >>
  impl_tac
  >- (
    qpat_x_assum `(_ (_,_) _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
    ) >>
  simp[returnS] >> strip_tac >> simp[seqS, returnS]
QED

Theorem l3_models_asl_LoadStoreImmediate_NORMAL_STORE_FFFFF_3:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@64
        (3w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, unsigned,
         (-1w : 56 word) @@ j, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >> IF_CASES_TAC >> gvs[]
  >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  reverse IF_CASES_TAC >> gvs[]
  >- (pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  ntac 2 $ pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `(_ >< _) (w @@ _)` >>
  `(8 >< 0) (w @@ j) : 9 word = (0b1w : 1 word) @@ j` by (
    unabbrev_all_tac >> blastLib.BBLAST_TAC) >>
  simp[] >> ntac 2 $ pop_assum kall_tac >>
  DEP_REWRITE_TAC[word_concat_assoc |> INST_TYPE [``:ε`` |-> ``:20``]] >> simp[] >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >>
  rw[] >> asl_cexecute_tac >>
  simp[
    decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def
    ] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  `asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qcollapse_tac `1w : word1 @@ j` >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    drule X_read >> disch_then $ qspec_then `&w2n r1` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`8`,`F`,`&w2n r1`,`T`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_set0_8_AccType_NORMAL >> simp[] >>
    disch_then $ qspecl_then [`sw2sw (1w :word1 @@ j) + X r2 l3`,`X r1 l3`] mp_tac >>
    impl_tac
    >- (
      qpat_x_assum `_.exception = NoException` mp_tac >>
      simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
      ) >>
    simp[returnS] >> strip_tac >> simp[seqS, returnS]
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  `asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> gvs[sp_rel_access_pc_ref_def] >> state_rel_tac[]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'Mem_def] >>
    gvs[CheckAlignment_def, raise'exception_def] >>
    rpt $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read >> disch_then $ qspec_then `&w2n r1` mp_tac >>
  impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`8`,`F`,`&w2n r1`,`T`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_set0_8_AccType_NORMAL >> simp[] >>
  disch_then $ qspecl_then [`SP l3 + sw2sw (1w : word1 @@ j)`,`X r1 l3`] mp_tac >>
  impl_tac
  >- (
    qpat_x_assum `(_ (_,_) _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
    ) >>
  simp[returnS] >> strip_tac >> simp[seqS, returnS]
QED

Theorem l3_models_asl_LoadStoreImmediate_NORMAL_STORE_FFFFF:
  ∀b w unsigned r2 r1.
    let instr =
      LoadStore (LoadStoreImmediate@64
        (3w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, unsigned, w, r2, r1))
    in (∀s. Encode instr ≠ BadCode s) ⇒ l3_models_asl_instr instr
Proof
  rw[encode_rws] >> gvs[load_store_encode_lemma]
  >- simp[l3_models_asl_LoadStoreImmediate_NORMAL_STORE_FFFFF_1] >>
  Cases_on `word_bit 8 w` >> gvs[] >> qpat_x_assum `w = _` SUBST_ALL_TAC
  >- (
    assume_tac l3_models_asl_LoadStoreImmediate_NORMAL_STORE_FFFFF_3 >>
    gvs[]
    )
  >- (
    `∃j : word8. (7 >< 0) w : word64 = w2w j` by (
      qexists_tac `(7 >< 0) w` >> blastLib.BBLAST_TAC) >>
    pop_assum SUBST_ALL_TAC >>
    simp[l3_models_asl_LoadStoreImmediate_NORMAL_STORE_FFFFF_2]
    )
QED

(********** 32-bit loads **********)

Theorem l3_models_asl_LoadStoreImmediate_32_NORMAL_LOAD_FFFFF_1:
  ∀b (j : word12) r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@32
        (2w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, T,
         (0b0w :50 word) @@ j @@ (0b0w :word2), r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >>
  ‘(11 >< 0) ((0b0w :50 word) @@ j @@ (0b0w :word2) ⋙ 2) = j’ by WORD_DECIDE_TAC >>
  simp[] >> pop_assum kall_tac >>
  reverse IF_CASES_TAC >> gvs[]
  >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> WORD_DECIDE_TAC) >>
  l3_decode_tac >> simp[] >> l3_run_tac >>
  asl_cexecute_tac >>
  simp[
    decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def
    ] >>
  ntac 2 $ pop_assum kall_tac >>
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[
    HaveMTEExt_def, IMPDEF_boolean_def, IMPDEF_boolean_map_def,
    mte_implemented_def,
    SetNotTagCheckedInstruction_def
    ] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`4`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos,
         GSYM word_add_def, n2w_w2n, ExtendWord_def] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_read0_4_AccType_NORMAL >> simp[] >>
    disch_then $ qspec_then `X r2 l3 + w2w j ≪ 2` mp_tac >> impl_keep_tac
    >- (
      CCONTR_TAC >> gvs[] >>
      qpat_x_assum `_.exception = NoException` mp_tac >>
      simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'X_def] >>
      pairarg_tac >> simp[] >> qsuff_tac `s.exception ≠ NoException` >> rw[] >>
      qpat_x_assum `Mem _ _ = _` mp_tac >>
      simp[Mem_def, CheckAlignment_def, raise'exception_def] >>
      ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
      simp[state_transformerTheory.BIND_DEF] >>
      Cases_on `l3.exception = NoException` >> gvs[] >>
      strip_tac >> simp[] >> gvs[arm8_state_component_equality]
      ) >>
    strip_tac >> drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    pairarg_tac >> gvs[] >>
    `s = l3` by (
      pop_assum mp_tac >> simp[Mem_def, CheckAlignment_def] >>
      ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
      simp[state_transformerTheory.BIND_DEF] >> Cases_on `(SCTLR l3).A` >> gvs[]) >>
    gvs[] >> simp[write'X_def] >> reverse IF_CASES_TAC >> gvs[]
    >- simp[X_set_31, returnS] >>
    drule $ b32 alpha X_set_not_31 >> (* YO *)
    disch_then $ qspecl_then [`32`,`&w2n r1`,`v'`] mp_tac >> simp[] >>
    impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
    simp[seqS, returnS] >> gvs[write'X_def] >>
    qpat_x_assum `X_set _ _ _ _ = _` mp_tac >>
    simp[X_set_def, int_ge] >>
    every_case_tac >> gvs[returnS, bindS, asl_reg_rws] >>
    rw[] >> gvs[asl_sys_regs_ok_def] >>
    irule FALSITY >> pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
    WORD_DECIDE_TAC
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
    simp[write'X_def] >> pairarg_tac >> simp[] >>
    qsuff_tac `s.exception ≠ NoException` >> rw[] >>
    qmatch_asmsub_abbrev_tac `Mem (foo,_,_) bar` >>
    gvs[Mem_def, CheckAlignment_def, raise'exception_def] >>
    rpt $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`4`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos,
       GSYM word_add_def, n2w_w2n] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_read0_4_AccType_NORMAL >> simp[] >>
  disch_then $ qspec_then `SP l3 + w2w j ≪ 2` mp_tac >> impl_keep_tac
  >- (
    CCONTR_TAC >> gvs[] >>
    qpat_x_assum `(_ _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'X_def] >>
    pairarg_tac >> simp[] >> qsuff_tac `s.exception ≠ NoException` >> rw[] >>
    qpat_x_assum `Mem _ _ = _` mp_tac >>
    simp[Mem_def, CheckAlignment_def, raise'exception_def] >>
    ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    Cases_on `l3.exception = NoException` >> gvs[] >>
    strip_tac >> simp[] >> gvs[arm8_state_component_equality]
    ) >>
  strip_tac >> drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  pairarg_tac >> gvs[] >>
  `s = l3` by (
    pop_assum mp_tac >> simp[Mem_def, CheckAlignment_def] >>
    ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    Cases_on `(SCTLR l3).A` >> gvs[]) >>
  gvs[] >> simp[write'X_def] >> reverse IF_CASES_TAC >> gvs[]
  >- simp[X_set_31, returnS] >>
  drule $ b32 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`32`,`&w2n r1`,`v'`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
  simp[seqS, returnS] >> gvs[write'X_def] >> simp[ExtendWord_def] >>
  qpat_x_assum `X_set _ _ _ _ = _` mp_tac >>
  simp[X_set_def, int_ge] >>
  every_case_tac >> gvs[returnS, bindS, asl_reg_rws] >>
  rw[] >> gvs[asl_sys_regs_ok_def] >>
  irule FALSITY >> pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
  WORD_DECIDE_TAC
QED

Theorem l3_models_asl_LoadStoreImmediate_32_NORMAL_LOAD_FFFFF_2:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@32
        (2w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, unsigned,
         w2w j, r2, r1)))
Proof
  rw[] >>
  Cases_on `
    ∃i :word12. unsigned ∧ w2w j : word64 = (0w : 50 word) @@ i @@ (0w : word2)` >>
  gvs[l3_models_asl_LoadStoreImmediate_32_NORMAL_LOAD_FFFFF_1] >>
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >> IF_CASES_TAC >> gvs[] >- gvs[load_store_encode_lemma] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  ntac 3 $ pop_assum kall_tac >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >> rw[] >>
  asl_cexecute_tac >>
  simp[
    decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def
    ] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qcollapse_tac `0w : word1 @@ j` >> gvs[sw2sw_w2w] >>
  `¬word_msb (0w : word1 @@ j)` by blastLib.BBLAST_TAC >> simp[] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`4`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[ExtendWord_def, LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_read0_4_AccType_NORMAL >> simp[] >>
    disch_then $ qspec_then `w2w (0w :word1 @@ j) + X r2 l3` mp_tac >> impl_keep_tac
    >- (
      CCONTR_TAC >> gvs[] >>
      qpat_x_assum `_.exception = NoException` mp_tac >>
      simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'X_def] >>
      pairarg_tac >> simp[] >> qsuff_tac `s.exception ≠ NoException` >> rw[] >>
      qpat_x_assum `Mem _ _ = _` mp_tac >>
      simp[Mem_def, CheckAlignment_def, raise'exception_def] >>
      ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
      simp[state_transformerTheory.BIND_DEF] >>
      Cases_on `l3.exception = NoException` >> gvs[] >>
      strip_tac >> simp[] >> gvs[arm8_state_component_equality]
      ) >>
    strip_tac >> drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    pairarg_tac >> gvs[] >>
    `s = l3` by (
      pop_assum mp_tac >> simp[Mem_def, CheckAlignment_def] >>
      ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
      simp[state_transformerTheory.BIND_DEF] >> Cases_on `(SCTLR l3).A` >> gvs[]) >>
    gvs[] >> simp[write'X_def] >> reverse IF_CASES_TAC >> gvs[]
    >- simp[X_set_31, returnS] >>
    drule $ b32 alpha X_set_not_31 >>
    disch_then $ qspecl_then [`32`,`&w2n r1`,`v'`] mp_tac >> simp[] >>
    impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
    simp[seqS, returnS] >> gvs[write'X_def] >>
    qpat_x_assum `X_set _ _ _ _ = _` mp_tac >>
    simp[X_set_def, int_ge] >>
    every_case_tac >> gvs[returnS, bindS, asl_reg_rws] >>
    rw[] >> gvs[asl_sys_regs_ok_def] >>
    irule FALSITY >> pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
    WORD_DECIDE_TAC
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  `asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> gvs[sp_rel_access_pc_ref_def] >> state_rel_tac[]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
    simp[write'X_def] >> pairarg_tac >> simp[] >>
    qsuff_tac `s.exception ≠ NoException` >> rw[] >>
    qmatch_asmsub_abbrev_tac `Mem (foo,_,_) bar` >>
    gvs[Mem_def, CheckAlignment_def, raise'exception_def] >>
    rpt $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`4`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos,
       GSYM word_add_def, n2w_w2n] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_read0_4_AccType_NORMAL >> simp[] >>
  disch_then $ qspec_then `SP l3 + w2w (0w : word1 @@ j)` mp_tac >> impl_keep_tac
  >- (
    CCONTR_TAC >> gvs[] >>
    qpat_x_assum `(_ _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'X_def] >>
    pairarg_tac >> simp[] >> qsuff_tac `s.exception ≠ NoException` >> rw[] >>
    qpat_x_assum `Mem _ _ = _` mp_tac >>
    simp[Mem_def, CheckAlignment_def, raise'exception_def] >>
    ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    Cases_on `l3.exception = NoException` >> gvs[] >>
    strip_tac >> simp[] >> gvs[arm8_state_component_equality]
    ) >>
  strip_tac >> drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  pairarg_tac >> gvs[] >>
  `s = l3` by (
    pop_assum mp_tac >> simp[Mem_def, CheckAlignment_def] >>
    ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    Cases_on `(SCTLR l3).A` >> gvs[]) >>
  gvs[] >> simp[write'X_def] >> reverse IF_CASES_TAC >> gvs[]
  >- simp[X_set_31, returnS] >>
  drule $ b32 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`32`,`&w2n r1`,`v'`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
  simp[seqS, returnS] >> gvs[write'X_def] >> simp[ExtendWord_def] >>
  qpat_x_assum `X_set _ _ _ _ = _` mp_tac >>
  simp[X_set_def, int_ge] >>
  every_case_tac >> gvs[returnS, bindS, asl_reg_rws] >>
  rw[] >> gvs[asl_sys_regs_ok_def] >>
  irule FALSITY >> pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
  WORD_DECIDE_TAC
QED

Theorem l3_models_asl_LoadStoreImmediate_32_NORMAL_LOAD_FFFFF_3:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@32
        (2w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, unsigned,
         (-1w : 56 word) @@ j, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >> IF_CASES_TAC >> gvs[]
  >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  reverse IF_CASES_TAC >> gvs[]
  >- (pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  ntac 2 $ pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `(_ >< _) (w @@ _)` >>
  `(8 >< 0) (w @@ j) : 9 word = (0b1w : 1 word) @@ j` by (
    unabbrev_all_tac >> blastLib.BBLAST_TAC) >>
  simp[] >> ntac 2 $ pop_assum kall_tac >>
  DEP_REWRITE_TAC[word_concat_assoc |> INST_TYPE [``:ε`` |-> ``:20``]] >> simp[] >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >>
  rw[] >> asl_cexecute_tac >>
  simp[
    decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def
    ] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  `asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qcollapse_tac `1w : word1 @@ j` >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`4`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[ExtendWord_def, LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_read0_4_AccType_NORMAL >> simp[] >>
    disch_then $ qspec_then `sw2sw (1w :word1 @@ j) + X r2 l3` mp_tac >> impl_keep_tac
    >- (
      CCONTR_TAC >> gvs[] >>
      qpat_x_assum `_.exception = NoException` mp_tac >>
      simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'X_def] >>
      pairarg_tac >> simp[] >> qsuff_tac `s.exception ≠ NoException` >> rw[] >>
      qpat_x_assum `Mem _ _ = _` mp_tac >>
      simp[Mem_def, CheckAlignment_def, raise'exception_def] >>
      ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
      simp[state_transformerTheory.BIND_DEF] >>
      Cases_on `l3.exception = NoException` >> gvs[] >>
      strip_tac >> simp[] >> gvs[arm8_state_component_equality]
      ) >>
    strip_tac >> drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    pairarg_tac >> gvs[] >>
    `s = l3` by (
      pop_assum mp_tac >> simp[Mem_def, CheckAlignment_def] >>
      ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
      simp[state_transformerTheory.BIND_DEF] >> Cases_on `(SCTLR l3).A` >> gvs[]) >>
    gvs[] >> simp[write'X_def] >> reverse IF_CASES_TAC >> gvs[]
    >- simp[X_set_31, returnS] >>
    drule $ b32 alpha X_set_not_31 >>
    disch_then $ qspecl_then [`32`,`&w2n r1`,`v'`] mp_tac >> simp[] >>
    impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
    simp[seqS, returnS] >> gvs[write'X_def] >>
    qpat_x_assum `X_set _ _ _ _ = _` mp_tac >>
    simp[X_set_def, int_ge] >>
    every_case_tac >> gvs[returnS, bindS, asl_reg_rws] >>
    rw[] >> gvs[asl_sys_regs_ok_def] >>
    irule FALSITY >> pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
    WORD_DECIDE_TAC
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  `asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> gvs[sp_rel_access_pc_ref_def] >> state_rel_tac[]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
    simp[write'X_def] >> pairarg_tac >> simp[] >>
    qsuff_tac `s.exception ≠ NoException` >> rw[] >>
    qmatch_asmsub_abbrev_tac `Mem (foo,_,_) bar` >>
    gvs[Mem_def, CheckAlignment_def, raise'exception_def] >>
    rpt $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`4`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos,
       GSYM word_add_def, n2w_w2n] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_read0_4_AccType_NORMAL >> simp[] >>
  disch_then $ qspec_then `SP l3 + sw2sw (1w : word1 @@ j)` mp_tac >> impl_keep_tac
  >- (
    CCONTR_TAC >> gvs[] >>
    qpat_x_assum `(_ _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'X_def] >>
    pairarg_tac >> simp[] >> qsuff_tac `s.exception ≠ NoException` >> rw[] >>
    qpat_x_assum `Mem _ _ = _` mp_tac >>
    simp[Mem_def, CheckAlignment_def, raise'exception_def] >>
    ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    Cases_on `l3.exception = NoException` >> gvs[] >>
    strip_tac >> simp[] >> gvs[arm8_state_component_equality]
    ) >>
  strip_tac >> drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  pairarg_tac >> gvs[] >>
  `s = l3` by (
    pop_assum mp_tac >> simp[Mem_def, CheckAlignment_def] >>
    ntac 4 (ntac 8 $ simp[Once state_transformerTheory.FOR_def]) >>
    simp[state_transformerTheory.BIND_DEF] >>
    Cases_on `(SCTLR l3).A` >> gvs[]) >>
  gvs[] >> simp[write'X_def] >> reverse IF_CASES_TAC >> gvs[]
  >- simp[X_set_31, returnS] >>
  drule $ b32 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`32`,`&w2n r1`,`v'`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
  simp[seqS, returnS] >> gvs[write'X_def] >> simp[ExtendWord_def] >>
  qpat_x_assum `X_set _ _ _ _ = _` mp_tac >>
  simp[X_set_def, int_ge] >>
  every_case_tac >> gvs[returnS, bindS, asl_reg_rws] >>
  rw[] >> gvs[asl_sys_regs_ok_def] >>
  irule FALSITY >> pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
  WORD_DECIDE_TAC
QED

Theorem l3_models_asl_LoadStoreImmediate_32_NORMAL_LOAD_FFFFF:
  ∀b w unsigned r2 r1.
    let instr =
      LoadStore (LoadStoreImmediate@32
        (2w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, unsigned, w, r2, r1))
    in (∀s. Encode instr ≠ BadCode s) ⇒ l3_models_asl_instr instr
Proof
  rw[encode_rws] >> gvs[load_store_encode_lemma]
  >- simp[l3_models_asl_LoadStoreImmediate_32_NORMAL_LOAD_FFFFF_1] >>
  Cases_on `word_bit 8 w` >> gvs[] >> qpat_x_assum `w = _` SUBST_ALL_TAC
  >- (
    assume_tac l3_models_asl_LoadStoreImmediate_32_NORMAL_LOAD_FFFFF_3 >>
    gvs[]
    )
  >- (
    `∃j : word8. (7 >< 0) w : word64 = w2w j` by (
      qexists_tac `(7 >< 0) w` >> blastLib.BBLAST_TAC) >>
    pop_assum SUBST_ALL_TAC >>
    simp[l3_models_asl_LoadStoreImmediate_32_NORMAL_LOAD_FFFFF_2]
    )
QED

(********** 32-bit stores **********)

Theorem l3_models_asl_LoadStoreImmediate_32_NORMAL_STORE_FFFFF_1:
  ∀b (j : word12) r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@32
        (2w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, T,
         (0w :50 word) @@ j @@ (0w :word2), r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >>
  `(11 >< 0) ((0w :50 word) @@ j @@ (0w :word2) ⋙ 2) = j` by WORD_DECIDE_TAC >>
  simp[] >> pop_assum kall_tac >>
  reverse IF_CASES_TAC >> gvs[]
  >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> WORD_DECIDE_TAC) >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >> rw[] >>
  asl_cexecute_tac >>
  simp[
    decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def
    ] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    drule X_read32 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`4`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2` by (unabbrev_all_tac >> state_rel_tac[]) >>
    `asl_sys_regs_ok asl2` by (unabbrev_all_tac >> gvs[asl_sys_regs_ok_def]) >>
    drule l3_asl_Mem_set0_4_AccType_NORMAL >> simp[] >>
    disch_then $ qspecl_then [`X r2 l3 + w2w j ≪ 2`,`X r1 l3`] mp_tac >> impl_keep_tac
    >- gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
    simp[Once returnS] >> strip_tac >> simp[seqS, returnS]
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  `asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> gvs[sp_rel_access_pc_ref_def] >> state_rel_tac[]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'Mem_def] >>
    gvs[CheckAlignment_def, raise'exception_def] >>
    rpt $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read32 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`4`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_set0_4_AccType_NORMAL >> simp[] >>
  disch_then $ qspecl_then [`SP l3 + w2w j ≪ 2`,`X r1 l3`] mp_tac >> impl_tac
  >- (
    qpat_x_assum `(_ (_,_) _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
    ) >>
  simp[returnS] >> strip_tac >> simp[seqS, returnS]
QED

Theorem l3_models_asl_LoadStoreImmediate_32_NORMAL_STORE_FFFFF_2:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@32
        (2w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, unsigned,
         w2w j, r2, r1)))
Proof
  rw[] >>
  Cases_on `
    ∃i :word12. unsigned ∧ w2w j : word64 = (0w : 50 word) @@ i @@ (0w : word2)` >>
  gvs[l3_models_asl_LoadStoreImmediate_32_NORMAL_STORE_FFFFF_1] >>
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >> IF_CASES_TAC >> gvs[] >- gvs[load_store_encode_lemma] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  ntac 3 $ pop_assum kall_tac >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >> rw[] >>
  asl_cexecute_tac >>
  simp[
    decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def
    ] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  `asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qcollapse_tac `0w : word1 @@ j` >> gvs[sw2sw_w2w] >>
  `¬word_msb (0w : word1 @@ j)` by blastLib.BBLAST_TAC >> simp[] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    drule X_read32 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`4`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_set0_4_AccType_NORMAL >> simp[] >>
    disch_then $ qspecl_then [`w2w (0w :word1 @@ j) + X r2 l3`,`X r1 l3`] mp_tac >>
    impl_tac
    >- (
      qpat_x_assum `_.exception = NoException` mp_tac >>
      simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
      ) >>
    simp[returnS] >> strip_tac >> simp[seqS, returnS]
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'Mem_def] >>
    gvs[CheckAlignment_def, raise'exception_def] >>
    rpt $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read32 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
  impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`4`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_set0_4_AccType_NORMAL >> simp[] >>
  disch_then $ qspecl_then [`SP l3 + w2w (0w : word1 @@ j)`,`X r1 l3`] mp_tac >>
  impl_tac
  >- (
    qpat_x_assum `(_ (_,_) _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
    ) >>
  simp[returnS] >> strip_tac >> simp[seqS, returnS]
QED

Theorem l3_models_asl_LoadStoreImmediate_32_NORMAL_STORE_FFFFF_3:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@32
        (2w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, unsigned,
         (-1w : 56 word) @@ j, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >> IF_CASES_TAC >> gvs[]
  >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  reverse IF_CASES_TAC >> gvs[]
  >- (pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  ntac 2 $ pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `(_ >< _) (w @@ _)` >>
  `(8 >< 0) (w @@ j) : 9 word = (0b1w : 1 word) @@ j` by (
    unabbrev_all_tac >> blastLib.BBLAST_TAC) >>
  simp[] >> ntac 2 $ pop_assum kall_tac >>
  DEP_REWRITE_TAC[word_concat_assoc |> INST_TYPE [``:ε`` |-> ``:20``]] >> simp[] >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >>
  rw[] >> asl_cexecute_tac >>
  simp[
    decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def
    ] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  `asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qcollapse_tac `1w : word1 @@ j` >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    drule X_read32 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`4`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_set0_4_AccType_NORMAL >> simp[] >>
    disch_then $ qspecl_then [`sw2sw (1w :word1 @@ j) + X r2 l3`,`X r1 l3`] mp_tac >>
    impl_tac
    >- (
      qpat_x_assum `_.exception = NoException` mp_tac >>
      simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
      ) >>
    simp[returnS] >> strip_tac >> simp[seqS, returnS]
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  `asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> gvs[sp_rel_access_pc_ref_def] >> state_rel_tac[]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'Mem_def] >>
    gvs[CheckAlignment_def, raise'exception_def] >>
    rpt $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read32 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
  impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`4`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_set0_4_AccType_NORMAL >> simp[] >>
  disch_then $ qspecl_then [`SP l3 + sw2sw (1w : word1 @@ j)`,`X r1 l3`] mp_tac >>
  impl_tac
  >- (
    qpat_x_assum `(_ (_,_) _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
    ) >>
  simp[returnS] >> strip_tac >> simp[seqS, returnS]
QED

Theorem l3_models_asl_LoadStoreImmediate_32_NORMAL_STORE_FFFFF:
  ∀b w unsigned r2 r1.
    let instr =
      LoadStore (LoadStoreImmediate@32
        (2w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, unsigned, w, r2, r1))
    in (∀s. Encode instr ≠ BadCode s) ⇒ l3_models_asl_instr instr
Proof
  rw[encode_rws] >> gvs[load_store_encode_lemma]
  >- simp[l3_models_asl_LoadStoreImmediate_32_NORMAL_STORE_FFFFF_1] >>
  Cases_on `word_bit 8 w` >> gvs[] >> qpat_x_assum `w = _` SUBST_ALL_TAC
  >- (
    assume_tac l3_models_asl_LoadStoreImmediate_32_NORMAL_STORE_FFFFF_3 >>
    gvs[]
    )
  >- (
    `∃j : word8. (7 >< 0) w : word64 = w2w j` by (
      qexists_tac `(7 >< 0) w` >> blastLib.BBLAST_TAC) >>
    pop_assum SUBST_ALL_TAC >>
    simp[l3_models_asl_LoadStoreImmediate_32_NORMAL_STORE_FFFFF_2]
    )
QED

(********** 8-bit loads **********)

Theorem l3_models_asl_LoadStoreImmediate_8_NORMAL_LOAD_FFFFF_1:
  ∀b (j : word12) r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@8
        (0w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, T,
         (0w :52 word) @@ j, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >>
  `(11 >< 0) ((0w :52 word) @@ j) = j` by WORD_DECIDE_TAC >>
  simp[] >> pop_assum kall_tac >>
  reverse IF_CASES_TAC >> gvs[]
  >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> WORD_DECIDE_TAC) >>
  l3_decode_tac >> simp[] >> l3_run_tac >> pop_assum kall_tac >>
  rw[] >> asl_cexecute_tac >>
  simp[
    decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def
    ] >>
  pop_assum kall_tac >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  `asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`1`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule_all l3_asl_Mem_read0_1_AccType_NORMAL >>
    simp[returnS, bindS] >> disch_then kall_tac >>
    qmatch_goalsub_abbrev_tac `FST val` >> PairCases_on `val` >> gvs[] >>
    `val1 = l3` by (
      gvs[Mem_def] >> simp[Once state_transformerTheory.FOR_def] >>
      simp[CheckAlignment_def, Aligned_def, Align_def]) >>
    Cases_on `r1 = 31w` >> gvs[] >- simp[X_set_31, returnS, write'X_def] >>
    drule $ INST_TYPE [alpha |-> ``:32``] X_set_not_31 >>
    disch_then $ qspecl_then [`32`,`&w2n r1`,`w2w val0 : word32`] mp_tac >>
    impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >>
    strip_tac >> simp[seqS, returnS, ExtendWord_def] >> gvs[] >>
    gvs[X_set_def, returnS, bindS, seqS, asl_reg_rws] >>
    every_case_tac >> gvs[returnS, bindS, seqS, failS] >>
    gvs[asl_sys_regs_ok_def]
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  `asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> gvs[sp_rel_access_pc_ref_def] >> state_rel_tac[]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, Mem_def] >>
    gvs[CheckAlignment_def, raise'exception_def] >>
    ntac 4 $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF] >>
    simp[write'X_def] >> every_case_tac >> gvs[]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`1`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  `asl_sys_regs_ok asl3` by (unabbrev_all_tac >> gvs[asl_sys_regs_ok_def]) >>
  drule_all l3_asl_Mem_read0_1_AccType_NORMAL >>
  simp[bindS, returnS] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `FST val` >> PairCases_on `val` >> gvs[] >>
  `val1 = l3` by (
    gvs[Mem_def] >> simp[Once state_transformerTheory.FOR_def] >>
    simp[CheckAlignment_def, Aligned_def, Align_def]) >>
  Cases_on `r1 = 31w` >> gvs[] >- simp[X_set_31, returnS, write'X_def] >>
  drule $ INST_TYPE [alpha |-> ``:32``] X_set_not_31 >>
  disch_then $ qspecl_then [`32`,`&w2n r1`,`w2w val0`] mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >>
  strip_tac >> simp[seqS, returnS] >> gvs[ExtendWord_def] >>
  gvs[X_set_def, returnS, bindS, seqS, asl_reg_rws] >>
  every_case_tac >> gvs[returnS, bindS, seqS, failS] >>
  gvs[asl_sys_regs_ok_def]
QED

Theorem l3_models_asl_LoadStoreImmediate_8_NORMAL_LOAD_FFFFF_2:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@8
        (0w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, unsigned,
         w2w j, r2, r1)))
Proof
  rw[] >>
  Cases_on `∃i :word12. unsigned ∧ w2w j : word64 = (0w : 52 word) @@ i` >>
  gvs[l3_models_asl_LoadStoreImmediate_8_NORMAL_LOAD_FFFFF_1] >>
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >> IF_CASES_TAC >> gvs[] >- gvs[load_store_encode_lemma] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  ntac 3 $ pop_assum kall_tac >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >> rw[] >>
  asl_cexecute_tac >>
  simp[
    decode_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def
    ] >>
  qcollapse_tac `0w : 1 word @@ j` >>
  `sw2sw (0w : word1 @@ j) : word64 = w2w j` by (
    simp[sw2sw_w2w] >> blastLib.BBLAST_TAC >> gvs[]) >>
  `(8 >< 0) (w2w j : word64) : 9 word = w2w j` by blastLib.BBLAST_TAC >>
  gvs[] >> ntac 3 $ pop_assum kall_tac >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`1`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule_all l3_asl_Mem_read0_1_AccType_NORMAL >>
    simp[returnS, bindS] >> disch_then kall_tac >>
    qmatch_goalsub_abbrev_tac `FST val` >> PairCases_on `val` >> gvs[] >>
    `val1 = l3` by (
      gvs[Mem_def] >> simp[Once state_transformerTheory.FOR_def] >>
      simp[CheckAlignment_def, Aligned_def, Align_def]) >>
    Cases_on `r1 = 31w` >> gvs[] >- simp[X_set_31, returnS, write'X_def] >>
    drule $ INST_TYPE [alpha |-> ``:32``] X_set_not_31 >>
    disch_then $ qspecl_then [`32`,`&w2n r1`,`w2w val0 : word32`] mp_tac >>
    impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >>
    strip_tac >> simp[seqS, returnS, ExtendWord_def] >> gvs[] >>
    gvs[X_set_def, returnS, bindS, seqS, asl_reg_rws] >>
    every_case_tac >> gvs[returnS, bindS, seqS, failS] >>
    gvs[asl_sys_regs_ok_def]
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, Mem_def] >>
    gvs[CheckAlignment_def, raise'exception_def] >>
    ntac 4 $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF] >>
    simp[write'X_def] >> every_case_tac >> gvs[]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`1`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule_all l3_asl_Mem_read0_1_AccType_NORMAL >>
  simp[bindS, returnS] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `FST val` >> PairCases_on `val` >> gvs[] >>
  `val1 = l3` by (
    gvs[Mem_def] >> simp[Once state_transformerTheory.FOR_def] >>
    simp[CheckAlignment_def, Aligned_def, Align_def]) >>
  Cases_on `r1 = 31w` >> gvs[] >- simp[X_set_31, returnS, write'X_def] >>
  drule $ INST_TYPE [alpha |-> ``:32``] X_set_not_31 >>
  disch_then $ qspecl_then [`32`,`&w2n r1`,`w2w val0`] mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >>
  strip_tac >> simp[seqS, returnS] >> gvs[ExtendWord_def] >>
  gvs[X_set_def, returnS, bindS, seqS, asl_reg_rws] >>
  every_case_tac >> gvs[returnS, bindS, seqS, failS] >>
  gvs[asl_sys_regs_ok_def]
QED

Theorem l3_models_asl_LoadStoreImmediate_8_NORMAL_LOAD_FFFFF_3:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@8
        (0w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, unsigned,
         (-1w : 56 word) @@ j, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >> IF_CASES_TAC >> gvs[]
  >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  reverse IF_CASES_TAC >> gvs[]
  >- (rpt $ pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  qmatch_goalsub_abbrev_tac `(_ >< _) (w @@ _)` >>
  `(8 >< 0) (w @@ j) : 9 word = (0b1w : 1 word) @@ j` by (
    unabbrev_all_tac >> blastLib.BBLAST_TAC) >>
  simp[] >> ntac 4 $ pop_assum kall_tac >>
  l3_decode_tac >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >> rw[] >>
  asl_cexecute_tac >>
  simp[
    decode_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def
    ] >>
  pop_assum kall_tac >> qcollapse_tac `1w : 1 word @@ j` >>
  `sw2sw (0w : word1 @@ j) : word64 = w2w j` by (
    simp[sw2sw_w2w] >> blastLib.BBLAST_TAC >> gvs[]) >>
  simp[] >> pop_assum kall_tac >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`1`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule_all l3_asl_Mem_read0_1_AccType_NORMAL >>
    simp[returnS, bindS] >> disch_then kall_tac >>
    qmatch_goalsub_abbrev_tac `FST val` >> PairCases_on `val` >> gvs[] >>
    `val1 = l3` by (
      gvs[Mem_def] >> simp[Once state_transformerTheory.FOR_def] >>
      simp[CheckAlignment_def, Aligned_def, Align_def]) >>
    Cases_on `r1 = 31w` >> gvs[] >- simp[X_set_31, returnS, write'X_def] >>
    drule $ INST_TYPE [alpha |-> ``:32``] X_set_not_31 >>
    disch_then $ qspecl_then [`32`,`&w2n r1`,`w2w val0`] mp_tac >>
    impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >>
    strip_tac >> simp[seqS, returnS, ExtendWord_def] >> gvs[] >>
    gvs[X_set_def, returnS, bindS, seqS, asl_reg_rws] >>
    every_case_tac >> gvs[returnS, bindS, seqS, failS] >>
    gvs[asl_sys_regs_ok_def]
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, Mem_def] >>
    gvs[CheckAlignment_def, raise'exception_def] >>
    ntac 4 $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF] >>
    simp[write'X_def] >> every_case_tac >> gvs[]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`1`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (
    unabbrev_all_tac >> state_rel_tac[]) >>
  drule_all l3_asl_Mem_read0_1_AccType_NORMAL >>
  simp[bindS, returnS] >> disch_then kall_tac >>
  qmatch_goalsub_abbrev_tac `FST val` >> PairCases_on `val` >> gvs[] >>
  `val1 = l3` by (
    gvs[Mem_def] >> simp[Once state_transformerTheory.FOR_def] >>
    simp[CheckAlignment_def, Aligned_def, Align_def]) >>
  Cases_on `r1 = 31w` >> gvs[] >- simp[X_set_31, returnS, write'X_def] >>
  drule $ INST_TYPE [alpha |-> ``:32``] X_set_not_31 >>
  disch_then $ qspecl_then [`32`,`&w2n r1`,`w2w val0`] mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >>
  strip_tac >> simp[seqS, returnS] >> gvs[ExtendWord_def] >>
  gvs[X_set_def, returnS, bindS, seqS, asl_reg_rws] >>
  every_case_tac >> gvs[returnS, bindS, seqS, failS] >>
  gvs[asl_sys_regs_ok_def]
QED

Theorem l3_models_asl_LoadStoreImmediate_8_NORMAL_LOAD_FFFFF:
  ∀b w unsigned r2 r1.
    let instr =
      LoadStore (LoadStoreImmediate@8
        (0w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, unsigned, w, r2, r1))
    in (∀s. Encode instr ≠ BadCode s) ⇒ l3_models_asl_instr instr
Proof
  rw[encode_rws] >> gvs[load_store_encode_lemma]
  >- simp[l3_models_asl_LoadStoreImmediate_8_NORMAL_LOAD_FFFFF_1] >>
  Cases_on `word_bit 8 w` >> gvs[] >> qpat_x_assum `w = _` SUBST_ALL_TAC
  >- (
    assume_tac l3_models_asl_LoadStoreImmediate_8_NORMAL_LOAD_FFFFF_3 >> gvs[]
    )
  >- (
    `∃j : word8. (7 >< 0) w : word64 = w2w j` by (
      qexists_tac `(7 >< 0) w` >> blastLib.BBLAST_TAC) >>
    pop_assum SUBST_ALL_TAC >>
    simp[l3_models_asl_LoadStoreImmediate_8_NORMAL_LOAD_FFFFF_2]
    )
QED

(********** 8-bit stores **********)

Theorem l3_models_asl_LoadStoreImmediate_8_NORMAL_STORE_FFFFF_1:
  ∀b (j : word12) r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@8
        (0w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, T,
          (0w : 52 word) @@ j, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >> reverse IF_CASES_TAC
  >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  `(11 >< 0) ((0w :52 word) @@ j) = j` by WORD_DECIDE_TAC >>
  pop_assum SUBST_ALL_TAC >> pop_assum kall_tac >> simp[] >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >> rw[] >>
  asl_cexecute_tac >>
  simp[
    decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx_def
    ] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    drule X_read_8 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`1`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_set0_1_AccType_NORMAL >> simp[] >>
    disch_then $ qspecl_then [`w2w j + X r2 l3`,`X r1 l3`] mp_tac >> impl_keep_tac
    >- gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
    simp[Once returnS] >> strip_tac >> simp[seqS, returnS]
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'Mem_def] >>
    gvs[CheckAlignment_def, raise'exception_def] >>
    rpt $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read_8 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`1`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_set0_1_AccType_NORMAL >> simp[] >>
  disch_then $ qspecl_then [`SP l3 + w2w j`,`X r1 l3`] mp_tac >> impl_tac
  >- (
    qpat_x_assum `(_ (_,_) _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
    ) >>
  simp[returnS] >> strip_tac >> simp[seqS, returnS]
QED

Theorem l3_models_asl_LoadStoreImmediate_8_NORMAL_STORE_FFFFF_2:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@8
        (0w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, unsigned,
         w2w j, r2, r1)))
Proof
  rw[] >>
  Cases_on `∃i :word12. unsigned ∧ w2w j : word64 = (0w : 52 word) @@ i` >>
  gvs[l3_models_asl_LoadStoreImmediate_8_NORMAL_STORE_FFFFF_1] >>
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >> IF_CASES_TAC >> gvs[] >- gvs[load_store_encode_lemma] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >> rw[] >>
  asl_cexecute_tac >>
  simp[
    decode_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def
    ] >>
  pop_assum kall_tac >> qcollapse_tac `0w : 1 word @@ j` >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  `sw2sw (0w : word1 @@ j) : word64 = w2w j` by (
    simp[sw2sw_w2w] >> blastLib.BBLAST_TAC >> gvs[]) >>
  gvs[] >> pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    drule X_read_8 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`1`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_set0_1_AccType_NORMAL >> simp[] >>
    disch_then $ qspecl_then [`w2w j + X r2 l3`,`X r1 l3`] mp_tac >> impl_keep_tac
    >- gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
    simp[Once returnS] >> strip_tac >> simp[seqS, returnS]
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'Mem_def] >>
    gvs[CheckAlignment_def, raise'exception_def] >>
    rpt $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read_8 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`1`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_set0_1_AccType_NORMAL >> simp[] >>
  disch_then $ qspecl_then [`SP l3 + w2w j`,`X r1 l3`] mp_tac >> impl_tac
  >- (
    qpat_x_assum `(_ (_,_) _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
    ) >>
  simp[returnS] >> strip_tac >> simp[seqS, returnS]
QED

Theorem l3_models_asl_LoadStoreImmediate_8_NORMAL_STORE_FFFFF_3:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@8
        (0w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, unsigned,
         (-1w : 56 word) @@ j, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >> IF_CASES_TAC >> gvs[]
  >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  reverse IF_CASES_TAC >> gvs[]
  >- (rpt $ pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  ntac 2 $ pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `(_ >< _) (w @@ _)` >>
  `(8 >< 0) (w @@ j) : 9 word = (0b1w : 1 word) @@ j` by (
    unabbrev_all_tac >> blastLib.BBLAST_TAC) >>
  simp[] >> ntac 2 $ pop_assum kall_tac >>
  DEP_REWRITE_TAC[word_concat_assoc |> INST_TYPE [``:ε`` |-> ``:20``]] >> simp[] >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >>
  rw[] >> asl_cexecute_tac >>
  simp[
    decode_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
    execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def
    ] >>
  pop_assum kall_tac >> qcollapse_tac `1w : 1 word @@ j` >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[undefined_MemOp_def, undefined_Constraint_def,
       sail2_state_monadTheory.undefined_boolS_def] >>
  simp[SetNotTagCheckedInstruction_def] >>
  simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
  reverse $ Cases_on `r2 = 31w` >> gvs[]
  >- (
    `w2n r2 ≠ 31` by WORD_DECIDE_TAC >> gvs[] >>
    drule X_read >> disch_then $ qspec_then `&w2n r2` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    drule X_read_8 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`1`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_set0_1_AccType_NORMAL >> simp[] >>
    disch_then $ qspecl_then [`sw2sw (1w : word1 @@ j) + X r2 l3`,`X r1 l3`] mp_tac >>
    impl_keep_tac
    >- gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def] >>
    simp[Once returnS] >> strip_tac >> simp[seqS, returnS]
    ) >>
  simp[ThisInstrAddr_def] >>
  `read_regS PC_ref asl1 = returnS l3.PC asl1 : word64 res` by state_rel_tac[] >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  simp[Once seqS, asl_reg_rws, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
  `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
    unabbrev_all_tac >> state_rel_tac[sp_rel_access_pc_ref_def]) >>
  drule l3_asl_CheckSPAlignment >> simp[] >> impl_keep_tac
  >- (
    qpat_x_assum `_ = NoException` mp_tac >> rpt $ pop_assum kall_tac >>
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    gvs[dfn'LoadStoreImmediate_def, LoadStoreSingle_def, write'Mem_def] >>
    gvs[CheckAlignment_def, raise'exception_def] >>
    rpt $ simp[Once state_transformerTheory.FOR_def,
                    state_transformerTheory.BIND_DEF]
    ) >>
  strip_tac >> qpat_x_assum `_ = CheckSPAlignment _` $ assume_tac o GSYM >>
  simp[Once seqS, Once returnS] >>
  drule SP_read >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  drule X_read_8 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`1`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_set0_1_AccType_NORMAL >> simp[] >>
  disch_then $ qspecl_then [`SP l3 + sw2sw (1w : word1 @@ j)`,`X r1 l3`] mp_tac >>
  impl_tac
  >- (
    qpat_x_assum `(_ (_,_) _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
    ) >>
  simp[returnS] >> strip_tac >> simp[seqS, returnS]
QED

Theorem l3_models_asl_LoadStoreImmediate_8_NORMAL_STORE_FFFFF:
  ∀b w unsigned r2 r1.
    let instr =
      LoadStore (LoadStoreImmediate@8
        (0w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, unsigned, w, r2, r1))
    in (∀s. Encode instr ≠ BadCode s) ⇒ l3_models_asl_instr instr
Proof
  rw[encode_rws] >> gvs[load_store_encode_lemma]
  >- simp[l3_models_asl_LoadStoreImmediate_8_NORMAL_STORE_FFFFF_1] >>
  Cases_on `word_bit 8 w` >> gvs[] >> qpat_x_assum `w = _` SUBST_ALL_TAC
  >- (
    assume_tac l3_models_asl_LoadStoreImmediate_8_NORMAL_STORE_FFFFF_3 >>
    gvs[]
    )
  >- (
    `∃j : word8. (7 >< 0) w : word64 = w2w j` by (
      qexists_tac `(7 >< 0) w` >> blastLib.BBLAST_TAC) >>
    pop_assum SUBST_ALL_TAC >>
    simp[l3_models_asl_LoadStoreImmediate_8_NORMAL_STORE_FFFFF_2]
    )
QED


(****************************************)

val _ = export_theory();
