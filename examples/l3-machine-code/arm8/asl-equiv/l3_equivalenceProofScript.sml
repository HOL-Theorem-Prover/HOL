Theory l3_equivalenceProof
Ancestors
  armv86a armv86a_termination armv86a_types arm8 arm8_step words
  bitstring finite_map list arithmetic integer real intreal
  binary_ieeeProps
  l3_equivalence l3_equivalence_misc l3_equivalence_lemmas
Libs
  BasicProvers dep_rewrite arm8Lib arm8_stepLib wordsLib intLib RealField
  l3_equivalenceLib

Type res = ``:('a, exception) result # regstate sequential_state``;

(* Keep the real mantissa variables used below distinct from Props' constant. *)
val _ = Parse.temp_remove_ovl_mapping "mantissa"
  {Name = "mantissa", Thy = "binary_ieeeProps"};

(* Keep ASL's large finite sentinel for infinity symbolic. *)
val _ = diminish_srw_ss ["REAL_REDUCE", "RMULCANON", "RMULRELNORM"];

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

Theorem X_read16:
  ∀l3 asl. state_rel l3 asl ⇒
  ∀i. i ≥ 0 ∧ i ≤ 31 ⇒
  X_read 16 i asl = returnS (X (n2w (nat_of_int i)) l3 : word16) asl
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

Theorem V_read64:
  ∀l3 asl reg. state_rel l3 asl ⇒
    V_read 64 (&w2n reg) asl = (returnS (l3.FP_REG reg) asl : word64 res)
Proof
  rpt gen_tac >> strip_tac >>
  `(&w2n reg : int) ≥ 0 ∧ w2n reg ≤ 31` by
    (qspec_then `reg` mp_tac w2n_lt >> simp[] >> intLib.ARITH_TAC) >>
  simp[V_read_def, bindS, seqS, returnS, asl_reg_rws, asl_word_rws] >>
  `w2w (EL (w2n reg) (Z_ref.read_from asl.regstate)) = l3.FP_REG reg` by
    metis_tac[state_rel_def, fp_reg_rel_read] >>
  fs[Z_ref_def, WORD_w2w_EXTRACT, WORD_EXTRACT_MIN_HIGH]
QED

Theorem Z_set_state_rel:
  state_rel l3 asl ⇒
  state_rel (l3 with FP_REG := (reg =+ w2w value) l3.FP_REG)
    (asl with regstate :=
      Z_ref.write_to
        (LUPDATE value (w2n reg) (Z_ref.read_from asl.regstate)) asl.regstate)
Proof
  strip_tac >>
  `fp_reg_rel ((reg =+ w2w value) l3.FP_REG)
     (Z_ref.write_to
       (LUPDATE value (w2n reg) (Z_ref.read_from asl.regstate)) asl.regstate)` by
    metis_tac[state_rel_def, fp_reg_rel_write] >>
  gvs[state_rel_def, read_rel_def, reg_rel_def, asl_reg_rws]
QED

Theorem IsInHost_F:
  asl_sys_regs_ok asl ⇒ IsInHost () asl = returnS F asl
Proof
  strip_tac >>
  `∀el. ELIsInHost el asl = returnS F asl` by
    (gen_tac >> irule ELIsInHost_F >> gvs[asl_sys_regs_ok_def]) >>
  simp[IsInHost_def, bindS, returnS, asl_reg_rws]
QED

Theorem EL2Enabled_T:
  asl_sys_regs_ok asl ⇒ EL2Enabled () asl = returnS T asl
Proof
  rw[asl_sys_regs_ok_def] >>
  simp[EL2Enabled_def, bindS, returnS, asl_sys_reg_rws, asl_word_rws,
       extract_bit_64]
QED

Theorem VL_read_total:
  asl_sys_regs_ok asl ⇒ ∃vl. VL_read () asl = returnS vl asl
Proof
  strip_tac >>
  drule IsInHost_F >> strip_tac >>
  drule EL2Enabled_T >> strip_tac >>
  namedCases_on `(asl.regstate.ProcState_reg "PSTATE").ProcState_EL`
    ["level"] >>
  gvs[NUMERAL_LESS_THM] >>
  simp[VL_read_def, bindS, returnS, asl_reg_rws,
       ZCR_EL1_ref_def, ZCR_EL2_ref_def, ZCR_EL3_ref_def]
QED

Theorem IsSVEEnabled_total:
  asl_sys_regs_ok asl ⇒
  ∃sve. IsSVEEnabled (PSTATE_ref.read_from asl.regstate).ProcState_EL asl =
    returnS sve asl
Proof
  strip_tac >>
  drule IsInHost_F >> strip_tac >>
  drule EL2Enabled_T >> strip_tac >>
  `ELUsingAArch32 (asl.regstate.ProcState_reg "PSTATE").ProcState_EL asl =
     returnS F asl` by
    (irule ELUsingAArch32_F >> gvs[asl_sys_regs_ok_def]) >>
  `¬word_bit 34 (asl.regstate.bitvector_64_dec_reg "HCR_EL2")` by
    fs[asl_sys_regs_ok_def] >>
  fs[asl_reg_rws] >>
  namedCases_on `(asl.regstate.ProcState_reg "PSTATE").ProcState_EL`
    ["level"] >>
  gvs[NUMERAL_LESS_THM] >>
  simp[IsSVEEnabled_def, CPACR_read_def, bindS, seqS, returnS,
       asl_reg_rws, asl_sys_reg_rws, asl_word_rws, extract_bit_64,
       sail2_state_monadTheory.undefined_boolS_def,
       sail2_state_monadTheory.catch_early_returnS_def,
       sail2_state_monadTheory.liftRS_def,
       sail2_state_monadTheory.early_returnS_def,
       sail2_state_monadTheory.try_catchS_def,
       sail2_state_monadTheory.throwS_def] >>
  Cases_on
    `(8 >< 8) (asl.regstate.bitvector_32_dec_reg "CPTR_EL3") = (0w : word1)` >>
  gvs[returnS, sail2_state_monadTheory.throwS_def] >>
  Cases_on
    `(8 >< 8) (asl.regstate.bitvector_32_dec_reg "CPTR_EL2") = (1w : word1)` >>
  gvs[returnS, sail2_state_monadTheory.throwS_def] >>
  namedCases_on
    `((17 >< 16) (asl.regstate.bitvector_32_dec_reg "CPACR_EL1") : word2)`
    ["control"] >>
  gvs[NUMERAL_LESS_THM, bindS, seqS, returnS,
      sail2_state_monadTheory.try_catchS_def,
      sail2_state_monadTheory.throwS_def]
QED

Theorem V_set64:
  ∀asl (reg : word5) (value : word64) vl sve.
    VL_read () asl = returnS vl asl ∧
    IsSVEEnabled (PSTATE_ref.read_from asl.regstate).ProcState_EL asl =
      returnS sve asl ⇒
    V_set 64 (&w2n reg) value asl =
      returnS () (asl with regstate :=
        Z_ref.write_to
          (LUPDATE (w2w value) (w2n reg) (Z_ref.read_from asl.regstate))
          asl.regstate)
Proof
  rpt gen_tac >> strip_tac >>
  `(&w2n reg : int) ≥ 0 ∧ w2n reg ≤ 31` by
    (qspec_then `reg` mp_tac w2n_lt >> simp[] >> intLib.ARITH_TAC) >>
  fs[asl_reg_rws] >>
  simp[V_set_def, ConstrainUnpredictableBool_def, ConstrainUnpredictable_def,
       bindS, seqS, returnS, asl_reg_rws, asl_word_rws]
QED

Theorem V_set64_state_rel:
  ∀l3 asl (reg : word5) (value : word64).
    state_rel l3 asl ∧ asl_sys_regs_ok asl ⇒
    ∃asl'.
      V_set 64 (&w2n reg) value asl = returnS () asl' ∧
      state_rel (l3 with FP_REG := (reg =+ value) l3.FP_REG) asl' ∧
      asl_sys_regs_ok asl'
Proof
  rpt gen_tac >> strip_tac >>
  drule VL_read_total >> disch_then (qx_choose_then `vl` assume_tac) >>
  drule IsSVEEnabled_total >> disch_then (qx_choose_then `sve` assume_tac) >>
  qspecl_then [`asl`, `reg`, `value`, `vl`, `sve`] mp_tac V_set64 >>
  simp[] >> strip_tac >>
  qexists_tac `asl with regstate :=
    Z_ref.write_to
      (LUPDATE (w2w value) (w2n reg) (Z_ref.read_from asl.regstate))
      asl.regstate` >>
  simp[] >> conj_tac
  >- (
    mp_tac (INST
      [``value : 2048 word`` |-> ``w2w (value : word64) : 2048 word``]
      Z_set_state_rel) >>
    simp[w2w_w2w, WORD_BITS_MIN_HIGH, WORD_ALL_BITS]) >>
  gvs[asl_sys_regs_ok_def, Z_ref_def]
QED

Theorem CheckFPAdvSIMDEnabled64_ok:
  asl_sys_regs_ok asl ⇒ CheckFPAdvSIMDEnabled64 () asl = returnS () asl
Proof
  strip_tac >>
  drule IsInHost_F >> strip_tac >>
  drule EL2Enabled_T >> strip_tac >>
  `¬word_bit 34 (asl.regstate.bitvector_64_dec_reg "HCR_EL2") ∧
   (21 >< 20) (asl.regstate.bitvector_32_dec_reg "CPACR_EL1") = (3w : word2) ∧
   (10 >< 10) (asl.regstate.bitvector_32_dec_reg "CPTR_EL2") = (0w : word1) ∧
   (10 >< 10) (asl.regstate.bitvector_32_dec_reg "CPTR_EL3") = (0w : word1)` by
    (fs[asl_sys_regs_ok_def] >> blastLib.BBLAST_TAC >> fs[word_bit]) >>
  fs[] >>
  namedCases_on `(asl.regstate.ProcState_reg "PSTATE").ProcState_EL`
    ["level"] >>
  gvs[NUMERAL_LESS_THM] >>
  simp[CheckFPAdvSIMDEnabled64_def, AArch64_CheckFPAdvSIMDEnabled_def,
       AArch64_CheckFPAdvSIMDTrap_def, CPACR_read_def,
       sail2_state_monadTheory.undefined_boolS_def,
       bindS, seqS, returnS, asl_reg_rws, asl_sys_reg_rws, asl_word_rws,
       extract_bit_64]
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

Theorem FPCR_read:
  ∀l3 asl. state_rel l3 asl ⇒
    read_regS FPCR_ref asl = returnS l3.FPCR asl
Proof
  rw[asl_reg_rws] >> state_rel_tac[]
QED

Theorem FPSR_read:
  ∀l3 asl. state_rel l3 asl ⇒
    read_regS FPSR_ref asl = returnS l3.FPSR asl
Proof
  rw[asl_reg_rws] >> state_rel_tac[]
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

Theorem realPowInteger_of_num:
  ∀exponent base. realPowInteger base (&exponent) = base pow exponent
Proof
  Induct >> gen_tac >>
  once_rewrite_tac[armv86a_terminationTheory.realPowInteger_def] >>
  simp[INT_GT, INT_LT, INT_SUB, realTheory.pow, REAL_MUL_COMM]
QED

Theorem realPowInteger_neg_of_num:
  ∀exponent base. realPowInteger base (-&exponent) = inv (base pow exponent)
Proof
  Induct >> gen_tac >>
  once_rewrite_tac[armv86a_terminationTheory.realPowInteger_def] >>
  simp[INT_GT, INT_NEG_GT0, INT_LT, realTheory.pow] >>
  `(-&SUC exponent + 1 : int) = -&exponent` by
    (simp[ADD1, GSYM INT_ADD] >> intLib.ARITH_TAC) >> simp[] >>
  Cases_on `base = 0` >>
  simp[real_div, REAL_INV_MUL, POW_NZ, REAL_MUL_COMM]
QED

Theorem realPowInteger_sub_of_num:
  ∀left right base. base ≠ 0 ⇒
    realPowInteger base (&left - &right) = base pow left / base pow right
Proof
  Induct_on `right` >> rpt gen_tac >> strip_tac
  >- simp[realPowInteger_of_num] >>
  namedCases_on `left` ["", "previous"]
  >- simp[INT_SUB_LZERO, realPowInteger_neg_of_num, real_div] >>
  `(&SUC previous - &SUC right : int) = &previous - &right` by
    (simp[ADD1, GSYM INT_ADD] >> intLib.ARITH_TAC) >>
  simp[realTheory.pow, REAL_DIV_LMUL_CANCEL]
QED

Theorem real_pow_suc_scale:
  ∀base exponent. base ≠ 0 ⇒
    base / base pow SUC exponent = inv (base pow exponent)
Proof
  rpt strip_tac >>
  simp[realTheory.pow, real_div, REAL_INV_MUL, POW_NZ,
       REAL_MUL_ASSOC, REAL_MUL_RINV]
QED

Theorem normalize_halving:
  !n (exponent : int) (mantissa : real).
    1 <= mantissa /\ mantissa < 2 ==>
    sail2_values$while (exponent, mantissa * 2 pow n)
      (\(e, m). 2 <= m) (\(e, m). (e + 1, m / 2)) =
    (exponent + &n, mantissa)
Proof
  Induct
  >- (
    qx_genl_tac [`exponent`, `mantissa`]
    \\ strip_tac
    \\ simp [realTheory.pow, Once sail2_valuesTheory.while_def,
             GSYM realTheory.REAL_NOT_LT])
  \\ qx_genl_tac [`exponent`, `mantissa`]
  \\ strip_tac
  \\ `1 <= (2 : real) pow n` by simp [realTheory.REAL_POW_LE_1]
  \\ `1 <= mantissa * 2 pow n` by (
    qspecl_then [`1`, `mantissa`, `1`, `2 pow n`] mp_tac realTheory.REAL_LE_MUL2
    \\ simp [])
  \\ `2 <= mantissa * 2 pow SUC n` by (
    simp [realTheory.pow]
    \\ qpat_x_assum `1 <= mantissa * 2 pow n` mp_tac
    \\ RealField.REAL_ARITH_TAC)
  \\ simp [Once sail2_valuesTheory.while_def]
  \\ `mantissa * 2 pow SUC n / 2 = mantissa * 2 pow n` by (
    simp [realTheory.pow]
    \\ RealField.REAL_ARITH_TAC)
  \\ simp [integerTheory.INT, integerTheory.INT_ADD_ASSOC,
           integerTheory.INT_ADD_COMM]
QED

Theorem normalize_doubling:
  !n (exponent : int) (mantissa : real).
    1 <= mantissa /\ mantissa < 2 ==>
    sail2_values$while (exponent, mantissa / 2 pow n)
      (\(e, m). m < 1) (\(e, m). (e - 1, m * 2)) =
    (exponent - &n, mantissa)
Proof
  Induct
  >- (
    qx_genl_tac [`exponent`, `mantissa`]
    \\ strip_tac
    \\ simp [realTheory.pow, Once sail2_valuesTheory.while_def,
             GSYM realTheory.REAL_NOT_LE])
  \\ qx_genl_tac [`exponent`, `mantissa`]
  \\ strip_tac
  \\ `1 <= (2 : real) pow n` by simp [realTheory.REAL_POW_LE_1]
  \\ `0 < (2 : real) pow SUC n` by simp [realTheory.REAL_POW_LT]
  \\ `2 <= (2 : real) pow SUC n` by (
    simp [realTheory.pow]
    \\ qpat_x_assum `1 <= (2 : real) pow n` mp_tac
    \\ RealField.REAL_ARITH_TAC)
  \\ `mantissa / 2 pow SUC n < 1` by (
    simp [realTheory.REAL_LT_LDIV_EQ]
    \\ irule realTheory.REAL_LTE_TRANS
    \\ qexists_tac `2`
    \\ simp [])
  \\ simp [Once sail2_valuesTheory.while_def]
  \\ `mantissa / 2 pow SUC n * 2 = mantissa / 2 pow n` by (
    simp [realTheory.pow]
    \\ RealField.REAL_FIELD_TAC)
  \\ full_simp_tac std_ss
       [realTheory.REAL_MUL_COMM, realTheory.real_div,
        integerTheory.INT, integerTheory.INT_SUB, integerTheory.INT_ADD_ASSOC,
        integerTheory.INT_ADD_COMM]
  \\ intLib.ARITH_TAC
QED

Theorem normalized_large_exists:
  !magnitude : real.
    1 <= magnitude ==>
    ?n mantissa. 1 <= mantissa /\ mantissa < 2 /\
                 magnitude = mantissa * 2 pow n
Proof
  qx_gen_tac `magnitude`
  \\ strip_tac
  \\ qspec_then `\n:num. (magnitude : real) < 2 pow n`
    (fn th => qspec_then `magnitude : real`
      (strip_assume_tac o MP (BETA_RULE th)) realTheory.REAL_ARCH_POW2)
    WhileTheory.LEAST_EXISTS_IMP
  \\ qabbrev_tac `least_power = LEAST n. magnitude < 2 pow n`
  \\ namedCases_on `least_power` ["", "power"]
  >- (
    fs [realTheory.pow]
    \\ RealField.REAL_ASM_ARITH_TAC)
  \\ `2 pow power <= magnitude` by (
    qpat_assum `!n. n < SUC power ==> _` (qspec_then `power` mp_tac)
    \\ simp [GSYM realTheory.REAL_NOT_LT])
  \\ `0 < (2 : real) pow power` by simp [realTheory.REAL_POW_LT]
  \\ `(2 : real) pow power <> 0` by simp [realTheory.POW_NZ]
  \\ qexistsl_tac [`power`, `magnitude / 2 pow power`]
  \\ asm_simp_tac std_ss
       [realTheory.REAL_LE_RDIV_EQ, realTheory.REAL_LT_LDIV_EQ,
        realTheory.REAL_MUL_LID, realTheory.REAL_DIV_RMUL]
  \\ fs [realTheory.pow]
QED

Theorem normalized_small_exists:
  !magnitude : real.
    0 < magnitude /\ magnitude < 1 ==>
    ?n mantissa. 1 <= mantissa /\ mantissa < 2 /\
                 magnitude = mantissa / 2 pow n
Proof
  qx_gen_tac `magnitude`
  \\ strip_tac
  \\ qspec_then `inv (magnitude : real)`
       (qx_choose_then `bound` assume_tac) realTheory.REAL_ARCH_POW2
  \\ Q.SUBGOAL_THEN `?n. 1 <= magnitude * 2 pow n` ASSUME_TAC
  >- (
    qexists_tac `bound`
    \\ fs [realTheory.REAL_INV_1OVER, realTheory.REAL_LT_LDIV_EQ]
    \\ qpat_x_assum `1 / magnitude < _` mp_tac
    \\ asm_simp_tac std_ss [realTheory.REAL_LT_LDIV_EQ]
    \\ RealField.REAL_ARITH_TAC)
  \\ qspec_then `\n:num. 1 <= (magnitude : real) * 2 pow n`
       (mp_tac o BETA_RULE) WhileTheory.LEAST_EXISTS_IMP
  \\ asm_simp_tac std_ss []
  \\ qabbrev_tac `least_power = LEAST n. 1 <= magnitude * 2 pow n`
  \\ strip_tac
  \\ namedCases_on `least_power` ["", "power"]
  >- (
    fs [realTheory.pow]
    \\ RealField.REAL_ASM_ARITH_TAC)
  \\ `magnitude * 2 pow power < 1` by (
    qpat_assum `!n. n < SUC power ==> _` (qspec_then `power` mp_tac)
    \\ simp [GSYM realTheory.REAL_NOT_LE])
  \\ `magnitude * 2 pow SUC power < 2` by (
    simp_tac std_ss [realTheory.pow]
    \\ qpat_assum `magnitude * 2 pow power < 1` mp_tac
    \\ RealField.REAL_ARITH_TAC)
  \\ `0 < (2 : real) pow SUC power` by simp [realTheory.REAL_POW_LT]
  \\ qexistsl_tac [`SUC power`, `magnitude * 2 pow SUC power`]
  \\ asm_simp_tac std_ss [realTheory.REAL_EQ_RDIV_EQ]
QED

Theorem FPRound_normalize:
  !magnitude : real.
    0 < magnitude ==>
    let initial = sail2_values$while (0 : int, magnitude)
      (\(e, m). m < 1) (\(e, m). (e - 1, m * 2)) in
    let result = sail2_values$while initial
      (\(e, m). 2 <= m) (\(e, m). (e + 1, m / 2)) in
    1 <= SND result /\ SND result < 2 /\
    magnitude = SND result * realPowInteger 2 (FST result)
Proof
  qx_gen_tac `magnitude`
  \\ strip_tac
  \\ Cases_on `magnitude < 1`
  >- (
    qspec_then `magnitude` mp_tac normalized_small_exists
    \\ impl_tac >- simp []
    \\ disch_then (qx_choosel_then [`power`, `mantissa`] strip_assume_tac)
    \\ `sail2_values$while (0 : int, magnitude)
         (\(e, m). m < 1) (\(e, m). (e - 1, m * 2)) =
         (-&power, mantissa)` by (
      qspecl_then [`power`, `0`, `mantissa`] mp_tac normalize_doubling
      \\ simp [])
    \\ `sail2_values$while (-&power : int, mantissa)
         (\(e, m). 2 <= m) (\(e, m). (e + 1, m / 2)) =
         (-&power, mantissa)` by
      simp [Once sail2_valuesTheory.while_def, GSYM realTheory.REAL_NOT_LT]
    \\ asm_simp_tac std_ss
         [LET_THM, pairTheory.FST, pairTheory.SND,
          realPowInteger_neg_of_num, GSYM realTheory.real_div])
  \\ `sail2_values$while (0 : int, magnitude)
     (\(e, m). m < 1) (\(e, m). (e - 1, m * 2)) =
     (0, magnitude)` by simp [Once sail2_valuesTheory.while_def]
  \\ `1 <= magnitude` by fs [GSYM realTheory.REAL_NOT_LT]
  \\ qspec_then `magnitude` mp_tac normalized_large_exists
  \\ simp []
  \\ disch_then (qx_choosel_then [`power`, `mantissa`] strip_assume_tac)
  \\ full_simp_tac std_ss
       [LET_THM, pairTheory.FST, pairTheory.SND, normalize_halving,
        integerTheory.INT_ADD_LID, realPowInteger_of_num]
QED

Theorem nearest_even_error_bound:
  !lower : int. !error : real. !tie_up.
    0 <= error /\ error < 1 ==>
    let rounded =
      if 1 / 2 < error \/ error = 1 / 2 /\ tie_up then lower + 1 else lower in
    abs (real_of_int rounded - (real_of_int lower + error)) <= 1 / 2 /\
    (abs (real_of_int rounded - (real_of_int lower + error)) = 1 / 2 ==>
     error = 1 / 2)
Proof
  qx_genl_tac [`lower`, `error`, `tie_up`]
  \\ strip_tac
  \\ Cases_on `1 / 2 < error \/ error = 1 / 2 /\ tie_up`
  \\ asm_simp_tac std_ss
       [LET_THM, intrealTheory.real_of_int_add, intrealTheory.real_of_int_num]
  >- (
    `0 <= 1 - error` by RealField.REAL_ASM_ARITH_TAC
    \\ asm_simp_tac std_ss
         [REAL_ARITH ``(a : real) + 1 - (a + b) = 1 - b``, realTheory.abs]
    \\ RealField.REAL_ASM_ARITH_TAC)
  \\ `error <= 1 / 2` by (
    qpat_x_assum `~(1 / 2 < error ∨ _)` mp_tac >>
    simp[DE_MORGAN_THM, realTheory.REAL_NOT_LT]) >>
  asm_simp_tac std_ss
    [REAL_ARITH ``(a : real) - (a + b) = -b``, realTheory.ABS_NEG] >>
  asm_simp_tac std_ss [realTheory.abs]
QED

Theorem integer_access_nat_zero:
  !n. (vec_of_bits [integer_access (&n) 0] : word1) =
      if ODD n then 1w else 0w
Proof
  qx_gen_tac `n`
  \\ once_rewrite_tac [armv86aTheory.integer_access_def]
  \\ once_rewrite_tac
       [SIMP_RULE std_ss [wordsTheory.DIMINDEX_GT_0]
          (Q.INST [`i` |-> `0`] vec_of_bits_access_vec_dec_single)]
  \\ simp[integer_subrange_pos, bitstringTheory.field_fixwidth,
       bitstringTheory.fixwidth_fixwidth,
       INST_TYPE [alpha |-> ``:1``] bitstringTheory.v2w_fixwidth
         |> SIMP_RULE (srw_ss()) [], bitstringTheory.v2w_n2v,
       wordsTheory.word_extract_n2w, bitTheory.BITS_THM,
       arithmeticTheory.MOD_2, arithmeticTheory.ODD_EVEN] >>
  Cases_on `EVEN n` >> simp[]
QED

Definition fp64_pow2_def:
  fp64_pow2 (exponent : int) =
    if 0 <= exponent then (2 : real) pow Num exponent
    else inv (2 pow Num (-exponent))
End

Definition fp64_round_quantize_def:
  fp64_round_quantize mode negative (exponent : int, mantissa : real) =
    let biased = if exponent + 1023 < 0 then 0 else exponent + 1023 in
    let scaled = if biased = 0 then
        mantissa / fp64_pow2 (-1022 - exponent) else mantissa in
    let lower = Num (flr (scaled * 2 pow 52)) in
    let error = scaled * 2 pow 52 - &lower in
    let round_up =
      case mode of
        roundTiesToEven => 1 / 2 < error ∨ error = 1 / 2 ∧ ODD lower
      | roundTowardPositive => error <> 0 ∧ ~negative
      | roundTowardNegative => error <> 0 ∧ negative
      | roundTowardZero => F in
    let to_infinity = (mode = roundTiesToEven ∨
      mode = roundTowardPositive ∧ ~negative ∨
      mode = roundTowardNegative ∧ negative) in
    let rounded = if round_up then SUC lower else lower in
    let biased = if round_up ∧ rounded = 2 ** 52 then 1 else biased in
    let (biased, rounded) =
      if round_up ∧ rounded = 2 ** 53 then (biased + 1, 2 ** 52)
      else (biased, rounded) in
    let overflow = (2047 <= biased) in
    let sign = if negative then (1w : word1) else 0w in
    let result =
      if overflow then
        machine_ieee$float_to_fp64
          <| Sign := sign;
             Exponent := if to_infinity then 2047w else 2046w;
             Significand := if to_infinity then 0w else -1w |>
      else
        machine_ieee$float_to_fp64
          <| Sign := sign; Exponent := n2w (Num biased);
             Significand := n2w rounded |> in
    (exponent < -1022 ∧ error <> 0, overflow, error <> 0 ∨ overflow, result)
End

Theorem fp64_pow2_of_num:
  !n. fp64_pow2 (&n) = (2 : real) pow n
Proof
  simp [fp64_pow2_def]
QED

Theorem fp64_pow2_neg_of_num:
  !n. fp64_pow2 (-&n) = inv ((2 : real) pow n)
Proof
  qx_gen_tac `n`
  \\ namedCases_on `n` ["", "previous"]
  \\ simp [fp64_pow2_def, realTheory.pow, realTheory.REAL_INV1]
QED

Theorem fp64_pow2_positive:
  !exponent. 0 < fp64_pow2 exponent
Proof
  qx_gen_tac `exponent`
  \\ qspec_then `exponent` strip_assume_tac integerTheory.INT_NUM_CASES
  \\ gvs [fp64_pow2_def, realTheory.REAL_POW_LT,
          realTheory.REAL_LT_INV_EQ, realTheory.pow]
QED

Theorem fp64_pow2_successor:
  !exponent. fp64_pow2 (exponent + 1) = 2 * fp64_pow2 exponent
Proof
  qx_gen_tac `exponent`
  \\ qspec_then `exponent` strip_assume_tac integerTheory.INT_NUM_CASES
  \\ gvs [fp64_pow2_of_num, fp64_pow2_neg_of_num,
          integerTheory.INT_ADD, GSYM arithmeticTheory.ADD1, realTheory.pow]
  \\ rename1 `fp64_pow2 (-&index + 1)`
  \\ namedCases_on `index` ["", "previous"] >- fs []
  \\ `(-&SUC previous + 1 : int) = -&previous` by (
    simp [arithmeticTheory.ADD1, GSYM integerTheory.INT_ADD]
    \\ intLib.ARITH_TAC)
  \\ simp [fp64_pow2_neg_of_num, realTheory.pow, realTheory.REAL_INV_MUL,
           realTheory.REAL_MUL_ASSOC, realTheory.REAL_MUL_RINV]
QED

Theorem fp64_pow2_add_nat:
  !n exponent.
    fp64_pow2 (exponent + &n) = fp64_pow2 exponent * 2 pow n
Proof
  Induct
  \\ gen_tac
  \\ simp [integerTheory.INT, integerTheory.INT_ADD_ASSOC,
           fp64_pow2_successor, realTheory.pow]
  \\ RealField.REAL_ARITH_TAC
QED

Theorem fp64_pow2_monotone:
  !left right. left <= right ==> fp64_pow2 left <= fp64_pow2 right
Proof
  qx_genl_tac [`left`, `right`]
  \\ strip_tac
  \\ Q.SUBGOAL_THEN `?distance. right = left + &distance`
       (qx_choose_then `distance` strip_assume_tac)
  >- (
    qexists_tac `Num (right - left)`
    \\ `0 <= right - left` by intLib.ARITH_TAC
    \\ `(&Num (right - left) : int) = right - left` by simp []
    \\ intLib.ARITH_TAC)
  \\ gvs [fp64_pow2_add_nat]
  \\ `0 < fp64_pow2 left` by simp [fp64_pow2_positive]
  \\ `1 <= (2 : real) pow distance` by simp [realTheory.REAL_POW_LE_1]
  \\ qspecl_then [`fp64_pow2 left`, `1`, `(2 : real) pow distance`]
       mp_tac realTheory.REAL_LE_LMUL
  \\ asm_simp_tac std_ss [realTheory.REAL_MUL_RID]
QED

Theorem normalized_pow2_threshold:
  !exponent mantissa bound.
    1 <= mantissa /\ mantissa < 2 ==>
    (mantissa * fp64_pow2 exponent < fp64_pow2 bound <=> exponent < bound)
Proof
  qx_genl_tac [`exponent`, `mantissa`, `bound`]
  \\ strip_tac
  \\ `0 < fp64_pow2 exponent` by simp [fp64_pow2_positive]
  \\ `0 <= fp64_pow2 exponent` by (irule realTheory.REAL_LT_IMP_LE \\ simp [])
  \\ Cases_on `exponent < bound`
  >- (
    simp []
    \\ irule realTheory.REAL_LTE_TRANS
    \\ qexists_tac `fp64_pow2 (exponent + 1)`
    \\ conj_tac
    >- (
      simp_tac std_ss [fp64_pow2_successor]
      \\ qspecl_then [`mantissa`, `2`, `fp64_pow2 exponent`]
           mp_tac realTheory.REAL_LT_RMUL_IMP
      \\ asm_simp_tac std_ss [])
    \\ irule fp64_pow2_monotone
    \\ intLib.ARITH_TAC)
  \\ asm_simp_tac std_ss [realTheory.REAL_NOT_LT]
  \\ irule realTheory.REAL_LE_TRANS
  \\ qexists_tac `fp64_pow2 exponent`
  \\ conj_tac
  >- (irule fp64_pow2_monotone \\ intLib.ARITH_TAC)
  \\ qspecl_then [`fp64_pow2 exponent`, `1`, `mantissa`]
       mp_tac realTheory.REAL_LE_RMUL_IMP
  \\ asm_simp_tac std_ss [realTheory.REAL_MUL_LID]
QED


Theorem nonnegative_floor_nat:
  ∀scaled : real. 0 <= scaled ⇒
    0 <= intreal$INT_FLOOR scaled ∧
    (&Num (flr scaled) : int) = flr scaled ∧
    (&Num (flr scaled) : real) = real_of_int (flr scaled)
Proof
  qx_gen_tac `scaled` >> strip_tac >>
  drule intrealTheory.INT_NUM_FLOOR >>
  disch_then (fn floor_equation => rewrite_tac [GSYM floor_equation]) >>
  simp[intrealTheory.real_of_int_num]
QED

Theorem fp64_round_carry_int_nat:
  ∀biased : int. ∀lower : int. ∀increment.
    0 <= lower ⇒
    let rounded = if increment then SUC (Num lower) else Num lower in
    let target_biased =
      if increment ∧ rounded = 2 ** 52 then 1 else biased in
    (if increment then
       if lower + 1 = &(2 ** 53) then (biased + 1, &(2 ** 52))
       else (if lower + 1 = &(2 ** 52) then 1 else biased, lower + 1)
     else (biased, lower)) =
    (if increment ∧ rounded = 2 ** 53 then
       (target_biased + 1, &(2 ** 52))
     else (target_biased, &rounded))
Proof
  qx_genl_tac [`biased`, `lower`, `increment`] >> strip_tac >>
  Q.SUBGOAL_THEN `∃natural. lower = &natural`
    (qx_choose_then `natural` assume_tac)
  >- (qexists_tac `Num lower` >> simp[]) >>
  gvs[] >>
  Cases_on `increment` >>
  simp[LET_THM, arithmeticTheory.ADD1] >>
  simp_tac std_ss [integerTheory.INT_ADD, integerTheory.INT_INJ]
QED

Theorem fp64_quantize_floor:
  ∀exponent mantissa.
    1 <= mantissa ⇒
    let biased = if exponent + 1023 < 0 then 0 else exponent + 1023 in
    let scaled =
      (if biased = 0 then mantissa / fp64_pow2 (-1022 - exponent)
       else mantissa) * 2 pow 52 in
    let lower = Num (flr scaled) in
    0 < scaled ∧
    (&lower : int) = flr scaled ∧
    (&lower : real) = real_of_int (flr scaled) ∧
    0 <= scaled - &lower ∧ scaled - &lower < 1
Proof
  qx_genl_tac [`exponent`, `mantissa`] >> strip_tac >>
  `0 < mantissa` by RealField.REAL_ASM_ARITH_TAC >>
  simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `flr scaled` >>
  `0 < scaled` by (
    simp_tac std_ss [Abbr `scaled`] >>
    irule realTheory.REAL_LT_MUL >>
    simp_tac std_ss [realTheory.REAL_POW_LT, EVAL ``(0 : real) < 2``] >>
    Cases_on `(if exponent + 1023 < 0 then 0 else exponent + 1023) = 0` >>
    simp[realTheory.REAL_LT_DIV, fp64_pow2_positive]) >>
  `0 <= scaled` by RealField.REAL_ASM_ARITH_TAC >>
  drule nonnegative_floor_nat >> strip_tac >>
  qspec_then `scaled` mp_tac intrealTheory.INT_FLOOR_BOUNDS >>
  asm_simp_tac std_ss
    [intrealTheory.real_of_int_add, intrealTheory.real_of_int_num] >>
  RealField.REAL_ARITH_TAC
QED

Theorem fp64_round_quantize_int_fields:
  ∀mode negative exponent mantissa.
    1 <= mantissa ⇒
    let biased = if exponent + 1023 < 0 then 0 else exponent + 1023 in
    let scaled =
      (if biased = 0 then mantissa / fp64_pow2 (-1022 - exponent)
       else mantissa) * 2 pow 52 in
    let lower : int = flr scaled in
    let error = scaled - real_of_int lower in
    let increment = case mode of
      roundTiesToEven => 1 / 2 < error ∨ error = 1 / 2 ∧ ODD (Num lower)
    | roundTowardPositive => error <> 0 ∧ ¬negative
    | roundTowardNegative => error <> 0 ∧ negative
    | roundTowardZero => F in
    let to_infinity =
      (mode = roundTiesToEven ∨ mode = roundTowardPositive ∧ ¬negative ∨
       mode = roundTowardNegative ∧ negative) in
    let (result_exponent, result_mantissa) =
      if increment then
        if lower + 1 = &(2 ** 53) then (biased + 1, &(2 ** 52))
        else (if lower + 1 = &(2 ** 52) then 1 else biased, lower + 1)
      else (biased, lower) in
    let overflow = (2047 <= result_exponent) in
    let sign = if negative then (1w : word1) else 0w in
    let result =
      if overflow then
        float_to_fp64
          <|Sign := sign; Exponent := if to_infinity then 2047w else 2046w;
            Significand := if to_infinity then 0w else -1w|>
      else
        float_to_fp64
          <|Sign := sign; Exponent := n2w (Num result_exponent);
            Significand := n2w (Num result_mantissa)|> in
    fp64_round_quantize mode negative (exponent, mantissa) =
      (biased = 0 ∧ error <> 0, overflow, error <> 0 ∨ overflow, result)
Proof
  qx_genl_tac [`mode`, `negative`, `exponent`, `mantissa`] >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `flr scaled` >>
  qmatch_goalsub_abbrev_tac `if increment then _ else (_, flr scaled)` >>
  `0 < scaled ∧
   (&Num (flr scaled) : int) = flr scaled ∧
   (&Num (flr scaled) : real) = real_of_int (flr scaled) ∧
   0 <= scaled - &Num (flr scaled) ∧ scaled - &Num (flr scaled) < 1` by (
    qspecl_then [`exponent`, `mantissa`] mp_tac fp64_quantize_floor >>
    simp[LET_THM, Abbr `scaled`]) >>
  `0 <= intreal$INT_FLOOR scaled` by (
    qpat_x_assum `(&Num (flr scaled) : int) = flr scaled`
      (fn floor_cast => once_rewrite_tac [GSYM floor_cast]) >>
    simp[]) >>
  qspecl_then
    [`if exponent + 1023 < 0 then 0 else exponent + 1023`,
     `flr scaled`, `increment`] mp_tac fp64_round_carry_int_nat >>
  asm_simp_tac std_ss
    [LET_THM, EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``] >>
  disch_then SUBST1_TAC >>
  qpat_x_assum `Abbrev (scaled = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (increment ⇔ _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_simp_tac std_ss [fp64_round_quantize_def, LET_THM] >>
  `((if exponent + 1023 < 0 then 0 else exponent + 1023) = 0) ⇔
    exponent < -1022` by (
    Cases_on `exponent + 1023 < 0` >>
    simp[] >> intLib.ARITH_TAC) >>
  Cases_on `increment` >>
  asm_simp_tac std_ss [LET_THM] >>
  simp[LET_THM] >>
  Cases_on `SUC (Num (flr scaled)) = 2 ** 53` >>
  fs[LET_THM]
QED


Theorem closest_greater_nonzero:
  ∀source (candidate : (52, 11) float).
    float_is_finite candidate ∧ ¬float_is_zero candidate ∧
    source <= float_to_real candidate ∧
    (∀other : (52, 11) float.
      float_is_finite other ∧ source <= float_to_real other ⇒
      float_to_real candidate <= float_to_real other) ⇒
    closest {other | float_is_finite other ∧ source <= float_to_real other}
      source = candidate
Proof
  qx_genl_tac [`source`, `candidate`] >> strip_tac >>
  simp_tac std_ss [binary_ieeeTheory.closest_def,
                  binary_ieeeTheory.closest_such_def, combinTheory.K_THM] >>
  irule SELECT_UNIQUE >> qx_gen_tac `other` >>
  eq_tac
  >- (
    simp_tac std_ss [binary_ieeeTheory.is_closest_def,
                     pred_setTheory.GSPECIFICATION] >> strip_tac >>
    `float_to_real candidate <= float_to_real other` by (
      qpat_x_assum `∀comparison. _ ⇒
        float_to_real candidate <= float_to_real comparison`
        (qspec_then `other` mp_tac) >> simp[]) >>
    `abs (float_to_real other - source) <=
     abs (float_to_real candidate - source)` by (
      qpat_x_assum `∀comparison. _ ⇒
        abs (float_to_real other - source) <=
        abs (float_to_real comparison - source)`
        (qspec_then `candidate` mp_tac) >> simp[]) >>
    `float_to_real other = float_to_real candidate` by
      RealField.REAL_ASM_ARITH_TAC >>
    gvs[binary_ieeeTheory.float_to_real_eq]) >>
  strip_tac >>
  gvs[binary_ieeeTheory.is_closest_def, pred_setTheory.GSPECIFICATION] >>
  qx_gen_tac `comparison` >> strip_tac >>
  `float_to_real candidate <= float_to_real comparison` by (
    qpat_x_assum `∀other. _ ⇒ float_to_real candidate <= float_to_real other`
      (qspec_then `comparison` mp_tac) >> simp[]) >>
  RealField.REAL_ASM_ARITH_TAC
QED

Theorem closest_less_nonzero:
  ∀source (candidate : (52, 11) float).
    float_is_finite candidate ∧ ¬float_is_zero candidate ∧
    float_to_real candidate <= source ∧
    (∀other : (52, 11) float.
      float_is_finite other ∧ float_to_real other <= source ⇒
      float_to_real other <= float_to_real candidate) ⇒
    closest {other | float_is_finite other ∧ float_to_real other <= source}
      source = candidate
Proof
  qx_genl_tac [`source`, `candidate`] >> strip_tac >>
  simp_tac std_ss [binary_ieeeTheory.closest_def,
                  binary_ieeeTheory.closest_such_def, combinTheory.K_THM] >>
  irule SELECT_UNIQUE >> qx_gen_tac `other` >>
  eq_tac
  >- (
    simp_tac std_ss [binary_ieeeTheory.is_closest_def,
                     pred_setTheory.GSPECIFICATION] >> strip_tac >>
    `float_to_real other <= float_to_real candidate` by (
      qpat_x_assum `∀comparison. _ ⇒
        float_to_real comparison <= float_to_real candidate`
        (qspec_then `other` mp_tac) >> simp[]) >>
    `abs (float_to_real other - source) <=
     abs (float_to_real candidate - source)` by (
      qpat_x_assum `∀comparison. _ ⇒
        abs (float_to_real other - source) <=
        abs (float_to_real comparison - source)`
        (qspec_then `candidate` mp_tac) >> simp[]) >>
    `float_to_real other = float_to_real candidate` by
      RealField.REAL_ASM_ARITH_TAC >>
    gvs[binary_ieeeTheory.float_to_real_eq]) >>
  strip_tac >>
  gvs[binary_ieeeTheory.is_closest_def, pred_setTheory.GSPECIFICATION] >>
  qx_gen_tac `comparison` >> strip_tac >>
  `float_to_real comparison <= float_to_real candidate` by (
    qpat_x_assum `∀other. _ ⇒ float_to_real other <= float_to_real candidate`
      (qspec_then `comparison` mp_tac) >> simp[]) >>
  RealField.REAL_ASM_ARITH_TAC
QED

Theorem round_positive_ordered:
  ∀source (candidate : (52, 11) float).
    abs source <= largest (:52 # 11) ∧
    float_is_finite candidate ∧ ¬float_is_zero candidate ∧
    source <= float_to_real candidate ∧
    (∀other : (52, 11) float.
      float_is_finite other ∧ source <= float_to_real other ⇒
      float_to_real candidate <= float_to_real other) ⇒
    round roundTowardPositive source = candidate
Proof
  qx_genl_tac [`source`, `candidate`] >> strip_tac >>
  `¬(source < -largest (:52 # 11)) ∧
   ¬(largest (:52 # 11) < source)` by RealField.REAL_ASM_ARITH_TAC >>
  asm_simp_tac std_ss [binary_ieeeTheory.round_def, binary_ieeeTheory.rounding_case_def, LET_THM,
                       realTheory.real_gt, realTheory.real_ge] >>
  irule closest_greater_nonzero >> simp[]
QED

Theorem round_negative_ordered:
  ∀source (candidate : (52, 11) float).
    abs source <= largest (:52 # 11) ∧
    float_is_finite candidate ∧ ¬float_is_zero candidate ∧
    float_to_real candidate <= source ∧
    (∀other : (52, 11) float.
      float_is_finite other ∧ float_to_real other <= source ⇒
      float_to_real other <= float_to_real candidate) ⇒
    round roundTowardNegative source = candidate
Proof
  qx_genl_tac [`source`, `candidate`] >> strip_tac >>
  `¬(source < -largest (:52 # 11)) ∧
   ¬(largest (:52 # 11) < source)` by RealField.REAL_ASM_ARITH_TAC >>
  asm_simp_tac std_ss [binary_ieeeTheory.round_def, binary_ieeeTheory.rounding_case_def, LET_THM,
                       realTheory.real_gt, realTheory.real_ge] >>
  irule closest_less_nonzero >> simp[]
QED

Theorem fp64_boundary_ULP:
  ∀candidate other : (52, 11) float.
    exponent_boundary other candidate ⇒
    ULP (candidate.Exponent, (:52)) = 2 * ULP (other.Exponent, (:52))
Proof
  qx_genl_tac [`candidate`, `other`] >>
  simp_tac std_ss [binary_ieeeTheory.exponent_boundary_def] >> strip_tac >>
  `candidate.Exponent <> 0w ∧ other.Exponent <> 0w` by (
    qpat_x_assum `candidate.Exponent <> 1w` mp_tac >>
    once_rewrite_tac [GSYM wordsTheory.w2n_11] >>
    simp_tac std_ss [EVAL ``w2n (0w : word11)``,
                     EVAL ``w2n (1w : word11)``] >> decide_tac) >>
  asm_simp_tac std_ss [binary_ieeeTheory.ULP_def,
    GSYM arithmeticTheory.ADD1, realTheory.pow, realTheory.real_div,
    realTheory.REAL_MUL_ASSOC]
QED

Theorem fp64_preceding_gap:
  ∀(candidate : (52, 11) float) (other : (52, 11) float).
    float_to_real candidate <> float_to_real other ⇒
    (if candidate.Significand = 0w ∧ candidate.Exponent <> 1w then
       ULP (candidate.Exponent, (:52)) / 2
     else ULP (candidate.Exponent, (:52))) <=
    abs (float_to_real candidate - float_to_real other)
Proof
  qx_genl_tac [`candidate`, `other`] >> strip_tac >>
  `0 <= ULP (candidate.Exponent, (:52))` by simp[] >>
  Cases_on `exponent_boundary other candidate`
  >- (
    `ULP (candidate.Exponent, (:52)) =
     2 * ULP (other.Exponent, (:52))` by (
      irule fp64_boundary_ULP >> simp[]) >>
    `¬exponent_boundary candidate other` by (
      strip_tac >> fs[binary_ieeeTheory.exponent_boundary_def] >> decide_tac) >>
    `float_to_real other <> float_to_real candidate` by simp[EQ_SYM_EQ] >>
    qspecl_then [`other`, `candidate`] drule_all binary_ieeeTheory.diff_float_ULP >>
    fs[binary_ieeeTheory.exponent_boundary_def, realTheory.ABS_SUB] >>
    RealField.REAL_ASM_ARITH_TAC) >>
  qspecl_then [`candidate`, `other`] mp_tac binary_ieeeTheory.diff_float_ULP >>
  impl_tac >- simp[] >> strip_tac >>
  Cases_on `candidate.Significand = 0w ∧ candidate.Exponent <> 1w` >>
  asm_simp_tac std_ss [] >> RealField.REAL_ASM_ARITH_TAC
QED

Theorem fp64_magnitude_gap:
  ∀(candidate : (52, 11) float) (other : (52, 11) float).
    abs (float_to_real candidate) < abs (float_to_real other) ⇒
    ULP (candidate.Exponent, (:52)) <=
    abs (float_to_real candidate - float_to_real other)
Proof
  qx_genl_tac [`candidate`, `other`] >> strip_tac >>
  `candidate.Exponent <=+ other.Exponent` by (
    irule binary_ieeeTheory.Exponent_monotone >> simp[]) >>
  `¬exponent_boundary other candidate` by (
    strip_tac >> fs[binary_ieeeTheory.exponent_boundary_def,
                   wordsTheory.WORD_LS] >> decide_tac) >>
  irule binary_ieeeTheory.diff_float_ULP >> simp[] >>
  strip_tac >> fs[]
QED

Theorem round_positive_spacing:
  ∀source (candidate : (52, 11) float).
    abs source <= largest (:52 # 11) ∧
    float_is_finite candidate ∧ ¬float_is_zero candidate ∧
    source <= float_to_real candidate ∧
    float_to_real candidate - source <
      (if 0 <= float_to_real candidate ∧ candidate.Significand = 0w ∧
          candidate.Exponent <> 1w then ULP (candidate.Exponent, (:52)) / 2
       else ULP (candidate.Exponent, (:52))) ⇒
    round roundTowardPositive source = candidate
Proof
  qx_genl_tac [`source`, `candidate`] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `float_to_real candidate - source < gap` >>
  irule round_positive_ordered >> simp[] >>
  qx_gen_tac `other` >> strip_tac >>
  Cases_on `float_to_real candidate <= float_to_real other` >> simp[] >>
  `gap <= abs (float_to_real candidate - float_to_real other)` by (
    Cases_on `0 <= float_to_real candidate`
    >- (
      qspecl_then [`candidate`, `other`] mp_tac fp64_preceding_gap >>
      impl_tac >- RealField.REAL_ASM_ARITH_TAC >>
      simp[Abbr `gap`]) >>
    `abs (float_to_real candidate) < abs (float_to_real other)` by
      RealField.REAL_ASM_ARITH_TAC >>
    qspecl_then [`candidate`, `other`] mp_tac fp64_magnitude_gap >>
    simp[Abbr `gap`]) >>
  RealField.REAL_ASM_ARITH_TAC
QED

Theorem round_negative_spacing:
  ∀source (candidate : (52, 11) float).
    abs source <= largest (:52 # 11) ∧
    float_is_finite candidate ∧ ¬float_is_zero candidate ∧
    float_to_real candidate <= source ∧
    source - float_to_real candidate <
      (if float_to_real candidate <= 0 ∧ candidate.Significand = 0w ∧
          candidate.Exponent <> 1w then ULP (candidate.Exponent, (:52)) / 2
       else ULP (candidate.Exponent, (:52))) ⇒
    round roundTowardNegative source = candidate
Proof
  qx_genl_tac [`source`, `candidate`] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `source - float_to_real candidate < gap` >>
  irule round_negative_ordered >> simp[] >>
  qx_gen_tac `other` >> strip_tac >>
  Cases_on `float_to_real other <= float_to_real candidate` >> simp[] >>
  `gap <= abs (float_to_real candidate - float_to_real other)` by (
    Cases_on `float_to_real candidate <= 0`
    >- (
      qspecl_then [`candidate`, `other`] mp_tac fp64_preceding_gap >>
      impl_tac >- RealField.REAL_ASM_ARITH_TAC >>
      simp[Abbr `gap`]) >>
    `abs (float_to_real candidate) < abs (float_to_real other)` by
      RealField.REAL_ASM_ARITH_TAC >>
    qspecl_then [`candidate`, `other`] mp_tac fp64_magnitude_gap >>
    simp[Abbr `gap`]) >>
  RealField.REAL_ASM_ARITH_TAC
QED

Theorem round_negative_tiny_zero:
  ∀source.
    0 <= source ∧ source < ulp (:52 # 11) ⇒
    float_is_zero (round roundTowardNegative source : (52, 11) float)
Proof
  qx_gen_tac `source` >> strip_tac >>
  `∀other : (52, 11) float.
    float_is_finite other ∧ float_to_real other <= source ⇒
    float_to_real other <= 0` by (
    qx_gen_tac `other` >> strip_tac >>
    Cases_on `float_to_real other <= 0` >> simp[] >>
    `abs (float_to_real other) < ulp (:52 # 11)` by
      RealField.REAL_ASM_ARITH_TAC >>
    `float_is_zero other` by
      fs[binary_ieeeTheory.less_than_ulp, binary_ieeeTheory.float_is_zero] >>
    fs[binary_ieeeTheory.float_is_zero_to_real]) >>
  `ulp (:52 # 11) < largest (:52 # 11)` by
    simp[binary_ieeeTheory.ulp_lt_largest] >>
  `¬(source < -largest (:52 # 11)) ∧
   ¬(largest (:52 # 11) < source)` by RealField.REAL_ASM_ARITH_TAC >>
  asm_simp_tac std_ss [binary_ieeeTheory.round_def,
    binary_ieeeTheory.rounding_case_def, LET_THM, realTheory.real_gt,
    realTheory.real_ge, binary_ieeeTheory.closest_def,
    binary_ieeeTheory.closest_such_def, combinTheory.K_THM] >>
  SELECT_ELIM_TAC >>
  conj_tac
  >- (
    qexists_tac `float_plus_zero (:52 # 11)` >>
    simp[binary_ieeeTheory.is_closest_def] >>
    qx_gen_tac `comparison` >> strip_tac >>
    `float_to_real comparison <= 0` by (
      qpat_x_assum `∀other. _ ⇒ float_to_real other <= 0`
        (qspec_then `comparison` mp_tac) >> simp[]) >>
    RealField.REAL_ASM_ARITH_TAC) >>
  qx_gen_tac `chosen` >>
  simp_tac std_ss [binary_ieeeTheory.is_closest_def,
                   pred_setTheory.GSPECIFICATION] >> strip_tac >>
  `float_to_real chosen <= 0` by (
    qpat_x_assum `∀other. _ ⇒ float_to_real other <= 0`
      (qspec_then `chosen` mp_tac) >> simp[]) >>
  `abs (float_to_real chosen - source) <= source` by (
    qpat_x_assum `∀comparison. _ ⇒
      abs (float_to_real chosen - source) <=
      abs (float_to_real comparison - source)`
      (qspec_then `float_plus_zero (:52 # 11)` mp_tac) >>
    simp[realTheory.ABS_NEG] >>
    RealField.REAL_ASM_ARITH_TAC) >>
  `float_to_real chosen = 0` by RealField.REAL_ASM_ARITH_TAC >>
  simp[binary_ieeeTheory.float_is_zero_to_real]
QED

Theorem round_positive_tiny_zero:
  ∀source.
    source <= 0 ∧ -ulp (:52 # 11) < source ⇒
    float_is_zero (round roundTowardPositive source : (52, 11) float)
Proof
  qx_gen_tac `source` >> strip_tac >>
  `∀other : (52, 11) float.
    float_is_finite other ∧ source <= float_to_real other ⇒
    0 <= float_to_real other` by (
    qx_gen_tac `other` >> strip_tac >>
    Cases_on `0 <= float_to_real other` >> simp[] >>
    `abs (float_to_real other) < ulp (:52 # 11)` by
      RealField.REAL_ASM_ARITH_TAC >>
    `float_is_zero other` by
      fs[binary_ieeeTheory.less_than_ulp, binary_ieeeTheory.float_is_zero] >>
    fs[binary_ieeeTheory.float_is_zero_to_real]) >>
  `ulp (:52 # 11) < largest (:52 # 11)` by
    simp[binary_ieeeTheory.ulp_lt_largest] >>
  `¬(source < -largest (:52 # 11)) ∧
   ¬(largest (:52 # 11) < source)` by RealField.REAL_ASM_ARITH_TAC >>
  asm_simp_tac std_ss [binary_ieeeTheory.round_def,
    binary_ieeeTheory.rounding_case_def, LET_THM, realTheory.real_gt,
    realTheory.real_ge, binary_ieeeTheory.closest_def,
    binary_ieeeTheory.closest_such_def, combinTheory.K_THM] >>
  SELECT_ELIM_TAC >>
  conj_tac
  >- (
    qexists_tac `float_plus_zero (:52 # 11)` >>
    simp[binary_ieeeTheory.is_closest_def] >>
    qx_gen_tac `comparison` >> strip_tac >>
    `0 <= float_to_real comparison` by (
      qpat_x_assum `∀other. _ ⇒ 0 <= float_to_real other`
        (qspec_then `comparison` mp_tac) >> simp[]) >>
    RealField.REAL_ASM_ARITH_TAC) >>
  qx_gen_tac `chosen` >>
  simp_tac std_ss [binary_ieeeTheory.is_closest_def,
                   pred_setTheory.GSPECIFICATION] >> strip_tac >>
  `0 <= float_to_real chosen` by (
    qpat_x_assum `∀other. _ ⇒ 0 <= float_to_real other`
      (qspec_then `chosen` mp_tac) >> simp[]) >>
  `abs (float_to_real chosen - source) <= -source` by (
    qpat_x_assum `∀comparison. _ ⇒
      abs (float_to_real chosen - source) <=
      abs (float_to_real comparison - source)`
      (qspec_then `float_plus_zero (:52 # 11)` mp_tac) >>
    simp[realTheory.ABS_NEG] >>
    RealField.REAL_ASM_ARITH_TAC) >>
  `float_to_real chosen = 0` by RealField.REAL_ASM_ARITH_TAC >>
  simp[binary_ieeeTheory.float_is_zero_to_real]
QED

Theorem float_round_negative_tiny_zero:
  ∀source negative.
    0 <= source ∧ source < ulp (:52 # 11) ⇒
    (float_round roundTowardNegative negative source : (52, 11) float) =
      if negative then float_minus_zero (:52 # 11) else float_plus_zero (:52 # 11)
Proof
  qx_genl_tac [`source`, `negative`] >> strip_tac >>
  simp[binary_ieeeTheory.float_round_def, round_negative_tiny_zero]
QED

Theorem float_round_positive_tiny_zero:
  ∀source negative.
    source <= 0 ∧ -ulp (:52 # 11) < source ⇒
    (float_round roundTowardPositive negative source : (52, 11) float) =
      if negative then float_minus_zero (:52 # 11) else float_plus_zero (:52 # 11)
Proof
  qx_genl_tac [`source`, `negative`] >> strip_tac >>
  simp[binary_ieeeTheory.float_round_def, round_positive_tiny_zero]
QED

Theorem normal_float_value_positive:
  !exponent significand.
    0 < exponent /\ exponent < 2047 /\
    2 ** 52 <= significand /\ significand < 2 ** 53 ==>
    float_value
      (<|Sign := 0w; Exponent := n2w exponent;
         Significand := n2w significand|> : (52, 11) float) =
    Float (&significand * (2 pow exponent / 2 pow 1075))
Proof
  qx_genl_tac [`exponent`, `significand`]
  \\ strip_tac
  \\ `exponent < 2048 /\ exponent <> 0 /\ exponent <> 2047` by decide_tac
  \\ `significand MOD 2 ** 52 = significand - 2 ** 52` by (
    irule arithmeticTheory.MOD_UNIQUE
    \\ qexists_tac `1`
    \\ fs [EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``]
    \\ decide_tac)
  \\ `(n2w exponent : word11) <> 0w /\
       (n2w exponent : word11) <> -1w` by
    simp [wordsTheory.n2w_11, EVAL ``(-1w : word11)``]
  \\ simp [binary_ieeeTheory.float_value_def, binary_ieeeTheory.float_to_real_def,
           wordsTheory.dimword_def, wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
           wordsTheory.w2n_n2w]
  \\ full_simp_tac std_ss
       [EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``,
        realTheory.REAL_OF_NUM_SUB]
  \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
  \\ RealField.REAL_ARITH_TAC
QED

Theorem subnormal_float_value_positive:
  !significand.
    significand < 2 ** 52 ==>
    float_value
      (<|Sign := 0w; Exponent := 0w;
         Significand := n2w significand|> : (52, 11) float) =
    Float (&significand / 2 pow 1074)
Proof
  qx_gen_tac `significand`
  \\ strip_tac
  \\ fs [EVAL ``(2 : num) ** 52``]
  \\ simp [binary_ieeeTheory.float_value_def, binary_ieeeTheory.float_to_real_def,
           wordsTheory.dimword_def, wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
           wordsTheory.w2n_n2w]
  \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
  \\ RealField.REAL_ARITH_TAC
QED

Theorem subnormal_rounding_value:
  !rounded.
    rounded <= 2 ** 52 ==>
    float_value
      (<|Sign := 0w; Exponent := if rounded = 2 ** 52 then 1w else 0w;
         Significand := n2w rounded|> : (52, 11) float) =
    Float (&rounded / 2 pow 1074)
Proof
  qx_gen_tac `rounded`
  \\ strip_tac
  \\ Cases_on `rounded = 2 ** 52`
  >- (
    qspecl_then [`1`, `(2 : num) ** 52`] mp_tac normal_float_value_positive
    \\ gvs []
    \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
    \\ simp [])
  \\ `rounded < 2 ** 52` by decide_tac
  \\ simp [subnormal_float_value_positive]
QED

Theorem subnormal_rounding_value_signed:
  ∀negative rounded.
    rounded <= 2 ** 52 ⇒
    float_value
      (<|Sign := if negative then 1w else 0w;
         Exponent := if rounded = 2 ** 52 then 1w else 0w;
         Significand := n2w rounded|> : (52, 11) float) =
    Float (if negative then -(&rounded / 2 pow 1074)
           else &rounded / 2 pow 1074)
Proof
  qx_genl_tac [`negative`, `rounded`] >> strip_tac >>
  qspec_then `rounded` mp_tac subnormal_rounding_value >>
  impl_tac >- simp[] >> strip_tac >>
  Cases_on `negative`
  >- (
    qspecl_then
      [`-(&rounded / 2 pow 1074)`,
       `(<|Sign := 0w;
            Exponent := if rounded = 2 ** 52 then 1w else 0w;
            Significand := n2w rounded|> : (52, 11) float)`]
      mp_tac (GEN_ALL binary_ieeeTheory.float_negate) >>
    gvs[binary_ieeeTheory.float_negate_def, EVAL ``(-1w : word1)``]) >>
  gvs[]
QED

Theorem subnormal_candidate:
  ∀negative rounded.
    0 < rounded ∧ rounded <= 2 ** 52 ⇒
    let candidate =
      (<|Sign := if negative then 1w else 0w;
         Exponent := if rounded = 2 ** 52 then 1w else 0w;
         Significand := n2w rounded|> : (52, 11) float) in
    float_is_finite candidate ∧ ¬float_is_zero candidate ∧
    float_to_real candidate =
      (if negative then -(&rounded * (1 / 2 pow 1074))
       else &rounded * (1 / 2 pow 1074)) ∧
    ULP (candidate.Exponent, (:52)) = 1 / 2 pow 1074 ∧
    ¬(candidate.Significand = 0w ∧ candidate.Exponent <> 1w)
Proof
  qx_genl_tac [`negative`, `rounded`] >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `float_is_finite candidate` >>
  `float_value candidate =
    Float (if negative then -(&rounded * (1 / 2 pow 1074))
           else &rounded * (1 / 2 pow 1074))` by (
    qspecl_then [`negative`, `rounded`] mp_tac subnormal_rounding_value_signed >>
    simp[Abbr `candidate`, realTheory.real_div]) >>
  `float_is_finite candidate` by
    simp[binary_ieeeTheory.float_is_finite_def] >>
  `float_to_real candidate =
    (if negative then -(&rounded * (1 / 2 pow 1074))
     else &rounded * (1 / 2 pow 1074))` by (
    qspec_then `candidate` mp_tac
      (GEN_ALL binary_ieeeTheory.float_is_finite_float_value) >>
    simp[EQ_SYM_EQ]) >>
  `0 < (&rounded : real) * (1 / 2 pow 1074)` by (
    irule realTheory.REAL_LT_MUL >>
    simp[realTheory.real_div, realTheory.REAL_LT_INV_EQ,
         realTheory.REAL_POW_LT]) >>
  `¬float_is_zero candidate` by (
    simp[binary_ieeeTheory.float_is_zero_def] >>
    Cases_on `negative` >> simp[] >>
    RealField.REAL_ASM_ARITH_TAC) >>
  `ULP (candidate.Exponent, (:52)) = 1 / 2 pow 1074` by (
    Cases_on `rounded = 2 ** 52` >>
    fs[Abbr `candidate`, binary_ieeeTheory.ULP_def,
       wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
       wordsTheory.dimword_def] >>
    CONV_TAC RealField.REAL_RAT_REDUCE_CONV) >>
  `¬(candidate.Significand = 0w ∧ candidate.Exponent <> 1w)` by (
    Cases_on `rounded = 2 ** 52`
    >- fs[Abbr `candidate`, EVAL ``(2 : num) ** 52``] >>
    `rounded < 2 ** 52` by decide_tac >>
    fs[Abbr `candidate`, EVAL ``(2 : num) ** 52``,
       wordsTheory.n2w_11, arithmeticTheory.LESS_MOD]) >>
  fs[]
QED

Theorem fp64_subnormal_range:
  ∀value : real.
    0 <= value ∧ value < &((2 : num) ** 52) ⇒
    0 <= value * (1 / 2 pow 1074) ∧
    value * (1 / 2 pow 1074) < largest (:52 # 11)
Proof
  simp[binary_ieeeTheory.largest_def, wordsTheory.INT_MAX_def,
       wordsTheory.INT_MIN_def, wordsTheory.UINT_MAX_def,
       wordsTheory.dimword_def] >>
  CONV_TAC RealField.REAL_RAT_REDUCE_CONV >>
  RealField.REAL_ARITH_TAC
QED

Theorem directed_nat_scaled_bounds:
  ∀lower : num. ∀(error : real) (scale : real).
    0 <= error ∧ error < 1 ∧ 0 < scale ⇒
    let source = (&lower + error) * scale in
    let floor_value = &lower * scale in
    let ceiling_value = &(if error = 0 then lower else SUC lower) * scale in
    floor_value <= source ∧ source - floor_value < scale ∧
    source <= ceiling_value ∧ ceiling_value - source < scale
Proof
  qx_genl_tac [`lower`, `error`, `scale`] >> strip_tac >>
  `0 <= scale` by RealField.REAL_ASM_ARITH_TAC >>
  `0 <= error * scale` by (
    irule realTheory.REAL_LE_MUL >> simp[]) >>
  `error * scale < scale` by (
    qspecl_then [`error`, `1`, `scale`] mp_tac realTheory.REAL_LT_RMUL_IMP >>
    simp[]) >>
  Cases_on `error = 0`
  >- simp[LET_THM] >>
  `0 < error` by RealField.REAL_ASM_ARITH_TAC >>
  `0 <= (1 - error) * scale` by (
    irule realTheory.REAL_LE_MUL >> conj_tac
    >- RealField.REAL_ASM_ARITH_TAC >> simp[]) >>
  `(1 - error) * scale < scale` by (
    qspecl_then [`1 - error`, `1`, `scale`] mp_tac
      realTheory.REAL_LT_RMUL_IMP >>
    impl_tac >- RealField.REAL_ASM_ARITH_TAC >> simp[]) >>
  asm_simp_tac std_ss [LET_THM, GSYM realTheory.REAL_OF_NUM_SUC,
    realTheory.REAL_ADD_RDISTRIB] >>
  RealField.REAL_ASM_ARITH_TAC
QED

Theorem subnormal_float_round_away:
  ∀negative lower error.
    0 <= error ∧ error < 1 ∧ 0 < &lower + error ∧
    &lower + error < &((2 : num) ** 52) ⇒
    let rounded = if error = 0 then lower else SUC lower in
    let magnitude = (&lower + error) * (1 / 2 pow 1074) in
    float_round (if negative then roundTowardNegative else roundTowardPositive)
      negative (if negative then -magnitude else magnitude) =
      (<|Sign := if negative then 1w else 0w;
         Exponent := if rounded = 2 ** 52 then 1w else 0w;
         Significand := n2w rounded|> : (52, 11) float)
Proof
  qx_genl_tac [`negative`, `lower`, `error`] >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  qabbrev_tac `rounded = if error = 0 then lower else SUC lower` >>
  qmatch_goalsub_abbrev_tac `(&lower + error) * scale` >>
  qmatch_goalsub_abbrev_tac
    `float_round _ _ (if negative then -magnitude else magnitude)` >>
  qmatch_goalsub_abbrev_tac `(float_round _ _ _) = candidate` >>
  `0 < scale` by (
    simp[Abbr `scale`, realTheory.real_div,
         realTheory.REAL_LT_INV_EQ, realTheory.REAL_POW_LT]) >>
  `lower < 2 ** 52` by (
    rewrite_tac [GSYM realTheory.REAL_LT] >>
    RealField.REAL_ASM_ARITH_TAC) >>
  `0 < rounded ∧ rounded <= 2 ** 52` by (
    Cases_on `error = 0` >>
    fs[Abbr `rounded`] >> decide_tac) >>
  `0 <= magnitude ∧ magnitude < largest (:52 # 11)` by (
    qspec_then `&lower + error` mp_tac fp64_subnormal_range >>
    impl_tac >- RealField.REAL_ASM_ARITH_TAC >>
    simp[Abbr `magnitude`, Abbr `scale`]) >>
  `float_is_finite candidate ∧ ¬float_is_zero candidate ∧
   float_to_real candidate =
     (if negative then -(&rounded * scale) else &rounded * scale) ∧
   ULP (candidate.Exponent, (:52)) = scale ∧
   ¬(candidate.Significand = 0w ∧ candidate.Exponent <> 1w)` by (
    qspecl_then [`negative`, `rounded`] mp_tac subnormal_candidate >>
    simp[LET_THM, Abbr `candidate`, Abbr `scale`]) >>
  `magnitude <= &rounded * scale ∧ &rounded * scale - magnitude < scale` by (
    qspecl_then [`lower`, `error`, `scale`] drule_all directed_nat_scaled_bounds >>
    asm_simp_tac std_ss [LET_THM, Abbr `rounded`, Abbr `magnitude`] >>
    strip_tac >> simp[]) >>
  Cases_on `negative`
  >- (
    `round roundTowardNegative (-magnitude) = candidate` by (
      irule round_negative_spacing >>
      asm_simp_tac std_ss [realTheory.ABS_NEG] >>
      RealField.REAL_ASM_ARITH_TAC) >>
    simp[binary_ieeeTheory.float_round_def]) >>
  `round roundTowardPositive magnitude = candidate` by (
    irule round_positive_spacing >>
    asm_simp_tac std_ss [] >> RealField.REAL_ASM_ARITH_TAC) >>
  simp[binary_ieeeTheory.float_round_def]
QED

Theorem subnormal_float_round_truncate:
  ∀negative mode lower error.
    (mode = roundTowardZero ∨
     mode = if negative then roundTowardPositive else roundTowardNegative) ∧
    0 <= error ∧ error < 1 ∧ &lower + error < &((2 : num) ** 52) ⇒
    let magnitude = (&lower + error) * (1 / 2 pow 1074) in
    float_round mode negative (if negative then -magnitude else magnitude) =
      (<|Sign := if negative then 1w else 0w;
         Exponent := if lower = 2 ** 52 then 1w else 0w;
         Significand := n2w lower|> : (52, 11) float)
Proof
  qx_genl_tac [`negative`, `mode`, `lower`, `error`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `(&lower + error) * scale` >>
  qmatch_goalsub_abbrev_tac
    `float_round _ _ (if negative then -magnitude else magnitude)` >>
  qmatch_goalsub_abbrev_tac `(float_round _ _ _) = candidate` >>
  `0 < scale` by (
    simp[Abbr `scale`, realTheory.real_div,
         realTheory.REAL_LT_INV_EQ, realTheory.REAL_POW_LT]) >>
  `0 <= &lower + error` by (irule realTheory.REAL_LE_ADD >> simp[]) >>
  `lower < 2 ** 52` by (
    rewrite_tac [GSYM realTheory.REAL_LT] >>
    RealField.REAL_ASM_ARITH_TAC) >>
  `0 <= magnitude ∧ magnitude < largest (:52 # 11)` by (
    qspec_then `&lower + error` drule_all fp64_subnormal_range >>
    simp[Abbr `magnitude`, Abbr `scale`]) >>
  `ulp (:52 # 11) = scale` by (
    simp[Abbr `scale`, binary_ieeeTheory.ulp_def, binary_ieeeTheory.ULP_def,
         wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
         wordsTheory.dimword_def] >>
    CONV_TAC RealField.REAL_RAT_REDUCE_CONV) >>
  `&lower * scale <= magnitude ∧ magnitude - &lower * scale < scale` by (
    qspecl_then [`lower`, `error`, `scale`] drule_all directed_nat_scaled_bounds >>
    asm_simp_tac std_ss [LET_THM, Abbr `magnitude`] >>
    strip_tac >> simp[]) >>
  Cases_on `lower = 0`
  >- (
    qpat_x_assum `lower = 0` SUBST_ALL_TAC >>
    `magnitude < ulp (:52 # 11)` by RealField.REAL_ASM_ARITH_TAC >>
    `candidate = if negative then float_minus_zero (:52 # 11)
                 else float_plus_zero (:52 # 11)` by (
      Cases_on `negative` >>
      simp[Abbr `candidate`, binary_ieeeTheory.float_minus_zero_def,
           binary_ieeeTheory.float_plus_zero_def,
           binary_ieeeTheory.float_negate_def, EVAL ``(-1w : word1)``]) >>
    Cases_on `mode = roundTowardZero`
    >- (
      qpat_x_assum `mode = roundTowardZero` SUBST_ALL_TAC >>
      Cases_on `negative`
      >- (
        asm_simp_tac std_ss [] >>
        irule binary_ieeeTheory.round_roundTowardZero_is_minus_zero >>
        RealField.REAL_ASM_ARITH_TAC) >>
      asm_simp_tac std_ss [] >>
      irule binary_ieeeTheory.round_roundTowardZero_is_plus_zero >>
      RealField.REAL_ASM_ARITH_TAC) >>
    qpat_x_assum `mode = roundTowardZero ∨ _` mp_tac >>
    simp[] >> disch_then SUBST_ALL_TAC >>
    Cases_on `negative`
    >- (
      qspecl_then [`-magnitude`, `T`] mp_tac float_round_positive_tiny_zero >>
      impl_tac >- RealField.REAL_ASM_ARITH_TAC >> simp[]) >>
    qspecl_then [`magnitude`, `F`] mp_tac float_round_negative_tiny_zero >>
    impl_tac >- RealField.REAL_ASM_ARITH_TAC >> simp[]) >>
  `0 < lower ∧ lower <= 2 ** 52 ∧ 1 <= lower` by decide_tac >>
  `0 <= scale` by RealField.REAL_ASM_ARITH_TAC >>
  `scale <= &lower * scale` by (
    qspecl_then [`scale`, `1`, `(&lower : real)`]
      mp_tac realTheory.REAL_LE_RMUL_IMP >> simp[]) >>
  `float_is_finite candidate ∧ ¬float_is_zero candidate ∧
   float_to_real candidate =
     (if negative then -(&lower * scale) else &lower * scale) ∧
   ULP (candidate.Exponent, (:52)) = scale ∧
   ¬(candidate.Significand = 0w ∧ candidate.Exponent <> 1w)` by (
    qspecl_then [`negative`, `lower`] mp_tac subnormal_candidate >>
    simp[LET_THM, Abbr `candidate`, Abbr `scale`]) >>
  `float_value candidate = Float (float_to_real candidate)` by (
    qspec_then `candidate` mp_tac
      (GEN_ALL binary_ieeeTheory.float_is_finite_float_value) >> simp[]) >>
  `0 < &lower * scale` by (
    qpat_assum `0 < scale` mp_tac >>
    qpat_assum `scale <= &lower * scale` mp_tac >>
    rpt (pop_assum kall_tac) >> RealField.REAL_ARITH_TAC) >>
  qpat_assum `float_is_finite candidate` mp_tac >>
  qpat_assum `¬float_is_zero candidate` mp_tac >>
  qpat_assum `float_value candidate = Float (float_to_real candidate)` mp_tac >>
  qpat_assum `float_to_real candidate = _` mp_tac >>
  qpat_assum `ULP (candidate.Exponent, (:52)) = scale` mp_tac >>
  qpat_assum `¬(candidate.Significand = 0w ∧ candidate.Exponent <> 1w)` mp_tac >>
  qpat_assum `scale <= &lower * scale` mp_tac >>
  qpat_assum `ulp (:52 # 11) = scale` mp_tac >>
  qpat_assum `magnitude < largest (:52 # 11)` mp_tac >>
  qpat_assum `0 <= magnitude` mp_tac >>
  qpat_assum `&lower * scale <= magnitude` mp_tac >>
  qpat_assum `magnitude - &lower * scale < scale` mp_tac >>
  qpat_assum `0 < scale` mp_tac >>
  qpat_assum `0 < &lower * scale` mp_tac >>
  qpat_assum `(mode = roundTowardZero ∨ _)` mp_tac >>
  rpt (pop_assum kall_tac) >> disch_then assume_tac >> rpt strip_tac >>
  Cases_on `mode = roundTowardZero`
  >- (
    qpat_x_assum `mode = roundTowardZero` SUBST_ALL_TAC >>
    `round roundTowardZero (if negative then -magnitude else magnitude) =
     candidate` by (
      qspecl_then [`candidate`, `if negative then -magnitude else magnitude`,
                   `float_to_real candidate`]
        match_mp_tac binary_ieeeTheory.round_roundTowardZero >>
      Cases_on `negative` >>
      asm_simp_tac std_ss [realTheory.ABS_NEG] >>
      qpat_assum `&lower * scale <= magnitude` mp_tac >>
      qpat_assum `magnitude - &lower * scale < scale` mp_tac >>
      qpat_assum `0 <= magnitude` mp_tac >>
      qpat_assum `magnitude < largest (:52 # 11)` mp_tac >>
      qpat_assum `scale <= &lower * scale` mp_tac >>
      qpat_assum `0 < scale` mp_tac >>
      qpat_assum `ulp (:52 # 11) = scale` mp_tac >>
      rpt (pop_assum kall_tac) >> RealField.REAL_ARITH_TAC) >>
    simp[binary_ieeeTheory.float_round_def]) >>
  qpat_x_assum `mode = roundTowardZero ∨ _` mp_tac >>
  simp[] >> disch_then SUBST_ALL_TAC >>
  Cases_on `negative`
  >- (
    `round roundTowardPositive (-magnitude) = candidate` by (
      irule round_positive_spacing >>
      asm_simp_tac std_ss [realTheory.ABS_NEG] >>
      qpat_assum `&lower * scale <= magnitude` mp_tac >>
      qpat_assum `magnitude - &lower * scale < scale` mp_tac >>
      qpat_assum `0 <= magnitude` mp_tac >>
      qpat_assum `magnitude < largest (:52 # 11)` mp_tac >>
      qpat_assum `scale <= &lower * scale` mp_tac >>
      qpat_assum `0 < scale` mp_tac >>
      rpt (pop_assum kall_tac) >> RealField.REAL_ARITH_TAC) >>
    simp[binary_ieeeTheory.float_round_def]) >>
  `round roundTowardNegative magnitude = candidate` by (
    irule round_negative_spacing >> asm_simp_tac std_ss [] >>
    qpat_assum `&lower * scale <= magnitude` mp_tac >>
    qpat_assum `magnitude - &lower * scale < scale` mp_tac >>
    qpat_assum `0 <= magnitude` mp_tac >>
    qpat_assum `magnitude < largest (:52 # 11)` mp_tac >>
    qpat_assum `scale <= &lower * scale` mp_tac >>
    qpat_assum `0 < scale` mp_tac >>
    rpt (pop_assum kall_tac) >> RealField.REAL_ARITH_TAC) >>
  simp[binary_ieeeTheory.float_round_def]
QED

Theorem fp64_pow2_add:
  !left right. fp64_pow2 (left + right) = fp64_pow2 left * fp64_pow2 right
Proof
  qx_genl_tac [`left`, `right`]
  \\ qspec_then `right` strip_assume_tac integerTheory.INT_NUM_CASES
  \\ gvs [fp64_pow2_add_nat, fp64_pow2_of_num, fp64_pow2_neg_of_num]
  \\ rename1 `fp64_pow2 (left + -&distance)`
  \\ `0 < (2 : real) pow distance` by simp [realTheory.REAL_POW_LT]
  \\ rewrite_tac [GSYM realTheory.real_div]
  \\ asm_simp_tac std_ss [realTheory.REAL_EQ_RDIV_EQ]
  \\ `left + -&distance + &distance = left` by intLib.ARITH_TAC
  \\ qspecl_then [`distance`, `left + -&distance`] mp_tac fp64_pow2_add_nat
  \\ asm_simp_tac std_ss []
QED

Theorem fp64_subnormal_scale:
  !exponent mantissa.
    (mantissa / fp64_pow2 (-1022 - exponent) * 2 pow 52) * (1 / 2 pow 1074) =
    mantissa * fp64_pow2 exponent
Proof
  qx_genl_tac [`exponent`, `mantissa`]
  \\ `exponent + (-1022 - exponent) = (-1022 : int)` by intLib.ARITH_TAC
  \\ `fp64_pow2 (-1022 - exponent) <> 0` by
    metis_tac [fp64_pow2_positive, realTheory.REAL_LT_IMP_NE]
  \\ qspecl_then [`exponent`, `-1022 - exponent`] mp_tac fp64_pow2_add
  \\ asm_simp_tac std_ss []
  \\ rewrite_tac [fp64_pow2_neg_of_num]
  \\ qpat_assum `fp64_pow2 (-1022 - exponent) <> 0` mp_tac
  \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
  \\ qabbrev_tac `power = fp64_pow2 exponent`
  \\ qabbrev_tac `divisor = fp64_pow2 (-1022 - exponent)`
  \\ RealField.REAL_FIELD_TAC
QED

Theorem subnormal_float_round_directed:
  ∀negative mode lower error.
    mode <> roundTiesToEven ∧
    0 <= error ∧ error < 1 ∧ &lower + error < &((2 : num) ** 52) ⇒
    let increment =
      (error <> 0 ∧ mode = if negative then roundTowardNegative else roundTowardPositive) in
    let rounded = if increment then SUC lower else lower in
    let magnitude = (&lower + error) * (1 / 2 pow 1074) in
    float_round mode negative (if negative then -magnitude else magnitude) =
      (<|Sign := if negative then 1w else 0w;
         Exponent := if rounded = 2 ** 52 then 1w else 0w;
         Significand := n2w rounded|> : (52, 11) float)
Proof
  qx_genl_tac [`negative`, `mode`, `lower`, `error`] >> strip_tac >>
  Cases_on
    `mode = if negative then roundTowardNegative else roundTowardPositive`
  >- (
    Cases_on `&lower + error = 0`
    >- (
      `0 <= (&lower : real)` by simp[] >>
      `(&lower : real) = 0 ∧ error = 0` by RealField.REAL_ASM_ARITH_TAC >>
      `lower = 0` by fs[] >>
      Cases_on `negative` >>
      gvs[LET_THM, binary_ieeeTheory.float_round_def,
          binary_ieeeTheory.float_is_zero_to_real,
          binary_ieeeTheory.float_minus_zero_def,
          binary_ieeeTheory.float_plus_zero_def,
          binary_ieeeTheory.float_negate_def, EVAL ``(-1w : word1)``]) >>
    `0 <= (&lower : real)` by simp[] >>
    `0 < &lower + error` by RealField.REAL_ASM_ARITH_TAC >>
    qspecl_then [`negative`, `lower`, `error`] mp_tac
      subnormal_float_round_away >>
    simp[LET_THM] >>
    Cases_on `error = 0` >> simp[]) >>
  `(mode = roundTowardZero ∨
    mode = if negative then roundTowardPositive else roundTowardNegative)` by (
    Cases_on `negative` >>
    Cases_on `mode` >> fs[]) >>
  qspecl_then [`negative`, `mode`, `lower`, `error`] mp_tac
    subnormal_float_round_truncate >>
  fs[LET_THM]
QED

Theorem fp64_round_quantize_subnormal_directed:
  ∀mode negative exponent mantissa lower error.
    mode <> roundTiesToEven ∧ exponent < -1022 ∧
    lower = Num (flr (mantissa / fp64_pow2 (-1022 - exponent) * 2 pow 52)) ∧
    error = mantissa / fp64_pow2 (-1022 - exponent) * 2 pow 52 - &lower ∧
    0 <= error ∧ error < 1 ∧ &lower + error < &((2 : num) ** 52) ⇒
    fp64_round_quantize mode negative (exponent, mantissa) =
      (error <> 0, F, error <> 0,
       float_to_fp64
         (float_round mode negative
           (if negative then -(mantissa * fp64_pow2 exponent)
            else mantissa * fp64_pow2 exponent)))
Proof
  qx_genl_tac [`mode`, `negative`, `exponent`, `mantissa`, `lower`, `error`] >>
  strip_tac >>
  `(if exponent + 1023 < 0 then 0 else exponent + 1023) = (0 : int)` by
    intLib.ARITH_TAC >>
  `lower < 2 ** 52` by (
    rewrite_tac [GSYM realTheory.REAL_LT] >>
    RealField.REAL_ASM_ARITH_TAC) >>
  `&lower + error = mantissa / fp64_pow2 (-1022 - exponent) * 2 pow 52` by
    RealField.REAL_ASM_ARITH_TAC >>
  `(&lower + error) * (1 / 2 pow 1074) = mantissa * fp64_pow2 exponent` by
    simp[fp64_subnormal_scale] >>
  qabbrev_tac `increment = (error <> 0 ∧
    mode = if negative then roundTowardNegative else roundTowardPositive)` >>
  qabbrev_tac `rounded = if increment then SUC lower else lower` >>
  `rounded <= 2 ** 52 ∧ rounded <> 2 ** 53` by (
    Cases_on `increment` >>
    fs[Abbr `rounded`] >> decide_tac) >>
  `float_round mode negative
    (if negative then -(mantissa * fp64_pow2 exponent)
     else mantissa * fp64_pow2 exponent) =
    (<|Sign := if negative then 1w else 0w;
       Exponent := if rounded = 2 ** 52 then 1w else 0w;
       Significand := n2w rounded|> : (52, 11) float)` by (
    qspecl_then [`negative`, `mode`, `lower`, `error`] mp_tac
      subnormal_float_round_directed >>
    simp[LET_THM, Abbr `rounded`, Abbr `increment`]) >>
  `(case mode of
      roundTiesToEven => 1 / 2 < error ∨ error = 1 / 2 ∧ ODD lower
    | roundTowardPositive => error <> 0 ∧ ¬negative
    | roundTowardNegative => error <> 0 ∧ negative
    | roundTowardZero => F) ⇔ increment` by (
    Cases_on `negative` >>
    Cases_on `mode` >>
    fs[Abbr `increment`]) >>
  `(increment ∧ rounded = 2 ** 52) ⇔ rounded = 2 ** 52` by (
    Cases_on `increment` >>
    fs[Abbr `rounded`] >> decide_tac) >>
  qpat_assum `(if exponent + 1023 < 0 then 0 else exponent + 1023) = 0`
    (fn biased_zero => simp_tac std_ss
      [fp64_round_quantize_def, LET_THM, binary_ieeeTheory.rounding_case_def,
       biased_zero]) >>
  qpat_assum `lower = Num (flr _)`
    (fn lower_equation => rewrite_tac [GSYM lower_equation]) >>
  qpat_assum `error = _ - &lower`
    (fn error_equation => rewrite_tac [GSYM error_equation]) >>
  qpat_assum `(_ : bool) ⇔ increment` SUBST1_TAC >>
  qpat_assum `Abbrev (rounded = _)`
    (fn rounded_equation => rewrite_tac
      [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] rounded_equation)]) >>
  qpat_assum `rounded <> 2 ** 53`
    (fn no_carry => simp_tac std_ss
      [REWRITE_RULE [EVAL ``(2 : num) ** 53``] no_carry]) >>
  qpat_assum `(_ ∧ rounded = 2 ** 52) ⇔ _`
    (fn carry => rewrite_tac [REWRITE_RULE [EVAL ``(2 : num) ** 52``] carry]) >>
  Cases_on `rounded = 2 ** 52` >>
  asm_simp_tac (srw_ss()) [EVAL ``(2 : num) ** 52``] >>
  CONV_TAC RealField.REAL_RAT_REDUCE_CONV >>
  gvs[EVAL ``(2 : num) ** 52``, EVAL ``(2 : real) pow 52``,
      EVAL ``(2047 : int) <= 0``, EVAL ``(2047 : int) <= 1``]
QED

Theorem ULP_binary64:
  !exponent.
    exponent < 2048 ==>
    ULP ((n2w exponent : word11), (:52)) =
    2 pow (if exponent = 0 then 1 else exponent) / 2 pow 1075
Proof
  qx_gen_tac `exponent`
  \\ strip_tac
  \\ simp [binary_ieeeTheory.ULP_def, wordsTheory.INT_MAX_def,
           wordsTheory.INT_MIN_def, wordsTheory.dimword_def, wordsTheory.n2w_11,
           wordsTheory.w2n_n2w]
QED

Theorem normal_significand_mod:
  !significand.
    2 ** 52 <= significand /\ significand < 2 ** 53 ==>
    significand MOD 2 ** 52 = significand - 2 ** 52
Proof
  qx_gen_tac `significand`
  \\ strip_tac
  \\ irule arithmeticTheory.MOD_UNIQUE
  \\ qexists_tac `1`
  \\ fs [EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``]
  \\ decide_tac
QED

Theorem normal_carry_value_positive:
  !exponent.
    0 < exponent /\ exponent < 2046 ==>
    float_value
      (<|Sign := 0w; Exponent := n2w (exponent + 1);
         Significand := 0w|> : (52, 11) float) =
    Float (&((2 : num) ** 53) * (2 pow exponent / 2 pow 1075))
Proof
  qx_gen_tac `exponent`
  \\ strip_tac
  \\ `0 < exponent + 1 /\ exponent + 1 < 2047` by decide_tac
  \\ `(n2w ((2 : num) ** 52) : 52 word) = 0w` by
    simp [wordsTheory.n2w_11, wordsTheory.dimword_def]
  \\ qspecl_then [`exponent + 1`, `(2 : num) ** 52`]
       mp_tac normal_float_value_positive
  \\ qpat_assum `(n2w ((2 : num) ** 52) : 52 word) = 0w`
       SUBST1_TAC
  \\ asm_simp_tac (srw_ss())
       [EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``,
        realTheory.REAL_POW_ADD, realTheory.POW_1]
  \\ disch_then SUBST1_TAC
  \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
  \\ RealField.REAL_ARITH_TAC
QED

Theorem normal_carry_ULP:
  !exponent.
    exponent < 2046 ==>
    ULP ((n2w (exponent + 1) : word11), (:52)) =
      2 * (2 pow exponent / 2 pow 1075)
Proof
  qx_gen_tac `exponent`
  \\ strip_tac
  \\ `exponent + 1 < 2048 /\ exponent + 1 <> 0` by decide_tac
  \\ simp [ULP_binary64, realTheory.REAL_POW_ADD, realTheory.POW_1]
  \\ RealField.REAL_ARITH_TAC
QED

Theorem normal_rounding_value_signed:
  ∀negative exponent rounded.
    0 < exponent ∧ exponent < 2047 ∧
    2 ** 52 <= rounded ∧ rounded <= 2 ** 53 ∧
    (rounded = 2 ** 53 ⇒ exponent < 2046) ⇒
    float_value
      (<|Sign := if negative then 1w else 0w;
         Exponent := if rounded = 2 ** 53 then n2w (exponent + 1)
                     else n2w exponent;
         Significand := if rounded = 2 ** 53 then 0w else n2w rounded|>
       : (52, 11) float) =
    Float (if negative then -(&rounded * (2 pow exponent / 2 pow 1075))
           else &rounded * (2 pow exponent / 2 pow 1075))
Proof
  qx_genl_tac [`negative`, `exponent`, `rounded`] >> strip_tac >>
  `float_value
     (<|Sign := 0w;
        Exponent := if rounded = 2 ** 53 then n2w (exponent + 1)
                    else n2w exponent;
        Significand := if rounded = 2 ** 53 then 0w else n2w rounded|>
      : (52, 11) float) =
   Float (&rounded * (2 pow exponent / 2 pow 1075))` by (
    Cases_on `rounded = 2 ** 53`
    >- (
      qspec_then `exponent` mp_tac normal_carry_value_positive >> gvs[]) >>
    `rounded < 2 ** 53` by decide_tac >>
    qspecl_then [`exponent`, `rounded`] mp_tac normal_float_value_positive >>
    impl_tac >- decide_tac >> simp[]) >>
  Cases_on `negative`
  >- (
    qspecl_then
      [`-(&rounded * (2 pow exponent / 2 pow 1075))`,
       `(<|Sign := 0w;
            Exponent := if rounded = 2 ** 53 then n2w (exponent + 1)
                        else n2w exponent;
            Significand := if rounded = 2 ** 53 then 0w else n2w rounded|>
         : (52, 11) float)`]
      mp_tac (GEN_ALL binary_ieeeTheory.float_negate) >>
    gvs[binary_ieeeTheory.float_negate_def, EVAL ``(-1w : word1)``]) >>
  gvs[]
QED

Theorem normal_candidate:
  ∀negative exponent rounded.
    0 < exponent ∧ exponent < 2047 ∧
    2 ** 52 <= rounded ∧ rounded <= 2 ** 53 ∧
    (rounded = 2 ** 53 ⇒ exponent < 2046) ⇒
    let scale = 2 pow exponent / 2 pow 1075 in
    let candidate =
      (<|Sign := if negative then 1w else 0w;
         Exponent := if rounded = 2 ** 53 then n2w (exponent + 1)
                     else n2w exponent;
         Significand := if rounded = 2 ** 53 then 0w else n2w rounded|>
       : (52, 11) float) in
    float_is_finite candidate ∧ ¬float_is_zero candidate ∧
    float_to_real candidate =
      (if negative then -(&rounded * scale) else &rounded * scale) ∧
    abs (float_to_real candidate) = &rounded * scale ∧
    ULP (candidate.Exponent, (:52)) =
      (if rounded = 2 ** 53 then 2 * scale else scale) ∧
    (candidate.Significand = 0w ⇒ rounded = 2 ** 52 ∨ rounded = 2 ** 53) ∧
    (word_lsb candidate.Significand ⇔ ODD rounded) ∧
    abs (float_to_real candidate) <= largest (:52 # 11) ∧
    ulp (:52 # 11) <= scale
Proof
  qx_genl_tac [`negative`, `exponent`, `rounded`] >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  qabbrev_tac `scale = 2 pow exponent / 2 pow 1075` >>
  qmatch_goalsub_abbrev_tac `float_is_finite (candidate : (52, 11) float)` >>
  `0 < scale` by (
    simp[Abbr `scale`, realTheory.REAL_LT_DIV, realTheory.REAL_POW_LT]) >>
  `0 < rounded` by (fs[EVAL ``(2 : num) ** 52``] >> decide_tac) >>
  `0 < (&rounded : real) * scale` by (
    irule realTheory.REAL_LT_MUL >> simp[]) >>
  `float_value candidate =
    Float (if negative then -(&rounded * scale) else &rounded * scale)` by (
    qspecl_then [`negative`, `exponent`, `rounded`] mp_tac
      normal_rounding_value_signed >>
    simp[Abbr `candidate`, Abbr `scale`]) >>
  `float_is_finite candidate` by
    simp[binary_ieeeTheory.float_is_finite_def] >>
  `float_to_real candidate =
    (if negative then -(&rounded * scale) else &rounded * scale)` by (
    qspec_then `candidate` mp_tac
      (GEN_ALL binary_ieeeTheory.float_is_finite_float_value) >>
    simp[EQ_SYM_EQ]) >>
  `abs (float_to_real candidate) = &rounded * scale ∧
   ¬float_is_zero candidate` by (
    Cases_on `negative` >>
    simp[binary_ieeeTheory.float_is_zero_def, realTheory.ABS_NEG] >>
    RealField.REAL_ASM_ARITH_TAC) >>
  `ULP (candidate.Exponent, (:52)) =
    (if rounded = 2 ** 53 then 2 * scale else scale)` by (
    Cases_on `rounded = 2 ** 53`
    >- (
      qspec_then `exponent` mp_tac normal_carry_ULP >>
      fs[Abbr `candidate`, Abbr `scale`]) >>
    `exponent < 2048 ∧ exponent <> 0` by decide_tac >>
    fs[Abbr `candidate`, ULP_binary64, Abbr `scale`]) >>
  `(candidate.Significand = 0w ⇒
    rounded = 2 ** 52 ∨ rounded = 2 ** 53)` by (
    Cases_on `rounded = 2 ** 53` >- simp[] >>
    `rounded < 2 ** 53` by decide_tac >>
    `rounded MOD 2 ** 52 = rounded - 2 ** 52` by (
      irule normal_significand_mod >> simp[]) >>
    fs[Abbr `candidate`, wordsTheory.n2w_11, wordsTheory.dimword_def,
       EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``] >> decide_tac) >>
  `(word_lsb candidate.Significand ⇔ ODD rounded)` by (
    Cases_on `rounded = 2 ** 53` >>
    fs[Abbr `candidate`, wordsTheory.word_lsb_n2w,
       EVAL ``(2 : num) ** 53``]) >>
  `abs (float_to_real candidate) <= largest (:52 # 11)` by (
    qspec_then `candidate` mp_tac (GEN_ALL binary_ieeeTheory.abs_float_bounds) >>
    simp[]) >>
  `ulp (:52 # 11) <= scale` by (
    `exponent < 2048 ∧ exponent <> 0` by decide_tac >>
    `ULP ((n2w exponent : word11), (:52)) = scale` by
      simp[ULP_binary64, Abbr `scale`] >>
    qpat_x_assum `ULP ((n2w exponent : word11), (:52)) = scale`
      (fn original_ulp => once_rewrite_tac [GSYM original_ulp]) >>
    irule binary_ieeeTheory.ulp_lt_ULP) >>
  fs[EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``]
QED

Theorem normal_float_round_away:
  ∀negative exponent lower error.
    0 < exponent ∧ exponent < 2047 ∧
    2 ** 52 <= lower ∧ lower < 2 ** 53 ∧ 0 <= error ∧ error < 1 ∧
    ((if error = 0 then lower else SUC lower) = 2 ** 53 ⇒ exponent < 2046) ⇒
    let rounded = if error = 0 then lower else SUC lower in
    let magnitude = (&lower + error) * (2 pow exponent / 2 pow 1075) in
    float_round (if negative then roundTowardNegative else roundTowardPositive)
      negative (if negative then -magnitude else magnitude) =
      (<|Sign := if negative then 1w else 0w;
         Exponent := if rounded = 2 ** 53 then n2w (exponent + 1)
                     else n2w exponent;
         Significand := if rounded = 2 ** 53 then 0w else n2w rounded|>
       : (52, 11) float)
Proof
  qx_genl_tac [`negative`, `exponent`, `lower`, `error`] >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  qabbrev_tac `rounded = if error = 0 then lower else SUC lower` >>
  qabbrev_tac `scale = 2 pow exponent / 2 pow 1075` >>
  qabbrev_tac `magnitude = (&lower + error) * scale` >>
  qmatch_goalsub_abbrev_tac `(float_round _ _ _) = candidate` >>
  `0 < scale` by
    simp[Abbr `scale`, realTheory.REAL_LT_DIV, realTheory.REAL_POW_LT] >>
  `0 <= scale` by RealField.REAL_ASM_ARITH_TAC >>
  `2 ** 52 <= rounded ∧ rounded <= 2 ** 53` by (
    Cases_on `error = 0` >>
    fs[Abbr `rounded`] >> decide_tac) >>
  `0 <= magnitude` by (
    simp_tac std_ss [Abbr `magnitude`] >>
    irule realTheory.REAL_LE_MUL >> conj_tac
    >- (irule realTheory.REAL_LE_ADD >> simp[]) >> simp[]) >>
  `float_is_finite candidate ∧ ¬float_is_zero candidate ∧
   float_to_real candidate =
     (if negative then -(&rounded * scale) else &rounded * scale) ∧
   abs (float_to_real candidate) = &rounded * scale ∧
   ULP (candidate.Exponent, (:52)) =
     (if rounded = 2 ** 53 then 2 * scale else scale) ∧
   (candidate.Significand = 0w ⇒ rounded = 2 ** 52 ∨ rounded = 2 ** 53) ∧
   (word_lsb candidate.Significand ⇔ ODD rounded) ∧
   abs (float_to_real candidate) <= largest (:52 # 11) ∧
   ulp (:52 # 11) <= scale` by (
    qspecl_then [`negative`, `exponent`, `rounded`] drule_all normal_candidate >>
    simp[LET_THM, Abbr `candidate`, Abbr `scale`]) >>
  `magnitude <= &rounded * scale ∧ &rounded * scale - magnitude < scale` by (
    qspecl_then [`lower`, `error`, `scale`] drule_all directed_nat_scaled_bounds >>
    asm_simp_tac std_ss [LET_THM, Abbr `rounded`, Abbr `magnitude`] >>
    strip_tac >> simp[]) >>
  `magnitude <= largest (:52 # 11)` by (
    irule realTheory.REAL_LE_TRANS >> qexists_tac `&rounded * scale` >>
    conj_tac >- simp[] >>
    qpat_x_assum `abs (float_to_real candidate) = &rounded * scale`
      (fn candidate_magnitude => once_rewrite_tac [GSYM candidate_magnitude]) >>
    simp[]) >>
  `(rounded = 2 ** 52 ⇒ magnitude = &rounded * scale)` by (
    strip_tac >>
    `error = 0` by (
      Cases_on `error = 0` >- simp[] >>
      fs[Abbr `rounded`, EVAL ``(2 : num) ** 52``] >> decide_tac) >>
    fs[Abbr `rounded`, Abbr `magnitude`]) >>
  `&rounded * scale - magnitude < ULP (candidate.Exponent, (:52))` by (
    qpat_x_assum `ULP (candidate.Exponent, (:52)) = _` SUBST1_TAC >>
    qpat_assum `&rounded * scale - magnitude < scale` mp_tac >>
    qpat_assum `0 < scale` mp_tac >>
    rpt (pop_assum kall_tac) >>
    Cases_on `rounded = 2 ** 53` >>
    asm_simp_tac std_ss [] >> RealField.REAL_ARITH_TAC) >>
  `(candidate.Significand = 0w ∧ candidate.Exponent <> 1w ⇒
    &rounded * scale - magnitude < ULP (candidate.Exponent, (:52)) / 2)` by (
    qpat_x_assum `ULP (candidate.Exponent, (:52)) = _` SUBST1_TAC >>
    qpat_assum `&rounded * scale - magnitude < scale` mp_tac >>
    qpat_assum `0 < scale` mp_tac >>
    qpat_assum `(rounded = 2 ** 52 ⇒ magnitude = &rounded * scale)` mp_tac >>
    qpat_assum `(candidate.Significand = 0w ⇒ _ ∨ _)` mp_tac >>
    rpt (pop_assum kall_tac) >> rpt strip_tac >>
    Cases_on `rounded = 2 ** 53` >>
    fs[EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``] >>
    RealField.REAL_ASM_ARITH_TAC) >>
  `0 <= &rounded * scale` by (
    irule realTheory.REAL_LE_TRANS >> qexists_tac `magnitude` >> simp[]) >>
  qpat_assum `float_is_finite candidate` mp_tac >>
  qpat_assum `¬float_is_zero candidate` mp_tac >>
  qpat_assum `float_to_real candidate = _` mp_tac >>
  qpat_assum `0 <= magnitude` mp_tac >>
  qpat_assum `magnitude <= largest (:52 # 11)` mp_tac >>
  qpat_assum `magnitude <= &rounded * scale` mp_tac >>
  qpat_assum `0 <= &rounded * scale` mp_tac >>
  qpat_assum `&rounded * scale - magnitude < ULP (candidate.Exponent, (:52))`
    mp_tac >>
  qpat_assum `(candidate.Significand = 0w ∧ candidate.Exponent <> 1w ⇒ _)`
    mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  Cases_on `negative`
  >- (
    `float_to_real candidate <= 0` by (
      asm_simp_tac std_ss [] >> RealField.REAL_ASM_ARITH_TAC) >>
    `round roundTowardNegative (-magnitude) = candidate` by (
      irule round_negative_spacing >>
      Cases_on `candidate.Significand = 0w ∧ candidate.Exponent <> 1w` >>
      fs[] >> RealField.REAL_ASM_ARITH_TAC) >>
    simp[binary_ieeeTheory.float_round_def]) >>
  `0 <= float_to_real candidate` by (
    asm_simp_tac std_ss [] >> RealField.REAL_ASM_ARITH_TAC) >>
  `round roundTowardPositive magnitude = candidate` by (
    irule round_positive_spacing >>
    Cases_on `candidate.Significand = 0w ∧ candidate.Exponent <> 1w` >>
    fs[] >> RealField.REAL_ASM_ARITH_TAC) >>
  simp[binary_ieeeTheory.float_round_def]
QED

Theorem normal_float_round_truncate:
  ∀negative mode exponent lower error.
    (mode = roundTowardZero ∨
     mode = if negative then roundTowardPositive else roundTowardNegative) ∧
    0 < exponent ∧ exponent < 2047 ∧
    2 ** 52 <= lower ∧ lower < 2 ** 53 ∧ 0 <= error ∧ error < 1 ∧
    (&lower + error) * (2 pow exponent / 2 pow 1075) <= largest (:52 # 11) ⇒
    let magnitude = (&lower + error) * (2 pow exponent / 2 pow 1075) in
    float_round mode negative (if negative then -magnitude else magnitude) =
      (<|Sign := if negative then 1w else 0w; Exponent := n2w exponent;
         Significand := n2w lower|> : (52, 11) float)
Proof
  qx_genl_tac [`negative`, `mode`, `exponent`, `lower`, `error`] >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  simp_tac std_ss [LET_THM] >>
  qabbrev_tac `scale = 2 pow exponent / 2 pow 1075` >>
  qabbrev_tac `magnitude = (&lower + error) * scale` >>
  qmatch_goalsub_abbrev_tac `(float_round _ _ _) = candidate` >>
  `0 < scale` by
    simp[Abbr `scale`, realTheory.REAL_LT_DIV, realTheory.REAL_POW_LT] >>
  `0 <= scale` by (irule realTheory.REAL_LT_IMP_LE >> simp[]) >>
  `0 < lower ∧ 1 <= lower ∧ lower <> 2 ** 53` by (
    fs[EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``] >> decide_tac) >>
  `0 < (&lower : real) * scale` by (
    irule realTheory.REAL_LT_MUL >> simp[]) >>
  `scale <= &lower * scale` by (
    qspecl_then [`scale`, `1`, `(&lower : real)`]
      mp_tac realTheory.REAL_LE_RMUL_IMP >> simp[]) >>
  `&lower * scale <= magnitude ∧ magnitude - &lower * scale < scale` by (
    qspecl_then [`lower`, `error`, `scale`] mp_tac directed_nat_scaled_bounds >>
    asm_simp_tac std_ss [LET_THM, Abbr `magnitude`]) >>
  `0 <= magnitude` by (
    irule realTheory.REAL_LE_TRANS >> qexists_tac `&lower * scale` >>
    conj_tac >- (irule realTheory.REAL_LT_IMP_LE >> simp[]) >> simp[]) >>
  `float_is_finite candidate ∧ ¬float_is_zero candidate ∧
   float_to_real candidate =
     (if negative then -(&lower * scale) else &lower * scale) ∧
   abs (float_to_real candidate) = &lower * scale ∧
   ULP (candidate.Exponent, (:52)) = scale ∧ ulp (:52 # 11) <= scale` by (
    qspecl_then [`negative`, `exponent`, `lower`] mp_tac normal_candidate >>
    impl_tac >- decide_tac >>
    qpat_assum `lower <> 2 ** 53`
      (fn no_carry => asm_simp_tac std_ss
        [LET_THM, Abbr `candidate`, Abbr `scale`, no_carry,
         REWRITE_RULE [EVAL ``(2 : num) ** 53``] no_carry]) >>
    strip_tac >> simp[]) >>
  `ulp (:52 # 11) <= magnitude` by (
    irule realTheory.REAL_LE_TRANS >> qexists_tac `scale` >>
    conj_tac >- simp[] >>
    irule realTheory.REAL_LE_TRANS >> qexists_tac `&lower * scale` >> simp[]) >>
  `float_value candidate = Float (float_to_real candidate)` by (
    qspec_then `candidate` mp_tac
      (GEN_ALL binary_ieeeTheory.float_is_finite_float_value) >> simp[]) >>
  qpat_assum `float_is_finite candidate` mp_tac >>
  qpat_assum `¬float_is_zero candidate` mp_tac >>
  qpat_assum `float_value candidate = Float (float_to_real candidate)` mp_tac >>
  qpat_assum `float_to_real candidate = _` mp_tac >>
  qpat_assum `abs (float_to_real candidate) = _` mp_tac >>
  qpat_assum `ULP (candidate.Exponent, (:52)) = scale` mp_tac >>
  qpat_assum `ulp (:52 # 11) <= magnitude` mp_tac >>
  qpat_assum `0 <= magnitude` mp_tac >>
  qpat_assum `magnitude <= largest (:52 # 11)` mp_tac >>
  qpat_assum `&lower * scale <= magnitude` mp_tac >>
  qpat_assum `magnitude - &lower * scale < scale` mp_tac >>
  qpat_assum `0 < &lower * scale` mp_tac >>
  qpat_assum `(mode = roundTowardZero ∨ _)` mp_tac >>
  rpt (pop_assum kall_tac) >> disch_then assume_tac >> rpt strip_tac >>
  Cases_on `mode = roundTowardZero`
  >- (
    qpat_x_assum `mode = roundTowardZero` SUBST_ALL_TAC >>
    `round roundTowardZero (if negative then -magnitude else magnitude) =
     candidate` by (
      qspecl_then [`candidate`, `if negative then -magnitude else magnitude`,
                   `float_to_real candidate`]
        match_mp_tac binary_ieeeTheory.round_roundTowardZero >>
      Cases_on `negative` >>
      asm_simp_tac std_ss [realTheory.ABS_NEG] >>
      RealField.REAL_ASM_ARITH_TAC) >>
    simp[binary_ieeeTheory.float_round_def]) >>
  qpat_x_assum `mode = roundTowardZero ∨ _` mp_tac >>
  simp[] >> disch_then SUBST_ALL_TAC >>
  Cases_on `negative`
  >- (
    `¬(0 <= float_to_real candidate)` by (
      asm_simp_tac std_ss [] >> RealField.REAL_ASM_ARITH_TAC) >>
    `round roundTowardPositive (-magnitude) = candidate` by (
      irule round_positive_spacing >>
      qpat_assum `¬(0 <= float_to_real candidate)`
        (SUBST1_TAC o EQF_INTRO) >>
      asm_simp_tac std_ss [] >> RealField.REAL_ASM_ARITH_TAC) >>
    simp[binary_ieeeTheory.float_round_def]) >>
  `¬(float_to_real candidate <= 0)` by (
    asm_simp_tac std_ss [] >> RealField.REAL_ASM_ARITH_TAC) >>
  `round roundTowardNegative magnitude = candidate` by (
    irule round_negative_spacing >>
    qpat_assum `¬(float_to_real candidate <= 0)`
      (SUBST1_TAC o EQF_INTRO) >>
    asm_simp_tac std_ss [] >> RealField.REAL_ASM_ARITH_TAC) >>
  simp[binary_ieeeTheory.float_round_def]
QED

Theorem normal_float_round_directed:
  ∀negative mode exponent lower error.
    mode <> roundTiesToEven ∧ 0 < exponent ∧ exponent < 2047 ∧
    2 ** 52 <= lower ∧ lower < 2 ** 53 ∧ 0 <= error ∧ error < 1 ∧
    (&lower + error) * (2 pow exponent / 2 pow 1075) <= largest (:52 # 11) ∧
    (mode = (if negative then roundTowardNegative else roundTowardPositive) ∧
     error <> 0 ∧ SUC lower = 2 ** 53 ⇒ exponent < 2046) ⇒
    let magnitude = (&lower + error) * (2 pow exponent / 2 pow 1075) in
    let increment = (error <> 0 ∧
      mode = (if negative then roundTowardNegative else roundTowardPositive)) in
    let rounded = if increment then SUC lower else lower in
    float_round mode negative (if negative then -magnitude else magnitude) =
      (<|Sign := if negative then 1w else 0w;
         Exponent := if rounded = 2 ** 53 then n2w (exponent + 1)
                     else n2w exponent;
         Significand := if rounded = 2 ** 53 then 0w else n2w rounded|>
       : (52, 11) float)
Proof
  qx_genl_tac [`negative`, `mode`, `exponent`, `lower`, `error`] >>
  strip_tac >>
  Cases_on
    `mode = (if negative then roundTowardNegative else roundTowardPositive)`
  >- (
    qspecl_then [`negative`, `exponent`, `lower`, `error`]
      mp_tac normal_float_round_away >>
    impl_tac
    >- (Cases_on `error = 0` >> fs[] >> decide_tac) >>
    Cases_on `error = 0` >> simp[LET_THM]) >>
  qspecl_then [`negative`, `mode`, `exponent`, `lower`, `error`]
    mp_tac normal_float_round_truncate >>
  impl_tac
  >- (
    Cases_on `mode` >>
    Cases_on `negative` >> fs[]) >>
  `lower <> 2 ** 53` by decide_tac >> fs[LET_THM]
QED

Theorem fp64_normal_scale:
  !exponent mantissa.
    -1022 <= exponent ==>
    (mantissa * 2 pow 52) * (2 pow Num (exponent + 1023) / 2 pow 1075) =
    mantissa * fp64_pow2 exponent
Proof
  qx_genl_tac [`exponent`, `mantissa`]
  \\ strip_tac
  \\ `0 <= exponent + 1023` by intLib.ARITH_TAC
  \\ `(&Num (exponent + 1023) : int) = exponent + 1023` by simp []
  \\ `fp64_pow2 (exponent + 1023) = 2 pow Num (exponent + 1023)` by (
    qspec_then `Num (exponent + 1023)` mp_tac fp64_pow2_of_num
    \\ asm_simp_tac std_ss [])
  \\ qspecl_then [`exponent`, `1023 : int`] mp_tac fp64_pow2_add
  \\ asm_simp_tac std_ss [fp64_pow2_of_num]
  \\ disch_then kall_tac
  \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
  \\ RealField.REAL_ARITH_TAC
QED

Theorem normal_scale_below_largest:
  !exponent value.
    0 < exponent /\ exponent < 2046 /\
    0 <= value /\ value < &((2 : num) ** 53) ==>
    value * (2 pow exponent / 2 pow 1075) < largest (:52 # 11)
Proof
  qx_genl_tac [`exponent`, `value`]
  \\ strip_tac
  \\ qabbrev_tac `scale = 2 pow exponent / ((2 : real) pow 1075)`
  \\ `exponent <= 2045` by decide_tac
  \\ `2 pow exponent <= (2 : real) pow 2045` by (
    irule realTheory.REAL_POW_MONO
    \\ simp [])
  \\ `0 < scale` by
    simp [Abbr `scale`, realTheory.REAL_LT_DIV, realTheory.REAL_POW_LT]
  \\ `scale <= (2 : real) pow 970` by (
    qpat_assum `2 pow exponent <= (2 : real) pow 2045` mp_tac
    \\ simp_tac std_ss [Abbr `scale`]
    \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
    \\ RealField.REAL_ARITH_TAC)
  \\ `value * scale < &((2 : num) ** 53) * scale` by (
    irule realTheory.REAL_LT_RMUL_IMP
    \\ asm_simp_tac std_ss [])
  \\ `&((2 : num) ** 53) * scale <= (2 : real) pow 1023` by (
    qpat_assum `scale <= (2 : real) pow 970` mp_tac
    \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
    \\ RealField.REAL_ARITH_TAC)
  \\ qspecl_then [`value * scale`, `(2 : real) pow 1023`, `largest (:52 # 11)`]
       match_mp_tac realTheory.REAL_LT_TRANS
  \\ conj_tac
  >- RealField.REAL_ASM_ARITH_TAC
  \\ simp [binary_ieeeTheory.largest_def, wordsTheory.INT_MAX_def,
           wordsTheory.INT_MIN_def, wordsTheory.UINT_MAX_def, wordsTheory.dimword_def]
  \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
QED

Theorem round_increment_not_lower:
  !lower increment bound.
    bound <= lower ==>
    ~(increment /\ (if increment then SUC lower else lower) = bound)
Proof
  qx_genl_tac [`lower`, `increment`, `bound`]
  \\ strip_tac
  \\ Cases_on `increment`
  \\ simp []
  \\ decide_tac
QED

Theorem round_increment_reaches_upper:
  !lower increment bound.
    lower < bound ==>
    (increment /\ (if increment then SUC lower else lower) = bound <=>
     (if increment then SUC lower else lower) = bound)
Proof
  qx_genl_tac [`lower`, `increment`, `bound`]
  \\ strip_tac
  \\ Cases_on `increment`
  \\ simp []
  \\ decide_tac
QED

Theorem fp64_normal_bias:
  !exponent.
    -1022 <= exponent ==>
    0 < Num (exponent + 1023) /\
    (&Num (exponent + 1023) : int) = exponent + 1023 /\
    Num (exponent + 1023 + 1) = Num (exponent + 1023) + 1 /\
    (if exponent + 1023 < 0 then 0 else exponent + 1023) = exponent + 1023
Proof
  qx_gen_tac `exponent`
  \\ strip_tac
  \\ `0 < exponent + 1023 /\ ~(exponent + 1023 < 0)` by intLib.ARITH_TAC
  \\ `0 <= exponent + 1023` by intLib.ARITH_TAC
  \\ `(&Num (exponent + 1023) : int) = exponent + 1023` by simp []
  \\ `0 < Num (exponent + 1023)` by (
    rewrite_tac [GSYM integerTheory.INT_LT]
    \\ asm_simp_tac std_ss [])
  \\ qspecl_then [`Num (exponent + 1023)`, `1`] mp_tac integerTheory.NUM_INT_ADD
  \\ asm_simp_tac std_ss []
QED

Theorem fp64_round_quantize_normal_directed:
  ∀mode negative exponent mantissa lower error.
    mode <> roundTiesToEven ∧ -1022 <= exponent ∧ exponent < 1023 ∧
    lower = Num (flr (mantissa * 2 pow 52)) ∧
    error = mantissa * 2 pow 52 - &lower ∧
    2 ** 52 <= lower ∧ lower < 2 ** 53 ∧ 0 <= error ∧ error < 1 ⇒
    fp64_round_quantize mode negative (exponent, mantissa) =
      (F, F, error <> 0,
       float_to_fp64 (float_round mode negative
         (if negative then -(mantissa * fp64_pow2 exponent)
          else mantissa * fp64_pow2 exponent)))
Proof
  qx_genl_tac [`mode`, `negative`, `exponent`, `mantissa`, `lower`, `error`] >>
  strip_tac >>
  qabbrev_tac `biased = Num (exponent + 1023)` >>
  qabbrev_tac `increment = (error <> 0 ∧
    mode = (if negative then roundTowardNegative else roundTowardPositive))` >>
  qabbrev_tac `rounded = if increment then SUC lower else lower` >>
  `0 < biased ∧ (&biased : int) = exponent + 1023 ∧
   Num (exponent + 1023 + 1) = biased + 1 ∧
   (if exponent + 1023 < 0 then 0 else exponent + 1023) = exponent + 1023` by (
    qspec_then `exponent` mp_tac fp64_normal_bias >> simp[Abbr `biased`]) >>
  `biased < 2046` by (
    rewrite_tac [GSYM integerTheory.INT_LT] >>
    asm_simp_tac std_ss [] >> intLib.ARITH_TAC) >>
  `exponent + 1023 <> 0 ∧ ¬(exponent < -1022) ∧
   ¬(2047 <= exponent + 1023) ∧ ¬(2047 <= exponent + 1023 + 1)` by
    intLib.ARITH_TAC >>
  `biased < 2047` by decide_tac >>
  `&lower + 1 <= (&((2 : num) ** 53) : real)` by (
    qpat_assum `lower < 2 ** 53` mp_tac >>
    simp_tac std_ss [realTheory.REAL_OF_NUM_SUC, realTheory.REAL_LE,
                    EVAL ``(2 : num) ** 53``] >> decide_tac) >>
  `0 <= &lower + error ∧ &lower + error < &((2 : num) ** 53)` by (
    `0 <= (&lower : real)` by simp[] >> RealField.REAL_ASM_ARITH_TAC) >>
  `&lower + error = mantissa * 2 pow 52` by RealField.REAL_ASM_ARITH_TAC >>
  `(&lower + error) * (2 pow biased / 2 pow 1075) =
   mantissa * fp64_pow2 exponent` by
    simp[Abbr `biased`, fp64_normal_scale] >>
  `(&lower + error) * (2 pow biased / 2 pow 1075) <= largest (:52 # 11)` by (
    irule realTheory.REAL_LT_IMP_LE >>
    irule normal_scale_below_largest >> simp[]) >>
  `float_round mode negative
    (if negative then -(mantissa * fp64_pow2 exponent)
     else mantissa * fp64_pow2 exponent) =
   (<|Sign := if negative then 1w else 0w;
      Exponent := if rounded = 2 ** 53 then n2w (biased + 1) else n2w biased;
      Significand := if rounded = 2 ** 53 then 0w else n2w rounded|>
    : (52, 11) float)` by (
    qspecl_then [`negative`, `mode`, `biased`, `lower`, `error`]
      mp_tac normal_float_round_directed >>
    asm_simp_tac std_ss [LET_THM, Abbr `rounded`, Abbr `increment`]) >>
  `¬(increment ∧ rounded = 2 ** 52)` by (
    qspecl_then [`lower`, `increment`, `(2 : num) ** 52`]
      mp_tac round_increment_not_lower >>
    asm_simp_tac std_ss [Abbr `rounded`]) >>
  `(increment ∧ rounded = 2 ** 53) ⇔ rounded = 2 ** 53` by (
    qspecl_then [`lower`, `increment`, `(2 : num) ** 53`]
      mp_tac round_increment_reaches_upper >>
    asm_simp_tac std_ss [Abbr `rounded`]) >>
  `(case mode of
      roundTiesToEven => 1 / 2 < error ∨ error = 1 / 2 ∧ ODD lower
    | roundTowardPositive => error <> 0 ∧ ¬negative
    | roundTowardNegative => error <> 0 ∧ negative
    | roundTowardZero => F) = increment` by (
    Cases_on `mode` >>
    Cases_on `negative` >> fs[Abbr `increment`]) >>
  `(n2w ((2 : num) ** 52) : 52 word) = 0w` by
    simp[wordsTheory.n2w_11, wordsTheory.dimword_def] >>
  qpat_assum `(if exponent + 1023 < 0 then 0 else exponent + 1023) = _`
    (fn normal_bias => simp_tac std_ss
      [fp64_round_quantize_def, LET_THM, normal_bias]) >>
  qpat_assum `exponent + 1023 <> 0`
    (fn normal_nonzero => simp_tac std_ss [normal_nonzero]) >>
  qpat_assum `lower = Num (flr _)`
    (fn lower_equation => rewrite_tac [GSYM lower_equation]) >>
  qpat_assum `error = _ - &lower`
    (fn error_equation => rewrite_tac [GSYM error_equation]) >>
  qpat_assum `(case mode of roundTiesToEven => _ | roundTowardPositive => _ |
    roundTowardNegative => _ | roundTowardZero => _) = increment`
    SUBST1_TAC >>
  qpat_x_assum `Abbrev (rounded = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_simp_tac std_ss [] >>
  `SUC lower <> 2 ** 52` by decide_tac >>
  qpat_assum `¬(increment ∧ rounded = 2 ** 52)`
    (fn not_lower => simp_tac std_ss
      [REWRITE_RULE [EVAL ``(2 : num) ** 52``] not_lower]) >>
  qpat_assum `SUC lower <> 2 ** 52`
    (fn increment_not_lower => simp_tac std_ss
      [REWRITE_RULE [EVAL ``(2 : num) ** 52``] increment_not_lower]) >>
  qpat_assum `(increment ∧ rounded = 2 ** 53) ⇔ _`
    (fn carry => rewrite_tac [REWRITE_RULE [EVAL ``(2 : num) ** 53``] carry]) >>
  qpat_assum `float_round mode negative _ = _` SUBST1_TAC >>
  Cases_on `rounded = 2 ** 53` >>
  asm_simp_tac std_ss [EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``] >>
  qpat_assum `(n2w ((2 : num) ** 52) : 52 word) = 0w`
    (fn significand_zero => rewrite_tac
      [REWRITE_RULE [EVAL ``(2 : num) ** 52``] significand_zero]) >>
  gvs[Abbr `biased`, EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``,
      EVAL ``(2 : real) pow 52``]
QED

Theorem float_round_directed_beyond_largest:
  ∀mode negative magnitude.
    mode <> roundTiesToEven ∧ largest (:52 # 11) < magnitude ⇒
    float_round mode negative (if negative then -magnitude else magnitude) =
      (<|Sign := if negative then 1w else 0w;
         Exponent :=
           if mode = (if negative then roundTowardNegative else roundTowardPositive)
           then 2047w else 2046w;
         Significand :=
           if mode = (if negative then roundTowardNegative else roundTowardPositive)
           then 0w else -1w|> : (52, 11) float)
Proof
  qx_genl_tac [`mode`, `negative`, `magnitude`] >> strip_tac >>
  `0 <= largest (:52 # 11)` by simp[] >>
  `magnitude > largest (:52 # 11) ∧
   -magnitude < -largest (:52 # 11) ∧
   ¬(magnitude < -largest (:52 # 11)) ∧
   ¬(-magnitude > largest (:52 # 11))` by
    RealField.REAL_ASM_ARITH_TAC >>
  Cases_on `mode` >>
  Cases_on `negative` >> fs[] >>
  simp[binary_ieeeTheory.float_round_def, binary_ieeeTheory.round_def,
       LET_THM, binary_ieeeTheory.float_top_def,
       binary_ieeeTheory.float_bottom_def,
       binary_ieeeTheory.float_plus_infinity_def,
       binary_ieeeTheory.float_minus_infinity_def,
       binary_ieeeTheory.float_negate_def,
       binary_ieeeTheory.float_is_zero, EVAL ``(-1w : word1)``,
       wordsTheory.UINT_MAX_def,
       wordsTheory.dimword_def]
QED

Theorem fp64_largest_top_scale:
  largest (:52 # 11) =
    (&((2 : num) ** 53) - 1) * (2 pow 2046 / 2 pow 1075)
Proof
  simp[binary_ieeeTheory.largest_def, wordsTheory.INT_MAX_def,
       wordsTheory.INT_MIN_def, wordsTheory.UINT_MAX_def, wordsTheory.dimword_def] >>
  CONV_TAC RealField.REAL_RAT_REDUCE_CONV
QED

Theorem normal_top_exceeds_largest:
  ∀lower error.
    lower < 2 ** 53 ∧ 0 <= error ∧ error < 1 ⇒
    (largest (:52 # 11) <
      (&lower + error) * (2 pow 2046 / 2 pow 1075) ⇔
     SUC lower = 2 ** 53 ∧ error <> 0)
Proof
  qx_genl_tac [`lower`, `error`] >> strip_tac >>
  `0 < (2 : real) pow 2046 / 2 pow 1075` by
    simp[realTheory.REAL_LT_DIV, realTheory.REAL_POW_LT] >>
  rewrite_tac [fp64_largest_top_scale] >>
  asm_simp_tac std_ss [realTheory.REAL_LT_RMUL] >>
  Cases_on `SUC lower = 2 ** 53`
  >- (
    `&lower + 1 = (&((2 : num) ** 53) : real)` by
      simp[realTheory.REAL_OF_NUM_SUC, realTheory.REAL_INJ] >>
    qpat_assum `SUC lower = 2 ** 53`
      (fn carry => simp_tac std_ss [REWRITE_RULE [EVAL ``(2 : num) ** 53``] carry]) >>
    qpat_assum `(&lower : real) + 1 = _` mp_tac >>
    qpat_assum `0 <= error` mp_tac >> rpt (pop_assum kall_tac) >>
    CONV_TAC RealField.REAL_RAT_REDUCE_CONV >> RealField.REAL_ARITH_TAC) >>
  `&lower + 2 <= (&((2 : num) ** 53) : real)` by (
    qpat_assum `lower < 2 ** 53` mp_tac >>
    qpat_assum `SUC lower <> 2 ** 53` mp_tac >>
    simp_tac std_ss [realTheory.REAL_OF_NUM_ADD, realTheory.REAL_LE,
      EVAL ``(2 : num) ** 53``] >> decide_tac) >>
  qpat_assum `SUC lower <> 2 ** 53`
    (fn no_carry => simp_tac std_ss
      [REWRITE_RULE [EVAL ``(2 : num) ** 53``] no_carry]) >>
  qpat_assum `(&lower : real) + 2 <= _` mp_tac >>
  qpat_assum `error < 1` mp_tac >> rpt (pop_assum kall_tac) >>
  CONV_TAC RealField.REAL_RAT_REDUCE_CONV >> RealField.REAL_ARITH_TAC
QED

Theorem normal_float_round_directed_top:
  ∀mode negative lower error.
    mode <> roundTiesToEven ∧
    2 ** 52 <= lower ∧ lower < 2 ** 53 ∧ 0 <= error ∧ error < 1 ⇒
    let magnitude = (&lower + error) * (2 pow 2046 / 2 pow 1075) in
    let increment = (error <> 0 ∧
      mode = (if negative then roundTowardNegative else roundTowardPositive)) in
    let rounded = if increment then SUC lower else lower in
    float_round mode negative (if negative then -magnitude else magnitude) =
      (<|Sign := if negative then 1w else 0w;
         Exponent := if rounded = 2 ** 53 then 2047w else 2046w;
         Significand := if rounded = 2 ** 53 then 0w else n2w rounded|>
       : (52, 11) float)
Proof
  qx_genl_tac [`mode`, `negative`, `lower`, `error`] >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  qabbrev_tac `magnitude = (&lower + error) * (2 pow 2046 / 2 pow 1075)` >>
  `(largest (:52 # 11) < magnitude) ⇔ SUC lower = 2 ** 53 ∧ error <> 0` by (
    qspecl_then [`lower`, `error`] mp_tac normal_top_exceeds_largest >>
    asm_simp_tac std_ss [Abbr `magnitude`]) >>
  Cases_on `largest (:52 # 11) < magnitude`
  >- (
    `SUC lower = 2 ** 53 ∧ error <> 0` by fs[] >>
    `lower = 2 ** 53 - 1` by decide_tac >>
    qspecl_then [`mode`, `negative`, `magnitude`]
      mp_tac float_round_directed_beyond_largest >>
    asm_simp_tac std_ss [] >>
    Cases_on
      `mode = (if negative then roundTowardNegative else roundTowardPositive)` >>
    fs[EVAL ``(n2w ((2 : num) ** 53 - 1) : 52 word)``,
       EVAL ``(2 : num) ** 53``]) >>
  qspecl_then [`negative`, `mode`, `2046`, `lower`, `error`]
    mp_tac normal_float_round_directed >>
  impl_tac
  >- (
    asm_simp_tac std_ss [GSYM realTheory.REAL_NOT_LT, Abbr `magnitude`] >>
    fs[]) >>
  asm_simp_tac std_ss [LET_THM, Abbr `magnitude`] >> simp[]
QED

Theorem fp64_round_quantize_top_directed:
  ∀mode negative mantissa lower error.
    mode <> roundTiesToEven ∧
    lower = Num (flr (mantissa * 2 pow 52)) ∧
    error = mantissa * 2 pow 52 - &lower ∧
    2 ** 52 <= lower ∧ lower < 2 ** 53 ∧ 0 <= error ∧ error < 1 ⇒
    let increment = (error <> 0 ∧
      mode = (if negative then roundTowardNegative else roundTowardPositive)) in
    let rounded = if increment then SUC lower else lower in
    fp64_round_quantize mode negative (1023, mantissa) =
      (F, rounded = 2 ** 53, error <> 0 ∨ rounded = 2 ** 53,
       float_to_fp64 (float_round mode negative
         (if negative then -(mantissa * fp64_pow2 1023)
          else mantissa * fp64_pow2 1023)))
Proof
  qx_genl_tac [`mode`, `negative`, `mantissa`, `lower`, `error`] >> strip_tac >>
  simp_tac std_ss [LET_THM] >>
  qabbrev_tac `increment = (error <> 0 ∧
    mode = (if negative then roundTowardNegative else roundTowardPositive))` >>
  qabbrev_tac `rounded = if increment then SUC lower else lower` >>
  `&lower + error = mantissa * 2 pow 52` by RealField.REAL_ASM_ARITH_TAC >>
  `(&lower + error) * (2 pow 2046 / 2 pow 1075) =
   mantissa * fp64_pow2 1023` by (
    qspecl_then [`1023`, `mantissa`] mp_tac fp64_normal_scale >> simp[]) >>
  `float_round mode negative
    (if negative then -(mantissa * fp64_pow2 1023)
     else mantissa * fp64_pow2 1023) =
   (<|Sign := if negative then 1w else 0w;
      Exponent := if rounded = 2 ** 53 then 2047w else 2046w;
      Significand := if rounded = 2 ** 53 then 0w else n2w rounded|>
    : (52, 11) float)` by (
    qspecl_then [`mode`, `negative`, `lower`, `error`]
      mp_tac normal_float_round_directed_top >>
    asm_simp_tac std_ss [LET_THM, Abbr `rounded`, Abbr `increment`]) >>
  `¬(increment ∧ rounded = 2 ** 52)` by (
    qspecl_then [`lower`, `increment`, `(2 : num) ** 52`]
      mp_tac round_increment_not_lower >>
    asm_simp_tac std_ss [Abbr `rounded`]) >>
  `(increment ∧ rounded = 2 ** 53) ⇔ rounded = 2 ** 53` by (
    qspecl_then [`lower`, `increment`, `(2 : num) ** 53`]
      mp_tac round_increment_reaches_upper >>
    asm_simp_tac std_ss [Abbr `rounded`]) >>
  `(case mode of
      roundTiesToEven => 1 / 2 < error ∨ error = 1 / 2 ∧ ODD lower
    | roundTowardPositive => error <> 0 ∧ ¬negative
    | roundTowardNegative => error <> 0 ∧ negative
    | roundTowardZero => F) = increment` by (
    Cases_on `mode` >>
    Cases_on `negative` >> fs[Abbr `increment`]) >>
  `(mode = roundTiesToEven ∨ mode = roundTowardPositive ∧ ¬negative ∨
    mode = roundTowardNegative ∧ negative) ⇔
   mode = (if negative then roundTowardNegative else roundTowardPositive)` by (
    Cases_on `mode` >>
    Cases_on `negative` >> fs[]) >>
  `rounded = 2 ** 53 ⇒
   mode = (if negative then roundTowardNegative else roundTowardPositive)` by (
    strip_tac >> `increment` by fs[] >> fs[Abbr `increment`]) >>
  `(mantissa * 2 pow 52 = &lower) ⇔ error = 0` by (
    qpat_assum `error = _ - &lower` mp_tac >>
    rpt (pop_assum kall_tac) >> RealField.REAL_ARITH_TAC) >>
  simp_tac (srw_ss()) [fp64_round_quantize_def, LET_THM] >>
  qpat_assum `lower = Num (flr _)`
    (fn lower_equation => rewrite_tac [GSYM lower_equation]) >>
  qpat_assum `error = _ - &lower`
    (fn error_equation => rewrite_tac [GSYM error_equation]) >>
  qpat_x_assum `lower = Num (flr _)` kall_tac >>
  qpat_x_assum `error = _ - &lower` kall_tac >>
  qpat_x_assum `&lower + error = _` kall_tac >>
  qpat_x_assum `(_ + error) * _ = _` kall_tac >>
  asm_simp_tac std_ss [] >>
  qpat_assum `(case mode of roundTiesToEven => _ | roundTowardPositive => _ |
    roundTowardNegative => _ | roundTowardZero => _) = increment`
    SUBST1_TAC >>
  qpat_x_assum `Abbrev (rounded = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_simp_tac std_ss [] >>
  `SUC lower <> 2 ** 52` by decide_tac >>
  qpat_assum `¬(increment ∧ rounded = 2 ** 52)`
    (fn not_lower => simp_tac std_ss
      [REWRITE_RULE [EVAL ``(2 : num) ** 52``] not_lower]) >>
  qpat_assum `SUC lower <> 2 ** 52`
    (fn increment_not_lower => simp_tac std_ss
      [REWRITE_RULE [EVAL ``(2 : num) ** 52``] increment_not_lower]) >>
  qpat_assum `(increment ∧ rounded = 2 ** 53) ⇔ _`
    (fn carry => rewrite_tac [REWRITE_RULE [EVAL ``(2 : num) ** 53``] carry]) >>
  qpat_assum `float_round mode negative _ = _` SUBST1_TAC >>
  RULE_ASSUM_TAC (REWRITE_RULE
    [EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``]) >>
  Cases_on `rounded = 9007199254740992` >>
  asm_simp_tac std_ss [] >>
  Cases_on `error = 0` >>
  gvs[Abbr `increment`, LET_THM, EVAL ``(2 : num) ** 53``]
QED

Theorem fp64_largest_below_power_1024:
  largest (:52 # 11) < fp64_pow2 1024
Proof
  simp[fp64_largest_top_scale, fp64_pow2_def] >>
  CONV_TAC RealField.REAL_RAT_REDUCE_CONV
QED

Theorem normalized_float_round_directed_large:
  ∀mode negative exponent mantissa.
    mode <> roundTiesToEven ∧ 1024 <= exponent ∧ 1 <= mantissa ⇒
    float_round mode negative
      (if negative then -(mantissa * fp64_pow2 exponent)
       else mantissa * fp64_pow2 exponent) =
      (<|Sign := if negative then 1w else 0w;
         Exponent :=
           if mode = (if negative then roundTowardNegative else roundTowardPositive)
           then 2047w else 2046w;
         Significand :=
           if mode = (if negative then roundTowardNegative else roundTowardPositive)
           then 0w else -1w|> : (52, 11) float)
Proof
  qx_genl_tac [`mode`, `negative`, `exponent`, `mantissa`] >> strip_tac >>
  `0 <= fp64_pow2 exponent` by (
    irule realTheory.REAL_LT_IMP_LE >> simp[fp64_pow2_positive]) >>
  `fp64_pow2 1024 <= fp64_pow2 exponent` by
    (irule fp64_pow2_monotone >> simp[]) >>
  `fp64_pow2 exponent <= mantissa * fp64_pow2 exponent` by (
    qspecl_then [`fp64_pow2 exponent`, `1`, `mantissa`]
      mp_tac realTheory.REAL_LE_RMUL1 >> simp[]) >>
  irule float_round_directed_beyond_largest >> asm_simp_tac std_ss [] >>
  assume_tac fp64_largest_below_power_1024 >> RealField.REAL_ASM_ARITH_TAC
QED

Theorem fp64_round_quantize_large_directed:
  ∀mode negative exponent mantissa lower.
    mode <> roundTiesToEven ∧ 1024 <= exponent ∧ 1 <= mantissa ∧
    lower = Num (flr (mantissa * 2 pow 52)) ∧ 2 ** 52 <= lower ⇒
    fp64_round_quantize mode negative (exponent, mantissa) =
      (F, T, T, float_to_fp64 (float_round mode negative
         (if negative then -(mantissa * fp64_pow2 exponent)
          else mantissa * fp64_pow2 exponent)))
Proof
  qx_genl_tac [`mode`, `negative`, `exponent`, `mantissa`, `lower`] >> strip_tac >>
  `¬(exponent + 1023 < 0) ∧ exponent + 1023 <> 0 ∧
   ¬(exponent < -1022) ∧ 2047 <= exponent + 1023 ∧
   2047 <= exponent + 1023 + 1` by intLib.ARITH_TAC >>
  `SUC lower <> 2 ** 52` by decide_tac >>
  `float_round mode negative
    (if negative then -(mantissa * fp64_pow2 exponent)
     else mantissa * fp64_pow2 exponent) =
   (<|Sign := if negative then 1w else 0w;
      Exponent :=
        if mode = (if negative then roundTowardNegative else roundTowardPositive)
        then 2047w else 2046w;
      Significand :=
        if mode = (if negative then roundTowardNegative else roundTowardPositive)
        then 0w else -1w|> : (52, 11) float)` by (
    irule normalized_float_round_directed_large >> simp[]) >>
  `(mode = roundTiesToEven ∨ mode = roundTowardPositive ∧ ¬negative ∨
    mode = roundTowardNegative ∧ negative) ⇔
   mode = (if negative then roundTowardNegative else roundTowardPositive)` by (
    Cases_on `mode` >>
    Cases_on `negative` >> fs[]) >>
  asm_simp_tac std_ss [fp64_round_quantize_def, LET_THM] >>
  qpat_assum `lower = Num (flr _)`
    (fn lower_equation => rewrite_tac [GSYM lower_equation]) >>
  qabbrev_tac `error = mantissa * 2 pow 52 - &lower` >>
  qpat_x_assum `lower = Num (flr _)` kall_tac >>
  qmatch_goalsub_abbrev_tac `if increment then SUC lower else lower` >>
  RULE_ASSUM_TAC (REWRITE_RULE
    [EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``]) >>
  Cases_on `increment` >>
  asm_simp_tac std_ss [] >>
  Cases_on `SUC lower = 2 ** 53` >>
  asm_simp_tac std_ss [EVAL ``(2 : num) ** 53``] >>
  fs[EVAL ``(2 : num) ** 53``]
QED

Theorem floor_nat_interval:
  !(scaled : real) (lower_bound : num) upper_bound.
    &lower_bound <= scaled /\ scaled < &upper_bound ==>
    let lower = Num (flr scaled) in
    lower_bound <= lower /\ lower < upper_bound /\
    0 <= scaled - &lower /\ scaled - &lower < 1
Proof
  qx_genl_tac [`scaled`, `lower_bound`, `upper_bound`] \\ strip_tac
  \\ `0 <= scaled` by (
    `0 <= (&lower_bound : real)` by simp []
    \\ RealField.REAL_ASM_ARITH_TAC)
  \\ drule nonnegative_floor_nat \\ strip_tac
  \\ qspec_then `scaled` mp_tac intrealTheory.INT_FLOOR_BOUNDS
  \\ qpat_assum `(&Num (flr scaled) : real) = _`
       (fn cast => rewrite_tac
         [intrealTheory.real_of_int_add, intrealTheory.real_of_int_num,
          GSYM cast])
  \\ strip_tac
  \\ simp_tac std_ss [LET_THM]
  \\ qabbrev_tac `lower = Num (flr scaled)`
  \\ `lower < upper_bound` by (
    rewrite_tac [GSYM realTheory.REAL_LT]
    \\ RealField.REAL_ASM_ARITH_TAC)
  \\ `lower_bound <= lower` by (
    CCONTR_TAC
    \\ `(&lower : real) + 1 <= &lower_bound` by (
      simp_tac std_ss [realTheory.REAL_OF_NUM_SUC, realTheory.REAL_LE]
      \\ decide_tac)
    \\ RealField.REAL_ASM_ARITH_TAC)
  \\ simp []
  \\ RealField.REAL_ASM_ARITH_TAC
QED

Theorem fp64_normal_scaled_floor:
  !mantissa.
    1 <= mantissa /\ mantissa < 2 ==>
    let lower = Num (flr (mantissa * 2 pow 52)) in
    let error = mantissa * 2 pow 52 - &lower in
    2 ** 52 <= lower /\ lower < 2 ** 53 /\ 0 <= error /\ error < 1
Proof
  qx_gen_tac `mantissa` \\ strip_tac
  \\ qspecl_then [`mantissa * 2 pow 52`, `(2 : num) ** 52`, `(2 : num) ** 53`]
       mp_tac floor_nat_interval
  \\ impl_tac
  >- (
    CONV_TAC RealField.REAL_RAT_REDUCE_CONV
    \\ RealField.REAL_ASM_ARITH_TAC)
  \\ simp_tac std_ss [LET_THM]
QED

Theorem fp64_subnormal_scaled_floor:
  !exponent mantissa.
    exponent < -1022 /\ 1 <= mantissa /\ mantissa < 2 ==>
    let scaled = mantissa / fp64_pow2 (-1022 - exponent) * 2 pow 52 in
    let lower = Num (flr scaled) in
    let error = scaled - &lower in
    0 < scaled /\ scaled < &((2 : num) ** 52) /\ lower < 2 ** 52 /\
    0 <= error /\ error < 1
Proof
  qx_genl_tac [`exponent`, `mantissa`] \\ strip_tac
  \\ `2 <= fp64_pow2 (-1022 - exponent)` by (
    qspecl_then [`1`, `-1022 - exponent`] mp_tac fp64_pow2_monotone
    \\ impl_tac >- intLib.ARITH_TAC
    \\ simp_tac std_ss [EVAL ``fp64_pow2 1``])
  \\ `0 < fp64_pow2 (-1022 - exponent)` by simp [fp64_pow2_positive]
  \\ `0 < mantissa` by RealField.REAL_ASM_ARITH_TAC
  \\ `0 < mantissa / fp64_pow2 (-1022 - exponent)` by
    simp [realTheory.REAL_LT_DIV]
  \\ `mantissa / fp64_pow2 (-1022 - exponent) < 1` by (
    asm_simp_tac std_ss [realTheory.REAL_LT_LDIV_EQ, realTheory.REAL_MUL_LID]
    \\ RealField.REAL_ASM_ARITH_TAC)
  \\ simp_tac std_ss [LET_THM]
  \\ qmatch_goalsub_abbrev_tac `Num (flr scaled)`
  \\ `0 < scaled /\ scaled < &((2 : num) ** 52)` by (
    simp_tac std_ss [Abbr `scaled`]
    \\ qpat_assum `mantissa / _ < 1` mp_tac
    \\ qpat_assum `0 < mantissa / _` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
    \\ qabbrev_tac `ratio = mantissa / fp64_pow2 (-1022 - exponent)`
    \\ RealField.REAL_ARITH_TAC)
  \\ qspecl_then [`scaled`, `0`, `(2 : num) ** 52`] mp_tac floor_nat_interval
  \\ gvs [LET_THM, realTheory.REAL_LE_LT, EVAL ``(2 : num) ** 52``]
QED

Theorem normalized_fp64_source:
  !negative exponent mantissa.
    1 <= mantissa /\ mantissa < 2 ==>
    let magnitude = mantissa * fp64_pow2 exponent in
    let source = if negative then -magnitude else magnitude in
    0 < magnitude /\ abs source = magnitude /\
    (abs source < 2 / 2 pow (INT_MAX (:11)) <=> exponent < -1022) /\
    (2 pow (INT_MIN (:11)) <= abs source <=> 1024 <= exponent)
Proof
  qx_genl_tac [`negative`, `exponent`, `mantissa`] \\ strip_tac
  \\ `0 < mantissa` by RealField.REAL_ASM_ARITH_TAC
  \\ `0 < mantissa * fp64_pow2 exponent` by
    (irule realTheory.REAL_LT_MUL \\ simp [fp64_pow2_positive])
  \\ `0 <= mantissa * fp64_pow2 exponent` by
    (irule realTheory.REAL_LT_IMP_LE \\ simp [])
  \\ `2 / 2 pow (INT_MAX (:11)) = fp64_pow2 (-1022)` by (
    simp [fp64_pow2_def, wordsTheory.INT_MAX_def,
          wordsTheory.INT_MIN_def, wordsTheory.dimword_def]
    \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV)
  \\ `2 pow (INT_MIN (:11)) = fp64_pow2 1024` by (
    simp [fp64_pow2_def, wordsTheory.INT_MIN_def])
  \\ qspecl_then [`exponent`, `mantissa`, `-1022`]
       mp_tac normalized_pow2_threshold
  \\ impl_tac >- simp []
  \\ strip_tac
  \\ qspecl_then [`exponent`, `mantissa`, `1024`]
       mp_tac normalized_pow2_threshold
  \\ impl_tac >- simp []
  \\ strip_tac
  \\ `abs (mantissa * fp64_pow2 exponent) = mantissa * fp64_pow2 exponent` by
    asm_simp_tac std_ss [realTheory.ABS_REFL]
  \\ Cases_on `negative`
  \\ asm_simp_tac std_ss
       [LET_THM, realTheory.ABS_NEG, GSYM realTheory.REAL_NOT_LT,
        GSYM integerTheory.INT_NOT_LT]
QED

Theorem round_increment_exact:
  ∀lower error increment.
    0 <= error ∧ error < 1 ∧ (error = 0 ⇒ ¬increment) ⇒
    ((&(if increment then SUC lower else lower) : real) = &lower + error ⇔
     error = 0)
Proof
  qx_genl_tac [`lower`, `error`, `increment`] >> strip_tac >>
  Cases_on `increment` >> fs[] >>
  rewrite_tac [GSYM realTheory.REAL_OF_NUM_SUC] >>
  RealField.REAL_ASM_ARITH_TAC
QED

Theorem round_increment_signed_precision:
  ∀negative lower error increment scale (candidate : (52, 11) float).
    0 <= error ∧ error < 1 ∧ 0 < scale ∧ (error = 0 ⇒ ¬increment) ∧
    float_value candidate =
      Float (if negative then -(&(if increment then SUC lower else lower) * scale)
             else &(if increment then SUC lower else lower) * scale) ⇒
    (float_value candidate =
      Float (if negative then -((&lower + error) * scale)
             else (&lower + error) * scale) ⇔ error = 0)
Proof
  qx_genl_tac [`negative`, `lower`, `error`, `increment`, `scale`, `candidate`] >>
  strip_tac >>
  `scale <> 0` by RealField.REAL_ASM_ARITH_TAC >>
  Cases_on `negative` >>
  gvs[realTheory.REAL_EQ_RMUL, round_increment_exact]
QED

Theorem fp64_round_quantize_subnormal_directed_flags:
  ∀mode negative exponent mantissa.
    mode <> roundTiesToEven ∧ exponent < -1022 ∧ 1 <= mantissa ∧ mantissa < 2 ⇒
    let source = if negative then -(mantissa * fp64_pow2 exponent)
                 else mantissa * fp64_pow2 exponent in
    let (flags, result) =
      (float_round_with_flags mode negative source : flags # (52, 11) float) in
    fp64_round_quantize mode negative (exponent, mantissa) =
      (flags.Underflow_BeforeRounding, flags.Overflow, flags.Precision,
       float_to_fp64 result)
Proof
  qx_genl_tac [`mode`, `negative`, `exponent`, `mantissa`] >> strip_tac >>
  qspecl_then [`exponent`, `mantissa`] mp_tac fp64_subnormal_scaled_floor >>
  impl_tac >- simp[] >> simp_tac std_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `scaled = mantissa / fp64_pow2 (-1022 - exponent) * 2 pow 52` >>
  qabbrev_tac `lower = Num (flr scaled)` >>
  qabbrev_tac `error = scaled - &lower` >>
  qabbrev_tac `source = if negative then -(mantissa * fp64_pow2 exponent)
                       else mantissa * fp64_pow2 exponent` >>
  qabbrev_tac `result : (52, 11) float = float_round mode negative source` >>
  qabbrev_tac `increment = (error <> 0 ∧
    mode = (if negative then roundTowardNegative else roundTowardPositive))` >>
  qabbrev_tac `rounded = if increment then SUC lower else lower` >>
  `&lower + error = scaled` by
    (simp_tac std_ss [Abbr `error`] >> RealField.REAL_ARITH_TAC) >>
  `scaled * (1 / 2 pow 1074) = mantissa * fp64_pow2 exponent` by
    simp[Abbr `scaled`, fp64_subnormal_scale] >>
  `rounded <= 2 ** 52` by (
    Cases_on `increment` >>
    fs[Abbr `rounded`] >> decide_tac) >>
  `result =
   (<|Sign := if negative then 1w else 0w;
      Exponent := if rounded = 2 ** 52 then 1w else 0w;
      Significand := n2w rounded|> : (52, 11) float)` by (
    qspecl_then [`negative`, `mode`, `lower`, `error`]
      mp_tac subnormal_float_round_directed >>
    asm_simp_tac std_ss [LET_THM, Abbr `source`, Abbr `result`,
      Abbr `rounded`, Abbr `increment`]) >>
  `float_value result =
   Float (if negative then -(&rounded * (1 / 2 pow 1074))
          else &rounded * (1 / 2 pow 1074))` by (
    qspecl_then [`negative`, `rounded`] mp_tac subnormal_rounding_value_signed >>
    asm_simp_tac std_ss [realTheory.real_div, realTheory.REAL_MUL_LID]) >>
  `(float_value result = Float source) ⇔ error = 0` by (
    qspecl_then [`negative`, `lower`, `error`, `increment`,
      `1 / 2 pow 1074`, `result`] mp_tac round_increment_signed_precision >>
    asm_simp_tac std_ss [Abbr `source`, Abbr `rounded`, Abbr `increment`,
      realTheory.REAL_LT_DIV, realTheory.REAL_POW_LT,
      EVAL ``(0 : real) < 1``, EVAL ``(0 : real) < 2``]) >>
  `¬float_is_infinite result` by simp[binary_ieeeTheory.float_is_infinite_def] >>
  `(abs source < 2 / 2 pow (INT_MAX (:11))) ∧
   ¬(2 pow (INT_MIN (:11)) <= abs source)` by (
    qspecl_then [`negative`, `exponent`, `mantissa`] mp_tac normalized_fp64_source >>
    asm_simp_tac std_ss [LET_THM, Abbr `source`] >>
    strip_tac >> intLib.ARITH_TAC) >>
  `fp64_round_quantize mode negative (exponent, mantissa) =
    (error <> 0, F, error <> 0, float_to_fp64 result)` by (
    qspecl_then [`mode`, `negative`, `exponent`, `mantissa`, `lower`, `error`]
      mp_tac fp64_round_quantize_subnormal_directed >>
    asm_simp_tac std_ss [Abbr `scaled`, Abbr `lower`, Abbr `error`,
      Abbr `source`, Abbr `result`]) >>
  qpat_x_assum `result = _` kall_tac >>
  qpat_x_assum `float_value result = Float _` kall_tac >>
  qpat_x_assum `Abbrev (result = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_simp_tac (srw_ss())
    [binary_ieeeTheory.float_round_with_flags_def, LET_THM] >> fs[]
QED

Theorem fp64_round_quantize_normal_directed_flags:
  ∀mode negative exponent mantissa.
    mode <> roundTiesToEven ∧ -1022 <= exponent ∧ exponent < 1023 ∧
    1 <= mantissa ∧ mantissa < 2 ⇒
    let source = if negative then -(mantissa * fp64_pow2 exponent)
                 else mantissa * fp64_pow2 exponent in
    let (flags, result) =
      (float_round_with_flags mode negative source : flags # (52, 11) float) in
    fp64_round_quantize mode negative (exponent, mantissa) =
      (flags.Underflow_BeforeRounding, flags.Overflow, flags.Precision,
       float_to_fp64 result)
Proof
  qx_genl_tac [`mode`, `negative`, `exponent`, `mantissa`] >> strip_tac >>
  qspec_then `mantissa` mp_tac fp64_normal_scaled_floor >>
  impl_tac >- simp[] >> simp_tac std_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `lower = Num (flr (mantissa * 2 pow 52))` >>
  qabbrev_tac `error = mantissa * 2 pow 52 - &lower` >>
  qabbrev_tac `biased = Num (exponent + 1023)` >>
  qabbrev_tac `source = if negative then -(mantissa * fp64_pow2 exponent)
                       else mantissa * fp64_pow2 exponent` >>
  qabbrev_tac `result : (52, 11) float = float_round mode negative source` >>
  qabbrev_tac `increment = (error <> 0 ∧
    mode = (if negative then roundTowardNegative else roundTowardPositive))` >>
  qabbrev_tac `rounded = if increment then SUC lower else lower` >>
  `0 < biased ∧ (&biased : int) = exponent + 1023` by (
    qspec_then `exponent` mp_tac fp64_normal_bias >> simp[Abbr `biased`]) >>
  `biased < 2046` by (
    rewrite_tac [GSYM integerTheory.INT_LT] >>
    asm_simp_tac std_ss [] >> intLib.ARITH_TAC) >>
  `&lower + error = mantissa * 2 pow 52` by
    (simp_tac std_ss [Abbr `error`] >> RealField.REAL_ARITH_TAC) >>
  `(&lower + error) * (2 pow biased / 2 pow 1075) =
   mantissa * fp64_pow2 exponent` by simp[Abbr `biased`, fp64_normal_scale] >>
  `2 ** 52 <= rounded ∧ rounded <= 2 ** 53` by (
    Cases_on `increment` >> fs[Abbr `rounded`] >> decide_tac) >>
  `&lower + 1 <= (&((2 : num) ** 53) : real)` by (
    qpat_assum `lower < _` mp_tac >>
    simp_tac std_ss [realTheory.REAL_OF_NUM_SUC, realTheory.REAL_LE,
      EVAL ``(2 : num) ** 53``] >> decide_tac) >>
  `0 <= &lower + error ∧ &lower + error < &((2 : num) ** 53)` by (
    qpat_assum `(&lower : real) + 1 <= _` mp_tac >>
    qpat_assum `0 <= error` mp_tac >> qpat_assum `error < 1` mp_tac >>
    `0 <= (&lower : real)` by simp[] >> pop_assum mp_tac >>
    rpt (pop_assum kall_tac) >> RealField.REAL_ARITH_TAC) >>
  `(&lower + error) * (2 pow biased / 2 pow 1075) <= largest (:52 # 11)` by (
    irule realTheory.REAL_LT_IMP_LE >>
    irule normal_scale_below_largest >> simp[]) >>
  `result =
   (<|Sign := if negative then 1w else 0w;
      Exponent := if rounded = 2 ** 53 then n2w (biased + 1) else n2w biased;
      Significand := if rounded = 2 ** 53 then 0w else n2w rounded|>
    : (52, 11) float)` by (
    qspecl_then [`negative`, `mode`, `biased`, `lower`, `error`]
      mp_tac normal_float_round_directed >>
    `biased < 2047` by decide_tac >>
    asm_simp_tac std_ss [LET_THM, Abbr `source`, Abbr `result`,
      Abbr `rounded`, Abbr `increment`]) >>
  `float_value result =
   Float (if negative then -(&rounded * (2 pow biased / 2 pow 1075))
          else &rounded * (2 pow biased / 2 pow 1075))` by (
    qspecl_then [`negative`, `biased`, `rounded`]
      mp_tac normal_rounding_value_signed >>
    asm_simp_tac std_ss [] >> impl_tac >- decide_tac >>
    asm_simp_tac std_ss [LET_THM]) >>
  `(float_value result = Float source) ⇔ error = 0` by (
    qspecl_then [`negative`, `lower`, `error`, `increment`,
      `2 pow biased / 2 pow 1075`, `result`] mp_tac round_increment_signed_precision >>
    asm_simp_tac std_ss [Abbr `source`, Abbr `rounded`, Abbr `increment`,
      realTheory.REAL_LT_DIV, realTheory.REAL_POW_LT, EVAL ``(0 : real) < 2``]) >>
  `¬float_is_infinite result` by simp[binary_ieeeTheory.float_is_infinite_def] >>
  `¬(abs source < 2 / 2 pow (INT_MAX (:11))) ∧
   ¬(2 pow (INT_MIN (:11)) <= abs source)` by (
    qspecl_then [`negative`, `exponent`, `mantissa`] mp_tac normalized_fp64_source >>
    asm_simp_tac std_ss [LET_THM, Abbr `source`] >>
    strip_tac >> intLib.ARITH_TAC) >>
  `fp64_round_quantize mode negative (exponent, mantissa) =
    (F, F, error <> 0, float_to_fp64 result)` by (
    qspecl_then [`mode`, `negative`, `exponent`, `mantissa`, `lower`, `error`]
      mp_tac fp64_round_quantize_normal_directed >>
    asm_simp_tac std_ss [Abbr `lower`, Abbr `error`, Abbr `source`, Abbr `result`]) >>
  qpat_x_assum `result = _` kall_tac >>
  qpat_x_assum `float_value result = Float _` kall_tac >>
  qpat_x_assum `Abbrev (result = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_simp_tac (srw_ss())
    [binary_ieeeTheory.float_round_with_flags_def, LET_THM] >> fs[]
QED

Theorem fp64_round_quantize_top_directed_flags:
  ∀mode negative mantissa.
    mode <> roundTiesToEven ∧ 1 <= mantissa ∧ mantissa < 2 ⇒
    let source = if negative then -(mantissa * fp64_pow2 1023)
                 else mantissa * fp64_pow2 1023 in
    let (flags, result) =
      (float_round_with_flags mode negative source : flags # (52, 11) float) in
    fp64_round_quantize mode negative (1023, mantissa) =
      (flags.Underflow_BeforeRounding, flags.Overflow, flags.Precision,
       float_to_fp64 result)
Proof
  qx_genl_tac [`mode`, `negative`, `mantissa`] >> strip_tac >>
  qspec_then `mantissa` mp_tac fp64_normal_scaled_floor >>
  impl_tac >- simp[] >> simp_tac std_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `lower = Num (flr (mantissa * 2 pow 52))` >>
  qabbrev_tac `error = mantissa * 2 pow 52 - &lower` >>
  qabbrev_tac `source = if negative then -(mantissa * fp64_pow2 1023)
                       else mantissa * fp64_pow2 1023` >>
  qabbrev_tac `result : (52, 11) float = float_round mode negative source` >>
  qabbrev_tac `increment = (error <> 0 ∧
    mode = (if negative then roundTowardNegative else roundTowardPositive))` >>
  qabbrev_tac `rounded = if increment then SUC lower else lower` >>
  `&lower + error = mantissa * 2 pow 52` by
    (simp_tac std_ss [Abbr `error`] >> RealField.REAL_ARITH_TAC) >>
  `(&lower + error) * (2 pow 2046 / 2 pow 1075) =
   mantissa * fp64_pow2 1023` by (
    qspecl_then [`1023`, `mantissa`] mp_tac fp64_normal_scale >> simp[]) >>
  `2 ** 52 <= rounded ∧ rounded <= 2 ** 53` by (
    Cases_on `increment` >> fs[Abbr `rounded`] >> decide_tac) >>
  `result =
   (<|Sign := if negative then 1w else 0w;
      Exponent := if rounded = 2 ** 53 then 2047w else 2046w;
      Significand := if rounded = 2 ** 53 then 0w else n2w rounded|>
    : (52, 11) float)` by (
    qspecl_then [`mode`, `negative`, `lower`, `error`]
      mp_tac normal_float_round_directed_top >>
    asm_simp_tac std_ss [LET_THM, Abbr `source`, Abbr `result`,
      Abbr `rounded`, Abbr `increment`]) >>
  `(float_is_infinite result ⇔ rounded = 2 ** 53)` by (
    Cases_on `rounded = 2 ** 53` >>
    simp[binary_ieeeTheory.float_is_infinite_def,
      binary_ieeeTheory.float_value_def, wordsTheory.UINT_MAX_def]) >>
  `(float_value result = Float source) ⇔ error = 0 ∧ rounded <> 2 ** 53` by (
    Cases_on `rounded = 2 ** 53`
    >- simp[binary_ieeeTheory.float_value_def, wordsTheory.UINT_MAX_def] >>
    `float_value result =
      Float (if negative then -(&rounded * (2 pow 2046 / 2 pow 1075))
             else &rounded * (2 pow 2046 / 2 pow 1075))` by (
      qspecl_then [`negative`, `2046`, `rounded`]
        mp_tac normal_rounding_value_signed >> asm_simp_tac std_ss []) >>
    qspecl_then [`negative`, `lower`, `error`, `increment`,
      `2 pow 2046 / 2 pow 1075`, `result`] mp_tac round_increment_signed_precision >>
    asm_simp_tac std_ss [Abbr `source`, Abbr `rounded`, Abbr `increment`,
      realTheory.REAL_LT_DIV, realTheory.REAL_POW_LT, EVAL ``(0 : real) < 2``]) >>
  `¬(abs source < 2 / 2 pow (INT_MAX (:11))) ∧
   ¬(2 pow (INT_MIN (:11)) <= abs source)` by (
    qspecl_then [`negative`, `1023`, `mantissa`] mp_tac normalized_fp64_source >>
    asm_simp_tac std_ss [LET_THM, Abbr `source`] >> simp[]) >>
  `fp64_round_quantize mode negative (1023, mantissa) =
    (F, rounded = 2 ** 53, error <> 0 ∨ rounded = 2 ** 53,
     float_to_fp64 result)` by (
    qspecl_then [`mode`, `negative`, `mantissa`, `lower`, `error`]
      mp_tac fp64_round_quantize_top_directed >>
    asm_simp_tac std_ss [LET_THM, Abbr `lower`, Abbr `error`, Abbr `source`,
      Abbr `result`, Abbr `rounded`, Abbr `increment`]) >>
  qpat_x_assum `result = _` kall_tac >>
  qpat_x_assum `Abbrev (result = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_simp_tac (srw_ss())
    [binary_ieeeTheory.float_round_with_flags_def, LET_THM] >> fs[]
QED

Theorem binary64_inexact_outside_largest:
  ∀source (candidate : (52, 11) float).
    largest (:52 # 11) < abs source ⇒ float_value candidate <> Float source
Proof
  qx_genl_tac [`source`, `candidate`] >> strip_tac >> CCONTR_TAC >> fs[] >>
  qspecl_then [`source`, `candidate`] mp_tac (GEN_ALL binary_ieeeTheory.float_bounds) >>
  asm_simp_tac std_ss [EVAL ``(2 : num) <= dimindex(:11)``] >>
  once_rewrite_tac [GSYM DE_MORGAN_THM] >>
  once_rewrite_tac [GSYM realTheory.ABS_BOUNDS] >>
  asm_simp_tac std_ss [realTheory.REAL_NOT_LE]
QED

Theorem fp64_round_quantize_large_directed_flags:
  ∀mode negative exponent mantissa.
    mode <> roundTiesToEven ∧ 1024 <= exponent ∧ 1 <= mantissa ∧ mantissa < 2 ⇒
    let source = if negative then -(mantissa * fp64_pow2 exponent)
                 else mantissa * fp64_pow2 exponent in
    let (flags, result) =
      (float_round_with_flags mode negative source : flags # (52, 11) float) in
    fp64_round_quantize mode negative (exponent, mantissa) =
      (flags.Underflow_BeforeRounding, flags.Overflow, flags.Precision,
       float_to_fp64 result)
Proof
  qx_genl_tac [`mode`, `negative`, `exponent`, `mantissa`] >> strip_tac >>
  qspec_then `mantissa` mp_tac fp64_normal_scaled_floor >>
  impl_tac >- simp[] >> simp_tac std_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `lower = Num (flr (mantissa * 2 pow 52))` >>
  qabbrev_tac `source = if negative then -(mantissa * fp64_pow2 exponent)
                       else mantissa * fp64_pow2 exponent` >>
  qabbrev_tac `result : (52, 11) float = float_round mode negative source` >>
  `¬(abs source < 2 / 2 pow (INT_MAX (:11))) ∧
   2 pow (INT_MIN (:11)) <= abs source` by (
    qspecl_then [`negative`, `exponent`, `mantissa`] mp_tac normalized_fp64_source >>
    asm_simp_tac std_ss [LET_THM, Abbr `source`] >>
    strip_tac >> intLib.ARITH_TAC) >>
  `2 pow (INT_MIN (:11)) = fp64_pow2 1024` by
    simp[fp64_pow2_def, wordsTheory.INT_MIN_def] >>
  `largest (:52 # 11) < abs source` by (
    assume_tac fp64_largest_below_power_1024 >> RealField.REAL_ASM_ARITH_TAC) >>
  `float_value result <> Float source` by
    (irule binary64_inexact_outside_largest >> simp[]) >>
  `fp64_round_quantize mode negative (exponent, mantissa) =
    (F, T, T, float_to_fp64 result)` by (
    qspecl_then [`mode`, `negative`, `exponent`, `mantissa`, `lower`]
      mp_tac fp64_round_quantize_large_directed >>
    asm_simp_tac std_ss [Abbr `lower`, Abbr `source`, Abbr `result`]) >>
  qpat_x_assum `Abbrev (result = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_simp_tac (srw_ss())
    [binary_ieeeTheory.float_round_with_flags_def, LET_THM] >> fs[]
QED

Theorem fp64_round_quantize_directed_flags:
  ∀mode negative exponent mantissa.
    mode <> roundTiesToEven ∧ 1 <= mantissa ∧ mantissa < 2 ⇒
    let source = if negative then -(mantissa * fp64_pow2 exponent)
                 else mantissa * fp64_pow2 exponent in
    let (flags, result) =
      (float_round_with_flags mode negative source : flags # (52, 11) float) in
    fp64_round_quantize mode negative (exponent, mantissa) =
      (flags.Underflow_BeforeRounding, flags.Overflow, flags.Precision,
       float_to_fp64 result)
Proof
  qx_genl_tac [`mode`, `negative`, `exponent`, `mantissa`] >> strip_tac >>
  Cases_on `exponent < -1022`
  >- (
    qspecl_then [`mode`, `negative`, `exponent`, `mantissa`]
      mp_tac fp64_round_quantize_subnormal_directed_flags >>
    asm_simp_tac std_ss []) >>
  Cases_on `exponent < 1023`
  >- (
    `-1022 <= exponent` by intLib.ARITH_TAC >>
    qspecl_then [`mode`, `negative`, `exponent`, `mantissa`]
      mp_tac fp64_round_quantize_normal_directed_flags >>
    asm_simp_tac std_ss []) >>
  Cases_on `exponent = 1023`
  >- (
    qspecl_then [`mode`, `negative`, `mantissa`]
      mp_tac fp64_round_quantize_top_directed_flags >>
    asm_simp_tac std_ss []) >>
  `1024 <= exponent` by intLib.ARITH_TAC >>
  qspecl_then [`mode`, `negative`, `exponent`, `mantissa`]
    mp_tac fp64_round_quantize_large_directed_flags >>
  asm_simp_tac std_ss []
QED

Definition nearest_even_nat_def:
  nearest_even_nat (lower : num) (error : real) =
    if 1 / 2 < error \/ error = 1 / 2 /\ ODD lower then SUC lower else lower
End

Theorem nearest_even_nat_bounds:
  !lower error.
    lower <= nearest_even_nat lower error /\
    nearest_even_nat lower error <= SUC lower
Proof
  qx_genl_tac [`lower`, `error`]
  \\ Cases_on `1 / 2 < error \/ error = 1 / 2 /\ ODD lower`
  \\ simp [nearest_even_nat_def]
QED

Theorem nearest_even_nat_error:
  !lower error.
    0 <= error /\ error < 1 ==>
    abs (&(nearest_even_nat lower error) - (&lower + error)) <= 1 / 2 /\
    (abs (&(nearest_even_nat lower error) - (&lower + error)) = 1 / 2 ==>
     ~ODD (nearest_even_nat lower error))
Proof
  qx_genl_tac [`lower`, `error`]
  \\ strip_tac
  \\ `abs (&(nearest_even_nat lower error) - (&lower + error)) <= 1 / 2 /\
       (abs (&(nearest_even_nat lower error) - (&lower + error)) = 1 / 2 ==>
        error = 1 / 2)` by (
    qspecl_then [`&lower`, `error`, `ODD lower`] mp_tac nearest_even_error_bound
    \\ Cases_on `1 / 2 < error \/ error = 1 / 2 /\ ODD lower`
    \\ asm_simp_tac std_ss
         [nearest_even_nat_def, LET_THM, intrealTheory.real_of_int_add,
          intrealTheory.real_of_int_num, realTheory.REAL_OF_NUM_SUC])
  \\ conj_tac >- simp []
  \\ strip_tac
  \\ gvs []
  \\ Cases_on `ODD lower`
  \\ simp [nearest_even_nat_def, arithmeticTheory.ODD]
QED

Theorem nearest_even_nat_positive:
  !lower error.
    0 <= error /\ error < 1 ==>
    (0 < nearest_even_nat lower error <=> 1 / 2 < &lower + error)
Proof
  qx_genl_tac [`lower`, `error`]
  \\ strip_tac
  \\ namedCases_on `lower` ["", "previous"]
  >- simp [nearest_even_nat_def, arithmeticTheory.ODD, COND_RAND]
  \\ `0 < nearest_even_nat (SUC previous) error` by (
    qspecl_then [`SUC previous`, `error`] mp_tac nearest_even_nat_bounds
    \\ decide_tac)
  \\ simp []
  \\ `0 <= (&previous : real)` by simp []
  \\ simp_tac std_ss [GSYM realTheory.REAL_OF_NUM_SUC]
  \\ RealField.REAL_ASM_ARITH_TAC
QED

Theorem nearest_even_nat_scaled_error:
  !lower error scale.
    0 <= error /\ error < 1 /\ 0 < scale ==>
    2 * abs (&(nearest_even_nat lower error) * scale -
             (&lower + error) * scale) <= scale /\
    (2 * abs (&(nearest_even_nat lower error) * scale -
              (&lower + error) * scale) = scale ==>
     ~ODD (nearest_even_nat lower error))
Proof
  qx_genl_tac [`lower`, `error`, `scale`]
  \\ strip_tac
  \\ qspecl_then [`lower`, `error`] mp_tac nearest_even_nat_error
  \\ impl_tac >- simp []
  \\ disch_then strip_assume_tac
  \\ `0 <= scale /\ scale <> 0` by (
    qpat_assum `0 < scale` mp_tac
    \\ RealField.REAL_ARITH_TAC)
  \\ rewrite_tac [GSYM realTheory.REAL_SUB_RDISTRIB, realTheory.ABS_MUL]
  \\ asm_simp_tac std_ss [realTheory.ABS_REFL, realTheory.REAL_MUL_ASSOC]
  \\ qabbrev_tac `distance = abs (&(nearest_even_nat lower error) - (&lower + error))`
  \\ `abs scale = scale` by simp [realTheory.ABS_REFL]
  \\ asm_simp_tac std_ss []
  \\ `2 * distance <= 1` by (
    qpat_assum `distance <= 1 / 2` mp_tac
    \\ RealField.REAL_ARITH_TAC)
  \\ conj_tac
  >- (
    qspecl_then [`scale`, `2 * distance`, `1`] mp_tac realTheory.REAL_LE_RMUL_IMP
    \\ asm_simp_tac std_ss [realTheory.REAL_MUL_LID])
  \\ strip_tac
  \\ `2 * distance = 1` by (
    qspecl_then [`2 * distance`, `1`, `scale`] mp_tac realTheory.REAL_EQ_RMUL_IMP
    \\ asm_simp_tac std_ss [realTheory.REAL_MUL_LID])
  \\ `distance = 1 / 2` by (
    qpat_assum `2 * distance = 1` mp_tac
    \\ RealField.REAL_ARITH_TAC)
  \\ fs []
QED

Theorem round_nearest_even_scaled:
  !lower error scale (candidate : (52, 11) float).
    0 <= error /\ error < 1 /\ 0 < scale /\
    float_value candidate = Float (&(nearest_even_nat lower error) * scale) /\
    (candidate.Significand = 0w /\ candidate.Exponent <> 1w ==>
      &(nearest_even_nat lower error) <= &lower + error) /\
    ULP (candidate.Exponent, (:52)) = scale /\
    (word_lsb candidate.Significand <=> ODD (nearest_even_nat lower error)) /\
    ulp (:52 # 11) < 2 * ((&lower + error) * scale) /\
    (&lower + error) * scale < threshold (:52 # 11) ==>
    round roundTiesToEven ((&lower + error) * scale) = candidate
Proof
  qx_genl_tac [`lower`, `error`, `scale`, `candidate`]
  \\ strip_tac
  \\ `0 <= scale` by (irule realTheory.REAL_LT_IMP_LE \\ simp [])
  \\ `abs (&(nearest_even_nat lower error) * scale) =
         &(nearest_even_nat lower error) * scale /\
       abs ((&lower + error) * scale) = (&lower + error) * scale` by (
    simp_tac std_ss [realTheory.ABS_REFL]
    \\ conj_tac
    >- (irule realTheory.REAL_LE_MUL \\ simp [])
    \\ irule realTheory.REAL_LE_MUL
    \\ conj_tac >- (irule realTheory.REAL_LE_ADD \\ simp [])
    \\ simp [])
  \\ qspecl_then [`lower`, `error`, `scale`] mp_tac nearest_even_nat_scaled_error
  \\ impl_tac >- simp []
  \\ disch_then strip_assume_tac
  \\ `candidate.Significand = 0w /\ candidate.Exponent <> 1w ==>
       &(nearest_even_nat lower error) * scale <= (&lower + error) * scale` by (
    strip_tac
    \\ `&(nearest_even_nat lower error) <= &lower + error` by fs []
    \\ qspecl_then [`scale`, `&(nearest_even_nat lower error)`, `&lower + error`]
         mp_tac realTheory.REAL_LE_RMUL_IMP
    \\ asm_simp_tac std_ss [])
  \\ qspecl_then [`candidate`, `(&lower + error) * scale`,
                    `&(nearest_even_nat lower error) * scale`]
       match_mp_tac binary_ieeeTheory.round_roundTiesToEven
  \\ asm_simp_tac std_ss []
QED

Theorem normal_scale_above_ulp:
  !exponent lower error.
    0 < exponent /\ exponent < 2047 /\ 2 ** 52 <= lower /\ 0 <= error ==>
    ulp (:52 # 11) < 2 * ((&lower + error) * (2 pow exponent / 2 pow 1075))
Proof
  qx_genl_tac [`exponent`, `lower`, `error`]
  \\ strip_tac
  \\ `0 < 2 pow exponent / ((2 : real) pow 1075)` by
    simp [realTheory.REAL_LT_DIV, realTheory.REAL_POW_LT]
  \\ `ULP ((n2w exponent : word11), (:52)) = 2 pow exponent / 2 pow 1075` by (
    `exponent < 2048 /\ exponent <> 0` by decide_tac
    \\ simp [ULP_binary64])
  \\ irule realTheory.REAL_LET_TRANS
  \\ qexists_tac `2 pow exponent / ((2 : real) pow 1075)`
  \\ conj_tac
  >- (
    `1 < lower` by (
      qpat_assum `2 ** 52 <= lower` mp_tac
      \\ simp_tac std_ss [EVAL ``(2 : num) ** 52``]
      \\ decide_tac)
    \\ `1 < (&lower : real)` by simp []
    \\ `1 < 2 * (&lower + error)` by RealField.REAL_ASM_ARITH_TAC
    \\ qspecl_then [`1`, `2 * (&lower + error)`,
                      `2 pow exponent / ((2 : real) pow 1075)`]
         mp_tac realTheory.REAL_LT_RMUL_IMP
    \\ asm_simp_tac std_ss [realTheory.REAL_MUL_LID, realTheory.REAL_MUL_ASSOC])
  \\ qpat_assum `ULP ((n2w exponent : word11), (:52)) = _`
       (fn exponent_ulp => rewrite_tac [GSYM exponent_ulp])
  \\ irule binary_ieeeTheory.ulp_lt_ULP
QED

Theorem integer_unit_interval_exact:
  !lower rounded error.
    lower <= rounded /\ rounded <= SUC lower /\ 0 <= error /\ error < 1 ==>
    ((&rounded : real) = &lower + error <=> rounded = lower /\ error = 0)
Proof
  qx_genl_tac [`lower`, `rounded`, `error`]
  \\ strip_tac
  \\ Cases_on `rounded = lower`
  >- (
    asm_simp_tac std_ss []
    \\ RealField.REAL_ARITH_TAC)
  \\ `rounded = SUC lower` by decide_tac
  \\ asm_simp_tac std_ss [GSYM realTheory.REAL_OF_NUM_SUC]
  \\ RealField.REAL_ASM_ARITH_TAC
QED

Theorem round_nearest_even_negative_scaled:
  !lower error scale (candidate : (52, 11) float).
    0 <= error /\ error < 1 /\ 0 < scale /\
    float_value candidate = Float (-(&(nearest_even_nat lower error) * scale)) /\
    (candidate.Significand = 0w /\ candidate.Exponent <> 1w ==>
      &(nearest_even_nat lower error) <= &lower + error) /\
    ULP (candidate.Exponent, (:52)) = scale /\
    (word_lsb candidate.Significand <=> ODD (nearest_even_nat lower error)) /\
    ulp (:52 # 11) < 2 * ((&lower + error) * scale) /\
    (&lower + error) * scale < threshold (:52 # 11) ==>
    round roundTiesToEven (-((&lower + error) * scale)) = candidate
Proof
  qx_genl_tac [`lower`, `error`, `scale`, `candidate`]
  \\ strip_tac
  \\ `0 <= scale` by (irule realTheory.REAL_LT_IMP_LE \\ simp [])
  \\ `abs (&(nearest_even_nat lower error) * scale) =
         &(nearest_even_nat lower error) * scale /\
       abs ((&lower + error) * scale) = (&lower + error) * scale` by (
    simp_tac std_ss [realTheory.ABS_REFL]
    \\ conj_tac
    >- (irule realTheory.REAL_LE_MUL \\ simp [])
    \\ irule realTheory.REAL_LE_MUL
    \\ conj_tac >- (irule realTheory.REAL_LE_ADD \\ simp [])
    \\ simp [])
  \\ qspecl_then [`lower`, `error`, `scale`] mp_tac nearest_even_nat_scaled_error
  \\ impl_tac >- simp []
  \\ disch_then strip_assume_tac
  \\ `candidate.Significand = 0w /\ candidate.Exponent <> 1w ==>
       &(nearest_even_nat lower error) * scale <= (&lower + error) * scale` by (
    strip_tac
    \\ `&(nearest_even_nat lower error) <= &lower + error` by fs []
    \\ qspecl_then [`scale`, `&(nearest_even_nat lower error)`, `&lower + error`]
         mp_tac realTheory.REAL_LE_RMUL_IMP
    \\ asm_simp_tac std_ss [])
  \\ qspecl_then [`candidate`, `-((&lower + error) * scale)`,
                    `-(&(nearest_even_nat lower error) * scale)`]
       match_mp_tac binary_ieeeTheory.round_roundTiesToEven
  \\ asm_simp_tac std_ss [realTheory.ABS_NEG, realTheory.REAL_SUB_NEG2]
  \\ ONCE_REWRITE_TAC [realTheory.ABS_SUB]
  \\ asm_simp_tac std_ss []
QED

Theorem subnormal_float_round_nearest_signed:
  !negative lower error.
    0 <= error /\ error < 1 /\ &lower + error < &((2 : num) ** 52) ==>
    let magnitude = (&lower + error) * (1 / 2 pow 1074) in
    float_round roundTiesToEven negative
      (if negative then -magnitude else magnitude) =
      (<|Sign := if negative then 1w else 0w;
         Exponent := if nearest_even_nat lower error = 2 ** 52 then 1w else 0w;
         Significand := n2w (nearest_even_nat lower error)|> : (52, 11) float)
Proof
  qx_genl_tac [`negative`, `lower`, `error`]
  \\ strip_tac
  \\ simp_tac std_ss [LET_THM]
  \\ qmatch_goalsub_abbrev_tac `(&lower + error) * scale`
  \\ qmatch_goalsub_abbrev_tac
       `float_round _ _ (if negative then -magnitude else magnitude)`
  \\ qabbrev_tac `rounded = nearest_even_nat lower error`
  \\ qmatch_goalsub_abbrev_tac `float_round _ _ _ = candidate`
  \\ `0 < scale` by
    simp [Abbr `scale`, realTheory.real_div, realTheory.REAL_LT_INV_EQ,
          realTheory.REAL_POW_LT]
  \\ `lower < 2 ** 52` by (
    rewrite_tac [GSYM realTheory.REAL_LT]
    \\ RealField.REAL_ASM_ARITH_TAC)
  \\ `rounded <= 2 ** 52` by (
    qspecl_then [`lower`, `error`] mp_tac nearest_even_nat_bounds
    \\ qpat_assum `lower < 2 ** 52` mp_tac
    \\ simp_tac std_ss [Abbr `rounded`]
    \\ rpt (pop_assum kall_tac)
    \\ decide_tac)
  \\ Cases_on `1 / 2 < &lower + error`
  >- (
    `0 < rounded` by fs [Abbr `rounded`, nearest_even_nat_positive]
    \\ `float_is_finite candidate /\ ~float_is_zero candidate /\
         ULP (candidate.Exponent, (:52)) = scale /\
         ~(candidate.Significand = 0w /\ candidate.Exponent <> 1w)` by (
      qspecl_then [`negative`, `rounded`] mp_tac subnormal_candidate
      \\ simp [LET_THM, Abbr `candidate`, Abbr `scale`])
    \\ `float_value candidate = Float
          (if negative then -(&rounded * scale) else &rounded * scale)` by (
      qspecl_then [`negative`, `rounded`] mp_tac subnormal_rounding_value_signed
      \\ simp [Abbr `candidate`, Abbr `scale`, realTheory.real_div])
    \\ `(word_lsb candidate.Significand <=> ODD rounded)` by
      simp [Abbr `candidate`, wordsTheory.word_lsb_n2w]
    \\ `ulp (:52 # 11) < 2 * magnitude /\ magnitude < threshold (:52 # 11)` by (
      simp_tac (srw_ss())
        [Abbr `magnitude`, Abbr `scale`, binary_ieeeTheory.ulp_def,
         binary_ieeeTheory.ULP_def, binary_ieeeTheory.threshold_def,
         wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def,
         wordsTheory.UINT_MAX_def, wordsTheory.dimword_def]
      \\ qpat_assum `1 / 2 < &lower + error` mp_tac
      \\ qpat_assum `&lower + error < &((2 : num) ** 52)` mp_tac
      \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
      \\ RealField.REAL_ARITH_TAC)
    \\ qsuff_tac `round roundTiesToEven
          (if negative then -magnitude else magnitude) = candidate`
    >- (strip_tac \\ simp [binary_ieeeTheory.float_round_def])
    \\ fs [Abbr `rounded`, Abbr `magnitude`]
    \\ Cases_on `negative`
    >- (
      fs []
      \\ qspecl_then [`lower`, `error`, `scale`]
           match_mp_tac round_nearest_even_negative_scaled
      \\ asm_simp_tac std_ss []
      \\ strip_tac
      \\ fs [])
    \\ fs []
    \\ qspecl_then [`lower`, `error`, `scale`]
         match_mp_tac round_nearest_even_scaled
    \\ asm_simp_tac std_ss []
    \\ strip_tac
    \\ fs [])
  \\ `rounded = 0` by (
    qspecl_then [`lower`, `error`] mp_tac nearest_even_nat_positive
    \\ simp [Abbr `rounded`])
  \\ `0 <= magnitude` by (
    simp_tac std_ss [Abbr `magnitude`]
    \\ irule realTheory.REAL_LE_MUL
    \\ conj_tac
    >- (irule realTheory.REAL_LE_ADD \\ simp [])
    \\ irule realTheory.REAL_LT_IMP_LE
    \\ simp [])
  \\ `abs magnitude = magnitude` by simp [realTheory.ABS_REFL]
  \\ `2 * magnitude <= ulp (:52 # 11)` by (
    simp_tac (srw_ss())
      [Abbr `magnitude`, Abbr `scale`, binary_ieeeTheory.ulp_def,
       binary_ieeeTheory.ULP_def, wordsTheory.INT_MAX_def,
       wordsTheory.INT_MIN_def, wordsTheory.dimword_def]
    \\ qpat_assum `~(1 / 2 < &lower + error)` mp_tac
    \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
    \\ RealField.REAL_ARITH_TAC)
  \\ `candidate =
       (if negative then float_minus_zero (:52 # 11) else float_plus_zero (:52 # 11))` by (
    Cases_on `negative`
    \\ simp [Abbr `candidate`, binary_ieeeTheory.float_minus_zero_def,
             binary_ieeeTheory.float_plus_zero_def, binary_ieeeTheory.float_negate_def,
             EVAL ``(-1w : word1)``])
  \\ Cases_on `negative`
  \\ simp [binary_ieeeTheory.round_roundTiesToEven_is_minus_zero,
           binary_ieeeTheory.round_roundTiesToEven_is_plus_zero, realTheory.ABS_NEG]
QED

Theorem fp64_round_quantize_subnormal_nearest_signed:
  !negative exponent mantissa lower error.
    exponent < -1022 /\
    lower = Num (flr (mantissa / fp64_pow2 (-1022 - exponent) * 2 pow 52)) /\
    error = mantissa / fp64_pow2 (-1022 - exponent) * 2 pow 52 - &lower /\
    0 <= error /\ error < 1 /\ &lower + error < &((2 : num) ** 52) ==>
    fp64_round_quantize roundTiesToEven negative (exponent, mantissa) =
      (error <> 0, F, error <> 0,
       float_to_fp64 (float_round roundTiesToEven negative
         (if negative then -(mantissa * fp64_pow2 exponent)
          else mantissa * fp64_pow2 exponent)))
Proof
  qx_genl_tac [`negative`, `exponent`, `mantissa`, `lower`, `error`]
  \\ strip_tac
  \\ `(if exponent + 1023 < 0 then 0 else exponent + 1023) = (0 : int)` by
    intLib.ARITH_TAC
  \\ `lower < 2 ** 52` by (
    rewrite_tac [GSYM realTheory.REAL_LT]
    \\ RealField.REAL_ASM_ARITH_TAC)
  \\ `nearest_even_nat lower error <= 2 ** 52` by (
    qspecl_then [`lower`, `error`] mp_tac nearest_even_nat_bounds
    \\ decide_tac)
  \\ `nearest_even_nat lower error <> 2 ** 53` by (
    qpat_assum `nearest_even_nat lower error <= 2 ** 52` mp_tac
    \\ simp_tac std_ss [EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``]
    \\ rpt (pop_assum kall_tac)
    \\ decide_tac)
  \\ `&lower + error = mantissa / fp64_pow2 (-1022 - exponent) * 2 pow 52` by
    RealField.REAL_ASM_ARITH_TAC
  \\ `(&lower + error) * (1 / 2 pow 1074) = mantissa * fp64_pow2 exponent` by
    simp [fp64_subnormal_scale]
  \\ `float_round roundTiesToEven negative
        (if negative then -(mantissa * fp64_pow2 exponent)
         else mantissa * fp64_pow2 exponent) =
        (<|Sign := if negative then 1w else 0w;
           Exponent := if nearest_even_nat lower error = 2 ** 52 then 1w else 0w;
           Significand := n2w (nearest_even_nat lower error)|> : (52, 11) float)` by (
    qspecl_then [`negative`, `lower`, `error`] mp_tac subnormal_float_round_nearest_signed
    \\ asm_simp_tac std_ss [LET_THM])
  \\ `(1 / 2 < error \/ error = 1 / 2 /\ ODD lower) /\
       nearest_even_nat lower error = 2 ** 52 <=>
       nearest_even_nat lower error = 2 ** 52` by (
    Cases_on `1 / 2 < error \/ error = 1 / 2 /\ ODD lower`
    \\ asm_simp_tac std_ss [nearest_even_nat_def]
    \\ qpat_assum `lower = Num (flr _)`
         (fn lower_equation => rewrite_tac [GSYM lower_equation])
    \\ qpat_assum `lower < 2 ** 52` mp_tac
    \\ simp_tac std_ss [EVAL ``(2 : num) ** 52``]
    \\ rpt (pop_assum kall_tac)
    \\ decide_tac)
  \\ qpat_assum `(if exponent + 1023 < 0 then 0 else exponent + 1023) = 0`
       (fn biased_zero => simp_tac std_ss
         [fp64_round_quantize_def, LET_THM, binary_ieeeTheory.rounding_case_def,
          biased_zero])
  \\ qpat_assum `lower = Num (flr _)`
       (fn lower_equation => rewrite_tac [GSYM lower_equation])
  \\ qpat_assum `error = _ - &lower`
       (fn error_equation => rewrite_tac [GSYM error_equation])
  \\ rewrite_tac [GSYM nearest_even_nat_def]
  \\ qpat_assum `nearest_even_nat lower error <> 2 ** 53`
       (fn no_carry => simp_tac std_ss
         [REWRITE_RULE [EVAL ``(2 : num) ** 53``] no_carry])
  \\ qpat_assum `(_ /\ nearest_even_nat lower error = 2 ** 52) <=> _`
       (fn carry => rewrite_tac [REWRITE_RULE [EVAL ``(2 : num) ** 52``] carry])
  \\ Cases_on `nearest_even_nat lower error = 2 ** 52`
  \\ asm_simp_tac (srw_ss()) [EVAL ``(2 : num) ** 52``]
  \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
  \\ gvs [EVAL ``(2 : num) ** 52``, EVAL ``(2 : real) pow 52``,
          EVAL ``(2047 : int) <= 0``,
          EVAL ``(2047 : int) <= 1``]
QED

Theorem round_nearest_even_carry_signed:
  !negative lower error scale (candidate : (52, 11) float).
    0 <= error /\ error < 1 /\ 0 < scale /\
    float_value candidate = Float (if negative then -(&(nearest_even_nat lower error) * scale)
           else &(nearest_even_nat lower error) * scale) /\
    &lower + error < &(nearest_even_nat lower error) /\
    candidate.Significand = 0w /\ candidate.Exponent <> 1w /\
    ULP (candidate.Exponent, (:52)) = 2 * scale /\
    ulp (:52 # 11) < 2 * ((&lower + error) * scale) /\
    (&lower + error) * scale < threshold (:52 # 11) ==>
    round roundTiesToEven
      (if negative then -((&lower + error) * scale) else (&lower + error) * scale) = candidate
Proof
  qx_genl_tac [`negative`, `lower`, `error`, `scale`, `candidate`]
  \\ strip_tac
  \\ `0 <= scale` by (irule realTheory.REAL_LT_IMP_LE \\ simp [])
  \\ `abs (&(nearest_even_nat lower error) * scale) =
         &(nearest_even_nat lower error) * scale /\
       abs ((&lower + error) * scale) = (&lower + error) * scale` by (
    simp_tac std_ss [realTheory.ABS_REFL]
    \\ conj_tac
    >- (irule realTheory.REAL_LE_MUL \\ simp [])
    \\ irule realTheory.REAL_LE_MUL
    \\ conj_tac >- (irule realTheory.REAL_LE_ADD \\ simp [])
    \\ simp [])
  \\ `(&lower + error) * scale < &(nearest_even_nat lower error) * scale` by (
    irule realTheory.REAL_LT_RMUL_IMP
    \\ asm_simp_tac std_ss [])
  \\ `2 * abs (&(nearest_even_nat lower error) * scale -
         (&lower + error) * scale) <= scale` by (
    qspecl_then [`lower`, `error`, `scale`] mp_tac nearest_even_nat_scaled_error
    \\ asm_simp_tac std_ss [])
  \\ `4 * abs (&(nearest_even_nat lower error) * scale -
         (&lower + error) * scale) <= 2 * scale` by
    RealField.REAL_ASM_ARITH_TAC
  \\ qspecl_then [`candidate`, `if negative then -((&lower + error) * scale) else (&lower + error) * scale`,
                    `if negative then -(&(nearest_even_nat lower error) * scale)
                     else &(nearest_even_nat lower error) * scale`]
       match_mp_tac binary_ieeeTheory.round_roundTiesToEven0
  \\ asm_simp_tac std_ss []
  \\ Cases_on `negative`
  \\ asm_simp_tac std_ss
       [realTheory.ABS_NEG, realTheory.REAL_SUB_NEG2, realTheory.REAL_NOT_LE]
  \\ ONCE_REWRITE_TAC [realTheory.ABS_SUB]
  \\ asm_simp_tac std_ss []
QED

Theorem normal_float_round_nearest_signed:
  !negative exponent lower error.
    0 < exponent /\ exponent < 2047 /\ 2 ** 52 <= lower /\ lower < 2 ** 53 /\
    0 <= error /\ error < 1 /\
    (nearest_even_nat lower error = 2 ** 53 ==> exponent < 2046) /\
    (&lower + error) * (2 pow exponent / 2 pow 1075) < threshold (:52 # 11) ==>
    let rounded = nearest_even_nat lower error in
    let scale = 2 pow exponent / 2 pow 1075 in
    let magnitude = (&lower + error) * scale in
    float_round roundTiesToEven negative
      (if negative then -magnitude else magnitude) =
      (<|Sign := if negative then 1w else 0w;
         Exponent := if rounded = 2 ** 53 then n2w (exponent + 1)
                     else n2w exponent;
         Significand := if rounded = 2 ** 53 then 0w else n2w rounded|>
       : (52, 11) float)
Proof
  qx_genl_tac [`negative`, `exponent`, `lower`, `error`]
  \\ strip_tac
  \\ simp_tac std_ss [LET_THM]
  \\ qmatch_goalsub_abbrev_tac `(&lower + error) * scale`
  \\ qmatch_goalsub_abbrev_tac
       `float_round _ _ (if negative then -magnitude else magnitude)`
  \\ qabbrev_tac `rounded = nearest_even_nat lower error`
  \\ qmatch_goalsub_abbrev_tac `float_round _ _ _ = candidate`
  \\ `2 ** 52 <= rounded /\ rounded <= 2 ** 53` by (
    qspecl_then [`lower`, `error`] mp_tac nearest_even_nat_bounds
    \\ qpat_assum `2 ** 52 <= lower` mp_tac
    \\ qpat_assum `lower < 2 ** 53` mp_tac
    \\ simp_tac std_ss [Abbr `rounded`]
    \\ rpt (pop_assum kall_tac)
    \\ decide_tac)
  \\ `0 < scale` by
    simp [Abbr `scale`, realTheory.REAL_LT_DIV, realTheory.REAL_POW_LT]
  \\ `float_is_finite candidate /\ ~float_is_zero candidate /\
       ULP (candidate.Exponent, (:52)) =
         (if rounded = 2 ** 53 then 2 * scale else scale) /\
       (candidate.Significand = 0w ==> rounded = 2 ** 52 \/ rounded = 2 ** 53) /\
       (word_lsb candidate.Significand <=> ODD rounded)` by (
    qspecl_then [`negative`, `exponent`, `rounded`] mp_tac normal_candidate
    \\ simp [LET_THM, Abbr `candidate`, Abbr `scale`])
  \\ `float_value candidate = Float
        (if negative then -(&rounded * scale) else &rounded * scale)` by (
    qspecl_then [`negative`, `exponent`, `rounded`] mp_tac normal_rounding_value_signed
    \\ simp [Abbr `candidate`, Abbr `scale`])
  \\ `ulp (:52 # 11) < 2 * magnitude` by (
    simp_tac std_ss [Abbr `magnitude`, Abbr `scale`]
    \\ irule normal_scale_above_ulp
    \\ simp [])
  \\ `&((2 : num) ** 52) <= (&lower : real)` by (
    qpat_assum `2 ** 52 <= lower` mp_tac
    \\ simp [])
  \\ qsuff_tac `round roundTiesToEven
        (if negative then -magnitude else magnitude) = candidate`
  >- (strip_tac \\ simp [binary_ieeeTheory.float_round_def])
  \\ fs [Abbr `rounded`, Abbr `magnitude`]
  \\ Cases_on `nearest_even_nat lower error = 2 ** 53`
  >- (
    fs [EVAL ``(2 : num) ** 53``]
    \\ `exponent + 1 < 2048 /\ exponent + 1 <> 1` by decide_tac
    \\ `candidate.Significand = 0w /\ candidate.Exponent <> 1w` by
      simp [Abbr `candidate`, wordsTheory.n2w_11]
    \\ `&lower + 1 <= (&((2 : num) ** 53) : real)` by (
      qpat_assum `lower < _` mp_tac
      \\ simp_tac std_ss [realTheory.REAL_OF_NUM_SUC, realTheory.REAL_LE,
                            EVAL ``(2 : num) ** 53``]
      \\ decide_tac)
    \\ `&lower + error < &(nearest_even_nat lower error)` by (
      qpat_assum `nearest_even_nat lower error = _` SUBST1_TAC
      \\ qpat_assum `&lower + 1 <= &((2 : num) ** 53)` mp_tac
      \\ qpat_assum `error < 1` mp_tac
      \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
      \\ RealField.REAL_ARITH_TAC)
    \\ qspecl_then [`negative`, `lower`, `error`, `scale`]
         match_mp_tac round_nearest_even_carry_signed
    \\ asm_simp_tac std_ss [])
  \\ fs [EVAL ``(2 : num) ** 53``]
  \\ `candidate.Significand = 0w /\ candidate.Exponent <> 1w ==>
       &(nearest_even_nat lower error) <= &lower + error` by (
    strip_tac
    \\ `nearest_even_nat lower error = 2 ** 52` by fs [EVAL ``(2 : num) ** 52``]
    \\ `&(nearest_even_nat lower error) <= (&lower : real)` by (
      asm_simp_tac std_ss [realTheory.REAL_LE]
      \\ decide_tac)
    \\ RealField.REAL_ASM_ARITH_TAC)
  \\ Cases_on `negative`
  >- (
    fs []
    \\ qspecl_then [`lower`, `error`, `scale`]
         match_mp_tac round_nearest_even_negative_scaled
    \\ asm_simp_tac std_ss [])
  \\ fs []
  \\ qspecl_then [`lower`, `error`, `scale`]
       match_mp_tac round_nearest_even_scaled
  \\ asm_simp_tac std_ss []
QED

Theorem fp64_round_quantize_normal_nearest_signed:
  !negative exponent mantissa lower error.
    -1022 <= exponent /\ exponent < 1023 /\
    lower = Num (flr (mantissa * 2 pow 52)) /\
    error = mantissa * 2 pow 52 - &lower /\
    2 ** 52 <= lower /\ lower < 2 ** 53 /\ 0 <= error /\ error < 1 ==>
    fp64_round_quantize roundTiesToEven negative (exponent, mantissa) =
      (F, F, error <> 0,
       float_to_fp64 (float_round roundTiesToEven negative
         (if negative then -(mantissa * fp64_pow2 exponent)
          else mantissa * fp64_pow2 exponent)))
Proof
  qx_genl_tac [`negative`, `exponent`, `mantissa`, `lower`, `error`]
  \\ strip_tac
  \\ qabbrev_tac `biased = Num (exponent + 1023)`
  \\ `0 < biased /\ (&biased : int) = exponent + 1023 /\
       Num (exponent + 1023 + 1) = biased + 1 /\
       (if exponent + 1023 < 0 then 0 else exponent + 1023) = exponent + 1023` by (
    qspec_then `exponent` mp_tac fp64_normal_bias
    \\ simp [Abbr `biased`])
  \\ `biased < 2046` by (
    rewrite_tac [GSYM integerTheory.INT_LT]
    \\ asm_simp_tac std_ss []
    \\ intLib.ARITH_TAC)
  \\ `exponent + 1023 <> 0 /\ ~(exponent < -1022) /\
       ~(2047 <= exponent + 1023) /\ ~(2047 <= exponent + 1023 + 1)` by
    intLib.ARITH_TAC
  \\ `biased < 2047` by decide_tac
  \\ `&lower + 1 <= (&((2 : num) ** 53) : real)` by (
    qpat_assum `lower < 2 ** 53` mp_tac
    \\ simp_tac std_ss [realTheory.REAL_OF_NUM_SUC, realTheory.REAL_LE,
                          EVAL ``(2 : num) ** 53``]
    \\ decide_tac)
  \\ `0 <= &lower + error /\ &lower + error < &((2 : num) ** 53)` by (
    `0 <= (&lower : real)` by simp []
    \\ RealField.REAL_ASM_ARITH_TAC)
  \\ `&lower + error = mantissa * 2 pow 52` by RealField.REAL_ASM_ARITH_TAC
  \\ `(&lower + error) * (2 pow biased / 2 pow 1075) =
       mantissa * fp64_pow2 exponent` by
    simp [Abbr `biased`, fp64_normal_scale]
  \\ `(&lower + error) * (2 pow biased / 2 pow 1075) < threshold (:52 # 11)` by (
    qspecl_then [`(&lower + error) * (2 pow biased / 2 pow 1075)`,
                  `largest (:52 # 11)`, `threshold (:52 # 11)`]
         match_mp_tac realTheory.REAL_LT_TRANS
    \\ conj_tac
    >- (irule normal_scale_below_largest \\ simp [])
    \\ simp [binary_ieeeTheory.largest_lt_threshold])
  \\ `float_round roundTiesToEven negative
        (if negative then -(mantissa * fp64_pow2 exponent)
         else mantissa * fp64_pow2 exponent) =
       (<|Sign := if negative then 1w else 0w;
          Exponent := if nearest_even_nat lower error = 2 ** 53 then n2w (biased + 1)
                      else n2w biased;
          Significand := if nearest_even_nat lower error = 2 ** 53 then 0w
                         else n2w (nearest_even_nat lower error)|> : (52, 11) float)` by (
    qspecl_then [`negative`, `biased`, `lower`, `error`]
         mp_tac normal_float_round_nearest_signed
    \\ asm_simp_tac std_ss [LET_THM])
  \\ `~((1 / 2 < error \/ error = 1 / 2 /\ ODD lower) /\
         nearest_even_nat lower error = 2 ** 52)` by (
    qspecl_then [`lower`, `1 / 2 < error \/ error = 1 / 2 /\ ODD lower`,
                  `(2 : num) ** 52`] mp_tac round_increment_not_lower
    \\ asm_simp_tac std_ss [GSYM nearest_even_nat_def])
  \\ `(1 / 2 < error \/ error = 1 / 2 /\ ODD lower) /\
       nearest_even_nat lower error = 2 ** 53 <=>
       nearest_even_nat lower error = 2 ** 53` by (
    qspecl_then [`lower`, `1 / 2 < error \/ error = 1 / 2 /\ ODD lower`,
                  `(2 : num) ** 53`] mp_tac round_increment_reaches_upper
    \\ asm_simp_tac std_ss [GSYM nearest_even_nat_def])
  \\ `(n2w ((2 : num) ** 52) : 52 word) = 0w` by
    simp [wordsTheory.n2w_11, wordsTheory.dimword_def]
  \\ qpat_assum `(if exponent + 1023 < 0 then 0 else exponent + 1023) = _`
       (fn normal_bias => simp_tac std_ss
         [fp64_round_quantize_def, LET_THM, binary_ieeeTheory.rounding_case_def,
          normal_bias])
  \\ qpat_assum `exponent + 1023 <> 0`
       (fn normal_nonzero => simp_tac std_ss [normal_nonzero])
  \\ qpat_assum `lower = Num (flr _)`
       (fn lower_equation => rewrite_tac [GSYM lower_equation])
  \\ qpat_assum `error = _ - &lower`
       (fn error_equation => rewrite_tac [GSYM error_equation])
  \\ rewrite_tac [GSYM nearest_even_nat_def]
  \\ `SUC lower <> 2 ** 52` by decide_tac
  \\ qpat_assum `~(_ /\ nearest_even_nat lower error = 2 ** 52)`
       (fn not_lower => simp_tac std_ss
         [REWRITE_RULE [EVAL ``(2 : num) ** 52``] not_lower])
  \\ qpat_assum `SUC lower <> 2 ** 52`
       (fn increment_not_lower => simp_tac std_ss
         [REWRITE_RULE [EVAL ``(2 : num) ** 52``] increment_not_lower])
  \\ qpat_assum `(_ /\ nearest_even_nat lower error = 2 ** 53) <=> _`
       (fn carry => rewrite_tac [REWRITE_RULE [EVAL ``(2 : num) ** 53``] carry])
  \\ qpat_assum `float_round roundTiesToEven negative _ = _`
       SUBST1_TAC
  \\ Cases_on `nearest_even_nat lower error = 2 ** 53`
  \\ asm_simp_tac std_ss [EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``]
  \\ qpat_assum `(n2w ((2 : num) ** 52) : 52 word) = 0w`
       (fn significand_zero => rewrite_tac
         [REWRITE_RULE [EVAL ``(2 : num) ** 52``] significand_zero])
  \\ gvs [Abbr `biased`, EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``,
          EVAL ``(2 : real) pow 52``]
QED

Theorem nearest_even_nat_below_even_boundary:
  !lower error boundary.
    0 <= error /\ error < 1 /\ EVEN boundary /\
    nearest_even_nat lower error < boundary ==>
    &lower + error < &boundary - 1 / 2
Proof
  qx_genl_tac [`lower`, `error`, `boundary`]
  \\ strip_tac
  \\ qspecl_then [`lower`, `error`] mp_tac nearest_even_nat_error
  \\ impl_tac >- simp []
  \\ disch_then strip_assume_tac
  \\ `&(nearest_even_nat lower error) + 1 <= (&boundary : real)` by (
    simp_tac std_ss [realTheory.REAL_OF_NUM_SUC, realTheory.REAL_LE]
    \\ decide_tac)
  \\ `-(1 / 2) <= &(nearest_even_nat lower error) - (&lower + error) /\
       &(nearest_even_nat lower error) - (&lower + error) <= 1 / 2` by
    fs [realTheory.ABS_BOUNDS]
  \\ CCONTR_TAC
  \\ `&(nearest_even_nat lower error) + 1 = (&boundary : real) /\
       &(nearest_even_nat lower error) - (&lower + error) = -(1 / 2)` by
    RealField.REAL_ASM_ARITH_TAC
  \\ `SUC (nearest_even_nat lower error) = boundary` by (
    qpat_assum `&(nearest_even_nat lower error) + 1 = (&boundary : real)` mp_tac
    \\ simp_tac std_ss [realTheory.REAL_OF_NUM_SUC, realTheory.REAL_INJ])
  \\ `ODD (nearest_even_nat lower error)` by (
    qpat_assum `EVEN boundary` mp_tac
    \\ qpat_assum `SUC (nearest_even_nat lower error) = boundary`
         (fn adjacent => rewrite_tac [GSYM adjacent])
    \\ simp_tac std_ss [arithmeticTheory.EVEN, arithmeticTheory.EVEN_ODD])
  \\ `abs (&(nearest_even_nat lower error) - (&lower + error)) = 1 / 2` by (
    qpat_assum `&(nearest_even_nat lower error) - (&lower + error) = _`
      SUBST1_TAC
    \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV)
  \\ fs []
QED

Theorem nearest_even_nat_reaches_even_boundary:
  !lower error boundary.
    0 <= error /\ error < 1 /\ EVEN boundary /\ lower < boundary ==>
    (nearest_even_nat lower error = boundary <=>
     &boundary - 1 / 2 <= &lower + error)
Proof
  qx_genl_tac [`lower`, `error`, `boundary`]
  \\ strip_tac
  \\ `nearest_even_nat lower error <= boundary` by (
    qspecl_then [`lower`, `error`] mp_tac nearest_even_nat_bounds
    \\ decide_tac)
  \\ qspecl_then [`lower`, `error`] mp_tac nearest_even_nat_error
  \\ impl_tac >- simp []
  \\ disch_then strip_assume_tac
  \\ eq_tac
  >- (
    strip_tac \\ gvs [realTheory.ABS_BOUNDS]
    \\ RealField.REAL_ASM_ARITH_TAC)
  \\ strip_tac \\ CCONTR_TAC
  \\ `nearest_even_nat lower error < boundary` by decide_tac
  \\ qspecl_then [`lower`, `error`, `boundary`]
       mp_tac nearest_even_nat_below_even_boundary
  \\ impl_tac >- simp []
  \\ RealField.REAL_ASM_ARITH_TAC
QED

Theorem fp64_threshold_top_scale:
  threshold (:52 # 11) =
    (&((2 : num) ** 53) - 1 / 2) * (2 pow 2046 / 2 pow 1075)
Proof
  simp [binary_ieeeTheory.threshold_def, wordsTheory.UINT_MAX_def,
        wordsTheory.INT_MAX_def, wordsTheory.dimword_def]
  \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
QED

Theorem float_round_nearest_infinite_signed:
  !negative magnitude.
    threshold (:52 # 11) <= magnitude ==>
    float_round roundTiesToEven negative
      (if negative then -magnitude else magnitude) =
      (<|Sign := if negative then 1w else 0w;
         Exponent := 2047w; Significand := 0w|> : (52, 11) float)
Proof
  qx_genl_tac [`negative`, `magnitude`] \\ strip_tac
  \\ Cases_on `negative`
  >- (
    `(round roundTiesToEven (-magnitude) : (52,11) float) =
     float_minus_infinity (:52 # 11)` by (
      irule binary_ieeeTheory.round_roundTiesToEven_minus_infinity
      \\ RealField.REAL_ASM_ARITH_TAC)
    \\ `float_round roundTiesToEven T (-magnitude) =
         float_minus_infinity (:52 # 11)` by (
      irule binary_ieeeTheory.float_round_minus_infinity \\ simp [])
    \\ simp [binary_ieeeTheory.float_minus_infinity, wordsTheory.UINT_MAX_def,
             wordsTheory.dimword_def, EVAL ``(-1w : word11)``])
  \\ `(round roundTiesToEven magnitude : (52,11) float) =
   float_plus_infinity (:52 # 11)` by (
    irule binary_ieeeTheory.round_roundTiesToEven_plus_infinity \\ simp [])
  \\ `float_round roundTiesToEven F magnitude =
       float_plus_infinity (:52 # 11)` by (
    irule binary_ieeeTheory.float_round_plus_infinity \\ simp [])
  \\ simp [binary_ieeeTheory.float_plus_infinity_def, wordsTheory.UINT_MAX_def,
           wordsTheory.dimword_def, EVAL ``(-1w : word11)``]
QED

Theorem normal_float_round_nearest_top_signed:
  !negative lower error.
    2 ** 52 <= lower /\ lower < 2 ** 53 /\
    0 <= error /\ error < 1 ==>
    let rounded = nearest_even_nat lower error in
    let magnitude = (&lower + error) * (2 pow 2046 / 2 pow 1075) in
    float_round roundTiesToEven negative
      (if negative then -magnitude else magnitude) =
      (<|Sign := if negative then 1w else 0w;
         Exponent := if rounded = 2 ** 53 then 2047w else 2046w;
         Significand := if rounded = 2 ** 53 then 0w else n2w rounded|>
       : (52, 11) float)
Proof
  qx_genl_tac [`negative`, `lower`, `error`] \\ strip_tac
  \\ simp_tac std_ss [LET_THM]
  \\ qabbrev_tac `scale = (2 : real) pow 2046 / 2 pow 1075`
  \\ `0 < scale` by
    simp [Abbr `scale`, realTheory.REAL_LT_DIV, realTheory.REAL_POW_LT]
  \\ `nearest_even_nat lower error = 2 ** 53 <=>
       threshold (:52 # 11) <= (&lower + error) * scale` by (
    `EVEN ((2 : num) ** 53)` by simp []
    \\ qspecl_then [`lower`, `error`, `(2 : num) ** 53`]
         mp_tac nearest_even_nat_reaches_even_boundary
    \\ asm_simp_tac std_ss
         [fp64_threshold_top_scale, Abbr `scale`, realTheory.REAL_LE_RMUL,
          realTheory.REAL_LT_DIV, realTheory.REAL_POW_LT])
  \\ Cases_on `nearest_even_nat lower error = 2 ** 53`
  >- (
    gvs [EVAL ``(2 : num) ** 53``]
    \\ irule float_round_nearest_infinite_signed \\ simp [])
  \\ gvs [realTheory.REAL_NOT_LE, EVAL ``(2 : num) ** 53``]
  \\ qspecl_then [`negative`, `2046`, `lower`, `error`]
       mp_tac normal_float_round_nearest_signed
  \\ simp [LET_THM, Abbr `scale`]
QED

Theorem fp64_round_quantize_top_nearest_signed:
  !negative mantissa lower error.
    lower = Num (flr (mantissa * 2 pow 52)) /\
    error = mantissa * 2 pow 52 - &lower /\
    2 ** 52 <= lower /\ lower < 2 ** 53 /\ 0 <= error /\ error < 1 ==>
    fp64_round_quantize roundTiesToEven negative (1023, mantissa) =
      (F, nearest_even_nat lower error = 2 ** 53,
       error <> 0 \/ nearest_even_nat lower error = 2 ** 53,
       float_to_fp64 (float_round roundTiesToEven negative
         (if negative then -(mantissa * fp64_pow2 1023)
          else mantissa * fp64_pow2 1023)))
Proof
  qx_genl_tac [`negative`, `mantissa`, `lower`, `error`] \\ strip_tac
  \\ `&lower + error = mantissa * 2 pow 52` by RealField.REAL_ASM_ARITH_TAC
  \\ `(&lower + error) * (2 pow 2046 / 2 pow 1075) =
       mantissa * fp64_pow2 1023` by (
    qspecl_then [`1023`, `mantissa`] mp_tac fp64_normal_scale \\ simp [])
  \\ `float_round roundTiesToEven negative
        (if negative then -(mantissa * fp64_pow2 1023)
         else mantissa * fp64_pow2 1023) =
       (<|Sign := if negative then 1w else 0w;
          Exponent := if nearest_even_nat lower error = 2 ** 53
                      then 2047w else 2046w;
          Significand := if nearest_even_nat lower error = 2 ** 53
                         then 0w else n2w (nearest_even_nat lower error)|>
        : (52, 11) float)` by (
    qspecl_then [`negative`, `lower`, `error`]
         mp_tac normal_float_round_nearest_top_signed
    \\ asm_simp_tac std_ss [LET_THM])
  \\ `~((1 / 2 < error \/ error = 1 / 2 /\ ODD lower) /\
         nearest_even_nat lower error = 2 ** 52)` by (
    qspecl_then [`lower`, `1 / 2 < error \/ error = 1 / 2 /\ ODD lower`,
                  `(2 : num) ** 52`] mp_tac round_increment_not_lower
    \\ asm_simp_tac std_ss [GSYM nearest_even_nat_def])
  \\ `(1 / 2 < error \/ error = 1 / 2 /\ ODD lower) /\
       nearest_even_nat lower error = 2 ** 53 <=>
       nearest_even_nat lower error = 2 ** 53` by (
    qspecl_then [`lower`, `1 / 2 < error \/ error = 1 / 2 /\ ODD lower`,
                  `(2 : num) ** 53`] mp_tac round_increment_reaches_upper
    \\ asm_simp_tac std_ss [GSYM nearest_even_nat_def])
  \\ simp_tac (srw_ss()) [fp64_round_quantize_def, LET_THM]
  \\ qpat_assum `lower = Num (flr _)`
       (fn lower_equation => rewrite_tac [GSYM lower_equation])
  \\ qpat_assum `error = _ - &lower`
       (fn error_equation => rewrite_tac [GSYM error_equation])
  \\ rewrite_tac [GSYM nearest_even_nat_def]
  \\ `SUC lower <> 2 ** 52` by decide_tac
  \\ qpat_assum `~(_ /\ nearest_even_nat lower error = 2 ** 52)`
       (fn not_lower => simp_tac std_ss
         [REWRITE_RULE [EVAL ``(2 : num) ** 52``] not_lower])
  \\ qpat_assum `SUC lower <> 2 ** 52`
       (fn increment_not_lower => simp_tac std_ss
         [REWRITE_RULE [EVAL ``(2 : num) ** 52``] increment_not_lower])
  \\ qpat_assum `(_ /\ nearest_even_nat lower error = 2 ** 53) <=> _`
       (fn carry => rewrite_tac [REWRITE_RULE [EVAL ``(2 : num) ** 53``] carry])
  \\ qpat_assum `float_round roundTiesToEven negative _ = _`
       SUBST1_TAC
  \\ `(mantissa * 2 pow 52 = &lower) <=> error = 0` by (
    qpat_assum `error = _ - &lower` mp_tac
    \\ rpt (pop_assum kall_tac) \\ RealField.REAL_ASM_ARITH_TAC)
  \\ `nearest_even_nat lower 0 = lower` by (
    rpt (pop_assum kall_tac) \\ simp_tac std_ss [nearest_even_nat_def]
    \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV)
  \\ qpat_x_assum `lower = Num (flr _)` kall_tac
  \\ qpat_x_assum `error = _ - &lower` kall_tac
  \\ qpat_x_assum `&lower + error = _` kall_tac
  \\ qpat_x_assum `(_ + error) * _ = _` kall_tac
  \\ qpat_x_assum `float_round _ _ _ = _` kall_tac
  \\ qpat_x_assum `~(_ /\ nearest_even_nat lower error = 2 ** 52)` kall_tac
  \\ qpat_x_assum `(_ /\ nearest_even_nat lower error = 2 ** 53) <=> _` kall_tac
  \\ qpat_x_assum `SUC lower <> _` kall_tac
  \\ Cases_on `nearest_even_nat lower error = 2 ** 53`
  \\ gvs [EVAL ``(2 : num) ** 53``, LET_THM]
  \\ CCONTR_TAC \\ gvs []
QED

Theorem fp64_threshold_below_power_1024:
  threshold (:52 # 11) < fp64_pow2 1024
Proof
  simp [fp64_threshold_top_scale, fp64_pow2_def]
  \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
QED

Theorem normalized_float_round_nearest_large_signed:
  !negative exponent mantissa.
    1024 <= exponent /\ 1 <= mantissa ==>
    float_round roundTiesToEven negative
      (if negative then -(mantissa * fp64_pow2 exponent)
       else mantissa * fp64_pow2 exponent) =
      (<|Sign := if negative then 1w else 0w;
         Exponent := 2047w; Significand := 0w|> : (52, 11) float)
Proof
  qx_genl_tac [`negative`, `exponent`, `mantissa`] \\ strip_tac
  \\ `0 <= fp64_pow2 exponent` by
    metis_tac [fp64_pow2_positive, realTheory.REAL_LT_IMP_LE]
  \\ `fp64_pow2 1024 <= fp64_pow2 exponent` by
    (irule fp64_pow2_monotone \\ simp [])
  \\ `fp64_pow2 exponent <= mantissa * fp64_pow2 exponent` by (
    qspecl_then [`fp64_pow2 exponent`, `1`, `mantissa`]
         mp_tac realTheory.REAL_LE_RMUL1 \\ simp [])
  \\ irule float_round_nearest_infinite_signed
  \\ assume_tac fp64_threshold_below_power_1024
  \\ RealField.REAL_ASM_ARITH_TAC
QED

Theorem fp64_round_quantize_large_nearest_signed:
  !negative exponent mantissa lower.
    1024 <= exponent /\ 1 <= mantissa /\
    lower = Num (flr (mantissa * 2 pow 52)) /\ 2 ** 52 <= lower ==>
    fp64_round_quantize roundTiesToEven negative (exponent, mantissa) =
      (F, T, T, float_to_fp64 (float_round roundTiesToEven negative
         (if negative then -(mantissa * fp64_pow2 exponent)
          else mantissa * fp64_pow2 exponent)))
Proof
  qx_genl_tac [`negative`, `exponent`, `mantissa`, `lower`] \\ strip_tac
  \\ `~(exponent + 1023 < 0) /\ exponent + 1023 <> 0 /\
       ~(exponent < -1022) /\ 2047 <= exponent + 1023 /\
       2047 <= exponent + 1023 + 1` by intLib.ARITH_TAC
  \\ `SUC lower <> 2 ** 52` by decide_tac
  \\ `float_round roundTiesToEven negative
        (if negative then -(mantissa * fp64_pow2 exponent)
         else mantissa * fp64_pow2 exponent) =
       (<|Sign := if negative then 1w else 0w;
          Exponent := 2047w; Significand := 0w|> : (52,11) float)` by (
    irule normalized_float_round_nearest_large_signed \\ simp [])
  \\ asm_simp_tac std_ss [fp64_round_quantize_def, LET_THM,
                            binary_ieeeTheory.rounding_case_def]
  \\ qpat_assum `lower = Num (flr _)`
       (fn lower_equation => rewrite_tac [GSYM lower_equation])
  \\ qabbrev_tac `error = mantissa * 2 pow 52 - &lower`
  \\ qpat_x_assum `lower = Num (flr _)` kall_tac
  \\ RULE_ASSUM_TAC (REWRITE_RULE
       [EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``])
  \\ Cases_on `1 / 2 < error \/ error = 1 / 2 /\ ODD lower`
  \\ asm_simp_tac std_ss []
  \\ Cases_on `SUC lower = 2 ** 53`
  \\ asm_simp_tac std_ss [EVAL ``(2 : num) ** 53``]
  \\ fs [EVAL ``(2 : num) ** 53``]
QED

Theorem nearest_even_nat_zero:
  !lower. nearest_even_nat lower 0 = lower
Proof
  gen_tac \\ simp_tac std_ss [nearest_even_nat_def]
  \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
QED

Theorem nearest_even_nat_exact:
  !lower error.
    0 <= error /\ error < 1 ==>
    (&(nearest_even_nat lower error) = &lower + error <=> error = 0)
Proof
  qx_genl_tac [`lower`, `error`] \\ strip_tac
  \\ qspecl_then [`lower`, `nearest_even_nat lower error`, `error`]
       mp_tac integer_unit_interval_exact
  \\ simp [nearest_even_nat_bounds]
  \\ Cases_on `error = 0`
  \\ simp [nearest_even_nat_zero]
QED

Theorem nearest_even_signed_precision:
  !negative lower error scale (candidate : (52, 11) float).
    0 <= error /\ error < 1 /\ 0 < scale /\
    float_value candidate =
      Float (if negative then -(&(nearest_even_nat lower error) * scale)
             else &(nearest_even_nat lower error) * scale) ==>
    (float_value candidate =
      Float (if negative then -((&lower + error) * scale)
             else (&lower + error) * scale) <=> error = 0)
Proof
  qx_genl_tac [`negative`, `lower`, `error`, `scale`, `candidate`]
  \\ strip_tac
  \\ `scale <> 0` by RealField.REAL_ASM_ARITH_TAC
  \\ Cases_on `negative`
  \\ gvs [realTheory.REAL_EQ_RMUL, nearest_even_nat_exact]
QED

Theorem fp64_round_quantize_subnormal_nearest_flags:
  !negative exponent mantissa.
    exponent < -1022 /\ 1 <= mantissa /\ mantissa < 2 ==>
    let source = if negative then -(mantissa * fp64_pow2 exponent)
                 else mantissa * fp64_pow2 exponent in
    let (flags, result) =
      (float_round_with_flags roundTiesToEven negative source :
         flags # (52,11) float) in
    fp64_round_quantize roundTiesToEven negative (exponent, mantissa) =
      (flags.Underflow_BeforeRounding, flags.Overflow, flags.Precision,
       float_to_fp64 result)
Proof
  qx_genl_tac [`negative`, `exponent`, `mantissa`] \\ strip_tac
  \\ qspecl_then [`exponent`, `mantissa`] mp_tac fp64_subnormal_scaled_floor
  \\ impl_tac >- simp []
  \\ simp_tac std_ss [LET_THM] \\ strip_tac
  \\ qabbrev_tac `scaled = mantissa / fp64_pow2 (-1022 - exponent) * 2 pow 52`
  \\ qabbrev_tac `lower = Num (flr scaled)`
  \\ qabbrev_tac `error = scaled - &lower`
  \\ qabbrev_tac `source = if negative then -(mantissa * fp64_pow2 exponent)
                             else mantissa * fp64_pow2 exponent`
  \\ qabbrev_tac
       `result = (float_round roundTiesToEven negative source : (52,11) float)`
  \\ `&lower + error = scaled` by
    (simp_tac std_ss [Abbr `error`] \\ RealField.REAL_ARITH_TAC)
  \\ `scaled * (1 / 2 pow 1074) = mantissa * fp64_pow2 exponent` by
    simp [Abbr `scaled`, fp64_subnormal_scale]
  \\ `result =
       (<|Sign := if negative then 1w else 0w;
          Exponent := if nearest_even_nat lower error = 2 ** 52 then 1w else 0w;
          Significand := n2w (nearest_even_nat lower error)|> : (52,11) float)` by (
    qspecl_then [`negative`, `lower`, `error`]
         mp_tac subnormal_float_round_nearest_signed
    \\ asm_simp_tac std_ss
         [LET_THM, Abbr `source`, Abbr `result`, EVAL ``(2 : num) ** 52``])
  \\ `nearest_even_nat lower error <= 2 ** 52` by (
    qspecl_then [`lower`, `error`] mp_tac nearest_even_nat_bounds
    \\ simp_tac std_ss [EVAL ``(2 : num) ** 52``]
    \\ decide_tac)
  \\ `float_value result =
       Float (if negative then -(&(nearest_even_nat lower error) * (1 / 2 pow 1074))
              else &(nearest_even_nat lower error) * (1 / 2 pow 1074))` by (
    qspecl_then [`negative`, `nearest_even_nat lower error`]
         mp_tac subnormal_rounding_value_signed
    \\ asm_simp_tac std_ss [realTheory.real_div, realTheory.REAL_MUL_LID])
  \\ `(float_value result = Float source) <=> error = 0` by (
    qspecl_then [`negative`, `lower`, `error`, `1 / 2 pow 1074`, `result`]
         mp_tac nearest_even_signed_precision
    \\ `0 < (1 : real) / 2 pow 1074` by
      simp [realTheory.REAL_LT_DIV, realTheory.REAL_POW_LT]
    \\ asm_simp_tac std_ss [Abbr `source`])
  \\ `fp64_round_quantize roundTiesToEven negative (exponent,mantissa) =
       (error <> 0, F, error <> 0, float_to_fp64 result)` by (
    qspecl_then [`negative`, `exponent`, `mantissa`, `lower`, `error`]
         mp_tac fp64_round_quantize_subnormal_nearest_signed
    \\ impl_tac
    >- fs [Abbr `lower`, Abbr `scaled`, Abbr `error`, EVAL ``(2 : num) ** 52``]
    \\ asm_simp_tac std_ss [Abbr `result`, Abbr `source`])
  \\ `abs source < 2 / 2 pow (INT_MAX (:11)) /\
         ~(2 pow (INT_MIN (:11)) <= abs source)` by (
    `~(1024 <= exponent)` by intLib.ARITH_TAC
    \\ qspecl_then [`negative`, `exponent`, `mantissa`] mp_tac normalized_fp64_source
    \\ asm_simp_tac std_ss [LET_THM, Abbr `source`])
  \\ qunabbrev_tac `result`
  \\ asm_simp_tac (srw_ss())
       [binary_ieeeTheory.float_round_with_flags_def, LET_THM,
        binary_ieeeTheory.float_is_infinite_def]
  \\ RULE_ASSUM_TAC (REWRITE_RULE
       [EVAL ``words$INT_MAX (:11)``, EVAL ``words$INT_MIN (:11)``])
  \\ asm_simp_tac std_ss []
QED

Theorem normal_float_value_nearest_signed:
  !negative exponent lower error.
    0 < exponent /\ exponent < 2047 /\
    2 ** 52 <= lower /\ lower < 2 ** 53 /\ 0 <= error /\ error < 1 /\
    (nearest_even_nat lower error = 2 ** 53 ==> exponent < 2046) /\
    (&lower + error) * (2 pow exponent / 2 pow 1075) < threshold (:52 # 11) ==>
    let magnitude = (&lower + error) * (2 pow exponent / 2 pow 1075) in
    float_value (float_round roundTiesToEven negative
      (if negative then -magnitude else magnitude) : (52,11) float) =
    Float (if negative then
             -(&(nearest_even_nat lower error) * (2 pow exponent / 2 pow 1075))
           else &(nearest_even_nat lower error) * (2 pow exponent / 2 pow 1075))
Proof
  qx_genl_tac [`negative`, `exponent`, `lower`, `error`] \\ strip_tac
  \\ `2 ** 52 <= nearest_even_nat lower error /\
       nearest_even_nat lower error <= 2 ** 53` by (
    qspecl_then [`lower`, `error`] mp_tac nearest_even_nat_bounds
    \\ decide_tac)
  \\ qspecl_then [`negative`, `exponent`, `lower`, `error`]
       mp_tac normal_float_round_nearest_signed
  \\ impl_tac >- simp []
  \\ simp_tac std_ss [LET_THM] \\ strip_tac
  \\ qspecl_then [`negative`, `exponent`, `nearest_even_nat lower error`]
       mp_tac normal_rounding_value_signed
  \\ asm_simp_tac std_ss []
QED

Theorem fp64_power_1023_below_threshold:
  fp64_pow2 1023 < threshold (:52 # 11)
Proof
  simp [fp64_threshold_top_scale, fp64_pow2_def]
  \\ CONV_TAC RealField.REAL_RAT_REDUCE_CONV
QED

Theorem fp64_round_quantize_normal_nearest_flags:
  !negative exponent mantissa.
    -1022 <= exponent /\ exponent < 1023 /\
    1 <= mantissa /\ mantissa < 2 ==>
    let source = if negative then -(mantissa * fp64_pow2 exponent)
                 else mantissa * fp64_pow2 exponent in
    let (flags, result) =
      (float_round_with_flags roundTiesToEven negative source :
         flags # (52,11) float) in
    fp64_round_quantize roundTiesToEven negative (exponent, mantissa) =
      (flags.Underflow_BeforeRounding, flags.Overflow, flags.Precision,
       float_to_fp64 result)
Proof
  qx_genl_tac [`negative`, `exponent`, `mantissa`] \\ strip_tac
  \\ qspec_then `mantissa` mp_tac fp64_normal_scaled_floor
  \\ impl_tac >- simp []
  \\ simp_tac std_ss [LET_THM] \\ strip_tac
  \\ qabbrev_tac `lower = Num (flr (mantissa * 2 pow 52))`
  \\ qabbrev_tac `error = mantissa * 2 pow 52 - &lower`
  \\ qabbrev_tac `biased = Num (exponent + 1023)`
  \\ `0 < biased /\ (&biased : int) = exponent + 1023` by (
    qspec_then `exponent` mp_tac fp64_normal_bias
    \\ asm_simp_tac std_ss [Abbr `biased`])
  \\ `biased < 2046` by (
    rewrite_tac [GSYM integerTheory.INT_LT]
    \\ asm_simp_tac std_ss [] \\ intLib.ARITH_TAC)
  \\ `biased < 2047` by decide_tac
  \\ qabbrev_tac `scale = (2 : real) pow biased / 2 pow 1075`
  \\ qabbrev_tac `source = if negative then -(mantissa * fp64_pow2 exponent)
                             else mantissa * fp64_pow2 exponent`
  \\ qabbrev_tac
       `result = (float_round roundTiesToEven negative source : (52,11) float)`
  \\ `&lower + error = mantissa * 2 pow 52` by
    (simp_tac std_ss [Abbr `error`] \\ RealField.REAL_ARITH_TAC)
  \\ `(&lower + error) * scale = mantissa * fp64_pow2 exponent` by
    simp [Abbr `scale`, Abbr `biased`, fp64_normal_scale]
  \\ `mantissa * fp64_pow2 exponent < fp64_pow2 1023` by (
    qspecl_then [`exponent`, `mantissa`, `1023`] mp_tac normalized_pow2_threshold
    \\ simp [])
  \\ `mantissa * fp64_pow2 exponent < threshold (:52 # 11)` by
    metis_tac [fp64_power_1023_below_threshold, realTheory.REAL_LT_TRANS]
  \\ `0 < scale` by
    simp [Abbr `scale`, realTheory.REAL_LT_DIV, realTheory.REAL_POW_LT]
  \\ `float_value result =
       Float (if negative then -(&(nearest_even_nat lower error) * scale)
              else &(nearest_even_nat lower error) * scale)` by (
    qunabbrev_tac `scale`
    \\ qspecl_then [`negative`, `biased`, `lower`, `error`]
         mp_tac normal_float_value_nearest_signed
    \\ impl_tac
    >- asm_simp_tac std_ss [EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``]
    \\ asm_simp_tac std_ss [LET_THM, Abbr `result`, Abbr `source`])
  \\ `(float_value result = Float source) <=> error = 0` by (
    qspecl_then [`negative`, `lower`, `error`, `scale`, `result`]
         mp_tac nearest_even_signed_precision
    \\ asm_simp_tac std_ss [Abbr `source`])
  \\ `fp64_round_quantize roundTiesToEven negative (exponent,mantissa) =
       (F, F, error <> 0, float_to_fp64 result)` by (
    qspecl_then [`negative`, `exponent`, `mantissa`, `lower`, `error`]
         mp_tac fp64_round_quantize_normal_nearest_signed
    \\ impl_tac
    >- fs [Abbr `lower`, Abbr `error`,
           EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``]
    \\ asm_simp_tac std_ss [Abbr `result`, Abbr `source`])
  \\ `~(abs source < 2 / 2 pow (INT_MAX (:11))) /\
       ~(2 pow (INT_MIN (:11)) <= abs source)` by (
    `~(exponent < -1022) /\ ~(1024 <= exponent)` by intLib.ARITH_TAC
    \\ qspecl_then [`negative`, `exponent`, `mantissa`] mp_tac normalized_fp64_source
    \\ asm_simp_tac std_ss [LET_THM, Abbr `source`])
  \\ qunabbrev_tac `result`
  \\ asm_simp_tac (srw_ss())
       [binary_ieeeTheory.float_round_with_flags_def, LET_THM,
        binary_ieeeTheory.float_is_infinite_def]
  \\ RULE_ASSUM_TAC (REWRITE_RULE
       [EVAL ``words$INT_MAX (:11)``, EVAL ``words$INT_MIN (:11)``])
  \\ asm_simp_tac std_ss []
QED

Theorem fp64_round_quantize_large_nearest_flags:
  !negative exponent mantissa.
    1024 <= exponent /\ 1 <= mantissa /\ mantissa < 2 ==>
    let source = if negative then -(mantissa * fp64_pow2 exponent)
                 else mantissa * fp64_pow2 exponent in
    let (flags, result) =
      (float_round_with_flags roundTiesToEven negative source :
         flags # (52,11) float) in
    fp64_round_quantize roundTiesToEven negative (exponent, mantissa) =
      (flags.Underflow_BeforeRounding, flags.Overflow, flags.Precision,
       float_to_fp64 result)
Proof
  qx_genl_tac [`negative`, `exponent`, `mantissa`] \\ strip_tac
  \\ simp_tac std_ss [LET_THM]
  \\ qabbrev_tac `source = if negative then -(mantissa * fp64_pow2 exponent)
                             else mantissa * fp64_pow2 exponent`
  \\ qabbrev_tac
       `result = (float_round roundTiesToEven negative source : (52,11) float)`
  \\ `2 ** 52 <= Num (flr (mantissa * 2 pow 52))` by (
    qspec_then `mantissa` mp_tac fp64_normal_scaled_floor
    \\ impl_tac >- simp []
    \\ simp_tac std_ss [LET_THM])
  \\ `result =
       (<|Sign := if negative then 1w else 0w;
          Exponent := 2047w; Significand := 0w|> : (52,11) float)` by (
    qspecl_then [`negative`, `exponent`, `mantissa`]
         mp_tac normalized_float_round_nearest_large_signed
    \\ asm_simp_tac std_ss [Abbr `result`, Abbr `source`])
  \\ `float_value result = Infinity` by
    simp [binary_ieeeTheory.float_value_def, EVAL ``(-1w : word11)``]
  \\ `fp64_round_quantize roundTiesToEven negative (exponent,mantissa) =
       (F, T, T, float_to_fp64 result)` by (
    qspecl_then [`negative`, `exponent`, `mantissa`,
                  `Num (flr (mantissa * 2 pow 52))`]
         mp_tac fp64_round_quantize_large_nearest_signed
    \\ asm_simp_tac std_ss [Abbr `result`, Abbr `source`])
  \\ `~(abs source < 2 / 2 pow (INT_MAX (:11)))` by (
    `~(exponent < -1022)` by intLib.ARITH_TAC
    \\ qspecl_then [`negative`, `exponent`, `mantissa`] mp_tac normalized_fp64_source
    \\ asm_simp_tac std_ss [LET_THM, Abbr `source`])
  \\ qunabbrev_tac `result`
  \\ asm_simp_tac (srw_ss())
       [binary_ieeeTheory.float_round_with_flags_def, LET_THM,
        binary_ieeeTheory.float_is_infinite_def]
  \\ RULE_ASSUM_TAC (REWRITE_RULE
       [EVAL ``words$INT_MAX (:11)``, EVAL ``words$INT_MIN (:11)``])
  \\ asm_simp_tac std_ss []
QED

Theorem fp64_round_quantize_top_nearest_flags:
  !negative mantissa.
    1 <= mantissa /\ mantissa < 2 ==>
    let source = if negative then -(mantissa * fp64_pow2 1023)
                 else mantissa * fp64_pow2 1023 in
    let (flags, result) =
      (float_round_with_flags roundTiesToEven negative source :
         flags # (52,11) float) in
    fp64_round_quantize roundTiesToEven negative (1023, mantissa) =
      (flags.Underflow_BeforeRounding, flags.Overflow, flags.Precision,
       float_to_fp64 result)
Proof
  qx_genl_tac [`negative`, `mantissa`] \\ strip_tac
  \\ qspec_then `mantissa` mp_tac fp64_normal_scaled_floor
  \\ impl_tac >- simp []
  \\ simp_tac std_ss [LET_THM] \\ strip_tac
  \\ qabbrev_tac `lower = Num (flr (mantissa * 2 pow 52))`
  \\ qabbrev_tac `error = mantissa * 2 pow 52 - &lower`
  \\ qabbrev_tac `scale = (2 : real) pow 2046 / 2 pow 1075`
  \\ qabbrev_tac `source = if negative then -(mantissa * fp64_pow2 1023)
                             else mantissa * fp64_pow2 1023`
  \\ qabbrev_tac
       `result = (float_round roundTiesToEven negative source : (52,11) float)`
  \\ `&lower + error = mantissa * 2 pow 52` by
    (simp_tac std_ss [Abbr `error`] \\ RealField.REAL_ARITH_TAC)
  \\ `(&lower + error) * scale = mantissa * fp64_pow2 1023` by (
    qspecl_then [`1023`, `mantissa`] mp_tac fp64_normal_scale
    \\ simp [Abbr `scale`])
  \\ `2 ** 52 <= nearest_even_nat lower error /\
       nearest_even_nat lower error <= 2 ** 53` by (
    qspecl_then [`lower`, `error`] mp_tac nearest_even_nat_bounds
    \\ simp_tac std_ss [EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``]
    \\ decide_tac)
  \\ `result =
       (<|Sign := if negative then 1w else 0w;
          Exponent := if nearest_even_nat lower error = 2 ** 53 then 2047w else 2046w;
          Significand := if nearest_even_nat lower error = 2 ** 53
                         then 0w else n2w (nearest_even_nat lower error)|>
        : (52,11) float)` by (
    qunabbrev_tac `scale`
    \\ qspecl_then [`negative`, `lower`, `error`]
         mp_tac normal_float_round_nearest_top_signed
    \\ impl_tac
    >- asm_simp_tac std_ss [EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``]
    \\ asm_simp_tac std_ss [LET_THM, Abbr `result`, Abbr `source`])
  \\ `fp64_round_quantize roundTiesToEven negative (1023,mantissa) =
       (F, nearest_even_nat lower error = 2 ** 53,
        error <> 0 \/ nearest_even_nat lower error = 2 ** 53,
        float_to_fp64 result)` by (
    qspecl_then [`negative`, `mantissa`, `lower`, `error`]
         mp_tac fp64_round_quantize_top_nearest_signed
    \\ impl_tac
    >- fs [Abbr `lower`, Abbr `error`,
           EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``]
    \\ asm_simp_tac std_ss [Abbr `result`, Abbr `source`])
  \\ `~(abs source < 2 / 2 pow (INT_MAX (:11))) /\
       ~(2 pow (INT_MIN (:11)) <= abs source)` by (
    qspecl_then [`negative`, `1023`, `mantissa`] mp_tac normalized_fp64_source
    \\ asm_simp_tac std_ss
         [LET_THM, Abbr `source`, EVAL ``(1023 : int) < -1022``,
          EVAL ``(1024 : int) <= 1023``])
  \\ Cases_on `nearest_even_nat lower error = 2 ** 53`
  >- (
    RULE_ASSUM_TAC (REWRITE_RULE [EVAL ``(2 : num) ** 53``])
    \\ `float_value result = Infinity` by
      simp [binary_ieeeTheory.float_value_def, EVAL ``(-1w : word11)``]
    \\ qunabbrev_tac `result`
    \\ asm_simp_tac (srw_ss())
         [binary_ieeeTheory.float_round_with_flags_def, LET_THM,
          binary_ieeeTheory.float_is_infinite_def]
    \\ RULE_ASSUM_TAC (REWRITE_RULE
         [EVAL ``words$INT_MAX (:11)``, EVAL ``words$INT_MIN (:11)``])
    \\ asm_simp_tac std_ss [])
  \\ RULE_ASSUM_TAC (REWRITE_RULE
    [EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``])
  \\ `0 < scale` by
    simp [Abbr `scale`, realTheory.REAL_LT_DIV, realTheory.REAL_POW_LT]
  \\ `float_value result =
       Float (if negative then -(&(nearest_even_nat lower error) * scale)
              else &(nearest_even_nat lower error) * scale)` by (
    qunabbrev_tac `scale`
    \\ qspecl_then [`negative`, `2046`, `nearest_even_nat lower error`]
         mp_tac normal_rounding_value_signed
    \\ impl_tac >- simp [EVAL ``(2 : num) ** 52``, EVAL ``(2 : num) ** 53``]
    \\ asm_simp_tac std_ss [EVAL ``(2 : num) ** 53``])
  \\ `(float_value result = Float source) <=> error = 0` by (
    qspecl_then [`negative`, `lower`, `error`, `scale`, `result`]
         mp_tac nearest_even_signed_precision
    \\ asm_simp_tac std_ss [Abbr `source`])
  \\ qunabbrev_tac `result`
  \\ asm_simp_tac (srw_ss())
       [binary_ieeeTheory.float_round_with_flags_def, LET_THM,
        binary_ieeeTheory.float_is_infinite_def]
  \\ RULE_ASSUM_TAC (REWRITE_RULE
       [EVAL ``words$INT_MAX (:11)``, EVAL ``words$INT_MIN (:11)``])
  \\ asm_simp_tac std_ss []
QED

Theorem fp64_round_quantize_nearest_flags:
  !negative exponent mantissa.
    1 <= mantissa /\ mantissa < 2 ==>
    let source = if negative then -(mantissa * fp64_pow2 exponent)
                 else mantissa * fp64_pow2 exponent in
    let (flags, result) =
      (float_round_with_flags roundTiesToEven negative source :
         flags # (52,11) float) in
    fp64_round_quantize roundTiesToEven negative (exponent, mantissa) =
      (flags.Underflow_BeforeRounding, flags.Overflow, flags.Precision,
       float_to_fp64 result)
Proof
  qx_genl_tac [`negative`, `exponent`, `mantissa`] \\ strip_tac
  \\ Cases_on `exponent < -1022`
  >- (
    qspecl_then [`negative`, `exponent`, `mantissa`]
         mp_tac fp64_round_quantize_subnormal_nearest_flags
    \\ asm_simp_tac std_ss [])
  \\ Cases_on `exponent < 1023`
  >- (
    `-1022 <= exponent` by intLib.ARITH_TAC
    \\ qspecl_then [`negative`, `exponent`, `mantissa`]
         mp_tac fp64_round_quantize_normal_nearest_flags
    \\ asm_simp_tac std_ss [])
  \\ Cases_on `exponent = 1023`
  >- (
    qspecl_then [`negative`, `mantissa`] mp_tac fp64_round_quantize_top_nearest_flags
    \\ asm_simp_tac std_ss [])
  \\ `1024 <= exponent` by intLib.ARITH_TAC
  \\ qspecl_then [`negative`, `exponent`, `mantissa`]
       mp_tac fp64_round_quantize_large_nearest_flags
  \\ asm_simp_tac std_ss []
QED

Theorem fp64_round_quantize_flags:
  !mode negative exponent mantissa.
    1 <= mantissa /\ mantissa < 2 ==>
    let source = if negative then -(mantissa * fp64_pow2 exponent)
                 else mantissa * fp64_pow2 exponent in
    let (flags, result) =
      (float_round_with_flags mode negative source : flags # (52,11) float) in
    fp64_round_quantize mode negative (exponent, mantissa) =
      (flags.Underflow_BeforeRounding, flags.Overflow, flags.Precision,
       float_to_fp64 result)
Proof
  qx_genl_tac [`mode`, `negative`, `exponent`, `mantissa`] \\ strip_tac
  \\ Cases_on `mode = roundTiesToEven`
  >- (
    qspecl_then [`negative`, `exponent`, `mantissa`]
         mp_tac fp64_round_quantize_nearest_flags
    \\ asm_simp_tac std_ss [])
  \\ qspecl_then [`mode`, `negative`, `exponent`, `mantissa`]
       mp_tac fp64_round_quantize_directed_flags
  \\ asm_simp_tac std_ss []
QED

Definition asl_fp64_rounding_def:
  (asl_fp64_rounding roundTiesToEven = FPRounding_TIEEVEN) ∧
  (asl_fp64_rounding roundTowardPositive = FPRounding_POSINF) ∧
  (asl_fp64_rounding roundTowardNegative = FPRounding_NEGINF) ∧
  (asl_fp64_rounding roundTowardZero = FPRounding_ZERO)
End




Theorem realPowInteger_two:
  ∀exponent. realPowInteger 2 exponent = fp64_pow2 exponent
Proof
  qx_gen_tac `exponent` >>
  qspec_then `exponent` strip_assume_tac integerTheory.INT_NUM_CASES >>
  gvs[fp64_pow2_def, realPowInteger_of_num, realPowInteger_neg_of_num]
QED

Theorem integer_subrange_nat_low:
  hi + 1 = dimindex(:α) ⇒
    (integer_subrange (&value) (&hi) 0 : α word) = n2w value
Proof
  strip_tac >>
  simp[integer_subrange_pos, bitstringTheory.field_fixwidth,
       arithmeticTheory.ADD1, bitstringTheory.v2w_fixwidth,
       bitstringTheory.v2w_n2v]
QED

Theorem fp64_pack_fields:
  concat_vec (concat_vec (sign : word1) (exponent : word11) : 12 word)
    (fraction : 52 word) =
  machine_ieee$float_to_fp64
    <| Sign := sign; Exponent := exponent; Significand := fraction |>
Proof
  simp[sail2_operators_mwordsTheory.concat_vec_def,
       machine_ieeeTheory.float_to_fp64_def] >>
  irule wordsTheory.word_concat_assoc >> simp[]
QED

Theorem update_vec_dec_bitU_of_bool:
  update_vec_dec (word : α word) (&index) (bitU_of_bool bit) =
    (index :+ bit) word
Proof
  simp[sail2_operators_mwordsTheory.update_vec_dec_def,
       sail2_operators_mwordsTheory.update_vec_dec_maybe_def,
       sail2_valuesTheory.update_mword_dec_def,
       sail2_valuesTheory.update_mword_bool_dec_def,
       sail2_valuesTheory.maybe_failwith_def]
QED

Theorem FPUnpack64:
  let fp = machine_ieee$fp64_to_float bits in
  FPUnpack (bits : word64) 0w =
    returnS
      ((if binary_ieee$float_is_signalling fp then FPType_SNaN
        else if binary_ieee$float_is_nan fp then FPType_QNaN
        else if binary_ieee$float_is_infinite fp then FPType_Infinity
        else if binary_ieee$float_is_zero fp then FPType_Zero
        else FPType_Nonzero),
       fp.Sign,
       case binary_ieee$float_value fp of
         binary_ieee$Float number => number
       | binary_ieee$Infinity =>
           if fp.Sign = 1w then -(2 pow 1000000) else 2 pow 1000000
       | binary_ieee$NaN => 0)
Proof
  simp[LET_THM, FUN_EQ_THM] >> qx_gen_tac `asl` >>
  simp[FPUnpack_def, undefined_FPType_def,
       preludeTheory.undefined_bitvector_def, preludeTheory.undefined_real_def,
       bindS, seqS, returnS, asl_word_rws] >>
  simp[EVAL ``update_vec_dec (0w : word32) 26 (Bit 0w)``] >>
  simp[FPUnpackBase_def, vec_of_bits_access_vec_dec_single,
       Excl "access_vec_dec_def"] >>
  simp[undefined_FPType_def,
       preludeTheory.undefined_bitvector_def, preludeTheory.undefined_real_def,
       bindS, seqS, returnS, sail2_state_monadTheory.assert_expS_def,
       asl_word_rws] >>
  simp[IsOnes_def, sail_ones_def, asl_word_rws,
       lem_numTheory.realFromFrac_def, realPowInteger_of_num,
       realPowInteger_neg_of_num, realPowInteger_sub_of_num,
       binary_ieeeTheory.float_is_signalling_def,
       binary_ieeeTheory.float_is_nan_def,
       binary_ieeeTheory.float_is_infinite_def,
       binary_ieeeTheory.float_is_zero, binary_ieeeTheory.float_value_def,
       machine_ieeeTheory.fp64_to_float_def] >>
  `(20 : real) / 10 = 2` by
    (CONV_TAC SYM_CONV >> simp[REAL_EQ_RDIV_EQ, REAL_LT, REAL_OF_NUM_MUL]) >>
  simp[REAL_DIV_LZERO, REAL_DIV_REFL] >>
  qabbrev_tac `exponent : word11 = (62 >< 52) bits` >>
  qabbrev_tac `fraction : 52 word = (51 >< 0) bits` >>
  qabbrev_tac `sign : word1 = (63 >< 63) bits` >>
  Cases_on `exponent = 2047w` >>
  gvs[bindS, seqS, returnS]
  >- (
    `((51 >< 51) fraction : word1) = 1w ⇔ word_msb fraction` by
      (simp[word_msb_def] >> blastLib.BBLAST_TAC) >>
    Cases_on `fraction = 0w` >> gvs[bindS, seqS, returnS] >>
    Cases_on `word_msb fraction` >> gvs[bindS, seqS, returnS]) >>
  qspecl_then [`2 : real`, `1022 : num`]
    (assume_tac o SIMP_RULE (srw_ss()) []) real_pow_suc_scale >>
  `sign = 0w ∨ sign = 1w` by blastLib.BBLAST_TAC >>
  Cases_on `exponent = 0w` >>
  Cases_on `fraction = 0w` >>
  Cases_on `sign = 0w` >>
  gvs[bindS, seqS, returnS, binary_ieeeTheory.float_to_real_def,
      realTheory.pow0, POW_1, GSYM real_div, REAL_MUL_LNEG,
      REAL_MUL_ASSOC, REAL_DIV_LZERO] >>
  simp[real_div, REAL_MUL_ASSOC]
QED

Theorem FPUnpack64_no_flush:
  ¬word_bit 24 fpcr ⇒
    FPUnpack (bits : word64) fpcr = FPUnpack bits 0w
Proof
  strip_tac >>
  `((24 >< 24) ((26 :+ F) fpcr) : word1) = 0w` by (
    qpat_x_assum `¬word_bit 24 fpcr` mp_tac >> blastLib.BBLAST_TAC) >>
  simp[FUN_EQ_THM] >> qx_gen_tac `asl` >>
  simp[FPUnpack_def, EVAL ``Bit (0w : word1)``,
       GSYM (EVAL ``bitU_of_bool F``),
       update_vec_dec_bitU_of_bool, undefined_FPType_def,
       preludeTheory.undefined_bitvector_def, preludeTheory.undefined_real_def,
       bindS, seqS, returnS] >>
  simp[FPUnpackBase_def, vec_of_bits_access_vec_dec_single,
       Excl "access_vec_dec_def"]
QED

Theorem fp64_largest_bound:
  binary_ieee$largest (:52 # 11) < (2 : real) pow 2048
Proof
  simp[binary_ieeeTheory.largest, REAL_OF_NUM_POW] >>
  RealField.REAL_ARITH_TAC
QED

Theorem fp64_value_bounds:
  binary_ieee$float_value (fp : (52, 11) binary_ieee$float) =
    binary_ieee$Float number ⇒
  -(2 pow 1000000) < number ∧ number < (2 : real) pow 1000000
Proof
  strip_tac >>
  drule (SIMP_RULE (srw_ss()) []
    (INST_TYPE [alpha |-> ``:52``, beta |-> ``:11``]
      binary_ieeeTheory.float_bounds)) >> strip_tac >>
  `binary_ieee$largest (:52 # 11) < (2 : real) pow 1000000` by (
    irule REAL_LT_TRANS >> qexists_tac `(2 : real) pow 2048` >>
    conj_tac >- ACCEPT_TAC fp64_largest_bound >>
    irule REAL_POW_MONO_LT >> simp[]) >>
  conj_tac
  >- (
    irule REAL_LTE_TRANS >>
    qexists_tac `-binary_ieee$largest (:52 # 11)` >> simp[]) >>
  irule REAL_LET_TRANS >>
  qexists_tac `binary_ieee$largest (:52 # 11)` >> simp[]
QED

Theorem float_compare_with_infinity_bound:
  0 < (infinity_bound : real) ∧
  (∀number. binary_ieee$float_value left = binary_ieee$Float number ⇒
    -infinity_bound < number ∧ number < infinity_bound) ∧
  (∀number. binary_ieee$float_value right = binary_ieee$Float number ⇒
    -infinity_bound < number ∧ number < infinity_bound) ⇒
  let value = λfp.
    case binary_ieee$float_value fp of
      binary_ieee$Float number => number
    | binary_ieee$Infinity => if fp.Sign = 1w then -infinity_bound else infinity_bound
    | binary_ieee$NaN => 0 in
  (if binary_ieee$float_is_nan left ∨ binary_ieee$float_is_nan right then 3w
   else if value left = value right then 6w
   else if value left < value right then 8w else 2w) =
  (if binary_ieee$float_is_nan left ∨ binary_ieee$float_is_nan right then 3w
   else if binary_ieee$float_equal left right then 6w
   else if binary_ieee$float_less_than left right then 8w else 2w : word4)
Proof
  strip_tac >>
  namedCases_on `binary_ieee$float_value left` ["left_number", "", ""] >>
  namedCases_on `binary_ieee$float_value right` ["right_number", "", ""] >>
  gvs[LET_THM, binary_ieeeTheory.float_is_nan_def,
      binary_ieeeTheory.float_equal_def, binary_ieeeTheory.float_less_than_def,
      binary_ieeeTheory.float_compare_def]
  >- (
    Cases_on `left_number = right_number` >> gvs[] >>
    Cases_on `left_number < right_number` >> gvs[])
  >- (
    Cases_on `right.Sign = 1w` >> simp[] >>
    metis_tac[REAL_LT_IMP_NE, REAL_LT_ANTISYM])
  >- (
    Cases_on `left.Sign = 1w` >> simp[] >>
    metis_tac[REAL_LT_IMP_NE, REAL_LT_ANTISYM]) >>
  `(left.Sign = right.Sign) ⇔ ((left.Sign = 1w) ⇔ (right.Sign = 1w))` by
    blastLib.BBLAST_TAC >>
  `-infinity_bound < infinity_bound` by (
    qpat_x_assum `0 < infinity_bound` mp_tac >>
    RealArith.REAL_ARITH_TAC) >>
  Cases_on `left.Sign = 1w` >>
  Cases_on `right.Sign = 1w` >> gvs[] >>
  metis_tac[REAL_LT_IMP_NE, REAL_LT_ANTISYM]
QED

Theorem update_subrange_vec_dec_low_bit:
  update_subrange_vec_dec (word : α word) 0 0 (1w : word1) = word || 1w
Proof
  simp[asl_word_rws] >>
  simp[word_modify_def, word_or_def, fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >>
  qx_gen_tac `index` >> strip_tac >>
  Cases_on `index = 0` >> simp[word_index]
QED

Theorem update_subrange_vec_dec_set_bit:
  update_subrange_vec_dec (word : α word) (&bit) (&bit) (1w : word1) =
    word || (1w << bit)
Proof
  simp[asl_word_rws, word_modify_def, word_or_def, word_lsl_def,
       fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >>
  qx_gen_tac `index` >> strip_tac >>
  Cases_on `index = bit` >> simp[word_index]
QED

Theorem FPProcessException_InvalidOp:
  asl_sys_regs_ok asl ∧ ¬word_bit 8 fpcr ⇒
    FPProcessException FPExc_InvalidOp fpcr asl =
    write_regS FPSR_ref (FPSR_ref.read_from asl.regstate || 1w) asl
Proof
  strip_tac >>
  `((8 >< 8) fpcr : word1) = 0w` by (
    qpat_x_assum `¬word_bit 8 fpcr` mp_tac >> blastLib.BBLAST_TAC) >>
  `UsingAArch32 () asl = returnS F asl` by
    (irule UsingAArch32_F >> fs[asl_sys_regs_ok_def]) >>
  simp[FPProcessException_def, vec_of_bits_access_vec_dec_single,
       Excl "access_vec_dec_def"] >>
  simp[bindS, returnS, asl_reg_rws,
       SIMP_RULE (srw_ss()) [] update_subrange_vec_dec_low_bit]
QED

Theorem FPProcessException_zero:
  asl_sys_regs_ok asl ⇒
    FPProcessException exception 0w asl =
      write_regS FPSR_ref
        (FPSR_ref.read_from asl.regstate ||
          case exception of
            FPExc_InvalidOp => (1w : word32)
          | FPExc_DivideByZero => 2w
          | FPExc_Overflow => 4w
          | FPExc_Underflow => 8w
          | FPExc_Inexact => 16w
          | FPExc_InputDenorm => 128w) asl
Proof
  strip_tac >>
  `UsingAArch32 () asl = returnS F asl` by
    (irule UsingAArch32_F >> fs[asl_sys_regs_ok_def]) >>
  Cases_on `exception` >>
  simp[FPProcessException_def, vec_of_bits_access_vec_dec_single,
       Excl "access_vec_dec_def", bindS, returnS, asl_reg_rws,
       update_subrange_vec_dec_set_bit]
QED

Theorem asl_sys_regs_ok_write_FPSR:
  asl_sys_regs_ok
    (asl with regstate := FPSR_ref.write_to value asl.regstate) ⇔
  asl_sys_regs_ok asl
Proof
  simp[asl_sys_regs_ok_def, FPSR_ref_def]
QED

Theorem FPProcessNaN64:
  (kind = FPType_SNaN ∨ kind = FPType_QNaN) ∧
  asl_sys_regs_ok asl ∧ ¬word_bit 8 fpcr ⇒
    FPProcessNaN kind (value : word64) fpcr asl =
      seqS
        (if kind = FPType_SNaN then
           write_regS FPSR_ref (FPSR_ref.read_from asl.regstate || 1w)
         else returnS ())
        (returnS
          (if word_bit 25 fpcr then 0x7FF8000000000000w
           else if kind = FPType_SNaN then value || 0x0008000000000000w
           else value)) asl
Proof
  strip_tac >>
  simp[FPProcessNaN_def, FPDefaultNaN_def,
       vec_of_bits_access_vec_dec_single, update_vec_dec_bitU_of_bool,
       EVAL ``Bit (1w : word1)``, Excl "access_vec_dec_def"] >>
  gvs[seqS, bindS, returnS, FPProcessException_InvalidOp] >>
  simp[asl_reg_rws, returnS,
       SIMP_RULE (srw_ss()) [sail2_valuesTheory.bitU_of_bool_def]
         (Q.INST [`bit` |-> `T`] update_vec_dec_bitU_of_bool)]
  >> Cases_on `word_bit 25 fpcr`
  >> simp[extract_bit, returnS]
  >> blastLib.BBLAST_TAC
QED

Theorem fp64_nan_bits:
  (machine_ieee$fp64_isNan value ⇔
    ((62 >< 52) value : word11) = 2047w ∧
    ((51 >< 0) value : 52 word) ≠ 0w) ∧
  (machine_ieee$fp64_isSignallingNan value ⇔
    machine_ieee$fp64_isNan value ∧ ¬word_bit 51 value)
Proof
  conj_tac
  >- (
    simp[machine_ieeeTheory.fp64_isNan_def,
         binary_ieeeTheory.float_is_nan_def,
         binary_ieeeTheory.float_value_def,
         machine_ieeeTheory.fp64_to_float_def] >>
    Cases_on `((62 >< 52) value : word11) = 2047w` >>
    Cases_on `((51 >< 0) value : 52 word) = 0w` >> simp[])
  >> simp[machine_ieeeTheory.fp64_isSignallingNan_def,
       machine_ieeeTheory.fp64_isNan_def,
       binary_ieeeTheory.float_is_signalling_def,
       machine_ieeeTheory.fp64_to_float_def, word_msb_def, word_extract_def] >>
  blastLib.BBLAST_TAC
QED

Theorem fp64_default_nan:
  machine_ieee$fp64_isNan (0x7FF8000000000000w : word64) /\
  ~machine_ieee$fp64_isSignallingNan (0x7FF8000000000000w : word64)
Proof
  simp [fp64_nan_bits]
QED

Theorem FPNaNResult_not_nan:
  ¬machine_ieee$fp64_isNan result ⇒ FPNaNResult (result, a, b, c) = result
Proof
  simp[FPNaNResult_def]
QED

Theorem FPNaNResult_nan:
  machine_ieee$fp64_isNan result ⇒
    FPNaNResult (result, a, b, c) =
    FPNaNResult (0x7FF8000000000000w, a, b, c)
Proof
  simp[FPNaNResult_def, fp64_default_nan]
QED

Theorem FPProcessNaNs64_result:
  (left_kind = FPType_SNaN ⇔ machine_ieee$fp64_isSignallingNan left) ∧
  (right_kind = FPType_SNaN ⇔ machine_ieee$fp64_isSignallingNan right) ∧
  (left_kind = FPType_QNaN ⇔
    machine_ieee$fp64_isNan left ∧ ¬machine_ieee$fp64_isSignallingNan left) ∧
  (right_kind = FPType_QNaN ⇔
    machine_ieee$fp64_isNan right ∧ ¬machine_ieee$fp64_isSignallingNan right) ∧
  asl_sys_regs_ok asl ∧ ¬word_bit 8 fpcr ∧ ¬word_bit 25 fpcr ⇒
    FPProcessNaNs left_kind right_kind (left : word64) right fpcr asl =
      seqS
        (if machine_ieee$fp64_isSignallingNan left ∨
            machine_ieee$fp64_isSignallingNan right then
           write_regS FPSR_ref (FPSR_ref.read_from asl.regstate || 1w)
         else returnS ())
        (returnS
          (machine_ieee$fp64_isNan left ∨ machine_ieee$fp64_isNan right,
           if machine_ieee$fp64_isNan left ∨ machine_ieee$fp64_isNan right
           then FPNaNResult (0x7FF8000000000000w, left, right, right)
           else 0w)) asl
Proof
  strip_tac >>
  Cases_on `left_kind = FPType_SNaN` >> Cases_on `right_kind = FPType_SNaN` >>
  Cases_on `left_kind = FPType_QNaN` >> Cases_on `right_kind = FPType_QNaN` >>
  gvs[CONJUNCT2 fp64_nan_bits, FPProcessNaNs_def, FPProcessNaN64,
      FPNaNResult_def, fp64_default_nan, preludeTheory.undefined_bitvector_def,
      sail2_state_monadTheory.undefined_boolS_def,
      bindS, seqS, returnS, asl_reg_rws, asl_word_rws]
QED

Theorem FPUnpack64_classify:
  let kind =
    if binary_ieee$float_is_signalling fp then FPType_SNaN
    else if binary_ieee$float_is_nan fp then FPType_QNaN
    else if binary_ieee$float_is_infinite fp then FPType_Infinity
    else if binary_ieee$float_is_zero fp then FPType_Zero
    else FPType_Nonzero in
  (kind = FPType_SNaN ⇔ binary_ieee$float_is_signalling fp) ∧
  (kind = FPType_QNaN ⇔
    binary_ieee$float_is_nan fp ∧ ¬binary_ieee$float_is_signalling fp) ∧
  (kind = FPType_SNaN ∨ kind = FPType_QNaN ⇔ binary_ieee$float_is_nan fp)
Proof
  simp[LET_THM, binary_ieeeTheory.float_is_signalling_def] >>
  Cases_on `binary_ieee$float_is_nan fp` >>
  Cases_on `word_msb fp.Significand` >> simp[] >>
  Cases_on `binary_ieee$float_is_infinite fp` >> simp[] >>
  Cases_on `binary_ieee$float_is_zero fp` >> simp[]
QED

Theorem FPCompare64:
  asl_sys_regs_ok asl ∧ ¬word_bit 24 fpcr ∧ ¬word_bit 8 fpcr ⇒
    FPCompare (left : word64) right F fpcr asl =
    seqS
      (if machine_ieee$fp64_isSignallingNan left ∨
          machine_ieee$fp64_isSignallingNan right then
         write_regS FPSR_ref (FPSR_ref.read_from asl.regstate || 1w)
       else returnS ())
      (returnS (arm8$FPCompare64 (left, right))) asl
Proof
  strip_tac >>
  simp[FPCompare_def, FPUnpack64_no_flush,
       SIMP_RULE std_ss [LET_THM] FPUnpack64,
       undefined_FPType_def, preludeTheory.undefined_bitvector_def,
       preludeTheory.undefined_real_def,
       arm8Theory.FPCompare64_def, machine_ieeeTheory.fp64_isNan_def,
       machine_ieeeTheory.fp64_equal_def, machine_ieeeTheory.fp64_lessThan_def,
       machine_ieeeTheory.fp64_isSignallingNan_def,
       bindS, seqS, returnS, asl_word_rws] >>
  qabbrev_tac `left_fp = machine_ieee$fp64_to_float left` >>
  qabbrev_tac `right_fp = machine_ieee$fp64_to_float right` >>
  simp[SIMP_RULE std_ss [LET_THM] FPUnpack64_classify] >>
  mp_tac (float_compare_with_infinity_bound
    |> INST_TYPE [alpha |-> ``:52``, beta |-> ``:11``]
    |> Q.INST [`left` |-> `left_fp`, `right` |-> `right_fp`,
               `infinity_bound` |-> `(2 : real) pow 1000000`]) >>
  impl_tac
  >- (
    conj_tac >- (irule REAL_POW_LT >> simp[]) >>
    metis_tac[fp64_value_bounds]) >>
  simp[LET_THM] >> disch_tac >>
  Cases_on `binary_ieee$float_is_nan left_fp` >>
  Cases_on `binary_ieee$float_is_nan right_fp` >>
  gvs[binary_ieeeTheory.float_is_signalling_def] >>
  Cases_on `word_msb left_fp.Significand` >>
  Cases_on `word_msb right_fp.Significand` >>
  simp[seqS, returnS, FPProcessException_InvalidOp]
QED

Theorem FPRoundingMode_total:
  ∀fpcr. ∃mode. armv86a$FPRoundingMode fpcr = returnS mode
Proof
  qx_gen_tac `fpcr` >>
  simp[armv86aTheory.FPRoundingMode_def, asl_word_rws] >>
  wordsLib.Cases_on_word_value `((23 >< 22) fpcr : word2)` >>
  simp[FPDecodeRounding_def] >> metis_tac[]
QED

fun fp_binop_nan_tac asl_def =
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qspec_then `fpcr` (qx_choose_then `mode` assume_tac) FPRoundingMode_total >>
  simp[asl_def, FPUnpack64_no_flush,
       SIMP_RULE std_ss [LET_THM] FPUnpack64,
       undefined_FPType_def, preludeTheory.undefined_bitvector_def,
       preludeTheory.undefined_real_def,
       sail2_state_monadTheory.undefined_boolS_def,
       bindS, seqS, returnS, asl_word_rws] >>
  qmatch_goalsub_abbrev_tac
    `FPProcessNaNs left_kind right_kind left right fpcr asl` >>
  mp_tac FPProcessNaNs64_result >>
  impl_tac
  >- (
    unabbrev_all_tac >>
    simp[SIMP_RULE std_ss [LET_THM] FPUnpack64_classify,
         machine_ieeeTheory.fp64_isNan_def,
         machine_ieeeTheory.fp64_isSignallingNan_def]) >>
  disch_then (fn processed => rewrite_tac [processed]) >>
  Cases_on `machine_ieee$fp64_isSignallingNan left ∨
    machine_ieee$fp64_isSignallingNan right` >>
  gvs[bindS, seqS, returnS, asl_reg_rws];

Theorem FPAdd64_NaN:
  (machine_ieee$fp64_isNan left ∨ machine_ieee$fp64_isNan right) ∧
  asl_sys_regs_ok asl ∧ ¬word_bit 24 fpcr ∧ ¬word_bit 8 fpcr ∧
  ¬word_bit 25 fpcr ⇒
    FPAdd (left : word64) right fpcr asl =
      seqS
        (if machine_ieee$fp64_isSignallingNan left ∨
            machine_ieee$fp64_isSignallingNan right then
           write_regS FPSR_ref (FPSR_ref.read_from asl.regstate || 1w)
         else returnS ())
        (returnS (FPNaNResult (0x7FF8000000000000w, left, right, right))) asl
Proof
  fp_binop_nan_tac FPAdd_def
QED

Theorem FPSub64_NaN:
  (machine_ieee$fp64_isNan left ∨ machine_ieee$fp64_isNan right) ∧
  asl_sys_regs_ok asl ∧ ¬word_bit 24 fpcr ∧ ¬word_bit 8 fpcr ∧
  ¬word_bit 25 fpcr ⇒
    FPSub (left : word64) right fpcr asl =
      seqS
        (if machine_ieee$fp64_isSignallingNan left ∨
            machine_ieee$fp64_isSignallingNan right then
           write_regS FPSR_ref (FPSR_ref.read_from asl.regstate || 1w)
         else returnS ())
        (returnS (FPNaNResult (0x7FF8000000000000w, left, right, right))) asl
Proof
  fp_binop_nan_tac FPSub_def
QED

Theorem FPMul64_NaN:
  (machine_ieee$fp64_isNan left ∨ machine_ieee$fp64_isNan right) ∧
  asl_sys_regs_ok asl ∧ ¬word_bit 24 fpcr ∧ ¬word_bit 8 fpcr ∧
  ¬word_bit 25 fpcr ⇒
    FPMul (left : word64) right fpcr asl =
      seqS
        (if machine_ieee$fp64_isSignallingNan left ∨
            machine_ieee$fp64_isSignallingNan right then
           write_regS FPSR_ref (FPSR_ref.read_from asl.regstate || 1w)
         else returnS ())
        (returnS (FPNaNResult (0x7FF8000000000000w, left, right, right))) asl
Proof
  fp_binop_nan_tac FPMul_def
QED

Theorem FPDiv64_NaN:
  (machine_ieee$fp64_isNan left ∨ machine_ieee$fp64_isNan right) ∧
  asl_sys_regs_ok asl ∧ ¬word_bit 24 fpcr ∧ ¬word_bit 8 fpcr ∧
  ¬word_bit 25 fpcr ⇒
    FPDiv (left : word64) right fpcr asl =
      seqS
        (if machine_ieee$fp64_isSignallingNan left ∨
            machine_ieee$fp64_isSignallingNan right then
           write_regS FPSR_ref (FPSR_ref.read_from asl.regstate || 1w)
         else returnS ())
        (returnS (FPNaNResult (0x7FF8000000000000w, left, right, right))) asl
Proof
  fp_binop_nan_tac FPDiv_def
QED

Theorem FPSqrt64_NaN:
  machine_ieee$fp64_isNan value ∧ asl_sys_regs_ok asl ∧
  ¬word_bit 24 fpcr ∧ ¬word_bit 8 fpcr ∧ ¬word_bit 25 fpcr ⇒
    FPSqrt (value : word64) fpcr asl =
      seqS
        (if machine_ieee$fp64_isSignallingNan value then
           write_regS FPSR_ref (FPSR_ref.read_from asl.regstate || 1w)
         else returnS ())
        (returnS (FPNaNResult (0x7FF8000000000000w, value, value, value))) asl
Proof
  strip_tac >>
  `binary_ieee$float_is_nan (machine_ieee$fp64_to_float value)` by
    fs[machine_ieeeTheory.fp64_isNan_def] >>
  simp[FPSqrt_def, FPUnpack64_no_flush,
       SIMP_RULE std_ss [LET_THM] FPUnpack64,
       SIMP_RULE std_ss [LET_THM] FPUnpack64_classify,
       undefined_FPType_def, preludeTheory.undefined_bitvector_def,
       preludeTheory.undefined_real_def,
       bindS, seqS, returnS, asl_word_rws] >>
  Cases_on
    `binary_ieee$float_is_signalling (machine_ieee$fp64_to_float value)` >>
  gvs[FPProcessNaN64, FPNaNResult_def, fp64_default_nan,
      machine_ieeeTheory.fp64_isSignallingNan_def,
      bindS, seqS, returnS, asl_reg_rws]
QED

Theorem FPInfinity64:
  FPInfinity 64 sign =
    returnS (machine_ieee$float_to_fp64
      <| Sign := sign; Exponent := 2047w; Significand := 0w |>)
Proof
  rw[FUN_EQ_THM] >>
  simp[FPInfinity_def, seqS, returnS, asl_word_rws,
       machine_ieeeTheory.float_to_fp64_def] >> blastLib.BBLAST_TAC
QED

Theorem FPMaxNormal64:
  FPMaxNormal 64 sign =
    returnS (machine_ieee$float_to_fp64
      <| Sign := sign; Exponent := 2046w; Significand := -1w |>)
Proof
  rw[FUN_EQ_THM] >>
  simp[FPMaxNormal_def, seqS, returnS, asl_word_rws,
       machine_ieeeTheory.float_to_fp64_def] >> blastLib.BBLAST_TAC
QED

Theorem fp64_biased_max:
  ∀exponent.
    max_int (exponent + 1022 + 1) 0 =
    if exponent + 1023 < 0 then 0 else exponent + 1023
Proof
  gen_tac >> simp_tac std_ss [armv86aTheory.max_int_def] >>
  Cases_on `exponent + 1023 < 0` >>
  Cases_on `exponent + 1022 + 1 <= 0` >>
  asm_simp_tac std_ss [] >> intLib.ARITH_TAC
QED

Theorem integer_subrange_nonnegative_low:
  0 <= value ∧ hi + 1 = dimindex(:α) ⇒
    (integer_subrange value (&hi) 0 : α word) = n2w (Num value)
Proof
  strip_tac >>
  `value = &Num value` by simp[] >>
  qpat_x_assum `value = &Num value` SUBST1_TAC >>
  simp[integer_subrange_nat_low]
QED

Theorem integer_access_nonnegative_zero:
  ∀value : int. 0 <= value ⇒
    ((vec_of_bits [integer_access value 0] : word1) = 1w ⇔ ODD (Num value))
Proof
  qx_gen_tac `value` >> strip_tac >>
  `value = &Num value` by simp[] >>
  qpat_x_assum `value = &Num value` SUBST1_TAC >>
  simp[integer_access_nat_zero] >>
  Cases_on `ODD (Num value)` >> simp[]
QED

Theorem fp64_round_fields_nonnegative:
  ∀biased : int. ∀lower : int. ∀increment.
    0 <= biased ∧ 0 <= lower ⇒
    let fields = if increment then
      if lower + 1 = &(2 ** 53) then (biased + 1, &(2 ** 52))
      else (if lower + 1 = &(2 ** 52) then 1 else biased, lower + 1)
      else (biased, lower) in
    0 <= FST fields ∧ 0 <= SND fields
Proof
  qx_genl_tac [`biased`, `lower`, `increment`] >> strip_tac >>
  Cases_on `increment` >>
  simp_tac std_ss [LET_THM] >>
  Cases_on `lower + 1 = &(2 ** 53)` >>
  Cases_on `lower + 1 = &(2 ** 52)` >>
  gvs[] >> intLib.ARITH_TAC
QED

Theorem fp64_magnitude_sign[local]:
  ∀value : real.
    (if value < 0 then (-value, 1w : word1) else (value, 0w)) =
    (abs value, if value < 0 then 1w else 0w)
Proof
  qx_gen_tac `value` >>
  Cases_on `value < 0` >>
  simp[realTheory.abs, GSYM realTheory.REAL_NOT_LT]
QED

fun directed_round_tac mode increment =
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [armv86aTheory.FPRound_def, FPRoundBase_def, asl_fp64_rounding_def,
       EVAL ``update_vec_dec (0w : word32) 26 (Bit (0w : word1))``,
       EVAL ``(vec_of_bits [access_vec_dec (0w : word32) 24] : word1)``,
       EVAL ``(vec_of_bits [access_vec_dec (0w : word32) 11] : word1)``,
       preludeTheory.undefined_bitvector_def, preludeTheory.undefined_real_def,
       preludeTheory.undefined_int_def,
       sail2_state_monadTheory.undefined_boolS_def,
       sail2_state_monadTheory.choose_boolS_def,
       sail2_state_monadTheory.chooseS_def,
       sail2_state_monadTheory.assert_expS_def,
       sail2_state_monadTheory.liftRS_def,
       sail2_state_monadTheory.catch_early_returnS_def,
       sail2_state_monadTheory.early_returnS_def,
       sail2_state_monadTheory.try_catchS_def,
       sail2_state_monadTheory.throwS_def,
       bindS, seqS, returnS, LET_THM, wordsTheory.w2w_id,
       realTheory.REAL_SUB_LZERO, realTheory.real_ge,
       EVAL ``realFromFrac 0 10``, EVAL ``realFromFrac 5 10``,
       EVAL ``realFromFrac 10 10``, EVAL ``realFromFrac 20 10``] >>
  `(((if value < 0 then 1w else 0w) : word1) = 1w ⇔ value < 0) ∧
   (((if value < 0 then 1w else 0w) : word1) = 0w ⇔ ¬(value < 0))` by (
    Cases_on `value < 0` >> simp[]) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  asm_simp_tac std_ss [LET_THM] >>
  asm_simp_tac std_ss
    [fp64_biased_max, realPowInteger_two, fp64_pow2_of_num,
     binary_ieeeTheory.rounding_case_def, LET_THM] >>
  qabbrev_tac `biased = if exponent + 1023 < 0 then 0 else exponent + 1023` >>
  qabbrev_tac `scaled =
    (if biased = 0 then mantissa / fp64_pow2 (-1022 - exponent)
     else mantissa) * 2 pow 52` >>
  qabbrev_tac `lower : int = flr scaled` >>
  qabbrev_tac `error = scaled - real_of_int lower` >>
  qpat_x_assum `Abbrev (biased = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (scaled = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (lower = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (error = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qspecl_then [`exponent`, `mantissa`] mp_tac fp64_quantize_floor >>
  asm_simp_tac std_ss [LET_THM] >> strip_tac >>
  `0 <= lower` by (
    qpat_x_assum `(&Num lower : int) = lower`
      (fn cast => once_rewrite_tac [GSYM cast]) >> simp[]) >>
  `0 <= biased` by (
    qpat_x_assum `(if exponent + 1023 < 0 then 0 else exponent + 1023) = biased`
      (fn bias_equation => rewrite_tac [GSYM bias_equation]) >>
    Cases_on `exponent + 1023 < 0` >> simp[] >>
    intLib.ARITH_TAC) >>
  qspecl_then [mode, `value < 0`, `exponent`, `mantissa`]
    mp_tac fp64_round_quantize_int_fields >>
  asm_simp_tac std_ss [LET_THM, binary_ieeeTheory.rounding_case_def] >>
  asm_simp_tac std_ss [integer_access_nonnegative_zero,
    realTheory.real_gt, EVAL ``(1w : word1) = 1w``,
    EVAL ``(0w : word1) = 1w``] >>
  pairarg_tac >>
  qmatch_asmsub_rename_tac
    `(if _ then _ else _ : int # int) = (result_exponent, result_mantissa)` >>
  asm_simp_tac std_ss [LET_THM] >> strip_tac >>
  asm_simp_tac std_ss [pairTheory.UNCURRY, pairTheory.PAIR] >>
  qspecl_then [`biased`, `lower`, increment]
    mp_tac fp64_round_fields_nonnegative >>
  asm_simp_tac std_ss [LET_THM, EVAL ``(2 : num) ** 52``,
    EVAL ``(2 : num) ** 53``, pairTheory.FST, pairTheory.SND] >> strip_tac >>
  `(scaled <> real_of_int lower) ⇔ error <> 0` by (
    qpat_x_assum `scaled - real_of_int lower = error` mp_tac >>
    rpt (pop_assum kall_tac) >> RealField.REAL_ARITH_TAC) >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [integer_subrange_nonnegative_low, fp64_pack_fields,
     EVAL ``dimindex(:11)``, EVAL ``dimindex(:52)``,
     integerTheory.int_ge] >>
  qpat_x_assum `asl_sys_regs_ok asl` mp_tac >>
  rpt (pop_assum kall_tac) >> strip_tac >>
  Cases_on `value < 0` >>
  Cases_on `biased = 0 ∧ error <> 0` >>
  Cases_on `2047 <= result_exponent` >>
  Cases_on `error = 0` >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPInfinity64, FPMaxNormal64, FPProcessException_zero, asl_sys_regs_ok_write_FPSR,
     SIMP_RULE (srw_ss()) [FPSR_ref_def] asl_sys_regs_ok_write_FPSR,
     sail2_state_monadTheory.try_catchS_def,
     sail2_state_monadTheory.throwS_def,
     bindS, seqS, returnS, asl_reg_rws, FPSR_ref_def] >>
  gvs[] >>
  `(λreg. if reg = "FPSR" then asl.regstate.bitvector_32_dec_reg "FPSR"
     else asl.regstate.bitvector_32_dec_reg reg) =
   asl.regstate.bitvector_32_dec_reg` by (
    simp_tac std_ss [FUN_EQ_THM] >> qx_gen_tac `reg` >>
    Cases_on `reg = "FPSR"` >> simp[]) >>
  simp[];

Theorem FPRound64_algorithm:
  ∀value mode asl.
    value <> 0 ∧ asl_sys_regs_ok asl ⇒
    let initial = sail2_values$while (0 : int, abs value)
      (λ(e, m). m < 1) (λ(e, m). (e - 1, m * 2)) in
    let normalized = sail2_values$while initial
      (λ(e, m). 2 <= m) (λ(e, m). (e + 1, m / 2)) in
    let (underflow, overflow, inexact, result) =
      fp64_round_quantize mode (value < 0) normalized in
    FPRound 64 value 0w (asl_fp64_rounding mode) asl =
      returnS result
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate ||
           (if underflow then 8w else 0w) ||
           (if overflow then 4w else 0w) ||
           (if inexact then 16w else 0w)) asl.regstate)
Proof
  qx_genl_tac [`value`, `mode`, `asl`] >> strip_tac >>
  `0 < abs value` by simp[] >>
  assume_tac (Q.SPEC `value` fp64_magnitude_sign) >>
  namedCases_on
    `sail2_values$while (0 : int, abs value)
       (λ(e, m). m < 1) (λ(e, m). (e - 1, m * 2))`
    ["initial_exponent initial_mantissa"] >>
  namedCases_on
    `sail2_values$while (initial_exponent, initial_mantissa)
       (λ(e, m). 2 <= m) (λ(e, m). (e + 1, m / 2))`
    ["exponent mantissa"] >>
  `1 <= mantissa ∧ mantissa < 2` by (
    qspec_then `abs value` mp_tac FPRound_normalize >>
    asm_simp_tac std_ss [LET_THM, pairTheory.SND]) >>
  asm_simp_tac std_ss [LET_THM] >>
  Cases_on `mode`
  >- suspend "Nearest"
  >- directed_round_tac `roundTowardPositive` `error <> 0 ∧ ¬(value < 0)`
  >- directed_round_tac `roundTowardNegative` `error <> 0 ∧ value < 0`
  >- suspend "Zero"
QED

Resume FPRound64_algorithm[Nearest]:
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [armv86aTheory.FPRound_def, FPRoundBase_def, asl_fp64_rounding_def,
       EVAL ``update_vec_dec (0w : word32) 26 (Bit (0w : word1))``,
       EVAL ``(vec_of_bits [access_vec_dec (0w : word32) 24] : word1)``,
       EVAL ``(vec_of_bits [access_vec_dec (0w : word32) 11] : word1)``,
       preludeTheory.undefined_bitvector_def, preludeTheory.undefined_real_def,
       preludeTheory.undefined_int_def,
       sail2_state_monadTheory.undefined_boolS_def,
       sail2_state_monadTheory.choose_boolS_def,
       sail2_state_monadTheory.chooseS_def,
       sail2_state_monadTheory.assert_expS_def,
       sail2_state_monadTheory.liftRS_def,
       sail2_state_monadTheory.catch_early_returnS_def,
       sail2_state_monadTheory.early_returnS_def,
       sail2_state_monadTheory.try_catchS_def,
       sail2_state_monadTheory.throwS_def,
       bindS, seqS, returnS, LET_THM, wordsTheory.w2w_id,
       realTheory.REAL_SUB_LZERO, realTheory.real_ge,
       EVAL ``realFromFrac 0 10``, EVAL ``realFromFrac 5 10``,
       EVAL ``realFromFrac 10 10``, EVAL ``realFromFrac 20 10``] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  asm_simp_tac std_ss [LET_THM] >>
  asm_simp_tac std_ss
    [fp64_biased_max, realPowInteger_two, fp64_pow2_of_num,
     binary_ieeeTheory.rounding_case_def, LET_THM] >>
  qabbrev_tac `biased = if exponent + 1023 < 0 then 0 else exponent + 1023` >>
  qabbrev_tac `scaled =
    (if biased = 0 then mantissa / fp64_pow2 (-1022 - exponent)
     else mantissa) * 2 pow 52` >>
  qabbrev_tac `lower : int = flr scaled` >>
  qabbrev_tac `error = scaled - real_of_int lower` >>
  qpat_x_assum `Abbrev (biased = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (scaled = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (lower = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (error = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qspecl_then [`exponent`, `mantissa`] mp_tac fp64_quantize_floor >>
  asm_simp_tac std_ss [LET_THM] >> strip_tac >>
  `0 <= lower` by (
    qpat_x_assum `(&Num lower : int) = lower`
      (fn cast => once_rewrite_tac [GSYM cast]) >> simp[]) >>
  `0 <= biased` by (
    qpat_x_assum `(if exponent + 1023 < 0 then 0 else exponent + 1023) = biased`
      (fn bias_equation => rewrite_tac [GSYM bias_equation]) >>
    Cases_on `exponent + 1023 < 0` >> simp[] >>
    intLib.ARITH_TAC) >>
  qspecl_then [`roundTiesToEven`, `value < 0`, `exponent`, `mantissa`]
    mp_tac fp64_round_quantize_int_fields >>
  asm_simp_tac std_ss [LET_THM, binary_ieeeTheory.rounding_case_def] >>
  asm_simp_tac std_ss [integer_access_nonnegative_zero,
    realTheory.real_gt, EVAL ``(1w : word1) = 1w``,
    EVAL ``(0w : word1) = 1w``] >>
  pairarg_tac >>
  qmatch_asmsub_rename_tac
    `(if _ then _ else _ : int # int) = (result_exponent, result_mantissa)` >>
  asm_simp_tac std_ss [LET_THM] >> strip_tac >>
  asm_simp_tac std_ss [pairTheory.UNCURRY, pairTheory.PAIR] >>
  qspecl_then [`biased`, `lower`,
    `1 / 2 < error ∨ error = 1 / 2 ∧ ODD (Num lower)`]
    mp_tac fp64_round_fields_nonnegative >>
  asm_simp_tac std_ss [LET_THM, EVAL ``(2 : num) ** 52``,
    EVAL ``(2 : num) ** 53``, pairTheory.FST, pairTheory.SND] >> strip_tac >>
  `(scaled <> real_of_int lower) ⇔ error <> 0` by (
    qpat_x_assum `scaled - real_of_int lower = error` mp_tac >>
    rpt (pop_assum kall_tac) >> RealField.REAL_ARITH_TAC) >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [integer_subrange_nonnegative_low, fp64_pack_fields,
     EVAL ``dimindex(:11)``, EVAL ``dimindex(:52)``,
     integerTheory.int_ge] >>
  qpat_x_assum `asl_sys_regs_ok asl` mp_tac >>
  rpt (pop_assum kall_tac) >> strip_tac >>
  Cases_on `biased = 0 ∧ error <> 0` >>
  Cases_on `2047 <= result_exponent` >>
  Cases_on `error = 0` >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPInfinity64, FPProcessException_zero, asl_sys_regs_ok_write_FPSR,
     SIMP_RULE (srw_ss()) [FPSR_ref_def] asl_sys_regs_ok_write_FPSR,
     sail2_state_monadTheory.try_catchS_def,
     sail2_state_monadTheory.throwS_def,
     bindS, seqS, returnS, asl_reg_rws, FPSR_ref_def] >>
  gvs[] >>
  `(λreg. if reg = "FPSR" then asl.regstate.bitvector_32_dec_reg "FPSR"
     else asl.regstate.bitvector_32_dec_reg reg) =
   asl.regstate.bitvector_32_dec_reg` by (
    simp_tac std_ss [FUN_EQ_THM] >> qx_gen_tac `reg` >>
    Cases_on `reg = "FPSR"` >> simp[]) >>
  simp[]
QED

Resume FPRound64_algorithm[Zero]:
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [armv86aTheory.FPRound_def, FPRoundBase_def, asl_fp64_rounding_def,
       EVAL ``update_vec_dec (0w : word32) 26 (Bit (0w : word1))``,
       EVAL ``(vec_of_bits [access_vec_dec (0w : word32) 24] : word1)``,
       EVAL ``(vec_of_bits [access_vec_dec (0w : word32) 11] : word1)``,
       preludeTheory.undefined_bitvector_def, preludeTheory.undefined_real_def,
       preludeTheory.undefined_int_def,
       sail2_state_monadTheory.undefined_boolS_def,
       sail2_state_monadTheory.choose_boolS_def,
       sail2_state_monadTheory.chooseS_def,
       sail2_state_monadTheory.assert_expS_def,
       sail2_state_monadTheory.liftRS_def,
       sail2_state_monadTheory.catch_early_returnS_def,
       sail2_state_monadTheory.early_returnS_def,
       sail2_state_monadTheory.try_catchS_def,
       sail2_state_monadTheory.throwS_def,
       bindS, seqS, returnS, LET_THM, wordsTheory.w2w_id,
       realTheory.REAL_SUB_LZERO, realTheory.real_ge,
       EVAL ``realFromFrac 0 10``, EVAL ``realFromFrac 5 10``,
       EVAL ``realFromFrac 10 10``, EVAL ``realFromFrac 20 10``] >>
  `(((if value < 0 then 1w else 0w) : word1) = 1w ⇔ value < 0) ∧
   (((if value < 0 then 1w else 0w) : word1) = 0w ⇔ ¬(value < 0))` by (
    Cases_on `value < 0` >> simp[]) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  asm_simp_tac std_ss [LET_THM] >>
  asm_simp_tac std_ss
    [fp64_biased_max, realPowInteger_two, fp64_pow2_of_num,
     binary_ieeeTheory.rounding_case_def, LET_THM] >>
  qabbrev_tac `biased = if exponent + 1023 < 0 then 0 else exponent + 1023` >>
  qabbrev_tac `scaled =
    (if biased = 0 then mantissa / fp64_pow2 (-1022 - exponent)
     else mantissa) * 2 pow 52` >>
  qabbrev_tac `lower : int = flr scaled` >>
  qabbrev_tac `error = scaled - real_of_int lower` >>
  qpat_x_assum `Abbrev (biased = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (scaled = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (lower = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (error = _)`
    (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qspecl_then [`exponent`, `mantissa`] mp_tac fp64_quantize_floor >>
  asm_simp_tac std_ss [LET_THM] >> strip_tac >>
  `0 <= lower` by (
    qpat_x_assum `(&Num lower : int) = lower`
      (fn cast => once_rewrite_tac [GSYM cast]) >> simp[]) >>
  `0 <= biased` by (
    qpat_x_assum `(if exponent + 1023 < 0 then 0 else exponent + 1023) = biased`
      (fn bias_equation => rewrite_tac [GSYM bias_equation]) >>
    Cases_on `exponent + 1023 < 0` >> simp[] >>
    intLib.ARITH_TAC) >>
  qspecl_then [`roundTowardZero`, `value < 0`, `exponent`, `mantissa`]
    mp_tac fp64_round_quantize_int_fields >>
  asm_simp_tac std_ss [LET_THM, binary_ieeeTheory.rounding_case_def] >>
  asm_simp_tac std_ss [integer_access_nonnegative_zero,
    realTheory.real_gt, EVAL ``(1w : word1) = 1w``,
    EVAL ``(0w : word1) = 1w``] >>
  asm_simp_tac std_ss [LET_THM] >> strip_tac >>
  asm_simp_tac std_ss [pairTheory.UNCURRY, pairTheory.PAIR] >>
  `(scaled <> real_of_int lower) ⇔ error <> 0` by (
    qpat_x_assum `scaled - real_of_int lower = error` mp_tac >>
    rpt (pop_assum kall_tac) >> RealField.REAL_ARITH_TAC) >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [integer_subrange_nonnegative_low, fp64_pack_fields,
     EVAL ``dimindex(:11)``, EVAL ``dimindex(:52)``,
     integerTheory.int_ge] >>
  qpat_x_assum `asl_sys_regs_ok asl` mp_tac >>
  rpt (pop_assum kall_tac) >> strip_tac >>
  Cases_on `value < 0` >>
  Cases_on `biased = 0 ∧ error <> 0` >>
  Cases_on `2047 <= biased` >>
  Cases_on `error = 0` >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPInfinity64, FPMaxNormal64, FPProcessException_zero, asl_sys_regs_ok_write_FPSR,
     SIMP_RULE (srw_ss()) [FPSR_ref_def] asl_sys_regs_ok_write_FPSR,
     sail2_state_monadTheory.try_catchS_def,
     sail2_state_monadTheory.throwS_def,
     bindS, seqS, returnS, asl_reg_rws, FPSR_ref_def] >>
  gvs[] >>
  `(λreg. if reg = "FPSR" then asl.regstate.bitvector_32_dec_reg "FPSR"
     else asl.regstate.bitvector_32_dec_reg reg) =
   asl.regstate.bitvector_32_dec_reg` by (
    simp_tac std_ss [FUN_EQ_THM] >> qx_gen_tac `reg` >>
    Cases_on `reg = "FPSR"` >> simp[]) >>
  simp[]
QED

Finalise FPRound64_algorithm;

Theorem FPRound64:
  !value mode asl.
    value <> 0 /\ asl_sys_regs_ok asl ==>
    let (flags, result) =
      (float_round_with_flags mode (value < 0) value : flags # (52,11) float) in
    FPRound 64 value 0w (asl_fp64_rounding mode) asl =
      returnS (float_to_fp64 result)
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate ||
           (if flags.Underflow_BeforeRounding then 8w else 0w) ||
           (if flags.Overflow then 4w else 0w) ||
           (if flags.Precision then 16w else 0w)) asl.regstate)
Proof
  qx_genl_tac [`value`, `mode`, `asl`] \\ strip_tac
  \\ `0 < abs value` by simp []
  \\ namedCases_on
       `sail2_values$while (0 : int, abs value)
          (\(e, m). m < 1) (\(e, m). (e - 1, m * 2))`
       ["initial_exponent initial_mantissa"]
  \\ namedCases_on
       `sail2_values$while (initial_exponent, initial_mantissa)
          (\(e, m). 2 <= m) (\(e, m). (e + 1, m / 2))`
       ["exponent mantissa"]
  \\ `1 <= mantissa /\ mantissa < 2 /\
       abs value = mantissa * fp64_pow2 exponent` by (
    qspec_then `abs value` mp_tac FPRound_normalize
    \\ asm_simp_tac std_ss
         [LET_THM, pairTheory.FST, pairTheory.SND, realPowInteger_two])
  \\ `(if value < 0 then -(mantissa * fp64_pow2 exponent)
        else mantissa * fp64_pow2 exponent) = value` by (
    qpat_assum `abs value = mantissa * fp64_pow2 exponent` mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ Cases_on `value < 0`
    \\ asm_simp_tac std_ss
         [realTheory.abs, GSYM realTheory.REAL_NOT_LT, realTheory.REAL_NEGNEG]
    \\ RealField.REAL_ARITH_TAC)
  \\ namedCases_on
       `(float_round_with_flags mode (value < 0) value : flags # (52,11) float)`
       ["round_flags rounded_value"]
  \\ asm_simp_tac std_ss [LET_THM]
  \\ sg `fp64_round_quantize mode (value < 0) (exponent, mantissa) =
       (round_flags.Underflow_BeforeRounding, round_flags.Overflow, round_flags.Precision,
        float_to_fp64 rounded_value)`
  >- (
    qspecl_then [`mode`, `value < 0`, `exponent`, `mantissa`]
         mp_tac fp64_round_quantize_flags
    \\ asm_simp_tac std_ss [LET_THM])
  \\ qspecl_then [`value`, `mode`, `asl`] mp_tac FPRound64_algorithm
  \\ asm_simp_tac std_ss [LET_THM]
QED

Theorem FPCR_rounding_bits_cases:
  ∀fpcr : word32.
    fpcr && ~0x00C00000w = 0w ⇒
    fpcr = 0w ∨ fpcr = 0x00400000w ∨
    fpcr = 0x00800000w ∨ fpcr = 0x00C00000w
Proof
  gen_tac >> blastLib.BBLAST_TAC
QED

Theorem FPProcessException_rounding_bits:
  ∀exception fpcr.
    fpcr && ~0x00C00000w = 0w ⇒
    FPProcessException exception fpcr = FPProcessException exception 0w
Proof
  qx_genl_tac [`exception`, `fpcr`] >> strip_tac >>
  drule FPCR_rounding_bits_cases >> strip_tac >> gvs[] >>
  Cases_on `exception` >>
  simp[FPProcessException_def, vec_of_bits_access_vec_dec_single,
       Excl "access_vec_dec_def"]
QED

Theorem FPRoundingMode_agrees:
  ∀l3 : arm8_state.
    armv86a$FPRoundingMode l3.FPCR =
      returnS (asl_fp64_rounding (arm8$FPRoundingMode l3))
Proof
  qx_gen_tac `l3` >>
  simp[armv86aTheory.FPRoundingMode_def, arm8Theory.FPRoundingMode_def,
       asl_word_rws] >>
  wordsLib.Cases_on_word_value `((23 >< 22) l3.FPCR : word2)` >>
  simp[FPDecodeRounding_def, asl_fp64_rounding_def]
QED

Theorem FPRound64_rounding_bits:
  ∀fpcr value mode.
    fpcr && ~0x00C00000w = 0w ⇒
    (FPRound 64 value fpcr mode : regstate sequential_state -> word64 res) =
      FPRound 64 value 0w mode
Proof
  qx_genl_tac [`fpcr`, `value`, `mode`] >> strip_tac >>
  drule FPCR_rounding_bits_cases >> strip_tac >> gvs[] >>
  simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [armv86aTheory.FPRound_def, FPRoundBase_def, LET_THM,
     EVAL ``update_vec_dec (0w : word32) 26 (Bit (0w : word1))``,
     EVAL ``update_vec_dec (0x00400000w : word32) 26 (Bit (0w : word1))``,
     EVAL ``update_vec_dec (0x00800000w : word32) 26 (Bit (0w : word1))``,
     EVAL ``update_vec_dec (0x00C00000w : word32) 26 (Bit (0w : word1))``,
     FPProcessException_rounding_bits, vec_of_bits_access_vec_dec_single,
     EVAL ``(0x00400000w : word32) && ~0x00C00000w = 0w``,
     EVAL ``(0x00800000w : word32) && ~0x00C00000w = 0w``,
     EVAL ``(0x00C00000w : word32) && ~0x00C00000w = 0w``]
QED

Theorem FPUnpack64_rounding_bits:
  ∀fpcr : word32. ∀bits : word64.
    fpcr && ~0x00C00000w = 0w ⇒
    FPUnpack bits fpcr = FPUnpack bits 0w
Proof
  qx_genl_tac [`fpcr`, `bits`] >> strip_tac >>
  drule FPCR_rounding_bits_cases >> strip_tac >> gvs[] >>
  simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPUnpack_def, FPUnpackBase_def, LET_THM,
     EVAL ``update_vec_dec (0w : word32) 26 (Bit (0w : word1))``,
     EVAL ``update_vec_dec (0x00400000w : word32) 26 (Bit (0w : word1))``,
     EVAL ``update_vec_dec (0x00800000w : word32) 26 (Bit (0w : word1))``,
     EVAL ``update_vec_dec (0x00C00000w : word32) 26 (Bit (0w : word1))``,
     FPProcessException_rounding_bits, vec_of_bits_access_vec_dec_single,
     EVAL ``(0x00400000w : word32) && ~0x00C00000w = 0w``,
     EVAL ``(0x00800000w : word32) && ~0x00C00000w = 0w``,
     EVAL ``(0x00C00000w : word32) && ~0x00C00000w = 0w``]
QED




Theorem float_to_real_signed_abs:
  !fp : ('t, 'w) float.
    float_to_real fp =
      if fp.Sign = 1w then -abs (float_to_real fp)
      else abs (float_to_real fp)
Proof
  gen_tac >>
  Cases_on_word_value `fp.Sign` >>
  rw [binary_ieeeTheory.float_to_real_def] >>
  simp [ABS_MUL, ABS_INV, GSYM POW_ABS, REAL_LE_ADD,
        REAL_LE_MUL, REAL_LE_DIV, GSYM REAL_NEG_MINUS1,
        GSYM REAL_NEG_LMUL] >>
  simp [ABS_REDUCE, REAL_LE_DIV, REAL_LE_ADD]
QED

Theorem float_to_real_sign_nonzero:
  !fp : ('t, 'w) float.
    float_to_real fp <> 0 ==>
    (float_to_real fp < 0 <=> fp.Sign = 1w)
Proof
  gen_tac >> strip_tac >>
  `0 < abs (float_to_real fp)` by simp [GSYM ABS_NZ] >>
  qspec_then `fp` mp_tac float_to_real_signed_abs >>
  Cases_on `fp.Sign = 1w` >>
  asm_simp_tac std_ss [] >>
  REAL_ASM_ARITH_TAC
QED

Theorem float_product_sign_nonzero:
  !left : ('t, 'w) float. !right : ('u, 'v) float.
    float_to_real left <> 0 /\ float_to_real right <> 0 ==>
    (float_to_real left * float_to_real right < 0 <=>
      left.Sign <> right.Sign)
Proof
  rpt gen_tac >> strip_tac >>
  `(float_to_real left < 0 <=> left.Sign = 1w) /\
   (float_to_real right < 0 <=> right.Sign = 1w)` by
    simp [float_to_real_sign_nonzero] >>
  once_rewrite_tac [GSYM REAL_NOT_LE] >>
  rewrite_tac [REAL_MUL_SIGN] >>
  Cases_on_word_value `left.Sign` >>
  Cases_on_word_value `right.Sign` >>
  fs [] >>
  REAL_ASM_ARITH_TAC
QED

Theorem float_quotient_sign_nonzero:
  !left : ('t, 'w) float. !right : ('u, 'v) float.
    float_to_real left <> 0 /\ float_to_real right <> 0 ==>
    (float_to_real left / float_to_real right < 0 <=>
      left.Sign <> right.Sign)
Proof
  rpt gen_tac >> strip_tac >>
  `(float_to_real left < 0 <=> left.Sign = 1w) /\
   (float_to_real right < 0 <=> right.Sign = 1w)` by
    simp [float_to_real_sign_nonzero] >>
  once_rewrite_tac [GSYM REAL_NOT_LE] >>
  rewrite_tac [real_div, REAL_MUL_SIGN, REAL_LE_INV_EQ,
    REAL_ARITH ``(x : real) <= 0 <=> ~(0 < x)``, REAL_LT_INV_EQ] >>
  Cases_on_word_value `left.Sign` >>
  Cases_on_word_value `right.Sign` >>
  fs [] >>
  REAL_ASM_ARITH_TAC
QED

Theorem float_mul_finite_nonzero_real_sign:
  !mode. !left right : ('t, 'w) float. !left_real right_real.
    float_value left = Float left_real /\
    float_value right = Float right_real /\
    left_real <> 0 /\ right_real <> 0 ==>
    float_mul mode left right =
      float_round_with_flags mode (left_real * right_real < 0)
        (left_real * right_real)
Proof
  rpt gen_tac >> strip_tac >>
  `left_real = float_to_real left /\ right_real = float_to_real right` by
    fs [binary_ieeeTheory.float_value_def, AllCaseEqs()] >>
  fs [] >>
  simp [binary_ieeeTheory.float_mul_finite, float_product_sign_nonzero]
QED

Theorem float_div_finite_nonzero_real_sign:
  !mode. !left right : ('t, 'w) float. !left_real right_real.
    float_value left = Float left_real /\
    float_value right = Float right_real /\
    left_real <> 0 /\ right_real <> 0 ==>
    float_div mode left right =
      float_round_with_flags mode (left_real / right_real < 0)
        (left_real / right_real)
Proof
  rpt gen_tac >> strip_tac >>
  `left_real = float_to_real left /\ right_real = float_to_real right` by
    fs [binary_ieeeTheory.float_value_def, AllCaseEqs()] >>
  fs [] >>
  simp [float_quotient_sign_nonzero] >>
  qspecl_then [`mode`, `left`, `right`, `left_real`, `right_real`]
    mp_tac binary_ieeeTheory.float_div_finite >>
  asm_simp_tac std_ss []
QED

Theorem float_sqrt_finite_positive_real_sign:
  !mode. !fp : ('t, 'w) float. !number.
    float_value fp = Float number /\ 0 < number ==>
    float_sqrt mode fp =
      float_round_with_flags mode (sqrt number < 0) (sqrt number)
Proof
  rpt gen_tac >> strip_tac >>
  `number = float_to_real fp` by fs [binary_ieeeTheory.float_value_def, AllCaseEqs()] >>
  `float_to_real fp <> 0` by REAL_ASM_ARITH_TAC >>
  `fp.Sign <> 1w` by (
    qspec_then `fp` mp_tac float_to_real_sign_nonzero >>
    asm_simp_tac std_ss [] >> REAL_ASM_ARITH_TAC) >>
  `fp.Sign = 0w` by (Cases_on_word_value `fp.Sign` >> gvs []) >>
  `~(sqrt number < 0)` by (
    qspec_then `number` mp_tac SQRT_POS_LT >>
    asm_simp_tac std_ss [] >> REAL_ASM_ARITH_TAC) >>
  fs [] >> simp [binary_ieeeTheory.float_sqrt_def]
QED

Theorem float_round_zero:
  !mode negative.
    (float_round mode negative 0 : ('t, 'w) float) =
      if negative then float_minus_zero (:'t # 'w)
      else float_plus_zero (:'t # 'w)
Proof
  rpt gen_tac >>
  simp [binary_ieeeTheory.float_round_def, LET_THM, binary_ieeeTheory.float_is_zero_to_real, binary_ieeeTheory.float_to_real_round0]
QED

Theorem float_round_with_flags_zero:
  !mode negative.
    (float_round_with_flags mode negative 0 : flags # ('t, 'w) float) =
      (clear_flags, if negative then float_minus_zero (:'t # 'w)
                    else float_plus_zero (:'t # 'w))
Proof
  rpt gen_tac >>
  Cases_on `negative` >>
  simp [binary_ieeeTheory.float_round_with_flags_def, float_round_zero, LET_THM, binary_ieeeTheory.float_values,
        binary_ieeeTheory.clear_flags_def, binary_ieeeTheory.zero_lt_twopow, GSYM REAL_NOT_LT]
QED

Theorem float_mul_finite_zero:
  !mode. !left right : ('t, 'w) float. !left_real right_real.
    float_value left = Float left_real /\
    float_value right = Float right_real /\
    (left_real = 0 \/ right_real = 0) ==>
    float_mul mode left right =
      (clear_flags, if left.Sign <> right.Sign then
         float_minus_zero (:'t # 'w) else float_plus_zero (:'t # 'w))
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`mode`, `left`, `right`, `left_real`, `right_real`]
    mp_tac binary_ieeeTheory.float_mul_finite >>
  gvs [float_round_with_flags_zero]
QED

Theorem float_sqrt_finite_zero:
  !mode. !fp : ('t, 'w) float.
    float_value fp = Float 0 ==>
    float_sqrt mode fp = (clear_flags, fp)
Proof
  rpt gen_tac >> strip_tac >>
  fs [GSYM binary_ieeeTheory.float_is_zero_float_value_EQ0, binary_ieeeTheory.float_sets,
      pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
  simp [binary_ieeeTheory.float_sqrt_def, binary_ieeeTheory.float_values, binary_ieeeTheory.float_components,
        float_round_with_flags_zero, SQRT_0]
QED

Theorem FPUnpack64_finite:
  float_value (fp64_to_float bits) = Float number ==>
    FPUnpack (bits : word64) 0w =
      returnS ((if number = 0 then FPType_Zero else FPType_Nonzero),
        (fp64_to_float bits).Sign, number)
Proof
  strip_tac >>
  asm_simp_tac std_ss
    [SIMP_RULE std_ss [LET_THM] FPUnpack64,
     binary_ieeeTheory.float_is_signalling_def,
     binary_ieeeTheory.float_is_nan_def,
     binary_ieeeTheory.float_is_infinite_def,
     binary_ieeeTheory.float_is_zero_def,
     binary_ieeeTheory.float_value_case_def]
QED

Theorem FPUnpack64_infinite:
  !bits : word64.
    float_value (fp64_to_float bits) = Infinity ==>
    FPUnpack bits 0w =
      returnS (FPType_Infinity, (fp64_to_float bits).Sign,
        if (fp64_to_float bits).Sign = 1w then -(2 pow 1000000)
        else 2 pow 1000000)
Proof
  qx_gen_tac `bits` \\ strip_tac
  \\ asm_simp_tac std_ss
       [SIMP_RULE std_ss [LET_THM] FPUnpack64,
        binary_ieeeTheory.float_is_signalling_def,
        binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.float_is_infinite_def,
        binary_ieeeTheory.float_is_zero_def,
        binary_ieeeTheory.float_value_case_def]
QED

Theorem float_to_real_difference_min_ulp:
  !left : ('t,'w) float. !right : ('t,'w) float.
    float_to_real left <> float_to_real right ==>
    ulp (:'t # 'w) <= abs (float_to_real left - float_to_real right)
Proof
  qx_genl_tac [`left`, `right`] \\ strip_tac
  \\ Cases_on `exponent_boundary right left`
  >- (
    `~exponent_boundary left right` by (
      fs [binary_ieeeTheory.exponent_boundary_def] \\ decide_tac)
    \\ qspecl_then [`right`, `left`] mp_tac binary_ieeeTheory.diff_float_ULP
    \\ asm_simp_tac std_ss [realTheory.ABS_SUB, GSYM realTheory.REAL_NOT_LE]
    \\ metis_tac [binary_ieeeTheory.ulp_lt_ULP, realTheory.REAL_LE_TRANS])
  \\ qspecl_then [`left`, `right`] mp_tac binary_ieeeTheory.diff_float_ULP
  \\ asm_simp_tac std_ss []
  \\ metis_tac [binary_ieeeTheory.ulp_lt_ULP, realTheory.REAL_LE_TRANS]
QED

Theorem float_to_real_sum_min_ulp:
  !left : ('t,'w) float. !right : ('t,'w) float.
    float_to_real left + float_to_real right <> 0 ==>
    ulp (:'t # 'w) <= abs (float_to_real left + float_to_real right)
Proof
  qx_genl_tac [`left`, `right`] \\ strip_tac
  \\ qspecl_then [`left`, `float_negate right`]
       mp_tac float_to_real_difference_min_ulp
  \\ simp [binary_ieeeTheory.float_to_real_negate]
  \\ RealField.REAL_ASM_ARITH_TAC
QED

Theorem closest_such_is_closest:
  !allowed : ('t,'w) float set. !predicate source.
    allowed <> {} ==>
    is_closest allowed source (closest_such predicate allowed source)
Proof
  qx_genl_tac [`allowed`, `predicate`, `source`] \\ strip_tac
  \\ simp_tac std_ss [binary_ieeeTheory.closest_such_def]
  \\ SELECT_ELIM_TAC \\ conj_tac
  >- metis_tac [binary_ieeeTheory.is_closest_exists]
  \\ simp_tac std_ss []
QED

Theorem closest_such_nonzero:
  !allowed : ('t,'w) float set. !predicate source witness.
    witness IN allowed /\
    abs (float_to_real witness - source) < abs source ==>
    ~float_is_zero (closest_such predicate allowed source)
Proof
  qx_genl_tac [`allowed`, `predicate`, `source`, `witness`] \\ strip_tac
  \\ `allowed <> {}` by metis_tac [pred_setTheory.NOT_IN_EMPTY]
  \\ qspecl_then [`allowed`, `predicate`, `source`]
       mp_tac closest_such_is_closest
  \\ asm_simp_tac std_ss [binary_ieeeTheory.is_closest_def] \\ strip_tac
  \\ spose_not_then assume_tac
  \\ `float_to_real (closest_such predicate allowed source) = 0` by
    fs [binary_ieeeTheory.float_is_zero_to_real]
  \\ qpat_x_assum `!comparison. _` (qspec_then `witness` mp_tac)
  \\ asm_simp_tac std_ss [realTheory.REAL_SUB_LZERO, realTheory.ABS_NEG]
  \\ RealField.REAL_ASM_ARITH_TAC
QED

Theorem signed_minimum_closer:
  !source.
    ulp (:'t # 'w) <= abs source ==>
    let candidate = if source < 0 then float_minus_min (:'t # 'w)
                    else float_plus_min (:'t # 'w) in
    float_is_finite candidate /\
    abs (float_to_real candidate) <= abs source /\
    (source < 0 ==> source <= float_to_real candidate) /\
    (~(source < 0) ==> float_to_real candidate <= source) /\
    abs (float_to_real candidate - source) < abs source
Proof
  qx_gen_tac `source` \\ strip_tac
  \\ Cases_on `source < 0`
  \\ asm_simp_tac std_ss
       [LET_THM, binary_ieeeTheory.min_properties, binary_ieeeTheory.float_minus_min_def,
        binary_ieeeTheory.float_to_real_negate, binary_ieeeTheory.float_is_finite_float_negate, GSYM binary_ieeeTheory.ulp]
  \\ `0 < ulp (:'t # 'w)` by simp []
  \\ RealField.REAL_ASM_ARITH_TAC
QED

Theorem closest_such_nonzero_allowed:
  !allowed : ('t,'w) float set. !predicate source.
    allowed <> {} /\
    (!candidate. candidate IN allowed ==> ~float_is_zero candidate) ==>
    ~float_is_zero (closest_such predicate allowed source)
Proof
  qx_genl_tac [`allowed`, `predicate`, `source`] \\ strip_tac
  \\ metis_tac [closest_such_is_closest, binary_ieeeTheory.is_closest_def]
QED

Theorem round_minimum_nonzero:
  !mode source.
    ulp (:52 # 11) <= abs source ==>
    ~float_is_zero (round mode source : (52,11) float)
Proof
  qx_genl_tac [`mode`, `source`] \\ strip_tac
  \\ qspec_then `source` mp_tac
       (INST_TYPE [``:'t`` |-> ``:52``, ``:'w`` |-> ``:11``]
          signed_minimum_closer)
  \\ asm_simp_tac std_ss [LET_THM] \\ strip_tac
  \\ Cases_on `mode`
  >- (
    rw [binary_ieeeTheory.round_def, LET_THM]
    \\ irule closest_such_nonzero
    \\ qexists_tac `if source < 0 then float_minus_min (:52 # 11)
                    else float_plus_min (:52 # 11)`
    \\ asm_simp_tac std_ss [pred_setTheory.SPECIFICATION])
  >- (
    rw [binary_ieeeTheory.round_def, LET_THM, binary_ieeeTheory.closest_def]
    \\ Cases_on `source < 0`
    >- (
      irule closest_such_nonzero
      \\ qexists_tac `if source < 0 then float_minus_min (:52 # 11)
                      else float_plus_min (:52 # 11)`
      \\ fs [pred_setTheory.GSPECIFICATION, realTheory.real_ge])
    >- (
      irule closest_such_nonzero_allowed \\ conj_tac
      >- (
        qx_gen_tac `candidate`
        \\ simp_tac std_ss [pred_setTheory.GSPECIFICATION, realTheory.real_ge]
        \\ strip_tac \\ spose_not_then assume_tac
        \\ `float_to_real candidate = 0` by fs [binary_ieeeTheory.float_is_zero_to_real]
        \\ `0 < ulp (:52 # 11)` by simp []
        \\ RealField.REAL_ASM_ARITH_TAC)
      \\ rewrite_tac [GSYM pred_setTheory.MEMBER_NOT_EMPTY]
      \\ qexists_tac `float_top (:52 # 11)`
      \\ simp [pred_setTheory.GSPECIFICATION, GSYM binary_ieeeTheory.largest_is_top, realTheory.real_ge]
      \\ RealField.REAL_ASM_ARITH_TAC))
  >- (
    rw [binary_ieeeTheory.round_def, LET_THM, binary_ieeeTheory.closest_def]
    \\ Cases_on `source < 0`
    >- (
      irule closest_such_nonzero_allowed \\ conj_tac
      >- (
        qx_gen_tac `candidate`
        \\ simp_tac std_ss [pred_setTheory.GSPECIFICATION]
        \\ strip_tac \\ spose_not_then assume_tac
        \\ `float_to_real candidate = 0` by fs [binary_ieeeTheory.float_is_zero_to_real]
        \\ RealField.REAL_ASM_ARITH_TAC)
      \\ rewrite_tac [GSYM pred_setTheory.MEMBER_NOT_EMPTY]
      \\ qexists_tac `float_bottom (:52 # 11)`
      \\ simp [pred_setTheory.GSPECIFICATION, binary_ieeeTheory.float_bottom_def,
               binary_ieeeTheory.float_to_real_negate, GSYM binary_ieeeTheory.largest_is_top, realTheory.real_ge]
      \\ RealField.REAL_ASM_ARITH_TAC)
    >- (
      irule closest_such_nonzero
      \\ qexists_tac `if source < 0 then float_minus_min (:52 # 11)
                      else float_plus_min (:52 # 11)`
      \\ fs [pred_setTheory.GSPECIFICATION]))
  >- (
    rw [binary_ieeeTheory.round_def, LET_THM, binary_ieeeTheory.closest_def]
    \\ irule closest_such_nonzero
    \\ qexists_tac `if source < 0 then float_minus_min (:52 # 11)
                    else float_plus_min (:52 # 11)`
    \\ asm_simp_tac std_ss [pred_setTheory.GSPECIFICATION])
QED

Theorem float_round_sign_irrelevant:
  !mode first_sign second_sign source.
    ulp (:52 # 11) <= abs source ==>
    (float_round mode first_sign source : (52,11) float) =
    float_round mode second_sign source
Proof
  qx_genl_tac [`mode`, `first_sign`, `second_sign`, `source`] \\ strip_tac
  \\ qspecl_then [`mode`, `source`] mp_tac round_minimum_nonzero
  \\ asm_simp_tac std_ss [] \\ strip_tac
  \\ asm_simp_tac std_ss [binary_ieeeTheory.float_round_def, LET_THM]
QED

Theorem float_round_exponent_sign_irrelevant:
  !mode to_neg source.
    (float_round mode to_neg source : ('t,'w) float).Exponent =
    (float_round mode F source : ('t,'w) float).Exponent
Proof
  qx_genl_tac [`mode`, `to_neg`, `source`]
  \\ Cases_on `to_neg`
  \\ simp [binary_ieeeTheory.float_round_def, LET_THM, binary_ieeeTheory.float_minus_zero, binary_ieeeTheory.float_plus_zero_def]
  \\ Cases_on `float_is_zero (round mode source : ('t,'w) float)`
  \\ simp []
QED

Theorem float_round_with_flags_sign_irrelevant:
  !mode first_sign second_sign source.
    ulp (:52 # 11) <= abs source ==>
    (float_round_with_flags mode first_sign source : flags # (52,11) float) =
    float_round_with_flags mode second_sign source
Proof
  qx_genl_tac [`mode`, `first_sign`, `second_sign`, `source`] \\ strip_tac
  \\ qspecl_then [`mode`, `first_sign`, `second_sign`, `source`]
       mp_tac float_round_sign_irrelevant
  \\ asm_simp_tac std_ss [] \\ strip_tac
  \\ asm_simp_tac (srw_ss())
       [binary_ieeeTheory.float_round_with_flags_def, LET_THM, float_round_exponent_sign_irrelevant]
QED

Theorem float_add_finite_nonzero_real_sign:
  !mode. !left : (52,11) float. !right : (52,11) float.
  !left_real right_real.
    float_value left = Float left_real /\
    float_value right = Float right_real /\
    left_real + right_real <> 0 ==>
    float_add mode left right =
      float_round_with_flags mode (left_real + right_real < 0)
        (left_real + right_real)
Proof
  qx_genl_tac [`mode`, `left`, `right`, `left_real`, `right_real`] \\ strip_tac
  \\ `left_real = float_to_real left /\ right_real = float_to_real right` by
    fs [binary_ieeeTheory.float_value_def, AllCaseEqs()]
  \\ fs []
  \\ qspecl_then
       [`mode`, `left`, `right`, `float_to_real left`, `float_to_real right`]
       mp_tac binary_ieeeTheory.float_add_finite
  \\ asm_simp_tac std_ss [] \\ disch_then SUBST1_TAC
  \\ irule float_round_with_flags_sign_irrelevant
  \\ irule float_to_real_sum_min_ulp
  \\ asm_simp_tac std_ss []
QED

Theorem float_sub_finite_nonzero_real_sign:
  !mode. !left : (52,11) float. !right : (52,11) float.
  !left_real right_real.
    float_value left = Float left_real /\
    float_value right = Float right_real /\
    left_real - right_real <> 0 ==>
    float_sub mode left right =
      float_round_with_flags mode (left_real - right_real < 0)
        (left_real - right_real)
Proof
  qx_genl_tac [`mode`, `left`, `right`, `left_real`, `right_real`] \\ strip_tac
  \\ `left_real = float_to_real left /\ right_real = float_to_real right` by
    fs [binary_ieeeTheory.float_value_def, AllCaseEqs()]
  \\ fs []
  \\ qspecl_then
       [`mode`, `left`, `right`, `float_to_real left`, `float_to_real right`]
       mp_tac binary_ieeeTheory.float_sub_finite
  \\ asm_simp_tac std_ss [] \\ disch_then SUBST1_TAC
  \\ irule float_round_with_flags_sign_irrelevant
  \\ irule float_to_real_difference_min_ulp
  \\ RealField.REAL_ASM_ARITH_TAC
QED

Theorem FPMul64_finite_nonzero:
  !left : word64. !right : word64. !fpcr mode left_real right_real asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    armv86a$FPRoundingMode fpcr = returnS (asl_fp64_rounding mode) /\
    float_value (fp64_to_float left) = Float left_real /\
    float_value (fp64_to_float right) = Float right_real /\
    left_real <> 0 /\ right_real <> 0 ==>
    let (round_flags, result) =
      float_mul mode (fp64_to_float left) (fp64_to_float right) in
    FPMul left right fpcr asl =
      returnS (float_to_fp64 result)
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate ||
           (if round_flags.Underflow_BeforeRounding then 8w else 0w) ||
           (if round_flags.Overflow then 4w else 0w) ||
           (if round_flags.Precision then 16w else 0w)) asl.regstate)
Proof
  rpt gen_tac >> strip_tac >>
  `float_mul mode (fp64_to_float left) (fp64_to_float right) =
    float_round_with_flags mode (left_real * right_real < 0)
      (left_real * right_real)` by (
    qspecl_then [`mode`, `fp64_to_float left`, `fp64_to_float right`,
      `left_real`, `right_real`] mp_tac float_mul_finite_nonzero_real_sign >>
    asm_simp_tac std_ss []) >>
  imp_res_tac FPUnpack64_finite >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPMul_def, FPUnpack64_rounding_bits, FPUnpack64_finite,
     FPProcessNaNs_def, FPRound__1_def, LET_THM,
     undefined_FPType_def, preludeTheory.undefined_bitvector_def,
     preludeTheory.undefined_real_def,
     sail2_state_monadTheory.undefined_boolS_def,
     sail2_state_monadTheory.choose_boolS_def,
     sail2_state_monadTheory.chooseS_def,
     sail2_stateTheory.internal_pickS_def,
     sail2_state_monadTheory.assert_expS_def,
     bindS, seqS, returnS, asl_word_rws] >>
  qspecl_then [`left_real * right_real`, `mode`, `asl`] mp_tac FPRound64 >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPRound64_rounding_bits, REAL_ENTIRE, LET_THM, returnS]
QED

Theorem FPDiv64_finite_nonzero:
  !left : word64. !right : word64. !fpcr mode left_real right_real asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    armv86a$FPRoundingMode fpcr = returnS (asl_fp64_rounding mode) /\
    float_value (fp64_to_float left) = Float left_real /\
    float_value (fp64_to_float right) = Float right_real /\
    left_real <> 0 /\ right_real <> 0 ==>
    let (round_flags, result) =
      float_div mode (fp64_to_float left) (fp64_to_float right) in
    FPDiv left right fpcr asl =
      returnS (float_to_fp64 result)
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate ||
           (if round_flags.Underflow_BeforeRounding then 8w else 0w) ||
           (if round_flags.Overflow then 4w else 0w) ||
           (if round_flags.Precision then 16w else 0w)) asl.regstate)
Proof
  rpt gen_tac >> strip_tac >>
  `float_div mode (fp64_to_float left) (fp64_to_float right) =
    float_round_with_flags mode (left_real / right_real < 0)
      (left_real / right_real)` by (
    qspecl_then [`mode`, `fp64_to_float left`, `fp64_to_float right`,
      `left_real`, `right_real`] mp_tac float_div_finite_nonzero_real_sign >>
    asm_simp_tac std_ss []) >>
  imp_res_tac FPUnpack64_finite >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPDiv_def, FPUnpack64_rounding_bits, FPUnpack64_finite,
     FPProcessNaNs_def, FPRound__1_def, LET_THM,
     undefined_FPType_def, preludeTheory.undefined_bitvector_def,
     preludeTheory.undefined_real_def,
     sail2_state_monadTheory.undefined_boolS_def,
     sail2_state_monadTheory.choose_boolS_def,
     sail2_state_monadTheory.chooseS_def,
     sail2_stateTheory.internal_pickS_def,
     sail2_state_monadTheory.assert_expS_def,
     bindS, seqS, returnS, asl_word_rws] >>
  qspecl_then [`left_real / right_real`, `mode`, `asl`] mp_tac FPRound64 >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPRound64_rounding_bits, real_div, REAL_ENTIRE,
     REAL_INV_EQ_0, LET_THM, returnS]
QED

fun fp_add_sub_round_tac asl_def =
  qx_genl_tac [`left`, `right`, `fpcr`, `rounding`, `left_real`, `right_real`]
  \\ strip_tac
  \\ `FPUnpack left fpcr = returnS
        ((if left_real = 0 then FPType_Zero else FPType_Nonzero),
         (fp64_to_float left).Sign, left_real)` by (
    asm_simp_tac std_ss [FPUnpack64_rounding_bits]
    \\ irule FPUnpack64_finite \\ asm_simp_tac std_ss [])
  \\ `FPUnpack right fpcr = returnS
        ((if right_real = 0 then FPType_Zero else FPType_Nonzero),
         (fp64_to_float right).Sign, right_real)` by (
    asm_simp_tac std_ss [FPUnpack64_rounding_bits]
    \\ irule FPUnpack64_finite \\ asm_simp_tac std_ss [])
  \\ Cases_on `left_real = 0`
  \\ Cases_on `right_real = 0`
  \\ fs []
  \\ asm_simp_tac std_ss [FUN_EQ_THM] \\ qx_gen_tac `asl`
  \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
       [asl_def, FPProcessNaNs_def, LET_THM,
        undefined_FPType_def, preludeTheory.undefined_bitvector_def,
        preludeTheory.undefined_real_def,
        sail2_state_monadTheory.undefined_boolS_def,
        sail2_state_monadTheory.choose_boolS_def,
        sail2_state_monadTheory.chooseS_def,
        sail2_stateTheory.internal_pickS_def,
        sail2_state_monadTheory.assert_expS_def,
        bindS, seqS, returnS, asl_word_rws, EVAL ``realFromFrac 0 10``];

Theorem FPAdd64_finite_nonzero_round:
  !left : word64. !right : word64. !fpcr rounding left_real right_real.
    fpcr && ~0x00C00000w = 0w /\
    armv86a$FPRoundingMode fpcr = returnS rounding /\
    float_value (fp64_to_float left) = Float left_real /\
    float_value (fp64_to_float right) = Float right_real /\
    left_real + right_real <> 0 ==>
    FPAdd left right fpcr = FPRound 64 (left_real + right_real) fpcr rounding
Proof
  fp_add_sub_round_tac FPAdd_def
QED

Theorem FPAdd64_finite_nonzero_result:
  !left : word64. !right : word64. !fpcr mode left_real right_real asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    armv86a$FPRoundingMode fpcr = returnS (asl_fp64_rounding mode) /\
    float_value (fp64_to_float left) = Float left_real /\
    float_value (fp64_to_float right) = Float right_real /\
    left_real + right_real <> 0 ==>
    let (round_flags, result) =
      float_add mode (fp64_to_float left) (fp64_to_float right) in
    FPAdd left right fpcr asl =
      returnS (float_to_fp64 result)
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate ||
           (if round_flags.Underflow_BeforeRounding then 8w else 0w) ||
           (if round_flags.Overflow then 4w else 0w) ||
           (if round_flags.Precision then 16w else 0w)) asl.regstate)
Proof
  qx_genl_tac [`left`, `right`, `fpcr`, `mode`, `left_real`, `right_real`, `asl`]
  \\ strip_tac
  \\ qspecl_then
       [`mode`, `fp64_to_float left`, `fp64_to_float right`, `left_real`, `right_real`]
       mp_tac float_add_finite_nonzero_real_sign
  \\ asm_simp_tac std_ss [] \\ disch_then SUBST1_TAC
  \\ qspecl_then
       [`left`, `right`, `fpcr`, `asl_fp64_rounding mode`, `left_real`, `right_real`]
       mp_tac FPAdd64_finite_nonzero_round
  \\ asm_simp_tac std_ss [] \\ disch_then SUBST1_TAC
  \\ qspecl_then [`left_real + right_real`, `mode`, `asl`] mp_tac FPRound64
  \\ asm_simp_tac std_ss [FPRound64_rounding_bits]
QED

Theorem FPZero64:
  FPZero 64 sign =
    returnS (machine_ieee$float_to_fp64
      (<| Sign := sign; Exponent := 0w; Significand := 0w |> : (52,11) float))
Proof
  rw [FUN_EQ_THM] >>
  simp [FPZero_def, seqS, returnS, asl_word_rws,
        machine_ieeeTheory.float_to_fp64_def] >>
  blastLib.BBLAST_TAC
QED

Theorem FPDefaultNaN64:
  FPDefaultNaN 64 = returnS (0x7FF8000000000000w : word64)
Proof
  rw [FUN_EQ_THM] >>
  simp [FPDefaultNaN_def, seqS, returnS, asl_word_rws]
QED

Theorem FPSR_write_read:
  !registers.
    FPSR_ref.write_to (FPSR_ref.read_from registers) registers = registers
Proof
  qx_gen_tac `registers`
  \\ simp [FPSR_ref_def]
  \\ `(\reg. if reg = "FPSR" then registers.bitvector_32_dec_reg "FPSR"
             else registers.bitvector_32_dec_reg reg) =
       registers.bitvector_32_dec_reg` by (
    simp_tac std_ss [FUN_EQ_THM] \\ qx_gen_tac `reg`
    \\ Cases_on `reg = "FPSR"`
    \\ asm_simp_tac std_ss [])
  \\ asm_simp_tac (srw_ss()) []
QED

Theorem FPSR_set_state_rel:
  !l3 asl value.
    state_rel l3 asl /\ asl_sys_regs_ok asl ==>
    state_rel (l3 with FPSR := value)
      (asl with regstate := FPSR_ref.write_to value asl.regstate) /\
    asl_sys_regs_ok
      (asl with regstate := FPSR_ref.write_to value asl.regstate)
Proof
  rpt gen_tac >> strip_tac >> state_rel_tac []
QED

Theorem real_of_int_abs_magnitude:
  !value : int. abs (real_of_int value) = &Num (ABS value)
Proof
  qx_gen_tac `value` >>
  Cases_on `value` using integerTheory.INT_NUM_CASES >>
  simp_tac std_ss [intrealTheory.real_of_int_num, intrealTheory.real_of_int_neg,
    integerTheory.INT_ABS_NUM, integerTheory.INT_ABS_NEG, integerTheory.NUM_OF_INT,
    realTheory.ABS_N, realTheory.ABS_NEG] >>
  EVAL_TAC
QED

Theorem integer_binary64_representable:
  !value : int. abs (real_of_int value) < (2 : real) pow 53 ==>
    ?fp : (52,11) float. float_value fp = Float (real_of_int value)
Proof
  qx_gen_tac `value` >> strip_tac >>
  irule binary_ieeePropsTheory.representables >>
  qexistsl_tac [`1075`, `Num (ABS value)`] >>
  asm_simp_tac std_ss [EVAL ``words$INT_MAX (:11)``,
    EVAL ``dimindex (:52)``, EVAL ``dimindex (:11)``] >>
  conj_tac
  >- fs[real_of_int_abs_magnitude, realTheory.REAL_OF_NUM_POW]
  >> asm_simp_tac std_ss [real_of_int_abs_magnitude, realTheory.REAL_EQ_RDIV_EQ,
       realTheory.REAL_POW_LT, realTheory.REAL_LT, realTheory.REAL_MUL_COMM]
QED

Theorem float_round_representable_value:
  !fp : ('t,'w) float. !number mode negative.
    2 <= dimindex (:'w) /\ float_value fp = Float number ==>
    float_value (float_round mode negative number : ('t,'w) float) = Float number
Proof
  qx_genl_tac [`fp`, `number`, `mode`, `negative`] >> strip_tac >>
  `float_is_finite fp /\ float_to_real fp = number` by
    metis_tac[binary_ieeeTheory.float_is_finite_thm,
      binary_ieeePropsTheory.float_value_float_to_real] >>
  mp_tac (Q.INST [`m` |-> `mode`, `f` |-> `fp`]
    (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
      binary_ieeePropsTheory.round_representable)) >>
  asm_simp_tac std_ss [] >>
  strip_tac >>
  qabbrev_tac `rounded = (round mode number : ('t,'w) float)` >>
  Cases_on `float_is_zero rounded`
  >- (
    `number = 0` by metis_tac[binary_ieeeTheory.float_is_zero_to_real] >>
    qunabbrev_tac `rounded` >> Cases_on `negative` >>
    asm_simp_tac std_ss [binary_ieeeTheory.float_round_def, LET_THM,
      binary_ieeeTheory.float_values])
  >> qunabbrev_tac `rounded` >>
  asm_simp_tac std_ss [binary_ieeeTheory.float_round_def, LET_THM,
    binary_ieeePropsTheory.float_value_eq_float_to_real]
QED




Theorem integer_binary64_round_with_flags:
  !value : int. !mode negative.
    abs (real_of_int value) < (2 : real) pow 53 ==>
    float_value (float_round mode negative (real_of_int value) : (52,11) float) =
      Float (real_of_int value) /\
    float_round_with_flags mode negative (real_of_int value) =
      (clear_flags, (float_round mode negative (real_of_int value) : (52,11) float))
Proof
  qx_genl_tac [`value`, `mode`, `negative`] >> strip_tac >>
  drule integer_binary64_representable >>
  disch_then (qx_choose_then `fp` assume_tac) >>
  `float_value (float_round mode negative (real_of_int value) : (52,11) float) =
    Float (real_of_int value)` by (
    qspecl_then [`fp`, `real_of_int value`, `mode`, `negative`]
      mp_tac float_round_representable_value >> simp[]) >>
  `abs (real_of_int value) < (2 : real) pow 1024` by (
    irule realTheory.REAL_LT_TRANS >> qexists_tac `(2 : real) pow 53` >>
    asm_simp_tac std_ss [] >> irule realTheory.REAL_POW_MONO_LT >> simp[]) >>
  asm_simp_tac (srw_ss()) [binary_ieeeTheory.float_round_with_flags_def, LET_THM,
    binary_ieeeTheory.float_is_infinite_def, binary_ieeeTheory.clear_flags_def,
    EVAL ``words$INT_MIN (:11)``, realTheory.REAL_NOT_LE]
QED

Theorem float_round_representable_nonzero:
  !fp : ('t,'w) float. !number mode negative.
    2 <= dimindex (:'w) /\ float_value fp = Float number /\ number <> 0 ==>
    (float_round mode negative number : ('t,'w) float) = fp
Proof
  qx_genl_tac [`fp`, `number`, `mode`, `negative`] >> strip_tac >>
  `float_is_finite fp /\ float_to_real fp = number /\ ~float_is_zero fp` by
    metis_tac[binary_ieeeTheory.float_is_finite_thm,
      binary_ieeePropsTheory.float_value_float_to_real,
      binary_ieeeTheory.float_is_zero_to_real] >>
  mp_tac (Q.INST [`m` |-> `mode`, `f` |-> `fp`]
    (INST_TYPE [alpha |-> ``:'t``, beta |-> ``:'w``]
      binary_ieeePropsTheory.round_representable_nonzero)) >>
  asm_simp_tac std_ss [binary_ieeeTheory.float_round_def, LET_THM]
QED

Theorem integer_binary64_round_sign:
  !value : int. !mode negative alternate.
    abs (real_of_int value) < (2 : real) pow 53 /\ value <> 0 ==>
    (float_round mode negative (real_of_int value) : (52,11) float) =
      float_round mode alternate (real_of_int value)
Proof
  qx_genl_tac [`value`, `mode`, `negative`, `alternate`] >> strip_tac >>
  drule integer_binary64_representable >>
  disch_then (qx_choose_then `fp` assume_tac) >>
  metis_tac[float_round_representable_nonzero, EVAL ``2 <= dimindex (:11)``,
    intrealTheory.real_of_int_11, EVAL ``real_of_int 0``]
QED

Theorem word32_integer_binary64_bound:
  !operand : word32. abs (real_of_int (w2i operand)) < (2 : real) pow 53
Proof
  qx_gen_tac `operand` >>
  qspec_then `operand` mp_tac integer_wordTheory.w2i_le >>
  qspec_then `operand` mp_tac integer_wordTheory.w2i_ge >>
  rewrite_tac [EVAL ``(2 : real) pow 53``, real_of_int_abs_magnitude] >>
  simp_tac std_ss [EVAL ``integer_word$INT_MIN (:32)``,
    EVAL ``integer_word$INT_MAX (:32)``, GSYM intrealTheory.real_of_int_num,
    intrealTheory.real_of_int_lt, integerTheory.Num_EQ_ABS,
    integerTheory.INT_ABS_ABS, integerTheory.INT_ABS_LT] >>
  intLib.ARITH_TAC
QED

Theorem FixedToFP64_signed32_algorithm:
  !operand : word32. !fpcr mode.
    (FixedToFP 64 operand 0 F fpcr (asl_fp64_rounding mode) :
      regstate sequential_state -> word64 res) =
    if w2i operand = 0 then returnS 0w
    else FPRound 64 (real_of_int (w2i operand)) fpcr (asl_fp64_rounding mode)
Proof
  qx_genl_tac [`operand`, `fpcr`, `mode`] >>
  `asl_fp64_rounding mode <> FPRounding_ODD` by (
    Cases_on `mode` >> simp[asl_fp64_rounding_def]) >>
  simp_tac std_ss [FUN_EQ_THM] >> qx_gen_tac `asl` >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FixedToFP_def, asl_Int_def, LET_THM, wordsTheory.word_len_def,
     preludeTheory.undefined_bitvector_def, armv86aTheory.id_def,
     sail2_state_monadTheory.assert_expS_def,
     bindS, seqS, returnS,
     EVAL ``realPowInteger (realFromFrac 20 10) 0``,
     EVAL ``realFromFrac 0 10``, intrealTheory.real_of_int_EQN] >>
  simp[FPZero64, machine_ieeeTheory.float_to_fp64_def]
QED

Theorem FixedToFP64_signed32:
  !operand : word32. !fpcr mode asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl ==>
    FixedToFP 64 operand 0 F fpcr (asl_fp64_rounding mode) asl =
      returnS (if w2i operand = 0 then 0w
        else machine_ieee$int_to_fp64 mode (w2i operand)) asl
Proof
  qx_genl_tac [`operand`, `fpcr`, `mode`, `asl`] >> strip_tac >>
  Cases_on `w2i operand = 0` >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FixedToFP64_signed32_algorithm, FPRound64_rounding_bits] >>
  `abs (real_of_int (w2i operand)) < (2 : real) pow 53` by
    ACCEPT_TAC (Q.SPEC `operand` word32_integer_binary64_bound) >>
  `real_of_int (w2i operand) <> 0` by
    metis_tac[intrealTheory.real_of_int_11, EVAL ``real_of_int 0``] >>
  qspecl_then [`real_of_int (w2i operand)`, `mode`, `asl`] mp_tac FPRound64 >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [LET_THM, integer_binary64_round_with_flags,
     binary_ieeeTheory.clear_flags_def, FPSR_write_read] >>
  qspecl_then [`w2i operand`, `mode`, `real_of_int (w2i operand) < 0`,
    `mode = roundTowardNegative`] mp_tac integer_binary64_round_sign >>
  asm_simp_tac std_ss [machine_ieeeTheory.int_to_fp64_def,
    machine_ieeeTheory.real_to_fp64_def, binary_ieeeTheory.real_to_float_def]
QED

Theorem l3_models_asl_FFromInt32:
  !src dst. l3_models_asl_instr (FloatingPoint (FFromInt32 (src, dst)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >> l3_decode_tac >>
  rpt gen_tac >> strip_tac >>
  `l3.exception = NoException` by fs[state_rel_def] >>
  Cases_on `l3.FPCR && ~0x00C00000w = 0w` >>
  gvs[Run_def, dfn'FFromInt32_def, CheckFP_def, write'D_def,
      raise'exception_def] >>
  asl_cexecute_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac
    `decode_scvtf_float_int_aarch64_instrs_float_convert_int _ _ _ _ _ _ seen` >>
  `state_rel l3 seen /\ asl_sys_regs_ok seen` by
    (unabbrev_all_tac >> state_rel_tac[]) >>
  `CheckFPAdvSIMDEnabled64 () seen = returnS () seen` by
    (irule CheckFPAdvSIMDEnabled64_ok >> simp[]) >>
  `(X_read 32 (&w2n src) seen : word32 res) =
    returnS (X src l3 : word32) seen` by (
    qspecl_then [`l3`, `seen`] mp_tac X_read32 >> simp[] >>
    disch_then (qspec_then `&w2n src` mp_tac) >> simp[integerTheory.int_ge] >>
    qspec_then `src` mp_tac w2n_lt >> simp[]) >>
  `read_regS FPCR_ref seen = (returnS l3.FPCR seen : word32 res)` by
    metis_tac[FPCR_read] >>
  `armv86a$FPRoundingMode l3.FPCR =
    returnS (asl_fp64_rounding (arm8$FPRoundingMode l3))` by
    ACCEPT_TAC (Q.SPEC `l3` FPRoundingMode_agrees) >>
  qabbrev_tac `result = if w2i (X src l3 : word32) = 0 then 0w
    else machine_ieee$int_to_fp64 (arm8$FPRoundingMode l3)
      (w2i (X src l3 : word32))` >>
  `FixedToFP 64 (X src l3 : word32) 0 F l3.FPCR
    (asl_fp64_rounding (arm8$FPRoundingMode l3)) seen = returnS result seen` by
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [FixedToFP64_signed32, Abbr `result`] >>
  qspecl_then [`l3`, `seen`, `dst`, `result`] mp_tac V_set64_state_rel >>
  simp[] >> disch_then (qx_choose_then `finished` strip_assume_tac) >>
  simp[decode_scvtf_float_int_aarch64_instrs_float_convert_int_def,
    execute_aarch64_instrs_float_convert_int_def, undefined_FPConvOp_def,
    undefined_FPRounding_def, sail2_state_monadTheory.undefined_boolS_def,
    vec_of_bits_access_vec_dec_single, Excl "access_vec_dec_def", bindS, seqS, returnS]
QED

Theorem integer_subrange_low_word:
  !value : int. !hi.
    hi + 1 = dimindex (:'a) ==>
    (integer_subrange value (&hi) 0 : 'a word) = i2w value
Proof
  qx_genl_tac [`value`, `hi`] >> strip_tac >>
  Cases_on `value` using integerTheory.INT_NUM_CASES >>
  asm_simp_tac std_ss [integer_subrange_nat_low, integer_wordTheory.i2w_pos] >>
  qmatch_goalsub_rename_tac `integer_subrange (-&magnitude) _ _` >>
  asm_simp_tac std_ss [integer_subrange_neg, bitstringTheory.field_def,
    bitstringTheory.shiftr_def, listTheory.TAKE_LENGTH_ID, arithmeticTheory.ADD1,
    bitstringTheory.v2w_fixwidth] >>
  `(v2w (REPLICATE (dimindex (:'a)) F) : 'a word) = 0w` by (
    irule bitstringTheory.v2w_n2w_thm >> simp[v2n_REPLICATE_F]) >>
  mp_tac (Q.INST [`xs` |-> `n2v magnitude`]
    (INST_TYPE [alpha |-> ``:'a``] neg_v2n_lemma)) >>
  asm_simp_tac std_ss [bitstringTheory.v2n_n2v, v2n_fixwidth] >>
  simp[integer_wordTheory.i2w_def]
QED

Theorem SatQ32_signed:
  !value : int.
    (SatQ value 32 F : regstate sequential_state -> (word32 # bool) res) =
    returnS (if 2147483647 < value then (0x7FFFFFFFw, T)
      else if value < -2147483648 then (0x80000000w, T)
      else (i2w value, F))
Proof
  qx_gen_tac `value` >> simp_tac std_ss [FUN_EQ_THM] >> qx_gen_tac `asl` >>
  simp[SatQ_def, SignedSatQ_def, preludeTheory.undefined_int_def,
    sail2_state_monadTheory.undefined_boolS_def,
    preludeTheory.undefined_bitvector_def, bindS, seqS, returnS, LET_THM,
    EVAL ``pow2 (31 : int)``, integer_subrange_low_word] >>
  Cases_on `2147483647 < value` >>
  Cases_on `value < -2147483648` >>
  simp[integerTheory.int_gt, returnS, integer_wordTheory.i2w_def]
QED

Theorem integer_access_zero_parity:
  !value : int.
    (vec_of_bits [integer_access value 0] : word1) =
      if ODD (Num (ABS value)) then 1w else 0w
Proof
  qx_gen_tac `value` >>
  Cases_on `value` using integerTheory.INT_NUM_CASES >>
  asm_simp_tac std_ss [integer_access_nat_zero, integerTheory.INT_ABS_NUM,
    integerTheory.INT_ABS_NEG, integerTheory.NUM_OF_INT] >>
  qmatch_goalsub_rename_tac `integer_access (-&magnitude) _` >>
  once_rewrite_tac [armv86aTheory.integer_access_def] >>
  once_rewrite_tac [SIMP_RULE std_ss [wordsTheory.DIMINDEX_GT_0]
    (Q.INST [`i` |-> `0`] vec_of_bits_access_vec_dec_single)] >>
  simp[integer_subrange_low_word, integer_wordTheory.i2w_def] >>
  Cases_on `EVEN magnitude` >>
  simp[arithmeticTheory.MOD_2, arithmeticTheory.ODD_EVEN]
QED

Theorem integer_access_zero_odd:
  !value : int.
    ((vec_of_bits [integer_access value 0] : word1) = 1w <=>
     ODD (Num (ABS value)))
Proof
  qx_gen_tac `value` >> Cases_on `ODD (Num (ABS value))` >>
  simp[integer_access_zero_parity]
QED

Theorem float_to_int_nearest_even:
  !fp : ('t,'w) float. !number.
    float_value fp = Float number ==>
    let lower = intreal$INT_FLOOR number in
    let error = number - real_of_int lower in
    float_to_int roundTiesToEven fp =
      SOME (if 1 / 2 < error \/
        error = 1 / 2 /\ ODD (Num (ABS lower)) then lower + 1 else lower)
Proof
  qx_genl_tac [`fp`, `number`] >> strip_tac >>
  qspec_then `number` strip_assume_tac intrealTheory.INT_FLOOR_BOUNDS >>
  asm_simp_tac (srw_ss()) [binary_ieeeTheory.float_to_int_def, LET_THM,
    intrealTheory.INT_CEILING_INT_FLOOR] >>
  qabbrev_tac `lower = intreal$INT_FLOOR number` >>
  qabbrev_tac `error = number - real_of_int lower` >>
  `0 <= error` by (qunabbrev_tac `error` >> RealField.REAL_ASM_ARITH_TAC) >>
  asm_simp_tac std_ss [realTheory.abs] >>
  Cases_on `error < 1 / 2`
  >- (
    `~(1 / 2 < error) /\ error <> 1 / 2` by RealField.REAL_ASM_ARITH_TAC >>
    asm_simp_tac std_ss []) >>
  `real_of_int lower <> number` by (
    qunabbrev_tac `error` >> RealField.REAL_ASM_ARITH_TAC) >>
  Cases_on `error = 1 / 2`
  >- (
    Cases_on `EVEN (Num (ABS lower))` >>
    asm_simp_tac std_ss [arithmeticTheory.ODD_EVEN, realTheory.REAL_LT_REFL]) >>
  `1 / 2 < error` by RealField.REAL_ASM_ARITH_TAC >> asm_simp_tac std_ss []
QED

Theorem float_to_int_exact_iff_floor:
  !fp : ('t,'w) float. !number rounded.
    float_value fp = Float number /\
    float_to_int roundTiesToEven fp = SOME rounded ==>
    (number = real_of_int rounded <=>
     number = real_of_int (intreal$INT_FLOOR number))
Proof
  qx_genl_tac [`fp`, `number`, `rounded`] >> strip_tac >>
  drule float_to_int_nearest_even >> simp [LET_THM] >> disch_tac >>
  qspec_then `number` strip_assume_tac intrealTheory.INT_FLOOR_BOUNDS >>
  qabbrev_tac `lower = intreal$INT_FLOOR number` >>
  qabbrev_tac `error = number - real_of_int lower` >>
  Cases_on `1 / 2 < error \/
    error = 1 / 2 /\ ODD (Num (ABS lower))` >>
  asm_simp_tac std_ss [] >>
  fs [Abbr `error`, intrealTheory.real_of_int_add,
      intrealTheory.real_of_int_num] >>
  RealField.REAL_ASM_ARITH_TAC
QED

Theorem fp64_from_int_equal:
  !value : int. !operand : word64. !number.
    abs (real_of_int value) < (2 : real) pow 53 /\
    float_value (fp64_to_float operand) = Float number ==>
    (machine_ieee$fp64_equal
      (machine_ieee$int_to_fp64 roundTiesToEven value) operand <=>
     real_of_int value = number)
Proof
  qx_genl_tac [`value`, `operand`, `number`] >> strip_tac >>
  qspecl_then [`value`, `roundTiesToEven`, `F`] mp_tac
    integer_binary64_round_with_flags >>
  asm_simp_tac std_ss [] >> strip_tac >>
  simp [machine_ieeeTheory.int_to_fp64_def,
        machine_ieeeTheory.real_to_fp64_def, combinTheory.o_DEF,
        binary_ieeeTheory.real_to_float_def,
        machine_ieeeTheory.fp64_equal_def,
        machine_ieeeTheory.fp64_to_float_float_to_fp64,
        binary_ieeeTheory.float_equal_def, binary_ieeeTheory.float_compare_def] >>
  Cases_on `real_of_int value = number` >>
  Cases_on `real_of_int value < number` >> gvs []
QED

Theorem FPToFixed32_non_nan_algorithm:
  !operand : word64. !fpcr kind (sign_bit : word1) number asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    FPUnpack operand 0w = returnS (kind, sign_bit, number) /\
    kind <> FPType_SNaN /\ kind <> FPType_QNaN ==>
    let lower = intreal$INT_FLOOR number in
    let error = number - real_of_int lower in
    let integer_result = if 1 / 2 < error \/
      error = 1 / 2 /\ ODD (Num (ABS lower)) then lower + 1 else lower in
    let (result, saturated) =
      if 2147483647 < integer_result then (0x7FFFFFFFw : word32, T)
      else if integer_result < -2147483648 then (0x80000000w, T)
      else (i2w integer_result, F) in
    FPToFixed 32 operand 0 F fpcr FPRounding_TIEEVEN asl =
      returnS result (asl with regstate := FPSR_ref.write_to
        (FPSR_ref.read_from asl.regstate ||
         if saturated then 1w else if error <> 0 then 16w else 0w) asl.regstate)
Proof
  qx_genl_tac [`operand`, `fpcr`, `kind`, `sign_bit`, `number`, `asl`] >>
  strip_tac >>
  Cases_on `number = 0` >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPToFixed_def, FPUnpack64_rounding_bits, SatQ32_signed,
     integer_access_zero_odd, undefined_FPType_def,
     preludeTheory.undefined_bitvector_def, preludeTheory.undefined_real_def,
     sail2_state_monadTheory.undefined_boolS_def,
     sail2_state_monadTheory.choose_boolS_def,
     sail2_state_monadTheory.chooseS_def, sail2_stateTheory.internal_pickS_def,
     sail2_state_monadTheory.assert_expS_def, wordsTheory.word_len_def,
     armv86aTheory.id_def, realTheory.real_gt, integerTheory.int_gt,
     integerTheory.int_ge, LET_THM, bindS, seqS, returnS,
     FPProcessException_rounding_bits, FPProcessException_zero,
     sail2_state_monadTheory.write_regS_def, sail2_state_monadTheory.updateS_def,
     FPSR_write_read, EVAL ``intreal$INT_FLOOR (0 : real)``,
     EVAL ``(1 : real) / 2 < 0``, integer_wordTheory.i2w_0,
     EVAL ``realPowInteger (realFromFrac 20 10) 0``,
     EVAL ``realFromFrac 0 10``, EVAL ``realFromFrac 5 10``] >>
  qmatch_goalsub_abbrev_tac `2147483647 < rounded` >>
  Cases_on `2147483647 < rounded` >>
  Cases_on `rounded < -2147483648` >>
  Cases_on `number = real_of_int (intreal$INT_FLOOR number)` >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPProcessException_zero, seqS, bindS, returnS,
     sail2_state_monadTheory.write_regS_def, sail2_state_monadTheory.updateS_def,
     FPSR_write_read]
QED

Theorem FPToFixed32_finite_algorithm:
  !operand : word64. !fpcr number asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    float_value (fp64_to_float operand) = Float number ==>
    let lower = intreal$INT_FLOOR number in
    let error = number - real_of_int lower in
    let integer_result = if 1 / 2 < error \/
      error = 1 / 2 /\ ODD (Num (ABS lower)) then lower + 1 else lower in
    let (result, saturated) =
      if 2147483647 < integer_result then (0x7FFFFFFFw : word32, T)
      else if integer_result < -2147483648 then (0x80000000w, T)
      else (i2w integer_result, F) in
    FPToFixed 32 operand 0 F fpcr FPRounding_TIEEVEN asl =
      returnS result (asl with regstate := FPSR_ref.write_to
        (FPSR_ref.read_from asl.regstate ||
         if saturated then 1w else if error <> 0 then 16w else 0w) asl.regstate)
Proof
  qx_genl_tac [`operand`, `fpcr`, `number`, `asl`] >> strip_tac >>
  imp_res_tac FPUnpack64_finite >>
  qspecl_then [`operand`, `fpcr`,
    `if number = 0 then FPType_Zero else FPType_Nonzero`,
    `(fp64_to_float operand).Sign`, `number`, `asl`]
    mp_tac FPToFixed32_non_nan_algorithm >>
  impl_tac
  >- (Cases_on `number = 0` >> simp[]) >>
  disch_then ACCEPT_TAC
QED

Theorem FPToFixed32_NaN:
  !operand : word64. !fpcr asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    float_value (fp64_to_float operand) = NaN ==>
    FPToFixed 32 operand 0 F fpcr FPRounding_TIEEVEN asl =
      returnS (0w : word32) (asl with regstate := FPSR_ref.write_to
        (FPSR_ref.read_from asl.regstate || 1w) asl.regstate)
Proof
  qx_genl_tac [`operand`, `fpcr`, `asl`] >> strip_tac >>
  `FPUnpack operand 0w = returnS
    (if float_is_signalling (fp64_to_float operand) then FPType_SNaN
     else FPType_QNaN, (fp64_to_float operand).Sign, 0)` by
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [SIMP_RULE std_ss [LET_THM] FPUnpack64, binary_ieeeTheory.float_is_nan_def] >>
  Cases_on `float_is_signalling (fp64_to_float operand)` >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPToFixed_def, FPUnpack64_rounding_bits, SatQ32_signed,
     integer_access_zero_odd, undefined_FPType_def,
     preludeTheory.undefined_bitvector_def, preludeTheory.undefined_real_def,
     sail2_state_monadTheory.undefined_boolS_def,
     sail2_state_monadTheory.choose_boolS_def, sail2_state_monadTheory.chooseS_def,
     sail2_stateTheory.internal_pickS_def, sail2_state_monadTheory.assert_expS_def,
     wordsTheory.word_len_def, armv86aTheory.id_def, realTheory.real_gt,
     integerTheory.int_gt, integerTheory.int_ge, LET_THM, bindS, seqS, returnS,
     FPProcessException_rounding_bits, FPProcessException_zero,
     sail2_state_monadTheory.write_regS_def, sail2_state_monadTheory.updateS_def,
     EVAL ``intreal$INT_FLOOR (0 : real)``, EVAL ``(1 : real) / 2 < 0``,
     integer_wordTheory.i2w_0, EVAL ``realPowInteger (realFromFrac 20 10) 0``,
     EVAL ``realFromFrac 0 10``, EVAL ``realFromFrac 5 10``]
QED

Theorem FPToFixed32_Infinity:
  !operand : word64. !fpcr asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    float_value (fp64_to_float operand) = Infinity ==>
    FPToFixed 32 operand 0 F fpcr FPRounding_TIEEVEN asl =
      returnS (if (fp64_to_float operand).Sign = 1w then (0x80000000w : word32)
        else 0x7FFFFFFFw) (asl with regstate := FPSR_ref.write_to
        (FPSR_ref.read_from asl.regstate || 1w) asl.regstate)
Proof
  qx_genl_tac [`operand`, `fpcr`, `asl`] >> strip_tac >>
  imp_res_tac FPUnpack64_infinite >>
  qabbrev_tac `huge = (2 : real) pow 1000000` >>
  `4294967296 < huge` by (
    qunabbrev_tac `huge` >> rewrite_tac [GSYM (EVAL ``(2 : real) pow 32``)] >>
    irule realTheory.REAL_POW_MONO_LT >> simp[]) >>
  qspec_then `huge` strip_assume_tac
    (SIMP_RULE std_ss [intrealTheory.real_of_int_add, intrealTheory.real_of_int_num]
      intrealTheory.INT_FLOOR_BOUNDS) >>
  qspec_then `-huge` strip_assume_tac
    (SIMP_RULE std_ss [intrealTheory.real_of_int_add, intrealTheory.real_of_int_num]
      intrealTheory.INT_FLOOR_BOUNDS) >>
  `2147483647 < intreal$INT_FLOOR huge` by (
    rewrite_tac [GSYM intrealTheory.real_of_int_lt] >>
    simp_tac std_ss [intrealTheory.real_of_int_num] >>
    irule (REAL_ARITH
      ``4294967296 < x /\ x < y + 1 ==> (2147483647 : real) < y``) >>
    qexists_tac `huge` >> asm_simp_tac std_ss []) >>
  `intreal$INT_FLOOR (-huge) + 1 < -2147483648` by (
    rewrite_tac [GSYM intrealTheory.real_of_int_lt] >>
    simp_tac std_ss [intrealTheory.real_of_int_add, intrealTheory.real_of_int_num,
      intrealTheory.real_of_int_neg] >>
    irule (REAL_ARITH
      ``4294967296 < x /\ y <= -x ==> y + 1 < (-2147483648 : real)``) >>
    qexists_tac `huge` >> asm_simp_tac std_ss []) >>
  `2147483647 < intreal$INT_FLOOR huge + 1` by (
    irule (intLib.ARITH_PROVE ``(a : int) < b ==> a < b + 1``) >>
    asm_simp_tac std_ss []) >>
  `intreal$INT_FLOOR (-huge) < -2147483648` by (
    irule (intLib.ARITH_PROVE ``(a : int) + 1 < b ==> a < b``) >>
    asm_simp_tac std_ss []) >>
  Cases_on `(fp64_to_float operand).Sign = 1w` >>
  qspecl_then [`operand`, `fpcr`, `FPType_Infinity`,
    `(fp64_to_float operand).Sign`,
    `if (fp64_to_float operand).Sign = 1w then -huge else huge`, `asl`]
    mp_tac FPToFixed32_non_nan_algorithm >>
  asm_simp_tac std_ss [LET_THM, armv86a_typesTheory.FPType_distinct,
    COND_RAND, COND_RATOR,
    intLib.ARITH_PROVE ``(x : int) < -2147483648 ==> ~(2147483647 < x)``]
QED

Theorem FPToFixed32_finite:
  !operand : word64. !fpcr rounded asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    machine_ieee$fp64_to_int roundTiesToEven operand = SOME rounded ==>
    let (invalid, inexact, result) =
      if rounded < -2147483648 then (T, F, 0x80000000w : word32)
      else if 2147483647 < rounded then (T, F, 0x7FFFFFFFw)
      else (F, ~machine_ieee$fp64_equal
        (machine_ieee$int_to_fp64 roundTiesToEven rounded) operand, i2w rounded) in
    FPToFixed 32 operand 0 F fpcr FPRounding_TIEEVEN asl =
      returnS result (asl with regstate := FPSR_ref.write_to
        (FPSR_ref.read_from asl.regstate ||
         (if invalid then 1w else 0w) ||
         (if inexact then 16w else 0w)) asl.regstate)
Proof
  qx_genl_tac [`operand`, `fpcr`, `rounded`, `asl`] >> strip_tac >>
  Q.SUBGOAL_THEN `?number. float_value (fp64_to_float operand) = Float number`
    (qx_choose_then `number` assume_tac)
  >- (
    namedCases_on `float_value (fp64_to_float operand)` ["candidate", "", ""] >>
    fs[machine_ieeeTheory.fp64_to_int_def, combinTheory.o_THM,
       binary_ieeeTheory.float_to_int_def]) >>
  `float_to_int roundTiesToEven (fp64_to_float operand) = SOME rounded` by
    fs[machine_ieeeTheory.fp64_to_int_def, combinTheory.o_THM] >>
  `rounded = if 1 / 2 < number - real_of_int (intreal$INT_FLOOR number) \/
      number - real_of_int (intreal$INT_FLOOR number) = 1 / 2 /\
      ODD (Num (ABS (intreal$INT_FLOOR number)))
    then intreal$INT_FLOOR number + 1 else intreal$INT_FLOOR number` by (
    qspecl_then [`fp64_to_float operand`, `number`] mp_tac float_to_int_nearest_even >>
    simp[LET_THM]) >>
  `(number = real_of_int rounded <=>
    number = real_of_int (intreal$INT_FLOOR number))` by (
    qspecl_then [`fp64_to_float operand`, `number`, `rounded`]
      mp_tac float_to_int_exact_iff_floor >> simp[]) >>
  qspecl_then [`operand`, `fpcr`, `number`, `asl`]
    mp_tac FPToFixed32_finite_algorithm >>
  impl_tac >- simp[] >>
  simp_tac std_ss [LET_THM, realTheory.REAL_SUB_0] >>
  qpat_x_assum `rounded = _`
    (fn rounding => PURE_REWRITE_TAC [GSYM rounding]) >>
  qpat_x_assum `(number = real_of_int rounded) <=> _`
    (fn exactness => PURE_REWRITE_TAC [GSYM exactness]) >>
  Cases_on `rounded < -2147483648`
  >- asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
       [intLib.ARITH_PROVE ``(x : int) < -2147483648 ==> ~(2147483647 < x)``] >>
  Cases_on `2147483647 < rounded`
  >- asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss())) [] >>
  `w2i (i2w rounded : word32) = rounded` by (
    irule integer_wordTheory.w2i_i2w >>
    asm_simp_tac std_ss [EVAL ``integer_word$INT_MIN (:32)``,
      EVAL ``integer_word$INT_MAX (:32)``, GSYM integerTheory.INT_NOT_LT]) >>
  `abs (real_of_int rounded) < (2 : real) pow 53` by (
    qspec_then `i2w rounded : word32` mp_tac word32_integer_binary64_bound >>
    asm_simp_tac std_ss []) >>
  `(machine_ieee$fp64_equal (machine_ieee$int_to_fp64 roundTiesToEven rounded)
      operand <=> real_of_int rounded = number)` by (
    irule fp64_from_int_equal >> asm_simp_tac std_ss []) >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss())) [EQ_SYM_EQ]
QED

Theorem fp64_sign_bit:
  !operand : word64.
    ((fp64_to_float operand).Sign = 1w <=> word_bit 63 operand)
Proof
  qx_gen_tac `operand` >> simp[machine_ieeeTheory.fp64_to_float_def] >>
  blastLib.BBLAST_TAC
QED

Theorem FPToFixed32:
  !operand : word64. !fpcr asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl ==>
    let (invalid, inexact, result) =
      case machine_ieee$fp64_to_int roundTiesToEven operand of
        NONE => (T, F,
          if machine_ieee$fp64_isNan operand then (0w : word32)
          else if word_bit 63 operand then 0x80000000w else 0x7FFFFFFFw)
      | SOME rounded =>
          if rounded < -2147483648 then (T, F, 0x80000000w)
          else if 2147483647 < rounded then (T, F, 0x7FFFFFFFw)
          else (F, ~machine_ieee$fp64_equal
            (machine_ieee$int_to_fp64 roundTiesToEven rounded) operand,
            i2w rounded) in
    FPToFixed 32 operand 0 F fpcr FPRounding_TIEEVEN asl =
      returnS result (asl with regstate := FPSR_ref.write_to
        (FPSR_ref.read_from asl.regstate ||
         (if invalid then 1w else 0w) ||
         (if inexact then 16w else 0w)) asl.regstate)
Proof
  qx_genl_tac [`operand`, `fpcr`, `asl`] >> strip_tac >>
  namedCases_on `machine_ieee$fp64_to_int roundTiesToEven operand` ["", "rounded"]
  >- (
    namedCases_on `float_value (fp64_to_float operand)` ["number", "", ""] >>
    fs [machine_ieeeTheory.fp64_to_int_def, combinTheory.o_THM,
      binary_ieeeTheory.float_to_int_def] >>
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [FPToFixed32_NaN, FPToFixed32_Infinity, fp64_sign_bit,
       machine_ieeeTheory.fp64_isNan_def, binary_ieeeTheory.float_is_nan_def,
       LET_THM, wordsTheory.WORD_AND_COMM]) >>
  qspecl_then [`operand`, `fpcr`, `rounded`, `asl`] mp_tac FPToFixed32_finite >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss())) [LET_THM]
QED

Theorem fp_to_int_flags_word:
  !fpsr : word32. !invalid inexact.
    let first = bit_field_insert 0 0
      (v2w [word_bit 0 fpsr \/ invalid] : word1) fpsr in
    bit_field_insert 4 4
      (v2w [word_bit 4 first \/ inexact] : word1) first =
      fpsr || (if invalid then 1w else 0w) || (if inexact then 16w else 0w)
Proof
  simp[LET_THM, wordsTheory.bit_field_insert_def] >> blastLib.BBLAST_TAC
QED

Theorem write_X_exception:
  !state. !value : 'a word. !dst.
    (write'X (value, dst) state).exception = state.exception
Proof
  simp[write'X_def, COND_RAND]
QED

Theorem l3_models_asl_FToInt32:
  !src dst. l3_models_asl_instr (FloatingPoint (FToInt32 (src, dst)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >> l3_decode_tac >>
  rpt gen_tac >> strip_tac >>
  `l3.exception = NoException` by fs[state_rel_def] >>
  Cases_on `l3.FPCR && ~0x00C00000w = 0w` >>
  gvs[Run_def, dfn'FToInt32_def, CheckFP_def, D_def,
      raise'exception_def, integerTheory.int_gt] >>
  pairarg_tac >> gvs[write_X_exception] >>
  qmatch_asmsub_rename_tac
    `(_ : bool # bool # word32) = (invalid_flag, inexact_flag, result)` >>
  simp_tac std_ss [SIMP_RULE std_ss [LET_THM] fp_to_int_flags_word] >>
  asl_cexecute_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac
    `decode_fcvtns_float_aarch64_instrs_float_convert_int _ _ _ _ _ _ seen` >>
  `state_rel l3 seen /\ asl_sys_regs_ok seen` by
    (unabbrev_all_tac >> state_rel_tac[]) >>
  `CheckFPAdvSIMDEnabled64 () seen = returnS () seen` by
    (irule CheckFPAdvSIMDEnabled64_ok >> simp[]) >>
  `V_read 64 (&w2n src) seen = (returnS (l3.FP_REG src) seen : word64 res)` by
    metis_tac[V_read64] >>
  `read_regS FPCR_ref seen = (returnS l3.FPCR seen : word32 res)` by
    metis_tac[FPCR_read] >>
  `FPSR_ref.read_from seen.regstate = l3.FPSR` by
    fs[state_rel_def, read_rel_def] >>
  qabbrev_tac `status = l3.FPSR || (if invalid_flag then 1w else 0w) ||
    (if inexact_flag then 16w else 0w)` >>
  qabbrev_tac `flagged = seen with regstate :=
    FPSR_ref.write_to status seen.regstate` >>
  `FPToFixed 32 (l3.FP_REG src) 0 F l3.FPCR FPRounding_TIEEVEN seen =
    returnS result flagged` by (
    qspecl_then [`l3.FP_REG src`, `l3.FPCR`, `seen`] mp_tac FPToFixed32 >>
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [LET_THM, Abbr `status`, Abbr `flagged`, wordsTheory.WORD_AND_COMM]) >>
  `state_rel (l3 with FPSR := status) flagged /\ asl_sys_regs_ok flagged` by (
    qunabbrev_tac `flagged` >> irule FPSR_set_state_rel >> simp[]) >>
  simp[decode_fcvtns_float_aarch64_instrs_float_convert_int_def,
    undefined_FPConvOp_def, undefined_FPRounding_def,
    sail2_state_monadTheory.undefined_boolS_def,
    vec_of_bits_access_vec_dec_single, Excl "access_vec_dec_def",
    execute_aarch64_instrs_float_convert_int_def,
    preludeTheory.undefined_bitvector_def, FPDecodeRounding_def,
    bindS, seqS, returnS] >>
  `l3.FPSR || (if inexact_flag then 16w else 0w) ||
    (if invalid_flag then 1w else 0w) = status` by (
    simp[Abbr `status`] >> blastLib.BBLAST_TAC) >>
  asm_simp_tac std_ss [] >>
  Cases_on `dst = 31w`
  >- asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
       [X_set_31, returnS, write'X_def] >>
  qspecl_then [`l3 with FPSR := status`, `flagged`]
    mp_tac (b32 alpha X_set_not_31) >> simp[] >>
  disch_then (qspecl_then [`32`, `&w2n dst`, `result : word32`] mp_tac) >>
  `w2n dst < 31` by WORD_DECIDE_TAC >>
  simp[integerTheory.int_ge] >>
  disch_then (qx_choose_then `finished` strip_assume_tac) >>
  `asl_sys_regs_ok finished` by (
    qspecl_then [`flagged`, `finished`, `32`, `&w2n dst`, `result : word32`]
      mp_tac (b32 alpha X_set_asl_sys_regs_ok) >> simp[]) >>
  simp[returnS]
QED



















Theorem FPAdd64_finite:
  !left : word64. !right : word64. !fpcr mode left_real right_real asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    armv86a$FPRoundingMode fpcr = returnS (asl_fp64_rounding mode) /\
    float_value (fp64_to_float left) = Float left_real /\
    float_value (fp64_to_float right) = Float right_real ==>
    let (round_flags, result) =
      float_add mode (fp64_to_float left) (fp64_to_float right) in
    FPAdd left right fpcr asl =
      returnS (float_to_fp64 result)
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate ||
           (if round_flags.Underflow_BeforeRounding then 8w else 0w) ||
           (if round_flags.Overflow then 4w else 0w) ||
           (if round_flags.Precision then 16w else 0w)) asl.regstate)
Proof
  qx_genl_tac [`left`, `right`, `fpcr`, `mode`, `left_real`, `right_real`, `asl`]
  \\ strip_tac
  \\ Cases_on `left_real + right_real = 0`
  >- (
    qspecl_then
         [`mode`, `fp64_to_float left`, `fp64_to_float right`, `left_real`, `right_real`]
         mp_tac binary_ieeeTheory.float_add_finite
    \\ asm_simp_tac std_ss [] \\ disch_then SUBST1_TAC
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [float_round_with_flags_zero, LET_THM, binary_ieeeTheory.clear_flags_def]
    \\ imp_res_tac FPUnpack64_finite
    \\ Cases_on `left_real = 0`
    \\ Cases_on `right_real = 0`
    \\ fs []
    \\ Cases_on `mode`
    \\ Cases_on_word_value `(fp64_to_float left).Sign`
    \\ Cases_on_word_value `(fp64_to_float right).Sign`
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPAdd_def, FPUnpack64_rounding_bits, FPProcessNaNs_def,
          FPZero64, FPSR_write_read, asl_fp64_rounding_def,
          binary_ieeeTheory.float_minus_zero, binary_ieeeTheory.float_plus_zero_def,
          LET_THM, undefined_FPType_def, preludeTheory.undefined_bitvector_def,
          preludeTheory.undefined_real_def,
          sail2_state_monadTheory.undefined_boolS_def,
          sail2_state_monadTheory.choose_boolS_def,
          sail2_state_monadTheory.chooseS_def,
          sail2_stateTheory.internal_pickS_def,
          sail2_state_monadTheory.assert_expS_def,
          bindS, seqS, returnS, asl_word_rws, EVAL ``realFromFrac 0 10``])
  >- (
    qspecl_then [`left`, `right`, `fpcr`, `mode`, `left_real`, `right_real`, `asl`]
         mp_tac FPAdd64_finite_nonzero_result
    \\ asm_simp_tac std_ss [])
QED




Theorem FPSub64_finite_nonzero_round:
  !left : word64. !right : word64. !fpcr rounding left_real right_real.
    fpcr && ~0x00C00000w = 0w /\
    armv86a$FPRoundingMode fpcr = returnS rounding /\
    float_value (fp64_to_float left) = Float left_real /\
    float_value (fp64_to_float right) = Float right_real /\
    left_real - right_real <> 0 ==>
    FPSub left right fpcr = FPRound 64 (left_real - right_real) fpcr rounding
Proof
  fp_add_sub_round_tac FPSub_def
QED

Theorem FPSub64_finite_nonzero_result:
  !left : word64. !right : word64. !fpcr mode left_real right_real asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    armv86a$FPRoundingMode fpcr = returnS (asl_fp64_rounding mode) /\
    float_value (fp64_to_float left) = Float left_real /\
    float_value (fp64_to_float right) = Float right_real /\
    left_real - right_real <> 0 ==>
    let (round_flags, result) =
      float_sub mode (fp64_to_float left) (fp64_to_float right) in
    FPSub left right fpcr asl =
      returnS (float_to_fp64 result)
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate ||
           (if round_flags.Underflow_BeforeRounding then 8w else 0w) ||
           (if round_flags.Overflow then 4w else 0w) ||
           (if round_flags.Precision then 16w else 0w)) asl.regstate)
Proof
  qx_genl_tac [`left`, `right`, `fpcr`, `mode`, `left_real`, `right_real`, `asl`]
  \\ strip_tac
  \\ qspecl_then
       [`mode`, `fp64_to_float left`, `fp64_to_float right`, `left_real`, `right_real`]
       mp_tac float_sub_finite_nonzero_real_sign
  \\ asm_simp_tac std_ss [] \\ disch_then SUBST1_TAC
  \\ qspecl_then
       [`left`, `right`, `fpcr`, `asl_fp64_rounding mode`, `left_real`, `right_real`]
       mp_tac FPSub64_finite_nonzero_round
  \\ asm_simp_tac std_ss [] \\ disch_then SUBST1_TAC
  \\ qspecl_then [`left_real - right_real`, `mode`, `asl`] mp_tac FPRound64
  \\ asm_simp_tac std_ss [FPRound64_rounding_bits]
QED

Theorem FPSub64_finite:
  !left : word64. !right : word64. !fpcr mode left_real right_real asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    armv86a$FPRoundingMode fpcr = returnS (asl_fp64_rounding mode) /\
    float_value (fp64_to_float left) = Float left_real /\
    float_value (fp64_to_float right) = Float right_real ==>
    let (round_flags, result) =
      float_sub mode (fp64_to_float left) (fp64_to_float right) in
    FPSub left right fpcr asl =
      returnS (float_to_fp64 result)
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate ||
           (if round_flags.Underflow_BeforeRounding then 8w else 0w) ||
           (if round_flags.Overflow then 4w else 0w) ||
           (if round_flags.Precision then 16w else 0w)) asl.regstate)
Proof
  qx_genl_tac [`left`, `right`, `fpcr`, `mode`, `left_real`, `right_real`, `asl`]
  \\ strip_tac
  \\ Cases_on `left_real - right_real = 0`
  >- (
    qspecl_then
         [`mode`, `fp64_to_float left`, `fp64_to_float right`, `left_real`, `right_real`]
         mp_tac binary_ieeeTheory.float_sub_finite
    \\ asm_simp_tac std_ss [] \\ disch_then SUBST1_TAC
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [float_round_with_flags_zero, LET_THM, binary_ieeeTheory.clear_flags_def]
    \\ imp_res_tac FPUnpack64_finite
    \\ Cases_on `left_real = 0`
    \\ Cases_on `right_real = 0`
    \\ fs []
    \\ Cases_on `mode`
    \\ Cases_on_word_value `(fp64_to_float left).Sign`
    \\ Cases_on_word_value `(fp64_to_float right).Sign`
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPSub_def, FPUnpack64_rounding_bits, FPProcessNaNs_def,
          sail2_operators_mwordsTheory.not_vec_def,
          FPZero64, FPSR_write_read, asl_fp64_rounding_def,
          binary_ieeeTheory.float_minus_zero, binary_ieeeTheory.float_plus_zero_def,
          LET_THM, undefined_FPType_def, preludeTheory.undefined_bitvector_def,
          preludeTheory.undefined_real_def,
          sail2_state_monadTheory.undefined_boolS_def,
          sail2_state_monadTheory.choose_boolS_def,
          sail2_state_monadTheory.chooseS_def,
          sail2_stateTheory.internal_pickS_def,
          sail2_state_monadTheory.assert_expS_def,
          bindS, seqS, returnS, asl_word_rws, EVAL ``realFromFrac 0 10``])
  >- (
    qspecl_then [`left`, `right`, `fpcr`, `mode`, `left_real`, `right_real`, `asl`]
         mp_tac FPSub64_finite_nonzero_result
    \\ asm_simp_tac std_ss [])
QED




Theorem FPSqrt64_finite_positive:
  !bits : word64. !fpcr mode number asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    armv86a$FPRoundingMode fpcr = returnS (asl_fp64_rounding mode) /\
    float_value (fp64_to_float bits) = Float number /\ 0 < number ==>
    let (round_flags, result) = float_sqrt mode (fp64_to_float bits) in
    FPSqrt bits fpcr asl =
      returnS (float_to_fp64 result)
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate ||
           (if round_flags.Underflow_BeforeRounding then 8w else 0w) ||
           (if round_flags.Overflow then 4w else 0w) ||
           (if round_flags.Precision then 16w else 0w)) asl.regstate)
Proof
  rpt gen_tac >> strip_tac >>
  `number = float_to_real (fp64_to_float bits)` by
    fs [binary_ieeeTheory.float_value_def, AllCaseEqs()] >>
  `number <> 0` by REAL_ASM_ARITH_TAC >>
  `(fp64_to_float bits).Sign = 0w` by (
    qspec_then `fp64_to_float bits` mp_tac float_to_real_sign_nonzero >>
    Cases_on_word_value `(fp64_to_float bits).Sign` >>
    asm_simp_tac std_ss [] >> REAL_ASM_ARITH_TAC) >>
  qpat_x_assum `number = float_to_real _` kall_tac >>
  `float_sqrt mode (fp64_to_float bits) =
    float_round_with_flags mode (sqrt number < 0) (sqrt number)` by (
    qspecl_then [`mode`, `fp64_to_float bits`, `number`]
      mp_tac float_sqrt_finite_positive_real_sign >>
    asm_simp_tac std_ss []) >>
  imp_res_tac FPUnpack64_finite >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPSqrt_def, FPUnpack64_rounding_bits, FPRound__1_def, LET_THM,
     undefined_FPType_def, preludeTheory.undefined_bitvector_def,
     preludeTheory.undefined_real_def,
     sail2_stateTheory.internal_pickS_def,
     sail2_state_monadTheory.chooseS_def,
     sail2_state_monadTheory.assert_expS_def,
     bindS, seqS, returnS, asl_word_rws] >>
  `sqrt number <> 0` by (irule SQRT_POS_NE >> asm_simp_tac std_ss []) >>
  qspecl_then [`sqrt number`, `mode`, `asl`] mp_tac FPRound64 >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPRound64_rounding_bits, LET_THM, returnS]
QED





Theorem float_sqrt_nan_result:
  !mode. !fp : ('t, 'w) float.
    float_is_nan fp ==>
    float_is_nan (SND (float_sqrt mode fp)) /\
    ~float_is_signalling (SND (float_sqrt mode fp))
Proof
  rpt gen_tac >> strip_tac >>
  `float_value fp = NaN` by (
    namedCases_on `float_value fp` ["number", "", ""] >>
    fs [binary_ieeeTheory.float_is_nan_def]) >>
  `fp <> float_minus_zero (:'t # 'w)` by (
    strip_tac >> gvs [binary_ieeeTheory.float_values]) >>
  Cases_on `fp.Sign = 0w` >>
  simp [binary_ieeeTheory.float_sqrt_def,
        binary_ieeeTheory.some_nan_properties]
QED

Theorem float_round_with_flags_exceptions:
  !mode negative number.
    let (round_flags, result) =
      (float_round_with_flags mode negative number : flags # ('t, 'w) float) in
    ~round_flags.InvalidOp /\ ~round_flags.DivideByZero
Proof
  rpt gen_tac >>
  simp [binary_ieeeTheory.float_round_with_flags_def,
        binary_ieeeTheory.clear_flags_def, LET_THM]
QED

Theorem closest_such_finite:
  !allowed : ('t, 'w) float set. !predicate source.
    allowed <> {} /\
    (!candidate. candidate IN allowed ==> float_is_finite candidate) ==>
    float_is_finite (closest_such predicate allowed source)
Proof
  rpt gen_tac >> strip_tac >>
  metis_tac [closest_such_is_closest, binary_ieeeTheory.is_closest_def]
QED

Theorem round_not_nan:
  !mode number. ~float_is_nan (round mode number : (52,11) float)
Proof
  rpt gen_tac >> Cases_on `mode`
  >- (
    rw [binary_ieeeTheory.round_def, LET_THM] >>
    sg `float_is_finite
      (closest_such (\a. ~word_lsb a.Significand) float_is_finite number :
        (52,11) float)`
    >- (
      irule closest_such_finite >>
      simp [pred_setTheory.SPECIFICATION] >>
      rewrite_tac [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
      qexists_tac `float_plus_zero (:52 # 11)` >>
      simp [pred_setTheory.SPECIFICATION])
    >> metis_tac [binary_ieeeTheory.float_distinct_finite])
  >- (
    rw [binary_ieeeTheory.round_def, LET_THM, binary_ieeeTheory.closest_def,
        real_ge, real_gt] >>
    sg `float_is_finite
      (closest_such (K T)
        {candidate | float_is_finite candidate /\
          number <= float_to_real candidate} number : (52,11) float)`
    >- (
      irule closest_such_finite >>
      simp [pred_setTheory.GSPECIFICATION] >>
      rewrite_tac [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
      qexists_tac `float_top (:52 # 11)` >>
      simp [pred_setTheory.GSPECIFICATION, GSYM binary_ieeeTheory.largest_is_top] >>
      REAL_ASM_ARITH_TAC)
    >> metis_tac [binary_ieeeTheory.float_distinct_finite])
  >- (
    rw [binary_ieeeTheory.round_def, LET_THM, binary_ieeeTheory.closest_def,
        real_ge, real_gt] >>
    sg `float_is_finite
      (closest_such (K T)
        {candidate | float_is_finite candidate /\
          float_to_real candidate <= number} number : (52,11) float)`
    >- (
      irule closest_such_finite >>
      simp [pred_setTheory.GSPECIFICATION] >>
      rewrite_tac [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
      qexists_tac `float_bottom (:52 # 11)` >>
      simp [pred_setTheory.GSPECIFICATION, binary_ieeeTheory.float_bottom_def,
            binary_ieeeTheory.float_to_real_negate,
            binary_ieeeTheory.float_is_finite_float_negate,
            GSYM binary_ieeeTheory.largest_is_top] >>
      REAL_ASM_ARITH_TAC)
    >> metis_tac [binary_ieeeTheory.float_distinct_finite])
  >- (
    rw [binary_ieeeTheory.round_def, LET_THM, binary_ieeeTheory.closest_def] >>
    sg `float_is_finite
      (closest_such (K T)
        {candidate | float_is_finite candidate /\
          abs (float_to_real candidate) <= abs number} number : (52,11) float)`
    >- (
      irule closest_such_finite >>
      simp [pred_setTheory.GSPECIFICATION] >>
      rewrite_tac [GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
      qexists_tac `float_plus_zero (:52 # 11)` >>
      simp [pred_setTheory.GSPECIFICATION, binary_ieeeTheory.float_to_real_zeroes])
    >> metis_tac [binary_ieeeTheory.float_distinct_finite])
QED

Theorem float_round_not_nan:
  !mode negative number.
    ~float_is_nan (float_round mode negative number : (52,11) float)
Proof
  rpt gen_tac >>
  rw [binary_ieeeTheory.float_round_def, LET_THM, round_not_nan]
QED

Theorem float_round_with_flags_not_nan:
  !mode negative number.
    let (round_flags, result) =
      (float_round_with_flags mode negative number : flags # (52,11) float) in
    ~float_is_nan result
Proof
  rpt gen_tac >>
  simp [binary_ieeeTheory.float_round_with_flags_def, LET_THM,
        float_round_not_nan]
QED

Theorem FPCompare64_self_result:
  !bits. arm8$FPCompare64 (bits, bits) =
    if machine_ieee$fp64_isNan bits then 3w else 6w
Proof
  qx_gen_tac `bits` >>
  namedCases_on `float_value (fp64_to_float bits)` ["number", "", ""] >>
  simp [arm8Theory.FPCompare64_def,
        machine_ieeeTheory.fp64_isNan_def,
        machine_ieeeTheory.fp64_equal_def,
        binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.float_equal_def,
        binary_ieeeTheory.float_compare_def]
QED

Theorem fp64_zero_encoding:
  !bits : word64.
    float_value (fp64_to_float bits) = Float 0 ==>
    float_to_fp64
      (<| Sign := (fp64_to_float bits).Sign;
          Exponent := 0w; Significand := 0w |> : (52,11) float) = bits
Proof
  gen_tac >> strip_tac >>
  fs [GSYM binary_ieeeTheory.float_is_zero_float_value_EQ0,
      binary_ieeeTheory.float_is_zero] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV
    [GSYM machine_ieeeTheory.float_to_fp64_fp64_to_float])) >>
  simp [machine_ieeeTheory.float_to_fp64_11,
        binary_ieeeTheory.float_component_equality]
QED

Theorem FPSqrt64_negative:
  !bits : word64. !fpcr asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    ~machine_ieee$fp64_isNan bits /\
    ~float_is_zero (fp64_to_float bits) /\
    (fp64_to_float bits).Sign = 1w ==>
    FPSqrt bits fpcr asl =
      returnS (0x7FF8000000000000w : word64)
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate || 1w) asl.regstate)
Proof
  rpt gen_tac >> strip_tac >>
  `~float_is_nan (fp64_to_float bits) /\
   ~float_is_signalling (fp64_to_float bits)` by
    fs [machine_ieeeTheory.fp64_isNan_def,
        binary_ieeeTheory.float_is_signalling_def] >>
  Cases_on `float_is_infinite (fp64_to_float bits)` >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPSqrt_def, FPUnpack64_rounding_bits,
     SIMP_RULE std_ss [LET_THM] FPUnpack64, FPDefaultNaN64,
     FPProcessException_rounding_bits, FPProcessException_zero,
     undefined_FPType_def, preludeTheory.undefined_bitvector_def,
     preludeTheory.undefined_real_def,
     sail2_stateTheory.internal_pickS_def,
     sail2_state_monadTheory.chooseS_def,
     sail2_state_monadTheory.assert_expS_def,
     sail2_state_monadTheory.write_regS_def,
     sail2_state_monadTheory.updateS_def,
     bindS, seqS, returnS, LET_THM, asl_word_rws]
QED

Theorem float_infinite_record:
  !fp : ('t,'w) float.
    float_value fp = Infinity ==>
    fp = <| Sign := fp.Sign; Exponent := UINT_MAXw; Significand := 0w |>
Proof
  qx_gen_tac `fp` \\ strip_tac
  \\ fs [binary_ieeeTheory.float_value_def,
         binary_ieeeTheory.float_component_equality, AllCaseEqs()]
QED

Theorem FPInfinity64_negated_input:
  !bits : word64.
    float_value (fp64_to_float bits) = Infinity ==>
    FPInfinity 64 (~((fp64_to_float bits).Sign)) =
      returnS (machine_ieee$fp64_negate bits)
Proof
  qx_gen_tac `bits` \\ strip_tac
  \\ rewrite_tac [FPInfinity64, machine_ieeeTheory.fp64_negate_def,
                  combinTheory.o_THM]
  \\ AP_TERM_TAC \\ AP_TERM_TAC
  \\ fs [binary_ieeeTheory.float_negate_def,
         binary_ieeeTheory.float_component_equality,
         binary_ieeeTheory.float_value_def, AllCaseEqs(),
         EVAL ``(UINT_MAXw : word11)``]
QED

Theorem FPInfinity64_input:
  !bits : word64.
    float_value (fp64_to_float bits) = Infinity ==>
    FPInfinity 64 (fp64_to_float bits).Sign = returnS bits
Proof
  qx_gen_tac `bits` \\ strip_tac
  \\ qspec_then `fp64_to_float bits` mp_tac float_infinite_record
  \\ asm_simp_tac std_ss []
  \\ disch_then (mp_tac o AP_TERM ``float_to_fp64``)
  \\ simp_tac std_ss
       [machine_ieeeTheory.float_to_fp64_fp64_to_float,
        EVAL ``(UINT_MAXw : word11)``]
  \\ disch_then (fn packed => rewrite_tac [FPInfinity64, GSYM packed])
QED



Theorem FPSqrt64:
  !bits : word64. !fpcr mode asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    armv86a$FPRoundingMode fpcr = returnS (asl_fp64_rounding mode) ==>
    let (round_flags, expected) = float_sqrt mode (fp64_to_float bits) in
    let status =
      if machine_ieee$fp64_isNan bits then
        (if machine_ieee$fp64_isSignallingNan bits then 1w else 0w)
      else
        (if round_flags.InvalidOp then 1w else 0w) ||
        (if round_flags.DivideByZero then 2w else 0w) ||
        (if round_flags.Overflow then 4w else 0w) ||
        (if round_flags.Underflow_BeforeRounding then 8w else 0w) ||
        (if round_flags.Precision then 16w else 0w) in
    FPSqrt bits fpcr asl =
      returnS (FPNaNResult (float_to_fp64 expected, bits, bits, bits))
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate || status) asl.regstate)
Proof
  rpt gen_tac >> strip_tac >>
  namedCases_on `float_value (fp64_to_float bits)` ["number", "", ""]
  >- (
    Cases_on `number = 0`
    >- (
      `float_value (fp64_to_float bits) = Float 0` by
        asm_simp_tac std_ss [] >>
      `~machine_ieee$fp64_isNan bits /\
       ~machine_ieee$fp64_isSignallingNan bits` by
        simp [machine_ieeeTheory.fp64_isNan_def,
              machine_ieeeTheory.fp64_isSignallingNan_def,
              binary_ieeeTheory.float_is_nan_def,
              binary_ieeeTheory.float_is_signalling_def] >>
      `float_sqrt mode (fp64_to_float bits) =
        (clear_flags, fp64_to_float bits)` by (
        qspecl_then [`mode`, `fp64_to_float bits`] mp_tac float_sqrt_finite_zero >>
        asm_simp_tac std_ss []) >>
      imp_res_tac FPUnpack64_finite >>
      imp_res_tac fp64_zero_encoding >>
      asm_simp_tac std_ss [LET_THM] >>
      asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
        [FPNaNResult_not_nan, FPSqrt_def, FPUnpack64_rounding_bits, FPZero64, LET_THM,
         undefined_FPType_def, preludeTheory.undefined_bitvector_def,
         preludeTheory.undefined_real_def,
         sail2_stateTheory.internal_pickS_def,
         sail2_state_monadTheory.chooseS_def,
         sail2_state_monadTheory.assert_expS_def,
         bindS, seqS, returnS, asl_word_rws,
         binary_ieeeTheory.clear_flags_def,
         machine_ieeeTheory.float_to_fp64_fp64_to_float,
         FPSR_write_read])
    >> Cases_on `0 < number`
    >- (
      `~machine_ieee$fp64_isNan bits` by
        simp [machine_ieeeTheory.fp64_isNan_def,
              binary_ieeeTheory.float_is_nan_def] >>
      `float_sqrt mode (fp64_to_float bits) =
        float_round_with_flags mode (sqrt number < 0) (sqrt number)` by (
        qspecl_then [`mode`, `fp64_to_float bits`, `number`]
          mp_tac float_sqrt_finite_positive_real_sign >>
        asm_simp_tac std_ss []) >>
      namedCases_on
        `(float_round_with_flags mode (sqrt number < 0) (sqrt number) :
          flags # (52,11) float)` ["round_flags expected"] >>
      qspecl_then [`mode`, `sqrt number < 0`, `sqrt number`]
        mp_tac (INST_TYPE [``:'t`` |-> ``:52``, ``:'w`` |-> ``:11``]
          float_round_with_flags_exceptions) >>
      asm_simp_tac std_ss [LET_THM] >> strip_tac >>
      `~float_is_nan expected` by (
        qspecl_then [`mode`, `sqrt number < 0`, `sqrt number`]
          mp_tac float_round_with_flags_not_nan >>
        asm_simp_tac std_ss [LET_THM]) >>
      qspecl_then [`bits`, `fpcr`, `mode`, `number`, `asl`]
        mp_tac FPSqrt64_finite_positive >>
      asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
        [LET_THM, FPNaNResult_not_nan, machine_ieeeTheory.fp64_isNan_def,
         machine_ieeeTheory.fp64_to_float_float_to_fp64])
    >> `float_to_real (fp64_to_float bits) = number` by
      fs [binary_ieeeTheory.float_value_def, AllCaseEqs()] >>
    `(fp64_to_float bits).Sign = 1w` by (
      qspec_then `fp64_to_float bits` mp_tac float_to_real_sign_nonzero >>
      asm_simp_tac std_ss [] >> REAL_ASM_ARITH_TAC) >>
    `~machine_ieee$fp64_isNan bits /\
     ~float_is_zero (fp64_to_float bits)` by
      simp [machine_ieeeTheory.fp64_isNan_def,
            binary_ieeeTheory.float_is_nan_def,
            binary_ieeeTheory.float_is_zero_def] >>
    `fp64_to_float bits <> float_minus_zero (:52 # 11)` by (
      strip_tac >> gvs [binary_ieeeTheory.zero_properties]) >>
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [binary_ieeeTheory.float_sqrt_def, LET_THM,
       binary_ieeeTheory.invalidop_flags_def, binary_ieeeTheory.clear_flags_def] >>
    assume_tac (CONJUNCT1 fp64_default_nan) >>
    assume_tac (CONJUNCT2 fp64_default_nan) >>
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [FPSqrt64_negative, FPNaNResult_def, CONJUNCT2 fp64_nan_bits,
         binary_ieeeTheory.float_is_nan_def,
       machine_ieeeTheory.fp64_isNan_def,
       machine_ieeeTheory.fp64_to_float_float_to_fp64,
       binary_ieeeTheory.some_nan_properties])
  >- (
    `~machine_ieee$fp64_isNan bits /\
     ~float_is_zero (fp64_to_float bits) /\
     ~float_is_signalling (fp64_to_float bits) /\
     float_is_infinite (fp64_to_float bits)` by
      simp [machine_ieeeTheory.fp64_isNan_def,
            binary_ieeeTheory.float_is_nan_def,
            binary_ieeeTheory.float_is_zero_def,
            binary_ieeeTheory.float_is_signalling_def,
            binary_ieeeTheory.float_is_infinite_def] >>
    `fp64_to_float bits <> float_minus_zero (:52 # 11)` by (
      strip_tac >> gvs [binary_ieeeTheory.zero_properties]) >>
    Cases_on `(fp64_to_float bits).Sign = 1w`
    >- (
      asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
        [binary_ieeeTheory.float_sqrt_def, LET_THM,
         binary_ieeeTheory.invalidop_flags_def, binary_ieeeTheory.clear_flags_def] >>
      assume_tac (CONJUNCT1 fp64_default_nan) >>
      assume_tac (CONJUNCT2 fp64_default_nan) >>
      asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
        [FPSqrt64_negative, FPNaNResult_def, CONJUNCT2 fp64_nan_bits,
         binary_ieeeTheory.float_is_nan_def,
         machine_ieeeTheory.fp64_isNan_def,
         machine_ieeeTheory.fp64_to_float_float_to_fp64,
         binary_ieeeTheory.some_nan_properties])
    >> `(fp64_to_float bits).Sign = 0w` by (
      Cases_on_word_value `(fp64_to_float bits).Sign` >> gvs []) >>
    imp_res_tac FPUnpack64_infinite >>
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [binary_ieeeTheory.float_sqrt_def, LET_THM,
       binary_ieeeTheory.clear_flags_def] >>
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [FPNaNResult_not_nan, machine_ieeeTheory.fp64_isNan_def,
       machine_ieeeTheory.fp64_to_float_float_to_fp64,
       binary_ieeeTheory.float_is_nan_def,
       binary_ieeeTheory.float_plus_infinity_def,
       binary_ieeeTheory.float_value_def, FPSqrt_def, FPUnpack64_rounding_bits, FPInfinity64, LET_THM,
       undefined_FPType_def, preludeTheory.undefined_bitvector_def,
       preludeTheory.undefined_real_def,
       sail2_stateTheory.internal_pickS_def,
       sail2_state_monadTheory.chooseS_def,
       sail2_state_monadTheory.assert_expS_def,
       bindS, seqS, returnS, asl_word_rws,
       machine_ieeeTheory.fp64_isSignallingNan_def,
       machine_ieeeTheory.fp64_to_float_float_to_fp64,
       binary_ieeeTheory.float_is_signalling_def,
       binary_ieeeTheory.infinity_properties,
       binary_ieeeTheory.float_plus_infinity_def,
       FPSR_write_read] >>
    simp [binary_ieeeTheory.float_is_nan_def,
          binary_ieeeTheory.float_value_def])
  >- (
    `machine_ieee$fp64_isNan bits` by
      simp [machine_ieeeTheory.fp64_isNan_def,
            binary_ieeeTheory.float_is_nan_def] >>
    `~word_bit 24 fpcr /\ ~word_bit 8 fpcr /\ ~word_bit 25 fpcr` by (
      qpat_x_assum `fpcr && ~0x00C00000w = 0w` mp_tac >>
      blastLib.BBLAST_TAC) >>
    namedCases_on `float_sqrt mode (fp64_to_float bits)`
      ["round_flags expected"] >>
    `machine_ieee$fp64_isNan (float_to_fp64 expected)` by (
      qspecl_then [`mode`, `fp64_to_float bits`] mp_tac float_sqrt_nan_result >>
      asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
        [machine_ieeeTheory.fp64_isNan_def,
         machine_ieeeTheory.fp64_to_float_float_to_fp64,
         binary_ieeeTheory.float_is_nan_def]) >>
    mp_tac (Q.INST [`value` |-> `bits`] FPSqrt64_NaN) >>
    impl_tac >- asm_simp_tac std_ss [] >>
    disch_then SUBST1_TAC >>
    simp_tac std_ss [LET_THM] >>
    Cases_on `machine_ieee$fp64_isSignallingNan bits` >>
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [FPNaNResult_nan, seqS, bindS, returnS,
       sail2_state_monadTheory.write_regS_def,
       sail2_state_monadTheory.updateS_def, FPSR_write_read])
QED

Theorem fp64_some_qnan:
  !operation : (52,11) fp_op.
    machine_ieee$fp64_isNan (float_to_fp64 (float_some_qnan operation)) /\
    ~machine_ieee$fp64_isSignallingNan (float_to_fp64 (float_some_qnan operation))
Proof
  qx_gen_tac `operation`
  \\ simp [machine_ieeeTheory.fp64_isNan_def,
           machine_ieeeTheory.fp64_isSignallingNan_def,
           machine_ieeeTheory.fp64_to_float_float_to_fp64,
           binary_ieeeTheory.some_nan_properties]
QED

Theorem fp64_negate_nan:
  !bits : word64.
    (machine_ieee$fp64_isNan (machine_ieee$fp64_negate bits) <=>
     machine_ieee$fp64_isNan bits) /\
    (machine_ieee$fp64_isSignallingNan (machine_ieee$fp64_negate bits) <=>
     machine_ieee$fp64_isSignallingNan bits)
Proof
  qx_gen_tac `bits`
  \\ Cases_on `(fp64_to_float bits).Exponent = UINT_MAXw`
  \\ Cases_on `(fp64_to_float bits).Significand = 0w`
  \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
       [machine_ieeeTheory.fp64_isNan_def,
        machine_ieeeTheory.fp64_isSignallingNan_def,
        machine_ieeeTheory.fp64_negate_def, combinTheory.o_THM,
        machine_ieeeTheory.fp64_to_float_float_to_fp64,
        binary_ieeeTheory.float_is_nan_def,
        binary_ieeeTheory.float_is_signalling_def,
        binary_ieeeTheory.float_negate_def, binary_ieeeTheory.float_value_def]
  \\ fs [EVAL ``(UINT_MAXw : word11)``]
QED

Theorem FPAdd64:
  !left : word64. !right : word64. !fpcr mode asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    armv86a$FPRoundingMode fpcr = returnS (asl_fp64_rounding mode) ==>
    let (round_flags, expected) =
      float_add mode (fp64_to_float left) (fp64_to_float right) in
    FPAdd left right fpcr asl =
      returnS (FPNaNResult (float_to_fp64 expected, left, right, right))
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate ||
           (if round_flags.InvalidOp then 1w else 0w) ||
           (if round_flags.DivideByZero then 2w else 0w) ||
           (if round_flags.Overflow then 4w else 0w) ||
           (if round_flags.Underflow_BeforeRounding then 8w else 0w) ||
           (if round_flags.Precision then 16w else 0w)) asl.regstate)
Proof
  qx_genl_tac [`left`, `right`, `fpcr`, `mode`, `asl`] \\ strip_tac
  \\ Cases_on `machine_ieee$fp64_isNan left \/ machine_ieee$fp64_isNan right`
  >- (
    Q.SUBGOAL_THEN
         `float_value (fp64_to_float left) = NaN \/
          float_value (fp64_to_float right) = NaN` ASSUME_TAC
    >- (
      namedCases_on `float_value (fp64_to_float left)` ["left_number", "", ""]
      \\ namedCases_on `float_value (fp64_to_float right)` ["right_number", "", ""]
      \\ fs [machine_ieeeTheory.fp64_isNan_def, binary_ieeeTheory.float_is_nan_def])
    \\ `~word_bit 24 fpcr /\ ~word_bit 8 fpcr /\ ~word_bit 25 fpcr` by (
      qpat_assum `fpcr && ~0x00C00000w = 0w` mp_tac
      \\ blastLib.BBLAST_TAC)
    \\ qspecl_then [`mode`, `fp64_to_float left`, `fp64_to_float right`]
         mp_tac binary_ieeeTheory.float_add_nan
    \\ asm_simp_tac std_ss [] \\ disch_then SUBST1_TAC
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [LET_THM, binary_ieeeTheory.check_for_signalling_def,
          binary_ieeeTheory.clear_flags_def]
    \\ qabbrev_tac `expected = float_to_fp64
         (float_some_qnan (FP_Add mode (fp64_to_float left) (fp64_to_float right)))`
    \\ `machine_ieee$fp64_isNan expected` by
      simp [Abbr `expected`, machine_ieeeTheory.fp64_isNan_def,
            machine_ieeeTheory.fp64_to_float_float_to_fp64,
            binary_ieeeTheory.some_nan_properties]
    \\ mp_tac FPAdd64_NaN
    \\ impl_tac >- asm_simp_tac std_ss []
    \\ disch_then SUBST1_TAC
    \\ Cases_on `float_is_signalling (fp64_to_float left) \/
                        float_is_signalling (fp64_to_float right)`
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPNaNResult_nan, machine_ieeeTheory.fp64_isSignallingNan_def,
          seqS, bindS, returnS, sail2_state_monadTheory.write_regS_def,
          sail2_state_monadTheory.updateS_def, FPSR_write_read])
  \\ namedCases_on `float_value (fp64_to_float left)` ["left_real", "", ""]
  \\ namedCases_on `float_value (fp64_to_float right)` ["right_real", "", ""]
  \\ fs [machine_ieeeTheory.fp64_isNan_def, binary_ieeeTheory.float_is_nan_def]
  >- (
    qabbrev_tac `negative =
      if left_real = 0 /\ right_real = 0 /\
         (fp64_to_float left).Sign = (fp64_to_float right).Sign then
        (fp64_to_float left).Sign = 1w
      else mode = roundTowardNegative`
    \\ `float_add mode (fp64_to_float left) (fp64_to_float right) =
         float_round_with_flags mode negative (left_real + right_real)` by (
      qspecl_then
           [`mode`, `fp64_to_float left`, `fp64_to_float right`, `left_real`, `right_real`]
           mp_tac binary_ieeeTheory.float_add_finite
      \\ asm_simp_tac std_ss [Abbr `negative`])
    \\ namedCases_on
         `(float_round_with_flags mode negative (left_real + right_real) :
           flags # (52,11) float)` ["round_flags expected"]
    \\ qspecl_then [`mode`, `negative`, `left_real + right_real`]
         mp_tac (INST_TYPE [``:'t`` |-> ``:52``, ``:'w`` |-> ``:11``]
           float_round_with_flags_exceptions)
    \\ asm_simp_tac std_ss [LET_THM] \\ strip_tac
    \\ `~float_is_nan expected` by (
      qspecl_then [`mode`, `negative`, `left_real + right_real`]
           mp_tac float_round_with_flags_not_nan
      \\ asm_simp_tac std_ss [LET_THM])
    \\ qspecl_then [`left`, `right`, `fpcr`, `mode`, `left_real`, `right_real`, `asl`]
         mp_tac FPAdd64_finite
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [LET_THM, FPNaNResult_not_nan, machine_ieeeTheory.fp64_isNan_def,
          machine_ieeeTheory.fp64_to_float_float_to_fp64])
  >- (
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [binary_ieeeTheory.float_add_def, LET_THM,
          binary_ieeeTheory.clear_flags_def,
          machine_ieeeTheory.float_to_fp64_fp64_to_float, FPSR_write_read]
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPNaNResult_not_nan, machine_ieeeTheory.fp64_isNan_def,
          binary_ieeeTheory.float_is_nan_def]
    \\ imp_res_tac FPUnpack64_finite
    \\ imp_res_tac FPUnpack64_infinite
    \\ imp_res_tac FPInfinity64_input
    \\ Cases_on `left_real = 0`
    \\ fs []
    \\ Cases_on_word_value `(fp64_to_float right).Sign`
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPAdd_def, FPUnpack64_rounding_bits, FPProcessNaNs_def, LET_THM,
          undefined_FPType_def, preludeTheory.undefined_bitvector_def,
          preludeTheory.undefined_real_def,
          sail2_state_monadTheory.undefined_boolS_def,
          sail2_state_monadTheory.choose_boolS_def,
          sail2_state_monadTheory.chooseS_def,
          sail2_stateTheory.internal_pickS_def,
          sail2_state_monadTheory.assert_expS_def,
          bindS, seqS, returnS, asl_word_rws])
  >- (
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [binary_ieeeTheory.float_add_def, LET_THM,
          binary_ieeeTheory.clear_flags_def,
          machine_ieeeTheory.float_to_fp64_fp64_to_float, FPSR_write_read]
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPNaNResult_not_nan, machine_ieeeTheory.fp64_isNan_def,
          binary_ieeeTheory.float_is_nan_def]
    \\ imp_res_tac FPUnpack64_finite
    \\ imp_res_tac FPUnpack64_infinite
    \\ imp_res_tac FPInfinity64_input
    \\ Cases_on `right_real = 0`
    \\ fs []
    \\ Cases_on_word_value `(fp64_to_float left).Sign`
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPAdd_def, FPUnpack64_rounding_bits, FPProcessNaNs_def, LET_THM,
          undefined_FPType_def, preludeTheory.undefined_bitvector_def,
          preludeTheory.undefined_real_def,
          sail2_state_monadTheory.undefined_boolS_def,
          sail2_state_monadTheory.choose_boolS_def,
          sail2_state_monadTheory.chooseS_def,
          sail2_stateTheory.internal_pickS_def,
          sail2_state_monadTheory.assert_expS_def,
          bindS, seqS, returnS, asl_word_rws])
  >- (
    `~word_bit 8 fpcr` by (
      qpat_assum `_ && _ = (0w : word32)` mp_tac
      \\ blastLib.BBLAST_TAC)
    \\ `~machine_ieee$fp64_isSignallingNan left` by
      simp [machine_ieeeTheory.fp64_isSignallingNan_def,
            binary_ieeeTheory.float_is_signalling_def,
            binary_ieeeTheory.float_is_nan_def]
    \\ imp_res_tac FPUnpack64_infinite
    \\ `FPInfinity 64 (fp64_to_float left).Sign = returnS left` by (
      irule FPInfinity64_input \\ asm_simp_tac std_ss [])
    \\ Cases_on_word_value `(fp64_to_float left).Sign`
    \\ Cases_on_word_value `(fp64_to_float right).Sign`
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [binary_ieeeTheory.float_add_def, LET_THM,
          binary_ieeeTheory.invalidop_flags_def, binary_ieeeTheory.clear_flags_def,
          machine_ieeeTheory.float_to_fp64_fp64_to_float, FPSR_write_read]
    \\ `~machine_ieee$fp64_isNan left /\ ~machine_ieee$fp64_isNan right` by
      simp [machine_ieeeTheory.fp64_isNan_def, binary_ieeeTheory.float_is_nan_def]
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPNaNResult_def, CONJUNCT2 fp64_nan_bits, fp64_default_nan,
          fp64_some_qnan]
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPAdd_def, FPUnpack64_rounding_bits, FPProcessNaNs_def,
          FPDefaultNaN64, FPProcessException_InvalidOp,
          sail2_operators_mwordsTheory.not_vec_def, LET_THM,
          undefined_FPType_def, preludeTheory.undefined_bitvector_def,
          preludeTheory.undefined_real_def,
          sail2_state_monadTheory.undefined_boolS_def,
          sail2_state_monadTheory.choose_boolS_def,
          sail2_state_monadTheory.chooseS_def,
          sail2_stateTheory.internal_pickS_def,
          sail2_state_monadTheory.assert_expS_def,
          sail2_state_monadTheory.write_regS_def,
          sail2_state_monadTheory.updateS_def,
          bindS, seqS, returnS, asl_word_rws])
QED

Theorem FPSub64:
  !left : word64. !right : word64. !fpcr mode asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    armv86a$FPRoundingMode fpcr = returnS (asl_fp64_rounding mode) ==>
    let (round_flags, expected) =
      float_sub mode (fp64_to_float left) (fp64_to_float right) in
    FPSub left right fpcr asl =
      returnS (FPNaNResult (float_to_fp64 expected, left, right, right))
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate ||
           (if round_flags.InvalidOp then 1w else 0w) ||
           (if round_flags.DivideByZero then 2w else 0w) ||
           (if round_flags.Overflow then 4w else 0w) ||
           (if round_flags.Underflow_BeforeRounding then 8w else 0w) ||
           (if round_flags.Precision then 16w else 0w)) asl.regstate)
Proof
  qx_genl_tac [`left`, `right`, `fpcr`, `mode`, `asl`] \\ strip_tac
  \\ Cases_on `machine_ieee$fp64_isNan left \/ machine_ieee$fp64_isNan right`
  >- (
    Q.SUBGOAL_THEN
         `float_value (fp64_to_float left) = NaN \/
          float_value (fp64_to_float right) = NaN` ASSUME_TAC
    >- (
      namedCases_on `float_value (fp64_to_float left)` ["left_number", "", ""]
      \\ namedCases_on `float_value (fp64_to_float right)` ["right_number", "", ""]
      \\ fs [machine_ieeeTheory.fp64_isNan_def, binary_ieeeTheory.float_is_nan_def])
    \\ `~word_bit 24 fpcr /\ ~word_bit 8 fpcr /\ ~word_bit 25 fpcr` by (
      qpat_assum `fpcr && ~0x00C00000w = 0w` mp_tac
      \\ blastLib.BBLAST_TAC)
    \\ qspecl_then [`mode`, `fp64_to_float left`, `fp64_to_float right`]
         mp_tac binary_ieeeTheory.float_sub_nan
    \\ asm_simp_tac std_ss [] \\ disch_then SUBST1_TAC
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [LET_THM, binary_ieeeTheory.check_for_signalling_def,
          binary_ieeeTheory.clear_flags_def]
    \\ qabbrev_tac `expected = float_to_fp64
         (float_some_qnan (FP_Sub mode (fp64_to_float left) (fp64_to_float right)))`
    \\ `machine_ieee$fp64_isNan expected` by
      simp [Abbr `expected`, machine_ieeeTheory.fp64_isNan_def,
            machine_ieeeTheory.fp64_to_float_float_to_fp64,
            binary_ieeeTheory.some_nan_properties]
    \\ mp_tac FPSub64_NaN
    \\ impl_tac >- asm_simp_tac std_ss []
    \\ disch_then SUBST1_TAC
    \\ Cases_on `float_is_signalling (fp64_to_float left) \/
                        float_is_signalling (fp64_to_float right)`
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPNaNResult_nan, machine_ieeeTheory.fp64_isSignallingNan_def,
          seqS, bindS, returnS, sail2_state_monadTheory.write_regS_def,
          sail2_state_monadTheory.updateS_def, FPSR_write_read])
  \\ namedCases_on `float_value (fp64_to_float left)` ["left_real", "", ""]
  \\ namedCases_on `float_value (fp64_to_float right)` ["right_real", "", ""]
  \\ fs [machine_ieeeTheory.fp64_isNan_def, binary_ieeeTheory.float_is_nan_def]
  >- (
    qabbrev_tac `negative =
      if left_real = 0 /\ right_real = 0 /\
         (fp64_to_float left).Sign <> (fp64_to_float right).Sign then
        (fp64_to_float left).Sign = 1w
      else mode = roundTowardNegative`
    \\ `float_sub mode (fp64_to_float left) (fp64_to_float right) =
         float_round_with_flags mode negative (left_real - right_real)` by (
      qspecl_then
           [`mode`, `fp64_to_float left`, `fp64_to_float right`, `left_real`, `right_real`]
           mp_tac binary_ieeeTheory.float_sub_finite
      \\ asm_simp_tac std_ss [Abbr `negative`])
    \\ namedCases_on
         `(float_round_with_flags mode negative (left_real - right_real) :
           flags # (52,11) float)` ["round_flags expected"]
    \\ qspecl_then [`mode`, `negative`, `left_real - right_real`]
         mp_tac (INST_TYPE [``:'t`` |-> ``:52``, ``:'w`` |-> ``:11``]
           float_round_with_flags_exceptions)
    \\ asm_simp_tac std_ss [LET_THM] \\ strip_tac
    \\ `~float_is_nan expected` by (
      qspecl_then [`mode`, `negative`, `left_real - right_real`]
           mp_tac float_round_with_flags_not_nan
      \\ asm_simp_tac std_ss [LET_THM])
    \\ qspecl_then [`left`, `right`, `fpcr`, `mode`, `left_real`, `right_real`, `asl`]
         mp_tac FPSub64_finite
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [LET_THM, FPNaNResult_not_nan, machine_ieeeTheory.fp64_isNan_def,
          machine_ieeeTheory.fp64_to_float_float_to_fp64])
  >- (
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [binary_ieeeTheory.float_sub_def, LET_THM,
          binary_ieeeTheory.clear_flags_def,
          GSYM (CONJUNCT1 machine_ieeeTheory.fp64_negate),
          machine_ieeeTheory.float_to_fp64_fp64_to_float, FPSR_write_read]
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPNaNResult_not_nan, fp64_negate_nan, machine_ieeeTheory.fp64_isNan_def,
          binary_ieeeTheory.float_is_nan_def]
    \\ imp_res_tac FPUnpack64_finite
    \\ imp_res_tac FPUnpack64_infinite
    \\ imp_res_tac FPInfinity64_negated_input
    \\ Cases_on `left_real = 0`
    \\ fs []
    \\ Cases_on_word_value `(fp64_to_float right).Sign`
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPSub_def, FPUnpack64_rounding_bits, FPProcessNaNs_def, LET_THM,
          undefined_FPType_def, preludeTheory.undefined_bitvector_def,
          preludeTheory.undefined_real_def,
          sail2_state_monadTheory.undefined_boolS_def,
          sail2_state_monadTheory.choose_boolS_def,
          sail2_state_monadTheory.chooseS_def,
          sail2_stateTheory.internal_pickS_def,
          sail2_state_monadTheory.assert_expS_def,
          bindS, seqS, returnS, asl_word_rws]
    \\ qpat_assum `FPInfinity _ _ = _`
         (fn packed => rewrite_tac
           [PURE_REWRITE_RULE [EVAL ``~(1w:word1)``, EVAL ``~(0w:word1)``]
             packed, returnS]))
  >- (
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [binary_ieeeTheory.float_sub_def, LET_THM,
          binary_ieeeTheory.clear_flags_def,
          machine_ieeeTheory.float_to_fp64_fp64_to_float, FPSR_write_read]
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPNaNResult_not_nan, machine_ieeeTheory.fp64_isNan_def,
          binary_ieeeTheory.float_is_nan_def]
    \\ imp_res_tac FPUnpack64_finite
    \\ imp_res_tac FPUnpack64_infinite
    \\ imp_res_tac FPInfinity64_input
    \\ Cases_on `right_real = 0`
    \\ fs []
    \\ Cases_on_word_value `(fp64_to_float left).Sign`
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPSub_def, FPUnpack64_rounding_bits, FPProcessNaNs_def, LET_THM,
          undefined_FPType_def, preludeTheory.undefined_bitvector_def,
          preludeTheory.undefined_real_def,
          sail2_state_monadTheory.undefined_boolS_def,
          sail2_state_monadTheory.choose_boolS_def,
          sail2_state_monadTheory.chooseS_def,
          sail2_stateTheory.internal_pickS_def,
          sail2_state_monadTheory.assert_expS_def,
          bindS, seqS, returnS, asl_word_rws])
  >- (
    `~word_bit 8 fpcr` by (
      qpat_assum `_ && _ = (0w : word32)` mp_tac
      \\ blastLib.BBLAST_TAC)
    \\ `~machine_ieee$fp64_isSignallingNan left` by
      simp [machine_ieeeTheory.fp64_isSignallingNan_def,
            binary_ieeeTheory.float_is_signalling_def,
            binary_ieeeTheory.float_is_nan_def]
    \\ imp_res_tac FPUnpack64_infinite
    \\ `FPInfinity 64 (fp64_to_float left).Sign = returnS left` by (
      irule FPInfinity64_input \\ asm_simp_tac std_ss [])
    \\ Cases_on_word_value `(fp64_to_float left).Sign`
    \\ Cases_on_word_value `(fp64_to_float right).Sign`
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [binary_ieeeTheory.float_sub_def, LET_THM,
          binary_ieeeTheory.invalidop_flags_def, binary_ieeeTheory.clear_flags_def,
          machine_ieeeTheory.float_to_fp64_fp64_to_float, FPSR_write_read]
    \\ `~machine_ieee$fp64_isNan left /\ ~machine_ieee$fp64_isNan right` by
      simp [machine_ieeeTheory.fp64_isNan_def, binary_ieeeTheory.float_is_nan_def]
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPNaNResult_def, CONJUNCT2 fp64_nan_bits, fp64_default_nan,
          fp64_some_qnan]
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPSub_def, FPUnpack64_rounding_bits, FPProcessNaNs_def,
          FPDefaultNaN64, FPProcessException_InvalidOp,
          sail2_operators_mwordsTheory.not_vec_def, LET_THM,
          undefined_FPType_def, preludeTheory.undefined_bitvector_def,
          preludeTheory.undefined_real_def,
          sail2_state_monadTheory.undefined_boolS_def,
          sail2_state_monadTheory.choose_boolS_def,
          sail2_state_monadTheory.chooseS_def,
          sail2_stateTheory.internal_pickS_def,
          sail2_state_monadTheory.assert_expS_def,
          sail2_state_monadTheory.write_regS_def,
          sail2_state_monadTheory.updateS_def,
          bindS, seqS, returnS, asl_word_rws])
QED
















Theorem fp_flags_word:
  !round_flags : flags.
    (((0w : 27 word) @@ (v2w [round_flags.Precision] : word1) @@
     (v2w [round_flags.Underflow_BeforeRounding] : word1) @@
     (v2w [round_flags.Overflow] : word1) @@
     (v2w [round_flags.DivideByZero] : word1) @@
     (v2w [round_flags.InvalidOp] : word1)) : word32) =
    (if round_flags.InvalidOp then 1w else 0w) ||
    (if round_flags.DivideByZero then 2w else 0w) ||
    (if round_flags.Overflow then 4w else 0w) ||
    (if round_flags.Underflow_BeforeRounding then 8w else 0w) ||
    (if round_flags.Precision then 16w else 0w)
Proof
  gen_tac >> blastLib.BBLAST_TAC
QED

fun fp_binop_tac dfn_def flags_def spec asl_defs decode float_op asl_op =
  let
    fun wrap pre q post = QUOTE pre :: q @ [QUOTE post]
    val with_flags = flags_def |> SPEC_ALL |> concl |> lhs |> strip_comb |> fst
  in
    rw[l3_models_asl_instr_def, l3_models_asl_def] >>
    gvs[encode_rws] >> l3_decode_tac >>
    rpt gen_tac >> strip_tac >>
    `l3.exception = NoException` by fs[state_rel_def] >>
    Cases_on `l3.FPCR && ~0x00C00000w = 0w` >>
    gvs[Run_def, dfn_def, CheckFP_def, D_def, write'D_def,
        FPSetFlags_def, raise'exception_def] >>
    pairarg_tac >> gvs[] >>
    qmatch_asmsub_rename_tac `^with_flags _ _ _ = (round_flags, result)` >>
    asl_cexecute_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac decode >>
    `state_rel l3 seen /\ asl_sys_regs_ok seen` by
      (unabbrev_all_tac >> state_rel_tac[]) >>
    `CheckFPAdvSIMDEnabled64 () seen = returnS () seen` by
      (irule CheckFPAdvSIMDEnabled64_ok >> simp[]) >>
    `V_read 64 (&w2n left) seen = (returnS (l3.FP_REG left) seen : word64 res)` by
      metis_tac[V_read64] >>
    `V_read 64 (&w2n right) seen = (returnS (l3.FP_REG right) seen : word64 res)` by
      metis_tac[V_read64] >>
    `read_regS FPCR_ref seen = (returnS l3.FPCR seen : word32 res)` by
      metis_tac[FPCR_read] >>
    namedCases_on
      (wrap "(" float_op " (arm8$FPRoundingMode l3)\n\
        \ (fp64_to_float (l3.FP_REG left)) (fp64_to_float (l3.FP_REG right)) :\n\
        \ flags # (52,11) float)") ["ieee_flags ieee_result"] >>
    gvs[flags_def] >>
    `l3.FPCR && ~0x00C00000w = 0w` by simp[wordsTheory.WORD_AND_COMM] >>
    qspecl_then [`l3.FP_REG left`, `l3.FP_REG right`, `l3.FPCR`,
      `arm8$FPRoundingMode l3`, `seen`] mp_tac spec >>
    asm_simp_tac std_ss [FPRoundingMode_agrees, LET_THM] >>
    strip_tac >>
    qabbrev_tac `actual = FPNaNResult (float_to_fp64 ieee_result,
      l3.FP_REG left, l3.FP_REG right, l3.FP_REG right)` >>
    `FPSR_ref.read_from seen.regstate = l3.FPSR` by
      fs[state_rel_def, read_rel_def] >>
    qabbrev_tac `status =
      (0w : 27 word) @@ (v2w [ieee_flags.Precision] : word1) @@
      (v2w [ieee_flags.Underflow_BeforeRounding] : word1) @@
      (v2w [ieee_flags.Overflow] : word1) @@
      (v2w [ieee_flags.DivideByZero] : word1) @@
      (v2w [ieee_flags.InvalidOp] : word1)` >>
    qabbrev_tac `flagged = seen with regstate :=
      FPSR_ref.write_to (l3.FPSR || status) seen.regstate` >>
    wrap "" asl_op " (l3.FP_REG left) (l3.FP_REG right) l3.FPCR seen =\n\
      \ returnS actual flagged" by
      asm_simp_tac std_ss [Abbr `flagged`, Abbr `status`, fp_flags_word] >>
    `state_rel (l3 with FPSR := l3.FPSR || status) flagged /\
     asl_sys_regs_ok flagged` by (
      qunabbrev_tac `flagged` >> irule FPSR_set_state_rel >> simp[]) >>
    qspecl_then [`l3 with FPSR := l3.FPSR || status`, `flagged`, `dst`, `actual`]
      mp_tac V_set64_state_rel >>
    simp[] >> disch_then (qx_choose_then `finished` strip_assume_tac) >>
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      (asl_defs @
       [preludeTheory.undefined_bitvector_def, LET_THM,
        lemTheory.w2ui_def, sail2_valuesTheory.make_the_value_def,
        sail2_valuesTheory.size_itself_int_def,
        lem_machine_wordTheory.size_itself_def,
        bindS, seqS, returnS, asl_word_rws]) >>
    gvs[Abbr `actual`]
  end;

Theorem l3_models_asl_FAdd:
  !right left dst.
    l3_models_asl_instr (FloatingPoint (FAdd (right, left, dst)))
Proof
  fp_binop_tac dfn'FAdd_def machine_ieeeTheory.fp64_add_with_flags_def
    FPAdd64
    [decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub_def,
     execute_aarch64_instrs_float_arithmetic_add_sub_def]
    `decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub _ _ _ _ _ seen`
    `float_add` `FPAdd`
QED

Theorem l3_models_asl_FSub:
  !right left dst.
    l3_models_asl_instr (FloatingPoint (FSub (right, left, dst)))
Proof
  fp_binop_tac dfn'FSub_def machine_ieeeTheory.fp64_sub_with_flags_def
    FPSub64
    [decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub_def,
     execute_aarch64_instrs_float_arithmetic_add_sub_def]
    `decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub _ _ _ _ _ seen`
    `float_sub` `FPSub`
QED



Theorem FPMul64_finite_zero:
  !left : word64. !right : word64. !fpcr left_real right_real.
    fpcr && ~0x00C00000w = 0w /\
    float_value (fp64_to_float left) = Float left_real /\
    float_value (fp64_to_float right) = Float right_real /\
    (left_real = 0 \/ right_real = 0) ==>
    FPMul left right fpcr =
      FPZero 64 (xor_vec (fp64_to_float left).Sign (fp64_to_float right).Sign)
Proof
  rpt gen_tac >> disch_tac >>
  Cases_on `left_real = 0` >>
  Cases_on `right_real = 0` >>
  fs [] >>
  simp_tac std_ss [FUN_EQ_THM] >> qx_gen_tac `asl` >>
  imp_res_tac FPUnpack64_finite >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPMul_def, FPUnpack64_rounding_bits, FPProcessNaNs_def, LET_THM,
     undefined_FPType_def, preludeTheory.undefined_bitvector_def,
     preludeTheory.undefined_real_def,
     sail2_state_monadTheory.undefined_boolS_def,
     sail2_state_monadTheory.choose_boolS_def,
     sail2_state_monadTheory.chooseS_def,
     sail2_stateTheory.internal_pickS_def,
     sail2_state_monadTheory.assert_expS_def,
     bindS, seqS, returnS, asl_word_rws] >>
  simp [sail2_operators_mwordsTheory.xor_vec_def]
QED

Theorem FPMul64_finite:
  !left : word64. !right : word64. !fpcr mode left_real right_real asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    armv86a$FPRoundingMode fpcr = returnS (asl_fp64_rounding mode) /\
    float_value (fp64_to_float left) = Float left_real /\
    float_value (fp64_to_float right) = Float right_real ==>
    let (round_flags, result) =
      float_mul mode (fp64_to_float left) (fp64_to_float right) in
    FPMul left right fpcr asl =
      returnS (float_to_fp64 result)
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate ||
           (if round_flags.Underflow_BeforeRounding then 8w else 0w) ||
           (if round_flags.Overflow then 4w else 0w) ||
           (if round_flags.Precision then 16w else 0w)) asl.regstate)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `left_real = 0 \/ right_real = 0`
  >- (
    `FPMul left right fpcr =
      FPZero 64 (xor_vec (fp64_to_float left).Sign (fp64_to_float right).Sign)` by (
      qspecl_then [`left`, `right`, `fpcr`, `left_real`, `right_real`]
        mp_tac FPMul64_finite_zero >>
      asm_simp_tac std_ss []) >>
    `float_mul mode (fp64_to_float left) (fp64_to_float right) =
      (clear_flags, if (fp64_to_float left).Sign <> (fp64_to_float right).Sign
        then float_minus_zero (:52 # 11) else float_plus_zero (:52 # 11))` by (
      qspecl_then [`mode`, `fp64_to_float left`, `fp64_to_float right`,
        `left_real`, `right_real`] mp_tac float_mul_finite_zero >>
      asm_simp_tac std_ss []) >>
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [LET_THM, binary_ieeeTheory.clear_flags_def, FPSR_write_read] >>
    Cases_on_word_value `(fp64_to_float left).Sign` >>
    Cases_on_word_value `(fp64_to_float right).Sign` >>
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [FPZero64, sail2_operators_mwordsTheory.xor_vec_def,
       binary_ieeeTheory.float_plus_zero_def, binary_ieeeTheory.float_minus_zero])
  >> fs [] >>
  qspecl_then [`left`, `right`, `fpcr`, `mode`, `left_real`, `right_real`, `asl`]
    mp_tac FPMul64_finite_nonzero >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss())) [LET_THM]
QED

Theorem float_mul_infinite:
  !mode. !left right : ('t, 'w) float.
    ~float_is_nan left /\ ~float_is_nan right /\
    (float_is_infinite left \/ float_is_infinite right) ==>
    float_mul mode left right =
      if float_is_zero left \/ float_is_zero right then
        (invalidop_flags, float_some_qnan (FP_Mul mode left right))
      else
        (clear_flags, if left.Sign = right.Sign then
          float_plus_infinity (:'t # 'w) else float_minus_infinity (:'t # 'w))
Proof
  rpt gen_tac >> disch_tac >>
  namedCases_on `float_value left` ["left_real", "", ""] >>
  namedCases_on `float_value right` ["right_real", "", ""] >>
  fs [binary_ieeeTheory.float_is_nan_def,
      binary_ieeeTheory.float_is_infinite_def,
      binary_ieeeTheory.float_is_zero_def, binary_ieeeTheory.float_mul_def]
QED

Theorem FPMul64_infinite:
  !left : word64. !right : word64. !fpcr asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    ~machine_ieee$fp64_isNan left /\ ~machine_ieee$fp64_isNan right /\
    (float_is_infinite (fp64_to_float left) \/
     float_is_infinite (fp64_to_float right)) ==>
    FPMul left right fpcr asl =
      if float_is_zero (fp64_to_float left) \/
         float_is_zero (fp64_to_float right) then
        returnS (0x7FF8000000000000w : word64)
          (asl with regstate := FPSR_ref.write_to
            (FPSR_ref.read_from asl.regstate || 1w) asl.regstate)
      else
        FPInfinity 64
          (xor_vec (fp64_to_float left).Sign (fp64_to_float right).Sign) asl
Proof
  rpt gen_tac >> disch_tac >>
  Cases_on `float_is_infinite (fp64_to_float left)` >>
  Cases_on `float_is_infinite (fp64_to_float right)` >>
  fs [] >>
  `~float_is_nan (fp64_to_float left) /\
   ~float_is_nan (fp64_to_float right) /\
   ~float_is_signalling (fp64_to_float left) /\
   ~float_is_signalling (fp64_to_float right)` by
    fs [machine_ieeeTheory.fp64_isNan_def,
        binary_ieeeTheory.float_is_signalling_def] >>
  `~(float_is_infinite (fp64_to_float left) /\
      float_is_zero (fp64_to_float left)) /\
   ~(float_is_infinite (fp64_to_float right) /\
      float_is_zero (fp64_to_float right))` by
    metis_tac [binary_ieeeTheory.float_distinct_finite,
               binary_ieeeTheory.float_is_zero_float_is_finite] >>
  Cases_on `float_is_zero (fp64_to_float left)` >>
  Cases_on `float_is_zero (fp64_to_float right)` >>
  fs [] >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPMul_def, FPUnpack64_rounding_bits,
     SIMP_RULE std_ss [LET_THM] FPUnpack64,
     FPProcessNaNs_def, FPDefaultNaN64,
     FPProcessException_rounding_bits, FPProcessException_zero,
     undefined_FPType_def, preludeTheory.undefined_bitvector_def,
     preludeTheory.undefined_real_def,
     sail2_state_monadTheory.undefined_boolS_def,
     sail2_state_monadTheory.choose_boolS_def,
     sail2_state_monadTheory.chooseS_def,
     sail2_stateTheory.internal_pickS_def,
     sail2_state_monadTheory.assert_expS_def,
     sail2_state_monadTheory.write_regS_def,
     sail2_state_monadTheory.updateS_def,
     bindS, seqS, returnS, LET_THM, asl_word_rws] >>
  simp [sail2_operators_mwordsTheory.xor_vec_def]
QED

Theorem FPMul64:
  !left : word64. !right : word64. !fpcr mode asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    armv86a$FPRoundingMode fpcr = returnS (asl_fp64_rounding mode) ==>
    let (round_flags, expected) =
      float_mul mode (fp64_to_float left) (fp64_to_float right) in
    FPMul left right fpcr asl =
      returnS (FPNaNResult (float_to_fp64 expected, left, right, right))
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate ||
           (if round_flags.InvalidOp then 1w else 0w) ||
           (if round_flags.DivideByZero then 2w else 0w) ||
           (if round_flags.Overflow then 4w else 0w) ||
           (if round_flags.Underflow_BeforeRounding then 8w else 0w) ||
           (if round_flags.Precision then 16w else 0w)) asl.regstate)
Proof
  qx_genl_tac [`left`, `right`, `fpcr`, `mode`, `asl`] \\ strip_tac
  \\ Cases_on `machine_ieee$fp64_isNan left \/ machine_ieee$fp64_isNan right`
  >- (
    Q.SUBGOAL_THEN
         `float_value (fp64_to_float left) = NaN \/
          float_value (fp64_to_float right) = NaN` ASSUME_TAC
    >- (
      namedCases_on `float_value (fp64_to_float left)` ["left_number", "", ""]
      \\ namedCases_on `float_value (fp64_to_float right)` ["right_number", "", ""]
      \\ fs [machine_ieeeTheory.fp64_isNan_def, binary_ieeeTheory.float_is_nan_def])
    \\ `~word_bit 24 fpcr /\ ~word_bit 8 fpcr /\ ~word_bit 25 fpcr` by (
      qpat_assum `fpcr && ~0x00C00000w = 0w` mp_tac
      \\ blastLib.BBLAST_TAC)
    \\ qspecl_then [`mode`, `fp64_to_float left`, `fp64_to_float right`]
         mp_tac binary_ieeeTheory.float_mul_nan
    \\ asm_simp_tac std_ss [] \\ disch_then SUBST1_TAC
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [LET_THM, binary_ieeeTheory.check_for_signalling_def,
          binary_ieeeTheory.clear_flags_def]
    \\ qabbrev_tac `expected = float_to_fp64
         (float_some_qnan (FP_Mul mode (fp64_to_float left) (fp64_to_float right)))`
    \\ `machine_ieee$fp64_isNan expected` by
      simp [Abbr `expected`, machine_ieeeTheory.fp64_isNan_def,
            machine_ieeeTheory.fp64_to_float_float_to_fp64,
            binary_ieeeTheory.some_nan_properties]
    \\ mp_tac FPMul64_NaN
    \\ impl_tac >- asm_simp_tac std_ss []
    \\ disch_then SUBST1_TAC
    \\ Cases_on `float_is_signalling (fp64_to_float left) \/
                        float_is_signalling (fp64_to_float right)`
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPNaNResult_nan, machine_ieeeTheory.fp64_isSignallingNan_def,
          seqS, bindS, returnS, sail2_state_monadTheory.write_regS_def,
          sail2_state_monadTheory.updateS_def, FPSR_write_read])
  >> fs [] >>
  Cases_on `float_is_infinite (fp64_to_float left) \/
    float_is_infinite (fp64_to_float right)`
  >- (
    `~float_is_nan (fp64_to_float left) /\
     ~float_is_nan (fp64_to_float right)` by
      fs [machine_ieeeTheory.fp64_isNan_def] >>
    `float_mul mode (fp64_to_float left) (fp64_to_float right) =
      if float_is_zero (fp64_to_float left) \/
         float_is_zero (fp64_to_float right) then
        (invalidop_flags, float_some_qnan
          (FP_Mul mode (fp64_to_float left) (fp64_to_float right)))
      else
        (clear_flags,
         if (fp64_to_float left).Sign = (fp64_to_float right).Sign then
           float_plus_infinity (:52 # 11) else float_minus_infinity (:52 # 11))` by (
      qspecl_then [`mode`, `fp64_to_float left`, `fp64_to_float right`]
        mp_tac float_mul_infinite >>
      asm_simp_tac std_ss []) >>
    `FPMul left right fpcr asl =
      if float_is_zero (fp64_to_float left) \/
         float_is_zero (fp64_to_float right) then
        returnS (0x7FF8000000000000w : word64)
          (asl with regstate := FPSR_ref.write_to
            (FPSR_ref.read_from asl.regstate || 1w) asl.regstate)
      else FPInfinity 64
        (xor_vec (fp64_to_float left).Sign (fp64_to_float right).Sign) asl` by (
      qspecl_then [`left`, `right`, `fpcr`, `asl`] mp_tac FPMul64_infinite >>
      asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss())) []) >>
    Cases_on `float_is_zero (fp64_to_float left) \/
      float_is_zero (fp64_to_float right)`
    >- (
      asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
        [LET_THM, binary_ieeeTheory.invalidop_flags_def,
         binary_ieeeTheory.clear_flags_def] >>
      asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
        [FPNaNResult_def, CONJUNCT2 fp64_nan_bits, fp64_default_nan,
         machine_ieeeTheory.fp64_isNan_def,
         machine_ieeeTheory.fp64_to_float_float_to_fp64,
         binary_ieeeTheory.some_nan_properties])
    >> asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [LET_THM, binary_ieeeTheory.clear_flags_def, FPSR_write_read] >>
    Cases_on_word_value `(fp64_to_float left).Sign` >>
    Cases_on_word_value `(fp64_to_float right).Sign` >>
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [FPNaNResult_not_nan, machine_ieeeTheory.fp64_isNan_def, FPInfinity64,
       sail2_operators_mwordsTheory.xor_vec_def,
       machine_ieeeTheory.fp64_isSignallingNan_def,
       machine_ieeeTheory.fp64_to_float_float_to_fp64,
       binary_ieeeTheory.float_is_signalling_def,
       binary_ieeeTheory.float_plus_infinity_def,
       binary_ieeeTheory.float_minus_infinity_def,
       binary_ieeeTheory.float_negate_def,
       binary_ieeeTheory.float_is_nan_def, binary_ieeeTheory.float_value_def])
  >> namedCases_on `float_value (fp64_to_float left)` ["left_real", "", ""] >>
  namedCases_on `float_value (fp64_to_float right)` ["right_real", "", ""] >>
  fs [machine_ieeeTheory.fp64_isNan_def,
      binary_ieeeTheory.float_is_nan_def, binary_ieeeTheory.float_is_infinite_def] >>
  qabbrev_tac `negative = ((fp64_to_float left).Sign <> (fp64_to_float right).Sign)` >>
  `float_mul mode (fp64_to_float left) (fp64_to_float right) =
    float_round_with_flags mode negative (left_real * right_real)` by (
    qspecl_then [`mode`, `fp64_to_float left`, `fp64_to_float right`,
      `left_real`, `right_real`] mp_tac binary_ieeeTheory.float_mul_finite >>
    asm_simp_tac std_ss [Abbr `negative`]) >>
  namedCases_on
    `(float_round_with_flags mode negative (left_real * right_real) :
      flags # (52,11) float)` ["round_flags expected"] >>
  qspecl_then [`mode`, `negative`, `left_real * right_real`]
    mp_tac (INST_TYPE [``:'t`` |-> ``:52``, ``:'w`` |-> ``:11``]
      float_round_with_flags_exceptions) >>
  asm_simp_tac std_ss [LET_THM] >> strip_tac >>
  `~float_is_nan expected` by (
    qspecl_then [`mode`, `negative`, `left_real * right_real`]
      mp_tac float_round_with_flags_not_nan >>
    asm_simp_tac std_ss [LET_THM]) >>
  qspecl_then [`left`, `right`, `fpcr`, `mode`, `left_real`, `right_real`, `asl`]
    mp_tac FPMul64_finite >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [LET_THM, FPNaNResult_not_nan, machine_ieeeTheory.fp64_isNan_def,
     machine_ieeeTheory.fp64_to_float_float_to_fp64]
QED

Theorem float_div_special:
  !mode. !left right : ('t, 'w) float.
    ~float_is_nan left /\ ~float_is_nan right /\
    (float_is_infinite left \/ float_is_infinite right \/
     float_is_zero left \/ float_is_zero right) ==>
    float_div mode left right =
      if (float_is_infinite left /\ float_is_infinite right) \/
         (float_is_zero left /\ float_is_zero right) then
        (invalidop_flags, float_some_qnan (FP_Div mode left right))
      else if float_is_infinite left \/ float_is_zero right then
        ((if float_is_infinite left then clear_flags else dividezero_flags),
         if left.Sign = right.Sign then float_plus_infinity (:'t # 'w)
         else float_minus_infinity (:'t # 'w))
      else
        (clear_flags, if left.Sign = right.Sign then float_plus_zero (:'t # 'w)
                      else float_minus_zero (:'t # 'w))
Proof
  rpt gen_tac >> disch_tac >>
  namedCases_on `float_value left` ["left_real", "", ""] >>
  namedCases_on `float_value right` ["right_real", "", ""] >>
  fs [binary_ieeeTheory.float_is_nan_def,
      binary_ieeeTheory.float_is_infinite_def,
      binary_ieeeTheory.float_is_zero_def, binary_ieeeTheory.float_div_def,
      float_round_with_flags_zero, REAL_DIV_LZERO] >>
  Cases_on `left.Sign = right.Sign` >>
  asm_simp_tac std_ss []
QED

Theorem FPDiv64_special:
  !left : word64. !right : word64. !fpcr asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    ~machine_ieee$fp64_isNan left /\ ~machine_ieee$fp64_isNan right /\
    (float_is_infinite (fp64_to_float left) \/
     float_is_infinite (fp64_to_float right) \/
     float_is_zero (fp64_to_float left) \/
     float_is_zero (fp64_to_float right)) ==>
    FPDiv left right fpcr asl =
      if (float_is_infinite (fp64_to_float left) /\
          float_is_infinite (fp64_to_float right)) \/
         (float_is_zero (fp64_to_float left) /\
          float_is_zero (fp64_to_float right)) then
        returnS (0x7FF8000000000000w : word64)
          (asl with regstate := FPSR_ref.write_to
            (FPSR_ref.read_from asl.regstate || 1w) asl.regstate)
      else if float_is_infinite (fp64_to_float left) \/
              float_is_zero (fp64_to_float right) then
        FPInfinity 64
          (xor_vec (fp64_to_float left).Sign (fp64_to_float right).Sign)
          (if float_is_infinite (fp64_to_float left) then asl
           else asl with regstate := FPSR_ref.write_to
             (FPSR_ref.read_from asl.regstate || 2w) asl.regstate)
      else
        FPZero 64
          (xor_vec (fp64_to_float left).Sign (fp64_to_float right).Sign) asl
Proof
  rpt gen_tac >> disch_tac >>
  `~(float_is_infinite (fp64_to_float left) /\
      float_is_zero (fp64_to_float left)) /\
   ~(float_is_infinite (fp64_to_float right) /\
      float_is_zero (fp64_to_float right))` by
    metis_tac [binary_ieeeTheory.float_distinct_finite,
               binary_ieeeTheory.float_is_zero_float_is_finite] >>
  Cases_on `float_is_infinite (fp64_to_float left)` >>
  Cases_on `float_is_infinite (fp64_to_float right)` >>
  Cases_on `float_is_zero (fp64_to_float left)` >>
  Cases_on `float_is_zero (fp64_to_float right)` >>
  fs [] >>
  `~float_is_nan (fp64_to_float left) /\
   ~float_is_nan (fp64_to_float right) /\
   ~float_is_signalling (fp64_to_float left) /\
   ~float_is_signalling (fp64_to_float right)` by
    fs [machine_ieeeTheory.fp64_isNan_def,
        binary_ieeeTheory.float_is_signalling_def] >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [FPDiv_def, FPUnpack64_rounding_bits,
     SIMP_RULE std_ss [LET_THM] FPUnpack64,
     FPProcessNaNs_def, FPDefaultNaN64, FPInfinity64,
     FPProcessException_rounding_bits, FPProcessException_zero,
     undefined_FPType_def, preludeTheory.undefined_bitvector_def,
     preludeTheory.undefined_real_def,
     sail2_state_monadTheory.undefined_boolS_def,
     sail2_state_monadTheory.choose_boolS_def,
     sail2_state_monadTheory.chooseS_def,
     sail2_stateTheory.internal_pickS_def,
     sail2_state_monadTheory.assert_expS_def,
     sail2_state_monadTheory.write_regS_def,
     sail2_state_monadTheory.updateS_def,
     bindS, seqS, returnS, LET_THM, asl_word_rws] >>
  simp [sail2_operators_mwordsTheory.xor_vec_def]
QED

Theorem FPDiv64:
  !left : word64. !right : word64. !fpcr mode asl.
    fpcr && ~0x00C00000w = 0w /\ asl_sys_regs_ok asl /\
    armv86a$FPRoundingMode fpcr = returnS (asl_fp64_rounding mode) ==>
    let (round_flags, expected) =
      float_div mode (fp64_to_float left) (fp64_to_float right) in
    FPDiv left right fpcr asl =
      returnS (FPNaNResult (float_to_fp64 expected, left, right, right))
        (asl with regstate := FPSR_ref.write_to
          (FPSR_ref.read_from asl.regstate ||
           (if round_flags.InvalidOp then 1w else 0w) ||
           (if round_flags.DivideByZero then 2w else 0w) ||
           (if round_flags.Overflow then 4w else 0w) ||
           (if round_flags.Underflow_BeforeRounding then 8w else 0w) ||
           (if round_flags.Precision then 16w else 0w)) asl.regstate)
Proof
  qx_genl_tac [`left`, `right`, `fpcr`, `mode`, `asl`] \\ strip_tac
  \\ Cases_on `machine_ieee$fp64_isNan left \/ machine_ieee$fp64_isNan right`
  >- (
    Q.SUBGOAL_THEN
         `float_value (fp64_to_float left) = NaN \/
          float_value (fp64_to_float right) = NaN` ASSUME_TAC
    >- (
      namedCases_on `float_value (fp64_to_float left)` ["left_number", "", ""]
      \\ namedCases_on `float_value (fp64_to_float right)` ["right_number", "", ""]
      \\ fs [machine_ieeeTheory.fp64_isNan_def, binary_ieeeTheory.float_is_nan_def])
    \\ `~word_bit 24 fpcr /\ ~word_bit 8 fpcr /\ ~word_bit 25 fpcr` by (
      qpat_assum `fpcr && ~0x00C00000w = 0w` mp_tac
      \\ blastLib.BBLAST_TAC)
    \\ qspecl_then [`mode`, `fp64_to_float left`, `fp64_to_float right`]
         mp_tac binary_ieeeTheory.float_div_nan
    \\ asm_simp_tac std_ss [] \\ disch_then SUBST1_TAC
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [LET_THM, binary_ieeeTheory.check_for_signalling_def,
          binary_ieeeTheory.clear_flags_def]
    \\ qabbrev_tac `expected = float_to_fp64
         (float_some_qnan (FP_Div mode (fp64_to_float left) (fp64_to_float right)))`
    \\ `machine_ieee$fp64_isNan expected` by
      simp [Abbr `expected`, machine_ieeeTheory.fp64_isNan_def,
            machine_ieeeTheory.fp64_to_float_float_to_fp64,
            binary_ieeeTheory.some_nan_properties]
    \\ mp_tac FPDiv64_NaN
    \\ impl_tac >- asm_simp_tac std_ss []
    \\ disch_then SUBST1_TAC
    \\ Cases_on `float_is_signalling (fp64_to_float left) \/
                        float_is_signalling (fp64_to_float right)`
    \\ asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
         [FPNaNResult_nan, machine_ieeeTheory.fp64_isSignallingNan_def,
          seqS, bindS, returnS, sail2_state_monadTheory.write_regS_def,
          sail2_state_monadTheory.updateS_def, FPSR_write_read])
  >> fs [] >>
  Cases_on `float_is_infinite (fp64_to_float left) \/
    float_is_infinite (fp64_to_float right) \/
    float_is_zero (fp64_to_float left) \/ float_is_zero (fp64_to_float right)`
  >- (
    `~float_is_nan (fp64_to_float left) /\
     ~float_is_nan (fp64_to_float right)` by
      fs [machine_ieeeTheory.fp64_isNan_def] >>
    qspecl_then [`mode`, `fp64_to_float left`, `fp64_to_float right`]
      mp_tac float_div_special >>
    impl_tac >- asm_simp_tac std_ss [] >>
    disch_then assume_tac >>
    qspecl_then [`left`, `right`, `fpcr`, `asl`] mp_tac FPDiv64_special >>
    impl_tac
    >- asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss())) [] >>
    disch_then assume_tac >>
    Cases_on
      `(float_is_infinite (fp64_to_float left) /\
        float_is_infinite (fp64_to_float right)) \/
       (float_is_zero (fp64_to_float left) /\
        float_is_zero (fp64_to_float right))`
    >- (
      asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
        [LET_THM, binary_ieeeTheory.invalidop_flags_def,
         binary_ieeeTheory.clear_flags_def] >>
      asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
        [FPNaNResult_def, CONJUNCT2 fp64_nan_bits, fp64_default_nan,
         machine_ieeeTheory.fp64_isNan_def,
         machine_ieeeTheory.fp64_to_float_float_to_fp64,
         binary_ieeeTheory.some_nan_properties])
    >> Cases_on `float_is_infinite (fp64_to_float left) \/
         float_is_zero (fp64_to_float right)`
    >- (
      Cases_on `float_is_infinite (fp64_to_float left)` >>
      asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
        [LET_THM, binary_ieeeTheory.clear_flags_def,
         binary_ieeeTheory.dividezero_flags_def, FPSR_write_read] >>
      Cases_on_word_value `(fp64_to_float left).Sign` >>
      Cases_on_word_value `(fp64_to_float right).Sign` >>
      asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
        [FPNaNResult_not_nan, machine_ieeeTheory.fp64_isNan_def, FPInfinity64,
         sail2_operators_mwordsTheory.xor_vec_def,
         machine_ieeeTheory.fp64_isSignallingNan_def,
         machine_ieeeTheory.fp64_to_float_float_to_fp64,
         binary_ieeeTheory.float_is_signalling_def,
         binary_ieeeTheory.float_plus_infinity_def,
         binary_ieeeTheory.float_minus_infinity_def,
         binary_ieeeTheory.float_negate_def,
         binary_ieeeTheory.float_is_nan_def, binary_ieeeTheory.float_value_def])
    >> asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [LET_THM, binary_ieeeTheory.clear_flags_def, FPSR_write_read] >>
    Cases_on_word_value `(fp64_to_float left).Sign` >>
    Cases_on_word_value `(fp64_to_float right).Sign` >>
    asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
      [FPNaNResult_not_nan, machine_ieeeTheory.fp64_isNan_def, FPZero64,
       sail2_operators_mwordsTheory.xor_vec_def,
       machine_ieeeTheory.fp64_isSignallingNan_def,
       machine_ieeeTheory.fp64_to_float_float_to_fp64,
       binary_ieeeTheory.float_is_signalling_def,
       binary_ieeeTheory.float_plus_zero_def,
       binary_ieeeTheory.float_minus_zero_def,
       binary_ieeeTheory.float_negate_def,
       binary_ieeeTheory.float_is_nan_def, binary_ieeeTheory.float_value_def])
  >> namedCases_on `float_value (fp64_to_float left)` ["left_real", "", ""] >>
  namedCases_on `float_value (fp64_to_float right)` ["right_real", "", ""] >>
  fs [machine_ieeeTheory.fp64_isNan_def,
      binary_ieeeTheory.float_is_nan_def, binary_ieeeTheory.float_is_infinite_def,
      binary_ieeeTheory.float_is_zero_def] >>
  qabbrev_tac `negative = ((fp64_to_float left).Sign <> (fp64_to_float right).Sign)` >>
  `float_div mode (fp64_to_float left) (fp64_to_float right) =
    float_round_with_flags mode negative (left_real / right_real)` by (
    qspecl_then [`mode`, `fp64_to_float left`, `fp64_to_float right`,
      `left_real`, `right_real`] mp_tac binary_ieeeTheory.float_div_finite >>
    asm_simp_tac std_ss [Abbr `negative`]) >>
  namedCases_on
    `(float_round_with_flags mode negative (left_real / right_real) :
      flags # (52,11) float)` ["round_flags expected"] >>
  qspecl_then [`mode`, `negative`, `left_real / right_real`]
    mp_tac (INST_TYPE [``:'t`` |-> ``:52``, ``:'w`` |-> ``:11``]
      float_round_with_flags_exceptions) >>
  asm_simp_tac std_ss [LET_THM] >> strip_tac >>
  `~float_is_nan expected` by (
    qspecl_then [`mode`, `negative`, `left_real / right_real`]
      mp_tac float_round_with_flags_not_nan >>
    asm_simp_tac std_ss [LET_THM]) >>
  qspecl_then [`left`, `right`, `fpcr`, `mode`, `left_real`, `right_real`, `asl`]
    mp_tac FPDiv64_finite_nonzero >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [LET_THM, FPNaNResult_not_nan, machine_ieeeTheory.fp64_isNan_def,
     machine_ieeeTheory.fp64_to_float_float_to_fp64]
QED

Theorem l3_models_asl_FMul:
  !right left dst.
    l3_models_asl_instr (FloatingPoint (FMul (right, left, dst)))
Proof
  fp_binop_tac dfn'FMul_def machine_ieeeTheory.fp64_mul_with_flags_def
    FPMul64
    [decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product_def,
     execute_aarch64_instrs_float_arithmetic_mul_product_def]
    `decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product _ _ _ _ _ seen`
    `float_mul` `FPMul`
QED

Theorem l3_models_asl_FDiv:
  !right left dst.
    l3_models_asl_instr (FloatingPoint (FDiv (right, left, dst)))
Proof
  fp_binop_tac dfn'FDiv_def machine_ieeeTheory.fp64_div_with_flags_def
    FPDiv64
    [decode_fdiv_float_aarch64_instrs_float_arithmetic_div_def,
     execute_aarch64_instrs_float_arithmetic_div_def]
    `decode_fdiv_float_aarch64_instrs_float_arithmetic_div _ _ _ _ seen`
    `float_div` `FPDiv`
QED

Theorem l3_models_asl_FSqrt:
  !src dst.
    l3_models_asl_instr (FloatingPoint (FSqrt (src, dst)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >> l3_decode_tac >>
  rpt gen_tac >> strip_tac >>
  `l3.exception = NoException` by fs[state_rel_def] >>
  Cases_on `l3.FPCR && ~0x00C00000w = 0w` >>
  gvs[Run_def, dfn'FSqrt_def, CheckFP_def, D_def, write'D_def,
      FPSetFlags_def, raise'exception_def] >>
  pairarg_tac >> gvs[] >>
  qmatch_asmsub_rename_tac
    `machine_ieee$fp64_sqrt_with_flags _ _ = (round_flags, result)` >>
  asl_cexecute_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac
    `decode_fsqrt_float_aarch64_instrs_float_arithmetic_unary _ _ _ _ seen` >>
  `state_rel l3 seen /\ asl_sys_regs_ok seen` by
    (unabbrev_all_tac >> state_rel_tac[]) >>
  `CheckFPAdvSIMDEnabled64 () seen = returnS () seen` by
    (irule CheckFPAdvSIMDEnabled64_ok >> simp[]) >>
  `V_read 64 (&w2n src) seen = (returnS (l3.FP_REG src) seen : word64 res)` by
    metis_tac[V_read64] >>
  `read_regS FPCR_ref seen = (returnS l3.FPCR seen : word32 res)` by
    metis_tac[FPCR_read] >>
  namedCases_on
    `(float_sqrt (arm8$FPRoundingMode l3)
      (fp64_to_float (l3.FP_REG src)) :
      flags # (52,11) float)` ["ieee_flags ieee_result"] >>
  gvs[machine_ieeeTheory.fp64_sqrt_with_flags_def] >>
  `l3.FPCR && ~0x00C00000w = 0w` by simp[wordsTheory.WORD_AND_COMM] >>
  qspecl_then [`l3.FP_REG src`, `l3.FPCR`,
    `arm8$FPRoundingMode l3`, `seen`] mp_tac FPSqrt64 >>
  asm_simp_tac std_ss [FPRoundingMode_agrees, LET_THM] >>
  strip_tac >>
  qabbrev_tac `actual = FPNaNResult (float_to_fp64 ieee_result,
    l3.FP_REG src, l3.FP_REG src, l3.FP_REG src)` >>
  `FPSR_ref.read_from seen.regstate = l3.FPSR` by
    fs[state_rel_def, read_rel_def] >>
  qabbrev_tac `status =
    if machine_ieee$fp64_isNan (l3.FP_REG src) then
      (0w : 31 word) @@ (v2w [machine_ieee$fp64_isSignallingNan (l3.FP_REG src)] : word1)
    else (0w : 27 word) @@ (v2w [ieee_flags.Precision] : word1) @@
    (v2w [ieee_flags.Underflow_BeforeRounding] : word1) @@
    (v2w [ieee_flags.Overflow] : word1) @@
    (v2w [ieee_flags.DivideByZero] : word1) @@
    (v2w [ieee_flags.InvalidOp] : word1)` >>
  qabbrev_tac `flagged = seen with regstate :=
    FPSR_ref.write_to (l3.FPSR || status) seen.regstate` >>
  `FPSqrt (l3.FP_REG src) l3.FPCR seen = returnS actual flagged` by (
    Cases_on `machine_ieee$fp64_isSignallingNan (l3.FP_REG src)` >>
    asm_simp_tac std_ss [Abbr `flagged`, Abbr `status`, fp_flags_word,
      EVAL ``(0w : 31 word) @@ (v2w [T] : word1)``,
      EVAL ``(0w : 31 word) @@ (v2w [F] : word1)``]) >>
  `state_rel (l3 with FPSR := l3.FPSR || status) flagged /\
   asl_sys_regs_ok flagged` by (
    qunabbrev_tac `flagged` >> irule FPSR_set_state_rel >> simp[]) >>
  qspecl_then [`l3 with FPSR := l3.FPSR || status`, `flagged`, `dst`, `actual`]
    mp_tac V_set64_state_rel >>
  simp[] >> disch_then (qx_choose_then `finished` strip_assume_tac) >>
  asm_simp_tac (simpLib.remove_ssfrags ["armv86a"] (srw_ss()))
    [decode_fsqrt_float_aarch64_instrs_float_arithmetic_unary_def,
     execute_aarch64_instrs_float_arithmetic_unary_def,
     undefined_FPUnaryOp_def, sail2_stateTheory.internal_pickS_def,
     sail2_state_monadTheory.chooseS_def, sail2_state_monadTheory.assert_expS_def,
     preludeTheory.undefined_bitvector_def, LET_THM,
     lemTheory.w2ui_def, sail2_valuesTheory.make_the_value_def,
     sail2_valuesTheory.size_itself_int_def, lem_machine_wordTheory.size_itself_def,
     bindS, seqS, returnS, asl_word_rws] >>
  gvs[Abbr `actual`]
QED

Theorem FPAbs64:
  FPAbs (value : word64) = returnS (machine_ieee$fp64_abs value)
Proof
  rw[FUN_EQ_THM] >>
  simp[FPAbs_def, seqS, returnS, asl_word_rws,
       machine_ieeeTheory.fp64_abs_def, machine_ieeeTheory.fp64_to_float_def,
       binary_ieeeTheory.float_abs_def, machine_ieeeTheory.float_to_fp64_def] >>
  blastLib.BBLAST_TAC
QED

Theorem FPNeg64:
  FPNeg (value : word64) = returnS (machine_ieee$fp64_negate value)
Proof
  rw[FUN_EQ_THM] >>
  simp[FPNeg_def, seqS, returnS, asl_word_rws,
       vec_of_bits_access_vec_dec_single,
       machine_ieeeTheory.fp64_negate_def, machine_ieeeTheory.fp64_to_float_def,
       binary_ieeeTheory.float_negate_def, machine_ieeeTheory.float_to_fp64_def] >>
  blastLib.BBLAST_TAC
QED

fun fp_unary_tac dfn_def decode_def decode result extra =
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >> l3_decode_tac >>
  rpt gen_tac >> strip_tac >>
  `l3.exception = NoException` by fs[state_rel_def] >>
  Cases_on `l3.FPCR && ~0x00C00000w = 0w` >>
  gvs[Run_def, dfn_def, CheckFP_def, D_def, write'D_def,
      raise'exception_def] >>
  asl_cexecute_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac decode >>
  `state_rel l3 seen ∧ asl_sys_regs_ok seen` by
    (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[decode_def] >>
  `CheckFPAdvSIMDEnabled64 () seen = returnS () seen` by
    (irule CheckFPAdvSIMDEnabled64_ok >> simp[]) >>
  `V_read 64 (&w2n src) seen = (returnS (l3.FP_REG src) seen : word64 res)` by
    metis_tac[V_read64] >>
  qspecl_then [`l3`, `seen`, `dst`, result] mp_tac V_set64_state_rel >>
  simp[] >> disch_then (qx_choose_then `finished` strip_assume_tac) >>
  simp([undefined_FPUnaryOp_def,
        execute_aarch64_instrs_float_arithmetic_unary_def,
        bindS, seqS, returnS] @ extra);

Theorem l3_models_asl_FMov:
  ∀src dst. l3_models_asl_instr (FloatingPoint (FMov (src, dst)))
Proof
  fp_unary_tac dfn'FMov_def
    decode_fmov_float_aarch64_instrs_float_arithmetic_unary_def
    `decode_fmov_float_aarch64_instrs_float_arithmetic_unary _ _ _ _ seen`
    `l3.FP_REG src` []
QED

Theorem l3_models_asl_FAbs:
  ∀src dst. l3_models_asl_instr (FloatingPoint (FAbs (src, dst)))
Proof
  fp_unary_tac dfn'FAbs_def
    decode_fabs_float_aarch64_instrs_float_arithmetic_unary_def
    `decode_fabs_float_aarch64_instrs_float_arithmetic_unary _ _ _ _ seen`
    `machine_ieee$fp64_abs (l3.FP_REG src)` [FPAbs64]
QED

Theorem l3_models_asl_FNeg:
  ∀src dst. l3_models_asl_instr (FloatingPoint (FNeg (src, dst)))
Proof
  fp_unary_tac dfn'FNeg_def
    decode_fneg_float_aarch64_instrs_float_arithmetic_unary_def
    `decode_fneg_float_aarch64_instrs_float_arithmetic_unary _ _ _ _ seen`
    `machine_ieee$fp64_negate (l3.FP_REG src)` [FPNeg64]
QED

Theorem l3_models_asl_FCompare:
  ∀left right. l3_models_asl_instr (FloatingPoint (FCompare (left, right)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >> l3_decode_tac >>
  rpt gen_tac >> strip_tac >>
  `l3.exception = NoException` by fs[state_rel_def] >>
  Cases_on `l3.FPCR && ~0x00C00000w = 0w` >>
  gvs[Run_def, dfn'FCompare_def, CheckFP_def, D_def, SetTheFlags_def,
      raise'exception_def] >>
  asl_cexecute_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac
    `decode_fcmp_float_aarch64_instrs_float_compare_uncond _ _ _ _ seen` >>
  `state_rel l3 seen ∧ asl_sys_regs_ok seen` by
    (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[decode_fcmp_float_aarch64_instrs_float_compare_uncond_def,
       vec_of_bits_access_vec_dec_single, Excl "access_vec_dec_def"] >>
  `CheckFPAdvSIMDEnabled64 () seen = returnS () seen` by
    (irule CheckFPAdvSIMDEnabled64_ok >> simp[]) >>
  `V_read 64 (&w2n left) seen = (returnS (l3.FP_REG left) seen : word64 res)` by
    metis_tac[V_read64] >>
  `V_read 64 (&w2n right) seen = (returnS (l3.FP_REG right) seen : word64 res)` by
    metis_tac[V_read64] >>
  `read_regS FPCR_ref seen = (returnS l3.FPCR seen : word32 res)` by
    metis_tac[FPCR_read] >>
  `¬word_bit 24 l3.FPCR ∧ ¬word_bit 8 l3.FPCR` by (
    qpat_x_assum `_ && l3.FPCR = 0w` mp_tac >> blastLib.BBLAST_TAC) >>
  simp[execute_aarch64_instrs_float_compare_uncond_def, bindS, seqS, returnS] >>
  simp[FPCompare64, seqS, returnS] >>
  qpat_x_assum `∀right left asl. _` kall_tac >>
  qpat_x_assum `state_rel l3 asl` kall_tac >>
  qpat_x_assum `asl_sys_regs_ok asl` kall_tac >>
  qpat_x_assum `Abbrev (seen = _)` kall_tac >>
  Cases_on
    `machine_ieee$fp64_isSignallingNan (l3.FP_REG left) ∨
     machine_ieee$fp64_isSignallingNan (l3.FP_REG right)` >>
  gvs[asl_reg_rws, returnS] >> state_rel_tac[] >>
  blastLib.BBLAST_TAC
QED

Theorem l3_models_asl_FMovFromGeneral64:
  ∀src dst.
    l3_models_asl_instr (FloatingPoint (FMovFromGeneral@64 (1w, src, dst)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >> l3_decode_tac >>
  rpt gen_tac >> strip_tac >>
  `l3.exception = NoException` by fs[state_rel_def] >>
  Cases_on `l3.FPCR && ~0x00C00000w = 0w` >>
  gvs[Run_def, dfn'FMovFromGeneral_def, CheckFP_def, write'D_def,
      raise'exception_def] >>
  asl_cexecute_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac
    `decode_fmov_float_gen_aarch64_instrs_float_convert_int _ _ _ _ _ _ seen` >>
  `state_rel l3 seen ∧ asl_sys_regs_ok seen` by
    (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[decode_fmov_float_gen_aarch64_instrs_float_convert_int_def,
       undefined_FPConvOp_def, undefined_FPRounding_def,
       sail2_state_monadTheory.undefined_boolS_def,
       vec_of_bits_access_vec_dec_single, Excl "access_vec_dec_def"] >>
  `CheckFPAdvSIMDEnabled64 () seen = returnS () seen` by
    (irule CheckFPAdvSIMDEnabled64_ok >> simp[]) >>
  `(X_read 64 (&w2n src) seen : word64 res) =
     returnS (X src l3) seen` by (
    qspecl_then [`l3`, `seen`] mp_tac X_read >> simp[] >>
    disch_then (qspec_then `&w2n src` mp_tac) >> simp[integerTheory.int_ge] >>
    qspec_then `src` mp_tac w2n_lt >> simp[]) >>
  qspecl_then [`l3`, `seen`, `dst`, `X src l3 : word64`]
    mp_tac V_set64_state_rel >>
  simp[] >> disch_then (qx_choose_then `finished` strip_assume_tac) >>
  `(&w2n dst : int) >= 0 ∧ w2n dst <= 31` by (
    qspec_then `dst` mp_tac w2n_lt >>
    simp[integerTheory.int_ge] >> intLib.ARITH_TAC) >>
  simp[execute_aarch64_instrs_float_convert_int_def,
       preludeTheory.undefined_bitvector_def, Vpart_set_def,
       bindS, seqS, returnS, asl_word_rws] >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[returnS]
QED

Theorem l3_models_asl_FMovToGeneral64:
  ∀src dst.
    l3_models_asl_instr (FloatingPoint (FMovToGeneral@64 (1w, src, dst)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >> l3_decode_tac >>
  rpt gen_tac >> strip_tac >>
  `l3.exception = NoException` by fs[state_rel_def] >>
  Cases_on `l3.FPCR && ~0x00C00000w = 0w` >>
  gvs[Run_def, dfn'FMovToGeneral_def, CheckFP_def, D_def,
      raise'exception_def] >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [write'X_def, COND_RAND]) >>
  gvs[] >>
  asl_cexecute_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac
    `decode_fmov_float_gen_aarch64_instrs_float_convert_int _ _ _ _ _ _ seen` >>
  `state_rel l3 seen ∧ asl_sys_regs_ok seen` by
    (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[decode_fmov_float_gen_aarch64_instrs_float_convert_int_def,
       undefined_FPConvOp_def, undefined_FPRounding_def,
       sail2_state_monadTheory.undefined_boolS_def,
       vec_of_bits_access_vec_dec_single, Excl "access_vec_dec_def"] >>
  `CheckFPAdvSIMDEnabled64 () seen = returnS () seen` by
    (irule CheckFPAdvSIMDEnabled64_ok >> simp[]) >>
  `V_read 64 (&w2n src) seen = (returnS (l3.FP_REG src) seen : word64 res)` by
    metis_tac[V_read64] >>
  `(&w2n src : int) >= 0 ∧ w2n src <= 31` by (
    qspec_then `src` mp_tac w2n_lt >>
    simp[integerTheory.int_ge] >> intLib.ARITH_TAC) >>
  simp[execute_aarch64_instrs_float_convert_int_def,
       preludeTheory.undefined_bitvector_def, Vpart_read_def,
       bindS, seqS, returnS, asl_word_rws] >>
  Cases_on `dst = 31w`
  >- simp[X_set_31, returnS, write'X_def] >>
  qspecl_then [`l3`, `seen`] mp_tac (b64 alpha X_set_not_31) >> simp[] >>
  disch_then (qspecl_then [`64`, `&w2n dst`, `l3.FP_REG src`] mp_tac) >>
  `w2n dst < 31` by WORD_DECIDE_TAC >>
  simp[integerTheory.int_ge] >>
  disch_then (qx_choose_then `finished` strip_assume_tac) >>
  `asl_sys_regs_ok finished` by (
    qspecl_then [`seen`, `finished`, `64`, `&w2n dst`, `l3.FP_REG src`]
      mp_tac (b64 alpha X_set_asl_sys_regs_ok) >> simp[]) >>
  simp[returnS]
QED

Theorem V_read32:
  !l3 asl reg. state_rel l3 asl ==>
    V_read 32 (&w2n reg) asl =
      (returnS (w2w (l3.FP_REG reg)) asl : word32 res)
Proof
  rpt gen_tac >> strip_tac >>
  `(&w2n reg : int) ≥ 0 ∧ w2n reg ≤ 31` by
    (qspec_then `reg` mp_tac w2n_lt >> simp[] >> intLib.ARITH_TAC) >>
  simp[V_read_def, bindS, seqS, returnS, asl_reg_rws, asl_word_rws] >>
  `w2w (EL (w2n reg) (Z_ref.read_from asl.regstate)) = l3.FP_REG reg` by
    metis_tac[state_rel_def, fp_reg_rel_read] >>
  fs[Z_ref_def, WORD_w2w_EXTRACT, WORD_EXTRACT_MIN_HIGH] >>
  qpat_x_assum `(63 >< 0) _ = l3.FP_REG reg`
    (mp_tac o AP_TERM ``(31 >< 0) : word64 -> word32``) >>
  simp [WORD_EXTRACT_COMP_THM]
QED

Theorem V_set32:
  !asl (reg : word5) (value : word32) vl sve.
    VL_read () asl = returnS vl asl /\
    IsSVEEnabled (PSTATE_ref.read_from asl.regstate).ProcState_EL asl =
      returnS sve asl ==>
    V_set 32 (&w2n reg) value asl =
      returnS () (asl with regstate :=
        Z_ref.write_to
          (LUPDATE (w2w value) (w2n reg) (Z_ref.read_from asl.regstate))
          asl.regstate)
Proof
  rpt gen_tac >> strip_tac >>
  `(&w2n reg : int) ≥ 0 ∧ w2n reg ≤ 31` by
    (qspec_then `reg` mp_tac w2n_lt >> simp[] >> intLib.ARITH_TAC) >>
  fs[asl_reg_rws] >>
  simp[V_set_def, ConstrainUnpredictableBool_def, ConstrainUnpredictable_def,
       bindS, seqS, returnS, asl_reg_rws, asl_word_rws]
QED

Theorem V_set32_state_rel:
  !l3 asl (reg : word5) (value : word32).
    state_rel l3 asl /\ asl_sys_regs_ok asl ==>
    ?asl'.
      V_set 32 (&w2n reg) value asl = returnS () asl' /\
      state_rel (l3 with FP_REG := (reg =+ w2w value) l3.FP_REG) asl' /\
      asl_sys_regs_ok asl'
Proof
  rpt gen_tac >> strip_tac >>
  drule VL_read_total >> disch_then (qx_choose_then `vl` assume_tac) >>
  drule IsSVEEnabled_total >> disch_then (qx_choose_then `sve` assume_tac) >>
  qspecl_then [`asl`, `reg`, `value`, `vl`, `sve`] mp_tac V_set32 >>
  simp[] >> strip_tac >>
  qexists_tac `asl with regstate :=
    Z_ref.write_to
      (LUPDATE (w2w value) (w2n reg) (Z_ref.read_from asl.regstate))
      asl.regstate` >>
  simp[] >> conj_tac
  >- (
    mp_tac (INST
      [``value : 2048 word`` |-> ``w2w (value : word32) : 2048 word``]
      Z_set_state_rel) >>
    simp[w2w_w2w, WORD_BITS_MIN_HIGH, WORD_ALL_BITS]) >>
  gvs[asl_sys_regs_ok_def, Z_ref_def]
QED

Theorem l3_models_asl_FMovFromGeneral32:
  !src dst.
    l3_models_asl_instr (FloatingPoint (FMovFromGeneral@32 (0w, src, dst)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >> l3_decode_tac >>
  rpt gen_tac >> strip_tac >>
  `l3.exception = NoException` by fs[state_rel_def] >>
  Cases_on `l3.FPCR && ~0x00C00000w = 0w` >>
  gvs[Run_def, dfn'FMovFromGeneral_def, CheckFP_def, write'D_def,
      raise'exception_def] >>
  asl_cexecute_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac
    `decode_fmov_float_gen_aarch64_instrs_float_convert_int _ _ _ _ _ _ seen` >>
  `state_rel l3 seen ∧ asl_sys_regs_ok seen` by
    (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[decode_fmov_float_gen_aarch64_instrs_float_convert_int_def,
       undefined_FPConvOp_def, undefined_FPRounding_def,
       sail2_state_monadTheory.undefined_boolS_def,
       vec_of_bits_access_vec_dec_single, Excl "access_vec_dec_def"] >>
  `CheckFPAdvSIMDEnabled64 () seen = returnS () seen` by
    (irule CheckFPAdvSIMDEnabled64_ok >> simp[]) >>
  `(X_read 32 (&w2n src) seen : word32 res) =
     returnS (X src l3) seen` by (
    qspecl_then [`l3`, `seen`] mp_tac X_read32 >> simp[] >>
    disch_then (qspec_then `&w2n src` mp_tac) >> simp[integerTheory.int_ge] >>
    qspec_then `src` mp_tac w2n_lt >> simp[]) >>
  qspecl_then [`l3`, `seen`, `dst`, `X src l3 : word32`]
    mp_tac V_set32_state_rel >>
  simp[] >> disch_then (qx_choose_then `finished` strip_assume_tac) >>
  `(&w2n dst : int) >= 0 ∧ w2n dst <= 31` by (
    qspec_then `dst` mp_tac w2n_lt >>
    simp[integerTheory.int_ge] >> intLib.ARITH_TAC) >>
  simp[execute_aarch64_instrs_float_convert_int_def,
       preludeTheory.undefined_bitvector_def, Vpart_set_def,
       bindS, seqS, returnS, asl_word_rws] >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[returnS]
QED

Theorem l3_models_asl_FMovToGeneral32:
  !src dst.
    l3_models_asl_instr (FloatingPoint (FMovToGeneral@32 (0w, src, dst)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >> l3_decode_tac >>
  rpt gen_tac >> strip_tac >>
  `l3.exception = NoException` by fs[state_rel_def] >>
  Cases_on `l3.FPCR && ~0x00C00000w = 0w` >>
  gvs[Run_def, dfn'FMovToGeneral_def, CheckFP_def, D_def,
      raise'exception_def] >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [write'X_def, COND_RAND]) >>
  gvs[] >>
  asl_cexecute_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac
    `decode_fmov_float_gen_aarch64_instrs_float_convert_int _ _ _ _ _ _ seen` >>
  `state_rel l3 seen ∧ asl_sys_regs_ok seen` by
    (unabbrev_all_tac >> state_rel_tac[]) >>
  simp[decode_fmov_float_gen_aarch64_instrs_float_convert_int_def,
       undefined_FPConvOp_def, undefined_FPRounding_def,
       sail2_state_monadTheory.undefined_boolS_def,
       vec_of_bits_access_vec_dec_single, Excl "access_vec_dec_def"] >>
  `CheckFPAdvSIMDEnabled64 () seen = returnS () seen` by
    (irule CheckFPAdvSIMDEnabled64_ok >> simp[]) >>
  `V_read 32 (&w2n src) seen = (returnS (w2w (l3.FP_REG src)) seen : word32 res)` by
    metis_tac[V_read32] >>
  `(&w2n src : int) >= 0 ∧ w2n src <= 31` by (
    qspec_then `src` mp_tac w2n_lt >>
    simp[integerTheory.int_ge] >> intLib.ARITH_TAC) >>
  simp[execute_aarch64_instrs_float_convert_int_def,
       preludeTheory.undefined_bitvector_def, Vpart_read_def,
       bindS, seqS, returnS, asl_word_rws] >>
  Cases_on `dst = 31w`
  >- simp[X_set_31, returnS, write'X_def] >>
  qspecl_then [`l3`, `seen`] mp_tac (b32 alpha X_set_not_31) >> simp[] >>
  disch_then (qspecl_then [`32`, `&w2n dst`, `w2w (l3.FP_REG src) : word32`] mp_tac) >>
  `w2n dst < 31` by WORD_DECIDE_TAC >>
  simp[integerTheory.int_ge] >>
  disch_then (qx_choose_then `finished` strip_assume_tac) >>
  `asl_sys_regs_ok finished` by (
    qspecl_then [`seen`, `finished`, `32`, `&w2n dst`, `w2w (l3.FP_REG src) : word32`]
      mp_tac (b32 alpha X_set_asl_sys_regs_ok) >> simp[]) >>
  simp[returnS]
QED

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

Theorem l3_models_asl_Shift:
  l3_models_asl_instr (Data (Shift@64 (0x1w,sh,w1,w2,w3)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >>
  qmatch_goalsub_abbrev_tac `Decode opc` >>
  `Decode opc = Data (Shift@64 (0b1w,sh,w1,w2,w3))` by (
    unabbrev_all_tac >> l3_decode_tac >>
    Cases_on ‘sh’ >> gvs[DecodeShift_def]) >>
  unabbrev_all_tac >> simp[] >> rw[] >>
  l3_run_tac >>
  gvs[GSYM $ b64 ``:'N`` X_def |> SIMP_RULE (srw_ss()) [FUN_EQ_THM]] >>
  gvs[GSYM $ ShiftReg_def |> SIMP_RULE std_ss [FUN_EQ_THM]] >>
  gvs[PULL_FORALL] >> first_x_assum $ qspec_then `l3` assume_tac >>
  qmatch_goalsub_abbrev_tac `seqS (wr s) ex` >>
  `∃s'. (do wr s; ex od asl) = (do wr s';
    execute_aarch64_instrs_integer_shift_variable (&w2n w3) (:64)
      (&w2n w1) (&w2n w2) (l3_to_asl_ShiftType sh) od asl)` by (
    unabbrev_all_tac >>
    Cases_on ‘sh’ >> gvs [] >>
    asl_cexecute_tac >> gvs[] >>
    simp [decode_lslv_aarch64_instrs_integer_shift_variable_def,
          decode_lsrv_aarch64_instrs_integer_shift_variable_def,
          decode_asrv_aarch64_instrs_integer_shift_variable_def,
          decode_rorv_aarch64_instrs_integer_shift_variable_def] >>
    gvs[armv86aTheory.DecodeShift_def] >>
    simp[asl_reg_rws, returnS, seqS, l3_to_asl_LogicalOp_def, l3_to_asl_ShiftType_def] >>
    irule_at Any EQ_REFL) >>
  simp[] >> pop_assum kall_tac >> simp[Abbr `wr`, Abbr `s`, Abbr `ex`] >>
  simp[asl_reg_rws, seqS, Once returnS] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1 ∧ asl_sys_regs_ok asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel l3 asl` kall_tac >>
  simp[execute_aarch64_instrs_integer_shift_variable_def] >>
  drule X_read >> disch_then $ qspec_then `&w2n w1` mp_tac >> impl_tac
  >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >> simp[asl_word_rws] >>
  `ShiftReg 64 (&w2n w2) (l3_to_asl_ShiftType sh) (&(w2n (X w1 l3 : word64) MOD 64)) asl1 =
    returnS (ShiftReg (w2,sh,w2n (X w1 l3 : word64) MOD 64) l3) asl1 : word64 res` by (
      gvs[ShiftReg_def, ShiftValue_def, armv86aTheory.ShiftReg_def] >>
      drule X_read >> disch_then $ qspec_then `&w2n w2` mp_tac >> impl_tac
      >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
      drule returnS_bindS_word64 >> simp[] >> disch_then kall_tac >> simp[asl_word_rws] >>
      Cases_on `sh` >> gvs[l3_to_asl_ShiftType_def]) >>
  drule returnS_bindS_unit >> simp [] >> disch_then kall_tac >>
  Cases_on `w3 = 31w` >> gvs[X_set_31]
  >- (simp[returnS] >> gvs[SetTheFlags_def, w2v_v2w]) >>
  drule $ b64 alpha X_set_not_31 >>
  qmatch_goalsub_abbrev_tac `X_set _ _ shift` >>
  disch_then $ qspecl_then [`64`,`&w2n w3`,`shift`] mp_tac >> simp[] >>
  impl_tac >- (Cases_on ‘w3’ >> gvs [] >> simp[int_ge]) >> strip_tac >>
  simp[Abbr `shift`, returnS] >>
  gvs[write'X_def,ShiftReg_def,arm8Theory.X_def] >>
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

Theorem APPLY_UPDATE_ALT_THM[local]:
  ∀f a b c. f⦇a ↦ b⦈ c = if c = a then b else f c
Proof
  rw[combinTheory.APPLY_UPDATE_THM]
QED

Theorem FLOOKUP_UPDATE_ALT[local]:
  ∀fm k1 v k2. FLOOKUP (fm |+ (k1,v)) k2 = if k2 = k1 then SOME v else FLOOKUP fm k2
Proof
  rw[FLOOKUP_UPDATE]
QED

Theorem load_store_encode_lemma[local]:
  (w : word64 = w2w ((11 >< 0) (w ⋙ 3)) ≪ 3 ⇔
    ∃j : word12. w = (0w : 49 word) @@ j @@ (0w : word3)) ∧
  (w : word64 = w2w ((11 >< 0) (w ⋙ 2)) ≪ 2 ⇔
    ∃j : word12. w = (0w : 50 word) @@ j @@ (0w : word2)) ∧
  (w : word64 = w2w ((11 >< 0) (w ⋙ 1)) ≪ 1 ⇔
    ∃j : word12. w = (0w : 51 word) @@ j @@ (0w : word1)) ∧
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
  >- (
    reverse eq_tac >> rw[] >- blastLib.BBLAST_TAC >>
    qexists_tac `(12 >< 1) w` >> pop_assum mp_tac >> blastLib.BBLAST_TAC
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

Theorem l3_asl_Mem_read_2:
  ∀l3 asl addrdesc accdesc.
    mem_rel l3 asl.memstate asl.tagstate ∧
    asl.regstate.bitvector_64_dec_reg "__CNTControlBase" = 0w
  ⇒ let p = addrdesc.AddressDescriptor_paddress.FullAddress_address in
    Mem_read addrdesc 2 accdesc asl =
    returnS (l3 (p + 1w) @@ l3 p) asl
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
    [`p`,`p+1w`] >>
  last_x_assum kall_tac >> gvs[word_add_def] >>
  simp[sail2_valuesTheory.and_bit_def] >>
  ntac 3 $ simp[Once sail2_valuesTheory.just_list_def] >>
  simp[returnS] >>
  simp[sail2_valuesTheory.bits_of_mem_bytes_def,
       sail2_valuesTheory.bits_of_bytes_def] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  DEP_REWRITE_TAC[OPTION_MAP_just_list] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss, EVERY_MAP] >>
  simp[returnS] >> DEP_REWRITE_TAC[word_concat_v2w] >> simp[]
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

Theorem l3_asl_Mem_read0_2_AccType_NORMAL:
  ∀l3 asl addr. state_rel l3 asl ∧ asl_sys_regs_ok asl ∧
    ((SCTLR l3).A ⇒ Aligned (addr, 2)) ⇒
  Mem_read0 addr 2 AccType_NORMAL asl =
  returnS (FST (Mem (addr,2,AccType_NORMAL) l3)) asl : word16 res
Proof
  rw[] >> simp[Mem_read0_def, AArch64_CheckAlignment_def] >>
  simp[sail2_state_monadTheory.undefined_boolS_def, undefined_Constraint_def,
       ConstrainUnpredictable_def] >>
  simp[l3_asl_Align, asl_word_rws] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  simp[EL_MAP, sail2_valuesTheory.just_list_def, el_w2v] >>
  drule_all SCTLR_read__1 >> strip_tac >>
  drule $ INST_TYPE [gamma |-> ``:word16``] returnS_bindS >>
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
    qspecl_then [`addr`,`AccType_NORMAL`,`F`,`T`,`2`,`asl`]
      assume_tac AArch64_TranslateAddress >> gvs[] >>
    drule $ INST_TYPE [gamma |-> ``:word16``] returnS_bindS >>
    simp[] >> disch_then kall_tac >>
    qspecl_then [`AccType_NORMAL`,`asl`] mp_tac CreateAccessDescriptor >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
    qspec_then `asl` mp_tac IsSecure >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> rw[] >> simp[Once bindS] >>
    ntac 2 $ simp[Once returnS] >> simp[HaveMTEExt] >>
    qpat_abbrev_tac `addr = _.FullAddress_address` >>
    qspecl_then [`addr`,`AccType_NORMAL`,`asl`] mp_tac AArch64_AccessIsTagChecked >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
    drule $ INST_TYPE [gamma |-> ``:word16``] returnS_bindS >>
    simp[] >> disch_then kall_tac >>
    qmatch_goalsub_abbrev_tac `Mem_read _ _ accdesc` >>
    qspecl_then [`l3.MEM`,`asl`,`addrdesc`,`accdesc`] mp_tac l3_asl_Mem_read_2 >>
    impl_tac >- state_rel_tac[] >> rw[] >>
    drule $ INST_TYPE [gamma |-> ``:word16``] returnS_bindS >>
    simp[] >> disch_then kall_tac >>
    drule_all l3_asl_BigEndian >> strip_tac >>
    drule $ INST_TYPE [gamma |-> ``:word16``] returnS_bindS >>
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
  drule $ INST_TYPE [gamma |-> ``:word16``] returnS_bindS >>
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

Theorem l3_asl_Mem_set0_2_AccType_NORMAL:
  ∀l3 asl addr (val : word16) l3'.
    state_rel l3 asl ∧ asl_sys_regs_ok asl ∧
    write'Mem (val, addr, 2, AccType_NORMAL) l3 = l3' ∧
    l3'.exception = NoException
  ⇒ ∃asl'.
      Mem_set0 addr 2 AccType_NORMAL val asl = returnS () asl' ∧
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
  `(SCTLR l3).A ⇒ addr = Align (addr, 2)` by (
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
    qspecl_then [`addr`,`AccType_NORMAL`,`T`,`T`,`2`,`asl`]
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
    `∃mem. write'Mem (val,addr,2,AccType_NORMAL) l3 = l3 with MEM := mem` by (
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
      ntac 1 (
        IF_CASES_TAC >> simp[] >> gvs[]
        >- (
          rpt (IF_CASES_TAC >> gvs[]) >>
          irule_at Any EQ_REFL >> simp[] >> rpt AP_TERM_TAC >>
          SUBST_ALL_TAC $ GSYM $ mk_blast_thm ``val : word16`` >> EVAL_TAC
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
      simp[w2v_reverse_endianness0_16] >>
      `w2v val =
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
      ntac 1 (
        IF_CASES_TAC >> simp[] >> gvs[]
        >- (
          rpt (IF_CASES_TAC >> gvs[]) >>
          irule_at Any EQ_REFL >> simp[] >> rpt AP_TERM_TAC >>
          SUBST_ALL_TAC $ GSYM $ mk_blast_thm ``val : word16`` >> EVAL_TAC
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
  simp[returnS] >>
  `CheckAlignment (addr,2,AccType_NORMAL,T) l3 = l3` by (
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
      w2v ((15 >< 8) val) ++ w2v ((7 >< 0) val)` by (
      rewrite_tac[GSYM APPEND_ASSOC] >>
      map_every (rewrite_tac o single) [
        GSYM APPEND_ASSOC, concat16, concat32, concat64] >>
      AP_TERM_TAC >> blastLib.BBLAST_TAC) >>
    pop_assum SUBST_ALL_TAC >>
    rewrite_tac[GSYM APPEND_ASSOC] >>
    DEP_REWRITE_TAC[ByteList_APPEND_bytes] >> simp[] >>
    simp[field_concat_left, field_concat_right] >>
    `v2w (field 7 0 (w2v ((23 >< 16) val : word8))) : word8 = (23 >< 16) val` by (
      SUBST1_TAC $ GSYM $ mk_blast_thm ``val : word16`` >> EVAL_TAC) >>
    simp[] >> pop_assum kall_tac >> gvs[state_rel_def] >>
    simp[CONJ_ASSOC] >> conj_tac >- state_rel_tac[] >>
    rw[mem_rel_def]
    >- (simp[FLOOKUP_UPDATE] >> rpt IF_CASES_TAC >> simp[] >> gvs[mem_rel_def]) >>
    simp[FLOOKUP_UPDATE_ALT, APPLY_UPDATE_ALT_THM] >> simp[Once CONJ_SYM] >>
    ntac 1 (
      IF_CASES_TAC >> simp[] >> gvs[]
      >- (
        rpt (IF_CASES_TAC >> gvs[]) >>
        irule_at Any EQ_REFL >> simp[] >> rpt AP_TERM_TAC >>
        SUBST_ALL_TAC $ GSYM $ mk_blast_thm ``val : word16`` >> EVAL_TAC
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
    simp[extract_bits_reverse_endianness0_16] >>
    `w2v val =
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
    `v2w (field 7 0 (w2v ((23 >< 16) val : word8))) : word8 = (23 >< 16) val` by (
      SUBST1_TAC $ GSYM $ mk_blast_thm ``val : word16`` >> EVAL_TAC) >>
    simp[] >> pop_assum kall_tac >> gvs[state_rel_def] >>
    simp[CONJ_ASSOC] >> conj_tac >- state_rel_tac[] >>
    rw[mem_rel_def]
    >- (simp[FLOOKUP_UPDATE] >> rpt IF_CASES_TAC >> simp[] >> gvs[mem_rel_def]) >>
    simp[FLOOKUP_UPDATE_ALT, APPLY_UPDATE_ALT_THM] >> simp[Once CONJ_SYM] >>
    ntac 1 (
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

(********** 16-bit loads **********)

Theorem l3_models_asl_LoadStoreImmediate_16_NORMAL_LOAD_FFFFF_1:
  ∀b (j : word12) r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@16
        (1w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, T,
         (0b0w :51 word) @@ j @@ (0b0w :word1), r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >>
  ‘(11 >< 0) ((0b0w :51 word) @@ j @@ (0w :word1) ⋙ 1) = j’ by WORD_DECIDE_TAC >>
  simp[] >> pop_assum kall_tac >>
  reverse IF_CASES_TAC >> gvs[]
  >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> WORD_DECIDE_TAC) >>
  l3_decode_tac >> simp[] >> l3_run_tac >>
  asl_cexecute_tac >>
  simp[
    decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def,
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
    qspecl_then [`2`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos,
         GSYM word_add_def, n2w_w2n, ExtendWord_def] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
(**)
    drule l3_asl_Mem_read0_2_AccType_NORMAL >> simp[] >>
    disch_then $ qspec_then `X r2 l3 + w2w j ≪ 1` mp_tac >> impl_keep_tac
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
    >-  simp[X_set_31, returnS] >>
    drule $ INST_TYPE [alpha |-> ``:32``] X_set_not_31 >> (* YO *)
    disch_then $ qspecl_then [`32`,`&w2n r1`,`w2w v'`] mp_tac >> simp[] >>
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
  qspecl_then [`2`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos,
       GSYM word_add_def, n2w_w2n] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_read0_2_AccType_NORMAL >> simp[] >>
  disch_then $ qspec_then `SP l3 + w2w j ≪ 1` mp_tac >> impl_keep_tac
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
  disch_then $ qspecl_then [`32`,`&w2n r1`,`w2w v'`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
  simp[seqS, returnS] >> gvs[write'X_def] >> simp[ExtendWord_def] >>
  qpat_x_assum `X_set _ _ _ _ = _` mp_tac >>
  simp[X_set_def, int_ge] >>
  every_case_tac >> gvs[returnS, bindS, asl_reg_rws] >>
  rw[] >> gvs[asl_sys_regs_ok_def] >>
  irule FALSITY >> pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
  WORD_DECIDE_TAC
QED

Theorem l3_models_asl_LoadStoreImmediate_16_NORMAL_LOAD_FFFFF_2:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@16
        (1w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, unsigned,
         w2w j, r2, r1)))
Proof
  rw[] >>
  Cases_on `
    ∃i :word12. unsigned ∧ w2w j : word64 = (0w : 51 word) @@ i @@ (0w : word1)` >>
  gvs[l3_models_asl_LoadStoreImmediate_16_NORMAL_LOAD_FFFFF_1] >>
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >> IF_CASES_TAC >> gvs[] >- gvs[load_store_encode_lemma] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  ntac 3 $ pop_assum kall_tac >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >> rw[] >>
  asl_cexecute_tac >>
  simp[
    decode_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
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
    qspecl_then [`2`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[ExtendWord_def, LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_read0_2_AccType_NORMAL >> simp[] >>
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
    disch_then $ qspecl_then [`32`,`&w2n r1`,`w2w v'`] mp_tac >> simp[] >>
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
  qspecl_then [`2`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos,
       GSYM word_add_def, n2w_w2n] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_read0_2_AccType_NORMAL >> simp[] >>
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
  disch_then $ qspecl_then [`32`,`&w2n r1`,`w2w v'`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
  simp[seqS, returnS] >> gvs[write'X_def] >> simp[ExtendWord_def] >>
  qpat_x_assum `X_set _ _ _ _ = _` mp_tac >>
  simp[X_set_def, int_ge] >>
  every_case_tac >> gvs[returnS, bindS, asl_reg_rws] >>
  rw[] >> gvs[asl_sys_regs_ok_def] >>
  irule FALSITY >> pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
  WORD_DECIDE_TAC
QED

Theorem l3_models_asl_LoadStoreImmediate_16_NORMAL_LOAD_FFFFF_3:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@16
        (1w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, unsigned,
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
    decode_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
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
    qspecl_then [`2`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[ExtendWord_def, LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_read0_2_AccType_NORMAL >> simp[] >>
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
    disch_then $ qspecl_then [`32`,`&w2n r1`,`w2w v'`] mp_tac >> simp[] >>
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
  qspecl_then [`2`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos,
       GSYM word_add_def, n2w_w2n] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_read0_2_AccType_NORMAL >> simp[] >>
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
  disch_then $ qspecl_then [`32`,`&w2n r1`,`w2w v'`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
  simp[seqS, returnS] >> gvs[write'X_def] >> simp[ExtendWord_def] >>
  qpat_x_assum `X_set _ _ _ _ = _` mp_tac >>
  simp[X_set_def, int_ge] >>
  every_case_tac >> gvs[returnS, bindS, asl_reg_rws] >>
  rw[] >> gvs[asl_sys_regs_ok_def] >>
  irule FALSITY >> pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
  WORD_DECIDE_TAC
QED

Theorem l3_models_asl_LoadStoreImmediate_16_NORMAL_LOAD_FFFFF:
  ∀b w unsigned r2 r1.
    let instr =
      LoadStore (LoadStoreImmediate@16
        (1w, b, MemOp_LOAD, AccType_NORMAL, F,F,F,F,F, unsigned, w, r2, r1))
    in (∀s. Encode instr ≠ BadCode s) ⇒ l3_models_asl_instr instr
Proof
  rw[encode_rws] >> gvs[load_store_encode_lemma]
  >- simp[l3_models_asl_LoadStoreImmediate_16_NORMAL_LOAD_FFFFF_1] >>
  Cases_on `word_bit 8 w` >> gvs[] >> qpat_x_assum `w = _` SUBST_ALL_TAC
  >- (
    assume_tac l3_models_asl_LoadStoreImmediate_16_NORMAL_LOAD_FFFFF_3 >>
    gvs[]
    )
  >- (
    `∃j : word8. (7 >< 0) w : word64 = w2w j` by (
      qexists_tac `(7 >< 0) w` >> blastLib.BBLAST_TAC) >>
    pop_assum SUBST_ALL_TAC >>
    simp[l3_models_asl_LoadStoreImmediate_16_NORMAL_LOAD_FFFFF_2]
    )
QED

(********** 16-bit stores **********)

Theorem l3_models_asl_LoadStoreImmediate_16_NORMAL_STORE_FFFFF_1:
  ∀b (j : word12) r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@16
        (1w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, T,
         (0w :51 word) @@ j @@ (0w :word1), r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >>
  `(11 >< 0) ((0w :51 word) @@ j @@ (0w :word1) ⋙ 1) = j` by WORD_DECIDE_TAC >>
  simp[] >> pop_assum kall_tac >>
  reverse IF_CASES_TAC >> gvs[]
  >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> WORD_DECIDE_TAC) >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >> rw[] >>
  asl_cexecute_tac >>
  simp[
    decode_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned_def,
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
    drule X_read16 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`2`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2` by (unabbrev_all_tac >> state_rel_tac[]) >>
    `asl_sys_regs_ok asl2` by (unabbrev_all_tac >> gvs[asl_sys_regs_ok_def]) >>
    drule l3_asl_Mem_set0_2_AccType_NORMAL >> simp[] >>
    disch_then $ qspecl_then [`X r2 l3 + w2w j ≪ 1`,`X r1 l3`] mp_tac >> impl_keep_tac
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
  drule X_read16 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`2`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_set0_2_AccType_NORMAL >> simp[] >>
  disch_then $ qspecl_then [`SP l3 + w2w j ≪ 1`,`X r1 l3`] mp_tac >> impl_tac
  >- (
    qpat_x_assum `(_ (_,_) _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
    ) >>
  simp[returnS] >> strip_tac >> simp[seqS, returnS]
QED

Theorem l3_models_asl_LoadStoreImmediate_16_NORMAL_STORE_FFFFF_2:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@16
        (1w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, unsigned,
         w2w j, r2, r1)))
Proof
  rw[] >>
  Cases_on `
    ∃i :word12. unsigned ∧ w2w j : word64 = (0w : 51 word) @@ i @@ (0w : word1)` >>
  gvs[l3_models_asl_LoadStoreImmediate_16_NORMAL_STORE_FFFFF_1] >>
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  simp[encode_rws] >> IF_CASES_TAC >> gvs[] >- gvs[load_store_encode_lemma] >>
  reverse IF_CASES_TAC >> gvs[]
  >- (pop_assum mp_tac >> simp[] >> blastLib.BBLAST_TAC) >>
  ntac 3 $ pop_assum kall_tac >>
  l3_decode_tac >> simp[] >> l3_run_tac >> ntac 2 $ pop_assum kall_tac >> rw[] >>
  asl_cexecute_tac >>
  simp[
    decode_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
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
    drule X_read16 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`2`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_set0_2_AccType_NORMAL >> simp[] >>
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
  drule X_read16 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
  impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`2`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_set0_2_AccType_NORMAL >> simp[] >>
  disch_then $ qspecl_then [`SP l3 + w2w (0w : word1 @@ j)`,`X r1 l3`] mp_tac >>
  impl_tac
  >- (
    qpat_x_assum `(_ (_,_) _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
    ) >>
  simp[returnS] >> strip_tac >> simp[seqS, returnS]
QED

Theorem l3_models_asl_LoadStoreImmediate_16_NORMAL_STORE_FFFFF_3:
  ∀b (j : word8) unsigned r2 r1.
    l3_models_asl_instr
      (LoadStore (LoadStoreImmediate@16
        (1w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, unsigned,
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
    decode_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal_def,
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
    drule X_read16 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
    impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`2`,`F`,`&w2n r1`,`F`,`F`,`asl1`]
      mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
    impl_tac >- WORD_DECIDE_TAC >>
    simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
    simp[LSISyndrome_ref_def] >>
    qmatch_goalsub_abbrev_tac `asl2 : regstate sequential_state` >>
    `state_rel l3 asl2 ∧ asl_sys_regs_ok asl2` by (
      unabbrev_all_tac >> state_rel_tac[]) >>
    drule l3_asl_Mem_set0_2_AccType_NORMAL >> simp[] >>
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
  drule X_read16 >> disch_then $ qspec_then `&w2n r1` mp_tac >>
  impl_tac >- (simp[INT_GE_CALCULATE] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  qspecl_then [`2`,`F`,`&w2n r1`,`F`,`F`,`asl2`]
    mp_tac AArch64_SetLSInstructionSyndrome >> simp[] >>
  impl_tac >- WORD_DECIDE_TAC >>
  simp[asl_reg_rws] >> strip_tac >> simp[Once seqS, Once returnS] >>
  simp[LSISyndrome_ref_def] >>
  qmatch_goalsub_abbrev_tac `asl3 : regstate sequential_state` >>
  `state_rel l3 asl3 ∧ asl_sys_regs_ok asl3` by (unabbrev_all_tac >> state_rel_tac[]) >>
  drule l3_asl_Mem_set0_2_AccType_NORMAL >> simp[] >>
  disch_then $ qspecl_then [`SP l3 + sw2sw (1w : word1 @@ j)`,`X r1 l3`] mp_tac >>
  impl_tac
  >- (
    qpat_x_assum `(_ (_,_) _).exception = NoException` mp_tac >>
    simp[dfn'LoadStoreImmediate_def, LoadStoreSingle_def]
    ) >>
  simp[returnS] >> strip_tac >> simp[seqS, returnS]
QED

Theorem l3_models_asl_LoadStoreImmediate_16_NORMAL_STORE_FFFFF:
  ∀b w unsigned r2 r1.
    let instr =
      LoadStore (LoadStoreImmediate@16
        (1w, b, MemOp_STORE, AccType_NORMAL, F,F,F,F,F, unsigned, w, r2, r1))
    in (∀s. Encode instr ≠ BadCode s) ⇒ l3_models_asl_instr instr
Proof
  rw[encode_rws] >> gvs[load_store_encode_lemma]
  >- simp[l3_models_asl_LoadStoreImmediate_16_NORMAL_STORE_FFFFF_1] >>
  Cases_on `word_bit 8 w` >> gvs[] >> qpat_x_assum `w = _` SUBST_ALL_TAC
  >- (
    assume_tac l3_models_asl_LoadStoreImmediate_16_NORMAL_STORE_FFFFF_3 >>
    gvs[]
    )
  >- (
    `∃j : word8. (7 >< 0) w : word64 = w2w j` by (
      qexists_tac `(7 >< 0) w` >> blastLib.BBLAST_TAC) >>
    pop_assum SUBST_ALL_TAC >>
    simp[l3_models_asl_LoadStoreImmediate_16_NORMAL_STORE_FFFFF_2]
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
