open HolKernel boolLib bossLib Parse BasicProvers dep_rewrite
open armv86aTheory armv86a_terminationTheory armv86a_typesTheory
open arm8Theory arm8Lib arm8_stepTheory arm8_stepLib
open wordsTheory bitstringTheory finite_mapTheory listTheory
     arithmeticTheory integerTheory
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

(*
Theorem HavePACExt_T[simp]:
  HavePACExt () = T
Proof
  rw[HavePACExt_def]
QED
*)

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
  ∀hw imm16 r.
    l3_models_asl_instr (Data (MoveWide@64 (1w, MoveWideOp_Z, hw, imm16, r)))
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel _ asl` kall_tac >>
  dxrule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`reg`,`v`] mp_tac >> simp[Abbr `reg`, int_ge] >>
  impl_tac >- WORD_DECIDE_TAC >> strip_tac >> simp[] >> gvs[write'X_def, returnS]
QED

Theorem l3_models_asl_MoveWideOp_N:
  ∀hw imm16 r.
    l3_models_asl_instr (Data (MoveWide@64 (1w, MoveWideOp_N, hw, imm16, r)))
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel _ asl` kall_tac >>
  dxrule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`reg`,`v`] mp_tac >> simp[Abbr `reg`, int_ge] >>
  impl_tac >- WORD_DECIDE_TAC >> strip_tac >> simp[] >> gvs[write'X_def, returnS]
QED

Theorem l3_models_asl_MoveWideOp_K:
  ∀hw r.
    l3_models_asl_instr (Data (MoveWide@64 (1w, MoveWideOp_K, hw, i, r)))
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
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
  impl_tac >- WORD_DECIDE_TAC >> strip_tac >> simp[] >> gvs[write'X_def, returnS]
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
  ∀b1 b2 i r2 r1.
    (i && ¬0b111111111111w ≠ 0b0w ⇒ i && ¬0b111111111111000000000000w = 0b0w)
  ⇒ l3_models_asl_instr
      (Data (AddSubImmediate@64 (1w, b1, b2, i, r2, r1)))
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
    `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
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
      IF_CASES_TAC >> gvs[returnS] >>
      qpat_x_assum `w2n _ < _ ⇒ _` mp_tac >> impl_tac >- WORD_DECIDE_TAC >>
      strip_tac >> simp[]
      )
    >- (
      dxrule l3_asl_SetTheFlags >>
      disch_then $ qspecl_then
        [`v2w [add_res1]`,`v2w [add_res2]`,
         `v2w [add_res3]`,`v2w [add_res4]`,`X_set 64 (&w2n r1) add_res0`] mp_tac >>
      strip_tac >> simp[] >>
      drule $ b64 alpha X_set_not_31 >>
      disch_then $ qspecl_then [`64`,`&w2n r1`,`add_res0`] mp_tac >> simp[int_ge] >>
      Cases_on `r1 = 31w` >> gvs[]
      >- (gvs[X_set_31, returnS, write'X_def, w2v_v2w]) >>
      impl_tac >- WORD_DECIDE_TAC >>
      strip_tac >> simp[returnS] >> gvs[w2v_v2w]
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
    `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
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
      IF_CASES_TAC >> gvs[returnS] >>
      qpat_x_assum `w2n _ < _ ⇒ _` mp_tac >> impl_tac >- WORD_DECIDE_TAC >>
      strip_tac >> simp[]
      )
    >- (
      dxrule l3_asl_SetTheFlags >>
      disch_then $ qspecl_then
        [`v2w [add_res1]`,`v2w [add_res2]`,
         `v2w [add_res3]`,`v2w [add_res4]`,`X_set 64 (&w2n r1) add_res0`] mp_tac >>
      strip_tac >> simp[] >>
      drule $ b64 alpha X_set_not_31 >>
      disch_then $ qspecl_then [`64`,`&w2n r1`,`add_res0`] mp_tac >> simp[int_ge] >>
      Cases_on `r1 = 31w` >> gvs[]
      >- (gvs[X_set_31, returnS, write'X_def, w2v_v2w]) >>
      impl_tac >- WORD_DECIDE_TAC >>
      strip_tac >> simp[returnS] >> gvs[w2v_v2w]
      )
    )
QED

Theorem l3_models_asl_LogicalImmediate_T:
  ∀i r2 r1.
    IS_SOME (EncodeBitMask i)
  ⇒ l3_models_asl_instr
      (Data (LogicalImmediate@64 (1w, LogicalOp_AND, T, i, r2, r1)))
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
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
  Cases_on `r1 = 31w` >> gvs[X_set_31]
  >- (
    unabbrev_all_tac >> simp[returnS] >> gvs[SetTheFlags_def] >>
    pop_assum mp_tac >> rpt $ pop_assum kall_tac >> strip_tac >>
    state_rel_tac[] >> gvs[X_def] >> rpt $ pop_assum kall_tac >>
    rename1 `v2w [HD (w2v foo)] @@ _` >> Cases_on `HD (w2v foo)` >> simp[] >>
    pop_assum mp_tac >>
    rewrite_tac[GSYM EL] >> DEP_REWRITE_TAC[el_w2v] >> simp[word_msb_def]
    ) >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`i && X r2 l3`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >> simp[returnS] >>
  gvs[SetTheFlags_def, write'X_def, X_def, Abbr `flag`] >>
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
  ∀op i r2 r1.
    IS_SOME (EncodeBitMask i)
  ⇒ l3_models_asl_instr (Data (LogicalImmediate@64 (1w, op, F, i, r2, r1)))
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
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
    disch_then $ qspec_then `l3w` assume_tac >> gvs[returnS]
    )
  >- (
    drule $ b64 alpha X_set_not_31 >>
    disch_then $ qspecl_then [`64`,`&w2n r1`,`l3w`] mp_tac >> simp[] >>
    impl_tac >- ( simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> simp[returnS]
    )
QED

Theorem l3_models_asl_LogicalImmediate:
  ∀op b i r2 r1.
    IS_SOME (EncodeBitMask i) ∧
    IS_SOME (EncodeLogicalOp (op, b))
  ⇒ l3_models_asl_instr (Data (LogicalImmediate@64 (1w, op, b, i, r2, r1)))
Proof
  Cases >> Cases >> gvs[EncodeLogicalOp_def] >>
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
  ∀shift_type b1 b2 r3 w r2 r1.
    l3_models_asl_instr
      (Data (AddSubShiftedRegister@64 (1w, b1, b2, shift_type, r3, w, r2, r1)))
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
  l3_run_tac >> unabbrev_all_tac >>
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
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
    impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> simp[returnS]
    ) >>
  dxrule l3_asl_SetTheFlags >>
  disch_then $ qspecl_then
    [`v2w [add_res1]`,`v2w [add_res2]`,
      `v2w [add_res3]`,`v2w [add_res4]`,`X_set 64 (&w2n r1) add_res0`] mp_tac >>
  strip_tac >> simp[] >> gvs[SetTheFlags_def, w2v_v2w] >>
  Cases_on `r1 = 31w` >> gvs[X_set_31]
  >- (simp[returnS, write'X_def]) >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`add_res0`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> simp[returnS]
QED

Theorem l3_models_asl_LogicalShiftedRegister_T:
  ∀b1 shift_type i r3 r2 r1. i < 64 ⇒
  l3_models_asl_instr
      (Data (LogicalShiftedRegister@64
        (1w, LogicalOp_AND, b1, T, shift_type, i, r3, r2, r1)))
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
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
  Cases_on `r1 = 31w` >> gvs[X_set_31]
  >- (simp[returnS] >> gvs[SetTheFlags_def, w2v_v2w]) >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`shift_res`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >> simp[returnS] >>
  gvs[SetTheFlags_def, write'X_def, X_def, w2v_v2w]
QED

Theorem l3_models_asl_LogicalShiftedRegister_F:
  ∀lop b1 shift_type i r3 r2 r1. i < 64 ⇒
  l3_models_asl_instr
      (Data (LogicalShiftedRegister@64
        (1w, lop, b1, F, shift_type, i, r3, r2, r1)))
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
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
  Cases_on `lop` >> gvs[write'X_def, l3_to_asl_LogicalOp_def]
QED

Theorem l3_models_asl_LogicalShiftedRegister:
  ∀lop b1 b2 shift_type i r3 r2 r1. i < 64 ⇒
    IS_SOME (EncodeLogicalOp (lop, b2))
  ⇒ l3_models_asl_instr
      (Data (LogicalShiftedRegister@64
        (1w, lop, b1, b2, shift_type, i, r3, r2, r1)))
Proof
  Cases >> Cases >> Cases >> gvs[EncodeLogicalOp_def] >>
  simp[l3_models_asl_LogicalShiftedRegister_T,
       l3_models_asl_LogicalShiftedRegister_F]
QED

(* TODO alternatively unset bits 29 of TCR_EL3, ??? of TCR_EL2, and 51/52 of TCR_EL1? *)
Theorem l3_asl_BranchTo_CALL:
  ¬ HavePACExt () ⇒ (* TODO versioning issue here *)
  ∀target l3 asl1.
    state_rel l3 asl1 ∧ asl_sys_regs_ok asl1
  ⇒ ∃asl2.
      do addr <- AArch64_BranchAddr target; write_regS PC_ref addr od asl1 =
        returnS () asl2 ∧
      state_rel (BranchTo (target, BranchType_CALL) l3) asl2 ∧
      asl_sys_regs_ok asl2
Proof
  rw[AArch64_BranchAddr_def] >>
  qspec_then `asl1` mp_tac UsingAArch32_F >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
  drule returnS_bindS_unit >> rw[] >> pop_assum kall_tac >>
  qspec_then `asl1` assume_tac PSTATE_read >>
  drule returnS_bindS_unit >> rw[] >>
  pop_assum kall_tac >> simp[AddrTop_def] >>
  qmatch_goalsub_abbrev_tac `S1TranslationRegime el` >>
  `el = l3.PSTATE.EL` by (unabbrev_all_tac >> state_rel_tac[]) >> gvs[] >>
  qspecl_then [`asl1`,`l3.PSTATE.EL`] mp_tac S1TranslationRegime >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >>
  disch_then kall_tac >> qmatch_goalsub_abbrev_tac `ELUsingAArch32 el` >>
  qspecl_then [`asl1`,`el`] mp_tac ELUsingAArch32_F >> simp[] >> impl_tac
  >- (unabbrev_all_tac >> rw[] >> gvs[asl_sys_regs_ok_def]) >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >>
  disch_then kall_tac >>
  `el = 1w ∨ el = 2w ∨ el = 3w` by (
    rw[Abbr `el`] >> Cases_on_word_value `l3.PSTATE.EL` >> gvs[]) >>
  simp[asl_word_rws, EL_MAP, el_w2v]
  >- ( (* EL0 and EL1 *)
    ntac 2 $ simp[Once sail2_valuesTheory.just_list_def] >>
    simp[extract_bit_64, v2w_word1_eq] >>
    `arm8$BranchTo (target, BranchType_CALL) l3 =
      let s1 = arm8$Hint_Branch BranchType_CALL l3 in
      let s0 = (if word_bit 55 target ∧ s1.TCR_EL1.TBI1 then
                  bit_field_insert 63 56 (0b11111111w : 8 word) target else target) in
      let s = (if ¬word_bit 55 s0 ∧ s1.TCR_EL1.TBI0 then
                    bit_field_insert 63 56 (0b0w : 8 word) s0 else s0,s1) in
      SND s with PC := FST s` by (
        LET_ELIM_TAC >>
        `l3.PSTATE.EL = EL0 ∨ l3.PSTATE.EL = EL1` by (
          unabbrev_all_tac >> gvs[] >> every_case_tac >> gvs[]) >>
        simp[BranchTo_def, Abbr `s1`, Hint_Branch_def] >>
        unabbrev_all_tac >> gvs[Hint_Branch_def]) >>
    simp[Hint_Branch_def] >>
    `target ' 55 = word_bit 55 target` by WORD_DECIDE_TAC >> simp[] >>
    IF_CASES_TAC >> gvs[]
    >- (
      ntac 2 $ simp[Once sail2_valuesTheory.just_list_def] >>
      drule TCR_EL1_read >> strip_tac >>
      drule returnS_bindS_unit >> simp[] >>
      disch_then kall_tac >>
      qpat_x_assum `ELUsingAArch32 _ _ = _` assume_tac >>
      drule returnS_bindS_unit >> simp[] >>
      disch_then kall_tac >>
      `word_bit 38 (reg'TCR_EL1 l3.TCR_EL1) = l3.TCR_EL1.TBI1` by (
        rpt $ pop_assum kall_tac >> simp[reg'TCR_EL1_def] >>
        CASE_TAC >> simp[] >> blastLib.BBLAST_TAC) >>
      simp[] >>
      qpat_abbrev_tac `con = if _ then 55 else 63i` >>
      `¬ (63 - con < 0)` by (unabbrev_all_tac >> IF_CASES_TAC >> gvs[]) >>
      gvs[] >> DEP_REWRITE_TAC[EL_MAP] >> simp[sail2_valuesTheory.just_list_def] >>
      conj_tac >- (unabbrev_all_tac >> IF_CASES_TAC >> gvs[]) >>
      qmatch_goalsub_abbrev_tac `word_bit 55 foo` >>
      `word_bit 55 foo = word_bit 55 target` by (
        unabbrev_all_tac >> rpt $ pop_assum kall_tac >>
        IF_CASES_TAC >> simp[] >> blastLib.BBLAST_TAC) >>
      gvs[Abbr `foo`] >> pop_assum kall_tac >> simp[Abbr `con`] >>
      reverse $ Cases_on `l3.TCR_EL1.TBI1` >> gvs[]
      >- (simp[asl_reg_rws, returnS] >> state_rel_tac[] >> gvs[asl_sys_regs_ok_def]) >>
      qspec_then `asl1` assume_tac PSTATE_read >>
      drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
      qmatch_goalsub_abbrev_tac `monad_bind x f` >>
      `x asl1 = returnS T asl1` by (
        simp[Abbr `x`] >> IF_CASES_TAC >> simp[] >>
        drule $ INST_TYPE [gamma |-> bool] returnS_bindS >> simp[] >>
        disch_then kall_tac >> Cases_on `l3.PSTATE.EL` >> gvs[]) >>
      drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
      gvs[Abbr `x`, Abbr `f`, el_w2v] >>
      qmatch_goalsub_abbrev_tac `write_regS _ bfi` >>
      qsuff_tac `bfi = bit_field_insert 63 56 (0b11111111w : 8 word) target`
      >- (
        rw[Abbr `bfi`, asl_reg_rws, returnS] >> state_rel_tac[] >>
        gvs[asl_sys_regs_ok_def]
        ) >>
      simp[Abbr `bfi`, EVAL ``i2w 72057594037927935 : word64``] >>
      blastLib.BBLAST_TAC >> simp[]
      )
    >- (
      ntac 2 $ simp[Once sail2_valuesTheory.just_list_def] >>
      drule TCR_EL1_read >> strip_tac >>
      drule returnS_bindS_unit >> simp[] >>
      disch_then kall_tac >>
      qpat_x_assum `ELUsingAArch32 _ _ = _` assume_tac >>
      drule returnS_bindS_unit >> simp[] >>
      disch_then kall_tac >>
      `word_bit 37 (reg'TCR_EL1 l3.TCR_EL1) = l3.TCR_EL1.TBI0` by (
        rpt $ pop_assum kall_tac >> simp[reg'TCR_EL1_def] >>
        CASE_TAC >> simp[] >> blastLib.BBLAST_TAC) >>
      simp[] >>
      qpat_abbrev_tac `con = if _ then 55 else 63i` >>
      `¬ (63 - con < 0)` by (unabbrev_all_tac >> IF_CASES_TAC >> gvs[]) >>
      gvs[] >> DEP_REWRITE_TAC[EL_MAP] >> simp[sail2_valuesTheory.just_list_def] >>
      conj_tac >- (unabbrev_all_tac >> IF_CASES_TAC >> gvs[]) >>
      simp[Abbr `con`] >> reverse $ Cases_on `l3.TCR_EL1.TBI0` >> gvs[]
      >- (simp[asl_reg_rws, returnS] >> state_rel_tac[] >> gvs[asl_sys_regs_ok_def]) >>
      qspec_then `asl1` assume_tac PSTATE_read >>
      drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
      qmatch_goalsub_abbrev_tac `monad_bind x f` >>
      `x asl1 = returnS T asl1` by (
        simp[Abbr `x`] >> IF_CASES_TAC >> simp[] >>
        drule $ INST_TYPE [gamma |-> bool] returnS_bindS >> simp[] >>
        disch_then kall_tac >> Cases_on `l3.PSTATE.EL` >> gvs[]) >>
      drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
      gvs[Abbr `x`, Abbr `f`, el_w2v] >>
      qmatch_goalsub_abbrev_tac `write_regS _ bfi` >>
      qsuff_tac `bfi = bit_field_insert 63 56 (0b0w : 8 word) target`
      >- (
        rw[Abbr `bfi`, asl_reg_rws, returnS] >> state_rel_tac[] >>
        gvs[asl_sys_regs_ok_def]
        ) >>
      simp[Abbr `bfi`, EVAL ``i2w 72057594037927935 : word64``] >>
      blastLib.BBLAST_TAC >> simp[]
      )
    )
  >- ( (* EL2 *)
    gvs[Abbr `el`] >> `l3.PSTATE.EL = EL2` by (gvs[] >> every_case_tac >> gvs[]) >>
    gvs[] >>
    ntac 2 $ simp[Once sail2_valuesTheory.just_list_def] >>
    simp[extract_bit_64, v2w_word1_eq] >>
    qspecl_then [`asl1`,`EL2`] mp_tac ELIsInHost_F >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    drule TCR_EL2_read >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qmatch_goalsub_abbrev_tac `word_bit _ (hi @@ lo)` >>
    `word_bit 20 (hi @@ lo) = word_bit 20 lo` by WORD_DECIDE_TAC >> simp[] >>
    simp[BranchTo_def, Hint_Branch_def] >>
    `word_bit 20 lo = l3.TCR_EL2.TBI` by (
      unabbrev_all_tac >> simp[reg'TCR_EL2_EL3_def] >> CASE_TAC >> gvs[] >>
      blastLib.BBLAST_TAC) >>
    simp[] >>
    qpat_x_assum `ELUsingAArch32 _ _ = _` assume_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    reverse $ Cases_on `l3.TCR_EL2.TBI` >> gvs[]
    >- (rw[asl_reg_rws, returnS] >> state_rel_tac[] >> gvs[asl_sys_regs_ok_def]) >>
    simp[EL_MAP, sail2_valuesTheory.just_list_def, el_w2v] >>
    qpat_x_assum `read_regS PSTATE_ref _ = _` assume_tac >> simp[IsInHost_def] >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qpat_x_assum `ELIsInHost _ _ = _` assume_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qmatch_goalsub_abbrev_tac `write_regS _ bfi` >>
    qsuff_tac `bfi = bit_field_insert 63 56 (0b0w : 8 word) target`
    >- (
      rw[Abbr `bfi`, asl_reg_rws, returnS] >> state_rel_tac[] >>
      gvs[asl_sys_regs_ok_def]
      ) >>
    simp[Abbr `bfi`, EVAL ``i2w 72057594037927935 : word64``] >>
    blastLib.BBLAST_TAC >> simp[]
    )
  >- ( (* EL3 *)
    gvs[Abbr `el`] >> `l3.PSTATE.EL = EL3` by (gvs[] >> every_case_tac >> gvs[]) >>
    gvs[] >>
    ntac 2 $ simp[Once sail2_valuesTheory.just_list_def] >>
    simp[extract_bit |> INST_TYPE [alpha |-> ``:32``] |> SIMP_RULE (srw_ss()) []] >>
    drule TCR_EL3_read >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qpat_x_assum `ELUsingAArch32 _ _ = _` assume_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    simp[BranchTo_def, Hint_Branch_def] >>
    `word_bit 20 (reg'TCR_EL2_EL3 l3.TCR_EL3) = l3.TCR_EL3.TBI` by (
      simp[reg'TCR_EL2_EL3_def] >> CASE_TAC >> gvs[] >> blastLib.BBLAST_TAC) >>
    simp[] >> DEP_REWRITE_TAC[EL_MAP] >> simp[] >>
    conj_tac >- (every_case_tac >> gvs[]) >>
    reverse $ Cases_on `l3.TCR_EL3.TBI` >> gvs[]
    >- (rw[asl_reg_rws, returnS] >> state_rel_tac[] >> gvs[asl_sys_regs_ok_def]) >>
    simp[el_w2v] >>
    qpat_x_assum `read_regS PSTATE_ref _ = _` assume_tac >> simp[IsInHost_def] >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qspecl_then [`asl1`,`EL3`] mp_tac ELIsInHost_F >>
    impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
    drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
    qmatch_goalsub_abbrev_tac `write_regS _ bfi` >>
    qsuff_tac `bfi = bit_field_insert 63 56 (0b0w : 8 word) target`
    >- (
      rw[Abbr `bfi`, asl_reg_rws, returnS] >> state_rel_tac[] >>
      gvs[asl_sys_regs_ok_def]
      ) >>
    simp[Abbr `bfi`, EVAL ``i2w 72057594037927935 : word64``] >>
    blastLib.BBLAST_TAC >> simp[]
    )
QED

Theorem l3_models_asl_BranchImmediate_CALL:
  ¬ HavePACExt () ⇒
  ∀a. a = sw2sw ((27 >< 2) a @@ (0b0w : word2)) ⇒
    l3_models_asl_instr_subject_to asl_sys_regs_ok
      (Branch (BranchImmediate (a, BranchType_CALL)))
Proof
  rw[l3_models_asl_instr_subject_to_def, l3_models_asl_subject_to_def] >>
  simp[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >> pop_assum kall_tac >>
  asl_cexecute_tac >> simp[] >> pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac `v2w aa` >>
  qmatch_goalsub_abbrev_tac `sw2sw $ v2w aF` >>
  `aa = w2v $ (27 >< 2) a` by (
    unabbrev_all_tac >> assume_tac $ GSYM $ mk_blast_thm ``a : 64 word`` >>
    pop_assum SUBST1_TAC >> EVAL_TAC) >>
  `aF = w2v $ (27 >< 2) a @@ (0b0w : 2 word)` by (
    unabbrev_all_tac >>
    assume_tac $ mk_blast_thm ``(27 >< 2) (a : 64 word) : 26 word`` >>
    pop_assum $ SUBST1_TAC o GSYM >> once_rewrite_tac[ops_to_v2w] >>
    once_rewrite_tac[word_concat_v2w_rwt] >> simp[w2v_v2w]) >>
  simp[] >> ntac 4 $ pop_assum kall_tac >>
  simp[dfn'BranchImmediate_def] >>
  simp[
    decode_bl_aarch64_instrs_branch_unconditional_immediate_def,
    execute_aarch64_instrs_branch_unconditional_immediate_def
    ] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  `asl_sys_regs_ok asl1` by (unabbrev_all_tac >> gvs[asl_sys_regs_ok_def]) >>
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
  drule l3_asl_BranchTo_CALL >> disch_then drule_all >>
  disch_then $ qspec_then `addr` strip_assume_tac >>
  qpat_x_assum `_ = returnS _ _` mp_tac >>
  simp[returnS, bindS, seqS] >>
  Cases_on `AArch64_BranchAddr addr asl2` >> Cases_on `q` >> simp[] >>
  strip_tac >> simp[asl_reg_rws, returnS, BranchTaken_ref_def] >> conj_tac
  >- state_rel_tac[]
  >- gvs[asl_sys_regs_ok_def]
QED

(****************************************)

(* TODO for CakeML
  Data (LogicalShiftedRegister@64 _)
  Data (BitfieldMove@64 _)
  Data (Division@64 _)
  Data (MultiplyHigh _)
  Data (MultiplyAddSub@64 _)
  Data (ConditionalCompareImmediate@64 _)
  Data (AddSubCarry@64 _)
  Data (ConditionalSelect@64 _)
  Branch (BranchImmediate (_, BranchType_JMP))
  Branch (BranchConditional _)
  Branch (BranchRegister _)
  LoadStore (LoadStoreImmediate@64 _)
  LoadStore (LoadStoreImmediate@8 _) (* XXX *)
*)

(****************************************)

val _ = export_theory();
