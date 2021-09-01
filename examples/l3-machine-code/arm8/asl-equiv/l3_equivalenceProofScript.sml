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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel _ asl` kall_tac >>
  dxrule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`reg`,`v`] mp_tac >> simp[Abbr `reg`, int_ge] >>
  impl_tac >- WORD_DECIDE_TAC >> strip_tac >> simp[] >> gvs[write'X_def, returnS]
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel _ asl` kall_tac >>
  dxrule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`reg`,`v`] mp_tac >> simp[Abbr `reg`, int_ge] >>
  impl_tac >- WORD_DECIDE_TAC >> strip_tac >> simp[] >> gvs[write'X_def, returnS]
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
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
    simp[integer_subrange_def, asl_word_rws] >>
    qmatch_goalsub_abbrev_tac `foo = 0` >>
    Cases_on `foo = 0` >> gvs[] >- (unabbrev_all_tac >> gvs[]) >>
    simp[v2n_fixwidth] >>
    `foo < 2 ** 64` by (
      simp[Abbr `foo`, DIV_LT_X] >>
      qspec_then `word_abs x2` assume_tac w2n_lt >> gvs[]) >>
    gvs[] >>
    qmatch_goalsub_abbrev_tac `&s` >>
    `64 ≤ s` by simp[Abbr `s`, LENGTH_add] >>
    `&s - 1i - 63 = &(s - 64)` by (
      simp[int_arithTheory.INT_NUM_SUB] >> ARITH_TAC) >>
    pop_assum SUBST_ALL_TAC >> simp[Abbr `s`] >>
    cheat (* TODO *)
    )
  >- (
    simp[neg_rat, lt_ratl, INT_CEILING_NEG_DIV, INT_FLOOR_EQNS] >>
    reverse IF_CASES_TAC >> gvs[]
    >- (gvs[ZERO_DIV] >> simp[integer_subrange_def, asl_word_rws]) >>
    simp[integer_subrange_def, asl_word_rws] >>
    qmatch_goalsub_abbrev_tac `foo = 0` >>
    Cases_on `foo = 0` >> gvs[] >- (unabbrev_all_tac >> gvs[]) >>
    simp[v2n_fixwidth] >>
    `foo < 2 ** 64` by (
      simp[Abbr `foo`, DIV_LT_X] >>
      qspec_then `word_abs x2` assume_tac w2n_lt >> gvs[]) >>
    gvs[] >>
    qmatch_goalsub_abbrev_tac `&s` >>
    `64 ≤ s` by simp[Abbr `s`, LENGTH_add] >>
    `&s - 1i - 63 = &(s - 64)` by (
      simp[int_arithTheory.INT_NUM_SUB] >> ARITH_TAC) >>
    pop_assum SUBST_ALL_TAC >> simp[Abbr `s`] >>
    cheat (* TODO *)
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
    simp[GSYM $ (SIMP_CONV (srw_ss()) [sail2_valuesTheory.just_list_primitive_def]
                  THENC CEVAL) $ ``just_list``] >>
    simp[sail2_valuesTheory.just_list_def] >>
    simp[
      decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi_def,
      decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi_def
      ] >>
    simp[asl_reg_rws, seqS, returnS] >> irule_at Any EQ_REFL) >>
  simp[Abbr `wr`, Abbr `s`, asl_reg_rws, seqS, returnS] >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
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
  qmatch_goalsub_abbrev_tac `_⦇ r1 ↦ l3_res ⦈` >>
  qsuff_tac `res = l3_res` >> rw[] >> gvs[write'X_def] >>
  unabbrev_all_tac >>
  map_every qabbrev_tac [`x2 = X r2 l3 : 64 word`,`x3 = X r3 l3 : 64 word`] >>
  rpt $ pop_assum kall_tac >>
  simp[asl_Int_def, ExtendWord_def] >> IF_CASES_TAC >> gvs[]
  >- (
    simp[integer_subrange_def, asl_word_rws] >>
    cheat (* TODO *)
    )
  >- (
    cheat (* TODO *)
    )
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
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
  cheat (* TODO *)
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
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
    simp[returnS] >> gvs[write'X_def]
    ) >>
  drule l3_asl_SetTheFlags >>
  disch_then $ qspecl_then [
    `v2w [res1]`,`v2w [res2]`,`v2w [res3]`,`v2w [res4]`,
    `X_set 64 (&w2n r1) res0`] assume_tac >> gvs[] >>
  gvs[w2v_v2w] >>
  Cases_on `r1 = 31w` >> gvs[X_set_31, returnS, write'X_def] >>
  drule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`&w2n r1`,`res0`] mp_tac >> simp[] >>
  impl_tac >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >> gvs[] >>
  simp[returnS] >> gvs[write'X_def]
QED

(* TODO alternatively unset bits 29 of TCR_EL3, ??? of TCR_EL2, and 51/52 of TCR_EL1? *)
Theorem l3_asl_BranchTo:
  ¬ HavePACExt () ⇒ (* TODO versioning issue here *)
  ∀l3 asl1.
    state_rel l3 asl1 ∧ asl_sys_regs_ok asl1
  ⇒ ∀target btype. ∃asl2.
      do addr <- AArch64_BranchAddr target; write_regS PC_ref addr od asl1 =
        returnS () asl2 ∧
      state_rel (BranchTo (target, btype) l3) asl2 ∧
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
    `arm8$BranchTo (target, btype) l3 =
      let s1 = arm8$Hint_Branch btype l3 in
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
  qcollapse_tac `(27 >< 2) a : 26 word` >>
  qcollapse_tac `(((27 >< 2) a : 26 word) @@ (0w : 2 word)) : 28 word` >>
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
  drule l3_asl_BranchTo >> disch_then drule_all >>
  disch_then $ qspecl_then [`addr`,`BranchType_CALL`] strip_assume_tac >>
  qpat_x_assum `_ = returnS _ _` mp_tac >>
  simp[returnS, bindS, seqS] >>
  Cases_on `AArch64_BranchAddr addr asl2` >> Cases_on `q` >> simp[] >>
  strip_tac >> simp[asl_reg_rws, returnS, BranchTaken_ref_def] >> conj_tac
  >- state_rel_tac[]
  >- gvs[asl_sys_regs_ok_def]
QED

Theorem l3_models_asl_BranchImmediate_JMP:
  ¬ HavePACExt () ⇒
  ∀a. a = sw2sw ((27 >< 2) a @@ (0b0w : word2)) ⇒
    l3_models_asl_instr_subject_to asl_sys_regs_ok
      (Branch (BranchImmediate (a, BranchType_JMP)))
Proof
  rw[l3_models_asl_instr_subject_to_def, l3_models_asl_subject_to_def] >>
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
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  `asl_sys_regs_ok asl1` by (unabbrev_all_tac >> gvs[asl_sys_regs_ok_def]) >>
  drule PC_read >> strip_tac >> drule returnS_bindS_unit >> rw[] >>
  ntac 2 $ pop_assum kall_tac >>
  simp[INT_ADD_CALCULATE, integer_wordTheory.i2w_pos, GSYM word_add_def] >>
  qmatch_goalsub_abbrev_tac `BranchTo (addr, _)` >>
  simp[armv86aTheory.BranchTo_def] >>
  qspec_then `asl1` mp_tac $ GEN_ALL UsingAArch32_F >>
  impl_tac >- gvs[asl_sys_regs_ok_def] >> strip_tac >>
  drule returnS_bindS_unit >> simp[] >> disch_then kall_tac >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  drule l3_asl_BranchTo >> disch_then drule_all >>
  disch_then $ qspecl_then [`addr`,`BranchType_JMP`] strip_assume_tac >>
  qpat_x_assum `_ = returnS _ _` mp_tac >>
  simp[returnS, bindS, seqS] >>
  Cases_on `AArch64_BranchAddr addr asl1` >> Cases_on `q` >> simp[] >>
  strip_tac >> simp[asl_reg_rws, returnS, BranchTaken_ref_def] >> conj_tac
  >- state_rel_tac[]
  >- gvs[asl_sys_regs_ok_def]
QED

Theorem l3_models_asl_BranchConditional:
  ¬ HavePACExt () ⇒
  ∀a i. a = sw2sw ((20 >< 2) a @@ (0b0w : word2)) ∧ i ≠ 0b1111w ⇒
    l3_models_asl_instr_subject_to asl_sys_regs_ok
      (Branch (BranchConditional (a, i)))
Proof
  rw[l3_models_asl_instr_subject_to_def, l3_models_asl_subject_to_def] >>
  simp[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >> pop_assum kall_tac >>
  asl_cexecute_tac >> simp[] >> pop_assum kall_tac >>
  qcollapse_tac `(20 >< 2) a : 19 word` >>
  qcollapse_tac `(((20 >< 2) a : 19 word) @@ (0w : 2 word)) : 21 word` >>
  qmatch_goalsub_abbrev_tac `if cnd then _ else _` >>
  `cnd` by (
    unabbrev_all_tac >> CCONTR_TAC >> gvs[] >>
    qpat_x_assum `i ≠ _` mp_tac >> blastLib.BBLAST_TAC >> simp[]) >>
  simp[bindS, returnS] >>
  qpat_x_assum `Abbrev (cnd ⇔ _)` kall_tac >>
  qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  `asl_sys_regs_ok asl1` by (unabbrev_all_tac >> gvs[asl_sys_regs_ok_def]) >>
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
  drule l3_asl_BranchTo >> disch_then drule_all >>
  disch_then $ qspecl_then [`addr`,`BranchType_JMP`] strip_assume_tac >>
  qpat_x_assum `_ = returnS _ _` mp_tac >>
  simp[returnS, bindS, seqS] >>
  Cases_on `AArch64_BranchAddr addr asl1` >> Cases_on `q` >> simp[] >>
  strip_tac >> simp[asl_reg_rws, returnS, BranchTaken_ref_def] >> conj_tac
  >- state_rel_tac[]
  >- gvs[asl_sys_regs_ok_def]
QED

(****************************************)

(* TODO for CakeML
  Branch (BranchRegister _)
  LoadStore (LoadStoreImmediate@64 _)
  LoadStore (LoadStoreImmediate@8 _) (* XXX *)
*)

(****************************************)

val _ = export_theory();
