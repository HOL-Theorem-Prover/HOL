open HolKernel boolLib bossLib Parse BasicProvers dep_rewrite
open armv86aTheory armv86a_terminationTheory armv86a_typesTheory
open arm8Theory arm8Lib arm8_stepTheory arm8_stepLib
open wordsTheory bitstringTheory finite_mapTheory listTheory
     arithmeticTheory integerTheory
open l3_equivalenceTheory l3_equivalence_miscTheory l3_equivalence_lemmasTheory
open wordsLib intLib l3_equivalenceLib

val _ = new_theory "l3_equivalenceProof";

(****************************************)

Theorem l3_models_asl_NoOperation:
  l3_models_asl_instr NoOperation
Proof
  rw[unfold_rws] >>
  gvs[encode_rws] >>
  l3_decode_tac >>
  l3_run_tac >>
  asl_execute_tac >> gvs[] >>
  state_rel_tac []
QED

Theorem l3_models_asl_MoveWideOp_Z:
  ∀hw imm16 r.
    l3_models_asl_instr (Data (MoveWide@64 (1w, MoveWideOp_Z, hw, imm16, r)))
Proof
  rw[unfold_rws] >>
  gvs[encode_rws] >>
  l3_decode_tac >> rw[] >>
  l3_run_tac >>
  asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
  gvs[decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[undefined_MoveWideOp_def, monad_rws] >>
  gvs[execute_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[asl_word_rws, monad_rws] >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `hw` >> gvs[]) >>
  gvs[X_set_def, monad_rws] >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `r` >> gvs[]) >>
  gvs[monad_rws] >>
  Cases_on `r = 31w` >> gvs[monad_rws] >- (state_rel_tac []) >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `r` >> gvs[]) >>
  gvs[monad_rws] >>
  state_rel_tac[asl_word_rws]
  >- (
    CCONTR_TAC >>
    qpat_x_assum `_ < 0` mp_tac >> gvs[] >>
    Cases_on_word_value `hw` >> gvs[]
    )
  >- (
    gvs[EL_LUPDATE] >>
    `Num (ABS (((&w2n ((hw @@ (0b0w :word4)) :word6)) :int) + (15 :int))) =
      w2n (((hw :word2) @@ (0b0w :word4)) :word6) + 15` by (
        Cases_on_word_value `hw` >> gvs[]) >> gvs[]
    )
  >> (
    gvs[EL_LUPDATE] >>
    IF_CASES_TAC >> gvs[] >>
    rpt (BasicProvers.VAR_EQ_TAC) >>
    gvs[n2w_w2n]
    )
QED

Theorem l3_models_asl_MoveWideOp_N:
  ∀hw imm16 r.
    l3_models_asl_instr (Data (MoveWide@64 (1w, MoveWideOp_N, hw, imm16, r)))
Proof
  rw[unfold_rws] >>
  gvs[encode_rws] >>
  l3_decode_tac >> rw[] >>
  l3_run_tac >>
  asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
  gvs[decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[undefined_MoveWideOp_def, monad_rws] >>
  gvs[execute_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[asl_word_rws, monad_rws] >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `hw` >> gvs[]) >>
  gvs[X_set_def, monad_rws] >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `r` >> gvs[]) >>
  gvs[monad_rws] >>
  Cases_on `r = 31w` >> gvs[monad_rws] >- (state_rel_tac []) >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `r` >> gvs[]) >>
  gvs[monad_rws] >> state_rel_tac[asl_word_rws]
  >- (
    CCONTR_TAC >>
    qpat_x_assum `_ < 0` mp_tac >> gvs[] >>
    Cases_on_word_value `hw` >> gvs[]
    )
  >- (
    gvs[EL_LUPDATE] >>
    `Num (ABS (((&w2n ((hw @@ (0b0w :word4)) :word6)) :int) + (15 :int))) =
      w2n (((hw :word2) @@ (0b0w :word4)) :word6) + 15` by (
        Cases_on_word_value `hw` >> gvs[]) >> gvs[]
    )
  >> (
    gvs[EL_LUPDATE] >>
    IF_CASES_TAC >> gvs[] >>
    rpt (BasicProvers.VAR_EQ_TAC) >>
    gvs[n2w_w2n]
    )
QED

Theorem l3_models_asl_MoveWideOp_K:
  ∀hw imm16 r.
    l3_models_asl_instr (Data (MoveWide@64 (1w, MoveWideOp_K, hw, i, r)))
Proof
  rw[unfold_rws] >>
  gvs[encode_rws] >>
  l3_decode_tac >> rw[] >>
  l3_run_tac >>
  asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
  gvs[decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[undefined_MoveWideOp_def, monad_rws] >>
  gvs[execute_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[X_read_def, asl_word_rws, monad_rws] >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `r` >> gvs[]) >>
  gvs[X_set_def, monad_rws] >>
  Cases_on `r = 31w` >> gvs[monad_rws]
  >- (
    reverse IF_CASES_TAC >- (Cases_on_word_value `hw` >> gvs[]) >>
    gvs[X_set_def, monad_rws] >>
    state_rel_tac []
    ) >>
  reverse IF_CASES_TAC >- (Cases_on_word_value `r` >> gvs[]) >>
  gvs[monad_rws] >>
  reverse IF_CASES_TAC
  >- (Cases_on_word_value `hw` >> gvs[]) >>
  gvs[X_set_def, monad_rws] >> state_rel_tac[asl_word_rws]
  >- (
    CCONTR_TAC >>
    qpat_x_assum `_ < 0` mp_tac >> gvs[] >>
    Cases_on_word_value `hw` >> gvs[]
    )
  >- (
    gvs[EL_LUPDATE] >>
    `Num (ABS (((&w2n ((hw @@ (0b0w :word4)) :word6)) :int) + (15 :int))) =
      w2n (((hw :word2) @@ (0b0w :word4)) :word6) + 15` by (
        Cases_on_word_value `hw` >> gvs[]) >> gvs[] >>
    `∀ w : 64 word. (63 >< 0) w = (w2w w : 64 word)` by (
      strip_tac >> irule EXTRACT_ALL_BITS >> gvs[]) >> gvs[]
    )
  >> (
    gvs[EL_LUPDATE] >>
    IF_CASES_TAC >> gvs[] >>
    rpt (VAR_EQ_TAC) >>
    gvs[n2w_w2n]
    )
QED

Theorem l3_asl_AddWithCarry:
  ∀x y carry_b carry_v.
    flag_rel carry_b carry_v
  ⇒ armv86a$AddWithCarry x y carry_v =
     (I ## (λ(a,b,c,d).v2w [a;b;c;d])) (arm8$AddWithCarry (x, y, carry_b))
Proof
  rw[flag_rel_def] >> gvs[armv86aTheory.AddWithCarry_def, AddWithCarry_def] >>
  simp[integer_subrange_def, asl_word_rws] >> conj_asm1_tac
  >- (
    simp[lemTheory.w2ui_def, INT_ADD] >>
    simp[w2n_v2w, v2n, bitTheory.MOD_2EXP_def] >>
    qmatch_goalsub_abbrev_tac `b MOD 2` >>
    `b MOD 2 = b` by (unabbrev_all_tac >> rw[]) >> simp[] >>
    map_every qmatch_goalsub_abbrev_tac [`n2w n`, `TAKE l`] >>
    qspec_then `fixwidth l (n2v n)` mp_tac TAKE_LENGTH_ID >>
    rewrite_tac[length_fixwidth] >> disch_then SUBST_ALL_TAC >>
    unabbrev_all_tac >> simp[v2w_fixwidth]
    ) >>
  simp[lemTheory.w2ui_def, INT_ADD] >>
  simp[w2n_v2w, v2n, bitTheory.MOD_2EXP_def] >>
  qmatch_goalsub_abbrev_tac `b MOD 2` >>
  `b MOD 2 = b` by (unabbrev_all_tac >> rw[]) >> simp[] >>
  qmatch_goalsub_abbrev_tac `n2w stuff` >>
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

(* TODO this proof is tedious and repetitive - automation needed *)
Theorem l3_models_asl_AddSubImmediate:
  ∀b1 b2 i r2 r1.
    (i && ¬0b111111111111w ≠ 0b0w ⇒ i && ¬0b111111111111000000000000w = 0b0w)
  ⇒ l3_models_asl_instr
      (Data (AddSubImmediate@64 (1w, b1, b2, i, r2, r1)))
Proof
  rw[unfold_rws] >> gvs[encode_rws] >>
  reverse $ rpt IF_CASES_TAC >> gvs[]
  >- (
    `i = (0w : 40 word) @@ ((23 >< 12) i : 12 word) @@ (0w : 12 word)` by
      blastLib.FULL_BBLAST_TAC >> gvs[] >>
    qpat_x_assum `_ && i = _` kall_tac >>
    rename1 `_ @@ _ @@ _ @@ _ @@ j @@ _ @@ _` >>
    Cases_on `b1` >> Cases_on `b2` >> gvs[] >>
    l3_decode_tac >> rw[] >>
    l3_run_tac >> gvs[] >> pop_assum kall_tac >>
    asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL0" = l3.SP_EL0` by state_rel_tac[] >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL1" = l3.SP_EL1` by state_rel_tac[] >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL2" = l3.SP_EL2` by state_rel_tac[] >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL3" = l3.SP_EL3` by state_rel_tac[] >>
    `flag_rel (l3.PSTATE.SPS)
      ((asl.regstate.ProcState_reg "PSTATE").ProcState_SP)` by
      state_rel_tac [] >>
    `(asl.regstate.ProcState_reg "PSTATE").ProcState_EL =
        l3.PSTATE.EL` by state_rel_tac[] >>
    gvs[
      decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
      decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
      decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
      decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def
      ] >>
    gvs[asl_word_rws, monad_rws] >>
    gvs[execute_aarch64_instrs_integer_arithmetic_add_sub_immediate_def] >>
    gvs[asl_word_rws, monad_rws] >>
    gvs[dfn'AddSubImmediate_def] >>
    `flag_rel T 0b1w` by simp[flag_rel_def] >>
    drule (l3_asl_AddWithCarry |> INST_TYPE [alpha |-> ``:64``]) >>
    `flag_rel F 0b0w` by simp[flag_rel_def] >>
    drule (l3_asl_AddWithCarry |> INST_TYPE [alpha |-> ``:64``]) >>
    strip_tac >> strip_tac >> simp[COND_RATOR, monad_rws] >>
    `(r1 = 31w ⇔ w2n r1 = 31) ∧ (r2 = 31w ⇔ w2n r2 = 31)` by (
        rw[] >> eq_tac >> rw[] >> irule $ iffLR w2n_11 >>
        `w2n (0b11111w : 5 word) = 31` by simp[] >>
        pop_assum SUBST_ALL_TAC >> simp[]) >>
    `w2n r1 ≤ 31 ∧ w2n r2 ≤ 31` by (
      rw[] >> rename1 `w2n a` >>
      assume_tac (w2n_lt |> INST_TYPE [alpha |-> ``:5``]) >>
      pop_assum $ qspec_then `a` assume_tac >> drule SUB_LESS_OR >> simp[]) >>
    simp[]
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg, ps, _` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, ps, T)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        qmatch_goalsub_abbrev_tac `(_, ps, _)` >>
        Cases_on `AddWithCarry (l3.SP_EL0, ps, T)` >> gvs[] >>
        simp[write'X_rwt, X_set_def] >>
        reverse IF_CASES_TAC >> gvs[monad_rws]
        >- (
          PairCases_on `r` >> simp[SetTheFlags_def] >>
          state_rel_tac[] >> blastLib.BBLAST_TAC
          ) >>
        PairCases_on `r` >> simp[SetTheFlags_def, int_ge, monad_rws, R_ref_def] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, ps, _)` >>
      Cases_on `AddWithCarry (sp_el, ps, T)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      IF_CASES_TAC >> gvs[SetTheFlags_def] >>
      state_rel_tac[] >> blastLib.BBLAST_TAC >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg, ps, _` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, ps, T)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        reverse IF_CASES_TAC >> gvs[]
        >- (
          state_rel_tac[] >> blastLib.BBLAST_TAC >>
          simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
          ) >>
        simp[SP_set_def, write'SP_def, monad_rws, PSTATE_ref_def] >>
        simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
        reverse (Cases_on `l3.PSTATE.SPS`) >>
        gvs[flag_rel_def, monad_rws, asl_word_rws] >- state_rel_tac[] >>
        wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
        state_rel_tac[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        qmatch_goalsub_abbrev_tac `(_, ps, _)` >>
        Cases_on `AddWithCarry (l3.SP_EL0, ps, T)` >> gvs[] >>
        simp[SP_set_def, write'SP_def, write'X_rwt, X_set_def] >>
        PairCases_on `r` >> simp[SetTheFlags_def] >>
        simp[monad_rws, int_ge, COND_RATOR, PSTATE_ref_def] >>
        simp[SP_EL0_ref_def, R_ref_def] >>
        IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> gvs[asl_word_rws, EL_LUPDATE] >>
        IF_CASES_TAC >> gvs[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      simp[SP_set_def, write'SP_def, R_ref_def, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      simp[monad_rws, COND_RATOR] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, ps, _)` >>
      Cases_on `AddWithCarry (sp_el, ps, T)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      IF_CASES_TAC >> gvs[] >>
      state_rel_tac[] >> blastLib.BBLAST_TAC >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg, ps, _` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, ps, F)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        qmatch_goalsub_abbrev_tac `(_, ps, _)` >>
        Cases_on `AddWithCarry (l3.SP_EL0, ps, F)` >> gvs[] >>
        simp[SP_set_def, write'SP_def, write'X_rwt, X_set_def] >>
        PairCases_on `r` >> simp[SetTheFlags_def] >>
        simp[monad_rws, int_ge, COND_RATOR, PSTATE_ref_def] >>
        simp[SP_EL0_ref_def, R_ref_def] >>
        IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        gvs[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      simp[SP_set_def, write'SP_def, R_ref_def, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      simp[monad_rws, COND_RATOR] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, ps, _)` >>
      Cases_on `AddWithCarry (sp_el, ps, F)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      IF_CASES_TAC >> gvs[] >>
      state_rel_tac[] >> blastLib.BBLAST_TAC >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg, ps, _` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, ps, F)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        reverse IF_CASES_TAC >> gvs[]
        >- (
          state_rel_tac[] >> blastLib.BBLAST_TAC >>
          simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
          ) >>
        simp[SP_set_def, write'SP_def, monad_rws, PSTATE_ref_def] >>
        simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
        reverse (Cases_on `l3.PSTATE.SPS`) >>
        gvs[flag_rel_def, monad_rws, asl_word_rws] >- state_rel_tac[] >>
        wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
        state_rel_tac[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      assume_tac (EVAL ``slice_mask 12 0 12 : word12``) >> simp[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        qmatch_goalsub_abbrev_tac `(_, ps, _)` >>
        Cases_on `AddWithCarry (l3.SP_EL0, ps, F)` >> gvs[] >>
        simp[SP_set_def, write'SP_def, write'X_rwt, X_set_def] >>
        PairCases_on `r` >> simp[SetTheFlags_def] >>
        simp[monad_rws, int_ge, COND_RATOR, PSTATE_ref_def] >>
        simp[SP_EL0_ref_def, R_ref_def] >>
        IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        gvs[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      simp[SP_set_def, write'SP_def, R_ref_def, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      simp[monad_rws, COND_RATOR] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, ps, _)` >>
      Cases_on `AddWithCarry (sp_el, ps, F)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      IF_CASES_TAC >> gvs[] >>
      state_rel_tac[] >> blastLib.BBLAST_TAC >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    )
  >- (
    `i = (0w : 52 word) @@ ((11 >< 0) i : 12 word)` by
      blastLib.FULL_BBLAST_TAC >> gvs[] >>
    last_x_assum kall_tac >> rename1 `_ @@ _ @@ _ @@ _ @@ j @@ _ @@ _` >>
    Cases_on `b1` >> Cases_on `b2` >> gvs[] >>
    l3_decode_tac >> rw[] >>
    l3_run_tac >> gvs[] >> pop_assum kall_tac >>
    asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL0" = l3.SP_EL0` by state_rel_tac[] >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL1" = l3.SP_EL1` by state_rel_tac[] >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL2" = l3.SP_EL2` by state_rel_tac[] >>
    `asl.regstate.bitvector_64_dec_reg "SP_EL3" = l3.SP_EL3` by state_rel_tac[] >>
    `flag_rel (l3.PSTATE.SPS)
      ((asl.regstate.ProcState_reg "PSTATE").ProcState_SP)` by
      state_rel_tac [] >>
    `(asl.regstate.ProcState_reg "PSTATE").ProcState_EL =
        l3.PSTATE.EL` by state_rel_tac[] >>
    gvs[
      decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
      decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
      decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
      decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def
      ] >>
    gvs[asl_word_rws, monad_rws] >>
    gvs[execute_aarch64_instrs_integer_arithmetic_add_sub_immediate_def] >>
    gvs[asl_word_rws, monad_rws] >>
    gvs[dfn'AddSubImmediate_def] >>
    `flag_rel T 0b1w` by simp[flag_rel_def] >>
    drule (l3_asl_AddWithCarry |> INST_TYPE [alpha |-> ``:64``]) >>
    `flag_rel F 0b0w` by simp[flag_rel_def] >>
    drule (l3_asl_AddWithCarry |> INST_TYPE [alpha |-> ``:64``]) >>
    strip_tac >> strip_tac >> simp[COND_RATOR, monad_rws] >>
    `(r1 = 31w ⇔ w2n r1 = 31) ∧ (r2 = 31w ⇔ w2n r2 = 31)` by (
        rw[] >> eq_tac >> rw[] >> irule $ iffLR w2n_11 >>
        `w2n (0b11111w : 5 word) = 31` by simp[] >>
        pop_assum SUBST_ALL_TAC >> simp[]) >>
    `w2n r1 ≤ 31 ∧ w2n r2 ≤ 31` by (
      rw[] >> rename1 `w2n a` >>
      assume_tac (w2n_lt |> INST_TYPE [alpha |-> ``:5``]) >>
      pop_assum $ qspec_then `a` assume_tac >> drule SUB_LESS_OR >> simp[]) >>
    simp[]
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, ¬w2w j, T)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        Cases_on `AddWithCarry (l3.SP_EL0, ¬w2w j, T)` >> gvs[] >>
        simp[write'X_rwt, X_set_def] >>
        reverse IF_CASES_TAC >> gvs[monad_rws]
        >- (
          PairCases_on `r` >> simp[SetTheFlags_def] >>
          state_rel_tac[] >> blastLib.BBLAST_TAC
          ) >>
        PairCases_on `r` >> simp[SetTheFlags_def, int_ge, monad_rws] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, _ _)` >>
      Cases_on `AddWithCarry (sp_el, ¬w2w j, T)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      IF_CASES_TAC >> gvs[SetTheFlags_def] >>
      state_rel_tac[] >> blastLib.BBLAST_TAC >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, ¬w2w j, T)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        reverse $ IF_CASES_TAC >> gvs[]
        >- (
          state_rel_tac[] >> blastLib.BBLAST_TAC >>
          simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
          ) >>
        simp[SP_set_def, write'SP_def, monad_rws, PSTATE_ref_def] >>
        gvs[flag_rel_def] >> Cases_on `¬l3.PSTATE.SPS` >> gvs[]
        >- state_rel_tac[] >>
        simp[monad_rws, COND_RATOR] >>
        wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
        state_rel_tac[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        Cases_on `AddWithCarry (l3.SP_EL0, ¬w2w j, T)` >> gvs[] >>
        simp[write'X_rwt, X_set_def, monad_rws, COND_RATOR, int_ge] >>
        simp[R_ref_def, asl_word_rws] >>
        reverse IF_CASES_TAC >> gvs[]
        >- (
          PairCases_on `r` >> simp[SetTheFlags_def] >>
          state_rel_tac[] >> blastLib.BBLAST_TAC >> simp[EL_LUPDATE] >>
          IF_CASES_TAC >> gvs[]
          ) >>
        simp[SP_set_def, write'SP_def, monad_rws, COND_RATOR, PSTATE_ref_def] >>
        PairCases_on `r` >> simp[SetTheFlags_def] >> state_rel_tac[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, _ _)` >>
      Cases_on `AddWithCarry (sp_el, ¬w2w j, T)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      IF_CASES_TAC >> gvs[SetTheFlags_def] >>
      simp[SP_set_def, write'SP_def, monad_rws, COND_RATOR, PSTATE_ref_def] >>
      state_rel_tac[] >> blastLib.BBLAST_TAC >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, w2w j, F)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        reverse $ IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        Cases_on `AddWithCarry (l3.SP_EL0, w2w j, F)` >> gvs[] >>
        simp[write'X_rwt, X_set_def, monad_rws, COND_RATOR, int_ge] >>
        simp[R_ref_def, asl_word_rws] >>
        IF_CASES_TAC >> gvs[] >>
        PairCases_on `r` >> simp[SetTheFlags_def] >>
        state_rel_tac[] >> blastLib.BBLAST_TAC >>
        simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, _ _)` >>
      Cases_on `AddWithCarry (sp_el, w2w j, F)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      IF_CASES_TAC >> gvs[SetTheFlags_def] >>
      state_rel_tac[] >> blastLib.BBLAST_TAC >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    >- (
      reverse $ IF_CASES_TAC >> gvs[]
      >- (
        simp[X_read_def, write'X_def, X_set_def, X_def, int_ge, monad_rws] >>
        simp[R_ref_def, asl_word_rws] >>
        assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
        qmatch_goalsub_abbrev_tac `EL _ reg` >>
        `EL (w2n r2) reg = l3.REG r2` by (
          state_rel_tac[] >> unabbrev_all_tac >> gvs[] >>
          ntac 2 $ last_x_assum $ qspec_then `w2n r2` assume_tac >> gvs[]) >>
        simp[] >> Cases_on `AddWithCarry (l3.REG r2, w2w j, F)` >> gvs[] >>
        simp[PSTATE_ref_def, monad_rws, COND_RATOR] >>
        PairCases_on `r` >> gvs[SetTheFlags_def] >>
        reverse $ IF_CASES_TAC >> gvs[]
        >- (
          state_rel_tac[] >> blastLib.BBLAST_TAC >>
          simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
          ) >>
        simp[SP_set_def, write'SP_def, monad_rws, PSTATE_ref_def, COND_RATOR] >>
        gvs[flag_rel_def] >>
        simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
        Cases_on `¬ l3.PSTATE.SPS` >> gvs[] >- state_rel_tac[] >>
        wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >> state_rel_tac[]
        ) >>
      gvs[SP_read_def, SP_def, monad_rws, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      assume_tac (extract_all_bits |> INST_TYPE [alpha |-> ``:64``]) >> gvs[] >>
      gvs[COND_RATOR, monad_rws, asl_word_rws] >>
      reverse (Cases_on `l3.PSTATE.SPS`) >>
      gvs[flag_rel_def, monad_rws, asl_word_rws]
      >- (
        Cases_on `AddWithCarry (l3.SP_EL0, w2w j, F)` >> gvs[] >>
        simp[write'X_rwt, X_set_def, write'SP_def, SP_set_def, PSTATE_ref_def] >>
        simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
        simp[monad_rws, COND_RATOR, int_ge] >>
        simp[R_ref_def, asl_word_rws] >>
        PairCases_on `r` >> simp[SetTheFlags_def] >>
        IF_CASES_TAC >> gvs[] >>
        state_rel_tac[] >> simp[EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
        ) >>
      simp[monad_rws, X_set_def, write'X_rwt, int_ge] >>
      wordsLib.Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >>
      qmatch_goalsub_abbrev_tac `AddWithCarry (sp_el, _ _)` >>
      Cases_on `AddWithCarry (sp_el, w2w j, F)` >> gvs[] >>
      simp[monad_rws, R_ref_def, COND_RATOR] >>
      PairCases_on `r` >> simp[SetTheFlags_def] >>
      simp[SP_set_def, write'SP_def, monad_rws, COND_RATOR, PSTATE_ref_def] >>
      simp[SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def] >>
      IF_CASES_TAC >> gvs[] >>
      state_rel_tac[] >>
      simp[asl_word_rws, EL_LUPDATE] >> IF_CASES_TAC >> gvs[]
      )
    )
QED

(****************************************)

val _ = export_theory();
