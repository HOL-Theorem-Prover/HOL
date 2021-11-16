open HolKernel boolLib bossLib Parse BasicProvers dep_rewrite
open armv86aTheory armv86a_typesTheory arm8Theory
open wordsTheory bitstringTheory listTheory
open l3_equivalenceTheory l3_equivalenceProofTheory arm8_targetTheory
open wordsLib l3_equivalenceLib

val _ = new_theory "l3_cakemlProof";

Triviality l3_asl_arm8_encode_fail[simp]:
  ∀instr. MEM instr arm8_target$arm8_encode_fail ⇒ l3_models_asl_instr instr
Proof
  rw[arm8_encode_fail_def] >> simp[l3_models_asl_NoOperation]
QED

Theorem l3_asl_arm8_load_store_ast:
  ∀instr ls r1 r2 a.
    MEM instr (arm8_target$arm8_load_store_ast ls r1 r2 a) ∧
    ls ≠ MemOp_PREFETCH ∧
    (∀s. Encode instr ≠ BadCode s)
  ⇒ l3_models_asl_instr instr
Proof
  rw[arm8_load_store_ast_def] >> gvs[]
  >- (
    irule l3_models_asl_AddSubImmediate >> simp[] >>
    gvs[encode_rws] >> every_case_tac >> gvs[]
    )
  >~ [`AddSubImmediate@64`]
  >- (
    irule l3_models_asl_AddSubImmediate >> simp[] >>
    gvs[encode_rws] >> every_case_tac >> gvs[]
    ) >>
  (
    Cases_on `ls` >> gvs[]
    >- ( (* Load *)
      irule $ SIMP_RULE std_ss [LET_DEF]
        l3_models_asl_LoadStoreImmediate_NORMAL_LOAD_FFFFF >>
      simp[]
      )
    >- ( (* Store *)
      irule $ SIMP_RULE std_ss [LET_DEF]
        l3_models_asl_LoadStoreImmediate_NORMAL_STORE_FFFFF >>
      simp[]
      )
  )
QED

Theorem l3_asl_arm8_ast:
  ∀instr prog.
    MEM instr (arm8_target$arm8_ast prog) ∧
    (∀s. Encode instr ≠ BadCode s)
  ⇒ l3_models_asl_instr instr
Proof
  rpt gen_tac >> Cases_on `prog` >> simp[arm8_ast_def]
  >- ( (* Inst *)
    Cases_on `i` >> simp[arm8_ast_def] >> rw[]
    >- simp[l3_models_asl_NoOperation] (* Skip *)
    >- ( (* Const - 1 *)
      gvs[arm8_enc_mov_imm_def] >>
      every_case_tac >> gvs[l3_models_asl_MoveWideOp_Z, l3_models_asl_MoveWideOp_N] >>
      irule l3_models_asl_LogicalImmediate >> simp[EncodeLogicalOp_def]
      )
    >- ( (* Const - 2 *)
      gvs[arm8_enc_mov_imm_def] >>
      every_case_tac >>
      gvs[l3_models_asl_MoveWideOp_Z,
          l3_models_asl_MoveWideOp_N, l3_models_asl_MoveWideOp_K]
      )
    >- ( (* Arith *)
      Cases_on `a` >> gvs[arm8_ast_def]
      >- ( (* Binop *)
        Cases_on `r` >> gvs[arm8_ast_def]
        >- ( (* Reg *)
          Cases_on `b` >> simp[]
          >- simp[l3_models_asl_AddSubShiftedRegister] (* Add *)
          >- simp[l3_models_asl_AddSubShiftedRegister] (* Sub *) >>
          (* And, Or, Xor *)
          irule l3_models_asl_LogicalShiftedRegister >>
          simp[EncodeLogicalOp_def, bop_enc_def]
          )
        >- ( (* Imm *)
          Cases_on `b` >> gvs[]
          >- ( (* Add *)
            irule l3_models_asl_AddSubImmediate >> gvs[encode_rws] >>
            every_case_tac >> gvs[]
            )
          >- ( (* Sub *)
            irule l3_models_asl_AddSubImmediate >> gvs[encode_rws] >>
            every_case_tac >> gvs[]
            )
          >- ( (* And *)
            irule l3_models_asl_LogicalImmediate >>
            simp[EncodeLogicalOp_def, bop_enc_def] >>
            gvs[encode_rws] >> every_case_tac >> gvs[]
            )
          >- ( (* Or *)
            irule l3_models_asl_LogicalImmediate >>
            simp[EncodeLogicalOp_def, bop_enc_def] >>
            gvs[encode_rws] >> every_case_tac >> gvs[]
            )
          >- ( (* Xor *)
            IF_CASES_TAC >> gvs[]
            >- (
              irule l3_models_asl_LogicalShiftedRegister >>
              simp[EncodeLogicalOp_def, bop_enc_def]
              )
            >- (
              irule l3_models_asl_LogicalImmediate >>
              simp[EncodeLogicalOp_def, bop_enc_def] >>
              gvs[encode_rws] >> every_case_tac >> gvs[]
              )
            )
          )
        )
      >- ( (* Shift *)
        Cases_on `s` >> gvs[arm8_ast_def]
        >- ( (* Lsl *)
          every_case_tac >> gvs[] >>
          irule l3_models_asl_BitfieldMove >> simp[] >> WORD_DECIDE_TAC
          )
        >- ( (* Lsr *)
          every_case_tac >> gvs[] >>
          irule l3_models_asl_BitfieldMove >> simp[] >>
          gvs[encode_rws] >> every_case_tac >> gvs[]
          )
        >- ( (* Asr *)
          every_case_tac >> gvs[] >>
          irule l3_models_asl_BitfieldMove >> simp[] >>
          gvs[encode_rws] >> every_case_tac >> gvs[]
          )
        >- simp[l3_models_asl_ExtractRegister] (* Ror *)
        )
      >- simp[l3_models_asl_Division] (* Div *)
      >- simp[l3_models_asl_MultiplyHigh] (* LongMul - 1 *)
      >- simp[l3_models_asl_MultiplyAddSub] (* LongMul - 2 *)
      >- simp[l3_models_asl_AddSubImmediate] (* AddCarry - 1 *)
      >- simp[l3_models_asl_ConditionalCompareImmediate] (* AddCarry - 2 *)
      >- simp[l3_models_asl_AddSubCarry] (* AddCarry - 3 *)
      >- simp[l3_models_asl_MoveWideOp_Z] (* AddCarry - 4 *)
      >- simp[l3_models_asl_AddSubCarry] (* AddCarry - 5 *)
      >- simp[l3_models_asl_AddSubShiftedRegister] (* AddOverflow - 1 *)
      >- simp[l3_models_asl_ConditionalSelect] (* AddOverflow - 2 *)
      >- simp[l3_models_asl_AddSubShiftedRegister] (* SubOverflow - 1 *)
      >- simp[l3_models_asl_ConditionalSelect] (* SubOverflow - 2 *)
      )
    >- ( (* Mem *)
      Cases_on `m` >>
      gvs[arm8_ast_def]
      >- ( (* Load *)
        Cases_on `a` >> gvs[arm8_ast_def] >>
        irule l3_asl_arm8_load_store_ast >> simp[] >>
        goal_assum $ drule_at Any >> simp[]
        )
      >- ( (* Load8 *)
        Cases_on `a` >> gvs[arm8_ast_def] >>
        irule $ SIMP_RULE std_ss [LET_DEF]
          l3_models_asl_LoadStoreImmediate_8_NORMAL_LOAD_FFFFF >>
        simp[]
        )
      >- ( (* Store *)
        Cases_on `a` >> gvs[arm8_ast_def] >>
        irule l3_asl_arm8_load_store_ast >> simp[] >>
        goal_assum $ drule_at Any >> simp[]
        )
      >- ( (* Store8 *)
        Cases_on `a` >> gvs[arm8_ast_def] >>
        irule $ SIMP_RULE std_ss [LET_DEF]
          l3_models_asl_LoadStoreImmediate_8_NORMAL_STORE_FFFFF >>
        simp[]
        )
      )
    )
  >- ( (* Jump *)
    rw[] >> irule l3_models_asl_BranchImmediate_JMP >>
    gvs[encode_rws] >> pop_assum mp_tac >> IF_CASES_TAC >> simp[]
    )
  >- ( (* JumpCmp *)
    Cases_on `r` >> gvs[arm8_ast_def] >> rw[]
    >- ( (* Reg - 1 *)
      irule l3_models_asl_LogicalShiftedRegister >>
      simp[EncodeLogicalOp_def]
      )
    >- ( (* Reg - 2 *)
      irule l3_models_asl_BranchConditional >>
      conj_tac >- gvs[asmSemTheory.is_test_def, cmp_cond_def] >>
      gvs[encode_rws] >> pop_assum mp_tac >> IF_CASES_TAC >> gvs[]
      )
    >- simp[l3_models_asl_AddSubShiftedRegister] (* Reg - 3 *)
    >- ( (* Reg - 4 *)
      irule l3_models_asl_BranchConditional >>
      conj_tac >- (Cases_on `c` >> gvs[asmSemTheory.is_test_def, cmp_cond_def]) >>
      gvs[encode_rws] >> pop_assum mp_tac >> IF_CASES_TAC >> gvs[]
      )
    >- ( (* Imm - 1 *)
      irule l3_models_asl_LogicalImmediate >>
      simp[EncodeLogicalOp_def] >> gvs[encode_rws] >> every_case_tac >> gvs[]
      )
    >- ( (* Imm - 2 *)
      irule l3_models_asl_BranchConditional >>
      conj_tac >- gvs[asmSemTheory.is_test_def, cmp_cond_def] >>
      gvs[encode_rws] >> pop_assum mp_tac >> IF_CASES_TAC >> gvs[]
      )
    >- ( (* Imm - 3 *)
      irule l3_models_asl_AddSubImmediate >>
      gvs[encode_rws] >> every_case_tac >> gvs[]
      )
    >- (
      irule l3_models_asl_BranchConditional >>
      conj_tac >- (Cases_on `c` >> gvs[asmSemTheory.is_test_def, cmp_cond_def]) >>
      gvs[encode_rws] >> pop_assum mp_tac >> IF_CASES_TAC >> gvs[]
      )
    )
  >- ( (* Call *)
    rw[] >> irule l3_models_asl_BranchImmediate_CALL >>
    gvs[encode_rws] >> pop_assum mp_tac >> IF_CASES_TAC >> gvs[]
    )
  >- simp[l3_models_asl_BranchRegister_JMP] (* JumpReg *)
  >- ( (* Loc *)
    rw[] >> simp[l3_models_asl_MoveWideOp_K]
    >- simp[l3_models_asl_Address |> SIMP_RULE std_ss [LET_DEF]]
    >- simp[l3_models_asl_Address |> SIMP_RULE std_ss [LET_DEF]]
    >- simp[l3_models_asl_AddSubShiftedRegister]
    )
QED

val _ = export_theory();
