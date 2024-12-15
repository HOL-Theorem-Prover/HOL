open HolKernel boolLib bossLib Parse
open armv86aTheory armv86a_terminationTheory armv86a_typesTheory
open arm8Theory arm8Lib arm8_stepTheory arm8_stepLib
open wordsTheory bitstringTheory finite_mapTheory listTheory
     arithmeticTheory integerTheory
open wordsLib optionLib combinLib

val _ = new_theory "l3_equivalence";
val _ = set_grammar_ancestry ["arm8_step", "arm8", "armv86a_termination"];

val _ = wordsLib.output_words_as_bin();
val _ = wordsLib.guess_lengths();

val _ = numLib.temp_prefer_num();

(******************************************************************************)

Definition flag_rel_def:
  flag_rel b (w : 1 word) ⇔ (w = v2w [b])
End

Definition pstate_rel_def:
  pstate_rel (l3 : arm8$ProcState) (asl : armv86a_types$ProcState) ⇔
    l3.EL = asl.ProcState_EL ∧
    flag_rel l3.SPS asl.ProcState_SP ∧
    flag_rel l3.N asl.ProcState_N ∧
    flag_rel l3.Z asl.ProcState_Z ∧
    flag_rel l3.C asl.ProcState_C ∧
    flag_rel l3.V asl.ProcState_V
End

Definition tcr_el1_rel_def:
  tcr_el1_rel (l3 : TCR_EL1) (asl : 64 word) ⇔
    reg'TCR_EL1 l3 = asl
End

(* L3 TCR_EL2 is 32-bits, though 64-bit with upper 32 bits clear in spec *)
Definition tcr_el2_3_rel_def:
  tcr_el2_3_rel (l3 : TCR_EL2_EL3) asl ⇔
    reg'TCR_EL2_EL3 l3 = (31 >< 0) asl
End

(* XXX version difference here - L3 SCTLRs are only 32-bit *)
Definition sctlr_rel_def:
  sctlr_rel (l3 : arm8$SCTLRType) (asl : 64 word) ⇔
    reg'SCTLRType l3 = (31 >< 0) asl
End

Definition branch_hint_rel_def:
  branch_hint_rel (l3 : arm8$BranchType option) (asl : bool) ⇔
    asl = IS_SOME l3
End

Definition read_rel_def:
  read_rel rel l3 asl asl_reg ⇔
    rel l3 (asl_reg.read_from asl)
End

Definition reg_rel_def:
  reg_rel (l3 : word5 -> word64) (asl : regstate) ⇔
    LENGTH (R_ref.read_from asl) = 32 ∧
    ∀n. n ≤ 31 ⇒ l3 (n2w n) = EL n (R_ref.read_from asl)
End

Definition mem_rel_def:
  mem_rel (l3 : word64 -> word8) (asl : num |-> bitU list) tags =
    ∀w.
      FLOOKUP tags (w2n w) = SOME B0 ∧
      ∃byt.
        FLOOKUP asl (w2n w) = SOME (MAP bitU_of_bool byt) ∧
        LENGTH byt = 8 ∧
        l3 w = v2w byt
End

Theorem mem_rel:
  mem_rel (l3 : word64 -> word8) (asl : num |-> bitU list) tags =
    ∀w.
      FLOOKUP tags (w2n w) = SOME B0 ∧
      FLOOKUP asl (w2n w) = SOME $ MAP bitU_of_bool $ w2v (l3 w)
Proof
  rw[mem_rel_def] >> eq_tac >> rw[]
  >- (first_x_assum $ qspec_then `w` assume_tac >> gvs[w2v_v2w])
  >- (irule_at Any EQ_REFL >> simp[])
QED

Definition state_rel_def:
  state_rel (l3 : arm8_state) (asl : regstate sequential_state) ⇔
    read_rel pstate_rel l3.PSTATE asl.regstate PSTATE_ref ∧
    read_rel sctlr_rel l3.SCTLR_EL1 asl.regstate SCTLR_EL1_ref ∧
    read_rel sctlr_rel l3.SCTLR_EL2 asl.regstate SCTLR_EL2_ref ∧
    read_rel sctlr_rel l3.SCTLR_EL3 asl.regstate SCTLR_EL3_ref ∧
    read_rel ($=) l3.PC asl.regstate PC_ref ∧
    read_rel ($=) l3.SP_EL0 asl.regstate SP_EL0_ref ∧
    read_rel ($=) l3.SP_EL1 asl.regstate SP_EL1_ref ∧
    read_rel ($=) l3.SP_EL2 asl.regstate SP_EL2_ref ∧
    read_rel ($=) l3.SP_EL3 asl.regstate SP_EL3_ref ∧
    read_rel tcr_el1_rel l3.TCR_EL1 asl.regstate TCR_EL1_ref ∧
    read_rel tcr_el2_3_rel l3.TCR_EL2 asl.regstate TCR_EL2_ref ∧
    read_rel tcr_el2_3_rel l3.TCR_EL3 asl.regstate TCR_EL3_ref ∧
    read_rel branch_hint_rel l3.branch_hint asl.regstate BranchTaken_ref ∧
    reg_rel l3.REG asl.regstate ∧
    mem_rel l3.MEM asl.memstate asl.tagstate ∧
    l3.exception = NoException
End

Definition asl_sys_regs_ok_def:
  asl_sys_regs_ok asl ⇔

    ¬ asl.regstate.bool_reg "__highest_el_aarch32" ∧
    (asl.regstate.ProcState_reg "PSTATE").ProcState_nRW = 0b0w ∧

    (let SCR_EL3 = asl.regstate.bitvector_64_dec_reg "SCR_EL3" in
     word_bit 0 SCR_EL3 (* ELs below 3 are non-secure *) ∧
     word_bit 10 SCR_EL3 (* RW bit - ELs below 3 are not AArch32 *) ∧
     ¬word_bit 18 SCR_EL3 (* Secure EL2 disabled *)) ∧

    (let HCR_EL2 = asl.regstate.bitvector_64_dec_reg "HCR_EL2" in
      word_bit 31 HCR_EL2 (* RW bit - EL1 is AArch64 *) ∧
      ¬word_bit 34 HCR_EL2 (* Virtualization Host Extension (FEAT_VHE) disabled *)) ∧

    asl.regstate.bitvector_64_dec_reg "__CNTControlBase" = 0b0w ∧
    word_bit 4 ((asl.regstate.ProcState_reg "PSTATE").ProcState_M) ∧

    (let TCR_EL1 = asl.regstate.bitvector_64_dec_reg "TCR_EL1" in
      ¬word_bit 51 TCR_EL1 ∧ ¬word_bit 52 TCR_EL1) ∧

    (let TCR_EL2 = asl.regstate.bitvector_64_dec_reg "TCR_EL2" in
      ¬word_bit 29 TCR_EL2) ∧

    (let TCR_EL3 = asl.regstate.bitvector_32_dec_reg "TCR_EL3" in
      ¬word_bit 29 TCR_EL3)
End

Definition l3_models_asl_def:
  l3_models_asl opcode ⇔
    Decode opcode ≠ Unallocated ∧
    ∀ l3 asl l3'.
      state_rel l3 asl ∧ asl_sys_regs_ok asl ∧
      Run (Decode opcode) l3 = l3' ∧
      l3'.exception = NoException
    ⇒ case seqS (write_regS SEE_ref (~1)) (ExecuteA64 opcode) asl of
        | (Value _, asl') => state_rel l3' asl' ∧ asl_sys_regs_ok asl'
        | _ => F
End

Definition l3_models_asl_instr_def:
  l3_models_asl_instr instr ⇔
    case Encode instr of
      | ARM8 opcode => l3_models_asl opcode
      | _ => F
End

val _ = export_theory();

