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

val _ = numLib.prefer_num();

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

Definition read_rel_def:
  read_rel rel l3 asl asl_reg ⇔
    rel l3 (asl_reg.read_from asl)
End

Definition reg_rel_def:
  reg_rel (l3 : word5 -> word64) (asl : regstate) ⇔
    l3 (n2w 31) = 0w ∧
    LENGTH (R_ref.read_from asl) = 32 ∧
    ∀n. n ≤ 31 ⇒ l3 (n2w n) = EL n (R_ref.read_from asl)
End

Definition mem_rel_def:
  mem_rel (l3 : word64 -> word8) (asl : num |-> bitU list) tags =
    ∀n. FLOOKUP tags n = SOME B0
      ⇒ ∃byt.
          FLOOKUP asl n = SOME byt ∧
          l3 (n2w n) = vec_of_bits byt
End

(* what to do about tagstate? *)
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
    reg_rel l3.REG asl.regstate ∧
    mem_rel l3.MEM asl.memstate asl.tagstate ∧
    l3.exception = NoException
End

Definition l3_models_asl_def:
  l3_models_asl opcode ⇔
    Decode opcode ≠ Unallocated ∧
    ∀ l3 asl l3'.
      state_rel l3 asl ∧
      Run (Decode opcode) l3 = l3' ∧
      l3'.exception = NoException
    ⇒ case seqS (write_regS SEE_ref (~1)) (ExecuteA64 opcode) asl of
        | (Value _, asl') => state_rel l3' asl'
        | _ => F
End

Definition l3_models_asl_instr_def:
  l3_models_asl_instr instr ⇔
    case Encode instr of
      | ARM8 opcode => l3_models_asl opcode
      | _ => F
End

val _ = export_theory();

