Theory riscv_prog
Ancestors
  set_sep prog riscv_step temporal_state
Libs
  stateLib

val _ = ParseExtras.temp_loose_equality()
(* ------------------------------------------------------------------------ *)

val _ = stateLib.sep_definitions "riscv" []
          (List.map Lib.list_of_singleton
             ["c_update", "log", "totalCore", "done", "clock", "c_tlb",
              "c_instret", "c_cycles", "c_UCSR", "c_SCSR", "c_ReserveLoad",
              "c_HCSR", "c_ExitCode"])
          riscv_stepTheory.NextRISCV_def

Definition riscv_mem_def:
   riscv_mem a (l: word8 list) =
   set (GENLIST (\i. (riscv_c_MEM8 (a + n2w i),
                      riscv_d_word8 (EL i l))) (LENGTH l))
End

Definition riscv_instr_def:
  riscv_instr (a, i) = riscv_mem a i
End

val riscv_proj_def = DB.definition "riscv_proj_def"

Definition RISCV_MODEL_def:
  RISCV_MODEL =
    (STATE riscv_proj, NEXT_REL (=) NextRISCV, riscv_instr,
     ($= :riscv_state -> riscv_state -> bool), K F : riscv_state -> bool)
End

val RISCV_IMP_SPEC = Theory.save_thm ("RISCV_IMP_SPEC",
  stateTheory.IMP_SPEC
  |> Q.ISPECL [`riscv_proj`, `NextRISCV`, `riscv_instr`]
  |> REWRITE_RULE [GSYM RISCV_MODEL_def]
  )

val RISCV_IMP_TEMPORAL = Theory.save_thm ("RISCV_IMP_TEMPORAL",
  temporal_stateTheory.IMP_TEMPORAL
  |> Q.ISPECL [`riscv_proj`, `NextRISCV`, `riscv_instr`,
               `(=) : riscv_state -> riscv_state -> bool`,
               `K F : riscv_state -> bool`]
  |> REWRITE_RULE [GSYM RISCV_MODEL_def]
  )

(* ------------------------------------------------------------------------ *)

Definition riscv_ID_def:
   riscv_ID id mcsr =
   riscv_exception NoException * riscv_procID id * riscv_c_NextFetch id NONE *
   riscv_c_MCSR id mcsr * cond (mcsr.mstatus.VM = 0w)
End

Definition riscv_ID_PC_def:
  riscv_ID_PC id pc = riscv_c_PC id pc * cond (aligned 1 pc) * ~ riscv_c_Skip id
End

(* ------------------------------------------------------------------------
   Specialize to RV64I, core 0
   ------------------------------------------------------------------------ *)

Definition riscv_RV64I_def:
  riscv_RV64I mcsr = cond (mcsr.mcpuid.ArchBase = 2w) * riscv_ID 0w mcsr
End

Definition riscv_REG_def:  riscv_REG  = riscv_c_gpr 0w
End
Definition riscv_PC_def:  riscv_PC = riscv_ID_PC 0w
End

(* ------------------------------------------------------------------------ *)

val aligned_1_intro = store_thm("aligned_1_intro",
  ``~word_bit 0 pc <=> aligned 1 (pc:word64)``,
  fs [alignmentTheory.aligned_bitwise_and] \\ blastLib.BBLAST_TAC);

Theorem RISCV_PC_INTRO:
    SPEC m (p1 * riscv_ID_PC c pc) code
           (p2 * riscv_c_PC c pc' * ~ riscv_c_Skip c) ==>
    (aligned 1 pc ==> aligned 1 pc') ==>
    SPEC m (p1 * riscv_ID_PC c pc) code (p2 * riscv_ID_PC c pc')
Proof
   REPEAT STRIP_TAC
   \\ FULL_SIMP_TAC (std_ss++helperLib.sep_cond_ss)
        [riscv_ID_PC_def, SPEC_MOVE_COND, STAR_ASSOC, SEP_CLAUSES]
QED

Theorem RISCV_TEMPORAL_PC_INTRO:
    TEMPORAL_NEXT m (p1 * riscv_ID_PC c pc) code
                    (p2 * riscv_c_PC c pc' * ~ riscv_c_Skip c) ==>
    (aligned 1 pc ==> aligned 1 pc') ==>
    TEMPORAL_NEXT m (p1 * riscv_ID_PC c pc) code (p2 * riscv_ID_PC c pc')
Proof
   REPEAT STRIP_TAC
   \\ FULL_SIMP_TAC (std_ss++helperLib.sep_cond_ss)
        [riscv_ID_PC_def, temporal_stateTheory.TEMPORAL_NEXT_MOVE_COND,
         STAR_ASSOC, SEP_CLAUSES]
QED

Theorem cond_branch_aligned:
   ((aligned 1 (pc: word64) ==>
     aligned 1 (if b then pc + w << 1 else pc + 4w)) = T) /\
   ((aligned 1 (pc: word64) ==>
     aligned 1 (if b then pc + w << 1 else pc + 2w)) = T)
Proof
  rw [alignmentTheory.aligned_extract]
  \\ blastLib.FULL_BBLAST_TAC
QED

Theorem jal_aligned:
   (aligned 1 (pc: word64) ==> aligned 1 (pc + w << 1)) = T
Proof
  rw [alignmentTheory.aligned_extract] \\ pop_assum mp_tac
  \\ blastLib.BBLAST_TAC
QED

Theorem jalr_aligned:
   ~(a: word12) ' 1 /\ (b \/ aligned 1 (v: word64)) /\
   (c ==> aligned 1 (if b then sw2sw a && 0xFFFFFFFFFFFFFFFEw
                     else v + sw2sw a && 0xFFFFFFFFFFFFFFFEw)) =
   ~(a: word12) ' 1 /\ (b \/ aligned 1 (v: word64))
Proof
  rw [alignmentTheory.aligned_extract]
  \\ blastLib.FULL_BBLAST_TAC
QED

(* ------------------------------------------------------------------------ *)

val riscv_MEM8_def = fetch "-" "riscv_MEM8_def";

val (riscv_MEMORY_def, riscv_MEMORY_INSERT) =
   stateLib.define_map_component ("riscv_MEMORY", "mem", riscv_MEM8_def)

(* ------------------------------------------------------------------------ *)

Theorem c_gpr_frame:
   !c_gpr a b w s x.
     riscv_c_c_gpr a b IN x ==>
     (FRAME_STATE riscv_proj x
         (s with c_gpr := (a =+ (b =+ w) (c_gpr a)) c_gpr) =
      FRAME_STATE riscv_proj x (s with c_gpr := c_gpr))
Proof
  rw [stateTheory.FRAME_STATE_def, stateTheory.SELECT_STATE_def,
      set_sepTheory.fun2set_def, pred_setTheory.EXTENSION]
  \\ eq_tac
  \\ rw []
  \\ Cases_on `a'`
  \\ rw [combinTheory.APPLY_UPDATE_THM, riscv_proj_def]
  \\ Cases_on `b = c0`
  \\ fs []
QED

(* ------------------------------------------------------------------------ *)

val riscv_opcode_bytes = Theory.save_thm("riscv_opcode_bytes",
   blastLib.BBLAST_PROVE
    ``(d @@ ((c @@ ((b @@ a) : word16)) : word24) = r: word32) =
      (a = ( 7 ><  0) r : word8) /\
      (b = (15 ><  8) r : word8) /\
      (c = (23 >< 16) r : word8) /\
      (d = (31 >< 24) r : word8)``)
