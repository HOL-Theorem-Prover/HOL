(* ========================================================================= *)
(* FILE          : arm_evalScript.sml                                        *)
(* DESCRIPTION   : I/O and exception free model of the ARM ISA               *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005                                                      *)
(* ========================================================================= *)

(* interactive use:
  app load ["rich_listTheory", "wordsLib", "simTheory",
            "armLib", "lemmasTheory"];
*)

open HolKernel boolLib Parse bossLib;
open Q rich_listTheory wordsLib onestepTheory armTheory lemmasTheory;

val _ = new_theory "arm_eval";

(* ------------------------------------------------------------------------- *)
(* The State Space --------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

val _ = mk_word_size 30;

val _ = type_abbrev("mem", ``:word30->word32``);

val _ = Hol_datatype
 `state_arme = <| registers : reg; psrs : psr;
                  memory : mem; undefined : bool |>`;

(* ------------------------------------------------------------------------- *)

val ADDR30_def = Define `ADDR30 (addr:word32) = (31 >< 2) addr:word30`;

val SET_BYTE_def = Define`
  SET_BYTE (oareg:word2) (b:word8) (w:word32) =
    word_modify (\i x.
                  (i < 8) /\ (if oareg = 0w then b %% i else x) \/
       (8 <= i /\ i < 16) /\ (if oareg = 1w then b %% (i - 8) else x) \/
      (16 <= i /\ i < 24) /\ (if oareg = 2w then b %% (i - 16) else x) \/
      (24 <= i /\ i < 32) /\ (if oareg = 3w then b %% (i - 24) else x)) w`;

val MEM_WRITE_BYTE_def = Define`
  MEM_WRITE_BYTE (mem:mem) addr (word:word32) =
    let addr30 = ADDR30 addr in
      (addr30 :- SET_BYTE ((1 >< 0) addr) ((7 >< 0) word) (mem addr30)) mem`;

val MEM_WRITE_WORD_def = Define`
  MEM_WRITE_WORD (mem:mem) addr word = (ADDR30 addr :- word) mem`;

val MEM_WRITE_def = Define`
  MEM_WRITE b = if b then MEM_WRITE_BYTE else MEM_WRITE_WORD`;

val TRANSFERS_def = Define`
  (TRANSFERS mem data [] = (mem,data)) /\
  (TRANSFERS mem data (r::rs) =
   case r of
      MemRead addr -> TRANSFERS mem (SNOC (mem (ADDR30 addr)) data) rs
   || MemWrite b addr word -> TRANSFERS (MEM_WRITE b mem addr word) data rs
   || _ -> TRANSFERS mem data rs)`;

val NEXT_ARMe_def = Define`
  NEXT_ARMe state =
    let pc = FETCH_PC state.registers in
    let ireg = state.memory (ADDR30 pc) in
    let s = ARM_EX (ARM state.registers state.psrs) ireg
              (if state.undefined then undefined else software) in
    let mrqs = OUT_ARM s in
    let (next_mem,data) = TRANSFERS state.memory [] mrqs
    and (flags,i,f,m) = DECODE_PSR (CPSR_READ state.psrs)
    in case EXEC_INST s NONE data T of
      ARM reg psr -> 
         <| registers := reg; psrs := psr; memory := next_mem;
           undefined := (~state.undefined /\ CONDITION_PASSED flags ireg /\
            DECODE_INST ireg IN {cdp_und; mrc; mcr; stc; ldc}) |>`;

val STATE_ARMe_def = Define`
  (STATE_ARMe 0 s = s) /\
  (STATE_ARMe (SUC t) s = NEXT_ARMe (STATE_ARMe t s))`;

(* ------------------------------------------------------------------------- *)

infix \\ << >>

val op \\ = op THEN;
val op << = op THENL;
val op >> = op THEN1;

val STATE_ARMe_THM = store_thm("STATE_ARMe_THM",
  `IMAP STATE_ARMe I NEXT_ARMe`,
  RW_TAC (std_ss++boolSimps.LET_ss)
    [STATE_ARMe_def,IMAP_def,combinTheory.I_THM]);

val Sa_RULE_WORD = store_thm("Sa_RULE_WORD",
  `!m a b d e. Sa a e (Sa b d m) =
     if a <+ b then
       Sb b d (Sa a e m)
     else
       Sb a e (Sa b d m)`,
  METIS_TAC [simTheory.Sa_def,simTheory.Sb_def,SUBST_COMMUTES]);

val Sb_RULE_WORD = store_thm("Sb_RULE_WORD",
  `!m a b d e. Sa a e (Sb b d m) =
     if a <+ b then
       Sb b d (Sa a e m)
     else
       Sb a e (Sb b d m)`,
  METIS_TAC [simTheory.Sa_def,simTheory.Sb_def,SUBST_COMMUTES]);

val SUBST_EQ2 = store_thm("SUBST_EQ2",
  `!m a v. (m a = v) ==> ((a :- v) m = m)`,
  REPEAT STRIP_TAC \\ REWRITE_TAC [FUN_EQ_THM] \\ RW_TAC std_ss [SUBST_def]);

(* ------------------------------------------------------------------------- *)

val ABS_ARMe_def = Define`
  ABS_ARMe state  =
     ARM_EX (ARM state.registers state.psrs)
       (state.memory (ADDR30 (FETCH_PC state.registers)))
       (if state.undefined then undefined else software)`;

val ABS_STRMe_def = Define`
  ABS_STRMe a t =
    let s0 = STATE_ARMe t a and s1 = STATE_ARMe (SUC t) a in
      (if s1.undefined then SOME Undef else NONE, T,
       s1.memory (ADDR30 (FETCH_PC s1.registers)),
       SND (TRANSFERS s0.memory [] (OUT_ARM (ABS_ARMe s0))))`;

(*
val trans = GEN_ALL o SIMP_CONV (srw_ss()) [SNOC,HD,TRANSFERS_def]
val TRANSFER_LDR = trans ``TRANSFERS mem [] [MemRead a]``
val TRANSFER_STR = trans ``TRANSFERS mem [] [MemWrite B a d]``
val TRANSFER_SWP = trans ``TRANSFERS mem [] [MemRead a; MemWrite B a2 d]``
val alu_nchotomy = METIS_PROVE [pairTheory.ABS_PAIR_THM]
  ``!a. ?n z c v r. (a:(bool # bool # bool # bool) # word32) = ((n,z,c,v),r)``;

fun Cases_on_alu tm = SPEC_THEN tm FULL_STRUCT_CASES_TAC alu_nchotomy;

val ARMe_CORRECT = Count.apply store_thm("ARMe_CORRECT",
  `!t a. ABS_ARMe (STATE_ARMe t a) =
         STATE_ARM t <| state := ABS_ARMe a; inp := ABS_STRMe a |>`,
  Induct \\ STRIP_TAC \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss)
         [STATE_ARM_def,STATE_ARMe_def,ABS_STRMe_def]
    \\ POP_ASSUM (SUBST1_TAC o SYM o SPEC `a`)
    \\ ABBREV_TAC `s = STATE_ARMe t a`
    \\ ABBREV_TAC `ns = NEXT_ARMe s` \\ POP_ASSUM MP_TAC
    \\ ABBREV_TAC `ireg = s.memory (ADDR30 (FETCH_PC s.registers))`
    \\ ABBREV_TAC `mode = DECODE_MODE ((4 >< 0) (CPSR_READ s.psrs))`
    \\ SIMP_TAC (srw_ss()++armLib.PBETA_ss++boolSimps.LET_ss)
         [IS_Reset_def,IS_Dabort_def,ABS_ARMe_def,OUT_ARM_def,DECODE_PSR_def,
          NEXT_ARMe_def,NEXT_ARM_def]
    \\ Cases_on `s.undefined`
    \\ ASM_SIMP_TAC (srw_ss()) [CONJUNCT1 TRANSFERS_def]
    << [
      SIMP_TAC (srw_ss()++boolSimps.LET_ss++armLib.PBETA_ss)
             [EXEC_INST_def,EXCEPTION_def]
        \\ STRIP_TAC \\ UNABBREV_TAC `ns`
        \\ SIMP_TAC (srw_ss()++boolSimps.LET_ss++armLib.PBETA_ss)
             [PROJ_IF_FLAGS_def,interrupt2exception_def],
       Tactical.REVERSE
        (Cases_on `CONDITION_PASSED (NZCV (CPSR_READ s.psrs)) ireg`)
        \\ ASM_SIMP_TAC (srw_ss()) [CONJUNCT1 TRANSFERS_def]
        << [
          ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss++armLib.PBETA_ss)
                 [EXEC_INST_def,DECODE_PSR_def]
            \\ STRIP_TAC \\ UNABBREV_TAC `ns`
            \\ SIMP_TAC (srw_ss()++boolSimps.LET_ss++armLib.PBETA_ss)
                 [PROJ_IF_FLAGS_def,interrupt2exception_def],
          Cases_on `DECODE_INST ireg`
            \\ MAP_EVERY IMP_RES_TAC [DECODE_INST_LDM,DECODE_INST_STM]
            \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss++armLib.PBETA_ss)
              [EXEC_INST_def,NEXT_ARM_def,EXCEPTION_def,PROJ_IF_FLAGS_def,
               IS_Reset_def,IS_Dabort_def,DECODE_PSR_def,
               TRANSFER_LDR,TRANSFER_STR,TRANSFER_SWP,
               LDM_STM_def,DECODE_LDM_STM_def,ADDR_MODE4_def,
               LDR_STR_def,DECODE_LDR_STR_def,ADDR_MODE2_def,
               SWP_def,DECODE_SWP_def,MLA_MUL_def,DECODE_MLA_MUL_def,
               MRS_def,DECODE_MRS_def,MSR_def,DECODE_MSR_def,
               DATA_PROCESSING_def,ADDR_MODE1_def,
               BRANCH_def,DECODE_BRANCH_def]
            \\ TRY (PAT_ABBREV_TAC `alu = ALU opc rn op2 c` \\
                    Cases_on_alu `alu`)
            \\ STRIP_TAC \\ UNABBREV_TAC `ns`
            \\ RW_TAC (srw_ss()++boolSimps.LET_ss++armLib.PBETA_ss)
                 [PROJ_IF_FLAGS_def,DECODE_PSR_def,interrupt2exception_def]
            \\ FULL_SIMP_TAC (srw_ss()) []]]);
*)

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
