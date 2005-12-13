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

val _ = mk_word_type 30;

val _ = type_abbrev("mem", ``:word30->word32``);

val _ = Hol_datatype `state_arme = ARM_EVAL of state_arm=>mem=>bool`;

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
  MEM_WRITE_BYTE (mem:mem) (word:word32) addr =
    let addr30 = ADDR30 addr in
      (addr30 :- SET_BYTE ((1 >< 0) addr) ((7 >< 0) word) (mem addr30)) mem`;

val MEM_WRITE_WORD_def = Define`
  MEM_WRITE_WORD (mem:mem) word addr = (ADDR30 addr :- word) mem`;

val MEM_WRITE_def = Define`
  MEM_WRITE b = if b then MEM_WRITE_BYTE else MEM_WRITE_WORD`;

val TRANSFERS_def = Define`
  (TRANSFERS mem data [] = (mem,data)) /\
  (TRANSFERS mem data (r::rs) =
   case r of
      MemRead addr -> TRANSFERS mem (SNOC (mem (ADDR30 addr)) data) rs
   || MemWrite B addr word -> TRANSFERS (MEM_WRITE B mem word addr) data rs
   || _ -> TRANSFERS mem data rs)`;

val NEXT_ARMe_def = Define`
  NEXT_ARMe (ARM_EVAL (ARM reg psr) mem undef) =
    let pc = FETCH_PC reg in
    let ireg = mem (ADDR30 pc) in
    let s = ARM_EX (ARM reg psr) ireg (if undef then undefined else software) in
    let mrqs = OUT_ARM s in
    let (str_mem,data) = TRANSFERS mem [] mrqs in
    let ns = EXEC_INST s NONE data T
    and (flags,i,f,m) = DECODE_PSR (CPSR_READ psr)
    in
      ARM_EVAL ns str_mem
        (~undef /\ CONDITION_PASSED flags ireg /\
         DECODE_INST ireg IN {cdp_und; mrc; mcr; stc; ldc})`;

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

(*
val ABS_ARMe_def = Define`
  ABS_ARMe (ARM_EVAL s mem undef) =
    case s of
      ARM reg psrs ->
        ARM_EX s (mem (ADDR30 (FETCH_PC reg)))
          (if undef then undefined else software)`;

val ABS_STRMe_def = Define`
  ABS_STRMe a t =
    case (STATE_ARMe t a, STATE_ARMe (SUC t) a) of
      (ARM_EVAL (ARM reg0 psr0) mem0 undef0,
       ARM_EVAL (ARM reg1 psr1) mem1 undef1) ->
        (if undef1 then SOME Undef else NONE, T, mem1 (ADDR30 (FETCH_PC reg1)),
         SND (TRANSFERS mem0 [] (OUT_ARM (ABS_ARMe (STATE_ARMe t a)))))`;

local
  val trans = GEN_ALL o SIMP_CONV (srw_ss()) [SNOC,HD,TRANSFERS_def]
  val TRANSFER_LDR = trans ``TRANSFERS mem [] [MemRead a]``
  val TRANSFER_STR = trans ``TRANSFERS mem [] [MemWrite B a d]``
  val TRANSFER_SWP = trans ``TRANSFERS mem [] [MemRead a; MemWrite B a2 d]``
in
  val ARMe_CORRECT_TAC =
    RW_TAC (srw_ss()++boolSimps.LET_ss++armLib.PBETA_ss)
      [EXEC_INST_def,NEXT_ARM_def,EXCEPTION_def,PROJ_IF_FLAGS_def,
       IS_Reset_def,IS_Dabort_def,DECODE_PSR_def,interrupt2exception_def,
       TRANSFER_LDR,TRANSFER_STR,TRANSFER_SWP,
       LDM_STM_def,DECODE_LDM_STM_def,ADDR_MODE4_def,
       LDR_STR_def,DECODE_LDR_STR_def,ADDR_MODE2_def,
       SWP_def,DECODE_SWP_def,MLA_MUL_def,DECODE_MLA_MUL_def,
       MRS_def,DECODE_MRS_def,MSR_def,DECODE_MSR_def,
       DATA_PROCESSING_def,ADDR_MODE1_def,BRANCH_def,DECODE_BRANCH_def]
      \\ FULL_SIMP_TAC std_ss [];
end;

val alu_nchotomy = METIS_PROVE [pairTheory.ABS_PAIR_THM]
  ``!a. ?n z c v r. (a:(bool # bool # bool # bool) # word32) = ((n,z,c,v),r)``;

fun Cases_on_alu tm = SPEC_THEN tm FULL_STRUCT_CASES_TAC alu_nchotomy;

val ARMe_CORRECT = Count.apply store_thm("ARMe_CORRECT",
  `!t a. ABS_ARMe (STATE_ARMe t a) =
         STATE_ARM t <| state := ABS_ARMe a; inp := ABS_STRMe a |>`,
  Induct \\ STRIP_TAC \\ ASM_SIMP_TAC (srw_ss()++boolSimps.LET_ss)
         [STATE_ARM_def,STATE_ARMe_def,ABS_STRMe_def]
    \\ POP_ASSUM (SUBST1_TAC o SYM o SPEC `a`)
    \\ Cases_on `STATE_ARMe t a` \\ Cases_on `s`
    \\ RW_TAC (std_ss++armLib.PBETA_ss++boolSimps.LET_ss)
         [IS_Reset_def,IS_Dabort_def,ABS_ARMe_def,OUT_ARM_def,DECODE_PSR_def,
          NEXT_ARMe_def,NEXT_ARM_def,CONJUNCT1 TRANSFERS_def]
    \\ NTAC 2 (FULL_SIMP_TAC (srw_ss()) [])
    \\ MAP_EVERY IMP_RES_TAC [DECODE_INST_LDM,DECODE_INST_STM]
    \\ ARMe_CORRECT_TAC
    \\ TRY (PAT_ABBREV_TAC `alu = ALU opc rn op2 c` \\ Cases_on_alu `alu`)
    \\ ARMe_CORRECT_TAC);
*)

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
