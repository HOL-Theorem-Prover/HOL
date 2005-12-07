(* ========================================================================= *)
(* FILE          : arm_evalScript.sml                                        *)
(* DESCRIPTION   : I/O and exception free model of the ARM ISA               *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2005                                                      *)
(* ========================================================================= *)

(* interactive use:
  app load ["wordsLib", "armTheory", "simTheory"];
*)

open HolKernel boolLib Parse bossLib;
open Q wordsLib onestepTheory armTheory;

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
    in
      ARM_EVAL ns str_mem (DECODE_INST ireg IN {cdp_und; mrc; mcr; stc; ldc})`;

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

val _ = export_theory();
