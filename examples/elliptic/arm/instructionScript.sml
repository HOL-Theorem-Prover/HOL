(* ========================================================================= *)
(* FILE          : instructionScript.sml                                     *)
(* DESCRIPTION   : Datatype for ARM instructions, and an encoder -> word32   *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2006                                                      *)
(* ========================================================================= *)

(* interactive use:
  app load ["wordsTheory", "armTheory"];
*)

open HolKernel boolLib Parse bossLib;
open Q wordsTheory armTheory;

val _ = new_theory "instruction";

(* ------------------------------------------------------------------------- *)

val _ = Hol_datatype`
  shift =
    LSL of word4
  | LSR of word4
  | ASR of word4
  | ROR of word4`;

val _ = Hol_datatype
  `addr_mode1 =
     Dp_immediate of word4=>word8
   | Dp_shift_immediate of shift=>word5
   | Dp_shift_register of shift=>word4`;

val _ = Hol_datatype
  `addr_mode2 =
     Dt_immediate of word12
   | Dt_shift_immediate of shift=>word5`;

val _ = Hol_datatype
  `msr_mode =
     Msr_immediate of word4=>word8
   | Msr_register of word4`;

val _ = Hol_datatype
  `msr_psr = CPSR_c | CPSR_f | CPSR_a | SPSR_c | SPSR_f | SPSR_a`;

val _ = Hol_datatype
  `transfer_options = <| Pre : bool; Up : bool; BSN :bool; Wb : bool |>`;

val _ = Hol_datatype
 `arm_instruction =
    B of condition=>word24
  | BL of condition=>word24
  | SWI of condition
  | AND of condition=>bool=>word4=>word4=>addr_mode1
  | EOR of condition=>bool=>word4=>word4=>addr_mode1
  | SUB of condition=>bool=>word4=>word4=>addr_mode1
  | RSB of condition=>bool=>word4=>word4=>addr_mode1
  | ADD of condition=>bool=>word4=>word4=>addr_mode1
  | ADC of condition=>bool=>word4=>word4=>addr_mode1
  | SBC of condition=>bool=>word4=>word4=>addr_mode1
  | RSC of condition=>bool=>word4=>word4=>addr_mode1
  | TST of condition=>word4=>addr_mode1
  | TEQ of condition=>word4=>addr_mode1
  | CMP of condition=>word4=>addr_mode1
  | CMN of condition=>word4=>addr_mode1
  | ORR of condition=>bool=>word4=>word4=>addr_mode1
  | MOV of condition=>bool=>word4=>addr_mode1
  | BIC of condition=>bool=>word4=>word4=>addr_mode1
  | MVN of condition=>bool=>word4=>addr_mode1
  | MUL of condition=>bool=>word4=>word4=>word4
  | MLA of condition=>bool=>word4=>word4=>word4=>word4
  | UMULL of condition=>bool=>word4=>word4=>word4=>word4
  | UMLAL of condition=>bool=>word4=>word4=>word4=>word4
  | SMULL of condition=>bool=>word4=>word4=>word4=>word4
  | SMLAL of condition=>bool=>word4=>word4=>word4=>word4
  | LDR of condition=>transfer_options=>word4=>word4=>addr_mode2
  | STR of condition=>transfer_options=>word4=>word4=>addr_mode2
  | LDM of condition=>transfer_options=>word4=>word16
  | STM of condition=>transfer_options=>word4=>word16
  | SWP of condition=>bool=>word4=>word4=>word4
  | MRS of condition=>bool=>word4
  | MSR of condition=>msr_psr=>msr_mode
  | CDP of condition=>word4=>word4=>word4=>word4=>word4=>word3
  | LDC of condition=>transfer_options=>word4=>word4=>word4=>word8
  | STC of condition=>transfer_options=>word4=>word4=>word4=>word8
  | MRC of condition=>word4=>word3=>word4=>word4=>word4=>word3
  | MCR of condition=>word4=>word3=>word4=>word4=>word4=>word3
  | UND of condition`;

(* ------------------------------------------------------------------------- *)

val condition_encode_def = Define`
  condition_encode cond =
    (w2w (n2w (condition2num cond):word4 #<< 1) << 28):word32`;

val shift_encode_def = Define`
  (shift_encode (LSL Rm) = (w2w Rm):word32) /\
  (shift_encode (LSR Rm) = 0x20w !! w2w Rm) /\
  (shift_encode (ASR Rm) = 0x40w !! w2w Rm) /\
  (shift_encode (ROR Rm) = 0x60w !! w2w Rm)`;

val addr_mode1_encode_def = Define`
  addr_mode1_encode op2 =
   case op2 of
      Dp_immediate rot imm -> (0x2000000w !! w2w rot << 8 !! w2w imm):word32
   || Dp_shift_immediate shift amount -> w2w amount << 7 !! shift_encode shift
   || Dp_shift_register shift Rs -> 0x10w !! w2w Rs << 8 !! shift_encode shift`;

val addr_mode2_encode_def = Define`
  addr_mode2_encode op2 =
   case op2 of
      Dt_immediate imm -> (w2w imm):word32
   || Dt_shift_immediate shift amount ->
        0x2000000w !! w2w amount << 7 !! shift_encode shift`;

val msr_mode_encode_def = Define`
  msr_mode_encode op =
   case op of
      Msr_immediate rot imm -> (0x2000000w !! w2w rot << 8 !! w2w imm):word32
   || Msr_register Rm -> w2w Rm`;

val msr_psr_encode_def = Define`
  (msr_psr_encode CPSR_c = 0x10000w:word32) /\
  (msr_psr_encode CPSR_f = 0x80000w) /\
  (msr_psr_encode CPSR_a = 0x90000w) /\
  (msr_psr_encode SPSR_c = 0x410000w) /\
  (msr_psr_encode SPSR_f = 0x480000w) /\
  (msr_psr_encode SPSR_a = 0x490000w)`;

val options_encode_def = Define`
  options_encode opt =
    word_modify (\i b. (i = 24) /\ opt.Pre \/ (i = 23) /\ opt.Up \/
                       (i = 22) /\ opt.BSN \/ (i = 21) /\ opt.Wb) (0w:word32)`;

val instruction_encode_def = Define`
  instruction_encode i =
    case i of
       B  cond offset24 -> condition_encode cond !! 0xA000000w !! w2w offset24
    || BL cond offset24 -> condition_encode cond !! 0xB000000w !! w2w offset24
    || SWI cond -> condition_encode cond !! 0xF000000w
    || AND cond s Rd Rn Op2 ->
         condition_encode cond !! (s => 0x100000w | 0w) !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode1_encode Op2
    || EOR cond s Rd Rn Op2 ->
         condition_encode cond !! (s => 0x300000w | 0x200000w) !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode1_encode Op2
    || SUB cond s Rd Rn Op2 ->
         condition_encode cond !! (s => 0x500000w | 0x400000w) !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode1_encode Op2
    || RSB cond s Rd Rn Op2 ->
         condition_encode cond !! (s => 0x700000w | 0x600000w) !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode1_encode Op2
    || ADD cond s Rd Rn Op2 ->
         condition_encode cond !! (s => 0x900000w | 0x800000w) !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode1_encode Op2
    || ADC cond s Rd Rn Op2 ->
         condition_encode cond !! (s => 0xB00000w | 0xA00000w) !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode1_encode Op2
    || SBC cond s Rd Rn Op2 ->
         condition_encode cond !! (s => 0xD00000w | 0xC00000w) !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode1_encode Op2
    || RSC cond s Rd Rn Op2 ->
         condition_encode cond !! (s => 0xF00000w | 0xE00000w) !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode1_encode Op2
    || TST cond Rn Op2 ->
         condition_encode cond !! 0x1100000w !!
         w2w Rn << 16 !! addr_mode1_encode Op2
    || TEQ cond Rn Op2 ->
         condition_encode cond !! 0x1300000w !!
         w2w Rn << 16 !! addr_mode1_encode Op2
    || CMP cond Rn Op2 ->
         condition_encode cond !! 0x1500000w !!
         w2w Rn << 16 !! addr_mode1_encode Op2
    || CMN cond Rn Op2 ->
         condition_encode cond !! 0x1700000w !!
         w2w Rn << 16 !! addr_mode1_encode Op2
    || ORR cond s Rd Rn Op2 ->
         condition_encode cond !! (s => 0x1900000w | 0x1800000w) !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode1_encode Op2
    || MOV cond s Rd Op2 ->
         condition_encode cond !! (s => 0x1B00000w | 0x1A00000w) !!
         w2w Rd << 12 !! addr_mode1_encode Op2
    || BIC cond s Rd Rn Op2 ->
         condition_encode cond !! (s => 0x1D00000w | 0x1C00000w) !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode1_encode Op2
    || MVN cond s Rd Op2 ->
         condition_encode cond !! (s => 0x1F00000w | 0x1E00000w) !!
         w2w Rd << 12 !! addr_mode1_encode Op2
    || MUL cond s Rd Rm Rs ->
         condition_encode cond !! (s => 0x100090w | 0x90w) !!
         w2w Rd << 16 !! w2w Rs << 8 !! w2w Rm
    || MLA cond s Rd Rm Rs Rn ->
         condition_encode cond !! (s => 0x300090w | 0x200090w) !!
         w2w Rd << 16 !! w2w Rn << 12 !! w2w Rs << 8 !! w2w Rm
    || UMULL cond s RdHi RdLo Rm Rs ->
         condition_encode cond !! (s => 0x900090w | 0x800090w) !!
         w2w RdHi << 16 !! w2w RdLo << 12 !! w2w Rs << 8 !! w2w Rm
    || UMLAL cond s RdHi RdLo Rm Rs ->
         condition_encode cond !! (s => 0xB00090w | 0xA00090w) !!
         w2w RdHi << 16 !! w2w RdLo << 12 !! w2w Rs << 8 !! w2w Rm
    || SMULL cond s RdHi RdLo Rm Rs ->
         condition_encode cond !! (s => 0xD00090w | 0xC00090w) !!
         w2w RdHi << 16 !! w2w RdLo << 12 !! w2w Rs << 8 !! w2w Rm
    || SMLAL cond s RdHi RdLo Rm Rs ->
         condition_encode cond !! (s => 0xF00090w | 0xE00090w) !!
         w2w RdHi << 16 !! w2w RdLo << 12 !! w2w Rs << 8 !! w2w Rm
    || LDR cond options Rd Rn offset ->
         condition_encode cond !! 0x4100000w !! options_encode options !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode2_encode offset
    || STR cond options Rd Rn offset ->
         condition_encode cond !! 0x4000000w !! options_encode options !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode2_encode offset
    || LDM cond options Rn list ->
         condition_encode cond !! 0x8100000w !! options_encode options !!
         w2w Rn << 16 !! w2w list
    || STM cond options Rn list ->
         condition_encode cond !! 0x8000000w !! options_encode options !!
         w2w Rn << 16 !! w2w list
    || SWP cond byte Rd Rm Rn ->
         condition_encode cond !! (byte => 0x1400090w | 0x1000090w) !!
         w2w Rn << 16 !! w2w Rd << 12 !! w2w Rm
    || MRS cond R Rd ->
         condition_encode cond !! (R => 0x14F0000w | 0x10F0000w) !!
         w2w Rd << 12
    || MSR cond psrd Op ->
         condition_encode cond !! 0x120F000w !! msr_psr_encode psrd !!
         (msr_mode_encode Op)
    || CDP cond CPn Cop1 CRd CRn CRm Cop2 ->
         condition_encode cond !! 0xE000000w !! w2w Cop1 << 20 !!
         w2w CRn << 16 !! w2w CRd << 12 !! w2w CPn << 8 !!
         w2w Cop2 << 5 !! w2w CRm
    || LDC cond options CPn CRd Rn offset8 ->
         condition_encode cond !! 0xC100000w !! options_encode options !!
         w2w Rn << 16 !! w2w CRd << 12 !! w2w CPn << 8 !! w2w offset8
    || STC cond options CPn CRd Rn offset8 ->
         condition_encode cond !! 0xC000000w !! options_encode options !!
         w2w Rn << 16 !! w2w CRd << 12 !! w2w CPn << 8 !! w2w offset8
    || MRC cond CPn Cop1b Rd CRn CRm Cop2 ->
         condition_encode cond !! 0xE100010w !! w2w Cop1b << 21 !!
         w2w CRn << 16 !! w2w Rd << 12 !! w2w CPn << 8 !!
         w2w Cop2 << 5 !! w2w CRm
    || MCR cond CPn Cop1b Rd CRn CRm Cop2 ->
         condition_encode cond !! 0xE000010w !! w2w Cop1b << 21 !!
         w2w CRn << 16 !! w2w Rd << 12 !! w2w CPn << 8 !!
         w2w Cop2 << 5 !! w2w CRm
    || UND cond -> condition_encode cond !! 0x6000010w`;

val _ = overload_on("enc", ``instruction_encode``);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
