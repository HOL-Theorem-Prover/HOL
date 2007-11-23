(* ========================================================================= *)
(* FILE          : instructionScript.sml                                     *)
(* DESCRIPTION   : Datatype for ARM instructions, and an encoder -> word32   *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2006 - 2007                                               *)
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
  `addr_mode3 =
     Dth_immediate of word8
   | Dth_register of word4`;

val _ = Hol_datatype
  `msr_mode =
     Msr_immediate of word4=>word8
   | Msr_register of word4`;

val _ = Hol_datatype
  `msr_psr = CPSR_c | CPSR_f | CPSR_a | SPSR_c | SPSR_f | SPSR_a`;

val _ = Hol_datatype
  `transfer_options = <| Pre : bool; Up : bool; Wb : bool |>`;

val _ = Hol_datatype
 `arm_instruction =
    B of condition=>word24
  | BX of condition=>word4
  | BL of condition=>word24
  | SWI of condition=>word24
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
  | LDRH of condition=>bool=>bool=>transfer_options=>word4=>word4=>addr_mode3
  | STRH of condition=>transfer_options=>word4=>word4=>addr_mode3
  | LDR of condition=>bool=>transfer_options=>word4=>word4=>addr_mode2
  | STR of condition=>bool=>transfer_options=>word4=>word4=>addr_mode2
  | LDM of condition=>bool=>transfer_options=>word4=>word16
  | STM of condition=>bool=>transfer_options=>word4=>word16
  | SWP of condition=>bool=>word4=>word4=>word4
  | MRS of condition=>bool=>word4
  | MSR of condition=>msr_psr=>msr_mode
  | CDP of condition=>word4=>word4=>word4=>word4=>word4=>word3
  | LDC of condition=>bool=>transfer_options=>word4=>word4=>word4=>word8
  | STC of condition=>bool=>transfer_options=>word4=>word4=>word4=>word8
  | MRC of condition=>word4=>word3=>word4=>word4=>word4=>word3
  | MCR of condition=>word4=>word3=>word4=>word4=>word4=>word3
  | UND of condition`;

val _ = Hol_datatype
 `thumb_instruction =
    LSL_1  of word3=>word3=>word5
  | LSR_1  of word3=>word3=>word5
  | ASR_1  of word3=>word3=>word5
  | ADD_3  of word3=>word3=>word3
  | SUB_3  of word3=>word3=>word3
  | ADD_1  of word3=>word3=>word3
  | SUB_1  of word3=>word3=>word3
  | MOV_1  of word3=>word8
  | CMP_1  of word3=>word8
  | ADD_2  of word3=>word8
  | SUB_2  of word3=>word8
  | AND_   of word3=>word3
  | EOR_   of word3=>word3
  | LSL_2  of word3=>word3
  | LSR_2  of word3=>word3
  | ASR_2  of word3=>word3
  | ADC_   of word3=>word3
  | SBC_   of word3=>word3
  | ROR_   of word3=>word3
  | TST_   of word3=>word3
  | NEG_   of word3=>word3
  | CMP_2  of word3=>word3
  | CMN_   of word3=>word3
  | ORR_   of word3=>word3
  | MUL_   of word3=>word3
  | BIC_   of word3=>word3
  | MVN_   of word3=>word3
  | ADD_4  of word4=>word4
  | CMP_3  of word4=>word4
  | MOV_3  of word4=>word4
  | BX_    of word4
  | LDR_3  of word3=>word8
  | STR_2  of word3=>word3=>word3
  | STRH_2 of word3=>word3=>word3
  | STRB_2 of word3=>word3=>word3
  | LDRSB_ of word3=>word3=>word3
  | LDR_2  of word3=>word3=>word3
  | LDRH_2 of word3=>word3=>word3
  | LDRB_2 of word3=>word3=>word3
  | LDRSH_ of word3=>word3=>word3
  | STR_1  of word3=>word3=>word5
  | LDR_1  of word3=>word3=>word5
  | STRB_1 of word3=>word3=>word5
  | LDRB_1 of word3=>word3=>word5
  | STRH_1 of word3=>word3=>word5
  | LDRH_1 of word3=>word3=>word5
  | STR_3  of word3=>word8
  | LDR_4  of word3=>word8
  | ADD_5  of word3=>word8
  | ADD_6  of word3=>word8
  | ADD_7  of word7
  | SUB_4  of word7
  | PUSH   of bool=>word8
  | POP    of bool=>word8
  | LDMIA_ of word3=>word8
  | STMIA_ of word3=>word8
  | B_1    of condition=>word8
  | UND_
  | SWI_   of word8
  | B_2    of 11 word
  | BL_a   of 11 word
  | BL_b   of 11 word`;

(* ------------------------------------------------------------------------- *)

val condition_encode_def = Define`
  condition_encode cond =
    (w2w (n2w (condition2num cond):word4 #<< 1) << 28):word32`;

val condition_encode__def = Define`
  condition_encode_ cond =
    (w2w (n2w (condition2num cond):word4 #<< 1) << 8):word16`;

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

val addr_mode3_encode_def = Define`
  addr_mode3_encode op2 =
   case op2 of
      Dth_immediate imm -> 0x400000w !! ((7 >< 4) imm) << 8 !! ((3 >< 0) imm)
   || Dth_register Rm -> (w2w Rm):word32`;

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
  options_encode x opt =
    word_modify (\i b. (i = 24) /\ opt.Pre \/ (i = 23) /\ opt.Up \/
                       (i = 22) /\ x \/ (i = 21) /\ opt.Wb) (0w:word32)`;

val options_encode2_def = Define`
  options_encode2 h opt =
    word_modify (\i b. (i = 24) /\ opt.Pre \/ (i = 23) /\ opt.Up \/
                       (i = 21) /\ opt.Wb \/ (i = 5) /\ h) (0w:word32)`;

val data_proc_encode_def = Define`
  data_proc_encode cond (op:word4) s (Rn:word4) (Rd:word4) Op2 =
    condition_encode cond !! w2w op << 21 !! (if s then 0x100000w else 0w) !!
       w2w Rn << 16 !! w2w Rd << 12 !! addr_mode1_encode Op2`;

val instruction_encode_def = Define`
  instruction_encode i =
    case i of
       B  cond offset24 -> condition_encode cond !! 0xA000000w !! w2w offset24
    || BX cond Rm -> condition_encode cond !! 0x1200010w !! w2w Rm
    || BL cond offset24 -> condition_encode cond !! 0xB000000w !! w2w offset24
    || SWI cond imm24 -> condition_encode cond !! 0xF000000w !! w2w imm24
    || AND cond s Rd Rn Op2 -> data_proc_encode cond 0w s Rn Rd Op2
    || EOR cond s Rd Rn Op2 -> data_proc_encode cond 1w s Rn Rd Op2
    || SUB cond s Rd Rn Op2 -> data_proc_encode cond 2w s Rn Rd Op2
    || RSB cond s Rd Rn Op2 -> data_proc_encode cond 3w s Rn Rd Op2
    || ADD cond s Rd Rn Op2 -> data_proc_encode cond 4w s Rn Rd Op2
    || ADC cond s Rd Rn Op2 -> data_proc_encode cond 5w s Rn Rd Op2
    || SBC cond s Rd Rn Op2 -> data_proc_encode cond 6w s Rn Rd Op2
    || RSC cond s Rd Rn Op2 -> data_proc_encode cond 7w s Rn Rd Op2
    || TST cond Rn Op2      -> data_proc_encode cond 8w T Rn 0w Op2
    || TEQ cond Rn Op2      -> data_proc_encode cond 9w T Rn 0w Op2
    || CMP cond Rn Op2      -> data_proc_encode cond 10w T Rn 0w Op2
    || CMN cond Rn Op2      -> data_proc_encode cond 11w T Rn 0w Op2
    || ORR cond s Rd Rn Op2 -> data_proc_encode cond 12w s Rn Rd Op2
    || MOV cond s Rd Op2    -> data_proc_encode cond 13w s 0w Rd Op2
    || BIC cond s Rd Rn Op2 -> data_proc_encode cond 14w s Rn Rd Op2
    || MVN cond s Rd Op2    -> data_proc_encode cond 15w s 0w Rd Op2
    || MUL cond s Rd Rm Rs ->
         condition_encode cond !! (if s then 0x100090w else 0x90w) !!
         w2w Rd << 16 !! w2w Rs << 8 !! w2w Rm
    || MLA cond s Rd Rm Rs Rn ->
         condition_encode cond !! (if s then 0x300090w else 0x200090w) !!
         w2w Rd << 16 !! w2w Rn << 12 !! w2w Rs << 8 !! w2w Rm
    || UMULL cond s RdLo RdHi Rm Rs ->
         condition_encode cond !! (if s then 0x900090w else 0x800090w) !!
         w2w RdHi << 16 !! w2w RdLo << 12 !! w2w Rs << 8 !! w2w Rm
    || UMLAL cond s RdLo RdHi Rm Rs ->
         condition_encode cond !! (if s then 0xB00090w else 0xA00090w) !!
         w2w RdHi << 16 !! w2w RdLo << 12 !! w2w Rs << 8 !! w2w Rm
    || SMULL cond s RdLo RdHi Rm Rs ->
         condition_encode cond !! (if s then 0xD00090w else 0xC00090w) !!
         w2w RdHi << 16 !! w2w RdLo << 12 !! w2w Rs << 8 !! w2w Rm
    || SMLAL cond s RdLo RdHi Rm Rs ->
         condition_encode cond !! (if s then 0xF00090w else 0xE00090w) !!
         w2w RdHi << 16 !! w2w RdLo << 12 !! w2w Rs << 8 !! w2w Rm
    || LDRH cond s h options Rd Rn mode3 ->
         condition_encode cond !! (if s then 0x1000D0w else 0x100090w) !!
         options_encode2 (h \/ (~h /\ ~s)) options !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode3_encode mode3
    || STRH cond options Rd Rn mode3 ->
         condition_encode cond !! 0x90w !! options_encode2 T options !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode3_encode mode3
    || LDR cond b options Rd Rn offset ->
         condition_encode cond !! 0x4100000w !! options_encode b options !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode2_encode offset
    || STR cond b options Rd Rn offset ->
         condition_encode cond !! 0x4000000w !! options_encode b options !!
         w2w Rn << 16 !! w2w Rd << 12 !! addr_mode2_encode offset
    || LDM cond s options Rn list ->
         condition_encode cond !! 0x8100000w !! options_encode s options !!
         w2w Rn << 16 !! w2w list
    || STM cond s options Rn list ->
         condition_encode cond !! 0x8000000w !! options_encode s options !!
         w2w Rn << 16 !! w2w list
    || SWP cond b Rd Rm Rn ->
         condition_encode cond !! (if b then 0x1400090w else 0x1000090w) !!
         w2w Rn << 16 !! w2w Rd << 12 !! w2w Rm
    || MRS cond R Rd ->
         condition_encode cond !! (if R then 0x14F0000w else 0x10F0000w) !!
         w2w Rd << 12
    || MSR cond psrd Op ->
         condition_encode cond !! 0x120F000w !! msr_psr_encode psrd !!
         (msr_mode_encode Op)
    || CDP cond CPn Cop1 CRd CRn CRm Cop2 ->
         condition_encode cond !! 0xE000000w !! w2w Cop1 << 20 !!
         w2w CRn << 16 !! w2w CRd << 12 !! w2w CPn << 8 !!
         w2w Cop2 << 5 !! w2w CRm
    || LDC cond n options CPn CRd Rn offset8 ->
         condition_encode cond !! 0xC100000w !! options_encode n options !!
         w2w Rn << 16 !! w2w CRd << 12 !! w2w CPn << 8 !! w2w offset8
    || STC cond n options CPn CRd Rn offset8 ->
         condition_encode cond !! 0xC000000w !! options_encode n options !!
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

val thumb_encode_def = Define`
  thumb_encode i =
  case i of
     LSL_1 Rd Rm imm5  ->            w2w imm5 << 6 !! w2w Rm << 3 !! w2w Rd
  || LSR_1 Rd Rm imm5  -> 0x0800w !! w2w imm5 << 6 !! w2w Rm << 3 !! w2w Rd
  || ASR_1 Rd Rm imm5  -> 0x1000w !! w2w imm5 << 6 !! w2w Rm << 3 !! w2w Rd
  || ADD_3 Rd Rn Rm    -> 0x1800w !! w2w Rm << 6 !! w2w Rn << 3 !! w2w Rd
  || SUB_3 Rd Rn Rm    -> 0x1A00w !! w2w Rm << 6 !! w2w Rn << 3 !! w2w Rd
  || ADD_1 Rd Rn imm3  -> 0x1C00w !! w2w imm3 << 6 !! w2w Rn << 3 !! w2w Rd
  || SUB_1 Rd Rn imm3  -> 0x1E00w !! w2w imm3 << 6 !! w2w Rn << 3 !! w2w Rd
  || MOV_1 Rd imm8     -> 0x2000w !! w2w Rd << 8 !! w2w imm8
  || CMP_1 Rn imm8     -> 0x2800w !! w2w Rn << 8 !! w2w imm8
  || ADD_2 Rd imm8     -> 0x3000w !! w2w Rd << 8 !! w2w imm8
  || SUB_2 Rd imm8     -> 0x3800w !! w2w Rd << 8 !! w2w imm8
  || AND_  Rd Rm       -> 0x4000w !! w2w Rm << 3 !! w2w Rd
  || EOR_  Rd Rm       -> 0x4040w !! w2w Rm << 3 !! w2w Rd
  || LSL_2 Rd Rm       -> 0x4080w !! w2w Rm << 3 !! w2w Rd
  || LSR_2 Rd Rm       -> 0x40C0w !! w2w Rm << 3 !! w2w Rd
  || ASR_2 Rd Rm       -> 0x4100w !! w2w Rm << 3 !! w2w Rd
  || ADC_  Rd Rm       -> 0x4140w !! w2w Rm << 3 !! w2w Rd
  || SBC_  Rd Rm       -> 0x4180w !! w2w Rm << 3 !! w2w Rd
  || ROR_  Rd Rm       -> 0x41C0w !! w2w Rm << 3 !! w2w Rd
  || TST_  Rd Rm       -> 0x4200w !! w2w Rm << 3 !! w2w Rd
  || NEG_  Rd Rm       -> 0x4240w !! w2w Rm << 3 !! w2w Rd
  || CMP_2 Rd Rm       -> 0x4280w !! w2w Rm << 3 !! w2w Rd
  || CMN_  Rd Rm       -> 0x42C0w !! w2w Rm << 3 !! w2w Rd
  || ORR_  Rd Rm       -> 0x4300w !! w2w Rm << 3 !! w2w Rd
  || MUL_  Rd Rm       -> 0x4340w !! w2w Rm << 3 !! w2w Rd
  || BIC_  Rd Rm       -> 0x4380w !! w2w Rm << 3 !! w2w Rd
  || MVN_  Rd Rm       -> 0x43C0w !! w2w Rm << 3 !! w2w Rd
  || ADD_4 H1Rd H2Rm   -> 0x4400w !! (3 >< 3) H1Rd << 7 !! (3 >< 3) H2Rm << 6 !!
                          (2 >< 0) H2Rm << 3 !! (2 >< 0) H1Rd
  || CMP_3 H1Rn H2Rm   -> 0x4500w !! (3 >< 3) H1Rn << 7 !! (3 >< 3) H2Rm << 6 !!
                          (2 >< 0) H2Rm << 3 !! (2 >< 0) H1Rn
  || MOV_3 H1Rd H2Rm   -> 0x4600w !! (3 >< 3) H1Rd << 7 !! (3 >< 3) H2Rm << 6 !!
                          (2 >< 0) H2Rm << 3 !! (2 >< 0) H1Rd
  || BX_ H2Rm          -> 0x4700w !! w2w H2Rm << 3
  || LDR_3 Rd imm8     -> 0x4800w !! w2w Rd << 8 !! w2w imm8
  || STR_2  Rd Rn Rm   -> 0x5000w !! w2w Rm << 6 !! w2w Rn << 3 !! w2w Rd
  || STRH_2 Rd Rn Rm   -> 0x5200w !! w2w Rm << 6 !! w2w Rn << 3 !! w2w Rd
  || STRB_2 Rd Rn Rm   -> 0x5400w !! w2w Rm << 6 !! w2w Rn << 3 !! w2w Rd
  || LDRSB_ Rd Rn Rm   -> 0x5600w !! w2w Rm << 6 !! w2w Rn << 3 !! w2w Rd
  || LDR_2  Rd Rn Rm   -> 0x5800w !! w2w Rm << 6 !! w2w Rn << 3 !! w2w Rd
  || LDRH_2 Rd Rn Rm   -> 0x5A00w !! w2w Rm << 6 !! w2w Rn << 3 !! w2w Rd
  || LDRB_2 Rd Rn Rm   -> 0x5C00w !! w2w Rm << 6 !! w2w Rn << 3 !! w2w Rd
  || LDRSH_ Rd Rn Rm   -> 0x5E00w !! w2w Rm << 6 !! w2w Rn << 3 !! w2w Rd
  || STR_1  Rd Rn imm5 -> 0x6000w !! w2w imm5 << 6 !! w2w Rn << 3 !! w2w Rd
  || LDR_1  Rd Rn imm5 -> 0x6800w !! w2w imm5 << 6 !! w2w Rn << 3 !! w2w Rd
  || STRB_1 Rd Rn imm5 -> 0x7000w !! w2w imm5 << 6 !! w2w Rn << 3 !! w2w Rd
  || LDRB_1 Rd Rn imm5 -> 0x7800w !! w2w imm5 << 6 !! w2w Rn << 3 !! w2w Rd
  || STRH_1 Rd Rn imm5 -> 0x8000w !! w2w imm5 << 6 !! w2w Rn << 3 !! w2w Rd
  || LDRH_1 Rd Rn imm5 -> 0x8800w !! w2w imm5 << 6 !! w2w Rn << 3 !! w2w Rd
  || STR_3 Rd imm8     -> 0x9000w !! w2w Rd << 8 !! w2w imm8
  || LDR_4 Rd imm8     -> 0x9800w !! w2w Rd << 8 !! w2w imm8
  || ADD_5 Rd imm8     -> 0xA000w !! w2w Rd << 8 !! w2w imm8
  || ADD_6 Rd imm8     -> 0xA800w !! w2w Rd << 8 !! w2w imm8
  || ADD_7 imm7        -> 0xB000w !! w2w imm7
  || SUB_4 imm7        -> 0xB080w !! w2w imm7
  || PUSH R list       -> (if R then 0xB500w else 0xB400w) !! w2w list
  || POP  R list       -> (if R then 0xBD00w else 0xBC00w) !! w2w list
  || STMIA_ Rn list    -> 0xC000w !! w2w Rn << 8 !! w2w list
  || LDMIA_ Rn list    -> 0xC800w !! w2w Rn << 8 !! w2w list
  || B_1  cond imm8    -> 0xD000w !! condition_encode_ cond !! w2w imm8
  || UND_              -> 0xDE00w
  || SWI_ imm8         -> 0xDF00w !! w2w imm8
  || B_2  imm11        -> 0xE000w !! w2w imm11
  || BL_a imm11        -> 0xF000w !! w2w imm11
  || BL_b imm11        -> 0xF800w !! w2w imm11`;

val _ = overload_on("enc", ``instruction_encode``);
val _ = overload_on("enc_", ``thumb_encode``);

(* ------------------------------------------------------------------------- *)

val _ = export_theory();
