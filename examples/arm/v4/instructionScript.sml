(* ========================================================================= *)
(* FILE          : instructionScript.sml                                     *)
(* DESCRIPTION   : Datatype for ARM instructions, and an encoder -> word32   *)
(*                                                                           *)
(* AUTHORS       : (c) Anthony Fox, University of Cambridge                  *)
(* DATE          : 2006 - 2007                                               *)
(* ========================================================================= *)

Theory instruction
Ancestors
  words arm
Libs
  Q


(* ------------------------------------------------------------------------- *)

Datatype:
  shift =
    LSL word4
  | LSR word4
  | ASR word4
  | ROR word4
End

Datatype:
   addr_mode1 =
     Dp_immediate word4 word8
   | Dp_shift_immediate shift word5
   | Dp_shift_register shift word4
End

Datatype:
   addr_mode2 =
     Dt_immediate word12
   | Dt_shift_immediate shift word5
End

Datatype:
   addr_mode3 =
     Dth_immediate word8
   | Dth_register word4
End

Datatype:
   msr_mode =
     Msr_immediate word4 word8
   | Msr_register word4
End

Datatype:
   msr_psr = CPSR_c | CPSR_f | CPSR_a | SPSR_c | SPSR_f | SPSR_a
End

Datatype:
   transfer_options = <| Pre : bool; Up : bool; Wb : bool |>
End

Datatype:
  arm_instruction =
    B condition word24
  | BL condition word24
  | SWI condition
  | AND condition bool word4 word4 addr_mode1
  | EOR condition bool word4 word4 addr_mode1
  | SUB condition bool word4 word4 addr_mode1
  | RSB condition bool word4 word4 addr_mode1
  | ADD condition bool word4 word4 addr_mode1
  | ADC condition bool word4 word4 addr_mode1
  | SBC condition bool word4 word4 addr_mode1
  | RSC condition bool word4 word4 addr_mode1
  | TST condition word4 addr_mode1
  | TEQ condition word4 addr_mode1
  | CMP condition word4 addr_mode1
  | CMN condition word4 addr_mode1
  | ORR condition bool word4 word4 addr_mode1
  | MOV condition bool word4 addr_mode1
  | BIC condition bool word4 word4 addr_mode1
  | MVN condition bool word4 addr_mode1
  | MUL condition bool word4 word4 word4
  | MLA condition bool word4 word4 word4 word4
  | UMULL condition bool word4 word4 word4 word4
  | UMLAL condition bool word4 word4 word4 word4
  | SMULL condition bool word4 word4 word4 word4
  | SMLAL condition bool word4 word4 word4 word4
  | LDRH condition bool bool transfer_options word4 word4 addr_mode3
  | STRH condition transfer_options word4 word4 addr_mode3
  | LDR condition bool transfer_options word4 word4 addr_mode2
  | STR condition bool transfer_options word4 word4 addr_mode2
  | LDM condition bool transfer_options word4 word16
  | STM condition bool transfer_options word4 word16
  | SWP condition bool word4 word4 word4
  | MRS condition bool word4
  | MSR condition msr_psr msr_mode
  | CDP condition word4 word4 word4 word4 word4 word3
  | LDC condition bool transfer_options word4 word4 word4 word8
  | STC condition bool transfer_options word4 word4 word4 word8
  | MRC condition word4 word3 word4 word4 word4 word3
  | MCR condition word4 word3 word4 word4 word4 word3
  | UND condition
End

(* ------------------------------------------------------------------------- *)

Definition condition_encode_def:
  condition_encode cond =
    (w2w (n2w (condition2num cond):word4 #<< 1) << 28):word32
End

Definition shift_encode_def:
  (shift_encode (LSL Rm) = (w2w Rm):word32) /\
  (shift_encode (LSR Rm) = 0x20w || w2w Rm) /\
  (shift_encode (ASR Rm) = 0x40w || w2w Rm) /\
  (shift_encode (ROR Rm) = 0x60w || w2w Rm)
End

Definition addr_mode1_encode_def:
  addr_mode1_encode op2 =
   case op2 of
     Dp_immediate rot imm => (0x2000000w || w2w rot << 8 || w2w imm):word32
   | Dp_shift_immediate shift amount => w2w amount << 7 || shift_encode shift
   | Dp_shift_register shift Rs => 0x10w || w2w Rs << 8 || shift_encode shift
End

Definition addr_mode2_encode_def:
  addr_mode2_encode op2 =
   case op2 of
     Dt_immediate imm => (w2w imm):word32
   | Dt_shift_immediate shift amount =>
        0x2000000w || w2w amount << 7 || shift_encode shift
End

Definition addr_mode3_encode_def:
  addr_mode3_encode op2 =
   case op2 of
     Dth_immediate imm => 0x400000w || ((7 >< 4) imm) << 8 || ((3 >< 0) imm)
   | Dth_register Rm => (w2w Rm):word32
End

Definition msr_mode_encode_def:
  msr_mode_encode op =
   case op of
     Msr_immediate rot imm => (0x2000000w || w2w rot << 8 || w2w imm):word32
   | Msr_register Rm => w2w Rm
End

Definition msr_psr_encode_def:
  (msr_psr_encode CPSR_c = 0x10000w:word32) /\
  (msr_psr_encode CPSR_f = 0x80000w) /\
  (msr_psr_encode CPSR_a = 0x90000w) /\
  (msr_psr_encode SPSR_c = 0x410000w) /\
  (msr_psr_encode SPSR_f = 0x480000w) /\
  (msr_psr_encode SPSR_a = 0x490000w)
End

Definition options_encode_def:
  options_encode x opt =
    word_modify (\i b. (i = 24) /\ opt.Pre \/ (i = 23) /\ opt.Up \/
                       (i = 22) /\ x \/ (i = 21) /\ opt.Wb) (0w:word32)
End

Definition options_encode2_def:
  options_encode2 h opt =
    word_modify (\i b. (i = 24) /\ opt.Pre \/ (i = 23) /\ opt.Up \/
                       (i = 21) /\ opt.Wb \/ (i = 5) /\ h) (0w:word32)
End

Definition data_proc_encode_def:
  data_proc_encode cond (op:word4) s (Rn:word4) (Rd:word4) Op2 =
    condition_encode cond || w2w op << 21 || (if s then 0x100000w else 0w) ||
       w2w Rn << 16 || w2w Rd << 12 || addr_mode1_encode Op2
End

Definition instruction_encode_def:
  instruction_encode i =
    case i of
      B  cond offset24 => condition_encode cond || 0xA000000w || w2w offset24
    | BL cond offset24 => condition_encode cond || 0xB000000w || w2w offset24
    | SWI cond => condition_encode cond || 0xF000000w
    | AND cond s Rd Rn Op2 => data_proc_encode cond 0w s Rn Rd Op2
    | EOR cond s Rd Rn Op2 => data_proc_encode cond 1w s Rn Rd Op2
    | SUB cond s Rd Rn Op2 => data_proc_encode cond 2w s Rn Rd Op2
    | RSB cond s Rd Rn Op2 => data_proc_encode cond 3w s Rn Rd Op2
    | ADD cond s Rd Rn Op2 => data_proc_encode cond 4w s Rn Rd Op2
    | ADC cond s Rd Rn Op2 => data_proc_encode cond 5w s Rn Rd Op2
    | SBC cond s Rd Rn Op2 => data_proc_encode cond 6w s Rn Rd Op2
    | RSC cond s Rd Rn Op2 => data_proc_encode cond 7w s Rn Rd Op2
    | TST cond Rn Op2      => data_proc_encode cond 8w T Rn 0w Op2
    | TEQ cond Rn Op2      => data_proc_encode cond 9w T Rn 0w Op2
    | CMP cond Rn Op2      => data_proc_encode cond 10w T Rn 0w Op2
    | CMN cond Rn Op2      => data_proc_encode cond 11w T Rn 0w Op2
    | ORR cond s Rd Rn Op2 => data_proc_encode cond 12w s Rn Rd Op2
    | MOV cond s Rd Op2    => data_proc_encode cond 13w s 0w Rd Op2
    | BIC cond s Rd Rn Op2 => data_proc_encode cond 14w s Rn Rd Op2
    | MVN cond s Rd Op2    => data_proc_encode cond 15w s 0w Rd Op2
    | MUL cond s Rd Rm Rs =>
         condition_encode cond || (if s then 0x100090w else 0x90w) ||
         w2w Rd << 16 || w2w Rs << 8 || w2w Rm
    | MLA cond s Rd Rm Rs Rn =>
         condition_encode cond || (if s then 0x300090w else 0x200090w) ||
         w2w Rd << 16 || w2w Rn << 12 || w2w Rs << 8 || w2w Rm
    | UMULL cond s RdLo RdHi Rm Rs =>
         condition_encode cond || (if s then 0x900090w else 0x800090w) ||
         w2w RdHi << 16 || w2w RdLo << 12 || w2w Rs << 8 || w2w Rm
    | UMLAL cond s RdLo RdHi Rm Rs =>
         condition_encode cond || (if s then 0xB00090w else 0xA00090w) ||
         w2w RdHi << 16 || w2w RdLo << 12 || w2w Rs << 8 || w2w Rm
    | SMULL cond s RdLo RdHi Rm Rs =>
         condition_encode cond || (if s then 0xD00090w else 0xC00090w) ||
         w2w RdHi << 16 || w2w RdLo << 12 || w2w Rs << 8 || w2w Rm
    | SMLAL cond s RdLo RdHi Rm Rs =>
         condition_encode cond || (if s then 0xF00090w else 0xE00090w) ||
         w2w RdHi << 16 || w2w RdLo << 12 || w2w Rs << 8 || w2w Rm
    | LDRH cond s h options Rd Rn mode3 =>
         condition_encode cond || (if s then 0x1000D0w else 0x100090w) ||
         options_encode2 (h \/ (~h /\ ~s)) options ||
         w2w Rn << 16 || w2w Rd << 12 || addr_mode3_encode mode3
    | STRH cond options Rd Rn mode3 =>
         condition_encode cond || 0x90w || options_encode2 T options ||
         w2w Rn << 16 || w2w Rd << 12 || addr_mode3_encode mode3
    | LDR cond b options Rd Rn offset =>
         condition_encode cond || 0x4100000w || options_encode b options ||
         w2w Rn << 16 || w2w Rd << 12 || addr_mode2_encode offset
    | STR cond b options Rd Rn offset =>
         condition_encode cond || 0x4000000w || options_encode b options ||
         w2w Rn << 16 || w2w Rd << 12 || addr_mode2_encode offset
    | LDM cond s options Rn list =>
         condition_encode cond || 0x8100000w || options_encode s options ||
         w2w Rn << 16 || w2w list
    | STM cond s options Rn list =>
         condition_encode cond || 0x8000000w || options_encode s options ||
         w2w Rn << 16 || w2w list
    | SWP cond b Rd Rm Rn =>
         condition_encode cond || (if b then 0x1400090w else 0x1000090w) ||
         w2w Rn << 16 || w2w Rd << 12 || w2w Rm
    | MRS cond R Rd =>
         condition_encode cond || (if R then 0x14F0000w else 0x10F0000w) ||
         w2w Rd << 12
    | MSR cond psrd Op =>
         condition_encode cond || 0x120F000w || msr_psr_encode psrd ||
         (msr_mode_encode Op)
    | CDP cond CPn Cop1 CRd CRn CRm Cop2 =>
         condition_encode cond || 0xE000000w || w2w Cop1 << 20 ||
         w2w CRn << 16 || w2w CRd << 12 || w2w CPn << 8 ||
         w2w Cop2 << 5 || w2w CRm
    | LDC cond n options CPn CRd Rn offset8 =>
         condition_encode cond || 0xC100000w || options_encode n options ||
         w2w Rn << 16 || w2w CRd << 12 || w2w CPn << 8 || w2w offset8
    | STC cond n options CPn CRd Rn offset8 =>
         condition_encode cond || 0xC000000w || options_encode n options ||
         w2w Rn << 16 || w2w CRd << 12 || w2w CPn << 8 || w2w offset8
    | MRC cond CPn Cop1b Rd CRn CRm Cop2 =>
         condition_encode cond || 0xE100010w || w2w Cop1b << 21 ||
         w2w CRn << 16 || w2w Rd << 12 || w2w CPn << 8 ||
         w2w Cop2 << 5 || w2w CRm
    | MCR cond CPn Cop1b Rd CRn CRm Cop2 =>
         condition_encode cond || 0xE000010w || w2w Cop1b << 21 ||
         w2w CRn << 16 || w2w Rd << 12 || w2w CPn << 8 ||
         w2w Cop2 << 5 || w2w CRm
    | UND cond => condition_encode cond || 0x6000010w
End

val _ = overload_on("enc", ``instruction_encode``);

(* ------------------------------------------------------------------------- *)
