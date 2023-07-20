(* ------------------------------------------------------------------------ *)
(*     ARM Machine Code Semantics                                           *)
(*     ==========================                                           *)
(*     Abstract syntax tree (AST) for ARM instructions                      *)
(* ------------------------------------------------------------------------ *)

open HolKernel boolLib bossLib Parse;
open arm_coretypesTheory;

val _ = new_theory "arm_ast";

(* ------------------------------------------------------------------------ *)

val _ = temp_type_abbrev("reg", ``:word4``);

val _ = Hol_datatype
  `addressing_mode1 =
     Mode1_immediate of word12
   | Mode1_register of word5=>word2=>reg
   | Mode1_register_shifted_register of reg=>word2=>reg`;

val _ = Hol_datatype
  `addressing_mode2 =
     Mode2_immediate of word12
   | Mode2_register of word5=>word2=>reg`;

val _ = Hol_datatype
  `addressing_mode3 =
     Mode3_immediate of word12
   | Mode3_register of word2=>reg`;

val _ = Hol_datatype
 `parallel_add_sub_op1 =
    Parallel_normal
  | Parallel_saturating
  | Parallel_halving`;

val _ = Hol_datatype
 `parallel_add_sub_op2 =
    Parallel_add_16
  | Parallel_add_sub_exchange
  | Parallel_sub_add_exchange
  | Parallel_sub_16
  | Parallel_add_8
  | Parallel_sub_8`;

val _ = temp_type_abbrev("parallel_add_sub",
  ``: parallel_add_sub_op1 # parallel_add_sub_op2``);

val _ = Hol_datatype `hint =
    Hint_nop
  | Hint_yield
  | Hint_wait_for_event
  | Hint_wait_for_interrupt
  | Hint_send_event
  | Hint_debug of word4`;

(* ------------------------------------------------------------------------ *)

val _ = Hol_datatype `branch_instruction =
    Branch_Target                  of word24
  | Branch_Exchange                of reg
  | Branch_Link_Exchange_Immediate of bool=>bool=>word24
  | Branch_Link_Exchange_Register  of reg
  | Compare_Branch                 of bool=>word6=>word3
  | Table_Branch_Byte              of reg=>bool=>reg
  | Check_Array                    of word4=>word4
  | Handler_Branch_Link            of bool=>word8
  | Handler_Branch_Link_Parameter  of word5=>word5
  | Handler_Branch_Parameter       of word3=>word5`;

val _ = Hol_datatype `data_processing_instruction =
    Data_Processing                   of word4=>bool=>reg=>reg=>addressing_mode1
  | Add_Sub                           of bool=>reg=>reg=>word12
  | Move_Halfword                     of bool=>reg=>word16
  | Multiply                          of bool=>bool=>reg=>reg=>reg=>reg
  | Multiply_Subtract                 of reg=>reg=>reg=>reg
  | Signed_Halfword_Multiply          of word2=>bool=>bool=>reg=>reg=>reg=>reg
  | Signed_Multiply_Dual              of reg=>reg=>reg=>bool=>bool=>reg
  | Signed_Multiply_Long_Dual         of reg=>reg=>reg=>bool=>bool=>reg
  | Signed_Most_Significant_Multiply  of reg=>reg=>reg=>bool=>reg
  | Signed_Most_Significant_Multiply_Subtract
                                      of reg=>reg=>reg=>bool=>reg
  | Multiply_Long                     of bool=>bool=>bool=>reg=>reg=>reg=>reg
  | Multiply_Accumulate_Accumulate    of reg=>reg=>reg=>reg
  | Saturate                          of bool=>word5=>reg=>word5=>bool=>reg
  | Saturate_16                       of bool=>word4=>reg=>reg
  | Saturating_Add_Subtract           of word2=>reg=>reg=>reg
  | Pack_Halfword                     of reg=>reg=>word5=>bool=>reg
  | Extend_Byte                       of bool=>reg=>reg=>word2=>reg
  | Extend_Byte_16                    of bool=>reg=>reg=>word2=>reg
  | Extend_Halfword                   of bool=>reg=>reg=>word2=>reg
  | Bit_Field_Clear_Insert            of word5=>reg=>word5=>reg
  | Count_Leading_Zeroes              of reg=>reg
  | Reverse_Bits                      of reg=>reg
  | Byte_Reverse_Word                 of reg=>reg
  | Byte_Reverse_Packed_Halfword      of reg=>reg
  | Byte_Reverse_Signed_Halfword      of reg=>reg
  | Bit_Field_Extract                 of bool=>word5=>reg=>word5=>reg
  | Select_Bytes                      of reg=>reg=>reg
  | Unsigned_Sum_Absolute_Differences of reg=>reg=>reg=>reg
  | Parallel_Add_Subtract             of bool=>parallel_add_sub=>reg=>reg=>reg
  | Divide                            of bool=>reg=>reg=>reg`;

val _ = Hol_datatype `status_access_instruction =
    Status_to_Register     of bool=>reg
  | Register_to_Status     of bool=>word4=>reg
  | Immediate_to_Status    of bool=>word4=>word12
  | Change_Processor_State of word2=>bool=>bool=>bool=>word5 option
  | Set_Endianness         of bool`;

val _ = Hol_datatype `load_store_instruction =
    Load                       of bool=>bool=>bool=>bool=>bool=>reg=>reg=>
                                  addressing_mode2
  | Store                      of bool=>bool=>bool=>bool=>bool=>reg=>reg=>
                                  addressing_mode2
  | Load_Halfword              of bool=>bool=>bool=>bool=>bool=>bool=>reg=>reg=>
                                  addressing_mode3
  | Store_Halfword             of bool=>bool=>bool=>bool=>reg=>reg=>
                                  addressing_mode3
  | Load_Dual                  of bool=>bool=>bool=>reg=>reg=>reg=>
                                  addressing_mode3
  | Store_Dual                 of bool=>bool=>bool=>reg=>reg=>reg=>
                                  addressing_mode3
  | Load_Multiple              of bool=>bool=>bool=>bool=>reg=>word16
  | Store_Multiple             of bool=>bool=>bool=>bool=>reg=>word16
  | Load_Exclusive             of reg=>reg=>word8
  | Store_Exclusive            of reg=>reg=>reg=>word8
  | Load_Exclusive_Doubleword  of reg=>reg=>reg
  | Store_Exclusive_Doubleword of reg=>reg=>reg=>reg
  | Load_Exclusive_Halfword    of reg=>reg
  | Store_Exclusive_Halfword   of reg=>reg=>reg
  | Load_Exclusive_Byte        of reg=>reg
  | Store_Exclusive_Byte       of reg=>reg=>reg
  | Store_Return_State         of bool=>bool=>bool=>word5
  | Return_From_Exception      of bool=>bool=>bool=>reg`;

val _ = Hol_datatype `miscellaneous_instruction =
    Hint                         of hint
  | Breakpoint                   of word16
  | Data_Memory_Barrier          of word4
  | Data_Synchronization_Barrier of word4
  | Instruction_Synchronization_Barrier
                                 of word4
  | Swap                         of bool=>reg=>reg=>reg
  | Preload_Data                 of bool=>bool=>reg=>addressing_mode2
  | Preload_Instruction          of bool=>reg=>addressing_mode2
  | Supervisor_Call              of word24
  | Secure_Monitor_Call          of word4
  | Enterx_Leavex                of bool
  | Clear_Exclusive
  | If_Then                      of word4=>word4`;

val _ = Hol_datatype `coprocessor_instruction =
    Coprocessor_Load            of bool=>bool=>bool=>bool=>reg=>reg=>word4=>
                                   word8
  | Coprocessor_Store           of bool=>bool=>bool=>bool=>reg=>reg=>word4=>
                                   word8
  | Coprocessor_Data_Processing of word4=>reg=>reg=>word4=>word3=>reg
  | Coprocessor_Transfer        of word3=>bool=>reg=>reg=>word4=>word3=>reg
  | Coprocessor_Transfer_Two    of bool=>reg=>reg=>word4=>word4=>reg`;

(* ------------------------------------------------------------------------ *)

val _ = Hol_datatype `ARMinstruction =
    Unpredictable
  | Undefined
  | Branch         of branch_instruction
  | DataProcessing of data_processing_instruction
  | StatusAccess   of status_access_instruction
  | LoadStore      of load_store_instruction
  | Miscellaneous  of miscellaneous_instruction
  | Coprocessor    of coprocessor_instruction`;

(* ------------------------------------------------------------------------ *)

val _ = type_abbrev("CPinstruction",``:cpid # word4 # coprocessor_instruction``)

val is_mode1_immediate_def = Define`
  is_mode1_immediate x = case x of Mode1_immediate imm12 => T | _ => F`;

val is_mode2_immediate_def = Define`
  is_mode2_immediate x = case x of Mode2_immediate imm12 => T | _ => F`;

val is_mode3_immediate_def = Define`
  is_mode3_immediate x = case x of Mode3_immediate imm8 => T | _ => F`;

val _ = export_theory ();
