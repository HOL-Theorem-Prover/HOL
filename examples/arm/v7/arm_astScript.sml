(* ------------------------------------------------------------------------ *)
(*     ARM Machine Code Semantics                                           *)
(*     ==========================                                           *)
(*     Abstract syntax tree (AST) for ARM instructions                      *)
(* ------------------------------------------------------------------------ *)
Theory arm_ast
Ancestors
  arm_coretypes


(* ------------------------------------------------------------------------ *)

val _ = temp_type_abbrev("reg", ``:word4``);

Datatype:
   addressing_mode1 =
     Mode1_immediate word12
   | Mode1_register word5 word2 reg
   | Mode1_register_shifted_register reg word2 reg
End

Datatype:
   addressing_mode2 =
     Mode2_immediate word12
   | Mode2_register word5 word2 reg
End

Datatype:
   addressing_mode3 =
     Mode3_immediate word12
   | Mode3_register word2 reg
End

Datatype:
  parallel_add_sub_op1 =
    Parallel_normal
  | Parallel_saturating
  | Parallel_halving
End

Datatype:
  parallel_add_sub_op2 =
    Parallel_add_16
  | Parallel_add_sub_exchange
  | Parallel_sub_add_exchange
  | Parallel_sub_16
  | Parallel_add_8
  | Parallel_sub_8
End

val _ = temp_type_abbrev("parallel_add_sub",
  ``: parallel_add_sub_op1 # parallel_add_sub_op2``);

Datatype: hint =
    Hint_nop
  | Hint_yield
  | Hint_wait_for_event
  | Hint_wait_for_interrupt
  | Hint_send_event
  | Hint_debug word4
End

(* ------------------------------------------------------------------------ *)

Datatype: branch_instruction =
    Branch_Target                  word24
  | Branch_Exchange                reg
  | Branch_Link_Exchange_Immediate bool bool word24
  | Branch_Link_Exchange_Register  reg
  | Compare_Branch                 bool word6 word3
  | Table_Branch_Byte              reg bool reg
  | Check_Array                    word4 word4
  | Handler_Branch_Link            bool word8
  | Handler_Branch_Link_Parameter  word5 word5
  | Handler_Branch_Parameter       word3 word5
End

Datatype: data_processing_instruction =
    Data_Processing                   word4 bool reg reg addressing_mode1
  | Add_Sub                           bool reg reg word12
  | Move_Halfword                     bool reg word16
  | Multiply                          bool bool reg reg reg reg
  | Multiply_Subtract                 reg reg reg reg
  | Signed_Halfword_Multiply          word2 bool bool reg reg reg reg
  | Signed_Multiply_Dual              reg reg reg bool bool reg
  | Signed_Multiply_Long_Dual         reg reg reg bool bool reg
  | Signed_Most_Significant_Multiply  reg reg reg bool reg
  | Signed_Most_Significant_Multiply_Subtract
                                      reg reg reg bool reg
  | Multiply_Long                     bool bool bool reg reg reg reg
  | Multiply_Accumulate_Accumulate    reg reg reg reg
  | Saturate                          bool word5 reg word5 bool reg
  | Saturate_16                       bool word4 reg reg
  | Saturating_Add_Subtract           word2 reg reg reg
  | Pack_Halfword                     reg reg word5 bool reg
  | Extend_Byte                       bool reg reg word2 reg
  | Extend_Byte_16                    bool reg reg word2 reg
  | Extend_Halfword                   bool reg reg word2 reg
  | Bit_Field_Clear_Insert            word5 reg word5 reg
  | Count_Leading_Zeroes              reg reg
  | Reverse_Bits                      reg reg
  | Byte_Reverse_Word                 reg reg
  | Byte_Reverse_Packed_Halfword      reg reg
  | Byte_Reverse_Signed_Halfword      reg reg
  | Bit_Field_Extract                 bool word5 reg word5 reg
  | Select_Bytes                      reg reg reg
  | Unsigned_Sum_Absolute_Differences reg reg reg reg
  | Parallel_Add_Subtract             bool parallel_add_sub reg reg reg
  | Divide                            bool reg reg reg
End

Datatype: status_access_instruction =
    Status_to_Register     bool reg
  | Register_to_Status     bool word4 reg
  | Immediate_to_Status    bool word4 word12
  | Change_Processor_State word2 bool bool bool (word5 option)
  | Set_Endianness         bool
End

Datatype: load_store_instruction =
    Load                       bool bool bool bool bool reg reg
                                  addressing_mode2
  | Store                      bool bool bool bool bool reg reg
                                  addressing_mode2
  | Load_Halfword              bool bool bool bool bool bool reg reg
                                  addressing_mode3
  | Store_Halfword             bool bool bool bool reg reg
                                  addressing_mode3
  | Load_Dual                  bool bool bool reg reg reg
                                  addressing_mode3
  | Store_Dual                 bool bool bool reg reg reg
                                  addressing_mode3
  | Load_Multiple              bool bool bool bool reg word16
  | Store_Multiple             bool bool bool bool reg word16
  | Load_Exclusive             reg reg word8
  | Store_Exclusive            reg reg reg word8
  | Load_Exclusive_Doubleword  reg reg reg
  | Store_Exclusive_Doubleword reg reg reg reg
  | Load_Exclusive_Halfword    reg reg
  | Store_Exclusive_Halfword   reg reg reg
  | Load_Exclusive_Byte        reg reg
  | Store_Exclusive_Byte       reg reg reg
  | Store_Return_State         bool bool bool word5
  | Return_From_Exception      bool bool bool reg
End

Datatype: miscellaneous_instruction =
    Hint                         hint
  | Breakpoint                   word16
  | Data_Memory_Barrier          word4
  | Data_Synchronization_Barrier word4
  | Instruction_Synchronization_Barrier
                                 word4
  | Swap                         bool reg reg reg
  | Preload_Data                 bool bool reg addressing_mode2
  | Preload_Instruction          bool reg addressing_mode2
  | Supervisor_Call              word24
  | Secure_Monitor_Call          word4
  | Enterx_Leavex                bool
  | Clear_Exclusive
  | If_Then                      word4 word4
End

Datatype: coprocessor_instruction =
    Coprocessor_Load            bool bool bool bool reg reg word4
                                   word8
  | Coprocessor_Store           bool bool bool bool reg reg word4
                                   word8
  | Coprocessor_Data_Processing word4 reg reg word4 word3 reg
  | Coprocessor_Transfer        word3 bool reg reg word4 word3 reg
  | Coprocessor_Transfer_Two    bool reg reg word4 word4 reg
End

(* ------------------------------------------------------------------------ *)

Datatype: ARMinstruction =
    Unpredictable
  | Undefined
  | Branch         branch_instruction
  | DataProcessing data_processing_instruction
  | StatusAccess   status_access_instruction
  | LoadStore      load_store_instruction
  | Miscellaneous  miscellaneous_instruction
  | Coprocessor    coprocessor_instruction
End

(* ------------------------------------------------------------------------ *)

val _ = type_abbrev("CPinstruction",``:cpid # word4 # coprocessor_instruction``)

Definition is_mode1_immediate_def:
  is_mode1_immediate x = case x of Mode1_immediate imm12 => T | _ => F
End

Definition is_mode2_immediate_def:
  is_mode2_immediate x = case x of Mode2_immediate imm12 => T | _ => F
End

Definition is_mode3_immediate_def:
  is_mode3_immediate x = case x of Mode3_immediate imm8 => T | _ => F
End
