structure arm_astSyntax :> arm_astSyntax =
struct

(* interactive use:
  app load ["arm_astTheory", "wordsSyntax"];
*)

open Abbrev HolKernel arm_astTheory;

(* ------------------------------------------------------------------------- *)

val ERR = Feedback.mk_HOL_ERR "arm_astSyntax";

fun inst_word_alpha ty tm =
  Term.inst [Type.alpha |->
   (if wordsSyntax.is_word_type (Term.type_of tm) then
      ty
    else
      wordsSyntax.mk_word_type ty)] tm;

fun in_numeral_type ty =
  case Lib.total Type.dest_thy_type ty
  of NONE => false
   | SOME {Tyop,...} => Lib.mem Tyop ["one","bit0","bit1"];

fun inst_list x y =
  List.map (fn (ty,v) =>
         (if in_numeral_type ty then
            inst_word_alpha ty
          else
            Term.inst [Type.alpha |-> ty]) v) (Lib.zip x y);

(* ------------------------------------------------------------------------- *)

fun mk_ast_const s = Term.prim_mk_const {Name = s, Thy = "arm_ast"}

val Mode1_register_shifted_register_tm =
  mk_ast_const "Mode1_register_shifted_register"

val Mode1_immediate_tm           = mk_ast_const "Mode1_immediate"
val Mode1_register_tm            = mk_ast_const "Mode1_register"
val Mode2_immediate_tm           = mk_ast_const "Mode2_immediate"
val Mode2_register_tm            = mk_ast_const "Mode2_register"
val Mode3_immediate_tm           = mk_ast_const "Mode3_immediate"
val Mode3_register_tm            = mk_ast_const "Mode3_register"

val Parallel_normal_tm           = mk_ast_const "Parallel_normal"
val Parallel_saturating_tm       = mk_ast_const "Parallel_saturating"
val Parallel_halving_tm          = mk_ast_const "Parallel_halving"
val Parallel_add_16_tm           = mk_ast_const "Parallel_add_16"
val Parallel_add_sub_exchange_tm = mk_ast_const "Parallel_add_sub_exchange"
val Parallel_sub_add_exchange_tm = mk_ast_const "Parallel_sub_add_exchange"
val Parallel_sub_16_tm           = mk_ast_const "Parallel_sub_16"
val Parallel_add_8_tm            = mk_ast_const "Parallel_add_8"
val Parallel_sub_8_tm            = mk_ast_const "Parallel_sub_8"

val Hint_nop_tm                  = mk_ast_const "Hint_nop"
val Hint_yield_tm                = mk_ast_const "Hint_yield"
val Hint_wait_for_event_tm       = mk_ast_const "Hint_wait_for_event"
val Hint_wait_for_interrupt_tm   = mk_ast_const "Hint_wait_for_interrupt"
val Hint_send_event_tm           = mk_ast_const "Hint_send_event"
val Hint_debug_tm                = mk_ast_const "Hint_debug"

val Branch_Target_tm             = mk_ast_const "Branch_Target"
val Branch_Exchange_tm           = mk_ast_const "Branch_Exchange"
val Compare_Branch_tm            = mk_ast_const "Compare_Branch"
val Table_Branch_Byte_tm         = mk_ast_const "Table_Branch_Byte"

val Branch_Link_Exchange_Immediate_tm =
   mk_ast_const "Branch_Link_Exchange_Immediate"

val Branch_Link_Exchange_Register_tm =
   mk_ast_const "Branch_Link_Exchange_Register"

val Data_Processing_tm           = mk_ast_const "Data_Processing"
val Add_Sub_tm                   = mk_ast_const "Add_Sub"
val Move_Halfword_tm             = mk_ast_const "Move_Halfword"
val Multiply_tm                  = mk_ast_const "Multiply"
val Multiply_Subtract_tm         = mk_ast_const "Multiply_Subtract"
val Signed_Halfword_Multiply_tm  = mk_ast_const "Signed_Halfword_Multiply"
val Signed_Multiply_Dual_tm      = mk_ast_const "Signed_Multiply_Dual"
val Signed_Multiply_Long_Dual_tm = mk_ast_const "Signed_Multiply_Long_Dual"
val Multiply_Long_tm             = mk_ast_const "Multiply_Long"
val Saturate_tm                  = mk_ast_const "Saturate"
val Saturate_16_tm               = mk_ast_const "Saturate_16"
val Saturating_Add_Subtract_tm   = mk_ast_const "Saturating_Add_Subtract"
val Pack_Halfword_tm             = mk_ast_const "Pack_Halfword"
val Extend_Byte_tm               = mk_ast_const "Extend_Byte"
val Extend_Byte_16_tm            = mk_ast_const "Extend_Byte_16"
val Extend_Halfword_tm           = mk_ast_const "Extend_Halfword"
val Bit_Field_Clear_Insert_tm    = mk_ast_const "Bit_Field_Clear_Insert"
val Count_Leading_Zeroes_tm      = mk_ast_const "Count_Leading_Zeroes"
val Reverse_Bits_tm              = mk_ast_const "Reverse_Bits"
val Byte_Reverse_Word_tm         = mk_ast_const "Byte_Reverse_Word"
val Bit_Field_Extract_tm         = mk_ast_const "Bit_Field_Extract"
val Select_Bytes_tm              = mk_ast_const "Select_Bytes"
val Parallel_Add_Subtract_tm     = mk_ast_const "Parallel_Add_Subtract"
val Divide_tm                    = mk_ast_const "Divide"

val Signed_Most_Significant_Multiply_tm =
  mk_ast_const "Signed_Most_Significant_Multiply"

val Signed_Most_Significant_Multiply_Subtract_tm =
  mk_ast_const "Signed_Most_Significant_Multiply_Subtract"

val Multiply_Accumulate_Accumulate_tm =
  mk_ast_const "Multiply_Accumulate_Accumulate"

val Byte_Reverse_Packed_Halfword_tm =
  mk_ast_const "Byte_Reverse_Packed_Halfword"

val Byte_Reverse_Signed_Halfword_tm =
  mk_ast_const "Byte_Reverse_Signed_Halfword"

val Unsigned_Sum_Absolute_Differences_tm =
  mk_ast_const "Unsigned_Sum_Absolute_Differences"

val Status_to_Register_tm     = mk_ast_const "Status_to_Register"
val Register_to_Status_tm     = mk_ast_const "Register_to_Status"
val Immediate_to_Status_tm    = mk_ast_const "Immediate_to_Status"
val Change_Processor_State_tm = mk_ast_const "Change_Processor_State"
val Set_Endianness_tm         = mk_ast_const "Set_Endianness"

val Load_tm                       = mk_ast_const "Load"
val Store_tm                      = mk_ast_const "Store"
val Load_Halfword_tm              = mk_ast_const "Load_Halfword"
val Store_Halfword_tm             = mk_ast_const "Store_Halfword"
val Load_Dual_tm                  = mk_ast_const "Load_Dual"
val Store_Dual_tm                 = mk_ast_const "Store_Dual"
val Load_Multiple_tm              = mk_ast_const "Load_Multiple"
val Store_Multiple_tm             = mk_ast_const "Store_Multiple"
val Load_Exclusive_tm             = mk_ast_const "Load_Exclusive"
val Store_Exclusive_tm            = mk_ast_const "Store_Exclusive"
val Load_Exclusive_Doubleword_tm  = mk_ast_const "Load_Exclusive_Doubleword"
val Store_Exclusive_Doubleword_tm = mk_ast_const "Store_Exclusive_Doubleword"
val Load_Exclusive_Halfword_tm    = mk_ast_const "Load_Exclusive_Halfword"
val Store_Exclusive_Halfword_tm   = mk_ast_const "Store_Exclusive_Halfword"
val Load_Exclusive_Byte_tm        = mk_ast_const "Load_Exclusive_Byte"
val Store_Exclusive_Byte_tm       = mk_ast_const "Store_Exclusive_Byte"
val Store_Return_State_tm         = mk_ast_const "Store_Return_State"
val Return_From_Exception_tm      = mk_ast_const "Return_From_Exception"

val Hint_tm                = mk_ast_const "Hint"
val Breakpoint_tm          = mk_ast_const "Breakpoint"
val Data_Memory_Barrier_tm = mk_ast_const "Data_Memory_Barrier"
val Swap_tm                = mk_ast_const "Swap"
val Preload_Data_tm        = mk_ast_const "Preload_Data"
val Preload_Instruction_tm = mk_ast_const "Preload_Instruction"
val Supervisor_Call_tm     = mk_ast_const "Supervisor_Call"
val Secure_Monitor_Call_tm = mk_ast_const "Secure_Monitor_Call"
val Clear_Exclusive_tm     = mk_ast_const "Clear_Exclusive"
val If_Then_tm             = mk_ast_const "If_Then"

val Data_Synchronization_Barrier_tm =
   mk_ast_const "Data_Synchronization_Barrier"

val Instruction_Synchronization_Barrier_tm =
   mk_ast_const "Instruction_Synchronization_Barrier"

val Coprocessor_Load_tm            = mk_ast_const "Coprocessor_Load"
val Coprocessor_Store_tm           = mk_ast_const "Coprocessor_Store"
val Coprocessor_Data_Processing_tm = mk_ast_const "Coprocessor_Data_Processing"
val Coprocessor_Transfer_tm        = mk_ast_const "Coprocessor_Transfer"
val Coprocessor_Transfer_Two_tm    = mk_ast_const "Coprocessor_Transfer_Two"

val Unpredictable_tm       = mk_ast_const "Unpredictable"
val Undefined_tm           = mk_ast_const "Undefined"
val Branch_tm              = mk_ast_const "Branch"
val DataProcessing_tm      = mk_ast_const "DataProcessing"
val StatusAccess_tm        = mk_ast_const "StatusAccess"
val LoadStore_tm           = mk_ast_const "LoadStore"
val Miscellaneous_tm       = mk_ast_const "Miscellaneous"
val Coprocessor_tm         = mk_ast_const "Coprocessor"

(* ------------------------------------------------------------------------- *)

fun mk_Mode1_immediate t =
  Term.mk_comb(Mode1_immediate_tm, inst_word_alpha ``:12`` t)
  handle HOL_ERR _ => raise ERR "mk_Mode1_immediate" "";

fun mk_Mode1_register(r,s,t) =
  Term.list_mk_comb(Mode1_register_tm, inst_list [``:5``,``:2``,``:4``] [r,s,t])
  handle HOL_ERR _ => raise ERR "mk_Mode1_register" "";

fun mk_Mode1_register_shifted_register(r,s,t) =
  Term.list_mk_comb(Mode1_register_shifted_register_tm,
    inst_list [``:4``,``:2``,``:4``] [r,s,t])
  handle HOL_ERR _ => raise ERR "mk_Mode1_register_shifted_register" "";

fun mk_Mode2_immediate t =
  Term.mk_comb(Mode2_immediate_tm, inst_word_alpha ``:12`` t)
  handle HOL_ERR _ => raise ERR "mk_Mode2_immediate" "";

fun mk_Mode2_register(r,s,t) =
  Term.list_mk_comb(Mode2_register_tm, inst_list [``:5``,``:2``,``:3``] [r,s,t])
  handle HOL_ERR _ => raise ERR "mk_Mode2_register" "";

fun mk_Mode3_immediate t =
  Term.mk_comb(Mode3_immediate_tm, inst_word_alpha ``:12`` t)
  handle HOL_ERR _ => raise ERR "mk_Mode3_immediate" "";

fun mk_Mode3_register(r,s) =
  Term.list_mk_comb(Mode3_register_tm, inst_list [``:2``,``:4``] [r,s])
  handle HOL_ERR _ => raise ERR "mk_Mode3_register" "";

fun mk_Hint_debug t =
  Term.mk_comb(Hint_debug_tm, inst_word_alpha ``:4`` t)
  handle HOL_ERR _ => raise ERR "mk_Hint_debug" "";

(* .. *)

fun mk_Branch t =
  Term.mk_comb(Branch_tm, inst [alpha |-> ``:branch_instruction``] t)
  handle HOL_ERR _ => raise ERR "mk_Branch" "";

fun mk_Branch_Target t =
  Term.mk_comb(Branch_Target_tm, inst_word_alpha ``:24`` t) |> mk_Branch
  handle HOL_ERR _ => raise ERR "mk_Branch_Target" "";

fun mk_Branch_Exchange t =
  Term.mk_comb(Branch_Exchange_tm, inst_word_alpha ``:4`` t) |> mk_Branch
  handle HOL_ERR _ => raise ERR "mk_Branch_Exchange" "";

fun mk_Branch_Link_Exchange_Immediate(r,s,t) =
  Term.list_mk_comb(Branch_Link_Exchange_Immediate_tm,
    inst_list [bool,bool,``:24``] [r,s,t]) |> mk_Branch
  handle HOL_ERR _ => raise ERR "mk_Branch_Link_Exchange_Immediate" "";

fun mk_Branch_Link_Exchange_Register t =
  Term.mk_comb(Branch_Link_Exchange_Register_tm, inst_word_alpha ``:4`` t)
    |> mk_Branch
  handle HOL_ERR _ => raise ERR "mk_Branch_Link_Exchange_Register" "";

fun mk_Compare_Branch(r,s,t) =
  Term.list_mk_comb(Compare_Branch_tm, inst_list [bool,``:6``,``:3``] [r,s,t])
    |> mk_Branch
  handle HOL_ERR _ => raise ERR "mk_Compare_Branch" "";

fun mk_Table_Branch_Byte(r,s,t) =
  Term.list_mk_comb
       (Table_Branch_Byte_tm, inst_list [``:4``,bool,``:4``] [r,s,t])
    |> mk_Branch
  handle HOL_ERR _ => raise ERR "mk_Table_Branch_Byte" "";

(* .. *)

fun mk_DataProcessing t =
  Term.mk_comb(DataProcessing_tm,
    inst [alpha |-> ``:data_processing_instruction``] t)
  handle HOL_ERR _ => raise ERR "mk_DataProcessing" "";

fun mk_Data_Processing(r,s,t,u,v) =
  Term.list_mk_comb(Data_Processing_tm,
    inst_list [``:4``,bool,``:4``,``:4``,``:addressing_mode1``] [r,s,t,u,v])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Data_Processing" "";

fun mk_Add_Sub(r,s,t,u) =
  Term.list_mk_comb
       (Add_Sub_tm, inst_list [bool,``:4``,``:4``,``:12``] [r,s,t,u])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Add_Sub" "";

fun mk_Move_Halfword(r,s,t) =
  Term.list_mk_comb(Move_Halfword_tm, inst_list [bool,``:4``,``:16``] [r,s,t])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Move_Halfword" "";

fun mk_Multiply(r,s,t,u,v,w) =
  Term.list_mk_comb(Multiply_tm,
    inst_list [bool,bool,``:4``,``:4``,``:4``,``:4``] [r,s,t,u,v,w])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Multiply" "";

fun mk_Multiply_Subtract(r,s,t,u) =
  Term.list_mk_comb(Multiply_Subtract_tm,
    inst_list [``:4``,``:4``,``:4``,``:4``] [r,s,t,u])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Multiply_Subtract" "";

fun mk_Signed_Halfword_Multiply(r,s,t,u,v,w,x) =
  Term.list_mk_comb(Signed_Halfword_Multiply_tm,
    inst_list [``:2``,bool,bool,``:4``,``:4``,``:4``,``:4``] [r,s,t,u,v,w,x])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Signed_Halfword_Multiply" "";

fun mk_Signed_Multiply_Dual(r,s,t,u,v,w) =
  Term.list_mk_comb(Signed_Multiply_Dual_tm,
    inst_list [``:4``,``:4``,``:4``,bool,bool,``:4``] [r,s,t,u,v,w])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Signed_Multiply_Dual" "";

fun mk_Signed_Multiply_Long_Dual(r,s,t,u,v,w) =
  Term.list_mk_comb(Signed_Multiply_Long_Dual_tm,
    inst_list [``:4``,``:4``,``:4``,bool,bool,``:4``] [r,s,t,u,v,w])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Signed_Multiply_Long_Dual" "";

fun mk_Multiply_Long(r,s,t,u,v,w,x) =
  Term.list_mk_comb(Multiply_Long_tm,
    inst_list [bool,bool,bool,``:4``,``:4``,``:4``,``:4``] [r,s,t,u,v,w,x])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Multiply_Long" "";

fun mk_Saturate(r,s,t,u,v,w) =
  Term.list_mk_comb(Saturate_tm,
    inst_list [bool,``:5``,``:4``,``:5``,bool,``:4``] [r,s,t,u,v,w])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Saturate" "";

fun mk_Saturate_16(r,s,t,u) =
  Term.list_mk_comb(Saturate_16_tm,
    inst_list [bool,``:4``,``:4``,``:4``] [r,s,t,u])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Saturate_16" "";

fun mk_Saturating_Add_Subtract(r,s,t,u) =
  Term.list_mk_comb(Saturating_Add_Subtract_tm,
    inst_list [``:2``,``:4``,``:4``,``:4``] [r,s,t,u])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Saturating_Add_Subtract" "";

fun mk_Pack_Halfword(r,s,t,u,v) =
  Term.list_mk_comb(Pack_Halfword_tm,
    inst_list [``:4``,``:4``,``:5``,bool,``:4``] [r,s,t,u,v])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Pack_Halfword" "";

fun mk_Extend_Byte(r,s,t,u,v) =
  Term.list_mk_comb(Extend_Byte_tm,
    inst_list [bool,``:4``,``:4``,``:2``,``:4``] [r,s,t,u,v])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Extend_Byte" "";

fun mk_Extend_Byte_16(r,s,t,u,v) =
  Term.list_mk_comb(Extend_Byte_16_tm,
    inst_list [bool,``:4``,``:4``,``:2``,``:4``] [r,s,t,u,v])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Extend_Byte_16" "";

fun mk_Extend_Halfword(r,s,t,u,v) =
  Term.list_mk_comb(Extend_Halfword_tm,
    inst_list [bool,``:4``,``:4``,``:2``,``:4``] [r,s,t,u,v])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Extend_Halfword" "";

fun mk_Bit_Field_Clear_Insert(r,s,t,u) =
  Term.list_mk_comb(Bit_Field_Clear_Insert_tm,
    inst_list [``:5``,``:4``,``:5``,``:4``] [r,s,t,u])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Bit_Field_Clear_Insert" "";

fun mk_Count_Leading_Zeroes(r,s) =
  Term.list_mk_comb(Count_Leading_Zeroes_tm, inst_list [``:4``,``:4``] [r,s])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Count_Leading_Zeroes" "";

fun mk_Reverse_Bits(r,s) =
  Term.list_mk_comb(Reverse_Bits_tm, inst_list [``:4``,``:4``] [r,s])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Reverse_Bits" "";

fun mk_Byte_Reverse_Word(r,s) =
  Term.list_mk_comb(Byte_Reverse_Word_tm, inst_list [``:4``,``:4``] [r,s])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Byte_Reverse_Word" "";

fun mk_Bit_Field_Extract(r,s,t,u,v) =
  Term.list_mk_comb(Bit_Field_Extract_tm,
    inst_list [bool,``:5``,``:4``,``:5``,``:4``] [r,s,t,u,v])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Bit_Field_Extract" "";

fun mk_Select_Bytes(r,s,t) =
  Term.list_mk_comb(Select_Bytes_tm, inst_list [``:4``,``:4``,``:4``] [r,s,t])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Select_Bytes" "";

fun mk_Parallel_Add_Subtract(r,s,t,u,v) =
  Term.list_mk_comb(Parallel_Add_Subtract_tm,
    inst_list [bool,``:parallel_add_sub_op1 # parallel_add_sub_op2``,
               ``:4``,``:4``,``:4``] [r,s,t,u,v])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Parallel_Add_Subtract" "";

fun mk_Divide(r,s,t,u) =
  Term.list_mk_comb(Divide_tm, inst_list [bool,``:4``,``:4``,``:4``] [r,s,t,u])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Divide" "";

fun mk_Signed_Most_Significant_Multiply(r,s,t,u,v) =
  Term.list_mk_comb(Signed_Most_Significant_Multiply_tm,
    inst_list [``:4``,``:4``,``:4``,bool,``:4``] [r,s,t,u,v])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Signed_Most_Significant_Multiply" "";

fun mk_Signed_Most_Significant_Multiply_Subtract(r,s,t,u,v) =
  Term.list_mk_comb(Signed_Most_Significant_Multiply_Subtract_tm,
    inst_list [``:4``,``:4``,``:4``,bool,``:4``] [r,s,t,u,v])
    |> mk_DataProcessing
  handle HOL_ERR _ =>
    raise ERR "mk_Signed_Most_Significant_Multiply_Subtract" "";

fun mk_Multiply_Accumulate_Accumulate(r,s,t,u) =
  Term.list_mk_comb(Multiply_Accumulate_Accumulate_tm,
    inst_list [``:4``,``:4``,``:4``,``:4``] [r,s,t,u])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Multiply_Accumulate_Accumulate" "";

fun mk_Byte_Reverse_Packed_Halfword(r,s) =
  Term.list_mk_comb(Byte_Reverse_Packed_Halfword_tm,
    inst_list [``:4``,``:4``] [r,s])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Byte_Reverse_Packed_Halfword" "";

fun mk_Byte_Reverse_Signed_Halfword(r,s) =
  Term.list_mk_comb(Byte_Reverse_Signed_Halfword_tm,
    inst_list [``:4``,``:4``] [r,s])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Byte_Reverse_Signed_Halfword" "";

fun mk_Unsigned_Sum_Absolute_Differences(r,s,t,u) =
  Term.list_mk_comb(Unsigned_Sum_Absolute_Differences_tm,
    inst_list [``:4``,``:4``,``:4``,``:4``] [r,s,t,u])
    |> mk_DataProcessing
  handle HOL_ERR _ => raise ERR "mk_Unsigned_Sum_Absolute_Differences" "";

(* .. *)

fun mk_StatusAccess t =
  Term.mk_comb(StatusAccess_tm, inst [alpha |-> ``:status_access_instruction``] t)
  handle HOL_ERR _ => raise ERR "mk_StatusAccess" "";

fun mk_Status_to_Register(r,s) =
  Term.list_mk_comb(Status_to_Register_tm, inst_list [bool,``:4``] [r,s])
    |> mk_StatusAccess
  handle HOL_ERR _ => raise ERR "mk_Status_to_Register" "";

fun mk_Register_to_Status(r,s,t) =
  Term.list_mk_comb
       (Register_to_Status_tm, inst_list [bool,``:4``,``:4``] [r,s,t])
    |> mk_StatusAccess
  handle HOL_ERR _ => raise ERR "mk_Register_to_Status" "";

fun mk_Immediate_to_Status(r,s,t) =
  Term.list_mk_comb
       (Immediate_to_Status_tm, inst_list [bool,``:4``,``:12``] [r,s,t])
    |> mk_StatusAccess
  handle HOL_ERR _ => raise ERR "mk_Immediate_to_Status" "";

fun mk_Change_Processor_State(r,s,t,u,v) =
  Term.list_mk_comb(Change_Processor_State_tm,
    inst_list [``:2``,bool,bool,bool,``:word5 option``] [r,s,t,u,v])
    |> mk_StatusAccess
  handle HOL_ERR _ => raise ERR "mk_Change_Processor_State" "";

fun mk_Set_Endianness t =
  Term.mk_comb(Set_Endianness_tm, inst [alpha |-> bool] t)
    |> mk_StatusAccess
  handle HOL_ERR _ => raise ERR "mk_Set_Endianness" "";

(* .. *)

fun mk_LoadStore t =
  Term.mk_comb(LoadStore_tm, inst [alpha |-> ``:load_store_instruction``] t)
  handle HOL_ERR _ => raise ERR "mk_LoadStore" "";

fun mk_Load(r,s,t,u,v,w,x,y) =
  Term.list_mk_comb(Load_tm,
    inst_list [bool,bool,bool,bool,bool,``:4``,``:4``,``:addressing_mode2``]
              [r,s,t,u,v,w,x,y]) |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Load" "";

fun mk_Store(r,s,t,u,v,w,x,y) =
  Term.list_mk_comb(Store_tm,
    inst_list [bool,bool,bool,bool,bool,``:4``,``:4``,``:addressing_mode2``]
              [r,s,t,u,v,w,x,y]) |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Store" "";

fun mk_Load_Halfword(r,s,t,u,v,w,x,y,z) =
  Term.list_mk_comb(Load_Halfword_tm,
    inst_list [bool,bool,bool,bool,bool,bool,``:4``,``:4``,
               ``:addressing_mode3``]
              [r,s,t,u,v,w,x,y,z]) |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Load_Halfword" "";

fun mk_Store_Halfword(r,s,t,u,v,w,x) =
  Term.list_mk_comb(Store_Halfword_tm,
    inst_list [bool,bool,bool,bool,``:4``,``:4``,``:addressing_mode3``]
              [r,s,t,u,v,w,x]) |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Store_Halfword" "";

fun mk_Load_Dual(r,s,t,u,v,w,x) =
  Term.list_mk_comb(Load_Dual_tm,
    inst_list [bool,bool,bool,``:4``,``:4``,``:4``,``:addressing_mode3``]
              [r,s,t,u,v,w,x]) |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Load_Dual" "";

fun mk_Store_Dual(r,s,t,u,v,w,x) =
  Term.list_mk_comb(Store_Dual_tm,
    inst_list [bool,bool,bool,``:4``,``:4``,``:4``,``:addressing_mode3``]
              [r,s,t,u,v,w,x]) |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Store_Dual" "";

fun mk_Load_Multiple(r,s,t,u,v,w) =
  Term.list_mk_comb(Load_Multiple_tm,
    inst_list [bool,bool,bool,bool,``:4``,``:16``] [r,s,t,u,v,w])
    |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Load_Multiple" "";

fun mk_Store_Multiple(r,s,t,u,v,w) =
  Term.list_mk_comb(Store_Multiple_tm,
    inst_list [bool,bool,bool,bool,``:4``,``:16``] [r,s,t,u,v,w])
    |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Store_Multiple" "";

fun mk_Load_Exclusive(r,s,t) =
  Term.list_mk_comb
       (Load_Exclusive_tm, inst_list [``:4``,``:4``,``:8``] [r,s,t])
    |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Load_Exclusive" "";

fun mk_Store_Exclusive(r,s,t,u) =
  Term.list_mk_comb(Store_Exclusive_tm,
    inst_list [``:4``,``:4``,``:4``,``:8``] [r,s,t,u])
    |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Store_Exclusive" "";

fun mk_Load_Exclusive_Doubleword(r,s,t) =
  Term.list_mk_comb(Load_Exclusive_Doubleword_tm,
    inst_list [``:4``,``:4``,``:4``] [r,s,t])
    |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Load_Exclusive_Doubleword" "";

fun mk_Store_Exclusive_Doubleword(r,s,t,u) =
  Term.list_mk_comb(Store_Exclusive_Doubleword_tm,
    inst_list [``:4``,``:4``,``:4``,``:4``] [r,s,t,u])
    |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Store_Exclusive_Doubleword" "";

fun mk_Load_Exclusive_Halfword(r,s) =
  Term.list_mk_comb
       (Load_Exclusive_Halfword_tm, inst_list [``:4``,``:4``] [r,s])
    |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Load_Exclusive_Halfword" "";

fun mk_Store_Exclusive_Halfword(r,s,t) =
  Term.list_mk_comb(Store_Exclusive_Halfword_tm,
    inst_list [``:4``,``:4``,``:4``] [r,s,t])
    |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Store_Exclusive_Halfword" "";

fun mk_Load_Exclusive_Byte(r,s) =
  Term.list_mk_comb
       (Load_Exclusive_Byte_tm, inst_list [``:4``,``:4``] [r,s])
    |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Load_Exclusive_Byte" "";

fun mk_Store_Exclusive_Byte(r,s,t) =
  Term.list_mk_comb(Store_Exclusive_Byte_tm,
    inst_list [``:4``,``:4``,``:4``] [r,s,t])
    |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Store_Exclusive_Byte" "";

fun mk_Store_Return_State(r,s,t,u) =
  Term.list_mk_comb(Store_Return_State_tm,
    inst_list [bool,bool,bool,``:5``] [r,s,t,u])
    |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Store_Return_State" "";

fun mk_Return_From_Exception(r,s,t,u) =
  Term.list_mk_comb(Return_From_Exception_tm,
    inst_list [bool,bool,bool,``:5``] [r,s,t,u])
    |> mk_LoadStore
  handle HOL_ERR _ => raise ERR "mk_Return_From_Exception" "";

(* .. *)

fun mk_Miscellaneous t =
  Term.mk_comb
       (Miscellaneous_tm, inst [alpha |-> ``:load_store_instruction``] t)
  handle HOL_ERR _ => raise ERR "mk_Miscellaneous" "";

fun mk_Hint t =
  Term.mk_comb(Hint_tm, inst [alpha |-> ``:hint``] t)
    |> mk_Miscellaneous
  handle HOL_ERR _ => raise ERR "mk_Hint" "";

fun mk_Breakpoint t =
  Term.mk_comb(Breakpoint_tm, inst_word_alpha ``:16`` t) |> mk_Miscellaneous
  handle HOL_ERR _ => raise ERR "mk_Breakpoint" "";

fun mk_Data_Memory_Barrier t =
  Term.mk_comb
       (Data_Memory_Barrier_tm, inst_word_alpha ``:4`` t) |> mk_Miscellaneous
  handle HOL_ERR _ => raise ERR "mk_Data_Memory_Barrier" "";

fun mk_Swap(r,s,t,u) =
  Term.list_mk_comb
       (Swap_tm, inst_list [bool,``:4``,``:4``,``:4``] [r,s,t,u])
    |> mk_Miscellaneous
  handle HOL_ERR _ => raise ERR "mk_Swap" "";

fun mk_Preload_Data(r,s,t,u) =
  Term.list_mk_comb(Preload_Data_tm,
    inst_list [bool,bool,``:4``,``:addressing_mode2``] [r,s,t,u])
    |> mk_Miscellaneous
  handle HOL_ERR _ => raise ERR "mk_Preload_Data" "";

fun mk_Preload_Instruction(r,s,t) =
  Term.list_mk_comb(Preload_Instruction_tm,
    inst_list [bool,``:4``,``:addressing_mode2``] [r,s,t])
    |> mk_Miscellaneous
  handle HOL_ERR _ => raise ERR "mk_Preload_Instruction" "";

fun mk_Supervisor_Call t =
  Term.mk_comb(Supervisor_Call_tm, inst_word_alpha ``:24`` t)
    |> mk_Miscellaneous
  handle HOL_ERR _ => raise ERR "mk_Supervisor_Call" "";

fun mk_Secure_Monitor_Call t =
  Term.mk_comb(Secure_Monitor_Call_tm, inst_word_alpha ``:4`` t)
    |> mk_Miscellaneous
  handle HOL_ERR _ => raise ERR "mk_Secure_Monitor_Call" "";

fun mk_If_Then(r,s) =
  Term.list_mk_comb(If_Then_tm, inst_list [``:4``,``:4``] [r,s])
    |> mk_Miscellaneous
  handle HOL_ERR _ => raise ERR "mk_If_Then" "";

fun mk_Data_Synchronization_Barrier t =
  Term.mk_comb(Data_Synchronization_Barrier_tm, inst_word_alpha ``:4`` t)
    |> mk_Miscellaneous
  handle HOL_ERR _ => raise ERR "mk_Data_Synchronization_Barrier" "";

fun mk_Instruction_Synchronization_Barrier t =
  Term.mk_comb(Instruction_Synchronization_Barrier_tm, inst_word_alpha ``:4`` t)
    |> mk_Miscellaneous
  handle HOL_ERR _ => raise ERR "mk_Instruction_Synchronization_Barrier" "";

(* .. *)

fun mk_Coprocessor t =
  Term.mk_comb(Coprocessor_tm, inst [alpha |-> ``:coprocessor_instruction``] t)
  handle HOL_ERR _ => raise ERR "mk_Coprocessor" "";

fun mk_Coprocessor_Load (r,s,t,u,v,w,x,y) =
  Term.list_mk_comb(Coprocessor_Load_tm,
    inst_list [bool,bool,bool,bool,``:4``,``:4``,``:4``,``:8``]
              [r,s,t,u,v,w,x,y]) |> mk_Coprocessor
  handle HOL_ERR _ => raise ERR "mk_Coprocessor_Load" "";

fun mk_Coprocessor_Store (r,s,t,u,v,w,x,y) =
  Term.list_mk_comb(Coprocessor_Store_tm,
    inst_list [bool,bool,bool,bool,``:4``,``:4``,``:4``,``:8``]
              [r,s,t,u,v,w,x,y]) |> mk_Coprocessor
  handle HOL_ERR _ => raise ERR "mk_Coprocessor_Store" "";

fun mk_Coprocessor_Data_Processing (r,s,t,u,v,w) =
  Term.list_mk_comb(Coprocessor_Data_Processing_tm,
    inst_list [``:4``,``:4``,``:4``,``:4``,``:3``,``:4``]
              [r,s,t,u,v,w]) |> mk_Coprocessor
  handle HOL_ERR _ => raise ERR "mk_Coprocessor_Data_Processing" "";

fun mk_Coprocessor_Transfer (r,s,t,u,v,w,x) =
  Term.list_mk_comb(Coprocessor_Transfer_tm,
    inst_list [``:3``,bool,``:4``,``:4``,``:4``,``:3``,``:4``]
              [r,s,t,u,v,w,x]) |> mk_Coprocessor
  handle HOL_ERR _ => raise ERR "mk_Coprocessor_Transfer" "";

fun mk_Coprocessor_Transfer_Two (r,s,t,u,v,w) =
  Term.list_mk_comb(Coprocessor_Transfer_Two_tm,
    inst_list [bool,``:4``,``:4``,``:4``,``:4``,``:4``]
              [r,s,t,u,v,w]) |> mk_Coprocessor
  handle HOL_ERR _ => raise ERR "mk_Coprocessor_Transfer_Two" "";

(* ------------------------------------------------------------------------- *)

fun dest_op4 c e tm =
  case Lib.with_exn boolSyntax.strip_comb tm e of
    (t,[t1,t2,t3,t4]) => if Term.same_const t c then (t1,t2,t3,t4) else raise e
  | _ => raise e;

fun dest_op5 c e tm =
  case Lib.with_exn boolSyntax.strip_comb tm e of
    (t,[t1,t2,t3,t4,t5]) =>
      if Term.same_const t c then (t1,t2,t3,t4,t5) else raise e
  | _ => raise e;

fun dest_op6 c e tm =
  case Lib.with_exn boolSyntax.strip_comb tm e of
    (t,[t1,t2,t3,t4,t5,t6]) =>
      if Term.same_const t c then (t1,t2,t3,t4,t5,t6) else raise e
  | _ => raise e;

fun dest_op7 c e tm =
  case Lib.with_exn boolSyntax.strip_comb tm e of
    (t,[t1,t2,t3,t4,t5,t6,t7]) =>
      if Term.same_const t c then (t1,t2,t3,t4,t5,t6,t7) else raise e
  | _ => raise e;

fun dest_op8 c e tm =
  case Lib.with_exn boolSyntax.strip_comb tm e of
    (t,[t1,t2,t3,t4,t5,t6,t7,t8]) =>
      if Term.same_const t c then (t1,t2,t3,t4,t5,t6,t7,t8) else raise e
  | _ => raise e;

fun dest_op9 c e tm =
  case Lib.with_exn boolSyntax.strip_comb tm e of
    (t,[t1,t2,t3,t4,t5,t6,t7,t8,t9]) =>
      if Term.same_const t c then (t1,t2,t3,t4,t5,t6,t7,t8,t9) else raise e
  | _ => raise e;

(* .. *)

val dest_Mode1_immediate =
  HolKernel.dest_monop Mode1_immediate_tm (ERR "dest_Mode1_immediate" "");

val dest_Mode1_register =
  HolKernel.dest_triop Mode1_register_tm (ERR "dest_Mode1_register" "");

val dest_Mode1_register_shifted_register =
  HolKernel.dest_triop Mode1_register_shifted_register_tm
    (ERR "dest_Mode1_register_shifted_register" "");

val dest_Mode2_immediate =
  HolKernel.dest_monop Mode2_immediate_tm (ERR "dest_Mode2_immediate" "");

val dest_Mode2_register =
  HolKernel.dest_triop Mode2_register_tm (ERR "dest_Mode2_register" "");

val dest_Mode3_immediate =
  HolKernel.dest_monop Mode3_immediate_tm (ERR "dest_Mode3_immediate" "");

val dest_Mode3_register =
  HolKernel.dest_binop Mode3_register_tm (ERR "dest_Mode3_register" "");

val dest_Hint_debug =
  HolKernel.dest_monop Hint_debug_tm (ERR "dest_Hint_debug" "");

(* .. *)

val dest_Branch = HolKernel.dest_monop Branch_tm (ERR "dest_Branch" "");

val dest_Branch_Target =
  HolKernel.dest_monop Branch_Target_tm (ERR "dest_Branch_Target" "") o
  dest_Branch;

val dest_Branch_Exchange =
  HolKernel.dest_monop Branch_Exchange_tm (ERR "dest_Branch_Exchange" "") o
  dest_Branch;

val dest_Branch_Link_Exchange_Immediate =
  HolKernel.dest_triop Branch_Link_Exchange_Immediate_tm
    (ERR "dest_Branch_Link_Exchange_Immediate" "") o dest_Branch;

val dest_Branch_Link_Exchange_Register =
  HolKernel.dest_monop Branch_Link_Exchange_Register_tm
    (ERR "dest_Branch_Link_Exchange_Register" "") o dest_Branch;

val dest_Compare_Branch =
  HolKernel.dest_triop Compare_Branch_tm (ERR "dest_Compare_Branch" "") o
  dest_Branch;

val dest_Table_Branch_Byte =
  HolKernel.dest_triop Table_Branch_Byte_tm (ERR "dest_Table_Branch_Byte" "") o
  dest_Branch;

(* .. *)

val dest_DataProcessing =
  HolKernel.dest_monop DataProcessing_tm (ERR "dest_DataProcessing" "");

val dest_Data_Processing =
  dest_op5 Data_Processing_tm (ERR "dest_Data_Processing" "") o
  dest_DataProcessing;

val dest_Add_Sub =
  dest_op4 Add_Sub_tm (ERR "dest_Add_Sub" "") o dest_DataProcessing;

val dest_Move_Halfword =
  HolKernel.dest_triop Move_Halfword_tm (ERR "dest_Move_Halfword" "") o
  dest_DataProcessing;

val dest_Multiply =
  dest_op6 Multiply_tm (ERR "dest_Multiply" "") o dest_DataProcessing;

val dest_Multiply_Subtract =
  dest_op4 Multiply_Subtract_tm (ERR "dest_Multiply_Subtract" "") o
  dest_DataProcessing;

val dest_Signed_Halfword_Multiply =
  dest_op7 Signed_Halfword_Multiply_tm
    (ERR "dest_Signed_Halfword_Multiply" "") o dest_DataProcessing;

val dest_Signed_Multiply_Dual =
  dest_op6 Signed_Multiply_Dual_tm (ERR "dest_Signed_Multiply_Dual" "") o
  dest_DataProcessing;

val dest_Signed_Multiply_Long_Dual =
  dest_op6 Signed_Multiply_Dual_tm (ERR "dest_Signed_Multiply_Dual" "") o
  dest_DataProcessing;

val dest_Multiply_Long =
  dest_op7 Multiply_Long_tm (ERR "dest_Multiply_Long" "") o
  dest_DataProcessing;

val dest_Saturate =
  dest_op6 Saturate_tm (ERR "dest_Saturate" "") o
  dest_DataProcessing;

val dest_Saturate_16 =
  dest_op4 Saturate_16_tm (ERR "dest_Saturate_16" "") o
  dest_DataProcessing;

val dest_Saturating_Add_Subtract =
  dest_op4 Saturating_Add_Subtract_tm (ERR "dest_Saturating_Add_Subtract" "") o
  dest_DataProcessing;

val dest_Pack_Halfword =
  dest_op5 Pack_Halfword_tm (ERR "dest_Pack_Halfword" "") o
  dest_DataProcessing;

val dest_Extend_Byte =
  dest_op5 Extend_Byte_tm (ERR "dest_Extend_Byte" "") o
  dest_DataProcessing;

val dest_Extend_Byte_16 =
  dest_op5 Extend_Byte_16_tm (ERR "dest_Extend_Byte_16" "") o
  dest_DataProcessing;

val dest_Extend_Halfword =
  dest_op5 Extend_Halfword_tm (ERR "dest_Extend_Halfword" "") o
  dest_DataProcessing;

val dest_Bit_Field_Clear_Insert =
  dest_op4 Bit_Field_Clear_Insert_tm (ERR "dest_Bit_Field_Clear_Insert" "") o
  dest_DataProcessing;

val dest_Count_Leading_Zeroes =
  HolKernel.dest_binop
    Count_Leading_Zeroes_tm (ERR "dest_Count_Leading_Zeroes" "") o
  dest_DataProcessing;

val dest_Reverse_Bits =
  HolKernel.dest_binop Reverse_Bits_tm (ERR "dest_Reverse_Bits" "") o
  dest_DataProcessing;

val dest_Byte_Reverse_Word =
  HolKernel.dest_binop Byte_Reverse_Word_tm (ERR "dest_Byte_Reverse_Word" "") o
  dest_DataProcessing;

val dest_Bit_Field_Extract =
  dest_op5 Bit_Field_Extract_tm (ERR "dest_Bit_Field_Extract" "") o
  dest_DataProcessing;

val dest_Select_Bytes =
  HolKernel.dest_triop Select_Bytes_tm (ERR "dest_Select_Bytes" "") o
  dest_DataProcessing;

val dest_Parallel_Add_Subtract =
  dest_op5 Parallel_Add_Subtract_tm (ERR "dest_Parallel_Add_Subtract" "") o
  dest_DataProcessing;

val dest_Divide =
  dest_op4 Divide_tm (ERR "dest_Divide" "") o
  dest_DataProcessing;

val dest_Signed_Most_Significant_Multiply =
  dest_op5 Signed_Most_Significant_Multiply_tm
    (ERR "dest_Signed_Most_Significant_Multiply" "") o
  dest_DataProcessing;

val dest_Signed_Most_Significant_Multiply_Subtract =
  dest_op5 Signed_Most_Significant_Multiply_Subtract_tm
    (ERR "dest_Signed_Most_Significant_Multiply_Subtract" "") o
  dest_DataProcessing;

val dest_Multiply_Accumulate_Accumulate =
  dest_op4 Multiply_Accumulate_Accumulate_tm
    (ERR "dest_Multiply_Accumulate_Accumulate" "") o
  dest_DataProcessing;

val dest_Byte_Reverse_Packed_Halfword =
  HolKernel.dest_binop Byte_Reverse_Packed_Halfword_tm
    (ERR "dest_Byte_Reverse_Packed_Halfword" "") o
  dest_DataProcessing;

val dest_Byte_Reverse_Signed_Halfword =
  HolKernel.dest_binop Byte_Reverse_Signed_Halfword_tm
    (ERR "dest_Byte_Reverse_Signed_Halfword" "") o
  dest_DataProcessing;

val dest_Unsigned_Sum_Absolute_Differences =
  dest_op4 Unsigned_Sum_Absolute_Differences_tm
    (ERR "dest_Unsigned_Sum_Absolute_Differences" "") o
  dest_DataProcessing;

(* .. *)

val dest_StatusAccess =
  HolKernel.dest_monop StatusAccess_tm (ERR "dest_StatusAccess" "");

val dest_Status_to_Register =
  HolKernel.dest_binop
    Status_to_Register_tm (ERR "dest_Status_to_Register" "") o
  dest_StatusAccess;

val dest_Register_to_Status =
  HolKernel.dest_triop
    Register_to_Status_tm (ERR "dest_Register_to_Status" "") o
  dest_StatusAccess;

val dest_Immediate_to_Status =
  HolKernel.dest_triop
    Immediate_to_Status_tm (ERR "dest_Immediate_to_Status" "") o
  dest_StatusAccess;

val dest_Change_Processor_State =
  dest_op5 Change_Processor_State_tm (ERR "dest_Change_Processor_State" "") o
  dest_StatusAccess;

val dest_Set_Endianness =
  HolKernel.dest_monop Set_Endianness_tm (ERR "dest_Set_Endianness" "") o
  dest_StatusAccess;

(* .. *)

val dest_LoadStore =
  HolKernel.dest_monop LoadStore_tm (ERR "dest_LoadStore" "");

val dest_Load =
  dest_op8 Load_tm (ERR "dest_Load" "") o
  dest_LoadStore;

val dest_Store =
  dest_op8 Store_tm (ERR "dest_Store" "") o
  dest_LoadStore;

val dest_Load_Halfword =
  dest_op9 Load_Halfword_tm (ERR "dest_Load_Halfword" "") o
  dest_LoadStore;

val dest_Store_Halfword =
  dest_op7 Store_Halfword_tm (ERR "dest_Store_Halfword" "") o
  dest_LoadStore;

val dest_Load_Dual =
  dest_op7 Load_Dual_tm (ERR "dest_Load_Dual" "") o
  dest_LoadStore;

val dest_Store_Dual =
  dest_op7 Store_Dual_tm (ERR "dest_Store_Dual" "") o
  dest_LoadStore;

val dest_Load_Multiple =
  dest_op6 Load_Multiple_tm (ERR "dest_Load_Multiple" "") o
  dest_LoadStore;

val dest_Store_Multiple =
  dest_op6 Store_Multiple_tm (ERR "dest_Store_Multiple" "") o
  dest_LoadStore;

val dest_Load_Exclusive =
  HolKernel.dest_triop Load_Exclusive_tm (ERR "dest_Load_Exclusive" "") o
  dest_LoadStore;

val dest_Store_Exclusive =
  dest_op4 Store_Exclusive_tm (ERR "dest_Store_Exclusive" "") o
  dest_LoadStore;

val dest_Load_Exclusive_Doubleword =
  HolKernel.dest_triop Load_Exclusive_Doubleword_tm
    (ERR "dest_Load_Exclusive_Doubleword" "") o
  dest_LoadStore;

val dest_Store_Exclusive_Doubleword =
  dest_op4 Store_Exclusive_Doubleword_tm
    (ERR "dest_Store_Exclusive_Doubleword" "") o
  dest_LoadStore;

val dest_Load_Exclusive_Halfword =
  HolKernel.dest_binop Load_Exclusive_Halfword_tm
    (ERR "dest_Load_Exclusive_Halfword" "") o
  dest_LoadStore;

val dest_Store_Exclusive_Halfword =
  HolKernel.dest_triop Store_Exclusive_Halfword_tm
    (ERR "dest_Store_Exclusive_Halfword" "") o
  dest_LoadStore;

val dest_Load_Exclusive_Byte =
  HolKernel.dest_binop
    Load_Exclusive_Byte_tm (ERR "dest_Load_Exclusive_Byte" "") o
  dest_LoadStore;

val dest_Store_Exclusive_Byte =
  HolKernel.dest_triop
    Store_Exclusive_Byte_tm (ERR "dest_Store_Exclusive_Byte" "") o
  dest_LoadStore;

val dest_Store_Return_State =
  dest_op4 Store_Return_State_tm (ERR "dest_Store_Return_State" "") o
  dest_LoadStore;

val dest_Return_From_Exception =
  dest_op4 Return_From_Exception_tm (ERR "dest_Return_From_Exception" "") o
  dest_LoadStore;

(* .. *)

val dest_Miscellaneous =
  HolKernel.dest_monop Miscellaneous_tm (ERR "dest_Miscellaneous" "");

val dest_Hint =
  HolKernel.dest_monop Hint_tm (ERR "dest_Hint" "") o
  dest_Miscellaneous;

val dest_Breakpoint =
  HolKernel.dest_monop Breakpoint_tm (ERR "dest_Breakpoint" "") o
  dest_Miscellaneous;

val dest_Data_Memory_Barrier =
  HolKernel.dest_monop
    Data_Memory_Barrier_tm (ERR "dest_Data_Memory_Barrier" "") o
  dest_Miscellaneous;

val dest_Swap =
  dest_op4 Swap_tm (ERR "dest_Swap" "") o
  dest_Miscellaneous;

val dest_Preload_Data =
  dest_op4 Preload_Data_tm (ERR "dest_Preload_Data" "") o
  dest_Miscellaneous;

val dest_Preload_Instruction =
  HolKernel.dest_triop
    Preload_Instruction_tm (ERR "dest_Preload_Instruction" "") o
  dest_Miscellaneous;

val dest_Supervisor_Call =
  HolKernel.dest_monop Supervisor_Call_tm (ERR "dest_Supervisor_Call" "") o
  dest_Miscellaneous;

val dest_Secure_Monitor_Call =
  HolKernel.dest_monop
    Secure_Monitor_Call_tm (ERR "dest_Secure_Monitor_Call" "") o
  dest_Miscellaneous;

val dest_If_Then =
  HolKernel.dest_binop If_Then_tm (ERR "dest_If_Then" "") o
  dest_Miscellaneous;

val dest_Data_Synchronization_Barrier =
  HolKernel.dest_monop Data_Synchronization_Barrier_tm
    (ERR "dest_Data_Synchronization_Barrier" "") o
  dest_Miscellaneous;

val dest_Instruction_Synchronization_Barrier =
  HolKernel.dest_monop Instruction_Synchronization_Barrier_tm
    (ERR "dest_Instruction_Synchronization_Barrier" "") o
  dest_Miscellaneous;

(* .. *)

val dest_Coprocessor =
  HolKernel.dest_monop Coprocessor_tm (ERR "dest_Coprocessor" "");

val dest_Coprocessor_Load =
  dest_op8 Coprocessor_Load_tm (ERR "dest_Coprocessor_Load" "") o
  dest_Coprocessor;

val dest_Coprocessor_Store =
  dest_op8 Coprocessor_Store_tm (ERR "dest_Coprocessor_Store" "") o
  dest_Coprocessor;

val dest_Coprocessor_Data_Processing =
  dest_op6 Coprocessor_Data_Processing_tm
    (ERR "dest_Coprocessor_Data_Processing" "") o
  dest_Coprocessor;

val dest_Coprocessor_Transfer =
  dest_op7 Coprocessor_Transfer_tm (ERR "dest_Coprocessor_Transfer" "") o
  dest_Coprocessor;

val dest_Coprocessor_Transfer_Two =
  dest_op6 Coprocessor_Transfer_Two_tm
    (ERR "dest_Coprocessor_Transfer_Two" "") o
  dest_Coprocessor;

(* ------------------------------------------------------------------------- *)

val can = Lib.can

val is_Mode1_immediate                = can dest_Mode1_immediate
val is_Mode1_register                 = can dest_Mode1_register

val is_Mode1_register_shifted_register =
  can dest_Mode1_register_shifted_register

val is_Mode2_immediate                = can dest_Mode2_immediate
val is_Mode2_register                 = can dest_Mode2_register
val is_Mode3_immediate                = can dest_Mode3_immediate
val is_Mode3_register                 = can dest_Mode3_register
val is_Hint_debug                     = can dest_Hint_debug
val is_Branch                         = can dest_Branch
val is_Branch_Target                  = can dest_Branch_Target
val is_Branch_Exchange                = can dest_Branch_Exchange
val is_Branch_Link_Exchange_Immediate = can dest_Branch_Link_Exchange_Immediate
val is_Branch_Link_Exchange_Register  = can dest_Branch_Link_Exchange_Register
val is_Compare_Branch                 = can dest_Compare_Branch
val is_Table_Branch_Byte              = can dest_Table_Branch_Byte
val is_DataProcessing                 = can dest_DataProcessing
val is_Data_Processing                = can dest_Data_Processing
val is_Add_Sub                        = can dest_Add_Sub
val is_Move_Halfword                  = can dest_Move_Halfword
val is_Multiply                       = can dest_Multiply
val is_Multiply_Subtract              = can dest_Multiply_Subtract
val is_Signed_Halfword_Multiply       = can dest_Signed_Halfword_Multiply
val is_Signed_Multiply_Dual           = can dest_Signed_Multiply_Dual
val is_Signed_Multiply_Long_Dual      = can dest_Signed_Multiply_Long_Dual
val is_Multiply_Long                  = can dest_Multiply_Long
val is_Saturate                       = can dest_Saturate
val is_Saturate_16                    = can dest_Saturate_16
val is_Saturating_Add_Subtract        = can dest_Saturating_Add_Subtract
val is_Pack_Halfword                  = can dest_Pack_Halfword
val is_Extend_Byte                    = can dest_Extend_Byte
val is_Extend_Byte_16                 = can dest_Extend_Byte_16
val is_Extend_Halfword                = can dest_Extend_Halfword
val is_Bit_Field_Clear_Insert         = can dest_Bit_Field_Clear_Insert
val is_Count_Leading_Zeroes           = can dest_Count_Leading_Zeroes
val is_Reverse_Bits                   = can dest_Reverse_Bits
val is_Byte_Reverse_Word              = can dest_Byte_Reverse_Word
val is_Bit_Field_Extract              = can dest_Bit_Field_Extract
val is_Select_Bytes                   = can dest_Select_Bytes
val is_Parallel_Add_Subtract          = can dest_Parallel_Add_Subtract
val is_Divide                         = can dest_Divide
val is_Multiply_Accumulate_Accumulate = can dest_Multiply_Accumulate_Accumulate
val is_Byte_Reverse_Packed_Halfword   = can dest_Byte_Reverse_Packed_Halfword
val is_Byte_Reverse_Signed_Halfword   = can dest_Byte_Reverse_Signed_Halfword

val is_Signed_Most_Significant_Multiply =
  can dest_Signed_Most_Significant_Multiply

val is_Signed_Most_Significant_Multiply_Subtract =
  can dest_Signed_Most_Significant_Multiply_Subtract

val is_Unsigned_Sum_Absolute_Differences =
  can dest_Unsigned_Sum_Absolute_Differences

val is_StatusAccess                   = can dest_StatusAccess
val is_Status_to_Register             = can dest_Status_to_Register
val is_Register_to_Status             = can dest_Register_to_Status
val is_Immediate_to_Status            = can dest_Immediate_to_Status
val is_Change_Processor_State         = can dest_Change_Processor_State
val is_Set_Endianness                 = can dest_Set_Endianness
val is_LoadStore                      = can dest_LoadStore
val is_Load                           = can dest_Load
val is_Store                          = can dest_Store
val is_Load_Halfword                  = can dest_Load_Halfword
val is_Store_Halfword                 = can dest_Store_Halfword
val is_Load_Dual                      = can dest_Load_Dual
val is_Store_Dual                     = can dest_Store_Dual
val is_Load_Multiple                  = can dest_Load_Multiple
val is_Store_Multiple                 = can dest_Store_Multiple
val is_Load_Exclusive                 = can dest_Load_Exclusive
val is_Store_Exclusive                = can dest_Store_Exclusive
val is_Load_Exclusive_Doubleword      = can dest_Load_Exclusive_Doubleword
val is_Store_Exclusive_Doubleword     = can dest_Store_Exclusive_Doubleword
val is_Load_Exclusive_Halfword        = can dest_Load_Exclusive_Halfword
val is_Store_Exclusive_Halfword       = can dest_Store_Exclusive_Halfword
val is_Load_Exclusive_Byte            = can dest_Load_Exclusive_Byte
val is_Store_Exclusive_Byte           = can dest_Store_Exclusive_Byte
val is_Store_Return_State             = can dest_Store_Return_State
val is_Return_From_Exception          = can dest_Return_From_Exception
val is_Miscellaneous                  = can dest_Miscellaneous
val is_Hint                           = can dest_Hint
val is_Breakpoint                     = can dest_Breakpoint
val is_Data_Memory_Barrier            = can dest_Data_Memory_Barrier
val is_Swap                           = can dest_Swap
val is_Preload_Data                   = can dest_Preload_Data
val is_Preload_Instruction            = can dest_Preload_Instruction
val is_Supervisor_Call                = can dest_Supervisor_Call
val is_Secure_Monitor_Call            = can dest_Secure_Monitor_Call
val is_If_Then                        = can dest_If_Then
val is_Data_Synchronization_Barrier   = can dest_Data_Synchronization_Barrier

val is_Instruction_Synchronization_Barrier =
  can dest_Instruction_Synchronization_Barrier

val is_Coprocessor                    = can dest_Coprocessor
val is_Coprocessor_Load               = can dest_Coprocessor_Load
val is_Coprocessor_Store              = can dest_Coprocessor_Store
val is_Coprocessor_Data_Processing    = can dest_Coprocessor_Data_Processing
val is_Coprocessor_Transfer           = can dest_Coprocessor_Transfer
val is_Coprocessor_Transfer_Two       = can dest_Coprocessor_Transfer_Two

end
