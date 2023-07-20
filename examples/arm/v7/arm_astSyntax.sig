signature arm_astSyntax =
sig

  include Abbrev

  val Mode1_register_shifted_register_tm   : term
  val Mode1_immediate_tm                   : term
  val Mode1_register_tm                    : term
  val Mode2_immediate_tm                   : term
  val Mode2_register_tm                    : term
  val Mode3_immediate_tm                   : term
  val Mode3_register_tm                    : term
  val Parallel_normal_tm                   : term
  val Parallel_saturating_tm               : term
  val Parallel_halving_tm                  : term
  val Parallel_add_16_tm                   : term
  val Parallel_add_sub_exchange_tm         : term
  val Parallel_sub_add_exchange_tm         : term
  val Parallel_sub_16_tm                   : term
  val Parallel_add_8_tm                    : term
  val Parallel_sub_8_tm                    : term
  val Hint_nop_tm                          : term
  val Hint_yield_tm                        : term
  val Hint_wait_for_event_tm               : term
  val Hint_wait_for_interrupt_tm           : term
  val Hint_send_event_tm                   : term
  val Hint_debug_tm                        : term
  val Branch_Target_tm                     : term
  val Branch_Exchange_tm                   : term
  val Compare_Branch_tm                    : term
  val Table_Branch_Byte_tm                 : term
  val Check_Array_tm                       : term
  val Handler_Branch_Link_tm               : term
  val Handler_Branch_Link_Parameter_tm     : term
  val Handler_Branch_Parameter_tm          : term
  val Branch_Link_Exchange_Immediate_tm    : term
  val Branch_Link_Exchange_Register_tm     : term
  val Data_Processing_tm                   : term
  val Add_Sub_tm                           : term
  val Move_Halfword_tm                     : term
  val Multiply_tm                          : term
  val Multiply_Subtract_tm                 : term
  val Signed_Halfword_Multiply_tm          : term
  val Signed_Multiply_Dual_tm              : term
  val Signed_Multiply_Long_Dual_tm         : term
  val Multiply_Long_tm                     : term
  val Saturate_tm                          : term
  val Saturate_16_tm                       : term
  val Saturating_Add_Subtract_tm           : term
  val Pack_Halfword_tm                     : term
  val Extend_Byte_tm                       : term
  val Extend_Byte_16_tm                    : term
  val Extend_Halfword_tm                   : term
  val Bit_Field_Clear_Insert_tm            : term
  val Count_Leading_Zeroes_tm              : term
  val Reverse_Bits_tm                      : term
  val Byte_Reverse_Word_tm                 : term
  val Bit_Field_Extract_tm                 : term
  val Select_Bytes_tm                      : term
  val Parallel_Add_Subtract_tm             : term
  val Divide_tm                            : term
  val Signed_Most_Significant_Multiply_tm  : term
  val Signed_Most_Significant_Multiply_Subtract_tm : term
  val Multiply_Accumulate_Accumulate_tm    : term
  val Byte_Reverse_Packed_Halfword_tm      : term
  val Byte_Reverse_Signed_Halfword_tm      : term
  val Unsigned_Sum_Absolute_Differences_tm : term
  val Status_to_Register_tm                : term
  val Register_to_Status_tm                : term
  val Immediate_to_Status_tm               : term
  val Change_Processor_State_tm            : term
  val Set_Endianness_tm                    : term
  val Load_tm                              : term
  val Store_tm                             : term
  val Load_Halfword_tm                     : term
  val Store_Halfword_tm                    : term
  val Load_Dual_tm                         : term
  val Store_Dual_tm                        : term
  val Load_Multiple_tm                     : term
  val Store_Multiple_tm                    : term
  val Load_Exclusive_tm                    : term
  val Store_Exclusive_tm                   : term
  val Load_Exclusive_Doubleword_tm         : term
  val Store_Exclusive_Doubleword_tm        : term
  val Load_Exclusive_Halfword_tm           : term
  val Store_Exclusive_Halfword_tm          : term
  val Load_Exclusive_Byte_tm               : term
  val Store_Exclusive_Byte_tm              : term
  val Store_Return_State_tm                : term
  val Return_From_Exception_tm             : term
  val Hint_tm                              : term
  val Breakpoint_tm                        : term
  val Data_Memory_Barrier_tm               : term
  val Swap_tm                              : term
  val Preload_Data_tm                      : term
  val Preload_Instruction_tm               : term
  val Supervisor_Call_tm                   : term
  val Secure_Monitor_Call_tm               : term
  val Enterx_Leavex_tm                     : term
  val Clear_Exclusive_tm                   : term
  val If_Then_tm                           : term
  val Data_Synchronization_Barrier_tm      : term
  val Instruction_Synchronization_Barrier_tm : term
  val Coprocessor_Load_tm                  : term
  val Coprocessor_Store_tm                 : term
  val Coprocessor_Data_Processing_tm       : term
  val Coprocessor_Transfer_tm              : term
  val Coprocessor_Transfer_Two_tm          : term
  val Unpredictable_tm                     : term
  val Undefined_tm                         : term
  val Branch_tm                            : term
  val DataProcessing_tm                    : term
  val StatusAccess_tm                      : term
  val LoadStore_tm                         : term
  val Miscellaneous_tm                     : term
  val Coprocessor_tm                       : term

  val mk_Mode1_register_shifted_register   : term * term * term -> term
  val mk_Mode1_immediate                   : term -> term
  val mk_Mode1_register                    : term * term * term -> term
  val mk_Mode2_immediate                   : term -> term
  val mk_Mode2_register                    : term * term * term -> term
  val mk_Mode3_immediate                   : term -> term
  val mk_Mode3_register                    : term * term -> term
  val mk_Hint_debug                        : term -> term
  val mk_Branch_Target                     : term -> term
  val mk_Branch_Exchange                   : term -> term
  val mk_Compare_Branch                    : term * term * term -> term
  val mk_Table_Branch_Byte                 : term * term * term -> term
  val mk_Check_Array                       : term * term -> term
  val mk_Handler_Branch_Link               : term * term -> term
  val mk_Handler_Branch_Link_Parameter     : term * term -> term
  val mk_Handler_Branch_Parameter          : term * term -> term
  val mk_Branch_Link_Exchange_Immediate    : term * term * term -> term
  val mk_Branch_Link_Exchange_Register     : term -> term
  val mk_Data_Processing                   : term * term * term * term *
                                             term -> term
  val mk_Add_Sub                           : term * term * term * term -> term
  val mk_Move_Halfword                     : term * term * term -> term
  val mk_Multiply                          : term * term * term * term *
                                             term * term -> term
  val mk_Multiply_Subtract                 : term * term * term * term -> term
  val mk_Signed_Halfword_Multiply          : term * term * term * term *
                                             term * term * term -> term
  val mk_Signed_Multiply_Dual              : term * term * term * term *
                                             term * term -> term
  val mk_Signed_Multiply_Long_Dual         : term * term * term * term *
                                             term * term -> term
  val mk_Multiply_Long                     : term * term * term * term *
                                             term * term * term -> term
  val mk_Saturate                          : term * term * term * term *
                                             term * term -> term
  val mk_Saturate_16                       : term * term * term * term -> term
  val mk_Saturating_Add_Subtract           : term * term * term * term -> term
  val mk_Pack_Halfword                     : term * term * term * term *
                                             term -> term
  val mk_Extend_Byte                       : term * term * term * term *
                                             term -> term
  val mk_Extend_Byte_16                    : term * term * term * term *
                                             term -> term
  val mk_Extend_Halfword                   : term * term * term * term *
                                             term -> term
  val mk_Bit_Field_Clear_Insert            : term * term * term * term -> term
  val mk_Count_Leading_Zeroes              : term * term -> term
  val mk_Reverse_Bits                      : term * term -> term
  val mk_Byte_Reverse_Word                 : term * term -> term
  val mk_Bit_Field_Extract                 : term * term * term * term *
                                             term -> term
  val mk_Select_Bytes                      : term * term * term -> term
  val mk_Parallel_Add_Subtract             : term * term * term * term *
                                             term -> term
  val mk_Divide                            : term * term * term * term -> term
  val mk_Signed_Most_Significant_Multiply  : term * term * term * term *
                                             term -> term
  val mk_Signed_Most_Significant_Multiply_Subtract : term * term * term * term *
                                             term -> term
  val mk_Multiply_Accumulate_Accumulate    : term * term * term * term -> term
  val mk_Byte_Reverse_Packed_Halfword      : term * term -> term
  val mk_Byte_Reverse_Signed_Halfword      : term * term -> term
  val mk_Unsigned_Sum_Absolute_Differences : term * term * term * term -> term
  val mk_Status_to_Register                : term * term -> term
  val mk_Register_to_Status                : term * term * term -> term
  val mk_Immediate_to_Status               : term * term * term -> term
  val mk_Change_Processor_State            : term * term * term * term *
                                             term -> term
  val mk_Set_Endianness                    : term -> term
  val mk_Load                              : term * term * term * term * term *
                                             term * term * term -> term
  val mk_Store                             : term * term * term * term * term *
                                             term * term * term -> term
  val mk_Load_Halfword                     : term * term * term * term * term *
                                             term * term * term * term -> term
  val mk_Store_Halfword                    : term * term * term * term * term *
                                             term * term -> term
  val mk_Load_Dual                         : term * term * term * term *
                                             term * term * term -> term
  val mk_Store_Dual                        : term * term * term * term *
                                             term * term * term -> term
  val mk_Load_Multiple                     : term * term * term * term *
                                             term * term -> term
  val mk_Store_Multiple                    : term * term * term * term *
                                             term * term -> term
  val mk_Load_Exclusive                    : term * term * term -> term
  val mk_Store_Exclusive                   : term * term * term * term -> term
  val mk_Load_Exclusive_Doubleword         : term * term * term -> term
  val mk_Store_Exclusive_Doubleword        : term * term * term * term -> term
  val mk_Load_Exclusive_Halfword           : term * term -> term
  val mk_Store_Exclusive_Halfword          : term * term * term -> term
  val mk_Load_Exclusive_Byte               : term * term -> term
  val mk_Store_Exclusive_Byte              : term * term * term -> term
  val mk_Store_Return_State                : term * term * term * term -> term
  val mk_Return_From_Exception             : term * term * term * term -> term
  val mk_Hint                              : term -> term
  val mk_Breakpoint                        : term -> term
  val mk_Data_Memory_Barrier               : term -> term
  val mk_Swap                              : term * term * term * term -> term
  val mk_Preload_Data                      : term * term * term * term -> term
  val mk_Preload_Instruction               : term * term * term -> term
  val mk_Supervisor_Call                   : term -> term
  val mk_Secure_Monitor_Call               : term -> term
  val mk_Enterx_Leavex                     : term -> term
  val mk_If_Then                           : term * term -> term
  val mk_Data_Synchronization_Barrier      : term -> term
  val mk_Instruction_Synchronization_Barrier : term -> term
  val mk_Coprocessor_Load                  : term * term * term * term * term *
                                             term * term * term -> term
  val mk_Coprocessor_Store                 : term * term * term * term * term *
                                             term * term * term -> term
  val mk_Coprocessor_Data_Processing       : term * term * term * term *
                                             term * term -> term
  val mk_Coprocessor_Transfer              : term * term * term * term *
                                             term * term * term -> term
  val mk_Coprocessor_Transfer_Two          : term * term * term * term *
                                             term * term -> term
  val mk_Branch                            : term -> term
  val mk_DataProcessing                    : term -> term
  val mk_StatusAccess                      : term -> term
  val mk_LoadStore                         : term -> term
  val mk_Miscellaneous                     : term -> term
  val mk_Coprocessor                       : term -> term

  val dest_Mode1_register_shifted_register : term -> term * term * term
  val dest_Mode1_immediate                 : term -> term
  val dest_Mode1_register                  : term -> term * term * term
  val dest_Mode2_immediate                 : term -> term
  val dest_Mode2_register                  : term -> term * term * term
  val dest_Mode3_immediate                 : term -> term
  val dest_Mode3_register                  : term -> term * term
  val dest_Hint_debug                      : term -> term
  val dest_Branch_Target                   : term -> term
  val dest_Branch_Exchange                 : term -> term
  val dest_Compare_Branch                  : term -> term * term * term
  val dest_Table_Branch_Byte               : term -> term * term * term
  val dest_Check_Array                     : term -> term * term
  val dest_Handler_Branch_Link             : term -> term * term
  val dest_Handler_Branch_Link_Parameter   : term -> term * term
  val dest_Handler_Branch_Parameter        : term -> term * term
  val dest_Branch_Link_Exchange_Immediate  : term -> term * term * term
  val dest_Branch_Link_Exchange_Register   : term -> term
  val dest_Data_Processing                 : term -> term * term * term *
                                             term * term
  val dest_Add_Sub                         : term -> term * term * term * term
  val dest_Move_Halfword                   : term -> term * term * term
  val dest_Multiply                        : term -> term * term * term * term *
                                             term * term
  val dest_Multiply_Subtract               : term -> term * term * term * term
  val dest_Signed_Halfword_Multiply        : term -> term * term * term * term *
                                             term * term * term
  val dest_Signed_Multiply_Dual            : term -> term * term * term * term *
                                             term * term
  val dest_Signed_Multiply_Long_Dual       : term -> term * term * term * term *
                                             term * term
  val dest_Multiply_Long                   : term -> term * term * term * term *
                                             term * term * term
  val dest_Saturate                        : term -> term * term * term * term *
                                             term * term
  val dest_Saturate_16                     : term -> term * term * term * term
  val dest_Saturating_Add_Subtract         : term -> term * term * term * term
  val dest_Pack_Halfword                   : term -> term * term * term * term *
                                             term
  val dest_Extend_Byte                     : term -> term * term * term * term *
                                             term
  val dest_Extend_Byte_16                  : term -> term * term * term * term *
                                             term
  val dest_Extend_Halfword                 : term -> term * term * term * term *
                                             term
  val dest_Bit_Field_Clear_Insert          : term -> term * term * term * term
  val dest_Count_Leading_Zeroes            : term -> term * term
  val dest_Reverse_Bits                    : term -> term * term
  val dest_Byte_Reverse_Word               : term -> term * term
  val dest_Bit_Field_Extract               : term -> term * term * term * term *
                                             term
  val dest_Select_Bytes                    : term -> term * term * term
  val dest_Parallel_Add_Subtract           : term -> term * term * term * term *
                                             term
  val dest_Divide                          : term -> term * term * term * term
  val dest_Signed_Most_Significant_Multiply  : term -> term * term * term *
                                             term * term
  val dest_Signed_Most_Significant_Multiply_Subtract : term -> term * term *
                                             term * term * term
  val dest_Multiply_Accumulate_Accumulate  : term -> term * term * term * term
  val dest_Byte_Reverse_Packed_Halfword    : term -> term * term
  val dest_Byte_Reverse_Signed_Halfword    : term -> term * term
  val dest_Unsigned_Sum_Absolute_Differences : term -> term * term * term * term
  val dest_Status_to_Register              : term -> term * term
  val dest_Register_to_Status              : term -> term * term * term
  val dest_Immediate_to_Status             : term -> term * term * term
  val dest_Change_Processor_State          : term -> term * term * term * term *
                                             term
  val dest_Set_Endianness                  : term -> term
  val dest_Load                            : term -> term * term * term * term *
                                             term * term * term * term
  val dest_Store                           : term -> term * term * term * term *
                                             term * term * term * term
  val dest_Load_Halfword                   : term -> term * term * term * term *
                                             term * term * term * term * term
  val dest_Store_Halfword                  : term -> term * term * term * term *
                                             term * term * term
  val dest_Load_Dual                       : term -> term * term * term * term *
                                             term * term * term
  val dest_Store_Dual                      : term -> term * term * term * term *
                                             term * term * term
  val dest_Load_Multiple                   : term -> term * term * term * term *
                                             term * term
  val dest_Store_Multiple                  : term -> term * term * term * term *
                                             term * term
  val dest_Load_Exclusive                  : term -> term * term * term
  val dest_Store_Exclusive                 : term -> term * term * term * term
  val dest_Load_Exclusive_Doubleword       : term -> term * term * term
  val dest_Store_Exclusive_Doubleword      : term -> term * term * term * term
  val dest_Load_Exclusive_Halfword         : term -> term * term
  val dest_Store_Exclusive_Halfword        : term -> term * term * term
  val dest_Load_Exclusive_Byte             : term -> term * term
  val dest_Store_Exclusive_Byte            : term -> term * term * term
  val dest_Store_Return_State              : term -> term * term * term * term
  val dest_Return_From_Exception           : term -> term * term * term * term
  val dest_Hint                            : term -> term
  val dest_Breakpoint                      : term -> term
  val dest_Data_Memory_Barrier             : term -> term
  val dest_Swap                            : term -> term * term * term * term
  val dest_Preload_Data                    : term -> term * term * term * term
  val dest_Preload_Instruction             : term -> term * term * term
  val dest_Supervisor_Call                 : term -> term
  val dest_Secure_Monitor_Call             : term -> term
  val dest_Enterx_Leavex                   : term -> term
  val dest_If_Then                         : term -> term * term
  val dest_Data_Synchronization_Barrier    : term -> term
  val dest_Instruction_Synchronization_Barrier : term -> term
  val dest_Coprocessor_Load                : term -> term * term * term *
                                             term * term * term * term * term
  val dest_Coprocessor_Store               : term -> term * term * term *
                                             term * term * term * term * term
  val dest_Coprocessor_Data_Processing     : term -> term * term * term * term *
                                             term * term
  val dest_Coprocessor_Transfer            : term -> term * term * term * term *
                                             term * term * term
  val dest_Coprocessor_Transfer_Two        : term -> term * term * term * term *
                                             term * term
  val dest_Branch                          : term -> term
  val dest_DataProcessing                  : term -> term
  val dest_StatusAccess                    : term -> term
  val dest_LoadStore                       : term -> term
  val dest_Miscellaneous                   : term -> term
  val dest_Coprocessor                     : term -> term

  val is_Mode1_register_shifted_register   : term -> bool
  val is_Mode1_immediate                   : term -> bool
  val is_Mode1_register                    : term -> bool
  val is_Mode2_immediate                   : term -> bool
  val is_Mode2_register                    : term -> bool
  val is_Mode3_immediate                   : term -> bool
  val is_Mode3_register                    : term -> bool
  val is_Hint_debug                        : term -> bool
  val is_Branch_Target                     : term -> bool
  val is_Branch_Exchange                   : term -> bool
  val is_Compare_Branch                    : term -> bool
  val is_Table_Branch_Byte                 : term -> bool
  val is_Check_Array                       : term -> bool
  val is_Handler_Branch_Link               : term -> bool
  val is_Handler_Branch_Link_Parameter     : term -> bool
  val is_Handler_Branch_Parameter          : term -> bool
  val is_Branch_Link_Exchange_Immediate    : term -> bool
  val is_Branch_Link_Exchange_Register     : term -> bool
  val is_Data_Processing                   : term -> bool
  val is_Add_Sub                           : term -> bool
  val is_Move_Halfword                     : term -> bool
  val is_Multiply                          : term -> bool
  val is_Multiply_Subtract                 : term -> bool
  val is_Signed_Halfword_Multiply          : term -> bool
  val is_Signed_Multiply_Dual              : term -> bool
  val is_Signed_Multiply_Long_Dual         : term -> bool
  val is_Multiply_Long                     : term -> bool
  val is_Saturate                          : term -> bool
  val is_Saturate_16                       : term -> bool
  val is_Saturating_Add_Subtract           : term -> bool
  val is_Pack_Halfword                     : term -> bool
  val is_Extend_Byte                       : term -> bool
  val is_Extend_Byte_16                    : term -> bool
  val is_Extend_Halfword                   : term -> bool
  val is_Bit_Field_Clear_Insert            : term -> bool
  val is_Count_Leading_Zeroes              : term -> bool
  val is_Reverse_Bits                      : term -> bool
  val is_Byte_Reverse_Word                 : term -> bool
  val is_Bit_Field_Extract                 : term -> bool
  val is_Select_Bytes                      : term -> bool
  val is_Parallel_Add_Subtract             : term -> bool
  val is_Divide                            : term -> bool
  val is_Signed_Most_Significant_Multiply  : term -> bool
  val is_Signed_Most_Significant_Multiply_Subtract : term -> bool
  val is_Multiply_Accumulate_Accumulate    : term -> bool
  val is_Byte_Reverse_Packed_Halfword      : term -> bool
  val is_Byte_Reverse_Signed_Halfword      : term -> bool
  val is_Unsigned_Sum_Absolute_Differences : term -> bool
  val is_Status_to_Register                : term -> bool
  val is_Register_to_Status                : term -> bool
  val is_Immediate_to_Status               : term -> bool
  val is_Change_Processor_State            : term -> bool
  val is_Set_Endianness                    : term -> bool
  val is_Load                              : term -> bool
  val is_Store                             : term -> bool
  val is_Load_Halfword                     : term -> bool
  val is_Store_Halfword                    : term -> bool
  val is_Load_Dual                         : term -> bool
  val is_Store_Dual                        : term -> bool
  val is_Load_Multiple                     : term -> bool
  val is_Store_Multiple                    : term -> bool
  val is_Load_Exclusive                    : term -> bool
  val is_Store_Exclusive                   : term -> bool
  val is_Load_Exclusive_Doubleword         : term -> bool
  val is_Store_Exclusive_Doubleword        : term -> bool
  val is_Load_Exclusive_Halfword           : term -> bool
  val is_Store_Exclusive_Halfword          : term -> bool
  val is_Load_Exclusive_Byte               : term -> bool
  val is_Store_Exclusive_Byte              : term -> bool
  val is_Store_Return_State                : term -> bool
  val is_Return_From_Exception             : term -> bool
  val is_Hint                              : term -> bool
  val is_Breakpoint                        : term -> bool
  val is_Data_Memory_Barrier               : term -> bool
  val is_Swap                              : term -> bool
  val is_Preload_Data                      : term -> bool
  val is_Preload_Instruction               : term -> bool
  val is_Supervisor_Call                   : term -> bool
  val is_Secure_Monitor_Call               : term -> bool
  val is_If_Then                           : term -> bool
  val is_Data_Synchronization_Barrier      : term -> bool
  val is_Instruction_Synchronization_Barrier : term -> bool
  val is_Coprocessor_Load                  : term -> bool
  val is_Coprocessor_Store                 : term -> bool
  val is_Coprocessor_Data_Processing       : term -> bool
  val is_Coprocessor_Transfer              : term -> bool
  val is_Coprocessor_Transfer_Two          : term -> bool
  val is_Branch                            : term -> bool
  val is_DataProcessing                    : term -> bool
  val is_StatusAccess                      : term -> bool
  val is_LoadStore                         : term -> bool
  val is_Miscellaneous                     : term -> bool
  val is_Coprocessor                       : term -> bool

end
