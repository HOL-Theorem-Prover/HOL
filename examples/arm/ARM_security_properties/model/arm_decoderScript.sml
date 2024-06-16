(* ------------------------------------------------------------------------ *)
(*     ARM Machine Code Semantics                                           *)
(*     ==========================                                           *)
(*     Decode from machine code to the AST data type                        *)
(* ------------------------------------------------------------------------ *)

(* interactive use:
  app load ["arm_astTheory", "wordsLib"];
*)

open HolKernel boolLib bossLib Parse;

open arithmeticTheory bitTheory;
open arm_astTheory;

val _ = new_theory "arm_decoder";
val _ = ParseExtras.temp_loose_equality()

(* ------------------------------------------------------------------------ *)

val _ = numLib.temp_prefer_num();
val _ = wordsLib.prefer_word();

(* ------------------------------------------------------------------------ *)

val _ = type_abbrev_pp ("word1",  ``:1 word``);
val _ = type_abbrev_pp ("word10", ``:10 word``);
val _ = type_abbrev_pp ("word11", ``:11 word``);

val _ = temp_overload_on("DP",
         ``\opc setflags rn rd mode1.
              DataProcessing (Data_Processing opc setflags rn rd mode1)``);
val _ = temp_overload_on("IMM",``Mode1_immediate``);
val _ = temp_overload_on("REG",``Mode1_register``);
val _ = temp_overload_on("SHIFTED",``Mode1_register_shifted_register``);

val hint_decode_def = Define`
  hint_decode (w:word8) =
    case w
    of 0b000w => Hint_nop
     | 0b001w => Hint_yield
     | 0b010w => Hint_wait_for_event
     | 0b011w => Hint_wait_for_interrupt
     | 0b100w => Hint_send_event
     | _      => if (7 -- 4) w = 0b1111w then
                   Hint_debug (w2w w)
                 else
                   Hint_nop`;

val parallel_add_sub_decode_defs = TotalDefn.multiDefine`
  (parallel_add_sub_op1 (0b01w :word2) = Parallel_normal) /\
  (parallel_add_sub_op1 (0b10w :word2) = Parallel_saturating) /\
  (parallel_add_sub_op1 (0b11w :word2) = Parallel_halving) /\
  (parallel_add_sub_op2 (0b000w:word3) = Parallel_add_16) /\
  (parallel_add_sub_op2 (0b001w:word3) = Parallel_add_sub_exchange) /\
  (parallel_add_sub_op2 (0b010w:word3) = Parallel_sub_add_exchange) /\
  (parallel_add_sub_op2 (0b011w:word3) = Parallel_sub_16) /\
  (parallel_add_sub_op2 (0b100w:word3) = Parallel_add_8) /\
  (parallel_add_sub_op2 (0b111w:word3) = Parallel_sub_8) /\
  (parallel_add_sub_thumb_op2 (0b001w:word3) = Parallel_add_16) /\
  (parallel_add_sub_thumb_op2 (0b010w:word3) = Parallel_add_sub_exchange) /\
  (parallel_add_sub_thumb_op2 (0b110w:word3) = Parallel_sub_add_exchange) /\
  (parallel_add_sub_thumb_op2 (0b101w:word3) = Parallel_sub_16) /\
  (parallel_add_sub_thumb_op2 (0b000w:word3) = Parallel_add_8) /\
  (parallel_add_sub_thumb_op2 (0b100w:word3) = Parallel_sub_8) /\
  (parallel_add_sub_decode (a,b) =
    (parallel_add_sub_op1 a, parallel_add_sub_op2 b)) /\
  (parallel_add_sub_thumb_decode (a,b) =
    (parallel_add_sub_op1 (a + 0b01w), parallel_add_sub_thumb_op2 b))`;

val InITBlock_def = Define`
  InITBlock (IT:word8) = (3 -- 0) IT <> 0w`;

val LastInITBlock_def = Define`
  LastInITBlock (IT:word8) = ((3 -- 0) IT = 0b1000w)`;

(* ------------------------------------------------------------------------ *)

val arm_decode_def = zDefine`
  arm_decode v4 (ireg : word32) =
  let b n = ireg ' n
  and i2 n  = ( n + 1  >< n ) ireg : word2
  and i3 n  = ( n + 2  >< n ) ireg : word3
  and i4 n  = ( n + 3  >< n ) ireg : word4
  and i5 n  = ( n + 4  >< n ) ireg : word5
  and i8 n  = ( n + 7  >< n ) ireg : word8
  and i12 n = ( n + 11 >< n ) ireg : word12
  and i16 n = ( n + 15 >< n ) ireg : word16
  and i24 n = (   23   >< 0 ) ireg : word24 in
  let cond = i4 28 and r = i4
  in
   (cond,
    if cond = 15w then
      if v4 then
        Unpredictable
      else
        case (b 27,b 26,b 25,b 24,b 23,b 22,b 21,b 20,b 7,b 6,b 5,b 4)
        of (F, F , F , T , F , F , F , F,b7,b6, F,b4) =>
             (if b 16 then
                if ~b7 /\ ~b6 /\ ~b4 then
                  StatusAccess (Set_Endianness (b 9))
                else
                  Undefined
              else let m = b 17 and mode = i5 0 in
                if ~m /\ (mode <> 0w) then
                  Unpredictable
                else
                  StatusAccess
                    (Change_Processor_State (i2 18) (b 8) (b 7)
                       (b 6) (if m then SOME mode else NONE)))
         | (F, T , F , F ,b23, T , F , T,_7,_6,_5,_4) =>
              Miscellaneous
                (Preload_Instruction b23 (r 16) (Mode2_immediate (i12 0)))
         | (F, T , T , F ,b23, T , F , T,_7,_6,_5,_4) =>
              Miscellaneous
                (Preload_Instruction b23 (r 16)
                   (Mode2_register (i5 7) (i2 5) (r 0)))
         | (F, T , F , T , F , T , T , T, F, F, F, T) =>
              Miscellaneous Clear_Exclusive
         | (F, T , F , T , F , T , T , T, F, T, F, F) =>
              Miscellaneous (Data_Synchronization_Barrier (i4 0))
         | (F, T , F , T , F , T , T , T, F, T, F, T) =>
              Miscellaneous (Data_Memory_Barrier (i4 0))
         | (F, T , F , T , F , T , T , T, F, T, T, F) =>
              Miscellaneous (Instruction_Synchronization_Barrier (i4 0))
         | (F, T , F , T ,b23,b22, F , T,_7,_6,_5,_4) =>
              if ~b22 /\ (r 12 = 15w) then
                Undefined
              else
                Miscellaneous
                  (Preload_Data b23 (~b22) (r 16) (Mode2_immediate (i12 0)))
         | (F, T , T , T ,b23,b22, F , T,_7,_6,_5,_4) =>
              Miscellaneous
                (Preload_Data b23 (~b22) (r 16)
                   (Mode2_register (i5 7) (i2 5) (r 0)))
         | (F,_26,_25,_24,_23,_22,_21,_20,_7,_6,_5,_4) => Undefined
         | (T, F , F ,b24,b23, T ,b21, F ,_7,_6,_5,_4) =>
              LoadStore (Store_Return_State b24 b23 b21 (i5 0))
         | (T, F , F ,b24,b23, F ,b21, T ,_7,_6,_5,_4) =>
              LoadStore (Return_From_Exception b24 b23 b21 (r 16))
         | (T, F , F ,_24,_23,_22,_21,_20,_7,_6,_5,_4) => Undefined
         | (T, F , T ,b24,_23,_22,_21,_20,_7,_6,_5,_4) =>
              Branch (Branch_Link_Exchange_Immediate b24 F (i24 0))
         | (T,T,F, F , F , T , F ,b20,_7,_6,_5,_4) =>
              Coprocessor
                (Coprocessor_Transfer_Two b20 (r 16) (r 12) (i4 8) (i4 4) (r 0))
         | (T, T , F ,b24,_23,_22,_21, F ,_7,_6,_5,_4) =>
              Coprocessor
                (Coprocessor_Store b24 (b 23) (b 22) (b 21) (r 16) (r 12)
                   (i4 8) (i8 0))
         | (T, T , F ,b24,_23,_22,_21, T ,_7,_6,_5,_4) =>
              Coprocessor
                (Coprocessor_Load b24 (b 23) (b 22) (b 21) (r 16) (r 12) (i4 8)
                   (i8 0))
         | (T, T , T , F ,_23,_22,_21,_20,_7,_6,_5, F) =>
              Coprocessor
                (Coprocessor_Data_Processing (i4 20) (r 16) (r 12) (i4 8)
                   (i3 5) (r 0))
         | (T, T , T , F ,_23,_22,_21,_20,_7,_6,_5, T) =>
              Coprocessor
                (Coprocessor_Transfer (i3 21) (b 20) (r 16) (r 12) (i4 8)
                   (i3 5) (r 0))
         | (T,T,T,T,_23,_22,_21,_20,_7,_6,_5,_4) => Undefined
   else
     case (b 27,b 26,b 25,b 24,b 23,b 22,b 21,b 20,b 7,b 6,b 5,b 4)
     of (F,F,F, T , F ,b22, F , F , F, F, F, F) =>
           StatusAccess (Status_to_Register b22 (r 12))
      | (F,F,F, T , F ,b22, T , F , F, F, F, F) =>
           StatusAccess (Register_to_Status b22 (i4 16) (r 0))
      | (F,F,F, T , F , F , T , F , F, F, F, T) =>
           Branch (Branch_Exchange (r 0))
      | (F,F,F, T , F , T , T , F , F, F, F, T) =>
           DataProcessing (Count_Leading_Zeroes (r 12) (r 0))
      | (F,F,F, T , F , F , T , F , F, F, T, T) =>
           Branch (Branch_Link_Exchange_Register (r 0))
      | (F,F,F, T , F ,_22,_21, F , F, T, F, T) =>
           DataProcessing (Saturating_Add_Subtract (i2 21) (r 16) (r 12) (r 0))
      | (F,F,F, T , F , F , T , F , F, T, T, T) =>
           if cond = 14w then
             Miscellaneous (Breakpoint (i12 8 @@ i4 0))
           else
             Unpredictable
      | (F,F,F, T , F , T , T , F , F, T, T, T) =>
           Miscellaneous (Secure_Monitor_Call (i4 0))
      | (F,F,F, T , F ,_22,_21, F , T,b6,b5, F) =>
           DataProcessing
             (Signed_Halfword_Multiply (i2 21) b6 b5 (r 16) (r 12) (r 8) (r 0))
      | (F,F,F,_24,_23,_22,_21,b20,_7,_6,_5, F) =>
           DP (i4 21) b20 (r 16) (r 12) (REG (i5 7) (i2 5) (r 0))
      | (F,F,F,_24,_23,_22,_21,b20, F,_6,_5, T) =>
           DP (i4 21) b20 (r 16) (r 12) (SHIFTED (r 8) (i2 5) (r 0))
      | (F,F,F, F , F , F ,b21,b20, T, F, F, T) =>
           DataProcessing (Multiply b21 b20 (r 16) (r 12) (r 8) (r 0))
      | (F,F,F, F , F , T , F , F , T, F, F, T) =>
           DataProcessing
             (Multiply_Accumulate_Accumulate (r 16) (r 12) (r 8) (r 0))
      | (F,F,F, F , F , T , T , F , T, F, F, T) =>
           DataProcessing (Multiply_Subtract (r 16) (r 12) (r 8) (r 0))
      | (F,F,F, F , T ,b22,b21,b20, T, F, F, T) =>
           DataProcessing (Multiply_Long b22 b21 b20 (r 16) (r 12) (r 8) (r 0))
      | (F,F,F, T , F ,b22, F , F , T, F, F, T) =>
           Miscellaneous (Swap b22 (r 16) (r 12) (r 0))
      | (F,F,F, T , T , F , F , F , T, F, F, T) =>
           LoadStore (Store_Exclusive (r 16) (r 12) (r 0) 0w)
      | (F,F,F, T , T , F , F , T , T, F, F, T) =>
           LoadStore (Load_Exclusive (r 16) (r 12) 0w)
      | (F,F,F, T , T , F , T , F , T, F, F, T) =>
          (let rt = r 0 in
             LoadStore (Store_Exclusive_Doubleword (r 16) (r 12) rt (rt + 1w)))
      | (F,F,F, T , T , F , T , T , T, F, F, T) =>
          (let rt = r 12 in
             LoadStore (Load_Exclusive_Doubleword (r 16) rt (rt + 1w)))
      | (F,F,F, T , T , T , F , F , T, F, F, T) =>
           LoadStore (Store_Exclusive_Byte (r 16) (r 12) (r 0))
      | (F,F,F, T , T , T , F , T , T, F, F, T) =>
           LoadStore (Load_Exclusive_Byte (r 16) (r 12))
      | (F,F,F, T , T , T , T , F , T, F, F, T) =>
           LoadStore (Store_Exclusive_Halfword (r 16) (r 12) (r 0))
      | (F,F,F, T , T , T , T , T , T, F, F, T) =>
           LoadStore (Load_Exclusive_Halfword (r 16) (r 12))
      | (F,F,F,b24,b23, F ,b21, F , T, F, T, T) =>
           LoadStore (Store_Halfword b24 b23 b21 (~b24 /\ b21) (r 16) (r 12)
             (Mode3_register 0w (r 0)))
      | (F,F,F,b24,b23, F ,b21, T , T, F, T, T) =>
           LoadStore (Load_Halfword b24 b23 b21 F T (~b24 /\ b21) (r 16) (r 12)
             (Mode3_register 0w (r 0)))
      | (F,F,F,b24,b23, T ,b21, F , T, F, T, T) =>
           LoadStore (Store_Halfword b24 b23 b21 (~b24 /\ b21) (r 16) (r 12)
             (Mode3_immediate (i4 8 @@ i4 0)))
      | (F,F,F,b24,b23, T ,b21, T , T, F, T, T) =>
           LoadStore (Load_Halfword b24 b23 b21 F T (~b24 /\ b21) (r 16) (r 12)
             (Mode3_immediate (i4 8 @@ i4 0)))
      | (F,F,F,b24,b23, F ,b21, F , T, T, F, T) =>
          (let rt = r 12 in
             LoadStore (Load_Dual b24 b23 b21 (r 16) rt (rt + 1w)
               (Mode3_register 0w (r 0))))
      | (F,F,F,b24,b23, F ,b21, F , T, T, T, T) =>
          (let rt = r 12 in
             LoadStore (Store_Dual b24 b23 b21 (r 16) rt (rt + 1w)
               (Mode3_register 0w (r 0))))
      | (F,F,F,b24,b23, F ,b21, T , T, T,b5, T) =>
           LoadStore (Load_Halfword b24 b23 b21 T b5 (~b24 /\ b21) (r 16) (r 12)
             (Mode3_register 0w (r 0)))
      | (F,F,F,b24,b23, T ,b21, F , T, T, F, T) =>
          (let rt = r 12 in
             LoadStore (Load_Dual b24 b23 b21 (r 16) rt (rt + 1w)
               (Mode3_immediate (i4 8 @@ i4 0))))
      | (F,F,F,b24,b23, T ,b21, F , T, T, T, T) =>
          (let rt = r 12 in
             LoadStore (Store_Dual b24 b23 b21 (r 16) rt (rt + 1w)
               (Mode3_immediate (i4 8 @@ i4 0))))
      | (F,F,F,b24,b23, T ,b21, T , T, T,b5, T) =>
           LoadStore (Load_Halfword b24 b23 b21 T b5 (~b24 /\ b21) (r 16) (r 12)
             (Mode3_immediate (i4 8 @@ i4 0)))
      | (F,F,T, F , F , T , F , F ,_7,_6,_5,_4) =>
          (let rn = r 16 in
             if rn = 15w then
               DataProcessing (Add_Sub F rn (r 12) (i12 0))
             else
               DP 0b0010w F rn (r 12) (IMM (i12 0)))
      | (F,F,T, F , T , F , F , F ,_7,_6,_5,_4) =>
          (let rn = r 16 in
             if rn = 15w then
               DataProcessing (Add_Sub T rn (r 12) (i12 0))
             else
               DP 0b0100w F rn (r 12) (IMM (i12 0)))
      | (F,F,T, T , F ,b22, F , F ,_7,_6,_5,_4) =>
           DataProcessing (Move_Halfword b22 (r 12) (i4 16 @@ i12 0))
      | (F,F,T, T , F ,b22, T , F ,_7,_6,_5,_4) =>
           if ~b22 /\ (r 16 = 0w) then
             Miscellaneous (Hint (hint_decode (i8 0)))
           else
             StatusAccess (Immediate_to_Status b22 (i4 16) (i12 0))
      | (F,F,T, T , T , T , T ,b20,_7,_6,_5,_4) =>
           DP 0b1111w b20 0b1111w (r 12) (IMM (i12 0))
      | (F,F,T,_24,_23,_22,_21,b20,_7,_6,_5,_4) =>
           DP (i4 21) b20 (r 16) (r 12) (IMM (i12 0))
      | (F,T,F,b24,b23,b22,b21, F ,_7,_6,_5,_4) =>
           LoadStore (Store b24 b23 b22 b21 (~b24 /\ b21) (r 16) (r 12)
             (Mode2_immediate (i12 0)))
      | (F,T,F,b24,b23,b22,b21, T ,_7,_6,_5,_4) =>
           LoadStore (Load b24 b23 b22 b21 (~b24 /\ b21) (r 16) (r 12)
             (Mode2_immediate (i12 0)))
      | (F,T,T,b24,b23,b22,b21, F ,_7,_6,_5, F) =>
           LoadStore (Store b24 b23 b22 b21 (~b24 /\ b21) (r 16) (r 12)
             (Mode2_register (i5 7) (i2 5) (r 0)))
      | (F,T,T,b24,b23,b22,b21, T ,_7,_6,_5, F) =>
           LoadStore (Load b24 b23 b22 b21 (~b24 /\ b21) (r 16) (r 12)
             (Mode2_register (i5 7) (i2 5) (r 0)))
      | (F,T,T, F , F ,b22,_21,_20,_7,_6,_5, T) =>
          (let op1 = i2 20 and op2 = i3 5 in
             if op1 <> 0w /\ (op2 <+ 5w \/ (op2 = 7w)) then
               DataProcessing (Parallel_Add_Subtract b22
                 (parallel_add_sub_decode (op1,op2)) (r 16) (r 12) (r 0))
             else
               Undefined)
      | (F,T,T, F , T , F , F , F ,_7,b6, F, T) =>
           DataProcessing (Pack_Halfword (r 16) (r 12) (i5 7) b6 (r 0))
      | (F,T,T, F , T , F , F , F , T, F, T, T) =>
           DataProcessing (Select_Bytes (r 16) (r 12) (r 0))
      | (F,T,T, F , T ,b22, F , F , F, T, T, T) =>
           DataProcessing (Extend_Byte_16 b22 (r 16) (r 12) (i2 10) (r 0))
      | (F,T,T, F , T ,b22, T ,_20,_7,b6, F, T) =>
           DataProcessing (Saturate b22 (i5 16) (r 12) (i5 7) b6 (r 0))
      | (F,T,T, F , T ,b22, T , F , F, F, T, T) =>
           DataProcessing (Saturate_16 b22 (i4 16) (r 12) (r 0))
      | (F,T,T, F , T ,b22, T , F , F, T, T, T) =>
           DataProcessing (Extend_Byte b22 (r 16) (r 12) (i2 10) (r 0))
      | (F,T,T, F , T , F , T , T , F, F, T, T) =>
           DataProcessing (Byte_Reverse_Word (r 12) (r 0))
      | (F,T,T, F , T ,b22, T , T , F, T, T, T) =>
           DataProcessing (Extend_Halfword b22 (r 16) (r 12) (i2 10) (r 0))
      | (F,T,T, F , T , F , T , T , T, F, T, T) =>
           DataProcessing (Byte_Reverse_Packed_Halfword (r 12) (r 0))
      | (F,T,T, F , T , T , T , T , F, F, T, T) =>
           DataProcessing (Reverse_Bits (r 12) (r 0))
      | (F,T,T, F , T , T , T , T , T, F, T, T) =>
           DataProcessing (Byte_Reverse_Signed_Halfword (r 12) (r 0))
      | (F,T,T, T , F , F , F , F , F,b6,b5, T) =>
           DataProcessing (Signed_Multiply_Dual (r 16) (r 12) (r 8) b6 b5 (r 0))
      | (F,T,T, T , F , T , F , F , F,b6,b5, T) =>
           DataProcessing
             (Signed_Multiply_Long_Dual (r 16) (r 12) (r 8) b6 b5 (r 0))
      | (F,T,T, T , F , T , F , T , F, F,b5, T) =>
           DataProcessing
             (Signed_Most_Significant_Multiply (r 16) (r 12) (r 8) b5 (r 0))
      | (F,T,T, T , F , T , F , T , T, T,b5, T) =>
           DataProcessing (Signed_Most_Significant_Multiply_Subtract (r 16)
             (r 12) (r 8) b5 (r 0))
      | (F,T,T, T , T , F , F , F , F, F, F, T) =>
           DataProcessing (Unsigned_Sum_Absolute_Differences (r 16) (r 12)
             (r 8) (r 0))
      | (F,T,T, T , T ,b22, T ,b20,b7, T, F, T) =>
           DataProcessing (Bit_Field_Extract b22 (i5 16) (r 12) (i5 7) (r 0))
      | (F,T,T, T , T , T , F ,b20,b7, F, F, T) =>
           DataProcessing (Bit_Field_Clear_Insert (i5 16) (r 12) (i5 7) (r 0))
      | (F,T,T,_24,_23,_22,_21,_20,_7,_6,_5, T) =>
           Undefined
      | (T,F,F,b24,b23,b22,b21, F ,_7,_6,_5,_4) =>
           LoadStore (Store_Multiple b24 b23 b22 b21 (r 16) (i16 0))
      | (T,F,F,b24,b23,b22,b21, T ,_7,_6,_5,_4) =>
           LoadStore (Load_Multiple b24 b23 b22 b21 (r 16) (i16 0))
      | (T,F,T, F ,_23,_22,_21,_20,_7,_6,_5,_4) =>
           Branch (Branch_Target (i24 0))
      | (T,F,T, T ,_23,_22,_21,_20,_7,_6,_5,_4) =>
           Branch (Branch_Link_Exchange_Immediate T T (i24 0))
      | (T,T,F, F , F , T , F ,b20,_7,_6,_5,_4) =>
           Coprocessor
             (Coprocessor_Transfer_Two b20 (r 16) (r 12) (i4 8) (i4 4) (r 0))
      | (T,T,F,b24,b23,b22,b21, F ,_7,_6,_5,_4) =>
           Coprocessor (Coprocessor_Store b24 b23 b22 b21 (r 16) (r 12) (i4 8)
             (i8 0))
      | (T,T,F,b24,b23,b22,b21, T ,_7,_6,_5,_4) =>
           Coprocessor (Coprocessor_Load b24 b23 b22 b21 (r 16) (r 12) (i4 8)
             (i8 0))
      | (T,T,T, F ,_23,_22,_21,_20,_7,_6,_5, F) =>
           Coprocessor (Coprocessor_Data_Processing (i4 20) (r 16) (r 12)
             (i4 8) (i3 5) (r 0))
      | (T,T,T, F ,_23,_22,_21,b20,_7,_6,_5, T) =>
           Coprocessor (Coprocessor_Transfer (i3 21) b20 (r 16) (r 12) (i4 8)
             (i3 5) (r 0))
      | (T,T,T, T ,_23,_22,_21,_20,_7,_6,_5,_4) =>
           Miscellaneous (Supervisor_Call (i24 0))
      | __ => Undefined)`;

(* ------------------------------------------------------------------------ *)

val thumb_decode_def = zDefine`
  thumb_decode arch IT (ireg : word16) =
    let IT = if arch IN thumb2_support then IT else 0w in
    let b n = ireg ' n
    and r n  = ( n + 2  >< n ) ireg : word4
    and r4 n = ( n + 3  >< n ) ireg : word4
    and InITBlock = InITBlock IT
    and LastInITBlock = LastInITBlock IT
    in
     ((let cond = r4 8 in
        if (15 >< 12) ireg <> (13w:word4) \/ cond IN {14w; 15w} then
          if IT = 0w then 0b1110w else (7 >< 4) IT
        else
          cond),
      case (b 15,b 14,b 13,b 12,b 11,b 10,b 9,b 8,b 7,b 6)
      of (F,F,F, T , T , F , F,_8,_7,_6) => (* ADD(3) *)
           DP 0b0100w (~InITBlock) (r 3) (r 0) (REG 0w 0w (r 6))
       | (F,F,F, T , T , F , T,_8,_7,_6) => (* SUB(3) *)
           DP 0b0010w (~InITBlock) (r 3) (r 0) (REG 0w 0w (r 6))
       | (F,F,F, T , T , T , F,_8,_7,_6) => (* ADD(1) *)
           DP 0b0100w (~InITBlock) (r 3) (r 0) (IMM ((8 >< 6) ireg))
       | (F,F,F, T , T , T , T,_8,_7,_6) => (* SUB(1) *)
           DP 0b0010w (~InITBlock) (r 3) (r 0) (IMM ((8 >< 6) ireg))
       | (F,F,F,b12,b11,_10,_9,_8,_7,_6) => (* LSL(1), LSR(1), ASR(1) *)
           DP 0b1101w (~InITBlock) 0w (r 0)
              (REG ((10 >< 6) ireg) ((12 >< 11) ireg) (r 3))
       | (F,F,T, F , F ,_10,_9,_8,_7,_6) => (* MOV(1) *)
           DP 0b1101w (~InITBlock) 0w (r 8) (IMM ((7 >< 0) ireg))
       | (F,F,T, F , T ,_10,_9,_8,_7,_6) => (* CMP(1) *)
           DP 0b1010w T (r 8) 0w (IMM ((7 >< 0) ireg))
       | (F,F,T, T , F ,_10,_9,_8,_7,_6) => (* ADD(2) *)
           DP 0b0100w (~InITBlock) (r 8) (r 8) (IMM ((7 >< 0) ireg))
       | (F,F,T, T , T ,_10,_9,_8,_7,_6) => (* SUB(2) *)
           DP 0b0010w (~InITBlock) (r 8) (r 8) (IMM ((7 >< 0) ireg))
       | (F,T,F, F , F , F , F, F, F, F) => (* AND *)
           DP 0b0000w (~InITBlock) (r 0) (r 0) (REG 0w 0w (r 3))
       | (F,T,F, F , F , F , F, F, F, T) => (* EOR *)
           DP 0b0001w (~InITBlock) (r 0) (r 0) (REG 0w 0w (r 3))
       | (F,T,F, F , F , F , F, F, T, F) => (* LSL(2) *)
           DP 0b1101w (~InITBlock) 0w (r 0) (SHIFTED (r 3) 0b00w (r 0))
       | (F,T,F, F , F , F , F, F, T, T) => (* LSR(2) *)
           DP 0b1101w (~InITBlock) 0w (r 0) (SHIFTED (r 3) 0b01w (r 0))
       | (F,T,F, F , F , F , F, T, F, F) => (* ASR(2) *)
           DP 0b1101w (~InITBlock) 0w (r 0) (SHIFTED (r 3) 0b10w (r 0))
       | (F,T,F, F , F , F , F, T, F, T) => (* ADC *)
           DP 0b0101w (~InITBlock) (r 0) (r 0) (REG 0w 0w (r 3))
       | (F,T,F, F , F , F , F, T, T, F) => (* SBC *)
           DP 0b0110w (~InITBlock) (r 0) (r 0) (REG 0w 0w (r 3))
       | (F,T,F, F , F , F , F, T, T, T) => (* ROR *)
           DP 0b1101w (~InITBlock) 0w (r 0) (SHIFTED (r 3) 0b11w (r 0))
       | (F,T,F, F , F , F , T, F, F, F) => (* TST *)
           DP 0b1000w T (r 0) 0w (REG 0w 0w (r 3))
       | (F,T,F, F , F , F , T, F, F, T) => (* RSB *)
           DP 0b0011w (~InITBlock) (r 3) (r 0) (IMM 0w)
       | (F,T,F, F , F , F , T, F, T, F) => (* CMP(2) *)
           DP 0b1010w T (r 0) 0w (REG 0w 0w (r 3))
       | (F,T,F, F , F , F , T, F, T, T) => (* CMN *)
           DP 0b1011w T (r 0) 0w (REG 0w 0w (r 3))
       | (F,T,F, F , F , F , T, T, F, F) => (* ORR *)
           DP 0b1100w (~InITBlock) (r 0) (r 0) (REG 0w 0w (r 3))
       | (F,T,F, F , F , F , T, T, F, T) => (* MUL *)
           DataProcessing (Multiply F (~InITBlock) (r 0) 0w (r 0) (r 3))
       | (F,T,F, F , F , F , T, T, T, F) => (* BIC *)
           DP 0b1110w (~InITBlock) (r 0) (r 0) (REG 0w 0w (r 3))
       | (F,T,F, F , F , F , T, T, T, T) => (* MVN *)
           DP 0b1111w (~InITBlock) 0w (r 0) (REG 0w 0w (r 3))
       | (F,T,F, F , F , T , F, F,b7,b6) => (* ADD(4) *)
          (let rdn = (3 :+ b7) (r 0) and rm = r4 3 in
             if ~b7 /\ ~b6 /\ arch NOTIN thumb2_support \/
                (rdn = 15w) /\ ((rm = 15w) \/ InITBlock /\ ~LastInITBlock)
             then
               Unpredictable
             else
               DP 0b0100w F rdn rdn (REG 0w 0w rm))
       | (F,T,F, F , F , T , F, T, F, F) =>
           Unpredictable
       | (F,T,F, F , F , T , F, T,b7,_6) => (* CMP(3) *)
           DP 0b1010w T ((3 :+ b7) (r 0)) 0w (REG 0w 0w (r4 3))
       | (F,T,F, F , F , T , T, F,b7,b6) => (* MOV(3) *)
          (let rd = (3 :+ b7) (r 0) in
             if ~b7 /\ ~b6 /\ version_number arch < 6 \/
                (rd = 15w) /\ InITBlock /\ ~LastInITBlock
             then
               Unpredictable
             else
               DP 0b1101w F 0w rd (REG 0w 0w (r4 3)))
       | (F,T,F, F , F , T , T, T, F,_6) => (* BX *)
           if InITBlock /\ ~LastInITBlock then
             Unpredictable
           else
             Branch (Branch_Exchange (r4 3))
       | (F,T,F, F , F , T , T, T, T,_6) => (* BLX(2) *)
           if InITBlock /\ ~LastInITBlock then
             Unpredictable
           else
             Branch (Branch_Link_Exchange_Register (r4 3))
       | (F,T,F, F , T ,_10,_9,_8,_7,_6) => (* LDR(3) *)
           LoadStore (Load T T F F F 15w (r 8)
             (Mode2_immediate (((7 >< 0) ireg) << 2)))
       | (F,T,F, T , F , F , F,_8,_7,_6) => (* STR(2) *)
           LoadStore (Store T T F F F (r 3) (r 0) (Mode2_register 0w 0w (r 6)))
       | (F,T,F, T , F , F , T,_8,_7,_6) => (* STRH(2) *)
           LoadStore (Store_Halfword T T F F (r 3) (r 0)
             (Mode3_register 0w (r 6)))
       | (F,T,F, T , F , T , F,_8,_7,_6) => (* STRB(2) *)
           LoadStore (Store T T T F F (r 3) (r 0) (Mode2_register 0w 0w (r 6)))
       | (F,T,F, T , F , T , T,_8,_7,_6) => (* LDRSB *)
           LoadStore (Load_Halfword T T F T F F (r 3) (r 0)
             (Mode3_register 0w (r 6)))
       | (F,T,F, T , T , F , F,_8,_7,_6) => (* LDR(2) *)
           LoadStore (Load T T F F F (r 3) (r 0) (Mode2_register 0w 0w (r 6)))
       | (F,T,F, T , T , F , T,_8,_7,_6) => (* LDRH(2) *)
           LoadStore (Load_Halfword T T F F T F (r 3) (r 0)
             (Mode3_register 0w (r 6)))
       | (F,T,F, T , T , T , F,_8,_7,_6) => (* LDRB(2) *)
           LoadStore (Load T T T F F (r 3) (r 0) (Mode2_register 0w 0w (r 6)))
       | (F,T,F, T , T , T , T,_8,_7,_6) => (* LDRSH *)
           LoadStore (Load_Halfword T T F T T F (r 3) (r 0)
             (Mode3_register 0w (r 6)))
       | (F,T,T, F , F ,_10,_9,_8,_7,_6) => (* STR(1) *)
           LoadStore (Store T T F F F (r 3) (r 0)
             (Mode2_immediate (((10 >< 6) ireg) << 2)))
       | (F,T,T, F , T ,_10,_9,_8,_7,_6) => (* LDR(1) *)
           LoadStore (Load T T F F F (r 3) (r 0)
             (Mode2_immediate (((10 >< 6) ireg) << 2)))
       | (F,T,T, T , F ,_10,_9,_8,_7,_6) => (* STRB(1) *)
           LoadStore (Store T T T F F (r 3) (r 0)
             (Mode2_immediate ((10 >< 6) ireg)))
       | (F,T,T, T , T ,_10,_9,_8,_7,_6) => (* LDRB(1) *)
           LoadStore (Load T T T F F (r 3) (r 0)
             (Mode2_immediate ((10 >< 6) ireg)))
       | (T,F,F, F , F ,_10,_9,_8,_7,_6) => (* STRH(1) *)
           LoadStore (Store_Halfword T T F F (r 3) (r 0)
             (Mode3_immediate (((10 >< 6) ireg) << 1)))
       | (T,F,F, F , T ,_10,_9,_8,_7,_6) => (* LDRH(1) *)
           LoadStore (Load_Halfword T T F F T F (r 3) (r 0)
             (Mode3_immediate (((10 >< 6) ireg) << 1)))
       | (T,F,F, T , F ,_10,_9,_8,_7,_6) => (* STR(3) *)
           LoadStore (Store T T F F F 13w (r 8)
             (Mode2_immediate (((7 >< 0) ireg) << 2)))
       | (T,F,F, T , T ,_10,_9,_8,_7,_6) => (* LDR(4) *)
           LoadStore (Load T T F F F 13w (r 8)
             (Mode2_immediate (((7 >< 0) ireg) << 2)))
       | (T,F,T, F , F ,_10,_9,_8,_7,_6) => (* ADD(5) *)
           DataProcessing (Add_Sub T 15w (r 8) (((7 >< 0) ireg) << 2))
       | (T,F,T, F , T ,_10,_9,_8,_7,_6) => (* ADD(6) *)
           DP 0b0100w F 13w (r 8) (IMM (0b1111_0000_0000w || ((7 >< 0) ireg)))
       | (T,F,T, T , F , F , F, F, F,_6) => (* ADD(7) *)
           DP 0b0100w F 13w 13w (IMM (0b1111_0000_0000w || ((6 >< 0) ireg)))
       | (T,F,T, T , F , F , F, F, T,_6) => (* SUB(4) *)
           DP 0b0010w F 13w 13w (IMM (0b1111_0000_0000w || ((6 >< 0) ireg)))
       | (T,F,T, T ,b11, F ,b9, T,_7,_6) =>
           if InITBlock then
             Unpredictable
           else
             Branch
               (Compare_Branch b11 ((5 :+ b9) ((7 >< 3) ireg)) ((2 >< 0) ireg))
       | (T,F,T, T , F , F , T, F,b7, F) =>
           DataProcessing (Extend_Halfword b7 15w (r 0) 0w (r 3))
       | (T,F,T, T , F , F , T, F,b7, T) =>
           DataProcessing (Extend_Byte b7 15w (r 0) 0w (r 3))
       | (T,F,T, T , F , T , F,b8,_7,_6) => (* PUSH *)
           LoadStore (Store_Multiple T F F T 13w ((14 :+ b8) ((7 >< 0) ireg)))
       | (T,F,T, T , T , F , T, F, F, F) =>
           DataProcessing (Byte_Reverse_Word (r 0) (r 3))
       | (T,F,T, T , T , F , T, F, F, T) =>
           DataProcessing (Byte_Reverse_Packed_Halfword (r 0) (r 3))
       | (T,F,T, T , T , F , T, F, T, T) =>
           DataProcessing (Byte_Reverse_Signed_Halfword (r 0) (r 3))
       | (T,F,T, T , T , T , F,b8,_7,_6) => (* POP *)
           if b8 /\ InITBlock /\ ~LastInITBlock then
             Unpredictable
           else
             LoadStore (Load_Multiple F T F T 13w ((15 :+ b8) ((7 >< 0) ireg)))
       | (T,F,T, T , F , T , T, F, F, T) =>
           if b 5 then
             StatusAccess
               (Change_Processor_State (if b 4 then 0b11w else 0b10w)
                  (b 2) (b 1) (b 0) NONE)
           else
             StatusAccess (Set_Endianness (b 3))
       | (T,F,T, T , T , T , T, F,_7,_6) => (* BKPT *)
           Miscellaneous (Breakpoint ((7 >< 0) ireg))
       | (T,F,T, T , T , T , T, T,_7,_6) =>
          (let mask = r4 0 in
             if mask = 0w then
               Miscellaneous (Hint (hint_decode ((7 >< 4) ireg)))
             else
               Miscellaneous (If_Then (r4 4) mask))
       | (T,T,F, F , F ,b10,b9,b8,_7,_6) => (* STMIA *)
           LoadStore (Store_Multiple F T F T (r 8) ((7 >< 0) ireg))
       | (T,T,F, F , T ,b10,b9,b8,b7,_6) => (* LDMIA *)
          (let rn = r 8 in
           let wback = ~(ireg ' (w2n rn)) in
             LoadStore (Load_Multiple F T F wback rn ((7 >< 0) ireg)))
       | (T,T,F, T , T , T , T, F,_7,_6) =>
           Undefined
       | (T,T,F, T , T , T , T, T,_7,_6) => (* SVC *)
           Miscellaneous (Supervisor_Call ((7 >< 0) ireg))
       | (T,T,F, T ,_11,_10,_9,_8,_7,_6) => (* B(1) *)
           if InITBlock then
             Unpredictable
           else
             Branch (Branch_Target (sw2sw ((7 >< 0) ireg : word8)))
       | (T,T,T, F , F ,_10,_9,_8,_7,_6) => (* B(2) *)
           if InITBlock /\ ~LastInITBlock then
             Unpredictable
           else
             Branch (Branch_Target (sw2sw ((10 >< 0) ireg : word11)))
       | _ => Undefined)`;

val thumbee_decode_def = zDefine`
  thumbee_decode arch IT (ireg : word16) =
    let b n = ireg ' n
    and r n  = ( n + 2  >< n ) ireg : word4
    and r4 n = ( n + 3  >< n ) ireg : word4
    and cond = if IT = 0w then 0b1110w else (7 >< 4) IT
    in
      case (b 15,b 14,b 13,b 12,b 11,b 10,b 9,b 8)
      of (F,T,F,T,F,F,F,_) => (* STR(2) *)
           (Encoding_ThumbEE, cond,
            LoadStore
              (Store T T F F F (r 3) (r 0) (Mode2_register 2w 0w (r 6))))
       | (F,T,F,T,F,F,T,_) => (* STRH(2) *)
           (Encoding_ThumbEE, cond,
            LoadStore
              (Store_Halfword T T F F (r 3) (r 0) (Mode3_register 1w (r 6))))
       | (F,T,F,T,T,F,F,_) => (* LDR(2) *)
           (Encoding_ThumbEE, cond,
            LoadStore (Load T T F F F (r 3) (r 0) (Mode2_register 2w 0w (r 6))))
       | (F,T,F,T,T,F,T,_) => (* LDRH(2) *)
           (Encoding_ThumbEE, cond,
            LoadStore
              (Load_Halfword T T F F T F (r 3) (r 0) (Mode3_register 1w (r 6))))
       | (F,T,F,T,T,T,T,_) => (* LDRSH *)
           (Encoding_ThumbEE, cond,
            LoadStore
              (Load_Halfword T T F T T F (r 3) (r 0) (Mode3_register 1w (r 6))))
       | (T,T,F,F,F,F,F,F) =>
           (Encoding_ThumbEE, cond,
            if InITBlock IT /\ ~LastInITBlock IT then
              Unpredictable
            else
              Branch (Handler_Branch_Parameter ((7 >< 5) ireg) ((4 >< 0) ireg)))
       | (T,T,F,F,F,F,F,T) =>
           (Encoding_ThumbEE, cond, Undefined)
       | (T,T,F,F,F,F,T,_) =>
           (Encoding_ThumbEE, cond,
            if InITBlock IT /\ ~LastInITBlock IT then
              Unpredictable
            else
              Branch (Handler_Branch_Link (b 8) ((7 >< 0) ireg)))
       | (T,T,F,F,F,T,_,_) =>
           (Encoding_ThumbEE, cond,
            if InITBlock IT /\ ~LastInITBlock IT then
              Unpredictable
            else
              Branch
                (Handler_Branch_Link_Parameter ((9 >< 5) ireg) ((4 >< 0) ireg)))
       | (T,T,F,F,T,F,F,_) =>
           (Encoding_ThumbEE, cond,
            LoadStore
              (Load T F F F F (r 3) (r 0)
                (Mode2_immediate (((8 >< 6) ireg) << 2))))
       | (T,T,F,F,T,F,T,F) =>
           (Encoding_ThumbEE, cond,
            Branch (Check_Array ((3 :+ b 7) (r 0)) (r4 3)))
       | (T,T,F,F,T,F,T,T) =>
           (Encoding_ThumbEE, cond,
            LoadStore
              (Load T T F F F 10w (r 0)
                (Mode2_immediate (((7 >< 3) ireg) << 2))))
       | (T,T,F,F,T,T,F,_) =>
           (Encoding_ThumbEE, cond,
            LoadStore
              (Load T T F F F 9w (r 0)
                (Mode2_immediate (((8 >< 3) ireg) << 2))))
       | (T,T,F,F,T,T,T,_) =>
           (Encoding_ThumbEE, cond,
            LoadStore
              (Store T T F F F 9w (r 0)
                (Mode2_immediate (((8 >< 3) ireg) << 2))))
       | _ => (Encoding_Thumb, thumb_decode arch IT ireg)`;

(* ------------------------------------------------------------------------ *)

(* Load/store multiple, dual and exclusive, table branch *)
val thumb2_decode_aux1_def = Define`
  thumb2_decode_aux1 IT (ireg1 : word16, ireg2 : word16) =
    let a n = ireg1 ' n
    and b n = ireg2 ' n
    and ra n = ( n + 3  >< n ) ireg1 : word4
    and rb n = ( n + 3  >< n ) ireg2 : word4
    in
      case (a 8,a 7,a 6,a 5,a 4, b 7,b 6,b 5,b 4)
      of (a8,a7, F,a5, F, b7,b6,b5,b4) =>
          (if a8 = a7 then
             LoadStore (Store_Return_State (~a8) a8 a5 ((4 >< 0) ireg2))
           else
             LoadStore (Store_Multiple a8 a7 F a5 (ra 0) ireg2))
       | (a8,a7, F,a5, T, b7,b6,b5,b4) =>
          (if a8 = a7 then
             if InITBlock IT /\ ~LastInITBlock IT then
               Unpredictable
             else
               LoadStore (Return_From_Exception (~a8) a8 a5 (ra 0))
           else
             if b 15 /\ InITBlock IT /\ ~LastInITBlock IT then
               Unpredictable
             else
               LoadStore (Load_Multiple a8 a7 F a5 (ra 0) ireg2))
       | ( F, F, T, F, F, b7,b6,b5,b4) =>
           LoadStore (Store_Exclusive (ra 0) (rb 8) (rb 12) ((7 >< 0) ireg2))
       | ( F, F, T, F, T, b7,b6,b5,b4) =>
           LoadStore (Load_Exclusive (ra 0) (rb 12) ((7 >< 0) ireg2))
       | ( F, T, T, F, F, F, T, F,b4) =>
           LoadStore
              (if b4 then Store_Exclusive_Halfword (ra 0) (rb 0) (rb 12)
                     else Store_Exclusive_Byte (ra 0) (rb 0) (rb 12))
       | ( F, T, T, F, F, F, T, T, T) =>
           LoadStore (Store_Exclusive_Doubleword (ra 0) (rb 0) (rb 12) (rb 8))
       | ( F, T, T, F, T, F, F, F,b4) =>
           if InITBlock IT /\ ~LastInITBlock IT then
             Unpredictable
           else
             Branch (Table_Branch_Byte (ra 0) b4 (rb 0))
       | ( F, T, T, F, T, F, T, F,b4) =>
           LoadStore
              (if b4 then Load_Exclusive_Halfword (ra 0) (rb 12)
                     else Load_Exclusive_Byte (ra 0) (rb 12))
       | ( F, T, T, F, T, F, T, T, T) =>
           LoadStore (Load_Exclusive_Doubleword (ra 0) (rb 12) (rb 8))
       | ( F,a7, T, T, F, b7,b6,b5,b4) =>
           LoadStore (Store_Dual F a7 T (ra 0) (rb 12) (rb 8)
             (Mode3_immediate (((7 >< 0) ireg2) << 2)))
       | ( T,a7, T,a5, F, b7,b6,b5,b4) =>
           LoadStore (Store_Dual T a7 a5 (ra 0) (rb 12) (rb 8)
             (Mode3_immediate (((7 >< 0) ireg2) << 2)))
       | ( F,a7, T, T, T, b7,b6,b5,b4) =>
           LoadStore (Load_Dual F a7 T (ra 0) (rb 12) (rb 8)
             (Mode3_immediate (((7 >< 0) ireg2) << 2)))
       | ( T,a7, T,a5, T, b7,b6,b5,b4) =>
           LoadStore (Load_Dual T a7 a5 (ra 0) (rb 12) (rb 8)
             (Mode3_immediate (((7 >< 0) ireg2) << 2)))
       | _ => Undefined`;

(* Data-processing (shifted register) *)
val thumb2_decode_aux2_def = Define`
  thumb2_decode_aux2 (ireg1 : word16, ireg2 : word16) =
    let a n = ireg1 ' n
    and b n = ireg2 ' n
    and ra  n = ( n + 3  >< n ) ireg1 : word4
    and ib2 n = ( n + 1  >< n ) ireg2 : word2
    and ib3 n = ( n + 2  >< n ) ireg2 : word3
    and rb  n = ( n + 3  >< n ) ireg2 : word4
    in
    let S = a 4 and rn = ra 0 and rd = rb 8
    in
      case (a 8,a 7,a 6,a 5)
      of (F, F, F, F) =>
           (if rd = 15w then
              if S then
                DP 0b1000w T rn 0w (REG (ib3 12 @@ ib2 6) (ib2 4) (rb 0))
              else
                Unpredictable
            else
              DP 0b0000w S rn rd (REG (ib3 12 @@ ib2 6) (ib2 4) (rb 0)))
       | (F, F, F, T) =>
           DP 0b1110w S rn rd (REG (ib3 12 @@ ib2 6) (ib2 4) (rb 0))
       | (F, F, T, F) =>
           DP (if rn = 15w then 0b1101w else 0b1100w) S rn rd
              (REG (ib3 12 @@ ib2 6) (ib2 4) (rb 0))
       | (F, F, T, T) =>
           DP 0b1111w S rn rd (REG (ib3 12 @@ ib2 6) (ib2 4) (rb 0))
       | (F, T, F, F) =>
           (if rd = 15w then
              if S then
                DP 0b1001w T rn 0w (REG (ib3 12 @@ ib2 6) (ib2 4) (rb 0))
              else
                Unpredictable
            else
              DP 0b0001w S rn rd (REG (ib3 12 @@ ib2 6) (ib2 4) (rb 0)))
       | (F, T, T, F) =>
           (if S \/ b 4 then
              Undefined
            else
              DataProcessing
                (Pack_Halfword rn rd (ib3 12 @@ ib2 6) (b 5) (rb 0)))
       | (T, F, F, F) =>
           (if rd = 15w then
              if S then
                DP 0b1011w T rn 0w (REG (ib3 12 @@ ib2 6) (ib2 4) (rb 0))
              else
                Unpredictable
            else
              DP 0b0100w S rn rd (REG (ib3 12 @@ ib2 6) (ib2 4) (rb 0)))
       | (T, F, T, F) =>
           DP 0b0101w S rn rd (REG (ib3 12 @@ ib2 6) (ib2 4) (rb 0))
       | (T, F, T, T) =>
           DP 0b0110w S rn rd (REG (ib3 12 @@ ib2 6) (ib2 4) (rb 0))
       | (T, T, F, T) =>
           (if rd = 15w then
              if S then
                DP 0b1010w T rn 0w (REG (ib3 12 @@ ib2 6) (ib2 4) (rb 0))
              else
                Unpredictable
            else
              DP 0b0010w S rn rd (REG (ib3 12 @@ ib2 6) (ib2 4) (rb 0)))
       | (T, T, T, F) =>
           DP 0b0011w S rn rd (REG (ib3 12 @@ ib2 6) (ib2 4) (rb 0))
       | _ => Undefined`;

(* Coprocessor *)
val thumb2_decode_aux3_def = Define`
  thumb2_decode_aux3 (ireg1 : word16, ireg2 : word16) =
    let a n = ireg1 ' n
    and b n = ireg2 ' n
    and ia3 n = ( n + 2  >< n ) ireg1 : word3
    and ia4 n = ( n + 3  >< n ) ireg1 : word4
    and ib3 n = ( n + 2  >< n ) ireg2 : word3
    and ib4 n = ( n + 3  >< n ) ireg2 : word4
    and ib8 n = ( n + 7  >< n ) ireg2 : word8
    in
    let ra = ia4 and rb = ib4
    in
      case (a 9,a 8,a 7,a 6,a 5,a 4)
      of (F,F, F, T, F,a4) =>
           Coprocessor
             (Coprocessor_Transfer_Two a4 (ra 0) (rb 12) (ib4 8) (ib4 4) (rb 0))
       | (F,F, F,a6, T, F) =>
           Coprocessor
             (Coprocessor_Store F F a6 T (ra 0) (rb 12) (ib4 8) (ib8 0))
       | (F,F, T,a6,a5, F) =>
           Coprocessor
             (Coprocessor_Store F T a6 a5 (ra 0) (rb 12) (ib4 8) (ib8 0))
       | (F,T,a7,a6,a5, F) =>
           Coprocessor
             (Coprocessor_Store T a7 a6 a5 (ra 0) (rb 12) (ib4 8) (ib8 0))
       | (F,F, F,a6, T, T) =>
           Coprocessor
             (Coprocessor_Load F F a6 T (ra 0) (rb 12) (ib4 8) (ib8 0))
       | (F,F, T,a6,a5, T) =>
           Coprocessor
             (Coprocessor_Load F T a6 a5 (ra 0) (rb 12) (ib4 8) (ib8 0))
       | (F,T,a7,a6,a5, T) =>
           Coprocessor
             (Coprocessor_Load T a7 a6 a5 (ra 0) (rb 12) (ib4 8) (ib8 0))
       | (T,F,a7,a6,a5,a4) =>
           if b 4 then
             Coprocessor
               (Coprocessor_Transfer (ia3 4) a4 (ra 0) (rb 12) (ib4 8)
                  (ib3 5) (rb 0))
           else
             Coprocessor
               (Coprocessor_Data_Processing (ia4 4) (ra 0) (rb 12) (ib4 8)
                  (ib3 5) (rb 0))
       | _ => Undefined`;

val _ = wordsLib.guess_lengths();

(* Data-processing (modified immediate) *)
val thumb2_decode_aux4_def = Define`
  thumb2_decode_aux4 (ireg1 : word16, ireg2 : word16) =
    let a n = ireg1 ' n
    and ia1 n = ( n + 0  >< n ) ireg1 : word1
    and ra  n = ( n + 3  >< n ) ireg1 : word4
    and ib3 n = ( n + 2  >< n ) ireg2 : word3
    and ib8 n = ( n + 7  >< n ) ireg2 : word8
    and rb  n = ( n + 3  >< n ) ireg2 : word4
    in
    let S = a 4 and rn = ra 0 and rd = rb 8
    in
      case (a 8,a 7,a 6,a 5)
      of (F, F, F, F) =>
           if rd = 15w then
             if S then
               DP 0b1000w T rn 0w (IMM (ia1 10 @@ ib3 12 @@ ib8 0))
             else
               Unpredictable
           else
             DP 0b0000w S rn rd (IMM (ia1 10 @@ ib3 12 @@ ib8 0))
       | (F, F, F, T) =>
           DP 0b1110w S rn rd (IMM (ia1 10 @@ ib3 12 @@ ib8 0))
       | (F, F, T, F) =>
           DP (if rn = 15w then 0b1101w else 0b1100w) S rn rd
              (IMM (ia1 10 @@ ib3 12 @@ ib8 0))
       | (F, F, T, T) =>
           DP 0b1111w S rn rd (IMM (ia1 10 @@ ib3 12 @@ ib8 0))
       | (F, T, F, F) =>
           if rd = 15w then
             if S then
               DP 0b1001w T rn 0w (IMM (ia1 10 @@ ib3 12 @@ ib8 0))
             else
               Unpredictable
           else
             DP 0b0001w S rn rd (IMM (ia1 10 @@ ib3 12 @@ ib8 0))
       | (T, F, F, F) =>
           if rd = 15w then
             if S then
               DP 0b1011w T rn 0w (IMM (ia1 10 @@ ib3 12 @@ ib8 0))
             else
               Unpredictable
           else
             DP 0b0100w S rn rd (IMM (ia1 10 @@ ib3 12 @@ ib8 0))
       | (T, F, T, F) =>
           DP 0b0101w S rn rd (IMM (ia1 10 @@ ib3 12 @@ ib8 0))
       | (T, F, T, T) =>
           DP 0b0110w S rn rd (IMM (ia1 10 @@ ib3 12 @@ ib8 0))
       | (T, T, F, T) =>
           if rd = 15w then
             if S then
               DP 0b1010w T rn 0w (IMM (ia1 10 @@ ib3 12 @@ ib8 0))
             else
               Unpredictable
           else
             DP 0b0010w S rn rd (IMM (ia1 10 @@ ib3 12 @@ ib8 0))
       | (T, T, T, F) =>
           DP 0b0011w S rn rd (IMM (ia1 10 @@ ib3 12 @@ ib8 0))
       | _ => Undefined`;

(* Data-processing (plain binary immediate) *)
val thumb2_decode_aux5_def = Define`
  thumb2_decode_aux5 (ireg1 : word16, ireg2 : word16) =
    let a n = ireg1 ' n
    and ia1 n = ( n + 0  >< n ) ireg1 : word1
    and ia4 n = ( n + 3  >< n ) ireg1 : word4
    and ib2 n = ( n + 1  >< n ) ireg2 : word2
    and ib3 n = ( n + 2  >< n ) ireg2 : word3
    and ib4 n = ( n + 3  >< n ) ireg2 : word4
    and ib5 n = ( n + 4  >< n ) ireg2 : word5
    and ib8 n = ( n + 7  >< n ) ireg2 : word8
    in
    let ra = ia4 and rb = ib4
    in
      if a 4 then Undefined else
        case (a 8,a 7,a 6,a 5)
        of (F, F, F, F) =>
            DataProcessing (Add_Sub T (ra 0) (rb 8) (ia1 10 @@ ib3 12 @@ ib8 0))
         | (F, T, F, T) =>
            DataProcessing (Add_Sub F (ra 0) (rb 8) (ia1 10 @@ ib3 12 @@ ib8 0))
         | (F,a7, T, F) =>
            DataProcessing
              (Move_Halfword a7 (rb 8) (ia4 0 @@ ia1 10 @@ ib3 12 @@ ib8 0))
         | (T,a7, F,a5) =>
           (let imm5 = ib3 12 @@ ib2 6 in
              if a5 /\ (imm5 = 0w) then
                DataProcessing (Saturate_16 a7 (ib4 0) (rb 8) (ra 0))
              else
                DataProcessing (Saturate a7 (ib5 0) (rb 8) imm5 a5 (ra 0)))
         | (T,a7, T, F) =>
            DataProcessing
              (Bit_Field_Extract a7 (ib5 0) (rb 8) (ib3 12 @@ ib2 6) (ra 0))
         | (T, F, T, T) =>
            DataProcessing
              (Bit_Field_Clear_Insert (ib5 0) (rb 8) (ib3 12 @@ ib2 6) (ra 0))
         | _ => Undefined`;

(* Branches and miscellaneous control *)
val thumb2_decode_aux6_def = Define`
  thumb2_decode_aux6 IT (ireg1 : word16, ireg2 : word16) =
    let a n = ireg1 ' n
    and b n = ireg2 ' n
    and ia1  n = ( n + 0  >< n ) ireg1 : word1
    and ia4  n = ( n + 3  >< n ) ireg1 : word4
    and ia6  n = ( n + 5  >< n ) ireg1 : word6
    and ia10 n = ( n + 9  >< n ) ireg1 : word10
    and ib1  n = ( n + 0  >< n ) ireg2 : word1
    and ib2  n = ( n + 1  >< n ) ireg2 : word2
    and ib4  n = ( n + 3  >< n ) ireg2 : word4
    and ib5  n = ( n + 4  >< n ) ireg2 : word5
    and ib8  n = ( n + 7  >< n ) ireg2 : word8
    and ib10 n = ( n + 9  >< n ) ireg2 : word10
    and ib11 n = ( n + 10 >< n ) ireg2 : word11
    in
    let ra = ia4 and rb = ib4
    and InITBlock = InITBlock IT
    and LastInITBlock = LastInITBlock IT
    in
      case (a 10,a 9,a 8,a 7,a 6,a 5,a 4,
            b 14,b 13,b 12,b 11,b 10,b 9,b 8,b 7,b 6,b 5,b 4)
      of (F , T, T, T, F, F, a4,  F ,b13, F ,b11,b10,b9,b8,b7,b6,b5,b4) =>
           StatusAccess (Register_to_Status a4 (rb 8) (ra 0))
       | (F , T, T, T, F, T, F,  F ,b13, F ,b11, F , F, F,b7,b6,b5,b4) =>
           Miscellaneous (Hint (hint_decode (ib8 0)))
       | (F , T, T, T, F, T, F,  F ,b13, F ,b11,b10,b9,b8,b7,b6,b5,b4) =>
          (if InITBlock then
             Unpredictable
           else let mode = ib5 0 in
             if ~b8 /\ (mode <> 0w) then
               Unpredictable
             else
               StatusAccess
                 (Change_Processor_State (ib2 9) b7 b6 b5
                    (if b8 then SOME mode else NONE)))
       | (F , T, T, T, F, T, T,  F ,b13, F ,b11,b10,b9,b8, F, F, F, b4) =>
           if InITBlock then
             Unpredictable
           else
             Miscellaneous (Enterx_Leavex b4)
       | (F , T, T, T, F, T, T,  F ,b13, F ,b11,b10,b9,b8, F, F, T, F) =>
           Miscellaneous Clear_Exclusive
       | (F , T, T, T, F, T, T,  F ,b13, F ,b11,b10,b9,b8, F, T, F, F) =>
           Miscellaneous (Data_Synchronization_Barrier (ib4 0))
       | (F , T, T, T, F, T, T,  F ,b13, F ,b11,b10,b9,b8, F, T, F, T) =>
           Miscellaneous (Data_Memory_Barrier (ib4 0))
       | (F , T, T, T, F, T, T,  F ,b13, F ,b11,b10,b9,b8, F, T, T, F) =>
           Miscellaneous (Instruction_Synchronization_Barrier (ib4 0))
       | (F , T, T, T, T, F, T,  F ,b13, F ,b11,b10,b9,b8,b7,b6,b5,b4) =>
           if InITBlock /\ ~LastInITBlock then
               Unpredictable
             else
               DP 0b0010w T 14w 15w (IMM ((7 >< 0) ireg2))
       | (F , T, T, T, T, T,a4,  F ,b13, F ,b11,b10,b9,b8,b7,b6,b5,b4) =>
           StatusAccess (Status_to_Register a4 (rb 8))
       | (T , T, T, T, T, T, T,  F , F , F ,b11,b10,b9,b8,b7,b6,b5,b4) =>
           Miscellaneous (Secure_Monitor_Call (ia4 0))
       | (a10, T, T, T,a6,a5,a4, F ,b13, F ,b11,b10,b9,b8,b7,b6,b5,b4) =>
           Undefined
       | (a10,a9,a8,a7,a6,a5,a4, F ,b13, F ,b11,b10,b9,b8,b7,b6,b5,b4) =>
          (if InITBlock then
             Unpredictable
           else let S = ia1 10 and J1 = ib1 13 and J2 = ib1 11 in
             Branch
               (Branch_Target (sw2sw (S @@ J2 @@ J1 @@ ia6 0 @@ ib11 0))))
       | (a10,a9,a8,a7,a6,a5,a4, F ,b13, T ,b11,b10,b9,b8,b7,b6,b5,b4) =>
          (if InITBlock /\ ~LastInITBlock then
             Unpredictable
           else let S = ia1 10 and J1 = ib1 13 and J2 = ib1 11 in
                let I1 = ~(J1 ?? S) and I2 = ~(J2 ?? S) in
             Branch (Branch_Target (S @@ I1 @@ I2 @@ ia10 0 @@ ib11 0)))
       | (a10,a9,a8,a7,a6,a5,a4, T ,b13,b12,b11,b10,b9,b8,b7,b6,b5,b4) =>
          (if ~b12 /\ b 0 then
             Undefined
           else if InITBlock /\ ~LastInITBlock then
             Unpredictable
           else let S = ia1 10 and J1 = ib1 13 and J2 = ib1 11 in
                let I1 = ~(J1 ?? S) and I2 = ~(J2 ?? S) in
             Branch
               (Branch_Link_Exchange_Immediate (b 0) (~b12)
                  (S @@ I1 @@ I2 @@ ia10 0 @@ ib10 1)))`;

(* Load/store, memory hints *)
val thumb2_decode_aux7_def = Define`
  thumb2_decode_aux7 IT (ireg1 : word16, ireg2 : word16) =
    let a n = ireg1 ' n
    and b n = ireg2 ' n
    and ra   n = ( n + 3  >< n ) ireg1 : word4
    and ib2  n = ( n + 1  >< n ) ireg2 : word2
    and rb   n = ( n + 3  >< n ) ireg2 : word4
    and ib5  n = ( n + 4  >< n ) ireg2 : word5
    and ib12 n = ( n + 11 >< n ) ireg2 : word12
    in
    let rn = ra 0 and rt = rb 12
    in
      if a 4 then
        if rt = 15w then
          if rn = 15w then
            case (a 8,a 7,a 6,a 5)
            of (F,a7,F , F) =>
                 Miscellaneous
                   (Preload_Data a7 F rn (Mode2_immediate (ib12 0)))
             | (F,a7,F , T) =>
                 Unpredictable
             | (F,a7,T , F) =>
                 if InITBlock IT /\ ~LastInITBlock IT then
                   Unpredictable
                 else
                   LoadStore
                     (Load T a7 F F F rn rt (Mode2_immediate (ib12 0)))
             | (T,a7,F , F) =>
                 Miscellaneous
                   (Preload_Instruction a7 rn (Mode2_immediate (ib12 0)))
             | (T,a7,a6,a5) =>
                 Miscellaneous (Hint Hint_nop)
             | _ => Undefined
          else
            case (a 8,a 7,a 6,a 5, b 11,b 10,b 9,b 8,b 7,b 6)
            of (F,T,F,a5,  b11,b10,b9,b8,b7,b6) =>
                 Miscellaneous
                   (Preload_Data T a5 rn (Mode2_immediate (ib12 0)))
             | (F,F,F,a5,   T , T , F, F,b7,b6) =>
                 Miscellaneous
                   (Preload_Data T a5 rn (Mode2_immediate ((7 >< 0) ireg2)))
             | (F,F,F,a5,   F , F , F, F, F, F) =>
                 Miscellaneous
                   (Preload_Data T a5 rn
                      (Mode2_register ((5 >< 4) ireg2) 0w (rb 0)))
             | (F,F,F,a5,   T ,b10,b9, T,b7,b6) =>
                 Unpredictable
             | (F,F,F,a5,   T , T , T, F,b7,b6) =>
                 Unpredictable
             | (F,T,T, F,  b11,b10,b9,b8,b7,b6) =>
                 if InITBlock IT /\ ~LastInITBlock IT then
                   Unpredictable
                 else
                   LoadStore (Load T T F F F rn rt (Mode2_immediate (ib12 0)))
             | (F,F,T, F,   T ,b10,b9, T,b7,b6) =>
                 if InITBlock IT /\ ~LastInITBlock IT then
                   Unpredictable
                 else
                   LoadStore
                     (Load b10 b9 F T F rn rt
                        (Mode2_immediate ((7 >< 0) ireg2)))
             | (F,F,T, F,   T , T ,b9, F,b7,b6) =>
                 if InITBlock IT /\ ~LastInITBlock IT then
                   Unpredictable
                 else
                   LoadStore
                     (Load T b9 F F b9 rn rt (Mode2_immediate ((7 >< 0) ireg2)))
             | (F,F,T, F,   F , F , F, F, F, F) =>
                 if InITBlock IT /\ ~LastInITBlock IT then
                   Unpredictable
                 else
                   LoadStore
                     (Load T T F F F rn rt
                        (Mode2_register ((5 >< 4) ireg2) 0w (rb 0)))
             | (T,F,F,F,    F , F , F, F, F, F) =>
                 Miscellaneous
                   (Preload_Instruction F rn
                      (Mode2_register ((5 >< 4) ireg2) 0w (rb 0)))
             | (T,F,F,F,    T , T , F, F,b7,b6) =>
                 Miscellaneous
                   (Preload_Instruction F rn (Mode2_immediate (ib12 0)))
             | (T,F,F,T,    F , F , F, F, F, F) =>
                 Miscellaneous (Hint Hint_nop)
             | (T,F,F,T,    T , T , F, F,b7,b6) =>
                 Miscellaneous (Hint Hint_nop)
             | (T,F,F,a5,   T ,b10,b9, T,b7,b6) =>
                 Unpredictable
             | (T,F,F,a5,   T , T , T, F,b7,b6) =>
                 Unpredictable
             | (T,T,F,T,   b11,b10,b9,b8,b7,b6) =>
                 Miscellaneous (Hint Hint_nop)
             | _ => Undefined
        else
          if rn = 15w then
            case (a 8,a 7,a 6,a 5)
            of (F,a7,a6, F) =>
                 LoadStore
                   (Load T a7 (~a6) F F rn rt (Mode2_immediate (ib12 0)))
             | (F,a7, F, T) =>
                 LoadStore
                   (Load_Halfword T a7 F F T F rn rt (Mode3_immediate (ib12 0)))
             | (T,a7, F,a5) =>
                 LoadStore
                   (Load_Halfword T a7 F T a5 F rn rt
                      (Mode3_immediate (ib12 0)))
             | _ => Undefined
          else
            case (a 8,a 7,a 6,a 5, b 11,b 10,b 9,b 8,b 7,b 6)
            of ( F, T,a6, F,  b11,b10,b9,b8,b7,b6) =>
                 LoadStore (Load T T (~a6) F F rn rt (Mode2_immediate (ib12 0)))
             | ( F, F,a6, F,   T ,b10,b9, T,b7,b6) =>
                 LoadStore
                   (Load b10 b9 (~a6) T F rn rt
                      (Mode2_immediate ((7 >< 0) ireg2)))
             | ( F, F,a6, F,   T , T ,b9, F,b7,b6) =>
                 LoadStore
                   (Load T b9 (~a6) F b9 rn rt
                      (Mode2_immediate ((7 >< 0) ireg2)))
             | ( F, F,a6, F,   F , F , F, F, F, F) =>
                 LoadStore
                   (Load T T (~a6) F F rn rt
                      (Mode2_register ((5 >< 4) ireg2) 0w (rb 0)))
             | ( F, T, F, T,  b11,b10,b9,b8,b7,b6) =>
                 LoadStore
                   (Load_Halfword T T F F T F rn rt (Mode3_immediate (ib12 0)))
             | ( F, F, F, T,   T ,b10,b9, T,b7,b6) =>
                 LoadStore
                   (Load_Halfword b10 b9 T F T F rn rt
                      (Mode3_immediate ((7 >< 0) ireg2)))
             | ( F, F, F, T,   T , T ,b9, F,b7,b6) =>
                 LoadStore
                   (Load_Halfword T b9 F F T b9 rn rt
                      (Mode3_immediate ((7 >< 0) ireg2)))
             | ( F, F, F, T,   F , F , F, F, F, F) =>
                 LoadStore
                   (Load_Halfword T T F F T F rn rt
                      (Mode3_register (ib2 4) (rb 0)))
             | ( T, T, F,a5,  b11,b10,b9,b8,b7,b6) =>
                 LoadStore
                   (Load_Halfword T T F T a5 F rn rt (Mode3_immediate (ib12 0)))
             | ( T, F, F,a5,   T ,b10,b9, T,b7,b6) =>
                 LoadStore
                   (Load_Halfword b10 b9 T T a5 F rn rt
                      (Mode3_immediate ((7 >< 0) ireg2)))
             | ( T, F, F,a5,   T , T ,b9, F,b7,b6) =>
                 LoadStore
                   (Load_Halfword T b9 F T a5 b9 rn rt
                      (Mode3_immediate ((7 >< 0) ireg2)))
             | ( T, F, F,a5,   F , F , F, F, F, F) =>
                 LoadStore
                   (Load_Halfword T T F T a5 F rn rt
                      (Mode3_register (ib2 4) (rb 0)))
             | _ => Undefined
      else
        if rn = 15w then
          Undefined
        else
          case (a 8,a 7,a 6,a 5, b 11)
          of (F, T,a6, F,  b11) =>
               LoadStore (Store T T (~a6) F F rn rt (Mode2_immediate (ib12 0)))
           | (F, F,a6, F,   T ) =>
              (let b10 = b 10 and b9 = b 9 and b8 = b 8 in
                 if b10 \/ b8 then
                   LoadStore
                     (Store b10 b9 (~a6) b8 (b10 /\ b9 /\ ~b8) rn rt
                        (Mode2_immediate ((7 >< 0) ireg2)))
                 else
                   Undefined)
           | (F, F,a6, F,   F ) =>
               if ib5 6 = 0w then
                 LoadStore
                   (Store T T (~a6) F F rn rt
                     (Mode2_register ((5 >< 4) ireg2) 0w (rb 0)))
               else
                 Undefined
           | (F, T, F, T,  b11) =>
               LoadStore
                 (Store_Halfword T T F F rn rt (Mode3_immediate (ib12 0)))
           | (F, F, F, T,   T ) =>
              (let b10 = b 10 and b9 = b 9 and b8 = b 8 in
                 if b10 \/ b8 then
                   LoadStore
                     (Store_Halfword b10 b9 b8 (b10 /\ b9 /\ ~b8) rn rt
                        (Mode3_immediate ((7 >< 0) ireg2)))
                 else
                   Undefined)
           | (F, F, F, T,   F ) =>
               if ib5 6 = 0w then
                 LoadStore
                   (Store_Halfword T T F F rn rt
                      (Mode3_register (ib2 4) (rb 0)))
               else
                 Undefined
           | _ => Undefined`;

(* Data-processing (register) *)
val thumb2_decode_aux8_def = Define`
  thumb2_decode_aux8 (ireg1 : word16, ireg2 : word16) =
    let a n = ireg1 ' n
    and b n = ireg2 ' n
    and ia2  n = ( n + 1  >< n ) ireg1 : word2
    and ia3  n = ( n + 2  >< n ) ireg1 : word3
    and ia4  n = ( n + 3  >< n ) ireg1 : word4
    and ib2  n = ( n + 1  >< n ) ireg2 : word2
    and ib3  n = ( n + 2  >< n ) ireg2 : word3
    and ib4  n = ( n + 3  >< n ) ireg2 : word4
    in
    let ra = ia4 and rb = ib4
    in
      if rb 12 <> 15w then
        Undefined
      else
        case (a 7,b 7,b 6)
        of (F,F, F) =>
            if ib2 4 = 0w then
              DP 0b1101w (a 4) 0w (rb 8) (SHIFTED (rb 0) (ia2 5) (ra 0))
            else
              Undefined
         | (F,T,b6) =>
           (case (a 6,a 5)
            of (F,F) => DataProcessing
                          (Extend_Halfword (a 4) (ra 0) (rb 8) (ib2 4) (rb 0))
             | (F,T) => DataProcessing
                          (Extend_Byte_16  (a 4) (ra 0) (rb 8) (ib2 4) (rb 0))
             | (T,F) => DataProcessing
                          (Extend_Byte     (a 4) (ra 0) (rb 8) (ib2 4) (rb 0))
             | (T,T) => Undefined)
         | (T,F,b6) =>
             DataProcessing
               (Parallel_Add_Subtract b6
                   (parallel_add_sub_thumb_decode (ib2 4,ia3 4))
                   (ra 0) (rb 8) (rb 0))
         | (T,T, F) =>
            (let opc2 = ib2 4 in
               case (a 6,a 5,a 4)
               of (F,F,F) =>
                    (let opc3 = case opc2
                                of 0b01w => 0b10w
                                 | 0b10w => 0b01w
                                 | _ => opc2
                     in
                       DataProcessing
                         (Saturating_Add_Subtract opc3 (ra 0) (rb 8) (rb 0)))
                | (F,F,T) => (let rm1 = ra 0 and rm2 = rb 0 in
                     if rm1 <> rm2 then
                       Unpredictable
                     else
                       case opc2
                       of 0b00w => DataProcessing
                                     (Byte_Reverse_Word (rb 8) rm1)
                        | 0b01w => DataProcessing
                                     (Byte_Reverse_Packed_Halfword (rb 8) rm1)
                        | 0b10w => DataProcessing
                                     (Reverse_Bits (rb 8) rm1)
                        | 0b11w => DataProcessing
                                     (Byte_Reverse_Signed_Halfword (rb 8) rm1))
                | (F,T,F) =>
                     if opc2 = 0w then
                       DataProcessing (Select_Bytes (ra 0) (rb 8) (rb 0))
                     else
                       Undefined
                | (F,T,T) =>
                     if opc2 = 0w then
                       let rm1 = ra 0 and rm2 = rb 0 in
                         if rm1 <> rm2 then
                           Unpredictable
                         else
                           DataProcessing (Count_Leading_Zeroes (rb 8) rm1)
                     else
                       Undefined
                | _ => Undefined)
         | _ => Undefined`;

(* Multiplies, divide and absolute difference *)
val thumb2_decode_aux9_def = Define`
  thumb2_decode_aux9 (ireg1 : word16, ireg2 : word16) =
    let a n = ireg1 ' n in
      if ~a 8 then thumb2_decode_aux8 (ireg1,ireg2)
      else
        let b n = ireg2 ' n
        and ra n = ( n + 3  >< n ) ireg1 : word4
        and rb n = ( n + 3  >< n ) ireg2 : word4
        in
        let rb12 = rb 12
        in
          case (a 7,a 6,a 5,a 4,  b 7,b 6,b 5,b 4)
          of (F, F, F, F,  F,F, F, F) =>
              (let A = rb12 <> 15w in
                 DataProcessing
                   (Multiply A F (rb 8) (if A then rb12 else 0w) (rb 0) (ra 0)))
           | (F, F, F, F,  F,F, F, T) =>
               DataProcessing (Multiply_Subtract (rb 8) rb12 (rb 0) (ra 0))
           | (F, F, F, T,  F,F,b5,b4) =>
               if rb12 = 15w then
                 DataProcessing
                   (Signed_Halfword_Multiply 3w b4 b5 (rb 8) 0w (rb 0) (ra 0))
               else
                 DataProcessing
                   (Signed_Halfword_Multiply 0w b4 b5 (rb 8) rb12 (rb 0) (ra 0))
           | (F, F, T, F,  F,F, F,b4) =>
               DataProcessing
                 (Signed_Multiply_Dual (rb 8) rb12 (rb 0) F b4 (ra 0))
           | (F, F, T, T,  F,F, F,b4) =>
               if rb12 = 15w then
                 DataProcessing
                   (Signed_Halfword_Multiply 1w b4 T (rb 8) 0w (rb 0) (ra 0))
               else
                 DataProcessing
                   (Signed_Halfword_Multiply 1w b4 F (rb 8) rb12 (rb 0) (ra 0))
           | (F, T, F, F,  F,F, F,b4) =>
               DataProcessing
                 (Signed_Multiply_Dual (rb 8) rb12 (rb 0) T b4 (ra 0))
           | (F, T, F, T,  F,F, F,b4) =>
               DataProcessing
                 (Signed_Most_Significant_Multiply (rb 8) rb12 (rb 0) b4 (ra 0))
           | (F, T, T, F,  F,F, F,b4) =>
               DataProcessing
                 (Signed_Most_Significant_Multiply_Subtract (rb 8) rb12 (rb 0)
                    b4 (ra 0))
           | (F, T, T, T,  F,F, F, F) =>
               DataProcessing
                 (Unsigned_Sum_Absolute_Differences (rb 8) rb12 (rb 0) (ra 0))
           | (T,a6,a5, F,  F,F, F, F) =>
               DataProcessing
                 (Multiply_Long (~a5) a6 F (rb 8) rb12 (rb 0) (ra 0))
           | (T, F,a5, T,  T,T, T, T) =>
               DataProcessing (Divide a5 (ra 0) (rb 8) (rb 0))
           | (T, T, F, F,  T,F,b5,b4) =>
               DataProcessing
                 (Signed_Halfword_Multiply 2w b4 b5 (rb 8) rb12 (rb 0) (ra 0))
           | (T, T, F,a4,  T,T, F,b4) =>
               DataProcessing
                 (Signed_Multiply_Long_Dual (rb 8) rb12 (rb 0) a4 b4 (ra 0))
           | (T, T, T, F,  F,T, T, F) =>
               DataProcessing
                 (Multiply_Accumulate_Accumulate (rb 8) rb12 (rb 0) (ra 0))
           | _ => Undefined`;

(* ........................................................................ *)

val thumb2_decode_def = Define`
  thumb2_decode arch IT (ireg1 : word16, ireg2 : word16) =
    let IT = if arch IN thumb2_support then IT else 0w
    and a n = ireg1 ' n
    and b n = ireg2 ' n
    in
    let a12 = a 12 and a11 = a 11 and a9 = a 9 and b15 = b 15
    in
     ((if a12 /\ ~a11 /\ ~(a9 /\ a 8 /\ a 7) /\
          b15 /\ ~b 14 /\ ~b 12
       then
         (9 >< 6) ireg1 : word4
       else
         if IT = 0w then 0b1110w else (7 >< 4) IT),
      case (a12,a11,a 10,a9,b15) of
         (F,T,F,F,_) => thumb2_decode_aux1 IT (ireg1,ireg2)
       | (F,T,F,T,_) => thumb2_decode_aux2 (ireg1,ireg2)
       | (_,T,T,_,_) => thumb2_decode_aux3 (ireg1,ireg2)
       | (T,F,_,F,F) => thumb2_decode_aux4 (ireg1,ireg2)
       | (T,F,_,T,F) => thumb2_decode_aux5 (ireg1,ireg2)
       | (T,F,_,_,T) => thumb2_decode_aux6 IT (ireg1,ireg2)
       | (T,T,F,F,_) => thumb2_decode_aux7 IT (ireg1,ireg2)
       | (T,T,F,T,_) => thumb2_decode_aux9 (ireg1,ireg2)
       | _ => Undefined)`;

(* ------------------------------------------------------------------------ *)

(* speed up evaluation *)

val decode_lem = Q.prove(
  `((BIT 27 n,BIT 26 n,BIT 25 n,BIT 24 n,BIT 23 n,BIT 22 n,BIT 21 n,
         BIT 20 n,BIT 7 n,BIT 6 n,BIT 5 n,BIT 4 n) =
   let (q0,b4)   = DIVMOD_2EXP 1 (DIV_2EXP 4 n) in
   let (q1,b5)   = DIVMOD_2EXP 1 q0 in
   let (q2,b6)   = DIVMOD_2EXP 1 q1 in
   let (q3,b7)   = DIVMOD_2EXP 1 q2 in
   let (q4,b20)  = DIVMOD_2EXP 1 (DIV_2EXP 12 q3) in
   let (q5,b21)  = DIVMOD_2EXP 1 q4 in
   let (q6,b22)  = DIVMOD_2EXP 1 q5 in
   let (q7,b23)  = DIVMOD_2EXP 1 q6 in
   let (q8,b24)  = DIVMOD_2EXP 1 q7 in
   let (q9,b25)  = DIVMOD_2EXP 1 q8 in
   let (q10,b26) = DIVMOD_2EXP 1 q9 in
     (ODD q10,b26 = 1,b25 = 1,b24 = 1,b23 = 1,b22 = 1,b21 = 1,b20 = 1,
      b7 = 1,b6 = 1,b5 = 1,b4 = 1)) /\
   ((BIT 15 n,BIT 14 n,BIT 13 n,BIT 12 n,BIT 11 n,BIT 10 n,BIT 9 n,
       BIT 8 n,BIT 7 n,BIT 6 n) =
   let (q0,b6)   = DIVMOD_2EXP 1 (DIV_2EXP 6 n) in
   let (q1,b7)   = DIVMOD_2EXP 1 q0 in
   let (q2,b8)   = DIVMOD_2EXP 1 q1 in
   let (q3,b9)   = DIVMOD_2EXP 1 q2 in
   let (q4,b10)  = DIVMOD_2EXP 1 q3 in
   let (q5,b11)  = DIVMOD_2EXP 1 q4 in
   let (q6,b12)  = DIVMOD_2EXP 1 q5 in
   let (q7,b13)  = DIVMOD_2EXP 1 q6 in
   let (q8,b14)  = DIVMOD_2EXP 1 q7 in
     (ODD q8,b14 = 1,b13 = 1,b12 = 1,b11 = 1,b10 = 1,b9 = 1,b8 = 1,
      b7 = 1,b6 = 1)) /\
   ((BIT 8 m,BIT 7 m,BIT 6 m,BIT 5 m,BIT 4 m,BIT 7 n,BIT 6 n,BIT 5 n,
      BIT 4 n) =
   let (q0,a4)   = DIVMOD_2EXP 1 (DIV_2EXP 4 m) in
   let (q1,a5)   = DIVMOD_2EXP 1 q0 in
   let (q2,a6)   = DIVMOD_2EXP 1 q1 in
   let (q3,a7)   = DIVMOD_2EXP 1 q2 in
   let (q0,b4)   = DIVMOD_2EXP 1 (DIV_2EXP 4 n) in
   let (q1,b5)   = DIVMOD_2EXP 1 q0 in
   let (q2,b6)   = DIVMOD_2EXP 1 q1 in
     (ODD q3,a7 = 1,a6 = 1,a5 = 1,a4 = 1,
      ODD q2,b6 = 1,b5 = 1,b4 = 1)) /\
   ((BIT 8 m,BIT 7 m,BIT 6 m,BIT 5 m) =
   let (q0,a4)   = DIVMOD_2EXP 1 (DIV_2EXP 4 m) in
   let (q1,a5)   = DIVMOD_2EXP 1 q0 in
   let (q2,a6)   = DIVMOD_2EXP 1 q1 in
   let (q3,a7)   = DIVMOD_2EXP 1 q2 in
     (ODD q3,a7 = 1,a6 = 1,a5 = 1)) /\
   ((BIT 10 m,BIT 9 m,BIT 8 m,BIT 7 m,BIT 6 m,BIT 5 m,BIT 4 m,BIT 14 n,
     BIT 13 n,BIT 12 n,BIT 11 n,BIT 10 n,BIT 9 n,BIT 8 n,BIT 7 n,
     BIT 6 n,BIT 5 n,BIT 4 n) =
   let (q0,a4)   = DIVMOD_2EXP 1 (DIV_2EXP 4 m) in
   let (q1,a5)   = DIVMOD_2EXP 1 q0 in
   let (q2,a6)   = DIVMOD_2EXP 1 q1 in
   let (q3,a7)   = DIVMOD_2EXP 1 q2 in
   let (q4,a8)   = DIVMOD_2EXP 1 q3 in
   let (r5,a9)   = DIVMOD_2EXP 1 q4 in
   let (q0,b4)   = DIVMOD_2EXP 1 (DIV_2EXP 4 n) in
   let (q1,b5)   = DIVMOD_2EXP 1 q0 in
   let (q2,b6)   = DIVMOD_2EXP 1 q1 in
   let (q3,b7)   = DIVMOD_2EXP 1 q2 in
   let (q4,b8)   = DIVMOD_2EXP 1 q3 in
   let (q5,b9)   = DIVMOD_2EXP 1 q4 in
   let (q6,b10)  = DIVMOD_2EXP 1 q5 in
   let (q7,b11)  = DIVMOD_2EXP 1 q6 in
   let (q8,b12)  = DIVMOD_2EXP 1 q7 in
   let (q9,b13)  = DIVMOD_2EXP 1 q8 in
     (ODD r5,a9 = 1,a8 = 1,a7 = 1,a6 = 1,a5 = 1,a4 = 1,
      ODD q9,b13 = 1,b12 = 1,b11 = 1,b10 = 1,b9 = 1,b8 = 1,
      b7 = 1,b6 = 1,b5 = 1,b4 = 1)) /\
   ((BIT 9 m,BIT 8 m,BIT 7 m,BIT 6 m,BIT 5 m,BIT 4 m) =
   let (q0,a4)   = DIVMOD_2EXP 1 (DIV_2EXP 4 m) in
   let (q1,a5)   = DIVMOD_2EXP 1 q0 in
   let (q2,a6)   = DIVMOD_2EXP 1 q1 in
   let (q3,a7)   = DIVMOD_2EXP 1 q2 in
   let (q4,a8)   = DIVMOD_2EXP 1 q3 in
     (ODD q4,a8 = 1,a7 = 1,a6 = 1,a5 = 1,a4 = 1)) /\
   ((BIT 12 m,BIT 11 m,BIT 10 m,BIT 9 m,BIT 15 n) =
   let (q0,a9)   = DIVMOD_2EXP 1 (DIV_2EXP 9 m) in
   let (q1,a10)  = DIVMOD_2EXP 1 q0 in
   let (q2,a11)  = DIVMOD_2EXP 1 q1 in
     (ODD q2,a11 = 1,a10 = 1,a9 = 1,BIT 15 n)) /\
   ((BIT 7 m,BIT 6 m,BIT 5 m,BIT 4 m,BIT 7 n,BIT 6 n,BIT 5 n,BIT 4 n) =
   let (q0,a4)   = DIVMOD_2EXP 1 (DIV_2EXP 4 m) in
   let (q1,a5)   = DIVMOD_2EXP 1 q0 in
   let (r2,a6)   = DIVMOD_2EXP 1 q1 in
   let (q0,b4)   = DIVMOD_2EXP 1 (DIV_2EXP 4 n) in
   let (q1,b5)   = DIVMOD_2EXP 1 q0 in
   let (q2,b6)   = DIVMOD_2EXP 1 q1 in
     (ODD r2,a6 = 1,a5 = 1,a4 = 1,
      ODD q2,b6 = 1,b5 = 1,b4 = 1)) /\
   ((BIT 8 m,BIT 7 m,BIT 6 m,BIT 5 m,BIT 11 n,BIT 10 n,BIT 9 n,BIT 8 n,
     BIT 7 n,BIT 6 n) =
   let (q0,a5)   = DIVMOD_2EXP 1 (DIV_2EXP 5 m) in
   let (q1,a6)   = DIVMOD_2EXP 1 q0 in
   let (r2,a7)   = DIVMOD_2EXP 1 q1 in
   let (q0,b6)   = DIVMOD_2EXP 1 (DIV_2EXP 6 n) in
   let (q1,b7)   = DIVMOD_2EXP 1 q0 in
   let (q2,b8)   = DIVMOD_2EXP 1 q1 in
   let (q3,b9)   = DIVMOD_2EXP 1 q2 in
   let (q4,b10)  = DIVMOD_2EXP 1 q3 in
     (ODD r2,a7 = 1,a6 = 1,a5 = 1,
      ODD q4,b10 = 1,b9 = 1,b8 = 1,b7 = 1,b6 = 1)) /\
   ((BIT 8 m,BIT 7 m,BIT 6 m,BIT 5 m,BIT 11 n) =
   let (q0,a5)   = DIVMOD_2EXP 1 (DIV_2EXP 5 m) in
   let (q1,a6)   = DIVMOD_2EXP 1 q0 in
   let (q2,a7)   = DIVMOD_2EXP 1 q1 in
   (ODD q2,a7 = 1,a6 = 1,a5 = 1,BIT 11 n))`,
  SRW_TAC [boolSimps.LET_ss]
     [BIT_def,BITS_THM,DIVMOD_2EXP_def,DIV_2EXP_def,DIV_1,
      DIV2_def,ODD_MOD2_LEM,DIV_DIV_DIV_MULT,MOD_2EXP_def]);

val n2w = CONJ (INST_TYPE [alpha |-> ``:16``] wordsTheory.word_index)
               (INST_TYPE [alpha |-> ``:32``] wordsTheory.word_index)
            |> SIMP_RULE (srw_ss()) [];

val EQ_BITS =
   wordsTheory.word_eq_n2w
     |> CONJUNCT1
     |> REWRITE_RULE
          [MOD_2EXP_EQ_def, MOD_2EXP_def, GSYM wordsTheory.dimword_def,
           wordsTheory.MOD_DIMINDEX];

fun rule l =
  SIMP_RULE std_ss [decode_lem] o
  SIMP_RULE (std_ss++wordsLib.WORD_ss++boolSimps.LET_ss)
    [n2w, EQ_BITS, BITS_COMP_THM2, BITS_ZERO2] o
  SIMP_RULE (std_ss++wordsLib.SIZES_ss)
    [InITBlock_def, LastInITBlock_def,
     wordsTheory.word_extract_n2w,
     wordsTheory.word_bits_n2w] o
  Q.SPECL l;

val arm_decode = rule [`v4`,`n2w n`] arm_decode_def;

val arm_decode_v4 = save_thm("arm_decode_v4",
  arm_decode
    |> Q.INST [`v4:bool` |-> `T`]
    |> REWRITE_RULE []);

val arm_decode_not_v4 = save_thm("arm_decode_not_v4",
  arm_decode
    |> Q.INST [`v4:bool` |-> `F`]
    |> REWRITE_RULE []);

val thumb_decode = save_thm("thumb_decode",
  rule [`arch`,`it`,`n2w n`] thumb_decode_def);

val thumbee_decode = save_thm("thumbee_decode",
  rule [`arch`,`it`,`n2w n`] thumbee_decode_def);

val thumb2_decode_aux1 = save_thm("thumb2_decode_aux1",
  rule [`n2w it`, `n2w m`, `n2w n`] thumb2_decode_aux1_def);

val thumb2_decode_aux2 = save_thm("thumb2_decode_aux2",
  rule [`n2w m`, `n2w n`] thumb2_decode_aux2_def);

val thumb2_decode_aux3 = save_thm("thumb2_decode_aux3",
  rule [`n2w m`, `n2w n`] thumb2_decode_aux3_def);

val thumb2_decode_aux4 = save_thm("thumb2_decode_aux4",
  rule [`n2w m`, `n2w n`] thumb2_decode_aux4_def);

val thumb2_decode_aux5 = save_thm("thumb2_decode_aux5",
  rule [`n2w m`, `n2w n`] thumb2_decode_aux5_def);

val thumb2_decode_aux6 = save_thm("thumb2_decode_aux6",
  rule [`n2w it`, `n2w m`, `n2w n`] thumb2_decode_aux6_def);

val thumb2_decode_aux7 = save_thm("thumb2_decode_aux7",
  rule [`n2w it`, `n2w m`, `n2w n`] thumb2_decode_aux7_def);

val thumb2_decode_aux8 = save_thm("thumb2_decode_aux8",
  rule [`n2w m`, `n2w n`] thumb2_decode_aux8_def);

val thumb2_decode_aux9 = save_thm("thumb2_decode_aux9",
  rule [`n2w m`, `n2w n`] thumb2_decode_aux9_def);

val thumb2_decode = save_thm("thumb2_decode",
  rule [`arch`,`n2w it`, `n2w m`, `n2w n`] thumb2_decode_def);

val _ = computeLib.add_persistent_funs
  ["arm_decode_v4",
   "arm_decode_not_v4",
   "thumb_decode",
   "thumbee_decode",
   "thumb2_decode_aux1",
   "thumb2_decode_aux2",
   "thumb2_decode_aux3",
   "thumb2_decode_aux4",
   "thumb2_decode_aux5",
   "thumb2_decode_aux6",
   "thumb2_decode_aux7",
   "thumb2_decode_aux8",
   "thumb2_decode_aux9",
   "thumb2_decode"];

(* ------------------------------------------------------------------------ *)

val _ = export_theory();
