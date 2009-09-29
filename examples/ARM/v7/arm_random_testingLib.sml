structure arm_random_testingLib :> arm_random_testingLib =
struct

(* interactive use:
  app load ["armLib"];
*)

open HolKernel boolLib bossLib Parse;
local open armLib in end;

(* ------------------------------------------------------------------------- *)

val ERR = Feedback.mk_HOL_ERR "arm_random_testingLib";

val arm_random_trace = ref true;

val _ = Feedback.register_btrace ("arm random", arm_random_trace);

datatype arch = ARMv4 | ARMv4T
              | ARMv5T | ARMv5TE
              | ARMv6 | ARMv6K | ARMv6T2
              | ARMv7_A | ARMv7_R | ARMv7_M;

datatype encoding = ARM | Thumb | Thumb2;

datatype class = DataProcessing | LoadStore | Branch
               | StatusAccess | Miscellaneous

(* ------------------------------------------------------------------------- *)

val generator = Random.newgen();
(* val generator = Random.newgenseed 1.0; *)

val eval = rhs o concl o EVAL;

fun dest_strip t =
let val (l,r) = strip_comb t in
  (fst (dest_const l), r)
end;

val is_T = term_eq T;
val is_F = term_eq F;

fun mk_bool b = if b then T else F;

fun pow2 0 = 1
  | pow2 n = 2 * pow2 (n - 1);

fun mk_word2  i = wordsSyntax.mk_wordii (i,2);
fun mk_word4  i = wordsSyntax.mk_wordii (i,4);
fun mk_word5  i = wordsSyntax.mk_wordii (i,5);
fun mk_word12 i = wordsSyntax.mk_wordii (i,12);

fun is_word4 n = term_eq (mk_word4 n);

fun random_range n = Random.range (0, n) generator;
fun random_const n = random_range (pow2 n);
fun random_from_list l = List.nth(l, random_range (length l));

local
  val sp = mk_word4 13
  val valid_modes = map mk_word5 [16,17,18,19,23,27,31]
  val valid_registers = map mk_word4 [0,1,2,3,6,7,8,9,10,11,12,13,14]
  val (_,valid_thumb2_registers) = Lib.pluck (fn t => t = sp) valid_registers
  val valid_thumb_registers = List.take(valid_thumb2_registers, 6)
in
  fun random_mode ()            = random_from_list valid_modes
  fun random_arm_register ()    = random_from_list valid_registers
  fun random_thumb_register ()  = random_from_list valid_thumb_registers
  fun random_thumb2_register () = random_from_list valid_thumb2_registers
end;

val int_of_word =
  Arbnum.toInt o numLib.dest_numeral o fst o wordsSyntax.dest_n2w;

fun test_or_compare i = (i div 4) = 2;

(* ------------------------------------------------------------------------- *)

fun random_term enc typ =
let val rand_term = random_term enc
    val pc = mk_word4 15
    fun r2 p t = case rand_term t
                 of [a,b] => p (a,b)
                  | _ => raise ERR "random_term" "r2"
    fun r3 p t = case rand_term t
                 of [a,b,c] => p (a,b,c)
                  | _ => raise ERR "random_term" "r3"
    fun r4 p t = case rand_term t
                 of [a,b,c,d] => p (a,b,c,d)
                  | _ => raise ERR "random_term" "r4"
    fun r5 p t = case rand_term t
                 of [a,b,c,d,e] => (p (a,b,c,d,e)
                      handle HOL_ERR g =>
                        (app (fn tm => (Hol_pp.print_term tm; print "\n"))
                           [a,b,c,d,e]; Raise (HOL_ERR g)))
                  | _ => raise ERR "random_term" "r5"
    fun r6 p t = case rand_term t
                 of [a,b,c,d,e,f] => p (a,b,c,d,e,f)
                  | _ => raise ERR "random_term" "r6"
    fun r7 p t = case rand_term t
                 of [a,b,c,d,e,f,g] => p (a,b,c,d,e,f,g)
                  | _ => raise ERR "random_term" "r7"
    fun r8 p t = case rand_term t
                 of [a,b,c,d,e,f,g,h] => p (a,b,c,d,e,f,g,h)
                  | _ => raise ERR "random_term" "r8"
    fun r9 p t = case rand_term t
                 of [a,b,c,d,e,f,g,h,i] => p (a,b,c,d,e,f,g,h,i)
                  | _ => raise ERR "random_term" "r9"
    fun dp () = case rand_term ``:word4 -> bool -> 'reg word -> 'reg word ->
                                  addressing_mode1``
                of [a,b,c,d,e] =>
                     let val opc = int_of_word a
                         val p = mk_word4 (if enc = ARM then 0 else 15)
                         val (rd,rn) = if test_or_compare opc then
                                         (p,c)
                                       else
                                         (d,if opc = 13 orelse opc = 15 andalso
                                               (enc <> Thumb2 orelse
                                                random_range 2 = 0)
                                            then p else c)
                         val sflag = if enc = Thumb orelse test_or_compare opc
                                     then T else b
                         val mode1 = if enc = Thumb andalso opc <> 13 andalso
                                        arm_astSyntax.is_Mode1_register e
                                     then
                                       arm_astSyntax.mk_Mode1_register
                                         (``0w:word5``,``0w:word2``,
                                          random_thumb_register ())
                                     else
                                       e
                     in
                       arm_astSyntax.mk_Data_Processing (a,sflag,rn,rd,mode1)
                     end
                 | _ => raise ERR "random_term" "dp"
    fun mul () = case rand_term ``:bool -> bool -> 'reg word -> 'reg word ->
                                  'reg word -> 'reg word``
                 of [a,b,c,d,e,f] =>
                     let val (acc,sflag) = if enc = Thumb then (F,T) else (a,b)
                     in arm_astSyntax.mk_Multiply (acc,sflag,c,d,e,f) end
                  | _ => raise ERR "random_term" "mul"
    fun ls () = case rand_term ``:bool -> bool -> bool -> bool ->
                                  'reg word -> 'reg word``
                of [p,u,b,w,n,t] =>
                     let val load = random_range 2 = 0
                         val immediate = (enc <> ARM andalso is_F p) orelse
                                         random_range 2 = 0
                         val imm_no_wb = immediate andalso is_F w
                         val rn = if imm_no_wb andalso random_range 4 = 0 then
                                    mk_word4
                                      (if load andalso random_range 2 = 0
                                       then 15 else 13)
                                  else
                                    n
                         val p = if enc = Thumb then T else p
                         val w = mk_bool (enc = ARM andalso is_T w orelse
                                          is_F p)
                         val wide = imm_no_wb andalso is_T p andalso is_T u
                         val unpriv =
                                    case enc
                                    of Thumb => false
                                     | Thumb2 => wide andalso random_range 3 = 0
                                     | ARM => is_F p andalso is_T w
                         val (u,mode2) =
                                     if immediate then
                                       (if wide then T else u,
                                        arm_astSyntax.mk_Mode2_immediate
                                          (mk_word12 (random_const
                                             (if enc = ARM orelse
                                                 enc = Thumb2 andalso
                                                 wide andalso not unpriv
                                              then 12 else
                                                if enc <> Thumb orelse
                                                   is_word4 13 rn orelse
                                                   is_word4 15 rn
                                                then 8 else 5))))
                                     else
                                       (if enc = ARM then u else T,
                                        arm_astSyntax.mk_Mode2_register
                                          (mk_word5 (random_const
                                            (case enc
                                             of Thumb => 0
                                              | Thumb2 => 2
                                              | ARM => 5)),
                                           mk_word2 (random_const
                                             (if enc = ARM then 2 else 0)),
                                           hd (rand_term ``:'reg word``)))
                     in
                       (if load then arm_astSyntax.mk_Load
                                else arm_astSyntax.mk_Store)
                         (p,u,b,w,mk_bool unpriv,rn,t,mode2)
                     end
                 | _ => raise ERR "random_term" "ls"
    fun lsh () = case rand_term ``:bool -> bool -> bool -> bool -> bool ->
                                  'reg word -> 'reg word -> addressing_mode3``
                 of [p,u,w,s,h,n,t,mode3] =>
                      let val load = random_range 2 = 0
                          val immediate = arm_astSyntax.is_Mode3_immediate mode3
                          val imm_no_wb = immediate andalso is_F w
                          val p = if enc = Thumb orelse enc <> ARM andalso
                                     not immediate
                                  then T else p
                          val w = mk_bool (enc = ARM andalso is_T w orelse
                                           is_F p)
                          val wide = imm_no_wb andalso is_T p andalso is_T u
                          val unpriv =
                                     case enc
                                     of Thumb => false
                                      | Thumb2 => wide andalso
                                                  random_range 3 = 0
                                      | ARM => is_F p andalso is_T w
                          val u = if immediate then
                                    if wide then T else u
                                  else
                                    if enc = ARM then u else T
                          val mode3 = if enc = Thumb2 andalso immediate andalso
                                         wide andalso not unpriv
                                      then
                                        arm_astSyntax.mk_Mode3_immediate
                                          (mk_word12 (random_const 12))
                                      else
                                        mode3
                          val h = if is_F s andalso is_F h then T else h
                      in
                        if load then
                          arm_astSyntax.mk_Load_Halfword
                            (p,u,w,s,h,mk_bool unpriv,n,t,mode3)
                        else
                          arm_astSyntax.mk_Store_Halfword
                            (p,u,w,mk_bool unpriv,n,t,mode3)
                      end
                  | _ => raise ERR "random_term" "lsh"
    fun lsm () = case rand_term ``:bool -> bool -> bool -> 'reg word``
                 of [p,u,w,n] =>
                       let val load = random_range 2 = 0
                           val u = if enc = ARM then u else mk_bool (is_F p)
                           val s = mk_bool
                                     (enc = ARM andalso random_range 5 = 0)
                           val n = if random_range 2 = 0 then mk_word4 13 else n
                           val list = wordsSyntax.mk_wordii
                                        (random_const
                                           (if enc = Thumb then 8 else 13), 16)
                           val list = if (enc = Thumb andalso is_word4 13 n
                                          orelse enc = ARM) andalso
                                         random_range 3 = 0
                                      then
                                        let val p = if load
                                                      then ``15n``
                                                      else ``14n``
                                        in eval ``(^p :+ T) ^list`` end
                                      else
                                        list
                       in
                         (if load then arm_astSyntax.mk_Load_Multiple
                                  else arm_astSyntax.mk_Store_Multiple)
                           (p,u,s,w,n,list)
                       end
                  | _ => raise ERR "random_term" "lsm"
    fun double () = if enc = ARM then
                      let val n = 2 * random_range 7 in
                        (mk_word4 n, mk_word4 (n + 1))
                      end
                    else
                      r2 I ``:'reg word -> 'reg word``
    fun lsd p = case rand_term ``:bool -> bool -> bool -> 'reg word ->
                                  addressing_mode3``
                of [a,b,c,d,e] =>
                     let val (t,t2) = double () in
                       p (a,b,c,d,t,t2,e)
                     end
                 | _ => raise ERR "random_term" "lsd"
in
  case dest_type typ
  of ("fun", [h,t]) => (rand_term h) @ (rand_term t)
   | ("bool", []) => [random_from_list [T,F]]
   | ("prod", [a,b]) =>
       [pairSyntax.mk_pair (hd (rand_term a), hd (rand_term b))]
   | ("option", [t]) =>
       [if random_range 4 = 0 then
          optionSyntax.mk_none (if t = ``:'mode word`` then ``:word5`` else t)
        else
          optionSyntax.mk_some (hd (rand_term t))]
   | ("cart", [b, n]) =>
       (if b = bool then
          if n = ``:'reg`` orelse n = ``:'areg`` andalso random_range 2 = 0 then
            [case enc
             of ARM => random_arm_register ()
              | Thumb => random_thumb_register ()
              | Thumb2 => random_thumb2_register ()]
          else if n = ``:'areg`` then
            [pc]
          else if n = ``:'mode`` then
            [random_mode ()]
          else let val n = Arbnum.toInt (fcpLib.index_to_num n) in
            [wordsSyntax.mk_wordii (random_const n, n)]
          end
        else
          raise ERR "random_term" "cart")
   | ("addressing_mode1", []) =>
       [case random_range (if enc = Thumb then 2 else 3)
        of 0 => arm_astSyntax.mk_Mode1_immediate
                  (wordsSyntax.mk_wordii
                     (random_const (if enc = Thumb then 8 else 12), 12))
         | 1 => r3 arm_astSyntax.mk_Mode1_register
                   ``:word5 -> word2 -> 'reg word``
         | 2 => r3 arm_astSyntax.mk_Mode1_register_shifted_register
                   ``:'reg word -> word2 -> 'reg word``
         | _ => raise ERR "random_term" "addressing_mode1"]
   | ("addressing_mode3", []) =>
       [case random_range 2
        of 0 => arm_astSyntax.mk_Mode3_immediate
                  (mk_word12 (random_const (if enc = Thumb then 5 else 8)))
         | 1 => arm_astSyntax.mk_Mode3_register
                  (mk_word2 (random_const (if enc = Thumb2 then 2 else 0)),
                   hd (rand_term ``:'reg word``))
         | _ => raise ERR "random_term" "addressing_mode3"]
   | ("parallel_add_sub_op1", []) =>
       [random_from_list [arm_astSyntax.Parallel_normal_tm,
                          arm_astSyntax.Parallel_saturating_tm,
                          arm_astSyntax.Parallel_halving_tm]]
   | ("parallel_add_sub_op2", []) =>
       [random_from_list [arm_astSyntax.Parallel_add_16_tm,
                          arm_astSyntax.Parallel_add_sub_exchange_tm,
                          arm_astSyntax.Parallel_sub_add_exchange_tm,
                          arm_astSyntax.Parallel_sub_16_tm,
                          arm_astSyntax.Parallel_add_8_tm,
                          arm_astSyntax.Parallel_sub_8_tm]]
   | ("hint", []) =>
       [random_from_list [arm_astSyntax.Hint_nop_tm,
                          arm_astSyntax.Hint_yield_tm,
                          arm_astSyntax.Hint_wait_for_event_tm,
                          arm_astSyntax.Hint_wait_for_interrupt_tm,
                          arm_astSyntax.Hint_send_event_tm,
                          arm_astSyntax.mk_Hint_debug
                            (hd (rand_term ``:word4``))]]
   | ("branch_instruction", []) =>
       [case random_range 6
        of 0 => arm_astSyntax.mk_Branch_Target (hd (rand_term ``:word24``))
         | 1 => arm_astSyntax.mk_Branch_Exchange (hd (rand_term ``:'reg word``))
         | 2 => r3 arm_astSyntax.mk_Branch_Link_Exchange_Immediate
                     ``:bool -> bool -> word24``
         | 3 => arm_astSyntax.mk_Branch_Link_Exchange_Register
                     (hd (rand_term ``:'reg word``))
         | 4 => r3 arm_astSyntax.mk_Compare_Branch ``:bool -> word6 -> word3``
         | 5 => r3 arm_astSyntax.mk_Table_Branch_Byte
                     ``:'reg word -> bool -> 'reg word``
         | _ => raise ERR "random_term" "branch_instruction"]
   | ("data_processing_instruction", []) =>
       if random_range 3 = 0 then
         [dp ()]
       else
         [case random_range (if enc = Thumb then 8 else 30)
          of 0 => dp ()
           | 1 => r4 arm_astSyntax.mk_Add_Sub
                     ``:bool -> 'reg word -> 'reg word -> word12``
           | 2 => mul ()
           | 3 => r5 arm_astSyntax.mk_Extend_Byte
                     ``:bool -> 'areg word -> 'reg word -> word2 -> 'reg word``
           | 4 => r5 arm_astSyntax.mk_Extend_Halfword
                     ``:bool -> 'areg word -> 'reg word -> word2 -> 'reg word``
           | 5 => r2 arm_astSyntax.mk_Byte_Reverse_Word
                     ``:'reg word -> 'reg word``
           | 6 => r2 arm_astSyntax.mk_Byte_Reverse_Packed_Halfword
                     ``:'reg word -> 'reg word``
           | 7 => r2 arm_astSyntax.mk_Byte_Reverse_Signed_Halfword
                     ``:'reg word -> 'reg word``
           | 8 => r3 arm_astSyntax.mk_Move_Halfword
                     ``:bool -> 'reg word -> word16``
           | 9 => r4 arm_astSyntax.mk_Multiply_Subtract
                     ``:'reg word -> 'reg word -> 'reg word -> 'reg word``
           | 10 => r7 arm_astSyntax.mk_Signed_Halfword_Multiply
                     ``:word2 -> bool -> bool -> 'reg word -> 'reg word ->
                        'reg word -> 'reg word``
           | 11 => r6 arm_astSyntax.mk_Signed_Multiply_Dual
                     ``:'reg word -> 'areg word -> 'reg word -> bool -> bool ->
                        'reg word``
           | 12 => r6 arm_astSyntax.mk_Signed_Multiply_Long_Dual
                     ``:'reg word -> 'reg word -> 'reg word -> bool -> bool ->
                        'reg word``
           | 13 => r5 arm_astSyntax.mk_Signed_Most_Significant_Multiply
                     ``:'reg word -> 'areg word -> 'reg word -> bool ->
                        'reg word``
           | 14 => r5 arm_astSyntax.mk_Signed_Most_Significant_Multiply_Subtract
                     ``:'reg word -> 'reg word -> 'reg word -> bool ->
                        'reg word``
           | 15 => r7 arm_astSyntax.mk_Multiply_Long
                     ``:bool -> bool -> bool -> 'reg word -> 'reg word ->
                        'reg word -> 'reg word``
           | 16 => r4 arm_astSyntax.mk_Multiply_Accumulate_Accumulate
                     ``:'reg word -> 'reg word -> 'reg word -> 'reg word``
           | 17 => r6 arm_astSyntax.mk_Saturate
                     ``:bool -> word5 -> 'reg word -> word5 -> bool ->
                        'reg word``
           | 18 => r4 arm_astSyntax.mk_Saturate_16
                     ``:bool -> word4 -> 'reg word -> 'reg word``
           | 19 => r4 arm_astSyntax.mk_Saturating_Add_Subtract
                     ``:word2 -> 'reg word -> 'reg word -> 'reg word``
           | 20 => r5 arm_astSyntax.mk_Pack_Halfword
                     ``:'reg word -> 'reg word -> word5 -> bool -> 'reg word``
           | 21 => r5 arm_astSyntax.mk_Extend_Byte_16
                     ``:bool -> 'areg word -> 'reg word -> word2 -> 'reg word``
           | 22 => r4 arm_astSyntax.mk_Bit_Field_Clear_Insert
                     ``:word5 -> 'reg word -> word5 -> 'areg word``
           | 23 => r2 arm_astSyntax.mk_Count_Leading_Zeroes
                     ``:'reg word -> 'reg word``
           | 24 => r2 arm_astSyntax.mk_Reverse_Bits
                     ``:'reg word -> 'reg word``
           | 25 => r5 arm_astSyntax.mk_Bit_Field_Extract
                     ``:bool -> word5 -> 'reg word -> word5 -> 'reg word``
           | 26 => r3 arm_astSyntax.mk_Select_Bytes
                     ``:'reg word -> 'reg word -> 'reg word``
           | 27 => r4 arm_astSyntax.mk_Unsigned_Sum_Absolute_Differences
                     ``:'reg word -> 'areg word -> 'reg word -> 'reg word``
           | 28 => r5 arm_astSyntax.mk_Parallel_Add_Subtract
                     ``:bool -> parallel_add_sub_op1 # parallel_add_sub_op2 ->
                        'reg word -> 'reg word -> 'reg word``
           | 29 => r4 arm_astSyntax.mk_Divide
                     ``:bool -> 'reg word -> 'reg word -> 'reg word``
           | _ => raise ERR "random_term" "data_processing_instruction"]
   | ("status_access_instruction", []) =>
       [case random_range 5
        of 0 => r2 arm_astSyntax.mk_Status_to_Register ``:bool -> 'reg word``
         | 1 => r3 arm_astSyntax.mk_Register_to_Status
                     ``:bool -> word4 -> 'reg word``
         | 2 => r3 arm_astSyntax.mk_Immediate_to_Status
                     ``:bool -> word4 -> word12``
         | 3 => r5 arm_astSyntax.mk_Change_Processor_State
                     ``:word2 -> bool -> bool -> bool -> 'mode word option``
         | 4 => arm_astSyntax.mk_Set_Endianness (hd (rand_term ``:bool``))
         | _ => raise ERR "random_term" "status_access_instruction"]
   | ("load_store_instruction", []) =>
      [if random_range 3 = 0 then
         ls ()
       else if random_range 2 = 0 then
         lsh ()
       else if enc = Thumb orelse random_range 2 = 0 then
         lsm ()
       else
         case random_range 12
         of 0 => lsd arm_astSyntax.mk_Load_Dual
          | 1 => lsd arm_astSyntax.mk_Store_Dual
          | 2 => r3 arm_astSyntax.mk_Load_Exclusive
                      ``:'reg word -> 'reg word -> word8``
          | 3 => r4 arm_astSyntax.mk_Store_Exclusive
                      ``:'reg word -> 'reg word -> 'reg word -> word8``
          | 4 => let val (t,t2) = double () in
                   arm_astSyntax.mk_Load_Exclusive_Doubleword
                     (hd (rand_term  ``:'reg word``), t, t2)
                 end
          | 5 => let val (t,t2) = double ()
                     val (n,d) = r2 I ``:'reg word -> 'reg word``
                 in
                   arm_astSyntax.mk_Store_Exclusive_Doubleword (n,d,t,t2)
                 end
          | 6 => r2 arm_astSyntax.mk_Load_Exclusive_Halfword
                      ``:'reg word -> 'reg word``
          | 7 => r3 arm_astSyntax.mk_Store_Exclusive_Halfword
                      ``:'reg word -> 'reg word -> 'reg word``
          | 8 => r2 arm_astSyntax.mk_Load_Exclusive_Byte
                      ``:'reg word -> 'reg word``
          | 9 => r3 arm_astSyntax.mk_Store_Exclusive_Byte
                      ``:'reg word -> 'reg word -> 'reg word``
          | 10 => r4 arm_astSyntax.mk_Store_Return_State
                      ``:bool -> bool -> bool -> 'mode word``
          | 11 => r4 arm_astSyntax.mk_Return_From_Exception
                      ``:bool -> bool -> bool -> 'reg word``
          | _ => raise ERR "random_term" "load_store_instruction"]
   | ("miscellaneous_instruction", []) =>
       [case enc
        of Thumb =>
             (case random_range 4
              of 0 => arm_astSyntax.mk_Hint (hd (rand_term ``:hint``))
               | 1 => arm_astSyntax.mk_Breakpoint
                        (wordsSyntax.mk_wordii
                           (random_const (if enc = ARM then 16 else 8), 16))
               | 2 => arm_astSyntax.mk_Supervisor_Call
                        (wordsSyntax.mk_wordii
                           (random_const (if enc = ARM then 24 else 8), 24))
               | 3 => r2 arm_astSyntax.mk_If_Then ``:word4 -> word4``
               | _ => raise ERR "random_term" "miscellaneous_instruction")
         | Thumb2 =>
             (case random_range 6
              of 0 => arm_astSyntax.mk_Hint (hd (rand_term ``:hint``))
               | 1 => arm_astSyntax.mk_Data_Memory_Barrier
                        (hd (rand_term ``:word4``))
               | 2 => arm_astSyntax.mk_Data_Synchronization_Barrier
                        (hd (rand_term ``:word4``))
               | 3 => arm_astSyntax.mk_Instruction_Synchronization_Barrier
                        (hd (rand_term ``:word4``))
               | 4 => arm_astSyntax.mk_Secure_Monitor_Call
                        (hd (rand_term ``:word4``))
               | 5 => arm_astSyntax.mk_Miscellaneous
                        arm_astSyntax.Clear_Exclusive_tm
               | _ => raise ERR "random_term" "miscellaneous_instruction")
         | ARM =>
             (case random_range 9
              of 0 => arm_astSyntax.mk_Hint (hd (rand_term ``:hint``))
               | 1 => arm_astSyntax.mk_Breakpoint
                        (wordsSyntax.mk_wordii
                           (random_const (if enc = ARM then 16 else 8), 16))
               | 2 => arm_astSyntax.mk_Supervisor_Call
                        (wordsSyntax.mk_wordii
                           (random_const (if enc = ARM then 24 else 8), 24))
               | 3 => arm_astSyntax.mk_Data_Memory_Barrier
                        (hd (rand_term ``:word4``))
               | 4 => arm_astSyntax.mk_Data_Synchronization_Barrier
                        (hd (rand_term ``:word4``))
               | 5 => arm_astSyntax.mk_Instruction_Synchronization_Barrier
                        (hd (rand_term ``:word4``))
               | 6 => r4 arm_astSyntax.mk_Swap
                        ``:bool -> 'reg word -> 'reg word -> 'reg word``
               | 7 => arm_astSyntax.mk_Secure_Monitor_Call
                        (hd (rand_term ``:word4``))
               | 8 => arm_astSyntax.mk_Miscellaneous
                        arm_astSyntax.Clear_Exclusive_tm
               | _ => raise ERR "random_term" "miscellaneous_instruction")]
   | _ => raise ERR "random_term" (type_to_string typ)
end

(* ------------------------------------------------------------------------- *)

local
  fun try_dest_label thm = markerLib.DEST_LABEL thm handle HOL_ERR _ => thm;
  fun reg tm = mk_var ("r" ^ Int.toString (int_of_word tm), ``:word32``);
  fun flag tm = mk_var (fst (dest_const tm), bool);
  val cpsr = mk_var ("cpsr", ``:ARMpsr``)
  val GE   = mk_var ("GE", ``:word4``)
  val IT   = mk_var ("IT", ``:word8``)
  val mode = mk_var ("mode", ``:word5``)
  val mem  = mk_var ("mem", ``:word32 -> word8 option``)

  fun is_read tm =
       (case dest_strip tm
        of ("ARM_READ_REG", [_,_])    => true
         | ("ARM_READ_MEM", [_,_])    => true
         | ("ARM_READ_STATUS", [_,_]) => true
         | ("ARM_READ_SCTLR", [_,_])  => true
         | ("ARM_READ_CPSR", [_])     => true
         | ("ARM_READ_GE", [_])       => true
         | ("ARM_READ_IT", [_])       => true
         | ("ARM_MODE", [_])          => true
         | _ => false) handle HOL_ERR _ => false;

  fun component_subst tm =
        tm |-> (case dest_strip tm
                of ("ARM_READ_REG", [a,_])    => reg a
                 | ("ARM_READ_MEM", [a,_])    => mk_comb (mem, a)
                 | ("ARM_READ_STATUS", [a,_]) => flag a
                 | ("ARM_READ_SCTLR", [a,_])  => flag a
                 | ("ARM_READ_CPSR", _)       => cpsr
                 | ("ARM_READ_GE", _)         => GE
                 | ("ARM_READ_IT", _)         => IT
                 | ("ARM_MODE", _)            => mode
                 | _ => raise ERR "component_subst" "")

  fun component_substs tm =
        Term.subst (map component_subst (find_terms is_read tm)) tm

  val component_substs = component_substs o component_substs;

  fun get_updates tm =
  let
    fun recurse tm l =
         (case dest_strip tm
          of ("ARM_WRITE_MEM", [a,d,s]) => recurse s ((mk_comb (mem,a), d)::l)
           | ("ARM_WRITE_REG", [a,d,s]) => recurse s ((reg a, d)::l)
           | ("ARM_WRITE_STATUS", [f,d,s]) => recurse s ((flag f,d)::l)
           | ("ARM_WRITE_SCTLR", [f,d,s]) => recurse s ((flag f,d)::l)
           | ("ARM_WRITE_CPSR", [d,s]) => recurse s ((cpsr,d)::l)
           | ("ARM_WRITE_GE", [d,s]) => recurse s ((GE,d)::l)
           | ("ARM_WRITE_IT", [d,s]) => recurse s ((IT,d)::l)
           | (_,tml) => recurse (last tml) l) handle HOL_ERR _ => List.rev l
  in
    recurse (component_substs tm) []
  end
in
  fun step_updates arch (opc,ass:string,arm) =
    let val opt = arch ^ ", " ^ (if arm then "arm" else "thumb")
        val _ = if !arm_random_trace then
                  print (String.concat ["Processing... ", ass, "\n"])
                else
                  ()
        val tm = opc |> try (armLib.arm_step opt)
                     |> try_dest_label
                     |> SPEC_ALL |> concl
        val (l,r) = boolSyntax.dest_imp tm
    in
      (opc,ass,
       l |> component_substs
         |> boolSyntax.strip_conj
         |> (fn l => List.drop(l,8)),
       r |> boolSyntax.dest_eq |> snd
         |> optionSyntax.dest_some
         |> get_updates)
    end
end;

local
  fun remove_duplicates l =
  let fun recurse (h1::h2::t) l =
            recurse (h2::t) (if h1 = h2 then l else h1::l)
        | recurse [h] l = List.rev (h::l)
        | recurse [] l = List.rev l
  in
    recurse l []
  end

  fun encoding Thumb  = armSyntax.Encoding_Thumb_tm
    | encoding Thumb2 = armSyntax.Encoding_Thumb2_tm
    | encoding ARM    = armSyntax.Encoding_ARM_tm

  fun disassemble c =
        let val (l,r) = armLib.arm_disassemble c in l ^ " " ^ r end

  fun decode arm n =
        let val c = if arm then
                      armLib.arm_decode n
                    else
                      armLib.thumb_decode 0 n
        in
          case c
          of armLib.Instruction (_,_,tm) => tm | _ => raise ERR "decode" ""
        end

  fun arm_uncoditional tm =
        arm_astSyntax.is_Branch_Link_Exchange_Immediate tm andalso
          (let val (_,toarm,_) =
                      arm_astSyntax.dest_Branch_Link_Exchange_Immediate tm
           in
             toarm = F
           end) orelse
        arm_astSyntax.is_Preload_Instruction tm orelse
        term_eq arm_astSyntax.Clear_Exclusive_tm tm orelse
        arm_astSyntax.is_Data_Synchronization_Barrier tm orelse
        arm_astSyntax.is_Data_Memory_Barrier tm orelse
        arm_astSyntax.is_Instruction_Synchronization_Barrier tm orelse
        arm_astSyntax.is_Preload_Data tm orelse
        arm_astSyntax.is_Store_Return_State tm orelse
        arm_astSyntax.is_Return_From_Exception tm orelse
        arm_astSyntax.is_Set_Endianness tm orelse
        arm_astSyntax.is_Change_Processor_State tm orelse
        arm_astSyntax.is_Coprocessor tm andalso random_range 2 = 0

  fun mk_code arch (code as (enc, _, tm)) =
    let val arm = enc = armSyntax.Encoding_ARM_tm
        val c = armLib.Instruction code
        val e = armLib.arm_encode c
        val s = disassemble c
        val a = arch ^ (if arm then s else "THUMB\n " ^ s)
        val d = a |> with_flag (Feedback.emit_WARNING,false)
                       armLib.arm_assemble_from_string |> hd |> snd
        val _ = if d <> e then
                  HOL_WARNING "arm_randomLib" "mk_code" (String.concat
                    ["<<parse warning>>:", "\n",
                     a, "\n",
                     Hol_pp.term_to_string tm, "\n",
                     "\t", e, " =/= ", d, "\n",
                     Hol_pp.term_to_string (decode arm d), "\n"])
                 else
                   ()
    in
      (e,a,arm)
    end handle HOL_ERR e =>
          (HOL_WARNING (#origin_structure e) (#origin_function e)
             (String.concat
                [Hol_pp.term_to_string enc, ": ",
                 Hol_pp.term_to_string tm, "\n"]);
           raise HOL_ERR e)

  fun arch_to_string a =
    case a
    of ARMv4   => "ARMv4"
     | ARMv4T  => "ARMv4T"
     | ARMv5T  => "ARMv5T"
     | ARMv5TE => "ARMv5TE"
     | ARMv6   => "ARMv6"
     | ARMv6K  => "ARMv6K"
     | ARMv6T2 => "ARMv6T2"
     | ARMv7_A => "ARMv7-A"
     | ARMv7_R => "ARMv7-R"
     | ARMv7_M => "ARMv7-M"

  fun arch_to_ecodings a =
    case a
    of ARMv4   => [ARM]
     | ARMv4T  => [ARM, Thumb]
     | ARMv5T  => [ARM, Thumb]
     | ARMv5TE => [ARM, Thumb]
     | ARMv6   => [ARM, Thumb]
     | ARMv6K  => [ARM, Thumb]
     | ARMv6T2 => [ARM, Thumb, Thumb2]
     | ARMv7_A => [ARM, Thumb, Thumb2]
     | ARMv7_R => [ARM, Thumb, Thumb2]
     | ARMv7_M => [Thumb, Thumb2]

  fun random_code encs typ =
        let val enc = random_from_list encs
            val tm = hd (random_term enc typ)
            val cond = mk_word4
                         (if enc = ARM andalso arm_uncoditional tm
                          then 15 else 14)
        in
          (encoding enc, cond, tm)
        end

   fun compare_code ((a,_,b),(c,_,d)) =
         Lib.pair_compare (Term.compare,Term.compare) ((a,b),(c,d))
in
  fun generate_random arch n class =
    let val a = arch_to_string arch
        val aa = String.concat ["ARCH ", a, "\n "]
        val typ = case class
                  of DataProcessing => ``:data_processing_instruction``
                   | LoadStore      => ``:load_store_instruction``
                   | Branch         => ``:branch_instruction``
                   | StatusAccess   => ``:status_access_instruction``
                   | Miscellaneous  => ``:miscellaneous_instruction``
    in
      (n, fn i => random_code (arch_to_ecodings arch) typ)
        |> List.tabulate
        |> Listsort.sort compare_code
        |> remove_duplicates
        |> Lib.mapfilter (step_updates a o mk_code aa)
    end
end;

end;
