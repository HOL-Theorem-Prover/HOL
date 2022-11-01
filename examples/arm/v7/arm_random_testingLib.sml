structure arm_random_testingLib :> arm_random_testingLib =
struct

open HolKernel boolLib bossLib Parse;
local open armLib in end;

(* ------------------------------------------------------------------------- *)

val ERR = Feedback.mk_HOL_ERR "arm_random_testingLib";

val arm_random_trace = ref true;

val _ = Feedback.register_btrace ("arm random", arm_random_trace);

datatype arch = ARMv4 | ARMv4T
              | ARMv5T | ARMv5TE
              | ARMv6 | ARMv6K | ARMv6T2
              | ARMv7_A | ARMv7_R;

datatype encoding = ARM | Thumb | Thumb2 | ThumbEE;

datatype class = DataProcessing | LoadStore | Branch
               | StatusAccess | Miscellaneous

datatype step_output
  = Simple_step of (term * term) list
  | Conditional_step of term * (term * term) list * (term * term) list

(* ------------------------------------------------------------------------- *)

local
  val tm_g = Parse.term_grammar ()
  val ty_g = Parse.type_grammar ()
in
  val term_to_string =
        PP.pp_to_string 70
          (Parse.mlower o term_pp.pp_term tm_g ty_g PPBackEnd.raw_terminal)
end

val generator = Random.newgen();
(* val generator = Random.newgenseed 1.0; *)

val eval = rhs o concl o EVAL;

val dest_strip = armSyntax.dest_strip;

val is_T = term_eq T;
val is_F = term_eq F;

val is_PC = term_eq ``15w:word4``;

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
  val regs = List.map mk_word4
  val sp = mk_word4 13
  val valid_modes = List.map mk_word5 [16,17,18,19,23,27,31]
  val valid_registers = regs [2,3,4,5,6,7,8,9,10,11,12,13,14]
  val valid_thumb2_registers = regs [2,3,4,5,6,7,8,9,10,11,12,14]
  val valid_thumb_registers = regs [2,3,4,5,6,7]
in
  fun random_mode ()            = random_from_list valid_modes
  fun random_arm_register ()    = random_from_list valid_registers
  fun random_thumb_register ()  = random_from_list valid_thumb_registers
  fun random_thumb2_register () = random_from_list valid_thumb2_registers
end;

fun test_or_compare i = (i div 4) = 2;

fun version_number a =
  case a
  of ARMv4   => 4
   | ARMv4T  => 4
   | ARMv5T  => 5
   | ARMv5TE => 5
   | ARMv6   => 6
   | ARMv6K  => 6
   | ARMv6T2 => 6
   | ARMv7_A => 7
   | ARMv7_R => 7;

(* ------------------------------------------------------------------------- *)

fun data_processing_list n enc =
  List.tabulate (4, fn _ => 0) @
  List.tabulate
    (if n < 6 then 3 else
      case enc
      of Thumb   => 8
       | ThumbEE => 8
       | Thumb2  => 30
       | ARM     => 29, I) @
   (if n = 5 andalso enc = ARM then [23] else []);

fun random_term arch enc typ =
let val rand_term = random_term arch enc
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
                     let val opc = wordsSyntax.uint_of_word a
                         val p = mk_word4 (if enc = ARM then 0 else 15)
                         val (rd,rn) = if test_or_compare opc then
                                         (p,c)
                                       else
                                         (d,if opc = 13 orelse opc = 15 andalso
                                                (enc <> Thumb2 orelse
                                                 random_range 2 = 0)
                                            then p else c)
                         val sflag = if enc = Thumb orelse enc = ThumbEE orelse
                                        test_or_compare opc
                                     then T else b
                         val mode1 = if (enc = Thumb orelse enc = ThumbEE)
                                        andalso opc <> 13 andalso
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
                     let val (acc,sflag,rm) =
                                 if enc = Thumb orelse enc = ThumbEE
                                 then (F,T,c) else (a,b,e)
                     in arm_astSyntax.mk_Multiply (acc,sflag,c,d,rm,f) end
                  | _ => raise ERR "random_term" "mul"
    fun ls () = case rand_term ``:bool -> bool -> bool -> bool ->
                                  'reg word -> 'reg word``
                of [p,u,b,w,n,t] =>
                     let val load = random_range 2 = 0
                         val p = if enc = Thumb orelse enc = ThumbEE
                                 then T else p
                         val immediate = (enc <> ARM andalso is_F p) orelse
                                         random_range 2 = 0
                         val w = mk_bool (enc = ARM andalso is_T w orelse
                                          is_F p)
                         val imm_no_wb = immediate andalso is_F w
                         val rn = if imm_no_wb andalso random_range 2 = 0 then
                                    mk_word4
                                      (if load andalso random_range 4 < 3
                                       then 15 else 13)
                                  else
                                    n
                         val wide = imm_no_wb andalso is_T p andalso is_T u
                         val unpriv =
                                  case enc
                                  of Thumb   => false
                                   | ThumbEE => false
                                   | Thumb2  => wide andalso random_range 3 = 0
                                   | ARM     => is_F p andalso is_T w
                         val (u,mode2) =
                                     if immediate then
                                       (if wide then T else u,
                                        arm_astSyntax.mk_Mode2_immediate
                                          (mk_word12 (random_const
                                            (if is_PC rn
                                             then 4
                                             else
                                               if enc = ARM orelse
                                                  enc = Thumb2 andalso
                                                  wide andalso not unpriv
                                               then 12
                                               else
                                                 if enc = ARM orelse
                                                    enc = Thumb2  orelse
                                                    is_word4 13 rn orelse
                                                    is_word4 15 rn
                                                 then 8 else 5))))
                                     else
                                       (if enc = ARM then u else T,
                                        arm_astSyntax.mk_Mode2_register
                                          (mk_word5 (random_const
                                            (case enc
                                             of Thumb   => 0
                                              | ThumbEE => 2
                                              | Thumb2  => 2
                                              | ARM     => 5)),
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
                          val p = if enc = Thumb orelse enc = ThumbEE orelse
                                     enc <> ARM andalso not immediate
                                  then T else p
                          val w = mk_bool (enc = ARM andalso is_T w orelse
                                           is_F p)
                          val imm_no_wb = immediate andalso is_F w
                          val wide = imm_no_wb andalso is_T p andalso is_T u
                          val unpriv =
                                     case enc
                                     of Thumb   => false
                                      | ThumbEE => false
                                      | Thumb2  => wide andalso
                                                   random_range 3 = 0
                                      | ARM     => is_F p andalso is_T w
                          val u = if immediate then
                                    if wide then T else u
                                  else
                                    if enc = ARM then u else T
                          val rn = if load andalso imm_no_wb andalso
                                      (enc = ARM orelse enc = Thumb2) andalso
                                      random_range 3 = 0
                                   then
                                     pc
                                   else
                                     n
                          val mode3 = if enc = Thumb2 andalso immediate andalso
                                         wide andalso not unpriv
                                      then
                                        arm_astSyntax.mk_Mode3_immediate
                                          (mk_word12 (random_const
                                             (if is_PC rn then 4 else 12)))
                                      else
                                        mode3
                          val h = if is_F s andalso is_F h then T else h
                      in
                        if load then
                          arm_astSyntax.mk_Load_Halfword
                            (p,u,w,s,h,mk_bool unpriv,rn,t,mode3)
                        else
                          arm_astSyntax.mk_Store_Halfword
                            (p,u,w,mk_bool unpriv,rn,t,mode3)
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
                                           (if enc = Thumb orelse enc = ThumbEE
                                            then 8 else 16), 16)
                           val list = wordsSyntax.mk_word_and(list,
                                        ``0b0101111111111100w:word16``) |> eval
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
    fun lsd load = case rand_term ``:bool -> bool -> bool -> 'reg word ->
                                  addressing_mode3``
                of [a,b,c,d,e] =>
                     let val (t,t2) = double ()
                         val (rn,mode3) =
                                  if load andalso random_range 3 = 0 andalso
                                     arm_astSyntax.is_Mode3_immediate e andalso
                                     (enc = Thumb2 orelse is_T a) andalso
                                     is_T b andalso is_F d
                                  then
                                    (pc,
                                     arm_astSyntax.mk_Mode3_immediate
                                       (mk_word12 (random_const 4)))
                                  else
                                    (d,e)
                     in
                       (if load then
                          arm_astSyntax.mk_Load_Dual
                        else
                          arm_astSyntax.mk_Store_Dual)
                         (a,b,c,rn,t,t2,mode3)
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
             of ARM     => random_arm_register ()
              | Thumb   => random_thumb_register ()
              | ThumbEE => random_thumb_register ()
              | Thumb2  => random_thumb2_register ()]
          else if n = ``:'areg`` then
            [pc]
          else if n = ``:'mode`` then
            [random_mode ()]
          else if n = ``:'offset`` then
            [let val i = wordsSyntax.mk_wordii (random_const 5, 24) in
               if random_range 2 = 0 then
                 eval (wordsSyntax.mk_word_2comp i)
               else
                 i
             end]
          else let val n = Arbnum.toInt (fcpLib.index_to_num n) in
            [wordsSyntax.mk_wordii (random_const n, n)]
          end
        else
          raise ERR "random_term" "cart")
   | ("addressing_mode1", []) =>
       [case random_range (if enc = Thumb orelse enc = ThumbEE then 2 else 3)
        of 0 => arm_astSyntax.mk_Mode1_immediate
                  (wordsSyntax.mk_wordii (random_const
                     (if enc = Thumb orelse enc = ThumbEE then 8 else 12), 12))
         | 1 => r3 arm_astSyntax.mk_Mode1_register
                   ``:word5 -> word2 -> 'reg word``
         | 2 => r3 arm_astSyntax.mk_Mode1_register_shifted_register
                   ``:'reg word -> word2 -> 'reg word``
         | _ => raise ERR "random_term" "addressing_mode1"]
   | ("addressing_mode3", []) =>
       [case random_range 2
        of 0 => arm_astSyntax.mk_Mode3_immediate
                  (mk_word12 (random_const
                     (if enc = Thumb orelse enc = ThumbEE then 5 else 8)))
         | 1 => arm_astSyntax.mk_Mode3_register
                  (mk_word2 (case enc
                             of Thumb2  => random_const 2
                              | ThumbEE => 1
                              | _       => 0),
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
       [case enc
        of ARM =>
           (case random_range 4
            of 0 => arm_astSyntax.mk_Branch_Target
                         (hd (rand_term ``:'offset word``))
             | 1 => arm_astSyntax.mk_Branch_Exchange
                         (hd (rand_term ``:'reg word``))
             | 2 => r3 arm_astSyntax.mk_Branch_Link_Exchange_Immediate
                         ``:bool -> bool -> 'offset word``
             | 3 => arm_astSyntax.mk_Branch_Link_Exchange_Register
                         (hd (rand_term ``:'reg word``))
             | _ => raise ERR "random_term" "branch_instruction")
         | Thumb2 =>
           (case random_range 3
            of 0 => arm_astSyntax.mk_Branch_Target
                         (hd (rand_term ``:'offset word``))
             | 1 => r3 arm_astSyntax.mk_Branch_Link_Exchange_Immediate
                         ``:bool -> bool -> 'offset word``
             | 2 => r3 arm_astSyntax.mk_Table_Branch_Byte
                         ``:'reg word -> bool -> 'reg word``
             | _ => raise ERR "random_term" "branch_instruction")
         | Thumb =>
           (case random_range 4
            of 0 => arm_astSyntax.mk_Branch_Target
                         (hd (rand_term ``:'offset word``))
             | 1 => arm_astSyntax.mk_Branch_Exchange
                         (hd (rand_term ``:'reg word``))
             | 2 => arm_astSyntax.mk_Branch_Link_Exchange_Register
                         (hd (rand_term ``:'reg word``))
             | 3 => r3 arm_astSyntax.mk_Compare_Branch
                         ``:bool -> word6 -> word3``
             | _ => raise ERR "random_term" "branch_instruction")
         | ThumbEE =>
           (case random_range 4
            of 0 => r2 arm_astSyntax.mk_Check_Array ``:'reg word -> 'reg word``
             | 1 => r2 arm_astSyntax.mk_Handler_Branch_Link ``:bool -> word8``
             | 2 => r2 arm_astSyntax.mk_Handler_Branch_Link_Parameter
                         ``:word5 -> word5``
             | 3 => r2 arm_astSyntax.mk_Handler_Branch_Parameter
                         ``:word3 -> word5``
             | _ => raise ERR "random_term" "branch_instruction")]
   | ("data_processing_instruction", []) =>
         Lib.assert_exn (K (enc <> ThumbEE))
         [case random_from_list (data_processing_list (version_number arch) enc)
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
           (ERR "random_term" "data_processing_instruction")
   | ("status_access_instruction", []) =>
       Lib.assert_exn (K (enc <> ThumbEE))
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
       (ERR "random_term" "status_access_instruction")
   | ("load_store_instruction", []) =>
      [if random_range 3 = 0 then
         ls ()
       else if enc = ThumbEE orelse random_range 2 = 0 then
         lsh ()
       else if enc = Thumb orelse random_range 2 = 0 then
         lsm ()
       else
         case random_range 8
         of 0 => lsd true
          | 1 => lsd false
          | 2 => r3 arm_astSyntax.mk_Load_Exclusive
                      ``:'reg word -> 'reg word -> word8``
          | 3 => let val (t,t2) = double () in
                   arm_astSyntax.mk_Load_Exclusive_Doubleword
                     (hd (rand_term  ``:'reg word``), t, t2)
                 end
          | 4 => r2 arm_astSyntax.mk_Load_Exclusive_Halfword
                      ``:'reg word -> 'reg word``
          | 5 => r2 arm_astSyntax.mk_Load_Exclusive_Byte
                      ``:'reg word -> 'reg word``
          | 6 => r4 arm_astSyntax.mk_Store_Return_State
                      ``:bool -> bool -> bool -> 'mode word``
          | 7 => r4 arm_astSyntax.mk_Return_From_Exception
                      ``:bool -> bool -> bool -> 'reg word``
          | 8 => r3 arm_astSyntax.mk_Store_Exclusive_Byte
                      ``:'reg word -> 'reg word -> 'reg word``
          | 9 => r4 arm_astSyntax.mk_Store_Exclusive
                      ``:'reg word -> 'reg word -> 'reg word -> word8``
          | 10 => r3 arm_astSyntax.mk_Store_Exclusive_Halfword
                      ``:'reg word -> 'reg word -> 'reg word``
          | 11 => let val (t,t2) = double ()
                      val (n,d) = r2 I ``:'reg word -> 'reg word``
                  in
                    arm_astSyntax.mk_Store_Exclusive_Doubleword (n,d,t,t2)
                  end
          | _ => raise ERR "random_term" "load_store_instruction"]
   | ("miscellaneous_instruction", []) =>
       Lib.assert_exn (K (enc <> ThumbEE))
       [case enc
        of Thumb2 =>
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
               | _ => raise ERR "random_term" "miscellaneous_instruction")
         | _ =>
             (case random_range 4
              of 0 => arm_astSyntax.mk_Hint (hd (rand_term ``:hint``))
               | 1 => arm_astSyntax.mk_Breakpoint
                        (wordsSyntax.mk_wordii
                           (random_const (if enc = ARM then 16 else 8), 16))
               | 2 => arm_astSyntax.mk_Supervisor_Call
                        (wordsSyntax.mk_wordii
                           (random_const (if enc = ARM then 24 else 8), 24))
               | 3 => r2 arm_astSyntax.mk_If_Then ``:word4 -> word4``
               | _ => raise ERR "random_term" "miscellaneous_instruction")]
       (ERR "random_term" "miscellaneous_instruction")
   | _ => raise ERR "random_term" (type_to_string typ)
end

(* ------------------------------------------------------------------------- *)

local
  fun filter_mk_set [] = []
    | filter_mk_set ((x as (a,_))::rst) =
        x::filter_mk_set (List.filter (fn (b,_) => b !~ a) rst)

  val uint_of_word = wordsSyntax.uint_of_word
  fun try_dest_label thm = markerLib.DEST_LABEL thm handle HOL_ERR _ => thm;
  fun reg tm = mk_var ("r" ^ Int.toString (uint_of_word tm), ``:word32``);
  fun flag tm = mk_var (fst (dest_const tm), bool);
  val arch     = mk_var ("architecture",``:ARMarch``)
  val cpsr     = mk_var ("cpsr", ``:ARMpsr``)
  val spsr     = mk_var ("spsr", ``:ARMpsr``)
  val GE       = mk_var ("GE", ``:word4``)
  val IT       = mk_var ("IT", ``:word8``)
  val teehbr   = mk_var ("TEEHBR", ``:word32``)
  val mode     = mk_var ("mode", ``:word5``)
  val mem      = mk_var ("mem", ``:word32 -> word8``)
  val spsrGE   = mk_var ("spsrGE", ``:word4``)
  val spsrIT   = mk_var ("spsrIT", ``:word8``)
  val spsrmode = mk_var ("spsrmode", ``:word5``)
  fun mode_str tm = case uint_of_word tm
                    of 16 => "usr"
                     | 17 => "fiq"
                     | 18 => "irq"
                     | 19 => "svc"
                     | 22 => "mon"
                     | 23 => "abt"
                     | 27 => "und"
                     | 31 => "usr"
                     | _  => "??"
  fun reg_mode tm = let val (r,m) =  pairSyntax.dest_pair tm in
          mk_var (String.concat
            ["r", Int.toString (uint_of_word r), "_", mode_str m], ``:word32``)
        end
  fun spsr_mode tm =
          mk_var (String.concat ["spsr", "_", mode_str tm], ``:word32``)
  fun spsr_flag tm = mk_var ("s" ^ fst (dest_const tm), bool);

  fun component_subst tm =
        tm |-> (case dest_strip tm
                of ("ARM_READ_MEM", [a,_])         => mk_comb (mem, a)
                 | ("ARM_READ_REG", [a,_])         => reg a
                 | ("ARM_READ_REG_MODE", [x,_])    => reg_mode x
                 | ("ARM_READ_STATUS", [a,_])      => flag a
                 | ("ARM_READ_STATUS_SPSR", [a,_]) => spsr_flag a
                 | ("ARM_READ_CPSR", [_])          => cpsr
                 | ("ARM_READ_SPSR", [_])          => spsr
                 | ("ARM_READ_TEEHBR", [_])        => teehbr
                 | ("ARM_READ_SPSR_MODE", [m,_])   => spsr_mode m
                 | ("ARM_READ_GE", [_])            => GE
                 | ("ARM_READ_IT", [_])            => IT
                 | ("ARM_MODE", [_])               => mode
                 | ("ARM_READ_GE_SPSR", [_])       => spsrGE
                 | ("ARM_READ_IT_SPSR", [_])       => spsrIT
                 | ("ARM_READ_MODE_SPSR", [_])     => spsrmode
                 | ("ARM_READ_SCTLR", [a,_])       => flag a
                 | ("ARM_READ_SCR", [a,_])         => flag a
                 | ("ARM_ARCH", [_])               => arch
                 | _ => raise ERR "component_subst" "")

  fun component_substs tm =
        Term.subst (List.map component_subst
          (HolKernel.find_terms (Lib.can component_subst) tm)) tm

  val component_substs = component_substs o component_substs

  fun updates tm l =
     (case dest_strip tm
      of ("ARM_WRITE_MEM", [a,d,s]) => updates s ((mk_comb (mem,a), d)::l)
       | ("ARM_WRITE_REG", [a,d,s]) => updates s ((reg a, d)::l)
       | ("ARM_WRITE_REG_MODE", [x,d,s]) => updates s ((reg_mode x, d)::l)
       | ("ARM_WRITE_STATUS", [f,d,s]) => updates s ((flag f,d)::l)
       | ("ARM_WRITE_STATUS_SPSR", [f,d,s]) => updates s ((spsr_flag f,d)::l)
       | ("ARM_WRITE_CPSR", [d,s]) => updates s ((cpsr,d)::l)
       | ("ARM_WRITE_SPSR", [d,s]) => updates s ((spsr,d)::l)
       | ("ARM_WRITE_SPSR_MODE", [m,d,s]) => updates s ((spsr_mode m,d)::l)
       | ("ARM_WRITE_GE", [d,s]) => updates s ((GE,d)::l)
       | ("ARM_WRITE_IT", [d,s]) => updates s ((IT,d)::l)
       | ("ARM_WRITE_MODE", [d,s]) => updates s ((mode,d)::l)
       | ("ARM_WRITE_GE_SPSR", [d,s]) => updates s ((spsrGE,d)::l)
       | ("ARM_WRITE_IT_SPSR", [d,s]) => updates s ((spsrIT,d)::l)
       | ("ARM_WRITE_MODE_SPSR", [d,s]) => updates s ((spsrmode,d)::l)
       | (_,tml) => updates (List.last tml) l) handle HOL_ERR _ => List.rev l

  fun updates_set tm = filter_mk_set (updates tm [])

  fun get_updates tm =
  let
    val tm' = component_substs tm
  in
    case Lib.total boolSyntax.dest_cond tm'
    of SOME (c,a,b) => Conditional_step (c, updates_set a, updates_set b)
     | NONE => Simple_step (updates_set tm')
  end
in
  fun arm_step_updates opt opc = let
        val tm = opc |> try (armLib.arm_step opt)
                     |> try_dest_label
                     |> SPEC_ALL |> concl
        val (l,r) = boolSyntax.dest_imp tm
      in
        (l |> component_substs
           |> boolSyntax.strip_conj,
         r |> boolSyntax.dest_eq |> snd
           |> optionSyntax.dest_some
           |> get_updates)
      end
  fun step_updates (pass,arch) (opc,ass:string,block) = let
      val opt = String.concat [arch, ", ", block, ", ",
                               if pass then "pass" else "fail"]
      val _ = if !arm_random_trace then
                print (String.concat ["Processing... ", ass, "\n"])
              else
                ()
      val (l,r) = case arm_step_updates opt opc
                  of (l, Simple_step r) => (l,r)
                   | _ => raise ERR "step_updates" "Condition at top-level"
    in
      (opc, ass, List.drop(l,8), r)
    end
end;

local
  fun encoding Thumb   = armSyntax.Encoding_Thumb_tm
    | encoding ThumbEE = armSyntax.Encoding_ThumbEE_tm
    | encoding Thumb2  = armSyntax.Encoding_Thumb2_tm
    | encoding ARM     = armSyntax.Encoding_ARM_tm

  fun block enc =
        if enc ~~ armSyntax.Encoding_Thumb_tm orelse
           enc ~~ armSyntax.Encoding_Thumb2_tm
        then
          "THUMB"
        else if enc ~~ armSyntax.Encoding_ThumbEE_tm then
          "THUMBX"
        else
          "ARM"

  fun disassemble c =
        let val (l,r) = armLib.arm_disassemble c in l ^ " " ^ r end

  fun decode block n =
        let val c = case block
                    of "ARM"    => armLib.arm_decode n
                     | "THUMB"  => armLib.thumb_decode 0 n
                     | "THUMBX" => armLib.thumbee_decode 0 n
                     | _ => raise ERR "decode" block
        in
          case c
          of armLib.Instruction (_,_,tm) => tm | _ => raise ERR "decode" ""
        end

  fun arm_uncoditional tm =
        arm_astSyntax.is_Branch_Link_Exchange_Immediate tm andalso
          (let val (_,toarm,_) =
                      arm_astSyntax.dest_Branch_Link_Exchange_Immediate tm
           in
             Feq toarm
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
    let val b = block enc
        val c = armLib.Instruction code
        val e = armLib.arm_encode c
        val s = disassemble c
        val a = arch ^ (if b = "ARM" then s else b ^ "\n " ^ s)
        val d = a |> with_flag (Feedback.emit_WARNING,false)
                       armLib.arm_encode_from_string
        val w = if d <> e then
                   (HOL_WARNING "arm_randomLib" "mk_code" (String.concat
                     ["<<parse warning>>:", "\n",
                      a, "\n",
                      Hol_pp.term_to_string tm, "\n",
                      "\t", e, " =/= ", d, "\n",
                      Hol_pp.term_to_string (decode b d), "\n"]);
                     String.concat
                       [" // warning, ", e, " equivalent to ", d, "?"])
                 else
                   ""
    in
      (e,a ^ w,b)
    end handle HOL_ERR e =>
          (HOL_WARNING (#origin_structure e) (#origin_function e)
             (String.concat
                [Hol_pp.term_to_string enc, ": ",
                 Hol_pp.term_to_string tm, "\n"]);
           raise HOL_ERR e)
      | Option =>
          (HOL_WARNING "" ""
             (String.concat
                [Hol_pp.term_to_string enc, ": ",
                 Hol_pp.term_to_string tm, "\n"]);
           raise Option)

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

  fun valid_arch_ecoding e a = Lib.mem e
   (case a
    of ARMv4   => [ARM]
     | ARMv4T  => [ARM, Thumb]
     | ARMv5T  => [ARM, Thumb]
     | ARMv5TE => [ARM, Thumb]
     | ARMv6   => [ARM, Thumb]
     | ARMv6K  => [ARM, Thumb]
     | ARMv6T2 => [ARM, Thumb, Thumb2]
     | ARMv7_A => [ARM, Thumb, Thumb2, ThumbEE]
     | ARMv7_R => [ARM, Thumb, Thumb2, ThumbEE])

  fun random_code arch enc typ =
        let val tm = hd (random_term arch enc typ)
            val cond = mk_word4
                         (if enc = ARM andalso arm_uncoditional tm then
                            15
                          else if arm_astSyntax.is_Branch_Target tm then
                            random_range 14
                          else
                            14)
        in
          (encoding enc, cond, tm)
        end

  fun generate_opcode_cond pass arch enc opc = let
    val _ = valid_arch_ecoding enc arch orelse
              raise ERR "generate_opcode"
                        "Architecture does not support encoding"
    val b = block (encoding enc)
    val ass = case b
              of "ARM"    => armLib.arm_disassemble_decode opc
               | "THUMB"  => armLib.thumb_disassemble_decode 0 opc
               | "THUMBX" => armLib.thumbee_disassemble_decode 0 opc
               | _ => raise ERR "generate_opcode_cond" b
  in
    step_updates (pass,arch_to_string arch) (opc,ass,b)
  end
in
  fun generate_random arch enc class =
    let val _ = valid_arch_ecoding enc arch orelse
                  raise ERR "generate_random"
                            "Architecture does not support encoding"
        val a = arch_to_string arch
        val aa = String.concat ["ARCH ", a, "\n "]
        val typ = case class
                  of DataProcessing => ``:data_processing_instruction``
                   | LoadStore      => ``:load_store_instruction``
                   | Branch         => ``:branch_instruction``
                   | StatusAccess   => ``:status_access_instruction``
                   | Miscellaneous  => ``:miscellaneous_instruction``
    in
      random_code arch enc typ
        |> mk_code aa
        |> step_updates (true,a)
    end

  val generate_opcode     = generate_opcode_cond true
  val generate_opcode_nop = generate_opcode_cond false
end;

fun instruction_type enc opc =
let
  val code =
    case enc
      of ARM     => armLib.arm_decode opc
       | Thumb   => armLib.thumb_decode 0 (String.extract(opc,4,NONE))
       | ThumbEE => armLib.thumb_decode 0 (String.extract(opc,4,NONE))
       | Thumb2  => armLib.thumb_decode 0 (String.extract(opc,4,NONE) ^
                                           String.extract(opc,0,SOME 4))
  val (e,tm) =
    case code
      of arm_parserLib.Instruction (e,_,tm) => (e,tm)
       | _ => raise ERR "instruction_type" ""
  val mode =
    if arm_astSyntax.is_Data_Processing tm then
      let val (_,_,_,_,mode1) = arm_astSyntax.dest_Data_Processing tm in
        if arm_astSyntax.is_Mode1_register_shifted_register mode1 then
          " (reg-sh-reg)"
        else if arm_astSyntax.is_Mode1_register mode1 then
          " (reg)"
        else if arm_astSyntax.is_Mode1_immediate mode1 then
          " (imm)"
        else
          raise ERR "instruction_type" ""
      end
    else if arm_astSyntax.is_Load tm then
      let val (_,_,_,_,_,n,_,mode2) = arm_astSyntax.dest_Load tm in
        if arm_astSyntax.is_Mode2_immediate mode2 then
          (if is_PC n then " (lit)" else " (imm)")
        else if arm_astSyntax.is_Mode2_register mode2 then
          " (reg)"
        else
          raise ERR "instruction_type" ""
      end
    else if arm_astSyntax.is_Load_Halfword tm then
      let val (_,_,_,_,_,_,n,_,mode3) = arm_astSyntax.dest_Load_Halfword tm in
        if arm_astSyntax.is_Mode3_immediate mode3 then
          if is_PC n then " (lit)" else " (imm)"
        else if arm_astSyntax.is_Mode3_register mode3 then
          " (reg)"
        else
          raise ERR "instruction_type" ""
      end
    else if arm_astSyntax.is_Load_Dual tm then
      let val (_,_,_,n,_,_,mode3) = arm_astSyntax.dest_Load_Dual tm
      in
        if arm_astSyntax.is_Mode3_immediate mode3 then
          if is_PC n then " (lit)" else " (imm)"
        else if arm_astSyntax.is_Mode3_register mode3 then
          " (reg)"
        else
          raise ERR "instruction_type" ""
      end
    else if arm_astSyntax.is_Store tm then
      let val (_,_,_,_,_,n,_,mode2) = arm_astSyntax.dest_Store tm in
        if arm_astSyntax.is_Mode2_immediate mode2 then
          " (imm)"
        else if arm_astSyntax.is_Mode2_register mode2 then
          " (reg)"
        else
          raise ERR "instruction_type" ""
      end
    else if arm_astSyntax.is_Store_Halfword tm then
      let val (_,_,_,_,n,_,mode3) = arm_astSyntax.dest_Store_Halfword tm in
        if arm_astSyntax.is_Mode3_immediate mode3 then
          " (imm)"
        else if arm_astSyntax.is_Mode3_register mode3 then
          " (reg)"
        else
          raise ERR "instruction_type" ""
      end
    else if arm_astSyntax.is_Store_Dual tm then
      let val (_,_,_,n,_,_,mode3) = arm_astSyntax.dest_Store_Dual tm in
        if arm_astSyntax.is_Mode3_immediate mode3 then
          " (imm)"
        else if arm_astSyntax.is_Mode3_register mode3 then
          " (reg)"
        else
          raise ERR "instruction_type" ""
      end
    else if arm_astSyntax.is_Preload_Data tm then
      let val (_,_,_,mode2) = arm_astSyntax.dest_Preload_Data tm in
        if arm_astSyntax.is_Mode2_immediate mode2 then
          " (imm)"
        else if arm_astSyntax.is_Mode2_register mode2 then
          " (reg)"
        else
          raise ERR "instruction_type" ""
      end
    else if arm_astSyntax.is_Preload_Instruction tm then
      let val (_,_,mode2) = arm_astSyntax.dest_Preload_Instruction tm in
        if arm_astSyntax.is_Mode2_immediate mode2 then
          " (imm)"
        else if arm_astSyntax.is_Mode2_register mode2 then
          " (reg)"
        else
          raise ERR "instruction_type" ""
      end
    else if arm_astSyntax.is_Branch_Link_Exchange_Immediate tm orelse
            arm_astSyntax.is_Immediate_to_Status tm then
      " (imm)"
    else if arm_astSyntax.is_Branch_Link_Exchange_Register tm orelse
            arm_astSyntax.is_Register_to_Status tm then
      " (reg)"
    else
      ""
  fun remove_suffix (s,_) =
        let val m = hd (String.tokens (fn c => c = #".") s) in
          if String.isPrefix "it" m then "it" else m
        end
  val code' = arm_parserLib.Instruction (e,``14w:word4``,tm)
in
  remove_suffix (armLib.arm_disassemble code') ^ mode
end;

end;
