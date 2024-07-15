structure arm_encoderLib :> arm_encoderLib =
struct

(* interactive use:
  app load ["arm_parserLib"];
*)

open HolKernel boolLib bossLib;
open armSyntax arm_astSyntax;

(* ------------------------------------------------------------------------- *)

val _ = numLib.temp_prefer_num();
val _ = wordsLib.prefer_word();

val ERR = Feedback.mk_HOL_ERR "arm_encoderLib";

local
  val tm_g = Parse.term_grammar ()
  val ty_g = Parse.type_grammar ()
in
  val term_to_string =
        PP.pp_to_string 70
          (Parse.mlower o term_pp.pp_term tm_g ty_g PPBackEnd.raw_terminal)
end

(* ------------------------------------------------------------------------- *)

val eval = boolSyntax.rhs o Thm.concl o bossLib.EVAL;

val pad = StringCvt.padLeft #"0"

val uint_of_word = wordsSyntax.uint_of_word;
val sint_of_term = Arbint.toInt o intSyntax.int_of_term;

fun mk_bool b  = if b then T else F;
fun mk_word4 i = wordsSyntax.mk_wordii (i,4);

val PC = mk_word4 15;

val is_T   = Term.term_eq T;
val is_F   = Term.term_eq F;
val is_R9  = Term.term_eq (mk_word4 9);
val is_R10 = Term.term_eq (mk_word4 10);
val is_SP  = Term.term_eq (mk_word4 13);
val is_AL  = Term.term_eq (mk_word4 14);
val is_PC  = Term.term_eq PC;
val is_LR  = is_AL;

fun NOT tm = if is_T tm then F else if is_F tm then T else raise ERR "NOT" "";

val dest_strip = armSyntax.dest_strip;

infix $;

fun op $ (n,(h,l)) =
  wordsSyntax.mk_word_bits (numSyntax.term_of_int h, numSyntax.term_of_int l, n)
    |> eval;

local
  open Arbnum
  infix pow

  fun term_to_num tm =
    let open wordsSyntax in
      if is_word_type (Term.type_of tm) then
        tm |> dest_n2w |> fst |> numSyntax.dest_numeral
      else if is_T tm then
        Arbnum.one
      else if is_F tm then
        Arbnum.zero
      else
        raise ERR "term_to_num" ""
    end

  fun lsl (n,i) = n * (two pow (fromInt i))
in
  fun is_0 tm = term_to_num tm = zero

  fun width_okay w tm =
        let val n = term_to_num tm in
          if n = zero then Int.<(0,w) else Int.<(toInt (log2 n),w)
        end

  val term_list_to_num =
        List.foldl (fn ((tm,i),n) => n + lsl (term_to_num tm,i)) zero
end;

fun check (f,m) b = (b () orelse raise ERR f (term_to_string m); I);

fun check_is_15 s tm = check (s,tm) (fn _ => is_PC tm);

(* ------------------------------------------------------------------------- *)

fun encode_ascii s =
  s |> String.explode
    |> List.map (pad 2 o Int.fmt StringCvt.HEX o Char.ord)
    |> Lib.separate " "
    |> String.concat;

fun encode_byte l =
let fun byte_to_int tm =
      let val i = sint_of_term tm in
        if i < 0 then i + 256 else i
      end
in
  l |> map (pad 2 o Int.fmt StringCvt.HEX o byte_to_int)
    |> Lib.separate " "
    |> String.concat
end;

fun encode_short l =
let fun short_to_int tm =
      let val i = sint_of_term tm in
        if i < 0 then i + 65536 else i
      end
in
  l |> List.map (pad 4 o Int.fmt StringCvt.HEX o short_to_int)
    |> Lib.separate " "
    |> String.concat
end;

fun encode_word l =
let open Arbint
    fun int_to_num_string tm =
      let val i = intSyntax.int_of_term tm in
        (if i < zero then i + fromString "4294967296" else i)
          |> toNat |> Arbnum.toHexString |> pad 8
      end
in
  l |> List.map int_to_num_string
    |> Lib.separate " "
    |> String.concat
end;

(* ------------------------------------------------------------------------- *)

fun encode_mode1 tm =
  case dest_strip tm
  of ("Mode1_immediate", [imm12]) =>
        [(T,25), (imm12,0)]
   | ("Mode1_register", [imm5,typ,rm]) =>
        [(imm5,7), (typ,5), (rm,0)]
   | ("Mode1_register_shifted_register", [rs,typ,rm]) =>
        [(rs,8), (typ,5), (T,4), (rm,0)]
   | _ => raise ERR "encode_mode1" "";

fun encode_mode2 tm =
  case dest_strip tm
  of ("Mode2_immediate", [imm12])      => [(imm12,0)]
   | ("Mode2_register", [imm5,typ,rm]) => [(T,25), (imm5,7), (typ,5), (rm,0)]
   | _ => raise ERR "encode_mode2" "";

fun encode_mode3 tm =
  case dest_strip tm
  of ("Mode3_immediate", [imm12]) =>
        check ("encode_mode3", tm) (fn _ => width_okay 8 imm12)
          [(T,22), (imm12$(7,4),8), (imm12$(3,0),0)]
   | ("Mode3_register", [imm2,rm]) =>
        check ("encode_mode3", tm) (fn _ => is_0 imm2)
          [(rm,0)]
   | _ => raise ERR "encode_mode3" "";

fun parallel_add_sub_op1 tm =
  case fst (Term.dest_const tm)
  of "Parallel_normal"     => ``0b01w:word2``
   | "Parallel_saturating" => ``0b10w:word2``
   | "Parallel_halving"    => ``0b11w:word2``
   | _ => raise ERR "parallel_add_sub_op1" "";

fun thumb_parallel_add_sub_op1 tm =
  case fst (Term.dest_const tm)
  of "Parallel_normal"     => ``0b00w:word2``
   | "Parallel_saturating" => ``0b01w:word2``
   | "Parallel_halving"    => ``0b10w:word2``
   | _ => raise ERR "thumb_parallel_add_sub_op1" "";

fun parallel_add_sub_op2 tm =
  case fst (Term.dest_const tm)
  of "Parallel_add_16"           => ``0b000w:word3``
   | "Parallel_add_sub_exchange" => ``0b001w:word3``
   | "Parallel_sub_add_exchange" => ``0b010w:word3``
   | "Parallel_sub_16"           => ``0b011w:word3``
   | "Parallel_add_8"            => ``0b100w:word3``
   | "Parallel_sub_8"            => ``0b111w:word3``
   | _ => raise ERR "parallel_add_sub_op2" "";

fun thumb_parallel_add_sub_op2 tm =
  case fst (Term.dest_const tm)
  of "Parallel_add_16"           => ``0b001w:word3``
   | "Parallel_add_sub_exchange" => ``0b010w:word3``
   | "Parallel_sub_add_exchange" => ``0b110w:word3``
   | "Parallel_sub_16"           => ``0b101w:word3``
   | "Parallel_add_8"            => ``0b000w:word3``
   | "Parallel_sub_8"            => ``0b100w:word3``
   | _ => raise ERR "thumb_parallel_add_sub_op2" "";

val parallel_add_sub =
  (parallel_add_sub_op1 ## parallel_add_sub_op2) o pairSyntax.dest_pair;

val thumb_parallel_add_sub =
  (thumb_parallel_add_sub_op1 ## thumb_parallel_add_sub_op2) o
  pairSyntax.dest_pair;

fun hint tm =
  case dest_strip tm
  of ("Hint_nop", [])                => []
   | ("Hint_yield", [])              => [(T,0)]
   | ("Hint_wait_for_event", [])     => [(T,1)]
   | ("Hint_wait_for_interrupt", []) => [(``0b11w:word2``,0)]
   | ("Hint_send_event", [])         => [(T,2)]
   | ("Hint_debug", [opt])           => [(PC,4),(opt,0)]
   | _ => raise ERR "hint" "";

fun thumb_hint tm =
  case dest_strip tm
  of ("Hint_nop", [])                => []
   | ("Hint_yield", [])              => [(T,4)]
   | ("Hint_wait_for_event", [])     => [(T,5)]
   | ("Hint_wait_for_interrupt", []) => [(``0b11w:word2``,4)]
   | ("Hint_send_event", [])         => [(T,6)]
   | _ => raise ERR "thumb_hint" "cannot encode";

(* ------------------------------------------------------------------------- *)

fun encode_branch (cond,tm) = term_list_to_num ((cond,28)::
 (case dest_strip tm
  of ("Branch_Target", [imm24]) =>
        [(T,27), (T,25), (imm24,0)]
   | ("Branch_Exchange", [rm]) =>
        [(T,24), (T,21), (PC,16),(PC,12),(PC,8), (T,4), (rm,0)]
   | ("Branch_Link_Exchange_Immediate", [h,toarm,imm24]) =>
        check ("encode_branch", tm) (fn _ => is_T toarm orelse is_PC cond)
        [(T,27), (T,25), (if is_T toarm then T else h,24), (imm24,0)]
   | ("Branch_Link_Exchange_Register", [rm]) =>
        [(T,24), (T,21), (PC,16),(PC,12),(PC,8), (T,5), (T,4), (rm,0)]
   | _ => raise ERR "encode_branch" ("cannot encode: " ^ term_to_string tm)));

fun check_dp (tm,rd,rn) =
  case uint_of_word tm
  of 8  => is_0 rd
   | 9  => is_0 rd
   | 10 => is_0 rd
   | 11 => is_0 rd
   | 13 => is_0 rn
   | 15 => is_0 rn
   | _  => true;

fun encode_data_processing (cond,tm) = term_list_to_num ((cond,28)::
 (case dest_strip tm
  of ("Data_Processing", [opc,s,n,d,mode1]) =>
        check ("encode_data_processing", tm) (fn _ => check_dp (opc,d,n))
        [(opc,21), (s,20), (n,16), (d,12)] @ encode_mode1 mode1
   | ("Move_Halfword", [h,d,imm16]) =>
        [(T,25), (T,24), (h,22), (imm16$(15,12),16), (d,12), (imm16$(11,0),0)]
   | ("Add_Sub", [a,n,d,imm12]) =>
        [(a,23), (NOT a,22), (n,16), (d,12)] @
         encode_mode1 (mk_Mode1_immediate imm12)
   | ("Multiply", [acc,s,d,a,m,n]) =>
        [(acc,21), (s,20), (d,16), (if is_T acc then a else mk_word4 0,12),
         (m,8), (T,7), (T, 4), (n,0)]
   | ("Multiply_Subtract", [d,a,m,n]) =>
        [(T,22), (T,21), (d,16), (a,12), (m,8), (T,7), (T, 4), (n,0)]
   | ("Signed_Halfword_Multiply", [opc,M,N,d,a,m,n]) =>
        let val a = case uint_of_word opc
                    of 1 => if is_T N then mk_word4 0 else a
                     | 3 => mk_word4 0
                     | _ => a
        in
          [(T,24), (opc,21), (d,16), (a,12), (m,8), (T,7), (M,6), (N,5), (n,0)]
        end
   | ("Signed_Multiply_Dual", [d,a,m,M,N,n]) =>
        [(``7w:word3``,24), (d,16), (a,12), (m,8), (M,6), (N,5), (T,4), (n,0)]
   | ("Signed_Multiply_Long_Dual", [dhi,dlo,m,M,N,n]) =>
        [(``7w:word3``,24), (T,22), (dhi,16), (dlo,12), (m,8),
         (M,6), (N,5), (T,4), (n,0)]
   | ("Signed_Most_Significant_Multiply", [d,a,m,r,n]) =>
        [(``7w:word3``,24), (T,22), (T,20), (d,16), (a,12), (m,8),
         (r,5), (T,4), (n,0)]
   | ("Signed_Most_Significant_Multiply_Subtract", [d,a,m,r,n]) =>
        [(``7w:word3``,24), (T,22), (T,20), (d,16), (a,12), (m,8),
         (T,7), (T,6), (r,5), (T,4), (n,0)]
   | ("Multiply_Long", [sgnd,a,s,dhi,dlo,m,n]) =>
        [(T,23), (sgnd,22), (a,21), (s,20), (dhi,16), (dlo,12), (m,8),
         (T,7), (T,4), (n,0)]
   | ("Multiply_Accumulate_Accumulate", [dhi,dlo,m,n]) =>
        [(T,22), (dhi,16), (dlo,12), (m,8), (T,7), (T,4), (n,0)]
   | ("Saturate", [u,sat,d,imm5,sh,n]) =>
        [(T,26), (T,25), (T,23), (u,22), (T,21), (sat,16), (d,12), (imm5,7),
         (sh,6), (T,4), (n,0)]
   | ("Saturate_16", [u,imm4,d,n]) =>
        [(T,26), (T,25), (T,23), (u,22), (T,21), (imm4,16), (d,12), (PC,8),
         (T,5), (T,4), (n,0)]
   | ("Saturating_Add_Subtract", [opc,n,d,m]) =>
        [(T,24), (opc,21), (n,16), (d,12), (T,6), (T,4), (m,0)]
   | ("Pack_Halfword", [n,d,imm5,t,m]) =>
        [(T,26), (T,25), (T,23), (n,16), (d,12), (imm5,7), (t,6), (T,4), (m,0)]
   | ("Extend_Byte", [u,n,d,rot,m]) =>
        [(T,26), (T,25), (T,23), (u,22), (T,21), (n,16), (d,12),
         (rot,10), (T,6), (T,5), (T,4), (m,0)]
   | ("Extend_Byte_16", [u,n,d,rot,m]) =>
        [(T,26), (T,25), (T,23), (u,22), (n,16), (d,12),
         (rot,10), (T,6), (T,5), (T,4), (m,0)]
   | ("Extend_Halfword", [u,n,d,rot,m]) =>
        [(T,26), (T,25), (T,23), (u,22), (T,21), (T,20), (n,16), (d,12),
         (rot,10), (T,6), (T,5), (T,4), (m,0)]
   | ("Bit_Field_Clear_Insert", [msb,d,lsb,n]) =>
        [(``0b11111w:word5``,22), (msb,16), (d,12), (lsb,7), (T,4), (n,0)]
   | ("Count_Leading_Zeroes", [d,m]) =>
        [(T,24), (T,22), (T,21), (PC,16), (d,12), (PC,8), (T,4), (m, 0)]
   | ("Reverse_Bits", [d,m]) =>
        [(T,26), (T,25), (PC,20), (PC,16), (d,12), (PC,8), (T,5), (T,4), (m, 0)]
   | ("Byte_Reverse_Word", [d,m]) =>
        [(T,26), (T,25), (``0b1011w:word4``,20), (PC,16), (d,12), (PC,8),
         (T,5), (T,4), (m, 0)]
   | ("Byte_Reverse_Packed_Halfword", [d,m]) =>
        [(T,26), (T,25), (``0b1011w:word4``,20), (PC,16), (d,12), (PC,8),
         (T,7), (T,5), (T,4), (m, 0)]
   | ("Byte_Reverse_Signed_Halfword", [d,m]) =>
        [(T,26), (T,25), (PC,20), (PC,16), (d,12), (PC,8),
         (T,7), (T,5), (T,4), (m, 0)]
   | ("Bit_Field_Extract", [u,w,d,lsb,n]) =>
        [(PC,23), (u,22), (T,21), (w,16), (d,12), (lsb,7), (T,6), (T,4), (n, 0)]
   | ("Select_Bytes", [n,d,m]) =>
        [(T,26), (T,25), (T,23), (n,16), (d,12), (PC,8),
         (T,7), (T,5), (T,4), (m, 0)]
   | ("Unsigned_Sum_Absolute_Differences", [d,a,m,n]) =>
        [(PC,23), (d,16), (a,12), (m,8), (T,4), (n, 0)]
   | ("Parallel_Add_Subtract", [u,opc,n,d,m]) =>
        let val (opc1,opc2) = parallel_add_sub opc in
          [(T,26), (T,25), (u,22), (opc1,20), (n,16), (d,12), (PC,8),
           (opc2,5), (T,4), (m, 0)]
        end
   | _ => raise ERR "encode_data_processing"
            ("cannot encode: " ^ term_to_string tm)));

fun encode_status_access (cond,tm) = term_list_to_num ((cond,28)::
 (case dest_strip tm
  of ("Status_to_Register", [r,d]) =>
        [(T,24), (r,22), (PC, 16), (d,12)]
   | ("Immediate_to_Status", [r,mask,imm12]) =>
        [(T,25), (T,24), (r,22), (T,21), (mask,16), (PC, 12), (imm12,0)]
   | ("Register_to_Status", [r,mask,n]) =>
        [(T,24), (r,22), (T,21), (mask,16), (PC, 12), (n,0)]
   | ("Change_Processor_State", [imod,a,i,f,mode]) =>
        let val (M,m) = if optionSyntax.is_some mode then
                          (T,optionSyntax.dest_some mode)
                        else
                          (F,mk_word4 0)
        in
          check_is_15 "encode_status_access: cond" cond
            [(T,24), (imod,18), (M,17), (a,8), (i,7), (f,6), (m,0)]
        end
   | ("Set_Endianness", [e]) =>
        check_is_15 "encode_status_access: cond" cond [(T,24), (T,16), (e, 9)]
   | _ => raise ERR "encode_status_access"
            ("cannot encode: " ^ term_to_string tm)));

fun encode_load_store (cond,tm) = term_list_to_num ((cond,28)::
 (case dest_strip tm
  of ("Load", [p,u,b,w,_,n,t,mode2]) =>
        [(T,26), (p,24), (u,23), (b,22), (w,21), (T,20), (n,16), (t,12)] @
        encode_mode2 mode2
   | ("Store", [p,u,b,w,_,n,t,mode2]) =>
        [(T,26), (p,24), (u,23), (b,22), (w,21), (n,16), (t,12)] @
        encode_mode2 mode2
   | ("Load_Halfword", [p,u,w,s,h,_,n,t,mode3]) =>
        [(p,24), (u,23), (w,21), (T,20), (n,16), (t,12), (T,7), (s,6),
         (h,5), (T,4)] @ encode_mode3 mode3
   | ("Store_Halfword", [p,u,w,_,n,t,mode3]) =>
        [(p,24), (u,23), (w,21), (n,16), (t,12), (T,7), (T,5), (T,4)] @
        encode_mode3 mode3
   | ("Load_Dual", [p,u,w,n,t,t2,mode3]) =>
        [(p,24), (u,23), (w,21), (n,16), (t,12), (T,7), (T,6), (T,4)] @
        encode_mode3 mode3
   | ("Store_Dual", [p,u,w,n,t,t2,mode3]) =>
        [(p,24), (u,23), (w,21), (n,16), (t,12), (PC,4)] @ encode_mode3 mode3
   | ("Load_Multiple", [p,u,s,w,n,registers]) =>
        [(T,27), (p,24), (u,23), (s,22), (w,21), (T,20), (n,16), (registers,0)]
   | ("Store_Multiple", [p,u,s,w,n,registers]) =>
        [(T,27), (p,24), (u,23), (s,22), (w,21), (n,16), (registers,0)]
   | ("Load_Exclusive", [n,t,imm8]) =>
        check ("encode_load_store", tm) (fn _ => is_0 imm8)
          [(``0b11001w:word5``,20), (n,16), (t,12),
           (``0b111110011111w:word12``,0)]
   | ("Store_Exclusive", [n,d,t,imm8]) =>
        check ("encode_load_store", tm) (fn _ => is_0 imm8)
          [(T,24), (T,23), (n,16), (d,12), (``0b11111001w:word8``,4), (t,0)]
   | ("Load_Exclusive_Doubleword", [n,t,t2]) =>
        [(``0b11011w:word5``,20), (n,16), (t,12),
         (``0b111110011111w:word12``,0)]
   | ("Store_Exclusive_Doubleword", [n,d,t,t2]) =>
        [(``0b1101w:word4``,21), (n,16), (d,12),
         (``0b11111001w:word8``,4), (t,0)]
   | ("Load_Exclusive_Halfword", [n,t]) =>
        [(``0b11111w:word5``,20), (n,16), (t,12),
         (``0b111110011111w:word12``,0)]
   | ("Store_Exclusive_Halfword", [n,d,t]) =>
        [(PC,21), (n,16), (d,12), (``0b11111001w:word8``,4), (t,0)]
   | ("Load_Exclusive_Byte", [n,t]) =>
        [(``0b11101w:word5``,20), (n,16), (t,12),
         (``0b111110011111w:word12``,0)]
   | ("Store_Exclusive_Byte", [n,d,t]) =>
        [(``0b1110w:word4``,21), (n,16), (d,12),
         (``0b11111001w:word8``,4), (t,0)]
   | ("Store_Return_State", [p,u,w,mode]) =>
        check_is_15 "encode_load_store: cond" cond
          [(T,27), (p,24), (u,23), (T,22), (w,21),
           (``0b110100000101w:word12``,8), (mode,0)]
   | ("Return_From_Exception", [p,u,w,n]) =>
        check_is_15 "encode_load_store: cond" cond
          [(T,27), (p,24), (u,23), (w,21), (T,20), (n,16),
           (``0b1010w:word4``,8)]
   | _ => raise ERR "encode_load_store"
            ("cannot encode: " ^ term_to_string tm)));

fun encode_miscellaneous (cond,tm) = term_list_to_num ((cond,28)::
 (case dest_strip tm
  of ("Hint", [h]) =>
        [(T,25), (T,24), (T,21), (PC,12)] @ hint h
   | ("Breakpoint", [imm16]) =>
        check ("encode_miscellaneous", pairSyntax.mk_pair (cond,tm))
          (fn _ => is_AL cond)
          [(T,24), (T,21), (imm16$(15,4),8), (``0b111w:word3``,4),
           (imm16$(3,0),0)]
   | ("Data_Memory_Barrier", [opt]) =>
        check_is_15 "encode_miscellaneous: cond" cond
          [(``0b010101111111111100000101w:word24``,4), (opt,0)]
   | ("Data_Synchronization_Barrier", [opt]) =>
        check_is_15 "encode_miscellaneous: cond" cond
          [(``0b010101111111111100000100w:word24``,4), (opt,0)]
   | ("Instruction_Synchronization_Barrier", [opt]) =>
        check_is_15 "encode_miscellaneous: cond" cond
          [(``0b010101111111111100000110w:word24``,4), (opt,0)]
   | ("Swap", [b,n,t,t2]) =>
        [(T,24), (b,22), (n,16), (t,12), (``0b1001w:word4``,4), (t2,0)]
   | ("Preload_Data", [u,r,n,mode2]) =>
        check_is_15 "encode_miscellaneous: cond" cond
          ([(T,26), (T,24), (u,23), (NOT r,22), (T,20), (n,16), (PC,12)] @
           encode_mode2 mode2)
   | ("Preload_Instruction", [u,n,mode2]) =>
        check_is_15 "encode_miscellaneous: cond" cond
          ([(T,26), (u,23), (T,22), (T,20), (n,16), (PC,12)] @
           encode_mode2 mode2)
   | ("Supervisor_Call", [imm24]) =>
        [(PC,24), (imm24,0)]
   | ("Secure_Monitor_Call", [imm4]) =>
        [(``0b000101100000000000000111w:word24``,4), (imm4,0)]
   | ("Clear_Exclusive", []) =>
        check_is_15 "encode_miscellaneous: cond" cond
          [(``0b0101011111111111000000011111w:word28``,0)]
   | _ => raise ERR "encode_miscellaneous"
            ("cannot encode: " ^ term_to_string tm)));

fun encode_coprocessor (cond,tm) = term_list_to_num ((cond,28)::
 (case dest_strip tm
  of ("Coprocessor_Load", [p,u,d,w,n,cd,coproc,imm8]) =>
        [(T,27), (T,26), (p,24), (u,23), (d,22), (w,21), (T,20),
         (n,16), (cd,12), (coproc,8), (imm8,0)]
   | ("Coprocessor_Store", [p,u,d,w,n,cd,coproc,imm8]) =>
        [(T,27), (T,26), (p,24), (u,23), (d,22), (w,21),
         (n,16), (cd,12), (coproc,8), (imm8,0)]
   | ("Coprocessor_Data_Processing", [opc1,n,d,coproc,opc2,m]) =>
        [(``0b111w:word3``,25), (opc1,20), (n,16), (d,12),
         (coproc, 8), (opc2,5), (m,0)]
   | ("Coprocessor_Transfer", [opc1,mrc,n,t,coproc,opc2,m]) =>
        [(``0b111w:word3``,25), (opc1,21), (mrc,20), (n,16), (t,12),
         (coproc, 8), (opc2,5), (T,4), (m,0)]
   | ("Coprocessor_Transfer_Two", [mrrc,t2,t,coproc,opc,m]) =>
        [(``0b110001w:word6``,22), (mrrc,20), (t2,16), (t,12),
         (coproc, 8), (opc,4), (m,0)]
   | _ => raise ERR "encode_coprocessor"
            ("cannot encode: " ^ term_to_string tm)));

(* ------------------------------------------------------------------------- *)

fun thumb_encode_branch (cond,tm) =
let val checkbr = check ("thumb_encode_branch", tm) in
 term_list_to_num
   (case dest_strip tm
    of ("Branch_Target", [imm24]) =>
          if is_var cond orelse is_AL cond then
            let val high_bits = uint_of_word (imm24$(23,11)) in
              checkbr (fn _ => high_bits = 0 orelse high_bits = 8191)
                [(``0b111w:word3``,13), (imm24$(10,0),0)]
            end
          else
            let val high_bits = uint_of_word (imm24$(23,8)) in
              checkbr (fn _ => high_bits = 0 orelse high_bits = 65535)
                [(``0b1101w:word4``,12), (cond,8), (imm24$(7,0),0)]
            end
     | ("Branch_Exchange", [m]) =>
          [(``0b10001110w:word8``,7), (m, 3)]
     | ("Branch_Link_Exchange_Register", [m]) =>
          [(``0b10001111w:word8``,7), (m, 3)]
     | ("Compare_Branch", [nzero,imm6,n]) =>
          checkbr (fn _ => width_okay 3 n)
            [(``0b1011w:word4``,12), (nzero,11), (imm6$(5,5),9), (T,8),
             (imm6$(4,0),3), (n,0)]
     | _ => raise ERR "thumb_encode_branch"
              ("cannot encode: " ^ term_to_string tm))
end;

local
  fun thumb_encode_register (opc,n,d,mode1) s =
  let val (imm5,typ,m) = dest_Mode1_register mode1 in
    check ("thumb_encode_register", mode1)
      (fn _ => is_0 imm5 andalso is_0 typ andalso
               (is_PC n orelse d ~~ n) andalso Lib.all (width_okay 3) [d,m])
      [(T,14), (opc,6), (m,3), (d,0)]
  end

  fun arm_expand_imm tm =
        ``(((7 >< 0) ^tm) #>> (2 * (w2n ((11 -- 8) ^tm)))) : word32``
          |> eval

  fun aligned tm = (uint_of_word tm) mod 4 = 0
in
  fun thumb_encode_data_processing tm =
  let val checkdp = check ("thumb_encode_data_processing",tm) in
   term_list_to_num
   (case dest_strip tm
    of ("Data_Processing", [opc,sflag,n,d,mode1]) =>
          (case uint_of_word opc
           of 0  => thumb_encode_register (opc,n,d,mode1) "add"
            | 1  => thumb_encode_register (opc,n,d,mode1) "eor"
            | 2  => if is_Mode1_immediate mode1 then
                      let val imm = dest_Mode1_immediate mode1 in
                        if is_SP n then
                          let val imm32 = arm_expand_imm imm in
                            checkdp
                              (fn _ => is_SP d andalso width_okay 9 imm32
                                       andalso aligned imm32)
                              [(``0b101100001w:9 word``,7), (imm32$(8,2),0)]
                          end
                        else if d ~~ n then
                          checkdp (fn _ => width_okay 3 d andalso
                                           width_okay 8 imm)
                             [(``0b111w:word3``,11), (d,8), (imm,0)]
                        else
                          checkdp (fn _ => Lib.all (width_okay 3) [imm,n,d])
                            [(``0b1111w:word4``,9), (imm,6), (n,3), (d,0)]
                      end
                    else
                      let val (imm5,typ,m) = dest_Mode1_register mode1 in
                        checkdp
                          (fn _ => is_0 imm5 andalso is_0 typ andalso
                                   Lib.all (width_okay 3) [m,n,d])
                          [(``0b1101w:word4``,9), (m,6), (n,3), (d,0)]
                      end
            | 3  => let val imm = dest_Mode1_immediate mode1 in
                      checkdp
                        (fn _ => is_0 imm andalso Lib.all (width_okay 3) [n,d])
                        [(``0b100001001w:9 word``,6), (n,3), (d,0)]
                    end
            | 4  => if is_Mode1_immediate mode1 then
                      let val imm = dest_Mode1_immediate mode1 in
                        if is_SP n then
                          let val imm32 = arm_expand_imm imm in
                            if is_SP d then
                              checkdp
                                (fn _ => aligned imm32 andalso
                                         width_okay 9 imm32) (* ADD(7) *)
                                [(``0b1011w:word4``,12), (imm32$(8,2),0)]
                            else
                              checkdp (* ADD(6) *)
                                (fn _ => aligned imm32 andalso width_okay 3 d
                                         andalso width_okay 10 imm32)
                                [(``0b10101w:word5``,11), (d,8),
                                 (imm32$(9,2),0)]
                          end
                        else if d ~~ n then
                          checkdp (* ADD(2) *)
                             (fn _ => width_okay 8 imm andalso width_okay 3 d)
                             [(``0b11w:word2``,12), (d,8), (imm,0)]
                        else
                          checkdp (* ADD(1) *)
                            (fn _ => Lib.all (width_okay 3) [imm,n,d])
                            [(``0b111w:word3``,10), (imm,6), (n,3), (d,0)]
                      end
                    else
                      let val (imm5,typ,m) = dest_Mode1_register mode1
                          val _ = checkdp
                                    (fn _ => is_0 imm5 andalso is_0 typ) []
                      in
                        if is_F sflag andalso d ~~ n then (* ADD(4) *)
                          [(``0b10001w:word5``,10), (d$(3,3),7), (m,3),
                           (d$(2,0),0)]
                        else if is_F sflag andalso d ~~ m then (* ADD(4) *)
                          [(``0b10001w:word5``,10), (d$(3,3),7), (n,3),
                           (d$(2,0),0)]
                        else
                          checkdp (*  ADD(3) *)
                            (fn _ => Lib.all (width_okay 3) [m,n,d])
                            [(``0b11w:word2``,11), (m,6), (n,3), (d,0)]
                      end
            | 5  => thumb_encode_register (opc,n,d,mode1) "adc"
            | 6  => thumb_encode_register (opc,n,d,mode1) "sbc"
            | 7  => raise ERR "thumb_encode_data_processing" "invalid opcode"
            | 8  => thumb_encode_register (opc,d,n,mode1) "tst"
            | 9  => raise ERR "thumb_encode_data_processing" "invalid opcode"
            | 10 => if is_Mode1_immediate mode1 then
                      let val imm = dest_Mode1_immediate mode1 in
                        checkdp
                          (fn _ => width_okay 8 imm andalso width_okay 3 n)
                          [(``0b101w:word3``,11), (n,8), (imm,0)]
                      end
                    else
                      let val (imm5,typ,m) = dest_Mode1_register mode1
                          val _ = checkdp
                                    (fn _ => is_0 imm5 andalso is_0 typ) []
                      in
                        if Lib.all (width_okay 3) [n,m] then
                          [(``0b100001010w:9 word``,6), (m,3), (n,0)]
                        else
                          [(``0b1000101w:word7``,8), (n$(3,3),7), (m,3),
                           (n$(2,0),0)]
                      end
            | 11 => thumb_encode_register (opc,d,n,mode1) "cmn"
            | 12 => thumb_encode_register (opc,n,d,mode1) "orr"
            | 13 => if is_Mode1_immediate mode1 then
                      let val imm = dest_Mode1_immediate mode1 in
                        checkdp
                          (fn _ => width_okay 8 imm andalso width_okay 3 d)
                          [(T,13), (d,8), (imm,0)]
                      end
                    else if is_Mode1_register mode1 then
                      let val (imm5,typ,m) = dest_Mode1_register mode1 in
                        if Lib.all (width_okay 3) [d,m] then
                          checkdp
                            (fn _ => not (Term.term_eq typ ``0b11w:word2``))
                            [(typ,11), (imm5,6), (m,3), (d,0)]
                        else
                          checkdp (fn _ => is_0 imm5 andalso is_0 typ)
                            [(``0b100011w:word6``,9), (d$(3,3),7), (m,3),
                             (d$(2,0),0)]
                      end
                    else
                      let val (s,typ,m) =
                                   dest_Mode1_register_shifted_register mode1
                          val sh = case uint_of_word typ
                                   of 0 => ``0b010w:word3``
                                    | 1 => ``0b011w:word3``
                                    | 2 => ``0b100w:word3``
                                    | 3 => ``0b111w:word3``
                                    | _ => raise ERR
                                             "thumb_encode_data_processing"
                                             "not a valid mov (shift register)"
                      in
                        checkdp
                          (fn _ => d ~~ m andalso Lib.all (width_okay 3) [s,m])
                          [(T,14), (sh,6), (s,3), (m,0)]
                      end
            | 14 => thumb_encode_register (opc,n,d,mode1) "bic"
            | 15 => thumb_encode_register (opc,n,d,mode1) "mvn"
            | _  => raise ERR "thumb_encode_data_processing" "invalid opcode")
     | ("Add_Sub", [a,n,d,imm12]) =>
          let val imm8 = imm12$(9,2) in
            checkdp
              (fn _ => aligned imm12 andalso is_T a andalso is_PC n andalso
                       width_okay 3 d)
              [(``0b1010w:word3``,12), (d,8), (imm8,0)] (* ADD(5) *)
          end
     | ("Multiply", [acc,_,d,_,m,n]) =>
          checkdp (fn _ => is_F acc andalso d ~~ m andalso
                           Lib.all (width_okay 3) [m,n])
            [(``0b0100001101w:word10``,6), (n,3), (m,0)]
     | ("Extend_Byte", [u,n,d,rot,m]) =>
          checkdp (fn _ => is_0 rot andalso is_PC n andalso
                           Lib.all (width_okay 3) [m,d])
            [(``0b10110010w:word8``,8), (u,7), (T,6), (m,3), (d,0)]
     | ("Extend_Halfword", [u,n,d,rot,m]) =>
          checkdp (fn _ => is_0 rot andalso is_PC n andalso
                           Lib.all (width_okay 3) [m,d])
            [(``0b10110010w:word8``,8), (u,7), (m,3), (d,0)]
     | ("Byte_Reverse_Word", [d,m]) =>
          checkdp (fn _ => Lib.all (width_okay 3) [m,d])
            [(``0b10111010w:word8``,8), (m,3), (d,0)]
     | ("Byte_Reverse_Packed_Halfword", [d,m]) =>
          checkdp (fn _ => Lib.all (width_okay 3) [m,d])
            [(``0b10111010w:word8``,8), (T,6), (m,3), (d,0)]
     | ("Byte_Reverse_Signed_Halfword", [d,m]) =>
          checkdp (fn _ => Lib.all (width_okay 3) [m,d])
            [(``0b1011101011w:word10``,6), (m,3), (d,0)]
     | _ => raise ERR "thumb_encode_data_processing"
              ("cannot encode: " ^ term_to_string tm))
  end
end;

fun thumb_encode_status_access tm = term_list_to_num
 (case dest_strip tm
  of ("Change_Processor_State", [imod,a,i,f,mode]) =>
        let val im = case uint_of_word imod
                     of 2 => T
                      | 3 => F
                      | _ => raise ERR "thumb_encode_status_access"
                                       "invalid imod"
        in
          check ("encode_status_access", tm) (fn _ => optionSyntax.is_none mode)
            [(``0b10110110011w:word11``,5), (im,4), (a,2), (i,1), (f,0)]
        end
   | ("Set_Endianness", [e]) =>
          [(``0b101101100101w:word12``,4), (e,3)]
   | _ => raise ERR "thumb_encode_status_access"
            ("cannot encode: " ^ term_to_string tm));

fun thumb_encode_load_store tm = term_list_to_num
let val checkls = check ("thumb_encode_load_store",tm) in
   (case dest_strip tm
    of ("Load", [p,u,b,w,unpriv,n,t,mode2]) =>
         checkls (fn _ => is_F unpriv)
         (if is_Mode2_immediate mode2 then
            let val imm12 = dest_Mode2_immediate mode2 in
              if is_PC n orelse is_SP n then
                let val imm8 = imm12$(10,2)
                    val x = if is_PC n then ``0b01001w:word5``
                                       else ``0b10011w:word5``
                in
                  checkls
                    (fn _ => is_T p andalso is_T u andalso is_F b andalso
                             is_F w andalso width_okay 3 t andalso
                             is_0 (imm12$(1,0)) andalso width_okay 8 imm8)
                    [(x,11), (t,8), (imm8,0)]
                end
              else
                let val imm5 = if is_T b then imm12 else imm12$(11,2) in
                  checkls
                    (fn _ => is_T p andalso is_T u andalso is_F w andalso
                             (is_T b orelse is_0 (imm12$(1,0))) andalso
                             width_okay 5 imm5 andalso
                             Lib.all (width_okay 3) [n,t])
                    [(T,14), (T,13), (b,12), (T,11), (imm5,6), (n,3), (t,0)]
                end
            end
          else
            let val (imm5,typ,m) = dest_Mode2_register mode2 in
              checkls
                (fn _ => is_T p andalso is_T u andalso is_F w andalso
                         is_0 imm5 andalso is_0 typ andalso
                         Lib.all (width_okay 3) [m,n,t])
                [(``0b1011w:word4``,11), (b,10), (m,6), (n,3), (t,0)]
            end)
     | ("Store", [p,u,b,w,unpriv,n,t,mode2]) =>
         checkls (fn _ => is_F unpriv)
         (if is_Mode2_immediate mode2 then
            let val imm12 = dest_Mode2_immediate mode2 in
              if is_SP n then
                let val imm8 = imm12$(10,2) in
                  checkls
                    (fn _ => is_T p andalso is_T u andalso is_F b andalso
                             is_F w andalso width_okay 3 t andalso
                             is_0 (imm12$(1,0)) andalso width_okay 8 imm8)
                    [(``0b1001w:word4``,12), (t,8), (imm8,0)]
                end
              else
                let val imm5 = if is_T b then imm12 else imm12$(11,2) in
                  checkls
                    (fn _ => is_T p andalso is_T u andalso is_F w andalso
                             (is_T b orelse is_0 (imm12$(1,0))) andalso
                             width_okay 5 imm5 andalso
                             Lib.all (width_okay 3) [n,t])
                    [(T,14), (T,13), (b,12), (imm5,6), (n,3), (t,0)]
                end
            end
          else
            let val (imm5,typ,m) = dest_Mode2_register mode2 in
              checkls
                (fn _ => is_T p andalso is_T u andalso is_F w andalso
                         is_0 imm5 andalso is_0 typ andalso
                         Lib.all (width_okay 3) [m,n,t])
                [(``0b101w:word4``,12), (b,10), (m,6), (n,3), (t,0)]
            end)
     | ("Load_Halfword", [p,u,w,s,h,unpriv,n,t,mode3]) =>
         checkls (fn _ => is_F unpriv)
         (if is_Mode3_immediate mode3 then
            let val imm12 = dest_Mode3_immediate mode3
                val imm5 = imm12$(11,1)
            in
              checkls
                (fn _ => is_T p andalso is_T u andalso is_F w andalso
                         is_T h andalso is_F s andalso
                         is_0 (imm12$(0,0)) andalso width_okay 5 imm5 andalso
                         Lib.all (width_okay 3) [n,t])
                [(T,15), (T,11), (imm5,6), (n,3), (t,0)]
            end
          else
            let val (imm2,m) = dest_Mode3_register mode3 in
              checkls
                (fn _ => is_T p andalso is_T u andalso is_F w andalso
                         (is_T s orelse is_T h) andalso
                         is_0 imm2 andalso Lib.all (width_okay 3) [m,n,t])
                [(``0b101w:word3``,12), (h,11), (s,10), (T,9), (m,6), (n,3),
                 (t,0)]
            end)
     | ("Store_Halfword", [p,u,w,unpriv,n,t,mode3]) =>
         checkls (fn _ => is_F unpriv)
         (if is_Mode3_immediate mode3 then
            let val imm12 = dest_Mode3_immediate mode3
                val imm5 = imm12$(11,1)
            in
              checkls
                (fn _ => is_T p andalso is_T u andalso is_F w andalso
                         is_0 (imm12$(0,0)) andalso width_okay 5 imm5 andalso
                         Lib.all (width_okay 3) [n,t])
                [(T,15), (imm5,6), (n,3), (t,0)]
            end
          else
            let val (imm2,m) = dest_Mode3_register mode3 in
              checkls
                (fn _ => is_T p andalso is_T u andalso is_F w andalso
                         is_0 imm2 andalso Lib.all (width_okay 3) [m,n,t])
                [(``0b101001w:word6``,9), (m,6), (n,3), (t,0)]
            end)
     | ("Load_Multiple", [p,u,s,w,n,registers]) =>
          if is_SP n then
            checkls
              (fn _ => is_F p andalso is_T u andalso is_F s andalso
                       is_T w andalso is_0 (registers$(14,8)))
              [(``0b101111w:word6``,10), (registers$(15,15),8),
               (registers$(7,0),0)]
          else
            checkls
              (fn _ => let val rn = uint_of_word n in
                         is_F p andalso is_T u andalso is_F s andalso
                         is_T w = is_0 (registers$(rn,rn)) andalso
                         is_0 (registers$(15,8)) andalso width_okay 3 n
                       end)
              [(``0b11001w:word5``,11), (n,8), (registers$(7,0),0)]
     | ("Store_Multiple", [p,u,s,w,n,registers]) =>
          if is_SP n then
            checkls
              (fn _ => is_T p andalso is_F u andalso is_F s andalso
                       is_T w andalso is_0 (registers$(13,8)) andalso
                       is_0 (registers$(15,15)))
              [(``0b101101w:word6``,10), (registers$(14,14),8),
               (registers$(7,0),0)]
          else
            checkls
              (fn _ => is_F p andalso is_T u andalso is_F s andalso
                       is_T w andalso is_0 (registers$(15,8)) andalso
                       width_okay 3 n)
              [(``0b11w:word2``,14), (n,8), (registers$(7,0),0)]
     | _ => raise ERR "thumb_encode_load_store"
              ("cannot encode: " ^ term_to_string tm))
end;

fun thumb_encode_miscellaneous tm =
let val checkmisc = check ("thumb_encode_miscellaneous",tm) in
  term_list_to_num
   (case dest_strip tm
    of ("Hint", [h]) =>
          (``0b10111111w:word8``,8)::(thumb_hint h)
     | ("Breakpoint", [imm16]) =>
          checkmisc (fn _ => is_0 (imm16$(15,8)))
            [(``0b1011111w:word7``,9), (imm16$(7,0),0)]
     | ("Supervisor_Call", [imm24]) =>
          checkmisc (fn _ => is_0 (imm24$(23,8)))
            [(``0b11011111w:word8``,8), (imm24$(7,0),0)]
     | ("If_Then", [firstcond,mask]) =>
          checkmisc (fn _ => not (is_PC firstcond orelse is_0 mask))
          [(``0b10111111w:word8``,8), (firstcond,4), (mask,0)]
     | _ => raise ERR "thumb_encode_miscellaneous"
              ("cannot encode: " ^ term_to_string tm))
end;

(* ------------------------------------------------------------------------- *)

fun thumb2_encode_branch (cond,tm) =
let val checkb = check ("thumb2_encode_branch", tm)
    val is_1  = Term.term_eq ``1w:word24``
    val is_1s = Term.term_eq ``0b1111w:word24``
in
  term_list_to_num
   (case dest_strip tm
    of ("Branch_Target", [imm24]) =>
          if is_var cond orelse is_AL cond then
            let val s  = imm24$(23,23)
                val S  = is_1 s
                val i1 = is_1 (imm24$(21,21))
                val i2 = is_1 (imm24$(22,22))
                val j1 = mk_bool (i1 = S)
                val j2 = mk_bool (i2 = S)
            in
              [(PC,28), (s,26), (imm24$(20,11),16), (T,15), (j1,13), (T,12),
               (j2,11), (imm24$(10,0),0)]
            end
          else
            let val top_bits = imm24$(23,20) in
              checkb (fn _ => is_1s top_bits orelse is_0 top_bits)
                [(PC,28), (imm24$(19,19),26), (cond,22), (imm24$(16,11),16),
                 (T,15), (imm24$(17,17),13), (imm24$(18,18),11),
                 (imm24$(10,0),0)]
            end
     | ("Branch_Link_Exchange_Immediate", [h,toarm,imm24]) =>
          let val s  = imm24$(22,22)
              val S  = is_1 s
              val i1 = is_1 (imm24$(20,20))
              val i2 = is_1 (imm24$(21,21))
              val j1 = mk_bool (i1 = S)
              val j2 = mk_bool (i2 = S)
          in
            checkb (fn _ => is_F toarm orelse is_F h)
              [(PC,28), (s,26), (imm24$(19,10),16), (T,15), (T,14), (j1,13),
               (NOT toarm,12), (j2,11), (imm24$(9,0),1), (h,0)]
          end
     | ("Table_Branch_Byte", [n,h,m]) =>
          [(``0b111010001101w:word12``,20), (n,16), (PC,12), (h,4), (m,0)]
     | _ => raise ERR "encode_branch" ("cannot encode: " ^ term_to_string tm))
end;

fun thumb2_opcode tm =
  case uint_of_word tm
  of 0  => ``0b0000w:word4`` (* AND *)
   | 1  => ``0b0100w:word4`` (* EOR *)
   | 2  => ``0b1101w:word4`` (* SUB *)
   | 3  => ``0b1110w:word4`` (* RSB *)
   | 4  => ``0b1000w:word4`` (* ADD *)
   | 5  => ``0b1010w:word4`` (* ADC *)
   | 6  => ``0b1011w:word4`` (* SBC *)
   | 7  => raise ERR "thumb2_opcode" "rsc not available"
   | 8  => ``0b0000w:word4`` (* TST *)
   | 9  => ``0b0100w:word4`` (* TEQ *)
   | 10 => ``0b1101w:word4`` (* CMP *)
   | 11 => ``0b1000w:word4`` (* CMN *)
   | 12 => ``0b0010w:word4`` (* ORR *)
   | 13 => ``0b0010w:word4`` (* MOV *)
   | 14 => ``0b0001w:word4`` (* BIC *)
   | 15 => ``0b0011w:word4`` (* MVN/ORN *)
   | _  => raise ERR "thumb2_opcode" "cannot encode"

fun check_thumb2_dp (tm,rd,rn) =
  case uint_of_word tm
  of 8  => is_PC rd
   | 9  => is_PC rd
   | 10 => is_PC rd
   | 11 => is_PC rd
   | 13 => is_PC rn
   | _  => true;

fun thumb2_encode_data_processing tm =
let val checkdp = check ("thumb2_encode_data_processing",tm) in
 term_list_to_num ((``0b111w:word3``,29)::
   (case dest_strip tm
    of ("Data_Processing", [opc,s,n,d,mode1]) =>
        checkdp (fn _ => check_thumb2_dp (opc,d,n))
         (if is_Mode1_immediate mode1 then
            let val imm12 = dest_Mode1_immediate mode1 in
              if is_PC d andalso is_LR n andalso is_T s then
                checkdp (fn _ => width_okay 8 imm12)
                  [(``0b100111101111010001111w:21 word``,8), (imm12$(7,0),0)]
              else
                let val (i,imm3,imm8) = (imm12$(11,11),imm12$(10,8),imm12$(7,0))
                in
                  [(T,28), (i,26), (thumb2_opcode opc,21), (s,20), (n,16),
                   (imm3,12), (d,8), (imm8,0)]
                end
            end
          else if is_Mode1_register mode1 then
            let val (imm5,typ,m) = dest_Mode1_register mode1
                val (imm3,imm2) = (imm5$(4,2),imm5$(1,0))
            in
              [(``0b101w:word3``,25), (thumb2_opcode opc,21), (s,20), (n,16),
               (imm3,12), (d,8), (imm2,6), (typ,4), (m,0)]
            end
          else
            let val (rs,typ,m) = dest_Mode1_register_shifted_register mode1 in
              checkdp (fn _ => is_SP opc)
                [(``0b1101w:word4``,25), (typ,21), (s,20), (m,16),
                 (PC,12), (d,8), (rs,0)]
            end)
     | ("Move_Halfword", [h,d,imm16]) =>
          [(T,28), (imm16$(11,11),26), (T,25), (h,23), (T,22),
           (imm16$(15,12),16), (imm16$(10,8),12), (d,8), (imm16$(7,0),0)]
     | ("Add_Sub", [a,n,d,imm12]) =>
          [(T,28), (imm12$(11,11),26), (T,25), (NOT a,23), (NOT a,21), (n,16),
           (imm12$(10,8),12), (d,8), (imm12$(7,0),0)]
     | ("Multiply", [acc,s,d,a,m,n]) =>
          checkdp (fn _ => is_F s)
            [(``0b11011w:word5``,24), (n,16), (if is_T acc then a else PC,12),
             (d,8), (m,0)]
     | ("Multiply_Subtract", [d,a,m,n]) =>
          [(``0b11011w:word5``,24), (n,16), (a,12), (d,8), (T,4), (m,0)]
     | ("Signed_Halfword_Multiply", [opc,M,N,d,a,m,n]) =>
          let val (opc1,opc2,acc,N') =
                     case uint_of_word opc
                     of 0 => (``0b01w:word2``,F,a,N)
                      | 1 => (``0b11w:word2``,F,if is_T N then PC else a,F)
                      | 2 => (``0b1100w:word4``,T,a,N)
                      | 3 => (``0b01w:word2``,F,PC,N)
                      | _ => raise ERR "thumb2_encode_data_processing"
                                       "cannot encode"
          in
            [(``0b11011w:word5``,24), (opc1,20), (n,16), (acc,12), (d,8),
             (opc2,7), (N',5), (M,4), (m,0)]
          end
     | ("Signed_Multiply_Dual", [d,a,m,M,N,n]) =>
          [(``0b11011w:word5``,24), (M,22), (NOT M,21), (n,16), (a,12), (d,8),
           (N,4), (m,0)]
     | ("Signed_Multiply_Long_Dual", [dhi,dlo,m,M,N,n]) =>
          [(``0b1101111w:word7``,22), (M,20), (n,16), (dlo,12), (dhi,8),
           (``0b11w:word2``,6), (N,4), (m,0)]
     | ("Signed_Most_Significant_Multiply", [d,a,m,r,n]) =>
          [(``0b110110101w:9 word``,20), (n,16), (a,12), (d,8), (r,4), (m,0)]
     | ("Signed_Most_Significant_Multiply_Subtract", [d,a,m,r,n]) =>
          [(``0b11011011w:word8``,21), (n,16), (a,12), (d,8), (r,4), (m,0)]
     | ("Multiply_Long", [sgnd,a,s,dhi,dlo,m,n]) =>
          checkdp (fn _ => is_F s)
            [(``0b110111w:word6``,23), (a,22), (NOT sgnd,21), (n,16),
             (dlo,12), (dhi,8), (m,0)]
     | ("Multiply_Accumulate_Accumulate", [dhi,dlo,m,n]) =>
          [(``0b11011111w:word8``,21), (n,16), (dlo,12), (dhi,8),
           (``0b11w:word2``,5), (m,0)]
     | ("Saturate", [u,sat,d,imm5,sh,n]) =>
          [(``0b10011w:word4``,24), (u,23), (sh,21), (n,16),
           (imm5$(4,2),12), (d,8), (imm5$(1,0),6), (sat,0)]
     | ("Saturate_16", [u,imm4,d,n]) =>
          [(``0b10011w:word4``,24), (u,23), (T,21), (n,16), (d,8), (imm4,0)]
     | ("Saturating_Add_Subtract", [opc,n,d,m]) =>
          let val opc1 = case uint_of_word opc
                         of 1 => ``0b10w:word2``
                          | 2 => ``0b01w:word2``
                          | _ => opc
          in
            [(``0b110101w:word6``,23), (n,16), (PC,12), (d,8), (T,7),
             (opc1,4), (m,0)]
          end
     | ("Pack_Halfword", [n,d,imm5,t,m]) =>
          [(``0b101011w:word6``,22), (n,16), (imm5$(4,2),12), (d,8),
           (imm5$(1,0),6), (t,5), (m,0)]
     | ("Extend_Byte", [u,n,d,rot,m]) =>
          [(``0b1101001w:word7``,22), (u,20), (n,16), (PC,12), (d,8),
           (T,7), (rot,4), (m,0)]
     | ("Extend_Byte_16", [u,n,d,rot,m]) =>
          [(``0b11010001w:word7``,21), (u,20), (n,16), (PC,12), (d,8),
           (T,7), (rot,4), (m,0)]
     | ("Extend_Halfword", [u,n,d,rot,m]) =>
          [(``0b1101w:word4``,25), (u,20), (n,16), (PC,12), (d,8),
           (T,7), (rot,4), (m,0)]
     | ("Bit_Field_Clear_Insert", [msb,d,lsb,n]) =>
          [(``0b10011011w:word7``,21), (n,16), (lsb$(4,2),12), (d,8),
           (lsb$(1,0),6), (msb,0)]
     | ("Count_Leading_Zeroes", [d,m]) =>
          [(``0b110101011w:9 word``,20), (m,16), (PC,12), (d,8), (T,7), (m,0)]
     | ("Reverse_Bits", [d,m]) =>
          [(``0b110101001w:9 word``,20), (m,16), (PC,12), (d,8),
           (T,7), (T,5), (m,0)]
     | ("Byte_Reverse_Word", [d,m]) =>
          [(``0b110101001w:9 word``,20), (m,16), (PC,12), (d,8), (T,7), (m,0)]
     | ("Byte_Reverse_Packed_Halfword", [d,m]) =>
          [(``0b110101001w:9 word``,20), (m,16), (PC,12), (d,8),
           (T,7), (T,4), (m,0)]
     | ("Byte_Reverse_Signed_Halfword", [d,m]) =>
          [(``0b110101001w:9 word``,20), (m,16), (PC,12), (d,8),
           (``0b1011w:word4``,4), (m,0)]
     | ("Bit_Field_Extract", [u,w,d,lsb,n]) =>
          [(``0b10011w:word5``,24), (u,23), (T,22), (n,16), (lsb$(4,2),12),
           (d,8), (lsb$(1,0),6), (w,0)]
     | ("Select_Bytes", [n,d,m]) =>
          [(``0b11010101w:word8``,21), (n,16), (PC,12), (d,8), (T,7), (m,0)]
     | ("Unsigned_Sum_Absolute_Differences", [d,a,m,n]) =>
          [(``0b110110111w:9 word``,20), (n,16), (a,12), (d,8), (m,0)]
     | ("Parallel_Add_Subtract", [u,opc,n,d,m]) =>
          let val (opc1,opc2) = thumb_parallel_add_sub opc in
            [(``0b110101w:word6``,23), (opc2,20), (n,16), (PC,12), (d,8),
             (u,6), (opc1,4), (m,0)]
          end
     | ("Divide", [u,n,d,m]) =>
          [(``0b110111w:word6``,23), (u,21), (T,20), (n,16), (PC,12),
           (d,8), (PC,4), (m,0)]
     | _ => raise ERR "thumb2_encode_data_processing"
              ("cannot encode: " ^ term_to_string tm)))
end;

fun thumb2_encode_status_access tm = term_list_to_num
 (case dest_strip tm
  of ("Status_to_Register", [r,d]) =>
        [(``0b11110011111w:word11``,21), (r,20), (PC,16), (T,15), (d,8)]
   | ("Register_to_Status", [r,mask,n]) =>
        [(``0b111100111w:9 word``,23), (r,20), (n,16), (T,15), (mask,8)]
   | ("Change_Processor_State", [imod,a,i,f,mode]) =>
        let val (M,m) = if optionSyntax.is_some mode then
                          (T,optionSyntax.dest_some mode)
                        else
                          (F,mk_word4 0)
        in
          [(``0b11110011101011111w:17 word``,15), (imod,9),
           (M,8), (a,7), (i,6), (f,5), (m,0)]
        end
   | _ => raise ERR "thumb2_encode_status_access"
            ("cannot encode: " ^ term_to_string tm));

fun thumb2_encode_load_store tm =
let val checkls = check ("thumb2_encode_load_store",tm) in
   term_list_to_num ((``0b111w:word3``,29)::
   (case dest_strip tm
    of ("Load", [p,u,b,w,priv,n,t,mode2]) =>
          if is_Mode2_immediate mode2 then
            let val imm12 = dest_Mode2_immediate mode2 in
              if is_T p andalso is_F w andalso (is_T u orelse is_PC n) andalso
                 is_F priv
              then
                [(``0b11w:word2``,27), (u,23), (NOT b,22), (T,20), (n,16),
                 (t,12), (imm12,0)]
              else
                checkls (fn _ => width_okay 8 imm12 andalso
                     not (is_T b andalso is_PC t andalso is_T p andalso is_F u
                          andalso is_F w))
                  [(``0b11w:word2``,27), (NOT b,22), (T,20), (n,16), (t,12),
                   (T,11), (p,10), (u,9), (w,8), (imm12,0)]
            end
          else
            let val (imm5,typ,m) = dest_Mode2_register mode2 in
              checkls
                (fn _ => is_T p andalso is_T u andalso is_F w andalso
                         is_0 typ andalso width_okay 2 imm5)
                [(``0b11w:word2``,27), (NOT b,22), (T,20), (n,16), (t,12),
                 (imm5,4), (m,0)]
            end
     | ("Store", [p,u,b,w,priv,n,t,mode2]) =>
          if is_Mode2_immediate mode2 then
            let val imm12 = dest_Mode2_immediate mode2 in
              if is_T p andalso is_F w andalso (is_T u orelse is_PC n) andalso
                 is_F priv
              then
                [(``0b11w:word2``,27), (u,23), (NOT b,22), (n,16),
                 (t,12), (imm12,0)]
              else
                checkls (fn _ => width_okay 8 imm12)
                  [(``0b11w:word2``,27), (NOT b,22), (n,16), (t,12),
                   (T,11), (p,10), (u,9), (w,8), (imm12,0)]
            end
          else
            let val (imm5,typ,m) = dest_Mode2_register mode2 in
              checkls
                (fn _ => is_T p andalso is_T u andalso is_F w andalso
                         is_0 typ andalso width_okay 2 imm5)
                [(``0b11w:word2``,27), (NOT b,22), (n,16), (t,12),
                 (imm5,4), (m,0)]
            end
     | ("Load_Halfword", [p,u,w,s,h,priv,n,t,mode3]) =>
          if is_Mode3_immediate mode3 then
            let val imm12 = dest_Mode3_immediate mode3 in
              if is_T p andalso is_F w andalso (is_T u orelse is_PC n) andalso
                 is_F priv
              then
                [(``0b11w:word2``,27), (s,24), (u,23), (h,21), (T,20), (n,16),
                 (t,12), (imm12,0)]
              else
                checkls (fn _ => width_okay 8 imm12 andalso
                    not (is_PC t andalso is_T p andalso is_F u andalso is_F w))
                  [(``0b11w:word2``,27), (s,24), (h,21), (T,20), (n,16), (t,12),
                   (T,11), (p,10), (u,9), (w,8), (imm12,0)]
            end
          else
            let val (imm2,m) = dest_Mode3_register mode3 in
              checkls
                (fn _ => is_T p andalso is_T u andalso is_F w)
                [(``0b11w:word2``,27), (s,24), (h,21), (T,20), (n,16), (t,12),
                 (imm2,4), (m,0)]
            end
     | ("Store_Halfword", [p,u,w,priv,n,t,mode3]) =>
          if is_Mode3_immediate mode3 then
            let val imm12 = dest_Mode3_immediate mode3 in
              if is_T p andalso is_F w andalso (is_T u orelse is_PC n) andalso
                 is_F priv
              then
                [(``0b11w:word2``,27), (u,23), (T,21), (n,16),
                 (t,12), (imm12,0)]
              else
                checkls (fn _ => width_okay 8 imm12)
                  [(``0b11w:word2``,27), (T,21), (n,16), (t,12),
                   (T,11), (p,10), (u,9), (w,8), (imm12,0)]
            end
          else
            let val (imm2,m) = dest_Mode3_register mode3 in
              checkls
                (fn _ => is_T p andalso is_T u andalso is_F w)
                [(``0b11w:word2``,27), (T,21), (n,16), (t,12), (imm2,4), (m,0)]
            end
     | ("Load_Dual", [p,u,w,n,t,t2,mode3]) =>
          let val imm12 = dest_Mode3_immediate mode3
              val imm8 = imm12$(9,2)
          in
            checkls (fn _ => width_okay 10 imm12 andalso is_0 (imm12$(1,0)))
              [(T,27), (p,24), (u,23), (T,22), (w,21), (T,20), (n,16), (t,12),
               (t2,8), (imm8,0)]
          end
     | ("Store_Dual", [p,u,w,n,t,t2,mode3]) =>
          let val imm12 = dest_Mode3_immediate mode3
              val imm8 = imm12$(9,2)
          in
            checkls (fn _ => width_okay 8 imm12 andalso is_0 (imm12$(1,0)))
              [(T,27), (p,24), (u,23), (T,22), (w,21), (n,16), (t,12),
               (t2,8), (imm8,0)]
          end
     | ("Load_Multiple", [p,u,s,w,n,registers]) =>
          checkls
            (fn _ => is_F s andalso p ~~ NOT u andalso is_0 (registers$(13,13)))
            [(T,27), (p,24), (u,23), (w,21), (T,20), (n,16), (registers,0)]
     | ("Store_Multiple", [p,u,s,w,n,registers]) =>
          checkls
            (fn _ => is_F s andalso p ~~ NOT u andalso
                     is_0 (registers$(13,13)) andalso is_0 (registers$(15,15)))
            [(T,27), (p,24), (u,23), (w,21), (n,16), (registers,0)]
     | ("Load_Exclusive", [n,t,imm8]) =>
          [(``0b10000101w:word8``,20), (n,16), (t,12), (PC, 8), (imm8,0)]
     | ("Store_Exclusive", [n,d,t,imm8]) =>
          [(``0b10000100w:word8``,20), (n,16), (t,12), (d, 8), (imm8,0)]
     | ("Load_Exclusive_Doubleword", [n,t,t2]) =>
          [(``0b10001101w:word8``,20), (n,16), (t,12), (t2, 8),
           (``0b1111111w:word7``,0)]
     | ("Store_Exclusive_Doubleword", [n,d,t,t2]) =>
          [(``0b10001100w:word8``,20), (n,16), (t,12), (t2, 8),
           (``0b111w:word3``,4), (d,0)]
     | ("Load_Exclusive_Halfword", [n,t]) =>
          [(``0b10001101w:word8``,20), (n,16), (t,12),
           (``0b111101011111w:word12``,0)]
     | ("Store_Exclusive_Halfword", [n,d,t]) =>
          [(``0b10001100w:word8``,20), (n,16), (t,12),
           (``0b11110101w:word8``,4), (d,0)]
     | ("Load_Exclusive_Byte", [n,t]) =>
          [(``0b10001101w:word8``,20), (n,16), (t,12),
           (``0b111101001111w:word12``,0)]
     | ("Store_Exclusive_Byte", [n,d,t]) =>
          [(``0b10001100w:word8``,20), (n,16), (t,12),
           (``0b11110100w:word8``,4), (d,0)]
     | ("Store_Return_State", [p,u,w,mode]) =>
          checkls (fn _ => p ~~ NOT u)
            [(T,27), (u,24), (u,23), (w,21), (``0b110111w:word6``,14), (mode,0)]
     | ("Return_From_Exception", [p,u,w,n]) =>
          checkls (fn _ => p ~~ NOT u)
            [(T,27), (u,24), (u,23), (w,22), (T,20), (n,16),
             (``0b11w:word2``,14)]
     | _ => raise ERR "thumb2_encode_load_store"
              ("cannot encode: " ^ term_to_string tm)))
end;

fun thumb2_encode_miscellaneous tm =
let val checkmisc = check ("thumb2_encode_miscellaneous",tm) in
   term_list_to_num ((``0b111w:word3``,29)::
   (case dest_strip tm
    of ("Hint", [h]) =>
          (``0b10011101011111w:14 word``,15)::(hint h)
     | ("Data_Memory_Barrier", [opt]) =>
          [(``0b1001110111111100011110101w:25 word``,4), (opt,0)]
     | ("Data_Synchronization_Barrier", [opt]) =>
          [(``0b1001110111111100011110100w:25 word``,4), (opt,0)]
     | ("Instruction_Synchronization_Barrier", [opt]) =>
          [(``0b1001110111111100011110110w:25 word``,4), (opt,0)]
     | ("Preload_Data", [u,r,n,mode2]) =>
          if is_Mode2_immediate mode2 then
            let val imm12 = dest_Mode2_immediate mode2 in
              if is_T u orelse is_PC n then
                [(``0b11w:word2``,27), (u,23), (r,21), (T,20), (n,16),
                 (PC,12), (imm12,0)]
              else
                checkmisc (fn _ => width_okay 8 imm12)
                  [(``0b11w:word2``,27), (r,21), (T,20), (n,16),
                   (PC,12), (``0b11w:word2``,10), (imm12,0)]
            end
          else
            let val (imm5,typ,m) = dest_Mode2_register mode2 in
              checkmisc
                (fn _ => is_T u andalso is_0 typ andalso width_okay 2 imm5)
                [(``0b11w:word2``,27), (r,21), (T,20), (n,16), (PC,12),
                 (imm5,4), (m,0)]
            end
     | ("Preload_Instruction", [u,n,mode2]) =>
          if is_Mode2_immediate mode2 then
            let val imm12 = dest_Mode2_immediate mode2 in
              if is_T u orelse is_PC n then
                [(``0b11w:word2``,27), (T,24), (u,23), (T,20), (n,16),
                 (PC,12), (imm12,0)]
              else
                checkmisc (fn _ => width_okay 8 imm12)
                  [(``0b11w:word2``,27), (T,24), (T,20), (n,16),
                   (PC,12), (``0b11w:word2``,10), (imm12,0)]
            end
          else
            let val (imm5,typ,m) = dest_Mode2_register mode2 in
              checkmisc
                (fn _ => is_T u andalso is_0 typ andalso width_okay 2 imm5)
                [(``0b11w:word2``,27), (T,24), (T,20), (n,16), (PC,12),
                 (imm5,4), (m,0)]
            end
     | ("Secure_Monitor_Call", [imm4]) =>
          [(``0b101111111w:9 word``,20), (imm4,16), (T,15)]
     | ("Enterx_Leavex", [l]) =>
          [(``0b100111011111110001111000w:word24``,5), (l,4), (PC,0)]
     | ("Clear_Exclusive", []) =>
          [(``0b10011101111111000111100101111w:29 word``,0)]
     | _ => raise ERR "thumb2_encode_miscellaneous"
              ("cannot encode: " ^ term_to_string tm)))
end;

(* ------------------------------------------------------------------------- *)

fun thumbee_encode_branch tm =
let val checkbr = check ("thumbee_encode_branch", tm) in
 term_list_to_num
   (case dest_strip tm
    of ("Check_Array", [n,m]) =>
          [(``0b11001010w:word8``,8), (n$(3,3), 7), (m,3), (n$(2,0),0)]
     | ("Handler_Branch_Link", [l,h]) =>
          [(``0b1100001w:word7``,9), (l,8), (h,0)]
     | ("Handler_Branch_Link_Parameter", [imm5,h]) =>
          [(``0b110001w:word6``,10), (imm5,5), (h,0)]
     | ("Handler_Branch_Parameter", [imm3,h]) =>
          [(``0b11w:word2``,14), (imm3,5), (h,0)]
     | _ => raise ERR "thumbee_encode_branch"
              ("cannot encode: " ^ term_to_string tm))
end;

fun thumbee_encode_load_store tm = term_list_to_num
let val checkls = check ("thumbee_encode_load_store",tm) in
   (case dest_strip tm
    of ("Load", [p,u,b,w,unpriv,n,t,mode2]) =>
         checkls (fn _ => is_F unpriv)
         (if is_Mode2_immediate mode2 then
            let val imm12 = dest_Mode2_immediate mode2 in
              if is_R9 n then
                let val imm6 = imm12$(11,2) in
                  checkls
                    (fn _ => is_F b andalso is_T p andalso is_T u andalso
                             is_F w andalso is_0 (imm12$(1,0)) andalso
                             width_okay 6 imm6 andalso width_okay 3 t)
                    [(``0b110011w:word6``,10), (imm6,3), (t,0)]
                end
              else if is_R10 n then
                let val imm5 = imm12$(11,2) in
                  checkls
                    (fn _ => is_F b andalso is_T p andalso is_T u andalso
                             is_F w andalso is_0 (imm12$(1,0)) andalso
                             width_okay 5 imm5 andalso width_okay 3 t)
                    [(``0b11001011w:word8``,8), (imm5,3), (t,0)]
                end
              else
                let val imm3 = imm12$(11,2) in
                  checkls
                    (fn _ => is_F b andalso is_T p andalso is_F u andalso
                             is_F w andalso is_0 (imm12$(1,0)) andalso
                             width_okay 3 imm3 andalso
                             Lib.all (width_okay 3) [n,t])
                    [(``0b11001w:word5``,11), (imm3,6), (n,3), (t,0)]
                end
            end
          else
            let val (imm5,typ,m) = dest_Mode2_register mode2 in
              checkls
                (fn _ => is_T p andalso is_T u andalso is_F w andalso
                         is_F b andalso term_eq imm5 ``2w:word5`` andalso
                         is_0 typ andalso Lib.all (width_okay 3) [m,n,t])
                [(``0b1011w:word4``,11), (m,6), (n,3), (t,0)]
            end)
     | ("Store", [p,u,b,w,unpriv,n,t,mode2]) =>
         checkls (fn _ => is_F unpriv)
         (if is_Mode2_immediate mode2 then
            let val imm12 = dest_Mode2_immediate mode2
                val imm6 = imm12$(11,2)
            in
              checkls
                (fn _ => is_F b andalso is_T p andalso is_T u andalso
                         is_F w andalso is_0 (imm12$(1,0)) andalso
                         width_okay 6 imm6 andalso is_R9 n andalso
                         width_okay 3 t)
                [(``0b1100111w:word7``,9), (imm6,3), (t,0)]
            end
          else
            let val (imm5,typ,m) = dest_Mode2_register mode2 in
              checkls
                (fn _ => is_F b andalso is_T p andalso is_T u andalso
                         is_F w andalso term_eq imm5 ``2w:word5`` andalso
                         is_0 typ andalso Lib.all (width_okay 3) [m,n,t])
                [(``0b101w:word4``,12), (m,6), (n,3), (t,0)]
            end)
     | ("Load_Halfword", [p,u,w,s,h,unpriv,n,t,mode3]) =>
         checkls (fn _ => is_F unpriv andalso is_T p andalso is_T u andalso
                          is_F w andalso is_T h andalso
                          Lib.all (width_okay 3) [n,t] andalso
                          Lib.can dest_Mode3_register mode3)
         (let val (imm2,m) = dest_Mode3_register mode3 in
            checkls
              (fn _ => term_eq imm2 ``1w:word2`` andalso width_okay 3 m)
              [(``0b1011w:word4``,11), (s,10), (T,9), (m,6), (n,3), (t,0)]
          end)
     | ("Store_Halfword", [p,u,w,unpriv,n,t,mode3]) =>
         checkls (fn _ => is_F unpriv andalso is_T p andalso is_T u andalso
                          is_F w andalso Lib.all (width_okay 3) [n,t] andalso
                          Lib.can dest_Mode3_register mode3)
         (let val (imm2,m) = dest_Mode3_register mode3 in
            checkls
              (fn _ => term_eq imm2 ``1w:word2`` andalso width_okay 3 m)
              [(``0b101001w:word6``,9), (m,6), (n,3), (t,0)]
          end)
     | _ => raise ERR "thumbee_encode_load_store"
              ("cannot encode: " ^ term_to_string tm))
end;

(* ------------------------------------------------------------------------- *)

fun encode_instruction (enc,cond,tm) =
 (case (fst (Term.dest_const enc), dest_strip tm)
  of ("Encoding_ARM",("Branch", [i])) =>
         encode_branch (cond,i)
   | ("Encoding_ARM",("DataProcessing", [i])) =>
         encode_data_processing (cond,i)
   | ("Encoding_ARM",("StatusAccess", [i])) =>
         encode_status_access (cond,i)
   | ("Encoding_ARM",("LoadStore", [i])) =>
         encode_load_store (cond,i)
   | ("Encoding_ARM",("Miscellaneous", [i])) =>
         encode_miscellaneous (cond,i)
   | ("Encoding_ARM",("Coprocessor", [i])) =>
         encode_coprocessor (cond,i)
   | ("Encoding_ARM",("Undefined", [])) =>
         term_list_to_num [(cond,28), (``0x6000010w:word28``,0)]
   | ("Encoding_Thumb",("Branch", [i])) =>
         thumb_encode_branch (cond,i)
   | ("Encoding_Thumb",("DataProcessing", [i])) =>
         thumb_encode_data_processing i
   | ("Encoding_Thumb",("StatusAccess", [i])) =>
         thumb_encode_status_access i
   | ("Encoding_Thumb",("LoadStore", [i])) =>
         thumb_encode_load_store i
   | ("Encoding_Thumb",("Miscellaneous", [i])) =>
         thumb_encode_miscellaneous i
   | ("Encoding_Thumb",("Undefined", [])) =>
         term_list_to_num [(``0b1101111w:word7``,9)]
   | ("Encoding_Thumb2",("Branch", [i])) =>
         thumb2_encode_branch (cond,i)
   | ("Encoding_Thumb2",("DataProcessing", [i])) =>
         thumb2_encode_data_processing i
   | ("Encoding_Thumb2",("StatusAccess", [i])) =>
         thumb2_encode_status_access i
   | ("Encoding_Thumb2",("LoadStore", [i])) =>
         thumb2_encode_load_store i
   | ("Encoding_Thumb2",("Miscellaneous", [i])) =>
         thumb2_encode_miscellaneous i
   | ("Encoding_Thumb2",("Coprocessor", [i])) =>
         encode_coprocessor
           (mk_word4 (if is_var cond orelse is_PC cond then 15 else 14),i)
   | ("Encoding_Thumb2",("Undefined", [])) =>
         term_list_to_num [(``0b1111011111110000101w:19 word``,13)]
   | ("Encoding_ThumbEE",("Branch", [i])) =>
         thumbee_encode_branch i
   | ("Encoding_ThumbEE",("LoadStore", [i])) =>
         thumbee_encode_load_store i
   | ("Encoding_ThumbEE",("Undefined", [])) =>
         term_list_to_num [(``0b1101111w:word7``,9)]
   | _ => raise ERR "encode_instruction" ("cannot encode: " ^
            term_to_string (pairSyntax.mk_pair (enc,tm))))
     |> Arbnum.toHexString
     |> (if enc ~~ Encoding_Thumb_tm orelse enc ~~ Encoding_ThumbEE_tm then
           pad 4
         else if enc ~~ Encoding_ARM_tm then
           pad 8
         else
           (fn s => String.concat [String.substring (s, 0, 4), " ",
                                   String.substring (s, 4, 4)]));

(* ------------------------------------------------------------------------- *)

fun arm_encode (arm_parserLib.Ascii s)       = encode_ascii s
  | arm_encode (arm_parserLib.Byte l)        = encode_byte l
  | arm_encode (arm_parserLib.Short l)       = encode_short l
  | arm_encode (arm_parserLib.Word l)        = encode_word l
  | arm_encode (arm_parserLib.Instruction i) = encode_instruction i;

val arm_assemble_parse = List.map ((I:Arbnum.num -> Arbnum.num) ## arm_encode);

val arm_assemble_from_quote =
  (arm_assemble_parse ## I) o arm_parserLib.arm_parse_from_quote;

val arm_assemble_from_string =
  (arm_assemble_parse ## I) o arm_parserLib.arm_parse_from_string;

val arm_assemble_from_file =
  (arm_assemble_parse ## I) o arm_parserLib.arm_parse_from_file;

fun arm_encode_from_string s =
  case Lib.total arm_assemble_from_string s
  of SOME ([(_,opc)],_) => opc
   | _ => raise ERR "arm_encode_from_string" "could not encode assembler";

(*
fun print_code_from s =
let open Arbnum
    val start = fromHexString s
    val lower = String.map Char.toLower
    val count = StringCvt.padLeft #" " 8 o pad 4 o lower o toHexString
in
  app (fn (n,i) => print (count (start + n) ^ " " ^ i ^ "\n"))
end;
*)

end
