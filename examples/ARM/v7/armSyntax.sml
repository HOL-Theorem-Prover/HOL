structure armSyntax :> armSyntax =
struct

open Abbrev HolKernel arm_seq_monadTheory arm_decoderTheory;

val ERR = Feedback.mk_HOL_ERR "armSyntax";

fun dest_strip t =
let val (l,r) = strip_comb t in
  (fst (dest_const l), r)
end;

local
  val arm_state_type = ``:arm_state``;
  val err = ERR "dest_monad_type" "not an instance of 'a M"
in
  fun dest_monad_type ty =
  let val (tya,tyb) = dom_rng ty in
     if tya = arm_state_type then
       case total dest_thy_type tyb of
         SOME {Tyop = "error_option", Thy = "arm_seq_monad",
               Args = [tyc, tyd]} =>
           (if tyd = arm_state_type then tyc else raise err)
       | _ => raise err
     else
       raise err
  end handle HOL_ERR _ => raise err
end;

fun inst_word_alpha ty tm =
  inst [alpha |->
   (if wordsSyntax.is_word_type (type_of tm) then
      ty
    else
      wordsSyntax.mk_word_type ty)] tm;

fun mk_monad_const s  = prim_mk_const{Name = s, Thy = "arm_seq_monad"}
fun mk_core_const s   = prim_mk_const{Name = s, Thy = "arm_coretypes"}
fun mk_decode_const s = prim_mk_const{Name = s, Thy = "arm_decoder"};

val error_tm      = mk_monad_const "Error"
val valuestate_tm = mk_monad_const "ValueState"

val constT_tm = mk_monad_const "constT"
val seqT_tm   = mk_monad_const "seqT"
val parT_tm   = mk_monad_const "parT"
val forT_tm   = mk_monad_const "forT"
val readT_tm  = mk_monad_const "readT"
val writeT_tm = mk_monad_const "writeT"

val read__reg_tm  = mk_monad_const "read__reg"
val write__reg_tm = mk_monad_const "write__reg"
val read__psr_tm  = mk_monad_const "read__psr"
val write__psr_tm = mk_monad_const "write__psr"

val read_reg_mode_tm  = mk_monad_const "read_reg_mode"
val write_reg_mode_tm = mk_monad_const "write_reg_mode"
val read_reg_tm       = mk_monad_const "read_reg"
val write_reg_tm      = mk_monad_const "write_reg"
val read_cpsr_tm      = mk_monad_const "read_cpsr"
val write_cpsr_tm     = mk_monad_const "write_cpsr"
val read_spsr_tm      = mk_monad_const "read_spsr"
val write_spsr_tm     = mk_monad_const "write_spsr"
val read_memA_tm      = mk_monad_const "read_memA"
val write_memA_tm     = mk_monad_const "write_memA"

val clear_event_register_tm     = mk_monad_const "clear_event_register"
val send_event_tm               = mk_monad_const "send_event"
val wait_for_interrupt_tm       = mk_monad_const "wait_for_interrupt"
val clear_wait_for_interrupt_tm = mk_monad_const "clear_wait_for_interrupt"

val decode_psr_tm      = mk_core_const "decode_psr"
val bytes_tm           = mk_core_const "bytes"
val align_tm           = mk_core_const "align"
val aligned_tm         = mk_core_const "aligned"
val bit_count_tm       = mk_core_const "bit_count"
val Encoding_ARM_tm    = mk_core_const "Encoding_ARM"
val Encoding_Thumb_tm  = mk_core_const "Encoding_Thumb"
val Encoding_Thumb2_tm = mk_core_const "Encoding_Thumb2"
val ITAdvance_tm       = mk_core_const "ITAdvance"

val arm_decode_tm      = mk_decode_const "arm_decode"
val thumb_decode_tm    = mk_decode_const "thumb_decode"
val thumb2_decode_tm   = mk_decode_const "thumb2_decode";

fun mk_error s =
  mk_comb(error_tm, inst [alpha |-> stringSyntax.string_ty] s)
  handle HOL_ERR _ => raise ERR "mk_error" "";

fun mk_valuestate (v,s) =
  list_mk_comb(inst
    [alpha |-> type_of v, beta |-> type_of s] valuestate_tm, [v,s])
  handle HOL_ERR _ => raise ERR "mk_valuestate" "";

fun mk_constT t =
  mk_comb(inst[alpha |-> type_of t] constT_tm,t)
  handle HOL_ERR _ => raise ERR "mk_constT" "";

fun mk_seqT (f,g) =
  list_mk_comb(inst
    [alpha |-> dest_monad_type (type_of f),
     beta  |-> (dest_monad_type o snd o dom_rng o type_of) g] seqT_tm,[f,g])
  handle HOL_ERR _ => raise ERR "mk_seqT" "";

fun mk_parT (f,g) =
  list_mk_comb(inst
    [alpha |-> dest_monad_type (type_of f),
     beta  |-> dest_monad_type (type_of g)] parT_tm,[f,g])
  handle HOL_ERR _ => raise ERR "mk_parT" "";

fun mk_forT (l,h,f) =
  list_mk_comb(inst[alpha |-> (dest_monad_type o snd o dom_rng o type_of) f]
    forT_tm,[l,h,f])
  handle HOL_ERR _ => raise ERR "mk_forT" "";

fun mk_readT f =
  mk_comb(inst [alpha |-> snd (dom_rng (type_of f))] readT_tm, f)
  handle HOL_ERR _ => raise ERR "mk_readT" "";

fun mk_writeT f =
  mk_comb(writeT_tm, f)
  handle HOL_ERR _ => raise ERR "mk_writeT" "";

fun mk_read__reg (ii,r) =
  list_mk_comb(read__reg_tm,
    [inst [alpha |-> ``:iiid``] ii,
     inst [alpha |-> ``:RName``] r])
  handle HOL_ERR _ => raise ERR "mk_read__reg" "";

fun mk_write__reg (ii,r,v) =
  list_mk_comb(write__reg_tm,
    [inst [alpha |-> ``:iiid``] ii,
     inst [alpha |-> ``:RName``] r,
     inst_word_alpha ``:32`` v])
  handle HOL_ERR _ => raise ERR "mk_write__reg" "";

fun mk_read__psr (ii,r) =
  list_mk_comb(read__psr_tm,
    [inst [alpha |-> ``:iiid``] ii,
     inst [alpha |-> ``:PSRName``] r])
  handle HOL_ERR _ => raise ERR "mk_read__psr" "";

fun mk_write__psr (ii,r,v) =
  list_mk_comb(write__psr_tm,
    [inst [alpha |-> ``:iiid``] ii,
     inst [alpha |-> ``:PSRName``] r,
     inst [alpha |-> ``:ARMpsr``] v])
  handle HOL_ERR _ => raise ERR "mk_write__psr" "";

fun mk_read_reg (ii,n) =
  list_mk_comb(read_reg_tm,
    [inst [alpha |-> ``:iiid``] ii,
     inst_word_alpha ``:4`` n])
  handle HOL_ERR _ => raise ERR "mk_read_reg" "";

fun mk_write_reg (ii,n,v) =
  list_mk_comb(write_reg_tm,
    [inst [alpha |-> ``:iiid``] ii,
     inst_word_alpha ``:4`` n,
     inst_word_alpha ``:32`` v])
  handle HOL_ERR _ => raise ERR "mk_write_reg" "";

fun mk_read_reg_mode (ii,n,m) =
  list_mk_comb(read_reg_mode_tm,
    [inst [alpha |-> ``:iiid``] ii,
     pairSyntax.mk_pair
       (inst_word_alpha ``:4`` n, inst_word_alpha ``:5`` m)])
  handle HOL_ERR _ => raise ERR "mk_read_reg_mode" "";

fun mk_write_reg_mode (ii,n,m,v) =
  list_mk_comb(write_reg_mode_tm,
    [inst [alpha |-> ``:iiid``] ii,
     pairSyntax.mk_pair
       (inst_word_alpha ``:4`` n, inst_word_alpha ``:5`` m),
     inst_word_alpha ``:32`` v])
  handle HOL_ERR _ => raise ERR "mk_write_reg_mode" "";

fun mk_read_cpsr ii =
  mk_comb(read_cpsr_tm, inst [alpha |-> ``:iiid``] ii)
  handle HOL_ERR _ => raise ERR "mk_read_cpsr" "";

fun mk_write_cpsr (ii,v) =
  list_mk_comb(write_cpsr_tm,
    [inst [alpha |-> ``:iiid``] ii,
     inst [alpha |-> ``:ARMpsr``] v])
  handle HOL_ERR _ => raise ERR "mk_write_cpsr" "";

fun mk_read_spsr ii =
  mk_comb(read_spsr_tm, inst [alpha |-> ``:iiid``] ii)
  handle HOL_ERR _ => raise ERR "mk_read_spsr" "";

fun mk_write_spsr (ii,v) =
  list_mk_comb(write_spsr_tm,
    [inst [alpha |-> ``:iiid``] ii,
     inst [alpha |-> ``:ARMpsr``] v])
  handle HOL_ERR _ => raise ERR "mk_write_spsr" "";

fun mk_read_memA (ii,a,s) =
  list_mk_comb(read_memA_tm,
    [inst [alpha |-> ``:iiid``] ii,
     pairSyntax.mk_pair
       (inst_word_alpha ``:32`` a,
        inst [alpha |-> ``:num``] s)])
  handle HOL_ERR _ => raise ERR "mk_read_memA" "";

fun mk_write_memA (ii,a,s,v) =
  list_mk_comb(write_memA_tm,
    [inst [alpha |-> ``:iiid``] ii,
     pairSyntax.mk_pair
       (inst_word_alpha ``:32`` a,
        inst [alpha |-> ``:num``] s),
     v])
  handle HOL_ERR _ => raise ERR "mk_write_memA" "";

fun mk_clear_event_register ii =
  mk_comb(clear_event_register_tm, inst [alpha |-> ``:iiid``] ii)
  handle HOL_ERR _ => raise ERR "mk_clear_event_register" "";

fun mk_send_event ii =
  mk_comb(send_event_tm, inst [alpha |-> ``:iiid``] ii)
  handle HOL_ERR _ => raise ERR "mk_send_event" "";

fun mk_wait_for_interrupt ii =
  mk_comb(wait_for_interrupt_tm, inst [alpha |-> ``:iiid``] ii)
  handle HOL_ERR _ => raise ERR "mk_wait_for_interrupt" "";

fun mk_clear_wait_for_interrupt ii =
  mk_comb(clear_wait_for_interrupt_tm, inst [alpha |-> ``:iiid``] ii)
  handle HOL_ERR _ => raise ERR "mk_clear_wait_for_interrupt" "";

fun mk_decode_psr w =
  mk_comb(decode_psr_tm, inst_word_alpha ``:32`` w)
  handle HOL_ERR _ => raise ERR "mk_decode_psr" "";

fun mk_bytes (w,n) =
  mk_comb(bytes_tm, pairSyntax.mk_pair(inst_word_alpha ``:32`` w, n))
  handle HOL_ERR _ => raise ERR "mk_bytes" "";

fun mk_align (w,n) =
  mk_comb(inst [alpha |-> wordsSyntax.dest_word_type (type_of w)] align_tm,
    pairSyntax.mk_pair(w, n))
  handle HOL_ERR _ => raise ERR "mk_align" "";

fun mk_aligned (w,n) =
  mk_comb(inst [alpha |-> wordsSyntax.dest_word_type (type_of w)] aligned_tm,
    pairSyntax.mk_pair(w, n))
  handle HOL_ERR _ => raise ERR "mk_aligned" "";

fun mk_bit_count w =
  mk_comb(
   inst [alpha |-> wordsSyntax.dest_word_type (type_of w)] bit_count_tm, w)
  handle HOL_ERR _ => raise ERR "mk_bit_count" "";

fun mk_ITAdvance w =
  mk_comb(
   inst [alpha |-> wordsSyntax.dest_word_type (type_of w)] ITAdvance_tm, w)
  handle HOL_ERR _ => raise ERR "mk_ITAdvance" "";

fun mk_read_memA_1 (ii,a) = mk_read_memA (ii,a,``1n``);

fun mk_write_memA_1 (ii,a,v) =
   mk_write_memA (ii,a,``1n``,listSyntax.mk_list([v],``:word8``));

fun mk_read_memA_2 (ii,a) = mk_read_memA (ii,a,``2n``);
fun mk_write_memA_2 (ii,a,v) = mk_write_memA (ii,a,``2n``,mk_bytes(v,``2n``));
fun mk_read_memA_4 (ii,a) = mk_read_memA (ii,a,``4n``);
fun mk_write_memA_4 (ii,a,v) = mk_write_memA (ii,a,``4n``,mk_bytes(v,``4n``));

fun mk_arm_decode(b,w) =
  list_mk_comb(arm_decode_tm, [b,inst_word_alpha ``:32`` w])
  handle HOL_ERR _ => raise ERR "mk_arm_decode" "";

fun mk_thumb_decode(a,itstate,w) =
  list_mk_comb(thumb_decode_tm,
    [a,inst_word_alpha ``:8`` itstate, inst_word_alpha ``:16`` w])
  handle HOL_ERR _ => raise ERR "mk_thumb_decode" "";

fun mk_thumb2_decode(itstate,w1,w2) =
  list_mk_comb(thumb2_decode_tm,
    [inst_word_alpha ``:8`` itstate,
     pairSyntax.mk_pair
       (inst_word_alpha ``:16`` w1,
        inst_word_alpha ``:16`` w2)])
  handle HOL_ERR _ => raise ERR "mk_thumb2_decode" "";

val dest_error      = dest_monop error_tm (ERR "dest_error" "")
val dest_valuestate = dest_binop valuestate_tm (ERR "dest_valuestate" "")

val dest_constT = dest_monop constT_tm (ERR "dest_constT" "")
val dest_seqT   = dest_binop seqT_tm   (ERR "dest_seqT" "")
val dest_parT   = dest_binop parT_tm   (ERR "dest_parT" "")
val dest_forT   = dest_triop forT_tm   (ERR "dest_forT" "")
val dest_readT  = dest_monop readT_tm  (ERR "dest_readT" "")
val dest_writeT = dest_monop writeT_tm (ERR "dest_writeT" "")

val dest_read__reg =
  dest_binop read__reg_tm  (ERR "dest_read__reg" "")

val dest_write__reg =
  dest_triop write__reg_tm (ERR "dest_write__reg" "")

val dest_read__psr =
  dest_binop read__psr_tm  (ERR "dest_read__psr" "")

val dest_write__psr =
  dest_triop write__psr_tm (ERR "dest_write__psr" "")

val dest_read_reg_mode =
  dest_binop read_reg_mode_tm  (ERR "dest_read_reg_mode" "")

val dest_write_reg_mode =
  dest_triop write_reg_mode_tm (ERR "dest_write_reg_mode" "")

val dest_read_reg   = dest_binop read_reg_tm   (ERR "dest_read_reg" "")
val dest_write_reg  = dest_triop write_reg_tm  (ERR "dest_write_reg" "")
val dest_read_cpsr  = dest_monop read_cpsr_tm  (ERR "dest_read_cpsr" "")
val dest_write_cpsr = dest_binop write_cpsr_tm (ERR "dest_write_cpsr" "")
val dest_read_spsr  = dest_monop read_spsr_tm  (ERR "dest_read_spsr" "")
val dest_write_spsr = dest_binop write_spsr_tm (ERR "dest_write_spsr" "")
val dest_read_memA  = dest_binop read_memA_tm  (ERR "dest_read_memA" "")
val dest_write_memA = dest_triop write_memA_tm (ERR "dest_write_memA" "")
val dest_decode_psr = dest_monop decode_psr_tm (ERR "dest_decode_psr" "")
val dest_bytes      = dest_monop bytes_tm      (ERR "dest_bytes" "");
val dest_align      = dest_monop align_tm      (ERR "dest_align" "");
val dest_aligned    = dest_monop aligned_tm    (ERR "dest_align" "");
val dest_bit_count  = dest_monop bit_count_tm  (ERR "dest_bit_count" "");
val dest_ITAdvance  = dest_monop ITAdvance_tm  (ERR "dest_ITAdvance" "");

val dest_clear_event_register =
    dest_monop decode_psr_tm (ERR "dest_clear_event_register" "");

val dest_send_event =
    dest_monop send_event_tm (ERR "dest_send_event" "");

val dest_wait_for_interrupt =
    dest_monop wait_for_interrupt_tm (ERR "dest_wait_for_interrupt" "");

val dest_clear_wait_for_interrupt =
    dest_monop clear_wait_for_interrupt_tm
    (ERR "dest_clear_wait_for_interrupt" "");

val dest_arm_decode =
    dest_binop arm_decode_tm (ERR "dest_arm_decode" "");

val dest_thumb_decode =
    dest_triop thumb_decode_tm (ERR "dest_thumb_decode" "");

val dest_thumb2_decode =
    dest_binop thumb2_decode_tm (ERR "dest_thumb2_decode" "");

val is_error      = can dest_error
val is_valuestate = can dest_valuestate

val is_constT = can dest_constT
val is_seqT   = can dest_seqT
val is_parT   = can dest_parT
val is_forT   = can dest_forT
val is_readT  = can dest_readT
val is_writeT = can dest_writeT

val is_read__reg      = can dest_read__reg
val is_write__reg     = can dest_write__reg
val is_read__psr      = can dest_read__psr
val is_write__psr     = can dest_write__psr
val is_read_reg_mode  = can dest_read_reg_mode
val is_write_reg_mode = can dest_write_reg_mode
val is_read_reg       = can dest_read_reg
val is_write_reg      = can dest_write_reg
val is_read_cpsr      = can dest_read_cpsr
val is_write_cpsr     = can dest_write_cpsr
val is_read_spsr      = can dest_read_spsr
val is_write_spsr     = can dest_write_spsr
val is_read_memA      = can dest_read_memA
val is_write_memA     = can dest_write_memA
val is_decode_psr     = can dest_decode_psr
val is_bytes          = can dest_bytes
val is_align          = can dest_align
val is_aligned        = can dest_aligned
val is_bit_count      = can dest_bit_count
val is_ITAdvance      = can dest_ITAdvance

val is_clear_event_register     = can dest_clear_event_register
val is_send_event               = can dest_send_event
val is_wait_for_interrupt       = can dest_wait_for_interrupt
val is_clear_wait_for_interrupt = can dest_clear_wait_for_interrupt;

val is_arm_decode    = can dest_arm_decode
val is_thumb_decode  = can dest_thumb_decode
val is_thumb2_decode = can dest_thumb2_decode;

end
