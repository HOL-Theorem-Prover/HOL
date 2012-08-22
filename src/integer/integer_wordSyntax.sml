structure integer_wordSyntax :> integer_wordSyntax =
struct

open HolKernel boolLib
open wordsSyntax integer_wordTheory

val ERR = Feedback.mk_HOL_ERR "integer_wordSyntax"

val syntax_fns = HolKernel.syntax_fns

(*------------------------------------------------------------------------- *)

val s = syntax_fns "integer_word" 1 HolKernel.dest_monop HolKernel.mk_monop

val (toString_tm, mk_toString, dest_toString, is_toString) = s "toString"

val (fromString_tm, mk_fromString, dest_fromString, is_fromString) =
    s "fromString"

val (w2i_tm, mk_w2i, dest_w2i, is_w2i) = s "w2i"

(* - - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns "integer_word" 1
   (fn tm1 => fn e => boolSyntax.dest_itself o HolKernel.dest_monop tm1 e)
   (fn tm => fn ty =>
      Term.mk_comb (Term.inst [Type.alpha |-> ty] tm, boolSyntax.mk_itself ty))

val (int_min_tm, mk_int_min, dest_int_min, is_int_min) = s "INT_MIN"
val (int_max_tm, mk_int_max, dest_int_max, is_int_max) = s "INT_MAX"
val (uint_max_tm, mk_uint_max, dest_uint_max, is_uint_max) = s "UINT_MAX"

(* - - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns "integer_word" 1
   (fn tm1 => fn e => fn w => (HolKernel.dest_monop tm1 e w, dim_of w))
   (fn tm => fn (w, ty) => Term.mk_comb (Term.inst [Type.alpha |-> ty] tm, w))

val (i2w_tm, mk_i2w, dest_i2w, is_i2w) = s "i2w"

val (saturate_i2sw_tm, mk_saturate_i2sw,
     dest_saturate_i2sw, is_saturate_i2sw) = s "saturate_i2sw"

val (saturate_i2w_tm, mk_saturate_i2w, dest_saturate_i2w, is_saturate_i2w) =
    s "saturate_i2w"

(* - - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns "integer_word" 1
   (fn tm1 => fn e => fn w => (HolKernel.dest_monop tm1 e w, dim_of w))
   (fn tm => fn (w, ty) =>
       Term.mk_comb (Term.inst [Type.alpha |-> wordsSyntax.dim_of w,
                                Type.beta |-> ty] tm, w))

val (saturate_sw2sw_tm, mk_saturate_sw2sw,
     dest_saturate_sw2sw, is_saturate_sw2sw) = s "saturate_sw2sw"

val (saturate_sw2w_tm, mk_saturate_sw2w,
     dest_saturate_sw2w, is_saturate_sw2w) = s "saturate_sw2w"

val (saturate_w2sw_tm, mk_saturate_w2sw,
     dest_saturate_w2sw, is_saturate_w2sw) = s "saturate_w2sw"

(* - - - - - - - - - - - - - - - - - - - - - - - *)

val s = syntax_fns "integer_word" 2 HolKernel.dest_binop HolKernel.mk_binop

val (signed_saturate_add_tm, mk_signed_saturate_add,
     dest_signed_saturate_add, is_signed_saturate_add) = s "signed_saturate_add"

val (signed_saturate_sub_tm, mk_signed_saturate_sub,
     dest_signed_saturate_sub, is_signed_saturate_sub) = s "signed_saturate_sub"

(*------------------------------------------------------------------------- *)

end
