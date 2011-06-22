structure integer_wordSyntax :> integer_wordSyntax =
struct

open HolKernel boolLib;
open wordsSyntax integer_wordTheory;

val ERR = Feedback.mk_HOL_ERR "integer_wordSyntax";

(*---------------------------------------------------------------------------
  Terms
  ---------------------------------------------------------------------------*)

fun mk_integer_word_const s =
   Term.prim_mk_const {Name = s, Thy = "integer_word"};

val w2i_tm = mk_integer_word_const "w2i";
val i2w_tm = mk_integer_word_const "i2w";

val int_min_tm  = mk_integer_word_const "INT_MIN";
val int_max_tm  = mk_integer_word_const "INT_MAX";
val uint_max_tm = mk_integer_word_const "UINT_MAX";

val saturate_i2sw_tm  = mk_integer_word_const "saturate_i2sw";
val saturate_i2w_tm   = mk_integer_word_const "saturate_i2w";
val saturate_sw2sw_tm = mk_integer_word_const "saturate_sw2sw";
val saturate_sw2w_tm  = mk_integer_word_const "saturate_sw2w";
val saturate_w2sw_tm  = mk_integer_word_const "saturate_w2sw";
val signed_saturate_add_tm = mk_integer_word_const "signed_saturate_add";
val signed_saturate_sub_tm = mk_integer_word_const "signed_saturate_sub";

(*---------------------------------------------------------------------------
  Constructors
  ---------------------------------------------------------------------------*)

fun mk_w2i w =
  Term.mk_comb (Term.inst [Type.alpha |-> wordsSyntax.dim_of w] w2i_tm, w)
  handle HOL_ERR _ => raise ERR "mk_word_w2i" "";

fun mk_i2w (n, ty) =
  Term.mk_comb (Term.inst [Type.alpha |-> ty] i2w_tm, n)
  handle HOL_ERR _ => raise ERR "mk_word_i2w" "";

fun mk_uint_max ty =
  Term.mk_comb
    (Term.inst [Type.alpha |-> ty] uint_max_tm,
     boolSyntax.mk_itself ty)
  handle HOL_ERR _ => raise ERR "mk_uint_max" "";

fun mk_int_min ty =
  Term.mk_comb
    (Term.inst [Type.alpha |-> ty] int_min_tm,
     boolSyntax.mk_itself ty)
  handle HOL_ERR _ => raise ERR "mk_int_min" "";

fun mk_int_max ty =
  Term.mk_comb
    (Term.inst [Type.alpha |-> ty] int_max_tm,
     boolSyntax.mk_itself ty)
  handle HOL_ERR _ => raise ERR "mk_int_max" "";

fun mk_saturate_i2sw (n, ty) =
  Term.mk_comb (Term.inst [Type.alpha |-> ty] saturate_i2sw_tm, n)
  handle HOL_ERR _ => raise ERR "mk_saturate_i2sw" "";

fun mk_saturate_i2w (n, ty) =
  Term.mk_comb (Term.inst [Type.alpha |-> ty] saturate_i2w_tm, n)
  handle HOL_ERR _ => raise ERR "mk_saturate_i2w" "";

fun mk_saturate_sw2sw (w, ty) =
  Term.mk_comb
    (Term.inst
       [Type.alpha |-> wordsSyntax.dim_of w, Type.beta |-> ty]
       saturate_sw2sw_tm, w)
  handle HOL_ERR _ => raise ERR "mk_saturate_sw2sw" "";

fun mk_saturate_sw2w (w, ty) =
  Term.mk_comb
    (Term.inst
       [Type.alpha |-> wordsSyntax.dim_of w, Type.beta |-> ty]
       saturate_sw2w_tm, w)
  handle HOL_ERR _ => raise ERR "mk_saturate_sw2w" "";

fun mk_saturate_w2sw (w, ty) =
  Term.mk_comb
    (Term.inst
       [Type.alpha |-> wordsSyntax.dim_of w, Type.beta |-> ty]
       saturate_w2sw_tm, w)
  handle HOL_ERR _ => raise ERR "mk_saturate_w2sw" "";

fun mk_signed_saturate_add (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] signed_saturate_add_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_signed_saturate_add" "";

fun mk_signed_saturate_sub (w1, w2) =
  list_mk_comb (inst [alpha |-> dim_of w1] signed_saturate_sub_tm, [w1, w2])
  handle HOL_ERR _ => raise ERR "mk_signed_saturate_sub" "";

(*---------------------------------------------------------------------------
  Destructorss
  ---------------------------------------------------------------------------*)

val dest_i2w = HolKernel.dest_monop i2w_tm (ERR "dest_i2w" "");
val dest_w2i = HolKernel.dest_monop w2i_tm (ERR "dest_i2w" "");

val dest_uint_max =
  boolSyntax.dest_itself o
  HolKernel.dest_monop uint_max_tm (ERR "dest_uint_max" "");

val dest_int_min =
  boolSyntax.dest_itself o
  HolKernel.dest_monop int_min_tm (ERR "dest_int_min" "");

val dest_int_max =
  boolSyntax.dest_itself o
  HolKernel.dest_monop int_max_tm (ERR "dest_int_max" "");

fun dest_saturate_i2sw M =
  (dest_monop saturate_i2sw_tm (ERR "dest_saturate_i2sw" "") M,
   wordsSyntax.dim_of M);

fun dest_saturate_i2w M =
  (dest_monop saturate_i2w_tm (ERR "dest_saturate_i2w" "") M,
   wordsSyntax.dim_of M);

fun dest_saturate_sw2sw M =
  (dest_monop saturate_sw2sw_tm (ERR "dest_saturate_sw2sw" "") M,
   wordsSyntax.dim_of M);

fun dest_saturate_sw2w M =
  (dest_monop saturate_sw2w_tm (ERR "dest_saturate_sw2s" "") M,
   wordsSyntax.dim_of M);

fun dest_saturate_w2sw M =
  (dest_monop saturate_w2sw_tm (ERR "dest_saturate_w2sw" "") M,
   wordsSyntax.dim_of M);

val dest_signed_saturate_add =
  dest_binop signed_saturate_add_tm (ERR "dest_signed_saturate_add" "");

val dest_signed_saturate_sub =
  dest_binop signed_saturate_sub_tm (ERR "dest_signed_saturate_sub" "");

(*---------------------------------------------------------------------------
  Discriminators
  ---------------------------------------------------------------------------*)

val is_i2w = Lib.can dest_i2w;
val is_w2i = Lib.can dest_w2i;

val is_uint_max = Lib.can dest_uint_max;
val is_int_min  = Lib.can dest_int_min;
val is_int_max  = Lib.can dest_int_max;

val is_saturate_i2sw  = Lib.can dest_saturate_i2sw;
val is_saturate_i2w   = Lib.can dest_saturate_i2w;
val is_saturate_sw2sw = Lib.can dest_saturate_sw2sw;
val is_saturate_sw2w  = Lib.can dest_saturate_sw2w;
val is_saturate_w2sw  = Lib.can dest_saturate_w2sw;

val is_signed_saturate_add = Lib.can dest_signed_saturate_add
val is_signed_saturate_sub = Lib.can dest_signed_saturate_sub

end
