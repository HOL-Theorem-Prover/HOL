structure integer_wordSyntax :> integer_wordSyntax =
struct

open HolKernel boolLib;
open integer_wordTheory;

val ERR = mk_HOL_ERR "integer_wordSyntax";

fun mk_integer_word_const s =  prim_mk_const{Name = s, Thy = "integer_word"};

val w2i_tm = mk_integer_word_const "w2i";
val i2w_tm = mk_integer_word_const "i2w";

fun mk_w2i w =
  mk_comb (inst[alpha |-> wordsSyntax.dim_of w] w2i_tm,w)
  handle HOL_ERR _ => raise ERR "mk_word_w2i" "";

fun mk_i2w (n,ty) =
  mk_comb (inst[alpha |-> ty] i2w_tm,n)
  handle HOL_ERR _ => raise ERR "mk_word_i2w" "";

val dest_i2w = dest_monop i2w_tm (ERR "dest_i2w" "");
val dest_w2i = dest_monop w2i_tm (ERR "dest_i2w" "");

val is_i2w = Lib.can dest_i2w;
val is_w2i = Lib.can dest_w2i;

end
