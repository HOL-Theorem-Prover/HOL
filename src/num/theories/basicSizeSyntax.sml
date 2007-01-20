structure basicSizeSyntax :> basicSizeSyntax =
struct

open HolKernel boolLib Abbrev basicSizeTheory;

val ERR = mk_HOL_ERR "basicSizeSyntax";

val bool_size_tm = prim_mk_const {Thy = "basicSize", Name = "bool_size"};
val pair_size_tm = prim_mk_const {Thy = "basicSize", Name = "pair_size"};
val sum_size_tm = prim_mk_const {Thy = "basicSize", Name = "sum_size"};
val one_size_tm = prim_mk_const {Thy = "basicSize", Name = "one_size"};
val option_size_tm = prim_mk_const {Thy = "basicSize", Name = "option_size"};

fun dom tm = fst(dom_rng(type_of tm));

fun mk_bool_size tm = mk_comb(bool_size_tm,tm);
fun mk_one_size tm = mk_comb(one_size_tm,tm);
fun mk_pair_size (f,g,p) = 
 list_mk_comb(inst[alpha |-> dom f, beta |-> dom g] pair_size_tm,[f,g,p]);
fun mk_sum_size (f,g,s) = 
 list_mk_comb(inst[alpha |-> dom f, beta |-> dom g] sum_size_tm,[f,g,s]);
fun mk_option_size (f,tm) = 
 list_mk_comb(inst [alpha |-> dom f]option_size_tm,[f,tm]);

val dest_bool_size = dest_monop bool_size_tm  (ERR "dest_bool_size" "");
val dest_one_size = dest_monop one_size_tm    (ERR "dest_one_size" "");
val dest_pair_size = dest_triop pair_size_tm  (ERR "dest_pair_size" "");
val dest_sum_size = dest_triop pair_size_tm   (ERR "dest_sum_size" "");
val dest_option_size = dest_binop option_size_tm (ERR "dest_option_size" "");

val is_bool_size = can dest_bool_size;
val is_pair_size = can dest_pair_size;
val is_sum_size = can dest_sum_size;
val is_one_size = can dest_one_size;
val is_option_size = can dest_option_size;

end
