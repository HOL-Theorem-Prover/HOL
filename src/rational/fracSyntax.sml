structure fracSyntax :> fracSyntax =
struct

open HolKernel boolLib Parse;

(* interactive mode
app load ["fracTheory"];
*)

open fracTheory;


val ERR = mk_HOL_ERR "fracSyntax";

(*--------------------------------------------------------------------------*
 * constants
 *--------------------------------------------------------------------------*)

val int_ty = intSyntax.int_ty;
val frac = mk_thy_type{Tyop = "frac", Thy="frac", Args = []};

val frac_0_tm = prim_mk_const {Name="frac_0",Thy="frac"};
val frac_1_tm = prim_mk_const {Name="frac_1",Thy="frac"};

val frac_nmr_tm = prim_mk_const {Name="frac_nmr",Thy="frac"};
val frac_dnm_tm = prim_mk_const {Name="frac_dnm",Thy="frac"};
val frac_sgn_tm = prim_mk_const {Name="frac_sgn",Thy="frac"};

val frac_ainv_tm = prim_mk_const {Name="frac_ainv",Thy="frac"};
val frac_minv_tm = prim_mk_const {Name="frac_minv",Thy="frac"};

val frac_add_tm = prim_mk_const {Name="frac_add",Thy="frac"};
val frac_sub_tm = prim_mk_const {Name="frac_sub",Thy="frac"};
val frac_mul_tm = prim_mk_const {Name="frac_mul",Thy="frac"};
val frac_div_tm = prim_mk_const {Name="frac_div",Thy="frac"};

val frac_save_tm = prim_mk_const {Name="frac_save",Thy="frac"};

(*--------------------------------------------------------------------------*
 * constructors
 *--------------------------------------------------------------------------*)

fun mk_monop c tm = mk_comb(c,tm);
fun mk_binop c (tm1,tm2) = mk_comb(mk_comb(c,tm1),tm2);

val mk_frac_nmr = mk_monop frac_nmr_tm;
val mk_frac_dnm = mk_monop frac_dnm_tm;
val mk_frac_sgn = mk_monop frac_sgn_tm;

val mk_frac_ainv = mk_monop frac_ainv_tm;
val mk_frac_minv = mk_monop frac_minv_tm;

val mk_frac_add = mk_binop frac_add_tm;
val mk_frac_sub = mk_binop frac_sub_tm;
val mk_frac_mul = mk_binop frac_mul_tm;
val mk_frac_div = mk_binop frac_div_tm;

val mk_frac_save = mk_binop frac_save_tm;

(*--------------------------------------------------------------------------*
 * destructors
 *--------------------------------------------------------------------------*)

val dest_frac_nmr = dest_monop frac_nmr_tm (ERR "dest_frac_nmr" "");
val dest_frac_dnm = dest_monop frac_dnm_tm (ERR "dest_frac_dnm" "");
val dest_frac_sgn = dest_monop frac_sgn_tm (ERR "dest_frac_sgn" "");

val dest_frac_ainv = dest_monop frac_ainv_tm (ERR "dest_frac_ainv" "");
val dest_frac_minv = dest_monop frac_minv_tm (ERR "dest_frac_minv" "");

val dest_frac_add = dest_binop frac_add_tm (ERR "dest_frac_add" "");
val dest_frac_sub = dest_binop frac_sub_tm (ERR "dest_frac_sub" "");
val dest_frac_mul = dest_binop frac_mul_tm (ERR "dest_frac_mul" "");
val dest_frac_div = dest_binop frac_div_tm (ERR "dest_frac_div" "");

val dest_frac_save = dest_binop frac_save_tm (ERR "dest_frac_save" "");

(*--------------------------------------------------------------------------*
 * query operations
 *--------------------------------------------------------------------------*)

val is_frac_nmr = can dest_frac_nmr;
val is_frac_dnm = can dest_frac_dnm;
val is_frac_sgn = can dest_frac_sgn;

val is_frac_ainv = can dest_frac_ainv;
val is_frac_minv = can dest_frac_minv;

val is_frac_add = can dest_frac_add;
val is_frac_sub = can dest_frac_sub;
val is_frac_mul = can dest_frac_mul;
val is_frac_div = can dest_frac_div;

val is_frac_save = can dest_frac_save;

(*==========================================================================
 * end of structure
 *==========================================================================*)
end;
