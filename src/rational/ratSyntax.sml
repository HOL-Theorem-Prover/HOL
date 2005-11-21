structure ratSyntax :> ratSyntax =
struct

open HolKernel boolLib Parse;

(* interactive mode
app load ["ratTheory"];
*)

open ratTheory;


val ERR = mk_HOL_ERR "ratSyntax";

(*--------------------------------------------------------------------------*
 * constants
 *--------------------------------------------------------------------------*)

(*val int_ty = intSyntax.int_ty;*)
(*val rat = mk_thy_type{Tyop = "rat", Thy="rat", Args = []};*)

val rat_0_tm = prim_mk_const {Name="rat_0",Thy="rat"};
val rat_1_tm = prim_mk_const {Name="rat_1",Thy="rat"};

val rat_nmr_tm = prim_mk_const {Name="rat_nmr",Thy="rat"};
val rat_dnm_tm = prim_mk_const {Name="rat_dnm",Thy="rat"};
val rat_sgn_tm = prim_mk_const {Name="rat_sgn",Thy="rat"};

val rat_ainv_tm = prim_mk_const {Name="rat_ainv",Thy="rat"};
val rat_minv_tm = prim_mk_const {Name="rat_minv",Thy="rat"};

val rat_add_tm = prim_mk_const {Name="rat_add",Thy="rat"};
val rat_sub_tm = prim_mk_const {Name="rat_sub",Thy="rat"};
val rat_mul_tm = prim_mk_const {Name="rat_mul",Thy="rat"};
val rat_div_tm = prim_mk_const {Name="rat_div",Thy="rat"};

val rat_les_tm = prim_mk_const {Name="rat_les",Thy="rat"};
val rat_gre_tm = prim_mk_const {Name="rat_gre",Thy="rat"};
val rat_leq_tm = prim_mk_const {Name="rat_leq",Thy="rat"};
val rat_geq_tm = prim_mk_const {Name="rat_geq",Thy="rat"};

(*--------------------------------------------------------------------------*
 * constructors
 *--------------------------------------------------------------------------*)

fun mk_monop c tm = mk_comb(c,tm);
fun mk_binop c (tm1,tm2) = mk_comb(mk_comb(c,tm1),tm2);

val mk_rat_nmr = mk_monop rat_nmr_tm;
val mk_rat_dnm = mk_monop rat_dnm_tm;
val mk_rat_sgn = mk_monop rat_sgn_tm;

val mk_rat_ainv = mk_monop rat_ainv_tm;
val mk_rat_minv = mk_monop rat_minv_tm;

val mk_rat_add = mk_binop rat_add_tm;
val mk_rat_sub = mk_binop rat_sub_tm;
val mk_rat_mul = mk_binop rat_mul_tm;
val mk_rat_div = mk_binop rat_div_tm;

val mk_rat_les = mk_binop rat_les_tm;
val mk_rat_gre = mk_binop rat_gre_tm;
val mk_rat_leq = mk_binop rat_leq_tm;
val mk_rat_geq = mk_binop rat_geq_tm;

(*--------------------------------------------------------------------------*
 * destructors
 *--------------------------------------------------------------------------*)

val dest_rat_nmr = dest_monop rat_nmr_tm (ERR "dest_rat_nmr" "");
val dest_rat_dnm = dest_monop rat_dnm_tm (ERR "dest_rat_dnm" "");
val dest_rat_sgn = dest_monop rat_sgn_tm (ERR "dest_rat_sgn" "");

val dest_rat_ainv = dest_monop rat_ainv_tm (ERR "dest_rat_ainv" "");
val dest_rat_minv = dest_monop rat_minv_tm (ERR "dest_rat_minv" "");

val dest_rat_add = dest_binop rat_add_tm (ERR "dest_rat_add" "");
val dest_rat_sub = dest_binop rat_sub_tm (ERR "dest_rat_sub" "");
val dest_rat_mul = dest_binop rat_mul_tm (ERR "dest_rat_mul" "");
val dest_rat_div = dest_binop rat_div_tm (ERR "dest_rat_div" "");

val dest_rat_les = dest_binop rat_les_tm (ERR "dest_rat_les" "");
val dest_rat_gre = dest_binop rat_gre_tm (ERR "dest_rat_gre" "");
val dest_rat_leq = dest_binop rat_leq_tm (ERR "dest_rat_leq" "");
val dest_rat_geq = dest_binop rat_geq_tm (ERR "dest_rat_geq" "");

(*--------------------------------------------------------------------------*
 * query operations
 *--------------------------------------------------------------------------*)

val is_rat_nmr = can dest_rat_nmr;
val is_rat_dnm = can dest_rat_dnm;
val is_rat_sgn = can dest_rat_sgn;

val is_rat_ainv = can dest_rat_ainv;
val is_rat_minv = can dest_rat_minv;

val is_rat_add = can dest_rat_add;
val is_rat_sub = can dest_rat_sub;
val is_rat_mul = can dest_rat_mul;
val is_rat_div = can dest_rat_div;

val is_rat_les = can dest_rat_les;
val is_rat_gre = can dest_rat_gre;
val is_rat_leq = can dest_rat_leq;
val is_rat_geq = can dest_rat_geq;

(*--------------------------------------------------------------------------*
 * list constructors
 *--------------------------------------------------------------------------*)

fun list_rat_add summands =
let
	fun recurse acc [] = acc
	  | recurse acc (x::xs) = recurse (mk_rat_mul(acc, x)) xs
in
	recurse (hd summands) (tl summands)
	handle List.Empty => raise ERR "list_rat_add" "empty summand list"
end;


fun list_rat_mul multiplicands =
let
	fun recurse acc [] = acc
	  | recurse acc (x::xs) = recurse (mk_rat_mul(acc, x)) xs
in
	recurse (hd multiplicands) (tl multiplicands)
	handle List.Empty => raise ERR "list_rat_mul" "empty multiplicand list"
end;


(*--------------------------------------------------------------------------*
 * list destructors
 *--------------------------------------------------------------------------*)

fun strip_rat_add tm =
let
	fun recurse acc tm =
	let val (l,r) = dest_rat_add tm in
		recurse (recurse acc r) l
	end handle HOL_ERR _ => tm::acc
in
	recurse [] tm
end;


fun strip_rat_mul tm =
let
	fun recurse acc tm =
	let val (l,r) = dest_rat_mul tm in
		recurse (recurse acc r) l
	end handle HOL_ERR _ => tm::acc
in
	recurse [] tm
end;

(*==========================================================================
 * end of structure
 *==========================================================================*)
end;
