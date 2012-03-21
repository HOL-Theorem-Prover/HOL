structure intSyntax :> intSyntax =
struct

open HolKernel boolLib Parse integerTheory;

val ERR = mk_HOL_ERR "intSyntax";

val num_ty = numSyntax.num
val int_ty = mk_thy_type{Tyop = "int", Thy="integer", Args = []}

fun Const s = prim_mk_const{Name=s, Thy="integer"};

val negate_tm = Const "int_neg"
val plus_tm =  Const "int_add"
val minus_tm = Const "int_sub"
val mult_tm =  Const "int_mul"
val exp_tm =   Const "int_exp"
val div_tm =   Const "int_div"
val mod_tm =   Const "int_mod"
val quot_tm =  Const "int_quot"
val rem_tm =   Const "int_rem"
val less_tm =  Const "int_lt"
val leq_tm =   Const "int_le"
val great_tm = Const "int_gt"
val geq_tm =   Const "int_ge"
val min_tm =   Const "int_min"
val max_tm =   Const "int_max";
val absval_tm =  Const "ABS"
val divides_tm = Const "int_divides"
val LEAST_INT_tm = Const "LEAST_INT"
val int_injection = Const "int_of_num"
val Num_tm = Const "Num"

val int_eq_tm = inst [alpha |-> int_ty] boolSyntax.equality

fun dest_binop t (srcf,msg) tm = let
  val (farg1, arg2) = dest_comb tm
  val (f, arg1) = dest_comb farg1
in
  if f <> t then raise ERR srcf msg
  else (arg1, arg2)
end

val dest_plus = dest_binop plus_tm ("dest_plus", "Term not a plus")
val is_plus = can dest_plus
fun mk_plus (arg1, arg2) = list_mk_comb(plus_tm, [arg1, arg2])

fun list_mk_plus summands = let
  fun recurse acc [] = acc
    | recurse acc (x::xs) = recurse (mk_plus(acc, x)) xs
in
  recurse (hd summands) (tl summands)
  handle List.Empty => raise ERR "list_mk_plus" "empty summand list"
end

fun strip_plus tm = let
  fun recurse acc tm = let
    val (l,r) = dest_plus tm
  in
    recurse (recurse acc r) l
  end handle HOL_ERR _ => tm::acc
in
  recurse [] tm
end

val dest_minus = dest_binop minus_tm ("dest_minus", "Term not a minus")
val is_minus = can dest_minus
fun mk_minus (tm1, tm2) = list_mk_comb(minus_tm, [tm1, tm2])

val dest_mult = dest_binop mult_tm ("dest_mult", "Term not a multiplication")
val is_mult = can dest_mult
fun mk_mult (tm1, tm2) = list_mk_comb(mult_tm, [tm1, tm2]);

fun list_mk_mult multiplicands = let
  fun recurse acc [] = acc
    | recurse acc (x::xs) = recurse (mk_mult(acc, x)) xs
in
  recurse (hd multiplicands) (tl multiplicands)
  handle List.Empty => raise ERR "list_mk_mult" "empty multiplicand list"
end
fun strip_mult tm = let
  fun recurse acc tm = let
    val (l,r) = dest_mult tm
  in
    recurse (recurse acc r) l
  end handle HOL_ERR _ => tm::acc
in
  recurse [] tm
end

val dest_exp = dest_binop exp_tm ("dest_exp", "Term not an exp")
val is_exp = can dest_exp
fun mk_exp (arg1, arg2) = list_mk_comb(exp_tm, [arg1, arg2])

val dest_div = dest_binop div_tm ("dest_div", "Term not a division")
val is_div = can dest_div
fun mk_div (t1, t2) = list_mk_comb(div_tm, [t1, t2])

val dest_mod = dest_binop mod_tm ("dest_mod", "Term not a modulo")
val is_mod = can dest_mod
fun mk_mod (t1, t2) = list_mk_comb(mod_tm, [t1, t2])

val dest_quot = dest_binop quot_tm ("dest_quot", "Term not a quotient")
val is_quot = can dest_quot
fun mk_quot (t1, t2) = list_mk_comb(quot_tm, [t1, t2])

val dest_rem = dest_binop rem_tm ("dest_rem", "Term not a remainder")
val is_rem = can dest_rem
fun mk_rem (t1, t2) = list_mk_comb(rem_tm, [t1, t2])

fun mk_absval tm = mk_comb(absval_tm, tm)
fun dest_absval tm = let
  val (f,x) = dest_comb tm
      handle HOL_ERR _ => raise ERR "dest_absval" "term not an absolute value"
in
  if same_const f absval_tm then x
  else raise ERR "dest_absval" "term not an absolute value"
end
val is_absval = can dest_absval

fun mk_Num t = mk_comb(Num_tm, t)
fun dest_Num t = let
  val (f,x) = dest_comb t
      handle HOL_ERR _ => raise ERR "dest_Num" "term not a Num coercion"
in
  if same_const f Num_tm then x
  else raise ERR "dest_Num" "term not a Num coercion"
end
val is_Num = can dest_Num



val dest_less = dest_binop less_tm ("dest_less", "Term not a less-than")
val is_less = can dest_less
fun mk_less (tm1, tm2) = list_mk_comb(less_tm, [tm1, tm2])

val dest_leq = dest_binop leq_tm ("dest_leq", "Term not a less-than-or-equal")
val is_leq = can dest_leq
fun mk_leq (tm1, tm2) = list_mk_comb(leq_tm, [tm1, tm2])

val dest_great = dest_binop great_tm ("dest_great", "Term not a greater-than")
val is_great = can dest_great
fun mk_great (tm1, tm2) = list_mk_comb(great_tm, [tm1, tm2])

val dest_geq = dest_binop geq_tm ("dest_geq",
                                  "Term not a greater-than-or-equal")
val is_geq = can dest_geq
fun mk_geq (tm1, tm2) = list_mk_comb(geq_tm, [tm1, tm2])


val dest_divides = dest_binop divides_tm ("dest_divides", "Term not a divides")
val is_divides = can dest_divides
fun mk_divides (tm1, tm2) = list_mk_comb(divides_tm, [tm1, tm2])

val dest_min = dest_binop min_tm ("dest_min", "Term not a min")
val is_min = can dest_min
fun mk_min (tm1, tm2) = list_mk_comb(min_tm, [tm1, tm2])

val dest_max = dest_binop max_tm ("dest_max", "Term not a max")
val is_max = can dest_max
fun mk_max (tm1, tm2) = list_mk_comb(max_tm, [tm1, tm2])

fun dest_LEAST_INT t =
  let
    val (f, x) = dest_comb t
    val _ = assert (same_const LEAST_INT_tm) f
  in
    x
  end handle HOL_ERR _ =>
    raise ERR "dest_LEAST_INT" "term not a LEAST_INT"

val is_LEAST_INT = can dest_LEAST_INT
fun mk_LEAST_INT t = mk_comb (LEAST_INT_tm, t)

fun dest_injected tm = let
  val (f,x) = dest_comb tm
    handle HOL_ERR _ => raise ERR "dest_injected" "term not an injection"
in
  if f = int_injection then x
  else raise ERR "dest_injected" "term not an injection"
end
val is_injected = can dest_injected
fun mk_injected tm = mk_comb(int_injection, tm)


fun dest_negated tm = let
  val (l,r) = dest_comb tm
    handle HOL_ERR _ => raise ERR "dest_negated" "term not a negation"
in
  if l = negate_tm then r
  else raise ERR "dest_negated" "term not a negation"
end
val is_negated = can dest_negated
fun mk_negated tm = mk_comb(negate_tm, tm)

fun is_int_literal t =
  (rator t = int_injection andalso numSyntax.is_numeral (rand t)) orelse
  (rator t = negate_tm andalso is_int_literal (rand t))
  handle HOL_ERR _ => false

fun int_of_term tm = let
  val _ =
    is_int_literal tm orelse
    raise ERR "int_of_term" "applied to non-literal"
  val (l,r) = dest_comb tm
in
  if l = negate_tm then Arbint.~(int_of_term r)
  else Arbint.fromNat (numSyntax.dest_numeral r)
end

fun term_of_int i = let
  open Arbint
in
  if i < zero then
    mk_negated (term_of_int (~i))
  else
    mk_comb(int_injection, numSyntax.mk_numeral (toNat i))
end

val zero_tm = term_of_int Arbint.zero
val one_tm  = term_of_int Arbint.one

end
