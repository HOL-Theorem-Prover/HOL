structure intSyntax :> intSyntax =
struct

open HolKernel boolLib Parse integerTheory;

val ERR = mk_HOL_ERR "intSyntax";

infixr -->
infix THENC

val (Type,Term) = parse_from_grammars integerTheory.integer_grammars;
fun -- q x = Term q
fun == q x = Type q

val num_ty = numSyntax.num
val int_ty = mk_thy_type{Tyop = "int", Thy="integer", Args = []}

val plus_tm = Term`$+ : int -> int -> int`
val minus_tm = Term`$- : int -> int -> int`
val mult_tm = Term`$* : int -> int -> int`
val less_tm = Term`$< : int -> int -> bool`
val leq_tm = Term`$<= : int -> int -> bool`
val great_tm = Term`$> : int -> int -> bool`
val geq_tm = Term`$>= : int -> int -> bool`
val divides_tm = Term`$int_divides : int -> int -> bool`;
val absval_tm = Term`ABS : int -> int`;
val min_tm =
 Term.prim_mk_const {Name = "int_min", Thy="integer"}
val max_tm =
 Term.prim_mk_const {Name = "int_max", Thy="integer"}

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

fun mk_absval tm = mk_comb(absval_tm, tm)
fun is_absval tm = is_comb tm andalso rator tm = absval_tm

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


val int_injection = prim_mk_const{Name = "int_of_num", Thy = "integer"}
val negate_tm = prim_mk_const{Name = "int_neg", Thy = "integer"}
fun is_int_literal t =
  (rator t = int_injection andalso numSyntax.is_numeral (rand t)) orelse
  (rator t = negate_tm andalso is_int_literal (rand t))
  handle HOL_ERR _ => false
fun is_negated tm = is_comb tm andalso rator tm = negate_tm
fun mk_negated tm = mk_comb(negate_tm, tm)


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

end (* struct *)
