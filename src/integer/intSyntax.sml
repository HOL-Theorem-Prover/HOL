structure intSyntax :> intSyntax = 
struct

open HolKernel basicHol90Lib Parse integerTheory Psyntax;

fun ERR f s = HOL_ERR {origin_structure = "intSyntax",
                       origin_function = f,
                       message = s};

infixr -->
infix THENC

val (Type,Term) = parse_from_grammars integerTheory.integer_grammars;
fun -- q x = Term q
fun == q x = Type q

val num_ty = Rsyntax.mk_type{Tyop = "num", Args = []}
val int_ty = Rsyntax.mk_type{Tyop = "int", Args = []}
val plus_tm = Term`$+ : int -> int -> int`
val minus_tm = Term`$- : int -> int -> int`
val mult_tm = Term`$* : int -> int -> int`
val less_tm = Term`$< : int -> int -> bool`
val leq_tm = Term`$<= : int -> int -> bool`
val great_tm = Term`$> : int -> int -> bool`
val geq_tm = Term`$>= : int -> int -> bool`
val divides_tm = Term`$int_divides : int -> int -> bool`;
val absval_tm = Term`ABS : int -> int`;
val min_tm = Term.mk_const{Name = "int_min", Ty = int_ty --> int_ty --> int_ty}
val zero_tm = Term`0i`

fun is_plus tm = let
  val (hd, args) = strip_comb tm
in
  length args = 2 andalso hd = plus_tm
end
fun mk_plus (arg1, arg2) = list_mk_comb(plus_tm, [arg1, arg2])
fun list_mk_plus summands = let
  fun recurse acc [] = acc
    | recurse acc (x::xs) = recurse (mk_plus(acc, x)) xs
in
  recurse (hd summands) (tl summands)
  handle List.Empty => raise ERR "list_mk_plus" "empty summand list"
end
fun strip_plus tm = let
  fun recurse acc tm =
    if is_plus tm then
      recurse (recurse acc (rand tm)) (rand (rator tm))
    else
      tm::acc
in
  recurse [] tm
end

fun is_minus tm = let
  val (hd, args) = strip_comb tm
in
  length args = 2 andalso hd = minus_tm
end
fun mk_minus (tm1, tm2) = list_mk_comb(minus_tm, [tm1, tm2])


fun is_mult tm = let
  val (hd, args) = strip_comb tm
in
  length args = 2 andalso hd = mult_tm
end
fun mk_mult (tm1, tm2) = list_mk_comb(mult_tm, [tm1, tm2]);
fun list_mk_mult multiplicands = let
  fun recurse acc [] = acc
    | recurse acc (x::xs) = recurse (mk_mult(acc, x)) xs
in
  recurse (hd multiplicands) (tl multiplicands)
  handle List.Empty => raise ERR "list_mk_mult" "empty multiplicand list"
end
fun strip_mult tm = let
  fun recurse acc tm =
    if is_mult tm then
      recurse (recurse acc (rand tm)) (rand (rator tm))
    else
      tm::acc
in
  recurse [] tm
end

fun mk_absval tm = mk_comb(absval_tm, tm)
fun is_absval tm = is_comb tm andalso rator tm = absval_tm

fun is_bin_relop reltm tm = let
  val (hd, args) = strip_comb tm
in
  length args = 2 andalso hd = reltm
end

val is_less = is_bin_relop less_tm
fun mk_less (tm1, tm2) = list_mk_comb(less_tm, [tm1, tm2])

val is_leq = is_bin_relop leq_tm
fun mk_leq (tm1, tm2) = list_mk_comb(leq_tm, [tm1, tm2])

val is_great = is_bin_relop great_tm
fun mk_great (tm1, tm2) = list_mk_comb(great_tm, [tm1, tm2])

val is_geq = is_bin_relop geq_tm
fun mk_geq (tm1, tm2) = list_mk_comb(geq_tm, [tm1, tm2])



fun is_divides tm = let
  val (hd, args) = strip_comb tm
in
  length args = 2 andalso hd = divides_tm
end
fun mk_divides (tm1, tm2) = list_mk_comb(divides_tm, [tm1, tm2])


val int_injection =
  Rsyntax.mk_const{Name = "int_of_num", Ty = num_ty --> int_ty}
val negate_tm = Rsyntax.mk_const{Name = "int_neg", Ty = int_ty --> int_ty}
fun is_int_literal t =
  (rator t = int_injection andalso Term.is_numeral (rand t)) orelse
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
  else Arbint.fromNat (Term.dest_numeral r)
end

fun term_of_int i = let
  open Arbint
in
  if i < zero then
    mk_negated (term_of_int (~i))
  else
    mk_comb(int_injection, Term.mk_numeral (toNat i))
end


end (* struct *)
