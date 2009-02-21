structure realSyntax :> realSyntax =
struct

  local open realTheory in end;
  open HolKernel Abbrev

  val ERR = mk_HOL_ERR "realSyntax"


  (* Fundamental terms, mainly constants *)

  fun mk_raconst (n, ty) = mk_thy_const {Thy = "realax", Name = n, Ty = ty}
  fun mk_rconst (n, ty) = mk_thy_const {Thy = "real", Name = n, Ty = ty}

  val real_ty = mk_thy_type {Thy = "realax", Tyop = "real", Args = []}
  val bop_ty = real_ty --> real_ty --> real_ty
  val rel_ty = real_ty --> real_ty --> bool

  val real_injection = mk_rconst("real_of_num", numSyntax.num --> real_ty)

  val zero_tm = mk_comb(real_injection, numSyntax.zero_tm)
  val one_tm = mk_comb(real_injection, numSyntax.mk_numeral (Arbnum.fromInt 1))
  val negate_tm = mk_raconst("real_neg", real_ty --> real_ty)
  val absval_tm = mk_rconst("abs", real_ty --> real_ty)
  val plus_tm = mk_raconst("real_add", bop_ty)
  val minus_tm = mk_rconst("real_sub", bop_ty)
  val mult_tm = mk_raconst("real_mul", bop_ty)
  val div_tm = mk_rconst("/", bop_ty)
  val exp_tm = mk_rconst("pow", real_ty --> numSyntax.num --> real_ty)

  val real_eq_tm = mk_thy_const { Thy = "min", Name = "=", Ty = rel_ty}
  val less_tm = mk_raconst("real_lt", rel_ty)
  val leq_tm = mk_rconst("real_lte", rel_ty)
  val great_tm = mk_rconst("real_gt", rel_ty)
  val geq_tm = mk_rconst("real_ge", rel_ty)

  val min_tm = mk_rconst("min", bop_ty)
  val max_tm = mk_rconst("max", bop_ty)

  (* Functions *)

  fun dest1 c fnm nm t = let
    val (f, x) = dest_comb t
    val _ = assert (same_const f) c
  in
    x
  end handle HOL_ERR _ => raise ERR fnm ("Term is not a "^nm)

  fun dest2 c fnm nm t = let
    val (fx, y) = dest_comb t
    val (f, x) = dest_comb fx
    val _ = assert (same_const f) c
in
    (x, y)
  end handle HOL_ERR _ => raise ERR fnm ("Term is not a "^nm)

  val dest_negated = dest1 negate_tm "dest_negated" "negation"
  val is_negated = can dest_negated
  fun mk_negated t = mk_comb(negate_tm, t)

  val dest_injected = dest1 real_injection "dest_injected" "injection"
  val is_injected = can dest_injected
  fun mk_injected t = mk_comb(real_injection, t)



  fun is_real_literal t = let
    (* returns true if a term is in the range of the implicit injection from
       the integers *)
    fun remove_negs t = remove_negs (dest_negated t) handle HOL_ERR _ => t
    val number_part = dest_injected (remove_negs t)
  in
    numSyntax.is_numeral number_part
  end handle HOL_ERR _ => false

  fun term_of_int i = let
    fun posint i =
        mk_comb(real_injection, numSyntax.mk_numeral(Arbint.toNat i))
  in
    if Arbint.<(i,Arbint.zero) then mk_negated(posint(Arbint.~ i))
    else posint i
  end


  fun flip f (x,y) = f (y, x)
  val dest_plus = dest2 plus_tm "dest_plus" "plus"
  val is_plus = can dest_plus
  fun mk_plus(t1, t2) = list_mk_comb(plus_tm, [t1, t2])
  fun list_mk_plus tlist =
      case tlist of
        [] => raise ERR "list_mk_plus" "Empty list"
      | [t] => t
      | t::ts => List.foldl (flip mk_plus) t ts
  fun strip_plus t = let
    fun recurse a k =
        case k of
          [] => a
        | (t::ts) => let
            val (t1, t2) = dest_plus t
          in
            recurse a (t2::t1::ts)
          end handle HOL_ERR _ => recurse (t::a) ts
  in
    recurse [] [t]
  end

  val dest_minus = dest2 minus_tm "dest_minus" "subtraction"
  val is_minus = can dest_minus
  fun mk_minus(t1,t2) = list_mk_comb(minus_tm, [t1, t2])

  val dest_mult = dest2 mult_tm "dest_mult" "multiplication"
  val is_mult = can dest_mult
  fun mk_mult(t1, t2) = list_mk_comb(mult_tm, [t1, t2])
  fun list_mk_mult tlist =
      case tlist of
        [] => raise ERR "list_mk_mult" "Empty list"
      | [t] => t
      | t::ts => List.foldl (flip mk_mult) t ts
  fun strip_mult t = let
    fun recurse a k =
        case k of
          [] => a
        | t::ts => let
            val (t1, t2) = dest_mult t
          in
            recurse a (t2::t1::ts)
          end handle HOL_ERR _ => recurse (t::a) ts
  in
    recurse [] [t]
  end


  val dest_div = dest2 div_tm "dest_div" "division"
  val is_div = can dest_div
  fun mk_div(t1, t2) = list_mk_comb(div_tm, [t1, t2])

  val dest_absval = dest1 absval_tm "dest_absval" "absolute value"
  val is_absval = can dest_absval
  fun mk_absval t = mk_comb(absval_tm, t)

  val dest_less = dest2 less_tm "dest_less" "less-than term"
  val is_less = can dest_less
  fun mk_less(t1, t2) = list_mk_comb(less_tm, [t1, t2])

  val dest_leq = dest2 leq_tm "dest_leq" "less-than-or-equal term"
  val is_leq = can dest_leq
  fun mk_leq(t1, t2) = list_mk_comb(leq_tm, [t1, t2])

  val dest_great = dest2 great_tm "dest_great" "greater-than term"
  val is_great = can dest_great
  fun mk_great(t1, t2) = list_mk_comb(great_tm, [t1, t2])

  val dest_geq = dest2 geq_tm "dest_geq" "greater-than-or-equal term"
  val is_geq = can dest_geq
  fun mk_geq(t1, t2) = list_mk_comb(geq_tm, [t1, t2])

  val dest_min = dest2 min_tm "dest_min" "min term"
  val is_min = can dest_min
  fun mk_min(t1, t2) = list_mk_comb(min_tm, [t1, t2])

  val dest_max = dest2 max_tm "dest_max" "max term"
  val is_max = can dest_max
  fun mk_max(t1, t2) = list_mk_comb(max_tm, [t1, t2])


  fun int_of_term t = let
    val (is_pos, n) =
        case Lib.total dest_negated t of
          NONE => (true, numSyntax.dest_numeral (dest_injected t))
        | SOME neg_i => (false, numSyntax.dest_numeral (dest_injected neg_i))
  in
    if is_pos then Arbint.fromNat n
    else Arbint.~(Arbint.fromNat n)
  end

end ;
