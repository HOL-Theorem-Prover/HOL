structure OmegaMath :> OmegaMath = struct

open HolKernel boolLib intSyntax integerTheory int_arithTheory

open CooperMath QConv

infix THENC ORELSEC ##

val (Type, Term) = parse_from_grammars int_arith_grammars

fun c1 THENC c2 = THENQC c1 c2
fun c1 ORELSEC c2 = ORELSEQC c1 c2

fun ERR f msg = HOL_ERR { origin_structure = "OmegaMath",
                          origin_function = f,
                          message = msg}

val INT_RING_CONV = EQT_ELIM o integerRingLib.INT_RING_CONV

(* ----------------------------------------------------------------------
    gcd_eq_check tm

    tm must be of the form
        0 = r1 + .. + rn
    where rn is a numeral and all of the other ri's are of the form
        (numeral * variable)

    If all of the variables have coefficients divisible by some common
    factor, then this conversion returns an equality either with all the
    coefficients appropriately smaller, or equating it to false (which
    will happen if there the numeral term is of the wrong divisibility).

    If there is nothing to eliminate, then return QConv.UNCHANGED.
   ---------------------------------------------------------------------- *)

fun gcd_eq_check tm = let
  open Arbint
  val INT_RING_CONV =
      EQT_ELIM o (REWRITE_CONV [INT_LDISTRIB, INT_MUL_ASSOC] THENC REDUCE_CONV)
  val r = rand tm
  val summands = strip_plus r
  val (vars, numpart) = front_last summands
  val numpart_i = int_of_term numpart
  val coeffs = map (abs o int_of_term o #1 o dest_mult) vars
  val g = gcdl coeffs
  val _ = g <> one orelse raise UNCHANGED
  val g_t = term_of_int g
  fun mapthis t = let
    val (c, v) = dest_mult t
    val newc = term_of_int (int_of_term c div g)
  in
    mk_mult(newc, v)
  end
  val newvars_sum = list_mk_plus (map mapthis vars)
  val (nq, nr) = divmod(numpart_i, g)
in
  if nr = zero then let
      val varpart = mk_mult(g_t, mk_plus(newvars_sum, term_of_int nq))
      val newrhs_th = AP_TERM (rator tm) (INT_RING_CONV(mk_eq(r, varpart)))
    in
      K newrhs_th THENC REWR_CONV EQ_SYM_EQ THENC REWR_CONV INT_ENTIRE THENC
      LAND_CONV REDUCE_CONV THENC REWR_CONV CooperThms.F_or_l THENC
      REWR_CONV EQ_SYM_EQ
    end
  else let
      val newlhs = mk_negated numpart
      val newrhs = mk_plus(mk_mult(g_t, newvars_sum), numpart)
      val newrhs_th = AP_TERM (rator tm) (INT_RING_CONV(mk_eq(r, newrhs)))
      val g_num_t = rand g_t
      val g_num_nonzero =
          EQT_ELIM (REDUCE_CONV
                      (mk_neg(mk_eq(g_num_t, numSyntax.zero_tm))))
    in
      K newrhs_th THENC REWR_CONV eq_move_right_left THENC
      REWR_CONV EQ_SYM_EQ THENC RAND_CONV (REWR_CONV INT_ADD_LID) THENC
      K (MP (SPECL [g_num_t, newvars_sum, newlhs] elim_eq_coeffs)
            g_num_nonzero) THENC
      LAND_CONV REDUCE_CONV THENC REWR_CONV CooperThms.F_and_l
    end
end tm

(* ----------------------------------------------------------------------
    gcd_le_check tm

    performs a "gcd check" for terms of the form
      0 <= (c1 * v1) + (c2 * v2) + .. + (cn * vn) + n
   ---------------------------------------------------------------------- *)

fun gcd_le_check tm = let
  open Arbint
  val INT_RING_CONV =
      EQT_ELIM o (REWRITE_CONV [INT_LDISTRIB, INT_MUL_ASSOC] THENC REDUCE_CONV)
  val r = rand tm
  val (varpart, numpart) = dest_plus r
  val vars = strip_plus varpart
  val numpart_i = int_of_term numpart
  val coeffs = map (abs o int_of_term o #1 o dest_mult) vars
  val g = gcdl coeffs
  val _ = g <> one orelse raise UNCHANGED
  val g_t = term_of_int g
  val zero_lt_g = EQT_ELIM (REDUCE_CONV (mk_less(zero_tm, g_t)))
  fun mapthis t = let
    val (c,v) = dest_mult t
  in
    mk_mult(term_of_int (int_of_term c div g), v)
  end
  val newvars_sum = list_mk_plus (map mapthis vars)
  val (nq, nr) = divmod(numpart_i, g)
in
  if nr = zero then let
      val factor = mk_plus(newvars_sum, term_of_int nq)
      val newrhs = mk_mult(g_t, factor)
      val newrhs_th = AP_TERM (rator tm) (INT_RING_CONV (mk_eq(r, newrhs)))
      val final_th = MP (SPECL [g_t, zero_tm, factor] INT_LE_MONO) zero_lt_g
    in
      K newrhs_th THENC LAND_CONV (K (SYM (SPEC g_t INT_MUL_RZERO))) THENC
      K final_th
    end
  else let
      val gvars = mk_mult(g_t, newvars_sum)
      val newrhs = mk_plus(gvars, numpart)
      val newrhs_th = AP_TERM (rator tm) (INT_RING_CONV(mk_eq(r, newrhs)))
      val (negnegconv1, negnegconv2, elimth, newlhs) =
          if is_negated numpart then
            (REWR_CONV INT_NEGNEG, ALL_QCONV, elim_le_coeffs_pos,
             rand (rand numpart))
          else
            (ALL_QCONV, REWR_CONV INT_NEGNEG ORELSEC REWR_CONV INT_NEG_0,
             elim_le_coeffs_neg, rand numpart)
      val final_th = MP (SPECL [g_t, newlhs, newvars_sum] elimth)
                        zero_lt_g
    in
      K newrhs_th THENC REWR_CONV le_move_right_left THENC
      LAND_CONV (REWR_CONV INT_ADD_LID) THENC LAND_CONV negnegconv1 THENC
      K final_th THENC LAND_CONV REDUCE_CONV THENC
      REWR_CONV le_move_all_right THENC RAND_CONV (RAND_CONV negnegconv2)
    end
end tm

(* ----------------------------------------------------------------------
    gcd_check tm

    combines the above two checks, depending on the relational symbol of
    the term.
   ---------------------------------------------------------------------- *)

fun gcd_check tm =
    case #Name (dest_thy_const (#1 (strip_comb tm))) of
      "int_le" => gcd_le_check tm
    | "=" => gcd_eq_check tm
    | _ => raise ERR "gcd_check" "Term not an = or <="

end