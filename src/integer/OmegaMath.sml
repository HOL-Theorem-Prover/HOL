structure OmegaMath :> OmegaMath = struct

open HolKernel boolLib intSyntax integerTheory int_arithTheory

open CooperMath QConv

infix THEN THENL THENC ORELSEC ##

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

(* ----------------------------------------------------------------------
    addzero t

    if t (of integer type and not a numeral itself) does not have a
    numeral as its 'rand, then return thm |- t = t + 0, otherwise
    ALL_QCONV.
   ---------------------------------------------------------------------- *)

fun addzero t =
    if is_int_literal t orelse  is_int_literal (rand t) then ALL_QCONV t
    else SYM (SPEC t INT_ADD_RID)


(* ----------------------------------------------------------------------
    RLIB_INT_NORM_CONV tm

    returns a normalised term, with coefficients collected over all
    variables, etc.  Uses integerRingLib.INT_NORM_CONV but
    post-processes the result, because the ringLib code can return
    terms including subtractions, associates the additions to the
    right, and puts the numeral in the left-most position (if there is
    one; it will drop trailing + 0 terms)
   ---------------------------------------------------------------------- *)

val RLIB_INT_NORM_CONV = let
  val move_numeral_right = prove(
    ``!n y z:int. (&n + y = y + &n) /\ (~&n + y = y + ~&n) /\
                  (y + &n + z = y + z + &n) /\
                  (y + ~&n + z = y + z + ~&n)``,
    REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM INT_ADD_ASSOC, INT_EQ_LADD] THEN
    MATCH_ACCEPT_TAC INT_ADD_COMM);
  fun put_in_times1 t =
      if is_plus t then BINOP_QCONV put_in_times1 t
      else if is_var t then SYM (SPEC t INT_MUL_LID)
      else if is_negated t andalso is_var (rand t) then
        SPEC (rand t) INT_NEG_MINUS1
      else ALL_QCONV t
in
  Profile.profile "INC.ringLib" integerRingLib.INT_NORM_CONV THENC
  Profile.profile "INC.rewriting"
    (REWRITE_CONV [int_sub, INT_NEG_LMUL, INT_ADD_ASSOC,
                   move_numeral_right]) THENC
  Profile.profile "INC.final" (addzero THENC put_in_times1)
end

(* ----------------------------------------------------------------------
    NAIVE_INT_NORM_CONV tm

    as the above, but naively done.  Is intended to be quicker on small
    terms, where the overhead of the ringLib solution is too great.
   ---------------------------------------------------------------------- *)

val NAIVE_INT_NORM_CONV = let
  fun partition R acc l = let
    fun insert x [] = [[x]]
      | insert x (p1 :: ps) = if R (x, hd p1) then (x::p1) :: ps
                              else p1 :: insert x ps
  in
    case l of
      [] => acc
    | (x::xs) => partition R (insert x acc) xs
  end
  fun collect_vars tm = let
    val summands = strip_plus tm
    val dm = total (#2 o dest_mult)
    val collected = partition (op= o (dm ## dm)) [] summands
    val newrhs = let
      val (nums, vars) = Lib.pluck (fn p => is_int_literal (hd p)) collected
    in
      mk_plus (list_mk_plus (map list_mk_plus vars), list_mk_plus nums)
    end handle HOL_ERR _ => list_mk_plus (map list_mk_plus collected)
    val newrhs_th = EQT_ELIM(AC_CONV (INT_ADD_ASSOC, INT_ADD_COMM)
                                     (mk_eq(tm, newrhs)))
  in
    K newrhs_th THENC REWRITE_CONV [GSYM INT_RDISTRIB] THENC
    REDUCE_CONV
  end tm

in
  REWRITE_CONV [INT_LDISTRIB, INT_RDISTRIB, INT_MUL_ASSOC] THENC
  REDUCE_CONV THENC
  (* to this point have expanded all multiplications, and have reduced
     all coefficients; still need to collect vars together *)
  collect_vars THENC addzero
end

(* ----------------------------------------------------------------------
    INT_NORM_CONV tm

    picks the better of the two above, depending on the size of the term.
    Experiments suggest that the crossover point is at about 100 summands.
   ---------------------------------------------------------------------- *)

fun INT_NORM_CONV tm = let
  fun tmsize acc tm = let
    val (l,r) = dest_plus tm
  in
    tmsize (tmsize acc r) l
  end handle HOL_ERR _ => let
               val (l,r) = dest_mult tm
             in
               if is_var r then 1 + acc
               else tmsize acc r
             end handle HOL_ERR _ => acc + 1
in
  if tmsize 0 tm < 100 then NAIVE_INT_NORM_CONV tm
  else RLIB_INT_NORM_CONV tm
end



end
