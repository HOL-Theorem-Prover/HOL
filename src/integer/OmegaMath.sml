structure OmegaMath :> OmegaMath = struct

open HolKernel boolLib intSyntax integerTheory int_arithTheory

open CooperMath QConv

infix THEN THENL THENC ORELSEC ##

val (Type, Term) = parse_from_grammars int_arith_grammars

fun c1 THENC c2 = THENQC c1 c2
fun c1 ORELSEC c2 = ORELSEQC c1 c2
val ALL_CONV = ALL_QCONV
val BINOP_CONV = BINOP_QCONV
val TRY_CONV = TRY_QCONV

fun ERR f msg = HOL_ERR { origin_structure = "OmegaMath",
                          origin_function = f,
                          message = msg}

val lhand = rand o rator

(* ----------------------------------------------------------------------
    find_summand v tm

    finds the summand involving variable v in tm.  Raise a HOL_ERR if it's
    not there.  tm must be a left-associated sum with one numeral in the
    rightmost position.
   ---------------------------------------------------------------------- *)

exception fs_NotFound
fun find_summand v tm = let
  fun recurse tm = let
    val (l,r) = dest_plus tm
  in
    if rand r = v then r else recurse l
  end handle HOL_ERR _ => if rand tm = v then tm else raise fs_NotFound
in
  recurse (lhand tm) handle fs_NotFound =>
                            raise ERR "find_summand" "No such summand"
end


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
  val newrhs = mk_plus(mk_mult(g_t, newvars_sum), numpart)
  val newrhs_th = AP_TERM (rator tm) (INT_RING_CONV (mk_eq(r, newrhs)))
in
  K newrhs_th THENC
  K (MP (SPECL [g_t, numpart, newvars_sum] elim_le_coeffs) zero_lt_g) THENC
  RAND_CONV (RAND_CONV REDUCE_CONV)
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
    ALL_CONV.
   ---------------------------------------------------------------------- *)

fun addzero t =
    if is_int_literal t orelse  is_int_literal (rand t) then ALL_CONV t
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
      if is_plus t then BINOP_CONV put_in_times1 t
      else if is_var t then SYM (SPEC t INT_MUL_LID)
      else if is_negated t andalso is_var (rand t) then
        SPEC (rand t) INT_NEG_MINUS1
      else ALL_CONV t
in
  integerRingLib.INT_NORM_CONV THENC
  REWRITE_CONV [int_sub, INT_NEG_LMUL, INT_ADD_ASSOC,
                move_numeral_right] THENC
  addzero THENC put_in_times1
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
    fun partition_compare(pl1, pl2) =
        case (dm (hd pl1), dm (hd pl2)) of
          (NONE, NONE) => EQUAL
        | (NONE, SOME x) => GREATER
        | (SOME v, NONE) => LESS
        | (SOME v1, SOME v2) =>
          String.compare (#1 (dest_var v1), #1 (dest_var v2))
    val sorted_collected = Listsort.sort partition_compare collected
    val newrhs = list_mk_plus (map list_mk_plus sorted_collected)
    val newrhs_th = EQT_ELIM(AC_CONV (INT_ADD_ASSOC, INT_ADD_COMM)
                                     (mk_eq(tm, newrhs)))
  in
    K newrhs_th THENC REWRITE_CONV [GSYM INT_RDISTRIB] THENC
    REDUCE_CONV
  end tm

in
  REWRITE_CONV [INT_LDISTRIB, INT_RDISTRIB, INT_MUL_ASSOC, INT_NEG_ADD,
                INT_NEG_LMUL] THENC
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

(* ----------------------------------------------------------------------
    INT_EQ_CONV tm

    tm is of the form t1 = t2.
    This code normalises t1 and t2 using INT_NORM_CONV above, and if both
    reduce to the same term, returns the theorem |- t1 = t2
    Otherwise, fails.
   ---------------------------------------------------------------------- *)

fun INT_EQ_CONV tm = let
  val (l,r) = dest_eq tm
              handle HOL_ERR _ =>
                     raise ERR "INT_EQ_CONV" "Term not an equality"
  val lthm = INT_NORM_CONV l
  val rthm = INT_NORM_CONV r
in
  TRANS lthm (SYM rthm)
  handle HOL_ERR _ =>
         raise ERR "INT_EQ_CONV" "Terms don't reduce to equal terms"
end

(* ----------------------------------------------------------------------
    LASSOC_ADD_CONV tm

    left-associates a single addition, turning a + (b + c) into
    (a + b) + c
   ---------------------------------------------------------------------- *)

val LASSOC_ADD_CONV = REWR_CONV INT_ADD_ASSOC

(* ----------------------------------------------------------------------
    RASSOC_ADD_CONV tm

    right-associates a single addition, turning (a + b) + c into
    a + (b + c)
   ---------------------------------------------------------------------- *)

val RASSOC_ADD_CONV = let
  val th = GSYM INT_ADD_ASSOC
in
  REWR_CONV th
end

(* ----------------------------------------------------------------------
    RTOP_TWO_CONV c tm

    applies conversion c to the term a + b, where a and b are the
    two rightmost summands of tm.  The term is reassociated to present
    these two terms this way if necessary, and then put back into left-
    associative afterwards if necessary.  c should produce at most an
    addition of two terms.
   ---------------------------------------------------------------------- *)

fun RTOP_TWO_CONV c tm = let
  val (l,r) = dest_plus tm
in
  if is_plus l then
    RASSOC_ADD_CONV THENC RAND_CONV c THENC
    TRY_CONV LASSOC_ADD_CONV
  else
    c
end tm

(* ----------------------------------------------------------------------
    PAIRWISE_GATHER_CONV tm

    given that tm = tm1 + tm2, returns an equation of the form
      tm1 + tm2 = result
    where result is a "gathering" transformation as per
    SORT_AND_GATHER1_CONV below
   ---------------------------------------------------------------------- *)

val SYM_RDISTRIB = GSYM INT_RDISTRIB
fun PAIRWISE_GATHER_CONV tm = let
  val (tm1,tm2) = dest_plus tm
in
  if is_int_literal tm1 then
    if is_int_literal tm2 then REDUCE_CONV
    else (* is_mult tm2 *) REWR_CONV INT_ADD_COMM
  else (* is_mult tm1 *)
    if is_int_literal tm2 then ALL_CONV
    else (* is_mult tm2 *) let
        val (c1,v1) = dest_mult tm1
        val (c2,v2) = dest_mult tm2
      in
        case Term.compare(v1,v2) of
          LESS => ALL_CONV
        | EQUAL => REWR_CONV SYM_RDISTRIB THENC LAND_CONV REDUCE_CONV
        | GREATER => REWR_CONV INT_ADD_COMM
      end
end tm

(* ----------------------------------------------------------------------
    CHECK_ZERO_CONV tm

    checks for summands of tm being of the form
       0 * y
    and eliminates them.  Assume that tm is left-associated, and with
    a numeral as its rightmost summand.
   ---------------------------------------------------------------------- *)

val CHECK_RZERO_CONV = let
  fun recurse tm = let
    val (l,r) = dest_plus tm
  in
    case total dest_plus l of
      SOME(ll, lr) => let
        val (c,v) = dest_mult lr
      in
        if c = zero_tm then
          LAND_CONV (RAND_CONV (REWR_CONV INT_MUL_LZERO) THENC
                     REWR_CONV INT_ADD_RID) THENC recurse
        else LAND_CONV recurse
      end
    | NONE => let
        val (c,v) = dest_mult l
      in
        if c = zero_tm then LAND_CONV (REWR_CONV INT_MUL_LZERO) THENC
                            REWR_CONV INT_ADD_LID
        else ALL_CONV
      end
  end tm
in
  TRY_CONV recurse
end

(* ----------------------------------------------------------------------
    SORT_AND_GATHER1_CONV tm

    effectively does one step of an insertion sort on tm.  Taking a term
    of the form
        x + y
    where y is not itself an addition, and where x is already in normal
    form, this function transforms the input by moving y left "into" x
    until it comes to the appropriate resting place.

    Transformations and continuations are

     ... + num1 + num2       --> ... + num               stop
     ... + c * v + num       --> ... + c * v + num       stop
     ... + num + c * v       --> ... + c * v + num       cont
     ... + c1 * v1 + c2 * v2 --> ... + c1 * v1 + c2 * v2 stop (if v1 < v2)
     ... + c1 * v1 + c2 * v1 --> ... + (c1 + c2) * v1    stop
     ... + c1 * v1 + c2 * v2 --> ... + c2 * v2 + c1 * v1 cont (if v2 < v1)

   ---------------------------------------------------------------------- *)

fun SORT_AND_GATHER1_CONV tm =
    (RTOP_TWO_CONV PAIRWISE_GATHER_CONV THENC
     TRY_CONV (LAND_CONV SORT_AND_GATHER1_CONV) THENC
     CHECK_RZERO_CONV) tm

(* ----------------------------------------------------------------------
    SORT_AND_GATHER_CONV tm

    perform SORT_AND_GATHER1_CONV steps repeatedly to sort a sum term.
   ---------------------------------------------------------------------- *)

fun SORT_AND_GATHER_CONV tm = let
  fun prepare_insertion tm =
      (* term is a sum, if right argument is singleton, insert it using
         SORT_AND_GATHER1_CONV, otherwise, reassociate and recurse *)
      if is_plus (rand tm) then
        (LASSOC_ADD_CONV THENC LAND_CONV SORT_AND_GATHER_CONV THENC
         SORT_AND_GATHER_CONV) tm
      else
        SORT_AND_GATHER1_CONV tm
in
  if is_plus tm then
    LAND_CONV SORT_AND_GATHER_CONV THENC prepare_insertion
  else
    ALL_CONV
end tm

(* ----------------------------------------------------------------------
    S_AND_G_MULT tm

    as for SORT_AND_GATHER_CONV, but also taking into account summands
    of the form c * (...)  where the ... represents another summand.
   ---------------------------------------------------------------------- *)

fun S_AND_G_MULT tm = let
  fun prepare_insertion tm =
      (* term is a sum, if right argument is singleton, insert it using
         SORT_AND_GATHER1_CONV, otherwise, reassociate and recurse *)
      if is_plus (rand tm) then
        (LASSOC_ADD_CONV THENC LAND_CONV S_AND_G_MULT THENC S_AND_G_MULT) tm
      else if is_mult (rand tm) andalso not (is_var (rand (rand tm))) then
        (RAND_CONV LINEAR_MULT THENC prepare_insertion) tm
      else
        SORT_AND_GATHER1_CONV tm
in
  if is_plus tm then
    LAND_CONV S_AND_G_MULT THENC prepare_insertion
  else if is_mult tm andalso not (is_var (rand tm)) then
    CooperMath.LINEAR_MULT THENC S_AND_G_MULT
  else
    ALL_CONV
end tm




(* ----------------------------------------------------------------------
    NEG_SUM_CONV tm

    tm of form ~(cv + dv + ev + n)
   ---------------------------------------------------------------------- *)

fun NEG_SUM_CONV tm =
    ((REWR_CONV INT_NEG_ADD THENC BINOP_CONV NEG_SUM_CONV) ORELSEC
     (REWR_CONV INT_NEG_LMUL THENC
      TRY_CONV (LAND_CONV (REWR_CONV INT_NEGNEG))) ORELSEC
     TRY_CONV (REWR_CONV INT_NEGNEG)) tm


(* ----------------------------------------------------------------------
    MOVE_VCOEFF_TO_FRONT v tm

    moves the summand featuring variable v to the front of the sum
    tm.  Of course, this doesn't preserve the order in the sum.
   ---------------------------------------------------------------------- *)

(* ``!x y. x = y + (x + ~y)`` *)
val front_put_thm = prove(
  ``!x y. x = y + (x + ~y)``,
  REPEAT GEN_TAC THEN
  CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV INT_ADD_COMM))) THEN
  REWRITE_TAC [INT_ADD_ASSOC, INT_ADD_RINV, INT_ADD_LID]);
fun MOVE_VCOEFF_TO_FRONT v tm = let
  val cv = find_summand v tm
  val th = SPECL [tm,cv] front_put_thm
in
  K th THENC RAND_CONV (RAND_CONV NEG_SUM_CONV THENC SORT_AND_GATHER1_CONV)
end tm



end
