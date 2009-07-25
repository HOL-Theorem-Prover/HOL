structure OmegaMath :> OmegaMath = struct

open HolKernel boolLib intSyntax integerTheory int_arithTheory
open CooperMath
local open OmegaTheory in end

(* Fix the grammar used by this file *)
structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars int_arith_grammars
end
open Parse

val REWRITE_CONV = GEN_REWRITE_CONV TOP_DEPTH_CONV bool_rewrites


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

    If there are no variables, will evaluation 0 = rn to true or false.

    If there is nothing to eliminate, then return QConv.UNCHANGED.
   ---------------------------------------------------------------------- *)

exception Foo
fun gcd_eq_check tm = let
  open Arbint
  val INT_RING_CONV =
      EQT_ELIM o (REWRITE_CONV [INT_LDISTRIB, INT_MUL_ASSOC] THENC REDUCE_CONV)
  val r = rand tm
  val summands = strip_plus r
  val (vars, numpart) = front_last summands
  val _ = not (null vars) orelse raise Foo
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
end tm handle Foo => REDUCE_CONV tm

(* ----------------------------------------------------------------------
    gcd_le_check tm

    performs a "gcd check" for terms of the form
      0 <= (c1 * v1) + (c2 * v2) + .. + (cn * vn) + n
    if there are no variables, evaluates 0 <= n to true or false.
   ---------------------------------------------------------------------- *)

fun gcd_le_check tm = let
  open Arbint
  val INT_RING_CONV =
      EQT_ELIM o (REWRITE_CONV [INT_LDISTRIB, INT_MUL_ASSOC] THENC REDUCE_CONV)
  val r = rand tm
  val (varpart, numpart) = dest_plus r handle HOL_ERR _ => raise Foo
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
end tm handle Foo => REDUCE_CONV tm

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

    Eliminates summands which have zero coefficients, as long as the
    term being inserted into is in normal form, complete with numeral
    as rightmost summand.

   ---------------------------------------------------------------------- *)

fun SORT_AND_GATHER1_CONV tm =
    (RTOP_TWO_CONV PAIRWISE_GATHER_CONV THENC
     TRY_CONV (LAND_CONV SORT_AND_GATHER1_CONV) THENC
     CHECK_RZERO_CONV) tm

(* ----------------------------------------------------------------------
    INTERNAL_SG1_CONV tm

    does the insertion sort of SORT_AND_GATHER1_CONV, but doesn't
    attempt to normalise zero-coefficients.

   ---------------------------------------------------------------------- *)

fun INTERNAL_SG1_CONV tm =
    (RTOP_TWO_CONV PAIRWISE_GATHER_CONV THENC
     TRY_CONV (LAND_CONV INTERNAL_SG1_CONV)) tm

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
        INTERNAL_SG1_CONV tm
in
  if is_plus tm then
    LAND_CONV SORT_AND_GATHER_CONV THENC prepare_insertion THENC
    addzero THENC CHECK_RZERO_CONV
  else
    addzero THENC CHECK_RZERO_CONV
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

(* ----------------------------------------------------------------------
    NORMALISE_MULT tm

    normalises the multiplicative term tm, gathering up coefficients,
    and ususally turning it into the form n * (v1 * v2 * ... vn),
    where n is a numeral and the v's are the other multiplicands in
    the term, sorted into the order specified by Term.compare.  Works
    over both :num and :int.  Negations are also lifted out, so that only
    the numeral is negated.

    If the term is a multiplication of numerals, will reduce to just
    one numeral.  If the term includes no numerals, no extra 'n' will
    be introduced but the multiplicands will be sorted.

    Fails if the term is not a multiplication.

   ---------------------------------------------------------------------- *)

fun NORMALISE_MULT0 t = let
  open arithmeticTheory
  (* t is a multiplication term, over either :num or :int *)
  val (dest, strip, mk, listmk, AC, is_lit, MULT_LID, one_tm) =
      if numSyntax.is_mult t then
        (numSyntax.dest_mult,
         numSyntax.strip_mult,
         numSyntax.mk_mult,
         numSyntax.list_mk_mult,
         EQT_ELIM o AC_CONV (MULT_ASSOC, MULT_COMM),
         numSyntax.is_numeral,
         GSYM arithmeticTheory.MULT_LEFT_1,
         numSyntax.term_of_int 1)
      else if intSyntax.is_mult t then
        (intSyntax.dest_mult,
         intSyntax.strip_mult,
         intSyntax.mk_mult,
         intSyntax.list_mk_mult,
         EQT_ELIM o AC_CONV (INT_MUL_ASSOC, INT_MUL_COMM),
         intSyntax.is_int_literal,
         GSYM INT_MUL_LID,
         intSyntax.one_tm)
      else raise ERR "NORMALISE_MULT" "Term not a multiplication"
  val ms = strip t
  val (nums, others) = partition is_lit ms
  fun sort nums others t = let
    val newt = mk(listmk nums, listmk (Listsort.sort Term.compare others))
  in
    K (AC(mk_eq(t,newt))) THENC LAND_CONV REDUCE_CONV
  end t
in
  if null others then REDUCE_CONV
  else if null nums then
    REWR_CONV MULT_LID THENC sort [one_tm] others
  else
    sort nums others
end t

val NORMALISE_MULT  =
    NORMALISE_MULT0 THENC REWRITE_CONV [GSYM INT_NEG_RMUL, GSYM INT_NEG_LMUL,
                                        INT_NEGNEG] THENC
    REWRITE_CONV [INT_NEG_LMUL] THENC
    TRY_CONV (FIRST_CONV (map REWR_CONV [arithmeticTheory.MULT_LEFT_1,
                                         INT_MUL_LID]))


(* ----------------------------------------------------------------------
    leaf_normalise t

    Takes a "leaf term" (a relational operator over integer values) and
    normalises it to either an equality, a <= or a disjunction of two
    (un-normalised) <= leaves.  (The latter happens if called onto
    normalise ~(x = y)).
   ---------------------------------------------------------------------- *)

fun EVERY_SUMMAND c tm =
  if is_plus tm then BINOP_CONV (EVERY_SUMMAND c) tm
  else c tm

local
  val lt_elim = SPEC_ALL int_arithTheory.less_to_leq_samer
  val tac = REWRITE_TAC [GSYM int_le, INT_NOT_LE, lt_elim, int_gt,
                         INT_LE_RADD, int_ge, GSYM INT_LE_ANTISYM,
                         DE_MORGAN_THM]
  val not_le = prove(``~(x <= y) = (y + 1i <= x)``, tac)
  val not_lt = prove(``~(x:int < y) = y <= x``, tac)
  val not_gt = prove(``~(x:int > y) = x <= y``, tac)
  val not_ge = prove(``~(x >= y) = x + 1i <= y``, tac)
  val not_eq = prove(``~(x = y:int) = y + 1 <= x \/ x + 1 <= y``, tac)
  val ge_elim = prove(``x:int >= y = y <= x``, tac)
  val gt_elim = prove(``x > y = y + 1i <= x``, tac)
  val eq_elim = prove(``(x:int = y) = (x <= y /\ y <= x)``, tac)
  val mult1 = GSYM INT_MUL_LID
in

fun MULT1_CONV tm = if not (is_mult tm) andalso not (is_int_literal tm) then
                      REWR_CONV mult1 tm
                    else ALL_CONV tm

val sum_normalise =
    REWRITE_CONV [INT_NEG_ADD, INT_LDISTRIB, INT_RDISTRIB,
                  INT_NEG_LMUL, INT_NEGNEG, INT_NEG_0,
                  int_sub] THENC
    EVERY_SUMMAND (TRY_CONV NORMALISE_MULT THENC MULT1_CONV) THENC
    REWRITE_CONV [GSYM INT_NEG_RMUL, GSYM INT_NEG_LMUL,
                  INT_NEGNEG] THENC
    REWRITE_CONV [INT_NEG_LMUL] THENC
    SORT_AND_GATHER_CONV

val norm_divides =
    LAND_CONV CooperMath.REDUCE_CONV THENC
    RAND_CONV sum_normalise THENC
    REWRITE_CONV [INT_DIVIDES_NEG] THENC
    CooperMath.minimise_divides THENC
    CooperMath.check_divides

fun normalise_numbers tm = let
  val MK_LEQ =
    TRY_CONV (FIRST_CONV (map REWR_CONV [lt_elim, not_le, not_lt, not_gt,
                                         not_ge, ge_elim, gt_elim])) THENC
    (REWR_CONV int_arithTheory.le_move_all_right ORELSEC
     REWR_CONV int_arithTheory.eq_move_all_right)
  val base_normaliser = RAND_CONV sum_normalise THENC gcd_check
in
  if (is_leq tm orelse is_eq tm) andalso lhand tm = zero_tm then
    if is_plus (rand tm) then let
      val (rl, rr) = dest_plus (rand tm)
      fun mult_ok acc tm = let
        val (c,v) = dest_mult tm
      in
        is_int_literal c andalso is_var v andalso
        (case acc of
           NONE => true
         | SOME v0 => Term.compare(v0, v) = GREATER)
      end handle HOL_ERR _ => false
      fun rhs_ok acc tm = let
        val (l,r) = dest_plus tm
      in
        mult_ok acc r andalso rhs_ok (SOME (rand r)) l
      end handle HOL_ERR _ => mult_ok acc tm
    in
      if is_int_literal rr andalso rhs_ok NONE rl then
        if is_eq tm andalso is_negated (lhand (hd (strip_plus rl))) then
          REWR_CONV (GSYM INT_EQ_NEG) THENC
          LAND_CONV (REWR_CONV INT_NEG_0) THENC base_normaliser
        else NO_CONV
      else base_normaliser
    end
    else if is_int_literal (rand tm) then CooperMath.REDUCE_CONV
         else base_normaliser
  else if is_divides tm then
    CHANGED_CONV norm_divides
  else if is_neg tm andalso is_divides (rand tm) then
    CHANGED_CONV (RAND_CONV norm_divides)
  else MK_LEQ THENC base_normaliser
end tm

val leaf_normalise =
    (REWR_CONV not_eq THENC BINOP_CONV normalise_numbers) ORELSEC
    normalise_numbers
end (* local *)


(* ----------------------------------------------------------------------
    PRENEX_CONV t

    a prenexer which differs from Canon.PRENEX_CONV only in that it pulls
    quantifiers out of the then or else branches of conditional
    expressions.
   ---------------------------------------------------------------------- *)

val tac = COND_CASES_TAC THEN REWRITE_TAC []
val COND_FA_THEN_THM =
    prove(``(if p then !x:'a. P x else q) = !x. if p then P x else q``, tac)
val COND_FA_ELSE_THM =
    prove(``(if p then q else !x:'a. P x) = !x. if p then q else P x``, tac)
val COND_EX_THEN_THM =
    prove(``(if p then ?x:'a. P x else q) = ?x. if p then P x else q``, tac)
val COND_EX_ELSE_THM =
    prove(``(if p then q else ?x:'a. P x) = ?x. if p then q else P x``, tac)

fun COND_FA_THEN tm = let
  val (g, t, e) = dest_cond tm
  val (v, _) = dest_forall t
in
  HO_REWR_CONV COND_FA_THEN_THM THENC RAND_CONV (ALPHA_CONV v)
end tm
fun COND_FA_ELSE tm = let
  val (g, t, e) = dest_cond tm
  val (v, _) = dest_forall e
in
  HO_REWR_CONV COND_FA_ELSE_THM THENC RAND_CONV (ALPHA_CONV v)
end tm
fun COND_EX_THEN tm = let
  val (g, t, e) = dest_cond tm
  val (v, _) = dest_exists t
in
  HO_REWR_CONV COND_EX_THEN_THM THENC RAND_CONV (ALPHA_CONV v)
end tm
fun COND_EX_ELSE tm = let
  val (g, t, e) = dest_cond tm
  val (v, _) = dest_exists e
in
  HO_REWR_CONV COND_EX_ELSE_THM THENC RAND_CONV (ALPHA_CONV v)
end tm

val PRENEX_CONV =
    TOP_DEPTH_CONV
    (FIRST_CONV [NOT_FORALL_CONV, NOT_EXISTS_CONV,
                 AND_FORALL_CONV, OR_EXISTS_CONV,
                 RIGHT_AND_FORALL_CONV, LEFT_AND_FORALL_CONV,
                 RIGHT_AND_EXISTS_CONV, LEFT_AND_EXISTS_CONV,
                 RIGHT_IMP_FORALL_CONV, LEFT_IMP_FORALL_CONV,
                 RIGHT_IMP_EXISTS_CONV, LEFT_IMP_EXISTS_CONV,
                 RIGHT_OR_FORALL_CONV,  LEFT_OR_FORALL_CONV,
                 RIGHT_OR_EXISTS_CONV,  LEFT_OR_EXISTS_CONV,
                 COND_FA_THEN, COND_FA_ELSE, COND_EX_THEN, COND_EX_ELSE])

(* generate_nway_casesplit n: generates the theorem
      P v1 .. vn = P F F .. F F \/ P F F .. F T \/ P F F .. T F \/
                   P F F .. T T \/ ... \/ P T T .. F F \/
                   P T T .. F T \/ P T T .. T F \/ P T T .. T T
   that is, the 2^n possibilities for n boolean variables.
   Performance is exponential, so beware *)

fun generate_nway_casesplit n = let
  val _ = n >= 1 orelse raise Fail "generate_nway_casesplit: n < 1"
  fun genty n = if n = 1 then bool --> bool
                else bool --> (genty (n - 1))
  val P_ty = genty n
  val P_t = mk_var("P", P_ty)
  fun gen_cases (m, vs, t) =
      if m < n then let
          val v = mk_var("v"^Int.toString m, bool)
          val vT = (m + 1, v::vs, mk_comb(t, T))
          val vF = (m + 1, (mk_neg v)::vs, mk_comb(t, F))
        in
          mk_disj(gen_cases vT, gen_cases vF)
        end
      else
        mk_conj(t, list_mk_conj vs)
  val RHS = gen_cases (0, [], P_t)
  fun gen_vars n acc =
      if n < 0 then acc
      else gen_vars (n - 1) (mk_var("v"^Int.toString n, bool)::acc)
  val vars = gen_vars (n - 1) []
in
  GEN P_t (GENL vars
                (prove(mk_eq(list_mk_comb(P_t, vars), RHS),
                       MAP_EVERY BOOL_CASES_TAC vars THEN REWRITE_TAC [])))
end

fun UNBETA_LIST tlist =
    case tlist of
      [] => ALL_CONV
    | (t::ts) => UNBETA_CONV t THENC RATOR_CONV (UNBETA_LIST ts)



(* ----------------------------------------------------------------------
    reveal_a_disj t

    if t is "morally" a disjunction, map it clear that this is the case
    by rewriting appropriately.
   ---------------------------------------------------------------------- *)

val not_beq = prove(
  ``~(b1 = b2) = b1 /\ ~b2 \/ ~b1 /\ b2``,
  BOOL_CASES_TAC ``b1:bool`` THEN REWRITE_TAC []);
val beq = prove(
  ``(b1 = b2) = b1 /\ b2 \/ ~b1 /\ ~b2``,
  BOOL_CASES_TAC ``b1:bool`` THEN REWRITE_TAC []);

fun reveal_a_disj tm =
    if is_disj tm then ALL_CONV tm
    else
      (FIRST_CONV (map REWR_CONV [beq, not_beq, IMP_DISJ_THM,
                                  CooperThms.NOT_AND]) ORELSEC
       (REWR_CONV CooperThms.NOT_NOT_P THENC reveal_a_disj)) tm


(* ----------------------------------------------------------------------
    normalise_guard t

    t is a conditional expression with a single leaf term as its guard.
    If this is a <= leaf, flip its sense (and the corresponding then and
    else branches) so that the coefficient of the first variable is
    positive
   ---------------------------------------------------------------------- *)

val FLIP_COND = prove(
  ``(if g then t:'a else e) = if ~g then e else t``,
  COND_CASES_TAC THEN REWRITE_TAC []);

fun normalise_guard t = let
  val _ = dest_cond t
  fun make_guard_positive t = let
    val (g, _, _) = dest_cond t
  in
    if is_leq g then let
        val t1 = hd (strip_plus (rand g))
      in
        if is_negated (#1 (dest_mult t1)) handle HOL_ERR _ => false then
          REWR_CONV FLIP_COND THENC
          RATOR_CONV (LAND_CONV leaf_normalise)
        else
          ALL_CONV
      end
    else
      ALL_CONV
  end t
in
  RATOR_CONV (LAND_CONV leaf_normalise) THENC make_guard_positive
end t

fun TOP_SWEEP_ONCE_CONV c t =
    (TRY_CONV c THENC SUB_CONV (TOP_SWEEP_ONCE_CONV c)) t

val normalise_guards = TOP_SWEEP_ONCE_CONV normalise_guard

(* ----------------------------------------------------------------------
    cond_removal0 t

    If t contains conditional expressions where guards of these appear
    more than once, then do a case-split on these guard expressions at
    the top level.
    E.g.,
        (if g then t else e) /\ (if g then t' else e')
    will turn into
        g /\ t /\ t' \/ g /\ e /\ e'

   ---------------------------------------------------------------------- *)

fun cond_removal0 t = let
  open Binarymap
  val condexps = List.map (hd o #2 o strip_comb) (find_terms is_cond t)
  val empty_map = mkDict Term.compare
  fun my_insert(g, m) =
      case peek(m,g) of
        NONE => insert(m, g, 1)
      | SOME n => insert(m, g, n + 1)
  val final_map = List.foldl my_insert empty_map condexps
  fun find_gt2 (t,n,l) = if n >= 2 then t::l else l
  val gt2_guards = foldl find_gt2 [] final_map
  val n = assert (curry op < 0) (length gt2_guards)
  val case_split = generate_nway_casesplit n
in
  UNBETA_LIST (List.rev gt2_guards) THENC
  REWR_CONV case_split THENC
  EVERY_DISJ_CONV (LAND_CONV LIST_BETA_CONV THENC REWRITE_CONV [])
end t

(* ----------------------------------------------------------------------
    cond_removal t

    Perform cond_removal0 on all of t's disjunctions, not being put off
    by disjunctions hiding as negated conjunctions.
   ---------------------------------------------------------------------- *)

fun cond_removal t =
    ((reveal_a_disj THENC BINOP_CONV cond_removal) ORELSEC
     (normalise_guards THENC cond_removal0)) t


(* ----------------------------------------------------------------------
    calculate_range_disjunct tm

    tm is of form ?i. (0 <= i /\ i <= u) /\ ...
    transform this into an appropriate number of disjuncts (or possibly
    false, if u < 0), of the form
       P(0) \/ P(1) \/ ... \/ P(u)
   ---------------------------------------------------------------------- *)

val refl_case = prove(
  ``!u P. (?i:int. (u <= i /\ i <= u) /\ P i) = P u``,
  REWRITE_TAC [INT_LE_ANTISYM] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC [] THEN Q.EXISTS_TAC `u` THEN
  ASM_REWRITE_TAC []);
val nonrefl_case = prove(
  ``!lo hi P. (?i:int. (lo <= i /\ i <= hi) /\ P i) =
              lo <= hi /\ (P lo \/ ?i. (lo + 1 <= i /\ i <= hi) /\ P i)``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    Q.ASM_CASES_TAC `i = lo` THENL [
      POP_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC [],
      REWRITE_TAC [LEFT_AND_OVER_OR] THEN
      DISJ2_TAC THEN CONJ_TAC THENL [
        IMP_RES_TAC INT_LE_TRANS,
        ALL_TAC
      ] THEN Q.EXISTS_TAC `i` THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [GSYM int_arithTheory.less_to_leq_samer] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [INT_LE_LT]) THEN
      POP_ASSUM_LIST (MAP_EVERY STRIP_ASSUME_TAC) THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM (fn th => MP_TAC th THEN REWRITE_TAC [] THEN NO_TAC)
    ],
    Q.EXISTS_TAC `lo` THEN ASM_REWRITE_TAC [INT_LE_REFL],
    Q.EXISTS_TAC `i` THEN ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC INT_LE_TRANS THEN Q.EXISTS_TAC `lo + 1` THEN
    ASM_REWRITE_TAC [INT_LE_ADDR] THEN CONV_TAC CooperMath.REDUCE_CONV
  ]);


fun calculate_range_disjunct tm = let
  val (i, body) = dest_exists tm
  fun recurse tm =
      ((REWR_CONV refl_case THENC BETA_CONV) ORELSEC
       (REWR_CONV nonrefl_case THENC
        LAND_CONV CooperMath.REDUCE_CONV THENC
        (REWR_CONV CooperThms.F_and_l ORELSEC
         (REWR_CONV CooperThms.T_and_l THENC
          FORK_CONV(BETA_CONV,
                    BINDER_CONV (LAND_CONV
                                   (LAND_CONV CooperMath.REDUCE_CONV)) THENC
                    recurse))))) tm
in
  BINDER_CONV (RAND_CONV (UNBETA_CONV i)) THENC recurse
end tm

(* ----------------------------------------------------------------------
    rel_coeff v tm

    returns the coefficient (a term that is a numeral) of variable v in
    relational term tm.  A relational term is of the form
       0 <relop>  r1 + ... + rn + n
    where all of the ri are numerals multiplied by variables, and the n
    is a bare numerals.  Further, it is assumed that any given variable
    occurs once.  Returns zero as the coefficient of a variable not
    present.
   ---------------------------------------------------------------------- *)

fun rel_coeff v tm = let
  fun recurse t = let
    val (l,r) = dest_plus t
  in
    if rand r = v then lhand r
    else recurse l
  end handle HOL_ERR _ => if rand t = v then lhand t else zero_tm
in
  recurse (lhand (rand tm))
end


(* ----------------------------------------------------------------------
    find_eliminable_equality vset acc conjunctions

    finds an equality that can be eliminated from the conjunctions.  This
    has to be done wrt a set of variables that have scope over the
    conjunctions.  Returns a new version of acc, the fields of which are
      (leastv, conj, rest)
    of types
      ((term * Arbint) option * term option * term list)

    leastv is the variable that has the least coefficient coupled with
    that least coefficient.  NONE if there is none such.

    conj is the conjunct in which leastv was found to be least.  Again,
    NONE if there is nothing eliminable.

    rest is the list of all the unsatisfactory conjuncts.

   ---------------------------------------------------------------------- *)

fun find_eliminable_equality vs (acc as (leastv, conj, rest)) cs = let
  fun ocons NONE xs = xs | ocons (SOME x) xs = x::xs
  fun doclause (acc as (leastv, conj, rest)) unexamined c k = let
    val fvs = FVL [lhand (rand c)] empty_tmset
    val i = HOLset.intersection(vs,fvs)
    fun check_mins (v, (leastv, changed)) = let
      open Arbint
      val v_coeff = abs (int_of_term (rel_coeff v c))
    in
      case leastv of
        NONE => (SOME(v,v_coeff), true)
      | SOME(v', min) => if v_coeff < min then (SOME (v,v_coeff), true)
                         else (leastv, changed)
    end
    (* if this clause isn't interesting, we need to continue (by calling k)
       but we also need to put c onto the list of things seen so far; here's
       the "unchanged" accumulated state that we'll pass to k in these
       cases *)
    val unchanged_acc = (leastv, conj, c::rest)
  in
    case HOLset.numItems i of
      0 => k unchanged_acc
    | 1 => let
        val v = hd (HOLset.listItems i)
      in
        if Arbint.abs (int_of_term (rel_coeff v c)) = Arbint.one then
          (SOME (v,Arbint.one), SOME c, ocons conj rest @ unexamined)
        else k unchanged_acc
      end
    | sz => let
      in
        case HOLset.foldl check_mins (leastv, false) i of
          (least', true) => k (least', SOME c, ocons conj rest)
        | (_, false) => k unchanged_acc
      end
  end
in
  case cs of
    [] => acc
  | (c::cs) => if not (is_eq c) then
                 find_eliminable_equality vs (leastv,conj,c::rest) cs
               else
                 doclause acc cs c
                 (fn acc' => find_eliminable_equality vs acc' cs)
end

(* ----------------------------------------------------------------------
    sum_to_sumc tm

    takes tm (a sum of the form t1 + .. + tn) and returns a theorem of
    the form
       |- tm = sumc cs vs
    where cs is a list of numeral coefficients, and vs a list of
    variables (except that one of the vs will actually be the numeral 1).
   ---------------------------------------------------------------------- *)

val sumc_t = ``Omega$sumc``
fun sum_to_sumc tm = let
  fun dest_m t = dest_mult t handle HOL_ERR _ => (t, one_tm)
  val (cs, vs) = ListPair.unzip (map dest_m (strip_plus tm))
  fun mk_list l = listSyntax.mk_list(l, int_ty)
  val (cs_t, vs_t) = (mk_list ## mk_list) (cs, vs)
  val sumc_t = list_mk_comb(sumc_t, [cs_t, vs_t])
in
  SYM ((REWRITE_CONV [INT_ADD_ASSOC, OmegaTheory.sumc_def, INT_MUL_RID] THENC
        REWR_CONV INT_ADD_RID) sumc_t)
end

(* ----------------------------------------------------------------------
    sumc_eliminate reducer tm

    Takes a term of the form
      sumc (MAP f cs) vs
    and turns it into a regular sum, assuming that the last v will actually
    be the integer 1, using the reducer parameter to evaluate each
    instance of the application of f to c.
   ---------------------------------------------------------------------- *)

fun sumc_eliminate reducer tm = let
  open OmegaTheory
  fun recurse tm =
      if listSyntax.is_nil (rand (rand tm)) then
        (REWR_CONV sumc_singleton THENC reducer) tm
      else
        (REWR_CONV sumc_nonsingle THENC LAND_CONV (LAND_CONV reducer) THENC
         RAND_CONV recurse) tm
in
  if listSyntax.is_nil (rand tm) then
    REWRITE_CONV [listTheory.MAP, OmegaTheory.sumc_def]
  else
    recurse
end tm


(* ----------------------------------------------------------------------
    eliminate_equality v tm

    Takes a variable v, and an equality tm, of the general form
        0 = r1 + .. + rn
    and returns a theorem which is an equation of the general form

      |- tm = ?s. (v = ....) /\ tm

   ---------------------------------------------------------------------- *)

val SYM_EQ_NEG = GSYM INT_EQ_NEG
fun eliminate_equality v tm = let
  open OmegaTheory
  val instantiate_eqremoval =
      C MP TRUTH o CONV_RULE (LAND_CONV REDUCE_CONV) o
      PART_MATCH (lhand o rand) equality_removal
  val rhs_th = MOVE_VCOEFF_TO_FRONT v (rand tm)
  val cv_t = lhand (rand (concl rhs_th))
  val dealwith_negative_coefficient =
      if is_negated (lhand cv_t) then
        REWR_CONV SYM_EQ_NEG THENC
        FORK_CONV (REWR_CONV INT_NEG_0, NEG_SUM_CONV)
      else ALL_CONV
in
  RAND_CONV (K rhs_th) THENC dealwith_negative_coefficient THENC
  RAND_CONV (RAND_CONV sum_to_sumc) THENC instantiate_eqremoval THENC
  BINDER_CONV
     (LAND_CONV (* new equality conjunct *)
       (RAND_CONV (* rhs of equality *)
          (LAND_CONV (LAND_CONV REDUCE_CONV) THENC
           RAND_CONV (* sumc term *)
             (LAND_CONV (LAND_CONV (* first arg of MAP *)
                           (BINDER_CONV (RAND_CONV REDUCE_CONV THENC
                                         REWRITE_CONV [modhat_def] THENC
                                         REDUCE_CONV))) THENC
              sumc_eliminate (BETA_CONV THENC REDUCE_CONV)) THENC
             REWRITE_CONV [INT_MUL_LZERO, INT_ADD_RID, INT_ADD_ASSOC,
                           INT_ADD_LID])) THENC
     RAND_CONV (* old equality conjunct *)
       (REWRITE_CONV [sumc_def] THENC
        REWRITE_CONV [INT_MUL_RID, INT_ADD_ASSOC] THENC
        RAND_CONV (REWR_CONV INT_ADD_RID)))
end tm

val eliminate_equality =
    fn x => (*Profile.profile "eliminate_eq"*) (eliminate_equality x)




(* ----------------------------------------------------------------------
    OmegaEq : term -> thm

    Put all of the above together
   ---------------------------------------------------------------------- *)

fun push_exvar_to_bot v tm = let
  val (bv, body) = dest_exists tm
in
  if bv = v then (SWAP_VARS_CONV THENC
                  BINDER_CONV (push_exvar_to_bot v) ORELSEC
                  ALL_CONV)
  else (BINDER_CONV (push_exvar_to_bot v))
end tm

val EX_REFL = EQT_INTRO (SPEC_ALL EXISTS_REFL)
fun OmegaEq t = let
  val (exvars, body) = strip_exists t
  val exv_set = HOLset.addList(empty_tmset, exvars)
  val gcd_check = (*Profile.profile "gcd_check"*) gcd_check
  val _ = length exvars > 0 orelse
          raise ERR "OmegaEq" "Term not existentially quantified"
  val conjns = strip_conj body
  val (vwithleast, conj, rest) =
      find_eliminable_equality exv_set (NONE, NONE, []) conjns
  val _ = isSome vwithleast orelse raise UNCHANGED
  val (to_elim, elimc) = valOf vwithleast
  val c = valOf conj
  val newrhs = if null rest then c else mk_conj(c, list_mk_conj rest)
  val reordered_thm =
      EQT_ELIM (AC_CONV(CONJ_ASSOC, CONJ_COMM) (mk_eq(body, newrhs)))
  val bring_veq_to_top = let
    val (rCONV, finisher) = if null rest then (I, ALL_CONV)
                            else (LAND_CONV,
                                  LEFT_AND_EXISTS_CONV THENC
                                  BINDER_CONV (REWR_CONV (GSYM CONJ_ASSOC)))
  in
      if elimc = Arbint.one then
        rCONV (phase2_CONV to_elim THENC LAND_CONV (REWR_CONV INT_MUL_LID))
      else
        rCONV (eliminate_equality to_elim) THENC finisher
  end
  fun ifVarsRemain c t = if is_exists t then c t else ALL_CONV t
  val (absify, unwinder) =
      if null rest andalso elimc = Arbint.one then
        (ALL_CONV, REWR_CONV EX_REFL)
      else (STRIP_QUANT_CONV (RAND_CONV (UNBETA_CONV to_elim)),
            REWR_CONV UNWIND_THM2 THENC BETA_CONV)
in
  STRIP_QUANT_CONV (K reordered_thm THENC bring_veq_to_top THENC absify) THENC
  push_exvar_to_bot to_elim THENC LAST_EXISTS_CONV unwinder THENC
  STRIP_QUANT_CONV
    (BLEAF_CONV (op THENC)
                (TRY_CONV (RAND_CONV S_AND_G_MULT THENC
                           TRY_CONV gcd_check))) THENC
  REWRITE_CONV [EXISTS_SIMP] THENC
  ifVarsRemain OmegaEq
end t

(* some test terms:

time OmegaEq   ``?x y z. 0 <= 2 * x + ~3 * y + 5 * z + 10 /\
                         (0  = 3 * x + 4 * y + ~7 * z + 3)``;

time OmegaEq   ``?i j. 0 <= 1 * i + 0 /\ 0 <= 1 * j + 0 /\
                       (0 = 3 * i + 5 * j + ~1 * n + 0)``;

time OmegaEq   ``?i j. (0 = 3 * i + 5 * j + ~1 * n + 0)``;

time OmegaEq   ``?i j. (0 = 3 * i + 6 * j + ~1 * n + 0)``;

time OmegaEq   ``?x y. (0 = 2 * x + 3 * y + 2) /\ (0 = 2 * x + 3 * y + 4)``;

time OmegaEq   ``?n. (0 = 1 * n + 1) /\ 0 <= 1 * n + 0``;

*)


(* ----------------------------------------------------------------------
    eliminate_positive_divides t

    t is a term of the form ?x1 .. xn. body, where body is a conjunction
    of leaves, possibly including divisibility relations (negated or
    positive).  This function writes away those (positive) divisibility
    relations of the form   d | exp   where exp includes at least one
    variable from x1 .. xn.
   ---------------------------------------------------------------------- *)

fun eliminate_positive_divides t = let
  val (vs, body) = strip_exists t
  fun find_divides tm = let
  in
    if is_conj tm then
      (LAND_CONV find_divides THENC LEFT_AND_EXISTS_CONV) ORELSEC
      (RAND_CONV find_divides THENC RIGHT_AND_EXISTS_CONV)
    else if is_divides tm andalso
            not (null (intersect vs (free_vars (rand tm))))
    then
      REWR_CONV INT_DIVIDES THENC
      BINDER_CONV leaf_normalise
    else
      NO_CONV
  end tm
in
  STRIP_QUANT_CONV find_divides THENC OmegaEq THENC
  REWRITE_CONV [] THENC
  TRY_CONV eliminate_positive_divides
end t

(* ----------------------------------------------------------------------
    eliminate_negative_divides t

    t is a term of the form ?x1 .. xn. body, where body is a conjunction
    of leaves, possibly including divisibility relations (negated or
    positive).  This function writes away those negated divisibility
    relations of the form ~(d | exp) where exp includes at least one
    variable from x1 .. xn.  It introduces case splits.
   ---------------------------------------------------------------------- *)

fun eliminate_negative_divides t = let
  val (vs, _) = strip_exists t
  fun elim_ndivides tm = let
    val (c, d) = dest_divides (rand tm)
    val c_neq_0 = EQT_ELIM (CooperMath.REDUCE_CONV
                              (mk_neg(mk_eq(rand c, numSyntax.zero_tm))))
  in
    MP (SPECL [rand c, d] int_arithTheory.NOT_INT_DIVIDES_POS) c_neq_0
  end
  fun rdistrib tm =
      TRY_CONV (REWR_CONV RIGHT_AND_OVER_OR THENC RAND_CONV rdistrib) tm
  fun ldistrib tm =
      TRY_CONV (REWR_CONV LEFT_AND_OVER_OR THENC RAND_CONV ldistrib) tm
  fun find_divides tm = let
  in
    if is_conj tm then
      (LAND_CONV find_divides THENC rdistrib) ORELSEC
      (RAND_CONV find_divides THENC ldistrib)
    else if is_neg tm andalso
            not (null (intersect vs (free_vars (rand (rand tm)))))
    then
      elim_ndivides THENC
      BINDER_CONV (LAND_CONV (RAND_CONV (CooperMath.REDUCE_CONV))) THENC
      calculate_range_disjunct THENC
      EVERY_DISJ_CONV (RAND_CONV SORT_AND_GATHER1_CONV)
    else NO_CONV
  end tm
  fun push tm = let
    val (vs, body) = strip_exists tm
  in
    CooperSyntax.push_in_exists THENC
    EVERY_DISJ_CONV (RENAME_VARS_CONV (map (#1 o dest_var) vs))
  end tm
in
  STRIP_QUANT_CONV find_divides THENC push THENC
  TRY_CONV eliminate_negative_divides
end t

end (* struct *)
