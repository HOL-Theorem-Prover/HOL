structure Cooper :> Cooper =
struct

open HolKernel boolLib integerTheory Parse
     arithmeticTheory intSyntax int_arithTheory intSimps;

open CooperSyntax CooperThms

local open listTheory in end;

infix THEN THENC THENL |-> ## ORELSEC
infixr -->

val (Type,Term) = parse_from_grammars integerTheory.integer_grammars;
fun -- q x = Term q
fun == q x = Type q


val ERR = mk_HOL_ERR "Cooper";


val REWRITE_CONV = GEN_REWRITE_CONV Conv.TOP_DEPTH_CONV bool_rewrites


fun EXIN_CONJ_CONV t = let
  val (var,bdy) = dest_exists t
  val conjs = strip_conj bdy
in
  case partition (free_in var) conjs of
    ([], _) => REWR_CONV EXISTS_SIMP t
  | (_, []) => NO_CONV t
  | (there, notthere) => let
      val newbdy = mk_conj(list_mk_conj there, list_mk_conj notthere)
      val newthm = EQT_ELIM(AC_CONV (CONJ_ASSOC, CONJ_COMM)
                            (mk_eq(bdy, newbdy)))
    in
      BINDER_CONV (K newthm) THENC EXISTS_AND_CONV
    end t
end





val remove_negated_vars = let
  fun remove_negated tm = let
    (* turn ~ var into ~1 * var *)
    val t0 = dest_negated tm (* exception raised when term not a negation
                                will be trapped appropriately by DEPTH_CONV
                                below *)
  in
    if is_var t0 then
      REWR_CONV INT_NEG_MINUS1 tm
    else
      NO_CONV tm
  end
in
  DEPTH_CONV remove_negated
end

fun ADDITIVE_TERMS_CONV c tm =
  if is_disj tm orelse is_conj tm then
    BINOP_CONV (ADDITIVE_TERMS_CONV c) tm
  else if is_neg tm then RAND_CONV (ADDITIVE_TERMS_CONV c) tm
  else if is_less tm orelse is_divides tm orelse is_eq tm then
    BINOP_CONV c tm
  else ALL_CONV tm


val cooper_compset = intSimps.int_compset()
val _ = computeLib.add_thms [gcdTheory.GCD_EFFICIENTLY] cooper_compset
val REDUCE_CONV = computeLib.CBV_CONV cooper_compset

(*---------------------------------------------------------------------------*)
(* Function to compute the Greatest Common Divisor of two integers.          *)
(*---------------------------------------------------------------------------*)

fun gcd (i,j) = let
  exception non_neg
  open Arbint
  fun gcd' (i,j) = let
    val r = (i mod j)
  in
    if (r = zero) then j else gcd' (j,r)
  end
in
  (if ((i < zero) orelse (j < zero)) then raise non_neg
  else if (i < j) then gcd' (j,i) else gcd' (i,j))
  handle _ => raise ERR "gcd" "negative arguments to gcd"
end;

fun gcdl l =
  case l of
    [] => raise ERR "gcdl" "empty list"
  | (h::t) => foldl gcd h t

fun extended_gcd(a, b) = let
  open Arbnum
in
  if b = zero then (a,(Arbint.one,Arbint.zero))
  else let
    val (q,r) = divmod (a,b)
    val (d,(x,y)) = extended_gcd(b,r)
    open Arbint
  in
    (d,(y,x - fromNat q * y))
  end
end

(*---------------------------------------------------------------------------*)
(* Function to compute the Lowest Common Multiple of two integers.           *)
(*---------------------------------------------------------------------------*)

fun lcm (i,j) = let open Arbint in (i * j) div (gcd (i,j)) end
handle _ => raise ERR "lcm" "negative arguments to lcm";

fun calc_lcm ints =
  case ints of
    [] => raise Fail "calc_lcm: should never happen"
  | [x] => x
  | (x::y::xs) => calc_lcm (lcm (x, y)::xs)





val remove_bare_vars = let
  fun Munge t = if is_var t then REWR_CONV (GSYM INT_MUL_LID) t
                else NO_CONV t
in
  DEPTH_CONV Munge
end

local
  val basic_rewrite_conv =
    REWRITE_CONV [boolTheory.NOT_IMP,
                  boolTheory.IMP_DISJ_THM, boolTheory.EQ_IMP_THM,
                  elim_le, elim_ge, elim_gt,
                  INT_SUB_CALCULATE, INT_RDISTRIB, INT_LDISTRIB,
                  INT_NEG_LMUL, INT_NEG_ADD, INT_NEGNEG, INT_NEG_0,
                  INT_MUL_RZERO, INT_MUL_LZERO]
  fun flip_muls tm =
    if is_mult tm andalso not (is_var (rand tm)) then let
      val mcands = strip_mult tm
      val (var, rest) = Lib.pluck is_var mcands
    in
      EQT_ELIM (AC_CONV (INT_MUL_ASSOC, INT_MUL_SYM)
                (mk_eq(tm, mk_mult(list_mk_mult rest, var))))
    end handle HOL_ERR {origin_structure = "Lib", ...} => ALL_CONV tm
    else if is_comb tm then
      (RATOR_CONV flip_muls THENC RAND_CONV flip_muls) tm
    else if is_abs tm then
      ABS_CONV flip_muls tm
    else
      ALL_CONV tm
in
  val phase1_CONV =
  (* to push negations inwards; formula must be quantifier free *)
    REDUCE_CONV THENC basic_rewrite_conv THENC
    remove_negated_vars THENC remove_bare_vars THENC flip_muls THENC
    REDUCE_CONV
end

val simple_disj_congruence =
  tautLib.TAUT_PROVE (Term`!p q r. (~p ==> (q = r)) ==>
                                   (p \/ q = p \/ r)`)
val simple_conj_congruence =
  tautLib.TAUT_PROVE (Term`!p q r. (p ==> (q = r)) ==>
                                   (p /\ q = p /\ r)`)

fun congruential_simplification tm = let
in
  if is_disj tm then let
    val (d1, d2) = dest_disj tm
  in
    if is_disj d1 then
      REWR_CONV (GSYM DISJ_ASSOC) THENC congruential_simplification
    else if is_conj d1 then
      LAND_CONV congruential_simplification THENC
      RAND_CONV congruential_simplification
    else if d1 = true_tm then
      K (SPEC d2 T_or_l)
    else if d1 = false_tm then
      K (SPEC d2 F_or_l)
    else let
      val notd1_t = mk_neg d1
      val notd1_thm = ASSUME notd1_t
      val notd1 =
        if is_neg d1 then EQT_INTRO (CONV_RULE (REWR_CONV NOT_NOT_P) notd1_thm)
        else EQF_INTRO (notd1_thm)
      val d2_rewritten = DISCH notd1_t (REWRITE_CONV [notd1] d2)
    in
      K (MATCH_MP simple_disj_congruence d2_rewritten) THENC
      (REWR_CONV T_or_r ORELSEC REWR_CONV F_or_r ORELSEC
       RAND_CONV congruential_simplification)
    end
  end else if is_conj tm then let
    val (c1, c2) = dest_conj tm
  in
    if is_conj c1 then
      REWR_CONV (GSYM CONJ_ASSOC) THENC congruential_simplification
    else if is_disj c1 then
      LAND_CONV congruential_simplification THENC
      RAND_CONV congruential_simplification
    else if c1 = true_tm then
      K (SPEC c2 T_and_l)
    else if c1 =  false_tm then
      K (SPEC c2 F_and_l)
    else let
      val c2_rewritten = DISCH c1 (REWRITE_CONV [EQT_INTRO (ASSUME c1)] c2)
    in
      K (MATCH_MP simple_conj_congruence c2_rewritten) THENC
      (REWR_CONV T_and_r ORELSEC REWR_CONV F_and_r ORELSEC
       RAND_CONV congruential_simplification)
    end
  end else if is_neg tm then RAND_CONV congruential_simplification
  else ALL_CONV
end tm

fun sum_var_coeffs var tm = let
  open Arbint
in
  if is_plus tm then
    sum_var_coeffs var (rand (rator tm)) + sum_var_coeffs var (rand tm)
  else if is_mult tm then let
    val (l,r) = (rand (rator tm), rand tm)
  in
    if r = var then int_of_term l else zero
  end else zero
end

datatype dir = Left | Right
datatype termtype = EQ | LT

fun dir_of_pair Left (l,r) = l
  | dir_of_pair Right (l,r) = r
fun term_at Left tm = rand (rator tm)
  | term_at Right tm = rand tm

fun conv_at Left = LAND_CONV
  | conv_at Right = RAND_CONV

(* moves summands from one side or the other of a less-than or an
   equality term *)
local
  val myrewrite_conv = REWRITE_CONV [INT_NEG_ADD, INT_NEGNEG, INT_NEG_LMUL]
in
  fun move_terms_from ttype dir P tm = let
    val arg = term_at dir tm
    val arg_summands = strip_plus arg
  in
    case partition P arg_summands of
      ([], to_stay) => REFL tm  (* none to move *)
    | (to_move, []) => let
        (* all must move *)
        val move_conv =
          case (dir,ttype) of
            (Left, LT) => REWR_CONV lt_move_all_right
          | (Right, LT) => REWR_CONV lt_move_all_left
          | (Left, EQ) => REWR_CONV eq_move_all_right
          | (Right, EQ) => REWR_CONV eq_move_all_left
      in
        (move_conv THENC myrewrite_conv) tm
      end
    | (to_move, to_stay) => let
        val new_arg = mk_plus(list_mk_plus to_move, list_mk_plus to_stay)
        val arg_eq_new = EQT_ELIM (AC_CONV (INT_ADD_ASSOC, INT_ADD_COMM)
                                   (mk_eq(arg, new_arg)))
        val move_conv =
          case (dir,ttype) of
            (Left, LT) => REWR_CONV lt_move_left_right
          | (Right, LT) => REWR_CONV lt_move_left_left
          | (Left, EQ) => REWR_CONV eq_move_left_right
          | (Right, EQ) => REWR_CONV eq_move_left_left
      in
        (conv_at dir (K arg_eq_new) THENC move_conv THENC myrewrite_conv) tm
      end
  end
end

fun collect_terms tm = let
  (* assuming that tm is of the form c * x + d * x + e * x
     turns it into (c + d + e) * x
  *)
in
  if is_plus tm then
    BINOP_CONV collect_terms THENC REWR_CONV (GSYM INT_RDISTRIB)
  else
    ALL_CONV
end tm

fun collect_in_sum var tm = let
  (* all terms involving var in tm are collected together such that the
     form of the tm becomes c * var + e *)
  val summands = strip_plus tm
in
  case partition (free_in var) summands of
    ([], _) => ALL_CONV
  | (_, []) => collect_terms THENC LAND_CONV REDUCE_CONV
  | (withvar, without) => let
      val newterm = mk_plus(list_mk_plus withvar, list_mk_plus without)
      val tm_eq_newterm = EQT_ELIM (AC_CONV (INT_ADD_ASSOC, INT_ADD_COMM)
                                    (mk_eq(tm, newterm)))
    in
      K tm_eq_newterm THENC (LAND_CONV (collect_terms THENC
                                        LAND_CONV REDUCE_CONV))
    end
end tm


(* phase 2 massages the terms so that all of the < terms have one side or
   the other with just n * x on it, where n is a non-negative integer, and x
   is the variable we're going to eliminate, unless x can be entirely
   eliminated, in which case the 0 * x is reduced to 0.

   All equality terms are similarly rewritten so that any involving
   x have a term of the form c * x on the left hand side.

   Further, all of the int_divides terms (negated or not) involving
   our variable are cast in the form
     c1 int_divides (c2 * x) + e
   where both c1 and c2 are positive constants

   Finally, if the coefficients of variables in less-than or equality terms
   have a gcd > 1, then we can divide through by that gcd.
*)


val INT_DIVIDES_NEG = CONV_RULE (DEPTH_CONV FORALL_AND_CONV) INT_DIVIDES_NEG
val INT_NEG_FLIP_LTL = prove(
  ``!x y. ~x < y = ~y < x``,
  REPEAT GEN_TAC THEN
  CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV (GSYM INT_NEGNEG)))) THEN
  REWRITE_TAC [INT_LT_NEG]);
val INT_NEG_FLIP_LTR = prove(
  ``!x y. x < ~y = y < ~x``,
  REPEAT GEN_TAC THEN
  CONV_TAC (RAND_CONV (LAND_CONV (REWR_CONV (GSYM INT_NEGNEG)))) THEN
  REWRITE_TAC [INT_LT_NEG]);

val negated_elim_lt_coeffs1 =
  (ONCE_REWRITE_RULE [INT_NEG_FLIP_LTR] o
   REWRITE_RULE [GSYM INT_NEG_RMUL] o
   Q.SPECL [`n`, `m`, `~x`])
  elim_lt_coeffs1;
val negated_elim_lt_coeffs2 =
  (ONCE_REWRITE_RULE [INT_NEG_FLIP_LTL] o
   REWRITE_RULE [GSYM INT_NEG_RMUL] o
   Q.SPECL [`n`, `m`, `~x`])
  elim_lt_coeffs2;



val elim_eq_coeffs' =
  CONV_RULE (STRIP_QUANT_CONV (RAND_CONV
                               (BINOP_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))))
  elim_eq_coeffs

local
  val myrewrite_conv = REWRITE_CONV [INT_NEG_ADD, INT_NEG_LMUL, INT_NEGNEG]
  fun normalise_eqs var tm =
    if is_eq tm andalso free_in var (rhs tm) then
      REWR_CONV EQ_SYM_EQ tm
    else
      ALL_CONV tm
in
  fun phase2_CONV var tm = let
    val land = rand o rator
    fun dealwith_negative_divides tm = let
      val coeff = if is_plus (rand tm) then land (land (rand tm))
                  else land (rand tm)
    in
      if is_negated coeff then
        REWR_CONV (GSYM (CONJUNCT1 INT_DIVIDES_NEG)) THENC myrewrite_conv
      else
        ALL_CONV
    end tm
    fun collect_up_other_freevars tm = let
      val fvs =
        Listsort.sort (String.compare o (#1 ## #1) o (dest_var ## dest_var))
        (free_vars tm)
    in
      EVERY_CONV (map collect_in_sum fvs) tm
    end
  in
    if is_disj tm orelse is_conj tm then
      BINOP_CONV (phase2_CONV var) tm
    else if is_neg tm then
      RAND_CONV (phase2_CONV var) tm
    else if free_in var tm then let
      val ((l,r),tt) = (dest_less tm, LT) handle HOL_ERR _ => (dest_eq tm, EQ)
      open Arbint
      val var_onL = sum_var_coeffs var l
      val var_onR = sum_var_coeffs var r
      val (dir1, dir2) = if var_onL < var_onR then (Left, Right)
                         else (Right, Left)
      (* dir2 is the side where x will be ending up *)
      val move_CONV =
        move_terms_from tt dir1 (free_in var) THENC
        move_terms_from tt dir2 (not o free_in var)
      fun factor_out g g_t tm =
        if is_plus tm then BINOP_CONV (factor_out g g_t) tm
        else let
          val (c,v) = dest_mult tm
          val c_n = int_of_term c
          val new_c = c_n div g
          val new_c_t = term_of_int new_c
          val new_c_thm = SYM (REDUCE_CONV (mk_mult(g_t,new_c_t)))
          val cx_eq_thm0 = LAND_CONV (K new_c_thm) tm
          val reassociate = SYM (SPECL [v, new_c_t, g_t]
                                 integerTheory.INT_MUL_ASSOC)
        in
          TRANS cx_eq_thm0 reassociate
        end handle HOL_ERR _ => REFL tm

      fun factor_out_over_sum tm = let
        (* tm is a sum of multiplications where the left hand argument
           of each multiplication is the same numeral.  We want to turn
              c * x + c * y + ... + c * z
           into
              c * (x + y + ... + z)
        *)
      in
        REWRITE_CONV [GSYM INT_LDISTRIB] tm
      end

      fun fiddle_negs tm = let
        (* used over a sum of multiplications to fix
           ~a * (b * c) into a * (~b * c) *)
        val _ = dest_mult tm
      in
        TRY_CONV (REWR_CONV (GSYM INT_NEG_LMUL) THENC
                  REWR_CONV INT_NEG_RMUL THENC
                  RAND_CONV (REWR_CONV INT_NEG_LMUL)) tm
      end handle HOL_ERR _ => BINOP_CONV fiddle_negs tm

      fun reduce_by_gcd tm = let
        val (l,r) = (land tm, rand tm)
        val ts = strip_plus l @ strip_plus r
        val coeffs =
          List.mapPartial (fn a => if is_var (rand a) then
                                     SOME (rand (rator a))
                                   else NONE) ts
        (* if there are no variables left in the term, the following will
           raise an exception, which is fine; it will be caught by the
           TRY_CONV above us *)
        val g = gcdl (map (Arbint.abs o intSyntax.int_of_term) coeffs)
        val _ = g <> one orelse raise ERR "" ""
        val g_t = term_of_int g
        val gnum_t = rand g_t
        val gnum_nonzero =
          EQF_ELIM (REDUCE_CONV (mk_eq(gnum_t, numSyntax.zero_tm)))
        val dir1_numeral =
          List.find is_int_literal (strip_plus (dir_of_pair dir1 (l,r)))
        val negative_numeral =
          case dir1_numeral of
            NONE => false
          | SOME t => is_negated t
        val elim_coeffs_thm =
          case (tt, dir2, negative_numeral) of
            (LT, Left, false) => MATCH_MP elim_lt_coeffs2 gnum_nonzero
          | (LT, Left, true) => MATCH_MP negated_elim_lt_coeffs1 gnum_nonzero
          | (LT, Right, false) => MATCH_MP elim_lt_coeffs1 gnum_nonzero
          | (LT, Right, true) => MATCH_MP negated_elim_lt_coeffs2 gnum_nonzero
          | (EQ, Left, _) => MATCH_MP elim_eq_coeffs gnum_nonzero
          | (EQ, Right, _) => MATCH_MP elim_eq_coeffs' gnum_nonzero
      in
        BINOP_CONV (factor_out g g_t) THENC
        move_terms_from tt dir1 is_mult THENC
        conv_at dir2 fiddle_negs THENC
        conv_at dir2 factor_out_over_sum THENC
        REWR_CONV elim_coeffs_thm THENC
        REDUCE_CONV
      end tm
    in
      (move_CONV THENC conv_at dir2 collect_terms THENC
       conv_at dir1 collect_up_other_freevars THENC
       TRY_CONV (conv_at dir1 collect_additive_consts) THENC
       conv_at dir2 (LAND_CONV REDUCE_CONV) THENC
       REWRITE_CONV [INT_MUL_LZERO, INT_ADD_LID, INT_ADD_RID] THENC
       TRY_CONV (reduce_by_gcd THENC TRY_CONV move_CONV) THENC
       normalise_eqs var) tm
    end handle HOL_ERR _ =>
      if is_divides tm then
        (TRY_CONV (REWR_CONV (CONJUNCT2 INT_DIVIDES_NEG)) THENC
         RAND_CONV (collect_in_sum var) THENC
         dealwith_negative_divides THENC
         REWRITE_CONV [INT_MUL_LZERO] THENC REDUCE_CONV) tm
      else ALL_CONV tm
   else ALL_CONV tm
  end
end
(* phase three takes all of the coefficients of the variable we're
   eliminating, and calculates their LCM.  Every term is then altered to
   be of the form
        LCM x < ..   or  .. < LCM x
   Then, we can rewrite
     ?x.  .... LCM x ... LCM x ...
   to
     ?x'. .... x' .... x' .... /\ LCM divides x'
   every occurrence of LCM x is replaced with a new variable

*)

fun find_coeff_binop var term = let
  val (_, args) = strip_comb term  (* operator will be < *)
  val arg1 = hd args
  val arg2 = hd (tl args)
in
  if is_mult arg1 andalso rand arg1 = var then
    SOME (int_of_term (rand (rator arg1)))
  else if is_mult arg2 andalso rand arg2 = var then
    SOME (int_of_term (rand (rator arg2)))
  else
    NONE
end

fun find_coeff_divides var term = let
  val (_, args) = strip_comb term (* operator will be int_divides *)
  val arg = hd (tl args)  (* first arg is uninteresting, it should be
                             just a constant *)
  fun recurse_on_rhs t =
    if is_plus t then recurse_on_rhs (rand (rator t))
    else if is_mult t andalso rand t = var then
      SOME (int_of_term (rand (rator t)))
    else
      NONE
in
  recurse_on_rhs arg
end

fun find_coeffs var term = let
  (* have disj/conj term including the following sorts of leaves that involve
     the var x:
       i.    c * x < e
       ii.   e < c * x
       iii.  ~(c * x = e)
       iv.   c * x = e
       v.    ~(e = c * x)
       vi.   e = c * x
       vii.  d | c * x + e0
       viii. ~(d | c * x + e0)
     want to get list of c's, which should all be integer constants.
     The e0 may not be present.
  *)
  fun deal_with_binop acc tm =
    case find_coeff_binop var tm of
      NONE => acc
    | SOME i => i :: acc
  fun recurse acc tm =
    if is_disj tm orelse is_conj tm then
      recurse (recurse acc (rand tm)) (rand (rator tm))
    else if is_less tm orelse is_eq tm then
      deal_with_binop acc tm
    else if is_neg tm then
      recurse acc (rand tm)
    else if is_divides tm then
      case find_coeff_divides var tm of
        NONE => acc
      | SOME x => x :: acc
    else
      acc
in
  Lib.mk_set (recurse [] term)
end

fun find_coeff var term =  (* works over un-negated leaves *)
  if is_divides term then find_coeff_divides var term
  else if is_less term orelse is_eq term then find_coeff_binop var term
  else NONE




(* Phase 3 multiplies up all coefficients of x in order to make them
   the lcm, and then eliminates this, by changing
     ?x. P (c * x)
   to
     ?x. P x /\ c | x
*)
(* this phase has to be done at the level of the existential quantifier *)
(* assume that the existential quantifier still has occurrences of the
   bound variable in the body *)
local
  val myrewrite_conv = REWRITE_CONV [INT_LDISTRIB, INT_RDISTRIB, INT_MUL_ASSOC]
in
  fun phase3_CONV term = let
    val (var, body) = Psyntax.dest_exists term
    (* first calculate the desired LCM *)
    val coeffs = find_coeffs var body
    val lcm = calc_lcm coeffs
    (* now descend to each less-than term, and update the coefficients of
     var to be the same lcm *)
    fun multiply_by_CONV zero_lti tm = let
      val divides_conv =
        REWR_CONV (MATCH_MP justify_divides zero_lti) THENC
        RAND_CONV (TRY_CONV (REWR_CONV INT_LDISTRIB)) THENC REDUCE_CONV
    in
      if is_divides tm then divides_conv
      else if is_less tm then
        REWR_CONV (MATCH_MP lt_justify_multiplication zero_lti)
      else (* must be equality *)
        REWR_CONV (MATCH_MP eq_justify_multiplication zero_lti)
    end tm

    fun LCMify term =
      if is_disj term orelse is_conj term then
        BINOP_CONV LCMify term
      else if is_neg term then RAND_CONV LCMify term
      else
        case (find_coeff var term) of
          NONE => ALL_CONV term
        | SOME c => let
            val i = Arbint.div(lcm, c)
            val zero_lti =
              EQT_ELIM (REDUCE_CONV (mk_less(zero_tm, term_of_int i)))
          in
            multiply_by_CONV zero_lti term
          end
    fun absify_CONV tm = let
      val arg = mk_mult(term_of_int lcm, var)
      val body = Term.subst[(arg |-> var)] tm
    in
      SYM (BETA_CONV (mk_comb(mk_abs(var, body), arg)))
    end
    val eliminate_1divides =
      if lcm = Arbint.one then
        BINDER_CONV (RAND_CONV (K
                                (EQT_INTRO (CONJUNCT1
                                            (SPEC var INT_DIVIDES_1)))) THENC
                     REWR_CONV T_and_r)
      else
        ALL_CONV
  in
    (BINDER_CONV (LCMify THENC myrewrite_conv THENC
                  REDUCE_CONV THENC absify_CONV) THENC
     REWR_CONV lcm_eliminate THENC
     RENAME_VARS_CONV [fst (dest_var var)] THENC
     BINDER_CONV (LAND_CONV BETA_CONV) THENC
     ADDITIVE_TERMS_CONV (TRY_CONV collect_additive_consts) THENC
     eliminate_1divides)
    term
  end
end

(* a "resquan" term is of the form
     low < x /\ x <= high
*)
val resquan_onestep =
  REWR_CONV restricted_quantification_simp THENC
  REDUCE_CONV THENC REWRITE_CONV []

fun resquan_remove tm =
  (resquan_onestep THENC TRY_CONV (RAND_CONV resquan_remove) THENC
   REWRITE_CONV []) tm

(* Phase 4 *)

fun prove_membership t1 t2 = let
  val (tmlist, elty) = listSyntax.dest_list t2
  fun recurse preds thmtodate laters =
    case (thmtodate, preds, laters) of
      (NONE, _, []) => raise ERR "prove_membership" "term not found in list"
    | (NONE, _, x::xs) =>
        if x = t1 then let
          val tailtm = listSyntax.mk_list(xs, elty)
          val whole_list = listSyntax.mk_cons(x, tailtm)
        in
          recurse preds (SOME (ISPECL [x, tailtm] MEM_base, whole_list)) []
        end
        else
          recurse (x::preds) NONE xs
    | (SOME (thm,_), [], _) => thm
    | (SOME (thm,tmlist), p::ps, _) => let
        val newlist = listSyntax.mk_cons(p, tmlist)
        val newthm = MP (ISPECL [tmlist, t1, p] MEM_build) thm
      in
        recurse ps (SOME (newthm, newlist)) []
      end
in
  recurse [] NONE tmlist
end

val move_add =
  GENL (map (fn n => mk_var(n, int_ty)) ["x", "y", "z"])
  (EQT_ELIM (AC_CONV(INT_ADD_ASSOC, INT_ADD_COMM)
            ``(x + y) + z = (x + z) + y:int``))

fun phase4_CONV tm = let
  (* have a formula of the form
       ?x. t1 <op> t2 <op> t3 <op> .... <tn>
     where each <op> is either /\ or \/ and
     where each ti either doesn't involve x at all, or is one of the
     following forms:
        x < a,
        b < x,
        x = a,
        ~(x = a),
        d int_divides x + u
        ~(e int_divides x + v)
     and where all of a, b, u and v are expressions not involving x.
     Further there will be at least one of the latter two.

     Want to calculate F_neginf such that each term of the first type is
     replaced by TRUE and each of the second replaced by FALSE.
  *)
  val lhand = rand o rator
  val {Bvar, Body} = Rsyntax.dest_exists tm
  val F = rand tm
  val Fx = mk_comb(F, Bvar)
  datatype relntype =
    x_LT of term
  | LT_x of term
  | x_EQ of term
  | DIVIDES of (term * term option)
  fun rtype_to_term rt =
    case rt of
      x_LT t => SOME t
    | LT_x t => SOME t
    | x_EQ t => SOME t
    | _ => NONE
  val leaf_arguments = let
    (* traverse the leaves of the term; classifying all those where the
       Bvar is involved.  If
          x < t    then     add x_LT t
          t < x    then     add LT_x t
          x = t    then     add x_EQ t
          t | x    then     add DIVIDES(t, NONE)
          t | x+a  then     add DIVIDES(t, SOME a)
       Note that t = x never occur because of normalisation carried out
       at the end of phase2.

       Pair these with a boolean indicating the parity
       (true = 0, false = 1) of the number of logical negations passed
       through to get to the leaf.
    *)
    fun recurse posp acc tm = let
      val (l,r) = dest_disj tm
        handle HOL_ERR _ => dest_conj tm
    in
      recurse posp (recurse posp acc r) l
    end handle HOL_ERR _ => let
      val (l,r) = dest_less tm
    in
      if l = Bvar then (x_LT r, posp) :: acc
      else if r = Bvar then (LT_x l, posp) :: acc else acc
    end handle HOL_ERR _ => let
      val (l,r) = dest_eq tm
    in
      if l = Bvar then (x_EQ r, posp) :: acc else acc
    end handle HOL_ERR _ => let
      val (l,r) = dest_divides tm
      val (first_rhs_arg, rest_rhs) = (I ## SOME) (dest_plus r)
        handle HOL_ERR _ => (r, NONE)
    in
      if first_rhs_arg = Bvar then
        (DIVIDES (l, rest_rhs), posp) :: acc
      else acc
    end handle HOL_ERR _ => (* must be a negation *)
      recurse (not posp) acc (dest_neg tm) handle HOL_ERR _ => acc
  in
    Lib.mk_set (recurse true [] Body)
  end
  val use_bis = let
    fun recurse (ai as (a, afv)) (bi as (b, bfv)) l =
      case l of
        [] => (ai, bi)
      | (x_LT tm, true)::t => recurse (a+1, afv + length (free_vars tm)) bi t
      | (x_LT tm, false)::t => recurse ai (b+1, bfv + length (free_vars tm)) t
      | (LT_x tm, true)::t => recurse ai (b+1, bfv + length (free_vars tm)) t
      | (LT_x tm, false)::t => recurse (a+1, afv + length (free_vars tm)) bi t
      | _ :: t => recurse ai bi t
    val ((at,afv), (bt, bfv)) = recurse (0, 0) (0, 0) leaf_arguments
  in
    (bt < at) orelse (bt = at andalso bfv < afv)
  end

  (* need prove either that ?y. !x. x < y ==> (neginf x = F x)  or
     that                   ?y. !x. y < x ==> (posinf x = F x)
     depending on the relative numbers of x_LT and LT_x leaves, i.e.
     our use_bis variable *)
  val lemma = let
    val y = genvar int_ty
    val all_terms = List.mapPartial (rtype_to_term o #1) leaf_arguments
    val MK_LESS = if use_bis then mk_less else (fn (x,y) => mk_less(y,x))
  in
    if null all_terms then let
      (* neginf and F are the same *)
      val without_ex = GEN Bvar (DISCH (MK_LESS(Bvar, y)) (REFL Fx))
    in
      EXISTS (mk_exists(y, concl without_ex), y) without_ex
    end
    else let
      val (minmax_op, minmax_thm, arg_accessor, eqthm_transform) =
        if use_bis then (min_tm, INT_MIN_LT, rand, I)
        else            (max_tm, INT_MAX_LT, lhand, GSYM)
      val witness = let
        infixr -->
        fun recurse acc tms =
          case tms of
            [] => acc
          | (x::xs) => recurse (list_mk_comb(minmax_op, [acc, x])) xs
      in
        recurse (hd all_terms) (tl all_terms)
      end
      fun gen_rewrites acc thm =
        if is_conj (concl thm) then
          gen_rewrites (gen_rewrites acc (CONJUNCT1 thm)) (CONJUNCT2 thm)
        else let
          val arg = arg_accessor (concl thm)
          val (hdt, _) = strip_comb arg
        in
          if hdt = minmax_op then
            gen_rewrites acc (MATCH_MP minmax_thm thm)
          else
            EQT_INTRO thm :: EQF_INTRO (MATCH_MP INT_LT_GT thm) ::
            EQF_INTRO (eqthm_transform (MATCH_MP INT_LT_IMP_NE thm)) :: acc
        end
      val rewrites =
        gen_rewrites [] (ASSUME (MK_LESS (Bvar, witness)))
      val thm0 =
        (BETA_CONV THENC REWRITE_CONV rewrites THENC mk_abs_CONV Bvar) Fx
      val thm1 = GEN Bvar (DISCH_ALL thm0)
      val exform = let
        val (x, body) = dest_forall (concl thm1)
        val (_,c) = dest_imp body
        val newh = MK_LESS(x, y)
      in
        mk_exists(y, mk_forall(x, mk_imp(newh, c)))
      end
    in
      EXISTS (exform, witness) thm1
    end
  end
  val neginf = (* call it neginf, though it will be "posinf" if ~ use_bis *)
    rator (rhs (#2 (dest_imp (#2 (dest_forall
                                  (#2 (dest_exists (concl lemma))))))))

  (* before proceeding, need to calculate the LCM of all the d and e of
     the above forms, call it delta *)

  val all_delta_tms = let
    fun collect (DIVIDES(c, _), _) = SOME c
      | collect _ = NONE
  in
    Lib.mk_set (List.mapPartial collect leaf_arguments)
  end
  val all_deltas = map int_of_term all_delta_tms
  val delta = if null all_deltas then Arbint.one else calc_lcm all_deltas
  val delta_tm = term_of_int delta
  val divides_info =
    map (fn ld_tm =>
         (ld_tm, EQT_ELIM (REDUCE_CONV (mk_divides(ld_tm, delta_tm)))))
    all_delta_tms

  (* further need that !x y. neginf x = neginf (x +/- y * delta_tm) *)
  (* The argument to neginf only appears as argument to divides terms.
     We must be able to reduce
       c int_divides (x +/- y * delta + e)   to
       c int_divides (x + e)
     given that c is a divisor of delta.  We first reduce
       (x +/- y + e) to (x + e +/- y)
     using either the theorem move_sub or move_add (proved above).
     Then we have
       c int_divides y ==> (c int_divides (x +/- y) = c int_divides x)  and
       c int_divides x ==> c int_divides (x * y)
     which we specialise with the appropriate values for x and y, and then
     use rewriting to do the right reductions
  *)
  val lemma2 = let
    val y = genvar int_ty
    val (tm0, move_thm, divides_thm) =
      if use_bis then (mk_comb (neginf, mk_minus(Bvar, mk_mult(y, delta_tm))),
                       move_sub, INT_DIVIDES_RSUB)
      else (mk_comb (neginf, mk_plus(Bvar, mk_mult(y, delta_tm))),
            move_add, INT_DIVIDES_RADD)
    fun recurse tm =
      if is_conj tm orelse is_disj tm then
        BINOP_CONV recurse tm
      else if is_neg tm then
        RAND_CONV recurse tm
      else let
        val (local_delta, arg2) = dest_divides tm
        val (l,r) = dest_plus arg2
          handle (e as HOL_ERR _) => if use_bis then dest_minus arg2
                                     else raise e
      in
        if l = Bvar then let
          (* the original divides term is of form c | x *)
          val ldel_divides = Lib.assoc local_delta divides_info
          val ldel_divides_dely =
            SPEC y (MATCH_MP INT_DIVIDES_RMUL ldel_divides)
          val ldel_simpler = MATCH_MP divides_thm ldel_divides_dely
        in
          REWR_CONV ldel_simpler tm
        end
        else let
          val (ll, lr) = (if use_bis then dest_minus else dest_plus) l
          val _ = ll = Bvar orelse raise ERR "" ""
          (* the original divides term of form c | x + e            *)
          (* we're rewriting something like c | (x +/- y * d) + e   *)
          val ldel_divides = Lib.assoc local_delta divides_info
          val ldel_divides_dely =
            SPEC y (MATCH_MP INT_DIVIDES_RMUL ldel_divides)
          val ldel_simpler = MATCH_MP divides_thm ldel_divides_dely
        in
          (RAND_CONV (REWR_CONV move_thm) THENC
           REWR_CONV ldel_simpler) tm
        end
      end handle HOL_ERR _ => ALL_CONV tm
    val c =
      BETA_CONV THENC recurse THENC mk_abs_CONV Bvar
  in
    GENL [y, Bvar] (c tm0)
  end

  val disj1 = let
    val i = genvar int_ty
    val restriction = mk_conj(mk_less(zero_tm, i),
                              mk_leq(i, delta_tm))
  in
    mk_exists(i, mk_conj(restriction, mk_comb(neginf, i)))
  end

  val (disj2, bis_list_tm) = let
    (* need all of the bi *)
    val intlist_ty = mk_thy_type{Args=[int_ty], Tyop="list",Thy="list"}
    val MEM_tm = mk_thy_const{Name = "MEM", Thy="list",
                               Ty = int_ty --> intlist_ty --> Type.bool}
    fun find_bi (LT_x t, true) = SOME t
      | find_bi (x_LT t, false) = SOME (mk_plus(t, mk_negated one_tm))
      | find_bi (x_EQ t, true) = SOME (mk_plus(t, mk_negated one_tm))
      | find_bi (x_EQ t, false) = SOME t
      | find_bi _ = NONE
    fun find_ai (x_LT t, true) = SOME t
      | find_ai (LT_x t, false) = SOME (mk_plus(t, one_tm))
      | find_ai (x_EQ t, true) = SOME (mk_plus(t, one_tm))
      | find_ai (x_EQ t, false) = SOME t
      | find_ai _ = NONE
    val (find_xi, arith_op) = if use_bis then (find_bi, mk_plus)
                              else (find_ai, mk_minus)
    val bis = Lib.mk_set (List.mapPartial find_xi leaf_arguments)
    val bis_list_tm = listSyntax.mk_list(bis, int_ty)
    val b = genvar int_ty
    val j = genvar int_ty
    val brestriction = list_mk_comb(MEM_tm, [b, bis_list_tm])
    val jrestriction = mk_conj(mk_less(zero_tm, j), mk_leq(j, delta_tm))
  in
    (list_mk_exists([b,j], mk_conj(mk_conj(brestriction, jrestriction),
                                   mk_comb(F, arith_op(b,j)))),
     bis_list_tm)
  end

  (* now must prove that (?x. F x) = disj1 \/ disj2 *)
  (* first show disj1 ==> (?x. F x) *)

  (* Comments true for use_bis = true.  Proof strategy for use_bis = false
     is the same; we just substitute can_get_big for can_get_small at
     the crucial moment.

     we have
       lemma:         ?y. !x. x < y ==> (F(x) = neginf(x))
       choose y:      !x. x < y ==> F(x) = neginf(x)                 (1)
       assumption:    ?c. (0 < c /\ c <= delta) /\ neginf(c)
       lemma2:        !x y. neginf(x - y * delta) = neginf(x)
       can_get_small: !x y d. 0 < d ==> ?c. 0 < c /\ y - c * d < x

     need a z such that z < y and neginf(z).  Then F(z) will be true.
     Specialise can_get_small with
           y, c and delta
     so
                      0 < delta ==> ?e. 0 < e /\ c - e * delta < y
     discharge 0 < delta to get
                      ?e. 0 < e /\ c - e * delta < y
     choose e, take second conjunct
                      c - e * delta < y                              (2)
     specialise lemma2 with c, e
                      neginf(c - e * delta) = neginf(c)              (3)
     MATCH_MP (1) and (2)
                      F(c - e * delta) = neginf(c - e * delta)       (4)
     trans with (3) to get
                      F(c - e * delta) = neginf(c)                   (5)
     given assumption,
                      F(c - e * delta)                               (6)
     so, there exists an x, such that F is true
                      ?x. F x                                        (7)

  *)
  val zero_lt_delta = EQT_ELIM (REDUCE_CONV (mk_less(zero_tm, delta_tm)))
  val delta_ok = CONJ zero_lt_delta (SPEC delta_tm INT_LE_REFL)
  val one_ok =
    EQT_ELIM (REDUCE_CONV (mk_conj(mk_less(zero_tm, one_tm),
                                   mk_leq(one_tm, delta_tm))))
  val disj1_implies_exFx = let
    val (disj1_var, disj1_body) = dest_exists disj1
    val assumption0 = ASSUME disj1_body
    val assumption = CONJUNCT2 assumption0
    val lemma_var = genvar int_ty
    val thm1 = let
      val (exvar, lemma_body) = dest_exists (concl lemma)
    in
      ASSUME (subst [exvar |-> lemma_var] lemma_body)
    end
    val c = rand (concl assumption)
    val spec_cgs =
      SPECL [lemma_var, c, delta_tm] (if use_bis then can_get_small
                                      else can_get_big)
    val thm0 = MP spec_cgs zero_lt_delta
    val e = genvar int_ty
    val thm2 = let
      val (v, body) = dest_exists (concl thm0)
    in
      CONJUNCT2 (ASSUME (subst [v |-> e] body))
    end
    val thm3 = SPECL [e,c] lemma2
    val thm4 = MATCH_MP thm1 thm2
    val thm5 = TRANS thm4 thm3
    val thm6 = EQ_MP (SYM thm5) assumption
    val thm7 = EXISTS (tm, rand (concl thm6)) (CONV_RULE BETA_CONV thm6)
  in
    CHOOSE(disj1_var, ASSUME disj1)
    (CHOOSE (lemma_var, lemma)
     (CHOOSE(e, thm0) thm7))
  end

  (* now need to prove that disj2 implies ?x. F x -- this is much
     simpler, because each disjunct of disj2 is just about an instance
     of F c *)

  val disj2_implies_exFx = let
    val (disj2_vars, disj2_body) = strip_exists disj2
    val assumption0 = ASSUME disj2_body
    val assumption = CONJUNCT2 assumption0
    val thm0 =
      EXISTS(tm, rand(concl assumption)) (CONV_RULE BETA_CONV assumption)
    val (b,j) = (hd disj2_vars, hd (tl disj2_vars))
  in
    CHOOSE(b, ASSUME disj2)
    (CHOOSE (j, ASSUME (mk_exists(j, disj2_body))) thm0)
  end
  val rhs_implies_exFx =
    DISCH_ALL (DISJ_CASES (ASSUME(mk_disj(disj1, disj2)))
               disj1_implies_exFx disj2_implies_exFx)

  (* to do the proof of exFx implies rhs, reason as follows:
       F x0                    (choose_x)
     specialise excluded middle to get
       disj2 \/ ~disj2         (disj2_exm)
     then
       disj2 |- disj2
     allows
       disj2 |- disj1 \/ disj2 (positive_disj2)

     with the other case, (not_disj2) we want to prove that
       !x. F x ==> F (x - delta)

     first rewrite not_disj2 with NOT_EXISTS_CONV twice and then
     tautLib.TAUT_PROVE ``~(p /\ q) = p ==> ~q``.  This will generate
     not_thm:
        |- !b j. MEM b [b1; b2; .. bn] /\ 0 < j /\ j <= delta ==>
                 ~F(b + j)

     so, ASSUME
       F x |- F x          (fx_thm)

     expand out F(x - delta) (i.e. do a BETA_CONV) and traverse this
     and F(x) in parallel.  This is a recursive procedure that takes
     a F(x) theorem and a F(x - delta) term and produces a theorem
     with the second term as its conclusion

     Recursive cases are as follows:
        if is_conj thm then
           CONJ (recurse (CONJUNCT1 thm) (#1 (dest_conj tm)))
                (recurse (CONJUNCT2 thm) (#2 (dest_conj tm)))
        else if is_disj thm then let
           val (d1_thm0, d2_thm0) = (ASSUME ## ASSUME) (dest_disj (concl thm))
           val (d1_tm, d2_tm) = dest_disj tm
           val d1_thm = recurse d1_thm0 d1_tm
           val d2_thm = recurse d2_thm0 d2_tm
        in
           DISJ_CASES thm d1_thm d2_thm
        end else if is_neg thm then let
           val Pxd_tm = dest_neg tm
           val subres = recurse (ASSUME Pxd_tm) (dest_neg (concl thm))
           val false_concl = MP thm subres
        in
           EQF_ELIM (DISCH Pxd_tm false_concl)
        end

    There are seven base cases depending on the form of the term and
    whether or not we're under a negation; the following are
    demonstrate what happens when use_bis is true.

         (A)   thm  = |- x < e
               tm   =    x - d < e
               posp = true

              0 < d              (zero_lt_delta)
           specialise INT_LT_ADD2 with x, e, 0, d to get
              x < e /\ 0 < d ==> x + 0 < e + d
           discharge with conjunction of thm and zero_lt_delta to get
              x + 0 < e + d
           CONV_RULE (RATOR_CONV (RAND_CONV (REWR_CONV INT_ADD_RID))) to get
              x < e + d
           CONV_RULE (REWR_CONV (GSYM INT_LT_SUB_ADD)) to get
              x - d < e
           as required

         (B)   thm  = |- x - d < e
               tm   = |- x < e
               posp = false

           e + ~1 is one of the bi terms

           ASSUME ~tm
                     |- ~(x < e)
           REWR_CONV with not_less
                     |- e < x + 1
           REWR_CONV with (GSYM INT_LT_ADDNEG2)
                     |- e + ~1 < x                  (lowbound)
           REWR_CONV thm with less_to_leq_samel
                     |- x - d <= e + ~1
           REWR_CONV with INT_LE_SUB_RADD
                     |- x <= (e + ~1) + d           (highbound)
           REWR_CONV (lowbound /\ highbound) with in_additive_range
                     |- ?j. (x = (e + ~1) + j) /\ 0 < j /\ j <= d
           choose j take conjuncts
                     |- (x = (e + ~1) + j)          (conj1)
                     |- 0 < j /\ j <= d             (conj2)
           prove e + ~1 in list of bis              (membership)
           match not_thm with membership /\ conj2
                     |- ~P((e + ~1) + j)            (notP)
           AP_TERM P conj1
                     |- P(x) = P((e + ~1) + j)
           EQ_TRANS with fx_thm
                     |- P((e + ~1) + j)
           MP with notP
                     |- F
           CCONTR tm
                     |- x < e    as required

         (C)   thm  = |- e < x
               tm   =    e < x - d
               posp = true

             ASSUME ~tm
                 ... |- ~(e < x - d)                 (not_tm)
             REWR_CONV with INT_NOT_LT
                     |- x - d <= e
             REWR_CONV with INT_LE_SUB_RADD
                     |- x <= e + d                   (var_leq)
             REWR_CONV (thm /\ var_leq) with in_additive_range
                     |- ?j. (x = e + j) /\ 0 < j /\ j <= d  (exists_j)

             demonstrate that e is in the list of bis,
                     |- MEM e [b1; b2; ... bn]       (membership)
             choose j from exists_j and take conjunct1
                     |- x = e + j                    (var_eq)
             and conjunct2
                     |- 0 < j /\ j <= d              (j_in_range)
             match not_thm with membership /\ j_in_range
                     |- ~F(e + j)
             EQF_INTRO
                     |- F(e + j) = F                 (not_fej)
             AP_TERM F (var_eq)
                     |- F(x) = F(e + j)              (fx_eq_fej)
             TRANS fx_eq_fej not_fej
                     |- F(x) = F                     (fx_eq_F)
             EQ_MP fx_thm fx_eq_F
                     |- F
             CCONTR tm
                     |- e < x - d      as required

         (D)   thm  = |- e < x - d
               tm   = |- e < x
               posp = false


                      |- 0 < d                  (zero_lt_delta)
               REWR_CONV (GSYM INT_NEG_LT0)
                      |- ~d < 0                 (part2)
               REWR_CONV INT_LT_SUB_LADD thm
                      |- e + d < x              (part1)
               MATCH_MP INT_LT_ADD2 (part1 /\ part2)
                      |- e + d + ~d < x + 0
               CONV_RULE (LAND_CONV (REWR_CONV (GSYM INT_ADD_ASSOC)))
                      |- e + (d + ~d) < x + 0
               CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV INT_ADD_RINV)))
                      |- e + 0 < x + 0
               CONV_RULE (BINOP_CONV (REWR_CONV INT_ADD_RID))
                      |- e < x

         (E)

             thm  =  |- x = e
             tm   =     x - d = e
             posp =  true

             given our assumption, the thm is an impossibility
             straightaway.

             specialise not_thm with e + ~1 and 1 to get
                    |- MEM (e + ~1) [...] /\ 0 < 1 /\ 1 <= d ==>
                       ~F(e + ~1 + 1)                     (spec_not_thm)
             prove e + ~1 is in list of bis
                    |- MEM (e + ~1) [b1; b2; ... bn]      (membership)
             prove arithmetics of 1 with REDUCE_CONV
                    |- 0 < 1 /\ 1 <= d                    (one_ok)
             match membership /\ one_ok against spec_not_thm to get
                    |- ~F(e + ~1 + 1)                     (not_f_11)
             EQF_INTRO not_f_11
                    |- F (e + ~1 + 1) = F                 (f_11_eqF)
             SYM (SPEC e elim_neg_ones)
                    |- e = e + ~1 + 1                     (e_eq_11)
             TRANS thm e_eq_11
                    |- x = e + ~1 + 1                     (x_eq_11)
             AP_TERM F x_eq_11
                    |- F(x) = F(e + ~1 + 1)               (Fx_eq_Fe_11)
             TRANS Fx_eq_Fe_11 f_11_eqF
                    |- F(x) = F                           (Fx_eq_F)
             EQ_MP fx_thm Fx_eq_F
                    |- F
             CONTR tm
                    |- x - d = e     as required

         (F)
             thm  = |- x - d = e
             tm   =    x = e
             posp = false

             e is in bis list

             thm
                   |- x - d = e                           (xlessd_eq_e)
             CONV_RULE (REWR_CONV INT_EQ_SUB_RADD)
                   |- x = e + d                           (x_eq_ed)
             SPECL [e, d] not_thm
                   |- MEM e [...] /\ 0 < d /\ 1 <= d ==>
                      ~F(e + d)                           (spec_not_thm)
             prove e is in list of bis
                   |- MEM e [b1;b2;... bn]                (membership)
             MP spec_not_thm (CONJ membership delta_ok)
                   |- ~F(e + d)                           (not_fed)
             EQF_INTRO not_fed
                   |- F(e + d) = F                        (fed_eq_f)
             AP_TERM F x_eq_ed
                   |- F(x) = F(e + d)                     (fx_eq_fed)
             TRANS fx_eq_fed fed_eq_f
                   |- F(x) = F                            (fx_eq_f)
             EQ_MP fx_thm fx_eq_f
                   |- F
             CCONTR tm
                   |- x = e

         (G)

              thm  = |- f int_divides (x + e)
              tm   =    f int_divides (x - d + e)
              posp = _

             specialise INT_DIVIDES_RMUL and match with divides_info
             theorem that f int_divides d to get
                  f int_divides (c * d)
             specialise INT_DIVIDES_RSUB to get
                  f int_divides (c * d) ==>
                  (f int_divides (x + e) - (c * d) = f int_divides (x + e))
             match two preceding and GSYM to get
                  f int_divides (x + e) = f int_divides (x + e) - c * d
             and if C) then EQ_MP this thm to get result.
             else if D) EQ_MP (AP_TERM ``~`` this) thm to get result


        *)

  val exFx_implies_rhs = let
    val disj2_exm = SPEC disj2 EXCLUDED_MIDDLE
    val positive_disj2 = DISJ2 disj1 (ASSUME disj2)
    val fx_goes_downward = let
      (* to prove either ~disj2 |- !x. F x ==> F (x - d)   (use_bis) or
                         ~disj2 |- !x. F x ==> F (x + d)   (~use_bis) *)
      val not_disj2_0 = mk_neg disj2
      val not_disj2_thm = ASSUME not_disj2_0
      val not_thm =
        CONV_RULE (NOT_EXISTS_CONV THENC
                   BINDER_CONV NOT_EXISTS_CONV THENC
                   STRIP_QUANT_CONV (REWR_CONV simple_bool_formula))
        not_disj2_thm
      val fx_thm = ASSUME (mk_comb(F, Bvar))
      val fx_thm_expanded = CONV_RULE BETA_CONV fx_thm
      fun arecurse posp thm tm = let
        val thm_concl = concl thm
      in let
        val (c1, c2) = dest_conj tm
      in
        CONJ (arecurse posp (CONJUNCT1 thm) c1)
             (arecurse posp (CONJUNCT2 thm) c2)
      end handle HOL_ERR _ => let
        val (d1_thm0, d2_thm0) = (ASSUME ## ASSUME) (dest_disj thm_concl)
        val (d1_tm, d2_tm) = dest_disj tm
        val d1_thm = DISJ1 (arecurse posp d1_thm0 d1_tm) d2_tm
        val d2_thm = DISJ2 d1_tm (arecurse posp d2_thm0 d2_tm)
      in
        DISJ_CASES thm d1_thm d2_thm
      end handle HOL_ERR _ => let
        val Pxd_tm = dest_neg tm
        val subres = arecurse (not posp) (ASSUME Pxd_tm) (dest_neg (concl thm))
        val false_concl = MP thm subres
      in
        NOT_INTRO (DISCH Pxd_tm false_concl)
      end handle HOL_ERR _ => let
        val (lthm,rthm) = dest_less thm_concl
        val (ltm, rtm) = dest_less tm
      in
        (* base cases with less as operator *)
        if posp then (* thm is positive instance *)
          if lthm = Bvar then let
            (* x < e - want to prove that x + d < e
               do it by contradiction *)
            val e = rthm
            val not_tm = ASSUME (mk_neg tm)
            val leq_var = CONV_RULE (REWR_CONV INT_NOT_LT THENC
                                     REWR_CONV (GSYM INT_LE_SUB_RADD)) not_tm
            (* ~(x + d < e) --> e <= x + d --> e - d <= x *)
            val exists_j =
              CONV_RULE (REWR_CONV in_subtractive_range) (CONJ leq_var thm)
            (* ?j. (x = e - j) /\ 0 < j /\ j <= d *)
            val membership = prove_membership e bis_list_tm
            val (jvar, jbody) = dest_exists (concl exists_j)
            val choose_j = ASSUME jbody
            val (var_eq, j_in_range) = CONJ_PAIR choose_j
            val not_fej =
              EQF_INTRO (MATCH_MP not_thm (CONJ membership j_in_range))
            val fx_eq_fej = AP_TERM F var_eq
            val fx_eq_F = TRANS fx_eq_fej not_fej
            val contradiction = EQ_MP fx_eq_F fx_thm
          in
            CCONTR tm (CHOOSE(jvar, exists_j) contradiction)
          end
          else if rthm = Bvar then let
            val e = lthm
            (* e < x - want to prove e < x + d *)
            val thm0 = SPECL [e, Bvar, zero_tm, delta_tm] INT_LT_ADD2
            (* e < x /\ 0 < d ==> e + 0 < x + d *)
            val thm1 = MP thm0 (CONJ thm zero_lt_delta)
          (* e + 0 < x + d *)
          in
            CONV_RULE (LAND_CONV (REWR_CONV INT_ADD_RID)) thm1
          end
          else (* Bvar not present *) thm
        else (* not posp *)
          if ltm = Bvar then let
            (* have x + d < e, want to show x < e *)
            val negdelta_lt_0 =
              CONV_RULE (REWR_CONV (GSYM INT_NEG_LT0)) zero_lt_delta
            val stage0 =
              MATCH_MP INT_LT_ADD2 (CONJ thm negdelta_lt_0)
              (* (x + d) + ~d < e + 0 *)
            val stage1 =
              CONV_RULE (LAND_CONV (REWR_CONV (GSYM INT_ADD_ASSOC))) stage0
              (* x + (d + ~d) < e + 0 *)
            val stage2 =
              CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV INT_ADD_RINV))) stage1
              (* x + 0 < e + 0 *)
          in
            CONV_RULE (BINOP_CONV (REWR_CONV INT_ADD_RID)) stage2
          end
          else if rtm = Bvar then let
            val e = ltm
            (* have e < x + d, want to show e < x  -- by contradiction *)
            val not_tm = ASSUME (mk_neg tm)
              (* |- ~(e < x) *)
            val x_lt_e1 = CONV_RULE (REWR_CONV not_less) not_tm
              (* |- x < e + 1 *)
            val e1_leq_xd = CONV_RULE (REWR_CONV less_to_leq_samer) thm
              (* |- e + 1 <= x + d *)
            val e1d_leq_x =
              CONV_RULE (REWR_CONV (GSYM INT_LE_SUB_RADD)) e1_leq_xd
              (* |- (e + 1) - d <= x *)
            val exists_j =
              CONV_RULE (REWR_CONV in_subtractive_range)
                        (CONJ e1d_leq_x x_lt_e1)
              (* ?j. (x = e + 1 - j) /\ 0 < j /\ j <= d *)
            val membership = prove_membership (mk_plus(e,one_tm)) bis_list_tm
            val (jvar, jbody) = dest_exists (concl exists_j)
            val choose_j = ASSUME jbody
            val (var_eq, j_in_range) = CONJ_PAIR choose_j
            val not_fej = MATCH_MP not_thm (CONJ membership j_in_range)
            val fej = EQ_MP (AP_TERM F var_eq) fx_thm
          in
            CCONTR tm (CHOOSE(jvar, exists_j) (MP not_fej fej))
          end
          else (* Bvar not present *) thm
      end handle HOL_ERR _ => let
        val (lthm,rthm) = dest_eq thm_concl
        val (ltm, rtm) = dest_eq tm
      in
        if posp then
          if lthm = Bvar then let
            (* x = e *)
            val e = rthm
            val e_plus_1 = mk_plus(e, one_tm)
            val spec_not_thm = SPECL [e_plus_1, one_tm] not_thm
            (* MEM (e + 1) [....; e + 1] /\ 0 < 1 /\ 1 <= d ==>
               ~F(e + 1 - 1) *)
            val membership = prove_membership e_plus_1 bis_list_tm
            val not_fe1 = MP spec_not_thm (CONJ membership one_ok)
            val fe1_eqF = EQF_INTRO not_fe1
            (* F(e + 1 - 1) = false *)
            val e_eq_e11 = SYM (SPEC e elim_minus_ones)
            (* e = e + 1 - 1 *)
            val x_eq_e11 = TRANS thm e_eq_e11
            (* x = e + 1 - 1 *)
            val Fx_eq_Fe11 = AP_TERM F x_eq_e11
            (* F x = F(e + 1 - 1) *)
            val Fx_eq_F = TRANS Fx_eq_Fe11 fe1_eqF
          in
            CONTR tm (EQ_MP Fx_eq_F fx_thm)
          end
          else (* Bvar not present *)
            thm
        else (* not posp *)
          if ltm = Bvar then let
            (* have x + d = e, want x = e *)
            val e = rtm
            val xplusd_eq_e = thm
            val x_eq_elessd =
              EQ_MP (SYM (SPECL [Bvar,e,delta_tm] INT_EQ_SUB_LADD)) xplusd_eq_e
              (* x = e - d *)
            val F_elessd = EQ_MP (AP_TERM F x_eq_elessd) fx_thm
            val spec_not_thm = SPECL [e, delta_tm] not_thm
            val membership = prove_membership e bis_list_tm
            val not_F_elessd = MP spec_not_thm (CONJ membership delta_ok)
          in
            CCONTR tm (MP not_F_elessd F_elessd)
          end
          else (* Bvar not present *) thm
      end handle HOL_ERR _ => let
        val (c,r) = dest_divides (if posp then thm_concl else tm)
          handle HOL_ERR _ => raise ERR "phase4" "Unexpected term type"
        val (var, rem) = (I ## SOME) (dest_plus r)
          handle HOL_ERR _ => (r, NONE)
      in
        if var = Bvar then let
          (* c | x [+ rem] - want to show that c | x + d [ + rem ] *)
          val c_div_d = Lib.assoc c divides_info
          val c_div_rplusd0 =
            SYM (MP (SPECL [c,delta_tm,r] INT_DIVIDES_RADD) c_div_d)
          (* c | x [+ rem] = c | x [+ rem] + d *)
          val c_div_rplusd1 =
            if isSome rem then
              CONV_RULE (RAND_CONV
                         (RAND_CONV (REWR_CONV move_add))) c_div_rplusd0
            else c_div_rplusd0
          val c_div_rplusd = if posp then c_div_rplusd1 else SYM c_div_rplusd1
        in
          EQ_MP c_div_rplusd thm
        end
        else thm
      end
      end (* need double end, because of double let at start of function *)

      fun brecurse posp thm tm = let
        val thm_concl = concl thm
      in let
        val (c1, c2) = dest_conj tm
      in
        CONJ (brecurse posp (CONJUNCT1 thm) c1)
             (brecurse posp (CONJUNCT2 thm) c2)
      end handle HOL_ERR _ => let
        val (d1_thm0, d2_thm0) = (ASSUME ## ASSUME) (dest_disj (concl thm))
        val (d1_tm, d2_tm) = dest_disj tm
        val d1_thm = DISJ1 (brecurse posp d1_thm0 d1_tm) d2_tm
        val d2_thm = DISJ2 d1_tm (brecurse posp d2_thm0 d2_tm)
      in
        DISJ_CASES thm d1_thm d2_thm
      end handle HOL_ERR _ => let
        val Pxd_tm = dest_neg tm
        val subres = brecurse (not posp) (ASSUME Pxd_tm) (dest_neg (concl thm))
        val false_concl = MP thm subres
      in
        NOT_INTRO (DISCH Pxd_tm false_concl)
      end handle HOL_ERR _ => let
        val (lthm,rthm) = dest_less thm_concl
        val (ltm, rtm) = dest_less tm
      in
        (* base cases with less as operator *)
        if posp then
          if lthm = Bvar then let
            (* x < e *)
            val e = rthm
            val thm0 = SPECL [Bvar, e, zero_tm, delta_tm] INT_LT_ADD2
            val thm1 = MP thm0 (CONJ thm zero_lt_delta)
            val thm2 =
              CONV_RULE (LAND_CONV (REWR_CONV INT_ADD_RID)) thm1
          in
            CONV_RULE (REWR_CONV (GSYM INT_LT_SUB_RADD)) thm2
          end
          else if rthm = Bvar then let
            (* e < x *)
            val e = lthm
            val not_tm = ASSUME (mk_neg tm)
            val var_leq = CONV_RULE (REWR_CONV INT_NOT_LT THENC
                                     REWR_CONV INT_LE_SUB_RADD) not_tm
            val exists_j =
              CONV_RULE (REWR_CONV in_additive_range) (CONJ thm var_leq)
            val membership = prove_membership e bis_list_tm
            (* choose j from exists_j *)
            val (jvar, jbody) = dest_exists (concl exists_j)
            val choose_j = ASSUME jbody
            val (var_eq, j_in_range) = CONJ_PAIR choose_j
            val not_fej =
              EQF_INTRO (MATCH_MP not_thm (CONJ membership j_in_range))
            val fx_eq_fej = AP_TERM F var_eq
            val fx_eq_F = TRANS fx_eq_fej not_fej
            val contradiction = EQ_MP fx_eq_F fx_thm
          in
            CCONTR tm (CHOOSE(jvar, exists_j) contradiction)
          end
          else (* Bvar not present *) thm
        else (* not posp *)
          if ltm = Bvar then let
            val e = rtm
            (* have x - d < e, want x < e  - by contradiction *)
            val not_tm = ASSUME (mk_neg tm)
            val e_less_x1 = CONV_RULE (REWR_CONV not_less) not_tm
              (* e < x + 1 *)
            val lobound = CONV_RULE (REWR_CONV (GSYM INT_LT_ADDNEG2)) e_less_x1
              (* e + ~1 < x *)
            val xd_leq_e1 = CONV_RULE (REWR_CONV less_to_leq_samel) thm
              (* x - d <= e + ~1 *)
            val hibound = CONV_RULE (REWR_CONV INT_LE_SUB_RADD) xd_leq_e1
              (* x <= e + ~1 + d *)
            val exists_j =
              CONV_RULE (REWR_CONV in_additive_range) (CONJ lobound hibound)
            val membership =
              prove_membership (mk_plus(e,mk_negated one_tm)) bis_list_tm
            val (jvar, jbody) = dest_exists (concl exists_j)
            val choose_j = ASSUME jbody
            val (var_eq, j_in_range) = CONJ_PAIR choose_j
            val not_fej = MATCH_MP not_thm (CONJ membership j_in_range)
            val fej = EQ_MP (AP_TERM F var_eq) fx_thm
          in
            CCONTR tm (CHOOSE(jvar, exists_j) (MP not_fej fej))
          end
          else if rtm = Bvar then let
            (* have e < x - d, want e < x *)
            val ed_lt_x = CONV_RULE (REWR_CONV INT_LT_SUB_LADD) thm
            (* have e + d < x, want to show e < x *)
            val negdelta_lt_0 =
              CONV_RULE (REWR_CONV (GSYM INT_NEG_LT0)) zero_lt_delta
            val stage0 =
              MATCH_MP INT_LT_ADD2 (CONJ ed_lt_x negdelta_lt_0)
              (* (e + d) + ~d < x + 0 *)
            val stage1 =
              CONV_RULE (LAND_CONV (REWR_CONV (GSYM INT_ADD_ASSOC))) stage0
              (* e + (d + ~d) < x + 0 *)
            val stage2 =
              CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV INT_ADD_RINV))) stage1
              (* e + 0 < x + 0 *)
          in
            CONV_RULE (BINOP_CONV (REWR_CONV INT_ADD_RID)) stage2
          end else (* Bvar not here *) thm
      end handle HOL_ERR _ => let
        val (lthm, rthm) = dest_eq thm_concl
        val (ltm, rtm) = dest_eq tm
      in
        if posp then
          if lthm = Bvar then let
            (* have x = e, want to show x - d = e *)
            val e = rtm
            val e_less1 = mk_plus(e, mk_negated one_tm)
            val spec_not_thm = SPECL [e_less1, one_tm] not_thm
            val membership = prove_membership e_less1 bis_list_tm
            val not_f_11 = MP spec_not_thm (CONJ membership one_ok)
            val f_11_eqF = EQF_INTRO not_f_11
            val e_eq_11 = SYM (SPEC e elim_neg_ones)
            val x_eq_11 = TRANS thm e_eq_11
            val Fx_eq_Fe_11 = AP_TERM F x_eq_11
            val Fx_eq_F = TRANS Fx_eq_Fe_11 f_11_eqF
          in
            CONTR tm (EQ_MP Fx_eq_F fx_thm)
          end
          else thm
        else (* not posp *)
          if ltm = Bvar then let
            (* have x - d = e, want to show x = e *)
            val e = rthm
            val xlessd_eq_e = thm
            val x_eq_ed = CONV_RULE (REWR_CONV INT_EQ_SUB_RADD) xlessd_eq_e
            val spec_not_thm = SPECL [e, delta_tm] not_thm
            val membership = prove_membership e bis_list_tm
            val not_fed = MP spec_not_thm (CONJ membership delta_ok)
            val fed = EQ_MP (AP_TERM F x_eq_ed) fx_thm
          in
            CCONTR tm (MP not_fed fed)
          end
          else thm
      end handle HOL_ERR _ => let
        val (c,r) = dest_divides (if posp then thm_concl else tm)
          handle HOL_ERR _ => raise ERR "phase4" "Unexpected term type"
        val (var, rem) = (I ## SOME) (dest_plus r)
          handle HOL_ERR _ => (r, NONE)
      in
        if var = Bvar then let
          (* c | x [+ rem] - want to show that c | x + d [ + rem ] *)
          val c_div_d = Lib.assoc c divides_info
          val c_div_rsubd0 =
            MP (SPECL [c,delta_tm,r] INT_DIVIDES_RSUB) c_div_d
          (* c | x [+ rem] = c | x [+ rem] + d *)
          val c_div_rsubd1 =
            if isSome rem then
              CONV_RULE (LAND_CONV
                         (RAND_CONV (REWR_CONV (GSYM move_sub)))) c_div_rsubd0
            else c_div_rsubd0
          val c_div_rsubd = if posp then SYM c_div_rsubd1 else c_div_rsubd1
        in
          EQ_MP c_div_rsubd thm
        end
        else thm
      end
      end (* again need a double end *)


      val (arith_op, recurse) =
        if use_bis then (mk_minus, brecurse) else (mk_plus, arecurse)
      val fxd_beta_thm = BETA_CONV (mk_comb(F, arith_op(Bvar, delta_tm)))
      val fxd_tm = rhs (concl fxd_beta_thm)
      val fxd_thm = recurse true fx_thm_expanded fxd_tm
    in
      GEN Bvar (DISCH Fx (EQ_MP (SYM fxd_beta_thm) fxd_thm))
    end
    val x0 = genvar int_ty
    val Fx0 = mk_comb(F, x0)
    val Fx0_thm = ASSUME Fx0
    val (change_by_dmultiples, can_become_extreme, change_to_extreme) =
      if use_bis then
        (MP (SPECL [F, delta_tm, x0] top_and_lessers)
         (CONJ fx_goes_downward Fx0_thm),
         can_get_small,
         subtract_to_small)
      else
        (MP (SPECL [F, delta_tm, x0] bot_and_greaters)
         (CONJ fx_goes_downward Fx0_thm), can_get_big,
         add_to_great)
    (* this looks like: .. |- !c. 0 < c ==> F (x0 - c * d) *)
    (* further have lemma:
                           |- ?y. !x. x < y ==> (F x = neginf x)
       and lemma2:         |- !c x. neginf (x - c * d) = neginf x
       and can_get_small:  |- !x y d. 0 < d ==> ?c. 0 < c /\ y - c * d < x

       so, choose a y for lemma
          (choose_lemma) . |- !x. x < y ==> (F x = neginf x)
    *)
    val y = genvar int_ty
    val choose_lemma = let
      val (exvar, exbody) = dest_exists (concl lemma)
    in
      ASSUME (subst [exvar |-> y] exbody)
    end
    (*
       specialise can_get_small with [y, x0, d] and MP with zero_lt_delta
          (little_c_ex)    |- ?c. 0 < c /\ x0 - c * d < y
    *)
    val little_c_ex =
      MP (SPECL [y, x0, delta_tm] can_become_extreme) zero_lt_delta
    (*
       choose a u for little c
          (choose_u)     . |- 0 < u /\ x0 - u * d < y
       conjunct1
          (zero_lt_u)    . |- 0 < u
       conjunct2
          (x0_less_ud)   . |- x0 - u * d < y
     *)
    val u = genvar int_ty
    val choose_u = let
      val (exvar, exbody) = dest_exists (concl little_c_ex)
    in
      ASSUME (subst [exvar |-> u] exbody)
    end
    val zero_lt_u = CONJUNCT1 choose_u
    val x0_less_ud = CONJUNCT2 choose_u
    (*
       SPEC change_by_dmultiples with u, and MP with zero_lt_u to get
          (Fx0_less_ud)   . |- F (x0 - u * d)
    *)
    val Fx0_less_ud = MP (SPEC u change_by_dmultiples) zero_lt_u
    (* SPEC choose_lemma with x0 - u * d and MP with x0_less_ud to get
     (Fneginf_x0_less_ud) . |- F (x0 - u * d) = neginf (x0 - u * d)
    *)
    val x0_less_ud_tm = if use_bis then lhand (concl x0_less_ud)
                        else rand (concl x0_less_ud)
    val Fneginf_x0_less_ud =
      MP (SPEC x0_less_ud_tm choose_lemma) x0_less_ud
    (* EQ_MP with Fx0_less_ud to get
      (neginf_x0_less_ud) . |- neginf (x0 - u * d)
    *)
    val neginf_x0_less_ud = EQ_MP Fneginf_x0_less_ud Fx0_less_ud
    (* have subtract_to_small
                            |- !x d. 0 < d ==>
                                     ?k. 0 < x - k * d /\ x - k * d <= d
       so specialise this with x0 - u * d and delta_tm, and then MP with
       zero_lt_delta to get
         (exists_small_k)   |- ?k. 0 < x0 - u * d - k * d   /\
                                   x0 - u * d - k * d <= d
    *)
    val exists_small_k =
      MP (SPECL [x0_less_ud_tm, delta_tm] change_to_extreme) zero_lt_delta
    (*
       choose k, to get
         (choose_k)         |- 0 < x0 - u * d - k * d /\ x0 - u*d - k*d <= d
    *)
    val k = genvar int_ty
    val choose_k = let
      val (exvar, exbody) = dest_exists (concl exists_small_k)
    in
      ASSUME (subst [exvar |-> k] exbody)
    end
    val u0_less_crap = rand (rand (rator (concl choose_k)))
    val neginf_crap_eq = SPECL [k, x0_less_ud_tm] lemma2
    val neginfo_crap = EQ_MP (SYM neginf_crap_eq) neginf_x0_less_ud
    val disj1_body = CONJ choose_k neginfo_crap
    val disj1_exists = EXISTS(disj1, u0_less_crap) disj1_body
    val disj1_or_disj2 = DISJ1 disj1_exists disj2
    (* now start discharging the choose obligations *)
    val res0 = CHOOSE (k, exists_small_k) disj1_or_disj2
    val res1 = CHOOSE (u, little_c_ex) res0
    val res2 = CHOOSE (y, lemma) res1
    (* and do disj_cases on excluded_middle *)
    val res3 = DISJ_CASES disj2_exm positive_disj2 res2
    (* choose on x0 to get an existential assumption *)
    val res4 = CHOOSE (x0, ASSUME (mk_exists(Bvar, Fx))) res3
  in
    CONV_RULE (LAND_CONV (BINDER_CONV BETA_CONV)) (DISCH_ALL res4)
  end
in
  IMP_ANTISYM_RULE exFx_implies_rhs rhs_implies_exFx
end

fun phase5_CONV defer_dexpansion = let
  (* have something of the form
       (?x. 0 < x /\ x <= k /\ neginf x) \/
       (?b k. MEM b [..] /\ 0 < k /\ k <= d /\ F (b + k))
  *)
  fun remove_vacuous_existential tm = let
    (* term is of form  ?x. x = e *)
    val value = rhs (#2 (dest_exists tm))
    val thm = ISPEC value EXISTS_REFL
  in
    EQT_INTRO thm
  end
  fun expand tm =
    ((REWR_CONV RIGHT_AND_OVER_OR THENC BINOP_CONV expand) ORELSEC
     ALL_CONV) tm
  fun EVERY_DISJ_CONV c tm =
    if is_disj tm then
      BINOP_CONV (EVERY_DISJ_CONV c) tm
    else c tm
  fun under_single_quantifier tm = let
    val (bvar, body) = dest_exists tm
  in
    BINDER_CONV (RAND_CONV (mk_abs_CONV bvar)) THENC
    REWR_CONV UNWIND_THM2 THENC BETA_CONV
  end tm

  val do_expanding_lhs =
    LAND_CONV (BINDER_CONV (LAND_CONV resquan_remove THENC expand) THENC
               TOP_DEPTH_CONV EXISTS_OR_CONV THENC
               EVERY_DISJ_CONV (under_single_quantifier THENC BETA_CONV)) THENC
    REWRITE_CONV []

  fun do_delta_eliminating_lhs continuation tm = let
    (* if there is a "conjunct" at the top level of the neginf term of the
       form
         c | x [ + d]
       where x is the bound variable of the neginf abstraction, and where
       d, if present at all, is a numeral, then we can reduce the number
       of cases needed to be considered, using the theorem
       int_arithTheory.gcdthm2. *)
    val (lhs_t, _) = dest_disj tm
    val (lhs_var, lhs_body) = dest_exists lhs_t
    val neginf_applied = rand lhs_body
    val neginf = rator neginf_applied
    val (neginf_absvar, neginf_body) = dest_abs neginf
    val body_conjuncts = cpstrip_conj neginf_body
    fun simple_divides tm = let
      val (l,r) = dest_divides tm
    in
      free_vars r = [neginf_absvar]
    end handle HOL_ERR _ => false
    fun find_sdivides c tm = let
      val (l,r) = dest_conj tm
    in
      if List.exists simple_divides (cpstrip_conj l) then
        LAND_CONV (find_sdivides c) tm
      else
        RAND_CONV (find_sdivides c) tm
    end handle HOL_ERR _ => let
      val tm0 = dest_neg tm
    in
      if is_neg tm0 then
        (REWR_CONV NOT_NOT_P THENC find_sdivides c) tm
      else (REWR_CONV NOT_OR THENC find_sdivides c) tm
    end handle HOL_ERR _ => (* must be there *) c tm

    val gcd_t = prim_mk_const {Thy = "gcd", Name = "gcd"}

    fun elim_sdivides tm0 = let
      (* term of form c | x + d *)
      val (l,r) = dest_divides tm0
      val normalise_plus_thm =
        (if not (is_plus r) then RAND_CONV (REWR_CONV (GSYM INT_ADD_RID))
         else ALL_CONV) tm0
      val tm1 = rhs (concl normalise_plus_thm)
      val normalised_thm = let
        val (lp,_) = dest_plus (rand tm1)
      in
        if not (is_mult lp) then
          TRANS normalise_plus_thm
          (RAND_CONV (LAND_CONV (REWR_CONV (GSYM INT_MUL_LID))) tm1)
        else
          normalise_plus_thm
      end
      val tm = rhs (concl normalised_thm)
      val r = rand tm
      val m = l
      val m_nt = rand l
      val (a,b) = let
        val (lp,rp) = dest_plus r
      in
        (#1 (dest_mult lp), rp)
      end
      (* gcdthm2 of the form
            m | ax + b  = d | b /\ ?t. ...
         where d is the gcd of m and a *)
      val a_nt = dest_injected a
      val m_n = numSyntax.dest_numeral m_nt
      val a_n = numSyntax.dest_numeral a_nt
      val (d_n, (x_i, y_i)) = extended_gcd(m_n, a_n)
      (* x_i * m_n + y_i * a_n = d_n *)
      val m_nonz =
        EQT_ELIM (REDUCE_CONV (mk_neg(mk_eq(m_nt,numSyntax.zero_tm))))
      val a_nonz =
        EQT_ELIM (REDUCE_CONV (mk_neg(mk_eq(a_nt,numSyntax.zero_tm))))
      val pa_qm = mk_plus(mk_mult(term_of_int y_i, a),
                          mk_mult(term_of_int x_i, m))
      val pa_qm_eq_d = REDUCE_CONV pa_qm
      val rwt =
        if d_n = Arbnum.one then let
          val hyp = LIST_CONJ [pa_qm_eq_d, m_nonz, a_nonz]
        in
          MATCH_MP gcd21_thm hyp
        end
        else let
          val d_eq_pa_qm = SYM pa_qm_eq_d
          val gcd_eq_d = REDUCE_CONV (list_mk_comb(gcd_t, [a_nt, m_nt]))
          val d_eq_gcd = SYM gcd_eq_d
          val d_nonz =
            EQT_ELIM (REDUCE_CONV (mk_neg(mk_eq(rhs (concl gcd_eq_d),
                                                numSyntax.zero_tm))))
        in
          MATCH_MP gcdthm2 (LIST_CONJ [d_eq_gcd, d_eq_pa_qm, d_nonz,
                                       m_nonz, a_nonz])
        end
      val replaced = REWR_CONV rwt THENC REDUCE_CONV THENC
                     ONCE_REWRITE_CONV [INT_MUL_COMM] THENC
                     ONCE_REWRITE_CONV [INT_ADD_COMM]
    in
      TRANS normalised_thm (replaced tm)
    end
    fun pull_out_exists tm = let
      val (c1, c2) = dest_conj tm
      val (cvl, thm) =
        if has_exists c1 then (LAND_CONV, GSYM LEFT_EXISTS_AND_THM)
        else (RAND_CONV, GSYM RIGHT_EXISTS_AND_THM)
    in
      (cvl pull_out_exists THENC HO_REWR_CONV thm) tm
    end handle HOL_ERR _ =>
      if is_exists tm then ALL_CONV tm
      else NO_CONV tm

    val simplify_constraints = let
      (* applied to term of the form    0 < e /\ e <= d
         where e is generally of the form    c * x [+ b]
      *)
      fun elim_coeff tm = let
        (* term of form    d < c * x,  d may be negative, c is +ve digit *)
        val r = rand tm (* i.e., &c * x *)
        val c = rand (rand (rator r))
        val cnonz = EQF_ELIM (REDUCE_CONV (mk_eq(c,numSyntax.zero_tm)))
      in
        if is_negated (rand (rator tm)) then        (* ~d < c * x *)
          REWR_CONV (GSYM INT_LT_NEG) THENC         (* ~(c * x) < ~~d *)
          RAND_CONV (REWR_CONV INT_NEGNEG) THENC    (* ~(c * x) < d *)
          LAND_CONV (REWR_CONV INT_NEG_MINUS1 THENC (* ~1 * (c * x) < d *)
                     REWR_CONV INT_MUL_COMM THENC   (* (c * x) * ~1 < d *)
                     REWR_CONV (GSYM INT_MUL_ASSOC)) THENC
                                                    (* c * (x * ~1) < d *)
          REWR_CONV (MATCH_MP elim_lt_coeffs2 cnonz) THENC
                                                    (* x * ~1 < if ... *)
          REWR_CONV (GSYM INT_LT_NEG) THENC         (* ~(if ..) < ~(x * ~1) *)
          RAND_CONV (REWR_CONV INT_NEG_RMUL THENC   (* ... < x * ~~1 *)
                     RAND_CONV (REWR_CONV INT_NEGNEG) THENC
                                                    (* ... < x * 1 *)
                     REWR_CONV INT_MUL_RID) THENC
          REDUCE_CONV
        else
          REWR_CONV (MATCH_MP elim_lt_coeffs1 cnonz) THENC
          REDUCE_CONV
      end tm
      val do_lt_case =
        (* deal with tm of form   e < c * x [+ b] *)
        move_terms_from LT Right (null o free_vars) THENC
        REDUCE_CONV THENC elim_coeff
    in
      LAND_CONV do_lt_case THENC
      RAND_CONV (REWR_CONV elim_le THENC
                 RAND_CONV do_lt_case THENC
                 REWR_CONV (GSYM elim_le))
    end

    fun protect tm = let
      (* turn tm into (\x. tm) x *)
      val gv = genvar int_ty
    in
      SYM (BETA_CONV (mk_comb(mk_abs(gv,tm), gv)))
    end

    fun find_abs c tm =
      if is_comb tm andalso is_abs (rator tm) then
        (BETA_CONV THENC c) tm
      else LAND_CONV (BETA_CONV THENC c) tm

    fun simp_if_rangeonly tm = let
      val (bv, body) = dest_exists tm
    in
      if length (strip_conj body) = 2 then
        BINDER_CONV resquan_onestep THENC
        EXISTS_OR_CONV THENC
        LAND_CONV remove_vacuous_existential THENC
        REWR_CONV T_or_l
      else
        ALL_CONV
    end tm

    fun pull_eliminate tm =
      (* it's possible that there is no existential to pull out because
         elim_sdivides will have rewritten the divides term to false. *)
      if has_exists (rand tm) then
        (BINDER_CONV pull_out_exists THENC
         SWAP_VARS_CONV THENC
         BINDER_CONV (BINDER_CONV (LAND_CONV protect) THENC
                      Unwind.UNWIND_EXISTS_CONV) THENC
         BINDER_CONV (find_abs simplify_constraints) THENC
         simp_if_rangeonly) tm
      else
        REWRITE_CONV [] tm

    fun absify_and_continue tm = let
      val (l,r) = dest_disj tm
      val (bv, body) = dest_exists l
    in
      (LAND_CONV (BINDER_CONV (RAND_CONV (mk_abs_CONV bv))) THENC
       continuation) tm
    end handle HOL_ERR _ => REWRITE_CONV [] tm

  in
    if List.exists simple_divides body_conjuncts then
      LAND_CONV (BINDER_CONV
                 (RAND_CONV (BETA_CONV THENC
                             find_sdivides elim_sdivides)) THENC
                 pull_eliminate) THENC
      absify_and_continue
    else
      NO_CONV
  end tm

  fun do_nonexpanding_lhs tm = let
    (* this one looks at the lhs and sees if the neginf predicate has
       the abstracted variable free in its body.  If so, the restricted
       quantification reduces to true, and the lhs reduces to the body
       of neginf *)
    val (lhs_t,_) = dest_disj tm
    val (lhs_var,lhs_body) = dest_exists lhs_t
    val neginf_var = rand lhs_body
    val neginf = rator neginf_var
    val (neginf_absvar, neginf_body) = dest_abs neginf

  in
    if free_in neginf_absvar neginf_body then
      NO_CONV
    else
      (* recall that lhs =  ?j. (0 < j /\ j <= delta) /\ P j *)
      LAND_CONV (BINDER_CONV (RAND_CONV BETA_CONV) THENC
                 EXISTS_AND_CONV THENC
                 LAND_CONV (BINDER_CONV resquan_onestep THENC
                            EXISTS_OR_CONV THENC
                            LAND_CONV remove_vacuous_existential THENC
                            REWR_CONV T_or_l) THENC
                 REWR_CONV T_and_l) THENC
      REWRITE_CONV []
  end tm


  fun do_lhs tm =
    (do_nonexpanding_lhs ORELSEC do_delta_eliminating_lhs do_lhs ORELSEC
     do_expanding_lhs) tm
  val prc_conv = PURE_REWRITE_CONV [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR,
                                    listTheory.MEM, OR_CLAUSES, AND_CLAUSES,
                                    NOT_CLAUSES]

  fun under_two_quantifiers tm = let
    val (bvar, body) = dest_exists tm
    val c =
      LAND_CONV (REWR_CONV CONJ_COMM) THENC REWR_CONV (GSYM CONJ_ASSOC) THENC
      RAND_CONV (mk_abs_CONV bvar)
  in
    BINDER_CONV c THENC REWR_CONV UNWIND_THM2 THENC
    BETA_CONV
  end tm

  fun do_rhs tm = let
    val f = if is_disj tm then RAND_CONV
            else if is_exists tm then I
            else K ALL_CONV
    val c =
      STRIP_QUANT_CONV
      (LAND_CONV (RAND_CONV resquan_remove THENC prc_conv) THENC expand) THENC
      ((STRIP_QUANT_CONV (REWR_CONV F_and_l) THENC REWRITE_CONV []) ORELSEC
       (TOP_DEPTH_CONV EXISTS_OR_CONV THENC
        EVERY_DISJ_CONV (BINDER_CONV under_two_quantifiers THENC
                         under_single_quantifier THENC
                         RAND_CONV (REWRITE_CONV [int_sub] THENC
                                    TRY_CONV collect_additive_consts) THENC
                         BETA_CONV)))
  in
    f c tm
  end
in
  do_lhs THENC do_rhs THENC
  ADDITIVE_TERMS_CONV (TRY_CONV collect_additive_consts)
end

val obvious_improvements = ALL_CONV
  (* simpLib.SIMP_CONV int_ss [INT_LT_REFL, INT_NEG_0, INT_DIVIDES_MUL,
                            INT_ADD_LID, INT_ADD_RID, INT_LT_ADD_NUMERAL,
                            INT_LT_LADD, INT_DIVIDES_1,
                            INT_DIVIDES_RADD, INT_DIVIDES_LMUL,
                            INT_DIVIDES_LADD, INT_DIVIDES_LSUB,
                            INT_DIVIDES_RSUB] *)



fun optpluck P l = SOME (Lib.pluck P l) handle HOL_ERR _ => NONE


fun do_equality_simplifications tm = let
  (* term is existentially quantified.  May contain leaf terms of the form
     v = e, where v is the variable quantified.  If there is such a term at
     the top level of conjuncts, then use UNWIND_CONV to eliminate the
     quantifier entirely, otherwise, descend the term looking for such
     terms in the middle of conjunctions and eliminate the equality from the
     neighbouring conjuncts. *)
  val (bvar, body) = dest_exists tm
  fun eq_term tm = is_eq tm andalso lhs tm = bvar
  fun neq_term t = eq_term (dest_neg t) handle HOL_ERR _ => false

  fun reveal_eq tm = let
    (* tm is a "conjunctive" term, in which there is an equality of the
       form (bvar = e).

       Our mission, should we choose to accept it, is to selectively rewrite
       with de-morgan's thm to reveal the tm to  be of the form:
           P /\ Q /\ (bvar = e) /\ R
    *)
    val (c1,c2) = dest_conj tm
    (* easy case because the top level operator is already correct *)
    val subconv =
      if List.exists eq_term (cpstrip_conj c1) then LAND_CONV
      else RAND_CONV
  in
    subconv reveal_eq tm
  end handle HOL_ERR _ => let
    val tm0 = dest_neg tm
  in
    if is_neg tm0 then
      (REWR_CONV NOT_NOT_P THENC reveal_eq) tm
    else (* must be a disjunction *)
      (REWR_CONV NOT_OR THENC reveal_eq) tm
  end handle HOL_ERR _ => ALL_CONV tm

  fun reveal_neq tm = let
    (* tm is a "disjunctive" term in which there is a negated equality *)
    val (d1,d2) = dest_disj tm
    val subconv = if List.exists neq_term (cpstrip_disj d1) then LAND_CONV
                  else RAND_CONV
  in
    subconv reveal_neq tm
  end handle HOL_ERR _ => let
    val tm0 = dest_neg tm
  in
    if is_neg tm0 then
      (REWR_CONV NOT_NOT_P THENC reveal_neq) tm
    else if is_conj tm0 then
      (REWR_CONV NOT_AND THENC reveal_neq) tm
    else ALL_CONV tm
  end handle HOL_ERR _ => ALL_CONV tm

  fun descend_and_eliminate tm =
    if is_conj tm then
      if List.exists eq_term (cpstrip_conj tm) then let
        val revealed = reveal_eq tm
        val revealed_t = rhs (concl revealed)
        val (eqt, rest) = valOf (optpluck eq_term (strip_conj revealed_t))
        val rearranged_t = mk_conj(eqt, list_mk_conj rest)
        val rearranged = EQT_ELIM (AC_CONV (CONJ_ASSOC, CONJ_COMM)
                                   (mk_eq(revealed_t, rearranged_t)))
        val eliminated =
          (RAND_CONV (mk_abs_CONV bvar) THENC
           REWR_CONV CONJ_EQ_ELIM THENC
           RAND_CONV BETA_CONV) rearranged_t
      in
        TRANS (TRANS revealed rearranged) eliminated
      end
      else
        cpEVERY_CONJ_CONV descend_and_eliminate tm
    else if is_disj tm then
      if List.exists neq_term (cpstrip_disj tm) then let
        val revealed = reveal_neq tm
        val revealed_t = rhs (concl revealed)
        val (eqt, rest) = valOf (optpluck neq_term (strip_disj revealed_t))
        val rearranged_t = mk_disj(eqt, list_mk_disj rest)
        val rearranged = EQT_ELIM (AC_CONV (DISJ_ASSOC, DISJ_COMM)
                                   (mk_eq(revealed_t, rearranged_t)))
        val eliminated =
          (RAND_CONV (mk_abs_CONV bvar) THENC
           REWR_CONV DISJ_NEQ_ELIM THENC
           RAND_CONV BETA_CONV) rearranged_t
      in
        TRANS (TRANS revealed rearranged) eliminated
      end
      else
        cpEVERY_DISJ_CONV descend_and_eliminate tm
    else if is_neg tm then
      RAND_CONV descend_and_eliminate tm
    else ALL_CONV tm
in
  if List.exists eq_term (cpstrip_conj body) then
    BINDER_CONV reveal_eq THENC Unwind.UNWIND_EXISTS_CONV
  else
    BINDER_CONV descend_and_eliminate
end tm

fun reveal_a_disj tm =
  if is_disj tm then ALL_CONV tm
  else let
    val tm0 = dest_neg tm
  in
    if is_conj tm0 then REWR_CONV NOT_AND tm
    else (REWR_CONV NOT_NOT_P THENC reveal_a_disj) tm
  end

local
  fun stop_if_exelim tm =
    if is_exists tm then NO_CONV tm
    else REDUCE_CONV tm
in
  fun eliminate_existential tm = let
    val (bvar, body) = dest_exists tm
      handle HOL_ERR _ =>
        raise ERR "eliminate_existential" "term not an exists"
    val base_case =
      BINDER_CONV (phase2_CONV bvar THENC
                   REPEATC (CHANGED_CONV congruential_simplification) THENC
                   REDUCE_CONV) THENC
      ((REWR_CONV EXISTS_SIMP THENC REWRITE_CONV []) ORELSEC
       (phase3_CONV THENC do_equality_simplifications THENC
        (stop_if_exelim ORELSEC (phase4_CONV THENC phase5_CONV false))))
  in
    if cpis_disj body then
      BINDER_CONV reveal_a_disj THENC EXISTS_OR_CONV THENC
      (RAND_CONV eliminate_existential) THENC
      (LAND_CONV eliminate_existential)
    else
      base_case (* THENC obvious_improvements *)
  end tm
end



fun eliminate_quantifier tm = let
(* assume that there are no quantifiers below the one we're eliminating *)
in
  if is_forall tm then
    flip_forall THENC RAND_CONV eliminate_existential
  else if is_exists tm then
    eliminate_existential
  else if is_exists1 tm then
    HO_REWR_CONV cpEU_THM THENC
    RAND_CONV (BINDER_CONV eliminate_quantifier THENC
               eliminate_quantifier) THENC
    RATOR_CONV (RAND_CONV eliminate_quantifier)
  else
    raise ERR "eliminate_quantifier"
      "Not a forall or an exists or a unique exists"
end tm

fun find_low_quantifier tm = let
  fun underc g f =
    case f of
      NONE => NONE
    | SOME f' => SOME (g o f')
in
  if (is_forall tm orelse is_exists tm orelse is_exists1 tm) then
    case find_low_quantifier (#2 (dest_abs (#2 (dest_comb tm)))) of
      NONE => SOME I
    | x => underc BINDER_CONV x
  else if is_comb tm then
    case find_low_quantifier (rand tm) of
      NONE => underc RATOR_CONV (find_low_quantifier (rator tm))
    | x => underc RAND_CONV x
  else
    NONE
end

fun myfind f [] = NONE
  | myfind f (h::t) = case f h of NONE => myfind f t | x => x

fun find_equality tm = let
  (* if there is an equality term as a conjunct underneath any number of
     disjuncts, then return one of the free variables of that equality *)
  fun check_conj tm =
    if is_eq tm then let
      val fvs = free_vars tm
    in
      if not (null fvs) then SOME (hd fvs) else NONE
    end else NONE
in
  myfind check_conj (cpstrip_conj tm)
end

fun LAST_EXISTS_CONV c tm = let
  val (bv, body) = dest_exists tm
in
  if is_exists body then BINDER_CONV (LAST_EXISTS_CONV c) tm
  else c tm
end

fun pure_goal tm = let
  (* pure_goal is called on those goals that have all existential
     quantifiers; these are assumed to be at the head of the term  *)
  val (vars, body) = strip_exists tm
  fun push_in_exists tm =
    if is_exists tm then
      (BINDER_CONV push_in_exists THENC
       EXISTS_OR_CONV) tm
    else
      ALL_CONV tm
  fun push_var_to_bot v tm = let
    val (bv, body) = dest_exists tm
  in
    if bv = v then (SWAP_VARS_CONV THENC
                    BINDER_CONV (push_var_to_bot v) ORELSEC
                    ALL_CONV)
    else (BINDER_CONV (push_var_to_bot v))
  end tm
  fun smallest_var () = let
    val var_counts = count_vars body
    fun recurse (m as (v0,c0)) l =
      case l of
        [] => v0
      | ((e as (v,c))::t) => if c <= c0 then recurse e t
                             else recurse m t
  in
    SOME (mk_var(recurse (hd var_counts) (tl var_counts), int_ty))
  end handle Empty => NONE  (* Empty can happen if there are
                               no variables left in the term *)
in
  if null vars then REDUCE_CONV
  else if cpis_disj body then
    STRIP_QUANT_CONV reveal_a_disj THENC
    push_in_exists THENC BINOP_CONV pure_goal THENC
    REDUCE_CONV
  else let
    val next_var =
      case find_equality body of
        NONE => let
        in
          case smallest_var() of
            NONE => NONE
          | x => x
        end
      | x => x
  in
    case next_var of
      NONE => REWRITE_CONV [EXISTS_SIMP] THENC REDUCE_CONV
    | SOME v =>
          push_var_to_bot v THENC
          LAST_EXISTS_CONV eliminate_existential THENC
          pure_goal
  end
end tm

fun decide_pure_presburger_term tm0 = let
  (* no free variables allowed *)
  val phase0_CONV =
    (* rewrites out conditional expression and absolute value terms *)
    REWRITE_CONV [INT_ABS] THENC Sub_and_cond.COND_ELIM_CONV
  val initial_thm = (phase0_CONV THENC phase1_CONV) tm0
  val tm = rhs (concl initial_thm)
  val qtype = goal_qtype tm
  val prelims =
    case qtype of
      NEITHER => ALL_CONV
    | EITHER => ALL_CONV
    | qsUNIV => (move_quants_up THENC flip_foralls)
    | qsEXISTS => move_quants_up

  fun mainwork tm = let
  in
    case find_low_quantifier tm of
      NONE => REDUCE_CONV
    | SOME f =>
        f eliminate_quantifier THENC
        REWRITE_CONV [] THENC mainwork
  end tm
  val strategy =
    case qtype of
      NEITHER => mainwork
    | EITHER => REDUCE_CONV
    | qsUNIV =>
        move_quants_up THENC flip_foralls THENC
        RAND_CONV pure_goal THENC REDUCE_CONV
    | qsEXISTS => move_quants_up THENC pure_goal
in
  TRANS initial_thm (strategy tm)
end

(* the following is useful in debugging the above; given an f, the
   function term_at_f will return the term "living" at f, as long as there
   are no terms of the form (I tm) in the original.
     local fun I_CONV tm = SYM (ISPEC tm combinTheory.I_THM)
           val I_tm = Term`I:bool->bool b`
     in
       fun term_at_f f tm =
         rand (find_term (can (match_term I_tm)) (rhs (concl (f I_CONV tm))))
     end
   another useful function is this, which allows for the elimination
   of the specified number of quantifiers:
     fun elim_nqs n tm = let
     in
       if n <= 0 then ALL_CONV
       else
          case find_low_quantifier tm of
            NONE => ALL_CONV
          | SOME f => f eliminate_quantifier THENC REWRITE_CONV [] THENC
                      elim_nqs (n - 1)
     end tm

*)

(* this draws on similar code in Richard Boulton's natural number
   arithmetic decision procedure *)

fun contains_var tm = can (find_term is_var) tm
fun is_linear_mult tm =
  is_mult tm andalso
  not (contains_var (rand tm) andalso contains_var (rand (rator tm)))
fun land tm = rand (rator tm)

(* returns a list of pairs, where the first element of each pair is a non-
   Presburger term that occurs in tm, and where the second is a boolean
   that is true if none of the variables that occur in the term are
   bound by a quantifier. *)
fun non_presburger_subterms0 ctxt tm =
  if
    (is_forall tm orelse is_exists1 tm orelse is_exists tm) andalso
    (type_of (bvar (rand tm)) = int_ty)
  then let
    val abst = rand tm
  in
    non_presburger_subterms0 (Lib.union [bvar abst] ctxt) (body abst)
  end
  else if is_neg tm orelse is_absval tm orelse is_negated tm then
    non_presburger_subterms0 ctxt (rand tm)
  else if (is_cond tm) then let
    val (b, t1, t2) = dest_cond tm
  in
    Lib.U [non_presburger_subterms0 ctxt b, non_presburger_subterms0 ctxt t1,
           non_presburger_subterms0 ctxt t2]
  end
  else if (is_great tm orelse is_geq tm orelse is_eq tm orelse
           is_less tm orelse is_leq tm orelse is_conj tm orelse
           is_disj tm orelse is_imp tm orelse is_plus tm orelse
           is_minus tm orelse is_linear_mult tm) then
    Lib.union (non_presburger_subterms0 ctxt (land tm))
              (non_presburger_subterms0 ctxt (rand tm))
  else if (is_divides tm andalso is_int_literal (land tm)) then
    non_presburger_subterms0 ctxt (rand tm)
  else if is_int_literal tm then []
  else if is_var tm andalso type_of tm = int_ty then []
  else if (tm = true_tm orelse tm = false_tm) then []
  else [(tm, not (List.exists (fn v => free_in v tm) ctxt))]

val is_presburger = null o non_presburger_subterms0 []
val non_presburger_subterms = map #1 o non_presburger_subterms0 []

fun decide_fv_presburger tm = let
  fun is_int_const tm = type_of tm = int_ty andalso is_const tm
  val fvs = free_vars tm @ (Lib.mk_set (find_terms is_int_const tm))
  fun dest_atom tm = dest_const tm handle HOL_ERR _ => dest_var tm
  fun gen(bv, t) =
    if is_var bv then mk_forall(bv, t)
    else let
      val gv = genvar int_ty
    in
      mk_forall(gv, subst [bv |-> gv] t)
    end
in
  if null fvs then
    decide_pure_presburger_term tm
  else let
    val newtm = List.foldr gen tm fvs   (* as there are no non-presburger
                                           sub-terms, all these variables
                                           will be of integer type *)
  in
    EQT_INTRO (SPECL fvs (EQT_ELIM (decide_pure_presburger_term newtm)))
  end handle HOL_ERR _ =>
    raise ERR "INT_ARITH_CONV"
      ("Tried to prove generalised goal (generalising "^
       #1 (dest_atom (hd fvs))^"...) but it was false")
end


fun abs_inj inj_n tm = let
  val gv = genvar int_ty
  val tm1 = subst [inj_n |-> gv] tm
in
  GSYM (BETA_CONV (mk_comb(mk_abs(gv,tm1), inj_n)))
end

fun eliminate_nat_quants tm = let
in
  if is_forall tm orelse is_exists tm orelse is_exists1 tm then let
    val (bvar, body) = dest_abs (rand tm)
  in
    if type_of bvar = num_ty then let
      val inj_bvar = mk_comb(int_injection, bvar)
      val rewrite_qaway =
        REWR_CONV (if is_forall tm then INT_NUM_FORALL
        else if is_exists tm then INT_NUM_EXISTS
             else INT_NUM_UEXISTS) THENC
        BINDER_CONV (RAND_CONV BETA_CONV)
    in
      BINDER_CONV (abs_inj inj_bvar) THENC rewrite_qaway THENC
      BINDER_CONV eliminate_nat_quants
    end
    else
      BINDER_CONV eliminate_nat_quants
  end
    else if is_neg tm then (* must test for is_neg before is_imp *)
      RAND_CONV eliminate_nat_quants
    else if (is_conj tm orelse is_disj tm orelse is_eq tm orelse
             is_imp tm) then
      BINOP_CONV eliminate_nat_quants
    else if is_cond tm then
      RATOR_CONV (RATOR_CONV (RAND_CONV eliminate_nat_quants))
    else ALL_CONV
end tm handle HOL_ERR {origin_function = "REWR_CONV", ...} =>
  raise ERR "ARITH_CONV" "Uneliminable natural number term remains"


val dealwith_nats = let
  open arithmeticTheory
  val rewrites = [GSYM INT_INJ, GSYM INT_LT, GSYM INT_LE,
                  GREATER_DEF, GREATER_EQ, GSYM INT_ADD,
                  GSYM INT_MUL, INT, INT_NUM_COND, INT_NUM_EVEN,
                  INT_NUM_ODD]
in
  Sub_and_cond.SUB_AND_COND_ELIM_CONV THENC PURE_REWRITE_CONV rewrites THENC
  eliminate_nat_quants
end

(* subterms is a list of subterms all of integer type *)
fun decide_nonpbints_presburger subterms tm = let
  fun tactic subtm tm =
    (* return both a new term and a function that will convert a theorem
       of the form <new term> = T into tm = T *)
    if is_comb subtm andalso rator subtm = int_injection then let
      val n = rand subtm
      val thm0 = abs_inj subtm tm (* |- tm = P subtm *)
      val tm0 = rhs (concl thm0)
      val gv = genvar num_ty
      val tm1 = mk_forall(gv, mk_comb (rator tm0, mk_comb(int_injection, gv)))
      val thm1 =  (* |- (!gv. P gv) = !x. 0 <= x ==> P x *)
        (REWR_CONV INT_NUM_FORALL THENC
         BINDER_CONV (RAND_CONV BETA_CONV)) tm1
      fun prove_it thm = let
        val without_true = EQT_ELIM thm (* |- !x. 0 <= x ==> P x *)
        val univ_nat = EQ_MP (SYM thm1) without_true
        val spec_nat = SPEC n univ_nat
      in
        EQT_INTRO (EQ_MP (SYM thm0) spec_nat)
      end
    in
      (rhs (concl thm1), prove_it)
    end
    else let
      val gv = genvar int_ty
    in
      (mk_forall(gv, subst [subtm |-> gv] tm),
       EQT_INTRO o SPEC subtm o EQT_ELIM)
    end
  fun gen_overall_tactic tmlist =
    case tmlist of
      [] => raise Fail "Can't happen in decide_nonpbints_presburger"
    | [t] => tactic t
    | (t::ts) => let
        fun doit base = let
          val (subgoal, vfn) = gen_overall_tactic ts base
          val (finalgoal, vfn') = tactic t subgoal
        in
          (finalgoal, vfn o vfn')
        end
      in
        doit
      end
  val overall_tactic = gen_overall_tactic subterms
  val (goal, vfn) = overall_tactic tm
  val thm = decide_fv_presburger goal
in
  vfn thm handle HOL_ERR _ =>
    raise ERR "ARITH_CONV"
      ("Tried to prove generalised goal (generalising "^
       term_to_string (hd subterms)^"...) but it was false")
end

fun COOPER_CONV tm = let
  fun stage2 tm =
    case non_presburger_subterms0 [] tm of
      [] => decide_fv_presburger tm
    | non_pbs => let
        fun bad_term (t,b) = not b orelse type_of t <> int_ty
      in
        case List.find bad_term non_pbs of
          NONE => decide_nonpbints_presburger (map #1 non_pbs) tm
        | SOME (t,_) => raise ERR "ARITH_CONV"
            ("Not in the allowed subset; consider "^term_to_string t)
      end
in
  dealwith_nats THENC stage2
end tm

val COOPER_PROVE = EQT_ELIM o COOPER_CONV
val COOPER_TAC = CONV_TAC COOPER_CONV;

end;
