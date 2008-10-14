structure CooperMath :> CooperMath = struct

  local open gcdTheory in end

  open HolKernel boolLib intSyntax integerTheory
       int_arithTheory intReduce CooperThms CooperSyntax

  type num = Arbnum.num

  val cooper_compset = int_compset()
  val _ = computeLib.add_thms [gcdTheory.GCD_EFFICIENTLY] cooper_compset
  val REDUCE_CONV = computeLib.CBV_CONV cooper_compset

val ERR = mk_HOL_ERR "CooperMath";

fun lhand t = rand (rator t)

(* Fix the grammar used by this file *)
structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars integer_grammars
end
open Parse

(*---------------------------------------------------------------------------*)
(* Function to compute the Greatest Common Divisor of two integers.          *)
(*---------------------------------------------------------------------------*)

local open Arbint in
fun gcd' i j = let
    val r = i mod j
in  if r = zero then j else gcd' j r
end

fun gcd (i,j) =
    if i < zero orelse j < zero then raise ERR "gcd""negative arguments to gcd"
    else if i = zero then j else if j = zero then i
    else if i < j then gcd' j i else gcd' i j
end (* local *)

fun gcdl l =
  case l of
    [] => raise ERR "gcdl" "empty list"
  | (h::t) => foldl gcd h t

(*---------------------------------------------------------------------------*)
(* Function to compute the Lowest Common Multiple of two integers.           *)
(*---------------------------------------------------------------------------*)

fun lcm (i,j) = let open Arbint in (i * j) div (gcd (i,j)) end
handle _ => raise ERR "lcm" "negative arguments to lcm";

fun lcml ints =
  case ints of
    [] => raise ERR "lcml" "empty list"
  | [x] => x
  | (x::y::xs) => lcml (lcm (x, y)::xs)


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

  val gcd_t = prim_mk_const {Thy = "gcd", Name = "gcd"}

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



  fun elim_sdivides tm0 = let
    (* term of form c | x + d *)
    val (l,r) = dest_divides tm0
    val normalise_plus_thm =
      (if not (is_plus r) then RAND_CONV (REWR_CONV (GSYM INT_ADD_RID))
       else REFL) tm0
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


  val simplify_constraints = let
    (* applied to term of the form    lo < e /\ e <= hi
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



  fun factor_out g g_t tm =
    if is_plus tm then BINOP_CONV (factor_out g g_t) tm
    else let
      open Arbint
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

  fun factor_out_lits g g_t tm =
      if is_plus tm then BINOP_CONV (factor_out_lits g g_t) tm
      else if is_int_literal tm then let
          val tm_i = int_of_term tm
          val factor = Arbint.div(tm_i, g)
          val factor_t = term_of_int factor
        in
          SYM (REDUCE_CONV (mk_mult(g_t, factor_t)))
        end
      else REFL tm


fun check_divides tm = let
  val (l,r) = dest_divides tm
  val rterms = strip_plus r
  fun getc t = Arbint.abs (int_of_term (rand (rator t)))
  fun pull_out_divisor tm =
    TRY_CONV (BINOP_CONV pull_out_divisor THENC
              REWR_CONV (GSYM INT_LDISTRIB)) tm
in
  case List.mapPartial (Lib.total getc) rterms of
    [] => CHANGED_CONV REDUCE_CONV tm
  | cs => let
      val g = gcdl (int_of_term l :: cs)
    in
      if g <> Arbint.one then let
          val g_t = term_of_int g
          val g_t_lt0 = EQT_ELIM (REDUCE_CONV (mk_less(zero_tm, g_t)))
          val divq = Arbint.div(int_of_term l, g)
          val divisor_ok = SYM (REDUCE_CONV (mk_mult(g_t, term_of_int divq)))
        in
          case Lib.total (Lib.pluck is_int_literal) rterms of
            NONE =>
              (* note that factor_out g g_t always changes the term as
                 far as QConv.THENQC is concerned, so the first line
                 below can not raise QConv.UNCHANGED *)
              RAND_CONV (factor_out g g_t THENC pull_out_divisor) THENC
              LAND_CONV (K divisor_ok) THENC
              REWR_CONV (GSYM (MATCH_MP justify_divides g_t_lt0)) THENC
              REWRITE_CONV [INT_DIVIDES_1]
          | SOME(literal,rest) => let
              val literal_i = int_of_term literal
              val (litq, litr) = Arbint.divmod(literal_i, g)
              val sorted =
                  EQT_ELIM (AC_CONV (INT_ADD_ASSOC, INT_ADD_COMM)
                                    (mk_eq(r,
                                           mk_plus(list_mk_plus rest,
                                                   literal))))
            in
              if litr = Arbint.zero then let
                  val literal_ok =
                      SYM (REDUCE_CONV (mk_mult(g_t, term_of_int litq)))
                in
                  RAND_CONV (K sorted THENC
                             factor_out g g_t THENC
                             RAND_CONV (K literal_ok) THENC
                             pull_out_divisor) THENC
                  LAND_CONV (K divisor_ok) THENC
                  REWR_CONV (GSYM (MATCH_MP justify_divides g_t_lt0)) THENC
                  REWRITE_CONV [INT_DIVIDES_1] THENC
                  TRY_CONV check_divides
                end
              else
                RAND_CONV (K sorted THENC
                           factor_out g g_t THENC
                           REWRITE_CONV [GSYM INT_LDISTRIB]) THENC
                LAND_CONV (K divisor_ok) THENC
                REWR_CONV justify_divides2 THENC
                RAND_CONV REDUCE_CONV THENC REWR_CONV F_and_r
            end
        end
      else
        (* gcd is 1, but if l divides any of the summands on the right *)
        (* these can still be eliminated *)
        let
          val li = int_of_term l
          fun getn t = getc t handle HOL_ERR _ => Arbint.abs (int_of_term t)
          val rns = map getn rterms
          fun ldivs t = Arbint.mod(getn t, li) = Arbint.zero
          val (ldivs, lndivs) = partition ldivs rterms
        in
          if not (null ldivs) then let
              val sorted =
                  EQT_ELIM (AC_CONV (INT_ADD_ASSOC, INT_ADD_COMM)
                                    (mk_eq(r,
                                           mk_plus(list_mk_plus ldivs,
                                                   list_mk_plus lndivs))))
            in
              RAND_CONV (K sorted THENC
                         LAND_CONV (factor_out li l THENC
                                    factor_out_lits li l THENC
                                    REWRITE_CONV [GSYM INT_LDISTRIB])) THENC
              REWR_CONV justify_divides3 THENC
              TRY_CONV check_divides
            end
          else let
              val r_gcd = gcdl rns
            in
              if r_gcd <> Arbint.one then let
                  val r_gcdt = term_of_int r_gcd
                  val gcd_term =
                      list_mk_comb(gcd_t,
                                   [dest_injected l,
                                    numSyntax.mk_numeral (Arbint.toNat r_gcd)])
                in
                  RAND_CONV (factor_out r_gcd r_gcdt THENC
                             factor_out_lits r_gcd r_gcdt THENC
                             REWRITE_CONV [GSYM INT_LDISTRIB]) THENC
                  REWR_CONV
                     (MATCH_MP INT_DIVIDES_RELPRIME_MUL
                               (REDUCE_CONV gcd_term))
                end
              else
                ALL_CONV
            end
        end
    end tm
end

fun EVERY_SUMMAND_CONV c t =
    if is_plus t then BINOP_CONV (EVERY_SUMMAND_CONV c) t
    else c t


fun minimise_divides tm = let
  val (l,r) = dest_divides tm
  val l_i = int_of_term l
  val _ = Arbint.<(Arbint.zero, l_i) orelse
          raise ERR "minimise_divides" "LHS of divides not positive"
  fun rhs_ok t = let
    val (l,r) = dest_plus t
  in
    rhs_ok l andalso rhs_ok r
  end handle HOL_ERR _ => let
               val c = #1 (dest_mult t) handle HOL_ERR _ => t
               val ci = int_of_term c
               open Arbint
             in
               zero <= ci andalso ci < l_i
             end
  val _ = not (rhs_ok r) orelse raise UNCHANGED
  fun split_summand t = let
    val ((c, v), cval) = (dest_mult t, LAND_CONV)
        handle HOL_ERR _ => ((t, one_tm), I)
    val c_i = int_of_term c
    val (d, m) = Arbint.divmod(c_i, l_i)
    val _ = d <> Arbint.zero orelse raise UNCHANGED
    val ld_pl_m =
        SYM (REDUCE_CONV (mk_plus(mk_mult(l, term_of_int d), term_of_int m)))
  in
    cval (K ld_pl_m) THENC
    TRY_CONV (REWR_CONV INT_RDISTRIB THENC
               LAND_CONV (REWR_CONV (GSYM INT_MUL_ASSOC)))
  end t
  fun sort1 tm = let
    (* tm is of form (l * x + y) + z, Here we add z to the appropriate
       sub-term *)
    val z = rand tm
  in
    if (lhand z = l handle HOL_ERR _ => false) then
      REWR_CONV INT_ADD_COMM THENC REWR_CONV INT_ADD_ASSOC THENC
      LAND_CONV (REWR_CONV (GSYM INT_LDISTRIB))
    else REWR_CONV (GSYM INT_ADD_ASSOC)
  end tm
  fun sort tm =
      if is_plus tm then (LAND_CONV sort THENC sort1) tm
      else (REWR_CONV (GSYM INT_ADD_LID) THENC
            LAND_CONV (REWR_CONV (GSYM INT_ADD_LID) THENC
                       LAND_CONV (K (SYM (SPEC l INT_MUL_RZERO)))) THENC
            sort1) tm
in
  RAND_CONV (EVERY_SUMMAND_CONV split_summand THENC
             REWRITE_CONV [INT_ADD_ASSOC] THENC sort) THENC
  REWR_CONV int_arithTheory.justify_divides3 THENC
  REWRITE_CONV [INT_ADD_LID, INT_ADD_RID, INT_MUL_LZERO]
end tm


fun elim_paired_divides tm = let
  val (c1, c2) = dest_conj tm
  val (mi, ax_b) = dest_divides c1
  val (ni, ux_v) = dest_divides c2
  val (ax, b) = dest_plus ax_b
  val (ux, v) = dest_plus ux_v
  val (ai, x)  = dest_mult ax
  val (ui, _)  = dest_mult ux
  val a = dest_injected ai
  val u = dest_injected ui
  val m = dest_injected mi
  val n = dest_injected ni
  val m_nzero = EQT_ELIM (REDUCE_CONV (mk_neg(mk_eq(m, numSyntax.zero_tm))))
  val n_nzero = EQT_ELIM (REDUCE_CONV (mk_neg(mk_eq(n, numSyntax.zero_tm))))
  val a_nzero = EQT_ELIM (REDUCE_CONV (mk_neg(mk_eq(a, numSyntax.zero_tm))))
  val u_nzero = EQT_ELIM (REDUCE_CONV (mk_neg(mk_eq(u, numSyntax.zero_tm))))
  val um = numSyntax.mk_mult(u,m)
  val an = numSyntax.mk_mult(a,n)
  val d_eq_gcd = SYM (REDUCE_CONV (list_mk_comb(gcd_t, [um,an])))
  val (d_an,(p_ai,q_ai)) =
      extended_gcd (Arbint.toNat (Arbint.*(int_of_term ui, int_of_term mi)),
                    Arbint.toNat (Arbint.*(int_of_term ai, int_of_term ni)))
  val d = lhs (concl d_eq_gcd)
  val di = mk_injected d
  val p = term_of_int p_ai
  val q = term_of_int q_ai
  val pum = list_mk_mult [p, ui, mi]
  val qan = list_mk_mult [q, ai, ni]
  val d_eq_pum_qan = EQT_ELIM (REDUCE_CONV (mk_eq(di, mk_plus(pum, qan))))
  val th0 =
      MATCH_MP cooper_lemma_1
               (LIST_CONJ [d_eq_gcd, d_eq_pum_qan, m_nzero,
                           n_nzero, a_nzero, u_nzero])
  val th = REWR_CONV th0 tm
in
  th
end


val my_INT_MUL_LID = prove(
  ``(1 * (c * d) = c * d) /\
    (~1 * (c * d) = ~c * d) /\
    (1 * (c * d + x) = c * d + x) /\
    (~1 * (c * d + x) = ~c * d + ~x) /\
    (~~x = x)``,
  REWRITE_TAC [INT_MUL_LID, GSYM INT_NEG_MINUS1, INT_NEG_LMUL,
               INT_NEG_ADD, INT_NEGNEG]);


fun BLEAF_CONV connector c tm =
    case bop_characterise tm of
      NONE => c tm
    | SOME NEGN => RAND_CONV (BLEAF_CONV connector c) tm
    | SOME _ => connector(LAND_CONV (BLEAF_CONV connector c),
                          RAND_CONV (BLEAF_CONV connector c))
                         tm




(* ----------------------------------------------------------------------
    Initial phases of the Cooper transformation
   ---------------------------------------------------------------------- *)


(* Phase 1 *)
val remove_bare_vars = let
  fun Munge t = if is_var t then REWR_CONV (GSYM INT_MUL_LID) t
                else if intSyntax.is_mult t then ALL_CONV t
                else NO_CONV t
in
  ONCE_DEPTH_CONV Munge
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
    (* formula must be quantifier free *)
    DEPTH_CONV RED_CONV THENC
    basic_rewrite_conv THENC remove_negated_vars THENC
    remove_bare_vars THENC flip_muls THENC
    DEPTH_CONV RED_CONV THENC REWRITE_CONV []
end

val phase1_CONV = Profile.profile "phase1" phase1_CONV

(* Phase 2 *)
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
         RAND_CONV (TRY_CONV (RAND_CONV collect_up_other_freevars)) THENC
         REWRITE_CONV [INT_MUL_LZERO] THENC REDUCE_CONV) tm
      else ALL_CONV tm
    else ALL_CONV tm
  end
end

val phase2_CONV =
    fn t => Profile.profile "phase2" (QCONV (phase2_CONV t))

(* Phase 3 *)
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
fun LINEAR_MULT tm = let
  (* tm is of form c * (e1 + e2 + ... en), where each
     ei is either a constant, or  c' * v, with v a variable.
     This conversion distributes the c over all the ei's *)
  val _ = if not (is_mult tm) then ignore (NO_CONV tm) else ()

  (* use this rather than is_mult, because the only binops about are
     multiplications *)
  fun is_binop tm = length (#2 (strip_comb tm)) = 2
  fun leaf_case tm =
      if not (is_binop (rand tm)) then REDUCE_CONV tm
      else (REWR_CONV INT_MUL_ASSOC THENC LAND_CONV REDUCE_CONV) tm
  fun recurse tm =
      ((REWR_CONV INT_LDISTRIB THENC BINOP_CONV recurse) ORELSEC leaf_case) tm
in
  recurse tm
end



(* Phase 3 multiplies up all coefficients of x in order to make them
   the lcm, and then eliminates this, by changing
     ?x. P (c * x)
   to
     ?x. P x /\ c | x
*)
(* this phase has to be done at the level of the existential quantifier *)
(* assume that the existential quantifier still has occurrences of the
   bound variable in the body *)
  fun phase3_CONV term = let
    val (var, body) = Psyntax.dest_exists term
    (* first calculate the desired LCM *)
    val coeffs = find_coeffs var body
    val lcm = lcml coeffs
    (* now descend to each less-than term, and update the coefficients of
     var to be the same lcm *)
    fun multiply_by_CONV zero_lti cat =
      case cat of
        rDIV => REWR_CONV (MATCH_MP justify_divides zero_lti) THENC
                RAND_CONV LINEAR_MULT THENC LAND_CONV REDUCE_CONV
      | rLT =>  REWR_CONV (MATCH_MP lt_justify_multiplication zero_lti) THENC
                BINOP_CONV LINEAR_MULT
      | rEQ =>  REWR_CONV (MATCH_MP eq_justify_multiplication zero_lti) THENC
                BINOP_CONV LINEAR_MULT

    fun LCMify term =
      if is_disj term orelse is_conj term then
        BINOP_CONV LCMify term
      else if is_neg term then RAND_CONV LCMify term
      else
        case (find_coeff var term) of
          NONE => ALL_CONV term
        | SOME c => let
            val i = Arbint.div(lcm, c)
          in
            if i = Arbint.one then ALL_CONV term
            else let
                val cat = categorise_leaf term
                val zero_lti =
                    EQT_ELIM (REDUCE_CONV (mk_less(zero_tm, term_of_int i)))
              in
                multiply_by_CONV zero_lti cat
              end term
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
    (BINDER_CONV (LCMify THENC absify_CONV) THENC
     REWR_CONV lcm_eliminate THENC
     RENAME_VARS_CONV [fst (dest_var var)] THENC
     BINDER_CONV (LAND_CONV BETA_CONV) THENC
     eliminate_1divides)
    term
  end

val phase3_CONV = Profile.profile "phase3" phase3_CONV

(* "sophisticated" simplification routines *)
fun simplify_constrained_disjunct tm = let
  (* takes a term of the form
       ?j.   ... /\ K (d1 < j /\ j <= d2) j /\ ...
     and simplifies it *)
  (* if there is a "conjunct" at the top level of the conjuncts of the
     form
       c | x [ + d]
     where x is the bound variable of the neginf abstraction, and where
     d, if present at all, is a numeral, then we can reduce the number
     of cases needed to be considered, using the theorem
     int_arithTheory.gcdthm2. *)
  open CooperSyntax
  val (var, body) = dest_exists tm
  val body_conjuncts = filter (not o is_constraint) (cpstrip_conj body)

  fun find_sdivides v c tm = let
    (* knowing that a simple divides term over variable v is a "conjunct"
       of tm, apply conversion c to that term *)
    val (l,r) = dest_conj tm
  in
    if List.exists (simple_divides v) (cpstrip_conj l) then
      LAND_CONV (find_sdivides v c) tm
    else
      RAND_CONV (find_sdivides v c) tm
  end handle HOL_ERR _ => let
    val tm0 = dest_neg tm
  in
    if is_neg tm0 then
      (REWR_CONV NOT_NOT_P THENC find_sdivides v c) tm
    else (REWR_CONV NOT_OR THENC find_sdivides v c) tm
  end handle HOL_ERR _ => (* must be there *) let
    (* possible that phase2 will eliminate variable entirely, turning the
       term into either true or false *)
    fun check_vars tm = if is_const tm then ALL_CONV tm else c tm
  in
    (phase1_CONV THENC phase2_CONV v THENC check_vars) tm
  end

  fun pull_out_exists tm = let
    (* pulls out a nested existential quantifier to the head of the term *)
    val (c1, c2) = dest_conj tm
    val (cvl, thm) =
      if has_exists c1 then (LAND_CONV, GSYM LEFT_EXISTS_AND_THM)
      else (RAND_CONV, GSYM RIGHT_EXISTS_AND_THM)
  in
    (cvl pull_out_exists THENC HO_REWR_CONV thm) tm
  end handle HOL_ERR _ =>
    if is_exists tm then ALL_CONV tm
    else NO_CONV tm


  fun find_cst v c tm = let
    fun atleaf tm =
        if is_vconstraint v tm then c tm
        else NO_CONV tm
  in
    BLEAF_CONV (op ORELSEC) atleaf tm
  end

  fun simp_if_rangeonly tm = let
    (* simplifies ?x. K (lo < x /\ x <= hi) x  to T, *)
    (* knowing that a contradictory constraint would have already been *)
    (* dealt with *)
    val (bv, body) = dest_exists tm
  in
    if is_constraint body then
      BINDER_CONV (UNCONSTRAIN THENC resquan_onestep) THENC
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
       BINDER_CONV Unwind.UNWIND_EXISTS_CONV THENC
       (fn tm => let val (v, _) = dest_exists tm
                 in
                   BINDER_CONV (find_cst v
                                         (IN_CONSTRAINT simplify_constraints))
                 end tm) THENC
       simp_if_rangeonly) tm
    else
      REWRITE_CONV [] tm

  val mainwork =
    if List.exists (simple_divides var) body_conjuncts then
      Profile.profile "simpcst.mainwork.simpelim" (

      BINDER_CONV (find_sdivides var elim_sdivides) THENC
      pull_eliminate THENC
      (* variable was present in form 1 * v or ~1 * v; have now just replaced it
         with things of the form c * v' [+ c'], so now have bunch of terms of form
         1 * (c * v' [+ y]) or ~1 * (c * v [+ y]); get rid of these *)
      PURE_REWRITE_CONV [my_INT_MUL_LID]) THENC
      (* have another go at this, recursively, but allow for the fact that
         we may have reduced the term to true or false or whatever *)
      TRY_CONV simplify_constrained_disjunct
    else if List.all (not o mem var o free_vars) body_conjuncts then
      (* case where existential only has scope over constraint, and
         bound variable doesn't appear elsewhere, which can happen if
         the F term is something like (\x. F), which tends to happen in
         the construction of the neginf term. *)
      Profile.profile "simpcst.mainwork.vacuous" (
      push_in_exists_and_follow
          (BINDER_CONV (UNCONSTRAIN THENC resquan_onestep) THENC
           EXISTS_OR_CONV THENC
           LAND_CONV remove_vacuous_existential THENC
           REWR_CONV T_or_l) THENC
      REWRITE_CONV []
      )
    else
      ALL_CONV
in
  (BINDER_CONV (Profile.profile "simpcst.quick" (find_cst var quick_cst_elim)) THENC
   (Profile.profile "simpcst.unwind" Unwind.UNWIND_EXISTS_CONV ORELSEC REWRITE_CONV []) THENC
   Profile.profile "simpcst.r_i_g" reduce_if_ground) ORELSEC
  Profile.profile "simpcst.mainwork" mainwork
end tm


end (* struct *)
