structure CooperMath :> CooperMath = struct

  local open gcdTheory
  in
  end

  open HolKernel boolLib intSyntax integerTheory int_arithTheory
  open CooperThms

  infix THENC

  type num = Arbnum.num

  val cooper_compset = intSimps.int_compset()
  val _ = computeLib.add_thms [gcdTheory.GCD_EFFICIENTLY] cooper_compset
  val REDUCE_CONV = computeLib.CBV_CONV cooper_compset

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



end