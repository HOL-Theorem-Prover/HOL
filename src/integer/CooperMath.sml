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

fun ERR f s = HOL_ERR { origin_function = f,
                        origin_structure = "CooperMath",
                        message = s};

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


fun optpluck P l = SOME (Lib.pluck P l) handle HOL_ERR _ => NONE


fun check_divides tm = let
  val (l,r) = dest_divides tm
  val rterms = strip_plus r
  fun getc t = Arbint.abs (int_of_term (rand (rator t)))
  fun pull_out_divisor tm = let
    val (l,r) = dest_plus tm
  in
    if is_plus l then
      LAND_CONV pull_out_divisor THENC REWR_CONV (GSYM INT_LDISTRIB)
    else
      REWR_CONV (GSYM INT_LDISTRIB)
  end tm handle HOL_ERR _ => ALL_CONV tm
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
          case optpluck is_int_literal rterms of
            NONE =>
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
                NO_CONV
            end
        end
    end tm
end

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




end (* struct *)