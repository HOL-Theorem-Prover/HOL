(* ========================================================================= *)
(* Relatively efficient HOL conversions for canonical polynomial form.       *)
(*                   (HOL-Light's normalizer.ml)                             *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                                                                           *)
(*               Ported to HOL4 by Chun Tian, June 2022                      *)
(* ========================================================================= *)

structure Normalizer :> Normalizer =
struct

open HolKernel Parse boolLib boolSimps liteLib
open arithmeticTheory numSyntax Num_conv tautLib Arithconv simpLib
     normalForms
open normalizerTheory

structure Parse = struct
  open Parse
  val (Type,Term) =
      parse_from_grammars $ valOf $ grammarDB {thyname = "arithmetic"}
end

open Parse


val ERR = mk_HOL_ERR "Normalizer"
fun failwith s = raise ERR "?" s

val NUM_ADD_CONV  = ADD_CONV
val NUM_MULT_CONV = MUL_CONV
val NUM_EXP_CONV  = EXP_CONV
val NUM_SUC_CONV  = SUC_CONV
val num_0         = Arbnum.zero
val num_1         = Arbnum.one

val true_tm = boolSyntax.T

(* This is for debugging RealArith or RealField:

   val sth = REAL_POLY_CLAUSES;
   val rth = REAL_POLY_NEG_CLAUSES;
   val (is_semiring_constant,
        SEMIRING_ADD_CONV,
        SEMIRING_MUL_CONV,
        SEMIRING_POW_CONV) =
       (is_realintconst,
        REAL_INT_ADD_CONV,REAL_INT_MUL_CONV,REAL_INT_POW_CONV);
   val variable_order = term_lt;

 OR

   val sth = REAL_POLY_CLAUSES;
   val rth = REAL_POLY_NEG_CLAUSES;
   val (is_semiring_constant,
        SEMIRING_ADD_CONV,
        SEMIRING_MUL_CONV,
        SEMIRING_POW_CONV) =
       (is_ratconst,
        REAL_RAT_ADD_CONV,REAL_RAT_MUL_CONV,REAL_RAT_POW_CONV);
   val variable_order = term_lt;
 *)

(* see NUM_NORMALIZE_CONV below for sample applications *)
fun SEMIRING_NORMALIZERS_CORE
      [pthm_01, (* |- 1 * x = x *)
       pthm_02, (* |- a * m + b * m = (a + b) * m *)
       pthm_03, (* |- a * m + m = (a + 1) * m *)
       pthm_04, (* |- m + a * m = (a + 1) * m *)
       pthm_05, (* |- m + m = (1 + 1) * m *)
       pthm_06, (* |- 0 * m = 0 *)
       pthm_07, (* |- 0 + a = a *)
       pthm_08, (* |- a + 0 = a *)
       pthm_09, (* |- a * b = b * a *)
       pthm_10, (* |- (a + b) * c = a * c + b * c *)
       pthm_11, (* |- 0 * a = 0 *)
       pthm_12, (* |- a * 0 = 0 *)
       pthm_13, (* |- 1 * a = a *)
       pthm_14, (* |- a * 1 = a *)
       pthm_15, (* |- lx * ly * (rx * ry) = lx * rx * (ly * ry) *)
       pthm_16, (* |- lx * ly * (rx * ry) = lx * (ly * (rx * ry)) *)
       pthm_17, (* |- lx * ly * (rx * ry) = rx * (lx * ly * ry) *)
       pthm_18, (* |- lx * ly * rx = lx * rx * ly *)
       pthm_19, (* |- lx * ly * rx = lx * (ly * rx) *)
       pthm_20, (* |- lx * rx = rx * lx *)
       pthm_21, (* |- lx * (rx * ry) = lx * rx * ry *)
       pthm_22, (* |- lx * (rx * ry) = rx * (lx * ry) *)
       pthm_23, (* |- a + b + (c + d) = a + c + (b + d) *)
       pthm_24, (* |- a + b + c = a + (b + c) *)
       pthm_25, (* |- a + (c + d) = c + (a + d) *)
       pthm_26, (* |- a + b + c = a + c + b *)
       pthm_27, (* |- a + c = c + a *)
       pthm_28, (* |- a + (c + d) = a + c + d *)
       pthm_29, (* |- x ** p * x ** q = x ** (p + q) *)
       pthm_30, (* |- x * x ** q = x ** SUC q *)
       pthm_31, (* |- x ** q * x = x ** SUC q *)
       pthm_32, (* |- x * x = x ** 2 *)
       pthm_33, (* |- (x * y) ** q = x ** q * y ** q *)
       pthm_34, (* |- (x ** p) ** q = x ** (p * q) *)
       pthm_35, (* |- x ** 0 = 1 *)
       pthm_36, (* |- x ** 1 = x *)
       pthm_37, (* |- x * (y + z) = x * y + x * z *)
       pthm_38] (* |- x ** SUC q = x * x ** q *)
      rth
      (is_semiring_constant,
       SEMIRING_ADD_CONV,
       SEMIRING_MUL_CONV,
       SEMIRING_POW_CONV)
      variable_order = let

    val add_tm = rator(rator(lhand(concl pthm_07)))
    and mul_tm = rator(rator(lhand(concl pthm_13)))
    and pow_tm = rator(rator(rand(concl pthm_32)))
    and zero_tm = rand(concl pthm_06)
    and one_tm = rand(lhand(concl pthm_14))
    and ty = type_of(rand(concl pthm_01))

    val p_tm = “p:num”
    and q_tm = “q:num”
    and zeron_tm = numSyntax.zero_tm
    and onen_tm = numSyntax.term_of_int 1
    and a_tm = mk_var("a",ty)
    and b_tm = mk_var("b",ty)
    and c_tm = mk_var("c",ty)
    and d_tm = mk_var("d",ty)
    and lx_tm = mk_var("lx",ty)
    and ly_tm = mk_var("ly",ty)
    and m_tm = mk_var("m",ty)
    and rx_tm = mk_var("rx",ty)
    and ry_tm = mk_var("ry",ty)
    and x_tm = mk_var("x",ty)
    and y_tm = mk_var("y",ty)
    and z_tm = mk_var("z",ty)

    val dest_add = dest_binop add_tm
    val dest_mul = dest_binop mul_tm
 (* old definition:
    fun dest_pow tm =
      let val (l,r) = dest_binop pow_tm tm in
      if is_numeral r then (l,r) else failwith "dest_pow" end
  *)
    fun dest_pow tm = dest_binop pow_tm tm

    val is_add = is_binop add_tm
    val is_mul = is_binop mul_tm

    val (nthm_1,nthm_2,sub_tm,neg_tm,dest_sub,is_sub) =
      if concl rth ~~ true_tm then
        (rth,rth,true_tm,true_tm,(fn t => (t,t)),K false)
      else let
        val nthm_1 = SPEC x_tm (CONJUNCT1 rth)
        and nthm_2 = SPECL [x_tm, y_tm] (CONJUNCT2 rth)
        val sub_tm = rator(rator(lhand(concl nthm_2)))
        and neg_tm = rator(lhand(concl nthm_1))
        val dest_sub = dest_binop sub_tm
        and is_sub = is_binop sub_tm
      in
        (nthm_1,nthm_2,sub_tm,neg_tm,dest_sub,is_sub) end

(* ------------------------------------------------------------------------- *)
(* Conversion for "x^n * x^m", with either x^n = x and/or x^m = x possible.  *)
(* Also deals with "const * const", but both terms must involve powers of    *)
(* the same variable, or both be constants, or behaviour may be incorrect.   *)
(* ------------------------------------------------------------------------- *)

    fun POWVAR_MUL_CONV tm = let
      val (l,r) = dest_mul tm in
      if is_semiring_constant l andalso is_semiring_constant r
      then SEMIRING_MUL_CONV tm else
      let val (lx,ln) = dest_pow l in
          let val (rx,rn) = dest_pow r
              val th1 = INST [x_tm |-> lx, p_tm |-> ln, q_tm |-> rn] pthm_29
              val (tm1,tm2) = dest_comb(rand(concl th1))
          in
              TRANS th1 (AP_TERM tm1 (QCONV (TRY_CONV NUM_ADD_CONV) tm2))
          end
          handle HOL_ERR _ =>
          let val th1 = INST [x_tm |-> lx, q_tm |-> ln] pthm_31
              val (tm1,tm2) = dest_comb(rand(concl th1))
          in
              TRANS th1 (AP_TERM tm1 (QCONV (TRY_CONV NUM_SUC_CONV) tm2))
          end
      end
      handle HOL_ERR _ =>
       (let val (rx,rn) = dest_pow r
            val th1 = INST [x_tm |-> rx, q_tm |-> rn] pthm_30
            val (tm1,tm2) = dest_comb(rand(concl th1))
        in
            TRANS th1 (AP_TERM tm1 (QCONV (TRY_CONV NUM_SUC_CONV) tm2))
        end
        (* NOTE: this exception must not come from NUM_SUC_CONV, e.g., when
           given a term like ‘x pow n’ (no literals).

           By changing the definition of "dest_pow" which returns (rx,rn)
           even for non-literals, this bug is fixed. -- Chun Tian, June 2022
         *)
        handle HOL_ERR _ => INST [x_tm |-> l] pthm_32)
    end (* of POWVAR_MUL_CONV *)

(* ------------------------------------------------------------------------- *)
(* Remove "1 * m" from a monomial, and just leave m.                         *)
(* ------------------------------------------------------------------------- *)

    fun MONOMIAL_DEONE th = let
      val (l,r) = dest_mul(rand(concl th)) in
        if l ~~ one_tm then TRANS th (INST [x_tm |-> r] pthm_01) else th
      end
    handle HOL_ERR _ => th

(* ------------------------------------------------------------------------- *)
(* Conversion for "(monomial)^n", where n is a numeral (or symbol).          *)
(* ------------------------------------------------------------------------- *)

    val MONOMIAL_POW_CONV = let
      fun MONOMIAL_POW tm bod ntm =
        if not(is_comb bod) then REFL tm
        else if is_semiring_constant bod then
            QCONV (TRY_CONV SEMIRING_POW_CONV) tm else
        let val (lop,r) = dest_comb bod in
          if not(is_comb lop) then REFL tm else
          let val (op',l) = dest_comb lop in
            if op' ~~ pow_tm (* andalso is_numeral r *) then
               let val th1 = INST [x_tm |-> l, p_tm |-> r, q_tm |-> ntm] pthm_34
                   val (l,r) = dest_comb(rand(concl th1)) in
                 TRANS th1 (AP_TERM l (QCONV (TRY_CONV NUM_MULT_CONV) r))
               end
            else if op' ~~ mul_tm then
               let val th1 = INST [x_tm |-> l, y_tm |-> r, q_tm |-> ntm] pthm_33
                   val (xy,z) = dest_comb(rand(concl th1))
                   val (x,y) = dest_comb xy
                   val thl = MONOMIAL_POW y l ntm
                   and thr = MONOMIAL_POW z r ntm in
                 TRANS th1 (MK_COMB(AP_TERM x thl,thr))
               end
            else REFL tm
          end
        end
    in
      fn tm => (let val (lop,r) = dest_comb tm
                    val (op',l) = dest_comb lop
                in
                    if not(op' ~~ pow_tm) (* orelse not(is_numeral r) *) then
                        failwith "MONOMIAL_POW_CONV"
                    else if r ~~ zeron_tm then INST [x_tm |-> l] pthm_35
                    else if r ~~ onen_tm then INST [x_tm |-> l] pthm_36
                    else MONOMIAL_DEONE(MONOMIAL_POW tm l r)
                end)
    end (* of MONOMIAL_POW_CONV *)

(* ------------------------------------------------------------------------- *)
(* Multiplication of canonical monomials.                                    *)
(* ------------------------------------------------------------------------- *)

    val MONOMIAL_MUL_CONV = let
      fun powvar tm =
        if is_semiring_constant tm then one_tm else
        let val (lop,r) = dest_comb tm
            val (op',l) = dest_comb lop in
            if op' ~~ pow_tm (* andalso is_numeral r *) then l
            else failwith ""
        end
        handle HOL_ERR _ => tm
      fun vorder x y =
        if x ~~ y then 0
        else if x ~~ one_tm then ~1
        else if y ~~ one_tm then 1
        else if variable_order x y then ~1 else 1
      fun MONOMIAL_MUL tm l r =
        let val (lx,ly) = dest_mul l
            val vl = powvar lx
        in
            let val (rx,ry) = dest_mul r
                val vr = powvar rx
                val ord = vorder vl vr
            in
                if ord = 0 then let
                    val th1 = INST [lx_tm |-> lx, ly_tm |-> ly,
                                    rx_tm |-> rx, ry_tm |-> ry] pthm_15
                    val (tm1,tm2) = dest_comb(rand(concl th1))
                    val (tm3,tm4) = dest_comb tm1
                    val th2 = AP_THM (AP_TERM tm3 (QCONV POWVAR_MUL_CONV tm4)) tm2
                    val th3 = TRANS th1 th2
                    val (tm5,tm6) = dest_comb(rand(concl th3))
                    val (tm7,tm8) = dest_comb tm6
                    val th4 = MONOMIAL_MUL tm6 (rand tm7) tm8
                in
                    TRANS th3 (AP_TERM tm5 th4)
                end
                else let
                  val th0 = if ord < 0 then pthm_16 else pthm_17
                  val th1 = INST
                    [lx_tm |-> lx, ly_tm |-> ly, rx_tm |-> rx, ry_tm |-> ry] th0
                  val (tm1,tm2) = dest_comb(rand(concl th1))
                  val (tm3,tm4) = dest_comb tm2 in
                  TRANS th1 (AP_TERM tm1 (MONOMIAL_MUL tm2 (rand tm3) tm4))
                end
            end
            handle HOL_ERR _ =>
               (let val vr = powvar r
                    val ord = vorder vl vr in
                if ord = 0 then
                  let val th1 = INST [lx_tm |-> lx, ly_tm |-> ly, rx_tm |-> r] pthm_18
                      val (tm1,tm2) = dest_comb(rand(concl th1))
                      val (tm3,tm4) = dest_comb tm1
                      val th2 = AP_THM (AP_TERM tm3 (QCONV POWVAR_MUL_CONV tm4)) tm2 in
                    TRANS th1 th2
                  end
                else if ord < 0 then
                  let val th1 = INST [lx_tm |-> lx, ly_tm |-> ly, rx_tm |-> r] pthm_19
                      val (tm1,tm2) = dest_comb(rand(concl th1))
                      val (tm3,tm4) = dest_comb tm2 in
                    TRANS th1 (AP_TERM tm1 (MONOMIAL_MUL tm2 (rand tm3) tm4))
                  end
                else INST [lx_tm |-> l, rx_tm |-> r] pthm_20
                end)
        end
        handle HOL_ERR _ =>
          (let val vl = powvar l in
             let val (rx,ry) = dest_mul r
                 val vr = powvar rx
                 val ord = vorder vl vr
             in
                if ord = 0 then
                  let val th1 = INST [lx_tm |-> l, rx_tm |-> rx, ry_tm |-> ry] pthm_21
                      val (tm1,tm2) = dest_comb(rand(concl th1))
                      val (tm3,tm4) = dest_comb tm1
                      val th2 = QCONV POWVAR_MUL_CONV tm4
                  in
                    TRANS th1 (AP_THM (AP_TERM tm3 th2) tm2)
                  end
                else if ord > 0 then
                  let val th1 = INST [lx_tm |-> l, rx_tm |-> rx, ry_tm |-> ry] pthm_22
                      val (tm1,tm2) = dest_comb(rand(concl th1))
                      val (tm3,tm4) = dest_comb tm2 in
                    TRANS th1 (AP_TERM tm1 (MONOMIAL_MUL tm2 (rand tm3) tm4))
                  end
                else REFL tm
             end
             handle HOL_ERR _ =>
               (let val vr = powvar r
                    val ord = vorder vl vr in
                  if ord = 0 then QCONV POWVAR_MUL_CONV tm
                  else if ord > 0 then INST [lx_tm |-> l, rx_tm |-> r] pthm_20
                  else REFL tm
                end)
           end)
    in
      fn tm => let val (l,r) = dest_mul tm in
                    MONOMIAL_DEONE(MONOMIAL_MUL tm l r)
               end
    end

(* ------------------------------------------------------------------------- *)
(* Multiplication by monomial of a polynomial.                               *)
(* ------------------------------------------------------------------------- *)

    val POLYNOMIAL_MONOMIAL_MUL_CONV = let
      fun PMM_CONV tm =
        let val (l,r) = dest_mul tm in
           let val (y,z) = dest_add r
               val th1 = INST [x_tm |-> l, y_tm |-> y, z_tm |-> z] pthm_37
               val (tm1,tm2) = dest_comb(rand(concl th1))
               val (tm3,tm4) = dest_comb tm1
               val th2 = MK_COMB(AP_TERM tm3 (QCONV MONOMIAL_MUL_CONV tm4),
                                 PMM_CONV tm2) in
             TRANS th1 th2
           end
           handle HOL_ERR _ => QCONV MONOMIAL_MUL_CONV tm
        end
    in
      PMM_CONV
    end

(* ------------------------------------------------------------------------- *)
(* Addition of two monomials identical except for constant multiples.        *)
(* ------------------------------------------------------------------------- *)

    fun MONOMIAL_ADD_CONV tm = let
      val (l,r) = dest_add tm in
      if is_semiring_constant l andalso is_semiring_constant r
      then SEMIRING_ADD_CONV tm else
      let val th1 =
        if is_mul l andalso is_semiring_constant(lhand l) then
          if is_mul r andalso is_semiring_constant(lhand r) then
            INST [a_tm |-> lhand l, b_tm |-> lhand r, m_tm |-> rand r] pthm_02
          else
            INST [a_tm |-> lhand l, m_tm |-> r] pthm_03
        else
          if is_mul r andalso is_semiring_constant(lhand r) then
            INST [a_tm |-> lhand r, m_tm |-> l] pthm_04
          else
            INST [m_tm |-> r] pthm_05
      val (tm1,tm2) = dest_comb(rand(concl th1))
      val (tm3,tm4) = dest_comb tm1
      val th2 = AP_TERM tm3 (QCONV SEMIRING_ADD_CONV tm4)
      val th3 = TRANS th1 (AP_THM th2 tm2)
      val tm5 = rand(concl th3) in
        if lhand tm5 ~~ zero_tm then TRANS th3 (INST [m_tm |-> rand tm5] pthm_06)
        else MONOMIAL_DEONE th3
      end
    end

(* ------------------------------------------------------------------------- *)
(* Ordering on monomials.                                                    *)
(* ------------------------------------------------------------------------- *)

    fun powervars tm =
      let val ptms = striplist dest_mul tm in
        if is_semiring_constant (hd ptms) then tl ptms else ptms
      end

    fun dest_numeral' (n :term) =
        if is_numeral n then dest_numeral n
        else if is_suc n then
            Arbnum.+ (num_1,dest_numeral' (dest_suc n))
        else num_0

    (* NOTE: this function is extended to support variable powers
       TODO: use something from Grobner.sml for comparing polynomial powers. *)
    fun dest_varpow tm =
      let val (x,n) = dest_pow tm in (x,dest_numeral' n) end
      handle HOL_ERR _ =>
       (tm,(if is_semiring_constant tm then num_0 else num_1))

    fun morder tm1 tm2 = let
      fun lexorder [] [] = 0
        | lexorder vps [] = ~1
        | lexorder [] vps = 1
        | lexorder ((x1,n1)::vs1) ((x2,n2)::vs2) =
              if variable_order x1 x2 then 1
              else if variable_order x2 x1 then ~1
              else if Arbnum.< (n1, n2) then ~1
              else if Arbnum.< (n2, n1) then 1
              else lexorder vs1 vs2
      val vdegs1 = map dest_varpow (powervars tm1)
      and vdegs2 = map dest_varpow (powervars tm2)
      val deg1 = itlist ((curry Arbnum.+) o snd) vdegs1 num_0
      and deg2 = itlist ((curry Arbnum.+) o snd) vdegs2 num_0
    in
        if Arbnum.< (deg1, deg2) then ~1
        else if Arbnum.> (deg1, deg2) then 1
        else lexorder vdegs1 vdegs2
    end

(* ------------------------------------------------------------------------- *)
(* Addition of two polynomials.                                              *)
(* ------------------------------------------------------------------------- *)

    val POLYNOMIAL_ADD_CONV = let
      fun DEZERO_RULE th = let val tm = rand(concl th) in
          if not(is_add tm) then th else
          let val (lop,r) = dest_comb tm
              val l = rand lop in
            if l ~~ zero_tm then TRANS th (INST [a_tm |-> r] pthm_07)
            else if r ~~ zero_tm then TRANS th (INST [a_tm |-> l] pthm_08)
            else th
          end
      end
      fun PADD tm = let val (l,r) = dest_add tm in
        if l ~~ zero_tm then INST [a_tm |-> r] pthm_07
        else if r ~~ zero_tm then INST [a_tm |-> l] pthm_08 else
        if is_add l then
          let val (a,b) = dest_add l in
          if is_add r then
            let val (c,d) = dest_add r
                val ord = morder a c in
            if ord = 0 then
              let val th1 = INST [a_tm |-> a, b_tm |-> b, c_tm |-> c, d_tm |-> d]
                                 pthm_23
                  val (tm1,tm2) = dest_comb(rand(concl th1))
                  val (tm3,tm4) = dest_comb tm1
                  val th2 = AP_TERM tm3 (MONOMIAL_ADD_CONV tm4) in
                DEZERO_RULE (TRANS th1 (MK_COMB(th2,PADD tm2)))
              end
            else
              let val th1 = if ord > 0 then
                                INST [a_tm |-> a, b_tm |-> b, c_tm |-> r] pthm_24
                            else INST [a_tm |-> l, c_tm |-> c, d_tm |-> d] pthm_25
                  val (tm1,tm2) = dest_comb(rand(concl th1)) in
                DEZERO_RULE (TRANS th1 (AP_TERM tm1 (PADD tm2)))
              end
            end
          else
            let val ord = morder a r in
            if ord = 0 then
              let val th1 = INST [a_tm |-> a, b_tm |-> b, c_tm |-> r] pthm_26
                  val (tm1,tm2) = dest_comb(rand(concl th1))
                  val (tm3,tm4) = dest_comb tm1
                  val th2 = AP_THM (AP_TERM tm3 (MONOMIAL_ADD_CONV tm4)) tm2 in
                DEZERO_RULE (TRANS th1 th2)
              end
            else if ord > 0 then
              let val th1 = INST [a_tm |-> a, b_tm |-> b, c_tm |-> r] pthm_24
                  val (tm1,tm2) = dest_comb(rand(concl th1)) in
                DEZERO_RULE (TRANS th1 (AP_TERM tm1 (PADD tm2)))
              end
            else
              DEZERO_RULE (INST [a_tm |-> l, c_tm |-> r] pthm_27)
            end
          end
        else
          if is_add r then
            let val (c,d) = dest_add r
                val ord = morder l c in
            if ord = 0 then
              let val th1 = INST [a_tm |-> l, c_tm |-> c, d_tm |-> d] pthm_28
                  val (tm1,tm2) = dest_comb(rand(concl th1))
                  val (tm3,tm4) = dest_comb tm1
                  val th2 = AP_THM (AP_TERM tm3 (MONOMIAL_ADD_CONV tm4)) tm2 in
                DEZERO_RULE (TRANS th1 th2)
              end
            else if ord > 0 then
              REFL tm
            else
              let val th1 = INST [a_tm |-> l, c_tm |-> c, d_tm |-> d] pthm_25
                  val (tm1,tm2) = dest_comb(rand(concl th1)) in
                DEZERO_RULE (TRANS th1 (AP_TERM tm1 (PADD tm2)))
              end
            end
          else
            let val ord = morder l r in
            if ord = 0 then MONOMIAL_ADD_CONV tm
            else if ord > 0 then DEZERO_RULE(REFL tm)
            else DEZERO_RULE(INST [a_tm |-> l, c_tm |-> r] pthm_27)
            end
      end
    in
      PADD
    end

(* ------------------------------------------------------------------------- *)
(* Multiplication of two polynomials.                                        *)
(* ------------------------------------------------------------------------- *)

    val POLYNOMIAL_MUL_CONV = let
      fun PMUL tm = let val (l,r) = dest_mul tm in
        if not(is_add l) then POLYNOMIAL_MONOMIAL_MUL_CONV tm
        else (* is_add l *) if not(is_add r) then
          let val th1 = INST [a_tm |-> l, b_tm |-> r] pthm_09
              val th2 = QCONV POLYNOMIAL_MONOMIAL_MUL_CONV(rand(concl th1))
          in
            TRANS th1 th2
          end
        else (* is_add l andalso is_add r *)
          let val (a,b) = dest_add l
              val th1 = INST [a_tm |-> a, b_tm |-> b, c_tm |-> r] pthm_10
              val (tm1,tm2) = dest_comb(rand(concl th1))
              val (tm3,tm4) = dest_comb tm1
              val th2 = AP_TERM tm3 (QCONV POLYNOMIAL_MONOMIAL_MUL_CONV tm4)
              val th3 = TRANS th1 (MK_COMB(th2,QCONV PMUL tm2)) in
            TRANS th3 (QCONV POLYNOMIAL_ADD_CONV (rand(concl th3)))
          end
      end
    in
      fn tm => let val (l,r) = dest_mul tm in
                   if l ~~ zero_tm then INST [a_tm |-> r] pthm_11
                   else if r ~~ zero_tm then INST [a_tm |-> l] pthm_12
                   else if l ~~ one_tm then INST [a_tm |-> r] pthm_13
                   else if r ~~ one_tm then INST [a_tm |-> l] pthm_14
                   else PMUL tm
               end
    end

(* ------------------------------------------------------------------------- *)
(* Power of polynomial (optimized for the monomial and trivial cases).       *)
(* ------------------------------------------------------------------------- *)

    val POLYNOMIAL_POW_CONV = let
      fun PPOW tm = let val (l,n) = dest_pow tm in
        if n ~~ zeron_tm then INST [x_tm |-> l] pthm_35
        else if n ~~ onen_tm then INST [x_tm |-> l] pthm_36 else
        let val th1 = num_CONV n
            val th2 = INST [x_tm |-> l, q_tm |-> rand(rand(concl th1))] pthm_38
            val (tm1,tm2) = dest_comb(rand(concl th2))
            val th3 = TRANS th2 (AP_TERM tm1 (PPOW tm2))
            val th4 = TRANS (AP_TERM (rator tm) th1) th3
            val th5 = QCONV POLYNOMIAL_MUL_CONV (rand(concl th4))
        in
          TRANS th4 th5
        end
      end
    in
      fn tm => if is_add(lhand tm) then PPOW tm else MONOMIAL_POW_CONV tm
    end

(* ------------------------------------------------------------------------- *)
(* Negation.                                                                 *)
(* ------------------------------------------------------------------------- *)

    fun POLYNOMIAL_NEG_CONV tm = let
      val (l,r) = dest_comb tm
    in
      if not(l ~~ neg_tm) then failwith "POLYNOMIAL_NEG_CONV"
      else
        let val th1 = INST [x_tm |-> r] nthm_1
            val th2 = QCONV POLYNOMIAL_MONOMIAL_MUL_CONV (rand(concl th1))
        in
          TRANS th1 th2
        end
    end

(* ------------------------------------------------------------------------- *)
(* Subtraction. |- x - y = x + -1 * y (it never raises UNCHANGED exception)  *)
(* ------------------------------------------------------------------------- *)

    fun POLYNOMIAL_SUB_CONV tm = let
       val (l,r) = dest_sub tm
       val th1 = INST [x_tm |-> l, y_tm |-> r] nthm_2
       val (tm1,tm2) = dest_comb(rand(concl th1))

       (* th2 reflects a possible one-step simplification of ‘-1 * y’, when
          y is either 0 or 1. Thus the QCONV is also reasonable. *)
       val th2 = AP_TERM tm1 (QCONV POLYNOMIAL_MONOMIAL_MUL_CONV tm2)

       (* th3 reflects a possible one-step simplification of the sum, when
          either side is 0. *)
       val th3 = QCONV POLYNOMIAL_ADD_CONV (rand(concl th2))
    in

       TRANS th1 (TRANS th2 th3)
    end

(* ------------------------------------------------------------------------- *)
(* Conversion from HOL term.                                                 *)
(* ------------------------------------------------------------------------- *)

    fun POLYNOMIAL_CONV tm =
      if not(is_comb tm) orelse is_semiring_constant tm then
          REFL tm
      else
      let val (lop,r) = dest_comb tm in
      if lop ~~ neg_tm then
         let val th1 = AP_TERM lop (QCONV POLYNOMIAL_CONV r) in
           TRANS th1 (POLYNOMIAL_NEG_CONV (rand(concl th1)))
         end
      else if not(is_comb lop) then REFL tm else
         let val (op',l) = dest_comb lop in
         if op' ~~ pow_tm andalso is_numeral r then
           let val th1 = AP_THM (AP_TERM op' (QCONV POLYNOMIAL_CONV l)) r in
             TRANS th1 (POLYNOMIAL_POW_CONV (rand(concl th1)))
           end
         else if op' ~~ add_tm orelse op' ~~ mul_tm orelse op' ~~ sub_tm then
           let val th1 = MK_COMB(AP_TERM op' (POLYNOMIAL_CONV l),
                                 POLYNOMIAL_CONV r)
               val fn' = if op' ~~ add_tm then POLYNOMIAL_ADD_CONV
                    else if op' ~~ mul_tm then POLYNOMIAL_MUL_CONV
                    else POLYNOMIAL_SUB_CONV in
               TRANS th1 (QCONV fn' (rand(concl th1)))
           end
         else REFL tm
         end
      end
  in
 (* 6 return values of SEMIRING_NORMALIZERS_CONV *)
   (POLYNOMIAL_NEG_CONV,POLYNOMIAL_ADD_CONV,POLYNOMIAL_SUB_CONV,
    POLYNOMIAL_MUL_CONV,POLYNOMIAL_POW_CONV,UNCHANGED_CONV POLYNOMIAL_CONV)

  end (* of SEMIRING_NORMALIZERS_CORE main branch *)

  (* to avoid incomplete match warning *)
  | SEMIRING_NORMALIZERS_CORE _ _ _ _ = raise Bind

val SEMIRING_NORMALIZERS_CONV = SEMIRING_NORMALIZERS_CORE o CONJUNCTS

(* ------------------------------------------------------------------------- *)
(* Instantiate it to the natural numbers.                                    *)
(* ------------------------------------------------------------------------- *)

val (_,_,_,_,_,NUM_NORMALIZE_CONV) =
  SEMIRING_NORMALIZERS_CONV NUM_NORMALIZE_CONV_sth
    TRUTH (* no support of negation and subtraction here *)
    (is_numeral,NUM_ADD_CONV,NUM_MULT_CONV,NUM_EXP_CONV)
    (* learnt from Oskar Abrahamsson.
       This should replace HOL-Light's (<) on terms *)
    (fn x => fn y => Term.compare (x,y) = LESS)

end; (* structure *)

(* References:

   [1] https://en.wikipedia.org/wiki/Gröbner_basis
   [2] https://en.wikipedia.org/wiki/Buchberger%27s_algorithm
 *)
