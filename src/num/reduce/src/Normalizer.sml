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

open HolKernel Parse boolLib boolSimps liteLib;

open arithmeticTheory numSyntax Num_conv tautLib Arithconv simpLib
     normalForms;

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars arithmetic_grammars
end

open Parse


val ERR = mk_HOL_ERR "Normalizer";
fun failwith s = raise ERR "?" s

val ADD_AC        = AC ADD_SYM ADD_ASSOC;
val MULT_AC       = AC MULT_SYM MULT_ASSOC;
val NUM_ADD_CONV  = ADD_CONV;
val NUM_MULT_CONV = MUL_CONV;
val NUM_EXP_CONV  = EXP_CONV;
val NUM_SUC_CONV  = SUC_CONV;
val num_0         = Arbnum.zero;
val num_1         = Arbnum.one;

(* from numLib.sml, not defined yet when compiling this file *)
fun INDUCT_TAC g =
  INDUCT_THEN numTheory.INDUCTION ASSUME_TAC g
  handle HOL_ERR _ => raise ERR "INDUCT_TAC" "";

fun is_comm t =
    let val (l,r) = dest_eq $ #2 $ strip_forall t
        val (f, xs) = strip_comb l
        val _ = length xs = 2 orelse raise mk_HOL_ERR "" "" ""
        val (g, ys) = strip_comb r
        val _ = length ys = 2 orelse raise mk_HOL_ERR "" "" ""
    in
      f ~~ g andalso el 1 xs ~~ el 2 ys andalso el 2 xs ~~ el 1 ys
    end handle HOL_ERR _ => false

val SEMIRING_PTHS = prove
   (“(!(x:'a) y z. add x (add y z) = add (add x y) z) /\
     (!x y. add x y = add y x) /\
     (!x. add r0 x = x) /\
     (!x y z. mul x (mul y z) = mul (mul x y) z) /\
     (!x y. mul x y = mul y x) /\
     (!x. mul r1 x = x) /\
     (!x. mul r0 x = r0) /\
     (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
     (!x. pwr x 0 = r1) /\
     (!x n. pwr x (SUC n) = mul x (pwr x n))
     ==> (mul r1 x = x) /\
         (add (mul a m) (mul b m) = mul (add a b) m) /\
         (add (mul a m) m = mul (add a r1) m) /\
         (add m (mul a m) = mul (add a r1) m) /\
         (add m m = mul (add r1 r1) m) /\
         (mul r0 m = r0) /\
         (add r0 a = a) /\
         (add a r0 = a) /\
         (mul a b = mul b a) /\
         (mul (add a b) c = add (mul a c) (mul b c)) /\
         (mul r0 a = r0) /\
         (mul a r0 = r0) /\
         (mul r1 a = a) /\
         (mul a r1 = a) /\
         (mul (mul lx ly) (mul rx ry) = mul (mul lx rx) (mul ly ry)) /\
         (mul (mul lx ly) (mul rx ry) = mul lx (mul ly (mul rx ry))) /\
         (mul (mul lx ly) (mul rx ry) = mul rx (mul (mul lx ly) ry)) /\
         (mul (mul lx ly) rx = mul (mul lx rx) ly) /\
         (mul (mul lx ly) rx = mul lx (mul ly rx)) /\
         (mul lx rx = mul rx lx) /\
         (mul lx (mul rx ry) = mul (mul lx rx) ry) /\
         (mul lx (mul rx ry) = mul rx (mul lx ry)) /\
         (add (add a b) (add c d) = add (add a c) (add b d)) /\
         (add (add a b) c = add a (add b c)) /\
         (add a (add c d) = add c (add a d)) /\
         (add (add a b) c = add (add a c) b) /\
         (add a c = add c a) /\
         (add a (add c d) = add (add a c) d) /\
         (mul (pwr x p) (pwr x q) = pwr x (p + q)) /\
         (mul x (pwr x q) = pwr x (SUC q)) /\
         (mul (pwr x q) x = pwr x (SUC q)) /\
         (mul x x = pwr x 2) /\
         (pwr (mul x y) q = mul (pwr x q) (pwr y q)) /\
         (pwr (pwr x p) q = pwr x (p * q)) /\
         (pwr x 0 = r1) /\
         (pwr x 1 = x) /\
         (mul x (add y z) = add (mul x y) (mul x z)) /\
         (pwr x (SUC q) = mul x (pwr x q))”,
 (* proof *)
    STRIP_TAC THEN
    SUBGOAL_THEN
     “(!m:'a n. add m n = add n m) /\
      (!m n p. add (add m n) p = add m (add n p)) /\
      (!m n p. add m (add n p) = add n (add m p)) /\
      (!x. add x r0 = x) /\
      (!m n. mul m n = mul n m) /\
      (!m n p. mul (mul m n) p = mul m (mul n p)) /\
      (!m n p. mul m (mul n p) = mul n (mul m p)) /\
      (!m n p. mul (add m n) p = add (mul m p) (mul n p)) /\
      (!x. mul x r1 = x) /\
      (!x. mul x r0 = r0)”
    MP_TAC
    >- (rpt strip_tac >>
        TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) >>
        FILTER_ASM_REWRITE_TAC (not o is_comm) [] >>
        rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
        TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) >>
        ONCE_ASM_REWRITE_TAC[] >>
        FILTER_ASM_REWRITE_TAC(not o is_comm)[] >>
        UNDISCH_THEN “!x:'a y. add x y :'a = add y x”
          (fn th => CONV_TAC (LAND_CONV (REWR_CONV th))) >>
        UNDISCH_THEN “!x:'a y. mul x y :'a = mul y x”
          (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
        REWRITE_TAC[]) >>
    MAP_EVERY (fn t => UNDISCH_THEN t (K ALL_TAC))
    [“!(x:'a) y z. add x (add y z) = add (add x y) z”,
     “!(x:'a) y. add x y :'a = add y x”,
     “!(x:'a) y z. mul x (mul y z) = mul (mul x y) z”,
     “!(x:'a) y. mul x y :'a = mul y x”] THEN STRIP_TAC THEN
    ASM_SIMP_TAC bool_ss [ONE, TWO] THEN
    SUBGOAL_THEN “!m (n:num) (x:'a). pwr x (m + n) :'a = mul (pwr x m) (pwr x n)”
    ASSUME_TAC
    >- (GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC bool_ss [ADD_CLAUSES]) \\
    SUBGOAL_THEN “!(x:'a) (y:'a) (n:num). pwr (mul x y) n = mul (pwr x n) (pwr y n)”
    ASSUME_TAC
    >- (GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC bool_ss []) \\
    FILTER_ASM_REWRITE_TAC (not o is_comm) [] >>
    ID_SPEC_TAC “q:num” THEN INDUCT_TAC THEN ASM_SIMP_TAC bool_ss[MULT_CLAUSES])

val true_tm = concl TRUTH; (* or T *)

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
fun SEMIRING_NORMALIZERS_CONV
      sth rth (is_semiring_constant,
               SEMIRING_ADD_CONV,
               SEMIRING_MUL_CONV,
               SEMIRING_POW_CONV) variable_order =
  let
    val pths = CONJUNCTS(MATCH_MP SEMIRING_PTHS sth);

    (* NOTE: it was "val [pthm_01, pthm_02, ..., pthm_38] = pths" here. The
       following code avoids "Pattern is not exhaustive" warnings. *)
    val pthm_01 = el 1 pths (* |- 1 * x = x *)
    and pthm_02 = el 2 pths (* |- a * m + b * m = (a + b) * m *)
    and pthm_03 = el 3 pths (* |- a * m + m = (a + 1) * m *)
    and pthm_04 = el 4 pths (* |- m + a * m = (a + 1) * m *)
    and pthm_05 = el 5 pths (* |- m + m = (1 + 1) * m *)
    and pthm_06 = el 6 pths (* |- 0 * m = 0 *)
    and pthm_07 = el 7 pths (* |- 0 + a = a *)
    and pthm_08 = el 8 pths (* |- a + 0 = a *)
    and pthm_09 = el 9 pths (* |- a * b = b * a *)
    and pthm_10 = el 10 pths (* |- (a + b) * c = a * c + b * c *)
    and pthm_11 = el 11 pths (* |- 0 * a = 0 *)
    and pthm_12 = el 12 pths (* |- a * 0 = 0 *)
    and pthm_13 = el 13 pths (* |- 1 * a = a *)
    and pthm_14 = el 14 pths (* |- a * 1 = a *)
    and pthm_15 = el 15 pths (* |- lx * ly * (rx * ry) = lx * rx * (ly * ry) *)
    and pthm_16 = el 16 pths (* |- lx * ly * (rx * ry) = lx * (ly * (rx * ry)) *)
    and pthm_17 = el 17 pths (* |- lx * ly * (rx * ry) = rx * (lx * ly * ry) *)
    and pthm_18 = el 18 pths (* |- lx * ly * rx = lx * rx * ly *)
    and pthm_19 = el 19 pths (* |- lx * ly * rx = lx * (ly * rx) *)
    and pthm_20 = el 20 pths (* |- lx * rx = rx * lx *)
    and pthm_21 = el 21 pths (* |- lx * (rx * ry) = lx * rx * ry *)
    and pthm_22 = el 22 pths (* |- lx * (rx * ry) = rx * (lx * ry) *)
    and pthm_23 = el 23 pths (* |- a + b + (c + d) = a + c + (b + d) *)
    and pthm_24 = el 24 pths (* |- a + b + c = a + (b + c) *)
    and pthm_25 = el 25 pths (* |- a + (c + d) = c + (a + d) *)
    and pthm_26 = el 26 pths (* |- a + b + c = a + c + b *)
    and pthm_27 = el 27 pths (* |- a + c = c + a *)
    and pthm_28 = el 28 pths (* |- a + (c + d) = a + c + d *)
    and pthm_29 = el 29 pths (* |- x ** p * x ** q = x ** (p + q) *)
    and pthm_30 = el 30 pths (* |- x * x ** q = x ** SUC q *)
    and pthm_31 = el 31 pths (* |- x ** q * x = x ** SUC q *)
    and pthm_32 = el 32 pths (* |- x * x = x ** 2 *)
    and pthm_33 = el 33 pths (* |- (x * y) ** q = x ** q * y ** q *)
    and pthm_34 = el 34 pths (* |- (x ** p) ** q = x ** (p * q) *)
    and pthm_35 = el 35 pths (* |- x ** 0 = 1 *)
    and pthm_36 = el 36 pths (* |- x ** 1 = x *)
    and pthm_37 = el 37 pths (* |- x * (y + z) = x * y + x * z *)
    and pthm_38 = el 38 pths; (* |- x ** SUC q = x * x ** q *)

    val add_tm = rator(rator(lhand(concl pthm_07)))
    and mul_tm = rator(rator(lhand(concl pthm_13)))
    and pow_tm = rator(rator(rand(concl pthm_32)))
    and zero_tm = rand(concl pthm_06)
    and one_tm = rand(lhand(concl pthm_14))
    and ty = type_of(rand(concl pthm_01));

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
    and z_tm = mk_var("z",ty);

    val dest_add = dest_binop add_tm
    val dest_mul = dest_binop mul_tm
 (* old definition:
    fun dest_pow tm =
      let val (l,r) = dest_binop pow_tm tm in
      if is_numeral r then (l,r) else failwith "dest_pow" end
  *)
    fun dest_pow tm = dest_binop pow_tm tm;

    val is_add = is_binop add_tm
    val is_mul = is_binop mul_tm;

    val (nthm_1,nthm_2,sub_tm,neg_tm,dest_sub,is_sub) =
      if concl rth ~~ true_tm then
        (rth,rth,true_tm,true_tm,(fn t => (t,t)),K false)
      else let
        val nthm_1 = SPEC x_tm (CONJUNCT1 rth)
        and nthm_2 = SPECL [x_tm, y_tm] (CONJUNCT2 rth);
        val sub_tm = rator(rator(lhand(concl nthm_2)))
        and neg_tm = rator(lhand(concl nthm_1));
        val dest_sub = dest_binop sub_tm
        and is_sub = is_binop sub_tm
      in
        (nthm_1,nthm_2,sub_tm,neg_tm,dest_sub,is_sub) end;

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
          let val (rx,rn) = dest_pow r;
              val th1 = INST [x_tm |-> lx, p_tm |-> ln, q_tm |-> rn] pthm_29;
              val (tm1,tm2) = dest_comb(rand(concl th1))
          in
              TRANS th1 (AP_TERM tm1 (QCONV (TRY_CONV NUM_ADD_CONV) tm2))
          end
          handle HOL_ERR _ =>
          let val th1 = INST [x_tm |-> lx, q_tm |-> ln] pthm_31;
              val (tm1,tm2) = dest_comb(rand(concl th1))
          in
              TRANS th1 (AP_TERM tm1 (QCONV (TRY_CONV NUM_SUC_CONV) tm2))
          end
      end
      handle HOL_ERR _ =>
       (let val (rx,rn) = dest_pow r;
            val th1 = INST [x_tm |-> rx, q_tm |-> rn] pthm_30;
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
    end; (* of POWVAR_MUL_CONV *)

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
               let val th1 = INST [x_tm |-> l, p_tm |-> r, q_tm |-> ntm] pthm_34;
                   val (l,r) = dest_comb(rand(concl th1)) in
                 TRANS th1 (AP_TERM l (QCONV (TRY_CONV NUM_MULT_CONV) r))
               end
            else if op' ~~ mul_tm then
               let val th1 = INST [x_tm |-> l, y_tm |-> r, q_tm |-> ntm] pthm_33;
                   val (xy,z) = dest_comb(rand(concl th1));
                   val (x,y) = dest_comb xy;
                   val thl = MONOMIAL_POW y l ntm
                   and thr = MONOMIAL_POW z r ntm in
                 TRANS th1 (MK_COMB(AP_TERM x thl,thr))
               end
            else REFL tm
          end
        end
    in
      fn tm => (let val (lop,r) = dest_comb tm;
                    val (op',l) = dest_comb lop
                in
                    if not(op' ~~ pow_tm) (* orelse not(is_numeral r) *) then
                        failwith "MONOMIAL_POW_CONV"
                    else if r ~~ zeron_tm then INST [x_tm |-> l] pthm_35
                    else if r ~~ onen_tm then INST [x_tm |-> l] pthm_36
                    else MONOMIAL_DEONE(MONOMIAL_POW tm l r)
                end)
    end; (* of MONOMIAL_POW_CONV *)

(* ------------------------------------------------------------------------- *)
(* Multiplication of canonical monomials.                                    *)
(* ------------------------------------------------------------------------- *)

    val MONOMIAL_MUL_CONV = let
      fun powvar tm =
        if is_semiring_constant tm then one_tm else
        let val (lop,r) = dest_comb tm;
            val (op',l) = dest_comb lop in
            if op' ~~ pow_tm (* andalso is_numeral r *) then l
            else failwith ""
        end
        handle HOL_ERR _ => tm;
      fun vorder x y =
        if x ~~ y then 0
        else if x ~~ one_tm then ~1
        else if y ~~ one_tm then 1
        else if variable_order x y then ~1 else 1;
      fun MONOMIAL_MUL tm l r =
        let val (lx,ly) = dest_mul l;
            val vl = powvar lx
        in
            let val (rx,ry) = dest_mul r;
                val vr = powvar rx;
                val ord = vorder vl vr
            in
                if ord = 0 then let
                    val th1 = INST [lx_tm |-> lx, ly_tm |-> ly,
                                    rx_tm |-> rx, ry_tm |-> ry] pthm_15;
                    val (tm1,tm2) = dest_comb(rand(concl th1));
                    val (tm3,tm4) = dest_comb tm1;
                    val th2 = AP_THM (AP_TERM tm3 (QCONV POWVAR_MUL_CONV tm4)) tm2;
                    val th3 = TRANS th1 th2;
                    val (tm5,tm6) = dest_comb(rand(concl th3));
                    val (tm7,tm8) = dest_comb tm6;
                    val th4 = MONOMIAL_MUL tm6 (rand tm7) tm8
                in
                    TRANS th3 (AP_TERM tm5 th4)
                end
                else let
                  val th0 = if ord < 0 then pthm_16 else pthm_17;
                  val th1 = INST
                    [lx_tm |-> lx, ly_tm |-> ly, rx_tm |-> rx, ry_tm |-> ry] th0;
                  val (tm1,tm2) = dest_comb(rand(concl th1));
                  val (tm3,tm4) = dest_comb tm2 in
                  TRANS th1 (AP_TERM tm1 (MONOMIAL_MUL tm2 (rand tm3) tm4))
                end
            end
            handle HOL_ERR _ =>
               (let val vr = powvar r;
                    val ord = vorder vl vr in
                if ord = 0 then
                  let val th1 = INST [lx_tm |-> lx, ly_tm |-> ly, rx_tm |-> r] pthm_18;
                      val (tm1,tm2) = dest_comb(rand(concl th1));
                      val (tm3,tm4) = dest_comb tm1;
                      val th2 = AP_THM (AP_TERM tm3 (QCONV POWVAR_MUL_CONV tm4)) tm2 in
                    TRANS th1 th2
                  end
                else if ord < 0 then
                  let val th1 = INST [lx_tm |-> lx, ly_tm |-> ly, rx_tm |-> r] pthm_19;
                      val (tm1,tm2) = dest_comb(rand(concl th1));
                      val (tm3,tm4) = dest_comb tm2 in
                    TRANS th1 (AP_TERM tm1 (MONOMIAL_MUL tm2 (rand tm3) tm4))
                  end
                else INST [lx_tm |-> l, rx_tm |-> r] pthm_20
                end)
        end
        handle HOL_ERR _ =>
          (let val vl = powvar l in
             let val (rx,ry) = dest_mul r;
                 val vr = powvar rx;
                 val ord = vorder vl vr
             in
                if ord = 0 then
                  let val th1 = INST [lx_tm |-> l, rx_tm |-> rx, ry_tm |-> ry] pthm_21;
                      val (tm1,tm2) = dest_comb(rand(concl th1));
                      val (tm3,tm4) = dest_comb tm1;
                      val th2 = QCONV POWVAR_MUL_CONV tm4
                  in
                    TRANS th1 (AP_THM (AP_TERM tm3 th2) tm2)
                  end
                else if ord > 0 then
                  let val th1 = INST [lx_tm |-> l, rx_tm |-> rx, ry_tm |-> ry] pthm_22;
                      val (tm1,tm2) = dest_comb(rand(concl th1));
                      val (tm3,tm4) = dest_comb tm2 in
                    TRANS th1 (AP_TERM tm1 (MONOMIAL_MUL tm2 (rand tm3) tm4))
                  end
                else REFL tm
             end
             handle HOL_ERR _ =>
               (let val vr = powvar r;
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
    end;

(* ------------------------------------------------------------------------- *)
(* Multiplication by monomial of a polynomial.                               *)
(* ------------------------------------------------------------------------- *)

    val POLYNOMIAL_MONOMIAL_MUL_CONV = let
      fun PMM_CONV tm =
        let val (l,r) = dest_mul tm in
           let val (y,z) = dest_add r;
               val th1 = INST [x_tm |-> l, y_tm |-> y, z_tm |-> z] pthm_37;
               val (tm1,tm2) = dest_comb(rand(concl th1));
               val (tm3,tm4) = dest_comb tm1;
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
            INST [m_tm |-> r] pthm_05;
      val (tm1,tm2) = dest_comb(rand(concl th1));
      val (tm3,tm4) = dest_comb tm1;
      val th2 = AP_TERM tm3 (QCONV SEMIRING_ADD_CONV tm4);
      val th3 = TRANS th1 (AP_THM th2 tm2);
      val tm5 = rand(concl th3) in
        if lhand tm5 ~~ zero_tm then TRANS th3 (INST [m_tm |-> rand tm5] pthm_06)
        else MONOMIAL_DEONE th3
      end
    end;

(* ------------------------------------------------------------------------- *)
(* Ordering on monomials.                                                    *)
(* ------------------------------------------------------------------------- *)

    fun powervars tm =
      let val ptms = striplist dest_mul tm in
        if is_semiring_constant (hd ptms) then tl ptms else ptms
      end;

    fun dest_numeral' (n :term) =
        if is_numeral n then dest_numeral n
        else if is_suc n then
            Arbnum.+ (num_1,dest_numeral' (dest_suc n))
        else num_0;

    (* NOTE: this function is extended to support variable powers
       TODO: use something from Grobner.sml for comparing polynomial powers. *)
    fun dest_varpow tm =
      let val (x,n) = dest_pow tm in (x,dest_numeral' n) end
      handle HOL_ERR _ =>
       (tm,(if is_semiring_constant tm then num_0 else num_1));

    fun morder tm1 tm2 = let
      fun lexorder [] [] = 0
        | lexorder vps [] = ~1
        | lexorder [] vps = 1
        | lexorder ((x1,n1)::vs1) ((x2,n2)::vs2) =
              if variable_order x1 x2 then 1
              else if variable_order x2 x1 then ~1
              else if Arbnum.< (n1, n2) then ~1
              else if Arbnum.< (n2, n1) then 1
              else lexorder vs1 vs2;
      val vdegs1 = map dest_varpow (powervars tm1)
      and vdegs2 = map dest_varpow (powervars tm2);
      val deg1 = itlist ((curry Arbnum.+) o snd) vdegs1 num_0
      and deg2 = itlist ((curry Arbnum.+) o snd) vdegs2 num_0
    in
        if Arbnum.< (deg1, deg2) then ~1
        else if Arbnum.> (deg1, deg2) then 1
        else lexorder vdegs1 vdegs2
    end;

(* ------------------------------------------------------------------------- *)
(* Addition of two polynomials.                                              *)
(* ------------------------------------------------------------------------- *)

    val POLYNOMIAL_ADD_CONV = let
      fun DEZERO_RULE th = let val tm = rand(concl th) in
          if not(is_add tm) then th else
          let val (lop,r) = dest_comb tm;
              val l = rand lop in
            if l ~~ zero_tm then TRANS th (INST [a_tm |-> r] pthm_07)
            else if r ~~ zero_tm then TRANS th (INST [a_tm |-> l] pthm_08)
            else th
          end
      end;
      fun PADD tm = let val (l,r) = dest_add tm in
        if l ~~ zero_tm then INST [a_tm |-> r] pthm_07
        else if r ~~ zero_tm then INST [a_tm |-> l] pthm_08 else
        if is_add l then
          let val (a,b) = dest_add l in
          if is_add r then
            let val (c,d) = dest_add r;
                val ord = morder a c in
            if ord = 0 then
              let val th1 = INST [a_tm |-> a, b_tm |-> b, c_tm |-> c, d_tm |-> d]
                                 pthm_23;
                  val (tm1,tm2) = dest_comb(rand(concl th1));
                  val (tm3,tm4) = dest_comb tm1;
                  val th2 = AP_TERM tm3 (MONOMIAL_ADD_CONV tm4) in
                DEZERO_RULE (TRANS th1 (MK_COMB(th2,PADD tm2)))
              end
            else
              let val th1 = if ord > 0 then
                                INST [a_tm |-> a, b_tm |-> b, c_tm |-> r] pthm_24
                            else INST [a_tm |-> l, c_tm |-> c, d_tm |-> d] pthm_25;
                  val (tm1,tm2) = dest_comb(rand(concl th1)) in
                DEZERO_RULE (TRANS th1 (AP_TERM tm1 (PADD tm2)))
              end
            end
          else
            let val ord = morder a r in
            if ord = 0 then
              let val th1 = INST [a_tm |-> a, b_tm |-> b, c_tm |-> r] pthm_26;
                  val (tm1,tm2) = dest_comb(rand(concl th1));
                  val (tm3,tm4) = dest_comb tm1;
                  val th2 = AP_THM (AP_TERM tm3 (MONOMIAL_ADD_CONV tm4)) tm2 in
                DEZERO_RULE (TRANS th1 th2)
              end
            else if ord > 0 then
              let val th1 = INST [a_tm |-> a, b_tm |-> b, c_tm |-> r] pthm_24;
                  val (tm1,tm2) = dest_comb(rand(concl th1)) in
                DEZERO_RULE (TRANS th1 (AP_TERM tm1 (PADD tm2)))
              end
            else
              DEZERO_RULE (INST [a_tm |-> l, c_tm |-> r] pthm_27)
            end
          end
        else
          if is_add r then
            let val (c,d) = dest_add r;
                val ord = morder l c in
            if ord = 0 then
              let val th1 = INST [a_tm |-> l, c_tm |-> c, d_tm |-> d] pthm_28;
                  val (tm1,tm2) = dest_comb(rand(concl th1));
                  val (tm3,tm4) = dest_comb tm1;
                  val th2 = AP_THM (AP_TERM tm3 (MONOMIAL_ADD_CONV tm4)) tm2 in
                DEZERO_RULE (TRANS th1 th2)
              end
            else if ord > 0 then
              REFL tm
            else
              let val th1 = INST [a_tm |-> l, c_tm |-> c, d_tm |-> d] pthm_25;
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
      end;
    in
      PADD
    end;

(* ------------------------------------------------------------------------- *)
(* Multiplication of two polynomials.                                        *)
(* ------------------------------------------------------------------------- *)

    val POLYNOMIAL_MUL_CONV = let
      fun PMUL tm = let val (l,r) = dest_mul tm in
        if not(is_add l) then POLYNOMIAL_MONOMIAL_MUL_CONV tm
        else (* is_add l *) if not(is_add r) then
          let val th1 = INST [a_tm |-> l, b_tm |-> r] pthm_09;
              val th2 = QCONV POLYNOMIAL_MONOMIAL_MUL_CONV(rand(concl th1))
          in
            TRANS th1 th2
          end
        else (* is_add l andalso is_add r *)
          let val (a,b) = dest_add l;
              val th1 = INST [a_tm |-> a, b_tm |-> b, c_tm |-> r] pthm_10;
              val (tm1,tm2) = dest_comb(rand(concl th1));
              val (tm3,tm4) = dest_comb tm1;
              val th2 = AP_TERM tm3 (QCONV POLYNOMIAL_MONOMIAL_MUL_CONV tm4);
              val th3 = TRANS th1 (MK_COMB(th2,QCONV PMUL tm2)) in
            TRANS th3 (QCONV POLYNOMIAL_ADD_CONV (rand(concl th3)))
          end
      end;
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
        let val th1 = num_CONV n;
            val th2 = INST [x_tm |-> l, q_tm |-> rand(rand(concl th1))] pthm_38;
            val (tm1,tm2) = dest_comb(rand(concl th2));
            val th3 = TRANS th2 (AP_TERM tm1 (PPOW tm2));
            val th4 = TRANS (AP_TERM (rator tm) th1) th3;
            val th5 = QCONV POLYNOMIAL_MUL_CONV (rand(concl th4))
        in
          TRANS th4 th5
        end
      end
    in
      fn tm => if is_add(lhand tm) then PPOW tm else MONOMIAL_POW_CONV tm
    end;

(* ------------------------------------------------------------------------- *)
(* Negation.                                                                 *)
(* ------------------------------------------------------------------------- *)

    fun POLYNOMIAL_NEG_CONV tm = let
      val (l,r) = dest_comb tm
    in
      if not(l ~~ neg_tm) then failwith "POLYNOMIAL_NEG_CONV"
      else
        let val th1 = INST [x_tm |-> r] nthm_1;
            val th2 = QCONV POLYNOMIAL_MONOMIAL_MUL_CONV (rand(concl th1))
        in
          TRANS th1 th2
        end
    end;

(* ------------------------------------------------------------------------- *)
(* Subtraction. |- x - y = x + -1 * y (it never raises UNCHANGED exception)  *)
(* ------------------------------------------------------------------------- *)

    fun POLYNOMIAL_SUB_CONV tm = let
       val (l,r) = dest_sub tm;
       val th1 = INST [x_tm |-> l, y_tm |-> r] nthm_2;
       val (tm1,tm2) = dest_comb(rand(concl th1));

       (* th2 reflects a possible one-step simplification of ‘-1 * y’, when
          y is either 0 or 1. Thus the QCONV is also reasonable. *)
       val th2 = AP_TERM tm1 (QCONV POLYNOMIAL_MONOMIAL_MUL_CONV tm2);

       (* th3 reflects a possible one-step simplification of the sum, when
          either side is 0. *)
       val th3 = QCONV POLYNOMIAL_ADD_CONV (rand(concl th2))
    in

       TRANS th1 (TRANS th2 th3)
    end;

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
                                 POLYNOMIAL_CONV r);
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

  end; (* of SEMIRING_NORMALIZERS_CONV *)

(* ------------------------------------------------------------------------- *)
(* Instantiate it to the natural numbers.                                    *)
(* ------------------------------------------------------------------------- *)

(* learnt from Oskar Arahamsson. This should replace HOL-Light's (<) on terms *)
fun term_lt x y = (Term.compare (x,y) = LESS);

val NUM_NORMALIZE_CONV = let
  val sth = prove
   (“(!x y z:num. x + (y + z) = (x + y) + z) /\
     (!x y:num. x + y = y + x) /\
     (!x:num. 0 + x = x) /\
     (!x y z:num. x * (y * z) = (x * y) * z) /\
     (!x y:num. x * y = y * x) /\
     (!x:num. 1 * x = x) /\
     (!x:num. 0 * x = 0) /\
     (!x y z:num. x * (y + z) = x * y + x * z) /\
     (!x. x EXP 0 = 1) /\
     (!x n. x EXP (SUC n) = x * x EXP n)”,
    REWRITE_TAC[EXP, MULT_CLAUSES, ADD_CLAUSES, LEFT_ADD_DISTRIB] THEN
    SIMP_TAC bool_ss [ADD_AC, MULT_AC])
  and rth = TRUTH (* no support of negation and subtraction here *)
  and is_semiring_constant = is_numeral
  and SEMIRING_ADD_CONV = NUM_ADD_CONV
  and SEMIRING_MUL_CONV = NUM_MULT_CONV
  and SEMIRING_POW_CONV = NUM_EXP_CONV;
  val (_,_,_,_,_,NUM_NORMALIZE_CONV) =
    SEMIRING_NORMALIZERS_CONV sth rth
     (is_semiring_constant,
      SEMIRING_ADD_CONV,SEMIRING_MUL_CONV,SEMIRING_POW_CONV)
     term_lt (* was: (<) *)
  in NUM_NORMALIZE_CONV end;

end; (* structure *)

(* References:

   [1] https://en.wikipedia.org/wiki/Gröbner_basis                           UOK
   [2] https://en.wikipedia.org/wiki/Buchberger%27s_algorithm
 *)
