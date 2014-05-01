structure binary_ieeeLib :> binary_ieeeLib =
struct

open HolKernel Parse boolLib bossLib
open realLib wordsLib binary_ieeeSyntax machine_ieeeSyntax

structure Parse =
struct
  open Parse
  val (Type, Term) =
     parse_from_grammars machine_ieeeTheory.machine_ieee_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "binary_ieeeLib"

val lhsc = boolSyntax.lhs o Thm.concl
val rhsc = boolSyntax.rhs o Thm.concl

fun mk_native_ieee_thm th = Thm.mk_oracle_thm "native_ieee" ([], th)

(* ------------------------------------------------------------------------
   real_to_arbrat
   arbrat_to_real
   ------------------------------------------------------------------------ *)

local
   fun real_to_pos_arbrat tm =
      case Lib.total realSyntax.dest_injected tm of
         SOME a => Arbrat.fromNat (numLib.dest_numeral a)
       | NONE => raise ERR "real_to_pos_arbrat" ""
   fun real_to_signed_arbrat tm =
      case Lib.total realSyntax.dest_negated tm of
         SOME a => Arbrat.negate (real_to_pos_arbrat a)
       | NONE => real_to_pos_arbrat tm
in
   fun real_to_arbrat tm =
      case Lib.total realSyntax.dest_div tm of
         SOME (a, b) =>
            Arbrat./ (real_to_signed_arbrat a, real_to_signed_arbrat b)
       | NONE => real_to_signed_arbrat tm
   fun arbrat_to_real r =
      let
         val n = realSyntax.term_of_int (Arbrat.numerator r)
         val d = Arbrat.denominator r
      in
         if d = Arbnum.one
            then n
         else realSyntax.mk_div (n, realSyntax.term_of_int (Arbint.fromNat d))
      end
end

(* ------------------------------------------------------------------------
   float_to_real
   real_to_float
   ------------------------------------------------------------------------ *)

local
   fun is_negative_rat r = Arbrat.< (r, Arbrat.zero)
   val nfloor = Arbint.toNat o Arbrat.floor
   fun lg2 n = if n = Arbnum.zero then Arbnum.zero else Arbnum.log2 n
   fun pow2 n = Arbnum.pow (Arbnum.two, n)
   fun dimword w = pow2 (Arbnum.fromInt w)
   fun uint_max w = Arbnum.less1 (dimword w)
   fun int_max w = Arbnum.less1 (dimword (w - 1))
   fun frac i = Arbrat.- (Arbrat.two, Arbrat.inv (Arbrat.fromNat (dimword i)))
   val diff = Arbrat.abs o Arbrat.-
   fun evenfloat (s: bool, e: Arbnum.num, f) = Arbnum.mod2 f = Arbnum.zero
   fun negativefloat (s: bool, e: Arbnum.num, f: Arbnum.num) = s
   val positivefloat = not o negativefloat
   fun real_to_float0 (t, w) =
      let
         val tt = Arbnum.fromInt t
         val ulp = Arbrat./ (Arbrat.two,
                             Arbrat.fromNat (pow2 (Arbnum.+ (int_max w, tt))))
         val d = pow2 (Arbnum.less1 tt)
         val c = pow2 tt
         fun exponent n = lg2 (Arbnum.div (n, d))
         fun fraction e n = Arbnum.- (Arbnum.div (n, pow2 (Arbnum.less1 e)), c)
      in
         fn r =>
            let
               val s = is_negative_rat r
               val n = nfloor (Arbrat./ (Arbrat.abs r, ulp))
               val e = exponent n
            in
               if e = Arbnum.zero
                  then (s, e, n)
               else (s, e, fraction e n)
            end
      end
   fun nextfloat (t, w) =
      let
         val mt = Arbnum.less1 (dimword t)
         val mw = Arbnum.less2 (dimword w)
      in
         fn (s: bool, e, f) =>
            if e = Arbnum.zero andalso f = Arbnum.zero
               then (s, e, Arbnum.one)
            else if Arbnum.< (f, mt)
               then (s, e, Arbnum.plus1 f)
            else if Arbnum.< (e, mw)
               then (s, Arbnum.plus1 e, Arbnum.zero)
            else (s, e, f)
      end
in
   datatype float = posInf | negInf | Float of bool * Arbnum.num * Arbnum.num
   fun float_to_real (t, w) =
      let
         val i = Arbrat.fromNat (pow2 (int_max w))
         val j = Arbrat./ (Arbrat.two, i)
         val d = Arbrat.fromNat (dimword t)
      in
         fn (s, e, f) =>
            let
               val f' = Arbrat./ (Arbrat.fromNat f, d)
               val r =
                  if e = Arbnum.zero
                     then Arbrat.* (j, f')
                  else let
                          val e2 = Arbrat./ (Arbrat.fromNat (pow2 e), i)
                       in
                          Arbrat.* (e2, Arbrat.+ (Arbrat.one, f'))
                       end
            in
               if s then Arbrat.negate r else r
            end
      end
   fun real_to_float ((t, w), mode) =
      let
         val real_to_float0 = real_to_float0 (t, w)
         val float_to_real = float_to_real (t, w)
         val nextfloat = nextfloat (t, w)
         val p = int_max w
         val f = uint_max t
         val m = Arbnum.less1 (uint_max w)
         val n = Arbrat./ (Arbrat.fromNat (pow2 m), Arbrat.fromNat (pow2 p))
         val largest = Arbrat.* (n, frac t)
         val threshold = Arbrat.* (n, frac (t + 1))
         val nlargest = Arbrat.negate largest
         val nthreshold = Arbrat.negate threshold
         val top = Float (false, m, f)
         val bottom = Float (true, m, f)
      in
         if mode = binary_ieeeSyntax.roundTiesToEven_tm
            then fn x =>
                    let
                       val r = real_to_arbrat x
                    in
                       if Arbrat.<= (r, nthreshold)
                          then negInf
                       else if Arbrat.>= (r, threshold)
                          then posInf
                       else let
                               val fp = real_to_float0 r
                               val fpr = float_to_real fp
                            in
                               Float
                                 (if fpr = r
                                     then fp
                                  else let
                                          val nfp = nextfloat fp
                                          val nfpr = float_to_real nfp
                                          val fp_diff = diff (fpr, r)
                                          val nfp_diff = diff (nfpr, r)
                                       in
                                          if fp_diff = nfp_diff
                                             then if evenfloat fp
                                                     then fp
                                                  else nfp
                                          else if Arbrat.< (fp_diff, nfp_diff)
                                             then fp
                                          else nfp
                                       end)
                            end
                    end
         else if mode = binary_ieeeSyntax.roundTowardPositive_tm
            then fn x =>
                    let
                       val r = real_to_arbrat x
                    in
                       if Arbrat.< (r, nlargest)
                          then bottom
                       else if Arbrat.> (r, largest)
                          then posInf
                       else let
                               val fp = real_to_float0 r
                            in
                               if float_to_real fp = r orelse negativefloat fp
                                  then Float fp
                               else Float (nextfloat fp)
                            end
                    end
         else if mode = binary_ieeeSyntax.roundTowardNegative_tm
            then fn x =>
                    let
                       val r = real_to_arbrat x
                    in
                       if Arbrat.< (r, nlargest)
                          then negInf
                       else if Arbrat.> (r, largest)
                          then top
                       else let
                               val fp = real_to_float0 r
                            in
                               if float_to_real fp = r orelse positivefloat fp
                                  then Float fp
                               else Float (nextfloat fp)
                            end
                    end
         else if mode = binary_ieeeSyntax.roundTowardZero_tm
            then fn x =>
                    let
                       val r = real_to_arbrat x
                    in
                       if Arbrat.< (r, nlargest)
                          then bottom
                       else if Arbrat.> (r, largest)
                          then top
                       else Float (real_to_float0 r)
                    end
         else raise ERR "real_to_float" "unknown mode"
      end
end

(* ------------------------------------------------------------------------
   REAL_REDUCE_CONV  - based on realSimps.real_compset
   ULP_CONV          - evaluates ground ``ULP (n2w a, (:n))``
   largest_CONV      - evaluates ground ``largest (:m # n)``
   threshold_CONV    - evaluates ground ``threshold (:m # n)``
   float_value_CONV  - evaluates ground ``float_value f``
   ------------------------------------------------------------------------ *)

val float_datatype_rwts =
   #rewrs (TypeBase.simpls_of ``:('a, 'b) float``) @
   #rewrs (TypeBase.simpls_of ``:rounding``)

val FLOAT_DATATYPE_CONV =
   REWRITE_CONV (combinTheory.K_THM :: float_datatype_rwts)

val REAL_REDUCE_CONV = computeLib.CBV_CONV (realSimps.real_compset())

fun memo_conv is_tm cnv0 s =
   let
      val rwts = ref ([]: thm list)
      val cnv = ref (fn _: term => raise Conv.UNCHANGED)
      val err = ERR (s ^ "_CONV") ""
   in
      fn tm =>
         if is_tm tm
            then !cnv tm
                 handle Conv.UNCHANGED =>
                    let
                       val thm = cnv0 tm
                    in
                       rwts := thm :: !rwts
                     ; cnv := PURE_ONCE_REWRITE_CONV (!rwts)
                     ; thm
                    end
         else raise err
   end

local
   val SZ_CONV = Conv.DEPTH_CONV wordsLib.SIZES_CONV THENC REAL_REDUCE_CONV
   fun RWT_CONV rwt = Conv.REWR_CONV rwt THENC SZ_CONV
in
   val ULP_CONV =
      memo_conv binary_ieeeSyntax.is_int_ULP
         (Conv.REWR_CONV binary_ieeeTheory.ULP_def
          THENC Conv.DEPTH_CONV wordsLib.word_EQ_CONV
          THENC PURE_REWRITE_CONV [wordsTheory.w2n_n2w]
          THENC SZ_CONV)
         "ULP"
   val largest_CONV =
      memo_conv binary_ieeeSyntax.is_int_largest
         (RWT_CONV binary_ieeeTheory.largest) "largest"
   val threshold_CONV =
      memo_conv binary_ieeeSyntax.is_int_threshold
         (RWT_CONV binary_ieeeTheory.threshold) "threshold"
end

val float_value_CONV0 =
   Conv.REWR_CONV binary_ieeeTheory.float_value_def
   THENC Conv.RATOR_CONV FLOAT_DATATYPE_CONV
   THENC wordsLib.WORD_CONV
   THENC TRY_CONV
           (Conv.RAND_CONV
               (Conv.REWR_CONV binary_ieeeTheory.float_to_real_def
                THENC FLOAT_DATATYPE_CONV
                THENC wordsLib.WORD_CONV
                THENC REAL_REDUCE_CONV))

val float_value_CONV =
   Conv.CHANGED_CONV (PURE_ONCE_REWRITE_CONV [binary_ieeeTheory.float_values])
   ORELSEC float_value_CONV0

(* ------------------------------------------------------------------------
   round_CONV           - evaluates ground ``round mode r``
   float_round_CONV     - evaluates ground ``float_round mode toneg r``
   ------------------------------------------------------------------------ *)

local
   val mk_real = realSyntax.term_of_int o Arbint.fromInt
   val mk_large = binary_ieeeSyntax.mk_int_largest
   val mk_neg_large = realSyntax.mk_negated o mk_large
   val mk_threshold = binary_ieeeSyntax.mk_int_threshold
   val mk_neg_threshold = realSyntax.mk_negated o mk_threshold
   val mk_ulp = binary_ieeeSyntax.mk_int_ulp
   fun mk_ULP (e, t) =
      binary_ieeeSyntax.mk_ULP
         (pairSyntax.mk_pair
            (e, boolSyntax.mk_itself (fcpSyntax.mk_int_numeric_type t)))
   fun mk_abs_diff (x, r) = realSyntax.mk_absval (realSyntax.mk_minus (x, r))
   fun mk_abs_diff_lt (x, r, u) = realSyntax.mk_less (mk_abs_diff (x, r), u)
   val cond_mk_absval = fn true => realSyntax.mk_absval | _ => Lib.I
   fun mk_abs_leq (b1, r, b2, x) =
      realSyntax.mk_leq (cond_mk_absval b1 r, cond_mk_absval b2 x)
   fun mk_abs_lt (r, x) = realSyntax.mk_less (cond_mk_absval true r, x)
   fun mk_times2 r = realSyntax.mk_mult (mk_real 2, r)
   fun mk_times4 r = realSyntax.mk_mult (mk_real 4, r)
   fun ties_thm (rx2_thm, u_thm, y) =
      boolSyntax.mk_imp
         (boolSyntax.mk_eq (lhsc rx2_thm, lhsc u_thm),
          boolSyntax.mk_neg
            (wordsSyntax.mk_word_lsb
               (binary_ieeeSyntax.mk_float_significand y)))
      |> (Conv.LAND_CONV
            (Conv.FORK_CONV (Conv.REWR_CONV rx2_thm, Conv.REWR_CONV u_thm))
          THENC EVAL)
      |> Drule.EQT_ELIM
   val twm_map =
      ref (Redblackmap.mkDict
            (Lib.pair_compare (Lib.pair_compare (Int.compare, Int.compare),
                               Term.compare))
           : ((int * int) * term, (term -> float) * conv) Redblackmap.dict)
   fun lookup (x as (tw, mode)) =
      case Redblackmap.peek (!twm_map, x) of
         SOME y => y
       | NONE =>
           let
              val f = real_to_float x
              val thm = if mode = binary_ieeeSyntax.roundTiesToEven_tm
                           then threshold_CONV (mk_threshold tw)
                        else largest_CONV (mk_large tw)
              val y = (f, Conv.REWR_CONV thm)
              val () = twm_map := Redblackmap.insert (!twm_map, x, y)
           in
              y
           end
   val toPosInf0 =
      Drule.MATCH_MP binary_ieeeTheory.round_roundTiesToEven_plus_infinity
   val toNegInf0 =
      Drule.MATCH_MP binary_ieeeTheory.round_roundTiesToEven_minus_infinity
   val toPosInf1 =
      Drule.MATCH_MP binary_ieeeTheory.round_roundTowardPositive_plus_infinity
   val toNegInf1 =
      Drule.MATCH_MP binary_ieeeTheory.round_roundTowardNegative_minus_infinity
   val toBot0 =
      Drule.MATCH_MP binary_ieeeTheory.round_roundTowardZero_bottom
   val toTop0 =
      Drule.MATCH_MP binary_ieeeTheory.round_roundTowardZero_top
   val err = ERR "round_CONV"
   fun EQT_REDUCE cnv = Drule.EQT_ELIM o (cnv THENC REAL_REDUCE_CONV)
   val EXPONENT_ULP_CONV = Conv.RAND_CONV FLOAT_DATATYPE_CONV THENC ULP_CONV
   val ulp_conv =
      Conv.LAND_CONV (Conv.REWR_CONV binary_ieeeTheory.ulp_def THENC ULP_CONV)
      THENC REAL_REDUCE_CONV
   val f_word_conv = Conv.LAND_CONV FLOAT_DATATYPE_CONV THENC wordsLib.WORD_CONV
   val ties_to_even =
      Drule.EQT_ELIM o
      (Conv.FORK_CONV (Conv.FORK_CONV (f_word_conv, Conv.RAND_CONV f_word_conv),
                      REAL_REDUCE_CONV)
       THENC REWRITE_CONV [])
   val conj_assoc_rule = PURE_ONCE_REWRITE_RULE [GSYM CONJ_ASSOC]
   fun ties_to_even_thm (y, r, x) =
      let
         val f = binary_ieeeSyntax.mk_float_significand y
         val f0 = boolSyntax.mk_eq
                    (f, wordsSyntax.mk_n2w (``0n``, wordsSyntax.dim_of f))
         val e = binary_ieeeSyntax.mk_float_exponent y
         val e0 = boolSyntax.mk_eq
                    (e, wordsSyntax.mk_n2w (``1n``, wordsSyntax.dim_of e))
         val e1 = boolSyntax.mk_neg e0
         val rx = mk_abs_leq (true, r, true, x)
         val c = boolSyntax.mk_conj (f0, e1)
      in
         mlibUseful.INL (ties_to_even (boolSyntax.mk_imp (c, rx)))
         handle HOL_ERR {origin_function = "EQT_ELIM", ...} =>
           mlibUseful.INR
              (conj_assoc_rule
                 (ties_to_even (boolSyntax.mk_conj (c, boolSyntax.mk_neg rx))))
      end
   val lt_thm =
      Drule.MATCH_MP (realLib.REAL_ARITH ``(a <= b = F) ==> b < a: real``)
   val le_thm =
      Drule.MATCH_MP (realLib.REAL_ARITH ``(a < b = F) ==> b <= a: real``)
   (*
   fun EQ_ELIM thm =
      mlibUseful.INL (Drule.EQT_ELIM thm)
      handle HOL_ERR _ => mlibUseful.INR (Drule.EQF_ELIM thm)
   *)
in
   exception PlusMinusZero of Thm.thm
   fun round_CONV tm =
   let
      val (mode, x, t, w) = binary_ieeeSyntax.dest_round tm
      val tw as (t, w) = (fcpSyntax.dest_int_numeric_type t,
                          fcpSyntax.dest_int_numeric_type w)
      val (r2f, cnv) = lookup (tw, mode)
   in
      (*
        val Float (sef as (s, _, _)) = r2f x
        val SOME l_thm =
           Lib.total
             (EQT_REDUCE (Conv.RAND_CONV cnv))
             (mk_abs_leq (true, x, false, mk_large tw))
      *)
      case r2f x of
         Float (sef as (s, _, _)) =>
            if mode = binary_ieeeSyntax.roundTiesToEven_tm
               then let
                       val u_thm =
                          ulp_conv
                             (realSyntax.mk_less
                                (mk_ulp tw,
                                 realSyntax.mk_mult
                                    (``2r``, realSyntax.mk_absval x)))
                       val u_thm =
                          Drule.EQT_ELIM u_thm
                          handle HOL_ERR _ => raise PlusMinusZero (le_thm u_thm)
                       val t_thm =
                          (EQT_REDUCE (Conv.RAND_CONV cnv))
                             (mk_abs_lt (x, mk_threshold tw))
                       val y = binary_ieeeSyntax.float_of_triple (tw, sef)
                       val r_thm =
                          float_value_CONV (binary_ieeeSyntax.mk_float_value y)
                       val r = binary_ieeeSyntax.dest_float (rhsc r_thm)
                       val u = mk_ULP (binary_ieeeSyntax.mk_float_exponent y, t)
                       val U_thm = EXPONENT_ULP_CONV u
                    in
                       case ties_to_even_thm (y, r, x) of
                          mlibUseful.INL s_thm =>
                             let
                                val rx2 = mk_times2 (mk_abs_diff (r, x))
                                val rx2_thm = REAL_REDUCE_CONV rx2
                                val rx2_u_thm =
                                   EQT_REDUCE
                                      (Conv.LAND_CONV (Conv.REWR_CONV rx2_thm)
                                       THENC Conv.RAND_CONV
                                               (Conv.REWR_CONV U_thm))
                                      (realSyntax.mk_leq (rx2, u))
                                val tie_thm = ties_thm (rx2_thm, U_thm, y)
                                val thm =
                                   Drule.LIST_CONJ
                                      [r_thm, s_thm, rx2_u_thm, tie_thm,
                                       u_thm, t_thm]
                             in
                                MATCH_MP
                                   binary_ieeeTheory.round_roundTiesToEven thm
                             end
                        | mlibUseful.INR s_thm =>
                             let
                                val rx4 = mk_times4 (mk_abs_diff (r, x))
                                val rx4_thm = REAL_REDUCE_CONV rx4
                                val rx4_u_thm =
                                   EQT_REDUCE
                                      (Conv.LAND_CONV (Conv.REWR_CONV rx4_thm)
                                       THENC Conv.RAND_CONV
                                               (Conv.REWR_CONV U_thm))
                                      (realSyntax.mk_leq (rx4, u))
                                val thm =
                                   Drule.LIST_CONJ
                                      [r_thm, s_thm, rx4_u_thm, u_thm, t_thm]
                             in
                                MATCH_MP
                                   binary_ieeeTheory.round_roundTiesToEven0 thm
                             end
                    end
            else if mode = binary_ieeeSyntax.roundTowardPositive_tm
               then raise err "roundTowardPositive: not implemented"
            else if mode = binary_ieeeSyntax.roundTowardNegative_tm
               then raise err "roundTowardNegative: not implemented"
            else if mode = binary_ieeeSyntax.roundTowardZero_tm
               then
                  case Lib.total
                         (EQT_REDUCE (Conv.RAND_CONV cnv))
                         (mk_abs_leq (true, x, false, mk_large tw)) of
                     SOME l_thm =>
                        let
                           val u_thm =
                              ulp_conv (mk_abs_leq (false, mk_ulp tw, true, x))
                           val u_thm =
                              Drule.EQT_ELIM u_thm
                              handle HOL_ERR _ =>
                                 raise PlusMinusZero (lt_thm u_thm)
                           val y = binary_ieeeSyntax.float_of_triple (tw, sef)
                           val r_thm =
                              float_value_CONV
                                 (binary_ieeeSyntax.mk_float_value y)
                           val r = binary_ieeeSyntax.dest_float (rhsc r_thm)
                           val u =
                              mk_ULP (binary_ieeeSyntax.mk_float_exponent y, t)
                           val d_thm =
                              EQT_REDUCE (Conv.RAND_CONV EXPONENT_ULP_CONV)
                                         (mk_abs_diff_lt (r, x, u))
                           val a_thm = EQT_REDUCE Conv.ALL_CONV
                                         (mk_abs_leq (true, r, true, x))
                           val thm = Drule.LIST_CONJ
                                       [r_thm, d_thm, a_thm, u_thm, l_thm]
                        in
                           MATCH_MP binary_ieeeTheory.round_roundTowardZero thm
                        end
                   | NONE =>
                        if s then
                           let
                              val lt =
                                 realSyntax.mk_less (x, mk_neg_large tw)
                              val thm =
                                 EQT_REDUCE
                                   (Conv.RAND_CONV (Conv.RAND_CONV cnv)) lt
                           in
                              toBot0 thm
                           end
                        else let
                                val lt = realSyntax.mk_less (mk_large tw, x)
                                val thm = EQT_REDUCE (Conv.LAND_CONV cnv) lt
                             in
                                toTop0 thm
                             end
            else raise err "unknown mode"
       | posInf =>
            if mode = binary_ieeeSyntax.roundTiesToEven_tm
               then let
                       val le = realSyntax.mk_leq (mk_threshold tw, x)
                       val thm = EQT_REDUCE (Conv.LAND_CONV cnv) le
                    in
                       toPosInf0 thm
                    end
            else if mode = binary_ieeeSyntax.roundTowardPositive_tm
               then let
                       val lt = realSyntax.mk_less (mk_large tw, x)
                       val thm = EQT_REDUCE (Conv.LAND_CONV cnv) lt
                    in
                       toPosInf1 thm
                    end
            else raise err "+inf"
       | negInf =>
            if mode = binary_ieeeSyntax.roundTiesToEven_tm
               then let
                       val le = realSyntax.mk_leq (x, mk_neg_threshold tw)
                       val thm =
                          EQT_REDUCE (Conv.RAND_CONV (Conv.RAND_CONV cnv)) le
                    in
                       toNegInf0 thm
                    end
            else if mode = binary_ieeeSyntax.roundTowardNegative_tm
               then let
                       val lt = realSyntax.mk_less (x, mk_neg_large tw)
                       val thm =
                          EQT_REDUCE (Conv.RAND_CONV (Conv.RAND_CONV cnv)) lt
                    in
                       toNegInf1 thm
                    end
            else raise err "+inf"
   end
end

local
   datatype round_result =
        NotZero of Thm.thm
      | Limit of Thm.thm
      | Zero of Thm.thm
   fun mk_neq_zero tm sz =
      boolSyntax.mk_neg (boolSyntax.mk_eq (tm, wordsSyntax.mk_wordii (0, sz)))
   fun try_round tm =
      let
         val thm = round_CONV tm
         val y = rhsc thm
      in
         if binary_ieeeSyntax.is_float_plus_infinity y
            then Limit (Drule.MATCH_MP
                           binary_ieeeTheory.float_round_plus_infinity thm)
         else if binary_ieeeSyntax.is_float_minus_infinity y
            then Limit (Drule.MATCH_MP
                           binary_ieeeTheory.float_round_minus_infinity thm)
         else if binary_ieeeSyntax.is_float_top y
            then Limit (Drule.MATCH_MP binary_ieeeTheory.float_round_top thm)
         else if binary_ieeeSyntax.is_float_bottom y
            then Limit (Drule.MATCH_MP binary_ieeeTheory.float_round_bottom thm)
         else NotZero thm
      end
      handle PlusMinusZero thm => Zero thm
   val err = ERR "float_round_CONV"
   val rule = REWRITE_RULE [binary_ieeeTheory.float_minus_zero,
                            binary_ieeeTheory.float_plus_zero_def]
   val rule = rule ## rule
   val toEven = rule (binary_ieeeTheory.round_roundTiesToEven_is_minus_zero,
                      binary_ieeeTheory.round_roundTiesToEven_is_plus_zero)
   val toZero = rule (binary_ieeeTheory.round_roundTowardZero_is_minus_zero,
                      binary_ieeeTheory.round_roundTowardZero_is_plus_zero)
   fun rnd_zero_thms toneg mode =
      (if toneg = boolSyntax.T then fst
       else if toneg = boolSyntax.F then snd
       else raise err "+/- 0")
      (if mode = binary_ieeeSyntax.roundTiesToEven_tm
          then toEven
       else if mode = binary_ieeeSyntax.roundTowardPositive_tm
          then raise err "roundTowardPositive: not implemented"
       else if mode = binary_ieeeSyntax.roundTowardNegative_tm
          then raise err "roundTowardNegative: not implemented"
       else if mode = binary_ieeeSyntax.roundTowardZero_tm
          then toZero
       else raise err "unknown mode")
in
   fun float_round_CONV tm =
      let
         val (mode, toneg, x, t, w) = binary_ieeeSyntax.dest_float_round tm
      in
         case try_round (binary_ieeeSyntax.mk_round (mode, x, t, w)) of
            NotZero rnd_thm =>
               let
                  val t = fcpSyntax.dest_int_numeric_type t
                  val w = fcpSyntax.dest_int_numeric_type w
                  val (_, e, f) =
                     binary_ieeeSyntax.dest_floating_point (rhsc rnd_thm)
                  val not_zero_tm =
                     boolSyntax.mk_disj (mk_neq_zero e w, mk_neq_zero f t)
                  val not_zero_thm =
                     Drule.EQT_ELIM (wordsLib.WORD_EVAL_CONV not_zero_tm)
               in
                  Drule.MATCH_MP binary_ieeeTheory.float_round_non_zero
                     (Thm.CONJ rnd_thm not_zero_thm)
                  |> Thm.SPEC toneg
               end
          | Limit thm => Thm.SPEC toneg thm
          | Zero thm => Drule.MATCH_MP (rnd_zero_thms toneg mode) thm
      end
end

local
   val cnv = round_CONV
in
   fun round_CONV tm =
      cnv tm handle PlusMinusZero _ => raise ERR "round_CONV" "+/- 0"
end

(* ------------------------------------------------------------------------
   infinity_intro_CONV - if possible, convert ground FP term to
                         float_plus_infinity or float_minus_infinity

   For example:

     infinity_intro_CONV
        ``<|Sign := 0w; Exponent := 31w; Significand := 0w|> : (10, 5) float``

   gives

     |- <|Sign := 0w; Exponent := 31w; Significand := 0w|> =
        float_plus_infinity (:10 # 5)

   ------------------------------------------------------------------------ *)

local
   fun pow2exp i = Arbnum.pow (Arbnum.two, Arbnum.fromInt i)
   fun mod2exp (w, i) = Arbnum.mod (w, pow2exp i)
   fun eq_thm (n, i, v) =
      Drule.EQT_ELIM
         (wordsLib.WORD_EVAL_CONV
            (boolSyntax.mk_eq (wordsSyntax.mk_wordi (n, i), v)))
   val uint_max = wordsSyntax.mk_word_T o fcpSyntax.mk_int_numeric_type
   val plus = GSYM binary_ieeeTheory.float_plus_infinity_def
   val minus = GSYM binary_ieeeTheory.float_minus_infinity
in
   fun infinity_intro_CONV tm =
      let
         val ((t, w), (s, e, f)) = binary_ieeeSyntax.triple_of_float tm
      in
         if mod2exp (f, t) = Arbnum.zero andalso
            mod2exp (e, w) = Arbnum.less1 (pow2exp w)
            then let
                    val thm = if s then minus else plus
                    val e_thm = eq_thm (e, w, uint_max w)
                    val f_thm = eq_thm (f, t, wordsSyntax.mk_wordii (0, t))
                 in
                    (Conv.RAND_CONV
                       (Conv.FORK_CONV
                          (Conv.RAND_CONV (Conv.REWR_CONV e_thm),
                           Conv.RATOR_CONV
                              (Conv.RAND_CONV
                                  (Conv.RAND_CONV (Conv.REWR_CONV f_thm)))))
                     THENC Conv.REWR_CONV thm) tm
                 end
         else raise ERR "emax_intro_CONV" "not emax term"
      end
end

(* ------------------------------------------------------------------------
   float_add_CONV
   float_sub_CONV
   float_mul_CONV
   float_div_CONV

   For example, float_add_CONV converts ground

      ``float_add mode a b``

   to one of

      ``float_round mode toneg (ra + rb)``
      ``float_some_nan (:10 # 5)``
      ``float_plus_infinity (:10 # 5)``
      ``float_minus_infinity (:10 # 5)``

   The latter two cases only apply when either ``a`` or ``b`` is the same
   infinity term. Missing cases are handled by adding further rewrites to
   the_compset.
   ------------------------------------------------------------------------ *)

local
   val rwt = boolTheory.IMP_CLAUSES |> Drule.SPEC_ALL |> Drule.CONJUNCTS |> hd
   fun is_nan_thm thm =
      case Lib.total boolSyntax.dest_eq (Thm.concl thm) of
         SOME (_, r) => r = binary_ieeeSyntax.nan_tm
       | _ => false
   fun float_x_CONV (name, compute, dest, nan, float_finite,
                     plus_infinity_finite, minus_infinity_finite,
                     finite_plus_infinity, finite_minus_infinity) =
      let
         val err = ERR ("float_" ^ name ^ "_CONV") ""
         fun float_nan (mode, x, y, thm) =
            nan
            |> Drule.ISPECL [mode, x, y]
            |> Conv.CONV_RULE
                 (Conv.LAND_CONV (REWRITE_CONV [thm]) THENC Conv.REWR_CONV rwt)
         val cnv = PURE_ONCE_REWRITE_CONV [compute]
      in
         fn tm =>
            cnv tm
            handle Conv.UNCHANGED =>
            let
               val (mode, x, y) = dest tm
               fun mtch_spec thm1 thm2 =
                  if is_nan_thm thm2
                     then float_nan (mode, x, y, thm2)
                  else (Thm.SPEC mode (Drule.MATCH_MP thm1 thm2)
                        handle HOL_ERR _ => raise err)
               val vx = binary_ieeeSyntax.mk_float_value x
               val vy = binary_ieeeSyntax.mk_float_value y
            in
               if binary_ieeeSyntax.is_float_plus_infinity x
                  then mtch_spec plus_infinity_finite (float_value_CONV vy)
               else if binary_ieeeSyntax.is_float_minus_infinity x
                  then mtch_spec minus_infinity_finite (float_value_CONV vy)
               else if binary_ieeeSyntax.is_float_plus_infinity y
                  then mtch_spec finite_plus_infinity (float_value_CONV vx)
               else if binary_ieeeSyntax.is_float_minus_infinity y
                  then mtch_spec finite_minus_infinity (float_value_CONV vx)
               else
                  let
                     val vx_thm = float_value_CONV vx
                  in
                     if rhsc vx_thm = binary_ieeeSyntax.nan_tm
                        then float_nan (mode, x, y, vx_thm)
                     else let
                             val vy_thm = float_value_CONV vy
                          in
                             if rhsc vy_thm = binary_ieeeSyntax.nan_tm
                                then float_nan (mode, x, y, vy_thm)
                             else
                                mtch_spec float_finite (Thm.CONJ vx_thm vy_thm)
                          end
                  end
            end
      end
in
   val float_add_CONV =
      float_x_CONV
         ("add",
          binary_ieeeTheory.float_add_compute,
          binary_ieeeSyntax.dest_float_add,
          binary_ieeeTheory.float_add_nan,
          binary_ieeeTheory.float_add_finite,
          binary_ieeeTheory.float_add_plus_infinity_finite,
          binary_ieeeTheory.float_add_minus_infinity_finite,
          binary_ieeeTheory.float_add_finite_plus_infinity,
          binary_ieeeTheory.float_add_finite_minus_infinity)
   val float_sub_CONV =
      float_x_CONV
         ("sub",
          binary_ieeeTheory.float_sub_compute,
          binary_ieeeSyntax.dest_float_sub,
          binary_ieeeTheory.float_sub_nan,
          binary_ieeeTheory.float_sub_finite,
          binary_ieeeTheory.float_sub_plus_infinity_finite,
          binary_ieeeTheory.float_sub_minus_infinity_finite,
          binary_ieeeTheory.float_sub_finite_plus_infinity,
          binary_ieeeTheory.float_sub_finite_minus_infinity)
   val float_mul_CONV =
      float_x_CONV
         ("mul",
          binary_ieeeTheory.float_mul_compute,
          binary_ieeeSyntax.dest_float_mul,
          binary_ieeeTheory.float_mul_nan,
          binary_ieeeTheory.float_mul_finite,
          binary_ieeeTheory.float_mul_plus_infinity_finite,
          binary_ieeeTheory.float_mul_minus_infinity_finite,
          binary_ieeeTheory.float_mul_finite_plus_infinity,
          binary_ieeeTheory.float_mul_finite_minus_infinity)
   val float_div_CONV =
      float_x_CONV
         ("div",
          binary_ieeeTheory.float_div_compute,
          binary_ieeeSyntax.dest_float_div,
          binary_ieeeTheory.float_div_nan,
          binary_ieeeTheory.float_div_finite,
          binary_ieeeTheory.float_div_plus_infinity_finite,
          binary_ieeeTheory.float_div_minus_infinity_finite,
          binary_ieeeTheory.float_div_finite_plus_infinity,
          binary_ieeeTheory.float_div_finite_minus_infinity)
end

(* ------------------------------------------------------------------------
   float_equal_CONV
   float_less_than_CONV
   float_less_equal_CONV
   float_greater_than_CONV
   float_greater_equal_CONV
   ------------------------------------------------------------------------ *)

local
   val cmp = realSimps.real_compset ()
   val () = computeLib.add_thms
                ([pairTheory.pair_CASE_def,
                  pairTheory.FST, pairTheory.SND] @
                 #rewrs (TypeBase.simpls_of ``:float_value``)) cmp
   val float_compare_CONV =
      Conv.REWR_CONV binary_ieeeTheory.float_compare_def
      THENC Conv.LAND_CONV (Conv.BINOP_CONV float_value_CONV)
      THENC computeLib.CBV_CONV cmp
   val FLOAT_COMPARE_CONV =
      REWRITE_CONV (#rewrs (TypeBase.simpls_of ``:float_compare``))
   val cnv1 = Conv.LAND_CONV float_compare_CONV THENC FLOAT_COMPARE_CONV
   val cnv2 =
      Conv.RATOR_CONV
         (Conv.RATOR_CONV
            (Conv.RATOR_CONV
               (Conv.RATOR_CONV
                  (Conv.RAND_CONV float_compare_CONV))))
      THENC FLOAT_COMPARE_CONV
in
   val float_compare_CONV = float_compare_CONV
   val float_equal_CONV =
      Conv.REWR_CONV binary_ieeeTheory.float_equal_def THENC cnv1
   val float_less_than_CONV =
      Conv.REWR_CONV binary_ieeeTheory.float_less_than_def THENC cnv1
   val float_less_equal_CONV =
      Conv.REWR_CONV binary_ieeeTheory.float_less_equal_def THENC cnv2
   val float_greater_than_CONV =
      Conv.REWR_CONV binary_ieeeTheory.float_greater_than_def THENC cnv1
   val float_greater_equal_CONV =
      Conv.REWR_CONV binary_ieeeTheory.float_greater_equal_def THENC cnv2
end

(* -------------------------------------------------------------------------
   liftNative
   ------------------------------------------------------------------------- *)

fun withRounding tm f x =
   let
      val mode = IEEEReal.getRoundingMode ()
   in
      IEEEReal.setRoundingMode
        (if tm = binary_ieeeSyntax.roundTiesToEven_tm
            then IEEEReal.TO_NEAREST
         else if tm = binary_ieeeSyntax.roundTowardZero_tm
            then IEEEReal.TO_ZERO
         else if tm = binary_ieeeSyntax.roundTowardNegative_tm
            then IEEEReal.TO_NEGINF
         else if tm = binary_ieeeSyntax.roundTowardPositive_tm
            then IEEEReal.TO_POSINF
         else raise ERR "setRounding" "not a valid mode")
     ; f x before IEEEReal.setRoundingMode mode
   end

fun liftNative1 f dst (tm: term) =
   case Lib.total dst tm of
      SOME (mode, a) =>
        (case Lib.total floatToReal a of
            SOME ra =>
               withRounding mode
                 (fn ra =>
                    mk_native_ieee_thm
                       (boolSyntax.mk_eq (tm, realToFloat (f ra)))) ra
          | _ => raise ERR "liftNative1" "failed to convert to native reals")
    | NONE => raise ERR "liftNative1" ""

fun liftNative2 f dst (tm: term) =
   case Lib.total dst tm of
      SOME (mode, a, b) =>
        (case (Lib.total floatToReal a, Lib.total floatToReal b) of
            (SOME ra, SOME rb) =>
               withRounding mode
                 (fn (ra, rb) =>
                    mk_native_ieee_thm
                       (boolSyntax.mk_eq (tm, realToFloat (f (ra, rb)))))
                 (ra, rb)
          | _ => raise ERR "liftNative2" "failed to convert to native reals")
    | NONE => raise ERR "liftNative2" ""

fun liftNative3 f dst (tm: term) =
   case Lib.total dst tm of
      SOME (mode, a, b, c) =>
        (case (Lib.total floatToReal a,
               Lib.total floatToReal b,
               Lib.total floatToReal c) of
            (SOME ra, SOME rb, SOME rc) =>
               withRounding mode
                 (fn (ra, rb, rc) =>
                    mk_native_ieee_thm
                       (boolSyntax.mk_eq (tm, realToFloat (f (ra, rb, rc)))))
                 (ra, rb, rc)
          | _ => raise ERR "liftNative2" "failed to convert to native reals")
    | NONE => raise ERR "liftNative2" ""

fun liftNativeOrder f dst (tm: term) =
   case Lib.total dst tm of
      SOME (a, b) =>
        (case (Lib.total floatToReal a, Lib.total floatToReal b) of
            (SOME ra, SOME rb) =>
                mk_native_ieee_thm (boolSyntax.mk_eq (tm, f (ra, rb)))
          | _ => raise ERR "liftNativeOrder"
                           "failed to convert to native reals")
    | NONE => raise ERR "liftNativeOrder" ""

(* -------------------------------------------------------------------------
   lcf_or_native_conv
   ------------------------------------------------------------------------- *)

fun mk_b true = boolSyntax.T
  | mk_b false = boolSyntax.F

val mk_float_compare =
   fn IEEEReal.LESS      => binary_ieeeSyntax.LT_tm
    | IEEEReal.EQUAL     => binary_ieeeSyntax.EQ_tm
    | IEEEReal.GREATER   => binary_ieeeSyntax.GT_tm
    | IEEEReal.UNORDERED => binary_ieeeSyntax.UN_tm

val native_eval = ref 0 (* off by default *)
val () = Feedback.register_trace ("native ieee", native_eval, 2)

fun lcf_or_native_conv0 (get_ty, lcf_conv: conv, native_conv: conv, level) =
   fn tm =>
      if !native_eval = level andalso get_ty tm = native_ty
         then native_conv tm (* doesn't cover NaN cases *)
              handle HOL_ERR _ => lcf_conv tm
      else lcf_conv tm

fun lcf_or_native_conv (lcf_conv, native_conv, level) =
   let
      val rnd_conv =
         REAL_REDUCE_CONV
         THENC Conv.RATOR_CONV
                  (Conv.RAND_CONV
                      (FLOAT_DATATYPE_CONV THENC wordsLib.WORD_EVAL_CONV))
         THENC float_round_CONV
      val cnv = lcf_conv THENC TRY_CONV rnd_conv
   in
      lcf_or_native_conv0 (Term.type_of, cnv, native_conv, level)
   end

fun lcf_or_native_order_conv (lcf_conv, native_conv) =
   lcf_or_native_conv0 (Term.type_of o Term.rand, lcf_conv, native_conv, 2)

val native_float_sqrt_CONV =
   liftNative1 Math.sqrt binary_ieeeSyntax.dest_float_sqrt

val native_float_add_CONV =
   liftNative2 Real.+ binary_ieeeSyntax.dest_float_add

val native_float_sub_CONV =
   liftNative2 Real.- binary_ieeeSyntax.dest_float_sub

(**************************************************************
 NOTE:
   Poly/ML's multiply isn't fully IEEE compliant on 64-bit machines, which
   results in some selftest failures
 **************************************************************)

val native_float_mul_CONV =
   liftNative2 Real.* binary_ieeeSyntax.dest_float_mul

val native_float_div_CONV =
   liftNative2 Real./ binary_ieeeSyntax.dest_float_div

val native_float_mul_add_CONV =
   liftNative3 Real.*+ binary_ieeeSyntax.dest_float_mul_add

val native_float_less_than_CONV =
   liftNativeOrder (mk_b o Real.<) binary_ieeeSyntax.dest_float_less_than

val native_float_less_equal_CONV =
   liftNativeOrder (mk_b o Real.<=) binary_ieeeSyntax.dest_float_less_equal

val native_float_greater_than_CONV =
   liftNativeOrder (mk_b o Real.>) binary_ieeeSyntax.dest_float_greater_than

val native_float_greater_equal_CONV =
   liftNativeOrder (mk_b o Real.>=) binary_ieeeSyntax.dest_float_greater_equal

val native_float_equal_CONV =
   liftNativeOrder (mk_b o Real.==) binary_ieeeSyntax.dest_float_equal

val native_float_compare_CONV =
   liftNativeOrder (mk_float_compare o Real.compareReal)
      binary_ieeeSyntax.dest_float_compare

val sqrt_CONV = lcf_or_native_conv (NO_CONV, native_float_sqrt_CONV, 1)

val add_CONV = lcf_or_native_conv (float_add_CONV, native_float_add_CONV, 2)
val sub_CONV = lcf_or_native_conv (float_sub_CONV, native_float_sub_CONV, 2)
val mul_CONV = lcf_or_native_conv (float_mul_CONV, native_float_mul_CONV, 2)
val div_CONV = lcf_or_native_conv (float_div_CONV, native_float_div_CONV, 2)

(* mul_add_CONV could benefit from a more efficient LCF custom conversion *)

val mul_add_CONV =
   lcf_or_native_conv
      (Conv.REWR_CONV binary_ieeeTheory.float_mul_add_def THENC EVAL,
       native_float_mul_add_CONV, 2)

(**************************************************************
 NOTE:
   Real.compareReal for Poly/ML < revision 1918 doesn't work for infinities.
 **************************************************************)

val compare_CONV =
   lcf_or_native_order_conv (float_compare_CONV, native_float_compare_CONV)

val equal_CONV =
   lcf_or_native_order_conv (float_equal_CONV, native_float_equal_CONV)

val less_than_CONV =
   lcf_or_native_order_conv (float_less_than_CONV, native_float_less_than_CONV)

val less_equal_CONV =
   lcf_or_native_order_conv
      (float_less_equal_CONV, native_float_less_equal_CONV)

val greater_than_CONV =
   lcf_or_native_order_conv
      (float_greater_than_CONV, native_float_greater_than_CONV)

val greater_equal_CONV =
   lcf_or_native_order_conv
      (float_greater_equal_CONV, native_float_greater_equal_CONV)

(* ------------------------------------------------------------------------
   Add rewrites and conversions to compsets
   ------------------------------------------------------------------------ *)

val ieee_rewrites =
   let
      open binary_ieeeTheory
      val sr = SIMP_RULE (srw_ss())
      val sr0 = sr []
      val spc = Drule.GEN_ALL o sr0 o
                Q.SPEC `<| Sign := s; Exponent := e; Significand := f |>`
   in
      [float_to_real, spc float_value_def, float_tests, ulp_def,
       infinity_properties, some_nan_properties, float_infinity_negate_abs,
       spc float_negate_def, spc float_abs_def, float_plus_zero_def,
       sr0 float_top_def, float_plus_min_def, float_minus_min_def,
       float_minus_zero, sr [float_top_def, float_negate_def] float_bottom_def,
       float_components
       ] @
      List.take (Drule.CONJUNCTS float_values, 3) @ float_datatype_rwts
   end

val float_Sign_fupd_tm =
   Term.mk_thy_const
      {Ty = ``:(word1 -> word1) -> ('t, 'w) float -> ('t, 'w) float``,
       Thy = "binary_ieee",
       Name = "float_Sign_fupd"}

fun add_ieee_to_compset cmp =
   let
      open computeLib
   in
      add_thms ieee_rewrites cmp
    ; List.app (fn a => add_conv a cmp)
        [
         (float_Sign_fupd_tm, 2, infinity_intro_CONV),
         (binary_ieeeSyntax.ULP_tm, 1, ULP_CONV),
         (binary_ieeeSyntax.largest_tm, 1, largest_CONV),
         (binary_ieeeSyntax.threshold_tm, 1, threshold_CONV),
         (binary_ieeeSyntax.round_tm, 2, round_CONV),
         (binary_ieeeSyntax.float_sqrt_tm, 2, sqrt_CONV),
         (binary_ieeeSyntax.float_add_tm, 3, add_CONV),
         (binary_ieeeSyntax.float_sub_tm, 3, sub_CONV),
         (binary_ieeeSyntax.float_mul_tm, 3, mul_CONV),
         (binary_ieeeSyntax.float_div_tm, 3, div_CONV),
         (binary_ieeeSyntax.float_mul_add_tm, 4, mul_add_CONV),
         (binary_ieeeSyntax.float_round_tm, 3, float_round_CONV),
         (binary_ieeeSyntax.float_compare_tm, 2, compare_CONV),
         (binary_ieeeSyntax.float_equal_tm, 2, equal_CONV),
         (binary_ieeeSyntax.float_less_than_tm, 2, less_than_CONV),
         (binary_ieeeSyntax.float_less_equal_tm, 2, less_equal_CONV),
         (binary_ieeeSyntax.float_greater_than_tm, 2, greater_than_CONV),
         (binary_ieeeSyntax.float_greater_equal_tm, 2, greater_equal_CONV)
        ]
   end

val () = add_ieee_to_compset computeLib.the_compset

(* ------------------------------------------------------------------------ *)

end
