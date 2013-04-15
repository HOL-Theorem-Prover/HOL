structure binary_ieeeLib :> binary_ieeeLib =
struct

open HolKernel Parse boolLib bossLib
open realLib wordsLib binary_ieeeSyntax
open lcsymtacs

structure Parse =
struct
  open Parse
  val (Type, Term) =
     Lib.with_flag (Feedback.emit_WARNING, false)
        parse_from_grammars binary_ieeeTheory.binary_ieee_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "binary_ieeeLib"
val lhsc = boolSyntax.lhs o Thm.concl
val rhsc = boolSyntax.rhs o Thm.concl

(* ------------------------------------------------------------------------
   Bit-vector Encodings
   ------------------------------------------------------------------------ *)

local
   infix 0 ==
   infix 8 &
   infixr 5 @@ o'
   open lcsymtacs binary_ieeeSyntax
   val op & = Term.mk_comb
   val op == = boolSyntax.mk_eq
   val op @@ = wordsSyntax.mk_word_concat
   val op o' = combinSyntax.mk_o
   val i2t = numLib.term_of_int
   val mk_w = wordsSyntax.mk_word_type
   val real_ty = realSyntax.real_ty
   val mode = Term.mk_var ("mode", rounding_ty)
   fun dest_float_ty ty =
      case Lib.total Type.dest_type ty of
         SOME ("float", [t, w]) => pairSyntax.mk_prod (t, w)
       | _ => raise ERR "dest_float_ty" "not a float type"
   val get_function =
      fst o boolSyntax.strip_comb o boolSyntax.lhs o
      snd o boolSyntax.strip_forall o List.hd o boolSyntax.strip_conj o
      Thm.concl
   fun mk_fp_to_float fp fp_ty float_ty pre_k t t_ty w_ty =
      let
         val fp_to_float = fp ^ "_to_float"
         val fp_to_float_var = Term.mk_var (fp_to_float, fp_ty --> float_ty)
         val w = Term.mk_var ("w", fp_ty)
         val s = i2t pre_k
         val float =
            TypeBase.mk_record (float_ty,
               [("Sign", wordsSyntax.mk_word_extract (s, s, w, ``:1``)),
                ("Exponent", wordsSyntax.mk_word_extract
                                (i2t (pre_k - 1), i2t t, w, w_ty)),
                ("Significand", wordsSyntax.mk_word_extract
                                   (i2t (t - 1), i2t 0, w, t_ty))])
         val def =
            Definition.new_definition (fp_to_float ^ "_def",
               fp_to_float_var & w == float)
      in
         (get_function def, def)
      end
   fun mk_float_to_fp fp fp_ty float_ty t_ty w_ty =
      let
         val float_to_fp = "float_to_" ^ fp
         val float_to_fp_var = Term.mk_var (float_to_fp, float_ty --> fp_ty)
         val x = Term.mk_var ("x", float_ty)
         val def =
            Definition.new_definition (float_to_fp ^ "_def",
              float_to_fp_var & x ==
              mk_float_sign x @@ mk_float_exponent x @@ mk_float_significand x)
      in
         (get_function def, def)
      end
   fun mk_fp_to_real fp float_to_real fp_to_float fp_ty =
      let
         val fp_to_real = fp ^ "_to_real"
         val fp_to_real_var = Term.mk_var (fp_to_real, fp_ty --> real_ty)
         val def =
            Definition.new_definition (fp_to_real ^ "_def",
              fp_to_real_var == float_to_real o' fp_to_float)
      in
         (get_function def, def)
      end
   fun mk_real_to_fp fp round float_to_fp fp_ty =
      let
         val real_to_fp = "real_to_" ^ fp
         val real_to_fp_var =
            Term.mk_var (real_to_fp, rounding_ty --> real_ty --> fp_ty)
         val def =
            Definition.new_definition (real_to_fp ^ "_def",
              real_to_fp_var & mode == float_to_fp o' round & mode)
      in
         (get_function def, def)
      end
   fun lift1 float_to_fp fp_to_float fp_ty float_ty =
      let
         val ty1 = fp_ty --> fp_ty
         val ty2 = float_ty --> float_ty
      in
         fn (s, f) =>
            let
               val (v, tm) =
                  (Term.mk_var (s, ty1), Term.mk_const (f, ty2))
                  handle HOL_ERR _ =>
                    (Term.mk_var (s, rounding_ty --> ty1) & mode,
                     Term.mk_const (f, rounding_ty --> ty2) & mode)
               val def =
                  Definition.new_definition (s ^ "_def",
                     v == float_to_fp o' tm o' fp_to_float)
            in
               def
            end
      end
   fun lift1b fp_to_float fp_ty float_ty =
      let
         val ty1 = fp_ty --> Type.bool
         val ty2 = float_ty --> Type.bool
      in
         fn (s, f) =>
            let
               val (v, tm) = (Term.mk_var (s, ty1), Term.mk_const (f, ty2))
               val def =
                  Definition.new_definition (s ^ "_def",
                     v == tm o' fp_to_float)
            in
               def
            end
      end
   fun lift1c float_to_fp fp_ty float_ty =
      let
         val dim_ty = dest_float_ty float_ty
         val ty = Type.mk_type ("itself", [dim_ty]) --> float_ty
         val a = boolSyntax.mk_itself dim_ty
      in
         fn (s, f) =>
            let
               val v = Term.mk_var (s, fp_ty)
               val tm = Term.mk_const (f, ty) & a
               val def =
                  Definition.new_definition (s ^ "_def", v == float_to_fp & tm)
            in
               def
            end
      end
   fun lift2 float_to_fp fp_to_float fp_ty float_ty =
      let
         val ty1 = rounding_ty --> fp_ty --> fp_ty --> fp_ty
         val ty2 = rounding_ty --> float_ty --> float_ty --> float_ty
         val a = Term.mk_var ("a", fp_ty)
         val b = Term.mk_var ("b", fp_ty)
      in
         fn (s, f) =>
            let
               val v = Term.mk_var (s, ty1)
               val tm = Term.mk_const (f, ty2)
               val def =
                  Definition.new_definition (s ^ "_def",
                     v & mode & a & b ==
                     float_to_fp & (tm & mode & (fp_to_float & a) &
                                                (fp_to_float & b)))
            in
               def
            end
      end
   fun lift2b fp_to_float fp_ty float_ty =
      let
         val ty1 = fp_ty --> fp_ty --> Type.bool
         val ty2 = float_ty --> float_ty --> Type.bool
         val a = Term.mk_var ("a", fp_ty)
         val b = Term.mk_var ("b", fp_ty)
      in
         fn (s, f) =>
            let
               val v = Term.mk_var (s, ty1)
               val tm = Term.mk_const (f, ty2)
               val def =
                  Definition.new_definition (s ^ "_def",
                     v & a & b ==
                     tm & (fp_to_float & a) & (fp_to_float & b))
            in
               def
            end
      end
   fun encoding_thms (fp, fp_to_float_def, float_to_fp_def) =
      let
         val fp_to_float = get_function fp_to_float_def
         val float_to_fp = get_function float_to_fp_def
         val fp_to_float_11 =
            Q.store_thm (fp ^ "_to_float_11",
               `!x y. (^fp_to_float x = ^fp_to_float y) = (x = y)`,
               srw_tac [wordsLib.WORD_BIT_EQ_ss]
                 [fp_to_float_def, binary_ieeeTheory.float_component_equality]
               >> decide_tac
               )
         val float_to_fp_11 =
            Q.store_thm ("float_to_" ^ fp ^ "_11",
               `!x y. (^float_to_fp x = ^float_to_fp y) = (x = y)`,
               srw_tac [wordsLib.WORD_BIT_EQ_ss]
                 [float_to_fp_def, binary_ieeeTheory.float_component_equality]
               >> decide_tac
               )
         val float_to_fp_fp_to_float =
            Q.store_thm ("float_to_" ^ fp ^ "_" ^ fp ^ "_to_float",
               `!x. ^float_to_fp (^fp_to_float x) = x`,
               srw_tac [wordsLib.WORD_EXTRACT_ss]
                 [float_to_fp_def, fp_to_float_def]
               )
         val fp_to_float_float_to_fp =
            Q.store_thm (fp ^ "_to_float_float_to_" ^ fp,
               `!x. ^fp_to_float (^float_to_fp x) = x`,
               rw [float_to_fp_def, fp_to_float_def,
                   binary_ieeeTheory.float_component_equality]
               >> simp_tac (srw_ss()++wordsLib.WORD_EXTRACT_ss) []
               )
         val fp_nchotomy =
            Q.store_thm(fp ^ "_nchotomy",
               `!x. ?y. x = ^float_to_fp y`,
               gen_tac
               >> qexists_tac `^fp_to_float x`
               >> rewrite_tac [float_to_fp_fp_to_float]
               )
         val float_nchotomy =
            Q.store_thm("float_" ^ fp ^ "_nchotomy",
               `!x. ?y. x = ^fp_to_float y`,
               gen_tac
               >> qexists_tac `^float_to_fp x`
               >> rewrite_tac [fp_to_float_float_to_fp]
               )
      in
         (fp_to_float_11, float_to_fp_11,
          float_to_fp_fp_to_float, fp_to_float_float_to_fp,
          fp_nchotomy, float_nchotomy)
      end
   val get_float_to_fp =
      boolSyntax.rator o boolSyntax.rand o boolSyntax.lhs o snd o
      boolSyntax.strip_forall o Thm.concl
   fun try_f f x = Option.getOpt (Lib.total f x, x)
   val opname = fst o Term.dest_const o get_function
   fun monop fp_to_float_float_to_fp =
      let
         val float_to_fp = get_float_to_fp fp_to_float_float_to_fp
      in
         fn op_def =>
            Theory.save_thm (opname op_def ^ "_float_to_fp",
               Q.AP_THM op_def `^(get_float_to_fp fp_to_float_float_to_fp) a`
               |> REWRITE_RULE [fp_to_float_float_to_fp, combinTheory.o_THM]
               |> Drule.GEN_ALL
            )
      end
   fun binop fp_to_float_float_to_fp =
      let
         val float_to_fp = get_float_to_fp fp_to_float_float_to_fp
      in
         fn op_def =>
            Theory.save_thm (opname op_def ^ "_float_to_fp",
               op_def
               |> try_f (Thm.SPEC ``mode:rounding``)
               |> Q.ISPEC `^float_to_fp a`
               |> Q.ISPEC `^float_to_fp b`
               |> REWRITE_RULE [fp_to_float_float_to_fp]
               |> Q.GENL [`b`, `a`]
               |> Drule.GEN_ALL
            )
      end
   fun monop_n2w op_def =
      Theory.save_thm (opname op_def ^ "_n2w",
         Q.AP_THM op_def `n2w a`
         |> REWRITE_RULE [combinTheory.o_THM]
         |> Drule.GEN_ALL
      )
   fun binop_n2w op_def =
      Theory.save_thm (opname op_def ^ "_n2w",
         op_def |> try_f (Thm.SPEC ``mode:rounding``)
                |> Q.SPECL [`n2w a`, `n2w b`]
                |> Drule.GEN_ALL
      )
   fun fp_to_float_n2w (fp, t, w, fp_to_float_def) =
      let
         open bitTheory arithmeticTheory
         val fp_to_float = get_function fp_to_float_def
      in
         Q.store_thm (fp ^ "_to_float_n2w",
            `!n.
               ^fp_to_float (n2w n) =
                  let (q, f) = DIVMOD_2EXP ^(i2t t) n in
                  let (s, e) = DIVMOD_2EXP ^(i2t w) q in
                     <| Sign := n2w (s MOD 2);
                        Exponent := n2w e;
                        Significand := n2w f |>`,
            lrw [fp_to_float_def, BIT_def, BITS_THM, DIVMOD_2EXP_def,
                 DIV_2EXP_def, MOD_2EXP_def, wordsTheory.word_extract_n2w,
                 DIV_1, DIV2_def, ODD_MOD2_LEM, DIV_DIV_DIV_MULT]
         )
      end
in
   fun mk_fp_encoding (fp, t, w) =
      let
 (* e.g. val fp = "fp16" and t = 10 and w = 5 *)
         val pre_k = t + w
         val k = pre_k + 1
         val t_ty = fcpSyntax.mk_int_numeric_type t
         val w_ty = fcpSyntax.mk_int_numeric_type w
         val fp_ty = mk_w (fcpSyntax.mk_int_numeric_type k)
         val float_ty = Type.mk_type ("float", [t_ty, w_ty])
         val float_to_real =
            Term.mk_const ("float_to_real", float_ty --> real_ty)
         val round =
            Term.mk_const ("round", rounding_ty --> real_ty --> float_ty)
         val (fp_to_float, fp_to_float_def) =
            mk_fp_to_float fp fp_ty float_ty pre_k t t_ty w_ty
         val (float_to_fp, float_to_fp_def) =
            mk_float_to_fp fp fp_ty float_ty t_ty w_ty
         val (fp_to_real, fp_to_real_def) =
            mk_fp_to_real fp float_to_real fp_to_float fp_ty
         val (real_to_fp, real_to_fp_def) =
            mk_real_to_fp fp round float_to_fp fp_ty
         val lift1 = lift1 float_to_fp fp_to_float fp_ty float_ty
         val lift1b = lift1b fp_to_float fp_ty float_ty
         val lift1c = lift1c float_to_fp fp_ty float_ty
         val lift2 = lift2 float_to_fp fp_to_float fp_ty float_ty
         val lift2b = lift2b fp_to_float fp_ty float_ty
         val fp_roundToIntegral_def =
            lift1 (fp ^ "_roundToIntegral", "float_round_to_integral")
         val fp_negate_def = lift1 (fp ^ "_negate", "float_negate")
         val fp_abs_def = lift1 (fp ^ "_abs", "float_abs")
         val fp_isnan_def = lift1b (fp ^ "_isNan", "float_is_nan")
         val fp_isintegral_def =
            lift1b (fp ^ "_isIntegral", "float_is_integral")
         val fp_iszero_def = lift1b (fp ^ "_isZero", "float_is_zero")
         val fp_isnormal_def = lift1b (fp ^ "_isNormal", "float_is_normal")
         val fp_issubnormal_def =
            lift1b (fp ^ "_isSubnormal", "float_is_subnormal")
         val fp_isfinite_def = lift1b (fp ^ "_isFinite", "float_is_finite")
         val fp_isinfinite_def =
            lift1b (fp ^ "_isInfinite", "float_is_infinite")
         val fp_posinf_def = lift1c (fp ^ "_posInf", "float_plus_infinity")
         val fp_neginf_def = lift1c (fp ^ "_negInf", "float_minus_infinity")
         val fp_poszero_def = lift1c (fp ^ "_posZero", "float_plus_zero")
         val fp_negzero_def = lift1c (fp ^ "_negZero", "float_minus_zero")
         val fp_minpos_def = lift1c (fp ^ "_posMin", "float_plus_min")
         val fp_minneg_def = lift1c (fp ^ "_negMin", "float_minus_min")
         val fp_top_def = lift1c (fp ^ "_top", "float_top")
         val fp_bottom_def = lift1c (fp ^ "_bottom", "float_bottom")
         val fp_add_def = lift2 (fp ^ "_add", "float_add")
         val fp_sub_def = lift2 (fp ^ "_sub", "float_sub")
         val fp_mul_def = lift2 (fp ^ "_mul", "float_mul")
         val fp_div_def = lift2 (fp ^ "_div", "float_div")
         val fp_equal_def = lift2b (fp ^ "_equal", "float_equal")
         val fp_lessthan_def = lift2b (fp ^ "_lessThan", "float_less_than")
         val fp_lessequal_def = lift2b (fp ^ "_lessEqual", "float_less_equal")
         val fp_greaterthan_def =
            lift2b (fp ^ "_greaterThan", "float_greater_than")
         val fp_greaterequal_def =
            lift2b (fp ^ "_greaterEqual", "float_greater_equal")
         val (fp_to_float_11, float_to_fp_11,
              float_to_fp_fp_to_float, fp_to_float_float_to_fp,
              fp_nchotomy, float_nchotomy) =
            encoding_thms (fp, fp_to_float_def, float_to_fp_def)
         val monop = monop fp_to_float_float_to_fp
         val binop = binop fp_to_float_float_to_fp
         val fp_to_float_n2w = fp_to_float_n2w (fp, t, w, fp_to_float_def)
      in
         [fp_to_float_float_to_fp, fp_to_float_n2w, real_to_fp_def,
          fp_posinf_def, fp_neginf_def, fp_poszero_def, fp_negzero_def,
          fp_minpos_def, fp_minneg_def, fp_top_def, fp_bottom_def,
          float_to_fp_fp_to_float, fp_to_float_float_to_fp] @
         (List.concat o List.map (fn th => [monop th, monop_n2w th]))
            [fp_to_real_def, fp_abs_def, fp_negate_def, fp_isnan_def,
             fp_isintegral_def, fp_iszero_def, fp_isnormal_def,
             fp_issubnormal_def, fp_isfinite_def, fp_isinfinite_def] @
         (List.concat o List.map (fn th => [binop th, binop_n2w th]))
            [fp_add_def, fp_sub_def, fp_mul_def, fp_div_def,
             fp_equal_def, fp_lessthan_def, fp_lessequal_def,
             fp_greaterthan_def, fp_greaterequal_def]
      end
end

(*

val thms = mk_fp_encoding ("fp", 10, 5)

open binary_ieeeLib machine_ieeeTheory

(EVAL THENC REWRITE_CONV [float_to_fp16_def] THENC EVAL)
   ``fp16_add roundTowardZero 284278w 284728w``;

Count.apply (EVAL THENC REWRITE_CONV [float_to_fp32_def] THENC EVAL)
   ``fp32_mul roundTowardZero 0xEEEE0000w 284728w``;

Count.apply EVAL ``fp32_mul roundTowardZero 0xEEEE0000w 284728w``;

Count.apply EVAL ``real_to_fp16 roundTowardZero (1 / 2)``
Count.apply EVAL ``real_to_fp32 roundTowardZero (1 / 2)``
Count.apply EVAL ``real_to_fp32 roundTowardZero (1 / 3)``
Count.apply EVAL ``real_to_fp64 roundTowardZero (1 / 3)``
Count.apply EVAL ``real_to_fp64 roundTowardZero (0.123456789)``

*)

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
   fun real_to_float1 (t, w) =
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
         val real_to_float1 = real_to_float1 (t, w)
         val float_to_real = float_to_real (t, w)
         val nextfloat = nextfloat (t, w)
         val p = int_max w
         val f = uint_max t
         val m = Arbnum.less1 (uint_max w)
         val n = Arbrat./ (Arbrat.fromNat (pow2 m), Arbrat.fromNat (pow2 p))
         val largest = Arbrat.* (n, frac t)
         val threshold = Arbrat.* (n, frac (t + 1))
         val top = Float (false, m, f)
         val bottom = Float (true, m, f)
      in
         if mode = binary_ieeeSyntax.roundTiesToEven_tm
            then fn x =>
                    let
                       val r = real_to_arbrat x
                    in
                       if Arbrat.<= (r, Arbrat.negate threshold)
                          then negInf
                       else if Arbrat.>= (r, threshold)
                          then posInf
                       else let
                               val fp = real_to_float1 r
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
                       if Arbrat.< (r, Arbrat.negate largest)
                          then bottom
                       else if Arbrat.> (r, largest)
                          then posInf
                       else let
                               val fp = real_to_float1 r
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
                       if Arbrat.< (r, Arbrat.negate largest)
                          then negInf
                       else if Arbrat.> (r, largest)
                          then top
                       else let
                               val fp = real_to_float1 r
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
                       if Arbrat.< (r, Arbrat.negate largest)
                          then bottom
                       else if Arbrat.> (r, largest)
                          then top
                       else Float (real_to_float1 r)
                    end
         else raise ERR "real_to_float" "unknown mode"
      end
end

(* ------------------------------------------------------------------------
   FLOAT_DATATYPE_CONV
   REAL_REDUCE_CONV
   ULP_CONV
   largest_CONV
   threshold_CONV
   ------------------------------------------------------------------------ *)

val float_datatype_rwts =
   case TypeBase.simpls_of ``:('a, 'b) float`` of
      {convs = [], rewrs = r} => r
    | _ => raise ERR "float_datatype_rwts" ""

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
                       val () = rwts := thm :: !rwts
                       val () = cnv := PURE_ONCE_REWRITE_CONV (!rwts)
                    in
                       thm
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

(* ------------------------------------------------------------------------
   round_CONV
   float_round_CONV
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
   fun significand0_thm (y, r, x) =
      let
         val f = binary_ieeeSyntax.mk_float_significand y
         val f0 = boolSyntax.mk_eq
                    (f, wordsSyntax.mk_n2w (``0n``, wordsSyntax.dim_of f))
         val e = binary_ieeeSyntax.mk_float_exponent y
         val e1 =
            boolSyntax.mk_neg
               (boolSyntax.mk_eq
                   (e, wordsSyntax.mk_n2w (``1n``, wordsSyntax.dim_of e)))
         val rx = mk_abs_leq (true, r, true, x)
         val s0 = boolSyntax.mk_imp (boolSyntax.mk_conj (f0, e1), rx)
      in
         Drule.EQT_ELIM (EVAL s0)
         handle HOL_ERR _ =>
            raise ERR "significand0_thm" "round to nearest special case"
        (*  Drule.EQT_ELIM
              (EVAL (boolSyntax.mk_conj (boolSyntax.mk_conj (f0, e1),
                                         boolSyntax.mk_neg rx))) *)
      end
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
   val FLOAT_DATATYPE_CONV =
      REWRITE_CONV (combinTheory.K_THM :: float_datatype_rwts)
   val EXPONENT_ULP_CONV = Conv.RAND_CONV FLOAT_DATATYPE_CONV THENC ULP_CONV
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
      val tw as (t, w) = binary_ieeeSyntax.dest_ifloat_ty (Term.type_of tm)
      val (mode, x) = binary_ieeeSyntax.dest_round tm
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
                          EVAL (realSyntax.mk_less
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
                       val r_thm = EVAL (binary_ieeeSyntax.mk_float_value y)
                       val r = binary_ieeeSyntax.dest_float (rhsc r_thm)
                       val s_thm = significand0_thm (y, r, x)
                       val u = mk_ULP (binary_ieeeSyntax.mk_float_exponent y, t)
                       val U_thm = EXPONENT_ULP_CONV u
                       val rx2 = mk_times2 (mk_abs_diff (r, x))
                       val rx2_thm = REAL_REDUCE_CONV rx2
                       val rx2_u_thm =
                          EQT_REDUCE
                             (Conv.LAND_CONV (Conv.REWR_CONV rx2_thm)
                              THENC Conv.RAND_CONV (Conv.REWR_CONV U_thm))
                             (realSyntax.mk_leq (rx2, u))
                       val tie_thm = ties_thm (rx2_thm, U_thm, y)
                       val thm =
                          Drule.LIST_CONJ [r_thm, s_thm, rx2_u_thm, tie_thm,
                                           u_thm, t_thm]
                    in
                       MATCH_MP binary_ieeeTheory.round_roundTiesToEven thm
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
                              EVAL (mk_abs_leq (false, mk_ulp tw, true, x))
                           val u_thm =
                              Drule.EQT_ELIM u_thm
                              handle HOL_ERR _ =>
                                 raise PlusMinusZero (lt_thm u_thm)
                           val y = binary_ieeeSyntax.float_of_triple (tw, sef)
                           val r_thm = EVAL (binary_ieeeSyntax.mk_float_value y)
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
   fun set_type ty tm = Term.inst (Type.match_type (Term.type_of tm) ty) tm
   fun mk_round_with_ty (mode, x, ty) =
      set_type ty (binary_ieeeSyntax.mk_round (mode, x))
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
         val ty = Term.type_of tm
         val tw as (t, w) = binary_ieeeSyntax.dest_ifloat_ty ty
         val (mode, toneg, x) = binary_ieeeSyntax.dest_float_round tm
      in
         case try_round (mk_round_with_ty (mode, x, ty)) of
            NotZero rnd_thm =>
               let
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
   infinity_intro_CONV
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
   ------------------------------------------------------------------------ *)

local
   val rwt = boolTheory.IMP_CLAUSES |> Drule.SPEC_ALL |> Drule.CONJUNCTS |> hd
   fun is_nan_thm thm =
      case Lib.total boolSyntax.dest_eq (Thm.concl thm) of
         SOME (_, r) => r = binary_ieeeSyntax.nan_tm
       | _ => false
   fun float_x_CONV
          (dest, nan, float_finite, plus_infinity_finite, minus_infinity_finite,
           finite_plus_infinity, finite_minus_infinity) =
      let
         fun float_nan (mode, x, y, thm) =
            nan
            |> Drule.ISPECL [mode, x, y]
            |> Conv.CONV_RULE
                 (Conv.LAND_CONV (REWRITE_CONV [thm]) THENC Conv.REWR_CONV rwt)
      in
         fn tm =>
            let
               val (mode, x, y) = dest tm
               fun mtch_spec thm1 thm2 =
                  if is_nan_thm thm2
                     then float_nan (mode, x, y, thm2)
                  else Thm.SPEC mode (Drule.MATCH_MP thm1 thm2)
               val vx = binary_ieeeSyntax.mk_float_value x
               val vy = binary_ieeeSyntax.mk_float_value y
            in
               if binary_ieeeSyntax.is_float_plus_infinity x
                  then mtch_spec plus_infinity_finite (EVAL vy)
               else if binary_ieeeSyntax.is_float_minus_infinity x
                  then mtch_spec minus_infinity_finite (EVAL vy)
               else if binary_ieeeSyntax.is_float_plus_infinity y
                  then mtch_spec finite_plus_infinity (EVAL vx)
               else if binary_ieeeSyntax.is_float_minus_infinity y
                  then mtch_spec finite_minus_infinity (EVAL vx)
               else
                  let
                     val vx_thm = EVAL vx
                  in
                     if rhsc vx_thm = binary_ieeeSyntax.nan_tm
                        then float_nan (mode, x, y, vx_thm)
                     else let
                             val vy_thm = EVAL vy
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
         (binary_ieeeSyntax.dest_float_add,
          binary_ieeeTheory.float_add_nan,
          binary_ieeeTheory.float_add_finite,
          binary_ieeeTheory.float_add_plus_infinity_finite,
          binary_ieeeTheory.float_add_minus_infinity_finite,
          binary_ieeeTheory.float_add_finite_plus_infinity,
          binary_ieeeTheory.float_add_finite_minus_infinity)
   val float_sub_CONV =
      float_x_CONV
         (binary_ieeeSyntax.dest_float_sub,
          binary_ieeeTheory.float_sub_nan,
          binary_ieeeTheory.float_sub_finite,
          binary_ieeeTheory.float_sub_plus_infinity_finite,
          binary_ieeeTheory.float_sub_minus_infinity_finite,
          binary_ieeeTheory.float_sub_finite_plus_infinity,
          binary_ieeeTheory.float_sub_finite_minus_infinity)
   val float_mul_CONV =
      float_x_CONV
         (binary_ieeeSyntax.dest_float_mul,
          binary_ieeeTheory.float_mul_nan,
          binary_ieeeTheory.float_mul_finite,
          binary_ieeeTheory.float_mul_plus_infinity_finite,
          binary_ieeeTheory.float_mul_minus_infinity_finite,
          binary_ieeeTheory.float_mul_finite_plus_infinity,
          binary_ieeeTheory.float_mul_finite_minus_infinity)
   val float_div_CONV =
      float_x_CONV
         (binary_ieeeSyntax.dest_float_div,
          binary_ieeeTheory.float_div_nan,
          binary_ieeeTheory.float_div_finite,
          binary_ieeeTheory.float_div_plus_infinity_finite,
          binary_ieeeTheory.float_div_minus_infinity_finite,
          binary_ieeeTheory.float_div_finite_plus_infinity,
          binary_ieeeTheory.float_div_finite_minus_infinity)
end

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
       float_add_compute, float_sub_compute,
       float_mul_compute, float_div_compute,
       rounding_distinct] @
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
      ; add_conv (binary_ieeeSyntax.ULP_tm, 1, ULP_CONV) cmp
      ; add_conv (binary_ieeeSyntax.largest_tm, 1, largest_CONV) cmp
      ; add_conv (binary_ieeeSyntax.threshold_tm, 1, threshold_CONV) cmp
      ; add_conv (binary_ieeeSyntax.float_add_tm, 3, float_add_CONV) cmp
      ; add_conv (binary_ieeeSyntax.float_sub_tm, 3, float_sub_CONV) cmp
      ; add_conv (binary_ieeeSyntax.float_mul_tm, 3, float_mul_CONV) cmp
      ; add_conv (binary_ieeeSyntax.float_div_tm, 3, float_div_CONV) cmp
      ; add_conv (float_Sign_fupd_tm, 2, infinity_intro_CONV) cmp
      ; add_conv (binary_ieeeSyntax.round_tm, 2, round_CONV) cmp
      ; add_conv (binary_ieeeSyntax.float_round_tm, 3, float_round_CONV) cmp
   end

val () = add_ieee_to_compset computeLib.the_compset

(* ------------------------------------------------------------------------ *)

(* Testing

open lcsymtacs binary_ieeeTheory

EVAL ``float_round roundTiesToEven F (-1 / 10000000) : (10, 5) float``
EVAL ``float_round roundTiesToEven F (1 / 1000000000) : (10, 5) float``
EVAL ``float_round roundTiesToEven T (1 / 1000000000) : (10, 5) float``
EVAL ``float_round roundTowardZero T (1 / 1000000000) : (10, 5) float``

fun op_inst tm i =
   Term.mk_comb (Term.inst [``:'t`` |-> ``:10``, ``:'w`` |-> ``:5``] tm,
                 case i of
                    0 => binary_ieeeSyntax.roundTiesToEven_tm
                  | 1 => binary_ieeeSyntax.roundTowardZero_tm
                  | 2 => binary_ieeeSyntax.roundTowardPositive_tm
                  | _ => binary_ieeeSyntax.roundTowardNegative_tm)

val opn = op_inst binary_ieeeSyntax.float_add_tm 0
val opn = op_inst binary_ieeeSyntax.float_sub_tm 0
val opn = op_inst binary_ieeeSyntax.float_mul_tm 0
val opn = op_inst binary_ieeeSyntax.float_div_tm 0

EVAL ``
   let a = float_to_real
              ^(binary_ieeeSyntax.float_of_triple
                   ((10, 5), (false, Arbnum.fromInt 10, Arbnum.fromInt 8))) in
   let b = float_to_real
              ^(binary_ieeeSyntax.float_of_triple
                   ((10, 5), (false, Arbnum.fromInt 10, Arbnum.fromInt 9)))
   in a + (b - a) / 2``

EVAL ``round roundTowardZero (2067 / 65536) : (10, 5) float``
EVAL ``round roundTiesToEven (2067 / 65536) : (10, 5) float``

EVAL ``round roundTowardZero (2065 / 65536) : (10, 5) float``
EVAL ``round roundTiesToEven (2065 / 65536) : (10, 5) float``

EVAL ``
   let a = float_to_real
              <|Sign := 0w; Exponent := 10w: word5; Significand := -1w: word10|>
   in
   let b = float_to_real
              <|Sign := 0w; Exponent := 11w: word5; Significand := 0w: word10|>
   in a + (b - a) / 2``

EVAL ``round roundTowardZero (4095 / 65536) : (10, 5) float``
EVAL ``round roundTiesToEven (4095 / 65536) : (10, 5) float`` (* fail *)


EVAL ``^opn (float_top (:10 # 5))
            (round roundTowardZero (2))``;

EVAL ``^opn (float_top (:10 # 5))
            (round roundTowardZero (200))``;

EVAL ``^opn (float_bottom (:10 # 5))
            (round roundTowardZero (2))``;

EVAL ``^opn (float_bottom (:10 # 5))
            (round roundTowardZero (200))``;


EVAL ``^opn <| Sign := 0w; Exponent := 0w; Significand := 0w |>
            <| Sign := 0w; Exponent := 0w; Significand := 0w |>``;

EVAL ``^opn <| Sign := 0w; Exponent := 11w; Significand := 11w |>
            <| Sign := 0w; Exponent := 0w; Significand := 0w |>``;

EVAL ``^opn <| Sign := 0w; Exponent := 11w; Significand := 11w |>
            <| Sign := 1w; Exponent := 0w; Significand := 0w |>``;

EVAL ``^opn <| Sign := 0w; Exponent := 11w; Significand := 11w |>
            (float_plus_infinity (:10 # 5))``;

EVAL ``^opn <| Sign := 1w; Exponent := 11w; Significand := 11w |>
            (float_plus_infinity (:10 # 5))``;

EVAL ``^opn <| Sign := 0w; Exponent := 11w; Significand := 11w |>
            (float_minus_infinity (:10 # 5))``;

EVAL ``^opn <| Sign := 1w; Exponent := 11w; Significand := 11w |>
            (float_minus_infinity (:10 # 5))``;


EVAL ``^opn <| Sign := 0w; Exponent := 11w; Significand := 11w |>
            <| Sign := 0w; Exponent := 31w; Significand := 0w |>``;

EVAL ``^opn <| Sign := 0w; Exponent := 31w; Significand := 0w |>
            <| Sign := 0w; Exponent := 11w; Significand := 11w |>``;

EVAL ``^opn <| Sign := 0w; Exponent := 11w; Significand := 11w |>
            <| Sign := 1w; Exponent := 31w; Significand := 0w |>``;

EVAL ``^opn <| Sign := 1w; Exponent := 31w; Significand := 0w |>
            <| Sign := 0w; Exponent := 11w; Significand := 11w |>``;


EVAL ``^opn <| Sign := 0w; Exponent := 11w; Significand := 11w |>
            <| Sign := 0w; Exponent := 31w; Significand := 1w |>``;

EVAL ``^opn <| Sign := 0w; Exponent := 31w; Significand := 1w |>
            <| Sign := 0w; Exponent := 11w; Significand := 11w |>``;


EVAL ``^opn <| Sign := 0w; Exponent := 11w; Significand := 12w |>
            <| Sign := 0w; Exponent := 11w; Significand := 11w |>``;

EVAL ``^opn (round roundTowardZero (1 / 3))
            (round roundTowardZero (2)) :> float_value``;


EVAL ``^opn (float_plus_infinity (:10 # 5))
            (round roundTowardZero (2))``;

EVAL ``^opn (float_minus_infinity (:10 # 5))
            (round roundTowardZero (2))``;

EVAL ``^opn (round roundTowardZero (2))
            (float_plus_infinity (:10 # 5))``;

EVAL ``^opn (round roundTowardZero (2))
            (float_minus_infinity (:10 # 5))``;


EVAL ``^opn (float_plus_infinity (:10 # 5))
            (float_plus_infinity (:10 # 5))``;

EVAL ``^opn (float_plus_infinity (:10 # 5))
            (float_minus_infinity (:10 # 5))``;

EVAL ``^opn (float_minus_infinity (:10 # 5))
            (float_plus_infinity (:10 # 5))``;

EVAL ``^opn (float_minus_infinity (:10 # 5))
            (float_minus_infinity (:10 # 5))``;


EVAL ``^opn <| Sign := 0w; Exponent := 31w; Significand := 1w |>
            (float_plus_infinity (:10 # 5))``;

EVAL ``^opn <| Sign := 0w; Exponent := 31w; Significand := 1w |>
            (float_minus_infinity (:10 # 5))``;

EVAL ``^opn (float_plus_infinity (:10 # 5))
            <| Sign := 0w; Exponent := 31w; Significand := 1w |>``;

EVAL ``^opn (float_minus_infinity (:10 # 5))
            <| Sign := 0w; Exponent := 31w; Significand := 1w |>``;





val tm = ``float_round roundTowardZero b (1/100000000) : (10, 5) float``

float_round_CONV ``float_round roundTowardNegative T (0) : (10, 5) float``

float_round_CONV ``float_round roundTowardZero F (0) : (10, 5) float``
float_round_CONV ``float_round roundTowardZero T (0) : (10, 5) float``
float_round_CONV ``float_round roundTowardZero b (34500) : (10, 5) float``

float_round_CONV ``float_round roundTowardZero T (1/100000000) : (10, 5) float``
float_round_CONV ``float_round roundTowardZero T (-1/100000000) : (10, 5) float``
float_round_CONV ``float_round roundTowardZero F (1/100000000) : (10, 5) float``
float_round_CONV ``float_round roundTowardZero F (-1/100000000) : (10, 5) float``
float_round_CONV ``float_round roundTowardZero b (1/100000000) : (10, 5) float``

float_round_CONV ``float_round roundTowardZero b (100000000) : (10, 5) float``
float_round_CONV ``float_round roundTowardZero b (-100000000) : (10, 5) float``

float_round_CONV ``float_round roundTowardPositive b (100000000) : (10, 5) float``
float_round_CONV ``float_round roundTowardNegative b (-100000000) : (10, 5) float``
float_round_CONV ``float_round roundTiesToEven T (100000000) : (10, 5) float``
float_round_CONV ``float_round roundTiesToEven b (-100000000) : (10, 5) float``

val tm = ``float_round roundTowardZero T (34500) : (10, 5) float``
val tm = ``float_round roundTowardZero F (1 / 100000000) : (10, 5) float``
val tm = ``float_round roundTowardZero T (1 / 100000000) : (10, 5) float``

val thm =
   Count.apply round_CONV
      ``round roundTowardZero (0xFFFFFFFF) : (53, 10) float``
val ethm = EVAL ``float_value ^(rhs (concl thm))``

val tm = ``round roundTowardZero (1 / 2) : (53, 10) float``
val tm = ``round roundTowardPositive (1280000) : (10, 5) float``

val tm = ``round roundTowardZero (34500) : (10, 5) float``
val tm = ``round roundTowardZero (100000) : (10, 5) float``
val tm = ``round roundTowardZero (1 / 100000) : (10, 5) float``
val tm = ``round roundTowardNegative (1280000) : (10, 5) float``

val thm =
   Count.apply round_CONV ``round roundTowardZero (-100000) : (10, 5) float``
val thm =
   Count.apply round_CONV ``round roundTowardZero (100000) : (10, 5) float``
val thm =
   Count.apply round_CONV ``round roundTowardZero (34500) : (10, 5) float``
val thm = Count.apply round_CONV ``round roundTowardZero (345) : (10, 5) float``
val thm = Count.apply round_CONV ``round roundTowardZero (135) : (10, 5) float``
val thm =
   Count.apply round_CONV ``round roundTowardZero (1 / 100000) : (10, 5) float``
val thm =
   Count.apply round_CONV ``round roundTowardZero (1 / 2) : (10, 5) float``

Count.apply round_CONV ``round roundTowardPositive (1280000) : (10, 5) float``
Count.apply round_CONV ``round roundTowardNegative (-1280000) : (10, 5) float``
Count.apply round_CONV ``round roundTiesToEven (1280000) : (10, 5) float``
Count.apply round_CONV ``round roundTiesToEven (-1280000) : (10, 5) float``

EVAL ``float_value ^(rhsc thm)``

EVAL ``float_value (<|Sign := 0w; Exponent := 30w; Significand := 54w|> :
                    (10, 5) float)``


EVAL ``ULP (1w: word5, (:10))``
EVAL ``ulp (:10 # 5)``;
EVAL ``largest (:10 # 5)``;
EVAL ``threshold (:10 # 5)``;

EVAL ``float_to_real (<| Sign := 0w; Exponent := -1w; Significand := 1w |> :
                    (10, 5) float)``;

EVAL ``float_plus_zero (:10 # 5)``;
EVAL ``float_minus_zero (:10 # 5)``;
EVAL ``float_plus_min (:10 # 5)``;
EVAL ``float_top (:10 # 5)``;
EVAL ``float_bottom (:10 # 5)``;
EVAL ``float_plus_infinity (:10 # 5)``;
EVAL ``float_minus_infinity (:10 # 5)``;
EVAL ``float_some_nan (:10 # 5)``;

EVAL ``float_negate (float_plus_zero (:10 # 5))``;
EVAL ``float_negate (float_minus_zero (:10 # 5))``;
EVAL ``float_negate (float_plus_min (:10 # 5))``;
EVAL ``float_negate (float_top (:10 # 5))``;
EVAL ``float_negate (float_bottom (:10 # 5))``;
EVAL ``float_negate (float_plus_infinity (:10 # 5))``;
EVAL ``float_negate (float_minus_infinity (:10 # 5))``;
EVAL ``float_negate (float_some_nan (:10 # 5))``;

EVAL ``float_abs (float_plus_zero (:10 # 5))``;
EVAL ``float_abs (float_minus_zero (:10 # 5))``;
EVAL ``float_abs (float_plus_min (:10 # 5))``;
EVAL ``float_abs (float_top (:10 # 5))``;
EVAL ``float_abs (float_bottom (:10 # 5))``;
EVAL ``float_abs (float_plus_infinity (:10 # 5))``;
EVAL ``float_abs (float_minus_infinity (:10 # 5))``;
EVAL ``float_abs (float_some_nan (:10 # 5))``;


EVAL ``float_negate (<| Sign := 0w; Exponent := 11w; Significand := 12w |> :
                    (10, 5) float)``;

EVAL ``float_negate (<| Sign := 0w; Exponent := -1w; Significand := 1w |> :
                    (10, 5) float)``;

EVAL ``float_value (float_plus_zero (:10 # 5))``;
EVAL ``float_value (float_minus_zero (:10 # 5))``;
EVAL ``float_value (float_plus_min (:10 # 5))``;
EVAL ``float_value (float_top (:10 # 5))``;
EVAL ``float_value (float_bottom (:10 # 5))``;
EVAL ``float_value (float_plus_infinity (:10 # 5))``;
EVAL ``float_value (float_minus_infinity (:10 # 5))``;
EVAL ``float_value (float_some_nan (:10 # 5))``;

EVAL ``float_value (<| Sign := 0w; Exponent := 11w; Significand := 12w |> :
                    (10, 5) float)``;

EVAL ``float_value (<| Sign := 0w; Exponent := -1w; Significand := 1w |> :
                    (10, 5) float)``;

EVAL ``float_is_nan (float_plus_zero (:10 # 5))``;
EVAL ``float_is_nan (float_minus_zero (:10 # 5))``;
EVAL ``float_is_nan (float_plus_min (:10 # 5))``;
EVAL ``float_is_nan (float_top (:10 # 5))``;
EVAL ``float_is_nan (float_bottom (:10 # 5))``;
EVAL ``float_is_nan (float_plus_infinity (:10 # 5))``;
EVAL ``float_is_nan (float_minus_infinity (:10 # 5))``;
EVAL ``float_is_nan (float_some_nan (:10 # 5))``;

EVAL ``float_is_nan (<| Sign := 0w; Exponent := 11w; Significand := 12w |> :
                     (10, 5) float)``;

EVAL ``float_is_nan (<| Sign := 0w; Exponent := -1w; Significand := 1w |> :
                     (10, 5) float)``;

EVAL ``float_is_infinite (float_plus_zero (:10 # 5))``;
EVAL ``float_is_infinite (float_minus_zero (:10 # 5))``;
EVAL ``float_is_infinite (float_plus_min (:10 # 5))``;
EVAL ``float_is_infinite (float_top (:10 # 5))``;
EVAL ``float_is_infinite (float_bottom (:10 # 5))``;
EVAL ``float_is_infinite (float_plus_infinity (:10 # 5))``;
EVAL ``float_is_infinite (float_minus_infinity (:10 # 5))``;
EVAL ``float_is_infinite (float_some_nan (:10 # 5))``;

EVAL ``float_is_infinite
          (<| Sign := 0w; Exponent := 11w; Significand := 12w |> :
           (10, 5) float)``;

EVAL ``float_is_infinite
          (<| Sign := 0w; Exponent := -1w; Significand := 1w |> :
           (10, 5) float)``;

EVAL ``float_is_finite (float_plus_zero (:10 # 5))``;
EVAL ``float_is_finite (float_minus_zero (:10 # 5))``;
EVAL ``float_is_finite (float_plus_min (:10 # 5))``;
EVAL ``float_is_finite (float_top (:10 # 5))``;
EVAL ``float_is_finite (float_bottom (:10 # 5))``;
EVAL ``float_is_finite (float_plus_infinity (:10 # 5))``;
EVAL ``float_is_finite (float_minus_infinity (:10 # 5))``;
EVAL ``float_is_finite (float_some_nan (:10 # 5))``;

EVAL ``float_is_finite
          (<| Sign := 0w; Exponent := 11w; Significand := 12w |> :
           (10, 5) float)``;

EVAL ``float_is_finite
          (<| Sign := 0w; Exponent := -1w; Significand := 1w |> :
           (10, 5) float)``;

EVAL ``float_is_normal (float_plus_zero (:10 # 5))``;
EVAL ``float_is_normal (float_minus_zero (:10 # 5))``;
EVAL ``float_is_normal (float_plus_min (:10 # 5))``;
EVAL ``float_is_normal (float_top (:10 # 5))``;
EVAL ``float_is_normal (float_bottom (:10 # 5))``;
EVAL ``float_is_normal (float_plus_infinity (:10 # 5))``;
EVAL ``float_is_normal (float_minus_infinity (:10 # 5))``;
EVAL ``float_is_normal (float_some_nan (:10 # 5))``;

EVAL ``float_is_normal (<| Sign := 0w; Exponent := 11w; Significand := 12w |> :
                     (10, 5) float)``;

EVAL ``float_is_normal (<| Sign := 0w; Exponent := -1w; Significand := 1w |> :
                     (10, 5) float)``;

EVAL ``float_is_subnormal (float_plus_zero (:10 # 5))``;
EVAL ``float_is_subnormal (float_minus_zero (:10 # 5))``;
EVAL ``float_is_subnormal (float_plus_min (:10 # 5))``;
EVAL ``float_is_subnormal (float_top (:10 # 5))``;
EVAL ``float_is_subnormal (float_bottom (:10 # 5))``;
EVAL ``float_is_subnormal (float_plus_infinity (:10 # 5))``;
EVAL ``float_is_subnormal (float_minus_infinity (:10 # 5))``;
EVAL ``float_is_subnormal (float_some_nan (:10 # 5))``;

EVAL ``float_is_subnormal
          (<| Sign := 0w; Exponent := 11w; Significand := 12w |> :
           (10, 5) float)``;

EVAL ``float_is_subnormal
          (<| Sign := 0w; Exponent := -1w; Significand := 1w |> :
           (10, 5) float)``;

EVAL ``float_is_zero (float_plus_zero (:10 # 5))``;
EVAL ``float_is_zero (float_minus_zero (:10 # 5))``;
EVAL ``float_is_zero (float_plus_min (:10 # 5))``;
EVAL ``float_is_zero (float_top (:10 # 5))``;
EVAL ``float_is_zero (float_bottom (:10 # 5))``;
EVAL ``float_is_zero (float_plus_infinity (:10 # 5))``;
EVAL ``float_is_zero (float_minus_infinity (:10 # 5))``;
EVAL ``float_is_zero (float_some_nan (:10 # 5))``;

EVAL ``float_is_zero (<| Sign := 0w; Exponent := 11w; Significand := 12w |> :
                      (10, 5) float)``;

EVAL ``float_is_zero (<| Sign := 0w; Exponent := -1w; Significand := 1w |> :
                      (10, 5) float)``;

*)

(* ------------------------------------------------------------------------ *)

end
