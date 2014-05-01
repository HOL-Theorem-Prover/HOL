structure machine_ieeeLib :> machine_ieeeLib =
struct

open HolKernel Parse boolLib bossLib
open lcsymtacs realSyntax wordsLib binary_ieeeSyntax

structure Parse =
struct
  open Parse
  val (Type, Term) = parse_from_grammars binary_ieeeTheory.binary_ieee_grammars
end
open Parse

val ERR = Feedback.mk_HOL_ERR "machine_ieeeLib"

(* ------------------------------------------------------------------------
   mk_fp_encoding (prefix, significand_width, exponent_width)

   Generate definitions & theorems for bit-vector encodings of fixed size FP
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
   fun lift3 float_to_fp fp_to_float fp_ty float_ty =
      let
         val ty1 = rounding_ty --> fp_ty --> fp_ty --> fp_ty --> fp_ty
         val ty2 =
           rounding_ty --> float_ty --> float_ty --> float_ty --> float_ty
         val a = Term.mk_var ("a", fp_ty)
         val b = Term.mk_var ("b", fp_ty)
         val c = Term.mk_var ("c", fp_ty)
      in
         fn (s, f) =>
            let
               val v = Term.mk_var (s, ty1)
               val tm = Term.mk_const (f, ty2)
               val def =
                  Definition.new_definition (s ^ "_def",
                     v & mode & a & b & c ==
                     float_to_fp & (tm & mode & (fp_to_float & a) &
                                                (fp_to_float & b) &
                                                (fp_to_float & c)))
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
               op_def
               |> try_f (Thm.SPEC ``mode:rounding``)
               |> Lib.C Q.AP_THM  `^float_to_fp a`
               |> REWRITE_RULE [fp_to_float_float_to_fp, combinTheory.o_THM]
               |> Drule.GEN_ALL
            )
      end
   fun mode_op vs fp_to_float_float_to_fp =
      let
         val float_to_fp = get_float_to_fp fp_to_float_float_to_fp
         val ty = fst (Type.dom_rng (Term.type_of float_to_fp))
         val vs = List.map (fn v => Term.mk_var (v, ty)) vs
         val l = List.map (fn v => boolSyntax.mk_icomb (float_to_fp, v)) vs
      in
         fn op_def =>
            Theory.save_thm (opname op_def ^ "_float_to_fp",
               op_def
               |> try_f (Thm.SPEC ``mode:rounding``)
               |> Drule.ISPECL l
               |> REWRITE_RULE [fp_to_float_float_to_fp]
               |> Thm.GENL (List.rev vs)
               |> Drule.GEN_ALL
            )
      end
   val binop = mode_op ["a", "b"]
   val triop = mode_op ["a", "b", "c"]
   fun monop_n2w op_def =
      Theory.save_thm (opname op_def ^ "_n2w",
         op_def
         |> try_f (Thm.SPEC ``mode:rounding``)
         |> Lib.C Q.AP_THM `n2w a`
         |> REWRITE_RULE [combinTheory.o_THM]
         |> Drule.GEN_ALL
      )
   fun mode_op_n2w l op_def =
      Theory.save_thm (opname op_def ^ "_n2w",
         op_def
         |> try_f (Thm.SPEC ``mode:rounding``)
         |> Q.SPECL l
         |> Drule.GEN_ALL
      )
   val binop_n2w = mode_op_n2w [`n2w a`, `n2w b`]
   val triop_n2w = mode_op_n2w [`n2w a`, `n2w b`, `n2w c`]
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
   fun mk_fp_encoding (fp, t, w, a) =
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
         val lift3 = lift3 float_to_fp fp_to_float fp_ty float_ty
         val fp_roundToIntegral_def =
            lift1 (fp ^ "_roundToIntegral", "float_round_to_integral")
         val fp_sqrt_def = lift1 (fp ^ "_sqrt", "float_sqrt")
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
         val fp_mul_add_def = lift3 (fp ^ "_mul_add", "float_mul_add")
         val (fp_to_float_11, float_to_fp_11,
              float_to_fp_fp_to_float, fp_to_float_float_to_fp,
              fp_nchotomy, float_nchotomy) =
            encoding_thms (fp, fp_to_float_def, float_to_fp_def)
         val monop = monop fp_to_float_float_to_fp
         val binop = binop fp_to_float_float_to_fp
         val triop = triop fp_to_float_float_to_fp
         val fp_to_float_n2w = fp_to_float_n2w (fp, t, w, fp_to_float_def)
      in
         case a of
            SOME name => Parse.type_abbrev (name, float_ty)
          | NONE => ()
       ; [fp_to_float_float_to_fp, fp_to_float_n2w, real_to_fp_def,
          fp_posinf_def, fp_neginf_def, fp_poszero_def, fp_negzero_def,
          fp_minpos_def, fp_minneg_def, fp_top_def, fp_bottom_def,
          float_to_fp_fp_to_float, fp_to_float_float_to_fp] @
         (List.concat o List.map (fn th => [monop th, monop_n2w th]))
            [fp_to_real_def, fp_abs_def, fp_negate_def, fp_isnan_def,
             fp_isintegral_def, fp_iszero_def, fp_isnormal_def,
             fp_issubnormal_def, fp_isfinite_def, fp_isinfinite_def,
             fp_roundToIntegral_def, fp_sqrt_def] @
         (List.concat o List.map (fn th => [binop th, binop_n2w th]))
            [fp_add_def, fp_sub_def, fp_mul_def, fp_div_def,
             fp_equal_def, fp_lessthan_def, fp_lessequal_def,
             fp_greaterthan_def, fp_greaterequal_def] @
         (List.concat o List.map (fn th => [triop th, triop_n2w th]))
            [fp_mul_add_def]
      end
end

end
