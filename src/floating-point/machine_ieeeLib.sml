structure machine_ieeeLib :> machine_ieeeLib =
struct

open HolKernel Parse boolLib bossLib
open realSyntax intrealSyntax wordsLib binary_ieeeSyntax

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
   infixr 5 @@ o' **
   open binary_ieeeSyntax
   val op & = Term.mk_comb
   val op == = boolSyntax.mk_eq
   val op @@ = wordsSyntax.mk_word_concat
   val op o' = combinSyntax.mk_o
   val op ** = pairSyntax.mk_prod
   val i2t = numLib.term_of_int
   val mk_w = wordsSyntax.mk_word_type
   val real_ty = realSyntax.real_ty
   val value_ty = binary_ieeeSyntax.float_value_ty
   val mode = Term.mk_var ("mode", rounding_ty)
   fun dest_float_ty ty =
      case Lib.total Type.dest_type ty of
         SOME ("float", [t, w]) => t ** w
       | _ => raise ERR "dest_float_ty" "not a float type"
   val get_function =
      fst o boolSyntax.strip_comb o boolSyntax.lhs o
      snd o boolSyntax.strip_forall o List.hd o boolSyntax.strip_conj o
      Thm.concl
   fun mk_I_hashhash f =
     pairSyntax.mk_pair_map
       (Term.inst [alpha |-> flags_ty] combinSyntax.I_tm, f)
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
   fun mk_fp_to_real fp float_value fp_to_float fp_ty =
      let
         val fp_to_real = fp ^ "_to_real"
         val fp_to_real_var = Term.mk_var (fp_to_real, fp_ty --> value_ty)
         val def =
            Definition.new_definition (fp_to_real ^ "_def",
              fp_to_real_var == float_value o' fp_to_float)
      in
         (get_function def, def)
      end
   fun mk_real_to_fp fp real_to_float float_to_fp fp_ty =
      let
         val real_to_fp = "real_to_" ^ fp
         val real_to_fp_var =
            Term.mk_var (real_to_fp, rounding_ty --> real_ty --> fp_ty)
         val def =
            Definition.new_definition (real_to_fp ^ "_def",
              real_to_fp_var & mode == float_to_fp o' real_to_float & mode)
      in
         (get_function def, def)
      end
   fun mk_real_to_fp_with_flags fp real_to_float_with_flags float_to_fp fp_ty =
      let
         val real_to_fp = "real_to_" ^ fp ^ "_with_flags"
         val real_to_fp_var =
            Term.mk_var
              (real_to_fp, rounding_ty --> real_ty --> flags_ty ** fp_ty)
         val def =
            Definition.new_definition (real_to_fp ^ "_def",
              real_to_fp_var & mode ==
              mk_I_hashhash float_to_fp o' real_to_float_with_flags & mode)
      in
         (get_function def, def)
      end
   fun mk_int_to_fp fp real_to_fp fp_ty =
      let
         val ty = rounding_ty --> intSyntax.int_ty --> fp_ty
         val a = Term.mk_var ("a", intSyntax.int_ty)
         val s = "int_to_" ^ fp
         val v = Term.mk_var (s, ty)
      in
         Definition.new_definition (s ^ "_def",
            v & mode & a ==
            real_to_fp & mode & (intrealSyntax.real_of_int_tm & a))
      end
   val int_option_ty = optionSyntax.mk_option intSyntax.int_ty
   fun mk_fp_to_int fp fp_to_float fp_ty float_ty =
      let
         val ty1 = rounding_ty --> fp_ty --> int_option_ty
         val ty2 = rounding_ty --> float_ty --> int_option_ty
         val s = fp ^ "_to_int"
         val v = Term.mk_var (s, ty1)
         val float_to_int = Term.mk_const ("float_to_int", ty2)
      in
         Definition.new_definition (s ^ "_def",
            v & mode == (float_to_int & mode) o' fp_to_float)
      end
   fun lift1 float_to_fp fp_to_float fp_ty float_ty with_flags has_flags =
      let
         val ty1 =
           if with_flags then fp_ty --> flags_ty ** fp_ty else fp_ty --> fp_ty
         val ty2 = if has_flags then float_ty --> flags_ty ** float_ty
                   else float_ty --> float_ty
         val snd_tm = Term.inst [alpha |-> flags_ty, beta |-> float_ty]
                      pairSyntax.snd_tm
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
                     v == (if with_flags then
                             mk_I_hashhash float_to_fp o' tm o' fp_to_float
                           else if has_flags then
                             float_to_fp o' snd_tm o' tm o' fp_to_float
                           else float_to_fp o' tm o' fp_to_float))
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
   fun lift2 float_to_fp fp_to_float fp_ty float_ty with_flags =
      let
         val ty1 =
           if with_flags then
             rounding_ty --> fp_ty --> fp_ty --> flags_ty ** fp_ty
           else rounding_ty --> fp_ty --> fp_ty --> fp_ty
         val ty2 =
           rounding_ty --> float_ty --> float_ty --> flags_ty ** float_ty
         val a = Term.mk_var ("a", fp_ty)
         val b = Term.mk_var ("b", fp_ty)
         val snd_tm = Term.inst [alpha |-> flags_ty, beta |-> float_ty]
                      pairSyntax.snd_tm
      in
         fn (s, f) =>
            let
               val v = Term.mk_var (s, ty1)
               val tm = Term.mk_const (f, ty2)
               val x = tm & mode & (fp_to_float & a) & (fp_to_float & b)
               val def =
                  Definition.new_definition (s ^ "_def",
                     v & mode & a & b ==
                     (if with_flags then
                        mk_I_hashhash float_to_fp & x
                      else float_to_fp & (snd_tm & x)))
            in
               def
            end
      end
   fun lift2b fp_to_float fp_ty float_ty res_ty =
      let
         val ty1 = fp_ty --> fp_ty --> res_ty
         val ty2 = float_ty --> float_ty --> res_ty
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
   fun lift3 float_to_fp fp_to_float fp_ty float_ty with_flags =
      let
         val ty1 =
           if with_flags then
             rounding_ty --> fp_ty --> fp_ty --> fp_ty --> flags_ty ** fp_ty
           else rounding_ty --> fp_ty --> fp_ty --> fp_ty --> fp_ty
         val ty2 = rounding_ty --> float_ty --> float_ty --> float_ty -->
                   flags_ty ** float_ty
         val a = Term.mk_var ("a", fp_ty)
         val b = Term.mk_var ("b", fp_ty)
         val c = Term.mk_var ("c", fp_ty)
         val snd_tm = Term.inst [alpha |-> flags_ty, beta |-> float_ty]
                      pairSyntax.snd_tm
      in
         fn (s, f) =>
            let
               val v = Term.mk_var (s, ty1)
               val tm = Term.mk_const (f, ty2)
               val x = tm & mode & (fp_to_float & a) & (fp_to_float & b) &
                                   (fp_to_float & c)
               val def =
                  Definition.new_definition (s ^ "_def",
                     v & mode & a & b & c ==
                     (if with_flags then
                        mk_I_hashhash float_to_fp & x
                      else float_to_fp & (snd_tm & x)))
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
   fun all_combs [h1] [h2] = [[h1], [h2]]
     | all_combs (h1 :: t1) (h2 :: t2) =
        let
          val r = all_combs t1 t2
        in
          List.map (fn x => h1 :: x) r @
          List.map (fn x => h2 :: x) r
        end
     | all_combs _ _ = raise ERR "all_combs" ""
   val get_float_to_fp =
      boolSyntax.rator o boolSyntax.rand o boolSyntax.lhs o snd o
      boolSyntax.strip_forall o Thm.concl
   fun try_f f x = Option.getOpt (Lib.total f x, x)
   val opname = fst o Term.dest_const o get_function
   fun xop vs fp_to_float_float_to_fp =
      let
         val float_to_fp = get_float_to_fp fp_to_float_float_to_fp
         val (ty1, ty2) = Type.dom_rng (Term.type_of float_to_fp)
         val ty2 = wordsSyntax.dest_word_type ty2
         fun f1 v = boolSyntax.mk_icomb (float_to_fp, Term.mk_var (v, ty1))
         fun f2 v = wordsSyntax.mk_n2w (Term.mk_var (v, numSyntax.num), ty2)
         val l = all_combs (List.map f1 vs) (List.map f2 vs)
      in
         fn op_def =>
            let
              fun f l =
                op_def
                |> try_f (Thm.SPEC ``mode:rounding``)
                |> (case l of [v] => Lib.C Thm.AP_THM v | _ => Drule.ISPECL l)
                |> REWRITE_RULE [fp_to_float_float_to_fp, combinTheory.o_THM]
                |> Drule.GEN_ALL
            in
              Theory.save_thm (opname op_def, LIST_CONJ (List.map f l))
            end
      end
   val monop = xop ["a"]
   val binop = xop ["a", "b"]
   val triop = xop ["a", "b", "c"]
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
(* e.g. val fp = "fp16" and t = 10 and w = 5 and a = SOME "half" *)
        val pre_k = t + w
        val k = pre_k + 1
        val t_ty = fcpSyntax.mk_int_numeric_type t
        val w_ty = fcpSyntax.mk_int_numeric_type w
        val fp_ty = mk_w (fcpSyntax.mk_int_numeric_type k)
        val float_ty = Type.mk_type ("float", [t_ty, w_ty])
        val float_value = Term.mk_const ("float_value", float_ty --> value_ty)
        val real_to_float =
          Term.mk_const ("real_to_float", rounding_ty --> real_ty --> float_ty)
        val real_to_float_with_flags =
          Term.mk_const ("real_to_float_with_flags",
                         rounding_ty --> real_ty --> flags_ty ** float_ty)
        val (fp_to_float, fp_to_float_def) =
          mk_fp_to_float fp fp_ty float_ty pre_k t t_ty w_ty
        val (float_to_fp, float_to_fp_def) =
          mk_float_to_fp fp fp_ty float_ty t_ty w_ty
        val (fp_to_real, fp_to_real_def) =
          mk_fp_to_real fp float_value fp_to_float fp_ty
        val (real_to_fp, real_to_fp_def) =
          mk_real_to_fp fp real_to_float float_to_fp fp_ty
        val (real_to_fp_with_flags, real_to_fp_with_flags_def) =
          mk_real_to_fp_with_flags fp real_to_float_with_flags float_to_fp fp_ty
        val int_to_fp_def = mk_int_to_fp fp real_to_fp fp_ty
        val lift1 = lift1 float_to_fp fp_to_float fp_ty float_ty
        val lift1b = lift1b fp_to_float fp_ty float_ty
        val lift1c = lift1c float_to_fp fp_ty float_ty
        val lift2 = lift2 float_to_fp fp_to_float fp_ty float_ty
        val lift2c = lift2b fp_to_float fp_ty float_ty float_compare_ty
        val lift2b = lift2b fp_to_float fp_ty float_ty Type.bool
        val lift3 = lift3 float_to_fp fp_to_float fp_ty float_ty
        val fp_roundToIntegral_def =
          lift1 false false (fp ^ "_roundToIntegral", "float_round_to_integral")
        val fp_to_int_def = mk_fp_to_int fp fp_to_float fp_ty float_ty
        val fp_sqrt_def = lift1 false true (fp ^ "_sqrt", "float_sqrt")
        val fp_sqrt_with_flags_def =
          lift1 true true (fp ^ "_sqrt_with_flags", "float_sqrt")
        val fp_negate_def = lift1 false false (fp ^ "_negate", "float_negate")
        val fp_abs_def = lift1 false false (fp ^ "_abs", "float_abs")
        val fp_isnan_def = lift1b (fp ^ "_isNan", "float_is_nan")
        val fp_issignallingnan_def =
          lift1b (fp ^ "_isSignallingNan", "float_is_signalling")
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
        val fp_add_def = lift2 false (fp ^ "_add", "float_add")
        val fp_sub_def = lift2 false (fp ^ "_sub", "float_sub")
        val fp_mul_def = lift2 false (fp ^ "_mul", "float_mul")
        val fp_div_def = lift2 false (fp ^ "_div", "float_div")
        val fp_add_with_flags_def =
          lift2 true (fp ^ "_add_with_flags", "float_add")
        val fp_sub_with_flags_def =
          lift2 true (fp ^ "_sub_with_flags", "float_sub")
        val fp_mul_with_flags_def =
          lift2 true (fp ^ "_mul_with_flags", "float_mul")
        val fp_div_with_flags_def =
          lift2 true (fp ^ "_div_with_flags", "float_div")
        val fp_compare_def = lift2c (fp ^ "_compare", "float_compare")
        val fp_equal_def = lift2b (fp ^ "_equal", "float_equal")
        val fp_lessthan_def = lift2b (fp ^ "_lessThan", "float_less_than")
        val fp_lessequal_def = lift2b (fp ^ "_lessEqual", "float_less_equal")
        val fp_greaterthan_def =
           lift2b (fp ^ "_greaterThan", "float_greater_than")
        val fp_greaterequal_def =
           lift2b (fp ^ "_greaterEqual", "float_greater_equal")
        val fp_mul_add_def = lift3 false (fp ^ "_mul_add", "float_mul_add")
        val fp_mul_sub_def = lift3 false (fp ^ "_mul_sub", "float_mul_sub")
        val fp_mul_add_with_flags_def =
          lift3 true (fp ^ "_mul_add_with_flags", "float_mul_add")
        val fp_mul_sub_with_flags_def =
          lift3 true (fp ^ "_mul_sub_with_flags", "float_mul_sub")
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
      ; [monop fp_sqrt_def] @
        List.map binop
          [fp_add_def, fp_sub_def, fp_mul_def, fp_div_def, fp_compare_def,
           fp_equal_def, fp_lessthan_def, fp_lessequal_def,
           fp_greaterthan_def, fp_greaterequal_def] @
        [fp_to_float_float_to_fp, fp_to_float_n2w, real_to_fp_def,
         real_to_fp_with_flags_def, int_to_fp_def, fp_posinf_def, fp_neginf_def,
         fp_poszero_def, fp_negzero_def, fp_minpos_def, fp_minneg_def,
         fp_top_def, fp_bottom_def, float_to_fp_fp_to_float,
         fp_to_float_float_to_fp] @
        List.map monop
          [fp_to_real_def, fp_to_int_def, fp_abs_def, fp_negate_def,
           fp_isnan_def, fp_issignallingnan_def,
           fp_isintegral_def, fp_iszero_def, fp_isnormal_def,
           fp_issubnormal_def, fp_isfinite_def, fp_isinfinite_def,
           fp_roundToIntegral_def, fp_sqrt_with_flags_def] @
        List.map binop
          [fp_add_with_flags_def, fp_sub_with_flags_def, fp_mul_with_flags_def,
           fp_div_with_flags_def] @
        List.map triop
          [fp_mul_add_def, fp_mul_sub_def, fp_mul_add_with_flags_def,
           fp_mul_sub_with_flags_def]
     end
end

end
