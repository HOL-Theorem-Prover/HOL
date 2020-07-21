(* Copyright (c) 2010-2011 Tjark Weber. All rights reserved. *)

(* SMT-LIB 2 logics *)

structure SmtLib_Logics =
struct

local

  val ERR = Feedback.mk_HOL_ERR "SmtLib_Logics"

  fun union_dicts (x::xs) =
    List.foldl (Lib.uncurry Library.union_dict o Lib.swap) x xs
    | union_dicts [] =
    raise ERR "union_dicts" "empty list"

  (* because int-to-real conversions may be combined with :chainable
     and :{left,right}-assoc functions, 'one_int_to_real' converts *at
     most* (rather than exactly) one integer argument to real *)
  fun one_int_to_real (t1, t2) =
      (intrealSyntax.mk_real_of_int t1, t2)
    handle Feedback.HOL_ERR _ =>
      (t1, intrealSyntax.mk_real_of_int t2)
    handle Feedback.HOL_ERR _ =>
      (t1, t2)

  (* converts *at most* (rather than exactly) two integer arguments to
     reals (cf. 'one_int_to_real' *)
  fun two_ints_to_real (t1, t2) =
      (intrealSyntax.mk_real_of_int t1, intrealSyntax.mk_real_of_int t2)
    handle Feedback.HOL_ERR _ =>
      one_int_to_real (t1, t2)

  open SmtLib_Theories

  val BV_extension_tmdict = Library.dict_from_list [
    (* bit-vector constants *)
    ("_", one_zero (fn token =>
      if String.isPrefix "bv" token then
        let
          val decimal = String.extract (token, 2, NONE)
          val value = Arbnum.fromString decimal
        in
          Lib.curry wordsSyntax.mk_word value
        end
     else
        raise ERR "<BV_extension_dict._>" "not a bit-vector constant")),
    ("bvnand", K_zero_two wordsSyntax.mk_word_nand),
    ("bvnor", K_zero_two wordsSyntax.mk_word_nor),
    ("bvxor", K_zero_two wordsSyntax.mk_word_xor),
    ("bvxnor", K_zero_two wordsSyntax.mk_word_xnor),
    ("bvcomp", K_zero_two wordsSyntax.mk_word_compare),
    ("bvsub", K_zero_two wordsSyntax.mk_word_sub),
    ("bvsdiv", K_zero_two wordsSyntax.mk_word_quot),
    ("bvsrem", K_zero_two wordsSyntax.mk_word_rem),
    ("bvsmod", K_zero_two integer_wordSyntax.mk_word_smod),
    ("bvashr", K_zero_two wordsSyntax.mk_word_asr_bv),
    ("repeat", K_one_one
      (Lib.curry wordsSyntax.mk_word_replicate o numSyntax.mk_numeral)),
    ("zero_extend", K_one_one (fn n => fn t => wordsSyntax.mk_w2w (t,
      fcpLib.index_type
        (Arbnum.+ (fcpLib.index_to_num (wordsSyntax.dim_of t), n))))),
    ("sign_extend", K_one_one (fn n => fn t => wordsSyntax.mk_sw2sw (t,
      fcpLib.index_type
        (Arbnum.+ (fcpLib.index_to_num (wordsSyntax.dim_of t), n))))),
    ("rotate_left", K_one_one
      (Lib.C (Lib.curry wordsSyntax.mk_word_rol) o numSyntax.mk_numeral)),
    ("rotate_right", K_one_one
      (Lib.C (Lib.curry wordsSyntax.mk_word_ror) o numSyntax.mk_numeral)),
    ("bvule", K_zero_two wordsSyntax.mk_word_ls),
    ("bvugt", K_zero_two wordsSyntax.mk_word_hi),
    ("bvuge", K_zero_two wordsSyntax.mk_word_hs),
    ("bvslt", K_zero_two wordsSyntax.mk_word_lt),
    ("bvsle", K_zero_two wordsSyntax.mk_word_le),
    ("bvsgt", K_zero_two wordsSyntax.mk_word_gt),
    ("bvsge", K_zero_two wordsSyntax.mk_word_ge)
  ]

in

  (* In general, parsing is too liberal -- for instance, we do not
     check that the input satisfies the linearity constraints that are
     defined by various logics. Our aim is not to validate the SMT-LIB
     input, but merely to produce meaningful results for valid
     inputs. *)

  structure AUFLIA =
  struct
    val tydict = union_dicts [Core.tydict, Ints.tydict, ArraysEx.tydict]
    val tmdict = union_dicts [Core.tmdict, Ints.tmdict, ArraysEx.tmdict]
  end

  structure AUFLIRA =
  struct
    val tydict = union_dicts [Core.tydict, Reals_Ints.tydict, ArraysEx.tydict]
    val tmdict = union_dicts [Core.tmdict, Reals_Ints.tmdict, ArraysEx.tmdict,
      (* "For every operator op with declaration (op Real Real s) for
         some sort s, and every term t1, t2 of sort Int and t of sort
         Real, the expression

         - (op t1 t) is syntactic sugar for (op (to_real t1) t)
         - (op t t1) is syntactic sugar for (op t (to_real t1))
         - (/ t1 t2) is syntactic sugar for (/ (to_real t1) (to_real t2))"

         We only implement this for the operators in
         {Core,Reals_Ints,ArraysEx}.tmdict. Implementing it in
         general, also for user-defined operators, would require a
         change to our parser architecture.

         A discussion on the SMT-LIB mailing list in October 2010
         (http://www.cs.nyu.edu/pipermail/smt-lib/2010/000403.html)
         was in favor of removing implicit conversions from the
         SMT-LIB language altogether, but this is not reflected in the
         SMT-LIB standard yet. *)

      Library.dict_from_list [
        ("=", chainable (boolSyntax.mk_eq o one_int_to_real)),
        ("-", leftassoc (realSyntax.mk_minus o one_int_to_real)),
        ("+", leftassoc (realSyntax.mk_plus o one_int_to_real)),
        ("*", leftassoc (realSyntax.mk_mult o one_int_to_real)),
        ("/", leftassoc (realSyntax.mk_div o two_ints_to_real)),
        ("<=", chainable (realSyntax.mk_leq o one_int_to_real)),
        ("<", chainable (realSyntax.mk_less o one_int_to_real)),
        (">=", chainable (realSyntax.mk_geq o one_int_to_real)),
        (">", chainable (realSyntax.mk_greater o one_int_to_real))
      ]]
  end

  structure AUFNIRA =
  struct
    val tydict = AUFLIRA.tydict
    val tmdict = AUFLIRA.tmdict
  end

  structure LRA =
  struct
    val tydict = union_dicts [Core.tydict, Reals.tydict]
    val tmdict = union_dicts [Core.tmdict, Reals.tmdict]
  end

  structure QF_ABV =
  struct
    val tydict = union_dicts [Core.tydict, Fixed_Size_BitVectors.tydict,
      ArraysEx.tydict]
    val tmdict = union_dicts [Core.tmdict, Fixed_Size_BitVectors.tmdict,
      ArraysEx.tmdict, BV_extension_tmdict]
  end

  structure QF_AUFBV =
  struct
    val tydict = QF_ABV.tydict
    val tmdict = QF_ABV.tmdict
  end

  structure QF_AUFLIA =
  struct
    val tydict = AUFLIA.tydict
    val tmdict = AUFLIA.tmdict
  end

  structure QF_AX =
  struct
    val tydict = union_dicts [Core.tydict, ArraysEx.tydict]
    val tmdict = union_dicts [Core.tmdict, ArraysEx.tmdict]
  end

  structure QF_BV =
  struct
    val tydict = union_dicts [Core.tydict, Fixed_Size_BitVectors.tydict]
    val tmdict = union_dicts [Core.tmdict, Fixed_Size_BitVectors.tmdict,
      BV_extension_tmdict]
  end

  structure QF_IDL =
  struct
    val tydict = union_dicts [Core.tydict, Ints.tydict]
    val tmdict = union_dicts [Core.tmdict, Ints.tmdict]
  end

  structure QF_LIA =
  struct
    val tydict = QF_IDL.tydict
    val tmdict = QF_IDL.tmdict
  end

  structure QF_LRA =
  struct
    val tydict = LRA.tydict
    val tmdict = LRA.tmdict
  end

  structure QF_NIA =
  struct
    val tydict = QF_IDL.tydict
    val tmdict = QF_IDL.tmdict
  end

  structure QF_NRA =
  struct
    val tydict = LRA.tydict
    val tmdict = LRA.tmdict
  end

  structure QF_RDL =
  struct
    val tydict = LRA.tydict
    val tmdict = LRA.tmdict
  end

  structure QF_UF =
  struct
    val tydict = Core.tydict
    val tmdict = Core.tmdict
  end

  structure QF_UFBV =
  struct
    val tydict = QF_BV.tydict
    val tmdict = QF_BV.tmdict
  end

  structure QF_UFIDL =
  struct
    val tydict = QF_IDL.tydict
    val tmdict = QF_IDL.tmdict
  end

  structure QF_UFLIA =
  struct
    val tydict = QF_IDL.tydict
    val tmdict = QF_IDL.tmdict
  end

  structure QF_UFLRA =
  struct
    val tydict = LRA.tydict
    val tmdict = LRA.tmdict
  end

  structure QF_UFNRA =
  struct
    val tydict = LRA.tydict
    val tmdict = LRA.tmdict
  end

  structure UFLRA =
  struct
    val tydict = LRA.tydict
    val tmdict = LRA.tmdict
  end

  structure UFNIA =
  struct
    val tydict = QF_IDL.tydict
    val tmdict = QF_IDL.tmdict
  end

  (* returns a type dictionary and a term dictionary that can be used
     to parse types/terms of the given SMT-LIB 2 logic *)
  fun parsedicts_of_logic (logic : string) =
    case logic of
      "AUFLIA" =>
      (AUFLIA.tydict, AUFLIA.tmdict)
    | "AUFLIRA" =>
      (AUFLIRA.tydict, AUFLIRA.tmdict)
    | "AUFNIRA" =>
      (AUFNIRA.tydict, AUFNIRA.tmdict)
    | "LRA" =>
      (LRA.tydict, LRA.tmdict)
    | "QF_ABV" =>
      (QF_ABV.tydict, QF_ABV.tmdict)
    | "QF_AUFBV" =>
      (QF_AUFBV.tydict, QF_AUFBV.tmdict)
    | "QF_AUFLIA" =>
      (QF_AUFLIA.tydict, QF_AUFLIA.tmdict)
    | "QF_AX" =>
      (QF_AX.tydict, QF_AX.tmdict)
    | "QF_BV" =>
      (QF_BV.tydict, QF_BV.tmdict)
    | "QF_IDL" =>
      (QF_IDL.tydict, QF_IDL.tmdict)
    | "QF_LIA" =>
      (QF_LIA.tydict, QF_LIA.tmdict)
    | "QF_LRA" =>
      (QF_LRA.tydict, QF_LRA.tmdict)
    | "QF_NIA" =>
      (QF_NIA.tydict, QF_NIA.tmdict)
    | "QF_NRA" =>
      (QF_NRA.tydict, QF_NRA.tmdict)
    | "QF_RDL" =>
      (QF_RDL.tydict, QF_RDL.tmdict)
    | "QF_UF" =>
      (QF_UF.tydict, QF_UF.tmdict)
    | "QF_UFBV" =>
      (QF_UFBV.tydict, QF_UFBV.tmdict)
    | "QF_UFIDL" =>
      (QF_UFIDL.tydict, QF_UFIDL.tmdict)
    | "QF_UFLIA" =>
      (QF_UFLIA.tydict, QF_UFLIA.tmdict)
    | "QF_UFLRA" =>
      (QF_UFLRA.tydict, QF_UFLRA.tmdict)
    | "QF_UFNRA" =>
      (QF_UFNRA.tydict, QF_UFNRA.tmdict)
    | "UFLRA" =>
      (UFLRA.tydict, UFLRA.tmdict)
    | "UFNIA" =>
      (UFNIA.tydict, UFNIA.tmdict)
    | _ =>
      raise ERR "parsedicts_of_logic" ("unknown logic '" ^ logic ^ "'")

end  (* local *)

end
