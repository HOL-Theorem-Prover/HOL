(* Copyright (c) 2009-2011 Tjark Weber. All rights reserved. *)

(* Translation of HOL terms into SMT-LIB 2 format *)

structure SmtLib = struct

local

  (* FIXME: We translate into a fictitious SMT-LIB logic AUFBVNIRA
     that comprises arrays (A), uninterpreted functions (UF),
     bit-vectors (BV), non-linear (N) integer (I) and real arithmetic
     (RA).  Unfortunately, there is no actual SMT-LIB logic at the
     moment that contains all these features: AUFNIRA is missing
     bit-vectors, while QF_AUFBV is missing quantifiers and
     arithmetic.  See SmtLib_{Theories,Logics}.sml for details.  At
     present, we make no attempt to identify a less expressive SMT-LIB
     logic based on the constants that actually appear in the goal. *)

  (* For successful proof reconstruction, it is important that the
     translation implemented in SmtLib_{Theories,Logics}.sml is an
     inverse of the translation implemented in this file. *)

  val ERR = Feedback.mk_HOL_ERR "SmtLib"
  val WARNING = Feedback.HOL_WARNING "SmtLib"

  (* (HOL type, a function that maps the type to its SMT-LIB sort name) *)
  val builtin_types = List.foldl
    (fn ((ty, x), net) => TypeNet.insert (net, ty, x)) TypeNet.empty [
    (Type.bool, Lib.K "Bool"),
    (intSyntax.int_ty, Lib.K "Int"),
    (realSyntax.real_ty, Lib.K "Real"),
    (* bit-vector types *)
    (wordsSyntax.mk_word_type Type.alpha, fn ty =>
      "(_ BitVec " ^ Arbnum.toString
        (fcpSyntax.dest_numeric_type (wordsSyntax.dest_word_type ty)) ^ ")")
   ]

  val apfst_K = Lib.apfst o Lib.K

  (* returns true iff 'ty' is a word type that is not fixed-width *)
  fun is_non_numeric_word_type ty =
    not (fcpSyntax.is_numeric_type (wordsSyntax.dest_word_type ty))
      handle Feedback.HOL_ERR _ => false

  (* make sure that all word types in 't' are of fixed width; return 's' *)
  fun apfst_fixed_width s =
    Lib.apfst (fn t =>
      let
        val (domtys, rngty) = boolSyntax.strip_fun (Term.type_of t)
      in
        if List.exists is_non_numeric_word_type (rngty :: domtys) then
          raise ERR ("<builtin_symbols." ^ s ^ ">")
            "not a fixed-width word type"
        else
          s
      end)

  (* (HOL term, a function that maps a pair (rator, rands) to an
     SMT-LIB symbol and a list of remaining (still-to-be-encoded)
     argument terms) *)
  val builtin_symbols = List.foldl (Lib.uncurry Net.insert) Net.empty [
    (* Core *)
    (boolSyntax.T, apfst_K "true"),
    (boolSyntax.F, apfst_K "false"),
    (boolSyntax.negation, apfst_K "not"),
    (boolSyntax.implication, apfst_K "=>"),
    (boolSyntax.conjunction, apfst_K "and"),
    (boolSyntax.disjunction, apfst_K "or"),
    (* (..., "xor"), *)
    (boolSyntax.equality, apfst_K "="),
    (* (..., "distinct"), *)
    (boolSyntax.conditional, apfst_K "ite"),
    (* Reals_Ints *)
    (* numerals (excluding 'intSyntax.negate_tm') *)
    (Term.mk_var ("x", intSyntax.int_ty), Lib.apfst (fn tm =>
      if intSyntax.is_int_literal tm andalso not (intSyntax.is_negated tm) then
        let
          val i = intSyntax.int_of_term tm
          val s = Arbint.toString (Arbint.abs i)
          val s = String.substring (s, 0, String.size s - 1)
        in
          if Arbint.< (i, Arbint.zero) then
            "(- " ^ s ^ ")"
          else
            s
        end
      else
        raise ERR "<builtin_symbols.x:int>" "not a numeral (negated?)")),
    (intSyntax.negate_tm, apfst_K "-"),
    (intSyntax.minus_tm, apfst_K "-"),
    (intSyntax.plus_tm, apfst_K "+"),
    (intSyntax.mult_tm, apfst_K "*"),
    (* (..., "div"), *)
    (* (..., "mod"), *)
    (intSyntax.absval_tm, apfst_K "abs"),
    (intSyntax.leq_tm, apfst_K "<="),
    (intSyntax.less_tm, apfst_K "<"),
    (intSyntax.geq_tm, apfst_K ">="),
    (intSyntax.great_tm, apfst_K ">"),
    (* decimals (excluding 'realSyntax.negate_tm') *)
    (Term.mk_var ("x", realSyntax.real_ty), Lib.apfst (fn tm =>
      if realSyntax.is_real_literal tm andalso not (realSyntax.is_negated tm)
          then
        let
          val i = realSyntax.int_of_term tm
          val s = Arbint.toString (Arbint.abs i)
          val s = String.substring (s, 0, String.size s - 1)
          val s = s ^ ".0"
        in
          if Arbint.< (i, Arbint.zero) then
            "(- " ^ s ^ ")"
          else
            s
        end
      else
        raise ERR "<builtin_symbols.x:real>" "not a decimal (negated?)")),
    (realSyntax.negate_tm, apfst_K "-"),
    (realSyntax.minus_tm, apfst_K "-"),
    (realSyntax.plus_tm, apfst_K "+"),
    (realSyntax.mult_tm, apfst_K "*"),
    (realSyntax.div_tm, apfst_K "/"),
    (realSyntax.leq_tm, apfst_K "<="),
    (realSyntax.less_tm, apfst_K "<"),
    (realSyntax.geq_tm, apfst_K ">="),
    (realSyntax.great_tm, apfst_K ">"),
    (intrealSyntax.real_of_int_tm, apfst_K "to_real"),
    (intrealSyntax.INT_FLOOR_tm, apfst_K "to_int"),
    (intrealSyntax.is_int_tm, apfst_K "is_int"),
    (* bit-vector constants *)
    (Term.mk_var ("x", wordsSyntax.mk_word_type Type.alpha), Lib.apfst (fn tm =>
      if wordsSyntax.is_word_literal tm then
        let
          val value = wordsSyntax.dest_word_literal tm
          val width = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of tm)
        in
          "(_ bv" ^ Arbnum.toString value ^ " " ^ Arbnum.toString width ^ ")"
        end
      else
        raise ERR "<builtin_symbols.x:'a word>" "not a word literal")),
    (wordsSyntax.word_concat_tm, fn (t, ts) =>
      SmtLib_Theories.two_args (fn (w1, w2) =>
        let
          (* make sure that the result in HOL has the expected width *)
          val dim1 = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w1)
          val dim2 = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w2)
          val rngty = Lib.snd (boolSyntax.strip_fun (Term.type_of t))
          val rngdim = fcpSyntax.dest_numeric_type
            (wordsSyntax.dest_word_type rngty)
          val _ = if rngdim = Arbnum.+ (dim1, dim2) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "word_concat: wrong result type"
              else
                ();
              raise ERR "<builtin_symbols.word_concat_tm>" "wrong result type"
            )
        in
          ("concat", ts)
        end) ts),
    (wordsSyntax.word_extract_tm, fn (t, ts) =>
      SmtLib_Theories.three_args (fn (i, j, w) =>
        let
          (* make sure that j <= i < dim(w) *)
          val i = numSyntax.dest_numeral i
          val j = numSyntax.dest_numeral j
          val dim = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w)
          val _ = if Arbnum.<= (j, i) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term"
                  "word_extract: second index larger than first"
              else
                ();
              raise ERR "<builtin_symbols.word_extract_tm>"
                "second index larger than first"
            )
          val _ = if Arbnum.< (i, dim) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "word_extract: first index too large"
              else
                ();
              raise ERR "<builtin_symbols.word_extract_tm>"
                "first index too large"
            )
          (* make sure that the result in HOL has the expected width *)
          val rngty = Lib.snd (boolSyntax.strip_fun (Term.type_of t))
          val rngdim = fcpSyntax.dest_numeric_type
            (wordsSyntax.dest_word_type rngty)
          val _ = if rngdim = Arbnum.+ (Arbnum.- (i, j), Arbnum.one) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "word_extract: wrong result type"
              else
                ();
              raise ERR "<builtin_symbols.word_extract_tm>" "wrong result type"
            )
        in
          ("(_ extract " ^ Arbnum.toString i ^ " " ^ Arbnum.toString j ^ ")",
            [w])
        end) ts),
    (wordsSyntax.word_1comp_tm, apfst_fixed_width "bvnot"),
    (wordsSyntax.word_and_tm, apfst_fixed_width "bvand"),
    (wordsSyntax.word_or_tm, apfst_fixed_width "bvor"),
    (wordsSyntax.word_nand_tm, apfst_fixed_width "bvnand"),
    (wordsSyntax.word_nor_tm, apfst_fixed_width "bvnor"),
    (wordsSyntax.word_xor_tm, apfst_fixed_width "bvxor"),
    (wordsSyntax.word_xnor_tm, apfst_fixed_width "bvxnor"),
    (wordsSyntax.word_2comp_tm, apfst_fixed_width "bvneg"),
    (wordsSyntax.word_compare_tm, apfst_fixed_width "bvcomp"),
    (wordsSyntax.word_add_tm, apfst_fixed_width "bvadd"),
    (wordsSyntax.word_sub_tm, apfst_fixed_width "bvsub"),
    (wordsSyntax.word_mul_tm, apfst_fixed_width "bvmul"),
    (wordsSyntax.word_sdiv_tm, apfst_fixed_width "bvsdiv"),
    (wordsSyntax.word_srem_tm, apfst_fixed_width "bvsrem"),
    (wordsSyntax.word_smod_tm, apfst_fixed_width "bvsmod"),
    (wordsSyntax.word_div_tm, apfst_fixed_width "bvudiv"),
    (wordsSyntax.word_mod_tm, apfst_fixed_width "bvurem"),
    (* shift operations with two bit-vector arguments; the corresponding HOL
       shift operations that take a numeral as their second argument are not
       supported in SMT-LIB *)
    (wordsSyntax.word_lsl_bv_tm, apfst_fixed_width "bvshl"),
    (wordsSyntax.word_lsr_bv_tm, apfst_fixed_width "bvlshr"),
    (wordsSyntax.word_asr_bv_tm, apfst_fixed_width "bvashr"),
    (wordsSyntax.word_replicate_tm, fn (t, ts) =>
      SmtLib_Theories.two_args (fn (n, w) =>
        let
          val n = numSyntax.dest_numeral n
          (* make sure that the result in HOL has the expected width *)
          val dim = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w)
          val rngty = Lib.snd (boolSyntax.strip_fun (Term.type_of t))
          val rngdim = fcpSyntax.dest_numeric_type
            (wordsSyntax.dest_word_type rngty)
          val _ = if rngdim = Arbnum.* (n, dim) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "word_replicate: wrong result type"
              else
                ();
              raise ERR "<builtin_symbols.word_replicate_tm>"
                "wrong result type"
            )
        in
          ("(_ repeat " ^ Arbnum.toString n ^ ")", [w])
        end) ts),
    (wordsSyntax.w2w_tm, fn (t, ts) =>
      SmtLib_Theories.one_arg (fn w =>
        let
          (* make sure that the result in HOL is at least as long as 'w' *)
          val dim = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w)
          val rngty = Lib.snd (boolSyntax.strip_fun (Term.type_of t))
          val rngdim = fcpSyntax.dest_numeric_type
            (wordsSyntax.dest_word_type rngty)
          val _ = if Arbnum.>= (rngdim, dim) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "w2w: result type too short"
              else
                ();
              raise ERR "<builtin_symbols.w2w_tm>" "result type too short"
            )
          val n = Arbnum.- (rngdim, dim)
        in
          ("(_ zero_extend " ^ Arbnum.toString n ^ ")", [w])
        end) ts),
    (wordsSyntax.sw2sw_tm, fn (t, ts) =>
      SmtLib_Theories.one_arg (fn w =>
        let
          (* make sure that the result in HOL is at least as long as 'w' *)
          val dim = fcpSyntax.dest_numeric_type (wordsSyntax.dim_of w)
          val rngty = Lib.snd (boolSyntax.strip_fun (Term.type_of t))
          val rngdim = fcpSyntax.dest_numeric_type
            (wordsSyntax.dest_word_type rngty)
          val _ = if Arbnum.>= (rngdim, dim) then
              ()
            else (
              if !Library.trace > 0 then
                WARNING "translate_term" "sw2sw: result type too short"
              else
                ();
              raise ERR "<builtin_symbols.sw2sw_tm>" "result type too short"
            )
          val n = Arbnum.- (rngdim, dim)
        in
          ("(_ sign_extend " ^ Arbnum.toString n ^ ")", [w])
        end) ts),
    (* rotation by a numeral; the corresponding HOL rotation operations that
       take two bit-vector arguments are not supported in SMT-LIB *)
    (wordsSyntax.word_rol_tm, fn (t, ts) =>
      (
        apfst_fixed_width "rotate_left" (t, ());
        SmtLib_Theories.two_args (fn (w, n) =>
          ("(_ rotate_left " ^ Arbnum.toString (numSyntax.dest_numeral n)
            ^ ")", [w])) ts
      )),
    (wordsSyntax.word_ror_tm, fn (t, ts) =>
      (
        apfst_fixed_width "rotate_right" (t, ());
        SmtLib_Theories.two_args (fn (w, n) =>
          ("(_ rotate_right " ^ Arbnum.toString (numSyntax.dest_numeral n)
            ^ ")", [w])) ts
      )),
    (wordsSyntax.word_lo_tm, apfst_fixed_width "bvult"),
    (wordsSyntax.word_ls_tm, apfst_fixed_width "bvule"),
    (wordsSyntax.word_hi_tm, apfst_fixed_width "bvugt"),
    (wordsSyntax.word_hs_tm, apfst_fixed_width "bvuge"),
    (wordsSyntax.word_lt_tm, apfst_fixed_width "bvslt"),
    (wordsSyntax.word_le_tm, apfst_fixed_width "bvsle"),
    (wordsSyntax.word_gt_tm, apfst_fixed_width "bvsgt"),
    (wordsSyntax.word_ge_tm, apfst_fixed_width "bvsge")
  ]

  (* SMT-LIB type and function names are uniformly generated as "tN"
     and "vN", respectively, where N is a number. Prefixes must be
     distinct. *)

  val ty_prefix = "t"  (* for types *)
  val tm_prefix = "v"  (* for terms *)
  val bv_prefix = "b"  (* for bound variables *)

  (* returns an updated accumulator, a (possibly empty) list of
     SMT-LIB type declarations, and the SMT-LIB representation of the
     given type *)
  fun translate_type (tydict, ty) =
  let
    val name = Lib.tryfind (fn (_, f) => f ty)
        (TypeNet.match (builtin_types, ty)) (* may fail *)
      handle Feedback.HOL_ERR _ =>
        Redblackmap.find (tydict, ty)
  in
    (tydict, ([], name))
  end
  handle Redblackmap.NotFound =>
    (* uninterpreted types *)
    let
      val name = ty_prefix ^ Int.toString (Redblackmap.numItems tydict)
      val decl = "(declare-sort " ^ name ^ " 0)\n"
    in
      if !Library.trace > 0 andalso Type.is_type ty then
        WARNING "translate_type"
          ("uninterpreted type " ^ Hol_pp.type_to_string ty)
      else
        ();
      if !Library.trace > 2 then
        Feedback.HOL_MESG ("HolSmtLib (SmtLib): inventing name '" ^ name ^
          "' for HOL type '" ^ Hol_pp.type_to_string ty ^ "'")
      else
        ();
      (Redblackmap.insert (tydict, ty, name), ([decl], name))
    end

  (* SMT-LIB is first-order.  Thus, functions can only be applied to
     arguments of base type, but not to arguments of function type;
     all completely applied terms must be of base type.

     Thus, higher-order arguments must be abstracted so that they are
     of (uninterpreted) base type.  We achieve this by abstracting the
     offending function type to a fresh base type, and by abstracting
     the argument's rator to an uninterpreted term that returns the
     correct (abstracted) type.  Note that the same function/operator
     may appear both with and without arguments in a HOL formula.
     'tmdict' maps terms along with the number of their actual
     arguments to an SMT-LIB representation. *)

  (* returns an updated accumulator, a (possibly empty) list of
     SMT-LIB (type and term) declarations, and the SMT-LIB
     representation of the given term *)
  fun translate_term (acc as (tydict, tmdict), (bounds, tm)) =
  let
    fun sexpr x [] = x
      | sexpr x xs = "(" ^ x ^ " " ^ String.concatWith " " xs ^ ")"
    fun builtin_symbol (rator, rands) =
      let
        val (name, rands) = Lib.tryfind (fn parsefn => parsefn (rator, rands))
          (Net.match rator builtin_symbols)  (* may fail *)
        val (acc, declnames) = Lib.foldl_map
          (fn (a, t) => translate_term (a, (bounds, t))) (acc, rands)
        val (declss, names) = Lib.split declnames
      in
        (acc, (List.concat declss, sexpr name names))
      end
    (* creates a mapping from bound variables to their SMT-LIB names; if a
       variable is already mapped, we return its existing SMT-LIB name *)
    fun create_bound_name (bounds, v) =
      (bounds, Redblackmap.find (bounds, v))
      handle Redblackmap.NotFound =>
        let
          val name = bv_prefix ^ Int.toString (Redblackmap.numItems bounds)
        in
          (Redblackmap.insert (bounds, v, name), name)
        end
    val tm_has_base_type = not (Lib.can Type.dom_rng (Term.type_of tm))
  in
    (* binders *)
    let
      (* perhaps we should use a table of binders instead *)
      val (binder, (vars, body)) = if boolSyntax.is_forall tm then
          ("forall", boolSyntax.strip_forall tm)
        else if boolSyntax.is_exists tm then
          ("exists", boolSyntax.strip_exists tm)
        else
          raise ERR "translate_term" "not a binder"  (* handled below *)
      val (bounds, smtvars) = Lib.foldl_map create_bound_name (bounds, vars)
      val (tydict, vardecltys) = Lib.foldl_map translate_type
        (tydict, List.map Term.type_of vars)
      val (vardeclss, vartys) = Lib.split vardecltys
      val vardecls = List.concat vardeclss
      val smtvars = ListPair.mapEq (fn (v, ty) => "(" ^ v ^ " " ^ ty ^ ")")
        (smtvars, vartys)
      val (acc, (bodydecls, body)) = translate_term
        ((tydict, tmdict), (bounds, body))
    in
      (acc, (vardecls @ bodydecls, "(" ^ binder ^ " (" ^
        String.concatWith " " smtvars ^ ") " ^ body ^ ")"))
    end
    handle Feedback.HOL_ERR _ =>

    (* let binder - somewhat similar to quantifiers, but we only
       translate one let at a time (so we don't have to worry about
       semantic differences caused by parallel vs. sequential let) *)
    let
      val (M, N) = boolSyntax.dest_let tm
      val (var, body) = Term.dest_abs M
      val (acc, (Ndecls, N)) = translate_term (acc, (bounds, N))
      val (bounds, name) = create_bound_name (bounds, var)
      val (acc, (bodydecls, body)) = translate_term (acc, (bounds, body))
    in
      (acc, (Ndecls @ bodydecls,
        "(let ((" ^ name ^ " " ^ N ^ ")) " ^ body ^ ")"))
    end
    handle Feedback.HOL_ERR _ =>

    (* bound variables may shadow built-in symbols etc. *)
    (acc, ([], Redblackmap.find (bounds, tm)))
    handle Redblackmap.NotFound =>

    (* translate the entire term (e.g., for numerals), using the dictionary of
       built-in symbols; however, only do this if 'tm' has base type *)
    (if tm_has_base_type then
      builtin_symbol (tm, [])
    else
      raise ERR "translate_term" "not first-order")  (* handled below *)
    handle Feedback.HOL_ERR _ =>

    (* split the term into rator and rands *)
    let
      val (rator, rands) = boolSyntax.strip_comb tm
    in
      (* translate the rator as a built-in symbol (applied to its rands); only
         do this if 'tm' has base type *)
      (if tm_has_base_type then
        builtin_symbol (rator, rands)
      else
        raise ERR "translate_term" "not first-order")  (* handled below *)
      handle Feedback.HOL_ERR _ =>

      let
        val rands_count = List.length rands
        val (acc, (decls, name)) =
          (* translate the rator as a previously defined symbol *)
          (acc, ([], Redblackmap.find (tmdict, (rator, rands_count))))
          handle Redblackmap.NotFound =>

          (* translate the rator as a new (i.e., uninterpreted) symbol *)
          let
            (* translate 'rator' types required for the rator's
               SMT-LIB declaration *)
            fun doms_rng acc 0 ty =
              (List.rev acc, ty)
              | doms_rng acc n ty =
              let
                val (dom, rng) = Type.dom_rng ty
              in
                doms_rng (dom :: acc) (n - 1) rng
              end
            (* strip only 'rands_count' many 'domtys', leaving the remaining
               argument types in 'rngty' *)
            val (domtys, rngty) = doms_rng [] rands_count (Term.type_of rator)
            val (tydict, domdecltys) = Lib.foldl_map translate_type
              (tydict, domtys)
            val (domdeclss, domtys) = Lib.split domdecltys
            val domdecls = List.concat domdeclss
            val (tydict, (rngdecls, rngty)) = translate_type (tydict, rngty)
            (* invent new name for 'rator' *)
            val name = tm_prefix ^ Int.toString (Redblackmap.numItems tmdict)
            val _ = if !Library.trace > 0 andalso Term.is_const rator then
              WARNING "translate_term"
                ("uninterpreted constant " ^ Hol_pp.term_to_string rator)
              else
                ();
            val _ = if !Library.trace > 2 then
                Feedback.HOL_MESG ("HolSmtLib (SmtLib): inventing name '" ^
                  name ^ "' for HOL term '" ^ Hol_pp.term_to_string rator ^
                  "' (applied to " ^ Int.toString rands_count ^ " argument(s))")
              else
                ()
            val tmdict = Redblackmap.insert (tmdict, (rator, rands_count), name)
            val decl = "(declare-fun " ^ name ^ " (" ^
              String.concatWith " " domtys ^ ") " ^ rngty ^ ")\n"
          in
            ((tydict, tmdict), (domdecls @ rngdecls @ [decl], name))
          end
        (* translate 'rands' *)
        val (acc, declnames) = Lib.foldl_map
          (fn (a, t) => translate_term (a, (bounds, t))) (acc, rands)
        val (declss, names) = Lib.split declnames
      in
        (acc, (decls @ List.concat declss, sexpr name names))
      end
    end
  end

  (* Returns a string list representing the input goal in SMT-LIB file
     format, together with two dictionaries that map types and terms
     to identifiers used in the SMT-LIB representation.  The goal's
     conclusion is negated before translation into SMT-LIB format.
     The integer in the term dictionary gives the number of actual
     arguments to the term.  (Because SMT-LIB is first-order,
     partially applied functions are mapped to different SMT-LIB
     identifiers, depending on the number of actual arguments.) *)
  fun goal_to_SmtLib_aux (ts, t)
    : ((Type.hol_type, string) Redblackmap.dict *
      (Term.term * int, string) Redblackmap.dict) * string list =
  let
    val tydict = Redblackmap.mkDict Type.compare
    val tmdict = Redblackmap.mkDict
      (Lib.pair_compare (Term.compare, Int.compare))
    val bounds = Redblackmap.mkDict Term.compare
    val (acc, smtlibs) = Lib.foldl_map
      (fn (acc, tm) => translate_term (acc, (bounds, tm)))
      ((tydict, tmdict), ts @ [boolSyntax.mk_neg t])
    (* we choose to intertwine declarations and assertions (for no
       particular reason; an alternative would be to emit all
       declarations before all assertions) *)
    val smtlibs = List.foldl
      (fn ((xs, s), acc) => acc @ xs @ ["(assert " ^ s ^ ")\n"]) [] smtlibs
  in
    (acc, [
      "(set-logic AUFBVNIRA)\n",
      "(set-info :source |Automatically generated from HOL4 by SmtLib.goal_to_SmtLib.\n",
      "Copyright (c) 2011 Tjark Weber. All rights reserved.|)\n",
      "(set-info :smt-lib-version 2.0)\n"
    ] @ smtlibs @ [
      "(check-sat)\n"
    ])
  end

in

  val goal_to_SmtLib =
    Lib.apsnd (fn xs => xs @ ["(exit)\n"]) o goal_to_SmtLib_aux

  val goal_to_SmtLib_with_get_proof =
    Lib.apsnd (fn xs => xs @ ["(get-proof)\n", "(exit)\n"]) o goal_to_SmtLib_aux

  (* eliminates some HOL terms that are not supported by the SMT-LIB
     translation *)
  fun SIMP_TAC simp_let =
    let
      open Tactical simpLib
      val INT_ABS = intLib.ARITH_PROVE
                      ``!x. ABS (x:int) = if x < 0i then 0i - x else x``
    in
      REPEAT Tactic.GEN_TAC THEN
      (if simp_let then Library.LET_SIMP_TAC else ALL_TAC) THEN
      SIMP_TAC pureSimps.pure_ss
        [integerTheory.INT_MIN, integerTheory.INT_MAX, INT_ABS] THEN
      Library.WORD_SIMP_TAC THEN
      Library.SET_SIMP_TAC THEN
      Tactic.BETA_TAC
    end

end  (* local *)

end
