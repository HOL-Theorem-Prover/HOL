(* Copyright (c) 2009-2012 Tjark Weber. All rights reserved. *)

(* Functions to invoke the Yices SMT solver *)

structure Yices = struct

  (* FIXME: Yices 1.0.29 only supports linear arithmetic, bit-vector shifts by
            a numeric constant, etc.  We do not check these side conditions on
            arguments at the moment, therefore possibly producing invalid Yices
            input. *)

  (* translation of HOL terms into Yices' input syntax -- currently, all types
     and terms except the following are treated as uninterpreted:
     - types: 'bool', 'num', 'int', 'real', 'fun', 'prod', word types, data
              types, record types
     - terms: Boolean connectives (T, F, ==>, /\, \/, ~, if-then-else,
              bool-case), quantifiers (!, ?), numeric literals, arithmetic
              operators (SUC, +, -, *, /, ~, DIV, MOD, ABS, MIN, MAX), function
              application, lambda abstraction, tuple selectors FST and SND,
              various word operations, data type constructors, data type case
              constants, record field selectors, record updates *)

  val Yices_types = [
    (("min", "bool"), "bool", ""),
    (("num", "num"), "nat", ""),
    (("integer", "int"), "int", ""),
    (("realax", "real"), "real", ""),
    (* Yices considers "-> X Y Z" and "-> X (-> Y Z)" different types. We use
       the latter only. *)
    (("min", "fun"), "->", ""),
    (* Likewise, we only use tuples of arity 2. *)
    (("pair", "prod"), "tuple", "")
  ]

  (* many HOL operators can be translated by simply mapping them to the
     corresponding Yices operator, or to a function that we define in Yices
     ourselves (the last component of each tuple is the function's
     definition) *)
  val Yices_operator_terms = [
    (boolSyntax.T, "true", ""),
    (boolSyntax.F, "false", ""),
    (boolSyntax.equality, "=", ""),
    (boolSyntax.implication, "=>", ""),
    (boolSyntax.conjunction, "and", ""),
    (boolSyntax.disjunction, "or", ""),
    (boolSyntax.negation, "not", ""),
    (boolSyntax.conditional, "ite", ""),
    (numSyntax.suc_tm, "+ 1", ""),
    (numSyntax.plus_tm, "+", ""),
    (* in HOL, 's1 < s2' implies 's1 - s2 = 0' for naturals; Yices however
       would consider 's1 - s2' a negative integer *)
    (numSyntax.minus_tm, "hol_num_minus",
       "(define hol_num_minus::(-> nat nat nat) " ^
         "(lambda (x::nat y::nat) (ite (< x y) 0 (- x y))))"),
    (numSyntax.mult_tm, "*", ""),
    (* 'x div 0' and 'x mod 0' are unspecified in HOL, but not type-correct in
       Yices and, therefore, treated quite weirdly: Yices claims that, e.g.,
       'x = 42 div 0' is unsatisfiable. Similar for div/mod on integers. *)
    (numSyntax.div_tm, "hol_num_div",
       "(define hol_num_div0::(-> nat nat))\n" ^
         "(define hol_num_div::(-> nat nat nat) (lambda (x::nat y::nat) " ^
         "(ite (= y 0) (hol_num_div0 x) (div x y))))"),
    (numSyntax.mod_tm, "hol_num_mod",
       "(define hol_num_mod0::(-> nat nat))\n" ^
         "(define hol_num_mod::(-> nat nat nat) (lambda (x::nat y::nat) " ^
         "(ite (= y 0) (hol_num_mod0 x) (mod x y))))"),
    (numSyntax.min_tm, "hol_num_min",
       "(define hol_num_min::(-> nat nat nat) (lambda (x::nat y::nat) " ^
         "(ite (< x y) x y)))"),
    (numSyntax.max_tm, "hol_num_max",
       "(define hol_num_max::(-> nat nat nat) (lambda (x::nat y::nat) " ^
         "(ite (< x y) y x)))"),
    (numSyntax.less_tm, "<", ""),
    (numSyntax.leq_tm, "<=", ""),
    (numSyntax.greater_tm, ">", ""),
    (numSyntax.geq_tm, ">=", ""),
    (intSyntax.negate_tm, "- 0", ""),
    (intSyntax.absval_tm, "hol_int_abs",
       "(define hol_int_abs::(-> int int) (lambda (x::int) " ^
         "(ite (< x 0) (- 0 x) x)))"),
    (intSyntax.plus_tm, "+", ""),
    (intSyntax.minus_tm, "-", ""),
    (intSyntax.mult_tm, "*", ""),
    (intSyntax.div_tm, "hol_int_div",
       "(define hol_int_div0::(-> int int))\n" ^
         "(define hol_int_div::(-> int int int) (lambda (x::int y::int) " ^
         "(ite (= y 0) (hol_int_div0 x) (div x y))))"),
    (intSyntax.mod_tm, "hol_int_mod",
       "(define hol_int_mod0::(-> int int))\n" ^
         "(define hol_int_mod::(-> int int int) (lambda (x::int y::int) " ^
         "(ite (= y 0) (hol_int_mod0 x) (mod x y))))"),
    (intSyntax.min_tm, "hol_int_min",
       "(define hol_int_min::(-> int int int) (lambda (x::int y::int) " ^
         "(ite (< x y) x y)))"),
    (intSyntax.max_tm, "hol_int_max",
       "(define hol_int_max::(-> int int int) (lambda (x::int y::int) " ^
         "(ite (< x y) y x)))"),
    (intSyntax.less_tm, "<", ""),
    (intSyntax.leq_tm, "<=", ""),
    (intSyntax.great_tm, ">", ""),
    (intSyntax.geq_tm, ">=", ""),
    (realSyntax.negate_tm, "- 0", ""),
    (realSyntax.absval_tm, "hol_real_abs",
       "(define hol_real_abs::(-> real real) (lambda (x::real) " ^
         "(ite (< x 0) (- 0 x) x)))"),
    (realSyntax.plus_tm, "+", ""),
    (realSyntax.minus_tm, "-", ""),
    (realSyntax.mult_tm, "*", ""),
    (* note that Yices uses '/' for division on reals, not 'div'; Yices will
       fail if the second argument is 0 or not a numeral *)
    (realSyntax.div_tm, "/", ""),
    (realSyntax.min_tm, "hol_real_min",
       "(define hol_real_min::(-> real real real) (lambda (x::real y::real) " ^
         "(ite (< x y) x y)))"),
    (realSyntax.max_tm, "hol_real_max",
       "(define hol_real_max::(-> real real real) (lambda (x::real y::real) " ^
         "(ite (< x y) y x)))"),
    (realSyntax.less_tm, "<", ""),
    (realSyntax.leq_tm, "<=", ""),
    (realSyntax.great_tm, ">", ""),
    (realSyntax.geq_tm, ">=", ""),
    (pairSyntax.comma_tm, "mk-tuple", ""),
    (wordsSyntax.word_and_tm, "bv-and", ""),
    (wordsSyntax.word_or_tm, "bv-or", ""),
    (wordsSyntax.word_xor_tm, "bv-xor", ""),
    (wordsSyntax.word_1comp_tm, "bv-not", ""),
    (wordsSyntax.word_lsl_tm, "bv-shift-left0", ""),
    (wordsSyntax.word_lsr_tm, "bv-shift-right0", ""),
    (* bv-shl is an undocumented Yices feature (as of version 1.0.29) *)
    (wordsSyntax.word_lsl_bv_tm, "bv-shl", ""),
    (* FIXME: The following functions have no built-in counterparts in Yices,
              as far as I know.  We could try to provide our own definitions.
    (wordsSyntax.word_asr_tm, ...),
    (wordsSyntax.word_ror_tm, ...),
    (wordsSyntax.word_rol_tm, ...),
    (wordsSyntax.word_asr_bv_tm, ...),
    (wordsSyntax.word_ror_bv_tm, ...),
    (wordsSyntax.word_rol_bv_tm, ...), *)
    (* word_concat in HOL has a more general type than bv-concat in Yices *)
    (wordsSyntax.word_concat_tm, "bv-concat", ""),
    (wordsSyntax.word_add_tm, "bv-add", ""),
    (wordsSyntax.word_sub_tm, "bv-sub", ""),
    (wordsSyntax.word_mul_tm, "bv-mul", ""),
    (wordsSyntax.word_2comp_tm, "bv-neg", ""),
    (wordsSyntax.word_lt_tm, "bv-slt", ""),
    (wordsSyntax.word_le_tm, "bv-sle", ""),
    (wordsSyntax.word_gt_tm, "bv-sgt", ""),
    (wordsSyntax.word_ge_tm, "bv-sge", ""),
    (wordsSyntax.word_lo_tm, "bv-lt", ""),
    (wordsSyntax.word_ls_tm, "bv-le", ""),
    (wordsSyntax.word_hi_tm, "bv-gt", ""),
    (wordsSyntax.word_hs_tm, "bv-ge", "")
  ]

  (* binders need to be treated differently from the operators in
     'Yices_operator_terms' *)
  val Yices_binder_terms = [
    (boolSyntax.strip_forall, "forall"),
    (boolSyntax.strip_exists, "exists"),
    (* Yices considers "-> X Y Z" and "-> X (-> Y Z)" different types. We use
       the latter only. *)
    (fn t => let val (var, body) = Term.dest_abs t
             in
               ([var], body)
             end handle Feedback.HOL_ERR _ => ([], t), "lambda")
  ]

  (* ty_dict: dictionary that maps types to names
     fresh: next fresh index to generate a new type name
     defs: list of auxiliary Yices definitions *)
  fun translate_type (acc, ty) =
    let
      fun uninterpreted_type (acc as (ty_dict, fresh, defs), ty) =
        case Redblackmap.peek (ty_dict, ty) of
          SOME s => (acc, s)
        | NONE => let val name = "t" ^ Int.toString fresh
                      val ty_dict' = Redblackmap.insert (ty_dict, ty, name)
                      val defs' = "(define-type " ^ name ^ ")" :: defs
                  in
                    if !Library.trace > 0 andalso Type.is_type ty then
                      Feedback.HOL_WARNING "Yices" "translate_type"
                        ("uninterpreted type " ^ Hol_pp.type_to_string ty)
                    else
                      ();
                    if !Library.trace > 2 then
                      Feedback.HOL_MESG
                        ("HolSmtLib (Yices): inventing name '" ^ name ^
                        "' for HOL type '" ^ Hol_pp.type_to_string ty ^ "'")
                    else
                      ();
                    ((ty_dict', fresh + 1, defs'), name)
                  end
      (* data types, record types *)
      fun data_type tyinfo (acc as (ty_dict, fresh, defs), ty) =
        case Redblackmap.peek (ty_dict, ty) of
          SOME s => (acc, s)
        | NONE => let val name = "t" ^ Int.toString fresh
                      val ty_dict' = Redblackmap.insert (ty_dict, ty, name)
                      val acc = (ty_dict', fresh + 1, defs)
                      val is_record = not (List.null (TypeBasePure.fields_of
                        tyinfo))
                      val ((acc, _), constructors) = Lib.foldl_map
                        (fn ((acc, i), c) =>
                        let val cname = "c_" ^ name ^ "_" ^ Int.toString i
                            val c = TypeBasePure.cinst ty c
                            val (doms, _) = boolSyntax.strip_fun
                              (Term.type_of c)
                            val ((acc, _), doms) = Lib.foldl_map
                              (fn ((acc, j), dom) =>
                              let val aname = if is_record then
                                      "f_" ^ name ^ "_" ^ Int.toString j
                                    else
                                      "a_" ^ name ^ "_" ^ Int.toString i ^ "_" ^
                                        Int.toString j
                                  val (acc, atype) = translate_type (acc, dom)
                              in
                                ((acc, j + 1), aname ^ "::" ^ atype)
                              end) ((acc, 0), doms)
                            val doms = String.concatWith " " doms
                        in
                          ((acc, i + 1), (cname, doms))
                        end) ((acc, 0), TypeBasePure.constructors_of tyinfo)
                      val datatype_def = if is_record then
                          "(record " ^ Lib.snd (List.hd constructors) ^ ")"
                        else
                          "(datatype " ^ String.concatWith " " (List.map
                            (fn (cname, doms) => if doms = "" then cname else
                              "(" ^ cname ^ " " ^ doms ^ ")") constructors) ^
                          ")"
                      val (ty_dict, fresh, defs) = acc
                      val defs' = "(define-type " ^ name ^ " " ^ datatype_def ^
                        ")" :: defs
                  in
                    ((ty_dict, fresh, defs'), name)
                  end
    in
      if wordsSyntax.is_word_type ty then
        (* bit-vector types *)
        let val dim = fcpLib.index_to_num (wordsSyntax.dest_word_type ty)
        in
          (acc, "(bitvector " ^ Arbnum.toString dim ^ ")")
        end handle Feedback.HOL_ERR _ => (* index_to_num can fail *)
          raise (Feedback.mk_HOL_ERR "Yices" "translate_type"
            "bit-vector type of unknown size")
      else if Type.is_type ty then
        (* check table of types *)
        let val {Thy, Tyop, Args} = Type.dest_thy_type ty
        in
          case List.find (fn ((thy, tyop), _, _) =>
                 thy = Thy andalso tyop = Tyop) Yices_types of
            SOME (_, name, def) =>
            let val ((ty_dict, fresh, defs), yices_Args) = Lib.foldl_map
                  translate_type (acc, Args)
                val defs' = if def = "" orelse Lib.mem def defs then defs else
                  def :: defs
                val yices_Args = String.concatWith " " yices_Args
            in
              ((ty_dict, fresh, defs'),
               if yices_Args = "" then name
               else "(" ^ name ^ " " ^ yices_Args ^ ")")
            end
          | NONE =>
            (* perhaps a data type? *)
            (case TypeBase.fetch ty of
              SOME tyinfo =>
                data_type tyinfo (acc, ty)
            | NONE =>
                uninterpreted_type (acc, ty))
        end
      else uninterpreted_type (acc, ty)
    end

  (* dict: dictionary that maps terms to names
     fresh: next fresh index to generate a new name
     ty_dict: cf. translate_type
     ty_fresh: cf. translate_type
     defs: list of auxiliary Yices definitions *)
  fun translate_term (acc, tm) =
    (* numerals *)
    if numSyntax.is_numeral tm then
      let val n = numSyntax.dest_numeral tm
      in
        (acc, Arbnum.toString n)
      end
    else if intSyntax.is_int_literal tm then
      let val i = intSyntax.int_of_term tm
          val s = Arbint.toString i
      in
        (acc, String.substring (s, 0, String.size s - 1))
      end
    else if realSyntax.is_real_literal tm then
      let val i = realSyntax.int_of_term tm
          val s = Arbint.toString i
      in
        (acc, String.substring (s, 0, String.size s - 1))
      end
    (* bool_case *)
    (* cannot be defined as a function in Yices because it is polymorphic *)
    else if boolSyntax.is_bool_case tm then
      let val (t1, t2, t3) = boolSyntax.dest_bool_case tm
          val (acc, s1) = translate_term (acc, t1)
          val (acc, s2) = translate_term (acc, t2)
          val (acc, s3) = translate_term (acc, t3)
      in
        (acc, "(ite " ^ s3 ^ " " ^ s1 ^ " " ^ s2 ^ ")")
      end
    (* FST *)
    (* cannot be defined as a function in Yices because it is polymorphic *)
    else if pairSyntax.is_fst tm then
      let val t1 = pairSyntax.dest_fst tm
          val (acc, s1) = translate_term (acc, t1)
      in
        (acc, "(select " ^ s1 ^ " 1)")
      end
    (* SND *)
    (* cannot be defined as a function in Yices because it is polymorphic *)
    else if pairSyntax.is_snd tm then
      let val t1 = pairSyntax.dest_snd tm
          val (acc, s1) = translate_term (acc, t1)
      in
        (acc, "(select " ^ s1 ^ " 2)")
      end
    (* word literals *)
    else if wordsSyntax.is_word_literal tm then
      let val (num, dim_ty) = wordsSyntax.dest_n2w tm
          val dim = fcpLib.index_to_num dim_ty
                      handle Feedback.HOL_ERR _ =>
                        raise (Feedback.mk_HOL_ERR "Yices" "translate_term"
                               "word literal: bit-vector type of unknown size")
          val n = numSyntax.dest_numeral num
      in
        (acc, "(mk-bv " ^ Arbnum.toString dim ^ " " ^ Arbnum.toString n ^ ")")
      end
    (* fcp_index *)
    (* Hopefully used as index into a bit vector, but we don't check -- Yices
       should. *)
    else if wordsSyntax.is_index tm then
      let val (t1, num) = wordsSyntax.dest_index tm
          val (acc, s1) = translate_term (acc, t1)
          val n = numSyntax.dest_numeral num
                    handle Feedback.HOL_ERR _ =>
                      raise (Feedback.mk_HOL_ERR "Yices" "translate_term"
                               "index into bit-vector is not a numeral")
          val sn = Arbnum.toString n
      in
        (acc, "(= (bv-extract " ^ sn ^ " " ^ sn ^ " " ^ s1 ^ ") 0b1)")
      end
    (* word_extract -- applies w2w after extraction to adjust the dimension of
       the result in HOL *)
    else if wordsSyntax.is_word_extract tm then
      let val (n1, n2, w, dim_ty) = wordsSyntax.dest_word_extract tm
          val n1 = numSyntax.dest_numeral n1
            handle Feedback.HOL_ERR _ =>
              raise (Feedback.mk_HOL_ERR "Yices" "translate_term"
                "word_extract: upper index is not a numeral")
          val n2 = numSyntax.dest_numeral n2
            handle Feedback.HOL_ERR _ =>
              raise (Feedback.mk_HOL_ERR "Yices" "translate_term"
                "word_extract: lower index is not a numeral")
          val dim = fcpLib.index_to_num dim_ty
            handle Feedback.HOL_ERR _ =>
              raise (Feedback.mk_HOL_ERR "Yices" "translate_term"
                "word_extract: result bit-vector type of unknown size")
          val extract_dim = Arbnum.+ (Arbnum.- (n1, n2), Arbnum.one)
          val old_dim = fcpLib.index_to_num (wordsSyntax.dim_of w)
            handle Feedback.HOL_ERR _ =>
              raise (Feedback.mk_HOL_ERR "Yices" "translate_term"
                "word_extract: argument bit-vector type of unknown size")
          val (acc, s1) = translate_term (acc, w)
          val s1 = if Arbnum.< (n1, n2) then
              (* Yices does not support bit-vector extraction with n1 < n2 *)
              "(mk-bv 1 0)"
            else
              "(bv-extract " ^ Arbnum.toString n1 ^ " " ^ Arbnum.toString n2 ^
                " " ^ (if Arbnum.< (n1, old_dim) then s1 else
                  (* n1 >= old_dim: we need to prepend 0s to 'w' to make
                     Yices happy *)
                  "(bv-concat (mk-bv " ^ Arbnum.toString (Arbnum.+
                    (Arbnum.- (n1, old_dim), Arbnum.one)) ^ " 0) " ^ s1 ^ ")")
                ^ ")"
      in
        if dim = extract_dim then
          (acc, s1)
        else if Arbnum.< (dim, extract_dim) then
          (acc, "(bv-extract " ^ Arbnum.toString (Arbnum.- (dim, Arbnum.one)) ^
             " 0 " ^ s1 ^ ")")
        else  (* dim > extract_dim *)
          (acc, "(bv-concat (mk-bv " ^ Arbnum.toString
            (Arbnum.- (dim, extract_dim)) ^ " 0) " ^ s1 ^ ")")
      end
    (* w2w *)
    else if wordsSyntax.is_w2w tm then
      let val (t1, dim_ty) = wordsSyntax.dest_w2w tm
          val dim = fcpLib.index_to_num dim_ty
            handle Feedback.HOL_ERR _ =>
              raise (Feedback.mk_HOL_ERR "Yices" "translate_term"
                "w2w: result bit-vector type of unknown size")
          val old_dim_ty = wordsSyntax.dim_of t1
          val old_dim = fcpLib.index_to_num old_dim_ty
            handle Feedback.HOL_ERR _ =>
              raise (Feedback.mk_HOL_ERR "Yices" "translate_term"
                "w2w: argument bit-vector type of unknown size")
          val (acc, s1) = translate_term (acc, t1)
      in
        if Arbnum.<= (dim, old_dim) then
          (acc, "(bv-extract " ^ Arbnum.toString (Arbnum.- (dim, Arbnum.one)) ^
             " 0 " ^ s1 ^ ")")
        else
          (acc, "(bv-concat (mk-bv " ^ Arbnum.toString
             (Arbnum.- (dim, old_dim)) ^ " 0) " ^ s1 ^ ")")
      end
    (* sw2sw *)
    else if wordsSyntax.is_sw2sw tm then
      let val (t1, dim_ty) = wordsSyntax.dest_sw2sw tm
          val dim = fcpLib.index_to_num dim_ty
            handle Feedback.HOL_ERR _ =>
              raise (Feedback.mk_HOL_ERR "Yices" "translate_term"
                "sw2sw: result bit-vector type of unknown size")
          val old_dim_ty = wordsSyntax.dim_of t1
          val old_dim = fcpLib.index_to_num old_dim_ty
            handle Feedback.HOL_ERR _ =>
              raise (Feedback.mk_HOL_ERR "Yices" "translate_term"
                "sw2sw: argument bit-vector type of unknown size")
          val (acc, s1) = translate_term (acc, t1)
      in
        if Arbnum.< (dim, old_dim) then
          (acc, "(bv-extract " ^ Arbnum.toString (Arbnum.- (dim, Arbnum.one)) ^
             " 0 " ^ s1 ^ ")")
        else
          (acc, "(bv-sign-extend " ^ s1 ^ " " ^ Arbnum.toString
             (Arbnum.- (dim, old_dim)) ^ ")")
      end
    (* word_msb *)
    else if wordsSyntax.is_word_msb tm then
      let val t1 = wordsSyntax.dest_word_msb tm
          val dim_ty = wordsSyntax.dim_of t1
          val n = fcpLib.index_to_num dim_ty
                    handle Feedback.HOL_ERR _ =>
                      raise (Feedback.mk_HOL_ERR "Yices" "translate_term"
                        "word_msb: argument bit-vector type of unknown size")
          val sn = Arbnum.toString (Arbnum.- (n, Arbnum.one))
          val (acc, s1) = translate_term (acc, t1)
      in
        (acc, "(= (bv-extract " ^ sn ^ " " ^ sn ^ " " ^ s1 ^ ") 0b1)")
      end
    (* binders *)
    else
      case Lib.get_first (fn (strip_fn, name) =>
        case strip_fn tm of
          ([], _) => NONE (* not this binder *)
        | (vars, body) =>
          let val typs = List.map Term.type_of vars
              (* We must gather Yices definitions for all types, and for all
                 terms in the body with the exception of bound vars. Still,
                 bound vars must not be mapped to names used elsewhere (to
                 avoid accidental capture). Also note that not all bound vars
                 need to occur in the body. *)
              val (dict, fresh, ty_dict, ty_fresh, defs) = acc
              (* translate types of bound variables separately, because we
                 don't want to discard their definitions *)
              val (ty_acc, yices_typs) = Lib.foldl_map translate_type
                ((ty_dict, ty_fresh, defs), typs)
              val (ty_dict, ty_fresh, defs) = ty_acc
              (* translate bound variables; make sure they are mapped to fresh
                 names; their types have just been translated already  *)
              val empty_dict = Redblackmap.mkDict Term.compare
              val (bound_acc, yices_vars) = Lib.foldl_map translate_term
                ((empty_dict, fresh, ty_dict, ty_fresh, []), vars)
              val (bound_dict, fresh, _, _, _) = bound_acc
              (* translate the body, with bound variables mapped properly *)
              fun union dict1 dict2 =
                Redblackmap.foldl (fn (t, s, d) => Redblackmap.insert (d, t, s))
                  dict1 dict2
              val acc = (union dict bound_dict, fresh, ty_dict, ty_fresh, defs)
              val (acc, yices_body) = translate_term (acc, body)
              val (body_dict, fresh, ty_dict, ty_fresh, defs) = acc
              (* discard the mapping of bound variables, but keep other term
                 mappings that result from translation of the body *)
              fun diff dict1 dict2 =
                Redblackmap.foldl (fn (t, _, d) =>
                  (Lib.fst o Redblackmap.remove) (d, t)) dict1 dict2
              val dict = union dict (diff body_dict bound_dict)
              val yices_bounds = String.concatWith " " (List.map (fn (v, t) =>
                v ^ "::" ^ t) (Lib.zip yices_vars yices_typs))
            in
              SOME ((dict, fresh, ty_dict, ty_fresh, defs),
                "(" ^ name ^ " (" ^ yices_bounds ^ ") " ^ yices_body ^ ")")
            end) Yices_binder_terms of
        SOME result => result
      | NONE =>
    (* operators + arguments *)
      let val (rator, rands) = boolSyntax.strip_comb tm
      in
        case List.find (fn (t, _, _) => Term.same_const t rator)
            Yices_operator_terms of
          SOME (_, name, def) =>
          let val (acc', yices_rands) = Lib.foldl_map
                translate_term (acc, rands)
              val (dict, fresh, ty_dict, ty_fresh, defs) = acc'
              val defs' = if def = "" orelse Lib.mem def defs then defs else
                def :: defs
              val yices_rands' = String.concatWith " " yices_rands
          in
            ((dict, fresh, ty_dict, ty_fresh, defs'),
             if yices_rands = [] then name
             else "(" ^ name ^ " " ^ yices_rands' ^ ")")
          end
        | NONE =>

          (* data type constructors + arguments *)
          let val ty = Term.type_of rator
              val (_, data_ty) = boolSyntax.strip_fun ty
          in
            case TypeBase.fetch data_ty of
              SOME tyinfo =>
                let val i = Lib.index (Term.same_const rator)
                      (TypeBasePure.constructors_of tyinfo)  (* may fail *)
                    (* also collect type definitions *)
                    val (dict, fresh, ty_dict, ty_fresh, defs) = acc
                    val ((ty_dict, ty_fresh, defs), _) = translate_type
                      ((ty_dict, ty_fresh, defs), ty)
                    val ty_name = Redblackmap.find (ty_dict, data_ty)
                    val cname = "c_" ^ ty_name ^ "_" ^ Int.toString i
                    (* translate argument terms *)
                    val (acc, yices_rands) = Lib.foldl_map translate_term
                      ((dict, fresh, ty_dict, ty_fresh, defs), rands)
                    val name = String.concatWith " " (cname :: yices_rands)
                    val name = if List.null yices_rands then name
                      else "(" ^ name ^ ")"
                in
                  (acc, name)
                end
            | NONE =>
                raise Feedback.mk_HOL_ERR "Yices" "translate_term"
                  "not a data type constructor (range type is not a data type)"
          end
          handle Feedback.HOL_ERR _ =>  (* not a data type constructor *)

          (* FIXME: There's a problem with the use of data type constructors
             (which are not curried in Yices, e.g., of type "-> X Y Z") as
             arguments to case constants, which expect curried functions (of
             type, e.g., "-> X (-> Y Z)").  Perhaps eta-expansion currently
             prevents this problem from showing up, but a good (clean) solution
             is still missing. *)

          (* case constants for data types (+ arguments) *)
          let val (cases, elem) =
                case rands of
                  [] =>
                    raise Feedback.mk_HOL_ERR "Yices" "translate_term"
                      "not a case constant (no operands)"
                | (h::t) => (t,h)
              val data_ty = Term.type_of elem
          in
            case TypeBase.fetch data_ty of
              SOME tyinfo =>
                if Term.same_const rator (TypeBasePure.case_const_of tyinfo)
                then
                  let (* constructors *)
                      val cs = TypeBasePure.constructors_of tyinfo
                      val _ = if List.length cs = List.length cases then ()
                        else
                          raise Feedback.mk_HOL_ERR "Yices" "translate_term"
                            "not a case constant (wrong number of cases)"
                      (* translate argument terms *)
                      val (acc, yices_cases) = Lib.foldl_map translate_term
                        (acc, cases)
                      val (acc, yices_elem) = translate_term (acc, elem)
                      val (_, _, ty_dict, _, _) = acc
                      val ty_name = Redblackmap.find (ty_dict, data_ty)
                      (* recognizers, accessors *)
                      val cs = List.map (List.length o Lib.fst o
                        boolSyntax.strip_fun o Term.type_of) cs
                      val (_, cs) = Lib.foldl_map (fn (i, n) =>
                        let val cname = "c_" ^ ty_name ^ "_" ^ Int.toString i
                            fun aname j =
                              "a_" ^ ty_name ^ "_" ^ Int.toString i ^ "_" ^
                                Int.toString j
                            val anames = List.tabulate (n, aname)
                        in
                          (i + 1, (cname, anames))
                        end) (0, cs)
                      (* build the cascaded ite expression *)
                      val mk_case = List.foldl (fn (aname, yices_case) =>
                        "(" ^ yices_case ^ " (" ^ aname ^ " " ^ yices_elem ^
                        "))")
                      fun cascaded_ite [ycase] [(_, anames)] =
                        mk_case ycase anames
                        | cascaded_ite (ycase::ys) ((cname, anames)::cs) =
                        "(ite (" ^ cname ^ "? " ^ yices_elem ^ ") " ^
                          mk_case ycase anames ^ " " ^ cascaded_ite ys cs ^
                          ")"
                        | cascaded_ite _ _ =
                        raise Feedback.mk_HOL_ERR "Yices" "translate_term"
                          "not a case constant (error in cascaded_ite)"
                  in
                    (acc, cascaded_ite yices_cases cs)
                  end
                else
                  raise Feedback.mk_HOL_ERR "Yices" "translate_term"
                    "not a case constant (different constant)"
            | NONE =>
                raise Feedback.mk_HOL_ERR "Yices" "translate_term"
                  "not a case constant (last argument is not a data type)"
          end
          handle Feedback.HOL_ERR _ =>  (* not a case constant *)

          (* record field selectors *)
          let val (select, x) = Term.dest_comb tm
              val (select_name, select_ty) = Term.dest_const select
              val (record_ty, rng_ty) = Type.dom_rng select_ty
              val (record_name, _) = Type.dest_type record_ty
              (* FIXME: This check for matching types may be too liberal, as it
                 does not take the record type into account. On the other hand,
                 it may not be needed at all: ensuring that the constant name
                 is identical to the field selector name may already be
                 sufficient. *)
              val j = Lib.index (fn (field_name, field_ty) =>
                  select_name = record_name ^ "_" ^ field_name andalso
                    Lib.can (Type.match_type field_ty) rng_ty)
                (TypeBase.fields_of record_ty)
              (* translate argument *)
              val (acc, yices_x) = translate_term (acc, x)
              val (_, _, ty_dict, _, _) = acc
              val ty_name = Redblackmap.find (ty_dict, record_ty)
              val yices_field = "f_" ^ ty_name ^ "_" ^ Int.toString j
          in
            (acc, "(select " ^ yices_x ^ " " ^ yices_field ^ ")")
          end
          handle Feedback.HOL_ERR _ =>  (* not a record field selector *)

          (* record field updates *)
          let
              val (update_f, x) = Term.dest_comb tm
              val (update, f) = Term.dest_comb update_f
              (* FIXME: Only field updates using the K combinator (in eta-long
                 form) are supported at the moment. *)
              val (var1, body) = Term.dest_abs f
              val (f, var2) = Term.dest_comb body
              val _ = Term.aconv var1 var2 orelse
                raise Feedback.mk_HOL_ERR "Yices" "translate_term"
                  "not a field selector (update function not in eta-long form)"
              val new_val = combinSyntax.dest_K_1 f
              val (update_name, _) = Term.dest_const update
              val record_ty = Term.type_of x
              val (record_name, _) = Type.dest_type record_ty
              val val_ty = Term.type_of new_val
              (* FIXME: This check for matching types may be too liberal, as it
                 does not take the record type into account. On the other hand,
                 it may not be needed at all: ensuring that the constant name
                 is identical to the field update function's name may already be
                 sufficient. *)
              val j = Lib.index (fn (field_name, field_ty) =>
                  update_name = record_name ^ "_" ^ field_name ^ "_fupd" andalso
                    Lib.can (Type.match_type field_ty) val_ty)
                (TypeBase.fields_of record_ty)
              val (acc, yices_x) = translate_term (acc, x)
              val (acc, yices_val) = translate_term (acc, new_val)
              val (_, _, ty_dict, _, _) = acc
              val ty_name = Redblackmap.find (ty_dict, record_ty)
              val fname = "f_" ^ ty_name ^ "_" ^ Int.toString j
          in
            (acc, "(update " ^ yices_x ^ " " ^ fname ^ " " ^ yices_val ^ ")")
          end
          handle Feedback.HOL_ERR _ =>  (* not a record field selector *)

          (* function application *)
          if Term.is_comb tm then
          (* Yices considers "-> X Y Z" and "-> X (-> Y Z)" different types. We
             use the latter only. *)
            let val (t1, t2) = Term.dest_comb tm
                val (acc, s1) = translate_term (acc, t1)
                val (acc, s2) = translate_term (acc, t2)
            in
              (acc, "(" ^ s1 ^ " " ^ s2 ^ ")")
            end
          else (* replace all other terms with a variable *)
          (* we even replace variables, to make sure there are no name clashes
             with either (i) variables generated by us, or (ii) reserved Yices
             names *)
            let val (dict, fresh, ty_dict, ty_fresh, defs) = acc
            in
              case Redblackmap.peek (dict, tm) of
                SOME s => (acc, s)
              | NONE =>
                let val name = "v" ^ Int.toString fresh
                    val dict = Redblackmap.insert (dict, tm, name)
                    (* also collect type definitions *)
                    val ((ty_dict, ty_fresh, defs), ty_name) = translate_type
                      ((ty_dict, ty_fresh, defs), Term.type_of tm)
                    val defs = "(define " ^ name ^ "::" ^ ty_name ^ ")" :: defs
                in
                  if !Library.trace > 0 andalso Term.is_const rator then
                    Feedback.HOL_WARNING "Yices" "translate_term"
                      ("uninterpreted constant " ^ Hol_pp.term_to_string tm)
                  else
                    ();
                  if !Library.trace > 2 then
                    Feedback.HOL_MESG
                      ("HolSmtLib (Yices): inventing name '" ^ name ^
                      "' for HOL term '" ^ Hol_pp.term_to_string tm ^ "'")
                  else
                    ();
                  ((dict, fresh + 1, ty_dict, ty_fresh, defs), name)
                end
            end
      end

  (* returns the eta-long form of a term, i.e., every variable/constant is
     applied to the correct number of arguments, as determined by its type *)
  fun full_eta_long_conv tm =
    if Term.is_abs tm then
      let val (v, body) = Term.dest_abs tm
      in
        Term.mk_abs (v, full_eta_long_conv body)
      end
    else
      let val (rand, args) = boolSyntax.strip_comb tm
      in
        if Term.is_abs rand then
          Term.list_mk_comb
            (full_eta_long_conv rand, map full_eta_long_conv args)
        else (* 'rand' is a variable/constant *)
          let val T = Term.type_of tm
          in
            if (Lib.can Type.dom_rng) T then
              (* eta expansion (by one argument) *)
              let val v = Term.mk_var ("x", Lib.fst (Type.dom_rng T))
                  val fresh = Term.variant (Term.free_vars tm) v
              in
                full_eta_long_conv (Term.mk_abs
                  (fresh, Term.list_mk_comb (rand, args @ [fresh])))
              end
            else
              Term.list_mk_comb (rand, map full_eta_long_conv args)
          end
      end

  fun goal_to_Yices goal =
  let
    (* simplification: eliminates some HOL terms that are not supported by the
       Yices translation *)
    val SIMP_TAC = Tactical.THENL (Tactical.REPEAT Tactic.GEN_TAC,
      [Tactical.THEN (Library.LET_SIMP_TAC,
        Tactical.THEN
         (Tactic.CONV_TAC (Conv.DEPTH_CONV wordsLib.EXPAND_REDUCE_CONV),
          Tactical.THEN (simpLib.SIMP_TAC (simpLib.++ (simpLib.++
            (pureSimps.pure_ss, numSimps.REDUCE_ss), wordsLib.SIZES_ss))
            [wordsTheory.word_lsr_bv_def, wordsTheory.w2n_n2w,
             wordsTheory.word_lsb_def, wordsTheory.word_msb_def,
             wordsTheory.WORD_SLICE_THM, wordsTheory.WORD_BITS_EXTRACT],
          Tactical.THEN (Library.SET_SIMP_TAC, Tactic.BETA_TAC))))])
    val ((asl, g), _) = SolverSpec.simplify SIMP_TAC goal
    val (asl, g) = (List.map full_eta_long_conv asl, full_eta_long_conv g)
    val empty = Redblackmap.mkDict Term.compare
    val empty_ty = Redblackmap.mkDict Type.compare
    val ((_, _, _, _, defs), yices_asl_g) = Lib.foldl_map translate_term
      ((empty, 0, empty_ty, 0, []), asl @ [boolSyntax.mk_neg g])
    val defs = List.map (fn s => s ^ "\n") (List.rev defs)
    val yices_asl_g = List.map (fn s => "(assert " ^ s ^ ")\n") yices_asl_g
  in
    defs @ yices_asl_g @ ["(check)\n"]
  end

  (* returns SAT if Yices reported "sat", UNSAT if Yices reported "unsat" *)
  fun result_fn path =
    let val instream = TextIO.openIn path
        val line     = TextIO.inputLine instream
    in
      TextIO.closeIn instream;
      if line = SOME "sat\n" then
        SolverSpec.SAT NONE
      else if line = SOME "unsat\n" then
        SolverSpec.UNSAT NONE
      else
        SolverSpec.UNKNOWN NONE
    end

  fun is_configured () =
    Option.isSome (OS.Process.getEnv "HOL4_YICES_EXECUTABLE")

  (* Yices 1.0.29, native file format *)
  fun Yices_Oracle goal =
    case OS.Process.getEnv "HOL4_YICES_EXECUTABLE" of
      SOME file =>
        SolverSpec.make_solver
          (Lib.pair () o goal_to_Yices)
          (file ^ " -tc ")
          (Lib.K result_fn)
          goal
    | NONE =>
        raise Feedback.mk_HOL_ERR "Yices" "Yices_Oracle"
          "Yices not configured: set the HOL4_YICES_EXECUTABLE environment variable to point to the Yices executable file."

end
