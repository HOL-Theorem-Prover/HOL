(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Functions to translate HOL terms into the SMT-LIB format. *)

structure SmtLib = struct

  (* So far, only the AUFLIA logic is supported (closed linear formulas over
     the theory of integer arrays with free sort, function and predicate
     symbols):

     :sorts (Int Array)

     :funs ((0 Int)
            (1 Int)
            (~ Int Int)     ; unary minus
            (- Int Int Int) ; binary minus
            (+ Int Int Int :assoc :comm :unit {0})
            ( * Int Int Int :assoc :comm :unit {1})
            (select Array Int Int)
            (store Array Int Int Array)
           )

     :preds ((<= Int Int :refl :trans :antisym)
             (< Int Int :trans :irref)
             (>= Int Int :refl :trans :antisym)
             (> Int Int :trans :irref)
            )

     All other types and terms are treated as uninterpreted.  Actually, even
     arrays are not supported yet.
  *)

  (* Types are called sorts in SMT-LIB.  Note that sorts cannot depend on
     argument sorts.  Even function types are only supported implicitly.  Also
     note that 'bool' (when it occurs as the domain of a function, or the type
     of a bound variable) is treated as an uninterpreted type. *)

  (* (HOL type, SMT-LIB sort name) *)
  val TypesTable = [
    (intSyntax.int_ty, "Int")
  ]

  (* SMT-LIB distinguishes between terms and formulas (and also between
     functions and predicates). *)

  (* (HOL term, SMT-LIB name, fun_symb_decl, an_formula) *)
  val OperatorsTable = [
    (boolSyntax.T, "true", "", ""),
    (boolSyntax.F, "false", "", ""),
    (Term.inst [{redex = Type.alpha, residue = Type.bool}] boolSyntax.equality,
       "iff", "", ""),
    (boolSyntax.equality, "=", "", ""),
    (boolSyntax.implication, "implies", "", ""),
    (boolSyntax.conjunction, "and", "", ""),
    (boolSyntax.disjunction, "or", "", ""),
    (* (..., "xor", "", ""), *)
    (boolSyntax.negation, "not", "", ""),
    (Term.inst [{redex = Type.alpha, residue = Type.bool}]
       boolSyntax.conditional, "if_then_else", "", ""),
    (boolSyntax.conditional, "ite", "", ""),
    (* integer operations *)
    (intSyntax.negate_tm, "~", "", ""),
    (intSyntax.absval_tm, "hol_int_abs", "hol_int_abs Int Int",
      "forall (?x Int) (= (hol_int_abs ?x) (ite (< ?x 0) (- 0 ?x) ?x))"),
    (intSyntax.plus_tm, "+", "", ""),
    (intSyntax.minus_tm, "-", "", ""),
    (intSyntax.mult_tm, "*", "", ""),
    (intSyntax.min_tm, "hol_int_min", "hol_int_min Int Int Int",
      "forall (?x Int) (?y Int) (= (hol_int_min ?x ?y) (ite (< ?x ?y) ?x ?y))"),
    (intSyntax.max_tm, "hol_int_max", "hol_int_max Int Int Int",
      "forall (?x Int) (?y Int) (= (hol_int_max ?x ?y) (ite (< ?x ?y) ?y ?x))"),
    (intSyntax.less_tm, "<", "", ""),
    (intSyntax.leq_tm, "<=", "", ""),
    (intSyntax.great_tm, ">", "", ""),
    (intSyntax.geq_tm, ">=", "", "")
  ]

  (* Binders need to be treated differently from the operators above. *)
  val BindersTable = [
    (boolSyntax.strip_forall, "forall"),
    (boolSyntax.strip_exists, "exists")
    (* no lambda abstraction in SMT-LIB syntax *)
  ]

  (* ty_dict: dictionary that maps types to names
     fresh: next fresh index to generate a new type name *)
  fun translate_type (acc, ty) =
  let fun translate (acc, ty) =
        (* check table of types *)
        case List.find (fn (ty', _) => ty' = ty) TypesTable of
          SOME (_, name) =>
            (acc, name)
        | NONE =>
          (* uninterpreted type *)
          let val (ty_dict, fresh) = acc
          in
            case Redblackmap.peek (ty_dict, ty) of
              SOME s => (acc, s)
            | NONE => let val name = "t" ^ Int.toString fresh
                          val ty_dict = Redblackmap.insert (ty_dict, ty, name)
                      in
                        ((ty_dict, fresh + 1), name)
                      end
          end
      val (doms, rng) = boolSyntax.strip_fun ty
      val types = if rng = Type.bool then doms else doms @ [rng]
      val (acc, smtlib_types) = Lib.foldl_map translate (acc, types)
  in
    (* a (possibly empty!) string giving the argument types and range type of a
       function, or the argument types of a predicate *)
    (acc, String.concatWith " " smtlib_types)
  end

  (* dict: dictionary that maps terms to names
     fresh: next fresh index to generate a new name
     ty_dict: cf. translate_type
     ty_fresh: cf. translate_type
     funs: list of additional function names
     defs: list of additional assumptions (i.e., definitions)
  *)
  fun translate_term (acc, tm) =
    (* numerals -- but not 'intSyntax.negate_tm'! *)
    if intSyntax.is_int_literal tm andalso (not (Term.is_comb tm) orelse
      Lib.fst (Term.dest_comb tm) <> intSyntax.negate_tm) then
      let val i = intSyntax.int_of_term tm
          val s = Arbint.toString (Arbint.abs i)
          val neg = Arbint.< (i, Arbint.zero)
      in
        (acc, (if neg then "(~ " else "") ^ String.substring
          (s, 0, String.size s - 1) ^ (if neg then ")" else ""))
      end
    (* bool_case *)
    (* cannot be defined as a function in SMT-LIB because it is polymorphic *)
    else if boolSyntax.is_bool_case tm then
      let val (t1, t2, t3) = boolSyntax.dest_bool_case tm
          val (acc, s1) = translate_term (acc, t1)
          val (acc, s2) = translate_term (acc, t2)
          val (acc, s3) = translate_term (acc, t3)
          val ite = (if Term.type_of tm = Type.bool then
                       "if_then_else" else "ite")
      in
        (acc, "(" ^ ite ^ " " ^ s3 ^ " " ^ s1 ^ " " ^ s2 ^ ")")
      end
    (* binders *)
    else
      case Lib.get_first (fn (strip_fn, name) =>
        case strip_fn tm of
          ([], _) => NONE (* not this binder *)
        | (vars, body) =>
          let val typs = List.map Term.type_of vars
              (* We must gather SMT-LIB definitions for all types, and for all
                 terms in the body with the exception of bound vars. Still,
                 bound vars must not be mapped to names used elsewhere (to
                 avoid accidental capture). Also note that not all bound vars
                 need to occur in the body. *)
              val (dict, fresh, ty_dict, ty_fresh, funs, defs) = acc
              (* translate types of bound variables separately, because we
                 don't want to discard their definitions *)
              val (ty_acc, smtlib_typs) = Lib.foldl_map translate_type
                ((ty_dict, ty_fresh), typs)
              val (ty_dict, ty_fresh) = ty_acc
              (* translate bound variables; make sure they are mapped to fresh
                 names; their types have just been translated already;
                 prepend a '?' to each name *)
              val empty_dict = Redblackmap.mkDict Term.compare
              val (bound_acc, _) = Lib.foldl_map translate_term
                ((empty_dict, fresh, ty_dict, ty_fresh, [], []), vars)
              val (bound_dict, fresh, _, _, _, _) = bound_acc
              val bound_dict = Redblackmap.transform (fn s => "?" ^ s)
                bound_dict
              val smtlib_vars = map (Lib.curry Redblackmap.find bound_dict) vars
              (* translate the body, with bound variables mapped properly *)
              fun union dict1 dict2 =
                Redblackmap.foldl (fn (t, s, d) => Redblackmap.insert (d, t, s))
                  dict1 dict2
              val acc = (union dict bound_dict, fresh, ty_dict, ty_fresh,
                           funs, defs)
              val (acc, smtlib_body) = translate_term (acc, body)
              val (body_dict, fresh, ty_dict, ty_fresh, funs, defs) = acc
              (* discard the mapping of bound variables, but keep other term
                 mappings that result from translation of the body *)
              fun diff dict1 dict2 =
                Redblackmap.foldl (fn (t, _, d) =>
                  (Lib.fst o Redblackmap.remove) (d, t)) dict1 dict2
              val dict = union dict (diff body_dict bound_dict)
              val smtlib_bounds = String.concatWith " "
                (List.map (fn (v, t) => "(" ^ v ^ " " ^ t ^ ")")
                  (Lib.zip smtlib_vars smtlib_typs))
            in
              SOME ((dict, fresh, ty_dict, ty_fresh, funs, defs),
                "(" ^ name ^ " " ^ smtlib_bounds ^ " " ^ smtlib_body ^ ")")
            end) BindersTable of
        SOME result => result
      | NONE =>
        (* let/flet *)

        (* TODO *)

        if Term.is_comb tm then
          (* function application *)
          let val (rator, rands) = boolSyntax.strip_comb tm
              val (acc, smtlib_rator) = translate_term (acc, rator)
              val (acc, smtlib_rands) = Lib.foldl_map translate_term
                                          (acc, rands)
          in
            (acc, "(" ^ smtlib_rator ^ " " ^
                    String.concatWith " " smtlib_rands ^ ")")
          end
        else
          (* base case: operator or uninterpreted term *)
          case List.find (fn (t, _, _, _) => Lib.can (Term.match_term t) tm)
            OperatorsTable of
            SOME (_, name, extrafun, extradef) =>
            let
              val (dict, fresh, ty_dict, ty_fresh, funs, defs) = acc
              val funs = if extrafun = "" orelse
                Lib.mem extrafun funs then funs
                else extrafun :: funs
              val defs = if extradef = "" orelse
                Lib.mem extradef defs then defs
                else extradef :: defs
              val acc = (dict, fresh, ty_dict, ty_fresh, funs, defs)
            in
              (acc, name)
            end
          | NONE =>
            (* replace all other terms with a variable *)
            (* we even replace variables, to make sure there are no name
               clashes with either (i) variables generated by us, or (ii)
               reserved SMT-LIB names *)
            let val (dict, fresh, ty_dict, ty_fresh, funs, defs) = acc
            in
              case Redblackmap.peek (dict, tm) of
                SOME s => (acc, s)
              | NONE =>
                let val name = "v" ^ Int.toString fresh
                    val dict = Redblackmap.insert (dict, tm, name)
                    (* update the type dictionary as well *)
                    val ((ty_dict, ty_fresh), _) =
                      translate_type ((ty_dict, ty_fresh), Term.type_of tm)
                    val acc = (dict, fresh + 1, ty_dict, ty_fresh, funs, defs)
                in
                  (acc, name)
                end
            end (* translate_term *)

  (* Returns a string representation of the input goal in SMT-LIB file format,
     together with two dictionaries that map types and terms to identifiers
     used in the SMT-LIB representation.  The goal's conclusion is negated
     before translation into SMT-LIB format. *)
  fun goal_to_SmtLib goal : ((Type.hol_type, string) Redblackmap.dict *
                             (Term.term, string) Redblackmap.dict) *
                            string list =
  let
    val (As, g) = goal
    val g = boolSyntax.mk_neg g

    val empty_ty_dict = Redblackmap.mkDict Type.compare
    val empty_tm_dict = Redblackmap.mkDict Term.compare
    val acc = (empty_tm_dict, 0, empty_ty_dict, 0, [], [])

    val ((dict, _, ty_dict, _, funs, defs), smtlib_As_g) = Lib.foldl_map
      translate_term (acc, As @ [g])
    val (smtlib_As, smtlib_g) = Lib.front_last smtlib_As_g

    fun is_pred tm =
      Lib.snd (boolSyntax.strip_fun (Term.type_of tm)) = Type.bool

    val sorts = map Lib.snd (Redblackmap.listItems ty_dict)

    val (preds', funs') = List.partition (is_pred o Lib.fst)
                            (Redblackmap.listItems dict)
    val preds = map (fn (tm, name) =>
      let val (_, smtlib_ty) = translate_type ((ty_dict, 0), Term.type_of tm)
      in
        "(" ^ name ^ (if smtlib_ty ="" then "" else " " ^ smtlib_ty) ^ ")"
      end) preds'
    val funs' = map (fn (tm, name) =>
      let val (_, smtlib_ty) = translate_type ((ty_dict, 0), Term.type_of tm)
      in
        "(" ^ name ^ " " ^ smtlib_ty ^ ")"
      end) funs'
    val funs = map (fn s => "(" ^ s ^ ")") funs @ funs'
    val defs = List.map (fn s => ":assumption (" ^ s ^ ")\n") defs
    val smtlib_As = List.map (fn s => ":assumption " ^ s ^ "\n") smtlib_As
  in
    ((ty_dict, dict),
     ["(benchmark NAME\n",
      ":logic AUFLIA\n"]
     @ (if sorts = [] then []
        else ":extrasorts (" :: Lib.separate " " sorts @ [")\n"])
     @ (if funs = [] then []
        else ":extrafuns (" :: Lib.separate " " funs @ [")\n"])
     @ (if preds = [] then []
        else ":extrapreds (" :: Lib.separate " " preds @ [")\n"])
     @ defs
     @ smtlib_As @
     [":formula ", smtlib_g, "\n",
      ":status unknown)\n"])
  end

end
