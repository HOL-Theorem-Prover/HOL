structure Refute_ModelFinder_Names = struct
  type term = Term.term
  type hol_type = Type.hol_type

  val reserved_prefix = "refute$"
  val name_sep = "$"

  val numeral_prefix = reserved_prefix ^ "num" ^ name_sep
  val sel_prefix = reserved_prefix ^ "sel"
  val discr_prefix = reserved_prefix ^ "is" ^ name_sep
  val lfp_iterator_prefix = reserved_prefix ^ "lfpit" ^ name_sep
  val gfp_iterator_prefix = reserved_prefix ^ "gfpit" ^ name_sep
  val unrolled_prefix = reserved_prefix ^ "unroll" ^ name_sep
  val base_prefix = reserved_prefix ^ "base" ^ name_sep
  val step_prefix = reserved_prefix ^ "step" ^ name_sep
  val ubfp_prefix = reserved_prefix ^ "ubfp" ^ name_sep
  val lbfp_prefix = reserved_prefix ^ "lbfp" ^ name_sep
  val quot_normal_prefix = reserved_prefix ^ "qn" ^ name_sep
  val skolem_prefix = reserved_prefix ^ "sk"
  val special_prefix = reserved_prefix ^ "sp"
  val uncurry_prefix = reserved_prefix ^ "unc"
  val eval_prefix = reserved_prefix ^ "eval"
  val iter_var_prefix = "i"

  fun err function message =
    Feedback.mk_HOL_ERR "Refute_ModelFinder_Names" function message

  fun drop_prefix prefix string =
    String.extract (string, size prefix, NONE)

  fun strip_first_name_sep string =
    let
      val (left, right) =
        Substring.position name_sep (Substring.full string)
      val suffix =
        if Substring.isEmpty right then right
        else Substring.triml (size name_sep) right
    in
      (Substring.string left, Substring.string suffix)
    end

  (* HOL4's reserved prefix itself ends in name_sep.  Strip that namespace
     first, then recurse through the remaining generated-name layer. *)
  fun original_name string =
    if String.isPrefix reserved_prefix string then
      let
        val body = drop_prefix reserved_prefix string
        val (_, original) = strip_first_name_sep body
      in
        if original = "" then string else original_name original
      end
    else
      string

  fun sel_prefix_for index =
    sel_prefix ^ Int.toString index ^ name_sep

  fun skolem_prefix_for arity serial =
    skolem_prefix ^ Int.toString arity ^ "@" ^ Int.toString serial ^
    name_sep

  fun is_sel name =
    String.isPrefix discr_prefix name orelse
    String.isPrefix sel_prefix name

  fun has_generated_layer prefix name =
    if String.isPrefix prefix name then
      true
    else
      let val (_, suffix) = strip_first_name_sep name
      in suffix <> "" andalso has_generated_layer prefix suffix end

  fun is_skolem_name name = has_generated_layer skolem_prefix name

  fun sel_no_from_name name =
    if String.isPrefix discr_prefix name then
      ~1
    else if String.isPrefix sel_prefix name then
      let
        val suffix = drop_prefix sel_prefix name
        val (number, _) = strip_first_name_sep suffix
      in
        case Int.fromString number of
            SOME index => index
          | NONE => raise err "sel_no_from_name"
              ("malformed selector name: " ^ name)
      end
    else if name = "pair$SND" then
      1
    else
      0

  fun mk_reserved_var name ty =
    if String.isPrefix reserved_prefix name then
      Term.mk_var (name, ty)
    else
      raise err "mk_reserved_var" ("unreserved name: " ^ name)

  fun mk_numeral value ty =
    mk_reserved_var (numeral_prefix ^ Int.toString value) ty

  fun mk_discriminator constructor ty =
    mk_reserved_var (discr_prefix ^ constructor) ty

  fun mk_selector index constructor ty =
    if index < 0 then
      raise err "mk_selector" "negative selector index"
    else
      mk_reserved_var (sel_prefix_for index ^ constructor) ty

  fun mk_skolem arity serial original ty =
    if arity < 0 orelse serial < 0 then
      raise err "mk_skolem" "negative arity or serial"
    else
      mk_reserved_var (skolem_prefix_for arity serial ^ original) ty

  fun mk_eval serial ty =
    if serial < 0 then
      raise err "mk_eval" "negative serial"
    else
      mk_reserved_var (eval_prefix ^ Int.toString serial) ty

  fun unknown_marker ty = Term.mk_var ("?", ty)
  fun unrepresented_marker ty = Term.mk_var ("…", ty)
  fun unrepresented_marker_ascii ty = Term.mk_var ("...", ty)
  fun irrelevant_marker ty = Term.mk_var ("_", ty)

  fun fake_atom serial ty =
    if serial < 1 then
      raise err "fake_atom" "atom serial must be positive"
    else
      Term.mk_var ("a" ^ Int.toString serial, ty)

  fun variable_name variable = #1 (Term.dest_var variable)

  fun is_reserved_name name = String.isPrefix reserved_prefix name

  fun reserved_frees term =
    List.filter (is_reserved_name o variable_name)
      (Term.free_vars_lr term)

  fun reserved_variables term =
    List.filter (is_reserved_name o variable_name) (Term.all_vars term)

  fun assert_user_goal term =
    case reserved_variables term of
        [] => ()
      | variable :: _ =>
          raise err "assert_user_goal"
            ("reserved variable in user goal: " ^
             variable_name variable)

  fun theorem_terms theorem = Thm.concl theorem :: Thm.hyp theorem

  fun assert_no_reserved_in_theorem label theorem =
    case List.concat (map reserved_variables (theorem_terms theorem)) of
        [] => ()
      | variable :: _ =>
          raise err "assert_no_reserved_in_theorem"
            (label ^ ": reserved variable escaped: " ^
             variable_name variable)

  fun member_name name = List.exists (fn variable =>
    variable_name variable = name)

  (* Fabricated variables keep their stable names.  Any colliding user-goal
     free is renamed first, using HOL4's name-based variant discipline. *)
  fun rename_colliding_goal_vars fabricated goal =
    let
      val _ = assert_user_goal goal
      val goal_frees = Term.free_vars_lr goal

      fun rename (variable, (avoids, substitutions, renaming)) =
        if member_name (variable_name variable) fabricated then
          let
            val fresh = Term.variant avoids variable
            val substitution = {redex = variable, residue = fresh}
          in
            (fresh :: avoids, substitution :: substitutions,
             (variable, fresh) :: renaming)
          end
        else
          (avoids, substitutions, renaming)

      val (_, substitutions, renaming) =
        List.foldl rename (fabricated @ goal_frees, [], []) goal_frees
    in
      (Term.subst (rev substitutions) goal, rev renaming)
    end
end

structure Refute_ModelFinder_HOL = struct
  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type
  type kname = KernelSig.kernelname

  type const_table = term list KNametab.table
  type special_fun = (term * int list * term list) * term
  type wf_cache = (term * (bool * bool)) list
  type type_operator = {Thy : string, Tyop : string}
  type ersatz = {original : kname, replacement : kname}
  type codatatype_info =
    {tyop : type_operator, case_const : term, constructors : term list}
  type quotient_info =
    {qty : hol_type, rty : hol_type, abs : term, rep : term,
     equiv_thm : thm, partial : bool}
  type frac_info = {tyop : type_operator, ersatz : ersatz list}

  (* M3 leaves these session registries empty.  Their record shapes are the
     hooks for M4; raw typedef harvesting is deliberately not attempted. *)
  val codatatype_registry = ref ([] : codatatype_info list)
  val quotient_registry = ref ([] : quotient_info list)
  val frac_registry = ref ([] : frac_info list)
  val ersatz_registry = ref ([] : ersatz list)

  type mf_context =
    {max_bisim_depth : int,
     boxes : (hol_type option * bool option) list,
     wfs : (term option * bool option) list,
     user_axioms : bool option,
     debug : bool,
     whacks : term list,
     binary_ints : bool option,
     destroy_constrs : bool,
     specialize : bool,
     star_linear_preds : bool,
     total_consts : bool option,
     needs : term list option,
     tac_timeout : Time.time,
     evals : term list,
     case_names : (kname * int) list,
     def_tables : const_table * const_table,
     nondef_table : const_table,
     nondefs : term list,
     simp_table : const_table ref,
     psimp_table : const_table,
     choice_spec_table : const_table,
     intro_table : const_table,
     ersatz_table : ersatz list,
     skolems : (string * string list) list ref,
     special_funs : special_fun list ref,
     wf_cache : wf_cache ref,
     constr_cache : (hol_type * term list) list ref}

  (* Upstream's ground theorem hash and vestigial unrolled-predicate ref are
     deliberately absent (PLAN_M3 minor decision 22). *)

  fun err function message =
    Feedback.mk_HOL_ERR "Refute_ModelFinder_HOL" function message

  fun const_key constant =
    let val {Thy, Name, ...} = Term.dest_thy_const constant
    in {Thy = Thy, Name = Name} end

  fun same_key left right =
    KernelSig.name_compare (left, right) = EQUAL

  fun table_lookup table constant =
    case Lib.total const_key constant of
        SOME key => Option.getOpt (KNametab.lookup table key, [])
      | NONE => []

  fun table_append key value table =
    let val old = Option.getOpt (KNametab.lookup table key, [])
    in KNametab.update (key, old @ [value]) table end

  fun theorem_term theorem =
    boolSyntax.list_mk_imp (Thm.hyp theorem, Thm.concl theorem)

  fun clauses_of theorem = map theorem_term (Drule.CONJUNCTS theorem)

  fun term_under_def term =
    if boolSyntax.is_forall term then
      term_under_def (#2 (boolSyntax.dest_forall term))
    else if boolSyntax.is_imp term then
      term_under_def (#2 (boolSyntax.dest_imp term))
    else if boolSyntax.is_eq term then
      term_under_def (#1 (boolSyntax.dest_eq term))
    else if Term.is_abs term then
      term_under_def (Term.body term)
    else if Term.is_comb term then
      term_under_def (#1 (Term.dest_comb term))
    else
      term

  fun extensional_equal avoids left right =
    case Lib.total Type.dom_rng (Term.type_of left) of
        NONE => boolSyntax.mk_eq (left, right)
      | SOME (domain, _) =>
          let
            val free = List.concat (map Term.free_vars_lr
              (left :: right :: avoids))
            val variable = Term.variant free (Term.mk_var ("x", domain))
          in
            extensional_equal (variable :: avoids)
              (Term.mk_comb (left, variable))
              (Term.mk_comb (right, variable))
          end

  fun equationalize_term label term =
    let
      val (variables, body) = boolSyntax.strip_forall term
      val (premises, conclusion) = boolSyntax.strip_imp body
      val equation =
        case Lib.total boolSyntax.dest_eq conclusion of
            SOME (left, right) =>
              extensional_equal (variables @ premises) left right
          | NONE => boolSyntax.mk_eq (conclusion, boolSyntax.T)
    in
      SOME (boolSyntax.list_mk_forall
        (variables, boolSyntax.list_mk_imp (premises, equation)))
    end
    handle HOL_ERR _ =>
      (Feedback.HOL_WARNING "Refute_ModelFinder_HOL"
         "equationalize_term" ("ignoring " ^ label ^ " non-equation");
       NONE)

  fun pair_for_prop prop =
    let val constant = term_under_def prop
    in
      if Term.is_const constant then (const_key constant, prop)
      else raise err "pair_for_prop" "no constant under definition"
    end

  fun def_table_for props =
    List.foldl (fn (prop, table) =>
      let val (key, value) = pair_for_prop prop
      in table_append key value table end) KNametab.empty props

  fun matching_instantiations constant prop =
    let
      val key = const_key constant
      fun is_matching term =
        Term.is_const term andalso same_key (const_key term) key
      fun instantiate occurrence =
        let
          val theta = Type.match_type (Term.type_of occurrence)
            (Term.type_of constant)
          val result = Term.inst theta prop
        in
          if Term.aconv (term_under_def result) constant then SOME result
          else NONE
        end handle HOL_ERR _ => NONE
    in
      List.mapPartial instantiate
        (HolKernel.find_terms is_matching prop)
    end

  fun aconv_member term = List.exists (Term.aconv term)

  fun distinct_terms terms =
    List.foldl (fn (term, result) =>
      if aconv_member term result then result else result @ [term]) [] terms

  val built_in_consts =
    [({Thy = "bool", Name = "~"}, 1),
     ({Thy = "bool", Name = "F"}, 0),
     ({Thy = "bool", Name = "T"}, 0),
     ({Thy = "bool", Name = "!"}, 1),
     ({Thy = "bool", Name = "?"}, 1),
     ({Thy = "min", Name = "="}, 1),
     ({Thy = "bool", Name = "/\\"}, 2),
     ({Thy = "bool", Name = "\\/"}, 2),
     ({Thy = "min", Name = "==>"}, 2),
     ({Thy = "bool", Name = "COND"}, 3),
     ({Thy = "bool", Name = "LET"}, 2),
     ({Thy = "bool", Name = "literal_case"}, 2),
     ({Thy = "pair", Name = ","}, 2),
     ({Thy = "pair", Name = "FST"}, 1),
     ({Thy = "pair", Name = "SND"}, 1),
     ({Thy = "bool", Name = "IN"}, 2),
     ({Thy = "pred_set", Name = "FINITE"}, 1),
     ({Thy = "refute", Name = "unknown"}, 0),
     ({Thy = "refute", Name = "is_unknown"}, 1),
     ({Thy = "refute", Name = "safe_The"}, 1),
     ({Thy = "num", Name = "SUC"}, 0),
     ({Thy = "integer", Name = "Num"}, 0),
     (* HOL4 numeral syntax is recognized directly.  Keeping its binary
        skeleton built in prevents accidental expansion to unary terms. *)
     ({Thy = "arithmetic", Name = "NUMERAL"}, 0),
     ({Thy = "arithmetic", Name = "BIT1"}, 0),
     ({Thy = "arithmetic", Name = "BIT2"}, 0),
     ({Thy = "arithmetic", Name = "ZERO"}, 0)]

  val num_type = Type.mk_thy_type
    {Thy = "num", Tyop = "num", Args = []}
  val int_type = Type.mk_thy_type
    {Thy = "integer", Tyop = "int", Args = []}

  fun fun_type (domain, range) = Type.-->(domain, range)
  fun binary_type argument result =
    fun_type (argument, fun_type (argument, result))

  val built_in_typed_consts =
    [(({Thy = "num", Name = "0"}, num_type), 0),
     (({Thy = "arithmetic", Name = "+"},
       binary_type num_type num_type), 0),
     (({Thy = "arithmetic", Name = "-"},
       binary_type num_type num_type), 0),
     (({Thy = "arithmetic", Name = "*"},
       binary_type num_type num_type), 0),
     (({Thy = "arithmetic", Name = "DIV"},
       binary_type num_type num_type), 0),
     (({Thy = "arithmetic", Name = "MOD"},
       binary_type num_type num_type), 0),
     (({Thy = "prim_rec", Name = "<"},
       binary_type num_type Type.bool), 2),
     (({Thy = "arithmetic", Name = "<="},
       binary_type num_type Type.bool), 2),
     (({Thy = "integer", Name = "int_of_num"},
       fun_type (num_type, int_type)), 0),
     (({Thy = "integer", Name = "int_add"},
       binary_type int_type int_type), 0),
     (({Thy = "integer", Name = "int_sub"},
       binary_type int_type int_type), 0),
     (({Thy = "integer", Name = "int_mul"},
       binary_type int_type int_type), 0),
     (({Thy = "integer", Name = "int_div"},
       binary_type int_type int_type), 0),
     (({Thy = "integer", Name = "int_mod"},
       binary_type int_type int_type), 0),
     (({Thy = "integer", Name = "int_neg"},
       fun_type (int_type, int_type)), 0),
     (({Thy = "integer", Name = "int_lt"},
       binary_type int_type Type.bool), 2),
     (({Thy = "integer", Name = "int_le"},
       binary_type int_type Type.bool), 2)]

  fun generic_built_in_arity key =
    Option.map #2 (List.find (fn (other, _) => same_key key other)
      built_in_consts)

  fun typed_built_in_arity key ty =
    Option.map #2 (List.find (fn ((other, other_ty), _) =>
      same_key key other andalso ty = other_ty) built_in_typed_consts)

  fun result_type_after 0 ty = ty
    | result_type_after count ty =
        result_type_after (count - 1) (#2 (Type.dom_rng ty))

  fun arity_of_built_in_const constant =
    let
      val key = const_key constant
      val ty = Term.type_of constant
    in
      if same_key key {Thy = "bool", Name = "COND"} andalso
         result_type_after 3 ty = Type.bool then
        NONE
      else
        case generic_built_in_arity key of
            SOME arity => SOME arity
          | NONE => typed_built_in_arity key ty
    end handle HOL_ERR _ => NONE

  fun is_built_in_const constant =
    Option.isSome (arity_of_built_in_const constant)

  (* Boolean-valued COND is not arity-limited because the nut layer handles
     fully applied Boolean conditionals.  It is nevertheless on the built-in
     table and must not be expanded through HOL4's choice-based COND_DEF. *)
  fun is_never_unfold_const constant =
    let
      val key = const_key constant
      val ty = Term.type_of constant
    in
      Option.isSome (generic_built_in_arity key) orelse
      Option.isSome (typed_built_in_arity key ty)
    end handle HOL_ERR _ => false

  fun def_props_for_const table constant =
    if is_built_in_const constant then []
    else
      table_lookup table constant
      |> List.mapPartial (fn prop =>
           case matching_instantiations constant prop of
               first :: _ => SOME first
             | [] => NONE)

  fun all_instantiations constant prop =
    let
      val key = const_key constant
      fun is_matching term =
        Term.is_const term andalso same_key (const_key term) key
      fun instantiate occurrence =
        SOME (Term.inst
          (Type.match_type (Term.type_of occurrence)
             (Term.type_of constant)) prop)
        handle HOL_ERR _ => NONE
    in
      HolKernel.find_terms is_matching prop
      |> List.mapPartial instantiate
      |> distinct_terms
    end

  fun nondef_props_for_const table constant =
    List.concat (map (all_instantiations constant)
      (table_lookup table constant))
    |> distinct_terms

  fun normalized_rhs_of prop =
    let
      val (_, body) = boolSyntax.strip_forall prop
      val (premises, conclusion) = boolSyntax.strip_imp body
      val (left, right) = boolSyntax.dest_eq conclusion
      val (_, arguments) = HolKernel.strip_comb left
      fun distinct_variables [] = true
        | distinct_variables (variable :: rest) =
            Term.is_var variable andalso
            not (List.exists (Term.aconv variable) rest) andalso
            distinct_variables rest
    in
      if null premises andalso distinct_variables arguments then
        SOME (Term.list_mk_abs (arguments, right))
      else NONE
    end handle HOL_ERR _ => NONE

  fun get_def_of_const table constant =
    case rev (def_props_for_const table constant) of
        latest :: _ => normalized_rhs_of latest
      | [] => NONE

  fun def_of_const_ext
        ({def_tables = (unfold_table, fallback_table), ...} : mf_context)
        constant =
    case Lib.total Term.dest_var constant of
        SOME (name, _) =>
          if Refute_ModelFinder_Names.is_reserved_name name then NONE
          else Option.map (fn definition => (false, definition))
            (get_def_of_const fallback_table constant)
      | NONE =>
          (case get_def_of_const unfold_table constant of
               SOME definition => SOME (true, definition)
             | NONE => Option.map (fn definition => (false, definition))
                 (get_def_of_const fallback_table constant))

  fun def_of_const context = Option.map #2 o def_of_const_ext context

  fun constants_in term =
    HolKernel.find_terms Term.is_const term
    |> map (fn constant => (const_key constant, constant))
    |> List.foldl (fn ((key, constant), result) =>
         if List.exists (fn (other, _) => same_key key other) result then
           result
         else result @ [(key, constant)]) []

  fun nondef_table_for props =
    List.foldl (fn (prop, table) =>
      List.foldl (fn ((key, _), result) => table_append key prop result)
        table (constants_in prop)) KNametab.empty props

  fun oldest_first_theories () =
    Theory.ancestry "-" @ [Theory.current_theory ()]

  fun definitions_of theory =
    if theory = Theory.current_theory () then Theory.current_definitions ()
    else DB.definitions theory

  fun axioms_of theory =
    if theory = Theory.current_theory () then Theory.current_axioms ()
    else DB.axioms theory

  fun presentation_key {const, ...} = const_key const

  fun has_presentation presentations key =
    List.exists (fn presentation =>
      same_key (presentation_key presentation) key) presentations

  fun standard_user_props presentations =
    List.concat (List.mapPartial (fn {thm, ...} =>
      case thm of
          DefnBase.STDEQNS theorem => SOME (clauses_of theorem)
        | DefnBase.OTHER _ => NONE) presentations)

  (* Clean DefnBase equations take precedence.  In particular, this keeps
     TotalDefn functions on their STDEQNS rules instead of exposing WFREC;
     raw DB definitions fill only constants with no user presentation. *)
  fun raw_standard_props presentations =
    let
      fun from_theorem (_, theorem) =
        let
          fun usable (key, equation) =
            if has_presentation presentations key then []
            else clauses_of equation
        in
          List.concat (map usable (DefnBase.defn_eqns theorem))
        end handle DefnBase.nonstdform => []
    in
      List.concat (map (fn theory =>
        List.concat (map from_theorem (definitions_of theory)))
        (oldest_first_theories ()))
    end

  fun choice_spec_entries () =
    let
      fun same_conclusion left right =
        Term.aconv (Thm.concl left) (Thm.concl right)
      fun eligible theory theorem (_, constant) =
        #Thy (const_key constant) = theory andalso
        (case DefnBase.lookup_userdef constant of
             SOME {thm = DefnBase.STDEQNS _, ...} => false
           | SOME {thm = DefnBase.OTHER other, ...} =>
               same_conclusion theorem other
           | NONE => true)
      fun from_definition theory (_, theorem) =
        ((DefnBase.constants_of_defn theorem; [])
         handle DefnBase.nonstdform =>
           constants_in (theorem_term theorem)
           |> List.filter (eligible theory theorem)
           |> map (fn (key, _) => (key, theorem_term theorem)))
    in
      List.concat (map (fn theory =>
        List.concat (map (from_definition theory)
          (definitions_of theory))) (oldest_first_theories ()))
    end

  fun raw_theorem_set_props set =
    rev (#getDB set ()) |> List.concat o map clauses_of

  fun theorem_set_props set label =
    raw_theorem_set_props set
    |> List.mapPartial (equationalize_term label)

  fun user_simp_props presentations =
    standard_user_props presentations
    |> List.mapPartial (equationalize_term "user definition")

  fun make_tables () =
    let
      val presentations = DefnBase.current_userdefs ()
      val fallback_props = standard_user_props presentations @
        raw_standard_props presentations
      val unfold_props = clauses_of (DB.fetch "bool"
        "EXISTS_UNIQUE_DEF") @
        raw_theorem_set_props Refute_Core.refute_unfold
      val simp_props = user_simp_props presentations @
        theorem_set_props Refute_Core.refute_simp "refute_simp"
      val psimp_props =
        theorem_set_props Refute_Core.refute_psimp "refute_psimp"
      val choice_table = List.foldl (fn ((key, prop), table) =>
        table_append key prop table) KNametab.empty
        (choice_spec_entries ())
    in
      {def_tables = (def_table_for unfold_props,
                     def_table_for fallback_props),
       simp_table = def_table_for simp_props,
       psimp_table = def_table_for psimp_props,
       choice_spec_table = choice_table}
    end

  val core_theories = "bool" :: Theory.ancestry "bool"

  fun is_core_theory theory = Lib.mem theory core_theories

  fun all_nondefs_of () =
    oldest_first_theories ()
    |> List.filter (not o is_core_theory)
    |> List.concat o map (map (theorem_term o #2) o axioms_of)

  fun is_poly_term term = not (null (Term.type_vars_in_term term))

  val const_nondef_table = nondef_table_for

  fun choice_spec_props_for_const
        ({choice_spec_table, ...} : mf_context) constant =
    nondef_props_for_const choice_spec_table constant

  fun is_choice_spec_fun context constant =
    not (null (choice_spec_props_for_const context constant))

  fun is_raw_equational_fun
        ({simp_table, psimp_table, ...} : mf_context) constant =
    not (null (def_props_for_const (!simp_table) constant)) orelse
    not (null (def_props_for_const psimp_table constant))

  fun equational_fun_axioms
        (context as {simp_table, psimp_table, ...} : mf_context) constant =
    case def_props_for_const (!simp_table) constant of
        [] =>
          (case def_props_for_const psimp_table constant of
               [] =>
                 (case def_of_const context constant of
                      SOME definition =>
                        (case equationalize_term "definition"
                           (boolSyntax.mk_eq (constant, definition)) of
                             SOME equation => [equation]
                           | NONE => [])
                    | NONE => [])
             | psimps => psimps)
      | simps => simps

  fun is_equational_fun_surely_complete context constant =
    case equational_fun_axioms context constant of
        [equation] =>
          let
            val (_, body) = boolSyntax.strip_forall equation
            val (premises, conclusion) = boolSyntax.strip_imp body
          in
            null premises andalso
            (case Lib.total boolSyntax.dest_eq conclusion of
                 SOME (left, _) =>
                   List.all Term.is_var (#2 (HolKernel.strip_comb left))
               | NONE => false)
          end
      | _ => false

  fun type_operator_of ty =
    let val {Thy, Tyop, ...} = Type.dest_thy_type ty
    in {Thy = Thy, Tyop = Tyop} end

  fun same_type_operator (left : type_operator) right =
    #Thy left = #Thy right andalso #Tyop left = #Tyop right

  fun has_type_operator project registry ty =
    let val operator = type_operator_of ty
    in
      List.exists (fn entry =>
        same_type_operator (project entry) operator) (!registry)
    end handle HOL_ERR _ => false

  fun is_fun_type ty = Option.isSome (Lib.total Type.dom_rng ty)

  fun is_pair_type ty =
    case Lib.total Type.dest_thy_type ty of
        SOME {Thy = "pair", Tyop = "prod", ...} => true
      | _ => false

  fun is_boolean_type ty =
    case Lib.total Type.dest_thy_type ty of
        SOME {Thy = "min", Tyop = "bool", ...} => true
      | _ => false

  fun is_integer_type ty =
    case Lib.total Type.dest_thy_type ty of
        SOME {Thy = "num", Tyop = "num", ...} => true
      | SOME {Thy = "integer", Tyop = "int", ...} => true
      | _ => false

  fun is_interpreted_type ty =
    case Lib.total Type.dest_thy_type ty of
        SOME {Thy = "min", Tyop = "bool", ...} => true
      | SOME {Thy = "min", Tyop = "fun", ...} => true
      | SOME {Thy = "pair", Tyop = "prod", ...} => true
      | SOME {Thy = "num", Tyop = "num", ...} => true
      | SOME {Thy = "integer", Tyop = "int", ...} => true
      | _ => false

  fun is_raw_free_datatype ty =
    case TypeBase.fetch ty of
        SOME info => not (null (TypeBasePure.constructors_of info))
      | NONE => false
    handle HOL_ERR _ => false

  fun is_codatatype ty = has_type_operator #tyop codatatype_registry ty

  fun is_quot_type ty =
    let val operator = type_operator_of ty
    in
      List.exists (fn {qty, ...} =>
        same_type_operator (type_operator_of qty) operator)
        (!quotient_registry)
    end handle HOL_ERR _ => false

  fun is_frac_type ty = has_type_operator #tyop frac_registry ty

  (* Raw typedefs and min$ind are intentionally unsupported in M3
     (PLAN_M3 minor decision 22). *)
  fun is_data_type ty =
    not (is_interpreted_type ty) andalso
    (is_raw_free_datatype ty orelse is_codatatype ty orelse
     is_quot_type ty orelse is_frac_type ty)

  fun registered_constructors ty =
    let val operator = type_operator_of ty
    in
      case List.find (fn {tyop, ...} =>
             same_type_operator tyop operator) (!codatatype_registry) of
          SOME {constructors, ...} =>
            map (fn constructor =>
              Term.inst
                (Type.match_type
                  (#2 (boolSyntax.strip_fun (Term.type_of constructor))) ty)
                constructor) constructors
        | NONE => []
    end handle HOL_ERR _ => []

  fun uncached_data_type_constrs ty =
    if is_interpreted_type ty then []
    else
      case registered_constructors ty of
          constructors as _ :: _ => constructors
        | [] =>
            (case TypeBase.fetch ty of
                 SOME info => map (TypeBasePure.cinst ty)
                   (TypeBasePure.constructors_of info)
               | NONE => [])

  fun data_type_constrs
        ({constr_cache, ...} : mf_context) ty =
    case List.find (fn (cached, _) => cached = ty) (!constr_cache) of
        SOME (_, constructors) => constructors
      | NONE =>
          let val constructors = uncached_data_type_constrs ty
          in
            constr_cache := (ty, constructors) :: !constr_cache;
            constructors
          end

  fun registered_constructor term =
    List.exists (fn {constructors, ...} =>
      List.exists (fn constructor =>
        Term.same_const constructor term) constructors)
      (!codatatype_registry)

  fun is_nonfree_constr term =
    TypeBase.is_constructor term orelse registered_constructor term

  val is_free_constr = is_nonfree_constr

  fun is_constr term =
    is_nonfree_constr term andalso
    not (is_interpreted_type (#2 (boolSyntax.strip_fun
      (Term.type_of term))))

  fun find_field which term =
    let
      val key = const_key term
      fun search_type info =
        let
          val ty = TypeBasePure.ty_of info
          fun search (_, []) = NONE
            | search (index, (field, data) :: rest) =
                if same_key (const_key (which data)) key then
                  SOME {record_ty = ty, index = index,
                        field = field, info = data}
                else search (index + 1, rest)
        in
          search (0, TypeBasePure.fields_of info)
        end
    in
      List.find Option.isSome (map search_type (TypeBase.elts ()))
      |> Option.mapPartial (fn item => item)
    end handle HOL_ERR _ => NONE

  fun dest_record_get term = find_field #accessor term
  fun dest_record_update term = find_field #fupd term
  fun is_record_get term = Option.isSome (dest_record_get term)
  fun is_record_update term = Option.isSome (dest_record_update term)

  fun is_named_const expected term =
    Term.is_const term andalso same_key (const_key term) expected

  fun is_descr term =
    is_named_const {Thy = "min", Name = "@"} term orelse
    is_named_const {Thy = "refute", Name = "safe_The"} term

  fun is_exists_unique term =
    is_named_const {Thy = "bool", Name = "?!"} term

  fun exists_unique_def () = Thm.concl (DB.fetch "bool"
    "EXISTS_UNIQUE_DEF")

  fun numeral_value term =
    if Term.type_of term = int_type then
      SOME (intSyntax.int_of_term term)
      handle HOL_ERR _ => NONE
    else if Term.type_of term = num_type then
      SOME (Arbint.fromNat (numSyntax.dest_numeral term))
      handle HOL_ERR _ => NONE
    else
      NONE

  fun is_numeral term = Option.isSome (numeral_value term)

  val builtin_ersatz =
    [{original = {Thy = "pred_set", Name = "CARD"},
      replacement = {Thy = "refute", Name = "card'"}}]

  fun register_ersatz replacement =
    let
      fun same_original ({original, ...} : ersatz) =
        same_key original (#original replacement)
    in
      ersatz_registry := replacement ::
        List.filter (not o same_original) (!ersatz_registry)
    end

  fun current_ersatz_table () =
    List.foldl (fn (entry, table) =>
      if List.exists (fn ({original, ...} : ersatz) =>
           same_key original (#original entry)) table then table
      else entry :: table) (!ersatz_registry) builtin_ersatz

  fun case_names () =
    let
      fun entry info =
        let
          val ty = TypeBasePure.ty_of info
          val constructors = TypeBasePure.constructors_of info
          val case_const = TypeBasePure.case_const_of info
        in
          if null constructors orelse not (is_data_type ty) then NONE
          else SOME (const_key case_const, length constructors)
        end handle HOL_ERR _ => NONE
    in
      List.mapPartial entry (TypeBase.elts ()) @
      map (fn {case_const, constructors, ...} =>
        (const_key case_const, length constructors))
        (!codatatype_registry)
    end

  fun constructor_name constructor =
    let val {Thy, Name, ...} = Term.dest_thy_const constructor
    in Thy ^ "$" ^ Name end

  fun constructor_arg_types constructor =
    #1 (boolSyntax.strip_fun (Term.type_of constructor))

  fun constructor_result_type constructor =
    #2 (boolSyntax.strip_fun (Term.type_of constructor))

  fun is_pair_constructor constructor =
    is_named_const {Thy = "pair", Name = ","} constructor

  fun constructors_for context ty =
    if is_pair_type ty then
      map (TypeBasePure.cinst ty) (TypeBase.constructors_of ty)
    else
      data_type_constrs context ty

  fun is_suc_constructor constructor =
    is_named_const {Thy = "num", Name = "SUC"} constructor

  fun discriminator_term context constructor =
    let
      val data_ty = constructor_result_type constructor
      val constructors = constructors_for context data_ty
    in
      if is_suc_constructor constructor then
        let
          val value = Term.mk_var ("n", data_ty)
          val test = boolSyntax.mk_neg
            (boolSyntax.mk_eq (value, numSyntax.zero_tm))
        in
          Term.mk_abs (value, test)
        end
      else if length constructors < 2 then
        let val value = Term.mk_var ("x", data_ty)
        in Term.mk_abs (value, boolSyntax.T) end
      else
        Refute_ModelFinder_Names.mk_discriminator
          (constructor_name constructor) (fun_type (data_ty, Type.bool))
    end

  fun s_betapply (function, argument) =
    if Term.is_abs function then
      Term.beta_conv (Term.mk_comb (function, argument))
    else
      Term.mk_comb (function, argument)

  fun s_betapplys (function, arguments) =
    List.foldl (fn (argument, result) =>
      s_betapply (result, argument)) function arguments

  fun discriminate_value context constructor value =
    let val (head, _) = HolKernel.strip_comb value
    in
      if Term.is_const head andalso
         Term.same_const constructor head then
        boolSyntax.T
      else if Term.is_const head andalso is_nonfree_constr head then
        boolSyntax.F
      else
        s_betapply (discriminator_term context constructor, value)
    end

  fun num_factors_in_type ty =
    if is_pair_type ty then
      let val (left, right) = pairSyntax.dest_prod ty
      in num_factors_in_type left + num_factors_in_type right end
    else
      1

  fun selector_term_for_constructor constructor argument_index =
    let
      val argument_tys = constructor_arg_types constructor
      val data_ty = constructor_result_type constructor
      val constructor_id = constructor_name constructor
      val first_index = List.foldl (fn (ty, total) =>
        total + num_factors_in_type ty) 0
        (List.take (argument_tys, argument_index))
      fun selector index result_ty =
        Refute_ModelFinder_Names.mk_selector index constructor_id
          (fun_type (data_ty, result_ty))
      fun build index ty value =
        if is_pair_type ty then
          let
            val (left_ty, right_ty) = pairSyntax.dest_prod ty
            val left = build index left_ty value
            val right = build (index + num_factors_in_type left_ty)
              right_ty value
          in
            pairSyntax.mk_pair (left, right)
          end
        else
          Term.mk_comb (selector index ty, value)
      val value = Term.mk_var ("x", data_ty)
    in
      if is_suc_constructor constructor then
        Term.mk_abs (value,
          numSyntax.mk_minus (value,
            numSyntax.mk_numeral Arbnum.one))
      else if is_pair_constructor constructor then
        let
          val selected =
            if argument_index = 0 then pairSyntax.mk_fst value
            else if argument_index = 1 then pairSyntax.mk_snd value
            else raise err "selector_term_for_constructor"
              "pair selector index out of range"
        in
          Term.mk_abs (value, selected)
        end
      else
        Term.mk_abs (value,
          build first_index (List.nth (argument_tys, argument_index)) value)
    end

  fun unknown_value ty =
    Term.mk_thy_const {Thy = "refute", Name = "unknown", Ty = ty}

  fun select_nth_constr_arg context constructor value index result_ty =
    let
      val (head, arguments) = HolKernel.strip_comb value
    in
      if Term.is_const head andalso
         Term.same_const constructor head andalso
         index < length arguments then
        List.nth (arguments, index)
      else if Term.is_const head andalso is_nonfree_constr head then
        unknown_value result_ty
      else
        s_betapply
          (selector_term_for_constructor constructor index, value)
    end

  fun generated_selector_argument constructor term =
    let
      fun direct term =
        let
          val (head, arguments) = HolKernel.strip_comb term
        in
          if length arguments <> 1 then NONE
          else if is_pair_constructor constructor andalso
                  Term.is_const head andalso
                  (is_named_const {Thy = "pair", Name = "FST"} head orelse
                   is_named_const {Thy = "pair", Name = "SND"} head) then
            SOME (hd arguments)
          else
            case Lib.total Term.dest_var head of
                SOME (name, _) =>
                  if Refute_ModelFinder_Names.is_sel name andalso
                     Refute_ModelFinder_Names.original_name name =
                       constructor_name constructor then
                    SOME (hd arguments)
                  else
                    NONE
              | NONE => NONE
        end
      fun search term =
        case direct term of
            result as SOME _ => result
          | NONE =>
              if pairSyntax.is_pair term then
                let val (left, right) = pairSyntax.dest_pair term
                in
                  case search left of
                      result as SOME _ => result
                    | NONE => search right
                end
              else
                NONE
    in
      search term
    end

  fun eta_contract term =
    if Term.is_abs term then
      let
        val (variable, body) = Term.dest_abs term
        val contracted_body = eta_contract body
      in
        if Term.is_comb contracted_body andalso
           Term.aconv (#2 (Term.dest_comb contracted_body)) variable andalso
           not (Term.free_in variable
             (#1 (Term.dest_comb contracted_body))) then
          eta_contract (#1 (Term.dest_comb contracted_body))
        else
          Term.mk_abs (variable, contracted_body)
      end
    else if Term.is_comb term then
      let val (function, argument) = Term.dest_comb term
      in Term.mk_comb (eta_contract function, eta_contract argument) end
    else
      term

  fun construct_value context constructor raw_arguments =
    let val arguments = map eta_contract raw_arguments
    in
      case arguments of
          [] => constructor
        | first :: _ =>
            (case generated_selector_argument constructor first of
                 SOME value =>
                   if Term.type_of value <>
                      constructor_result_type constructor then
                     Term.list_mk_comb (constructor, arguments)
                   else
                     let
                       val argument_tys = constructor_arg_types constructor
                       val expected = List.tabulate (length argument_tys,
                         fn index => select_nth_constr_arg context constructor
                           value index (List.nth (argument_tys, index)))
                     in
                       if ListPair.allEq (fn (left, right) =>
                            Term.aconv left right) (arguments, expected) then
                         value
                       else
                         Term.list_mk_comb (constructor, arguments)
                     end
               | NONE => Term.list_mk_comb (constructor, arguments))
    end

  fun constr_expand context ty value =
    let val (head, _) = HolKernel.strip_comb value
    in
      if Term.is_const head andalso is_nonfree_constr head then value
      else
        let
          val constructor = hd (constructors_for context ty)
          val argument_tys = constructor_arg_types constructor
          val arguments = List.tabulate (length argument_tys,
            fn index => select_nth_constr_arg context constructor value index
              (List.nth (argument_tys, index)))
        in
          Term.list_mk_comb (constructor, arguments)
        end
    end

  fun smart_conj (left, right) =
    if Term.aconv left boolSyntax.T then right
    else if Term.aconv right boolSyntax.T then left
    else if Term.aconv left boolSyntax.F orelse
            Term.aconv right boolSyntax.F then boolSyntax.F
    else boolSyntax.mk_conj (left, right)

  fun smart_imp (left, right) =
    if Term.aconv left boolSyntax.F orelse
       Term.aconv right boolSyntax.T then boolSyntax.T
    else if Term.aconv left boolSyntax.T then right
    else boolSyntax.mk_imp (left, right)

  fun case_body context constructor function value =
    let
      val argument_tys = constructor_arg_types constructor
      val arguments = List.tabulate (length argument_tys,
        fn index => select_nth_constr_arg context constructor value index
          (List.nth (argument_tys, index)))
    in
      s_betapplys (function, arguments)
    end

  fun optimized_case_value context data_ty result_ty functions value =
    let
      val constructors = constructors_for context data_ty
      val cases = ListPair.map (fn (function, constructor) =>
        (case_body context constructor function value,
         discriminate_value context constructor value))
        (functions, constructors)
      fun nonboolean [(body, _)] = body
        | nonboolean ((body, guard) :: rest) =
            if Term.aconv guard boolSyntax.T then body
            else if Term.aconv guard boolSyntax.F then nonboolean rest
            else boolSyntax.mk_cond (guard, body, nonboolean rest)
        | nonboolean [] = raise err "optimized_case_value" "no cases"
    in
      if result_ty = Type.bool then
        List.foldl (fn ((body, guard), result) =>
          smart_conj (smart_imp (guard, body), result)) boolSyntax.T cases
      else
        nonboolean cases
    end

  fun optimized_case_def context _ data_ty result_ty functions =
    let
      val avoids = List.concat (map Term.all_vars functions)
      val value = Term.variant avoids (Term.mk_var ("x", data_ty))
      val body = optimized_case_value context data_ty result_ty
        functions value
    in
      Term.mk_abs (value, body)
    end

  fun optimized_record_get context accessor record =
    case dest_record_get accessor of
        SOME {index, ...} =>
          let
            val record_ty = Term.type_of record
            val constructor = hd (data_type_constrs context record_ty)
            val result_ty = #2 (Type.dom_rng (Term.type_of accessor))
          in
            select_nth_constr_arg context constructor record index result_ty
          end
      | NONE => raise err "optimized_record_get" "not a record accessor"

  fun optimized_record_update context updater update record =
    case dest_record_update updater of
        SOME {index = updated_index, ...} =>
          let
            val input_ty = Term.type_of record
            val output_ty = result_type_after 2 (Term.type_of updater)
            val input_constructor = hd
              (data_type_constrs context input_ty)
            val output_constructor = hd
              (data_type_constrs context output_ty)
            val input_argument_tys =
              constructor_arg_types input_constructor
            fun argument index =
              let
                val old = select_nth_constr_arg context input_constructor
                  record index (List.nth (input_argument_tys, index))
              in
                if index = updated_index then s_betapply (update, old)
                else old
              end
            val arguments =
              List.tabulate (length input_argument_tys, argument)
          in
            construct_value context output_constructor arguments
          end
      | NONE => raise err "optimized_record_update" "not a record updater"

  fun assignment_lookup assigns ty =
    Option.map #2 (List.find (fn (other, _) => other = ty) assigns)

  fun is_itself_type ty =
    case Lib.total Type.dest_thy_type ty of
        SOME {Thy = "bool", Tyop = "itself", ...} => true
      | _ => false

  fun cart_type_parts ty = Lib.total fcpSyntax.dest_cart_type ty

  fun cart_dimension index_ty =
    Arbnum.toInt (fcpLib.index_to_num index_ty)

  fun word_dimension ty =
    Option.map cart_dimension
      (Lib.total wordsSyntax.dest_word_type ty)

  fun card_of_type assigns ty =
    if is_boolean_type ty then 2
    else if is_itself_type ty then 1
    else
      case Lib.total Type.dom_rng ty of
          SOME (domain, range) =>
            Refute_ModelFinder_Util.reasonable_power
              (card_of_type assigns range) (card_of_type assigns domain)
        | NONE =>
            if is_pair_type ty then
              let
                val (left, right) = pairSyntax.dest_prod ty
                val left_card = card_of_type assigns left
                val right_card = card_of_type assigns right
              in
                left_card * right_card
                handle Overflow =>
                  raise Refute_ModelFinder_Util.TOO_LARGE
                    ("Refute_ModelFinder_HOL.card_of_type",
                     "product cardinality does not fit in int")
              end
            else
              (case word_dimension ty of
                   SOME width =>
                     Refute_ModelFinder_Util.reasonable_power 2 width
                 | NONE =>
                     (case cart_type_parts ty of
                          SOME (element, index_ty) =>
                            Refute_ModelFinder_Util.reasonable_power
                              (card_of_type assigns element)
                              (cart_dimension index_ty)
                        | NONE =>
                            (case assignment_lookup assigns ty of
                                 SOME card => card
                               | NONE => raise err "card_of_type"
                                   "type has no exact cardinality")))

  fun bounded_power maximum base exponent =
    let
      fun multiply left right =
        if left = 0 orelse right = 0 then 0
        else if left >= maximum orelse right >= maximum orelse
                left > maximum div right then maximum
        else Int.min (maximum, left * right)
      fun power 0 = 1
        | power 1 = Int.min (maximum, base)
        | power n =
            let val half = power (n div 2)
            in multiply (multiply half half) (power (n mod 2)) end
    in
      if exponent < 0 then raise err "bounded_power" "negative exponent"
      else Int.min (maximum, power exponent)
    end

  fun bounded_card_of_type maximum default assigns ty =
    let
      fun recurse ty =
        case Lib.total Type.dom_rng ty of
            SOME (domain, range) =>
              bounded_power maximum (recurse range) (recurse domain)
          | NONE =>
              if is_pair_type ty then
                let
                  val (left, right) = pairSyntax.dest_prod ty
                  val left_card = recurse left
                  val right_card = recurse right
                in
                  if left_card = 0 orelse right_card = 0 then 0
                  else if left_card >= maximum orelse
                          right_card >= maximum orelse
                          left_card > maximum div right_card then maximum
                  else left_card * right_card
                end
              else
                (Int.min (maximum, card_of_type assigns ty)
                 handle error as HOL_ERR _ =>
                          if default = ~1 then raise error
                          else Int.min (maximum, default)
                      | Refute_ModelFinder_Util.TOO_LARGE _ => maximum)
    in
      recurse ty
    end

  fun bounded_exact_card_of_type context finitizable maximum default
        assigns ty =
    let
      fun fallback ty = Option.getOpt (assignment_lookup assigns ty, default)
      fun multiply left right =
        if left = 0 orelse right = 0 then 0
        else if left >= maximum orelse right >= maximum orelse
                left > maximum div right then maximum
        else Int.min (maximum, left * right)
      fun recurse avoid ty =
        if List.exists (fn other => other = ty) avoid then 0
        else if List.exists (fn other => other = ty) finitizable then
          fallback ty
        else if is_boolean_type ty then Int.min (maximum, 2)
        else if is_itself_type ty then Int.min (maximum, 1)
        else
          case Lib.total Type.dom_rng ty of
              SOME (domain, range) =>
                let
                  val domain_card = recurse avoid domain
                  val range_card = recurse avoid range
                in
                  if range_card = 1 then 1
                  else if domain_card = 0 orelse range_card = 0 then 0
                  else bounded_power maximum range_card domain_card
                end
            | NONE =>
                if is_pair_type ty then
                  let val (left, right) = pairSyntax.dest_prod ty
                  in multiply (recurse avoid left) (recurse avoid right) end
                else
                  (case word_dimension ty of
                       SOME width => bounded_power maximum 2 width
                     | NONE =>
                         (case cart_type_parts ty of
                              SOME (element, index_ty) =>
                                bounded_power maximum
                                  (recurse avoid element)
                                  (cart_dimension index_ty)
                            | NONE =>
                         let val constructors = data_type_constrs context ty
                         in
                           if null constructors then
                             if is_integer_type ty then 0 else fallback ty
                           else
                             let
                               fun constructor_card constructor =
                                 List.foldl (fn (argument_ty, total) =>
                                   multiply total
                                     (recurse (ty :: avoid) argument_ty))
                                   1 (constructor_arg_types constructor)
                               val cards = map constructor_card constructors
                             in
                               if List.exists (fn card => card = 0) cards then
                                 0
                               else List.foldl (fn (card, total) =>
                                 if total >= maximum - card then maximum
                                 else total + card) 0 cards
                             end
                         end))
    in
      Int.min (maximum, recurse [] ty)
    end

  val typical_atomic_card = 4

  fun typical_card_of_type ty =
    bounded_card_of_type 16777217 typical_atomic_card [] ty

  fun is_finite_type context ty =
    bounded_exact_card_of_type context [] 2 2 [] ty > 0

  fun eta_expand term missing =
    let
      fun domains 0 _ result = rev result
        | domains count ty result =
            let val (domain, range) = Type.dom_rng ty
            in domains (count - 1) range (domain :: result) end
      val argument_tys = domains missing (Term.type_of term) []
      fun fresh (ty, (index, avoids, arguments)) =
        let
          val candidate = Term.mk_var
            ("x" ^ Int.toString index, ty)
          val argument = Term.variant avoids candidate
        in
          (index + 1, argument :: avoids, argument :: arguments)
        end
      val (_, _, reversed_arguments) = List.foldl fresh
        (0, Term.all_vars term, []) argument_tys
      val arguments = rev reversed_arguments
    in
      Term.list_mk_abs (arguments, Term.list_mk_comb (term, arguments))
    end

  fun replacement_for table constant =
    let val key = const_key constant
    in
      case List.find (fn ({original, ...} : ersatz) =>
             same_key original key) table of
          SOME {replacement = {Thy, Name}, ...} =>
            SOME (Term.mk_thy_const
              {Thy = Thy, Name = Name, Ty = Term.type_of constant})
        | NONE => NONE
    end

  fun gspec_expansion function =
    let
      val (domain_ty, pair_ty) = Type.dom_rng (Term.type_of function)
      val (element_ty, truth_ty) = pairSyntax.dest_prod pair_ty
      val _ = if truth_ty = Type.bool then ()
              else raise err "gspec_expansion" "non-boolean guard"
      val avoids = Term.all_vars function
      val element = Term.variant avoids (Term.mk_var ("v", element_ty))
      val source = Term.variant (element :: avoids)
        (Term.mk_var ("x", domain_ty))
      val equation = boolSyntax.mk_eq
        (pairSyntax.mk_pair (element, boolSyntax.T),
         Term.mk_comb (function, source))
    in
      Term.mk_abs (element, boolSyntax.mk_exists (source, equation))
    end handle HOL_ERR _ =>
      raise Refute_ModelFinder_Util.NOT_SUPPORTED
        "set comprehension GSPEC has unsupported type"

  val unfold_max_depth = 255
  val def_inline_threshold_for_booleans = 60
  val def_inline_threshold_for_non_booleans = 20

  fun unfold_defs_in_term
        (context as {case_names, ersatz_table, whacks, total_consts, ...}
          : mf_context) term =
    let
      fun whacked candidate = List.exists (Term.aconv candidate) whacks
      fun process_args depth arguments = map (do_term depth) arguments
      and do_term depth candidate =
        if is_numeral candidate then candidate
        else if Term.is_abs candidate then
          let val (variable, body) = Term.dest_abs candidate
          in Term.mk_abs (variable, do_term depth body) end
        else if Term.is_comb candidate then
          let val (head, arguments) = HolKernel.strip_comb candidate
          in
            if Term.is_const head then
              do_const depth head arguments
            else
              s_betapplys (do_term depth head,
                process_args depth arguments)
          end
        else if Term.is_const candidate then
          do_const depth candidate []
        else if whacked candidate then unknown_value (Term.type_of candidate)
        else candidate
      and do_const depth constant arguments =
        let
          val key = const_key constant
          fun ordinary () =
            if is_never_unfold_const constant then
              Term.list_mk_comb (constant, process_args depth arguments)
            else
              case List.find (fn (other, _) => same_key key other)
                     case_names of
                  SOME (_, constructor_count) =>
                    let val needed = constructor_count + 1
                    in
                      if length arguments < needed then
                        do_term depth (eta_expand
                          (Term.list_mk_comb (constant, arguments))
                          (needed - length arguments))
                      else
                        let
                          val scrutinee = do_term depth (hd arguments)
                          val functions =
                            List.take (tl arguments, constructor_count)
                          val rest = List.drop (arguments, needed)
                          val data_ty = Term.type_of scrutinee
                          val full = Term.list_mk_comb (constant,
                            List.take (arguments, needed))
                          val result_ty = Term.type_of full
                          val value = optimized_case_value context data_ty
                            result_ty functions scrutinee
                        in
                          do_term depth
                            (s_betapplys (value, process_args depth rest))
                        end
                    end
                | NONE =>
                    if is_constr constant then
                      Term.list_mk_comb
                        (constant, process_args depth arguments)
                    else if is_record_get constant then
                      if null arguments then
                        do_term depth (eta_expand constant 1)
                      else
                        s_betapplys
                          (optimized_record_get context constant
                             (do_term depth (hd arguments)),
                           process_args depth (tl arguments))
                    else if is_record_update constant then
                      if length arguments < 2 then
                        do_term depth
                          (eta_expand (Term.list_mk_comb
                             (constant, arguments)) (2 - length arguments))
                      else
                        s_betapplys
                          (optimized_record_update context constant
                             (do_term depth (hd arguments))
                             (do_term depth (List.nth (arguments, 1))),
                           process_args depth (List.drop (arguments, 2)))
                    else if is_raw_equational_fun context constant orelse
                            is_choice_spec_fun context constant then
                      Term.list_mk_comb
                        (constant, process_args depth arguments)
                    else
                      case def_of_const_ext context constant of
                          SOME (force, definition) =>
                            if depth >= unfold_max_depth then
                              raise Refute_ModelFinder_Util.TOO_LARGE
                                ("Refute_ModelFinder_HOL.unfold_defs_in_term",
                                 "too many nested definitions")
                            else
                              let
                                val threshold =
                                  if is_boolean_type
                                       (constructor_result_type constant)
                                     andalso total_consts <> SOME true then
                                    def_inline_threshold_for_booleans
                                  else
                                    def_inline_threshold_for_non_booleans
                              in
                                if not force andalso
                                   Term.term_size definition > threshold then
                                  Term.list_mk_comb (constant,
                                    process_args depth arguments)
                                else
                                  do_term (depth + 1)
                                    (s_betapplys (definition, arguments))
                              end
                        | NONE => Term.list_mk_comb
                            (constant, process_args depth arguments)
        in
          if whacked constant then
            unknown_value (Term.type_of
              (Term.list_mk_comb (constant, arguments)))
          else if same_key key {Thy = "bool", Name = "LET"} orelse
                  same_key key
                    {Thy = "bool", Name = "literal_case"} then
            (case arguments of
                 function :: argument :: rest =>
                   s_betapplys
                     (do_term depth
                        (s_betapply (do_term depth function,
                           do_term depth argument)),
                      process_args depth rest)
               | _ => ordinary ())
          else if same_key key {Thy = "pred_set", Name = "GSPEC"} then
            (case arguments of
                 function :: rest =>
                   s_betapplys (do_term depth
                     (gspec_expansion (do_term depth function)),
                     process_args depth rest)
               | [] => do_term depth (eta_expand constant 1))
          else
            case replacement_for ersatz_table constant of
                SOME replacement =>
                  if depth >= unfold_max_depth then
                    raise Refute_ModelFinder_Util.TOO_LARGE
                      ("Refute_ModelFinder_HOL.unfold_defs_in_term",
                       "too many nested replacements")
                  else
                    do_const (depth + 1) replacement arguments
              | NONE => ordinary ()
        end
    in
      do_term 0 term
    end

  fun empty_context_fields () =
    let
      val tables = make_tables ()
      val nondefs = all_nondefs_of ()
    in
      {tables = tables, nondefs = nondefs,
       nondef_table = const_nondef_table nondefs}
    end

  fun make_context (mf : Refute_Core.mf_config) evals =
    let
      val {tables = {def_tables, simp_table, psimp_table,
                     choice_spec_table},
           nondefs, nondef_table} = empty_context_fields ()
      val max_bisim_depth = List.foldl Int.max (~1) (#bisim_depth mf)
    in
      {max_bisim_depth = max_bisim_depth,
       boxes = #box mf,
       wfs = #wf mf,
       user_axioms = #user_axioms mf,
       debug = #debug mf,
       whacks = #whack mf,
       binary_ints = #binary_ints mf,
       destroy_constrs = #destroy_constrs mf,
       specialize = #specialize mf,
       star_linear_preds = #star_linear_preds mf,
       total_consts = #total_consts mf,
       needs = #need mf,
       tac_timeout = Time.fromReal (#tac_timeout mf),
       evals = evals,
       case_names = case_names (),
       def_tables = def_tables,
       nondef_table = nondef_table,
       nondefs = nondefs,
       simp_table = ref simp_table,
       psimp_table = psimp_table,
       choice_spec_table = choice_spec_table,
       intro_table = KNametab.empty,
       ersatz_table = current_ersatz_table (),
       skolems = ref [],
       special_funs = ref [],
       wf_cache = ref [],
       constr_cache = ref []}
    end
end
