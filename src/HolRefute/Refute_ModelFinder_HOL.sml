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

  fun def_props_for_const table constant =
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
       case_names = [],
       def_tables = def_tables,
       nondef_table = nondef_table,
       nondefs = nondefs,
       simp_table = ref simp_table,
       psimp_table = psimp_table,
       choice_spec_table = choice_spec_table,
       intro_table = KNametab.empty,
       ersatz_table = !ersatz_registry,
       skolems = ref [],
       special_funs = ref [],
       wf_cache = ref [],
       constr_cache = ref []}
    end
end
