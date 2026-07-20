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
  val bound_var_prefix = reserved_prefix ^ "b"
  val cong_var_prefix = reserved_prefix ^ "c"
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

  fun special_prefix_for serial =
    special_prefix ^ Int.toString serial ^ name_sep

  fun bound_var_name index =
    bound_var_prefix ^ Int.toString index ^ name_sep

  fun cong_var_name index =
    cong_var_prefix ^ Int.toString index ^ name_sep

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

  fun is_special_name name = String.isPrefix special_prefix name

  fun is_indexed_var_name prefix name =
    if not (String.isPrefix prefix name) then false
    else
      let
        val suffix = drop_prefix prefix name
        val length = size suffix
        val digits =
          if length < 1 then ""
          else String.extract (suffix, 0, SOME (length - 1))
      in
        length > 1 andalso String.isSuffix name_sep suffix andalso
        List.all Char.isDigit (String.explode digits)
      end

  fun is_bound_var_name name = is_indexed_var_name bound_var_prefix name

  fun is_cong_var_name name = is_indexed_var_name cong_var_prefix name

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

  fun mk_special serial original ty =
    if serial < 1 then
      raise err "mk_special" "specialization serial must be positive"
    else
      mk_reserved_var (special_prefix_for serial ^ original) ty

  fun mk_bound_var index ty =
    if index < 0 then raise err "mk_bound_var" "negative bound index"
    else mk_reserved_var (bound_var_name index) ty

  fun mk_cong_var index ty =
    if index < 0 then raise err "mk_cong_var" "negative congruence index"
    else mk_reserved_var (cong_var_name index) ty

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
      val goal_frees = Term.free_vars_lr goal

      fun rename (variable, (avoids, substitutions, renaming)) =
        if member_name (variable_name variable) fabricated then
          let
            val (name, ty) = Term.dest_var variable
            val candidate =
              if is_reserved_name name then
                Term.mk_var ("user$" ^ name, ty)
              else
                variable
            val fresh = Term.variant avoids candidate
            val substitution = {redex = variable, residue = fresh}
          in
            (fresh :: avoids, substitution :: substitutions,
             (variable, fresh) :: renaming)
          end
        else
          (avoids, substitutions, renaming)

      val (_, substitutions, renaming) =
        List.foldl rename (fabricated @ goal_frees, [], []) goal_frees
      val renamed = Term.subst (rev substitutions) goal
      val _ = assert_user_goal renamed
    in
      (renamed, rev renaming)
    end
end

structure Refute_ModelFinder_HOL = struct
  open Portable Feedback
  infix |>

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
    case Lib.total Term.dest_thy_const constant of
        SOME {Thy, Name, ...} => {Thy = Thy, Name = Name}
      | NONE =>
          (case Lib.total Term.dest_var constant of
               SOME (name, _) =>
                 if Refute_ModelFinder_Names.is_reserved_name name then
                   {Thy = "refute.generated", Name = name}
                 else
                   raise err "const_key" "ordinary variable is not a constant"
             | NONE => raise err "const_key" "term is not a constant")

  fun same_key left right =
    KernelSig.name_compare (left, right) = EQUAL

  (* Buckets are stored newest-first so that table_append stays O(1);
     table_lookup is the only reader and restores insertion order. *)
  fun table_lookup table constant =
    case Lib.total const_key constant of
        SOME key => rev (Option.getOpt (KNametab.lookup table key, []))
      | NONE => []

  fun table_append key value table =
    let val old = Option.getOpt (KNametab.lookup table key, [])
    in KNametab.update (key, value :: old) table end

  fun add_simps table constant axioms =
    let val key = const_key constant
    in table := List.foldl (fn (axiom, result) =>
         table_append key axiom result) (!table) axioms
    end

  fun theorem_term theorem =
    let
      val proposition =
        boolSyntax.list_mk_imp (Thm.hyp theorem, Thm.concl theorem)
    in
      (* HOL theorem frees are implicitly universal.  Isabelle presents the
         corresponding table variables as schematic Vars, which close_form
         closes before nut conversion.  Close them here so they cannot be
         mistaken for freely interpreted model constants. *)
      boolSyntax.list_mk_forall
        (Term.free_vars_lr proposition, proposition)
    end

  fun clauses_of theorem = map theorem_term (Drule.CONJUNCTS theorem)

  fun term_under_def term =
    if boolSyntax.is_forall term then
      term_under_def (#2 (boolSyntax.dest_forall term))
    else if boolSyntax.is_imp_only term then
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
      val new_variables = List.filter (fn variable =>
        not (List.exists (Term.aconv variable) variables))
        (Term.free_vars_lr equation)
    in
      SOME (boolSyntax.list_mk_forall
        (variables @ new_variables,
         boolSyntax.list_mk_imp (premises, equation)))
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
        (Term.is_const term orelse
         (Term.is_var term andalso
          Refute_ModelFinder_Names.is_reserved_name
            (#1 (Term.dest_var term)))) andalso
        same_key (const_key term) key
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
  val unsigned_bit_type = Type.mk_thy_type
    {Thy = "refute", Tyop = "unsigned_bit", Args = []}
  val signed_bit_type = Type.mk_thy_type
    {Thy = "refute", Tyop = "signed_bit", Args = []}

  fun mk_bitword_type bit = Type.mk_thy_type
    {Thy = "refute", Tyop = "bitword", Args = [bit]}

  val unsigned_bitword_type = mk_bitword_type unsigned_bit_type
  val signed_bitword_type = mk_bitword_type signed_bit_type

  fun is_bit_type ty = ty = unsigned_bit_type orelse ty = signed_bit_type

  fun is_bitword_type ty =
    case Lib.total Type.dest_thy_type ty of
        SOME {Thy = "refute", Tyop = "bitword", ...} => true
      | _ => false

  fun binarize_nat_and_int_in_type ty =
    if ty = num_type then unsigned_bitword_type
    else if ty = int_type then signed_bitword_type
    else if Type.is_vartype ty then ty
    else
      let val {Thy, Tyop, Args} = Type.dest_thy_type ty
      in Type.mk_thy_type {Thy = Thy, Tyop = Tyop,
           Args = map binarize_nat_and_int_in_type Args}
      end

  fun retype_constant layer term ty =
    if Term.type_of term = ty then term
    else
      case Lib.total Term.dest_thy_const term of
          SOME {Thy, Name, ...} =>
            let
              val generic = Term.prim_mk_const {Thy = Thy, Name = Name}
              val legal = Lib.can
                (Type.match_type (Term.type_of generic)) ty
            in
              if legal then Term.mk_thy_const {Thy = Thy, Name = Name, Ty = ty}
              else Refute_ModelFinder_Names.mk_reserved_var
                (Refute_ModelFinder_Names.reserved_prefix ^ layer ^
                 Refute_ModelFinder_Names.name_sep ^ Thy ^
                 Refute_ModelFinder_Names.name_sep ^ Name) ty
            end
        | NONE =>
            let val (name, _) = Term.dest_var term
            in Term.mk_var (name, ty) end

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
     (* MOD has no nut primitive.  It must remain unfoldable rather than
        entering the built-in table and becoming an untranslatable leaf. *)
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
     (* As above, int_mod is deliberately unfolded in M3. *)
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
    let
      fun step (constant, (seen, result)) =
        let val key = const_key constant
        in
          if Option.isSome (KNametab.lookup seen key) then (seen, result)
          else (KNametab.update (key, ()) seen, (key, constant) :: result)
        end
    in
      List.foldl step (KNametab.empty, [])
        (HolKernel.find_terms Term.is_const term)
      |> rev o #2
    end

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

  (* PLAN_M3 section 13.2: bracketed tools may transiently register
     a DefnBase presentation and then delete its scratch constant.  The
     DefnBase store retains such entries, and current_userdefs reconstructs
     every presentation with prim_mk_const, so one stale entry makes an
     otherwise unrelated later MF run fail.  Discover presentations through
     the live constant table instead, so lookup_userdef is called only on
     constants that still exist. *)
  fun live_userdefs () =
    List.mapPartial (fn constant =>
      DefnBase.lookup_userdef constant handle HOL_ERR _ => NONE)
      (Term.all_consts ())

  fun presentation_key {const, ...} = const_key const

  (* Folded into a key set once per make_tables: raw_standard_props tests
     every equation of every ancestor definition against it. *)
  fun presentation_key_set presentations =
    List.foldl (fn (presentation, table) =>
      KNametab.update (presentation_key presentation, ()) table)
      KNametab.empty presentations

  fun has_presentation keys key = Option.isSome (KNametab.lookup keys key)

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
      val keys = presentation_key_set presentations
      fun from_theorem (_, theorem) =
        let
          fun usable (key, equation) =
            if has_presentation keys key then []
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
      val presentations = live_userdefs ()
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
            fun distinct_vars [] = true
              | distinct_vars (variable :: rest) =
                  Term.is_var variable andalso
                  not (List.exists (Term.aconv variable) rest) andalso
                  distinct_vars rest
          in
            null premises andalso
            (case Lib.total boolSyntax.dest_eq conclusion of
                 SOME (left, _) =>
                   distinct_vars (#2 (HolKernel.strip_comb left))
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

  fun is_funbox_type ty =
    case Lib.total Type.dest_thy_type ty of
        SOME {Thy = "refute", Tyop = "funbox", ...} => true
      | _ => false

  fun is_pairbox_type ty =
    case Lib.total Type.dest_thy_type ty of
        SOME {Thy = "refute", Tyop = "pairbox", ...} => true
      | _ => false

  fun is_iterator_type ty =
    Type.is_vartype ty andalso
    let val name = Type.dest_vartype ty
    in
      String.isPrefix
        ("'" ^ Refute_ModelFinder_Names.lfp_iterator_prefix) name orelse
      String.isPrefix
        ("'" ^ Refute_ModelFinder_Names.gfp_iterator_prefix) name
    end

  fun boxed_type_args ty = #Args (Type.dest_thy_type ty)

  fun mk_funbox_type (domain, range) = Type.mk_thy_type
    {Thy = "refute", Tyop = "funbox", Args = [domain, range]}

  fun mk_pairbox_type (left, right) = Type.mk_thy_type
    {Thy = "refute", Tyop = "pairbox", Args = [left, right]}

  fun unarize_unbox_etc_type ty =
    if ty = unsigned_bitword_type then num_type
    else if ty = signed_bitword_type then int_type
    else if Type.is_vartype ty then ty
    else
      let val {Thy, Tyop, Args} = Type.dest_thy_type ty
      in
        if Thy = "refute" andalso Tyop = "funbox" then
          Type.-->(unarize_unbox_etc_type (List.nth (Args, 0)),
            unarize_unbox_etc_type (List.nth (Args, 1)))
        else if Thy = "refute" andalso Tyop = "pairbox" then
          pairSyntax.mk_prod
            (unarize_unbox_etc_type (List.nth (Args, 0)),
             unarize_unbox_etc_type (List.nth (Args, 1)))
        else
          Type.mk_thy_type {Thy = Thy, Tyop = Tyop,
            Args = map unarize_unbox_etc_type Args}
      end

  fun type_matches_unboxed (pattern, actual) =
    Lib.can (Type.match_type (unarize_unbox_etc_type pattern))
      (unarize_unbox_etc_type actual)

  datatype box_position =
      InConstr | InSel | InExpr | InPair | InFunLHS | InFunRHS1 | InFunRHS2

  fun in_fun_lhs_for InConstr = InSel
    | in_fun_lhs_for _ = InFunLHS

  fun in_fun_rhs_for InConstr = InConstr
    | in_fun_rhs_for InSel = InSel
    | in_fun_rhs_for InFunRHS1 = InFunRHS2
    | in_fun_rhs_for _ = InFunRHS1

  fun is_boolean_type ty =
    case Lib.total Type.dest_thy_type ty of
        SOME {Thy = "min", Tyop = "bool", ...} => true
      | _ => false

  fun is_integer_type ty =
    case Lib.total Type.dest_thy_type ty of
        SOME {Thy = "num", Tyop = "num", ...} => true
      | SOME {Thy = "integer", Tyop = "int", ...} => true
      | _ => false

  fun is_boxing_worth_it context position ty =
    if is_fun_type ty then
      (position = InPair orelse position = InFunLHS) andalso
      not (is_boolean_type (#2 (boolSyntax.strip_fun ty)))
    else if is_pair_type ty then
      let val (left, right) = pairSyntax.dest_prod ty
      in
        position = InPair orelse position = InFunRHS1 orelse
        position = InFunRHS2 orelse
        ((position = InExpr orelse position = InFunLHS) andalso
         List.exists (is_boxing_worth_it context InPair)
           [box_type context InPair left, box_type context InPair right])
      end
    else
      false
  and should_box_type (context as {boxes, ...} : mf_context) position ty =
    (case Refute_ModelFinder_Util.triple_lookup type_matches_unboxed
            boxes ty of
         SOME (SOME box_me) => box_me
       | _ => is_boxing_worth_it context position ty)
  and box_type context position ty =
    if is_fun_type ty then
      let val (domain, range) = Type.dom_rng ty
      in
        if position <> InConstr andalso position <> InSel andalso
           should_box_type context position ty then
          mk_funbox_type
            (box_type context InFunLHS domain,
             box_type context InFunRHS1 range)
        else
          Type.-->(box_type context (in_fun_lhs_for position) domain,
            box_type context (in_fun_rhs_for position) range)
      end
    else if is_pair_type ty then
      let val (left, right) = pairSyntax.dest_prod ty
      in
        if position <> InConstr andalso position <> InSel andalso
           should_box_type context position ty then
          mk_pairbox_type
            (box_type context InSel left, box_type context InSel right)
        else
          let val nested =
            if position = InConstr orelse position = InSel then position
            else InPair
          in
            pairSyntax.mk_prod
              (box_type context nested left, box_type context nested right)
          end
      end
    else
      ty

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

  fun binarized_and_boxed_data_type_constrs context binarize ty =
    let
      fun transform constructor =
        let
          val boxed = box_type context InConstr (Term.type_of constructor)
          val transformed =
            if binarize then binarize_nat_and_int_in_type boxed else boxed
        in
          retype_constant "middle" constructor transformed
        end
    in
      map transform (data_type_constrs context ty)
    end

  fun registered_constructor term =
    List.exists (fn {constructors, ...} =>
      List.exists (fn constructor =>
        Term.same_const constructor term) constructors)
      (!codatatype_registry)

  fun raw_constructor_name constructor =
    let val {Thy, Name, ...} = Term.dest_thy_const constructor
    in Thy ^ "$" ^ Name end

  fun reserved_constructor term =
    case Lib.total Term.dest_var term of
        SOME (name, _) =>
          if not (Refute_ModelFinder_Names.is_reserved_name name) orelse
             Refute_ModelFinder_Names.is_sel name then false
          else
            let
              val original = Refute_ModelFinder_Names.original_name name
              val result_ty = #2 (boolSyntax.strip_fun (Term.type_of term))
              val raw =
                case TypeBase.fetch result_ty of
                    SOME info => TypeBasePure.constructors_of info
                  | NONE => []
              val registered = List.concat (map #constructors
                (List.filter (fn {constructors, ...} =>
                   case constructors of
                       constructor :: _ =>
                         #2 (boolSyntax.strip_fun
                           (Term.type_of constructor)) = result_ty
                     | [] => false) (!codatatype_registry)))
            in
              List.exists (fn constructor =>
                raw_constructor_name constructor = original)
                (raw @ registered)
            end
        | NONE => false
    handle HOL_ERR _ => false

  fun is_nonfree_constr term =
    if Term.is_const term then
      TypeBase.is_constructor term orelse registered_constructor term
    else
      reserved_constructor term

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
      (* Early exit: the old List.find over a full map searched every
         TypeBase entry even after the field was found. *)
      fun scan [] = NONE
        | scan (info :: rest) =
            (case search_type info of
                 NONE => scan rest
               | found => found)
    in
      scan (TypeBase.elts ())
    end handle HOL_ERR _ => NONE

  fun dest_record_get term = find_field #accessor term
  fun dest_record_update term = find_field #fupd term
  fun is_record_get term = Option.isSome (dest_record_get term)
  fun is_record_update term = Option.isSome (dest_record_update term)

  fun is_named_const expected term =
    (Term.is_const term andalso same_key (const_key term) expected) orelse
    (case Lib.total Term.dest_var term of
         SOME (name, _) =>
           Refute_ModelFinder_Names.is_reserved_name name andalso
           Refute_ModelFinder_Names.original_name name =
             #Thy expected ^ "$" ^ #Name expected
       | NONE => false)

  fun is_descr term =
    is_named_const {Thy = "min", Name = "@"} term orelse
    is_named_const {Thy = "refute", Name = "safe_The"} term

  fun is_exists_unique term =
    is_named_const {Thy = "bool", Name = "?!"} term

  fun exists_unique_def () = Thm.concl (DB.fetch "bool"
    "EXISTS_UNIQUE_DEF")

  fun relaxed_int_of_term term =
    case Lib.total intSyntax.dest_negated term of
        SOME positive => Arbint.~ (relaxed_int_of_term positive)
      | NONE => Arbint.fromNat (Literal.relaxed_dest_numeral
          (intSyntax.dest_injected term))

  fun numeral_value term =
    if Term.type_of term = int_type then
      SOME (relaxed_int_of_term term)
      handle HOL_ERR _ => NONE
    else if Term.type_of term = num_type then
      SOME (Arbint.fromNat (Literal.relaxed_dest_numeral term))
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
    case Lib.total Term.dest_thy_const constructor of
        SOME {Thy, Name, ...} => Thy ^ "$" ^ Name
      | NONE =>
          let val (name, _) = Term.dest_var constructor
          in Refute_ModelFinder_Names.original_name name end

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

  fun binarized_and_boxed_nth_sel_for_constr context binarize
        constructor index =
    let
      val transformed = retype_constant "middle" constructor
        ((if binarize then binarize_nat_and_int_in_type else fn ty => ty)
          (box_type context InConstr (Term.type_of constructor)))
      val data_ty = constructor_result_type transformed
      val constructor_id = constructor_name transformed
    in
      if index = ~1 then
        Refute_ModelFinder_Names.mk_discriminator constructor_id
          (Type.-->(data_ty, Type.bool))
      else
        Refute_ModelFinder_Names.mk_selector index constructor_id
          (Type.-->(data_ty,
             List.nth (constructor_arg_types transformed, index)))
    end

  fun binarized_and_boxed_constr_for_sel context binarize selector =
    let
      val (name, ty) = Term.dest_var selector
      val (domain, _) = Type.dom_rng ty
      val original = Refute_ModelFinder_Names.original_name name
      val constructors =
        binarized_and_boxed_data_type_constrs context binarize domain
    in
      case List.find (fn constructor =>
             constructor_name constructor = original) constructors of
          SOME constructor => constructor
        | NONE => raise err "binarized_and_boxed_constr_for_sel"
            ("no constructor for selector " ^ name)
    end

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
            (boolSyntax.mk_eq (numSyntax.zero_tm, value))
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

  (* These smart application forms are observable in preprocessor goldens
     and match Nitpick's s_betapply before ordinary beta reduction. *)
  fun s_betapply (function, argument) =
    let
      val application = Term.mk_comb (function, argument)
    in
      if boolSyntax.is_eq application then
        let val (left, right) = boolSyntax.dest_eq application
        in
          if Term.aconv left right then boolSyntax.T else application
        end
      else if boolSyntax.is_cond application then
        let val (condition, left, right) =
          boolSyntax.dest_cond application
        in
          if Term.aconv condition boolSyntax.T then left
          else if Term.aconv condition boolSyntax.F then right
          else application
        end
      else if boolSyntax.is_let function then
        let
          val (abstraction, value) = boolSyntax.dest_let function
        in
          case Lib.total Term.dest_abs abstraction of
              SOME (variable, body) =>
                let
                  val fresh =
                    if Term.free_in variable argument then
                      Term.variant
                        (Term.all_vars body @ Term.all_vars argument)
                        variable
                    else
                      variable
                  val renamed =
                    if Term.aconv fresh variable then body
                    else Term.subst [{redex = variable, residue = fresh}]
                      body
                in
                  boolSyntax.mk_let
                    (Term.mk_abs (fresh,
                       s_betapply (renamed, argument)), value)
                end
            | NONE => application
        end
      else if Term.is_abs function then
        Term.beta_conv application
      else
        application
    end

  fun s_betapplys (function, arguments) =
    List.foldl (fn (argument, result) =>
      s_betapply (result, argument)) function arguments

  fun same_constructor_term left right =
    is_nonfree_constr left andalso is_nonfree_constr right andalso
    constructor_name left = constructor_name right andalso
    constructor_result_type left = constructor_result_type right

  fun discriminate_value context constructor value =
    let val (head, _) = HolKernel.strip_comb value
    in
      if same_constructor_term constructor head then
        boolSyntax.T
      else if is_nonfree_constr head then
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
      if same_constructor_term constructor head andalso
         index < length arguments then
        List.nth (arguments, index)
      else if is_nonfree_constr head then
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
      if is_nonfree_constr head then value
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

  fun boxed_constructor context ty =
    case data_type_constrs context ty of
        constructor :: _ => constructor
      | [] => raise err "boxed_constructor" "boxed type has no constructor"

  fun coerce_term context new_ty old_ty term =
    if new_ty = old_ty then term
    else if is_funbox_type new_ty then
      let
        val arguments = boxed_type_args new_ty
        val domain = List.nth (arguments, 0)
        val range = List.nth (arguments, 1)
        val function_ty = Type.-->(domain, range)
        val function = coerce_term context function_ty old_ty term
      in
        construct_value context (boxed_constructor context new_ty) [function]
      end
    else if is_funbox_type old_ty then
      let
        val arguments = boxed_type_args old_ty
        val domain = List.nth (arguments, 0)
        val range = List.nth (arguments, 1)
        val expanded = constr_expand context old_ty term
        val function = hd (#2 (HolKernel.strip_comb expanded))
      in
        coerce_term context new_ty (Type.-->(domain, range)) function
      end
    else if is_fun_type new_ty andalso is_fun_type old_ty then
      let
        val (new_domain, new_range) = Type.dom_rng new_ty
        val (old_domain, old_range) = Type.dom_rng old_ty
        val variable = Term.variant (Term.all_vars term)
          (Term.mk_var ("x", new_domain))
        val old_argument = coerce_term context old_domain new_domain variable
        val body = Term.mk_comb (term, old_argument)
      in
        Term.mk_abs (variable,
          coerce_term context new_range old_range body)
      end
    else if (is_pair_type new_ty orelse is_pairbox_type new_ty) andalso
            (is_pair_type old_ty orelse is_pairbox_type old_ty) then
      let
        val new_args =
          if is_pair_type new_ty then
            let val (left, right) = pairSyntax.dest_prod new_ty
            in [left, right] end
          else boxed_type_args new_ty
        val old_args =
          if is_pair_type old_ty then
            let val (left, right) = pairSyntax.dest_prod old_ty
            in [left, right] end
          else boxed_type_args old_ty
        val expanded = constr_expand context old_ty term
        val arguments = #2 (HolKernel.strip_comb expanded)
        val coerced = ListPair.mapEq
          (fn ((new_arg, old_arg), argument) =>
            coerce_term context new_arg old_arg argument)
          (ListPair.zip (new_args, old_args), arguments)
      in
        if is_pair_type new_ty then pairSyntax.mk_pair
          (List.nth (coerced, 0), List.nth (coerced, 1))
        else construct_value context (boxed_constructor context new_ty)
          coerced
      end
    else
      raise err "coerce_term"
        ("incompatible types " ^ Parse.type_to_string old_ty ^ " and " ^
         Parse.type_to_string new_ty)

  fun unarize_unbox_etc_term term =
    let
      fun recurse environment candidate =
        let val (head, arguments) = HolKernel.strip_comb candidate
        in
          if Term.is_const head andalso
                  is_named_const {Thy = "refute", Name = "FunBox"} head andalso
                  length arguments = 1 then
            recurse environment (hd arguments)
          else if Term.is_const head andalso
                  is_named_const {Thy = "refute", Name = "PairBox"} head andalso
                  length arguments = 2 then
            pairSyntax.mk_pair
              (recurse environment (List.nth (arguments, 0)),
               recurse environment (List.nth (arguments, 1)))
          else if Term.is_abs candidate then
            let
              val (variable, body) = Term.dest_abs candidate
              val (name, ty) = Term.dest_var variable
              val variable' = Term.mk_var
                (name, unarize_unbox_etc_type ty)
            in
              Term.mk_abs (variable', recurse
                ((variable, variable') :: environment) body)
            end
          else if Term.is_comb candidate then
            let val (function, argument) = Term.dest_comb candidate
            in Term.mk_comb
              (recurse environment function, recurse environment argument)
            end
          else if Term.is_const candidate then
            retype_constant "unbox" candidate
              (unarize_unbox_etc_type (Term.type_of candidate))
          else if Term.is_var candidate then
            (case List.find (Term.aconv candidate o #1) environment of
                 SOME (_, replacement) => replacement
               | NONE =>
                   let val (name, ty) = Term.dest_var candidate
                   in Term.mk_var
                     (name, unarize_unbox_etc_type ty) end)
          else candidate
        end
    in recurse [] term end

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

  fun numeric_type_card ty =
    case Lib.total fcpLib.index_to_num ty of
        SOME card =>
          SOME (Arbnum.toInt card
            handle Overflow =>
              raise Refute_ModelFinder_Util.TOO_LARGE
                ("Refute_ModelFinder_HOL.numeric_type_card",
                 "finite type cardinality does not fit in int"))
      | NONE => NONE

  fun word_dimension ty =
    case Lib.total wordsSyntax.dest_word_type ty of
        SOME index_ty => numeric_type_card index_ty
      | NONE => NONE

  fun cart_type_card ty =
    case cart_type_parts ty of
        SOME (element, index_ty) =>
          Option.map (fn dimension => (element, dimension))
            (numeric_type_card index_ty)
      | NONE => NONE

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
              (case numeric_type_card ty of
                   SOME card => card
                 | NONE =>
                     (case word_dimension ty of
                          SOME width =>
                            Refute_ModelFinder_Util.reasonable_power 2 width
                        | NONE =>
                            (case cart_type_card ty of
                                 SOME (element, dimension) =>
                                   Refute_ModelFinder_Util.reasonable_power
                                     (card_of_type assigns element) dimension
                               | NONE =>
                                   (case assignment_lookup assigns ty of
                                        SOME card => card
                                      | NONE => raise err "card_of_type"
                                          "type has no exact cardinality"))))

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
              let
                val domain_card = recurse domain
                val range_card = recurse range
              in
                if domain_card >= maximum orelse
                   range_card >= maximum then
                  maximum
                else
                  bounded_power maximum range_card domain_card
              end
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
        else if is_boolean_type ty then 2
        else if is_itself_type ty then 1
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
                  (case numeric_type_card ty of
                       SOME card => card
                     | NONE =>
                         (case word_dimension ty of
                              SOME width => bounded_power maximum 2 width
                            | NONE =>
                                (case cart_type_card ty of
                                     SOME (element, dimension) =>
                                       bounded_power maximum
                                         (recurse avoid element) dimension
                                   | NONE =>
                                let
                                  val constructors =
                                    data_type_constrs context ty
                                in
                                  if null constructors then
                                    if is_integer_type ty then 0
                                    else fallback ty
                                  else
                                    let
                                      fun constructor_card constructor =
                                        List.foldl
                                          (fn (argument_ty, total) =>
                                            multiply total
                                              (recurse (ty :: avoid)
                                                argument_ty))
                                          1
                                          (constructor_arg_types constructor)
                                      val cards =
                                        map constructor_card constructors
                                    in
                                      if List.exists (fn card => card = 0)
                                           cards then
                                        0
                                      else
                                        List.foldl
                                          (fn (card, total) =>
                                            if total >= maximum - card then
                                              maximum
                                            else total + card)
                                          0 cards
                                    end
                                end)))
    in
      Int.min (maximum, recurse [] ty)
      handle Refute_ModelFinder_Util.TOO_LARGE _ => maximum
    end

  val typical_atomic_card = 4

  fun typical_card_of_type ty =
    bounded_card_of_type 16777217 typical_atomic_card [] ty

  fun is_finite_type context ty =
    bounded_exact_card_of_type context [] 1 2 [] ty > 0

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

  fun context_with_binary_ints
        ({max_bisim_depth, boxes, wfs, user_axioms, debug, whacks,
          destroy_constrs, specialize, star_linear_preds, total_consts,
          needs, tac_timeout, evals, case_names, def_tables, nondef_table,
          nondefs, simp_table, psimp_table, choice_spec_table, intro_table,
          ersatz_table, skolems, special_funs, wf_cache, constr_cache, ...}
         : mf_context) binary_ints : mf_context =
    {max_bisim_depth = max_bisim_depth, boxes = boxes, wfs = wfs,
     user_axioms = user_axioms, debug = debug, whacks = whacks,
     binary_ints = binary_ints, destroy_constrs = destroy_constrs,
     specialize = specialize, star_linear_preds = star_linear_preds,
     total_consts = total_consts, needs = needs, tac_timeout = tac_timeout,
     evals = evals, case_names = case_names, def_tables = def_tables,
     nondef_table = nondef_table, nondefs = nondefs, simp_table = simp_table,
     psimp_table = psimp_table, choice_spec_table = choice_spec_table,
     intro_table = intro_table, ersatz_table = ersatz_table,
     skolems = skolems, special_funs = special_funs, wf_cache = wf_cache,
     constr_cache = constr_cache}

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
