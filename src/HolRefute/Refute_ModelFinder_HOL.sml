structure Refute_ModelFinder_HOL = struct
  open Portable Feedback
  infix |>

  structure Util = Refute_ModelFinder_Util

  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type
  type kname = KernelSig.kernelname

  type const_table = term list KNametab.table
  type special_fun = (term * int list * term list) * term
  type wf_cache = (term * (bool * bool)) list
  type iterator_info =
    {pred : term, preds : term list, arg_tys : hol_type list,
     arg_tyss : hol_type list list, gfp : bool, token : string}
  type iterator_table = (hol_type * iterator_info) list ref

  datatype fixpoint_kind = Lfp | Gfp | NoFp

  type fixpoint_group =
    {kind : fixpoint_kind,
     stem : string,
     members : kname list,
     rules : term list,
     cases : term list}
  type fixpoint_cache = (kname * fixpoint_group option) list
  type type_operator = {Thy : string, Tyop : string}
  type ersatz = {original : kname, replacement : kname}
  type codatatype_info =
    {tyop : type_operator, case_const : term, constructors : term list}
  type quotient_info =
    {qty : hol_type, rty : hol_type, abs : term, rep : term,
     equiv_thm : thm, partial : bool}
  type typedef_info =
    {ty : hol_type, rty : hol_type, abs : term, rep : term,
     pred : term, inverse_axioms : term list, univ : bool}
  type frac_info = {tyop : type_operator, ersatz : ersatz list}

  (* Registrations are session-level ML state.  In particular, registering a
     codatatype, quotient, typedef, or frac type never extends the current HOL
     theory. *)
  val codatatype_registry = ref ([] : codatatype_info list)
  val quotient_registry = ref ([] : quotient_info list)
  val typedef_registry = ref ([] : typedef_info list)
  val frac_registry = ref ([] : frac_info list)
  val ersatz_registry = ref ([] : ersatz list)

  (* Every classification registration and lazy harvest is serialized here.
     Model-display registration shares the mutex so rational registration
     can install both halves atomically.  Functions suffixed "_unlocked" are
     internal helpers whose callers already hold it. *)
  val registration_mutex = Mutex.mutex ()

  fun with_registration_lock body =
    Multithreading.synchronized "Refute model registrations"
      registration_mutex body

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
     case_names : (kname * (int * int)) list,
     def_tables : const_table * const_table,
     nondef_table : const_table,
     nondefs : term list,
     simp_table : const_table ref,
     psimp_table : const_table,
     choice_spec_table : const_table,
     intro_table : const_table ref,
     case_table : const_table ref,
     fixpoint_cache : fixpoint_cache ref,
     iterator_table : iterator_table,
     ersatz_table : ersatz list,
     semantic_weakening : bool ref,
     skolems : (string * string list) list ref,
     special_funs : special_fun list ref,
     wf_cache : wf_cache ref,
     constr_cache : (hol_type * term list) list ref}

  (* Upstream's ground theorem hash and vestigial unrolled-predicate ref are
     deliberately absent: nothing in this port reads either. *)

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

  (* Retyping a monomorphic HOL4 constant can turn it into a reserved free
     variable.  Semantic recognizers must nevertheless keep using the
     original theory/name carried by that variable. *)
  fun original_const_key constant =
    case Lib.total Term.dest_thy_const constant of
        SOME {Thy, Name, ...} => {Thy = Thy, Name = Name}
      | NONE =>
          let
            val (name, _) = Term.dest_var constant
            val original = Refute_ModelFinder_Names.original_name name
            val (theory, const_name) =
              Refute_ModelFinder_Names.strip_first_name_sep original
          in
            if Refute_ModelFinder_Names.is_reserved_name name andalso
               const_name <> "" then
              {Thy = theory, Name = const_name}
            else
              const_key constant
          end

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

  (* Hol_reln puts parameters outside the conjunction for some mutual
     groups.  Split at term level and restore those parameters on every
     clause; Drule.CONJUNCTS only sees top-level conjunctions. *)
  fun quantified_conjuncts theorem =
    let
      val proposition = theorem_term theorem
      val (outer, body) = boolSyntax.strip_forall proposition
      fun close clause =
        let val (inner, core) = boolSyntax.strip_forall clause
        in boolSyntax.list_mk_forall (outer @ inner, core) end
    in
      map close (boolSyntax.strip_conj body)
    end

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
     ({Thy = "relation", Name = "TC"}, 1),
     ({Thy = "relation", Name = "inv"}, 1),
     ({Thy = "relation", Name = "O"}, 2),
     ({Thy = "refute", Name = "unknown"}, 0),
     ({Thy = "refute", Name = "is_unknown"}, 1),
     ({Thy = "refute", Name = "safe_The"}, 1),
     ({Thy = "refute", Name = "bisim_suc"}, 0),
     ({Thy = "refute", Name = "bisim_zero"}, 0),
     ({Thy = "gcd", Name = "gcd"}, 0),
     ({Thy = "gcd", Name = "lcm"}, 0),
     ({Thy = "refute", Name = "nat_gcd"}, 0),
     ({Thy = "refute", Name = "nat_lcm"}, 0),
     ({Thy = "refute", Name = "Frac"}, 0),
     ({Thy = "refute", Name = "norm_frac"}, 0),
     ({Thy = "num", Name = "SUC"}, 0),
     ({Thy = "integer", Name = "Num"}, 0),
     (* Fully formed numeral syntax is recognized directly.  Its binary
        constructors must remain ordinary constants when partially applied. *)
     ({Thy = "arithmetic", Name = "ZERO"}, 0)]

  val num_type = Type.mk_thy_type
    {Thy = "num", Tyop = "num", Args = []}
  val int_type = Type.mk_thy_type
    {Thy = "integer", Tyop = "int", Args = []}
  val frac_type = Type.mk_thy_type
    {Thy = "frac", Tyop = "frac", Args = []}
  val frac_pair_type = pairSyntax.mk_prod (int_type, int_type)
  val unsigned_bit_type = Type.mk_thy_type
    {Thy = "refute", Tyop = "unsigned_bit", Args = []}
  val signed_bit_type = Type.mk_thy_type
    {Thy = "refute", Tyop = "signed_bit", Args = []}
  val bisim_iterator_type = Type.mk_thy_type
    {Thy = "refute", Tyop = "bisim_iterator", Args = []}

  fun bisim_const ty = Term.mk_thy_const
    {Thy = "refute", Name = "bisim",
     Ty = Type.-->(bisim_iterator_type,
       Type.-->(ty, Type.-->(ty, Type.bool)))}

  val bisim_iterator_max_const = Term.mk_thy_const
    {Thy = "refute", Name = "bisim_iterator_max",
     Ty = bisim_iterator_type}
  val bisim_suc_const = Term.mk_thy_const
    {Thy = "refute", Name = "bisim_suc",
     Ty = Type.-->(bisim_iterator_type, bisim_iterator_type)}
  val bisim_zero_const = Term.mk_thy_const
    {Thy = "refute", Name = "bisim_zero", Ty = bisim_iterator_type}

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

  fun unbinarize_nat_and_int_in_type ty =
    if ty = unsigned_bitword_type then num_type
    else if ty = signed_bitword_type then int_type
    else if Type.is_vartype ty then ty
    else
      let val {Thy, Tyop, Args} = Type.dest_thy_type ty
      in Type.mk_thy_type {Thy = Thy, Tyop = Tyop,
           Args = map unbinarize_nat_and_int_in_type Args}
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

  fun registered_frac_type ty =
    case Lib.total Type.dest_thy_type ty of
        SOME {Thy, Tyop, Args = []} =>
          List.exists (fn ({tyop, ...} : frac_info) =>
            #Thy tyop = Thy andalso #Tyop tyop = Tyop) (!frac_registry)
      | _ => false

  fun frac_target_for_constant constant =
    let
      val key = original_const_key constant
      val source = Term.prim_mk_const {Thy = #Thy key, Name = #Name key}
      fun merge (NONE, target) = target
        | merge (target, NONE) = target
        | merge (SOME left, SOME right) =
            if left = right then SOME left else raise Match
      fun descend source_ty target_ty =
        if source_ty = frac_type then
          if registered_frac_type target_ty then SOME target_ty else raise Match
        else if Type.is_vartype source_ty then NONE
        else
          let
            val source_parts = Type.dest_thy_type source_ty
            val target_parts = Type.dest_thy_type target_ty
            val _ = if #Thy source_parts = #Thy target_parts andalso
                           #Tyop source_parts = #Tyop target_parts andalso
                           length (#Args source_parts) =
                             length (#Args target_parts) then ()
                    else raise Match
          in
            ListPair.foldlEq (fn (source_arg, target_arg, result) =>
              merge (result, descend source_arg target_arg)) NONE
              (#Args source_parts, #Args target_parts)
          end
    in
      descend (Term.type_of source) (Term.type_of constant)
    end handle HOL_ERR _ => NONE | Match => NONE

  fun replace_frac_type target ty =
    if ty = frac_type then target
    else if Type.is_vartype ty then ty
    else
      let val {Thy, Tyop, Args} = Type.dest_thy_type ty
      in Type.mk_thy_type
        {Thy = Thy, Tyop = Tyop,
         Args = map (replace_frac_type target) Args}
      end

  (* A monomorphic Frac operation retyped to a registered carrier cannot be
     a HOL constant.  All such occurrences, including the synthetic typedef's
     abs/rep pair, must nevertheless denote one reserved constant layer.
     A different layer string here creates a second Kodkod relation with the
     same printed raw name and disconnects the carrier axioms from
     operations. *)
  fun retype_frac_constant term ty = retype_constant "frac" term ty

  fun specialize_frac_prop target wanted prop =
    let
      val wanted_key = original_const_key wanted
      fun transform candidate =
        if Term.is_var candidate then
          let val (name, ty) = Term.dest_var candidate
          in Term.mk_var (name, replace_frac_type target ty) end
        else if Term.is_const candidate then
          let
            val ty = replace_frac_type target (Term.type_of candidate)
          in
            if same_key (original_const_key candidate) wanted_key andalso
               ty = Term.type_of wanted then wanted
            else retype_frac_constant candidate ty
          end
        else if Term.is_abs candidate then
          let val (variable, body) = Term.dest_abs candidate
          in Term.mk_abs (transform variable, transform body) end
        else
          let val (function, argument) = Term.dest_comb candidate
          in Term.mk_comb (transform function, transform argument) end
    in
      transform prop
    end

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
      val key = original_const_key constant
      val ty = unbinarize_nat_and_int_in_type (Term.type_of constant)
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

  fun is_registered_lfp constant =
    Option.isSome (KNametab.lookup (IndDefLib.rule_induction_map ())
      (original_const_key constant))
    handle HOL_ERR _ => false

  fun is_registered_gfp constant =
    Option.isSome (KNametab.lookup (CoIndDefLib.coinduction_map ())
      (original_const_key constant))
    handle HOL_ERR _ => false

  fun fixpoint_kind_from_memberships gfp lfp =
    if gfp then Gfp else if lfp then Lfp else NoFp

  fun raw_fixpoint_kind constant =
    fixpoint_kind_from_memberships
      (is_registered_gfp constant) (is_registered_lfp constant)

  (* Boolean-valued COND is not arity-limited because the nut layer handles
     fully applied Boolean conditionals.  It is nevertheless on the built-in
     table and must not be expanded through HOL4's choice-based COND_DEF. *)
  fun is_never_unfold_const constant =
    let
      val key = const_key constant
      val ty = Term.type_of constant
    in
      Option.isSome (generic_built_in_arity key) orelse
      Option.isSome (typed_built_in_arity key ty) orelse
      raw_fixpoint_kind constant <> NoFp
    end handle HOL_ERR _ => false

  (* A generated unroll name is shared by all type instances of its source
     predicate.  Do not reuse a polymorphic equation after instantiation if
     its iterator marker still carries another instance's token. *)
  fun has_matching_iterator_markers constant prop =
    case Lib.total Term.dest_var constant of
        SOME (name, ty) =>
          if Refute_ModelFinder_Names.is_unrolled_name name then
            let
              val (iterator_ty, _) = Type.dom_rng ty
              val token = String.extract
                (Type.dest_vartype iterator_ty, 1, NONE)
              val zero = Refute_ModelFinder_Names.mk_iterator_zero
                token iterator_ty
              val successor = Refute_ModelFinder_Names.mk_iterator_suc
                token iterator_ty
              fun matches candidate =
                case Lib.total Term.dest_var candidate of
                    SOME (candidate_name, _) =>
                      if Refute_ModelFinder_Names.is_iterator_zero_name
                           candidate_name then
                        Term.aconv candidate zero
                      else if
                        Refute_ModelFinder_Names.is_iterator_suc_name
                          candidate_name then
                        Term.aconv candidate successor
                      else true
                  | NONE => true
            in
              List.all matches (HolKernel.find_terms Term.is_var prop)
            end
            handle HOL_ERR _ => false
          else true
      | NONE => true

  fun def_props_for_const table constant =
    if is_built_in_const constant then []
    else
      let
        val props =
          case frac_target_for_constant constant of
              NONE => table_lookup table constant
            | SOME target =>
                let val key = original_const_key constant
                in
                  rev (Option.getOpt (KNametab.lookup table key, []))
                  |> map (specialize_frac_prop target constant)
                end
      in
        props
        |> List.mapPartial (fn prop =>
             case matching_instantiations constant prop of
                 first :: _ =>
                   if has_matching_iterator_markers constant first then
                     SOME first
                   else NONE
               | [] => NONE)
      end

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
      |> Util.distinct_terms
    end

  fun nondef_props_for_const table constant =
    List.concat (map (all_instantiations constant)
      (table_lookup table constant))
    |> Util.distinct_terms

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
          if Refute_ModelFinder_Names.is_reserved_name name andalso
             not (Option.isSome (frac_target_for_constant constant)) then NONE
          else Option.map (fn definition => (false, definition))
            (get_def_of_const fallback_table constant)
      | NONE =>
          (case get_def_of_const unfold_table constant of
               SOME definition => SOME (true, definition)
             | NONE => Option.map (fn definition => (false, definition))
                 (get_def_of_const fallback_table constant))

  fun def_of_const context = Option.map #2 o def_of_const_ext context

  fun fixpoint_kind_of_rhs rhs =
    let
      fun strip_abstractions term =
        if Term.is_abs term then strip_abstractions (Term.body term)
        else term
      val (head, _) = HolKernel.strip_comb (strip_abstractions rhs)
    in
      if Term.is_const head andalso
         same_key (const_key head) {Thy = "fixedPoint", Name = "gfp"}
      then Gfp
      else NoFp
    end
    handle HOL_ERR _ => NoFp

  (* CoIndDefLib's registry is authoritative for package-generated gfps.
     A definition headed directly by fixedPoint$gfp but absent from that
     registry has none of the rules/cases evidence needed by the encoding. *)
  fun is_hand_rolled_gfp context constant =
    raw_fixpoint_kind constant = NoFp andalso
    (case def_of_const context constant of
         SOME rhs => fixpoint_kind_of_rhs rhs = Gfp
       | NONE => false)

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

  (* Bracketed tools may transiently register a DefnBase presentation and
     then delete its scratch constant.  The DefnBase store retains such
     entries, and current_userdefs reconstructs every presentation with
     prim_mk_const, so one stale entry makes an otherwise unrelated later
     MF run fail.  Discover presentations through the live constant table
     instead, so lookup_userdef is called only on constants that still
     exist. *)
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
      val refute_simp_props =
        theorem_set_props Refute_Core.refute_simp "refute_simp"
      val refute_simp_keys = map (#1 o pair_for_prop) refute_simp_props
      fun is_refute_simp_key prop =
        let val key = #1 (pair_for_prop prop)
        in List.exists (same_key key) refute_simp_keys end
      (* A refute_simp restatement replaces, rather than supplements, the
         DefnBase equations for its head constant.  This is HOL4's static
         counterpart of Isabelle's [nitpick_simp del]: retaining an old
         SUC-pattern clause would make may_use_binary_ints reject the whole
         definition despite the Suc-free restatement. *)
      val simp_props =
        List.filter (not o is_refute_simp_key)
          (user_simp_props presentations) @ refute_simp_props
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

  fun prop_key prop = #1 (pair_for_prop prop)

  fun case_prop_key prop =
    let
      val (_, body) = boolSyntax.strip_forall prop
      val (premises, equation) = boolSyntax.strip_imp body
      val (left, _) = boolSyntax.dest_eq equation
      val (head, arguments) = HolKernel.strip_comb left
    in
      if null premises andalso Term.is_const head andalso
         List.all Term.is_var arguments then SOME (const_key head)
      else NONE
    end
    handle HOL_ERR _ => NONE

  fun same_conclusion left right =
    Term.aconv (Thm.concl left) (Thm.concl right)

  fun registered_stem Lfp key stem =
        (let
           val theorem = DB.fetch (#Thy key) (stem ^ "_strongind")
           val registered = Option.getOpt
             (KNametab.lookup (IndDefLib.rule_induction_map ()) key, [])
         in
           List.exists (same_conclusion theorem) registered
         end
         handle HOL_ERR _ => false)
    | registered_stem Gfp key stem =
        (let
           val theorem = DB.fetch (#Thy key) (stem ^ "_coind")
           val registered = Option.getOpt
             (KNametab.lookup (CoIndDefLib.coinduction_map ()) key, [])
         in
           List.exists (same_conclusion theorem) registered
         end
         handle HOL_ERR _ => false)
    | registered_stem NoFp _ _ = false

  fun theorem_has_member key theorem =
    List.exists (fn prop =>
      case case_prop_key prop of
          SOME head => same_key head key
        | NONE => false) (quantified_conjuncts theorem)
    handle HOL_ERR _ => false

  fun drop_cases_suffix name =
    String.substring (name, 0, size name - size "_cases")

  fun locate_cases_theorem kind ({Thy, Name} : kname) =
    let
      val key = {Thy = Thy, Name = Name}
      fun usable stem theorem =
        registered_stem kind key stem andalso
        theorem_has_member key theorem
      fun scan () =
        List.find (fn (binding, theorem) =>
          String.isSuffix "_cases" binding andalso
          usable (drop_cases_suffix binding) theorem)
          (DB.theorems Thy)
        |> Option.map (fn (binding, theorem) =>
             (drop_cases_suffix binding, theorem))
      val fast = Lib.total (DB.fetch Thy) (Name ^ "_cases")
    in
      case fast of
          SOME theorem => if usable Name theorem then
              SOME (Name, theorem) else scan ()
        | NONE => scan ()
    end
    handle HOL_ERR _ => NONE

  fun cache_lookup key entries =
    Option.map #2 (List.find (fn (other, _) => same_key other key) entries)

  fun fixpoint_group_of_const
        ({intro_table, case_table, fixpoint_cache, ...} : mf_context)
        constant =
    if is_built_in_const constant then NONE
    else
      let
        val key = original_const_key constant
        val kind = raw_fixpoint_kind constant
      in
        case cache_lookup key (!fixpoint_cache) of
            SOME result => result
          | NONE =>
              if kind = NoFp then
                (fixpoint_cache := (key, NONE) :: !fixpoint_cache; NONE)
              else
                (case locate_cases_theorem kind key of
                     NONE =>
                       (fixpoint_cache := (key, NONE) :: !fixpoint_cache;
                        NONE)
                   | SOME (stem, cases_theorem) =>
                       let
                         val rules_theorem = DB.fetch (#Thy key)
                           (stem ^ "_rules")
                         val cases = quantified_conjuncts cases_theorem
                         val rules = quantified_conjuncts rules_theorem
                         val member_options = map case_prop_key cases
                         val members = List.mapPartial (fn value => value)
                           member_options
                         val rule_heads = map prop_key rules
                         val valid = length members = length cases andalso
                           not (null rules) andalso
                           List.all (fn member =>
                             registered_stem kind member stem) members andalso
                           List.all (fn head => List.exists
                             (same_key head) members) rule_heads
                         val _ = if valid then () else
                           raise err "fixpoint_group_of_const"
                             "malformed fixpoint theorem group"
                         val group : fixpoint_group =
                           {kind = kind, stem = stem, members = members,
                            rules = rules, cases = cases}
                         fun install (member, entries) =
                           (member, SOME group) ::
                           List.filter (fn (other, _) =>
                             not (same_key other member)) entries
                         val _ = fixpoint_cache :=
                           List.foldl install (!fixpoint_cache) members
                         val _ = intro_table := List.foldl
                           (fn (prop, table) =>
                             let val (head, value) = pair_for_prop prop
                             in table_append head value table end)
                           (!intro_table) rules
                         val _ = case_table := List.foldl
                           (fn (prop, table) =>
                             let val (head, value) = pair_for_prop prop
                             in table_append head value table end)
                           (!case_table) cases
                       in
                         SOME group
                       end
                       handle HOL_ERR _ =>
                         (fixpoint_cache := (key, NONE) :: !fixpoint_cache;
                          NONE))
      end
      handle HOL_ERR _ => NONE

  fun fixpoint_kind_of_const context constant =
    case fixpoint_group_of_const context constant of
        SOME {kind, ...} => kind
      | NONE => raw_fixpoint_kind constant

  fun generated_name constant =
    case Lib.total Term.dest_var constant of
        SOME (name, _) =>
          if Refute_ModelFinder_Names.is_reserved_name name then SOME name
          else NONE
      | NONE => NONE

  fun is_fixpoint_bound_const constant =
    case generated_name constant of
        SOME name => Refute_ModelFinder_Names.is_ubfp_name name orelse
                     Refute_ModelFinder_Names.is_lbfp_name name
      | NONE => false

  fun is_unrolled_const constant =
    case generated_name constant of
        SOME name => Refute_ModelFinder_Names.is_unrolled_name name
      | NONE => false

  fun is_iterator_marker_const constant =
    case generated_name constant of
        SOME name =>
          Refute_ModelFinder_Names.is_iterator_zero_name name orelse
          Refute_ModelFinder_Names.is_iterator_suc_name name
      | NONE => false

  fun is_raw_inductive_pred context constant =
    not (is_built_in_const constant) andalso
    not (is_fixpoint_bound_const constant) andalso
    not (is_unrolled_const constant) andalso
    not (is_iterator_marker_const constant) andalso
    fixpoint_kind_of_const context constant <> NoFp

  fun is_inductive_pred context constant =
    is_raw_inductive_pred context constant orelse
    is_fixpoint_bound_const constant

  fun is_mutually_inductive_pred context constant =
    case fixpoint_group_of_const context constant of
        SOME {members, ...} => length members > 1
      | NONE => false

  type fixpoint_group_instance =
    {kind : fixpoint_kind, stem : string, members : term list,
     rules : term list, cases : term list}

  fun case_prop_head prop =
    let
      val (_, body) = boolSyntax.strip_forall prop
      val (_, equation) = boolSyntax.strip_imp body
      val (left, _) = boolSyntax.dest_eq equation
    in
      #1 (HolKernel.strip_comb left)
    end

  (* One type substitution is shared by every theorem in a mutual group.
     Instantiating the members independently could break the cross-member
     occurrences that joint wf and unrolling must replace in lockstep. *)
  fun instantiated_fixpoint_group context constant =
    case fixpoint_group_of_const context constant of
        NONE => NONE
      | SOME {kind, stem, rules, cases, ...} =>
          let
            val key = original_const_key constant
            val raw_head =
              case List.find (fn prop =>
                     same_key (const_key (case_prop_head prop)) key) cases of
                  SOME prop => case_prop_head prop
                | NONE => raise err "instantiated_fixpoint_group"
                    "queried member has no cases equation"
            val theta = Type.match_type (Term.type_of raw_head)
              (Term.type_of constant)
            val cases = map (Term.inst theta) cases
            val rules = map (Term.inst theta) rules
            val members = map case_prop_head cases
          in
            SOME {kind = kind, stem = stem, members = members,
                  rules = rules, cases = cases}
          end
          handle HOL_ERR _ => NONE

  fun intro_props_for_const context constant =
    (ignore (fixpoint_group_of_const context constant);
     def_props_for_const (!(#intro_table context)) constant)

  fun case_props_for_const context constant =
    (ignore (fixpoint_group_of_const context constant);
     def_props_for_const (!(#case_table context)) constant)

  fun is_raw_equational_fun
        ({simp_table, psimp_table, ...} : mf_context) constant =
    not (null (def_props_for_const (!simp_table) constant)) orelse
    not (null (def_props_for_const psimp_table constant))

  fun is_equational_fun context constant =
    is_raw_equational_fun context constant orelse
    is_raw_inductive_pred context constant

  fun substituted_fixpoint_axioms context generated =
    let
      val key = original_const_key generated
      val original = Term.mk_thy_const
        {Thy = #Thy key, Name = #Name key, Ty = Term.type_of generated}
      val upper =
        case generated_name generated of
            SOME name => Refute_ModelFinder_Names.is_ubfp_name name
          | NONE => raise err "substituted_fixpoint_axioms"
              "fixpoint bound has no generated name"
      val {members, cases, ...} =
        case instantiated_fixpoint_group context original of
            SOME group => group
          | NONE => raise err "substituted_fixpoint_axioms"
              "fixpoint bound has no theorem group"
      fun bound member =
        let
          val member_key = original_const_key member
          val name = #Thy member_key ^ Refute_ModelFinder_Names.name_sep ^
            #Name member_key
        in
          if upper then Refute_ModelFinder_Names.mk_ubfp name
              (Term.type_of member)
          else Refute_ModelFinder_Names.mk_lbfp name
              (Term.type_of member)
        end
      val substitution = ListPair.map (fn (member, replacement) =>
        {redex = member, residue = replacement})
        (members, map bound members)
      val own_cases = List.filter (fn prop =>
        same_key (const_key (case_prop_head prop)) key) cases
    in
      map (Term.subst substitution) own_cases
    end

  fun equational_fun_axioms
        (context as {simp_table, psimp_table, ...} : mf_context) constant =
    case def_props_for_const (!simp_table) constant of
        [] =>
          (case def_props_for_const psimp_table constant of
               [] =>
                 if is_fixpoint_bound_const constant then
                   substituted_fixpoint_axioms context constant
                 else if is_raw_inductive_pred context constant then
                   case_props_for_const context constant
                 else
                 (case def_of_const context constant of
                      SOME definition =>
                        (case equationalize_term "definition"
                           (boolSyntax.mk_eq (constant, definition)) of
                             SOME equation => [equation]
                           | NONE => [])
                    | NONE => [])
             | psimps => psimps)
      | simps => simps

  fun same_fixpoint_const left right =
    same_key (original_const_key left) (original_const_key right) andalso
    Lib.can (Type.match_type (Term.type_of right)) (Term.type_of left)
    handle HOL_ERR _ => false

  fun term_mentions_const constant term =
    List.exists (fn candidate =>
      (Term.is_const candidate orelse Term.is_var candidate) andalso
      same_key (original_const_key candidate)
        (original_const_key constant)
      handle HOL_ERR _ => false)
      (HolKernel.find_terms (fn candidate =>
         Term.is_const candidate orelse Term.is_var candidate) term)

  type intro_triple =
    {variables : term list, side : term list,
     main : term list, conclusion : term}

  fun intro_triple_for constant rule =
    let
      val (variables, body) = boolSyntax.strip_forall rule
      val (raw_premises, conclusion) = boolSyntax.strip_imp body
      val premises = List.concat (map boolSyntax.strip_conj raw_premises)
      val (main, side) = List.partition
        (term_mentions_const constant) premises
      fun directly_headed premise =
        let val (head, _) = HolKernel.strip_comb premise
        in same_fixpoint_const head constant end
      val (conclusion_head, _) = HolKernel.strip_comb conclusion
    in
      if same_fixpoint_const conclusion_head constant andalso
         List.all directly_headed main then
        SOME {variables = variables, side = side, main = main,
              conclusion = conclusion}
      else
        NONE
    end
    handle HOL_ERR _ => NONE

  fun tuple_term [] = oneSyntax.one_tm
    | tuple_term [term] = term
    | tuple_term terms = pairSyntax.list_mk_pair terms

  fun tuple_type [] = oneSyntax.one_ty
    | tuple_type [ty] = ty
    | tuple_type tys = pairSyntax.list_mk_prod tys

  fun wf_problem constant rules =
    let
      val triples = List.mapPartial (intro_triple_for constant) rules
      val malformed = length triples <> length rules
      val (_, argument_tys) =
        let val (domains, range) = boolSyntax.strip_fun
              (Term.type_of constant)
        in
          if range = Type.bool then (range, domains)
          else raise err "wf_problem" "predicate does not return bool"
        end
      val domain_ty = tuple_type argument_tys
      val relation = Term.variant
        (List.concat (map Term.all_vars rules))
        (Term.mk_var ("R",
          Type.-->(domain_ty, Type.-->(domain_ty, Type.bool))))
      fun constraint
            ({variables, side, main, conclusion} : intro_triple) recursive =
        let
          val (_, recursive_args) = HolKernel.strip_comb recursive
          val (_, conclusion_args) = HolKernel.strip_comb conclusion
          val decrease = Term.list_mk_comb
            (relation, [tuple_term recursive_args,
                        tuple_term conclusion_args])
        in
          boolSyntax.list_mk_forall
            (variables, boolSyntax.list_mk_imp (side, decrease))
        end
      val constraints = List.concat (map (fn triple =>
        map (constraint triple) (#main triple)) triples)
      val proposition = boolSyntax.mk_exists (relation,
        boolSyntax.mk_conj
          (relationSyntax.mk_wf relation,
           if null constraints then boolSyntax.T
           else boolSyntax.list_mk_conj constraints))
      fun argument_pairs
            ({main, conclusion, ...} : intro_triple) =
        let val (_, conclusion_args) = HolKernel.strip_comb conclusion
        in map (fn recursive =>
             let val (_, recursive_args) = HolKernel.strip_comb recursive
             in ListPair.zip (recursive_args, conclusion_args) end) main
        end
    in
      {malformed = malformed, proposition = proposition,
       argument_tys = argument_tys,
       pairs = List.concat (map argument_pairs triples),
       recursive = not (null constraints)}
    end

  fun member_index members candidate =
    let
      fun find _ [] = NONE
        | find index (member :: rest) =
            if same_fixpoint_const candidate member then SOME index
            else find (index + 1) rest
    in
      find 0 members
    end

  fun inject_sum tys index value =
    case (tys, index) of
        ([_], 0) => value
      | (ty :: rest, 0) =>
          sumSyntax.mk_inl (value, sumSyntax.list_mk_sum rest)
      | (ty :: rest, index) =>
          if index > 0 then
            sumSyntax.mk_inr (inject_sum rest (index - 1) value, ty)
          else raise err "inject_sum" "negative member index"
      | _ => raise err "inject_sum" "member index outside sum"

  fun joint_intro_triple_for members rule =
    let
      val (variables, body) = boolSyntax.strip_forall rule
      val (raw_premises, conclusion) = boolSyntax.strip_imp body
      val premises = List.concat (map boolSyntax.strip_conj raw_premises)
      fun mentions_member premise = List.exists (fn member =>
        term_mentions_const member premise) members
      val (main, side) = List.partition mentions_member premises
      fun direct_member premise =
        member_index members (#1 (HolKernel.strip_comb premise))
      val conclusion_member = direct_member conclusion
    in
      if Option.isSome conclusion_member andalso
         List.all (Option.isSome o direct_member) main then
        SOME {variables = variables, side = side, main = main,
              conclusion = conclusion}
      else NONE
    end
    handle HOL_ERR _ => NONE

  fun joint_wf_problem members rules =
    let
      val triples = List.mapPartial
        (joint_intro_triple_for members) rules
      val malformed = length triples <> length rules
      fun argument_tys member =
        let val (domains, range) = boolSyntax.strip_fun
              (Term.type_of member)
        in
          if range = Type.bool then domains
          else raise err "joint_wf_problem"
            "group member does not return bool"
        end
      val argument_tyss = map argument_tys members
      val tuple_tys = map tuple_type argument_tyss
      val domain_ty = sumSyntax.list_mk_sum tuple_tys
      val relation = Term.variant
        (List.concat (map Term.all_vars rules))
        (Term.mk_var ("R",
          Type.-->(domain_ty, Type.-->(domain_ty, Type.bool))))
      fun constraint
            ({variables, side, main, conclusion} : intro_triple) recursive =
        let
          val (recursive_head, recursive_args) =
            HolKernel.strip_comb recursive
          val (conclusion_head, conclusion_args) =
            HolKernel.strip_comb conclusion
          val recursive_index = valOf
            (member_index members recursive_head)
          val conclusion_index = valOf
            (member_index members conclusion_head)
          val decrease = Term.list_mk_comb
            (relation,
             [inject_sum tuple_tys recursive_index
                (tuple_term recursive_args),
              inject_sum tuple_tys conclusion_index
                (tuple_term conclusion_args)])
        in
          boolSyntax.list_mk_forall
            (variables, boolSyntax.list_mk_imp (side, decrease))
        end
      val constraints = List.concat (map (fn triple =>
        map (constraint triple) (#main triple)) triples)
      val proposition = boolSyntax.mk_exists (relation,
        boolSyntax.mk_conj
          (relationSyntax.mk_wf relation,
           if null constraints then boolSyntax.T
           else boolSyntax.list_mk_conj constraints))
    in
      {malformed = malformed, proposition = proposition,
       argument_tyss = argument_tyss,
       recursive = not (null constraints)}
    end

  fun permutations values =
    let
      fun insert value [] = [[value]]
        | insert value (head :: tail) =
            (value :: head :: tail) ::
            map (fn rest => head :: rest) (insert value tail)
    in
      List.foldl (fn (value, result) =>
        List.concat (map (insert value) result)) [[]] values
    end

  fun lex_relation 1 = numSyntax.less_tm
    | lex_relation count = pairSyntax.mk_lex
        (numSyntax.less_tm, lex_relation (count - 1))

  fun wf_candidates argument_tys pairs =
    let
      val domain_ty = tuple_type argument_tys
      val arguments = List.tabulate (length argument_tys, fn index =>
        Term.mk_var ("v" ^ Int.toString index,
          List.nth (argument_tys, index)))
      val tuple = tuple_term arguments
      fun size_function ty =
        TypeBasePure.type_size (TypeBase.theTypeBase ()) ty
      fun component_size (argument, ty) =
        Term.mk_comb (size_function ty, argument)
      fun abstraction body =
        if length arguments <= 1 then
          Term.mk_abs
            (if null arguments then
               Term.mk_var ("u", oneSyntax.one_ty)
             else hd arguments, body)
        else
          pairSyntax.mk_pabs (tuple, body)
      fun measure_of index =
        numSyntax.mk_cmeasure
          (abstraction (component_size
            (List.nth (arguments, index),
             List.nth (argument_tys, index))))
      val whole = Lib.total (fn ty =>
        numSyntax.mk_cmeasure (size_function ty)) domain_ty
      val components = List.mapPartial (fn index =>
        Lib.total measure_of index)
        (List.tabulate (length argument_tys, fn index => index))
      fun changed index = List.exists (fn row =>
        let val (left, right) = List.nth (row, index)
        in not (Term.aconv left right) end) pairs
      val changed_indices = List.filter changed
        (List.tabulate (length argument_tys, fn index => index))
      (* Cap factorial permutation growth as TotalDefn does, but retain
         forward and reverse measures over every changed component. *)
      val arrangements =
        if length changed_indices > 4 then
          permutations (List.take (changed_indices, 4)) @
          [changed_indices, rev changed_indices]
        else
          permutations changed_indices
      fun lex_candidate indices =
        if null indices then NONE
        else
          let
            val sizes = map (fn index => component_size
              (List.nth (arguments, index),
               List.nth (argument_tys, index))) indices
            val image = abstraction (tuple_term sizes)
          in
            SOME (relationSyntax.mk_inv_image
              (lex_relation (length indices), image))
          end
          handle HOL_ERR _ => NONE
      val lex = List.mapPartial lex_candidate arrangements
    in
      Util.distinct_terms ((case whole of SOME value => [value] | NONE => []) @
        components @ lex)
    end

  fun joint_wf_candidates argument_tyss =
    let
      val tuple_tys = map tuple_type argument_tyss
      val sum_ty = sumSyntax.list_mk_sum tuple_tys

      fun tuple_abstraction argument_tys body_for =
        let
          val arguments = List.tabulate (length argument_tys, fn index =>
            Term.mk_var ("v" ^ Int.toString index,
              List.nth (argument_tys, index)))
          val tuple = tuple_term arguments
          val body = body_for arguments
        in
          if length arguments <= 1 then
            Term.mk_abs
              (if null arguments then
                 Term.mk_var ("u", oneSyntax.one_ty)
               else hd arguments, body)
          else pairSyntax.mk_pabs (tuple, body)
        end

      fun sum_case_function [function] = function
        | sum_case_function (function :: rest) =
            let
              val right = sum_case_function rest
              val domain = sumSyntax.mk_sum
                (#1 (Type.dom_rng (Term.type_of function)),
                 #1 (Type.dom_rng (Term.type_of right)))
              val value = Term.mk_var ("s", domain)
            in
              Term.mk_abs (value,
                sumSyntax.mk_sum_case (function, right, value))
            end
        | sum_case_function [] = raise err "joint_wf_candidates"
            "empty fixpoint group"

      fun case_measure functions =
        SOME (numSyntax.mk_cmeasure (sum_case_function functions))
        handle HOL_ERR _ => NONE

      val whole_functions = List.mapPartial (fn ty =>
        Lib.total (TypeBasePure.type_size (TypeBase.theTypeBase ())) ty)
        tuple_tys
      val whole = if length whole_functions = length tuple_tys then
          case_measure whole_functions
        else NONE
      val common_arity = List.foldl Int.min
        (case argument_tyss of [] => 0 | first :: _ => length first)
        (map length argument_tyss)

      fun component_function argument_tys index =
        tuple_abstraction argument_tys (fn arguments =>
          Term.mk_comb
            (TypeBasePure.type_size (TypeBase.theTypeBase ())
               (List.nth (argument_tys, index)),
             List.nth (arguments, index)))

      fun component index =
        let
          val functions = map (fn argument_tys =>
            component_function argument_tys index) argument_tyss
        in
          case_measure functions
        end
        handle HOL_ERR _ => NONE

      val components = List.mapPartial component
        (List.tabulate (common_arity, fn index => index))
      val ordinary = wf_candidates [sum_ty] []
    in
      Util.distinct_terms
        ((case whole of SOME candidate => [candidate] | NONE => []) @
         components @ ordinary)
    end

  val max_cached_wfs = 50
  type cached_wf_state =
    {timeout : Time.time, entries : (term * bool) list}
  val cached_wf_props = Synchronized.var
    "Refute_ModelFinder_HOL.cached_wf_props"
    ({timeout = Time.zeroTime, entries = []} : cached_wf_state)

  fun cached_wf_lookup timeout proposition =
    let val {timeout = old_timeout, entries} =
          Synchronized.value cached_wf_props
    in
      if Time.compare (timeout, old_timeout) <> EQUAL then
        (Synchronized.change cached_wf_props (fn _ =>
           {timeout = timeout, entries = []}); NONE)
      else
        Option.map #2 (List.find (fn (other, _) =>
          Term.aconv other proposition) entries)
    end

  fun cache_wf timeout proposition result =
    Synchronized.change cached_wf_props (fn state =>
      let
        val entries =
          if Time.compare (timeout, #timeout state) <> EQUAL orelse
             length (#entries state) >= max_cached_wfs then []
          else #entries state
      in
        {timeout = timeout, entries = (proposition, result) :: entries}
      end)

  fun prove_wf_candidate timeout proposition candidate =
    let
      open Tactical Tactic
      val tactic = EXISTS_TAC candidate THEN CONJ_TAC THENL
        [TotalDefn.WF_TAC,
         TotalDefn.TC_SIMP_TAC (TotalDefn.termination_ss ()) []]
      fun prove () = ignore (TAC_PROOF (([], proposition), tactic))
    in
      Timeout.apply timeout (fn () => (prove (); true)) ()
    end
    handle Timeout.TIMEOUT _ => false
         | HOL_ERR _ => false

  fun uncached_is_well_founded_inductive_pred context constant =
    let
      val rules = intro_props_for_const context constant
      val {malformed, proposition, argument_tys, pairs, recursive} =
        wf_problem constant rules
    in
      if malformed orelse null rules then false
      else if not recursive then true
      else
        case cached_wf_lookup (#tac_timeout context) proposition of
            SOME result => result
          | NONE =>
              let
                val result = List.exists
                  (prove_wf_candidate (#tac_timeout context) proposition)
                  (wf_candidates argument_tys pairs)
                val _ = cache_wf (#tac_timeout context) proposition result
              in result end
    end
    handle HOL_ERR _ => false

  fun uncached_is_well_founded_group context members rules =
    let
      val {malformed, proposition, argument_tyss, recursive} =
        joint_wf_problem members rules
    in
      if malformed orelse null rules then false
      else if not recursive then true
      else
        case cached_wf_lookup (#tac_timeout context) proposition of
            SOME result => result
          | NONE =>
              let
                val result = List.exists
                  (prove_wf_candidate (#tac_timeout context) proposition)
                  (joint_wf_candidates argument_tyss)
                val _ = cache_wf (#tac_timeout context) proposition result
              in result end
    end
    handle HOL_ERR _ => false

  fun const_match (actual, pattern) =
    same_key (original_const_key actual) (original_const_key pattern) andalso
    Lib.can (Type.match_type (Term.type_of pattern)) (Term.type_of actual)
    handle HOL_ERR _ => false

  fun explicit_wf_override rows constant =
    Option.map #2 (List.find (fn (pattern, _) =>
      case pattern of
          SOME candidate => const_match (constant, candidate)
        | NONE => false) rows)

  fun default_wf_override rows = Option.map #2
    (List.find (fn (pattern, _) => not (Option.isSome pattern)) rows)

  fun wf_override rows constant =
    case explicit_wf_override rows constant of
        SOME value => SOME value
      | NONE => default_wf_override rows

  fun group_wf_override rows members =
    case get_first (explicit_wf_override rows) members of
        SOME value => SOME value
      | NONE => default_wf_override rows

  fun is_well_founded_inductive_pred
        (context as {wfs, wf_cache, ...} : mf_context) constant =
    let
      val instance = instantiated_fixpoint_group context constant
      val members = case instance of
          SOME {members, ...} => members
        | NONE => [constant]
      val override = if length members > 1 then
          group_wf_override wfs members
        else wf_override wfs constant
      fun cached [] = NONE
        | cached (member :: rest) =
            (case List.find (fn (other, _) => Term.aconv other member)
                    (!wf_cache) of
                 SOME (_, (_, result)) => SOME result
               | NONE => cached rest)
      fun remember kind result = wf_cache :=
        List.foldl (fn (member, entries) =>
          (member, (kind = Gfp, result)) :: entries)
          (!wf_cache) members
    in
      case override of
          SOME (SOME result) => result
        | _ =>
            (* Isabelle's hard-wired Nats/fold_graph' entries have no HOL4
               analog; all HOL4 predicates go through the hygienic prover. *)
            (case cached members of
                 SOME result => result
               | NONE =>
                   let
                     val kind = fixpoint_kind_of_const context constant
                     val result = kind <> NoFp andalso
                       (case instance of
                            SOME {rules, ...} =>
                              if length members > 1 then
                                uncached_is_well_founded_group
                                  context members rules
                              else
                                uncached_is_well_founded_inductive_pred
                                  context constant
                          | NONE => false)
                     val _ = remember kind result
                   in result end)
    end

  fun fixpoint_refusal_reason context constant =
    if is_hand_rolled_gfp context constant then
      SOME ("hand-rolled greatest fixpoint " ^
        Parse.term_to_string constant ^ " is not supported; " ^
        "define coinductive predicates with Hol_coreln")
    else
      case raw_fixpoint_kind constant of
          NoFp => NONE
        | raw_kind =>
            (case fixpoint_group_of_const context constant of
                 NONE =>
                   SOME ((if raw_kind = Gfp then "coinductive"
                          else "inductive") ^ " predicate " ^
                     Parse.term_to_string constant ^
                     " has no usable registered _cases/_rules theorem")
               | SOME {kind = Lfp, ...} => NONE
               | SOME {kind = Gfp, ...} => NONE
               | SOME {kind = NoFp, ...} => SOME ("predicate " ^
                   Parse.term_to_string constant ^ " is not a fixpoint"))

  fun first_fixpoint_refusal context term =
    let
      val constants = HolKernel.find_terms Term.is_const term
      fun check [] = NONE
        | check (constant :: rest) =
            if is_hand_rolled_gfp context constant orelse
               is_raw_inductive_pred context constant then
              (case fixpoint_refusal_reason context constant of
                   SOME reason => SOME reason
                 | NONE => check rest)
            else check rest
    in check constants end

  fun print_wf_cache ({wf_cache, ...} : mf_context) =
    List.app (fn (constant, (gfp, proved)) =>
      Refute_Core.Private.say 2
        ("The " ^ (if gfp then "coinductive" else "inductive") ^
         " predicate \"" ^ Parse.term_to_string constant ^ "\" " ^
         (if proved then
            "was proved well-founded; Refute can compute it efficiently\n"
          else
            "could not be proved well-founded; Refute might need to " ^
            "unroll it\n"))) (rev (!wf_cache))

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

  (* Successful harvests live in the normal registries above.  The session
     index records only theories directly mentioned by relevant theorem
     conclusions: the theorem's own theory and the owning theories of its
     constants.  In particular, neither index maintenance nor lookup walks a
     theory ancestry or enumerates the session's constants. *)
  type harvest_fingerprint = int * (string * int) list
  type harvest_miss = harvest_fingerprint KNametab.table
  type harvest_index_entry =
    {operator : type_operator,
     theorem_theories : string list,
     constant_theories : string list}
  type harvest_binding =
    {theory : string,
     name : string,
     theorem_operators : type_operator list,
     constant_operators : (type_operator * string) list}

  val quotient_harvest_misses =
    ref (KNametab.empty : harvest_miss)
  val typedef_harvest_misses =
    ref (KNametab.empty : harvest_miss)
  val quotient_harvest_scan_count = ref 0
  val typedef_harvest_scan_count = ref 0
  val quotient_harvest_scan_theories = ref ([] : string list)
  val typedef_harvest_scan_theories = ref ([] : string list)

  val harvest_session_index =
    ref (KNametab.empty : harvest_index_entry KNametab.table)
  val harvest_session_index_stale = ref false
  val harvest_session_rebuild_count = ref 0
  val harvest_binding_index =
    ref (KNametab.empty : harvest_binding KNametab.table)
  val harvest_theory_bindings =
    ref (Symtab.empty : string list Symtab.table)
  val harvest_operator_generations =
    ref (KNametab.empty : int KNametab.table)
  val harvest_operator_generation = ref 0
  val harvest_indexed_theories =
    ref (Symtab.empty : unit Symtab.table)
  val harvest_pending_theories = ref ([] : string list)
  val harvest_index_theory_scan_theories = ref ([] : string list)

  val harvest_db_generation = ref 0
  val harvest_theory_generations =
    ref (Symtab.empty : int Symtab.table)

  fun scan_harvest_theorems scan_log theory =
    (* Constant specifications (including define_new_type_bijections) are
       stored in HOL4's definition class, whereas quotient saves are ordinary
       theorems.  DB.thms covers both persisted classes. *)
    (scan_log := theory :: !scan_log;
     DB.thms theory)

  fun harvest_index_theory_scan_count () =
    length (!harvest_index_theory_scan_theories)

  fun add_string value values =
    if List.exists (fn old => old = value) values then values
    else value :: values

  fun add_type_operator operator operators =
    if List.exists (fn old => same_type_operator old operator) operators
    then operators
    else operator :: operators

  (* The collectors cons in O(1); reverse once at the construction boundary
     before imposing the canonical theory order. *)
  fun sort_strings values =
    Listsort.sort String.compare (rev values)

  fun type_operators_in_type ty operators =
    case Lib.total Type.dest_thy_type ty of
        NONE => operators
      | SOME {Thy, Tyop, Args} =>
          List.foldl (fn (arg, result) =>
            type_operators_in_type arg result)
            (add_type_operator {Thy = Thy, Tyop = Tyop} operators) Args

  fun type_operators_in_term term =
    let
      val atoms = map #2 (constants_in term) @ Term.all_vars term
    in
      rev (List.foldl (fn (atom, operators) =>
        type_operators_in_type (Term.type_of atom) operators) [] atoms)
    end

  fun constant_operator_pairs term =
    let
      fun add_pair pair pairs =
        if List.exists (fn (old, old_theory) =>
             same_type_operator old (#1 pair) andalso
             old_theory = #2 pair) pairs
        then pairs
        else pairs @ [pair]
      fun add ((_, constant), pairs) =
        let
          val {Thy, ...} = Term.dest_thy_const constant
          val operators = rev (type_operators_in_type
            (Term.type_of constant) [])
        in
          List.foldl (fn (operator, result) =>
            add_pair (operator, Thy) result) pairs operators
        end
    in
      List.foldl add [] (constants_in term)
    end

  fun operator_key ({Thy, Tyop} : type_operator) =
    {Thy = Thy, Name = Tyop}

  fun update_harvest_index operator update table =
    let
      val key = operator_key operator
      val entry =
        Option.getOpt (KNametab.lookup table key,
          {operator = operator, theorem_theories = [],
           constant_theories = []})
    in
      KNametab.update (key, update entry) table
    end

  fun add_theorem_theory operator theory table =
    update_harvest_index operator (fn {operator, theorem_theories,
                                       constant_theories} =>
      {operator = operator,
       theorem_theories = add_string theory theorem_theories,
       constant_theories = constant_theories}) table

  fun add_constant_theory operator theory table =
    update_harvest_index operator (fn {operator, theorem_theories,
                                       constant_theories} =>
      {operator = operator, theorem_theories = theorem_theories,
       constant_theories = add_string theory constant_theories}) table

  fun add_harvest_binding_to_index
        ({theory, theorem_operators, constant_operators, ...} :
         harvest_binding) table =
    let
      val with_theorem = List.foldl (fn (operator, result) =>
        add_theorem_theory operator theory result) table theorem_operators
    in
      List.foldl (fn ((operator, constant_theory), result) =>
        add_constant_theory operator constant_theory result)
        with_theorem constant_operators
    end

  fun rebuild_harvest_session_index () =
    (harvest_session_rebuild_count :=
       !harvest_session_rebuild_count + 1;
     harvest_session_index := KNametab.fold
       (fn (_, binding) => fn table =>
         add_harvest_binding_to_index binding table)
       (!harvest_binding_index) KNametab.empty)

  fun binding_operators
        ({theorem_operators, constant_operators, ...} : harvest_binding) =
    rev (List.foldl (fn (operator, result) =>
      add_type_operator operator result) []
      (theorem_operators @ map #1 constant_operators))

  fun note_harvest_operator_changes operators =
    if null operators then ()
    else
      let val generation = !harvest_operator_generation + 1
      in
        harvest_operator_generation := generation;
        harvest_operator_generations := List.foldl
          (fn (operator, table) =>
            KNametab.update (operator_key operator, generation) table)
          (!harvest_operator_generations) operators
      end

  fun note_harvest_theory_binding theory name =
    let
      val names = Option.getOpt
        (Symtab.lookup (!harvest_theory_bindings) theory, [])
    in
      harvest_theory_bindings := Symtab.update
        (theory, name :: names) (!harvest_theory_bindings)
    end

  fun forget_harvest_theory_binding theory name =
    case Symtab.lookup (!harvest_theory_bindings) theory of
        NONE => ()
      | SOME names =>
          let val remaining = List.filter (fn old => old <> name) names
          in
            harvest_theory_bindings :=
              if null remaining then
                Symtab.delete_safe theory (!harvest_theory_bindings)
              else
                Symtab.update (theory, remaining)
                  (!harvest_theory_bindings)
          end

  fun remove_harvest_binding theory name =
    let val key = {Thy = theory, Name = name}
    in
      case KNametab.lookup (!harvest_binding_index) key of
          NONE => ()
        | SOME old =>
            (note_harvest_operator_changes (binding_operators old);
             harvest_binding_index := KNametab.delete key
               (!harvest_binding_index);
             forget_harvest_theory_binding theory name;
             harvest_session_index_stale := true)
    end

  fun remove_harvest_theory theory =
    let
      fun remove (name, (table, removed)) =
        let val key = {Thy = theory, Name = name}
        in
          case KNametab.lookup table key of
              NONE => (table, removed)
            | SOME binding =>
                (KNametab.delete key table, binding :: removed)
        end
      val names = Option.getOpt
        (Symtab.lookup (!harvest_theory_bindings) theory, [])
      val (kept, removed) =
        List.foldl remove (!harvest_binding_index, []) names
      val operators = rev (List.foldl (fn (binding, result) =>
        List.foldl (fn (operator, operators) =>
          add_type_operator operator operators) result
          (binding_operators binding)) [] removed)
      val _ = note_harvest_operator_changes operators
    in
      harvest_binding_index := kept;
      harvest_theory_bindings :=
        Symtab.delete_safe theory (!harvest_theory_bindings);
      if null removed then () else harvest_session_index_stale := true
    end

  fun note_harvest_binding theory (name, theorem) =
    if Theory.is_temp_binding name then ()
    else
      let
        val conclusion = Thm.concl theorem
        val binding : harvest_binding =
          {theory = theory, name = name,
           theorem_operators = type_operators_in_term conclusion,
           constant_operators = constant_operator_pairs conclusion}
        val key = {Thy = theory, Name = name}
        val replacing =
          Option.isSome (KNametab.lookup (!harvest_binding_index) key)
        val _ = harvest_binding_index :=
          KNametab.update (key, binding) (!harvest_binding_index)
        val _ =
          if replacing then () else note_harvest_theory_binding theory name
        val _ = note_harvest_operator_changes
          (binding_operators binding)
      in
        if replacing then harvest_session_index_stale := true
        else harvest_session_index := add_harvest_binding_to_index binding
          (!harvest_session_index)
      end

  fun index_harvest_theory theory =
    let
      val theorems =
        scan_harvest_theorems harvest_index_theory_scan_theories theory
      val _ = remove_harvest_theory theory
      val _ = List.app (note_harvest_binding theory) theorems
    in
      harvest_indexed_theories := Symtab.update (theory, ())
        (!harvest_indexed_theories)
    end
    handle HOL_ERR _ => ()

  fun note_harvest_db_change theory =
    let val generation = !harvest_db_generation + 1
    in
      harvest_db_generation := generation;
      harvest_theory_generations := Symtab.update (theory, generation)
        (!harvest_theory_generations)
    end

  fun harvest_db_hook delta =
    with_registration_lock (fn () =>
      let
        fun current () = Theory.current_theory ()
        fun changed theory = note_harvest_db_change theory
        fun invalidate theory =
          (changed theory;
           harvest_indexed_theories :=
             Symtab.delete_safe theory (!harvest_indexed_theories);
           harvest_pending_theories := theory :: !harvest_pending_theories)
        fun add theory named_theorem =
          (changed theory; note_harvest_binding theory named_theorem)
      in
        case delta of
            TheoryDelta.NewBinding (name, (theorem, _)) =>
              if Theory.is_temp_binding name then ()
              else add (current ()) (name, theorem)
          | TheoryDelta.UpdBinding (name, {thm, ...}) =>
              if Theory.is_temp_binding name then ()
              else
                (remove_harvest_binding (current ()) name;
                 add (current ()) (name, thm))
          | TheoryDelta.DelBinding name =>
              if Theory.is_temp_binding name then ()
              else
                (changed (current ());
                 remove_harvest_binding (current ()) name)
          | TheoryDelta.NewTheory {oldseg, newseg} =>
              (Option.app changed oldseg; changed newseg)
          | TheoryDelta.ExportTheory theory =>
              invalidate theory
          | TheoryDelta.TheoryLoaded theory =>
              invalidate theory
          | _ => ()
      end)

  val _ = Theory.register_hook ("Refute_ModelFinder_HOL.harvest_db",
                                harvest_db_hook)

  (* [bin/hol run] loads no prelude, so a script can reach [load "Refute"]
     before any theory segment exists and the kernel then has no current
     theory at all.  Ask for it the way [Theory.get_parents] does rather
     than through [current_theory], which raises in that state; the
     ancestry below goes through [Graph.fringe] and needs no segment. *)
  fun theory_is_available theory =
    (case Thm.getCT () of SOME current => theory = current | NONE => false)
    orelse Lib.mem theory (Theory.ancestry "-")

  fun primitive_constant key = Term.prim_mk_const
    {Thy = #Thy key, Name = #Name key}

  fun distinct_type_variables function tys =
    let
      fun add (ty, seen) =
        if List.exists (fn old => Type.compare (ty, old) = EQUAL) seen then
          raise err function "type arguments must be distinct type variables"
        else
          ty :: seen
    in
      if List.all Type.is_vartype tys then
        ignore (List.foldl add [] tys)
      else
        raise err function "type arguments must all be type variables"
    end

  fun distinct_types tys = distinct_type_variables "register_codatatype" tys

  fun interpreted_type_operator ({Thy, Tyop} : type_operator) =
    (Thy = "min" andalso (Tyop = "bool" orelse Tyop = "fun")) orelse
    (Thy = "pair" andalso Tyop = "prod") orelse
    (Thy = "num" andalso Tyop = "num") orelse
    (Thy = "integer" andalso Tyop = "int")

  fun remove_nth index values =
    List.take (values, index) @ List.drop (values, index + 1)

  (* Case constants in HOL normally take the scrutinee first, but manually
     defined codata case constants may put it elsewhere.  A candidate
     position is accepted only if instantiating that domain to the registered
     codata type makes every remaining domain, in order, the branch type for
     the corresponding constructor. *)
  fun validate_codatatype_shape
        ({tyop, case_const, constructors} : codatatype_info) =
    let
      val function = "register_codatatype"
      val _ = if null constructors then
          raise err function "constructor list must not be empty"
        else ()
      val _ = if Term.is_const case_const andalso
                     List.all Term.is_const constructors then () else
        raise err function "case and constructor terms must be constants"
      fun distinct_constructor constructor =
        length (List.filter (Term.same_const constructor) constructors) = 1
      val _ = if List.all distinct_constructor constructors then () else
        raise err function "constructors must be distinct"
      val result_ty = #2 (boolSyntax.strip_fun
        (Term.type_of (hd constructors)))
      val {Thy, Tyop, Args} = Type.dest_thy_type result_ty
      val actual = {Thy = Thy, Tyop = Tyop}
      val _ = if same_type_operator tyop actual then () else
        raise err function "constructor result has the wrong type operator"
      val _ = if interpreted_type_operator tyop then
          raise err function
            "interpreted and function types cannot be codatatypes"
        else ()
      val _ = distinct_types Args
      fun normalize_constructor constructor =
        let
          val constructor_result = #2 (boolSyntax.strip_fun
            (Term.type_of constructor))
          val theta = Type.match_type constructor_result result_ty
          val normalized = Term.inst theta constructor
        in
          if #2 (boolSyntax.strip_fun (Term.type_of normalized)) = result_ty
          then normalized
          else raise err function "constructor result types do not agree"
        end
      val constructors = map normalize_constructor constructors
      (* Matching the scrutinee argument below pins down only the type
         variables occurring in it, leaving the rest of the case constant's
         variables - the case result above all - free to be captured by
         [result_ty]'s.  The stored [llist_CASE] has type
         [:'b llist -> 'a -> ('b -> 'b llist -> 'a) -> 'a], so matching its
         scrutinee against [:'a llist] collapses the case result into the
         element type, while a freshly parsed [llist_CASE] escapes unscathed;
         the two descriptions would then no longer be [aconv].  Rename the
         case constant apart from [result_ty] first, then rename whatever
         survives the match by order of first appearance, so that two
         descriptions of one codatatype differing only in the naming of their
         type variables still normalize to the same term.  [result_ty]'s own
         variables stay verbatim: the shape check compares the scrutinee
         domain against [result_ty] itself. *)
      val reserved = Type.type_vars result_ty
      val prefix =
        let
          val names = map Type.dest_vartype reserved
          fun widen prefix =
            if List.exists (String.isPrefix prefix) names then
              widen (prefix ^ "a")
            else prefix
        in
          widen "'a"
        end
      fun rename variables term =
        let
          fun entry (variable, (index, theta)) =
            (index + 1,
             {redex = variable,
              residue = Type.mk_vartype (prefix ^ Int.toString index)} ::
             theta)
        in
          Term.inst (#2 (List.foldl entry (0, []) variables)) term
        end
      fun appearances (ty, seen) =
        if Type.is_vartype ty then
          if Lib.mem ty seen then seen else seen @ [ty]
        else
          List.foldl appearances seen (#Args (Type.dest_thy_type ty))
      fun surviving term =
        List.filter (fn variable => not (Lib.mem variable reserved))
          (appearances (Term.type_of term, []))
      val case_const =
        rename (Type.type_vars (Term.type_of case_const)) case_const
      val (raw_domains, _) = boolSyntax.strip_fun (Term.type_of case_const)
      val _ = if length raw_domains = length constructors + 1 then () else
        raise err function
          "case constant must have one argument per branch and a scrutinee"
      fun candidate index =
        let
          val raw_domain = List.nth (raw_domains, index)
          val _ = if same_type_operator (type_operator_of raw_domain) tyop
                  then () else raise Match
          val theta = Type.match_type raw_domain result_ty
          val instance = Term.inst theta case_const
          val normalized = rename (surviving instance) instance
          val (domains, case_result) = boolSyntax.strip_fun
            (Term.type_of normalized)
          val branch_tys = remove_nth index domains
          fun valid_branch (constructor, branch_ty) =
            branch_ty = boolSyntax.list_mk_fun
              (#1 (boolSyntax.strip_fun (Term.type_of constructor)),
               case_result)
        in
          if List.nth (domains, index) = result_ty andalso
             ListPair.allEq valid_branch (constructors, branch_tys) then
            SOME normalized
          else
            NONE
        end handle HOL_ERR _ => NONE | Match => NONE
      val candidates = List.mapPartial (fn index =>
        Option.map (fn normalized => (index, normalized)) (candidate index))
        (List.tabulate (length raw_domains, fn index => index))
      val (scrutinee_index, case_const) =
        case candidates of
            [candidate] => candidate
          | [] => raise err function
              "case constant has no valid codatatype scrutinee argument"
          | _ => raise err function
              "case constant has more than one valid scrutinee argument"
    in
      ({tyop = tyop, case_const = case_const, constructors = constructors},
       scrutinee_index)
    end

  fun builtin_codatatype_info
        ({Thy, Tyop, case_name, constructor_names} :
         {Thy : string, Tyop : string, case_name : string,
          constructor_names : string list}) =
    if theory_is_available Thy then
      SOME (#1 (validate_codatatype_shape
        {tyop = {Thy = Thy, Tyop = Tyop},
         case_const = primitive_constant {Thy = Thy, Name = case_name},
         constructors = map (fn Name =>
           primitive_constant {Thy = Thy, Name = Name}) constructor_names}))
    else
      NONE

  (* Vis continuations in both interaction-tree theories have function type.
     As in Isabelle, SUB therefore compares their finite continuation graphs
     by equality rather than recursively by bisimulation. *)
  val builtin_codatatypes =
    [{Thy = "llist", Tyop = "llist", case_name = "llist_CASE",
      constructor_names = ["LNIL", "LCONS"]},
     {Thy = "ltree", Tyop = "ltree", case_name = "ltree_CASE",
      constructor_names = ["Branch"]},
     {Thy = "itree", Tyop = "itree", case_name = "itree_CASE",
      constructor_names = ["Ret", "Div", "Vis"]},
     {Thy = "itreeTau", Tyop = "itree", case_name = "itree_CASE",
      constructor_names = ["Ret", "Tau", "Vis"]},
     {Thy = "lbtree", Tyop = "lbtree", case_name = "lbtree_case",
      constructor_names = ["Lf", "Nd"]},
     {Thy = "path", Tyop = "path", case_name = "path_case",
      constructor_names = ["stopped_at", "pcons"]}]

  val builtin_codatatype_cache = ref ([] : codatatype_info list)

  fun builtin_codatatype_for (operator as {Thy, ...} : type_operator) =
    if not (theory_is_available Thy) then NONE
    else
      case List.find (fn {tyop, ...} => same_type_operator tyop operator)
             (!builtin_codatatype_cache) of
          SOME info => SOME info
        | NONE =>
            (case List.find (fn {Thy, Tyop, ...} =>
                     same_type_operator {Thy = Thy, Tyop = Tyop} operator)
                   builtin_codatatypes of
                 NONE => NONE
               | SOME descriptor =>
                   (case builtin_codatatype_info descriptor of
                        NONE => NONE
                      | SOME info =>
                          (builtin_codatatype_cache :=
                             info :: !builtin_codatatype_cache;
                           SOME info)))

  fun explicit_codatatype_for operator =
    List.find (fn {tyop, ...} => same_type_operator tyop operator)
      (!codatatype_registry)

  fun codatatype_for operator =
    case explicit_codatatype_for operator of
        SOME info => SOME info
      | NONE => builtin_codatatype_for operator

  fun current_codatatype_registry () =
    let
      val explicit = !codatatype_registry
      fun built_in {Thy, Tyop, ...} =
        builtin_codatatype_for {Thy = Thy, Tyop = Tyop}
      fun shadowed ({tyop, ...} : codatatype_info) =
        Option.isSome (explicit_codatatype_for tyop)
    in
      explicit @
      List.filter (not o shadowed)
        (List.mapPartial built_in builtin_codatatypes)
    end

  fun has_type_operator project registry ty =
    let val operator = type_operator_of ty
    in
      List.exists (fn entry =>
        same_type_operator (project entry) operator) (!registry)
    end handle HOL_ERR _ => false

  fun raw_free_datatype ty =
    case TypeBase.fetch ty of
        SOME info => not (null (TypeBasePure.constructors_of info))
      | NONE => false
    handle HOL_ERR _ => false

  fun register_codatatype (registration : codatatype_info) =
    let
      val (normalized as {tyop, constructors, ...}, _) =
        validate_codatatype_shape registration
      val result_ty = #2 (boolSyntax.strip_fun
        (Term.type_of (hd constructors)))
      (* Constructor/case types cannot distinguish inductive data from
         codata.  Until a registration carries a checked coinduction
         witness, accept only the audited built-in codata descriptions;
         treating an arbitrary TypeBase datatype as codata removes its
         acyclicity constraints. *)
      val _ =
        case builtin_codatatype_for tyop of
            SOME {case_const, constructors = builtin_constructors, ...} =>
              if Term.aconv case_const (#case_const normalized) andalso
                 ListPair.allEq (fn (left, right) => Term.aconv left right)
                   (builtin_constructors, constructors) then ()
              else raise err "register_codatatype"
                "registration disagrees with the built-in codatatype"
          | NONE => raise err "register_codatatype"
            "unverified codatatype registration requires a coinduction witness"
      val _ = if has_type_operator (type_operator_of o #qty)
                       quotient_registry result_ty orelse
                     has_type_operator (type_operator_of o #ty)
                       typedef_registry result_ty orelse
                     has_type_operator #tyop frac_registry result_ty then
          raise err "register_codatatype"
            "type operator already has an incompatible registration"
        else ()
      fun other ({tyop = old, ...} : codatatype_info) =
        not (same_type_operator old tyop)
    in
      codatatype_registry := normalized ::
        List.filter other (!codatatype_registry)
    end

  fun same_named key term =
    same_key (const_key term) key handle HOL_ERR _ => false

  fun beta_apply (function, argument) =
    let val application = Term.mk_comb (function, argument)
    in
      if Term.is_abs function then Term.beta_conv application
      else application
    end

  fun beta_normalize term =
    if Term.is_abs term then
      let val (variable, body) = Term.dest_abs term
      in Term.mk_abs (variable, beta_normalize body) end
    else if Term.is_comb term then
      let
        val (function, argument) = Term.dest_comb term
        val function = beta_normalize function
        val argument = beta_normalize argument
      in
        if Term.is_abs function then
          beta_normalize (Term.beta_conv (Term.mk_comb (function, argument)))
        else
          Term.mk_comb (function, argument)
      end
    else
      term

  (* Naming both accepted shapes keeps the diagnostic actionable: neither
     destructor alone can tell which one the caller was aiming at. *)
  val unsupported_shape =
    "equivalence theorem must be QUOTIENT R abs rep, or a total \
    \equivalence !x y. R x y <=> (R x = R y)"

  fun dest_total_equivalence theorem =
    let
      val _ = if null (Thm.hyp theorem) then () else
        raise err "register_quotient" "equivalence theorem has hypotheses"
      val (variables, body) = boolSyntax.strip_forall (Thm.concl theorem)
      val _ = if length variables = 2 then () else
        raise err "register_quotient" unsupported_shape
      val x = List.nth (variables, 0)
      val y = List.nth (variables, 1)
      val (left, right) = boolSyntax.dest_eq body
      val (relation, arguments) = HolKernel.strip_comb left
      val (right_x, right_y) = boolSyntax.dest_eq right
      val (relation_x, x_arguments) = HolKernel.strip_comb right_x
      val (relation_y, y_arguments) = HolKernel.strip_comb right_y
      val _ =
        if length arguments = 2 andalso length x_arguments = 1 andalso
           length y_arguments = 1 andalso
           Term.aconv relation relation_x andalso
           Term.aconv relation relation_y andalso
           Term.aconv (List.nth (arguments, 0)) x andalso
           Term.aconv (List.nth (arguments, 1)) y andalso
           Term.aconv (hd x_arguments) x andalso
           Term.aconv (hd y_arguments) y then ()
        else raise err "register_quotient" unsupported_shape
    in
      relation
    end

  fun dest_bare_quotient theorem =
    let
      val _ = if null (Thm.hyp theorem) then () else
        raise err "register_quotient" "quotient theorem has hypotheses"
      val (head, arguments) = HolKernel.strip_comb (Thm.concl theorem)
      val _ =
        if same_named {Thy = "quotient", Name = "QUOTIENT"} head andalso
           length arguments = 3 then ()
        else raise err "register_quotient" unsupported_shape
    in
      (List.nth (arguments, 0), List.nth (arguments, 1),
       List.nth (arguments, 2))
    end

  (* The head constant classifies the theorem: a QUOTIENT conclusion cannot
     be a universally quantified equation and vice versa, so dispatching on
     it keeps each shape's diagnostics its own.  Falling back to the total
     branch after a failed QUOTIENT parse would instead misreport a
     malformed QUOTIENT theorem as a malformed equivalence. *)
  fun is_bare_quotient theorem =
    let val (head, _) = HolKernel.strip_comb (Thm.concl theorem)
    in same_named {Thy = "quotient", Name = "QUOTIENT"} head end

  fun quotient_theorem_info theorem supplied_abs supplied_rep =
    if is_bare_quotient theorem then
      let
        val (raw_relation, theorem_abs, theorem_rep) =
          dest_bare_quotient theorem
        val theta = Type.match_type (Term.type_of theorem_abs)
          (Term.type_of supplied_abs)
        val relation = Term.inst theta raw_relation
        val theorem_abs = Term.inst theta theorem_abs
        val theorem_rep = Term.inst theta theorem_rep
        val _ =
          if Term.same_const supplied_abs theorem_abs andalso
             Term.type_of supplied_abs = Term.type_of theorem_abs andalso
             Term.same_const supplied_rep theorem_rep andalso
             Term.type_of supplied_rep = Term.type_of theorem_rep then ()
          else raise err "register_quotient"
            "QUOTIENT theorem does not mention the registered abs and rep"
      in
        (relation, true)
      end
    else
      (* A total equivalence theorem mentions only the representation
         relation; it cannot identify arbitrary supplied Abs/Rep constants,
         so there is nothing to cross-check here.  Its totality also makes
         the partial encoding's domain axiom redundant. *)
      (dest_total_equivalence theorem, false)

  fun validate_registered_type function ty =
    let
      val {Args, ...} = Type.dest_thy_type ty
      val _ = distinct_type_variables function Args
      val _ = if interpreted_type_operator (type_operator_of ty) then
          raise err function "interpreted types cannot be registered"
        else ()
    in
      ()
    end

  fun register_quotient_unlocked
        ({qty, rty, abs, rep, equiv_thm, partial = _} : quotient_info) =
    let
      val _ = validate_registered_type "register_quotient" qty
      val _ = if Term.is_const abs andalso Term.is_const rep then () else
        raise err "register_quotient" "abs and rep must be constants"
      val _ = if Term.type_of abs = Type.-->(rty, qty) andalso
                     Term.type_of rep = Type.-->(qty, rty) then () else
        raise err "register_quotient" "abs and rep have incompatible types"
      val _ =
        if List.all (fn variable => List.exists (fn parameter =>
             Type.compare (variable, parameter) = EQUAL)
             (Type.type_vars qty)) (Type.type_vars rty) then ()
        else raise err "register_quotient"
          "representation type has unbound type variables"
      val _ =
        if Option.isSome (codatatype_for (type_operator_of qty)) orelse
           has_type_operator (type_operator_of o #ty) typedef_registry qty
             orelse
           has_type_operator #tyop frac_registry qty orelse
           raw_free_datatype qty then
          raise err "register_quotient"
            "type operator already has an incompatible classification"
        else ()
      val (raw_relation, inferred_partial) =
        quotient_theorem_info equiv_thm abs rep
      val relation_ty = Type.-->(rty, Type.-->(rty, Type.bool))
      val relation = Term.inst
        (Type.match_type (Term.type_of raw_relation) relation_ty)
        raw_relation
      val _ = if Term.type_of relation = relation_ty then () else
        raise err "register_quotient"
          "equivalence relation has an incompatible type"
      val _ = if null (Term.free_vars_lr relation) then () else
        raise err "register_quotient"
          "equivalence relation has free term variables"
      (* The theorem shape, not the caller's legacy record bit, is
         authoritative.  A bare QUOTIENT theorem therefore defaults to the
         sound partial encoding; a total extensionality theorem disables the
         redundant domain axiom. *)
      val normalized : quotient_info =
        {qty = qty, rty = rty, abs = abs, rep = rep,
         equiv_thm = equiv_thm, partial = inferred_partial}
      val operator = type_operator_of qty
      fun other ({qty = old, ...} : quotient_info) =
        not (same_type_operator (type_operator_of old) operator)
    in
      quotient_registry := normalized ::
        List.filter other (!quotient_registry)
    end

  fun register_quotient registration =
    with_registration_lock (fn () =>
      register_quotient_unlocked registration)

  fun raw_typedef_data_generic ty =
    let
      val {Thy, Tyop, ...} = Type.dest_thy_type ty
      val theorem = DB.fetch Thy (Tyop ^ "_TY_DEF")
      val (witnesses, body) = boolSyntax.strip_exists (Thm.concl theorem)
      val _ = if length witnesses = 1 then () else
        raise err "raw_typedef_data" "malformed type definition theorem"
      val (head, arguments) = HolKernel.strip_comb body
      val _ =
        if same_named {Thy = "bool", Name = "TYPE_DEFINITION"} head
           andalso length arguments = 2 then ()
        else raise err "raw_typedef_data" "malformed type definition theorem"
      val witness = hd witnesses
      val (abs_pattern, rep_pattern) = Type.dom_rng (Term.type_of witness)
      val _ = Type.match_type abs_pattern ty
    in
      SOME {ty = abs_pattern, rty = rep_pattern, pred = hd arguments}
    end
    handle HOL_ERR _ => NONE

  fun raw_typedef_data ty =
    case raw_typedef_data_generic ty of
        SOME {ty = pattern, rty, pred} =>
          let val theta = Type.match_type pattern ty
          in
            SOME
              {rty = Type.type_subst theta rty,
               pred = Term.inst theta pred}
          end
      | NONE => NONE
    handle HOL_ERR _ => NONE

  fun parse_absrep theorem supplied_abs supplied_rep =
    let
      val _ = if null (Thm.hyp theorem) then () else
        raise err "register_typedef" "bijections theorem has hypotheses"
      val raw_conclusion = Thm.concl theorem
      val (raw_first, _) = boolSyntax.dest_conj raw_conclusion
      val (_, raw_first_body) = boolSyntax.strip_forall raw_first
      val (raw_first_left, _) = boolSyntax.dest_eq raw_first_body
      val (raw_abs, _) = HolKernel.strip_comb raw_first_left
      val theta = Type.match_type (Term.type_of raw_abs)
        (Term.type_of supplied_abs)
      val conclusion = Term.inst theta raw_conclusion
      val (first, second) = boolSyntax.dest_conj conclusion
      val (first_variables, first_body) = boolSyntax.strip_forall first
      val (second_variables, second_body) = boolSyntax.strip_forall second
      val _ = if length first_variables = 1 andalso
                     length second_variables = 1 then () else
        raise err "register_typedef" "bijections theorem has a bad shape"
      val abstract = hd first_variables
      val representation = hd second_variables
      val (first_left, first_right) = boolSyntax.dest_eq first_body
      val (first_abs, first_abs_arguments) =
        HolKernel.strip_comb first_left
      val _ = if length first_abs_arguments = 1 then () else
        raise err "register_typedef" "bijections theorem has a bad shape"
      val (first_rep, first_rep_arguments) =
        HolKernel.strip_comb (hd first_abs_arguments)
      val (predicate_body, second_right) = boolSyntax.dest_eq second_body
      val (second_rep, second_rep_arguments) =
        HolKernel.strip_comb (#1 (boolSyntax.dest_eq second_right))
      val _ = if length second_rep_arguments = 1 then () else
        raise err "register_typedef" "bijections theorem has a bad shape"
      val (second_abs, second_abs_arguments) =
        HolKernel.strip_comb (hd second_rep_arguments)
      val _ =
        if length first_rep_arguments = 1 andalso
           length second_abs_arguments = 1 andalso
           Term.same_const supplied_abs first_abs andalso
           Term.same_const supplied_abs second_abs andalso
           Term.same_const supplied_rep first_rep andalso
           Term.same_const supplied_rep second_rep andalso
           Term.aconv (hd first_rep_arguments) abstract andalso
           Term.aconv first_right abstract andalso
           Term.aconv (hd second_abs_arguments) representation andalso
           Term.aconv (#2 (boolSyntax.dest_eq second_right)) representation
        then ()
        else raise err "register_typedef" "bijections theorem has a bad shape"
      val pred = Term.mk_abs (representation, predicate_body)
      val probe = Term.variant (Term.all_vars pred)
        (Term.mk_var ("r", Term.type_of representation))
      val univ = Term.aconv
        (beta_normalize (beta_apply (pred, probe))) boolSyntax.T
      val inverse_axioms =
        let
          val (outer, body) = boolSyntax.strip_forall conclusion
          fun close conjunct =
            let val (inner, matrix) = boolSyntax.strip_forall conjunct
            in boolSyntax.list_mk_forall (outer @ inner, matrix) end
        in
          map close (boolSyntax.strip_conj body)
        end
    in
      (pred, inverse_axioms, univ)
    end

  fun register_typedef_unlocked
        {ty : hol_type, abs : term, rep : term, absrep_thm : thm} =
    let
      val _ = validate_registered_type "register_typedef" ty
      val _ = if Term.is_const abs andalso Term.is_const rep then () else
        raise err "register_typedef" "abs and rep must be constants"
      val (rty, _) = Type.dom_rng (Term.type_of abs)
      val _ = if Term.type_of abs = Type.-->(rty, ty) andalso
                     Term.type_of rep = Type.-->(ty, rty) then () else
        raise err "register_typedef" "abs and rep have incompatible types"
      val _ =
        if List.all (fn variable => List.exists (fn parameter =>
             Type.compare (variable, parameter) = EQUAL)
             (Type.type_vars ty)) (Type.type_vars rty) then ()
        else raise err "register_typedef"
          "representation type has unbound type variables"
      val _ =
        if Option.isSome (codatatype_for (type_operator_of ty)) orelse
           has_type_operator (type_operator_of o #qty) quotient_registry ty
             orelse
           has_type_operator #tyop frac_registry ty orelse
           raw_free_datatype ty then
          raise err "register_typedef"
            "type operator already has an incompatible classification"
        else ()
      val (pred, inverse_axioms, univ) =
        parse_absrep absrep_thm abs rep
      val {rty = raw_rty, pred = raw_pred} =
        case raw_typedef_data ty of
            SOME data => data
          | NONE => raise err "register_typedef"
              "the registered type has no <tyop>_TY_DEF theorem"
      val probe = Term.variant (Term.all_vars pred @ Term.all_vars raw_pred)
        (Term.mk_var ("r", rty))
      val _ =
        if raw_rty = rty andalso
           Term.aconv
             (beta_normalize (beta_apply (pred, probe)))
             (beta_normalize (beta_apply (raw_pred, probe))) then ()
        else raise err "register_typedef"
          "bijections predicate does not match the type definition"
      val normalized : typedef_info =
        {ty = ty, rty = rty, abs = abs, rep = rep, pred = pred,
         inverse_axioms = inverse_axioms, univ = univ}
      val operator = type_operator_of ty
      fun other ({ty = old, ...} : typedef_info) =
        not (same_type_operator (type_operator_of old) operator)
    in
      typedef_registry := normalized ::
        List.filter other (!typedef_registry)
    end

  fun register_typedef registration =
    with_registration_lock (fn () =>
      register_typedef_unlocked registration)

  fun validate_ersatz function ({original, replacement} : ersatz) =
    let
      val _ = Term.prim_mk_const
        {Thy = #Thy original, Name = #Name original}
      val _ = Term.prim_mk_const
        {Thy = #Thy replacement, Name = #Name replacement}
    in
      ()
    end handle HOL_ERR _ => raise err function
      "ersatz constants must name existing theory constants"

  fun prepare_frac_type_unlocked
        (registration as {tyop, ersatz} : frac_info) =
    let
      val function = "register_frac_type"
      val ty = Type.mk_thy_type
        {Thy = #Thy tyop, Tyop = #Tyop tyop, Args = []}
      (* Quotient and typedef entries can have been harvested merely by
         looking at a goal before Frac registration or after session-level
         customization.  They are the representation we are replacing, not
         an incompatible user choice. *)
      val _ = if interpreted_type_operator tyop orelse
                     raw_free_datatype ty orelse
                     Option.isSome (codatatype_for tyop) then
          raise err function
            "type operator already has an incompatible classification"
        else ()
      val _ = List.app (validate_ersatz function) ersatz
      fun unique [] = true
        | unique (entry :: rest) =
            not (List.exists (fn other =>
              same_key (#original entry) (#original other)) rest) andalso
            unique rest
      val _ = if unique ersatz then () else
        raise err function "ersatz originals must be distinct"

      (* Compute every replacement before touching session state.  The
         returned commit only assigns precomputed values and cannot fail. *)
      fun other_frac ({tyop = old, ...} : frac_info) =
        not (same_type_operator old tyop)
      fun other_quotient ({qty, ...} : quotient_info) =
        not (same_type_operator (type_operator_of qty) tyop)
      fun other_typedef ({ty = old, ...} : typedef_info) =
        not (same_type_operator (type_operator_of old) tyop)
      val new_fracs = registration ::
        List.filter other_frac (!frac_registry)
      val new_quotients = List.filter other_quotient (!quotient_registry)
      val new_typedefs = List.filter other_typedef (!typedef_registry)
      val key = operator_key tyop
      val new_quotient_misses =
        KNametab.delete_safe key (!quotient_harvest_misses)
      val new_typedef_misses =
        KNametab.delete_safe key (!typedef_harvest_misses)
      fun commit () =
        (quotient_registry := new_quotients;
         typedef_registry := new_typedefs;
         quotient_harvest_misses := new_quotient_misses;
         typedef_harvest_misses := new_typedef_misses;
         frac_registry := new_fracs)
    in
      commit
    end

  fun register_frac_type_unlocked registration =
    let val commit = prepare_frac_type_unlocked registration in
      Thread_Attributes.uninterruptible (fn _ => fn () => commit ()) ()
    end

  fun register_frac_type registration =
    with_registration_lock (fn () =>
      register_frac_type_unlocked registration)

  val rat_frac_registration : frac_info =
    {tyop = {Thy = "rat", Tyop = "rat"},
     ersatz =
       map (fn (original, replacement) =>
         {original = {Thy = "rat", Name = original},
          replacement = {Thy = "refute", Name = replacement}})
       [("rat_0", "zero_frac"),
        ("rat_1", "one_frac"),
        ("rat_ainv", "uminus_frac"),
        ("rat_minv", "inverse_frac"),
        ("rat_add", "plus_frac"),
        ("rat_sub", "subtract_frac"),
        ("rat_mul", "times_frac"),
        ("rat_div", "divide_frac"),
        ("rat_les", "less_frac"),
        ("rat_leq", "less_eq_frac"),
        ("rat_of_num", "of_num_frac"),
        ("rat_cons", "frac")]}

  fun harvest_index_entry operator =
    let
      val _ =
        if !harvest_session_index_stale then
          (rebuild_harvest_session_index ();
           harvest_session_index_stale := false)
        else ()
      val {operator, theorem_theories, constant_theories} =
        Option.getOpt (KNametab.lookup (!harvest_session_index)
          (operator_key operator),
          {operator = operator, theorem_theories = [],
           constant_theories = []})
    in
      {operator = operator,
       theorem_theories = sort_strings theorem_theories,
       constant_theories = sort_strings constant_theories}
    end

  fun seed_harvest_theory theory =
    if Option.isSome (Symtab.lookup (!harvest_indexed_theories) theory)
    then ()
    else index_harvest_theory theory

  fun seed_pending_harvest_theories () =
    let
      val pending = rev (!harvest_pending_theories)
      val _ = harvest_pending_theories := []
    in
      List.app seed_harvest_theory pending
    end

  fun indexed_harvest_theories ty =
    let
      val operator = type_operator_of ty
      val home = #Thy operator
      val _ = seed_pending_harvest_theories ()
      val _ = seed_harvest_theory home
      val {constant_theories = direct_constants, ...} =
        harvest_index_entry operator
      (* Seed only the type's home and directly observed constant owners.
         Do not close this set under either theory or constant ancestry. *)
      val _ = List.app seed_harvest_theory direct_constants
      val {theorem_theories, constant_theories, ...} =
        harvest_index_entry operator
    in
      rev (List.foldl (fn (theory, result) =>
        add_string theory result) []
        (home :: constant_theories @ theorem_theories))
    end

  fun harvest_theory_generation theory =
    Option.getOpt (Symtab.lookup (!harvest_theory_generations) theory, 0)

  fun harvest_fingerprint operator theories : harvest_fingerprint =
    (Option.getOpt (KNametab.lookup (!harvest_operator_generations)
       (operator_key operator), 0),
     map (fn theory => (theory, harvest_theory_generation theory)) theories)

  fun cached_harvest_miss operator fingerprint misses =
    KNametab.lookup misses (operator_key operator) = SOME fingerprint

  fun remember_harvest_miss misses operator fingerprint =
    misses := KNametab.update (operator_key operator, fingerprint) (!misses)

  fun quotient_candidate operator theorem =
    let
      val (_, abs, rep) = dest_bare_quotient theorem
      val (rty, qty) = Type.dom_rng (Term.type_of abs)
      val _ = if same_type_operator (type_operator_of qty) operator then ()
        else raise Match
      val _ = register_quotient_unlocked
        {qty = qty, rty = rty, abs = abs, rep = rep,
         equiv_thm = theorem, partial = true}
    in
      true
    end
    handle HOL_ERR _ => false | Match => false

  fun typedef_candidate operator theorem =
    let
      val (first, _) = boolSyntax.dest_conj (Thm.concl theorem)
      val (_, equation) = boolSyntax.strip_forall first
      val (left, _) = boolSyntax.dest_eq equation
      val (abs, abs_arguments) = HolKernel.strip_comb left
      val _ = if length abs_arguments = 1 then () else raise Match
      val (rep, rep_arguments) = HolKernel.strip_comb (hd abs_arguments)
      val _ = if length rep_arguments = 1 then () else raise Match
      val (_, ty) = Type.dom_rng (Term.type_of abs)
      val _ = if same_type_operator (type_operator_of ty) operator then ()
        else raise Match
      val _ = register_typedef_unlocked
        {ty = ty, abs = abs, rep = rep, absrep_thm = theorem}
    in
      true
    end
    handle HOL_ERR _ => false | Match => false

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

  fun is_lfp_iterator_type ty =
    Type.is_vartype ty andalso
    String.isPrefix
      ("'" ^ Refute_ModelFinder_Names.lfp_iterator_prefix)
      (Type.dest_vartype ty)

  fun is_gfp_iterator_type ty =
    Type.is_vartype ty andalso
    String.isPrefix
      ("'" ^ Refute_ModelFinder_Names.gfp_iterator_prefix)
      (Type.dest_vartype ty)

  fun is_fp_iterator_type ty =
    is_lfp_iterator_type ty orelse is_gfp_iterator_type ty

  fun is_bisim_iterator_type ty = ty = bisim_iterator_type

  fun is_iterator_type ty =
    is_bisim_iterator_type ty orelse is_fp_iterator_type ty

  fun iterator_info_for_type
        ({iterator_table, ...} : mf_context) ty =
    Option.map #2 (List.find (fn (other, _) => other = ty) (!iterator_table))

  fun refresh_iterator_arg_types
        ({iterator_table, ...} : mf_context) terms =
    let
      val generated = List.concat (map
        (HolKernel.find_terms (fn term =>
          case Lib.total Term.dest_var term of
              SOME (name, _) => Refute_ModelFinder_Names.is_unrolled_name name
            | NONE => false)) terms)

      fun transformed_arg_tys iterator_ty pred fallback =
        let
          fun matches term =
            let val arguments = #1 (boolSyntax.strip_fun
                  (Term.type_of term))
            in
              not (null arguments) andalso hd arguments = iterator_ty andalso
              same_key (original_const_key term)
                (original_const_key pred)
            end
            handle HOL_ERR _ => false
        in
          case List.find matches generated of
              SOME term => tl (#1 (boolSyntax.strip_fun (Term.type_of term)))
            | NONE => fallback
        end

      fun refresh (iterator_ty,
            {pred, preds, arg_tys, arg_tyss, gfp, token} : iterator_info) =
        let
          val arg_tyss = ListPair.map
            (fn (member, tys) =>
              transformed_arg_tys iterator_ty member tys)
            (preds, arg_tyss)
        in
          (iterator_ty,
           {pred = pred, preds = preds,
            arg_tys = if null arg_tyss then arg_tys else hd arg_tyss,
            arg_tyss = arg_tyss,
            gfp = gfp, token = token} : iterator_info)
        end
    in
      iterator_table := map refresh (!iterator_table)
    end

  fun iterator_type_for_const
        (context as {iterator_table, ...} : mf_context) gfp pred =
    let
      val (stem, preds) =
        case instantiated_fixpoint_group context pred of
            SOME {stem, members, ...} => (stem, members)
          | NONE =>
              let val key = original_const_key pred
              in (#Name key, [pred]) end
      fun same_group
            (_, {preds = others, gfp = other_gfp, ...} : iterator_info) =
        gfp = other_gfp andalso length preds = length others andalso
        ListPair.allEq (fn (left, right) => Term.aconv left right)
          (preds, others)
    in
      case List.find same_group (!iterator_table) of
          SOME (ty, _) => ty
        | NONE =>
            let
              val key = original_const_key (hd preds)
              val original = #Thy key ^ Refute_ModelFinder_Names.name_sep ^
                stem
              val prefix = if gfp then
                  Refute_ModelFinder_Names.gfp_iterator_prefix
                else Refute_ModelFinder_Names.lfp_iterator_prefix
              val base = "'" ^ prefix ^ original
              fun argument_tys member =
                let val (domains, result_ty) = boolSyntax.strip_fun
                      (Term.type_of member)
                in
                  if result_ty = Type.bool then domains
                  else raise err "iterator_type_for_const"
                    "fixpoint constant is not a predicate"
                end
              val arg_tyss = map argument_tys preds
              val occupied = map (Type.dest_vartype o #1)
                  (!iterator_table) @
                map Type.dest_vartype
                  (List.concat (map Type.type_vars
                    (List.concat arg_tyss)))
              fun fresh serial =
                let
                  val name = if serial = 0 then base
                    else base ^ Refute_ModelFinder_Names.name_sep ^
                      Int.toString serial
                in
                  if List.exists (fn old => old = name) occupied then
                    fresh (serial + 1)
                  else name
                end
              val name = fresh 0
              val ty = Lib.with_flag (Feedback.emit_WARNING, false)
                Type.mk_vartype name
              val token = String.extract (name, 1, NONE)
              val info : iterator_info =
                {pred = hd preds, preds = preds,
                 arg_tys = hd arg_tyss, arg_tyss = arg_tyss,
                 gfp = gfp, token = token}
              val _ = iterator_table := (ty, info) :: !iterator_table
            in ty end
    end

  fun const_for_iterator_type context ty =
    case iterator_info_for_type context ty of
        SOME {pred, ...} => pred
      | NONE => raise err "const_for_iterator_type"
          "unregistered iterator type"

  fun iterator_zero_for_type context ty =
    case iterator_info_for_type context ty of
        SOME {token, ...} =>
          Refute_ModelFinder_Names.mk_iterator_zero token ty
      | NONE => raise err "iterator_zero_for_type"
          "unregistered iterator type"

  fun iterator_suc_for_type context ty =
    case iterator_info_for_type context ty of
        SOME {token, ...} =>
          Refute_ModelFinder_Names.mk_iterator_suc token ty
      | NONE => raise err "iterator_suc_for_type"
          "unregistered iterator type"

  datatype iterator_marker = IteratorZero | IteratorSuc

  fun iterator_marker_of_term context term =
    if Term.aconv term bisim_zero_const then SOME IteratorZero
    else if Term.aconv term bisim_suc_const then SOME IteratorSuc
    else case Lib.total Term.dest_var term of
        SOME (name, ty) =>
          if Refute_ModelFinder_Names.is_iterator_zero_name name andalso
             Option.isSome (iterator_info_for_type context ty) andalso
             Term.aconv term (iterator_zero_for_type context ty) then
            SOME IteratorZero
          else if Refute_ModelFinder_Names.is_iterator_suc_name name then
            (case Lib.total Type.dom_rng ty of
                 SOME (domain, range) =>
                   if domain = range andalso
                      Option.isSome (iterator_info_for_type context domain)
                      andalso
                      Term.aconv term (iterator_suc_for_type context domain)
                   then SOME IteratorSuc else NONE
               | NONE => NONE)
          else NONE
      | NONE => NONE

  fun fixpoint_case_equation_from_prop pred case_prop =
    let
      val (variables, body) = boolSyntax.strip_forall case_prop
      val (premises, conclusion) = boolSyntax.strip_imp body
      val (left, right) = boolSyntax.dest_eq conclusion
      val (head, arguments) = HolKernel.strip_comb left
      val _ = if same_fixpoint_const head pred then () else
        raise err "fixpoint_case_equation_from_prop"
          "fixpoint equation has the wrong head"
    in
      (case_prop, variables, premises, arguments, right)
    end

  fun fixpoint_case_equation context pred =
    let
      val case_prop =
        case case_props_for_const context pred of
            [prop] => prop
          | _ => raise err "fixpoint_case_equation"
              "expected one fixpoint equation"
      val (variables, body) = boolSyntax.strip_forall case_prop
      val (premises, conclusion) = boolSyntax.strip_imp body
      val (left, right) = boolSyntax.dest_eq conclusion
      val (head, arguments) = HolKernel.strip_comb left
      val _ = if same_fixpoint_const head pred then () else
        raise err "fixpoint_case_equation"
          "fixpoint equation has the wrong head"
    in
      (case_prop, variables, premises, arguments, right)
    end

  fun disjuncts_of term =
    if boolSyntax.is_disj term then
      let val (left, right) = boolSyntax.dest_disj term
      in disjuncts_of left @ disjuncts_of right end
    else [term]

  fun mk_disjunction [] = boolSyntax.F
    | mk_disjunction terms = boolSyntax.list_mk_disj terms

  (* Count recursive calls as applications, rather than also counting every
     partial application on their spines.  A partial or bare occurrence is
     deliberately counted twice, and hence rejected by the linearity gate. *)
  fun recursive_call_count pred arity term =
    if Term.is_abs term then
      recursive_call_count pred arity (#2 (Term.dest_abs term))
    else if Term.is_comb term then
      let val (head, arguments) = HolKernel.strip_comb term
      in
        if same_fixpoint_const head pred then
          (if length arguments = arity then 1 else 2) +
          List.foldl (fn (argument, total) =>
            recursive_call_count pred arity argument + total) 0 arguments
        else
          List.foldl (fn (part, total) =>
            recursive_call_count pred arity part + total) 0
            (head :: arguments)
      end
    else if (Term.is_const term orelse Term.is_var term) andalso
            same_fixpoint_const term pred then 2
    else 0

  fun strip_existentials term = #2 (boolSyntax.strip_exists term)

  fun is_direct_recursive_conjunct pred arity conjunct =
    let val (head, arguments) = HolKernel.strip_comb conjunct
    in same_fixpoint_const head pred andalso length arguments = arity end

  fun is_linear_inductive_pred context pred =
    let
      val (_, _, premises, arguments, right) =
        fixpoint_case_equation context pred
      val arity = length arguments
      fun linear disjunct =
        let
          val body = strip_existentials disjunct
          val count = recursive_call_count pred arity body
        in
          count = 0 orelse
          (count = 1 andalso List.exists
            (is_direct_recursive_conjunct pred arity)
            (boolSyntax.strip_conj body))
        end
    in
      null premises andalso arity > 0 andalso
      List.all linear (disjuncts_of right)
    end
    handle HOL_ERR _ => false

  fun is_good_starred_linear_pred_type ty =
    let val (argument_tys, result_ty) = boolSyntax.strip_fun ty
    in
      result_ty = Type.bool andalso not (null argument_tys) andalso
      List.all (fn argument_ty =>
        not (is_fun_type argument_ty) andalso
        not (is_pair_type argument_ty)) argument_tys
    end

  fun recursive_conjunct pred arity disjunct =
    let
      val (_, body) = boolSyntax.strip_exists disjunct
    in
      case List.find (is_direct_recursive_conjunct pred arity)
             (boolSyntax.strip_conj body) of
          SOME occurrence => occurrence
        | NONE => raise err "recursive_conjunct"
            "linear disjunct has no direct recursive conjunct"
    end

  fun starred_linear_pred_const context pred =
    let
      val (_, variables, premises, arguments, right) =
        fixpoint_case_equation context pred
      val _ = if null premises then () else
        raise err "starred_linear_pred_const"
          "conditional fixpoint equation"
      val argument_tys = map Term.type_of arguments
      val tuple_ty = tuple_type argument_tys
      val relation_ty = Type.-->(tuple_ty,
        Type.-->(tuple_ty, Type.bool))
      val key = original_const_key pred
      val original = #Thy key ^ Refute_ModelFinder_Names.name_sep ^ #Name key
      val base = Refute_ModelFinder_Names.mk_base original
        (Type.-->(tuple_ty, Type.bool))
      val step = Refute_ModelFinder_Names.mk_step original relation_ty
      val arity = length arguments
      val disjuncts = disjuncts_of right
      val (base_disjuncts, step_disjuncts) = List.partition
        (fn disjunct => recursive_call_count pred arity disjunct = 0)
        disjuncts
      val base_body = mk_disjunction base_disjuncts
      val source = Term.variant
        (variables @ Term.all_vars right)
        (Term.mk_var ("y", tuple_ty))
      fun repair disjunct =
        let
          val occurrence = recursive_conjunct pred arity disjunct
          val (_, recursive_arguments) = HolKernel.strip_comb occurrence
          val replacement = boolSyntax.mk_eq
            (source, tuple_term recursive_arguments)
        in
          Term.subst [{redex = occurrence, residue = replacement}] disjunct
        end
      val step_body = mk_disjunction (map repair step_disjuncts)
      val destination = tuple_term arguments
      val base_equation = boolSyntax.list_mk_forall
        (variables, boolSyntax.mk_eq
          (Term.mk_comb (base, destination), base_body))
      val step_equation = boolSyntax.list_mk_forall
        (source :: variables, boolSyntax.mk_eq
          (Term.list_mk_comb (step, [source, destination]), step_body))
      val _ = if is_raw_equational_fun context base then ()
        else add_simps (#simp_table context) base [base_equation]
      val _ = if is_raw_equational_fun context step then ()
        else add_simps (#simp_table context) step [step_equation]
      val rtc = Term.mk_thy_const
        {Thy = "relation", Name = "RTC",
         Ty = Type.-->(relation_ty, relation_ty)}
      val reached = Term.list_mk_comb
        (rtc, [step, source, destination])
      (* HOL4 relations are curried predicates and have no separate
         relation-image operator.  This existential is the predicatified
         form of RTC step `` {y | base y}. *)
      val body = boolSyntax.mk_exists
        (source, boolSyntax.mk_conj (Term.mk_comb (base, source), reached))
    in
      Term.list_mk_abs (arguments, body)
    end

  fun should_star_linear_pred
        (context as {star_linear_preds, ...} : mf_context) gfp pred =
    not gfp andalso star_linear_preds andalso
    not (is_mutually_inductive_pred context pred) andalso
    is_linear_inductive_pred context pred andalso
    is_good_starred_linear_pred_type (Term.type_of pred)

  fun unrolled_inductive_pred_const context gfp pred =
    if should_star_linear_pred context gfp pred then
      starred_linear_pred_const context pred
    else
      let
        val {members, cases, ...} =
          case instantiated_fixpoint_group context pred of
              SOME group => group
            | NONE => raise err "unrolled_inductive_pred_const"
                "fixpoint predicate has no theorem group"
        val iterator_ty = iterator_type_for_const context gfp pred
        fun mk_unrolled member =
          let
            val key = original_const_key member
            val original = #Thy key ^ Refute_ModelFinder_Names.name_sep ^
              #Name key
          in
            Refute_ModelFinder_Names.mk_unrolled original
              iterator_ty (Term.type_of member)
          end
        val unrolleds = map mk_unrolled members
        fun queried (member, unrolled) =
          if same_fixpoint_const pred member then SOME unrolled else NONE
        val unrolled =
          case List.mapPartial queried (ListPair.zip (members, unrolleds)) of
              [result] => result
            | _ => raise err "unrolled_inductive_pred_const"
                "queried predicate is not a unique group member"
        val zero = iterator_zero_for_type context iterator_ty

        fun equation_for (member, (member_unrolled, case_prop)) =
          let
            val (_, variables, premises, arguments, right) =
              fixpoint_case_equation_from_prop member case_prop
            val iterator = Term.variant
              (variables @ Term.free_vars_lr case_prop)
              (Term.mk_var (Refute_ModelFinder_Names.iter_var_prefix,
                iterator_ty))
            val next = Term.mk_comb
              (iterator_suc_for_type context iterator_ty, iterator)
            val substitution = ListPair.map
              (fn (original, replacement) =>
                {redex = original,
                 residue = Term.mk_comb (replacement, next)})
              (members, unrolleds)
            val right = Term.subst substitution right
            val left = Term.list_mk_comb
              (member_unrolled, iterator :: arguments)
          in
            boolSyntax.list_mk_forall
              (iterator :: variables,
               boolSyntax.list_mk_imp
                 (premises, boolSyntax.mk_eq (left, right)))
          end
        val equations = ListPair.map equation_for
          (members, ListPair.zip (unrolleds, cases))
        fun install (member_unrolled, equation) =
          if is_raw_equational_fun context member_unrolled then ()
          else add_simps (#simp_table context) member_unrolled [equation]
        val _ = ListPair.app install (unrolleds, equations)
      in
        Term.mk_comb (unrolled, zero)
      end

  fun fixpoint_bound_const context upper pred =
    let
      val key = original_const_key pred
      val original = #Thy key ^ Refute_ModelFinder_Names.name_sep ^ #Name key
    in
      if upper then
        Refute_ModelFinder_Names.mk_ubfp original (Term.type_of pred)
      else
        Refute_ModelFinder_Names.mk_lbfp original (Term.type_of pred)
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

  fun uniterize_unarize_unbox_etc_type ty =
    if is_iterator_type ty then num_type
    else if Type.is_vartype ty then ty
    else
      let val {Thy, Tyop, Args} = Type.dest_thy_type ty
      in
        if Thy = "refute" andalso Tyop = "funbox" then
          Type.-->(uniterize_unarize_unbox_etc_type (List.nth (Args, 0)),
            uniterize_unarize_unbox_etc_type (List.nth (Args, 1)))
        else if Thy = "refute" andalso Tyop = "pairbox" then
          pairSyntax.mk_prod
            (uniterize_unarize_unbox_etc_type (List.nth (Args, 0)),
             uniterize_unarize_unbox_etc_type (List.nth (Args, 1)))
        else
          unarize_unbox_etc_type
            (Type.mk_thy_type {Thy = Thy, Tyop = Tyop,
              Args = map uniterize_unarize_unbox_etc_type Args})
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
    interpreted_type_operator (type_operator_of ty) handle HOL_ERR _ => false

  val is_raw_free_datatype = raw_free_datatype

  fun is_codatatype ty =
    Option.isSome (codatatype_for (type_operator_of ty))
    handle HOL_ERR _ => false

  fun quotient_for_type ty =
    let
      val operator = type_operator_of ty
      val info = List.find (fn {qty, ...} =>
        same_type_operator (type_operator_of qty) operator)
        (!quotient_registry)
    in
      case info of
          NONE => NONE
        | SOME {qty, rty, abs, rep, equiv_thm, partial} =>
            let val theta = Type.match_type qty ty
            in
              SOME
                {qty = ty, rty = Type.type_subst theta rty,
                 abs = Term.inst theta abs, rep = Term.inst theta rep,
                 equiv_thm = equiv_thm, partial = partial}
            end
    end handle HOL_ERR _ => NONE

  fun is_quot_type ty = Option.isSome (quotient_for_type ty)

  fun synthetic_frac_typedef ty =
    if not (registered_frac_type ty) then NONE
    else
      let
        val abs = retype_frac_constant
          (Term.prim_mk_const {Thy = "frac", Name = "abs_frac"})
          (Type.-->(frac_pair_type, ty))
        val rep = retype_frac_constant
          (Term.prim_mk_const {Thy = "frac", Name = "rep_frac"})
          (Type.-->(ty, frac_pair_type))
        val pred = Term.prim_mk_const {Thy = "refute", Name = "Frac"}
      in
        (* As in Nitpick's synthetic frac typedef, constructor/selector
           axioms provide the bijection.  Inverse theorems belong only to
           genuine HOL typedefs and would duplicate that encoding here. *)
        SOME {ty = ty, rty = frac_pair_type, abs = abs, rep = rep,
          pred = pred, inverse_axioms = [], univ = false}
      end

  fun typedef_for_type ty =
    let
      val operator = type_operator_of ty
      val info = List.find (fn ({ty = registered, ...} : typedef_info) =>
        same_type_operator (type_operator_of registered) operator)
        (!typedef_registry)
    in
      case info of
          NONE => synthetic_frac_typedef ty
        | SOME {ty = registered, rty, abs, rep, pred, inverse_axioms,
                univ} =>
            let val theta = Type.match_type registered ty
            in
              SOME
                {ty = ty, rty = Type.type_subst theta rty,
                 abs = Term.inst theta abs, rep = Term.inst theta rep,
                 pred = Term.inst theta pred,
                 inverse_axioms = map (Term.inst theta) inverse_axioms,
                 univ = univ}
            end
    end handle HOL_ERR _ => NONE

  fun is_typedef ty = Option.isSome (typedef_for_type ty)

  (* A restricted typedef is not cardinality-monotonic: increasing its
     representation scope need not increase the abstract carrier. *)
  fun is_univ_typedef ty =
    case typedef_for_type ty of
        SOME {univ, ...} => univ
      | NONE => false

  fun quotient_relation_for_type ty =
    case quotient_for_type ty of
        SOME {qty, rty, abs, rep, equiv_thm, ...} =>
          let
            val (relation, _) = quotient_theorem_info equiv_thm abs rep
            val relation_ty = Type.-->(rty, Type.-->(rty, Type.bool))
          in
            if Term.type_of relation = relation_ty then relation
            else
              let val theta = Type.match_type (Term.type_of relation)
                    relation_ty
              in Term.inst theta relation end
          end
      | NONE => raise err "quotient_relation_for_type"
          "unregistered quotient type"

  fun is_frac_type ty = has_type_operator #tyop frac_registry ty

  fun is_data_type ty =
    not (is_interpreted_type ty) andalso
    (is_codatatype ty orelse is_raw_free_datatype ty orelse
     is_quot_type ty orelse is_typedef ty orelse is_frac_type ty)

  fun harvest_quotient_unlocked ty =
    let
      val operator = type_operator_of ty
      val theories = indexed_harvest_theories ty
      val fingerprint = harvest_fingerprint operator theories
      fun scan [] = false
        | scan (theory :: rest) =
            List.exists (quotient_candidate operator o #2)
              (quotient_harvest_scan_count :=
                 !quotient_harvest_scan_count + 1;
               scan_harvest_theorems quotient_harvest_scan_theories theory)
            orelse scan rest
      fun fast () =
        case Lib.total (DB.fetch (#Thy operator))
               (#Tyop operator ^ "_QUOTIENT") of
            SOME theorem => quotient_candidate operator theorem
          | NONE => false
      val incompatible =
        is_interpreted_type ty orelse is_codatatype ty orelse
        is_typedef ty orelse is_frac_type ty orelse
        is_raw_free_datatype ty
    in
      if is_quot_type ty then true
      else if incompatible orelse
              cached_harvest_miss operator fingerprint
                (!quotient_harvest_misses) then false
      else if fast () orelse scan theories then true
      else
        (remember_harvest_miss quotient_harvest_misses operator fingerprint;
         false)
    end
    handle HOL_ERR _ => false

  fun harvest_quotient ty =
    with_registration_lock (fn () => harvest_quotient_unlocked ty)

  fun harvest_typedef_unlocked ty =
    let
      val operator = type_operator_of ty
      val theories = indexed_harvest_theories ty
      val fingerprint = harvest_fingerprint operator theories
      fun scan [] = false
        | scan (theory :: rest) =
            List.exists (typedef_candidate operator o #2)
              (typedef_harvest_scan_count :=
                 !typedef_harvest_scan_count + 1;
               scan_harvest_theorems typedef_harvest_scan_theories theory)
            orelse scan rest
      val incompatible =
        is_interpreted_type ty orelse is_codatatype ty orelse
        is_quot_type ty orelse is_frac_type ty orelse
        is_raw_free_datatype ty
      val has_definition = Option.isSome (raw_typedef_data_generic ty)
    in
      if is_typedef ty then true
      else if incompatible orelse not has_definition orelse
              cached_harvest_miss operator fingerprint
                (!typedef_harvest_misses) then false
      else if scan theories then true
      else
        (remember_harvest_miss typedef_harvest_misses operator fingerprint;
         false)
    end
    handle HOL_ERR _ => false

  fun harvest_typedef ty =
    with_registration_lock (fn () => harvest_typedef_unlocked ty)

  fun quot_constructor rty qty =
    Term.mk_thy_const
      {Thy = "refute", Name = "Quot", Ty = Type.-->(rty, qty)}

  fun registered_constructors ty =
    let val operator = type_operator_of ty
    in
      case codatatype_for operator of
          SOME {constructors, ...} =>
            map (fn constructor =>
              Term.inst
                (Type.match_type
                  (#2 (boolSyntax.strip_fun (Term.type_of constructor))) ty)
                constructor) constructors
        | NONE =>
            (case quotient_for_type ty of
                 SOME {rty, ...} => [quot_constructor rty ty]
               | NONE =>
                   (case typedef_for_type ty of
                        SOME {abs, ...} => [abs]
                      | NONE => []))
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
    let
      val result_ty = #2 (boolSyntax.strip_fun (Term.type_of term))
    in
      List.exists (fn constructor =>
        Term.same_const constructor term andalso
        Term.type_of constructor = Term.type_of term)
        (registered_constructors result_ty)
    end handle HOL_ERR _ => false

  fun raw_constructor_name constructor =
    case Lib.total Term.dest_thy_const constructor of
        SOME {Thy, Name, ...} => Thy ^ "$" ^ Name
      | NONE =>
          let val (name, _) = Term.dest_var constructor
          in Refute_ModelFinder_Names.original_name name end

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
                if is_codatatype result_ty then []
                else
                  (case TypeBase.fetch result_ty of
                       SOME info => map (TypeBasePure.cinst result_ty)
                         (TypeBasePure.constructors_of info)
                     | NONE => [])
              val registered = registered_constructors result_ty
            in
              List.exists (fn constructor =>
                raw_constructor_name constructor = original)
                (raw @ registered)
            end
        | NONE => false
    handle HOL_ERR _ => false

  fun is_nonfree_constr term =
    if Term.is_const term then
      let
        val result_ty = #2 (boolSyntax.strip_fun (Term.type_of term))
      in
        registered_constructor term orelse
        (not (is_codatatype result_ty) andalso
         TypeBase.is_constructor term)
      end handle HOL_ERR _ => false
    else
      reserved_constructor term

  (* A TypeBase pseudo-datatype may expose constructors other than the
     registered coconstructors.  They must not survive as unconstrained
     constants merely because the codatatype classification overrides the
     raw free-datatype classification. *)
  fun is_stale_constr term =
    if Term.is_const term then
      let
        val result_ty = #2 (boolSyntax.strip_fun (Term.type_of term))
      in
        is_codatatype result_ty andalso TypeBase.is_constructor term andalso
        not (registered_constructor term)
      end handle HOL_ERR _ => false
    else
      false

  fun is_free_constr term =
    if not (is_nonfree_constr term) then false
    else
      let val result_ty = #2 (boolSyntax.strip_fun (Term.type_of term))
      in
        if is_quot_type result_ty then false
        else
          case typedef_for_type result_ty of
              SOME {univ, ...} => univ
            | NONE => true
      end handle HOL_ERR _ => false

  fun is_constr term =
    is_nonfree_constr term andalso
    not (is_interpreted_type (#2 (boolSyntax.strip_fun
      (Term.type_of term))))

  fun same_registered_constant expected actual =
    Term.type_of expected = Term.type_of actual andalso
    (Term.aconv expected actual orelse Term.same_const expected actual)
    handle HOL_ERR _ => false

  fun quotient_for_abs constant =
    let val (_, qty) = Type.dom_rng (Term.type_of constant)
    in
      case quotient_for_type qty of
          SOME (info as {abs, ...}) =>
            if same_registered_constant abs constant then SOME info else NONE
        | NONE => NONE
    end handle HOL_ERR _ => NONE

  fun quotient_for_rep constant =
    let val (qty, _) = Type.dom_rng (Term.type_of constant)
    in
      case quotient_for_type qty of
          SOME (info as {rep, ...}) =>
            if same_registered_constant rep constant then SOME info else NONE
        | NONE => NONE
    end handle HOL_ERR _ => NONE

  fun typedef_for_abs constant =
    let val (_, ty) = Type.dom_rng (Term.type_of constant)
    in
      case typedef_for_type ty of
          SOME (info as {abs, ...}) =>
            if same_registered_constant abs constant then SOME info else NONE
        | NONE => NONE
    end handle HOL_ERR _ => NONE

  fun typedef_for_rep constant =
    let val (ty, _) = Type.dom_rng (Term.type_of constant)
    in
      case typedef_for_type ty of
          SOME (info as {rep, ...}) =>
            if same_registered_constant rep constant then SOME info else NONE
        | NONE => NONE
    end handle HOL_ERR _ => NONE

  fun quotient_class_abs_for constant =
    let
      val (_, qty) = Type.dom_rng (Term.type_of constant)
      val info = quotient_for_type qty
      val key = const_key constant
    in
      case info of
          SOME (found as {abs, rty, ...}) =>
            let val abs_key = const_key abs
            in
              if #Thy key = #Thy abs_key andalso
                 #Name key = #Name abs_key ^ "_CLASS" andalso
                 Term.type_of constant =
                   Type.-->(Type.-->(rty, Type.bool), qty)
              then SOME found else NONE
            end
        | NONE => NONE
    end handle HOL_ERR _ => NONE

  fun quotient_class_rep_for constant =
    let
      val (qty, _) = Type.dom_rng (Term.type_of constant)
      val info = quotient_for_type qty
      val key = const_key constant
    in
      case info of
          SOME (found as {rep, rty, ...}) =>
            let val rep_key = const_key rep
            in
              if #Thy key = #Thy rep_key andalso
                 #Name key = #Name rep_key ^ "_CLASS" andalso
                 Term.type_of constant =
                   Type.-->(qty, Type.-->(rty, Type.bool))
              then SOME found else NONE
            end
        | NONE => NONE
    end handle HOL_ERR _ => NONE

  fun is_quot_abs_fun term = Option.isSome (quotient_for_abs term)
  fun is_quot_rep_fun term = Option.isSome (quotient_for_rep term)
  fun is_abs_fun term = Option.isSome (typedef_for_abs term)
  fun is_rep_fun term = Option.isSome (typedef_for_rep term)

  fun mate_of_rep_fun term =
    case typedef_for_rep term of
        SOME {abs, ...} => abs
      | NONE => raise err "mate_of_rep_fun" "unregistered Rep function"

  fun unregistered_typedef_type constant =
    let
      val (domain, range) = Type.dom_rng (Term.type_of constant)
      fun candidate abstract representation =
        if is_interpreted_type abstract orelse is_codatatype abstract orelse
           is_quot_type abstract orelse is_typedef abstract orelse
           is_raw_free_datatype abstract then NONE
        else
          case raw_typedef_data abstract of
              SOME {rty, ...} =>
                if rty = representation then SOME abstract else NONE
            | NONE => NONE
    in
      case candidate range domain of
          SOME ty => SOME ty
        | NONE => candidate domain range
    end handle HOL_ERR _ => NONE

  (* A typedef need not occur through Abs or Rep: it can occur solely in a
     variable, binder, or equality.  Search every type in the term tree (and
     all type arguments) before scopes are constructed. *)
  fun first_unregistered_typedef terms =
    let
      fun type_parts ty =
        #2 (Type.dest_type ty) handle HOL_ERR _ => []
      fun types_beneath ty = ty :: List.concat (map types_beneath
        (type_parts ty))
      fun candidate ty =
        if is_interpreted_type ty orelse is_codatatype ty orelse
           is_quot_type ty orelse is_typedef ty orelse
           is_raw_free_datatype ty then NONE
        else
          case raw_typedef_data ty of
              SOME _ => SOME ty
            | NONE => NONE
      val subterms = List.concat
        (map (HolKernel.find_terms (K true)) terms)
      val types = List.concat (map (types_beneath o Term.type_of) subterms)
      val constants = List.concat
        (map (HolKernel.find_terms Term.is_const) terms)
    in
      (* Retain the morphism-specialized check as a fallback for unusual
         polymorphic constant instantiations. *)
      case get_first candidate types of
          SOME ty => SOME ty
        | NONE => get_first unregistered_typedef_type constants
    end

  fun unregistered_typedef_reason terms =
    Option.map (fn ty =>
      "unregistered typedef " ^ #Tyop (Type.dest_thy_type ty) ^
        ": register with Refute.register_typedef")
      (first_unregistered_typedef terms)

  fun find_field which term =
    let
      val key = original_const_key term
      fun search_type info =
        let
          val ty = TypeBasePure.ty_of info
          fun search (_, []) = NONE
            | search (index, (field, data) :: rest) =
                if same_key (original_const_key (which data)) key then
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
    same_key (original_const_key term) expected handle HOL_ERR _ => false

  fun is_descr term =
    let
      val specialized =
        case Lib.total Term.dest_var term of
            SOME (name, _) => Refute_ModelFinder_Names.is_special_name name
          | NONE => false
    in
      not specialized andalso
      (is_named_const {Thy = "min", Name = "@"} term orelse
       is_named_const {Thy = "refute", Name = "safe_The"} term)
    end

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

  fun append_new_ersatz (entry, table) =
    if List.exists (fn ({original, ...} : ersatz) =>
         same_key original (#original entry)) table then table
    else table @ [entry]

  fun current_ersatz_table () =
    let
      val ordinary = List.foldl append_new_ersatz
        (!ersatz_registry) builtin_ersatz
      val frac = List.concat (map #ersatz (!frac_registry))
    in
      (* Upstream prepends active frac mappings to the ordinary table.  Keep
         collisions rather than deduplicating them: replacement_for selects
         the first entry, so frac has deterministic highest precedence while
         the shadowed session registration remains available after restore. *)
      frac @ ordinary
    end

  fun case_names () =
    let
      val registered = current_codatatype_registry ()
      fun entry info =
        let
          val ty = TypeBasePure.ty_of info
          val constructors = TypeBasePure.constructors_of info
          val case_const = TypeBasePure.case_const_of info
        in
          if null constructors orelse is_codatatype ty orelse
             not (is_data_type ty) then NONE
          else SOME (const_key case_const, (length constructors, 0))
        end handle HOL_ERR _ => NONE
      val raw = List.mapPartial entry (TypeBase.elts ())
      fun registered_entry (info as {case_const, constructors, ...}) =
        let val (_, scrutinee_index) = validate_codatatype_shape info
        in
          (const_key case_const, (length constructors, scrutinee_index))
        end
    in
      raw @ map registered_entry registered
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
          val zero =
            if data_ty = unsigned_bitword_type then
              Refute_ModelFinder_Names.mk_numeral 0 data_ty
            else
              numSyntax.zero_tm
          val test = boolSyntax.mk_neg
            (boolSyntax.mk_eq (zero, value))
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
        let
          val one =
            if data_ty = unsigned_bitword_type then
              Refute_ModelFinder_Names.mk_numeral 1 data_ty
            else
              numSyntax.mk_numeral Arbnum.one
          val subtraction =
            if data_ty = unsigned_bitword_type then
              retype_constant "bin"
                (Term.prim_mk_const {Thy = "arithmetic", Name = "-"})
                (binary_type data_ty data_ty)
            else
              Term.prim_mk_const {Thy = "arithmetic", Name = "-"}
        in
          Term.mk_abs (value,
            Term.list_mk_comb (subtraction, [value, one]))
        end
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
                  is_named_const
                    {Thy = "refute", Name = "PairBox"} head andalso
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

  fun quot_normal_for_type qty rty =
    Refute_ModelFinder_Names.mk_quot_normal qty rty

  fun optimized_quot_type_axioms context qty =
    let
      val {rty, partial, ...} =
        case quotient_for_type qty of
            SOME info => info
          | NONE => raise err "optimized_quot_type_axioms"
              "unregistered quotient type"
      val relation = quotient_relation_for_type qty
      val constructor = quot_constructor rty qty
      val normal = quot_normal_for_type qty rty
      val a = Term.mk_var ("a", qty)
      val x = Term.mk_var ("x", rty)
      val y = Term.mk_var ("y", rty)
      val sel_a = select_nth_constr_arg context constructor a 0 rty
      val normal_sel = Term.mk_comb (normal, sel_a)
      val normal_x = Term.mk_comb (normal, x)
      val normal_y = Term.mk_comb (normal, y)
      val is_unknown = Term.mk_thy_const
        {Thy = "refute", Name = "is_unknown",
         Ty = Type.-->(rty, Type.bool)}
      fun unknown value = Term.mk_comb (is_unknown, value)
      fun relates left right = Term.list_mk_comb (relation, [left, right])
      val fixed = boolSyntax.mk_forall
        (a, boolSyntax.mk_eq (normal_sel, sel_a))
      val respects = boolSyntax.list_mk_forall ([x, y],
        boolSyntax.list_mk_imp
          ([boolSyntax.mk_neg (unknown normal_x),
            boolSyntax.mk_neg (unknown normal_y), relates x y],
           boolSyntax.mk_eq (normal_x, normal_y)))
      val representative = boolSyntax.mk_forall (x,
        boolSyntax.list_mk_imp
          ([boolSyntax.mk_neg (unknown normal_x),
            boolSyntax.mk_neg (boolSyntax.mk_eq (normal_x, x))],
           relates x normal_x))
      val domain = boolSyntax.mk_forall (a, relates sel_a sel_a)
    in
      [fixed, respects, representative] @ (if partial then [domain] else [])
    end

  fun optimized_typedef_axioms ty =
    case typedef_for_type ty of
        NONE => []
      | SOME {univ = true, ...} => []
      | SOME {rty, rep, pred, ...} =>
          let
            val abstract = Term.mk_var ("a", ty)
            val represented = Term.mk_comb (rep, abstract)
          in
            [boolSyntax.mk_forall
              (abstract, beta_normalize (beta_apply (pred, represented)))]
          end

  fun inverse_axioms_for_rep_fun rep =
    case typedef_for_rep rep of
        NONE => []
      | SOME {inverse_axioms, ...} => inverse_axioms

  (* HOL4 states the second bijection law as the biconditional
     [!r. P r <=> rep (abs r) = r], but the encoding cannot carry it: for
     an [r] outside [P] the value [abs r] is unrepresented, so
     [rep (abs r) = r] is unknown rather than false, the biconditional is
     unknown rather than true, and no scope of a proper-subset typedef is
     then satisfiable.  Guarding the equation by [P] keeps the half that
     mentions only represented values, and the surjectivity of [rep]
     restates the discarded half without naming [abs], so the abstract
     carrier stays pinned to [P]'s extension rather than to some subset of
     it.  Together with the membership axiom [!a. P (rep a)] emitted by
     [optimized_typedef_axioms], the pair is equivalent to the
     biconditional, so this trades no models either way.  A whole-type
     typedef has [P r] equal to [T] and degenerates to [T ==> ...]. *)
  fun guarded_inverse_axiom abs rep axiom =
    let
      val (variables, body) = boolSyntax.strip_forall axiom
      val (raw_guard, equation) = boolSyntax.dest_eq body
      val _ = if Term.type_of raw_guard = Type.bool then () else raise Match
      val (represented, argument) = boolSyntax.dest_eq equation
      val (rep_head, rep_arguments) = HolKernel.strip_comb represented
      val _ = if length rep_arguments = 1 then () else raise Match
      val (abs_head, abs_arguments) =
        HolKernel.strip_comb (hd rep_arguments)
      val _ =
        if length abs_arguments = 1 andalso
           same_registered_constant rep rep_head andalso
           same_registered_constant abs abs_head andalso
           Term.aconv (hd abs_arguments) argument then ()
        else raise Match
      val guard = beta_normalize raw_guard
      val abstract = Term.variant (Term.all_vars axiom)
        (Term.mk_var ("a", Term.type_of (hd rep_arguments)))
      val onto = boolSyntax.mk_exists (abstract,
        boolSyntax.mk_eq (Term.mk_comb (rep_head, abstract), argument))
      fun close matrix = boolSyntax.list_mk_forall
        (variables, boolSyntax.mk_imp (guard, matrix))
    in
      [close equation, close onto]
    end
    handle HOL_ERR _ => [axiom] | Match => [axiom]

  (* The registration accessor above keeps returning the theorem's own
     conjuncts; only the encoding sees the guarded restatement. *)
  fun optimized_inverse_axioms_for_rep_fun rep =
    case typedef_for_rep rep of
        NONE => []
      | SOME {abs, rep = registered, inverse_axioms, ...} =>
          List.concat
            (map (guarded_inverse_axiom abs registered) inverse_axioms)

  fun codatatype_bisim_axioms context ty =
    let
      val constructors = data_type_constrs context ty
      val n = Term.mk_var ("n", bisim_iterator_type)
      val x = Term.mk_var ("x", ty)
      val y = Term.mk_var ("y", ty)
      val m = Term.mk_var ("m", bisim_iterator_type)
      val predecessor = Term.mk_comb
        (Term.mk_thy_const
           {Thy = "refute", Name = "safe_The",
            Ty = Type.-->(Type.-->(bisim_iterator_type, Type.bool),
              bisim_iterator_type)},
         Term.mk_abs (m, boolSyntax.mk_eq
           (Term.mk_comb (bisim_suc_const, m), n)))

      fun comparison constructor index argument_ty =
        let
          val left = select_nth_constr_arg context constructor x index
            argument_ty
          val right = select_nth_constr_arg context constructor y index
            argument_ty
          val relation =
            if is_codatatype argument_ty then
              Term.mk_comb (bisim_const argument_ty, predecessor)
            else
              Term.mk_thy_const
                {Thy = "min", Name = "=",
                 Ty = Type.-->(argument_ty,
                   Type.-->(argument_ty, Type.bool))}
        in
          Term.list_mk_comb (relation, [left, right])
        end

      fun branch constructor =
        let
          val argument_tys = constructor_arg_types constructor
          val same_constructor = discriminate_value context constructor y
          val indexed = ListPair.zip
            (List.tabulate (length argument_tys, fn index => index),
             argument_tys)
          val comparisons = map (fn (index, argument_ty) =>
            comparison constructor index argument_ty) indexed
          val body = List.foldr smart_conj boolSyntax.T
            (same_constructor :: comparisons)
          fun abstract (argument_ty, (serial, result)) =
            (serial + 1,
             Term.mk_abs
               (Term.mk_var ("a" ^ Int.toString serial, argument_ty),
                result))
        in
          #2 (List.foldr abstract (0, body) argument_tys)
        end

      val case_function = optimized_case_def context [] ty Type.bool
        (map branch constructors)
      val one_step = boolSyntax.mk_imp
        (boolSyntax.mk_disj
           (boolSyntax.mk_eq (n, bisim_zero_const),
            s_betapply (case_function, x)),
         Term.list_mk_comb (bisim_const ty, [n, x, y]))
      val maximum = boolSyntax.mk_imp
        (Term.list_mk_comb
           (bisim_const ty, [bisim_iterator_max_const, x, y]),
         boolSyntax.mk_eq (x, y))
    in
      [boolSyntax.list_mk_forall ([n, x, y], one_step),
       boolSyntax.list_mk_forall ([x, y], maximum)]
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
            SOME (retype_constant "ersatz"
              (Term.prim_mk_const {Thy = Thy, Name = Name})
              (Term.type_of constant))
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
        (context as {case_names, ersatz_table, whacks, total_consts,
                     semantic_weakening, ...} : mf_context) term =
    let
      fun whack_matches pattern candidate =
        case (Lib.total Term.dest_thy_const pattern,
              Lib.total Term.dest_thy_const candidate) of
            (SOME {Thy = pattern_thy, Name = pattern_name, ...},
             SOME {Thy = actual_thy, Name = actual_name, ...}) =>
              pattern_thy = actual_thy andalso
              pattern_name = actual_name andalso
              type_matches_unboxed
                (Term.type_of pattern, Term.type_of candidate)
          | _ => Term.aconv pattern candidate
      fun whacked candidate =
        List.exists (fn pattern => whack_matches pattern candidate) whacks
      fun retyped_frac_constant candidate =
        Term.is_var candidate andalso
        Option.isSome (frac_target_for_constant candidate)
      fun process_args depth arguments = map (do_term depth) arguments
      and do_term depth candidate =
        if is_numeral candidate then candidate
        else if Term.is_abs candidate then
          let val (variable, body) = Term.dest_abs candidate
          in Term.mk_abs (variable, do_term depth body) end
        else if Term.is_comb candidate then
          let val (head, arguments) = HolKernel.strip_comb candidate
          in
            if Term.is_const head orelse retyped_frac_constant head then
              do_const depth head arguments
            else
              s_betapplys (do_term depth head,
                process_args depth arguments)
          end
        else if Term.is_const candidate orelse
                retyped_frac_constant candidate then
          do_const depth candidate []
        else if whacked candidate then
          (semantic_weakening := true;
           unknown_value (Term.type_of candidate))
        else candidate
      and do_const depth constant arguments =
        let
          val key = const_key constant
          fun ordinary () =
            if same_key key {Thy = "relation", Name = "RTC"} orelse
               same_key key {Thy = "relation", Name = "RC"} then
              (* RTC is itself a Hol_reln predicate and RC has ordinary
                 equational simplifications; both would normally be
                 preserved.  Their pinned refute_unfold entries
                 intentionally take precedence so the star trick and direct
                 RTC terms reach native TC/Closure. *)
              (case def_of_const_ext context constant of
                   SOME (_, definition) =>
                     if depth >= unfold_max_depth then
                       raise Refute_ModelFinder_Util.TOO_LARGE
                         ("Refute_ModelFinder_HOL.unfold_defs_in_term",
                          "too many nested relation closure definitions")
                     else
                       do_term (depth + 1)
                         (s_betapplys (definition, arguments))
                 | NONE => Term.list_mk_comb
                     (constant, process_args depth arguments))
            else if is_never_unfold_const constant then
              Term.list_mk_comb (constant, process_args depth arguments)
            else
              case List.find (fn (other, _) => same_key key other)
                     case_names of
                  SOME (_, (constructor_count, scrutinee_index)) =>
                    let val needed = constructor_count + 1
                    in
                      if length arguments < needed then
                        do_term depth (eta_expand
                          (Term.list_mk_comb (constant, arguments))
                          (needed - length arguments))
                      else
                        let
                          val case_arguments = List.take (arguments, needed)
                          val scrutinee = do_term depth
                            (List.nth (case_arguments, scrutinee_index))
                          val functions =
                            remove_nth scrutinee_index case_arguments
                          val rest = List.drop (arguments, needed)
                          val data_ty = Term.type_of scrutinee
                          val full = Term.list_mk_comb
                            (constant, case_arguments)
                          val result_ty = Term.type_of full
                          val value = optimized_case_value context data_ty
                            result_ty functions scrutinee
                        in
                          do_term depth
                            (s_betapplys (value, process_args depth rest))
                        end
                    end
                | NONE =>
                    (case quotient_for_abs constant of
                         SOME {qty, rty, ...} =>
                           let
                             val representation = Term.mk_var ("r", rty)
                             val body = Term.mk_comb
                               (quot_constructor rty qty,
                                Term.mk_comb
                                  (quot_normal_for_type qty rty,
                                   representation))
                           in
                             do_term depth (s_betapplys
                               (Term.mk_abs (representation, body),
                                arguments))
                           end
                       | NONE =>
                         (case quotient_for_rep constant of
                              SOME {qty, rty, ...} =>
                                do_term depth (s_betapplys
                                  (selector_term_for_constructor
                                     (quot_constructor rty qty) 0,
                                   arguments))
                            | NONE =>
                         (case quotient_class_abs_for constant of
                              SOME {qty, rty, ...} =>
                                let
                                  val set = Term.mk_var
                                    ("S", Type.-->(rty, Type.bool))
                                  val choice = Term.mk_thy_const
                                    {Thy = "min", Name = "@",
                                     Ty = Type.-->
                                       (Type.-->(rty, Type.bool), rty)}
                                  val body = Term.mk_comb
                                    (quot_constructor rty qty,
                                     Term.mk_comb
                                       (quot_normal_for_type qty rty,
                                        Term.mk_comb (choice, set)))
                                in
                                  do_term depth (s_betapplys
                                    (Term.mk_abs (set, body), arguments))
                                end
                            | NONE =>
                         (case quotient_class_rep_for constant of
                              SOME {qty, rty, ...} =>
                                let
                                  val abstract = Term.mk_var ("a", qty)
                                  val representation = Term.mk_var ("r", rty)
                                  val selected = Term.mk_comb
                                    (selector_term_for_constructor
                                       (quot_constructor rty qty) 0,
                                     abstract)
                                  val body = Term.list_mk_comb
                                    (quotient_relation_for_type qty,
                                     [selected, representation])
                                in
                                  do_term depth (s_betapplys
                                    (Term.mk_abs (abstract,
                                       Term.mk_abs (representation, body)),
                                     arguments))
                                end
                            | NONE =>
                         (case typedef_for_rep constant of
                              SOME {abs, rty, ...} =>
                                do_term depth (s_betapplys
                                  (selector_term_for_constructor abs 0,
                                   arguments))
                            | NONE =>
                    if is_constr constant then
                      Term.list_mk_comb
                        (constant, process_args depth arguments)
                    else if is_stale_constr constant then
                      raise Refute_ModelFinder_Util.NOT_SUPPORTED
                        ("(non-co)constructors of codatatypes (\"" ^
                         raw_constructor_name constant ^ "\")")
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
                    else if is_equational_fun context constant orelse
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
                            (constant, process_args depth arguments))))))
        in
          if whacked constant then
            (semantic_weakening := true;
             unknown_value (Term.type_of
               (Term.list_mk_comb (constant, arguments))))
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
                  (semantic_weakening := true;
                  if depth >= unfold_max_depth then
                    raise Refute_ModelFinder_Util.TOO_LARGE
                      ("Refute_ModelFinder_HOL.unfold_defs_in_term",
                       "too many nested replacements")
                  else
                    do_const (depth + 1) replacement arguments)
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
          case_table, fixpoint_cache, iterator_table, ersatz_table,
          semantic_weakening, skolems, special_funs, wf_cache, constr_cache,
          ...}
         : mf_context) binary_ints : mf_context =
    {max_bisim_depth = max_bisim_depth, boxes = boxes, wfs = wfs,
     user_axioms = user_axioms, debug = debug, whacks = whacks,
     binary_ints = binary_ints, destroy_constrs = destroy_constrs,
     specialize = specialize, star_linear_preds = star_linear_preds,
     total_consts = total_consts, needs = needs, tac_timeout = tac_timeout,
     evals = evals, case_names = case_names, def_tables = def_tables,
     nondef_table = nondef_table, nondefs = nondefs, simp_table = simp_table,
     psimp_table = psimp_table, choice_spec_table = choice_spec_table,
     intro_table = intro_table, case_table = case_table,
     fixpoint_cache = fixpoint_cache, iterator_table = iterator_table,
     ersatz_table = ersatz_table, semantic_weakening = semantic_weakening,
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
       intro_table = ref KNametab.empty,
       case_table = ref KNametab.empty,
       fixpoint_cache = ref [],
       iterator_table = ref [],
       ersatz_table = current_ersatz_table (),
       semantic_weakening = ref false,
       skolems = ref [],
       special_funs = ref [],
       wf_cache = ref [],
       constr_cache = ref []}
    end
end
