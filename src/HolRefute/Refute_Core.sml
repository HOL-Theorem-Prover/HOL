structure Refute_Core = struct
  type term = Term.term
  type thm = Thm.thm
  type hol_type = Type.hol_type

  val refute_simp =
    ThmSetData.export_list {settype = "refute_simp", initial = []}

  val refute_psimp =
    ThmSetData.export_list {settype = "refute_psimp", initial = []}

  val refute_unfold =
    ThmSetData.export_list {settype = "refute_unfold", initial = []}

  datatype certainty =
      Genuine
    | QuasiGenuine of string list
    | Potential of string list

  type counterexample =
    { backend : string,
      certainty : certainty,
      bindings : (term * term) list,
      evals : (term * term) list,
      cert : thm option,
      scope : (hol_type * int) list option,
      stats : (string * int) list }

  datatype outcome =
      Counterexample of counterexample list
    | NoCounterexample
    | Unknown of string list

  type problem =
    { goal : term,
      assumptions : term list,
      evals : term list }

  datatype expectation =
      ExpectCex
    | ExpectNone
    | ExpectUnknown
    | NoExpectation

  datatype substrate_choice = Auto | Compute | Cv | NativeSML

  type qc_config =
    { size : int,
      iterations : int,
      depth : int,
      finite_types : bool,
      finite_type_size : int,
      default_type : hol_type list,
      substrate : substrate_choice,
      allow_function_inversion : bool,
      use_subtype : bool,
      seed : int option,
      smart_quantifier : bool,
      optimise_equality : bool }

  type config =
    { timeout : real,
      backends : string list option,
      sequential : bool,
      genuine_only : bool,
      abort_potential : bool,
      no_assms : bool,
      evals : term list,
      expect : expectation,
      max_counterexamples : int,
      tag : string,
      qc : qc_config }

  type backend =
    { name : string,
      weight : int,
      configured : unit -> bool,
      run : config -> problem -> outcome }

  val default_qc_config : qc_config =
    { size = 10,
      iterations = 100,
      depth = 10,
      finite_types = true,
      finite_type_size = 3,
      default_type = [``:num``],
      substrate = Auto,
      allow_function_inversion = false,
      use_subtype = false,
      seed = NONE,
      smart_quantifier = true,
      optimise_equality = true }

  val default_config : config =
    { timeout = 30.0,
      backends = NONE,
      sequential = false,
      genuine_only = false,
      abort_potential = false,
      no_assms = false,
      evals = [],
      expect = NoExpectation,
      max_counterexamples = 1,
      tag = "",
      qc = default_qc_config }

  val the_config = ref default_config

  fun map_qc f (cfg : config) =
    let
      val {timeout, backends, sequential, genuine_only, abort_potential,
           no_assms, evals, expect, max_counterexamples, tag, qc} = cfg
    in
      { timeout = timeout,
        backends = backends,
        sequential = sequential,
        genuine_only = genuine_only,
        abort_potential = abort_potential,
        no_assms = no_assms,
        evals = evals,
        expect = expect,
        max_counterexamples = max_counterexamples,
        tag = tag,
        qc = f qc }
    end

  fun upd_timeout value (cfg : config) =
    let
      val {backends, sequential, genuine_only, abort_potential, no_assms,
           evals, expect, max_counterexamples, tag, qc, ...} = cfg
    in
      { timeout = value, backends = backends, sequential = sequential,
        genuine_only = genuine_only, abort_potential = abort_potential,
        no_assms = no_assms, evals = evals, expect = expect,
        max_counterexamples = max_counterexamples, tag = tag, qc = qc }
    end

  fun upd_backends value (cfg : config) =
    { timeout = #timeout cfg,
      backends = value,
      sequential = #sequential cfg,
      genuine_only = #genuine_only cfg,
      abort_potential = #abort_potential cfg,
      no_assms = #no_assms cfg,
      evals = #evals cfg,
      expect = #expect cfg,
      max_counterexamples = #max_counterexamples cfg,
      tag = #tag cfg,
      qc = #qc cfg }

  fun upd_sequential value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = value,
      genuine_only = #genuine_only cfg,
      abort_potential = #abort_potential cfg,
      no_assms = #no_assms cfg,
      evals = #evals cfg,
      expect = #expect cfg,
      max_counterexamples = #max_counterexamples cfg,
      tag = #tag cfg,
      qc = #qc cfg }

  fun upd_genuine_only value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = #sequential cfg,
      genuine_only = value,
      abort_potential = #abort_potential cfg,
      no_assms = #no_assms cfg,
      evals = #evals cfg,
      expect = #expect cfg,
      max_counterexamples = #max_counterexamples cfg,
      tag = #tag cfg,
      qc = #qc cfg }

  fun upd_abort_potential value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = #sequential cfg,
      genuine_only = #genuine_only cfg,
      abort_potential = value,
      no_assms = #no_assms cfg,
      evals = #evals cfg,
      expect = #expect cfg,
      max_counterexamples = #max_counterexamples cfg,
      tag = #tag cfg,
      qc = #qc cfg }

  fun upd_no_assms value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = #sequential cfg,
      genuine_only = #genuine_only cfg,
      abort_potential = #abort_potential cfg,
      no_assms = value,
      evals = #evals cfg,
      expect = #expect cfg,
      max_counterexamples = #max_counterexamples cfg,
      tag = #tag cfg,
      qc = #qc cfg }

  fun upd_evals value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = #sequential cfg,
      genuine_only = #genuine_only cfg,
      abort_potential = #abort_potential cfg,
      no_assms = #no_assms cfg,
      evals = value,
      expect = #expect cfg,
      max_counterexamples = #max_counterexamples cfg,
      tag = #tag cfg,
      qc = #qc cfg }

  fun upd_expect value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = #sequential cfg,
      genuine_only = #genuine_only cfg,
      abort_potential = #abort_potential cfg,
      no_assms = #no_assms cfg,
      evals = #evals cfg,
      expect = value,
      max_counterexamples = #max_counterexamples cfg,
      tag = #tag cfg,
      qc = #qc cfg }

  fun upd_max_counterexamples value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = #sequential cfg,
      genuine_only = #genuine_only cfg,
      abort_potential = #abort_potential cfg,
      no_assms = #no_assms cfg,
      evals = #evals cfg,
      expect = #expect cfg,
      max_counterexamples = value,
      tag = #tag cfg,
      qc = #qc cfg }

  fun upd_tag value (cfg : config) =
    { timeout = #timeout cfg,
      backends = #backends cfg,
      sequential = #sequential cfg,
      genuine_only = #genuine_only cfg,
      abort_potential = #abort_potential cfg,
      no_assms = #no_assms cfg,
      evals = #evals cfg,
      expect = #expect cfg,
      max_counterexamples = #max_counterexamples cfg,
      tag = value,
      qc = #qc cfg }

  fun upd_qc value (cfg : config) = map_qc (fn _ => value) cfg

  fun upd_size value = map_qc (fn (qc : qc_config) =>
    { size = value, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_iterations value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = value, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_depth value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = value,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_finite_types value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = value, finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_finite_type_size value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc, finite_type_size = value,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_default_type value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc, default_type = value,
      substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_substrate value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = value,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_allow_function_inversion value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = value, use_subtype = #use_subtype qc,
      seed = #seed qc, smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_use_subtype value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = value, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_seed value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = value,
      smart_quantifier = #smart_quantifier qc,
      optimise_equality = #optimise_equality qc })

  fun upd_smart_quantifier value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = value,
      optimise_equality = #optimise_equality qc })

  fun upd_optimise_equality value = map_qc (fn (qc : qc_config) =>
    { size = #size qc, iterations = #iterations qc, depth = #depth qc,
      finite_types = #finite_types qc,
      finite_type_size = #finite_type_size qc,
      default_type = #default_type qc, substrate = #substrate qc,
      allow_function_inversion = #allow_function_inversion qc,
      use_subtype = #use_subtype qc, seed = #seed qc,
      smart_quantifier = #smart_quantifier qc, optimise_equality = value })

  type instance =
    { goal : term,
      evals : term list,
      card : int,
      size_matters : bool }

  datatype preprocess_result =
      Preprocessed of instance list
    | NotExecutable of string list

  fun strip_outer_forall tm = boolSyntax.strip_forall tm

  val normal_rewrites =
    [ boolTheory.NOT_EXISTS_THM,
      boolTheory.NOT_FORALL_THM,
      boolTheory.AND_IMP_INTRO,
      boolTheory.FUN_EQ_THM ] @
    Drule.CONJUNCTS boolTheory.PULL_EXISTS @
    Drule.CONJUNCTS boolTheory.PULL_FORALL

  fun normalize tm =
    #2 (boolSyntax.dest_eq (Thm.concl
      (Ho_Rewrite.REWRITE_CONV normal_rewrites tm)))
    handle _ => tm

  fun expand_quantifiers tm =
    let
      fun expand tm =
        if boolSyntax.is_forall tm then
          let
            val (variable, body) = boolSyntax.dest_forall tm
            val body = expand body
          in
            case Refute_Gen.enumerate (Term.type_of variable) of
                NONE => boolSyntax.mk_forall (variable, body)
              | SOME values =>
                  boolSyntax.list_mk_conj
                    (map (fn value => Term.subst
                      [{redex = variable, residue = value}] body)
                      values)
          end
        else if boolSyntax.is_exists tm then
          let
            val (variable, body) = boolSyntax.dest_exists tm
            val body = expand body
          in
            case Refute_Gen.enumerate (Term.type_of variable) of
                NONE => boolSyntax.mk_exists (variable, body)
              | SOME values =>
                  boolSyntax.list_mk_disj
                    (map (fn value => Term.subst
                      [{redex = variable, residue = value}] body)
                      values)
          end
        else if Term.is_comb tm then
          let
            val (left, right) = Term.dest_comb tm
          in
            Term.mk_comb (expand left, expand right)
          end
        else if Term.is_abs tm then
          let
            val (variable, body) = Term.dest_abs tm
          in
            Term.mk_abs (variable, expand body)
          end
        else
          tm
    in
      expand tm
    end

  fun has_unexpanded_binder tm =
    if boolSyntax.is_forall tm orelse boolSyntax.is_exists tm orelse
       boolSyntax.is_select tm then
      true
    else if Term.is_abs tm then
      let
        val (variable, body) = Term.dest_abs tm
      in
        not (Option.isSome
          (Refute_Gen.enumerate (Term.type_of variable))) orelse
        has_unexpanded_binder body
      end
    else if Term.is_comb tm then
      let
        val (left, right) = Term.dest_comb tm
      in
        has_unexpanded_binder left orelse has_unexpanded_binder right
      end
    else
      false

  fun term_constants tm =
    let
      fun collect seen tm =
        if Term.is_const tm then
          if List.exists (fn old => Term.same_const old tm) seen then seen
          else tm :: seen
        else if Term.is_comb tm then
          let
            val (left, right) = Term.dest_comb tm
          in
            collect (collect seen left) right
          end
        else if Term.is_abs tm then
          collect seen (Term.body tm)
        else
          seen
    in
      collect [] tm
    end

  fun executable_constant comp_items constant =
    if TypeBase.is_constructor constant then
      true
    else
      let
        val {Name, Thy, ...} = Term.dest_thy_const constant
      in
        List.exists (fn ((name, thy), transforms) =>
          name = Name andalso thy = Thy andalso not (null transforms))
          comp_items
      end

  fun nonexecutable_constants terms =
    let
      val comp_items = computeLib.listItems (!computeLib.the_compset)
      fun add (term, constants) =
        List.foldl (fn (constant, collected) =>
          if List.exists (fn old => Term.same_const old constant) collected
          then collected
          else constant :: collected) constants (term_constants term)
      val constants = List.foldl add [] terms
    in
      List.filter (not o executable_constant comp_items) constants
    end

  fun show_constants constants =
    String.concatWith ", "
      (Listsort.sort String.compare
        (map Parse.term_to_string constants))

  fun rf_type number =
    Type.mk_thy_type
      { Thy = "refute", Tyop = "rf" ^ Int.toString number, Args = [] }

  fun clamped_finite_type_size size = Int.max (1, Int.min (6, size))

  fun monomorphic_types qc =
    if #finite_types qc then
      List.tabulate (clamped_finite_type_size (#finite_type_size qc),
        fn index => rf_type (index + 1))
    else
      #default_type qc

  fun add_equation_eval_terms goal evals =
    let
      val (_, conclusion) = boolSyntax.strip_imp goal
    in
      case Lib.total boolSyntax.dest_eq conclusion of
          SOME (left, right) =>
            if Term.is_var left orelse Term.is_var right then evals
            else evals @ [left, right]
        | NONE => evals
    end

  fun instance_size_matters goal =
    List.exists (fn variable =>
      not (Option.isSome (Refute_Gen.enumerate (Term.type_of variable))))
      (Term.free_vars_lr goal)

  fun preprocess (cfg : config) (problem : problem) =
    let
      val assumptions =
        if #no_assms cfg then [] else #assumptions problem
      val initial_goal = boolSyntax.list_mk_imp (assumptions, #goal problem)
      val normalized_goal = normalize initial_goal
      val expanded_goal = expand_quantifiers normalized_goal
      val input_evals = #evals problem @ #evals cfg
      val types = monomorphic_types (#qc cfg)
      val tyvars = Lib.U
        (map Term.type_vars_in_term (expanded_goal :: input_evals))
      fun make_instance (card, replacement) =
        let
          val theta = map (fn tyvar =>
            {redex = tyvar, residue = replacement}) tyvars
          val goal = Term.inst theta expanded_goal
          val evals = map (Term.inst theta) input_evals
          val evals = add_equation_eval_terms goal evals
        in
          { goal = goal,
            evals = evals,
            card = card,
            size_matters = instance_size_matters goal }
        end
      val instances =
        if null tyvars then
          [make_instance (1, Type.bool)]
        else
          List.map (fn (card, replacement) =>
            make_instance (card, replacement))
            (ListPair.zip (List.tabulate (length types, fn index => index + 1),
              types))
      val binders_remain = has_unexpanded_binder expanded_goal
      val constants =
        if binders_remain then []
        else nonexecutable_constants
          (List.concat (map (fn instance =>
            #goal instance :: #evals instance) instances))
    in
      if binders_remain then
        NotExecutable ["not executable: unexpanded binder"]
      else if null constants then
        Preprocessed instances
      else
        NotExecutable ["not executable: " ^ show_constants constants]
    end

  structure Private = struct
    val trace = ref 1
    val _ = Feedback.register_trace ("Refute", trace, 4)

    fun say level message =
      if !trace >= level then Feedback.HOL_MESG message else ()

    fun expectation_to_string ExpectCex = "ExpectCex"
      | expectation_to_string ExpectNone = "ExpectNone"
      | expectation_to_string ExpectUnknown = "ExpectUnknown"
      | expectation_to_string NoExpectation = "NoExpectation"

    fun substrate_to_string Auto = "Auto"
      | substrate_to_string Compute = "Compute"
      | substrate_to_string Cv = "Cv"
      | substrate_to_string NativeSML = "NativeSML"

    fun option_to_string f NONE = "NONE"
      | option_to_string f (SOME x) = "SOME " ^ f x

    fun bool_to_string true = "true"
      | bool_to_string false = "false"
  end

  fun show_config () =
    let
      val {timeout, backends, sequential, genuine_only, abort_potential,
           no_assms, evals, expect, max_counterexamples, tag, qc} =
        !the_config
      val q = qc
      val show = Private.say 1
      val types = String.concatWith ", " (map Parse.type_to_string
        (#default_type q))
    in
      List.app show
        [ "timeout = " ^ Real.toString timeout ^ "\n",
          "backends = " ^ Private.option_to_string
            (String.concatWith ", ") backends ^ "\n",
          "sequential = " ^ Private.bool_to_string sequential ^ "\n",
          "genuine_only = " ^ Private.bool_to_string genuine_only ^ "\n",
          "abort_potential = " ^ Private.bool_to_string abort_potential ^ "\n",
          "no_assms = " ^ Private.bool_to_string no_assms ^ "\n",
          "evals = " ^ Int.toString (length evals) ^ " terms\n",
          "expect = " ^ Private.expectation_to_string expect ^ "\n",
          "max_counterexamples = " ^ Int.toString max_counterexamples ^ "\n",
          "tag = " ^ tag ^ "\n",
          "size = " ^ Int.toString (#size q) ^ "\n",
          "iterations = " ^ Int.toString (#iterations q) ^ "\n",
          "depth = " ^ Int.toString (#depth q) ^ "\n",
          "finite_types = " ^ Private.bool_to_string (#finite_types q) ^
            "\n",
          "finite_type_size = " ^ Int.toString (#finite_type_size q) ^
            "\n",
          "default_type = " ^ types ^ "\n",
          "substrate = " ^ Private.substrate_to_string (#substrate q) ^
            "\n",
          "allow_function_inversion = " ^
            Private.bool_to_string (#allow_function_inversion q) ^ "\n",
          "use_subtype = " ^ Private.bool_to_string (#use_subtype q) ^
            "\n",
          "seed = " ^ Private.option_to_string Int.toString (#seed q) ^
            "\n",
          "smart_quantifier = " ^
            Private.bool_to_string (#smart_quantifier q) ^ "\n",
          "optimise_equality = " ^
            Private.bool_to_string (#optimise_equality q) ^ "\n" ]
    end

  val backend_registry : (string * backend) list ref = ref []

  fun backend_before (left : string * backend) (right : string * backend) =
    #weight (#2 left) < #weight (#2 right) orelse
    (#weight (#2 left) = #weight (#2 right) andalso #1 left < #1 right)

  fun insert_backend entry [] = [entry]
    | insert_backend entry (other :: rest) =
        if backend_before entry other then entry :: other :: rest
        else other :: insert_backend entry rest

  fun register_backend backend =
    let
      val without_old =
        List.filter (fn (name, _) => name <> #name backend) (!backend_registry)
      val entry = (#name backend, backend)
    in
      backend_registry := insert_backend entry without_old
    end

  fun registered_backends () = map #2 (!backend_registry)

  fun lookup_backend name =
    Option.map #2 (List.find (fn (registered, _) => registered = name)
      (!backend_registry))

  fun selected_backends names =
    let
      fun requested backend =
        case names of
            NONE => true
          | SOME wanted => List.exists (fn name => name = #name backend) wanted
    in
      map #2 (List.filter (fn (_, backend) =>
        requested backend andalso (#configured backend) ())
        (!backend_registry))
    end

  val select_backends = selected_backends
  fun configured_backends () = selected_backends NONE

  fun lookup_stat key stats =
    case List.find (fn (name, _) => name = key) stats of
        NONE => NONE
      | SOME (_, value) => SOME value

  fun format_stats stats =
    let
      fun ordinary (key, suffix) =
        case lookup_stat key stats of
            NONE => NONE
          | SOME value => SOME (Int.toString value ^ suffix)
      fun named (key, value) = key ^ " " ^ Int.toString value
      val msec =
        case lookup_stat "msec" stats of
            NONE => NONE
          | SOME value => SOME
              (Real.toString (Real.fromInt value / 1000.0) ^ "s")
      val fields =
        [ Option.map (fn value => "size " ^ Int.toString value)
            (lookup_stat "size" stats),
          Option.map (fn value => "card " ^ Int.toString value)
            (lookup_stat "card" stats),
          ordinary ("tests", " tests"),
          msec ]
      val fallback =
        map named (List.filter (fn (key, _) =>
          key <> "size" andalso key <> "card" andalso key <> "tests" andalso
          key <> "msec") stats)
      val present = List.mapPartial (fn value => value) fields @ fallback
    in
      if null present then "" else " (" ^ String.concatWith ", " present ^ ")"
    end

  fun format_bindings bindings =
    String.concatWith "\n" (map (fn (name, value) =>
      "  " ^ Parse.term_to_string name ^ " = " ^
      Parse.term_to_string value) bindings)

  fun format_evals evals =
    String.concatWith "\n" (map (fn (term, value) =>
      "  " ^ Parse.term_to_string term ^ " = " ^
      Parse.term_to_string value) evals)

  fun format_reasons title reasons =
    if null reasons then "" else
      "\n" ^ title ^ "\n" ^ String.concatWith "\n"
        (map (fn reason => "  " ^ reason) reasons)

  fun format_counterexample (cex : counterexample) =
    let
      val {backend, certainty, bindings, evals, cert, stats, ...} = cex
      val header = "Refute found a counterexample (backend: " ^ backend ^
        ")" ^ format_stats stats ^ ":"
      val binding_text =
        if null bindings then "" else "\n" ^ format_bindings bindings
      val eval_text =
        if null evals then "" else "\nEvaluated terms:\n" ^ format_evals evals
      val cert_text =
        case cert of
            NONE => ""
          | SOME theorem => "\nCertified: " ^ Parse.thm_to_string theorem
      val certainty_text =
        case certainty of
            Genuine => ""
          | QuasiGenuine reasons => format_reasons "Quasi-genuine:" reasons
          | Potential reasons =>
              format_reasons "Potential counterexample:" reasons ^
              "\n…continuing search for a genuine counterexample"
    in
      header ^ binding_text ^ eval_text ^ cert_text ^ certainty_text
    end

  fun format_outcome (cfg : config) result =
    let
      val body =
        case result of
            Counterexample cexs =>
              String.concatWith "\n\n" (map format_counterexample cexs)
          | NoCounterexample =>
              "Refute: goal holds for all tested finite instantiations"
          | Unknown reasons =>
              "Refute could not determine an answer" ^
              format_reasons "Reasons:" reasons
    in
      body ^ #tag cfg
    end

  fun report_outcome (cfg : config) result =
    Private.say 1 (format_outcome cfg result ^ "\n")
  val report = report_outcome
end
