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
