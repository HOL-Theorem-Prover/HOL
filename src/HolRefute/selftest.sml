open testutils
open refuteTheory
open sortingTheory
open realTheory
open Refute_Core
open Refute_Gen
open Refute_Cert
open Refute_Eval
open Refute_EvalCompute
open Refute_QC

val erc = ref 0
val _ = diemode := Remember erc

val _ = tprint "Refute skeleton smoke check"
val _ = require_msg (check_result (fn () => true)) (fn () => "")
                    (fn () => ()) ()

val _ = tprint "Refute support theory"

fun constructor_count ty =
  length (TypeBasePure.constructors_of (valOf (TypeBase.fetch ty)))

fun check_type (ty, count) =
  require_msg (check_result (fn () => constructor_count ty = count))
              (fn () => "unexpected TypeBase constructor count")
              (fn () => ()) ()

val _ = check_type (``:refute$rf1``, 1)
val _ = check_type (``:refute$rf2``, 2)
val _ = check_type (``:refute$rf3``, 3)
val _ = check_type (``:refute$rf4``, 4)
val _ = check_type (``:refute$rf5``, 5)
val _ = check_type (``:refute$rf6``, 6)

fun check_empty settype =
  require_msg (check_result
    (fn () => null (ThmSetData.current_data {settype = settype})))
    (fn () => "theorem set is not empty") (fn () => ()) ()

val _ = check_empty "refute_simp"
val _ = check_empty "refute_psimp"
val _ = check_empty "refute_unfold"

val _ = tprint "Refute core configuration"

fun size_update_is_local () =
  let
    val updated = upd_size 5 default_config
    val original = #qc default_config
    val after = #qc updated
  in
    #size after = 5 andalso
    #iterations after = #iterations original andalso
    #depth after = #depth original andalso
    #finite_types after = #finite_types original andalso
    #finite_type_size after = #finite_type_size original andalso
    #default_type after = #default_type original andalso
    #substrate after = #substrate original andalso
    #allow_function_inversion after =
      #allow_function_inversion original andalso
    #use_subtype after = #use_subtype original andalso
    #seed after = #seed original andalso
    #smart_quantifier after = #smart_quantifier original andalso
    #optimise_equality after = #optimise_equality original andalso
    Real.== (#timeout updated, #timeout default_config) andalso
    #backends updated = #backends default_config andalso
    #sequential updated = #sequential default_config andalso
    #genuine_only updated = #genuine_only default_config andalso
    #abort_potential updated = #abort_potential default_config andalso
    #no_assms updated = #no_assms default_config andalso
    null (#evals updated) andalso
    #expect updated = #expect default_config andalso
    #max_counterexamples updated = #max_counterexamples default_config andalso
    #tag updated = #tag default_config
  end

val _ = require_msg (check_result size_update_is_local) (fn () =>
  "upd_size changed a field other than qc.size") (fn () => ()) ()

val _ = tprint "Refute core backend registry"

fun dummy_backend name weight : backend =
  { name = name,
    weight = weight,
    configured = fn () => true,
    run = fn _ => fn _ => Unknown [] }

val registry_alpha = dummy_backend "refute-core-alpha" (~97)
val registry_beta = dummy_backend "refute-core-beta" (~98)
val registry_alpha_replacement = dummy_backend "refute-core-alpha" (~96)

val _ = register_backend registry_alpha
val _ = register_backend registry_beta
val _ = register_backend registry_alpha_replacement

fun core_backend_names () =
  map #name (List.filter (fn backend =>
    #name backend = "refute-core-alpha" orelse
    #name backend = "refute-core-beta") (registered_backends ()))

val _ = require_msg
  (check_result (fn names => names =
    ["refute-core-beta", "refute-core-alpha"]))
  (fn names => "unexpected registry order: " ^ String.concatWith ", " names)
  core_backend_names ()

val _ = tprint "Refute core silent report"

val report_cex : counterexample =
  { backend = "selftest",
    substrate = "compute",
    certainty = Genuine,
    bindings = [(``x : num``, ``0``)],
    evals = [],
    cert = NONE,
    scope = NONE,
    stats = [("size", 3), ("card", 2), ("tests", 412), ("msec", 400)] }

fun silent_report () =
  let
    val prior = Feedback.current_trace "Refute"
    val _ = Feedback.set_trace "Refute" 0
    val _ = report_outcome default_config (Counterexample [report_cex])
    val _ = Feedback.set_trace "Refute" prior
  in
    true
  end

val _ = require_msg (check_result silent_report) (fn () =>
  "reporting failed at trace level zero") (fn () => ()) ()

val _ = tprint "Refute generator derivation"

fun check_gen name predicate ty =
  require_msg (check_result (fn () => predicate (spec_of ty)))
    (fn () => "unexpected generator specification for " ^ name)
    (fn () => ()) ()

fun is_num_kind kind (GenNum actual) = kind = actual
  | is_num_kind _ _ = false

fun datatype_info (GenDatatype info) = SOME info
  | datatype_info _ = NONE

fun has_no_generator ty =
  ((ignore (spec_of ty); false)
   handle NoGenerator (_, reason) => String.size reason > 0)

val _ = check_gen "num" (is_num_kind Num) ``:num``
val _ = check_gen "char" (is_num_kind Char) ``:char``
val _ = check_gen "word" (fn GenNum (Word 8) => true | _ => false)
  ``:bool[8]``
val _ = check_gen "function" (fn GenFun _ => true | _ => false)
  ``:num -> bool``
val _ = check_gen "rf3" (fn GenEnum values => length values = 3 | _ => false)
  ``:refute$rf3``

fun list_shape () =
  case datatype_info (spec_of ``:'a list``) of
    SOME {constrs, recursive, min_size, family} =>
      length constrs = 2 andalso recursive = [[], [false, true]] andalso
      min_size = [[], [0, 1]] andalso length family = 1
  | NONE => false

fun option_shape () =
  case datatype_info (spec_of ``:'a option``) of
    SOME {constrs, recursive, min_size, family} =>
      length constrs = 2 andalso recursive = [[], [false]] andalso
      min_size = [[], [0]] andalso length family = 1
  | NONE => false

val _ = require_msg (check_result list_shape) (fn () =>
  "list generator has an unexpected recursive shape") (fn () => ()) ()
val _ = require_msg (check_result option_shape) (fn () =>
  "option generator has an unexpected recursive shape") (fn () => ()) ()

val _ = Datatype.Datatype `rg_rose = RGLeaf | RGNode ((rg_rose) list)`
val _ = Datatype.Datatype `rg_left = RGLeft | RGToRight rg_right;
                           rg_right = RGRight rg_left`
val _ = Datatype.Datatype `rg_record = <| rg_field : num |>`
val _ = Datatype.Datatype `rg_enum = RGRed | RGGreen | RGBlue`

val _ = require_msg (check_result (fn () =>
  case cached_spec ``:refute$rf3`` of NONE => true | SOME _ => false))
  (fn () => "generator cache was not invalidated") (fn () => ()) ()

fun rose_shape () =
  case datatype_info (spec_of ``:rg_rose``) of
    SOME {recursive, min_size, family, ...} =>
      recursive = [[], [true]] andalso min_size = [[], [1]] andalso
      length family = 1
  | NONE => false

fun mutual_shape () =
  case datatype_info (spec_of ``:rg_right``) of
    SOME {recursive, min_size, family, ...} =>
      recursive = [[true]] andalso min_size = [[1]] andalso
      length family = 2
  | NONE => false

val _ = require_msg (check_result rose_shape) (fn () =>
  "rose generator has an unexpected recursive shape") (fn () => ()) ()
val _ = require_msg (check_result mutual_shape) (fn () =>
  "mutual generator has an unexpected recursive shape") (fn () => ()) ()
val _ = check_gen "record" (fn GenDatatype _ => true | _ => false)
  ``:rg_record``
val _ = check_gen "enum" (fn GenEnum values => length values = 3 | _ => false)
  ``:rg_enum``
val _ = require_msg (check_result (fn () =>
  recursive_under_function [``:rg_rose``] ``:rg_rose -> bool``))
  (fn () => "recursive function occurrence was not detected")
  (fn () => ()) ()
val real_ty = Type.mk_thy_type {Thy = "real", Tyop = "real", Args = []}
  handle Feedback.HOL_ERR _ => ``:ind``
val _ = require_msg (check_result (fn () => has_no_generator real_ty))
  (fn () => "real unexpectedly has a generator") (fn () => ()) ()
val _ = require_msg (check_result (fn () => has_no_generator ``:ind``))
  (fn () => "unknown type unexpectedly has a generator") (fn () => ()) ()

val _ = tprint "Refute enumeration and registries"

fun check_cardinality ty expected =
  require_msg (check_result (fn () => cardinality ty = expected))
    (fn () => "unexpected cardinality") (fn () => ()) ()

val _ = check_cardinality ``:bool`` (SOME 2)
val _ = check_cardinality ``:refute$rf3`` (SOME 3)
val _ = check_cardinality ``:bool[8]`` (SOME 256)
val _ = check_cardinality ``:refute$rf2 # bool`` (SOME 4)
val _ = check_cardinality ``:bool -> bool`` (SOME 4)
val _ = check_cardinality ``:bool[8] -> bool`` NONE
val _ = check_cardinality ``:num`` NONE

fun is_enumerated ty count =
  case enumerate ty of
    SOME values => length values = count
  | NONE => false

val _ = require_msg (check_result (fn () => is_enumerated ``:bool`` 2))
  (fn () => "bool was not completely enumerated") (fn () => ()) ()
val _ = require_msg (check_result (fn () =>
  is_enumerated ``:refute$rf3`` 3))
  (fn () => "rf3 was not completely enumerated") (fn () => ()) ()
val _ = require_msg (check_result (fn () =>
  is_enumerated ``:refute$rf2 # bool`` 4))
  (fn () => "product was not completely enumerated") (fn () => ()) ()

fun eval_rhs tm =
  let
    val theorem = computeLib.CBV_CONV (!computeLib.the_compset) tm
  in
    #2 (boolSyntax.dest_eq (Thm.concl theorem))
  end

fun function_graphs_work () =
  case (enumerate ``:bool -> refute$rf2``, enumerate ``:refute$rf2``) of
    (SOME graphs, SOME values) =>
      length graphs = 4 andalso
      List.all (fn graph =>
        List.all (fn input =>
          List.exists (fn value =>
            Term.aconv (eval_rhs (Term.mk_comb (graph, input))) value)
            values) [boolSyntax.T, boolSyntax.F]) graphs
  | _ => false

val _ = require_msg (check_result function_graphs_work) (fn () =>
  "function graphs did not EVAL on both boolean inputs") (fn () => ()) ()

val empty_custom : custom_gen = {enumerate = NONE, random = NONE}
val finite_custom : custom_gen =
  {enumerate = SOME (fn _ => [``0``]), random = NONE}

fun rejects_empty_custom () =
  ((register_generator ``:ind`` empty_custom; false)
   handle Fail _ => true)

val _ = require_msg (check_result rejects_empty_custom) (fn () =>
  "an empty custom generator was accepted") (fn () => ()) ()
val _ = register_generator ``:ind`` finite_custom
val _ = require_msg (check_result (fn () =>
  case spec_of ``:ind`` of GenCustom _ => true | _ => false))
  (fn () => "custom generator was not registered") (fn () => ()) ()

val abstract_ty = ``:rg_record``
val abstract_predicate = ``\x : rg_record. T``
val abstract_constructor =
  hd (TypeBasePure.constructors_of (valOf (TypeBase.fetch abstract_ty)))
val _ = abstract_generator
  {ty = abstract_ty,
   constructors = [abstract_constructor],
   pred = SOME abstract_predicate}

fun abstract_generator_works () =
  (case spec_of abstract_ty of
     GenDatatype {constrs, family, ...} =>
       length constrs = 1 andalso family = [abstract_ty]
   | _ => false) andalso
  (case predicate_of abstract_ty of
     SOME predicate => Term.aconv predicate abstract_predicate
   | NONE => false)

val _ = require_msg (check_result abstract_generator_works) (fn () =>
  "abstract generator or predicate registry was not populated")
  (fn () => ()) ()

val _ = tprint "Refute preprocessing and executability"

fun preprocessing_problem goal : problem =
  { goal = goal, assumptions = [], evals = [] }

fun preprocessed_instances result =
  case result of
      Preprocessed instances => SOME instances
    | NotExecutable _ => NONE

fun has_conjunction tm =
  case Lib.total boolSyntax.dest_conj tm of
      SOME _ => true
    | NONE =>
        if Term.is_comb tm then
          let
            val (left, right) = Term.dest_comb tm
          in
            has_conjunction left orelse has_conjunction right
          end
        else
          false

fun two_way_disjunction tm =
  case Lib.total boolSyntax.dest_disj tm of
      SOME _ => true
    | NONE => false

fun bool_forall_expands () =
  case preprocessed_instances
    (preprocess default_config
      (preprocessing_problem ``p /\ (!x : bool. x)``)) of
      SOME [instance] => has_conjunction (#goal instance)
    | _ => false

val _ = require_msg (check_result bool_forall_expands) (fn () =>
  "a boolean universal did not expand to a two-way conjunction")
  (fn () => ()) ()

fun explicit_forall_is_stripped () =
  case preprocessed_instances
    (preprocess (upd_finite_types false default_config)
      (preprocessing_problem
        ``!x : 'a. (f : 'a -> 'a) x = (g x : 'a)``)) of
      SOME [instance] =>
        not (boolSyntax.is_forall (#goal instance)) andalso
        length (#evals instance) = 2
    | _ => false

val _ = require_msg (check_result explicit_forall_is_stripped) (fn () =>
  "an explicit outer universal was not stripped before preprocessing")
  (fn () => ()) ()

fun rf2_exists_expands () =
  case preprocessed_instances
    (preprocess default_config
      (preprocessing_problem ``?x : refute$rf2. x = rf2_1``)) of
      SOME [instance] => two_way_disjunction (#goal instance)
    | _ => false

val _ = require_msg (check_result rf2_exists_expands) (fn () =>
  "an rf2 existential did not expand to a two-way disjunction")
  (fn () => ()) ()

fun num_binder_is_not_executable () =
  case preprocess default_config
    (preprocessing_problem ``q (!n : num. n = 0)``) of
      NotExecutable _ => true
    | Preprocessed _ => false

val _ = require_msg (check_result num_binder_is_not_executable) (fn () =>
  "a universal over num was accepted as executable")
  (fn () => ()) ()

fun negated_exists_normalizes () =
  let
    val normalized = normalize ``~(?x : bool. x)``
    val (variables, body) = strip_outer_forall normalized
  in
    length variables = 1 andalso not (boolSyntax.is_forall body)
  end

val _ = require_msg (check_result negated_exists_normalizes) (fn () =>
  "a negated existential did not normalize and strip as a universal")
  (fn () => ()) ()

fun all_same_type ty variables =
  List.all (fn variable => Type.compare (Term.type_of variable, ty) = EQUAL)
    variables

val polymorphic_goal = ``p (x : 'a) /\ q (y : 'b)``

fun value_variable_types tm =
  List.map Term.type_of (List.filter (fn variable =>
    case Lib.total Type.dom_rng (Term.type_of variable) of
        NONE => true
      | SOME _ => false) (Term.free_vars_lr tm))

fun finite_type_instances () =
  case preprocessed_instances
    (preprocess (upd_finite_type_size 3 default_config)
      (preprocessing_problem polymorphic_goal)) of
      SOME instances =>
        length instances = 3 andalso
        List.all (fn instance =>
          all_same_type (rf_type (#card instance))
            (List.map (fn ty => Term.mk_var ("x", ty))
              (value_variable_types (#goal instance)))) instances
    | NONE => false

val _ = require_msg (check_result finite_type_instances) (fn () =>
  "finite-type monomorphization did not produce rf1 through rf3")
  (fn () => ()) ()

fun default_type_instance () =
  case preprocessed_instances
    (preprocess (upd_finite_types false default_config)
      (preprocessing_problem polymorphic_goal)) of
      SOME [instance] =>
        #card instance = 1 andalso
        all_same_type numSyntax.num
          (List.map (fn ty => Term.mk_var ("x", ty))
            (value_variable_types (#goal instance)))
    | _ => false

val _ = require_msg (check_result default_type_instance) (fn () =>
  "default-type monomorphization did not use num")
  (fn () => ()) ()

fun equation_adds_evals () =
  case preprocessed_instances
    (preprocess default_config
      (preprocessing_problem ``(f : bool -> bool) x = (g x : bool)``)) of
      SOME [instance] => length (#evals instance) = 2
    | _ => false

val _ = require_msg (check_result equation_adds_evals) (fn () =>
  "an equational conclusion did not add both evaluation terms")
  (fn () => ()) ()

val _ = Theory.new_constant ("refute_task07_unmapped", ``:bool``)

fun unmapped_constant_is_not_executable () =
  case preprocess default_config
    (preprocessing_problem ``refute_task07_unmapped``) of
      NotExecutable [reason] =>
        String.isSubstring "refute_task07_unmapped" reason
    | _ => false

val _ = require_msg
  (check_result unmapped_constant_is_not_executable) (fn () =>
  "a constant without a compute-set entry was accepted")
  (fn () => ()) ()

val _ = tprint "Refute QC plan compiler"

fun plan_is_bind_with_fallback plan =
  case plan of
      Gen (_, Gen (_, Bind (_, _, SOME (Gen (_, Gen (_, Test _))),
        Gen (_, Test _)))) => true
    | _ => false

fun plan_is_single_split plan =
  case plan of
      Gen (_, Split (_, [(_, variables, _)])) => length variables = 1
    | _ => false

fun plan_is_generic_guard plan =
  case plan of
      Gen (_, Gen (_, Guard (_, Gen (_, Test _)))) => true
    | _ => false

fun plan_is_fmap_lookup plan =
  case plan of
      Gen (_, Gen (_, Split (_, [(_, variables, _)]))) =>
        length variables = 1
    | _ => false

fun plan_is_distinct_zip plan =
  case plan of
      Gen (_, Gen (_, Guard (_, Test _))) => true
    | _ => false

fun plan_is_naive goal plan =
  case plan of
      Gen (_, Test tested) => Term.aconv tested goal
    | _ => false

fun plan_has_abstract_guard plan =
  case plan of
      Gen (_, Guard (_, Test _)) => true
    | _ => false

val bind_goal = ``(x : num) = f (y : num) ==> r (x : num)``
val split_goal = ``(z : num option) = SOME (x : num) ==> T``
val guard_goal = ``(p : num -> bool) x ==> q (x : num)``
val fmap_lookup_goal =
  ``(m1 : num -> num option) k = SOME (v : num) ==> p m1 k v``
val distinct_zip_goal =
  ``ALL_DISTINCT (ZIP (xs : num list, ys : num list)) ==> T``
val naive_goal = ``(x : num) = 0 ==> F``
val abstract_guard_goal = ``(r : rg_record) = r``

fun check_plan predicate message goal =
  require_msg (check_result predicate) (fn plan =>
    message ^ "\n" ^ pp_plan plan)
    (fn () => compile_plan default_config goal) ()

val _ = check_plan plan_is_bind_with_fallback
  "free-variable equality did not compile to Bind with fallback" bind_goal

val _ = check_plan plan_is_single_split
  "constructor equality did not compile to a single Split branch" split_goal

val _ = check_plan plan_is_generic_guard
  "generic premise did not compile to Guard" guard_goal

val _ = check_plan plan_is_fmap_lookup
  "fmap-lookup premise did not compile to the expected Split" fmap_lookup_goal

val _ = check_plan plan_is_distinct_zip
  "distinct/zip premise did not compile to Guard" distinct_zip_goal

val _ = require_msg (check_result (plan_is_naive naive_goal)) (fn _ =>
  "smart_quantifier := false did not retain the whole goal")
  (fn () => compile_plan (upd_smart_quantifier false default_config)
    naive_goal) ()

val _ = check_plan plan_has_abstract_guard
  "abstract-generator predicate was not inserted as Guard" abstract_guard_goal

val _ = tprint "Refute QC exhaustive backend"

fun compute_is_first_substrate () =
  case get_substrates () of
      substrate :: _ =>
        #name substrate = "compute" andalso #priority substrate = 30
    | [] => false

val _ = require_msg (check_result compute_is_first_substrate) (fn () =>
  "the compute substrate was not registered at priority 30")
  (fn () => ()) ()

fun dummy_compile _ _ _ = Inapplicable ["dummy substrate"]

val seam_alpha : substrate =
  {name = "refute-seam-alpha", priority = 50, compile = dummy_compile}
val seam_beta : substrate =
  {name = "refute-seam-beta", priority = 40, compile = dummy_compile}
val seam_alpha_replacement : substrate =
  {name = "refute-seam-alpha", priority = 35, compile = dummy_compile}

val _ = register_substrate seam_alpha
val _ = register_substrate seam_beta
val _ = register_substrate seam_alpha_replacement

fun seam_registry_order () =
  map #name (List.filter (fn substrate =>
    #name substrate = "refute-seam-alpha" orelse
    #name substrate = "refute-seam-beta") (get_substrates ())) =
  ["refute-seam-alpha", "refute-seam-beta"]

val _ = require_msg (check_result seam_registry_order) (fn () =>
  "substrate registry replacement or priority ordering failed")
  (fn () => ()) ()

fun qc_problem goal : problem = {goal = goal, assumptions = [], evals = []}

fun qc_instances config goal =
  case preprocess config (qc_problem goal) of
      Preprocessed instances => instances
    | NotExecutable _ => []

fun exhaustive config goal =
  case preprocess config (qc_problem goal) of
      NotExecutable reasons => Unknown reasons
    | Preprocessed instances => strategy_run Exhaustive config instances

fun has_binding predicate (Counterexample (cex :: _)) =
      List.exists predicate (#bindings cex)
  | has_binding _ _ = false

fun reverse_counterexample () =
  let
    val config = upd_size 3 (upd_max_counterexamples 1 default_config)
    val result = exhaustive config ``REVERSE (xs : num list) = xs``
  in
    (case result of
         Counterexample (cex :: _) => #substrate cex = "compute"
       | _ => false) andalso
    has_binding (fn (_, value) =>
      case Lib.total listSyntax.dest_list value of
          SOME (values, _) => length values >= 2 andalso
            not (Term.aconv (hd values) (List.nth (values, 1)))
        | NONE => false) result
  end

val _ = require_msg (check_result reverse_counterexample) (fn () =>
  "the exhaustive backend did not find a non-palindromic list")
  (fn () => ()) ()

fun complete_bool_goal () =
  case exhaustive default_config ``T`` of
      NoCounterexample => true
    | _ => false

val _ = require_msg (check_result complete_bool_goal) (fn () =>
  "a decidable closed boolean goal was not exhausted completely")
  (fn () => ()) ()

fun stuck_split_counts_failure () =
  let
    val config = default_config
    val goal =
      ``(if THE (NONE : bool option) then SOME 0 else NONE) =
        SOME (x : num) ==> F``
    val result = exhaustive config goal
    val instances = qc_instances config goal
    val plans = List.map (fn i => compile_plan config (#goal i)) instances
    val compiled =
      case Refute_EvalCompute.compile config Exhaustive plans of
          Compiled test => test
        | Inapplicable reasons => raise Fail (String.concatWith "; " reasons)
    val _ = List.app (fn (card, size) =>
      ignore (#run compiled
        {genuine_only = false, card = card, size = size, draws = 0,
         ignored = []}))
      (schedule instances (#size (#qc config)))
  in
    (case result of Unknown _ => true | _ => false) andalso
    (case lookup_stat "match_failures" (!(#last_stats compiled)) of
        SOME failures => failures > 0
      | NONE => false)
  end

val _ = require_msg (check_result stuck_split_counts_failure) (fn () =>
  "a stuck Split scrutinee did not increment match_failures")
  (fn () => ()) ()

fun no_generator_is_compile_inapplicable () =
  let
    val variable = Term.mk_var ("r", ``:real``)
  in
    case Refute_EvalCompute.compile default_config Exhaustive
      [Gen (variable, Test boolSyntax.T)] of
        Inapplicable reasons =>
          List.exists (fn reason =>
            String.isSubstring "no generator for :real" reason andalso
            String.isSubstring "quotient type" reason) reasons
      | Compiled _ => false
  end

val _ = require_msg
  (check_result no_generator_is_compile_inapplicable) (fn () =>
  "NoGenerator was not converted to compile-time Inapplicable")
  (fn () => ()) ()

fun explicit_unavailable_is_unknown strategy =
  let
    val config = upd_substrate Cv default_config
    val instances = qc_instances config ``T``
  in
    case strategy_run strategy config instances of
        Unknown reasons =>
          List.exists (String.isSubstring "unavailable") reasons
      | _ => false
  end

val _ = require_msg (check_result (fn () =>
  explicit_unavailable_is_unknown Exhaustive andalso
  explicit_unavailable_is_unknown (Random {seed = 1}))) (fn () =>
  "an explicit unavailable substrate did not produce Unknown")
  (fn () => ()) ()

fun gave_up_reason_is_plumbed () =
  let
    val original = valOf (List.find (fn substrate =>
      #name substrate = "compute") (get_substrates ()))
    val last_stats = ref []
    val test : compiled_test =
      {run = fn _ => GaveUp "selftest gave up", last_stats = last_stats}
    val replacement : substrate =
      {name = "compute", priority = 30,
       compile = fn _ => fn _ => fn _ => Compiled test}
    val config = upd_substrate Compute default_config
    val instances = qc_instances config ``T``
    val _ = register_substrate replacement
    val result = strategy_run Exhaustive config instances
      handle e => (register_substrate original; raise e)
    val _ = register_substrate original
  in
    case result of
        Unknown reasons => List.exists (fn reason =>
          reason = "selftest gave up") reasons
      | _ => false
  end

val _ = require_msg (check_result gave_up_reason_is_plumbed) (fn () =>
  "a substrate GaveUp reason was not merged into Unknown")
  (fn () => ()) ()

fun smart_pruning_works () =
  let
    val base = upd_size 3 default_config
    val smart = exhaustive (upd_smart_quantifier true base)
      ``(xs : bool list) = REVERSE [T; T; T; T] ==> F``
    val naive = exhaustive (upd_smart_quantifier false base)
      ``(xs : bool list) = REVERSE [T; T; T; T] ==> F``
  in
    (case smart of Counterexample _ => true | _ => false) andalso
    (case naive of Unknown _ => true | _ => false)
  end

val _ = require_msg (check_result smart_pruning_works) (fn () =>
  "smart premise pruning did not improve the bounded exhaustive search")
  (fn () => ()) ()

fun update_witness () =
  let
    val result = exhaustive (upd_size 2 default_config)
      ``(f : refute$rf2 -> refute$rf2) rf2_1 = rf2_1 /\
        f rf2_2 = rf2_2 ==> F``
  in
    has_binding (fn (_, value) =>
      not (null (#1 (combinSyntax.strip_update value)))) result
  end

val _ = require_msg (check_result update_witness) (fn () =>
  "a function-variable counterexample was not an UPDATE-chain witness")
  (fn () => ()) ()

val _ = tprint "Refute QC random backend"

fun random config goal =
  case preprocess config (qc_problem goal) of
      NotExecutable reasons => Unknown reasons
    | Preprocessed instances =>
        strategy_run (Random {seed = strategy_seed config}) config instances

fun same_bindings [] [] = true
  | same_bindings ((variable1, value1) :: rest1)
      ((variable2, value2) :: rest2) =
      Term.aconv variable1 variable2 andalso Term.aconv value1 value2 andalso
      same_bindings rest1 rest2
  | same_bindings _ _ = false

fun same_random_outcome (Counterexample (left :: _))
      (Counterexample (right :: _)) =
      #backend left = #backend right andalso
      #substrate left = #substrate right andalso
      #certainty left = #certainty right andalso
      same_bindings (#bindings left) (#bindings right) andalso
      List.filter (fn (name, _) => name <> "msec") (#stats left) =
      List.filter (fn (name, _) => name <> "msec") (#stats right)
  | same_random_outcome NoCounterexample NoCounterexample = true
  | same_random_outcome (Unknown left) (Unknown right) = left = right
  | same_random_outcome _ _ = false

val random_config = upd_iterations 50
  (upd_size 4 (upd_seed (SOME 1) default_config))

fun random_is_registered () =
  case lookup_backend "random" of
      SOME backend => #weight backend = 30
    | NONE => false

fun random_reverse_counterexample () =
  case random random_config ``REVERSE (xs : num list) = xs`` of
      Counterexample (cex :: _) =>
        #substrate cex = "compute" andalso
        Option.isSome (lookup_stat "msec" (#stats cex))
    | _ => false

fun random_arithmetic_counterexample () =
  case random random_config ``(x : num) - y + y = x`` of
      Counterexample _ => true
    | _ => false

fun random_seed_is_reproducible () =
  let
    val goal = ``REVERSE (xs : num list) = xs``
  in
    same_random_outcome (random random_config goal) (random random_config goal)
  end

fun session_random_completes () =
  let
    val config = upd_iterations 2 (upd_size 2 default_config)
  in
    case random config ``(x : num) = x`` of
        Counterexample _ => true
      | NoCounterexample => true
      | Unknown _ => true
  end

fun list_draws_respect_floors () =
  let
    val rng = Random.newgenseed 1.0
    fun draw 0 = true
      | draw remaining =
          let val _ = random_term ``:num list`` 0 rng
          in draw (remaining - 1) end
  in
    draw 100
  end

val _ = require_msg (check_result random_reverse_counterexample) (fn () =>
  "the random backend did not refute REVERSE xs = xs") (fn () => ()) ()

val _ = require_msg (check_result random_is_registered) (fn () =>
  "the random backend was not registered with weight 30") (fn () => ()) ()

val _ = require_msg (check_result random_arithmetic_counterexample) (fn () =>
  "the random backend did not refute x - y + y = x") (fn () => ()) ()

val _ = require_msg (check_result random_seed_is_reproducible) (fn () =>
  "the random backend was not reproducible for an explicit seed")
  (fn () => ()) ()

val _ = require_msg (check_result session_random_completes) (fn () =>
  "the session random generator did not complete a run") (fn () => ()) ()

val _ = require_msg (check_result list_draws_respect_floors) (fn () =>
  "small-budget recursive list draws raised an exception") (fn () => ()) ()

(* The public corpus precedes the potential-path tests below.  Those tests
   replace the ordinary list generator with tiny adversarial generators. *)
val selftest_level =
  case OS.Process.getEnv "HOLSELFTESTLEVEL" of
      NONE => 1
    | SOME text =>
        (case Int.fromString text of
            NONE => 1
          | SOME level => level)

val corpus_config =
  upd_timeout 5.0
    (upd_seed (SOME 1)
      (upd_sequential true
        (upd_backends (SOME ["exhaustive"]) default_config)))

fun cex_is_certified (Refute.Counterexample ({cert = SOME _, ...} :: _)) = true
  | cex_is_certified _ = false

fun cex_is_genuine_certified
      (Refute.Counterexample
        ({certainty = Refute.Genuine, cert = SOME _, ...} :: _)) = true
  | cex_is_genuine_certified _ = false

fun public_expect ExpectCex = Refute.ExpectCex
  | public_expect ExpectNone = Refute.ExpectNone
  | public_expect ExpectUnknown = Refute.ExpectUnknown
  | public_expect NoExpectation = Refute.NoExpectation

fun tc {name, cfg, tm, expect} =
  let
    val _ = tprint name
    val config = Refute.upd_expect (public_expect expect) cfg
    val result = Refute.refute config tm
    val _ =
      case expect of
          ExpectCex =>
            if cex_is_certified result then ()
            else raise Fail "expected a certified counterexample"
        | _ => ()
  in
    OK ()
  end
  handle e => die (Feedback.exn_to_string e)

fun is_unknown_with needle (Refute.Unknown reasons) =
      List.exists (String.isSubstring needle) reasons
  | is_unknown_with _ _ = false

fun check_corpus name predicate =
  let val _ = tprint name
  in if predicate () then OK () else die "corpus check failed" end
  handle e => die (Feedback.exn_to_string e)

fun same_corpus_outcome (Refute.Counterexample _, Refute.Counterexample _) =
      true
  | same_corpus_outcome (Refute.NoCounterexample, Refute.NoCounterexample) =
      true
  | same_corpus_outcome (Refute.Unknown left, Refute.Unknown right) =
      left = right
  | same_corpus_outcome _ = false

fun corpus_smoke () =
  (tc {name = "Refute corpus: classic reverse",
       cfg = corpus_config,
       tm = ``REVERSE (xs : num list) = xs``,
       expect = ExpectCex};
   tc {name = "Refute corpus: arithmetic",
       cfg = corpus_config,
       tm = ``(x : num) - y + y = x``,
       expect = ExpectCex};
   tc {name = "Refute corpus: sound reverse",
       cfg = corpus_config,
       tm = ``REVERSE (REVERSE [T; F; T]) = [T; F; T]``,
       expect = ExpectNone})

fun corpus_classics () =
  (tc {name = "Refute corpus: reverse append mutation",
       cfg = corpus_config,
       tm = ``REVERSE (xs : num list ++ ys) = REVERSE xs ++ REVERSE ys``,
       expect = ExpectCex};
   tc {name = "Refute corpus: ALL_DISTINCT append mutation",
       cfg = corpus_config,
       tm = ``ALL_DISTINCT (xs : num list ++ ys) <=>
             ALL_DISTINCT xs /\ ALL_DISTINCT ys``,
       expect = ExpectCex};
   tc {name = "Refute corpus: nub append mutation",
       cfg = corpus_config,
       tm = ``nub (xs : num list ++ ys) = nub xs ++ nub ys``,
       expect = ExpectCex};
   tc {name = "Refute corpus: integer order mutation",
       cfg = corpus_config,
       tm = ``~((x : int) = x)``,
       expect = ExpectCex})

fun corpus_smart_quantifiers () =
  let
    val ordered_insert =
      ``SORTED $= (xs : num list) ==> SORTED $= (x :: xs)``
    val lookup =
      ``(m1 : num -> num option) k = SOME (v : num) ==>
        m1 k = NONE``
    val let_case =
      ``let z = (xs : num option) in
          case z of NONE => F | SOME x => x = x``
  in
    tc {name = "Refute corpus: sorted insert mutation",
        cfg = corpus_config, tm = ordered_insert, expect = ExpectCex};
    tc {name = "Refute corpus: fmap lookup premise",
        cfg = corpus_config, tm = lookup, expect = ExpectCex};
    check_corpus "Refute corpus: let/case plan" (fn () =>
      case compile_plan corpus_config let_case of
          Gen (_, Test _) => true
        | _ => false)
  end

fun corpus_default_quickcheck () =
  let
    fun check name tm =
      check_corpus ("Refute default quickcheck: " ^ name) (fn () =>
        cex_is_genuine_certified (Refute.quickcheck tm))
  in
    check "classic reverse" ``REVERSE (xs : num list) = xs``;
    check "reverse append mutation"
      ``REVERSE (xs : num list ++ ys) = REVERSE xs ++ REVERSE ys``;
    check "ALL_DISTINCT append mutation"
      ``ALL_DISTINCT (xs : num list ++ ys) <=>
        ALL_DISTINCT xs /\ ALL_DISTINCT ys``;
    check "nub append mutation"
      ``nub (xs : num list ++ ys) = nub xs ++ nub ys``;
    check "integer order mutation" ``~((x : int) = x)``;
    check "sorted insert mutation"
      ``SORTED $= (xs : num list) ==> SORTED $= (x :: xs)``;
    check "fmap lookup premise"
      ``(m1 : num -> num option) k = SOME (v : num) ==>
        m1 k = NONE``
  end

fun corpus_potential () =
  let
    val hd_goal =
      ``HD (xs : num list) = if xs = [] then HD ys else HD xs``
    val hd_map = ``~(HD (MAP (f : num -> num) xs) = f (HD xs))``
    val short_lists : custom_gen =
      { enumerate = SOME (fn _ => [``[] : num list``, ``[0] : num list``]),
        random = NONE }
    val _ = register_generator ``:num list`` short_lists
    val abort_config = upd_abort_potential true corpus_config
    val genuine_config = upd_genuine_only true corpus_config
    fun potential result =
      case result of
          Refute_Core.Counterexample
            ({certainty = Refute_Core.Potential _, cert = NONE, ...} :: _) =>
              true
        | _ => false
  in
    check_corpus "Refute corpus: HD potential only" (fn () =>
      potential (exhaustive abort_config hd_goal));
    check_corpus "Refute corpus: abort potential" (fn () =>
      potential (exhaustive abort_config hd_goal));
    check_corpus "Refute corpus: genuine only" (fn () =>
      case exhaustive genuine_config hd_goal of
          Refute_Core.Counterexample _ => false
        | _ => true);
    tc {name = "Refute corpus: HD/MAP certification upgrade",
        cfg = corpus_config, tm = hd_map, expect = ExpectCex}
  end

fun corpus_polymorphism () =
  (tc {name = "Refute corpus: polymorphic lists",
       cfg = corpus_config,
       tm = ``(xs : 'a list) = ys``,
       expect = ExpectCex};
   tc {name = "Refute corpus: polymorphic card schedule",
       cfg = corpus_config,
       tm = ``(x : 'a) = y``,
       expect = ExpectCex};
   tc {name = "Refute corpus: num fallback",
       cfg = upd_finite_types false corpus_config,
       tm = ``(x : 'a) = y``,
       expect = ExpectCex})

fun corpus_functions () =
  let
    val map_goal =
      ``MAP (f : num -> num) xs = MAP (g : num -> num) xs ==> f = g``
    val goal =
      ``(f : refute$rf2 -> refute$rf2) rf2_1 = rf2_1 /\
        f rf2_2 = rf2_2 ==> F``
  in
    check_corpus "Refute corpus: MAP function plan" (fn () =>
      let val _ = compile_plan corpus_config map_goal in true end);
    tc {name = "Refute corpus: function UPDATE counterexample",
        cfg = corpus_config, tm = goal, expect = ExpectCex};
    check_corpus "Refute corpus: function UPDATE witness" (fn () =>
      case Refute.refute corpus_config goal of
          Refute.Counterexample ({bindings, ...} :: _) =>
            List.exists (fn (_, value) =>
              not (null (#1 (combinSyntax.strip_update value)))) bindings
        | _ => false)
  end

fun corpus_quantifiers () =
  let
    val finite =
      ``(p : bool) /\ (!x : bool. x) /\
        (?y : refute$rf2. y = y)``
    val infinite = ``(!n : num. n <= n)``
  in
    check_corpus "Refute corpus: finite quantifier expansion" (fn () =>
      case preprocess corpus_config (preprocessing_problem finite) of
          Preprocessed [instance] => has_conjunction (#goal instance)
        | _ => false);
    tc {name = "Refute corpus: finite check counterexample",
        cfg = corpus_config, tm = ``(b : bool)``, expect = ExpectCex};
    tc {name = "Refute corpus: num quantifier unknown",
        cfg = corpus_config, tm = infinite, expect = ExpectUnknown}
  end

fun corpus_hol4_specific () =
  let
    val record_goal = ``(r : rg_record) = s``
    val word_goal =
      ``w2n ((a : bool[8]) + b) = w2n a + w2n b``
    val quotient_goal = ``(x : real) = y``
  in
    tc {name = "Refute corpus: record type",
        cfg = corpus_config, tm = record_goal, expect = ExpectCex};
    tc {name = "Refute corpus: word addition",
        cfg = corpus_config, tm = word_goal, expect = ExpectCex};
    tc {name = "Refute corpus: quotient unknown",
        cfg = corpus_config, tm = quotient_goal, expect = ExpectUnknown};
    check_corpus "Refute corpus: quotient explanation" (fn () =>
      is_unknown_with "quotient" (Refute.refute corpus_config quotient_goal))
  end

(* Numeral/string/char literals in a goal must not be mistaken for
   non-executable constants (their internal NUMERAL/BIT1/STRING/CHR
   tags reduce natively under EVAL), so goals mentioning them stay
   testable and their counterexamples are found and certified. *)
fun corpus_literals () =
  (tc {name = "Refute corpus: numeral literal counterexample",
       cfg = corpus_config, tm = ``!n : num. n <> 2``, expect = ExpectCex};
   tc {name = "Refute corpus: character literal counterexample",
       cfg = corpus_config, tm = ``!c : char. c <> #"a"``,
       expect = ExpectCex};
   tc {name = "Refute corpus: string literal counterexample",
       cfg = corpus_config, tm = ``!s : string. s <> "x"``,
       expect = ExpectCex})

fun corpus_soundness () =
  (tc {name = "Refute corpus: sound reverse involution",
       cfg = corpus_config,
       tm = ``REVERSE (REVERSE [T; F; T]) = [T; F; T]``,
       expect = ExpectNone};
   tc {name = "Refute corpus: sound addition commutes",
       cfg = corpus_config,
       tm = ``T``,
       expect = ExpectNone};
   tc {name = "Refute corpus: sound bool check_all",
       cfg = corpus_config,
       tm = ``(b : bool) \/ ~b``,
       expect = ExpectNone};
   tc {name = "Refute corpus: sound rf check_all",
       cfg = corpus_config,
       tm = ``(x : refute$rf2) = rf2_1 \/ x = rf2_2``,
       expect = ExpectNone})

fun corpus_registries () =
  let
    val _ = Datatype.Datatype `rg_sorted = RGSorted (num list)`
    val sorted_ty = ``:rg_sorted``
    val sorted_constructor = ``RGSorted``
    val sorted_predicate =
      ``\s : rg_sorted. case s of RGSorted xs => SORTED $<= xs``
    val _ = abstract_generator
      {ty = sorted_ty,
       constructors = [sorted_constructor],
       pred = SOME sorted_predicate}
    val _ = Datatype.Datatype `rg_custom = RGC0 | RGC1`
    val custom_ty = ``:rg_custom``
    val custom : custom_gen =
      {enumerate = SOME (fn _ => [``RGC0``, ``RGC1``]), random = NONE}
    val _ = register_generator custom_ty custom
  in
    check_corpus "Refute corpus: sorted abstract generator" (fn () =>
      case (spec_of sorted_ty, predicate_of sorted_ty) of
          (GenDatatype _, SOME predicate) =>
            Term.aconv predicate sorted_predicate
        | _ => false);
    check_corpus "Refute corpus: registered custom generator" (fn () =>
      case spec_of custom_ty of GenCustom _ => true | _ => false);
    tc {name = "Refute corpus: custom generator counterexample",
        cfg = corpus_config,
        tm = ``(x : rg_custom) = RGC0``,
        expect = ExpectCex}
  end

fun corpus_parlist () =
  let
    val parallel_config =
      upd_backends (SOME ["exhaustive", "random"])
        (upd_sequential false corpus_config)
    val sequential_config =
      upd_backends (SOME ["exhaustive", "random"]) corpus_config
    val cex_goal = ``(x : num) - y + y = x``
    val sound_goal = ``(!b : bool. b \/ ~b)``
    fun same goal =
      same_corpus_outcome
        (Refute.refute sequential_config goal,
         Refute.refute parallel_config goal)
  in
    check_corpus "Refute corpus: ParList get_first" (fn () =>
      ParList.get_first (fn n => if n = 2 then SOME n else NONE) [1, 2, 3]
        = SOME 2);
    check_corpus "Refute corpus: ParList get_some" (fn () =>
      case ParList.get_some (fn n =>
        if n = 2 orelse n = 3 then SOME n else NONE) [1, 2, 3] of
          SOME 2 => true
        | SOME 3 => true
        | _ => false);
    check_corpus "Refute corpus: parallel counterexample outcome" (fn () =>
      same cex_goal);
    check_corpus "Refute corpus: parallel sound outcome" (fn () =>
      same sound_goal)
  end

val _ =
  if selftest_level >= 2 then
    (corpus_smoke ();
     corpus_classics ();
     corpus_smart_quantifiers ();
     corpus_default_quickcheck ();
     corpus_polymorphism ();
     corpus_functions ();
     corpus_quantifiers ();
     corpus_hol4_specific ();
     corpus_literals ();
     corpus_soundness ();
     corpus_registries ();
     corpus_parlist ())
  else
    corpus_smoke ()

val _ = tprint "Refute certification and potential retry"

fun certified_reverse () =
  case exhaustive (upd_size 3 default_config)
    ``REVERSE (xs : num list) = xs`` of
      Counterexample ({certainty = Genuine, cert = SOME theorem, ...} :: _) =>
        Term.aconv (Thm.concl theorem)
          ``~(!xs : num list. REVERSE xs = xs)`` andalso
        null (Tag.axioms_of (Thm.tag theorem))
    | _ => false

val _ = require_msg (check_result certified_reverse) (fn () =>
  "REVERSE xs = xs was not certified with a tag-clean theorem")
  (fn () => ()) ()

fun make_cex genuine : counterexample =
  { backend = "selftest",
    substrate = "compute",
    certainty = Refute_Core.Potential [],
    bindings = [],
    evals = [],
    cert = NONE,
    scope = NONE,
    stats = [("tests", 1)] }

fun upgrade_from_stuck_path () =
  case Refute_Cert.certify
    { original = ``F``,
      evals = [],
      env = [],
      cex = make_cex false } of
      Certified {certainty = Genuine, cert = SOME theorem, ...} =>
        Term.aconv (Thm.concl theorem) ``~F``
    | _ => false

val _ = require_msg (check_result upgrade_from_stuck_path) (fn () =>
  "certification did not upgrade a tainted candidate to Genuine")
  (fn () => ()) ()

fun false_positive_is_discarded () =
  case Refute_Cert.certify
    { original = ``T``,
      evals = [],
      env = [],
      cex = make_cex true } of
      Discarded => true
    | _ => false

val _ = require_msg (check_result false_positive_is_discarded) (fn () =>
  "certification did not discard an EVAL-true candidate") (fn () => ()) ()

val stuck_list_gen : custom_gen =
  { enumerate = SOME (fn _ => [``[] : num list``]), random = NONE }

val _ = register_generator ``:num list`` stuck_list_gen

val stuck_goal = ``HD (xs : num list) = 0``

fun potential_only config = exhaustive config stuck_goal

fun default_retries_potential () =
  case potential_only (upd_size 1 default_config) of
      Counterexample _ => false
    | Unknown _ => true
    | NoCounterexample => true

fun abort_returns_potential () =
  case potential_only (upd_abort_potential true
    (upd_size 1 default_config)) of
      Counterexample
        ({certainty = Refute_Core.Potential _, cert = NONE, ...} :: _) => true
    | _ => false

fun genuine_only_hides_potential () =
  case potential_only (upd_genuine_only true
    (upd_size 1 default_config)) of
      Counterexample _ => false
    | Unknown _ => true
    | NoCounterexample => true

val _ = require_msg (check_result default_retries_potential) (fn () =>
  "the default flow returned a potential instead of retrying genuinely")
  (fn () => ()) ()

val _ = require_msg (check_result abort_returns_potential) (fn () =>
  "abort_potential did not return the potential counterexample")
  (fn () => ()) ()

val _ = require_msg (check_result genuine_only_hides_potential) (fn () =>
  "genuine_only surfaced a potential counterexample") (fn () => ()) ()

val hd_map_lists : custom_gen =
  { enumerate = SOME (fn _ => [``[] : num list``, ``[0] : num list``]),
    random = NONE }

val _ = register_generator ``:num list`` hd_map_lists

fun hd_map_stuck_path_upgrades () =
  case exhaustive (upd_size 1 default_config)
    ``~(HD (MAP (f : num -> num) xs) = f (HD xs))`` of
      Counterexample ({certainty = Genuine, cert = SOME _, ...} :: _) => true
    | _ => false

val _ = require_msg (check_result hd_map_stuck_path_upgrades) (fn () =>
  "the HD/MAP stuck path was not upgraded to a genuine counterexample")
  (fn () => ()) ()

val _ = tprint "Refute public facade"

fun facade_reverse () =
  case Refute.quickcheck ``(x : num) - y + y = x`` of
      Refute.Counterexample _ => true
    | _ => false

fun facade_expectation () =
  ((ignore (Refute.refute
      (Refute.upd_expect Refute.ExpectNone
        (Refute.upd_backends (SOME ["exhaustive"]) default_config))
      ``(x : num) - y + y = x``); false)
   handle _ => true)

fun facade_parallel () =
  case Refute.refute
    (Refute.upd_sequential false
      (Refute.upd_backends (SOME ["exhaustive"]) default_config))
    ``(x : num) - y + y = x`` of
      Refute.Counterexample _ => true
    | _ => false

fun facade_tactic_fails () =
  ((ignore (Refute.REFUTE_TAC
      ([], ``(x : num) - y + y = x``)); false)
   handle _ => true)

fun facade_tactic_allows_unknown () =
  ((ignore (Refute.REFUTE_TAC ([], ``(x : ind) = x``)); true)
   handle _ => false)

fun facade_assumptions () =
  case (Refute.refute_goal
    (Refute.upd_backends (SOME ["exhaustive"]) default_config)
    ([``b : bool``], ``b : bool``),
    Refute.refute_goal
      (Refute.upd_no_assms true
        (Refute.upd_backends (SOME ["exhaustive"]) default_config))
      ([``b : bool``], ``b : bool``)) of
      (Refute.NoCounterexample, Refute.Counterexample _) => true
    | _ => false

val _ = require_msg (check_result facade_reverse) (fn () =>
  "the public quickcheck facade did not find a counterexample")
  (fn () => ()) ()
val _ = require_msg (check_result facade_expectation) (fn () =>
  "the public expect check did not raise on a mismatch") (fn () => ()) ()
val _ = require_msg (check_result facade_parallel) (fn () =>
  "the public parallel facade did not find a counterexample")
  (fn () => ()) ()
val _ = require_msg (check_result facade_tactic_fails) (fn () =>
  "REFUTE_TAC did not fail on a refutable goal") (fn () => ()) ()
val _ = require_msg (check_result facade_tactic_allows_unknown) (fn () =>
  "REFUTE_TAC blocked on an inconclusive goal") (fn () => ()) ()
val _ = require_msg (check_result facade_assumptions) (fn () =>
  "refute_goal did not handle assumptions or no_assms") (fn () => ()) ()

val _ = if selftest_level >= 2 then corpus_potential () else ()

val _ = exit_count0 erc
