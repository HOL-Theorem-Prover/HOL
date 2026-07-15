open testutils
open refuteTheory
open Refute_Core
open Refute_Gen
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

fun qc_problem goal : problem = {goal = goal, assumptions = [], evals = []}

fun exhaustive config goal =
  exhaustive_run config (qc_problem goal)

fun has_binding predicate (Counterexample (cex :: _)) =
      List.exists predicate (#bindings cex)
  | has_binding _ _ = false

fun reverse_counterexample () =
  let
    val config = upd_size 3 (upd_max_counterexamples 1 default_config)
    val result = exhaustive config ``REVERSE (xs : num list) = xs``
  in
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
    val result = exhaustive default_config
      ``(if THE (NONE : bool option) then SOME 0 else NONE) =
        SOME (x : num) ==> F``
  in
    (case result of Unknown _ => true | _ => false) andalso
    (case lookup_stat "match_failures" (!last_stats) of
        SOME failures => failures > 0
      | NONE => false)
  end

val _ = require_msg (check_result stuck_split_counts_failure) (fn () =>
  "a stuck Split scrutinee did not increment match_failures")
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

fun random config goal = random_run config (qc_problem goal)

fun same_bindings [] [] = true
  | same_bindings ((variable1, value1) :: rest1)
      ((variable2, value2) :: rest2) =
      Term.aconv variable1 variable2 andalso Term.aconv value1 value2 andalso
      same_bindings rest1 rest2
  | same_bindings _ _ = false

fun same_random_outcome (Counterexample (left :: _))
      (Counterexample (right :: _)) =
      #backend left = #backend right andalso #certainty left = #certainty right
      andalso same_bindings (#bindings left) (#bindings right)
      andalso #stats left = #stats right
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
      Counterexample _ => true
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

val _ = exit_count0 erc
