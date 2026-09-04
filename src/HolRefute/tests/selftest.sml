(* HolRefute selftest: user-visible behaviour through the public Refute
   API only.  Level 1 (default) runs in a few minutes; HOLSELFTESTLEVEL=2
   adds the substrate matrix and the model-finder acceptance corpus. *)

open testutils
open refuteTheory refuteTableZooTheory refuteUnusedTheory
open Refute

(* Three deliberate reaches outside the [Refute] signature.  One is a
   registry entry point with no user outside these tests: the composed
   display callback a registration installs, aliased here.  The second is
   [Refute_QC.strategy_run], called by "an expired deadline never claims
   NoCounterexample" because every public route to that verdict is decided
   by the same budget it is testing.  The third is [Refute_EvalEnum]'s
   theory bracket, called by "a theory bracket leaves the global message
   flags alone": the defect it pins is a process-global flag held flipped
   while a sibling backend of the same call runs, and the only public
   observer would be a second backend racing the first. *)
val lookup_term_postprocessor =
  Refute_ModelFinder_Model.lookup_term_postprocessor

local
  open sortingTheory realTheory ratTheory lbtreeTheory pathTheory
       llistTheory finite_mapTheory finite_setTheory refuteHarvestTypeTheory
       refuteHarvestAbsTheory wordsLib stringLib
in end

val _ = Thm.setCT "scratch"
val _ = numLib.prefer_num ()
val _ = Feedback.set_trace "Refute" 0

val erc = ref 0
val _ = diemode := Remember erc

val selftest_level =
  case OS.Process.getEnv "HOLSELFTESTLEVEL" of
      NONE => 1
    | SOME text => (case Int.fromString text of NONE => 1 | SOME n => n)

(* ------------------------------------------------------------------- *)
(* Harness                                                             *)
(* ------------------------------------------------------------------- *)

fun check_result P =
  testutils.check_result (fn r =>
    P r handle Interrupt => raise Interrupt
             | e => (print ("\n  raised: " ^ General.exnMessage e ^ "\n");
                     false))

fun test name pred =
  (tprint name;
   require_msg (check_result pred) (fn () => name ^ " failed")
     (fn () => ()) ())

fun section name = print ("\n== " ^ name ^ "\n")
fun skip name why = (tprint name; print ("skipped: " ^ why ^ "\n"))
(* Level-2 rows are silent at level 1; each level-2 section announces
   itself as skipped once. *)
fun level2_section name =
  (section name;
   if selftest_level < 2 then print "skipped: level 2 only\n" else ())

(* [raises_holerr name f (structure, function, message)]: NONE entries are
   not checked. *)
fun raises_holerr name f (str, fnm, msg) =
  test name (fn () =>
    (ignore (f ()); false)
    handle Feedback.HOL_ERR e =>
      (case str of NONE => true | SOME s => Feedback.top_structure_of e = s)
      andalso
      (case fnm of NONE => true | SOME s => Feedback.top_function_of e = s)
      andalso
      (case msg of NONE => true | SOME s => Feedback.message_of e = s))

fun capture level action =
  let
    val chunks = ref ([] : string list)
    fun output text = chunks := text :: !chunks
    val result = Lib.with_flag (Feedback.MESG_outstream, output)
      (Lib.with_flag (Feedback.WARNING_outstream, output)
        (Feedback.with_traces [("Refute", level)] action)) ()
  in
    (result, String.concat (rev (!chunks)))
  end

(* ------------------------------------------------------------------- *)
(* Outcome predicates                                                  *)
(* ------------------------------------------------------------------- *)

(* [outcome] carries terms and theorems, so it is not an equality type;
   [==] compares outcomes structurally. *)
fun outcome_eq (a : outcome) (b : outcome) =
  case (a, b) of
      (NoCounterexample, NoCounterexample) => true
    | (NoModel, NoModel) => true
    | (Unknown r1, Unknown r2) => r1 = r2
    | (Counterexample c1, Counterexample c2) =>
        ListPair.allEq (fn (x : counterexample, y : counterexample) =>
          ListPair.allEq (fn ((v, t), (w, u)) =>
                            Term.aconv v w andalso Term.aconv t u)
            (#bindings x, #bindings y)) (c1, c2)
    | (Model m1, Model m2) => length m1 = length m2
    | _ => false
infix 4 == =/=
fun a == b = outcome_eq a b
fun a =/= b = not (outcome_eq a b)

fun uncertified (cex : counterexample) = not (Option.isSome (#cert cex))

fun is_cex (Counterexample _) = true | is_cex _ = false
fun is_unknown (Unknown _) = true | is_unknown _ = false
fun not_refuted outcome = not (is_cex outcome)

fun first_cex (Counterexample (c :: _)) = SOME (c : counterexample)
  | first_cex _ = NONE

fun is_genuine (cex : counterexample) = #certainty cex = Genuine
fun is_potential (cex : counterexample) =
  case #certainty cex of Potential _ => true | _ => false
fun is_quasi (cex : counterexample) =
  case #certainty cex of QuasiGenuine _ => true | _ => false

fun cex_where P outcome =
  case first_cex outcome of SOME c => P c | NONE => false

fun single_cex_where P (Counterexample [c : counterexample]) = P c
  | single_cex_where _ _ = false

val genuine = cex_where is_genuine
val genuine_certified = cex_where (fn c => is_genuine c andalso
                                            Option.isSome (#cert c))
val genuine_uncertified = cex_where (fn c => is_genuine c andalso
                                              not (Option.isSome (#cert c)))
val potential = cex_where is_potential

fun reasons_of (Unknown rs) = rs | reasons_of _ = []
fun unknown_with needle outcome =
  is_unknown outcome andalso
  List.exists (String.isSubstring needle) (reasons_of outcome)
fun bounds_clean outcome =
  unknown_with "no counterexample within the tested scopes" outcome

fun binding (cex : counterexample) var =
  Option.map #2 (List.find (fn (v, _) => Term.aconv v var) (#bindings cex))

fun binding_is cex var value =
  case binding cex var of SOME v => Term.aconv v value | NONE => false

fun tag_clean thm = Tag.isEmpty (Thm.tag thm) orelse Tag.isDisk (Thm.tag thm)

(* The certificate of a genuine counterexample is the negated universal
   closure of the goal (leading universals of the goal included), proved
   without oracles. *)
fun certifies goal (cex : counterexample) =
  case #cert cex of
      NONE => false
    | SOME thm =>
        let
          val (gvars, gbody) = boolSyntax.strip_forall goal
          val (vars, body) =
            boolSyntax.strip_forall (boolSyntax.dest_neg (Thm.concl thm))
          fun set vs = HOLset.addList (Term.empty_tmset, vs)
        in
          null (Thm.hyp thm) andalso tag_clean thm andalso
          Term.aconv body gbody andalso
          HOLset.equal (set vars, set (Term.free_vars goal @ gvars))
        end handle HOL_ERR _ => false

fun scope_of (cex : counterexample) ty =
  case #scope cex of
      SOME rows =>
        Option.map #2 (List.find (fn (t, _) => Type.compare (t, ty) = EQUAL)
                                 rows)
    | NONE => NONE

fun footprint () =
  (Theory.current_theory (), map #1 (Theory.types "-"),
   map (#1 o Term.dest_const) (Theory.constants "-"),
   map (fn ((_, name), _) => name) (DB.thy "-"))

(* ------------------------------------------------------------------- *)
(* Configurations                                                      *)
(* ------------------------------------------------------------------- *)

val quiet = upd_quiet true
fun only bs = upd_search (Only bs)
val exhaustive = default_config |> only [Exhaustive] |> quiet
val random = default_config |> only [Random] |> quiet
val narrowing = default_config |> only [Narrowing] |> quiet
val qc = default_config |> upd_search QuickcheckBackends |> quiet
val mf = default_config |> only [ModelFinder] |> quiet
  |> upd_sequential true |> upd_max_threads 1 |> upd_timeout 120.0
  |> upd_batch_size 8 |> upd_card [(NONE, [1, 2, 3, 4, 5, 6])]
(* Default scope (cards 1..10): needed by whole-space claims over
   [bool |-> bool] and by witnesses longer than six elements. *)
val mf_wide = default_config |> only [ModelFinder] |> quiet
  |> upd_sequential true |> upd_timeout 120.0

fun with_compset thms body =
  let
    val saved = computeLib.the_compset ()
  in
    computeLib.put_compset (computeLib.add_thms thms saved);
    Portable.finally (fn () => computeLib.put_compset saved) body ()
  end

fun with_global_thread_count count body =
  let
    val saved = Multithreading.max_threads ()
  in
    Portable.finally (fn () => Multithreading.max_threads_update saved)
      (fn () => (Multithreading.max_threads_update count; body ())) ()
  end

(* The model finder is only exercised when kodkodi is installed. *)
val kodkodi_configured =
  refute (mf |> upd_timeout 30.0 |> upd_card [(NONE, [1])]) ``F``
  =/= Unknown ["no configured backend"]

fun mf_test name pred =
  if kodkodi_configured then test name pred
  else skip name "kodkodi not configured"

(* Registered stub backends: their [configured] flag is cleared after the
   test that uses them so they never join a later search. *)
fun stub_cex backend certainty : counterexample =
  {backend = backend, substrate = "stub", certainty = certainty,
   bindings = [], evals = [], cert = NONE, scope = NONE, model = NONE,
   stats = []}

fun stub name weight enabled run : backend =
  {name = name, weight = weight, configured = fn () => !enabled,
   requires = AnyGoal, input = MonoInstances,
   certainty_ceiling = fn _ => fn _ => Genuine, run = run}

(* The ceiling a backend races under is a field, so a stub overrides just
   that one and keeps the rest. *)
fun with_ceiling ceiling (b : backend) : backend =
  {name = #name b, weight = #weight b, configured = #configured b,
   requires = #requires b, input = #input b,
   certainty_ceiling = ceiling, run = #run b}

fun with_enabled flags body =
  (app (fn f => f := true) flags;
   Portable.finally (fn () => app (fn f => f := false) flags) body ())

(* ------------------------------------------------------------------- *)
(* Theories                                                            *)
(* ------------------------------------------------------------------- *)

val _ = section "theory ancestry"

val same_string_set : string list -> string list -> bool = Lib.set_eq

(* Ancestry is user-visible: a descendant theory inherits it.  [sorting] is
   declared but is not a computed parent -- [finite_map] already ancestors
   it, so HOL4's minimal-parent computation folds it in there.  [listRange]
   is one because the offset-interval rewrites are stated over
   [listRangeLHI]/[listRangeINC]. *)
fun refute_ancestry_is_exact () =
  same_string_set (Theory.parents "refute")
    ["real", "words", "rat", "finite_map", "listRange"]

val _ = tprint "refuteTheory has exactly its declared parents"
val _ = require_msg (check_result refute_ancestry_is_exact) (fn () =>
  "refute parents: " ^ String.concatWith ", " (Theory.parents "refute"))
  (fn () => ()) ()

(* ------------------------------------------------------------------- *)
(* Facade and tactics                                                  *)
(* ------------------------------------------------------------------- *)

val _ = section "facade"

val arith = ``(x : num) - y + y = x``

val _ = test "quickcheck refutes arithmetic" (fn () =>
  is_cex (quickcheck arith))

val _ = test "refute_with applies updates" (fn () =>
  is_cex (refute_with [only [Random], quiet] arith))

val _ = raises_holerr "unmet expectation raises from Refute.expect"
  (fn () => refute (exhaustive |> upd_expect ExpectNone) arith)
  (SOME "Refute", SOME "expect", NONE)

val _ = test "expectation met is silent" (fn () =>
  is_cex (refute (exhaustive |> upd_expect ExpectCex) arith) andalso
  refute (exhaustive |> upd_expect ExpectNone) ``T`` == NoCounterexample)

val _ = test "parallel search refutes" (fn () =>
  is_cex (refute (exhaustive |> upd_sequential false) arith))

val _ = test "refute_goal honours assumptions; no_assms drops them"
  (fn () =>
    let val g = ([``b : bool``], ``b : bool``) in
      refute_goal exhaustive g == NoCounterexample andalso
      is_cex (refute_goal (exhaustive |> upd_no_assms true) g)
    end)

fun same_goal ((asl1, c1), (asl2, c2)) =
  Term.aconv c1 c2 andalso ListPair.allEq (Lib.uncurry Term.aconv) (asl1, asl2)

fun tactic_keeps tac g =
  case tac g of ([g'], _) => same_goal (g, g') | _ => false

val _ = test "REFUTE_TAC leaves a refutable goal unchanged" (fn () =>
  tactic_keeps REFUTE_TAC ([``0 < (x : num)``], arith))

val _ = test "REFUTE_TAC leaves an inconclusive goal unchanged" (fn () =>
  tactic_keeps REFUTE_TAC ([], ``(x : ind) = x``))

val _ = test "preset tactics leave the goal unchanged" (fn () =>
  tactic_keeps QUICKCHECK_TAC ([], ``T``) andalso
  tactic_keeps NARROWING_TAC ([], ``T``) andalso
  tactic_keeps MODEL_REFUTE_TAC ([``T``], ``F``) andalso
  tactic_keeps (REFUTE_TAC_WITH [only [Random], upd_size 2])
    ([], arith))

val _ = test "REFUTE_TAC reads the_config at application time" (fn () =>
  let
    val raised = ref false
    fun body () =
      (ignore (REFUTE_TAC ([], arith)); false)
      handle Feedback.HOL_ERR e => Feedback.top_function_of e = "expect"
  in
    Lib.with_flag (the_config, exhaustive |> upd_expect ExpectNone) body ()
  end)

val _ = raises_holerr "REFUTE_CONFIG_TAC honours the given expectation"
  (fn () => REFUTE_CONFIG_TAC (exhaustive |> upd_expect ExpectUnknown)
              ([``T``], ``F``))
  (SOME "Refute", SOME "expect", NONE)

val _ = test "current_config applies updates left to right" (fn () =>
  let
    val cfg = current_config [only [Exhaustive], upd_size 2, upd_size 7,
                              upd_quiet true]
  in
    #size (#qc cfg) = 7 andalso #quiet cfg andalso
    #backends cfg = SOME ["exhaustive"]
  end)

val _ = raises_holerr "empty backend selection is rejected"
  (fn () => upd_search (Only []) default_config)
  (SOME "Refute", SOME "upd_search", NONE)

(* A zero-instance configuration was admitted and then reported as a bare
   Unknown ["search space not exhausted"], never saying nothing was searched. *)
val _ = raises_holerr "an empty default_type is rejected"
  (fn () => default_config |> upd_finite_types false |> upd_default_type [])
  (SOME "Refute_Core", SOME "validate_qc_config",
   SOME "default_type: must be nonempty")

val _ = test "unknown reasons carry the backend name" (fn () =>
  let
    val enabled = ref false
    val _ = register_backend
      (stub "selftest-reason" ~100 enabled (fn _ => fn _ => Unknown ["pin"]))
  in
    with_enabled [enabled] (fn () =>
      refute (default_config |> only [RegisteredBackend "selftest-reason"]
                |> quiet) ``T``)
    == Unknown ["selftest-reason: pin"]
  end)

val _ = test "re-registering a backend name replaces it" (fn () =>
  let
    val enabled = ref false
    fun answer s = stub "selftest-replace" ~100 enabled
                     (fn _ => fn _ => Unknown [s])
    val _ = register_backend (answer "first")
    val _ = register_backend (answer "second")
  in
    with_enabled [enabled] (fn () =>
      refute (default_config |> only [RegisteredBackend "selftest-replace"]
                |> quiet) ``T``)
    == Unknown ["selftest-replace: second"]
  end)

val _ = test "preset tactics never run a registered backend" (fn () =>
  let
    val enabled = ref false
    val runs = ref 0
    val _ = register_backend (stub "selftest-probe" ~100 enabled
      (fn _ => fn _ => (runs := !runs + 1; Unknown [])))
    fun count tac = (runs := 0; ignore (tac ([], ``T``)); !runs)
  in
    with_enabled [enabled] (fn () =>
      count QUICKCHECK_TAC = 0 andalso count NARROWING_TAC = 0 andalso
      count MODEL_REFUTE_TAC = 0 andalso
      count (REFUTE_CONFIG_TAC
               (default_config |> quiet
                  |> only [RegisteredBackend "selftest-probe"])) = 1)
  end)

val _ = test "quiet suppresses all output" (fn () =>
  let
    val (_, text) = capture 1 (fn () => refute (exhaustive) arith)
  in
    text = ""
  end)

val _ = test "quiet restores the output state after an exception" (fn () =>
  Feedback.with_traces [("Refute", 4)] (fn () =>
    ((ignore (refute (exhaustive |> upd_expect ExpectNone) arith); false)
     handle HOL_ERR _ => Feedback.current_trace "Refute" = 4)) ())

val _ = test "polymorphic goals never get a QC-only NoCounterexample"
  (fn () =>
    refute exhaustive ``T`` == NoCounterexample andalso
    not_refuted (refute exhaustive ``(x : 'a) = x``) andalso
    refute exhaustive ``(x : 'a) = x`` =/= NoCounterexample)

(* try_refute: quiet, sequential, seeded, returns the backend that hit. *)
val _ = test "try_refute reports a hit and a miss" (fn () =>
  (case try_refute default_config ([], arith) of
       SOME (backend, Counterexample _) =>
         Lib.mem backend ["exhaustive", "random", "narrowing", "kodkod"]
     | _ => false) andalso
  not (Option.isSome (try_refute default_config ([], ``T``))))

val _ = test "try_refute is quiet and deterministic" (fn () =>
  let
    val (r1, text) = capture 1 (fn () => try_refute default_config ([], arith))
    val r2 = try_refute default_config ([], arith)
  in
    text = "" andalso
    (case (r1, r2) of
         (SOME (b1, Counterexample (c1 :: _)),
          SOME (b2, Counterexample (c2 :: _))) =>
           b1 = b2 andalso
           ListPair.allEq (fn ((v, x), (w, y)) =>
             Term.aconv v w andalso Term.aconv x y)
             (#bindings c1, #bindings c2)
       | _ => false)
  end)

(* ------------------------------------------------------------------- *)
(* Configuration                                                       *)
(* ------------------------------------------------------------------- *)

val _ = section "configuration"

val _ = test "show_config prints every field" (fn () =>
  let
    val expected = String.concatWith "\n" [
      "timeout = 10.0", "backends = NONE", "sequential = false",
      "genuine_only = false", "abort_potential = false", "quiet = true",
      "no_assms = false", "evals = 0 terms", "expect = NoExpectation",
      "max_counterexamples = 1", "tag = ", "widths = [1, 2, 3, 4]",
      "size = 10", "size_mode = IterativeDeepening", "iterations = 100",
      "depth = 10", "finite_types = true", "finite_type_size = 3",
      "default_type = :num", "instantiate = []", "substrate = Auto",
      "seed = NONE", "allow_existentials = true", "finite_functions = true",
      "certify = false", "smart_quantifier = true",
      "smart_generators = true", "optimise_equality = true",
      "reorder_premises = true", "use_subtype = false",
      "allow_function_inversion = false",
      "mf.card = [NONE => [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]",
      "mf.card_mode = IterativeDeepening", "mf.max = [NONE => [~1]]",
      "mf.mono = [NONE => NONE]", "mf.wf = [NONE => NONE]",
      "mf.sat_solver = smart", "mf.batch_size = 50", "mf.falsify = true",
      "mf.user_axioms = NONE", "mf.destroy_constrs = true",
      "mf.total_consts = NONE", "mf.peephole_optim = true",
      "mf.datatype_sym_break = 5", "mf.kodkod_sym_break = 15",
      "mf.max_potential = 1", "mf.max_genuine = 1",
      "mf.atoms = [NONE => []]", "mf.format = [NONE => [1]]",
      "mf.show_types = false", "mf.show_skolems = true",
      "mf.show_consts = false", "mf.debug = false", "mf.overlord = false",
      "mf.max_threads = 0", "mf.tac_timeout = 0.5", "mf.specialize = true",
      "mf.box = [NONE => NONE]", "mf.binary_ints = NONE",
      "mf.bits = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]",
      "mf.star_linear_preds = true",
      "mf.iter = [NONE => [0, 1, 2, 4, 8, 12, 16, 20, 24, 28]]",
      "mf.bisim_depth = [9]", "mf.finitize = [NONE => NONE]",
      "mf.whack = []", "mf.need = NONE", "mf.merge_type_vars = false"] ^ "\n"
    val (_, text) =
      Lib.with_flag (the_config, upd_quiet true (upd_certify false
                                                   default_config))
        (Lib.with_flag (Feedback.MESG_to_string, fn text => text)
          (fn () => capture 1 show_config)) ()
  in
    text = expected
  end)

val _ = test "bound updaters select the bound mode" (fn () =>
  #size_mode (#qc default_config) = IterativeDeepening andalso
  #size_mode (#qc (upd_size 10 default_config)) = FixedBound andalso
  #size_mode (#qc (upd_iterative_size 12 (upd_size 10 default_config)))
    = IterativeDeepening andalso
  #card_mode (#mf (upd_card [(NONE, [2])] default_config)) = FixedBound
  andalso
  #card_mode (#mf (upd_iterative_card [(NONE, [1, 2, 3])] default_config))
    = IterativeDeepening)

val _ = test "upd_card without a fallback row adds one" (fn () =>
  List.exists (fn (k, _) => not (Option.isSome k))
    (#card (#mf (upd_card [(SOME ``:num``, [2])] default_config))))

val _ = test "malformed updates are rejected with a message" (fn () =>
  let
    fun rejected (f, message) =
      (ignore (f ()); false)
      handle Feedback.HOL_ERR e => Feedback.message_of e = message
    val leaf = SOME ``ZooLeaf 0``
    val rows = [
      (fn () => upd_max [(leaf, [1])] default_config,
       "max: row key must be a constant or variable; got: ZooLeaf 0"),
      (fn () => upd_wf [(leaf, SOME true)] default_config,
       "wf: row key must be a constant or variable; got: ZooLeaf 0"),
      (fn () => upd_iter [(leaf, [1])] default_config,
       "iter: row key must be a constant or variable; got: ZooLeaf 0"),
      (fn () => upd_max_genuine 0 default_config,
       "max_genuine: must be at least 1"),
      (fn () => upd_max_potential ~1 default_config,
       "max_potential: must not be negative"),
      (fn () => upd_bits [0] default_config,
       "bits: values must lie between 1 and 31"),
      (fn () => upd_bits [32] default_config,
       "bits: values must lie between 1 and 31"),
      (fn () => upd_iter [] default_config,
       "iter: rows must contain values with a representable successor"),
      (fn () => upd_iter [(NONE, [~1])] default_config,
       "iter: rows must contain values with a representable successor"),
      (fn () => upd_bisim_depth [] default_config,
       "bisim_depth: values must be -1 or have a representable successor"),
      (fn () => upd_bisim_depth [~2] default_config,
       "bisim_depth: values must be -1 or have a representable successor"),
      (fn () => upd_default_type [] default_config,
       "default_type: must be nonempty")]
    fun raises f = (ignore (f ()); false) handle Feedback.HOL_ERR _ => true
  in
    List.all rejected rows andalso
    raises (fn () => upd_iterative_size 0 default_config) andalso
    raises (fn () => upd_iterative_card [(NONE, [1, 3])] default_config)
    andalso
    raises (fn () => upd_iterative_card [(NONE, [1, 2, 2])] default_config)
  end)

(* ------------------------------------------------------------------- *)
(* Registered backends: dispatch, admission, racing                    *)
(* ------------------------------------------------------------------- *)

val _ = section "registered backends"

val _ = test "backend input form selects instances or the original"
  (fn () =>
    let
      val enabled = ref false
      val mono_seen = ref ([] : instance list)
      val poly_seen = ref ([] : instance list)
      val _ = register_backend
        {name = "selftest-input-mono", weight = ~94,
         configured = fn () => !enabled, requires = AnyGoal,
         input = MonoInstances,
         certainty_ceiling = fn _ => fn _ => Genuine,
         run = fn _ => fn insts => (mono_seen := insts; Unknown [])}
      val _ = register_backend
        {name = "selftest-input-poly", weight = ~93,
         configured = fn () => !enabled, requires = AnyGoal,
         input = PolyOriginal,
         certainty_ceiling = fn _ => fn _ => Genuine,
         run = fn _ => fn insts => (poly_seen := insts; Unknown [])}
      val cfg = default_config |> quiet |> upd_sequential true
        |> upd_finite_type_size 3
        |> only [RegisteredBackend "selftest-input-mono",
                 RegisteredBackend "selftest-input-poly"]
      val poly_goal = ``p (x : 'a) /\ q (y : 'b)``
    in
      with_enabled [enabled] (fn () =>
        (ignore (refute cfg poly_goal);
         length (!mono_seen) = 3 andalso
         (case !poly_seen of
              [inst] => Term.aconv (#original inst) poly_goal andalso
                        length (Term.type_vars_in_term (#goal inst)) = 2
            | _ => false)))
    end)

val _ = test "backends run concurrently unless sequential" (fn () =>
  let
    val enabled = ref false
    val mutex = Mutex.mutex ()
    val cond = ConditionVar.conditionVar ()
    val parties = ref 2
    val window = ref 1.0
    val inside = ref 0
    val peak = ref 0
    val arrived = ref 0
    val released = ref false
    (* Arrival of the [parties]th backend releases the barrier.  Concurrently
       that is all three, so the pin is decided by the meeting itself and
       [window] only keeps a lost meeting from wedging the run.  Sequentially
       a second arrival is already the regression, so there [window] is the
       waiting-for-nobody span whose expiry is the pass. *)
    fun barrier () =
      let
        val _ = Mutex.lock mutex
        val _ = inside := !inside + 1
        val _ = arrived := !arrived + 1
        val _ = if !inside > !peak then peak := !inside else ()
        val _ = if !inside >= !parties then released := true else ()
        val deadline = Time.+ (Time.now (), Time.fromReal (!window))
        fun wait () =
          if !released orelse Time.>= (Time.now (), deadline) then ()
          else (ignore (ConditionVar.waitUntil (cond, mutex, deadline));
                wait ())
      in
        wait ();
        ConditionVar.broadcast cond;
        inside := !inside - 1;
        Mutex.unlock mutex
      end
    val names = ["selftest-barrier-a", "selftest-barrier-b",
                 "selftest-barrier-c"]
    val _ = app (fn n => register_backend (stub n ~90 enabled
                  (fn _ => fn _ => (barrier (); Unknown [])))) names
    fun run sequential =
      (inside := 0; peak := 0; arrived := 0; released := false;
       parties := (if sequential then 2 else length names);
       window := (if sequential then 1.0 else 10.0);
       ignore (refute (default_config |> quiet
                         |> only (map RegisteredBackend names)
                         |> upd_sequential sequential |> upd_timeout 10.0)
                      ``T``);
       (!peak, !arrived))
  in
    with_enabled [enabled] (fn () =>
      with_global_thread_count 1 (fn () =>
        run false = (3, 3) andalso run true = (1, 3)))
  end)

val _ = test "admission is bounded by the timeout" (fn () =>
  let
    val enabled = ref false
    val _ = register_backend
      {name = "selftest-slow-admission", weight = ~80,
       configured = fn () => !enabled,
       requires = ExecutableGoalUnless (fn _ => fn _ =>
         (OS.Process.sleep (Time.fromReal 1.0); true)),
       input = MonoInstances, certainty_ceiling = fn _ => fn _ => Genuine,
       run = fn _ => fn _ => Unknown ["ran"]}
  in
    with_enabled [enabled] (fn () =>
      refute (default_config |> quiet |> upd_timeout 0.05
                |> only [RegisteredBackend "selftest-slow-admission"])
             ``q (!n : num. n = 0)``)
    == Unknown ["selftest-slow-admission admission timed out",
               "search timed out"]
  end)

val _ = test "admission errors are reported in registry order" (fn () =>
  let
    val enabled = ref false
    fun failing name delay = register_backend
      {name = name, weight = ~79,
       configured = fn () => !enabled,
       requires = ExecutableGoalUnless (fn _ => fn _ =>
         (OS.Process.sleep (Time.fromReal delay); raise Fail (name ^ " boom"))),
       input = MonoInstances, certainty_ceiling = fn _ => fn _ => Genuine,
       run = fn _ => fn _ => Unknown ["ran"]}
    val _ = failing "selftest-admission-alpha" 0.3
    val _ = failing "selftest-admission-beta" 0.0
  in
    case with_enabled [enabled] (fn () =>
      refute (default_config |> quiet |> upd_timeout 10.0
                |> upd_sequential false
                |> only [RegisteredBackend "selftest-admission-alpha",
                         RegisteredBackend "selftest-admission-beta"])
             ``q (!n : num. n = 0)``) of
        Unknown [alpha, beta] =>
          String.isSubstring "selftest-admission-alpha boom" alpha andalso
          String.isSubstring "selftest-admission-beta boom" beta
      | _ => false
  end)

(* A backend calling back into Refute would compile a second substrate test
   inside the enclosing call's open theory bracket, then wait on a theory
   lock its own caller holds.  Refused, and the refusal reaches the caller
   as the backend's reason rather than as a hang. *)
val _ = test "a backend may not call refute re-entrantly" (fn () =>
  let
    val enabled = ref false
    val nested_runs = ref 0
    val _ = register_backend (stub "selftest-nested" ~77 enabled
      (fn _ => fn _ => (nested_runs := !nested_runs + 1; Unknown [])))
    val _ = register_backend (stub "selftest-outer" ~76 enabled
      (fn _ => fn _ =>
        (ignore (refute (default_config |> quiet |> upd_sequential true
                           |> only [RegisteredBackend "selftest-nested"])
                        ``T``);
         Unknown ["outer completed"])))
  in
    with_enabled [enabled] (fn () =>
      with_global_thread_count 1 (fn () =>
        unknown_with "called from a backend of a running Refute call"
          (refute (default_config |> quiet |> upd_sequential false
                     |> upd_timeout 10.0
                     |> only [RegisteredBackend "selftest-outer",
                              RegisteredBackend "selftest-nested"]) ``T``)
        (* Only the top-level selection of it, never the refused call. *)
        andalso !nested_runs = 1))
  end)

val _ = test "interrupting the caller unwinds the backends" (fn () =>
  let
    val enabled = ref false
    val mutex = Mutex.mutex ()
    val ready = ConditionVar.conditionVar ()
    val started = ref 0
    val unwound = ref 0
    fun blocking_run _ _ =
      let
        fun forever () =
          Multithreading.synchronized "selftest wait" mutex (fn () =>
            let fun wait () = (ConditionVar.wait (ready, mutex); wait ())
            in wait () end)
        fun unwind () =
          Multithreading.synchronized "selftest unwind" mutex (fn () =>
            (unwound := !unwound + 1; ConditionVar.broadcast ready))
        val _ = Multithreading.synchronized "selftest start" mutex (fn () =>
          (started := !started + 1; ConditionVar.broadcast ready))
      in
        Portable.finally unwind forever (); Unknown []
      end
    val names = ["selftest-block-a", "selftest-block-b"]
    val _ = app (fn n => register_backend (stub n ~74 enabled blocking_run))
                names
    val cfg = default_config |> quiet |> upd_sequential false
      |> upd_timeout 10.0 |> only (map RegisteredBackend names)
    val caller_result = ref false
    fun call () =
      caller_result := ((ignore (refute cfg ``T``); false)
                        handle Interrupt => true)
  in
    with_enabled [enabled] (fn () =>
      let
        val caller = Standard_Thread.fork
          {name = "selftest caller", stack_limit = NONE, interrupts = false}
          (fn () => Thread_Attributes.with_attributes
            Thread_Attributes.private_interrupts (fn _ => call ()))
        val _ = Multithreading.synchronized "selftest parent" mutex (fn () =>
          let fun wait () = if !started = 2 then ()
                            else (ConditionVar.wait (ready, mutex);
                                  wait ())
          in wait () end)
        val _ = Standard_Thread.interrupt_unsynchronized caller
        val _ = Standard_Thread.join caller
      in
        !caller_result andalso !unwound = 2
      end)
  end)

(* Racing: a Genuine answer is never cut off by an earlier weaker one, a
   declared ceiling makes a weaker answer decisive, and merged Potential
   answers sort by backend weight. *)
local
  val enabled = ref false
  val genuine_may_start = ref false
  val slow_quasi_started = ref false
  fun cex_backend name weight certainty : backend =
    stub name weight enabled (fn _ => fn _ =>
      (genuine_may_start := true; Counterexample [stub_cex name certainty]))
  val _ = register_backend
    (cex_backend "selftest-race-potential" 50 (Potential ["stub"]))
  val quasi_ceiling = fn _ => fn _ => QuasiGenuine ["stub ceiling"]
  val _ = register_backend (with_ceiling quasi_ceiling
    (cex_backend "selftest-race-quasi" 50 (QuasiGenuine ["stub"])))
  val _ = register_backend (with_ceiling quasi_ceiling
    (stub "selftest-race-slow-quasi" 55 enabled (fn _ => fn _ =>
      (slow_quasi_started := true;
       Counterexample [stub_cex "selftest-race-slow-quasi"
                                (QuasiGenuine ["stub"])]))))
  val _ = register_backend
    {name = "selftest-race-genuine", weight = 20,
     configured = fn () => !enabled, requires = ExecutableGoal,
     input = MonoInstances,
     certainty_ceiling = fn _ => fn _ => Genuine,
     run = fn _ => fn _ =>
       let
         fun wait () = if !genuine_may_start then ()
                       else (OS.Process.sleep (Time.fromReal 0.01); wait ())
       in
         wait (); OS.Process.sleep (Time.fromReal 0.05);
         Counterexample [stub_cex "selftest-race-genuine" Genuine]
       end}
  val _ = register_backend
    (cex_backend "selftest-merge-low" 10 (Potential ["stub"]))
  val _ = register_backend
    (cex_backend "selftest-merge-high" 60 (Potential ["stub"]))
  fun race expectation names goal =
    (genuine_may_start := false; slow_quasi_started := false;
     with_enabled [enabled] (fn () =>
       with_global_thread_count 1 (fn () =>
         refute (default_config |> quiet |> upd_timeout 5.0
                   |> upd_sequential false |> upd_expect expectation
                   |> only (map RegisteredBackend names)) goal)))
  fun won_by name outcome =
    case first_cex outcome of SOME c => #backend c = name | NONE => false
in
  val _ = test "a Potential answer does not cut off a Genuine one" (fn () =>
    race ExpectGenuine ["selftest-race-potential", "selftest-race-genuine"]
         ``T`` |> won_by "selftest-race-genuine")
  val _ = test "a QuasiGenuine answer does not cut off a Genuine one"
    (fn () =>
      race ExpectGenuine ["selftest-race-quasi", "selftest-race-genuine"]
           ``T`` |> won_by "selftest-race-genuine")
  val _ = test "an answer at the declared ceiling is decisive" (fn () =>
    (genuine_may_start := false; slow_quasi_started := false;
     with_enabled [enabled] (fn () =>
       refute (default_config |> quiet |> upd_sequential true
                 |> upd_expect ExpectQuasiGenuine
                 |> only [RegisteredBackend "selftest-race-quasi",
                          RegisteredBackend "selftest-race-slow-quasi"])
              ``zoo_spec = 1``)
     |> won_by "selftest-race-quasi") andalso not (!slow_quasi_started))
  val _ = test "merged Potential answers sort by weight" (fn () =>
    race ExpectPotential ["selftest-merge-low", "selftest-merge-high"] ``T``
    |> won_by "selftest-merge-low")
end

(* ------------------------------------------------------------------- *)
(* Fixtures                                                            *)
(* ------------------------------------------------------------------- *)

val _ = Datatype.Datatype `rg_enum = RGRed | RGGreen | RGBlue`
val _ = Datatype.Datatype `rg_triad = RGTriA | RGTriB | RGTriC`
val _ = Datatype.Datatype `rg_shallow = RGDeep rg_shallow | RGShallow`
val _ = Datatype.Datatype `rg_custom_matrix = RGCustomA | RGCustomB`
val _ = Datatype.Datatype `rg_record = <| rg_field : num |>`
val _ = Datatype.Datatype `rg_binary = RGBLeaf | RGBNode rg_binary rg_binary`
val _ = Datatype.Datatype `rg_tree = RGTip num | RGBin rg_tree rg_tree`
val _ = Datatype.Datatype `rg_rose = RGLeaf | RGNode (rg_rose list)`
val _ = Datatype.Datatype
  `rg_stream_record = <| rg_stream_field : num; rg_stream_flag : bool |>`
val _ = Datatype.Datatype `rg_custom = RGC0 | RGC1`
val _ = Datatype.Datatype `rg_avl = RGET | RGMKT num rg_avl rg_avl num`

val rx_enum_code_def = TotalDefn.Define
  `rx_enum_code RGRed = 0 /\ rx_enum_code RGGreen = 1 /\
   rx_enum_code RGBlue = 2`
val rx_binary_choice_def = TotalDefn.Define
  `rx_binary_choice RGBLeaf = (@n : num. n < 1) /\
   rx_binary_choice (RGBNode l r) = 1`
val rx_rose_def = TotalDefn.Define
  `rx_rose RGLeaf = 0 /\ rx_rose (RGNode []) = 1 /\
   rx_rose (RGNode (child :: children)) = SUC (rx_rose child)`
val rx_mem_def = TotalDefn.Define
  `rx_mem x ([] : 'a list) = F /\
   rx_mem x (y :: ys) = ((x = y) \/ rx_mem x ys)`
val rx_all_distinct_def = TotalDefn.Define
  `rx_all_distinct ([] : 'a list) = T /\
   rx_all_distinct (x :: xs) = (~rx_mem x xs /\ rx_all_distinct xs)`
val rx_list_rel_def = TotalDefn.Define
  `rx_list_rel P ([] : 'a list) ([] : 'b list) = T /\
   rx_list_rel P [] (y :: ys) = F /\
   rx_list_rel P (x :: xs) [] = F /\
   rx_list_rel P (x :: xs) (y :: ys) = (P x y /\ rx_list_rel P xs ys)`
val rx_avl_values_def = TotalDefn.Define
  `rx_avl_values RGET = [] /\
   rx_avl_values (RGMKT n l r h) = n :: (rx_avl_values l ++ rx_avl_values r)`
val rx_avl_height_def = TotalDefn.Define
  `rx_avl_height RGET = 0 /\
   rx_avl_height (RGMKT n l r h) =
     MAX (rx_avl_height l) (rx_avl_height r) + 1`
val rx_avl_ordered_def = TotalDefn.Define
  `rx_avl_ordered RGET = T /\
   rx_avl_ordered (RGMKT n l r h) =
     (EVERY (\m. m < n) (rx_avl_values l) /\
      EVERY (\m. n < m) (rx_avl_values r) /\
      rx_avl_ordered l /\ rx_avl_ordered r)`
val rx_avl_stored_height_def = TotalDefn.Define
  `rx_avl_stored_height RGET = 0 /\
   rx_avl_stored_height (RGMKT n l r h) = h`
val rx_avl_mkt_def = TotalDefn.Define
  `rx_avl_mkt n l r =
     RGMKT n l r (MAX (rx_avl_stored_height l) (rx_avl_stored_height r) + 1)`
val rx_avl_l_bal_def = TotalDefn.Define
  `rx_avl_l_bal (n, RGMKT ln ll lr h, r) =
     if rx_avl_stored_height ll < rx_avl_stored_height lr then
       case lr of
           RGET => RGET
         | RGMKT lrn lrr lrl lrh =>
             rx_avl_mkt lrn (rx_avl_mkt ln ll lrl) (rx_avl_mkt n lrr r)
     else rx_avl_mkt ln ll (rx_avl_mkt n lr r)`
val mf_wf_sortedp_def = TotalDefn.Define
  `mf_wf_sortedp ([] : num list) = T /\
   mf_wf_sortedp [x] = T /\
   mf_wf_sortedp (x :: y :: xs) = (x <= y /\ mf_wf_sortedp (y :: xs))`

val _ = Theory.new_constant ("refute_unmapped_eval", ``:bool``)

(* A custom random half: a linear congruential step over the public rng
   state, choosing between two terms. *)
fun coin a b : rng -> term * rng = fn state =>
  let
    val next = (state * 6364136223846793005 + 1442695040888963407)
               mod IntInf.pow (2, 64)
  in
    (if next div 65536 mod 2 = 0 then a else b, next)
  end

val _ = register_generator ``:rg_custom_matrix``
  {enumerate = SOME (fn _ => [``RGCustomA``, ``RGCustomB``]),
   random = SOME (fn _ => coin ``RGCustomA`` ``RGCustomB``)}
val _ = register_generator ``:rg_enum -> bool``
  {enumerate = SOME (fn _ => [``\x : rg_enum. T``, ``\x : rg_enum. F``]),
   random = SOME (fn _ => coin ``\x : rg_enum. T`` ``\x : rg_enum. F``)}
val _ = register_generator ``:rg_custom``
  {enumerate = SOME (fn _ => [``RGC0``, ``RGC1``]), random = NONE}
val _ = abstract_generator
  {ty = ``:rg_record``,
   constructors = [hd (TypeBasePure.constructors_of
                         (valOf (TypeBase.fetch ``:rg_record``)))],
   pred = SOME ``\x : rg_record. T``}
val _ = register_generator ``:rg_avl``
  {enumerate = SOME (fn _ =>
     [``RGMKT 0 RGET (RGMKT 1 RGET (RGMKT 2 RGET RGET 0) 1) 0``,
      ``RGMKT 4 RGET RGET 0``]),
   random = NONE}

(* ------------------------------------------------------------------- *)
(* Exhaustive backend                                                  *)
(* ------------------------------------------------------------------- *)

val _ = section "exhaustive backend"

val reverse_goal = ``REVERSE (xs : num list) = xs``

val _ = test "reverse is refuted with a list witness" (fn () =>
  refute (exhaustive |> upd_size 3) reverse_goal |> cex_where (fn c =>
    #substrate c = "native" andalso #backend c = "exhaustive" andalso
    certifies reverse_goal c andalso
    List.exists (fn (_, v) =>
      length (#1 (listSyntax.dest_list v)) >= 2 handle HOL_ERR _ => false)
      (#bindings c)))

val _ = test "a closed true goal is NoCounterexample" (fn () =>
  refute exhaustive ``T`` == NoCounterexample)

val _ = test "bounded quantifiers are decided and certified" (fn () =>
  List.all (fn goal => refute exhaustive goal |> cex_where (certifies goal))
    [``(!n : num. n < 3 ==> n * n < 4) <=> T``,
     ``(?n : num. n < 3 /\ n = 3) <=> T``,
     ``(!n : num. n <= 2 ==> n < 2) <=> T``,
     ``(?n : num. n <= 2 /\ n = 3) <=> T``,
     ``(!n : num. n IN count 3 ==> n < 2) <=> T``,
     ``(?n : num. n IN count 3 /\ n = 3) <=> T``,
     ``(!n : num. MEM n [0; 2] ==> n < 2) <=> T``,
     ``(?n : num. MEM n [0; 2] /\ n = 1) <=> T``,
     ``(!i : num. i < LENGTH l ==> EL i l <= 5) <=> T``,
     ``!z : num. z = z ==> (!n : num. 2 <= n /\ n < 5 ==> n * n < 10)``]
  andalso
  refute (exhaustive |> upd_sequential true |> upd_expect ExpectNone)
    ``(!n : num. n < 4 ==> n <= 4) <=> T`` == NoCounterexample andalso
  refute (exhaustive |> upd_sequential true |> upd_expect ExpectNone)
    ``(!n : num. 2 <= n /\ n < 5 ==> n * n < 100) <=> T`` == NoCounterexample)

val _ = test "dependent interval bound is certified by random" (fn () =>
  let val goal = ``!i : num. lo <= i /\ i < LENGTH l ==> EL i l <= k`` in
    refute (random |> upd_seed (SOME 1)) goal |> cex_where (certifies goal)
  end)

val _ = test "a stuck scrutinee is Unknown" (fn () =>
  is_unknown (refute exhaustive
    ``(if THE (NONE : bool option) then SOME 0 else NONE) = SOME (x : num)
      ==> F``))

val _ = test "non-executable goals report the gate reason" (fn () =>
  refute exhaustive ``q (!n : num. n = 0)``
    == Unknown ["not executable: unexpanded binder"] andalso
  unknown_with "refute_unmapped_eval"
    (refute exhaustive ``refute_unmapped_eval``)
  andalso
  unknown_with "GSPEC" (refute (exhaustive |> upd_size 4)
                          ``!x : num. x IN {y | y < 3}``))

val _ = test "an any-goal backend still receives gated instances" (fn () =>
  let
    val enabled = ref false
    val gated = ref false
    val _ = register_backend (stub "selftest-any-goal" ~99 enabled
      (fn _ => fn insts =>
        (gated := (not (null insts) andalso
                   List.all (Option.isSome o #qc_gate) insts);
         Unknown ["received non-executable instance"])))
  in
    with_enabled [enabled] (fn () =>
      refute (default_config |> quiet
                |> only [Exhaustive, RegisteredBackend "selftest-any-goal"])
             ``q (!n : num. n = 0)``)
    == Unknown ["not executable: unexpanded binder",
               "selftest-any-goal: received non-executable instance"]
    andalso !gated
  end)

val _ = test "search is never exhausted over an infinite type" (fn () =>
  is_unknown (refute (exhaustive |> upd_size 3 |> upd_substrate NativeSML)
                     ``(n : num) < 5``) andalso
  refute (exhaustive |> upd_size 3 |> upd_substrate NativeSML)
    ``(SND (SND p, FST p), FST (SND p, FST p)) = (p : bool # bool)``
  == NoCounterexample andalso
  refute (narrowing |> upd_timeout 5.0)
    ``(SND (SND p, FST p), FST (SND p, FST p)) = (p : bool # bool)``
  == NoCounterexample andalso
  is_unknown (refute (narrowing |> upd_timeout 5.0) ``(n : num) < SUC n``)
  andalso
  is_unknown (refute (narrowing |> upd_timeout 5.0 |> upd_size 1)
                     ``(n : num) < SUC n``))

val _ = test "smart_quantifier prunes a premise" (fn () =>
  let val goal = ``(xs : bool list) = REVERSE [T; T; T; T] ==> F`` in
    is_cex (refute (exhaustive |> upd_size 3 |> upd_smart_quantifier true)
                   goal) andalso
    is_unknown (refute (exhaustive |> upd_size 3
                          |> upd_smart_quantifier false) goal)
  end)

val update_goal =
  ``(f : refute$rf2 -> refute$rf2) rf2_1 = rf2_1 /\ f rf2_2 = rf2_2 ==> F``

val _ = test "function witnesses are UPDATE chains" (fn () =>
  refute (exhaustive |> upd_size 2) update_goal |> cex_where (fn c =>
    List.exists (fn (_, v) => not (null (#1 (combinSyntax.strip_update v))))
      (#bindings c)))

val _ = test "function witnesses use readable binder names" (fn () =>
  let
    val goal = ``(f : num -> num) x = x``
    val f = ``f : num -> num``
    fun witness cfg = Option.mapPartial (fn c => binding c f)
                        (first_cex (refute cfg goal))
  in
    case (witness (exhaustive |> upd_substrate NativeSML),
          witness (exhaustive |> upd_substrate Compute)) of
        (SOME a, SOME b) =>
          Term.aconv a b andalso
          not (String.isSubstring "refute_" (Parse.term_to_string a))
      | _ => false
  end)

val _ = test "certify false gives an uncertified Genuine" (fn () =>
  let
    val cfg = exhaustive |> upd_sequential true |> upd_substrate Compute
      |> upd_size 2 |> upd_evals [``x + 1 : num``] |> upd_certify false
      |> upd_quiet false
    val (outcome, text) = capture 1 (fn () => refute cfg ``(x : num) = 0``)
  in
    single_cex_where (fn c => is_genuine c andalso uncertified c andalso
                              null (#evals c)) outcome andalso
    String.isSubstring "Certification: uncertified" text
  end)

val _ = test "the whole space of a finite type is covered" (fn () =>
  refute exhaustive ``(b : bool) \/ ~b`` == NoCounterexample andalso
  refute exhaustive ``(x : refute$rf2) = rf2_1 \/ x = rf2_2``
    == NoCounterexample andalso
  is_unknown (refute exhaustive ``!n : num. n <= n``))

(* A deadline already gone before the first schedule entry must not leave
   the run claiming NoCounterexample: nothing was tested.  Driven through
   the backend body rather than [refute], because every public route arms
   [Timeout.apply] from the same budget the search reads, so an expired run
   reports "timed out" either way and the pin would be blind. *)
val _ = test "an expired deadline never claims NoCounterexample" (fn () =>
  let
    val enabled = ref false
    val seen = ref ([] : instance list)
    val _ = register_backend (stub "selftest-expired" ~92 enabled
      (fn _ => fn instances => (seen := instances; Unknown [])))
    val cfg = exhaustive |> only [RegisteredBackend "selftest-expired"]
    val _ = with_enabled [enabled]
      (fn () => ignore (refute cfg ``(b : bool) \/ ~b``))
    (* The smart-gate cache is keyed by the call token, so the backend body
       needs one even with no call around it. *)
    fun run_exhaustive config =
      Thread_Data.setmp Refute_Core.active_refute_context (SOME (ref ()))
        (Refute_QC.strategy_run Refute_Eval.Exhaustive config) (!seen)
  in
    not (null (!seen)) andalso
    run_exhaustive exhaustive == NoCounterexample andalso
    run_exhaustive (exhaustive |> upd_timeout 0.0) =/= NoCounterexample
  end)

val _ = test "literals of every kind are witnesses" (fn () =>
  List.all (fn goal => genuine (refute exhaustive goal))
    [``!n : num. n <> 2``, ``!c : char. c <> #"a"``,
     ``!s : string. s <> "x"``, ``~((x : int) = x)``,
     ``w2n ((a : word8) + b) = w2n a + w2n b``])

val _ = test "specialised and higher-order list functions" (fn () =>
  List.all (fn goal => genuine (refute exhaustive goal))
    [``MAP SUC (xs : num list) = xs``,
     ``FILTER ($= 0) (xs : num list) = xs``,
     ``MAP (f : refute$rf2 -> bool) [rf2_1; rf2_2] = [T; T]``,
     ``FILTER (p : refute$rf2 -> bool) [rf2_1; rf2_2] = []``,
     ``SORTED $= (xs : num list) ==> SORTED $= (x :: xs)``,
     ``ALL_DISTINCT (xs : num list ++ ys) <=>
       ALL_DISTINCT xs /\ ALL_DISTINCT ys``])

val _ = test "parallel and sequential agree" (fn () =>
  let
    fun run sequential goal =
      refute (default_config |> quiet |> only [Exhaustive, Random]
                |> upd_seed (SOME 1) |> upd_sequential sequential) goal
    fun agree goal =
      case (run true goal, run false goal) of
          (Counterexample _, Counterexample _) => true
        | (NoCounterexample, NoCounterexample) => true
        | (Unknown a, Unknown b) => a = b
        | _ => false
  in
    agree arith andalso agree ``!b : bool. b \/ ~b``
  end)

(* ------------------------------------------------------------------- *)
(* Random backend                                                      *)
(* ------------------------------------------------------------------- *)

val _ = section "random backend"

val seeded = random |> upd_seed (SOME 1) |> upd_size 4 |> upd_iterations 50
  |> upd_sequential true

val _ = test "random refutes reverse natively" (fn () =>
  refute seeded reverse_goal |> cex_where (fn c =>
    #backend c = "random" andalso #substrate c = "native"))

val _ = test "random refutes arithmetic" (fn () => is_cex (refute seeded arith))

fun same_bindings (c1 : counterexample) (c2 : counterexample) =
  ListPair.allEq (fn ((v, x), (w, y)) => Term.aconv v w andalso Term.aconv x y)
    (#bindings c1, #bindings c2)

val _ = test "an explicit seed is reproducible" (fn () =>
  case (first_cex (refute seeded reverse_goal),
        first_cex (refute seeded reverse_goal)) of
      (SOME a, SOME b) => same_bindings a b
    | _ => false)

val _ = test "max_counterexamples collects several" (fn () =>
  case refute (random |> upd_substrate Compute |> upd_iterations 10
                 |> upd_size 1 |> upd_seed (SOME 1)
                 |> upd_max_counterexamples 3) ``(x : num) = x + 1`` of
      Counterexample cexs => length cexs = 3
    | _ => false)

val _ = test "a seed draws the same values on every substrate" (fn () =>
  let
    fun run s = first_cex (refute (random |> upd_iterations 3 |> upd_size 10
                                     |> upd_seed (SOME ~1) |> upd_substrate s)
                                  ``(x : num) = x + 1``)
  in
    case (run Compute, run NativeSML) of
        (SOME a, SOME b) => same_bindings a b
      | _ => false
  end)

val _ = test "an unseeded run completes" (fn () =>
  case refute (random |> upd_iterations 2 |> upd_size 2) ``(x : num) = 0`` of
      Model _ => false
    | NoModel => false
    | _ => true)

val _ = test "random stays Genuine on a specialised relation" (fn () =>
  genuine (refute (seeded |> upd_max_counterexamples 1 |> upd_iterations 100
                     |> upd_timeout 300.0)
                  ``SORTED $= (xs : num list) ==> SORTED $= (x :: xs)``))

(* ------------------------------------------------------------------- *)
(* Narrowing backend                                                   *)
(* ------------------------------------------------------------------- *)

val _ = section "narrowing backend"

val nar = narrowing |> upd_substrate NativeSML

fun has_hole tm = String.isSubstring "_" (Parse.term_to_string tm)

val _ = test "a ground hit is certified" (fn () =>
  refute (nar |> upd_size 1) ``(b : bool)`` |> single_cex_where (fn c =>
    #backend c = "narrowing" andalso #substrate c = "native" andalso
    certifies ``(b : bool)`` c andalso binding_is c ``b : bool`` ``F``))

val _ = test "a partial hit keeps its hole and is certified" (fn () =>
  let
    val cfg = nar |> upd_size 1 |> upd_evals [``xs : num list``]
      |> upd_quiet false
    val (outcome, text) = capture 1 (fn () =>
      refute cfg ``NULL (xs : num list)``)
  in
    single_cex_where (fn c =>
      certifies ``NULL (xs : num list)`` c andalso
      (case #evals c of [(_, v)] => Term.aconv v ``[0] : num list``
                      | _ => false) andalso
      (case #bindings c of [(_, v)] => has_hole v | _ => false)) outcome
    andalso String.isSubstring "_" text
  end)

val _ = test "certify false keeps the hole, drops the certificate" (fn () =>
  refute (nar |> upd_size 1 |> upd_certify false) ``NULL (xs : num list)``
  |> single_cex_where (fn c =>
       is_genuine c andalso uncertified c andalso
       (case #bindings c of [(_, v)] => has_hole v | _ => false)))

val exists_goal = ``?x : rg_enum. rx_enum_code x = 3``

val _ = test "existential replay is certified" (fn () =>
  refute (nar |> upd_size 2) exists_goal
    |> single_cex_where (certifies exists_goal) andalso
  refute (nar |> upd_size 2 |> upd_certify false) exists_goal
    |> single_cex_where (fn c => is_genuine c andalso uncertified c) andalso
  unknown_with "allow_existentials"
    (refute (nar |> upd_size 2 |> upd_allow_existentials false) exists_goal))

(* A universal witness keeps its unrefined positions as free variables, so
   the existential leaf below one holds [num]-typed holes.  The case split
   must follow the cover, not the leaf's first splittable free variable:
   the holes are recursive, and splitting them never terminates. *)
val hole_exists_goal =
  ``NULL (xs : num list) \/ ?x : rg_enum. rx_enum_code x = 3``

val _ = test "a witness hole does not divert the existential case split"
  (fn () =>
    refute (nar |> upd_size 2) hole_exists_goal
      |> single_cex_where (certifies hole_exists_goal))

val _ = test "mixed and incomplete prefixes are certified" (fn () =>
  let
    val mixed = ``(b : bool) /\ (?x : rg_enum. rx_enum_code x = 3)``
    val incomplete = ``?y : bool. (x : num) = 0 /\ y``
  in
    refute (nar |> upd_size 2) mixed |> single_cex_where (certifies mixed)
    andalso
    refute (nar |> upd_size 2) incomplete
      |> single_cex_where (certifies incomplete)
  end)

val _ = test "an exhausted narrowing search is Unknown" (fn () =>
  List.all (fn cfg => unknown_with "narrowing search exhausted"
                        (refute cfg ``?n : num. n = 4``))
    [nar |> upd_size 2, nar |> upd_size 2 |> upd_certify false] andalso
  unknown_with "narrowing search exhausted"
    (refute (nar |> upd_size 2) ``?xs : bool list. LENGTH xs = 3``))

val _ = test "true existential goals never yield Genuine" (fn () =>
  let
    fun sound size goal =
      List.all (fn certify =>
        not (genuine (refute (nar |> upd_size size |> upd_certify certify
                                |> upd_abort_potential true) goal)))
        [true, false]
  in
    sound 2 ``?f : (bool -> bool) -> bool. f (\x. x) /\ ~f (\x. ~x)`` andalso
    sound 2 ``?f : rg_enum -> bool. f RGRed /\ f RGGreen /\ ~f RGBlue`` andalso
    sound 3 ``?p : (rg_enum -> bool) # bool.
                FST p RGRed /\ FST p RGGreen /\ ~FST p RGBlue`` andalso
    sound 2 ``!x : num. ?y. y = SUC x`` andalso
    sound 2 ``!p : num # num. ?n. n = SUC (FST p + SND p)`` andalso
    sound 2 ``!xs : num list. ?ys. ys = 0 :: xs``
  end)

val _ = test "datatype and custom enumerations" (fn () =>
  refute (nar |> upd_size 1) ``(x : rg_shallow) = RGDeep RGShallow``
    |> single_cex_where (fn c =>
         Option.isSome (#cert c) andalso
         binding_is c ``x : rg_shallow`` ``RGShallow``) andalso
  refute (nar |> upd_size 1) ``(x : rg_custom_matrix) = RGCustomA``
    |> single_cex_where (fn c =>
         Option.isSome (#cert c) andalso
         binding_is c ``x : rg_custom_matrix`` ``RGCustomB``) andalso
  refute (nar |> upd_size 2) ``(s : bool set) = UNIV``
    |> single_cex_where (fn c => is_genuine c andalso Option.isSome (#cert c)))

val _ = test "partial function and product witnesses" (fn () =>
  refute (nar |> upd_size 2) ``FST ((f : bool -> bool # bool) F)``
    |> single_cex_where (fn c =>
         Option.isSome (#cert c) andalso
         (case #bindings c of [(_, v)] => has_hole v | _ => false)) andalso
  refute (nar |> upd_size 1) ``FST (p : bool # bool)``
    |> single_cex_where (fn c =>
         Option.isSome (#cert c) andalso
         (case #bindings c of
              [(_, v)] => pairSyntax.is_pair v andalso has_hole v
            | _ => false)) andalso
  refute (nar |> upd_size 3 |> upd_abort_potential true)
         ``FST (p : (bool -> bool) # bool) F = FST p T``
    |> single_cex_where (fn c =>
         case #bindings c of
             [(_, v)] => not (null (#1 (combinSyntax.strip_update
                                          (pairSyntax.dest_pair v |> #1))))
           | _ => false))

val _ = test "function witnesses are updates and lambdas" (fn () =>
  refute (nar |> upd_size 2) ``(f : bool -> bool) F = f T``
    |> single_cex_where (fn c =>
         Option.isSome (#cert c) andalso
         binding_is c ``f : bool -> bool`` ``(T =+ F) (\x. T)``) andalso
  refute (nar |> upd_size 1) ``(f : (bool -> bool) -> bool) (\x. T)``
    |> single_cex_where (fn c =>
         Option.isSome (#cert c) andalso
         binding_is c ``f : (bool -> bool) -> bool``
                      ``\g : bool -> bool. F``))

val _ = test "finite_functions false refuses function domains" (fn () =>
  let val outcome = refute (nar |> upd_size 2 |> upd_finite_functions false)
                           ``(f : bool -> bool) F = f T``
  in unknown_with "function type" outcome andalso
     unknown_with "before finitization" outcome
  end)

val _ = test "narrowing reaches MEM" (fn () =>
  genuine (refute narrowing ``!l : num list. MEM 0 l``))

(* An alternative id denotes the same character at every depth, so the
   generated program needs one reconstruction arm per character, not one
   per (depth, character).  Emitting the depth-indexed form instead makes
   a [char] carrier cost 256 arms and 256 shape entries at every depth of
   the window, and compiling that program alone outruns the budget. *)
val _ = test "narrowing refutes char and string goals" (fn () =>
  refute narrowing ``!c : char. c <> #"z"``
    |> single_cex_where (fn c => binding_is c ``c : char`` ``#"z"``)
  andalso
  refute narrowing ``!s : string. s <> "ab"``
    |> single_cex_where (fn c => binding_is c ``s : string`` ``"ab"``))

val _ = test "narrowing publishes an uncertified dependent interval"
  (fn () =>
    refute narrowing ``!i : num. lo <= i /\ i < LENGTH l ==> EL i l <= k``
    |> cex_where (fn c => is_genuine c andalso uncertified c))

val _ = test "narrowing declines by name what it cannot enumerate" (fn () =>
  unknown_with "not extractable"
    (refute narrowing ``FLOOKUP (fm : num |-> num) 0 = SOME 0``) andalso
  unknown_with "no TypeBase information for :rat"
    (refute narrowing ``(x : rat) = rat_of_num 1``) andalso
  unknown_with "no TypeBase information for :real"
    (refute narrowing ``(x : real) = real_of_num 1``))

(* ------------------------------------------------------------------- *)
(* Finite maps and finite sets                                         *)
(* ------------------------------------------------------------------- *)

val _ = section "finite maps"

val flookup_goal = ``FLOOKUP (fm : num |-> num) 0 = SOME 0``

val _ = test "finite sets ask for a generator" (fn () =>
  let
    fun clean outcome =
      is_unknown outcome andalso not (null (reasons_of outcome)) andalso
      List.all (fn r =>
        r <> "" andalso not (Char.isSpace (String.sub (r, 0))) andalso
        not (List.exists (fn bad => String.isSubstring bad r)
               ["Exception", "induction_of0", "Match"])) (reasons_of outcome)
    val member = ``fIN (0 : num) (fs : num fset)``
  in
    List.all (fn outcome => clean outcome andalso
                            unknown_with "register a generator" outcome)
      [refute exhaustive member, refute narrowing member] andalso
    clean (refute exhaustive ``(fs : num fset) = fEMPTY``)
  end)

val _ = test "FLOOKUP on an empty map is refuted and certified" (fn () =>
  refute exhaustive flookup_goal |> cex_where (fn c =>
    is_genuine c andalso
    (case #bindings c of [(_, v)] => finite_mapSyntax.is_fempty v
                       | _ => false)) andalso
  refute qc flookup_goal |> cex_where (fn c => is_genuine c andalso
                                                Option.isSome (#cert c)))

val _ = test "true finite-map properties are not refuted" (fn () =>
  refute qc ``FLOOKUP ((FEMPTY : num |-> num) |+ (0, 0)) 0 = SOME 0``
    == NoCounterexample andalso
  not_refuted (refute (qc |> upd_size 2) ``!fm : bool |-> bool.
                                             CARD (FDOM fm) <= 2``) andalso
  genuine (refute (qc |> upd_size 2) ``!fm : bool |-> bool.
                                         CARD (FDOM fm) <= 1``))

val _ = test "finite-map equality is decided during testing" (fn () =>
  let
    val compute = random |> upd_substrate Compute
  in
    refute compute ``FLOOKUP (fm : bool |-> bool) T =
                     FLOOKUP (fm' : bool |-> bool) T ==> fm = fm'``
    |> genuine_certified andalso
    not_refuted (refute (compute |> upd_abort_potential true)
                   ``(fm : bool |-> bool) |+ (F,F) |+ (T,T) =
                     fm |+ (T,T) |+ (F,F)``)
  end)

val _ = test "finite-map search is never exhausted" (fn () =>
  refute (exhaustive |> upd_substrate Compute |> upd_size 2)
         ``FDOM ((fm : num |-> num) |+ (k, v)) = k INSERT FDOM fm``
  == Unknown ["exhaustive: search space not exhausted",
              "exhaustive: searched up to size 2"])

val _ = test "function-update display drops shadowed points" (fn () =>
  case lookup_term_postprocessor ``:num -> num`` of
      NONE => false
    | SOME rewrite =>
        List.all (fn base =>
          let
            val upd = combinSyntax.mk_update
            val shadowed = Term.mk_comb (upd (``1 : num``, ``20 : num``),
                             Term.mk_comb (upd (``1 : num``, ``10 : num``),
                                           base))
            val direct = Term.mk_comb (upd (``1 : num``, ``20 : num``), base)
          in
            Term.aconv (rewrite shadowed) direct
          end)
          [combinSyntax.mk_K_1 (``0 : num``, ``:num``),
           Term.mk_abs (Term.mk_var ("x", ``:num``), ``0 : num``)])

(* ------------------------------------------------------------------- *)
(* Smart generators for inductive premises                             *)
(* ------------------------------------------------------------------- *)

val _ = section "smart generators"

val linear_goal = ``zoo_sg_linear (n : num) ==> n < 3``
val native = exhaustive |> upd_substrate NativeSML

val _ = test "an inductive premise is enumerated at depth" (fn () =>
  with_compset [zoo_sg_linear_compute] (fn () =>
    let val cfg = native |> upd_size 1 |> upd_timeout 5.0 in
      is_unknown (refute (cfg |> upd_depth 3) linear_goal) andalso
      refute (cfg |> upd_depth 4) linear_goal |> cex_where (fn c =>
        #substrate c = "native" andalso is_genuine c andalso
        Option.isSome (#cert c) andalso binding_is c ``n : num`` ``3 : num``)
      andalso
      (case refute (cfg |> upd_depth 4 |> upd_smart_generators false)
                   linear_goal of
           Unknown (r :: _) => r = "exhaustive: search space not exhausted"
         | _ => false)
    end))

val _ = test "smart_generators false reports the gate" (fn () =>
  let
    val (outcome, text) = capture 2 (fn () =>
      refute (exhaustive |> upd_smart_generators false |> upd_quiet false)
             linear_goal)
  in
    unknown_with "not executable: zoo_sg_linear" outcome andalso
    String.isSubstring "QC backends excluded: not executable" text
  end)

val _ = test "a Horn premise is enumerated" (fn () =>
  let
    val goal = ``ALL_DISTINCT (xs : bool list) ==> LENGTH xs < 1``
    val cfg = exhaustive |> upd_substrate Compute |> upd_size 1
      |> upd_depth 8 |> upd_timeout 5.0
  in
    refute cfg goal |> cex_where (fn c =>
      #substrate c = "compute" andalso is_genuine c andalso
      Option.isSome (#cert c) andalso
      (case binding c ``xs : bool list`` of
           SOME v => not (null (#1 (listSyntax.dest_list v)))
         | NONE => false)) andalso
    (case refute (cfg |> upd_smart_generators false) goal of
         Unknown (r :: _) => r = "exhaustive: search space not exhausted"
       | _ => false)
  end)

val _ = test "duplicate outputs, mutual, string and hygiene premises"
  (fn () =>
    with_compset [zoo_sg_duplicate_compute] (fn () =>
      refute (native |> upd_size 1 |> upd_depth 1)
             ``zoo_sg_duplicate (n : num) p ==> n = 0``
      |> cex_where (fn c => Option.isSome (#cert c) andalso
                            binding_is c ``p : num # num``
                                         ``(1, 1) : num # num``))
    andalso
    List.all (fn (depth, goal) =>
      genuine (refute (native |> upd_certify false |> upd_size 1
                         |> upd_depth depth) goal))
      [(4, ``zoo_sg_native_left (n : num) ==> n = 0``),
       (3, ``zoo_sg_string (s : char list) ==> LENGTH s < 2``),
       (2, ``zoo_sg_hygiene (x : num) y z ==> x = 0``),
       (1, ``(n : num) < 3 ==> zoo_sg_linear n ==> F``)])

val _ = test "static parameters are specialised" (fn () =>
  let
    val cfg = exhaustive |> upd_sequential true |> upd_certify false
    val headline =
      ``zoo_sg_listall (\n:num. n = 500) (xs:num list) ==> LENGTH xs <= 2``
    val twin = Thm.concl (fst (EQ_IMP_RULE (SPEC ``xs : num list``
                 (ISPEC ``\n:num. n = 500`` zoo_sg_listall_compute))))
    val sibling = ``zoo_sg_listall (\n:num. n = 500) (xs:num list) ==>
                    EVERY (\n:num. n = 499) xs``
  in
    refute (cfg |> upd_expect ExpectGenuine) headline |> cex_where (fn c =>
      binding_is c ``xs : num list`` ``[500; 500; 500] : num list``) andalso
    refute (exhaustive |> upd_depth 4 |> upd_size 1)
           ``zoo_sg_listall (\n:num. n = 7) (xs:num list) ==> LENGTH xs <= 2``
    |> cex_where (fn c => binding_is c ``xs : num list``
                                     ``[7; 7; 7] : num list``)
    andalso
    not_refuted (refute (cfg |> upd_size 3) twin) andalso
    refute (cfg |> upd_size 3 |> upd_expect ExpectGenuine) sibling
    |> cex_where (fn c => binding_is c ``xs : num list`` ``[500] : num list``)
  end)

val _ = test "a false listall goal is never NoCounterexample" (fn () =>
  refute exhaustive ``zoo_sg_listall (\n:num. n = 500) (xs:num list) ==> F``
  =/= NoCounterexample)

val _ = test "a negated inductive premise is complemented" (fn () =>
  let
    val goal = ``~zoo_sg_duplicate (n : num) (p : num # num) ==> p = (n, n)``
    val bool_goal =
      ``~zoo_sg_bool_duplicate (x : bool) (y, z) ==> (y, z) = (x, x)``
  in
    List.all (fn (s, name) =>
      refute (exhaustive |> upd_substrate s |> upd_certify false |> upd_size 2
                |> upd_depth 1) goal
      |> cex_where (fn c => #substrate c = name andalso is_genuine c))
      [(NativeSML, "native"), (Compute, "compute")] andalso
    unknown_with "not executable"
      (refute (exhaustive |> upd_sequential true |> upd_smart_generators false)
              ``~zoo_sg_bool_duplicate (x : bool) (y, z) ==> (y, z) <> (x, x)``)
    andalso
    genuine (refute (exhaustive |> upd_size 2 |> upd_sequential true
                       |> upd_certify false |> upd_expect ExpectGenuine)
                    bool_goal) andalso
    with_compset [zoo_sg_bool_duplicate_compute] (fn () =>
      genuine_certified (refute (exhaustive |> upd_size 2
                                   |> upd_substrate Compute
                                   |> upd_sequential true
                                   |> upd_expect ExpectGenuine) bool_goal))
    andalso
    refute (exhaustive |> upd_sequential true |> upd_certify false
              |> upd_expect ExpectNone)
           ``~zoo_sg_bool_duplicate (x : bool) (T, T) ==> x <> T``
    == NoCounterexample andalso
    unknown_with "search space not exhausted"
      (refute (exhaustive |> upd_sequential true |> upd_certify false)
              ``~zoo_sg_bool_stuck (x : bool) (T, T) ==> x <> T``)
  end)

val _ = test "premise reordering is sound both ways" (fn () =>
  List.all (fn (cfg, goal, pins) =>
    List.all (fn reorder =>
      refute (cfg |> upd_reorder_premises reorder |> upd_certify false) goal
      |> cex_where (fn c => is_genuine c andalso
                            List.all (fn (v, x) => binding_is c v x) pins))
      [true, false])
    [(exhaustive |> upd_size 2 |> upd_depth 1,
      ``~zoo_sg_duplicate (n : num) (p : num # num) ==> n = 0 ==> p = (n, n)``,
      [(``n : num``, ``0 : num``)]),
     (exhaustive |> upd_size 3 |> upd_depth 2 |> upd_substrate Compute,
      ``zoo_sg_listall (\n:num. n = 500) (xs:num list) ==> xs = [500] ==> F``,
      [(``xs : num list``, ``[500] : num list``)]),
     (exhaustive |> upd_allow_function_inversion true |> upd_timeout 3.0,
      ``(xs : num list) ++ ys = [1;2;3] ==> ys = [3] ==> F``,
      [(``ys : num list``, ``[3] : num list``),
       (``xs : num list``, ``[1;2] : num list``)])])

val _ = test "function inversion refutes and stays sound" (fn () =>
  genuine (refute (exhaustive |> upd_allow_function_inversion true)
                  ``(xs : num list) ++ ys = [1;2;3] ==> LENGTH xs <> 1``)
  andalso
  not_refuted (refute (exhaustive |> upd_allow_function_inversion true
                         |> upd_size 3 |> upd_sequential true)
                      ``(xs : num list) ++ ys = [1;2;3] ==> LENGTH xs <= 3``))

(* ------------------------------------------------------------------- *)
(* Native substrate                                                    *)
(* ------------------------------------------------------------------- *)

val _ = section "native substrate"

fun both_strategies cfg goal P =
  refute (cfg |> only [Exhaustive]) goal |> cex_where P andalso
  refute (cfg |> only [Random] |> upd_seed (SOME 1)) goal |> cex_where P

fun native_genuine (c : counterexample) =
  #substrate c = "native" andalso is_genuine c

val _ = test "native handles MEM, option maps and compound updates" (fn () =>
  both_strategies (native |> upd_size 4)
    ``nub (xs : num list ++ ys) = nub xs ++ nub ys`` native_genuine andalso
  both_strategies (native |> upd_size 4)
    ``(m : num -> num option) k = SOME (v : num) ==> m k = NONE``
    native_genuine andalso
  genuine (refute (exhaustive |> upd_size 4)
                  ``(m : num -> num option) k = SOME (v : num) ==> m k = NONE``)
  andalso
  both_strategies (native |> upd_size 3)
    ``((SOME 1 =+ T) (upd_f : num option -> bool)) NONE`` native_genuine)

(* A specification is keyed by its left-hand side's head constant and hides
   that constant's own definition: [zoo_hidden_pick_spec] shadows
   [zoo_hidden_def] the way [pred_set]'s [GSPECIFICATION] shadows
   [bool$IN_DEF].  The presented specification is refused for its shape, and
   extraction recovers the real equations from the constant's home theory.
   [zoo_opaque] is the other side: a specification introduces it and it has
   no definition anywhere, so it never becomes executable at all.  That
   refusal is the executability gate's, not extraction's -- it is reached
   before a substrate is chosen -- and all this pins of it is that it names
   the constant rather than failing anonymously. *)
val _ = test "native recovers a definition hidden by a specification"
  (fn () =>
    both_strategies (native |> upd_size 3) ``!n : num. zoo_hidden n``
      native_genuine andalso
    unknown_with "zoo_opaque"
      (refute (native |> upd_size 3) ``!n : num. zoo_opaque n``))

val _ = test "native char-list primitives" (fn () =>
  List.all (fn goal =>
    refute (native |> upd_smart_generators false |> upd_iterations 100
              |> upd_size 3 |> upd_sequential true) goal
    |> cex_where (fn c => native_genuine c andalso Option.isSome (#cert c)))
    [``!s : string. SNOC #"a" s = s``,
     ``!s : string. s <> [] ==> LAST s = #"a"``,
     ``!s : string. s <> [] ==> FRONT s = s``,
     ``!s : string. ALL_DISTINCT s ==> LENGTH s < 2``])

val _ = test "substrates agree on small goals" (fn () =>
  let
    val base = default_config |> quiet |> upd_iterations 100 |> upd_size 3
      |> upd_sequential true
    fun agree s1 s2 strategy goal =
      case (refute (base |> upd_substrate s1 |> strategy) goal,
            refute (base |> upd_substrate s2 |> strategy) goal) of
          (Counterexample (a :: _), Counterexample (b :: _)) =>
            same_bindings a b andalso #backend a = #backend b
        | (NoCounterexample, NoCounterexample) => true
        | (Unknown _, Unknown _) => true
        | _ => false
    val strategies =
      only [Exhaustive] :: map (fn s => fn c => c |> only [Random]
                                               |> upd_seed (SOME s)) [1, 2, 3]
    val goals = [reverse_goal, arith, ``(x : refute$rf3) = rf3_1``]
  in
    List.all (fn goal => List.all (fn strategy =>
      agree Compute NativeSML strategy goal) strategies) goals
  end)

(* word64 random draws are two draws of the 64-bit PRNG, one per half, and
   both substrates must consume them in the same order.  Almost every draw
   refutes this goal, so the witness is the draw itself and comparing
   witnesses really compares streams. *)
val _ = test "word64 random draws agree across substrates" (fn () =>
  let
    val goal = ``!w : word64. w = 0w``
    val cfg = random |> upd_seed (SOME 7) |> upd_iterations 10
      |> upd_sequential true
    fun draw s = first_cex (refute (cfg |> upd_substrate s) goal)
  in
    case (draw NativeSML, draw Compute) of
        (SOME a, SOME b) =>
          is_genuine a andalso is_genuine b andalso same_bindings a b
      | _ => false
  end)

(* Compute defines its enumerator programs inside the theory bracket, so
   the smart-generator goal is what actually drives the revert. *)
val _ = test "compute leaves the theory untouched" (fn () =>
  let
    val baseline = footprint ()
    val cfg = default_config |> quiet |> upd_substrate Compute
      |> upd_iterations 100 |> upd_size 2 |> upd_sequential true
  in
    ignore (refute (cfg |> only [Exhaustive]) reverse_goal);
    ignore (refute (cfg |> only [Random] |> upd_seed (SOME 1)) reverse_goal);
    ignore (refute (cfg |> only [Exhaustive] |> upd_depth 1)
              ``~zoo_sg_duplicate (n : num) (p : num # num) ==> p = (n, n)``);
    footprint () = baseline
  end)

(* Auto's chain is native then compute, and the trace test below pins the
   walk itself. *)
val _ = test "Auto picks a substrate per goal" (fn () =>
  let
    val cfg = default_config |> quiet |> upd_size 3 |> upd_iterations 30
    fun picks name goal strategy =
      refute (cfg |> strategy) goal |> cex_where (fn c => #substrate c = name)
    val ex = only [Exhaustive]
    fun rnd c = c |> only [Random] |> upd_seed (SOME 1)
  in
    picks "native" reverse_goal ex andalso picks "native" reverse_goal rnd
    andalso
    picks "compute" ``(r : rg_record) = s`` ex andalso
    picks "compute" ``(r : rg_record) = s`` rnd andalso
    picks "native" ``(w : word64) = 0w`` rnd andalso
    picks "compute" ``(f : rg_enum -> bool) RGRed`` ex andalso
    picks "compute" ``(f : rg_enum -> bool) RGRed`` rnd
  end)

val _ = test "an explicit substrate declines by name" (fn () =>
  let
    val goal = ``(r : rg_record) = s``
    fun declines s needle strategy =
      unknown_with needle (refute (default_config |> quiet |> upd_substrate s
                                     |> strategy) goal)
    val ex = only [Exhaustive]
    fun rnd c = c |> only [Random] |> upd_seed (SOME 1)
    val native = exhaustive |> upd_substrate NativeSML
  in
    declines NativeSML "custom generator registered" ex andalso
    declines NativeSML "custom generator registered" rnd andalso
    unknown_with "custom generator registered for :rg_custom_matrix"
      (refute native ``(x : rg_custom_matrix) = RGCustomA``) andalso
    (* A registered family must be declined by name, not by dying inside
       the generator derivation. *)
    (let val outcome = refute native flookup_goal in
       is_unknown outcome andalso
       not (unknown_with "HOL_ERR" outcome) andalso
       not (unknown_with "axiom_of" outcome)
     end)
  end)

(* The three message flags are process-global, and a compiled test's
   bracket outlives admission: a sibling backend of the same call runs on
   another worker while it is held.  So the quiet window is each piece of
   theory work, not the bracket's lifetime -- and it must be given back on
   the raising path too. *)
val _ = test "a theory bracket leaves the global message flags alone"
  (fn () =>
    let
      val saved_info = !Feedback.emit_INFO
      val saved_tyvar = !Globals.notify_on_tyvar_guess
      fun restore () =
        (Feedback.emit_INFO := saved_info;
         Globals.notify_on_tyvar_guess := saved_tyvar)
    in
      (* Compare against a baseline this test sets, never the ambient one.
         Every Refute call above has already used a quiet window, so a
         window that fails to give a flag back leaves it false here -- and
         a test that read the flag as its own baseline would then compare
         false against false and pass on the strength of the leak. *)
      Portable.finally restore (fn () =>
        let
          val _ = Feedback.emit_INFO := true
          val _ = Globals.notify_on_tyvar_guess := true
          val held = Refute_EvalEnum.held_bracket (fn () => ())
          val _ = Refute_EvalEnum.start_held_bracket held (fn () => ())
          val held_info = !Feedback.emit_INFO
          val held_tyvar = !Globals.notify_on_tyvar_guess
          val _ = Refute_EvalEnum.close_held_bracket held
          val quiet =
            Refute_EvalEnum.quiet_theory_work (fn () => !Feedback.emit_INFO)
          val after_info = !Feedback.emit_INFO
          val after_tyvar = !Globals.notify_on_tyvar_guess
          val restored_after_raise =
            (Refute_EvalEnum.quiet_theory_work
               (fn () => raise Fail "quiet_theory_work"); false)
            handle Fail _ => !Feedback.emit_INFO
        in
          held_info andalso held_tyvar andalso
          after_info andalso after_tyvar andalso
          not quiet andalso restored_after_raise
        end) ()
    end)

val _ = test "trace 2 reports selection and the race" (fn () =>
  let
    val (_, selection) = capture 2 (fn () =>
      refute (exhaustive |> upd_size 2 |> upd_quiet false)
             ``(r : rg_record) = s``)
    val (outcome, race) = capture 2 (fn () =>
      refute (default_config |> upd_size 0 |> upd_timeout 10.0) ``T``)
  in
    List.all (fn needle => String.isSubstring needle selection)
      ["native is inapplicable: custom generator registered",
       "selected compute"] andalso
    outcome == NoCounterexample andalso
    List.all (fn needle => String.isSubstring needle race)
      ["Refute backend started (weight 20): exhaustive",
       "Refute backend started (weight 30): random",
       "Refute backend started (weight 40): narrowing"] andalso
    (not kodkodi_configured orelse
     String.isSubstring "Refute backend started (weight 50): kodkod" race)
  end)

(* ------------------------------------------------------------------- *)
(* Function-recursive datatypes                                        *)
(* ------------------------------------------------------------------- *)

val _ = section "function-recursive datatypes"

val itree_true =
  ``!(t : (num, bool, num) itree$itree).
      itree$itree_CASE t (\r:num. T) T
        (\e:bool f:num->(num,bool,num)itree$itree. T)``

val _ = test "exhaustive refuses, random searches" (fn () =>
  unknown_with "recursive under a function type"
    (refute exhaustive
       ``!(t : (num, bool, num) itree$itree). (t = itree$Ret 0) \/
                                              (t <> itree$Ret 0)``) andalso
  genuine (refute random ``!(t : (num, bool, num) itree$itree).
                             t = itree$Ret 0``) andalso
  unknown_with "before finitization"
    (refute (nar |> upd_size 2)
            ``(left : (num, bool, num) itree$itree) = right``))

val _ = test "random never claims NoCounterexample for itree" (fn () =>
  let
    val cfg = random |> upd_size 2 |> upd_iterations 20 |> upd_seed (SOME 1)
      |> upd_timeout 3.0
    val outcome = refute cfg itree_true
  in
    unknown_with "random search exhausted" outcome andalso
    not (unknown_with "search timed out" outcome) andalso
    ((ignore (refute (cfg |> upd_expect ExpectNone) itree_true); false)
     handle e as Feedback.HOL_ERR _ =>
       String.isSubstring "random search exhausted"
         (Feedback.exn_to_string e))
  end)

(* ------------------------------------------------------------------- *)
(* Rationals and reals                                                 *)
(* ------------------------------------------------------------------- *)

val _ = section "rat and real"

val compute10 = exhaustive |> upd_size 10 |> upd_substrate Compute
val not_exhausted_10 =
  Unknown ["exhaustive: search space not exhausted",
           "exhaustive: searched up to size 10"]

fun compute_certified outcome =
  cex_where (fn c => #substrate c = "compute" andalso is_genuine c andalso
                     Option.isSome (#cert c)) outcome

fun numeral_display tm =
  let
    val text = Parse.term_to_string tm
    val body = if String.isPrefix "-" text orelse String.isPrefix "~" text
               then String.extract (text, 1, NONE) else text
  in
    List.all (fn c => Char.isDigit c orelse c = #"/" orelse c = #" ")
      (String.explode body) andalso
    not (String.isSubstring "abs_rat" text) andalso
    not (String.isSubstring "abs_frac" text)
  end

val _ = test "rat operations are decidable under Auto" (fn () =>
  List.all (fn goal => compute_certified (refute qc goal))
    [``(x : rat) = rat_of_num 0``, ``!x y : rat. x <= y``,
     ``!x y : rat. x >= y``, ``!x : rat. x > 0``, ``!x y : rat. x < y``,
     ``!x : rat. x + 1 = x``, ``!x : rat. x - 1 = x``, ``!x : rat. x * 2 = x``,
     ``!x : rat. x / 2 = x``, ``!x : rat. rat$rat_ainv x = x``,
     ``!x : rat. rat$rat_minv x = x``])

val _ = test "real operations are decidable under Auto" (fn () =>
  List.all (fn goal => compute_certified (refute qc goal))
    [``(x : real) = real_of_num 0``, ``!x y : real. x <= y``,
     ``!x y : real. x >= y``, ``!x : real. x > 0``, ``!x y : real. x < y``,
     ``!x : real. x + 1 = x``, ``!x : real. x - 1 = x``,
     ``!x : real. x * 2 = x``, ``!x : real. x / 2 = x``,
     ``!x : real. abs x = x``, ``!x : real. x pow 2 = x``])

val _ = test "rat and real searches are never exhausted" (fn () =>
  refute compute10 ``!x : rat. x < x + 1`` == not_exhausted_10 andalso
  refute compute10 ``!x : real. x < x + 1`` == not_exhausted_10 andalso
  refute compute10 ``!x : rat. x <= x`` == not_exhausted_10 andalso
  refute compute10 ``!x : real. x <= x`` == not_exhausted_10 andalso
  refute (compute10 |> only [Random]) ``!x : rat. x < x + 1``
    == Unknown ["random: random search exhausted",
               "random: searched up to size 10"] andalso
  refute (compute10 |> only [Random]) ``!x : real. x < x + 1``
    == Unknown ["random: random search exhausted",
               "random: searched up to size 10"])

val _ = test "rat and real witnesses display as numerals" (fn () =>
  List.all (fn goal =>
    refute qc goal |> cex_where (fn c =>
      case #bindings c of [(_, v)] => numeral_display v | _ => false))
    [``(x : rat) = rat_of_num 1``, ``(x : real) = real_of_num 1``] andalso
  List.all (fn goal =>
    refute qc goal |> cex_where (fn c =>
      is_genuine c andalso Option.isSome (#cert c) andalso
      length (#bindings c) = 4 andalso
      List.all (numeral_display o #2) (#bindings c) andalso
      List.exists (fn (_, v) =>
        let val t = Parse.term_to_string v in
          String.isPrefix "-" t orelse String.isPrefix "~" t
        end) (#bindings c)))
    [``!a b c d : rat. a <= b /\ c <= d ==> a * c <= b * d``,
     ``!a b c d : real. a <= b /\ c <= d ==> a * c <= b * d``])

val _ = test "closed rat and real goals are decided" (fn () =>
  List.all (fn goal =>
    refute compute10 goal == NoCounterexample andalso
    refute (compute10 |> only [Random]) goal == NoCounterexample andalso
    refute (default_config |> quiet) goal == NoCounterexample)
    [``rat_of_num 2 * rat_of_num 3 = rat_of_num 6``,
     ``inv (2 : real) * 2 = 1``])

(* ------------------------------------------------------------------- *)
(* Words, type-variable instantiation, subtype transport               *)
(* ------------------------------------------------------------------- *)

val _ = section "words and instantiation"

val word_goal = ``(w : 'a word) + 1w <> 0w``
val poly_goal = ``(!x y:'a. x = y) ==> (!x y:'b. x = y)``
val proxies_reason =
  "polymorphic search covered only configured monomorphic proxies"

fun witness_width outcome =
  case first_cex outcome of
      SOME {bindings = [(_, v)], ...} =>
        SOME (fcpSyntax.dest_int_numeric_type (wordsSyntax.dim_of v))
    | _ => NONE

val _ = test "word widths are instantiated from the widths row" (fn () =>
  refute (qc |> upd_timeout 30.0) word_goal |> cex_where (fn c =>
    is_genuine c andalso
    (case #cert c of
         SOME thm => null (Term.type_vars_in_term (Thm.concl thm))
       | NONE => false)) andalso
  Lib.mem (witness_width (refute (qc |> upd_finite_types false
                                    |> upd_widths [2, 5, 7])
                                 word_goal)) [SOME 2, SOME 5, SOME 7] andalso
  unknown_with proxies_reason
    (refute (qc |> upd_timeout 30.0) ``w2n (w : 'a word) < 16``))

val _ = test "instantiate pins type variables" (fn () =>
  let val cfg = qc |> upd_timeout 30.0 in
    unknown_with proxies_reason (refute cfg poly_goal) andalso
    genuine (refute (cfg |> upd_instantiate [(SOME ``:'a``, ``:refute$rf1``),
                                             (SOME ``:'b``, ``:refute$rf2``)])
                    poly_goal) andalso
    unknown_with proxies_reason
      (refute (cfg |> upd_instantiate [(NONE, ``:refute$rf1``)]) poly_goal)
    andalso
    refute (cfg |> upd_instantiate [(SOME ``:'a``, ``:refute$rf1``)])
           ``(!x y:'a. x = y) ==> (!u v:'b. u = v)``
    |> cex_where (fn c =>
         is_genuine c andalso not (null (#bindings c)) andalso
         not (List.exists (fn (_, v) => Type.compare (Term.type_of v,
                                                       ``:refute$rf1``) = EQUAL)
                          (#bindings c)))
  end)

val _ = test "instantiate errors are reported" (fn () =>
  let
    val cfg = qc |> upd_timeout 30.0
    val absent =
      refute (cfg |> upd_instantiate [(SOME ``:'c``, ``:refute$rf1``)])
                        poly_goal
    val no_gen = refute (cfg |> upd_instantiate [(SOME ``:'a``, ``:ind``),
                                                 (SOME ``:'b``, ``:bool``)])
                        poly_goal
    fun message f = (ignore (f ()); "")
                    handle Feedback.HOL_ERR e => Feedback.message_of e
  in
    unknown_with "does not occur in the goal" absent andalso
    not (unknown_with "Exception raised" absent) andalso
    not (unknown_with "\n" absent) andalso
    unknown_with "no TypeBase information" no_gen andalso
    unknown_with (Parse.type_to_string ``:ind``) no_gen andalso
    message (fn () => upd_instantiate [(SOME ``:bool``, ``:num``)]
                                      default_config)
      = "instantiate row key must be a type variable; got: " ^
        Parse.type_to_string ``:bool`` andalso
    message (fn () => upd_instantiate [(SOME ``:'a``, ``:'b list``)]
                                      default_config)
      = "instantiate row value must be a ground type (no type variables); " ^
        "got: " ^ Parse.type_to_string ``:'b list``
  end)

val _ = test "word width variables need a width pin" (fn () =>
  unknown_with "must be pinned to a concrete word-width type"
    (refute (qc |> upd_instantiate [(SOME ``:'a``, ``:bool``)]) word_goal)
  andalso
  witness_width (refute (qc |> upd_instantiate
                                [(SOME ``:'a``,
                                  fcpSyntax.mk_int_numeric_type 5)])
                        word_goal) = SOME 5 andalso
  Lib.mem (witness_width (refute (qc |> upd_instantiate
                                         [(NONE, ``:refute$rf1``)])
                                 word_goal))
          [SOME 1, SOME 2, SOME 3, SOME 4])

val _ = test "word types are classified before encoding" (fn () =>
  let
    val cfg = default_config |> quiet |> upd_timeout 2.0 |> only [ModelFinder]
    fun says goal message =
      Lib.mem ("kodkod: " ^ message) (reasons_of (refute cfg goal))
  in
    says ``(c : ('a, 'b) cart) = d``
      ("cart type " ^ Parse.type_to_string ``:('a, 'b) cart`` ^
       " is not encoded; only word types are") andalso
    says ``(w : 'a word) = v``
      ("word type " ^ Parse.type_to_string ``:'a word`` ^
       " has no concrete width")
  end)

val _ = section "use_subtype"

val small = qc |> upd_timeout 10.0 |> upd_size 5
val transport = small |> upd_use_subtype true
val three_goal = ``!x : zoo_three. zoo_three_rep x <> 2``

fun names_abs (c : counterexample) =
  case #bindings c of
      [(x, v)] => #1 (Term.dest_var x) = "x" andalso
                  Type.compare (Term.type_of x, ``:zoo_three``) = EQUAL andalso
                  Term.aconv v ``zoo_three_abs 2``
    | _ => false

val _ = test "transport reaches a typedef through its representation"
  (fn () =>
    unknown_with "no TypeBase information" (refute small three_goal) andalso
    refute transport three_goal |> cex_where (fn c => is_genuine c andalso
                                                       names_abs c) andalso
    refute (transport |> only [Narrowing]) three_goal
    |> cex_where (fn c => is_genuine c andalso uncertified c andalso
                          names_abs c))

val _ = test "transport is bounded and sound" (fn () =>
  let
    fun off_on goal =
      (refute small goal, refute transport goal)
    fun bounded (off, on) rep =
      is_unknown off andalso is_unknown on andalso
      unknown_with ("not executable: " ^ rep) off andalso
      unknown_with "no narrowing generator for" off andalso
      not (unknown_with "searched up to size" off) andalso
      unknown_with "searched up to size" on andalso
      not (unknown_with ("not executable: " ^ rep) on) andalso
      not (unknown_with "no narrowing generator for" on)
  in
    bounded (off_on ``!x : zoo_three. zoo_three_rep x <> 3``) "zoo_three_rep"
    andalso
    bounded (off_on ``!x : zoo_univ. EVEN (zoo_univ_rep x) \/
                                     ODD (zoo_univ_rep x)``) "zoo_univ_rep"
    andalso
    refute transport ``!x : zoo_three. zoo_three_rep x < 3`` == NoCounterexample
    andalso
    (case off_on ``!t : zoo_tree. t <> ZooLeaf 0`` of
         (Counterexample (a :: _), Counterexample (b :: _)) =>
           is_genuine a andalso same_bindings a b
       | _ => false) andalso
    (case off_on ``!x : zoo_unharvested. zoo_unharvested_rep x <> 2`` of
         (Unknown a, Unknown b) => a = b
       | _ => false) andalso
    (case (refute (qc |> upd_timeout 10.0)
                  ``!xs : zoo_three list. LENGTH (xs ++ xs) = 2 * LENGTH xs``,
           refute (qc |> upd_timeout 10.0 |> upd_use_subtype true)
                  ``!xs : zoo_three list. LENGTH (xs ++ xs) = 2 * LENGTH xs``)
       of (Unknown a, Unknown b) =>
            a = b andalso List.exists (String.isSubstring
                                         "no TypeBase information") a
        | _ => false)
  end)

val _ = test "a registered generator beats transport" (fn () =>
  (register_generator ``:zoo_univ``
     {enumerate = SOME (fn _ => [``zoo_univ_abs 7``]),
      random = SOME (fn _ => fn state => (``zoo_univ_abs 7``, state))};
   unknown_with "not executable: zoo_univ_rep"
     (refute transport ``!x : zoo_univ. zoo_univ_rep x <> 7``)))

(* ------------------------------------------------------------------- *)
(* Unused assumptions                                                  *)
(* ------------------------------------------------------------------- *)

val _ = section "unused assumptions"

val unused_cfg = default_config |> only [Exhaustive, Random]
  |> upd_substrate Compute |> upd_size 2 |> upd_iterations 20
  |> upd_timeout 2.0

val _ = test "find_unused_assms reports antichains of unused premises"
  (fn () =>
    find_unused_assms (SOME unused_cfg) "refuteUnused" =
      [("conjunctive_assumption", SOME []),
       ("incomparable_maximals", SOME [[0, 1], [2]]),
       ("needed_assumption", SOME []),
       ("no_assumptions", NONE),
       ("one_unused_assumption", SOME [[1]]),
       ("two_unused_assumptions", SOME [[0, 1]])] andalso
    check_unused_assms (SOME unused_cfg)
      ("one", refuteUnusedTheory.one_unused_assumption) = ("one", SOME [[1]]))

val _ = test "check_unused_assms NONE uses a quickcheck-only profile"
  (fn () =>
    let
      val enabled = ref false
      val seen = ref false
      val _ = register_backend (stub "selftest-unused-registry" ~89 enabled
        (fn _ => fn _ => (seen := true; Unknown ["registry"])))
      val theorem = ("selection", refuteUnusedTheory.needed_assumption)
    in
      with_enabled [enabled] (fn () =>
        Lib.with_flag (the_config,
          default_config |> upd_search AllBackends |> upd_substrate Compute
            |> upd_size 2 |> upd_timeout 2.0)
          (fn () =>
            (seen := false;
             check_unused_assms NONE theorem = ("selection", SOME []) andalso
             not (!seen) andalso
             check_unused_assms (SOME (!the_config)) theorem
               = ("selection", SOME []) andalso
             !seen)) ())
    end)

val _ = test "probes are quiet, sequential and never expectant" (fn () =>
  let
    val enabled = ref false
    val profile = ref false
    val _ = register_backend (stub "selftest-unused-profile" ~88 enabled
      (fn config => fn _ =>
        (profile := (#sequential config andalso #quiet config andalso
                     #abort_potential config andalso
                     #expect config = NoExpectation);
         Feedback.HOL_MESG "profile output"; NoCounterexample)))
    val cfg = default_config
      |> only [RegisteredBackend "selftest-unused-profile"]
      |> upd_sequential false |> upd_abort_potential false
      |> upd_quiet false |> upd_expect ExpectNone
    val (result, text) = with_enabled [enabled] (fn () =>
      capture 4 (fn () =>
        check_unused_assms (SOME cfg)
          ("profile", refuteUnusedTheory.needed_assumption)))
  in
    result = ("profile", SOME [[0]]) andalso !profile andalso text = ""
  end)

val _ = test "print_unused_assms counts inconclusive probes" (fn () =>
  let
    val enabled = ref false
    val _ = register_backend (stub "selftest-unused-unknown" ~91 enabled
      (fn _ => fn _ => Unknown ["probe"]))
    val cfg = default_config
      |> only [RegisteredBackend "selftest-unused-unknown"]
      |> upd_timeout 1.0
    val (_, text) = with_enabled [enabled] (fn () =>
      capture 4 (fn () => print_unused_assms (SOME cfg) (SOME "refuteUnused")))
  in
    List.all (fn needle => String.isSubstring needle text)
      ["Found 0 theorems", "Checked 5 theorems with assumptions (6 total)",
       "Skipped 9 inconclusive probes."]
  end)

(* ------------------------------------------------------------------- *)
(* Model finder                                                        *)
(* ------------------------------------------------------------------- *)

val _ = section "model finder"

val hand_gfp_and_def = TotalDefn.Define
  `hand_gfp_and = fixedPoint$gfp (\X (b:bool). b /\ X b)`
val hand_lfp_or_def = TotalDefn.Define
  `hand_lfp_or = fixedPoint$lfp (\X (b:bool). b \/ X b)`
val poly_lfp_top_def = TotalDefn.Define
  `poly_lfp_top = fixedPoint$lfp (\X (x:'a). (?y. y = x) \/ X x)`
val hand_lfp_noise_def = TotalDefn.Define
  `hand_lfp_noise = fixedPoint$lfp (\X (x:bool). ~ X x)`

fun kodkod_genuine (c : counterexample) =
  #backend c = "kodkod" andalso is_genuine c
fun model_genuine c =
  kodkod_genuine c andalso uncertified c andalso Option.isSome (#model c)

fun is_iterator_type ty =
  (Type.is_vartype ty andalso
   (String.isPrefix "'refute$lfpit" (Type.dest_vartype ty) orelse
    String.isPrefix "'refute$gfpit" (Type.dest_vartype ty))) orelse
  (case Lib.total Type.dest_thy_type ty of
       SOME {Thy = "refute", Tyop = "bisim_iterator", ...} => true
     | _ => false)

fun iterator_card (c : counterexample) =
  case #scope c of
      SOME rows => Option.map #2 (List.find (is_iterator_type o #1) rows)
    | NONE => NONE

val mf_num2 = mf |> upd_card [(SOME ``:num``, [2]), (NONE, [1])]
val mf_num3 = mf |> upd_card [(SOME ``:num``, [3]), (NONE, [1])]

val _ = test "unregistered typedefs are reported without kodkodi" (fn () =>
  List.all (fn goal =>
    case refute (mf |> upd_timeout 2.0) goal of
        Unknown [reason] =>
          String.isSuffix
            "unregistered typedef zoo_unharvested: register with \
            \Refute.register_typedef" reason
      | _ => false)
    [``zoo_unharvested_abs 0 = (x : zoo_unharvested)``,
     ``zoo_unharvested_wrapper T 0 = (x : zoo_unharvested)``])

val _ = mf_test "kodkod refutes and certifies a numeric goal" (fn () =>
  refute mf_num2 ``(x : num) = 0`` |> cex_where (fn c =>
    kodkod_genuine c andalso #substrate c = "kodkod" andalso
    Option.isSome (#cert c)))

(* [zoo_simp_neg]'s negated [refute_simp] clause restates it, replacing the
   DefnBase equations, so [zoo_simp_neg 0] is unconstrained and models of
   this true goal are found and then discarded.  Keyed on [bool$~] instead
   the restatement goes unrecognised, the definition survives, and the goal
   reduces to [0 = 0] -- [NoCounterexample], which is what this pin
   excludes.  One card keeps the search under a second, so the answer here
   is never a timeout. *)
val _ = mf_test "a negated refute_simp clause keys on its head constant"
  (fn () => unknown_with "discarded"
              (refute (mf |> upd_card [(NONE, [2])]) ``zoo_simp_neg 0``))

(* Kodkodi writes an external SAT solver's CNF file itself and never
   deletes it, so nothing may be left where the user started HOL. *)
val external_sat_solvers =
  [("MiniSat", "MINISAT_HOME", "minisat"),
   ("CryptoMiniSat", "CRYPTOMINISAT_HOME", "cryptominisat"),
   ("zChaff", "ZCHAFF_HOME", "zchaff"),
   ("RSat", "RSAT_HOME", "rsat"),
   ("Riss3g", "RISS3G_HOME", "riss3g")]

fun external_sat_ready (_, home, executable) =
  case OS.Process.getEnv home of
      NONE => false
    | SOME directory =>
        (OS.FileSys.access (OS.Path.concat (directory, executable),
           [OS.FileSys.A_READ, OS.FileSys.A_EXEC])
         handle OS.SysErr _ => false)

fun cnf_files_here () =
  let
    val stream = OS.FileSys.openDir (OS.FileSys.getDir ())
    fun collect names =
      case OS.FileSys.readDir stream of
          NONE => names
        | SOME name =>
            collect (if String.isSuffix ".cnf" name then name :: names
                     else names)
  in
    Portable.finally (fn () => OS.FileSys.closeDir stream)
      (fn () => collect []) ()
  end

val cnf_hygiene = "an external SAT solver leaves no CNF file in the cwd"

val _ =
  case List.find external_sat_ready external_sat_solvers of
      NONE => skip cnf_hygiene "no external SAT solver configured"
    | SOME (solver, _, _) =>
        if not kodkodi_configured then
          skip cnf_hygiene "kodkodi not configured"
        else
          test cnf_hygiene (fn () =>
            let
              val existing = cnf_files_here ()
              val result =
                refute (mf_num2 |> upd_sat_solver solver) ``(x : num) = 0``
            in
              (* The verdict pins that Kodkodi really ran: a skipped or
                 failed search would pass the file check vacuously. *)
              cex_where kodkod_genuine result andalso
              Portable.set_diff (cnf_files_here ()) existing = []
            end)

val _ = mf_test "whack keeps a certified counterexample" (fn () =>
  refute (mf_num2 |> upd_whack [``I : 'a -> 'a``])
         ``(n : num) = 0 /\ (I T \/ ~(I T))``
  |> cex_where (fn c => kodkod_genuine c andalso Option.isSome (#cert c)))

val _ = mf_test "inductive predicates: direct, unrolled, star-linear"
  (fn () =>
    refute mf_num3 ``zoo_wf_lfp n ==> n = 0`` |> cex_where model_genuine
    andalso
    refute (mf_num3 |> upd_star_linear_preds false
              |> upd_iter [(SOME ``zoo_unroll_lfp : num -> bool``, [2]),
                           (NONE, [0])])
           ``~zoo_unroll_lfp 2``
    |> cex_where (fn c => model_genuine c andalso iterator_card c = SOME 3)
    andalso
    refute (mf_num3 |> upd_wf [(SOME ``zoo_wf_lfp : num -> bool``, SOME false)]
              |> upd_star_linear_preds true |> upd_binary_ints (SOME false))
           ``zoo_wf_lfp 2 ==> (2 : num) = 0``
    |> cex_where (fn c => model_genuine c andalso iterator_card c = NONE))

val _ = mf_test "coinductive predicates are unrolled" (fn () =>
  refute (mf |> upd_iter [(SOME ``zoo_guarded_gfp : bool -> bool``, [2]),
                          (NONE, [0])])
         ``zoo_guarded_gfp F``
  |> cex_where (fn c => model_genuine c andalso iterator_card c = SOME 2)
  andalso
  refute (mf |> upd_iter [(SOME ``zoo_mutual_gfp : bool -> bool``, [2]),
                          (NONE, [0])])
         ``zoo_mutual_gfp F \/ zoo_mutual_other_gfp F``
  |> cex_where model_genuine)

val _ = mf_test "relation operators are encoded" (fn () =>
  let val cfg = mf_num2 |> upd_binary_ints (SOME false) in
    refute cfg ``~RTC (\x : num. \y : num. x = 0 /\ y = 1) 0 1``
      |> cex_where model_genuine andalso
    refute cfg ``~(inv (\n : num. \b : bool. n = 0 /\ b) T 0 /\
                   (((\b : bool. \n : num. b /\ n = 1) O
                     (\n : num. \b : bool. n = 0 /\ b)) 0 1))``
      |> cex_where model_genuine
  end)

val _ = mf_test "hand-rolled fixed points are recognised" (fn () =>
  let
    val cfg = mf |> upd_timeout 60.0
    fun refuted goal = genuine (refute cfg goal)
    fun holds goal = refute cfg goal == NoCounterexample
    val (_, text) = capture 2 (fn () => refute (cfg |> upd_quiet false)
                                               ``~ hand_lfp_noise F``)
  in
    refuted ``hand_gfp_and F`` andalso holds ``~hand_gfp_and F`` andalso
    refuted ``hand_lfp_or F`` andalso holds ``~hand_lfp_or F`` andalso
    holds ``hand_lfp_or T`` andalso
    holds ``poly_lfp_top T`` andalso
    holds ``poly_lfp_top ((T, F) : bool # bool)`` andalso
    refuted ``poly_lfp_top T ==> ~ poly_lfp_top ((T, F) : bool # bool)``
    andalso
    holds ``hand_lfp_noise F`` andalso holds ``!x. hand_lfp_noise x`` andalso
    refuted ``~ hand_lfp_noise F`` andalso
    String.isSubstring "monoton" text andalso
    String.isSubstring "hand_lfp_noise" text
  end)

val _ = mf_test "the model finder leaves the theory untouched" (fn () =>
  let val baseline = footprint () in
    List.all (fn goal => (ignore (refute mf goal); footprint () = baseline))
      [``zoo_wf_lfp n``, ``zoo_nonwf_lfp n``, ``zoo_mutual_lfp n``,
       ``zoo_mutual_nonwf_lfp n``]
  end)

val word_cfg = mf |> upd_timeout 60.0
  |> upd_card [(SOME ``:num``, [8]), (NONE, [1])]

val _ = mf_test "word carriers are exact" (fn () =>
  genuine (refute word_cfg ``!w : 3 word. w = 0w``) andalso
  refute word_cfg ``(w : 2 word) = 0w \/ w = 1w \/ w = 2w \/ w = 3w``
    == NoCounterexample)

val _ = mf_test "word operations are encoded" (fn () =>
  List.all (fn goal => refute word_cfg goal |> cex_where kodkod_genuine)
    [``(w : 3 word) + 1w = w``, ``(w : 3 word) * 2w <> w + w``,
     ``-(w : 3 word) <> 0w - w``, ``(w : 3 word) <+ 0w``,
     ``(4w : 3 word) < 0w ==> F``, ``(w : 3 word) && 0w <> 0w``,
     ``(w : 3 word) << 5 <> 0w``, ``w2n (7w : 3 word) <> 7``])

val _ = mf_test "unencoded word operations are refused by name" (fn () =>
  unknown_with "word operation words$w2w is not encoded"
    (refute word_cfg ``w2w (w : 3 word) = (0w : 4 word)``) andalso
  unknown_with "word operation words$word_rol is not encoded"
    (refute word_cfg ``(w : 3 word) #<< 1 = w``) andalso
  unknown_with "word operations are not encoded with binary integers"
    (refute (word_cfg |> upd_binary_ints (SOME true) |> upd_bits [4])
            ``(w : 3 word) * 2w <> w + w``))

val carrier = default_config |> quiet |> only [ModelFinder]
  |> upd_timeout 60.0 |> upd_max_threads 1

val _ = mf_test "chars are an exact carrier of 256 literals" (fn () =>
  refute carrier ``(c : char) = c'`` |> cex_where (fn c =>
    scope_of c ``:char`` = SOME 256 andalso scope_of c ``:num`` = NONE andalso
    not (null (#bindings c)) andalso
    List.all (fn (_, v) => String.isPrefix "#\"" (Parse.term_to_string v))
      (#bindings c)) andalso
  refute carrier ``STRCAT s "a" = s`` |> cex_where kodkod_genuine andalso
  List.all (fn goal => refute carrier goal |> cex_where kodkod_genuine)
    [``CHR 1 = CHR 2``, ``ORD (CHR 1) <> 1``, ``char_lt (CHR 2) (CHR 1)``,
     ``char_ge (CHR 1) (CHR 2)``] andalso
  List.all (fn goal => refute carrier goal == NoCounterexample)
    [``char_lt (CHR 1) (CHR 2)``, ``char_le (c : char) c``])

val _ = mf_test "typedefs over num are refuted" (fn () =>
  refute carrier ``(a : zoo_four) = b`` |> cex_where kodkod_genuine andalso
  refute (carrier |> upd_binary_ints (SOME true)
            |> upd_card [(SOME ``:num``, [4]), (NONE, [3])])
         ``(a : zoo_three) = b``
  |> cex_where (fn c =>
       not (null (#bindings c)) andalso
       List.all (fn (_, v) =>
         let val text = Parse.term_to_string v in
           String.isSubstring "zoo_three_abs" text andalso
           not (String.isSubstring "refute$" text)
         end) (#bindings c)) andalso
  bounds_clean (refute (carrier |> upd_binary_ints (SOME true)
                          |> upd_card [(SOME ``:num``, [3]), (NONE, [3])])
                       ``(a : zoo_three) = b``))

val _ = mf_test "a typedef stated as two halves is harvested" (fn () =>
  refute carrier ``(a : refute_harvest_split) = b`` |> cex_where kodkod_genuine
  andalso
  let
    val outcome =
      refute (carrier |> upd_card [(SOME ``:refute_harvest_split``, [2]),
                                   (NONE, [1, 2, 3, 4])])
             ``refute_harvest_split_home_abs
                 (refute_harvest_split_home_rep a) = a``
  in
    not (genuine outcome) andalso
    (not (is_unknown outcome) orelse
     (bounds_clean outcome andalso
      unknown_with "card refute_harvest_split = 2" outcome))
  end)

val _ = mf_test "a partial card row keeps the other defaults" (fn () =>
  refute (carrier |> upd_card [(SOME ``:num``, [4])])
         ``(n : num) = 0 /\ (b : bool)``
  |> cex_where (fn c => scope_of c ``:num`` = SOME 4) andalso
  is_cex (refute (carrier |> upd_card [(SOME ``:char``, [2])])
                 ``(c : char) = c'``))

val _ = mf_test "genuine_only keeps a certified model" (fn () =>
  refute (mf |> upd_genuine_only true |> upd_card [(NONE, [1])])
         ``!b : bool. b``
  |> cex_where (fn c => is_genuine c andalso certifies ``!b : bool. b`` c))

val _ = mf_test "proper-subset typedefs have countermodels" (fn () =>
  (register_typedef {ty = ``:zoo_three``, abs = ``zoo_three_abs``,
                     rep = ``zoo_three_rep``, absrep_thms = [zoo_three_absrep]};
   is_cex (refute mf ``zoo_three_abs (zoo_three_rep x) = (y : zoo_three)``)))

val _ = mf_test "a quasi-genuine model survives max_potential 0" (fn () =>
  refute (mf |> upd_wf [(NONE, SOME true)] |> upd_max_potential 0)
         ``zoo_wf_lfp n ==> n = 0`` |> cex_where is_quasi)

val _ = mf_test "NoCounterexample is a whole-space claim" (fn () =>
  let val cfg = mf |> upd_timeout 20.0 in
    (let val outcome = refute (cfg |> upd_card [(NONE, [1])]) ``(x : 'a) = y``
     in bounds_clean outcome andalso unknown_with "searched up to size" outcome
     end) andalso
    is_cex (refute cfg ``(x : 'a) = y``) andalso
    refute cfg ``(SND (SND p, FST p), FST (SND p, FST p)) = (p : num # bool)``
      == NoCounterexample andalso
    refute (cfg |> upd_card [(NONE, [3])])
           ``(x : rg_enum) = RGRed \/ x = RGGreen \/ x = RGBlue``
      == NoCounterexample andalso
    is_unknown (refute (cfg |> upd_card [(SOME ``:rg_enum``, [3, 1]),
                                         (SOME ``:rg_triad``, [1, 3]),
                                         (NONE, [1, 1])]
                          |> upd_mono [(SOME ``:rg_enum``, SOME true),
                                       (SOME ``:rg_triad``, SOME true),
                                       (NONE, NONE)])
                       ``(a1 : rg_enum) = a2 \/ a1 = a3 \/ a2 = a3 \/
                         (b1 : rg_triad) = b2 \/ b1 = b3 \/ b2 = b3``)
    andalso
    (case refute (cfg |> upd_falsify false) ``T`` of
         Model (_ :: _) => true
       | _ => false) andalso
    refute (cfg |> upd_falsify false) ``F`` == NoModel andalso
    bounds_clean (refute (cfg |> upd_card [(NONE, [3])])
      ``($@ (\x : rg_enum. x = RGRed) = RGRed) \/
        ($@ (\x : rg_enum. x = RGRed) = RGGreen) \/
        ($@ (\x : rg_enum. x = RGRed) = RGBlue)``)
  end)

val _ = mf_test "NoCounterexample preempts an auxiliary model search"
  (fn () =>
    refute (mf |> only [Exhaustive, ModelFinder] |> upd_falsify false) ``T``
    == NoCounterexample)

val _ = mf_test "well-foundedness over infinite types is only Potential"
  (fn () =>
    refute (mf |> upd_timeout 20.0 |> upd_card [(SOME ``:num``, [3]),
                                                 (NONE, [1, 2, 3])]
              |> upd_max_potential 1)
           ``WF (R : num -> num -> bool) ==> transitive R``
    |> single_cex_where is_potential andalso
    refute (mf_wide |> upd_timeout 60.0) ``mf_wf_sortedp (xs : num list) ==>
                                      LENGTH xs <= 8``
    |> single_cex_where (fn c => is_genuine c andalso Option.isSome (#cert c)))

val _ = mf_test "true set and recursion facts are bounds-clean" (fn () =>
  let val cfg = mf |> upd_timeout 30.0 in
    List.all (fn goal =>
      let val outcome = refute cfg goal in
        bounds_clean outcome andalso unknown_with "card num list" outcome
      end)
      [``SUM_IMAGE (\e:num. e) ({0; 1; 2} : num set) = 3``,
       ``SUM_SET ({0; 1; 2} : num set) = 3``] andalso
    bounds_clean (refute cfg ``x <> y ==> CARD {x; y} = 2``) andalso
    bounds_clean (refute (cfg |> upd_user_axioms (SOME false)
                            |> upd_timeout 90.0 |> upd_card [(NONE, [1, 2, 3])])
      ``WFREC ($< : num -> num -> bool)
          (\f n. if n = 0 then [] else (n - 1) :: f (n - 1)) 1 = [0]``)
  end)

val _ = mf_test "WFREC over a decided relation is Genuine and sound" (fn () =>
  let
    val cfg = mf |> upd_binary_ints (SOME false) |> upd_timeout 60.0
      |> upd_card [(NONE, [1, 2, 3, 4])]
    fun wfrec k = ``!x:bool. WFREC (\x y. (x = F) /\ (y = T))
                      (\f (b:bool). if b then (1:num) + f F else 0) x <> ^k``
  in
    refute cfg (wfrec ``1 : num``) |> single_cex_where is_genuine andalso
    is_unknown (refute cfg (wfrec ``2 : num``))
  end)

val _ = mf_test "a proposition and its negation are never both certified"
  (fn () =>
    let
      val cfg = mf |> upd_binary_ints (SOME false) |> upd_timeout 90.0
        |> upd_card [(NONE, [1, 2, 3])]
      val goal = ``WFREC (\x y:bool. T) (\f (b:bool). ~ f b) T``
      fun finished outcome =
        not (is_unknown outcome) orelse
        (bounds_clean outcome andalso unknown_with "card bool itself" outcome)
      val pos = refute cfg goal
      val neg = refute cfg (boolSyntax.mk_neg goal)
    in
      finished pos andalso finished neg andalso
      not (pos == NoCounterexample andalso neg == NoCounterexample) andalso
      refute cfg ``~WF (\(x:bool) y. T)`` == NoCounterexample
    end)

val _ = mf_test "Hilbert choice is guarded by scope" (fn () =>
  let
    val cfg = mf |> upd_timeout 30.0
    val choice = cfg
      |> upd_card [(SOME ``:num``, [2]), (NONE, [1, 2, 3, 4, 5, 6])]
      |> upd_max_potential 1 |> upd_binary_ints (SOME false)
  in
    refute cfg ``CARD ({} : 'a set) = 1``
      |> single_cex_where (fn c => is_genuine c andalso uncertified c)
    andalso
    refute choice ``($@ (\j : num. j < 3 /\ j > 3)) <> 0``
      |> single_cex_where is_genuine andalso
    bounds_clean (refute choice ``($@ (\j : num. j = 2 \/ j = 3)) <> 0``)
    andalso
    not (genuine (refute (cfg |> upd_card [(NONE, [3])])
                         ``!z. ((\g. g (\x. x > z /\ x <= SUC z)) $@) <> 0``))
  end)

val _ = mf_test "finite maps have models" (fn () =>
  refute mf flookup_goal |> cex_where (fn c => is_genuine c andalso
                                                uncertified c) andalso
  refute mf_wide ``FLOOKUP (fm : bool |-> bool) x = SOME v ==> x IN FDOM fm``
    == NoCounterexample andalso
  refute mf ``FLOOKUP (fm : bool # bool |-> num) (T,T) = SOME 5``
  |> cex_where (fn c =>
       is_genuine c andalso
       (case #bindings c of
            [(_, value)] =>
              finite_mapSyntax.is_fempty
                (#1 (finite_mapSyntax.strip_fupdate value)) andalso
              List.exists (fn (lhs, recorded) =>
                finite_mapSyntax.is_flookup lhs andalso
                let
                  val key = #2 (finite_mapSyntax.dest_flookup lhs)
                  val thm = computeLib.EVAL_CONV
                              (finite_mapSyntax.mk_flookup (value, key))
                in
                  Term.aconv (boolSyntax.rhs (Thm.concl thm)) recorded
                end) (#evals c)
          | _ => false)))

val _ = mf_test "finite-map application off the domain is unspecified"
  (fn () =>
    List.all (fn goal => refute mf goal =/= NoCounterexample)
      [``(FEMPTY : bool |-> bool) ' T = ARB``,
       ``((FEMPTY : bool |-> bool) |+ (F,T)) ' T = ARB``,
       ``!k. k NOTIN FDOM (fm : bool |-> bool) ==> fm ' k = ARB``] andalso
    List.all (fn goal => refute mf_wide goal == NoCounterexample)
      [``!x. x NOTIN FDOM (fm : bool |-> bool) ==>
             fm ' x = (FEMPTY : bool |-> bool) ' x``,
       ``FLOOKUP (fm1 : bool |-> bool) = FLOOKUP fm2 ==> fm1 = fm2``,
       ``FDOM (FEMPTY : bool |-> bool) = {}``,
       ``FDOM ((fm : bool |-> bool) |+ (T,F)) = T INSERT FDOM fm``,
       ``FLOOKUP (fm : bool |-> bool) x = SOME v ==> fm ' x = v``])

val _ = mf_test "function composition is not refuted" (fn () =>
  not_refuted (refute (mf |> upd_user_axioms (SOME false) |> upd_timeout 90.0
                         |> upd_card [(NONE, [1, 2])])
                      ``((Fn : (bool -> num) -> num) o
                         (g : bool -> bool -> num)) x = Fn (g x)``))

val _ = mf_test "rat facts are bounds-relative without a decision" (fn () =>
  bounds_clean (refute (mf |> upd_binary_ints (SOME true) |> upd_bits [4]
                          |> upd_card [(NONE, [1, 2, 3])])
                       ``rat$rat_add x y = rat$rat_add y (x : rat$rat)``))

(* [zoo_shadow]'s restatement calls itself under a lambda binding its own
   formal name.  Reading that argument as static drops it from the call
   under the lambda, leaving [sp1 <=> sp1] and a free specialized constant
   that falsifies this true goal, so models of it are found where there
   should be none.  The goal quantifies nothing and the type is infinite, so
   a clean search is bounds-relative, never [NoCounterexample]; what the
   defect changes is that models exist at all.  Fixed cards keep this under
   a tenth of a second -- the adaptive default never finishes. *)
val _ = mf_test "a shadowed binder is not a static argument" (fn () =>
  bounds_clean (refute (mf |> upd_card [(NONE, [1, 2, 3])])
                       ``zoo_shadow 3``))

(* ------------------------------------------------------------------- *)
(* Registration APIs                                                   *)
(* ------------------------------------------------------------------- *)

val _ = section "registrations"

fun accepted f = (f (); true) handle Feedback.HOL_ERR _ => false
fun rejected f = (f (); false) handle Feedback.HOL_ERR _ => true
fun rejected_with message f =
  (f (); false) handle Feedback.HOL_ERR e => Feedback.message_of e = message

val _ = test "codatatype registrations are validated" (fn () =>
  let
    fun llist constructors = register_codatatype
      {tyop = {Thy = "llist", Tyop = "llist"},
       case_const = ``llist$llist_CASE``, constructors = constructors,
       witness = NONE}
    val ret = ``itree$Ret``
    val result_args = #Args (Type.dest_thy_type
      (#2 (boolSyntax.strip_fun (Term.type_of ret))))
    val duplicate_ret = Term.inst
      [{redex = List.nth (result_args, 1), residue = hd result_args}] ret
    fun itree constructors = register_codatatype
      {tyop = {Thy = "itree", Tyop = "itree"},
       case_const = ``itree$itree_CASE``, constructors = constructors,
       witness = NONE}
  in
    accepted (fn () => llist [``llist$LNIL``, ``llist$LCONS``]) andalso
    accepted (fn () => register_codatatype
      {tyop = {Thy = "lbtree", Tyop = "lbtree"},
       case_const = ``lbtree$lbtree_case``,
       constructors = [``lbtree$Lf``, ``lbtree$Nd``], witness = NONE}) andalso
    rejected (fn () => llist []) andalso
    rejected (fn () => llist [``llist$LNIL``, ``llist$LNIL``]) andalso
    rejected (fn () => llist [``llist$LNIL``, ``list$NIL``]) andalso
    rejected (fn () => llist [``llist$LNIL``,
                              Term.mk_var ("fake_cons",
                                           Term.type_of ``llist$LCONS``)])
    andalso
    rejected (fn () => register_codatatype
      {tyop = {Thy = "num", Tyop = "num"}, case_const = ``llist$llist_CASE``,
       constructors = [``llist$LNIL``, ``llist$LCONS``], witness = NONE})
    andalso
    rejected (fn () => register_codatatype
      {tyop = {Thy = "min", Tyop = "bool"}, case_const = ``COND``,
       constructors = [``T``, ``F``], witness = NONE}) andalso
    rejected (fn () => register_codatatype
      {tyop = {Thy = "llist", Tyop = "llist"}, case_const = ``list$list_CASE``,
       constructors = [``llist$LNIL``, ``llist$LCONS``], witness = NONE})
    andalso
    rejected (fn () => register_codatatype
      {tyop = {Thy = "lbtree", Tyop = "lbtree"},
       case_const = ``lbtree$lbtree_case``,
       constructors = [``lbtree$Nd``, ``lbtree$Lf``], witness = NONE})
    andalso
    rejected (fn () => itree [duplicate_ret, ``itree$Div``, ``itree$Vis``])
    andalso
    rejected_with "constructor result has the wrong type operator" (fn () =>
      register_codatatype
        {tyop = {Thy = "refuteTableZoo", Tyop = "zoo_nat0"},
         case_const = ``zoo_nat0_CASE``,
         constructors = [``ZooZero``, ``combin$I : zoo_nat0 -> zoo_nat0``],
         witness = NONE}) andalso
    rejected_with
      "constructor is not one of the type's known datatype constructors"
      (fn () => register_codatatype
        {tyop = {Thy = "refuteTableZoo", Tyop = "zoo_nat0"},
         case_const = ``zoo_nat0_CASE``,
         constructors = [``ZooZero``, ``zoo_id``], witness = NONE})
  end)

val _ = test "codatatype witnesses are validated" (fn () =>
  let
    fun stream witness = register_codatatype
      {tyop = {Thy = "refuteTableZoo", Tyop = "zoo_stream"},
       case_const = ``zoo_stream_CASE``, constructors = [``zoo_scons``],
       witness = witness}
    fun nat0 witness = register_codatatype
      {tyop = {Thy = "refuteTableZoo", Tyop = "zoo_nat0"},
       case_const = ``zoo_nat0_CASE``,
       constructors = [``ZooZero``, ``ZooSucc``], witness = witness}
    val non_equation = Thm.EXISTS (``?x:bool. x``, ``T``) boolTheory.TRUTH
    val neither_side = Thm.EXISTS (``?x:'a. (x = x) = T``, ``ARB : 'a``)
      (Drule.EQT_INTRO (Thm.REFL ``ARB : 'a``))
    val abstraction = Thm.EXISTS (``?x:'a. x = (\y:'a. y) x``, ``ARB : 'a``)
      (Thm.SYM (Thm.BETA_CONV ``(\y:'a. y) (ARB : 'a)``))
  in
    accepted (fn () => stream NONE) andalso
    accepted (fn () => stream (SOME zoo_stream_witness)) andalso
    accepted (fn () => stream (SOME zoo_stream_instance_witness)) andalso
    accepted (fn () => stream (SOME zoo_stream_nested_witness)) andalso
    rejected_with "witness theorem has hypotheses" (fn () =>
      stream (SOME (Drule.ADD_ASSUM boolSyntax.T zoo_stream_witness)))
    andalso
    rejected_with "witness head is not one of the registration's constructors"
      (fn () => stream (SOME zoo_stream_non_constructor_witness)) andalso
    rejected_with "witness head is not one of the registration's constructors"
      (fn () => nat0 (SOME zoo_stream_witness)) andalso
    rejected_with "witness must be ?x. <equation>"
      (fn () => stream (SOME boolTheory.TRUTH)) andalso
    rejected_with "witness body must be an equation"
      (fn () => stream (SOME non_equation)) andalso
    rejected_with "witness equation must equate the bound variable with a \
                  \constructor application"
      (fn () => stream (SOME neither_side)) andalso
    rejected_with "witness equation's other side must be a constructor \
                  \application"
      (fn () => stream (SOME abstraction)) andalso
    rejected_with "no argument on the witness's constructor spine is the \
                  \bound variable itself"
      (fn () => register_codatatype
        {tyop = {Thy = "list", Tyop = "list"}, case_const = ``list$list_CASE``,
         constructors = [``list$NIL``, ``list$CONS``],
         witness = SOME zoo_list_free_occurrence_witness}) andalso
    rejected_with "constructor result has the wrong type operator" (fn () =>
      register_codatatype
        {tyop = {Thy = "refuteTableZoo", Tyop = "zoo_nat0"},
         case_const = ``zoo_nat0_CASE``,
         constructors = [``ZooZero``, ``combin$I : zoo_nat0 -> zoo_nat0``],
         witness = SOME zoo_nat0_instance_impostor_witness})
  end)

val _ = test "typedef and quotient registrations are validated" (fn () =>
  let
    fun three thms = register_typedef
      {ty = ``:zoo_three``, abs = ``zoo_three_abs``, rep = ``zoo_three_rep``,
       absrep_thms = thms}
    val split_ty = ``:refute_harvest_split``
    val split_abs = ``refute_harvest_split_home_abs``
    val split_rep = ``refute_harvest_split_home_rep``
    val half1 = refuteHarvestTypeTheory.refute_harvest_split_home_absrep_1
    val half2 = refuteHarvestTypeTheory.refute_harvest_split_home_absrep_2
    fun split thms = register_typedef
      {ty = split_ty, abs = split_abs, rep = split_rep, absrep_thms = thms}
  in
    accepted (fn () => three [zoo_three_absrep]) andalso
    accepted (fn () => register_typedef
      {ty = ``:zoo_univ``, abs = ``zoo_univ_abs``, rep = ``zoo_univ_rep``,
       absrep_thms = [zoo_univ_absrep]}) andalso
    rejected (fn () => three [boolTheory.TRUTH]) andalso
    rejected (fn () => register_quotient
      {qty = ``:zoo_three``, rty = ``:num``, abs = ``zoo_three_abs``,
       rep = ``zoo_three_rep``, equiv_thm = boolTheory.TRUTH}) andalso
    rejected (fn () => register_quotient
      {qty = ``:rat``, rty = ``:frac``, abs = ``rat$abs_rat``,
       rep = ``rat$rep_rat``, equiv_thm = ratTheory.RAT_EQUIV}) andalso
    rejected (fn () => register_typedef
      {ty = ``:rat``, abs = ``rat$abs_rat``, rep = ``rat$rep_rat``,
       absrep_thms = [boolTheory.TRUTH]}) andalso
    accepted (fn () => split [Thm.CONJ half1 half2]) andalso
    accepted (fn () => split [half1, half2]) andalso
    accepted (fn () => split [half2, half1]) andalso
    rejected (fn () => split []) andalso
    rejected (fn () => split [half1, half1]) andalso
    rejected (fn () => split [half1, Thm.CONJUNCT2 zoo_three_absrep])
  end)

val _ = test "frac registrations" (fn () =>
  Option.isSome (lookup_term_postprocessor ``:real``) andalso
  rejected (fn () => register_frac_type
    {tyop = {Thy = "rat", Tyop = "rat"},
     ersatz = [{original = {Thy = "rat", Name = "rat_add"},
                replacement = {Thy = "refute", Name = "plus_frac"}},
               {original = {Thy = "rat", Name = "rat_add"},
                replacement = {Thy = "refute", Name = "times_frac"}}]}))

val _ = test "an empty custom generator is refused" (fn () =>
  (register_generator ``:ind`` {enumerate = NONE, random = NONE}; false)
  handle Fail _ => true)

val _ = test "harvest_registrations reaches beyond a type's home theory"
  (fn () =>
  let
    val result = harvest_registrations ()
    val repeat = harvest_registrations ()
    val hreal = Type.mk_thy_type {Thy = "hreal", Tyop = "hreal", Args = []}
    val deep = Type.mk_thy_type
      {Thy = "refuteHarvestType", Tyop = "refute_harvest_deep", Args = []}
    fun found ty =
      List.exists (fn t => Type.compare (t, ty) = EQUAL) (#typedefs result)
  in
    found hreal andalso found deep andalso
    not (null (#theories_scanned result)) andalso
    null (#typedefs repeat) andalso null (#quotients repeat)
  end)

val _ = test "term postprocessors compose general to specific" (fn () =>
  let
    val trace = ref ([] : string list)
    fun record label term = (trace := !trace @ [label]; term)
    val _ = Datatype.Datatype `rg_unpostprocessed = RGUnpostprocessed`
  in
    not (Option.isSome (lookup_term_postprocessor ``:rg_unpostprocessed``))
    andalso
    (register_term_postprocessor ``:num list`` (record "specific-old");
     register_term_postprocessor ``:'a`` (record "general");
     register_term_postprocessor ``:'a list`` (record "list-old");
     register_term_postprocessor ``:'b list`` (record "list-new");
     register_term_postprocessor ``:num list`` (record "specific-new");
     case lookup_term_postprocessor ``:num list`` of
         SOME p => (ignore (p ``[] : num list``);
                    !trace = ["general", "list-new", "specific-new"])
       | NONE => false) andalso
    (register_term_postprocessor ``:num`` (fn _ => boolSyntax.T);
     case lookup_term_postprocessor ``:num`` of
         SOME p => Term.aconv (p ``3 : num``) ``3 : num``
       | NONE => false) andalso
    (register_term_postprocessor ``:bool`` (fn _ => raise Fail "display");
     case lookup_term_postprocessor ``:bool`` of
         SOME p => Term.aconv (p ``T``) ``T``
       | NONE => false)
  end)

(* ------------------------------------------------------------------- *)
(* Level 2: quickcheck conformance across substrates                    *)
(* ------------------------------------------------------------------- *)

val _ = level2_section "level 2: quickcheck conformance"

fun level2 name pred = if selftest_level >= 2 then test name pred else ()

val conformance = default_config |> quiet |> upd_timeout 300.0
  |> upd_iterations 100 |> upd_size 4 |> upd_max_counterexamples 1
  |> upd_sequential true

val strategies =
  (Only [Exhaustive], conformance) ::
  List.map (fn s => (Only [Random], conformance |> upd_seed (SOME s)))
    [1, 2, 3]

fun agrees (Counterexample (c1 :: _)) (Counterexample (c2 :: _)) =
      same_bindings c1 c2
  | agrees (Unknown r1) (Unknown r2) = r1 = r2
  | agrees NoCounterexample NoCounterexample = true
  | agrees _ _ = false

fun expectation_holds ExpectGenuine outcome =
      outcome |> cex_where (fn c => is_genuine c andalso
                                     Option.isSome (#cert c) andalso
                                     tag_clean (valOf (#cert c)))
  | expectation_holds ExpectNone outcome = not (is_cex outcome)
  | expectation_holds ExpectUnknown outcome = is_unknown outcome
  | expectation_holds _ _ = false

fun substrate_declines backend substrate text outcome =
  case outcome of
      Unknown reasons =>
        List.exists (String.isPrefix (backend ^ ": " ^ text)) reasons
    | _ => false

fun conformance_row (goal, expect, inapplicable, adjust) =
  List.all (fn (search, cfg) =>
    let
      val cfg = adjust cfg |> upd_search search
      val backend = case search of Only [Random] => "random" | _ => "exhaustive"
      val compute = refute (cfg |> upd_substrate Compute) goal
      fun conforms substrate =
        case List.find (fn (s, _) => s = substrate) inapplicable of
            SOME (_, text) =>
              substrate_declines backend substrate text
                (refute (cfg |> upd_substrate substrate) goal)
          | NONE =>
              agrees compute (refute (cfg |> upd_substrate substrate) goal)
    in
      expectation_holds expect compute andalso conforms NativeSML
    end) strategies

val conformance_rows = [
  (``(!n : num. n < 3 ==> n * n < 4) <=> T``, ExpectGenuine, [], I),
  (``(!n : num. 2 <= n /\ n < 5 ==> n * n < 10) <=> T``, ExpectGenuine, [], I),
  (``REVERSE (xs : num list) = xs``, ExpectGenuine, [], I),
  (``(x : num) - y + y = x``, ExpectGenuine, [], I),
  (``REVERSE (xs : num list ++ ys) = REVERSE xs ++ REVERSE ys``,
   ExpectGenuine, [], I),
  (``ALL_DISTINCT (xs : num list ++ ys) <=>
     ALL_DISTINCT xs /\ ALL_DISTINCT ys``, ExpectGenuine, [], I),
  (``nub (xs : num list ++ ys) = nub xs ++ nub ys``, ExpectGenuine, [], I),
  (``~((x : int) = x)``, ExpectGenuine, [], I),
  (``SORTED $= (xs : num list) ==> SORTED $= (x :: xs)``, ExpectGenuine, [], I),
  (``(m : num -> num option) k = SOME (v : num) ==> m k = NONE``,
   ExpectGenuine, [], I),
  (``(xs : 'a list) = ys``, ExpectGenuine, [], I),
  (``(x : 'a) = y``, ExpectGenuine, [], I),
  (``(x : 'a) = y``, ExpectGenuine, [], upd_finite_types false),
  (``(f : refute$rf2 -> refute$rf2) rf2_1 = rf2_1 /\ f rf2_2 = rf2_2 ==> F``,
   ExpectGenuine, [], I),
  (``(b : bool)``, ExpectGenuine, [], I),
  (``w2n ((a : word8) + b) = w2n a + w2n b``, ExpectGenuine, [], I),
  (``!w : word64. w = 0w``, ExpectGenuine, [], I),
  (``!n : num. n <> 2``, ExpectGenuine, [], I),
  (``!c : char. c <> #"a"``, ExpectGenuine, [], I),
  (``!s : string. s <> "x"``, ExpectGenuine, [], I),
  (``MAP SUC (xs : num list) = xs``, ExpectGenuine, [], I),
  (``FILTER ($= 0) (xs : num list) = xs``, ExpectGenuine, [], I),
  (``MAP (f : refute$rf2 -> bool) [rf2_1; rf2_2] = [T; T]``, ExpectGenuine,
   [], I),
  (``FILTER (p : refute$rf2 -> bool) [rf2_1; rf2_2] = []``, ExpectGenuine,
   [], I),
  (``word_xor (a : word8) b = a``, ExpectGenuine, [], I),
  (``(r : rg_stream_record) = s``, ExpectGenuine, [], I),
  (``rx_rose (t : rg_rose) = 0``, ExpectGenuine, [], I),
  (``HD (xs : num list) = 0``, ExpectGenuine, [], I),
  (``(r : rg_record) = s``, ExpectGenuine,
   [(NativeSML, "custom generator registered for :rg_record")], I),
  (``(x : rg_custom_matrix) = RGCustomA``, ExpectGenuine,
   [(NativeSML, "custom generator registered for :rg_custom_matrix")], I),
  (``(x : rat) = y``, ExpectGenuine,
   [(NativeSML, "custom generator registered for :rat")], I),
  (``(x : real) = y``, ExpectGenuine,
   [(NativeSML, "custom generator registered for :real")], I),
  (``(!n : num. n <= n)``, ExpectUnknown, [], I),
  (``T``, ExpectNone, [], I),
  (``REVERSE (REVERSE [T; F; T]) = [T; F; T]``, ExpectNone, [], I),
  (``(b : bool) \/ ~b``, ExpectNone, [], I),
  (``(x : refute$rf2) = rf2_1 \/ x = rf2_2``, ExpectNone, [], I)]

val _ = level2 "substrates conform on the quickcheck matrix" (fn () =>
  List.all conformance_row conformance_rows)

val _ = level2 "substrates conform on smart-generator goals" (fn () =>
  let
    fun run cfg goal substrate =
      refute (cfg |> upd_certify false |> upd_substrate substrate) goal
    fun all_agree cfg goal check =
      let
        val outcomes = List.map (run cfg goal) [Compute, NativeSML]
      in
        List.all (fn outcome => outcome |> cex_where (fn c =>
                    is_genuine c andalso uncertified c andalso check c))
          outcomes andalso
        List.all (agrees (hd outcomes)) (tl outcomes)
      end
  in
    all_agree (conformance |> only [Exhaustive] |> upd_depth 4 |> upd_size 1)
      ``zoo_sg_linear (n : num) ==> n < 3``
      (fn c => binding_is c ``n : num`` ``3 : num``) andalso
    all_agree (conformance |> only [Exhaustive])
      ``~zoo_sg_bool_duplicate (x : bool) (y, z) ==> (y, z) = (x, x)``
      (fn _ => true)
  end)

val _ = level2 "native and compute agree on datatype goals" (fn () =>
  List.all (fn goal =>
    List.all (fn (search, cfg) =>
      let val cfg = cfg |> upd_search search in
        agrees (refute (cfg |> upd_substrate Compute) goal)
               (refute (cfg |> upd_substrate NativeSML) goal)
      end) strategies)
    [``REVERSE (xs : num list) = xs``, ``(x : refute$rf3) = rf3_1``,
     ``(t : rg_tree) = RGTip n ==> F``])

(* Narrowing acceptance table. *)

val pnf_approx = "PNF testing used an incomplete finite approximation"
val eval_stuck = "evaluation stuck during testing"

fun display_bindings (c : counterexample) =
  String.concatWith "\n"
    (List.map (fn (v, x) => "  " ^ #1 (Term.dest_var v) ^ " = " ^
                            Parse.term_to_string x) (#bindings c))
fun display_evals (c : counterexample) =
  String.concatWith "\n"
    (List.map (fn (lhs, rhs) => "  " ^ Parse.term_to_string lhs ^ " = " ^
                                Parse.term_to_string rhs) (#evals c))

datatype needle = NGenuine of string option * string option
                | NPotential of string * string

fun needle_row (size, goal, verdict) =
  let
    val cfg = narrowing |> upd_substrate NativeSML |> upd_size size
      |> upd_abort_potential (case verdict of NPotential _ => true | _ => false)
    val outcome = refute cfg goal
    fun pinned NONE _ = true
      | pinned (SOME text) actual = text = actual
  in
    outcome |> single_cex_where (fn c =>
      #backend c = "narrowing" andalso #substrate c = "native" andalso
      (case verdict of
           NGenuine (bindings, evals) =>
             certifies goal c andalso pinned bindings (display_bindings c)
             andalso pinned evals (display_evals c)
         | NPotential (reason, bindings) =>
             #certainty c = Potential [reason] andalso uncertified c andalso
             null (#evals c) andalso display_bindings c = bindings))
  end

val genuine_any = NGenuine (NONE, NONE)
fun genuine_bindings text = NGenuine (SOME text, NONE)

val needle_rows = [
  (10, ``(x : int) = y``, genuine_any),
  (10, ``(x : num) = y``, genuine_any),
  (10, ``?y : num. !x. x = y``, NPotential (pnf_approx, "")),
  (10, ``(x : num) > 1 ==> ?y. x < y /\ y <= 1``,
   NPotential (pnf_approx, "  x = 2")),
  (10, ``(x : num) > 2 ==> ?y. x < y /\ y <= 2``,
   NPotential (pnf_approx, "  x = 3")),
  (7, ``!x : num. ?y. x > 3 ==> y < x /\ y > 3``, genuine_bindings "  x = 4"),
  (10, ``~rx_all_distinct (ws : num list) ==>
         ?xs ys zs y. ws = xs ++ [y] ++ ys ++ [y]``,
   NPotential (pnf_approx, "  ws = [1; 1; 0]")),
  (10, ``rx_mem (x : num) xs ==>
         ?ys zs. xs = ys ++ x :: zs /\ ~rx_mem x zs /\ ~rx_mem x ys``,
   NPotential (pnf_approx, "  x = 0\n  xs = [0; 0]")),
  (10, ``(MAP (f : num -> num) xs = y :: ys) =
         (?z zs. xs = (z' : num) :: zs /\ f z = y /\ MAP f zs = ys)``,
   genuine_bindings
     "  f = \206\187x. 0\n  xs = [0]\n  y = 0\n  ys = []\n  z' = 1"),
  (10, ``(a : num) :: xs = ys ++ [a] ==> ?zs. xs = zs ++ [a] /\ ys = a :: zs``,
   genuine_bindings "  a = 0\n  xs = []\n  ys = []"),
  (10, ``REVERSE (xs : num list) = xs``, genuine_bindings "  xs = [1; 0]"),
  (10, ``REVERSE (xs : int list) = xs``, genuine_any),
  (10, ``REVERSE (xs : bool list) = xs``, genuine_any),
  (10, ``MAP (f : bool -> bool) xs = MAP (g : bool -> bool) xs``,
   NGenuine (SOME "  f = \206\187x. T\n  xs = _::_\n  g = \206\187x. F",
             SOME "  MAP f xs = [T]\n  MAP g xs = [F]")),
  (10, ``MAP (f : bool -> bool) xs = MAP f ys ==> xs = ys``, genuine_any),
  (10, ``rx_list_rel (P : bool -> bool -> bool) (REVERSE xs) (REVERSE ys) =
         rx_list_rel P xs (REVERSE ys)``, genuine_any),
  (10, ``MAP (f : bool -> bool) xs =
         (funop : (bool -> bool) -> bool list -> bool list) f xs``,
   NGenuine (SOME "  f = _\n  xs = _::_\n  funop = \206\187x x. []",
             SOME "  MAP f xs = [T]\n  funop f xs = []")),
  (10, ``EVEN (n - 2) ==> EVEN n``, genuine_any),
  (6, ``rx_avl_ordered (RGMKT (x : num) l r h) /\
        rx_avl_height l = rx_avl_height r + 2 ==>
        rx_avl_ordered (rx_avl_l_bal (x, l, r))``, genuine_any),
  (10, ``HD ((xs : num list) ++ ys) = HD ys``,
   genuine_bindings "  xs = [0]\n  ys = [1]"),
  (10, ``LAST ((xs : num list) ++ ys) = LAST xs``,
   genuine_bindings "  xs = [1]\n  ys = [0]"),
  (10, ``(xs : num list) = [] ==> HD xs <> x``,
   NPotential (eval_stuck, "  xs = []\n  x = _")),
  (10, ``(xs : num list) = [] ==> HD xs = x``,
   NPotential (eval_stuck, "  xs = []\n  x = _")),
  (10, ``(xs : num list) = [] ==> HD xs = x ==> x = y``,
   NPotential (eval_stuck, "  xs = []\n  x = _\n  y = _")),
  (10, ``HD ((xs : num list) ++ ys) = (if xs = [] then HD ys else HD xs)``,
   NPotential (eval_stuck, "  xs = []\n  ys = []")),
  (10, ``HD (MAP (f : num -> num) xs) = f (HD xs)``,
   NPotential (eval_stuck, "  f = _\n  xs = []")),
  (1, ``FST (p : bool # bool)``, genuine_bindings "  p = (F,_)"),
  (2, ``(f : bool -> bool) F = f T``,
   NGenuine (SOME ("  f = (\206\187x. T)" ^
                   "\226\166\135T \226\134\166 F\226\166\136"),
             SOME "  f F = T\n  f T = F")),
  (1, ``(f : (bool -> bool) -> bool) (\x. T)``,
   genuine_bindings "  f = \206\187x. F"),
  (2, ``?y : bool. !x : bool. x = y``,
   genuine_bindings "  x = if y then F else T"),
  (2, ``(x : rg_enum) <> RGRed ==> ?y : rg_enum. x = RGRed /\ y = RGGreen``,
   genuine_any)]

val _ = level2 "narrowing acceptance table" (fn () =>
  List.all needle_row needle_rows)

val _ = level2 "a stuck existential is only Potential" (fn () =>
  let
    val cfg = narrowing |> upd_substrate NativeSML |> upd_size 2
    val goal = ``?b : bool. HD ([] : bool list) = b``
    fun stuck outcome =
      outcome |> single_cex_where (fn c =>
        is_potential c andalso uncertified c andalso
        List.exists (String.isSubstring "evaluation stuck")
          (case #certainty c of Potential rs => rs | _ => []))
  in
    stuck (refute (cfg |> upd_abort_potential true) goal) andalso
    stuck (refute (cfg |> upd_abort_potential true |> upd_certify false) goal)
    andalso not (genuine (refute cfg goal))
  end)

(* Corpus: expectations are enforced by refute itself. *)

val corpus_config = default_config |> quiet |> only [Exhaustive]
  |> upd_seed (SOME 1) |> upd_sequential true |> upd_timeout 5.0

fun corpus_row (goal, expect, adjust) =
  (refute (corpus_config |> adjust |> upd_expect expect) goal; true)

val frac_ty = Type.mk_thy_type {Thy = "frac", Tyop = "frac", Args = []}
val frac_goal =
  boolSyntax.mk_eq (Term.mk_var ("x", frac_ty), Term.mk_var ("y", frac_ty))

val _ = level2 "quickcheck corpus" (fn () =>
  List.all corpus_row [
    (``REVERSE (xs : num list) = xs``, ExpectGenuine, I),
    (``(x : num) - y + y = x``, ExpectGenuine, I),
    (``REVERSE (REVERSE [T; F; T]) = [T; F; T]``, ExpectNone, I),
    (``REVERSE (xs : num list ++ ys) = REVERSE xs ++ REVERSE ys``,
     ExpectGenuine, I),
    (``ALL_DISTINCT (xs : num list ++ ys) <=>
       ALL_DISTINCT xs /\ ALL_DISTINCT ys``, ExpectGenuine, I),
    (``nub (xs : num list ++ ys) = nub xs ++ nub ys``, ExpectGenuine, I),
    (``~((x : int) = x)``, ExpectGenuine, I),
    (``SORTED $= (xs : num list) ==> SORTED $= (x :: xs)``, ExpectGenuine, I),
    (``(m1 : num -> num option) k = SOME (v : num) ==> m1 k = NONE``,
     ExpectGenuine, I),
    (``(xs : 'a list) = ys``, ExpectGenuine, I),
    (``(x : 'a) = y``, ExpectGenuine, I),
    (``(x : 'a) = y``, ExpectGenuine, upd_finite_types false),
    (``(f : refute$rf2 -> refute$rf2) rf2_1 = rf2_1 /\ f rf2_2 = rf2_2 ==> F``,
     ExpectGenuine, I),
    (``(b : bool)``, ExpectGenuine, I),
    (``(!n : num. n <= n)``, ExpectUnknown, I),
    (``(r : rg_record) = s``, ExpectGenuine, I),
    (``w2n ((a : bool[8]) + b) = w2n a + w2n b``, ExpectGenuine, I),
    (``(x : real) + y = x``, ExpectGenuine, I),
    (frac_goal, ExpectUnknown, I),
    (``!n : num. n <> 2``, ExpectGenuine, I),
    (``!c : char. c <> #"a"``, ExpectGenuine, I),
    (``!s : string. s <> "x"``, ExpectGenuine, I),
    (``T``, ExpectNone, I),
    (``(b : bool) \/ ~b``, ExpectNone, I),
    (``(x : refute$rf2) = rf2_1 \/ x = rf2_2``, ExpectNone, I),
    (``(x : rg_custom) = RGC0``, ExpectGenuine, I)] andalso
  List.all (fn goal =>
    refute (default_config |> quiet |> upd_search QuickcheckBackends
              |> upd_expect ExpectGenuine) goal |> is_cex)
    [``REVERSE (xs : num list) = xs``, ``(x : num) - y + y = x``,
     ``nub (xs : num list ++ ys) = nub xs ++ nub ys``, ``~((x : int) = x)``]
  andalso
  unknown_with "no generator" (refute corpus_config frac_goal) andalso
  refute corpus_config
    ``(f : refute$rf2 -> refute$rf2) rf2_1 = rf2_1 /\ f rf2_2 = rf2_2 ==> F``
  |> cex_where (fn c => List.exists (fn (_, v) =>
       not (null (#1 (combinSyntax.strip_update v)))) (#bindings c)) andalso
  List.all (fn goal =>
    agrees (refute (corpus_config |> only [Exhaustive, Random]) goal)
           (refute (corpus_config |> only [Exhaustive, Random]
                      |> upd_sequential false) goal))
    [``(x : num) - y + y = x``, ``(!b : bool. b \/ ~b)``])

(* ------------------------------------------------------------------- *)
(* Level 2: model finder acceptance                                     *)
(* ------------------------------------------------------------------- *)

val _ = level2_section "level 2: model finder acceptance"

fun mf_level2 name pred =
  if selftest_level >= 2 then mf_test name pred else ()

datatype cert_pin = CSome | CNone | CAny
datatype verdict = V of expectation | GenuineOrPotential

fun cert_pin_holds CAny _ = true
  | cert_pin_holds pin (Counterexample (c :: _)) =
      is_potential c orelse
      (is_genuine c andalso
       (case (pin, #cert c) of
            (CSome, SOME thm) => tag_clean thm
          | (CNone, NONE) => true
          | _ => false))
  | cert_pin_holds _ _ = false

fun mf_row group configure (name, goal, adjust, verdict, pin) =
  mf_level2 (group ^ ": " ^ name) (fn () =>
    let
      val cfg = mf |> configure |> adjust
      val outcome =
        case verdict of
            V expect => refute (cfg |> upd_expect expect) goal
          | GenuineOrPotential =>
              refute cfg goal |> (fn outcome =>
                if outcome |> cex_where (fn c => is_genuine c orelse
                                                  is_potential c)
                then outcome else raise Fail "neither Genuine nor Potential")
    in
      cert_pin_holds pin outcome
    end)

fun mf_group group configure rows = List.app (mf_row group configure) rows

fun cards cs = upd_card [(NONE, cs)]
fun num_card n cs = upd_card [(SOME ``:num``, [n]), (NONE, cs)]
val no_box = upd_box [(NONE, SOME false)]
val no_specialize = upd_specialize false
val no_star = upd_star_linear_preds false
fun wf b = upd_wf [(NONE, SOME b)]
val unary = upd_binary_ints (SOME false)
val binary = upd_binary_ints (SOME true)
val mono = upd_mono [(NONE, SOME true)]

val _ = List.app register_typedef
  [{ty = ``:'a zoo_one_or_two``, abs = ``zoo_one_or_two_abs``,
    rep = ``zoo_one_or_two_rep``, absrep_thms = [zoo_one_or_two_absrep]},
   {ty = ``:'a zoo_bounded``, abs = ``zoo_bounded_abs``,
    rep = ``zoo_bounded_rep``, absrep_thms = [zoo_bounded_absrep]},
   {ty = ``:zoo_check``, abs = ``zoo_check_abs``, rep = ``zoo_check_rep``,
    absrep_thms = [zoo_check_absrep]}]
val _ = register_quotient
  {qty = ``:zoo_manual_my_int``, rty = ``:num # num``,
   abs = ``zoo_manual_my_int_abs``, rep = ``zoo_manual_my_int_rep``,
   equiv_thm = zoo_manual_my_int_equiv}

val _ = mf_group "baseline" I [
  ("HD", ``xs <> [] ==> HD (xs : num list) = 0``, I, V ExpectGenuine, CSome),
  ("TL", ``xs <> [] ==> TL (xs : num list) = []``, I, V ExpectGenuine, CSome),
  ("REVERSE", ``REVERSE (xs : num list) = xs``, I, V ExpectGenuine, CSome),
  ("REVERSE append",
   ``REVERSE (xs ++ ys : num list) = REVERSE xs ++ REVERSE ys``, I,
   V ExpectGenuine, CSome),
  ("tree shape", ``(tree : zoo_tree) = ZooLeaf 0``, I, V ExpectGenuine, CSome),
  ("constructor equation", ``ZooLeaf n = ZooLeaf 0``, I, V ExpectGenuine,
   CSome),
  ("record selector", ``(record : zoo_record).zoo_num = 0``, I,
   V ExpectGenuine, CSome),
  ("set membership", ``(n : num) IN (s : num set)``, I, V ExpectGenuine,
   CSome),
  ("specialized MAP", ``MAP SUC (xs : num list) = []``, I, V ExpectGenuine,
   CSome),
  ("function application", ``(f : bool -> num) b = 0``, I, V ExpectGenuine,
   CSome),
  ("TotalDefn equation", ``zoo_total n = 0``, I, V ExpectGenuine, CSome),
  ("DefnBase equation", ``zoo_height (ZooLeaf n) = SUC n``, I,
   V ExpectGenuine, CNone),
  ("unary natural", ``SUC n = n``, I, V ExpectGenuine, CSome),
  ("unary integer", ``(i : int) + 1 = i``, I, V ExpectGenuine, CSome),
  ("choice spec", ``zoo_spec = 1``, I, V ExpectGenuine, CNone),
  ("existential natural", ``?n : num. n <> n``, I, V ExpectGenuine, CSome),
  ("Boolean theorem", ``!b : bool. b \/ ~b``, I, V ExpectNone, CAny),
  ("finite theorem", ``!x : refute$rf2. x = rf2_1 \/ x = rf2_2``, I,
   V ExpectNone, CAny),
  ("wf inductive", ``zoo_wf_lfp n ==> n = 0``, I, V ExpectGenuine, CNone),
  ("non-wf unrolling", ``~zoo_unroll_lfp 2``, I, V ExpectGenuine, CNone),
  ("mutual wf", ``zoo_mutual_lfp n ==> zoo_mutual_other_lfp n``, I,
   V ExpectGenuine, CNone),
  ("mutual unrolling",
   ``zoo_mutual_nonwf_lfp n ==> zoo_mutual_nonwf_other_lfp n``, I,
   V ExpectGenuine, CNone),
  ("coinductive unrolling", ``zoo_guarded_gfp F``, I, V ExpectGenuine, CNone),
  ("mutual coinductive", ``zoo_mutual_gfp F \/ zoo_mutual_other_gfp F``, I,
   V ExpectGenuine, CNone)]

fun variants goal expect pin adjusts =
  List.map (fn (suffix, adjust) => (suffix, goal, adjust, expect, pin)) adjusts
val induct_all =
  [("auto", I), ("wf", wf true), ("non_wf", wf false),
   ("non_wf dont_star", wf false o no_star)]
val induct_nonwf_no_star =
  [("auto", I), ("non_wf", wf false), ("non_wf dont_star", wf false o no_star)]
val induct_no_star = [("auto", I), ("dont_star", no_star)]
val induct_nonwf = [("auto", I), ("non_wf", wf false)]

val _ = mf_group "Induct_Nits" (cards [1, 2, 3, 4, 5, 6, 7, 8] o unary)
  (List.concat [
    variants ``zoo_induct_p1 = zoo_induct_q1`` (V ExpectUnknown) CAny
      induct_all,
    variants ``zoo_induct_p1 <> zoo_induct_q1`` (V ExpectPotential) CAny
      induct_all,
    variants ``zoo_induct_p1 (n - 2) ==> zoo_induct_p1 n`` (V ExpectGenuine)
      CNone induct_nonwf_no_star,
    variants ``zoo_induct_q1 (n - 2) ==> zoo_induct_q1 n`` (V ExpectGenuine)
      CNone induct_nonwf_no_star,
    variants ``zoo_induct_p2 = (\n : num. F)`` (V ExpectUnknown) CAny
      induct_no_star,
    variants ``zoo_induct_q2 = (\n : num. F)`` (V ExpectGenuine) CNone
      induct_no_star,
    [("q2 bottom wf", ``zoo_induct_q2 = (\n : num. F)``, wf true,
      V ExpectQuasiGenuine, CAny)],
    variants ``zoo_induct_p2 = (\n : num. T)`` (V ExpectGenuine) CNone
      induct_no_star,
    variants ``zoo_induct_q2 = (\n : num. T)`` (V ExpectUnknown) CAny
      induct_no_star,
    [("q2 top wf", ``zoo_induct_q2 = (\n : num. T)``, wf true,
      V ExpectQuasiGenuine, CAny)],
    variants ``zoo_induct_p2 = zoo_induct_q2`` (V ExpectGenuine) CNone
      induct_no_star,
    variants ``zoo_induct_p2 n`` (V ExpectGenuine) CNone
      (induct_no_star @ [("dont_specialize", no_specialize)]),
    variants ``zoo_induct_q2 n`` (V ExpectUnknown) CAny induct_no_star,
    variants ``~zoo_induct_p2 n`` (V ExpectUnknown) CAny induct_no_star,
    variants ``~zoo_induct_q2 n`` (V ExpectGenuine) CNone
      (induct_no_star @ [("dont_specialize", no_specialize)]),
    variants ``zoo_induct_p3 = zoo_induct_q3`` (V ExpectUnknown) CAny
      induct_nonwf,
    variants ``zoo_induct_p4 = zoo_induct_q4`` (V ExpectUnknown) CAny
      induct_nonwf,
    variants ``zoo_induct_p3 = (\n : num. ~zoo_induct_p4 n)``
      (V ExpectUnknown) CAny induct_nonwf,
    variants ``zoo_induct_q3 = (\n : num. ~zoo_induct_q4 n)``
      (V ExpectUnknown) CAny induct_nonwf,
    variants ``(\n. zoo_induct_p3 n /\ zoo_induct_q4 n) <> (\n : num. F)``
      (V ExpectPotential) CAny induct_nonwf,
    variants ``(\n. zoo_induct_q3 n /\ zoo_induct_p4 n) <> (\n : num. F)``
      (V ExpectPotential) CAny induct_nonwf,
    variants ``(\n. zoo_induct_p3 n \/ zoo_induct_q4 n) <> (\n : num. T)``
      (V ExpectPotential) CAny induct_nonwf,
    variants ``(\n. zoo_induct_q3 n \/ zoo_induct_p4 n) <> (\n : num. T)``
      (V ExpectPotential) CAny induct_nonwf])

val special_pair = [("specialize", I), ("dont_specialize", no_specialize)]
val special_small =
  upd_card [(SOME ``:num``, [2]), (SOME ``:'a``, [1]), (NONE, [4])]
val special_five =
  ``\one two. zoo_special_f5
      (\a. if a = one then 1 else if a = two then 2 else a)``
fun special_ho body = ``(!a : num. g a = a) ==>
    ?b1 : num. ?b2 b3 b4 b5 b6 b7 b8 b9 b10 : 'a. ?b11 : num.
      b1 < b11 /\ ^body``
val h_sum = ``h b2 + h b3 + h b4 + h b5 + h b6 + h b7 + h b8 + h b9 + h b10``

val _ = mf_group "Special_Nits" (cards [4]) (List.concat [
  variants ``zoo_special_f1 0 0 0 0 0 = zoo_special_f1 0 0 0 0 (1 - 1)``
    (V ExpectUnknown) CAny special_pair,
  variants ``zoo_special_f1 u v w x y = zoo_special_f1 y x w v u``
    (V ExpectUnknown) CAny special_pair,
  variants ``zoo_special_f2 0 0 0 0 0 = zoo_special_f2 (1 - 1) 0 0 0 0``
    (V ExpectUnknown) CAny special_pair,
  variants ``zoo_special_f2 0 (v - v) 0 (x - x) 0 =
             zoo_special_f2 (u - u) 0 (w - w) 0 (y - y)``
    (V ExpectUnknown) CAny special_pair,
  variants ``zoo_special_f2 1 0 0 0 0 = zoo_special_f2 0 1 0 0 0``
    (V ExpectGenuine) CSome special_pair,
  variants ``zoo_special_f2 0 0 0 0 0 = zoo_special_f2 0 0 0 0 0``
    (V ExpectNone) CAny special_pair,
  variants ``zoo_special_f3 a b c d e = zoo_special_f3 e d c b a``
    (V ExpectGenuine) CSome special_pair,
  variants ``zoo_special_f3 a b c d a = zoo_special_f3 a d c d a``
    (V ExpectGenuine) CSome special_pair,
  variants ``c < 1 /\ e <= a /\ a <= e ==>
             zoo_special_f3 a b c d a = zoo_special_f3 e d c b e``
    (V ExpectUnknown) CAny special_pair,
  variants ``(!u. a = u ==>
                  zoo_special_f3 a a a a a = zoo_special_f3 u u u u u) /\
             (!u. b = u ==>
                  zoo_special_f3 b b u b b = zoo_special_f3 u u b u u)``
    (V ExpectUnknown) CAny special_pair,
  variants ``zoo_special_f4 a b = zoo_special_f4 b a`` (V ExpectUnknown) CAny
    special_pair,
  variants ``zoo_special_f4 a (SUC a) = zoo_special_f4 a a``
    (V ExpectGenuine) CSome special_pair,
  variants ``?one : num. one IN {1} /\ ?two : num. two IN {2} /\
             ^special_five one two (SUC x) = x``
    (V ExpectUnknown) CAny special_pair,
  variants ``?two : num. two IN {2} /\ ?one : num. one IN {1} /\
             ^special_five one two (SUC x) = x``
    (V ExpectUnknown) CAny special_pair,
  [("15", ``(if x = 1 then 2 else if x = 2 then 1 else x) = x``, I,
    V ExpectGenuine, CSome)],
  variants ``(!a : num. g a = a) ==>
             ?one : num. one IN {1} /\ ?two : num. two IN {2} /\
             zoo_special_f5 g x = ^special_five one two x``
    (V ExpectUnknown) CAny special_pair,
  variants ``(!a : num. g a = a) ==>
             ?one : num. one IN {2} /\ ?two : num. two IN {1} /\
             zoo_special_f5 g x = ^special_five one two x``
    (V ExpectPotential) CAny special_pair,
  let val goal = special_ho ``zoo_special_f5 g x =
        zoo_special_f5 (\a. if b1 < b11 then a else h b2) x`` in
    [("19 specialize", goal, I, V ExpectPotential, CAny),
     ("19 dont_specialize", goal, no_specialize, V ExpectUnknown, CAny),
     ("19 dont_box", goal, no_box, V ExpectUnknown, CAny),
     ("19 dont_box dont_specialize", goal, no_box o no_specialize,
      V ExpectUnknown, CAny)]
  end,
  variants (special_ho ``g x = (if b1 < b11 then x else ^h_sum)``)
    (V ExpectUnknown) CAny
    [("20 specialize", special_small), ("20 dont_box", special_small o no_box),
     ("20 dont_specialize", special_small o no_specialize),
     ("20 dont_box dont_specialize",
      special_small o no_box o no_specialize)],
  variants (special_ho ``zoo_special_f5 g x =
        zoo_special_f5 (\a. if b11 <= b1 then a else ^h_sum) x``)
    (V ExpectPotential) CAny
    [("21 specialize", special_small), ("21 dont_box", special_small o no_box),
     ("21 dont_specialize", special_small o no_box o no_specialize),
     ("21 dont_box dont_specialize",
      special_small o no_box o no_specialize)]])

val integer_pair = [("unary_ints", unary), ("binary_ints", binary)]
fun integer_rows (goal, expect, pin) = variants goal expect pin integer_pair

val _ = mf_group "Integer_Nits"
  (cards [1, 2, 3, 4, 5] o upd_bits [1, 2, 3, 4, 6])
  (List.concat (List.map integer_rows [
     (``SUC x = x + 1``, V ExpectUnknown, CAny),
     (``x < SUC x``, V ExpectUnknown, CAny),
     (``x + y >= (x : num)``, V ExpectUnknown, CAny),
     (``y <> 0 ==> x + y > (x : num)``, V ExpectUnknown, CAny),
     (``x + y = y + (x : num)``, V ExpectUnknown, CAny),
     (``x > y ==> x - y <> (0 : num)``, V ExpectUnknown, CAny),
     (``x <= y ==> x - y = (0 : num)``, V ExpectUnknown, CAny),
     (``x - (0 : num) = x``, V ExpectUnknown, CAny),
     (``(x <> 0 /\ y <> 0) ==> x * y <> (0 : num)``, V ExpectUnknown, CAny),
     (``0 * y = (0 : num)``, V ExpectUnknown, CAny),
     (``y * 0 = (0 : num)``, V ExpectUnknown, CAny),
     (``(x <> 0 /\ y <> 0) ==> x * y >= (x : num)``, V ExpectUnknown, CAny),
     (``(x <> 0 /\ y <> 0) ==> x * y >= (y : num)``, V ExpectUnknown, CAny),
     (``x * y DIV y = (x : num)``, V ExpectGenuine, CSome),
     (``y <> 0 ==> x * y DIV y = (x : num)``, V ExpectUnknown, CAny),
     (``5 * 55 < (260 : num)``, V ExpectUnknown, CAny),
     (``Num (&n) = n``, V ExpectUnknown, CAny),
     (``x + y >= (x : int)``, V ExpectGenuine, CSome),
     (``(x >= 0 /\ y >= 0) ==> x + y >= (0 : int)``, V ExpectUnknown, CAny),
     (``y >= 0 ==> x + y >= (x : int)``, V ExpectUnknown, CAny),
     (``x >= 0 ==> x + y >= (y : int)``, V ExpectUnknown, CAny),
     (``x >= 0 ==> x + y >= (x : int)``, V ExpectGenuine, CSome),
     (``(x <= 0 /\ y <= 0) ==> x + y <= (0 : int)``, V ExpectUnknown, CAny),
     (``y <> 0 ==> x + y > (x : int)``, V ExpectGenuine, CSome),
     (``x + y = y + (x : int)``, V ExpectUnknown, CAny),
     (``x > y ==> x - y <> (0 : int)``, V ExpectUnknown, CAny),
     (``x <= y ==> x - y = (0 : int)``, V ExpectGenuine, CSome),
     (``x - (0 : int) = x``, V ExpectUnknown, CAny),
     (``(x <> 0 /\ y <> 0) ==> x * y <> (0 : int)``, V ExpectUnknown, CAny),
     (``0 * y = (0 : int)``, V ExpectUnknown, CAny),
     (``y * 0 = (0 : int)``, V ExpectUnknown, CAny),
     (``(x <> 0 /\ y <> 0) ==> x * y >= (x : int)``, V ExpectGenuine, CSome),
     (``(x <> 0 /\ y <> 0) ==> x * y >= (y : int)``, V ExpectGenuine, CSome),
     (``(if y = 0 then 0 else x * y / y) = (x : int)``, V ExpectGenuine,
      CSome),
     (``(x * y < 0) <=> (x > 0 /\ y < 0) \/ (x < 0 /\ y > (0 : int))``,
      V ExpectUnknown, CAny),
     (``~5 * 55 > (~260 : int)``, V ExpectUnknown, CAny)]) @
   [("guarded int division unary", ``y <> 0 ==> x * y / y = (x : int)``,
     unary, V ExpectUnknown, CAny),
    ("guarded int division binary", ``y <> 0 ==> x * y / y = (x : int)``,
     binary o cards [1, 2, 3, 4] o upd_bits [1, 2, 3, 4], V ExpectUnknown,
     CAny),
    ("nat overflow bits 9", ``5 * 55 < (260 : num)``, binary o upd_bits [9],
     V ExpectGenuine, CSome),
    ("int overflow bits 9", ``~5 * 55 > (~260 : int)``, binary o upd_bits [9],
     V ExpectGenuine, CSome),
    ("labels nonempty",
     ``zoo_integer_labels (ZooIntegerNode x left right) <> ({} : num set)``,
     I, V ExpectUnknown, CAny),
    ("labels cardinality", ``CARD (zoo_integer_labels t) > 0``, I,
     GenuineOrPotential, CSome)])

fun max0 c = upd_max [(SOME c, [0])]
val nibble = ``n = ZooNibble2 ==> zoo_nibble_rot n <> ZooNibble3``

val _ = mf_group "Datatype_Nits"
  (cards [1, 2, 3, 4, 5, 6, 7, 8] o upd_max_potential 0) [
  ("rotation fixed point", ``zoo_nibble_rot n <> n``,
   cards [1, 2, 3, 4, 5, 6, 7, 8, 16], V ExpectNone, CAny),
  ("card 1", nibble, cards [1], V ExpectUnknown, CAny),
  ("max Nibble4 0", nibble, cards [2] o max0 ``ZooNibble4``, V ExpectGenuine,
   CSome),
  ("max Nibble2 0", nibble, cards [2] o max0 ``ZooNibble2``, V ExpectUnknown,
   CAny),
  ("FUNPOW 15 no fixed point", ``FUNPOW zoo_nibble_rot 15 n <> n``,
   cards [17], V ExpectUnknown, CAny),
  ("FUNPOW 15 fixed point", ``FUNPOW zoo_nibble_rot 15 n = n``, cards [17],
   V ExpectGenuine, CSome),
  ("FUNPOW 16", ``FUNPOW zoo_nibble_rot 16 n = n``, cards [17],
   V ExpectUnknown, CAny),
  ("first projection", ``zoo_pd_fs (ZooPd p) = FST p``, cards [12],
   V ExpectUnknown, CAny),
  ("wrong first projection", ``zoo_pd_fs (ZooPd p) = SND p``, I,
   V ExpectGenuine, CSome),
  ("second projection", ``zoo_pd_sn (ZooPd p) = SND p``, cards [12],
   V ExpectUnknown, CAny),
  ("wrong second projection", ``zoo_pd_sn (ZooPd p) = FST p``, I,
   V ExpectGenuine, CSome),
  ("nested projection", ``zoo_pd_fs (ZooPd ((a, b), (c, d))) = (a, b)``, I,
   V ExpectUnknown, CAny),
  ("wrong nested projection", ``zoo_pd_fs (ZooPd ((a, b), (c, d))) = (c, d)``,
   I, V ExpectGenuine, CSome),
  ("function constructor", ``zoo_fn_app (ZooFn g) y = g y``, I,
   V ExpectUnknown, CAny),
  ("different function", ``zoo_fn_app (ZooFn g) y = g' y``, I,
   V ExpectGenuine, CSome),
  ("different argument", ``zoo_fn_app (ZooFn g) y = g y'``, I,
   V ExpectGenuine, CSome)]

val _ = mf_group "Record_Nits" (cards [1, 2, 3, 4, 5, 6] o upd_max_potential 0)
  (List.map (fn (name, goal, expect, pin) => (name, goal, I, expect, pin)) [
   ("point2d all updates",
    ``zoo_point2d x y = (p : zoo_point2d) with <|zoo_xc2 := x; zoo_yc2 := y|>``,
    V ExpectUnknown, CAny),
   ("point2d partial update",
    ``zoo_point2d x y = (p : zoo_point2d) with zoo_xc2 := x``,
    V ExpectGenuine, CSome),
   ("point2d changed",
    ``((p : zoo_point2d) with <|zoo_xc2 := x; zoo_yc2 := y|>) <> p``,
    V ExpectGenuine, CSome),
   ("point2d unchanged",
    ``((p : zoo_point2d) with <|zoo_xc2 := x; zoo_yc2 := y|>) = p``,
    V ExpectGenuine, CSome),
   ("point3d all updates",
    ``zoo_point3d x y z =
      (p : zoo_point3d) with <|zoo_xc3 := x; zoo_yc3 := y; zoo_zc3 := z|>``,
    V ExpectUnknown, CAny),
   ("point3d x update",
    ``zoo_point3d x y z = (p : zoo_point3d) with zoo_xc3 := x``,
    V ExpectGenuine, CSome),
   ("point3d z update",
    ``zoo_point3d x y z = (p : zoo_point3d) with zoo_zc3 := z``,
    V ExpectGenuine, CSome),
   ("point3d changed",
    ``((p : zoo_point3d) with
       <|zoo_xc3 := x; zoo_yc3 := y; zoo_zc3 := z|>) <> p``,
    V ExpectGenuine, CSome),
   ("point3d unchanged",
    ``((p : zoo_point3d) with
       <|zoo_xc3 := x; zoo_yc3 := y; zoo_zc3 := z|>) = p``,
    V ExpectGenuine, CSome),
   ("point4d all updates",
    ``zoo_point4d x y z w = (p : zoo_point4d) with
       <|zoo_xc4 := x; zoo_yc4 := y; zoo_zc4 := z; zoo_wc4 := w|>``,
    V ExpectUnknown, CAny),
   ("point4d x update",
    ``zoo_point4d x y z w = (p : zoo_point4d) with zoo_xc4 := x``,
    V ExpectGenuine, CSome),
   ("point4d z update",
    ``zoo_point4d x y z w = (p : zoo_point4d) with zoo_zc4 := z``,
    V ExpectGenuine, CSome),
   ("point4d w update",
    ``zoo_point4d x y z w = (p : zoo_point4d) with zoo_wc4 := w``,
    V ExpectGenuine, CSome),
   ("point4d changed",
    ``((p : zoo_point4d) with
       <|zoo_xc4 := x; zoo_yc4 := y; zoo_zc4 := z; zoo_wc4 := w|>) <> p``,
    V ExpectGenuine, CSome),
   ("point4d unchanged",
    ``((p : zoo_point4d) with
       <|zoo_xc4 := x; zoo_yc4 := y; zoo_zc4 := z; zoo_wc4 := w|>) = p``,
    V ExpectGenuine, CSome)])

val _ = mf_group "Pattern_Nits"
  (cards [8] o upd_max_potential 0 o upd_destroy_constrs true)
  (List.map (fn (name, goal, expect, pin) => (name, goal, I, expect, pin)) [
   ("unit case", ``(x : 'a) = (case (u : unit) of () => y)``,
    V ExpectGenuine, CNone),
   ("Boolean case", ``(x : 'a) = (case b of T => x | F => y)``,
    V ExpectGenuine, CNone),
   ("pair case", ``(x : 'b) = (case (p : 'a # 'b) of (a, b) => b)``,
    V ExpectGenuine, CNone),
   ("natural case", ``(x : num) = (case n of 0 => x | SUC m => m)``,
    V ExpectGenuine, CSome),
   ("option case",
    ``(x : 'a) = (case (opt : 'a option) of NONE => x | SOME y => y)``,
    V ExpectGenuine, CNone),
   ("list case",
    ``(x : 'a) = (case (xs : 'a list) of [] => x | y :: ys => y)``,
    V ExpectGenuine, CNone),
   ("nested case",
    ``(x : 'b) =
      (case (xs : ('a # 'b) option list) of
           [] => x
         | y :: ys =>
             case ys of
                 [] => x
               | z :: zs =>
                   case z of NONE => x | SOME p => case p of (a, b) => b)``,
    V ExpectGenuine, CNone),
   ("f1", ``(x : 'a) = zoo_pattern_f1 (y : 'a) u``, V ExpectGenuine, CNone),
   ("f2", ``(x : 'a) = zoo_pattern_f2 x (y : 'a) b``, V ExpectGenuine, CNone),
   ("f3", ``(x : 'b) = zoo_pattern_f3 (p : 'a # 'b)``, V ExpectGenuine, CNone),
   ("f4", ``(x : num) = zoo_pattern_f4 x n``, V ExpectGenuine, CSome),
   ("f5", ``(x : 'a) = zoo_pattern_f5 x (opt : 'a option)``, V ExpectGenuine,
    CNone),
   ("f6", ``(x : 'a) = zoo_pattern_f6 x (xs : 'a list)``, V ExpectGenuine,
    CNone),
   ("f7", ``(x : 'b) = zoo_pattern_f7 x (xs : ('a # 'b) option list)``,
    V ExpectGenuine, CNone),
   ("unit constructor", ``(u : unit) = ()``, V ExpectNone, CAny),
   ("Boolean existential", ``?y : bool. b = y``, V ExpectNone, CAny),
   ("pair existential", ``?a b. (p : 'a # 'b) = (a, b)``, V ExpectNone, CAny),
   ("SUC existential", ``?m : num. n = SUC m``, V ExpectGenuine, CNone),
   ("SOME existential", ``?y : 'a. (x : 'a option) = SOME y``,
    V ExpectGenuine, CNone),
   ("CONS existential", ``?y ys. (xs : 'a list) = y :: ys``, V ExpectGenuine,
    CNone),
   ("nested constructor existential",
    ``?y a b zs. (xs : ('a # 'b) option list) = y :: SOME (a, b) :: zs``,
    V ExpectGenuine, CNone)])

val pair_swapped = ``(a, b) = ABS_prod (\x y. x = b /\ y = a)``
val fst_mutated = ``FST (ABS_prod (\x y. x = a /\ y = b)) = b``

val _ = mf_group "Typedef_Nits" (cards [1, 2, 3, 4]) [
  ("three equality", ``(x : zoo_three) = y``, I, V ExpectGenuine, CNone),
  ("unit one_or_two", ``(x : unit zoo_one_or_two) = y``, I, V ExpectNone,
   CAny),
  ("bool one_or_two", ``(x : bool zoo_one_or_two) = y``, I, V ExpectGenuine,
   CNone),
  ("collapsed one_or_two",
   ``((ARB F : bool) <=> ARB T) ==> (x : bool zoo_one_or_two) = y``, I,
   V ExpectNone, CAny),
  ("collapsed one_or_two distinct card 1",
   ``((ARB F : bool) <=> ARB T) ==> ?x y : bool zoo_one_or_two. x <> y``,
   cards [1], GenuineOrPotential, CAny),
  ("one_or_two distinct card 1", ``?x y : bool zoo_one_or_two. x <> y``,
   cards [1], GenuineOrPotential, CAny),
  ("one_or_two distinct card 2", ``?x y : bool zoo_one_or_two. x <> y``,
   cards [2], V ExpectNone, CAny),
  ("unit bounded", ``(x : unit zoo_bounded) = y``, I, V ExpectNone, CAny),
  ("bool bounded", ``(x : bool zoo_bounded) = y``, I, V ExpectGenuine, CNone),
  ("bool bounded two values",
   ``(x : bool zoo_bounded) <> y ==> z = x \/ z = y``, I, V ExpectNone, CAny),
  ("pair-bool bounded",
   ``(x : (bool # bool) zoo_bounded) <> y ==> z = x \/ z = y``,
   cards [1, 2, 3, 4, 5], V ExpectGenuine, CNone),
  ("check membership", ``zoo_check_rep (zoo_check_abs n) = n ==> n < 2``,
   cards [1, 2, 3], V ExpectUnknown, CAny),
  ("check mutation", ``zoo_check_rep (zoo_check_abs n) = n ==> n < 1``,
   cards [1, 2, 3], V ExpectGenuine, CNone),
  ("swapped product boxed", pair_swapped, cards [1, 2], V ExpectUnknown, CAny),
  ("swapped product dont_box", pair_swapped, no_box, V ExpectGenuine, CNone),
  ("mutated projection boxed", fst_mutated, cards [1, 2], V ExpectUnknown,
   CAny),
  ("mutated projection dont_box", fst_mutated, no_box, V ExpectGenuine,
   CNone)]

val cards12 = cards (List.tabulate (12, fn i => i + 1))
fun core_num n = upd_card [(SOME ``:num``, [n]), (NONE, [1, 2, 3, 4, 5, 6])]
val alternations = ``!u : 'a. ?v : 'b. !w : 'c. ?x : 'd. !y : 'e. ?z : 'f.
                      f u v w x y z = f u (g u) w (h u w) y (k u w y)``
val singleton_if = ``!x : 'a. if (!y : 'a. x = y) then F else T``
val eps_four = ``($@ (\j : num. j > SUC 2 /\ j <= 4)) = x``

val _ = mf_group "Core_Nits"
  (cards [1, 2, 3, 4, 5, 6] o unary o upd_max_potential 0) [
  ("curry composition",
   ``((\f x y. (CURRY o UNCURRY) f x y) = (\f x y. (\x. x) f x y)) /\
     ((\f p. (UNCURRY o CURRY) f p) = (\f p. (\x. x) f p))``, cards [1, 2],
   V ExpectUnknown, CAny),
  ("UNCURRY CURRY", ``UNCURRY (CURRY f) = f``, cards12, V ExpectUnknown, CAny),
  ("CURRY UNCURRY", ``CURRY (UNCURRY f) = f``, cards12, V ExpectUnknown, CAny),
  ("UNCURRY abstraction", ``UNCURRY (\x y. f (x, y)) = f``, cards12,
   V ExpectUnknown, CAny),
  ("mono inverse large cards",
   ``(?g : 'b -> 'a. !x : 'a. g (f x) = x) ==> !y : 'b. ?x : 'a. y = f x``,
   upd_card [(SOME ``:'a``, [24]), (SOME ``:'b``, [25]), (NONE, [1])],
   V ExpectGenuine, CNone),
  ("mono inverse forced",
   ``(?g : 'b -> 'a. !x : 'a. g (f x) = x) ==> !y : 'b. ?x : 'a. y = f x``,
   cards (List.tabulate (10, fn i => i + 1)) o mono, V ExpectUnknown, CAny),
  ("boxed relation", ``(R : ('a # 'a) -> ('a # 'a) -> bool) (a, a) (a, a)``,
   cards [1], V ExpectGenuine, CSome),
  ("relation dont_box", ``(R : ('a # 'a) -> ('a # 'a) -> bool) (a, a) (a, a)``,
   cards [5] o no_box, V ExpectGenuine, CSome),
  ("function argument dont_box",
   ``(f : ('a -> 'a) -> 'b) (g : 'a -> 'a) = x``, cards [3] o no_box,
   V ExpectGenuine, CNone),
  ("boxed quantifier sound",
   ``!u : 'a -> 'b. ?v : 'c. !w : 'd. ?x : 'e -> 'f.
       f u v w x = f u (g u) w (h u w)``, cards [1, 2] o no_box,
   V ExpectUnknown, CAny),
  ("boxed quantifier mutation",
   ``!u : 'a -> 'b. ?v : 'c. !w : 'd. ?x : 'e -> 'f.
       f u v w x = f u (g u w) w (h u)``, cards [1, 2] o no_box,
   V ExpectGenuine, CNone),
  ("one alternation", ``!x : 'a. ?y : 'b. f x y = f x (g x)``,
   cards [1, 2, 3, 4], V ExpectUnknown, CAny),
  ("two alternations",
   ``!u : 'a. ?v : 'b. !w : 'c. ?x : 'd. f u v w x = f u (g u) w (h u w)``,
   cards [1, 2, 3, 4], V ExpectUnknown, CAny),
  ("quantifier mutation",
   ``!u : 'a. ?v : 'b. !w : 'c. ?x : 'd. f u v w x = f u (g u w) w (h u)``,
   cards [3], V ExpectGenuine, CNone),
  ("three alternations", alternations, cards [1, 2], V ExpectUnknown, CAny),
  ("third dependency",
   ``!u : 'a. ?v : 'b. !w : 'c. ?x : 'd. !y : 'e. ?z : 'f.
       f u v w x y z = f u (g u) w (h u w y) y (k u w y)``, cards [1, 2],
   V ExpectGenuine, CNone),
  ("second dependency",
   ``!u : 'a. ?v : 'b. !w : 'c. ?x : 'd. !y : 'e. ?z : 'f.
       f u v w x y z = f u (g u w) w (h u w) y (k u w y)``, cards [1, 2],
   V ExpectGenuine, CNone),
  ("product quantifiers",
   ``!u : 'a # 'b. ?v : 'c. !w : 'd. ?x : 'e # 'f.
       f u v w x = f u (g u) w (h u w)``, cards [1, 2], V ExpectUnknown, CAny),
  ("product quantifier mutation",
   ``!u : 'a # 'b. ?v : 'c. !w : 'd. ?x : 'e # 'f.
       f u v w x = f u (g u w) w (h u)``, cards [1, 2] o no_box,
   V ExpectGenuine, CNone),
  ("singleton if", singleton_if, cards [1], V ExpectGenuine, CNone),
  ("nonsingleton if", singleton_if, cards [2, 3, 4, 5], V ExpectUnknown, CAny),
  ("let quantifier", ``let x = (!y : 'a. P y) in if x then x else ~x``, I,
   V ExpectUnknown, CAny),
  ("let product quantifier",
   ``let x = (!y : 'a # 'b. P y) in if x then x else ~x``, I,
   V ExpectUnknown, CAny),
  ("subset", ``(A : 'a set) SUBSET B``, cards [100], V ExpectGenuine, CNone),
  ("self complement", ``(A : 'a set) = COMPL A``, cards [10], V ExpectGenuine,
   CNone),
  ("union complement", ``(A : 'a set) UNION COMPL A = UNIV``, I,
   V ExpectUnknown, CAny),
  ("intersection complement", ``(A : 'a set) INTER COMPL A = {}``, I,
   V ExpectUnknown, CAny),
  ("FINITE trio",
   ``FINITE (A : 'a set) /\ (FINITE A ==> FINITE (B : 'b set)) /\
     (!C : 'c set. FINITE C)``, I, V ExpectUnknown, CAny),
  ("ARB", ``(x : 'a) = ARB``, I, V ExpectGenuine, CNone),
  ("Eps bounded three card 2", ``($@ (\j : num. j > SUC 2 /\ j <= 3)) <> 0``,
   core_num 2 o upd_max_potential 1, V ExpectGenuine, CNone),
  ("Eps bounded three card 6", ``($@ (\j : num. j > SUC 2 /\ j <= 3)) <> 0``,
   core_num 6 o upd_max_potential 1, V ExpectGenuine, CNone),
  ("Eps bounded four nonzero card 2", ``^eps_four ==> x <> 0``,
   core_num 2 o upd_max_potential 1, V ExpectUnknown, CAny),
  ("Eps bounded four nonzero card 6", ``^eps_four ==> x <> 0``,
   core_num 6 o upd_max_potential 1, V ExpectUnknown, CAny),
  ("Eps bounded four exact card 2", ``^eps_four ==> x = 4``,
   core_num 2 o upd_max_potential 1, V ExpectUnknown, CAny),
  ("Eps bounded four exact card 6", ``^eps_four ==> x = 4``,
   core_num 6 o upd_max_potential 1, V ExpectUnknown, CAny),
  ("Eps bounded five exact",
   ``($@ (\j : num. j > SUC 2 /\ j <= 5)) = x ==> x = 4``, core_num 6,
   V ExpectGenuine, CNone),
  ("Eps bounded five range",
   ``($@ (\j : num. j > SUC 2 /\ j <= 5)) = x ==> x = 4 \/ x = 5``,
   core_num 6, V ExpectUnknown, CAny),
  ("destructors and ARB",
   ``((x : 'a) = (case T of T => x | F => x)) /\
     (x = (case (x, y) of (x', y') => x')) /\
     (ARB : 'b) = ARB /\ (f : 'b -> 'c) ARB = f ARB``, cards [2],
   V ExpectUnknown, CAny)]

val _ = mf_group "Refute_Nits" (cards [1, 2, 3, 4, 5, 6] o upd_max_potential 0)
  [("drinker", ``(?x : 'a. f x = g x ==> f = g)``, I, V ExpectUnknown, CAny),
   ("weak drinker", ``(?x : 'a. f x = g x) ==> f = g``, I, V ExpectGenuine,
    CSome),
   ("surjective gives inverse",
    ``(!y : 'b. ?x : 'a. y = f x) ==> ?g : 'b -> 'a. !x. g (f x) = x``, I,
    V ExpectGenuine, CNone),
   ("inverse gives surjective",
    ``(?g : 'b -> 'a. !x. g (f x) = x) ==> !y : 'b. ?x. y = f x``, I,
    V ExpectGenuine, CNone),
   ("choice unique mutation",
    ``(!x : 'a. ?y : 'b. P x y) ==> ?!f. !x. P x (f x)``, I, V ExpectGenuine,
    CNone),
   ("choice", ``(!x : 'a. ?y : 'b. P x y) ==> ?f. !x. P x (f x)``,
    cards [1, 2, 3, 4], V ExpectUnknown, CAny),
   ("unique choice", ``(!x : 'a. ?!y : 'b. P x y) ==> ?!f. !x. P x (f x)``,
    cards [1, 2, 3], V ExpectUnknown, CAny),
   ("Eps value", ``($@ (P : bool -> bool))``, I, V ExpectGenuine, CNone),
   ("predicate of Eps", ``($@ (\n : num. n = 0)) = 1``, I, V ExpectGenuine,
    CSome),
   ("Eps application", ``~Q ($@ (Q : num -> bool))``, I, V ExpectGenuine,
    CNone),
   ("Eps equality", ``($@ (\x : num. x = y)) = z``, I, V ExpectGenuine, CSome),
   ("Eps axiom", ``(?x : 'a. P x) ==> P ($@ P)``, I, V ExpectUnknown, CAny),
   ("T3 constructor", ``(ZooRefE f : ('a, 'b) zoo_ref_t3) = ZooRefE g``, I,
    V ExpectGenuine, CNone),
   ("T3 recursor equation", ``zoo_ref_t3_CASE (ZooRefE x) e = e x``,
    cards [1, 2, 3, 4], V ExpectUnknown, CAny),
   ("T3 recursor", ``zoo_ref_t3_CASE x e = z``, I, V ExpectGenuine, CNone),
   ("BinTree leaf equation", ``zoo_ref_rec_bintree l n (ZooRefLeaf x) = l x``,
    I, V ExpectUnknown, CAny),
   ("BinTree node equation",
    ``zoo_ref_rec_bintree l n (ZooRefNode x y) =
      n x y (zoo_ref_rec_bintree l n x) (zoo_ref_rec_bintree l n y)``,
    cards [1, 2, 3, 4, 5], V ExpectUnknown, CAny),
   ("mutual aexp", ``(ZooRefNumber x : 'a zoo_ref_aexp) = ZooRefNumber x``,
    cards [1], V ExpectNone, CAny),
   ("mutual bexp", ``(x : 'a zoo_ref_bexp) = x``, cards [1], V ExpectNone,
    CAny),
   ("mutual X", ``ZooRefXA = ZooRefXB ZooRefXA``, I, V ExpectGenuine, CSome),
   ("mutual Y", ``ZooRefYF = ZooRefYD ZooRefXA``, I, V ExpectGenuine, CSome),
   ("nested option", ``ZooRefCX (SOME (ZooRefCX NONE)) = ZooRefCX NONE``, I,
    V ExpectGenuine, CSome),
   ("function option", ``ZooRefCY (SOME (\a : 'a. T)) = ZooRefCY NONE``, I,
    V ExpectGenuine, CSome),
   ("trie", ``ZooRefTR [ZooRefTR []] = ZooRefTR []``, I, V ExpectGenuine,
    CSome),
   ("infinite tree", ``ZooRefInfNode (\n. T) = ZooRefInfLeaf``, I,
    V ExpectGenuine, CSome),
   ("lambda", ``ZooRefLam (\a : 'a. T) = ZooRefVar a``, I, V ExpectGenuine,
    CSome),
   ("nested U", ``(x : 'a zoo_ref_u) = y``, I, V ExpectGenuine, CNone),
   ("point record", ``(x : ('a, 'b) zoo_ref_point) = y``, I, V ExpectGenuine,
    CNone),
   ("extended record", ``(x : ('a, 'b, 'c) zoo_ref_extpoint) = y``, I,
    V ExpectGenuine, CNone),
   ("undefined inductive set", ``zoo_ref_undefined_set (x : 'a)``, I,
    V ExpectGenuine, CNone),
   ("even-card inductive set", ``zoo_ref_even_card (ss : 'a set)``, I,
    V ExpectGenuine, CNone),
   ("mutual even odd", ``zoo_ref_odd n``, I, V ExpectGenuine, CNone),
   ("abstract even odd", ``zoo_ref_a_odd f (x : 'a)``, I, V ExpectGenuine,
    CNone),
   ("lfp equation", ``f (fixedPoint$lfp f) = fixedPoint$lfp f``, cards [2],
    V ExpectGenuine, CNone),
   ("gfp equation", ``f (fixedPoint$gfp f) = fixedPoint$gfp f``, cards [2],
    V ExpectGenuine, CNone),
   ("lfp gfp equality", ``fixedPoint$lfp f = fixedPoint$gfp f``, cards [2],
    V ExpectGenuine, CNone),
   ("empty cardinality", ``CARD (x : 'a set) = 0``, I, V ExpectGenuine, CSome),
   ("finite set", ``FINITE (x : 'a set)``, I, V ExpectUnknown, CAny),
   ("distinct list", ``ALL_DISTINCT [a; b]``, I, V ExpectGenuine, CSome),
   ("simplified distinct", ``a <> b``, I, V ExpectGenuine, CSome),
   ("WF not transitive poly", ``WF (R : 'a -> 'a -> bool) ==> transitive R``,
    I, V ExpectGenuine, CNone),
   ("WF not transitive rf3",
    ``WF (R : refute$rf3 -> refute$rf3 -> bool) ==> transitive R``, I,
    V ExpectGenuine, CNone),
   ("WF irreflexive rf3",
    ``WF (R : refute$rf3 -> refute$rf3 -> bool) ==> ~R x x``, I, V ExpectNone,
    CAny),
   ("SUM_IMAGE nonzero", ``SUM_IMAGE (f : 'a -> num) (s : 'a set) = 0``, I,
    V ExpectGenuine, CSome),
   ("SUM_SET nonzero", ``SUM_SET (s : num set) = 0``, I, V ExpectGenuine,
    CSome)]

val ten = List.tabulate (10, fn i => i + 1)
fun manual_num n = upd_card [(SOME ``:num``, [n]), (NONE, ten)]
val bisim_goal =
  ``(xs = llist$LCONS (a : num) xs /\ ys = llist$LCONS a ys) ==> xs = ys``

val _ = mf_group "Manual_Nits" (cards ten) [
  ("inverse surjective",
   ``(?g : 'b -> 'a. !x : 'a. g (f x) = x) ==> !y : 'b. ?x. y = f x``, I,
   V ExpectGenuine, CNone),
  ("universal fixed point", ``?x : 'a. !f : 'a -> 'a. f x = x``, I,
   V ExpectGenuine, CNone),
  ("reflexive not symmetric",
   ``(!x : 'a. r x x) ==> (!x y. r x y ==> r y x)``, I, V ExpectGenuine,
   CNone),
  ("integer inequality",
   ``i <= j /\ n <= (m : int) ==> i * n + j * m <= i * m + j * n``, I,
   V ExpectGenuine, CSome),
  ("integer inequality binary",
   ``i <= j /\ n <= (m : int) ==> i * n + j * m <= i * m + j * n``,
   binary o upd_bits [16], V ExpectGenuine, CSome),
  ("infinite nat axiom", ``(!n : num. SUC n <> n) ==> P``, manual_num 100,
   V ExpectPotential, CAny),
  ("P SUC", ``SUC n = n``, I, V ExpectGenuine, CSome),
  ("addition card one", ``x + y = (x : num)``, manual_num 1, V ExpectUnknown,
   CAny),
  ("addition card two", ``x + y = (x : num)``, manual_num 2, V ExpectGenuine,
   CSome),
  ("HD append", ``HD (xs ++ [y; y]) = HD xs``, I, V ExpectGenuine, CAny),
  ("singleton lists", ``LENGTH xs = 1 /\ LENGTH ys = 1 ==> xs = ys``, I,
   V ExpectGenuine, CSome),
  ("typedef three",
   ``zoo_three_abs 0 IN X /\ zoo_three_abs 1 IN X ==> (c : zoo_three) IN X``,
   upd_show_types true, V ExpectGenuine, CNone),
  ("quotient add", ``zoo_manual_add x y = zoo_manual_add x x``,
   upd_show_types true, V ExpectGenuine, CNone),
  ("record selector", ``zoo_xc2 (p : zoo_point2d) = zoo_xc2 q``,
   upd_show_types true, V ExpectGenuine, CNone),
  ("existential even", ``?n. zoo_manual_even n /\ zoo_manual_even (SUC n)``,
   manual_num 50 o unary, V ExpectPotential, CAny),
  ("bounded even",
   ``?n. n <= 49 /\ zoo_manual_even n /\ zoo_manual_even (SUC n)``,
   manual_num 50 o unary, V ExpectGenuine, CNone),
  ("non-wf even",
   ``?n. (n = 0 \/ n = 2 \/ n = 4 \/ n = 6 \/ n = 8) /\
         ~zoo_manual_even_alt n``, manual_num 10 o unary, V ExpectGenuine,
   CNone),
  ("non-wf even predecessor",
   ``zoo_manual_even_alt (n - 2) ==> zoo_manual_even_alt n``, manual_num 10,
   V ExpectGenuine, CNone),
  ("coinductive nats", ``zoo_manual_nats = (\n. n IN {0; 1; 2; 3; 4})``,
   manual_num 10, V ExpectGenuine, CNone),
  ("odd predecessor", ``zoo_manual_odd n ==> zoo_manual_odd (n - 2)``,
   manual_num 4, V ExpectGenuine, CNone),
  ("llist cyclic", ``(xs : num llist) <> llist$LCONS a xs``, I,
   V ExpectGenuine, CNone),
  ("llist iterates",
   ``(xs = llist$LCONS (a : num) xs /\ ys = zoo_manual_iterates (\b. a) b) ==>
     xs = ys``, I, V ExpectGenuine, CNone),
  ("bisim disabled", bisim_goal, upd_bisim_depth [~1] o upd_show_types true,
   V ExpectQuasiGenuine, CAny),
  ("bisim checked", bisim_goal, cards [1, 2, 3, 4, 5], V ExpectUnknown, CAny),
  ("subst1", ``~zoo_manual_loose t 0 ==> zoo_manual_subst1 sigma t = t``,
   cards [2], V ExpectUnknown, CAny),
  ("subst1 eval", ``~zoo_manual_loose t 0 ==> zoo_manual_subst1 sigma t = t``,
   cards [2] o upd_evals [``zoo_manual_subst1 sigma t``], V ExpectUnknown,
   CAny),
  ("reverse zip",
   ``LENGTH xs = LENGTH ys ==> REVERSE (ZIP (xs, ys)) = ZIP (xs, REVERSE ys)``,
   I, V ExpectGenuine, CSome),
  ("mono forced",
   ``(?g : 'a -> 'b. !x : 'b. g (f x) = x) ==> !y : 'a. ?x : 'b. y = f x``,
   mono, V ExpectUnknown, CAny),
  ("mono smart",
   ``(?g : 'a -> 'b. !x : 'b. g (f x) = x) ==> !y : 'a. ?x : 'b. y = f x``,
   I, V ExpectGenuine, CNone),
  ("AA dataset transforms",
   ``zoo_manual_dataset (zoo_manual_skew t) = zoo_manual_dataset t /\
     zoo_manual_dataset (zoo_manual_split t) = zoo_manual_dataset t``,
   cards [1, 2, 3], V ExpectUnknown, CAny),
  ("AA wf transforms",
   ``(zoo_manual_wf t ==> zoo_manual_skew t = t) /\
     (zoo_manual_wf t ==> zoo_manual_split t = t)``, cards [1, 2, 3, 4, 5],
   V ExpectUnknown, CAny),
  ("AA buggy insertion",
   ``zoo_manual_wf t ==> zoo_manual_wf (zoo_manual_insort1 t x)``, I,
   V ExpectGenuine, CSome),
  ("AA insertion eval",
   ``zoo_manual_wf t ==> zoo_manual_wf (zoo_manual_insort1 t x)``,
   upd_evals [``zoo_manual_insort1 t x``], V ExpectGenuine, CSome),
  ("AA corrected insertion",
   ``zoo_manual_wf t ==> zoo_manual_wf (zoo_manual_insort2 t x)``,
   cards [1, 2, 3, 4, 5], V ExpectUnknown, CAny),
  ("AA insertion dataset",
   ``zoo_manual_dataset (zoo_manual_insort2 t x) =
     {x} UNION zoo_manual_dataset t``, cards [1, 2, 3], V ExpectUnknown,
   CAny)]

val _ = mf_group "Hotel_Nits"
  (upd_card [(SOME ``:zoo_hotel_room``, [1]), (SOME ``:zoo_hotel_guest``, [2]),
             (SOME ``:zoo_hotel_guest option``, [3]),
             (SOME ``:zoo_hotel_key``, [4]), (SOME ``:zoo_hotel_state``, [6]),
             (NONE, [1, 2, 3, 4, 5, 6])]
   o upd_format [(NONE, [2])] o wf false o upd_show_consts true
   o upd_max_potential 0)
  [("pinned cards",
    ``zoo_hotel_pinned s r g ==> zoo_hotel_safe s r ==>
      g IN zoo_hotel_isin s r ==> zoo_hotel_owns s r = SOME g``, I,
    V ExpectGenuine, CNone)]

val _ = mf_group "refusal flips" I [
  ("RTC", ``RTC (r : num -> num -> bool) x y``, I, V ExpectGenuine, CNone),
  ("GSPEC over RTC", ``x IN GSPEC (\n : num. (n, RTC r n x))``, I,
   V ExpectUnknown, CAny)]

val _ = if selftest_level >= 2 then
  List.app register_ersatz
    [{original = {Thy = "refuteTableZoo", Name = "zoo_relation_inv"},
      replacement = {Thy = "relation", Name = "inv"}},
     {original = {Thy = "refuteTableZoo", Name = "zoo_bool_relcomp"},
      replacement = {Thy = "relation", Name = "O"}}]
  else ()

val _ = mf_group "ersatz relations"
  (upd_card [(SOME ``:num``, [2]), (NONE, [1])])
  [("inv argument order",
    ``~zoo_relation_inv (\n : num. \b : bool. n = 0 /\ b) T 0``, I,
    V ExpectGenuine, CSome),
   ("O argument order",
    ``~zoo_bool_relcomp (\b : bool. \n : num. b /\ n = 1)
                        (\n : num. \b : bool. n = 0 /\ b) 0 1``, I,
    V ExpectGenuine, CSome)]

(* Quickcheck and the model finder agree on decidable goals. *)

fun best_certainty outcome =
  case outcome of
      Counterexample cs =>
        if List.exists is_genuine cs then "genuine"
        else if List.exists is_quasi cs then "quasi" else "potential"
    | NoCounterexample => "none"
    | Unknown _ => "unknown"
    | _ => "fail"

val _ = mf_level2 "quickcheck and kodkod agree" (fn () =>
  let
    val qc_cfg = exhaustive |> upd_timeout 20.0 |> upd_size 4
      |> upd_substrate Compute |> upd_sequential true
    fun row (goal, has_cex, existence_only, adjusts) =
      let val qc = with_compset [zoo_wf_lfp_compute]
                     (fn () => refute qc_cfg goal) in
        is_cex qc = has_cex andalso
        List.all (fn adjust =>
          let val kk = refute (mf |> adjust) goal in
            is_cex kk = has_cex andalso
            (existence_only orelse best_certainty qc = best_certainty kk)
          end) adjusts
      end
  in
    List.all row [
      (``(b : bool)``, true, false, [I]),
      (``(x : refute$rf2) = rf2_1``, true, false, [I]),
      (``(x : 'a) = y``, true, true, [I]),
      (``REVERSE (xs : bool list) = xs``, true, false, [I]),
      (``(b : bool) \/ ~b``, false, false, [I]),
      (``(x : refute$rf2) = rf2_1 \/ x = rf2_2``, false, false, [I]),
      (``zoo_wf_lfp 2 ==> (2 : num) = 0``, true, false, [I]),
      (``zoo_wf_lfp 2``, false, true, [I]),
      (``zoo_special_f2 1 0 0 0 0 = zoo_special_f2 0 1 0 0 0``, true, false,
       [I, no_specialize]),
      (``(R : (unit # unit) -> (unit # unit) -> bool) ((), ()) ((), ()) \/
         ~R ((), ()) ((), ())``, false, false,
       [upd_box [(NONE, SOME true)], no_box])]
  end)

(* Soundness: true statements are never refuted; Unknown rows are
   bounds-relative facts the finder cannot decide. *)

fun sound_row group configure (name, goal, expect) =
  mf_level2 (group ^ ": " ^ name) (fn () =>
    (refute (mf |> configure |> upd_expect expect) goal; true))
fun sound_group group configure rows =
  List.app (sound_row group configure) rows

val _ = sound_group "soundness" I [
  ("reverse involution", ``REVERSE (REVERSE [T; F; T]) = [T; F; T]``,
   ExpectUnknown),
  ("closed", ``T``, ExpectNone),
  ("bool", ``(b : bool) \/ ~b``, ExpectNone),
  ("rf", ``(x : refute$rf2) = rf2_1 \/ x = rf2_2``, ExpectNone),
  ("mutual parity",
   ``(zoo_mutual_lfp n <=> zoo_even n) /\
     (zoo_mutual_other_lfp n <=> zoo_odd n)``,
   ExpectUnknown),
  ("unrolled mutual parity",
   ``(zoo_mutual_nonwf_lfp n <=> zoo_even n) /\
     (zoo_mutual_nonwf_other_lfp n <=> zoo_odd n)``, ExpectUnknown),
  ("coinductive gfp", ``zoo_guarded_gfp b <=> b``, ExpectUnknown),
  ("mutual gfp",
   ``(zoo_mutual_gfp b <=> b) /\ (zoo_mutual_other_gfp b <=> b)``,
   ExpectUnknown),
  ("llist injectivity",
   ``llist$LCONS (a : num) xs = llist$LCONS b ys ==> a = b``, ExpectUnknown),
  ("llist distinct", ``llist$LNIL <> llist$LCONS (a : num) xs``,
   ExpectUnknown),
  ("llist bisimulation", bisim_goal, ExpectUnknown),
  ("llist case",
   ``llist$llist_CASE (llist$LCONS (a : num) xs) T (\b tail. F) = F``,
   ExpectNone),
  ("lbtree injectivity",
   ``lbtree$Nd (a : num) l1 r1 = lbtree$Nd b l2 r2 ==>
     a = b /\ l1 = l2 /\ r1 = r2``, ExpectUnknown),
  ("lbtree distinct", ``lbtree$Lf <> lbtree$Nd (a : num) l r``, ExpectUnknown),
  ("lbtree bisimulation",
   ``(t = lbtree$Nd (a : num) t t /\ u = lbtree$Nd a u u) ==> t = u``,
   ExpectUnknown),
  ("lbtree leaf case",
   ``lbtree$lbtree_case T (\(a : num) l r. F) lbtree$Lf = T``, ExpectNone),
  ("lbtree node case",
   ``lbtree$lbtree_case T (\(a : num) l r. F) (lbtree$Nd b t u) = F``,
   ExpectNone),
  ("path injectivity",
   ``path$pcons (s : num) (l : bool) p = path$pcons t m q ==>
     s = t /\ l = m /\ p = q``, ExpectUnknown),
  ("path distinct",
   ``path$stopped_at (s : num) <> path$pcons s (l : bool) p``, ExpectUnknown),
  ("path bisimulation",
   ``(p = path$pcons (s : num) (l : bool) p /\ q = path$pcons s m q /\
      l = m) ==> p = q``, ExpectUnknown),
  ("typedef ABS/REP", ``zoo_three_abs (zoo_three_rep x) = (x : zoo_three)``,
   ExpectUnknown),
  ("typedef membership", ``zoo_three_rep (x : zoo_three) < 3``, ExpectUnknown),
  ("quotient ABS/REP",
   ``zoo_manual_my_int_abs (zoo_manual_my_int_rep x) =
     (x : zoo_manual_my_int)``, ExpectUnknown),
  ("quotient class",
   ``zoo_manual_my_int_rel p q ==>
     zoo_manual_my_int_abs p = zoo_manual_my_int_abs q``, ExpectUnknown)]

val _ = sound_group "binary soundness"
  (binary o upd_bits [4] o cards [1, 2, 3, 4])
  [("nat addition commutes", ``x + y = (y : num) + x``, ExpectUnknown),
   ("int addition commutes", ``x + y = (y : int) + x``, ExpectUnknown)]

val _ = sound_group "relation soundness" (cards [1, 2]) [
  ("double inverse", ``inv (inv (R : 'a -> 'b -> bool)) = R``, ExpectUnknown),
  ("composition associative",
   ``(((R : 'c -> 'd -> bool) O (rel2 : 'b -> 'c -> bool)) O
      (rel3 : 'a -> 'b -> bool)) = R O (rel2 O rel3)``, ExpectUnknown),
  ("inverse reverses composition",
   ``inv ((R : 'b -> 'c -> bool) O (rel2 : 'a -> 'b -> bool)) =
     inv rel2 O inv R``, ExpectUnknown),
  ("inverse application", ``inv (R : 'a -> 'b -> bool) y x <=> R x y``,
   ExpectUnknown)]

val frac_bounds = binary o upd_bits [4] o cards [1, 2, 3]

val _ = sound_group "rat soundness" frac_bounds (List.map (fn (n, g) =>
  (n, g, ExpectUnknown)) [
  ("additive identity", ``rat$rat_add x rat$rat_0 = (x : rat$rat)``),
  ("multiplicative identity", ``rat$rat_mul x rat$rat_1 = (x : rat$rat)``),
  ("addition commutes", ``rat$rat_add x y = rat$rat_add y (x : rat$rat)``),
  ("multiplication commutes",
   ``rat$rat_mul x y = rat$rat_mul y (x : rat$rat)``),
  ("additive inverse", ``rat$rat_add x (rat$rat_ainv x) = rat$rat_0``),
  ("double inverse", ``rat$rat_ainv (rat$rat_ainv x) = (x : rat$rat)``),
  ("strict irreflexive", ``~rat$rat_les x (x : rat$rat)``),
  ("reflexive", ``rat$rat_leq x (x : rat$rat)``),
  ("total", ``rat$rat_les x y \/ x = (y : rat$rat) \/ rat$rat_les y x``),
  ("antisymmetric",
   ``rat$rat_leq x y /\ rat$rat_leq y x ==> x = (y : rat$rat)``),
  ("inverse equality",
   ``(rat$rat_ainv x = rat$rat_ainv y) <=> x = (y : rat$rat)``),
  ("cancellation",
   ``(rat$rat_add z x = rat$rat_add z y) <=> x = (y : rat$rat)``),
  ("normalized literal",
   ``rat$rat_cons (1 : int) (2 : int) = rat$rat_cons (2 : int) (4 : int)``)])

val _ = sound_group "real soundness" frac_bounds (List.map (fn (n, g) =>
  (n, g, ExpectUnknown)) [
  ("additive identity", ``realax$real_add x realax$real_0 = (x : real)``),
  ("additive identity numeral", ``realax$real_add x (0 : real) = (x : real)``),
  ("multiplicative identity",
   ``realax$real_mul x realax$real_1 = (x : real)``),
  ("multiplicative identity numeral",
   ``realax$real_mul x (1 : real) = (x : real)``),
  ("addition commutes", ``realax$real_add x y = realax$real_add y (x : real)``),
  ("multiplication commutes",
   ``realax$real_mul x y = realax$real_mul y (x : real)``),
  ("additive inverse",
   ``realax$real_add x (realax$real_neg x) = realax$real_0``),
  ("double inverse", ``realax$real_neg (realax$real_neg x) = (x : real)``),
  ("strict irreflexive", ``~realax$real_lt x (x : real)``),
  ("reflexive", ``realax$real_lte x (x : real)``),
  ("total", ``realax$real_lt x y \/ x = (y : real) \/ realax$real_lt y x``),
  ("antisymmetric",
   ``realax$real_lte x y /\ realax$real_lte y x ==> x = (y : real)``),
  ("inverse equality",
   ``(realax$real_neg x = realax$real_neg y) <=> x = (y : real)``),
  ("cancellation",
   ``(realax$real_add z x = realax$real_add z y) <=> x = (y : real)``),
  ("division equality",
   ``realax$real_of_num 1 / realax$real_of_num 2 =
     realax$real_of_num 2 / realax$real_of_num 4``)])

(* Named model-finder behaviours. *)

val clean_certificate = certifies

val _ = mf_level2 "polymorphic goals are certified at small scopes" (fn () =>
  refute (mf |> cards [2]) ``(x : 'a) = y`` |> cex_where (fn c =>
    is_genuine c andalso Option.isSome (#cert c) andalso
    List.exists (fn (_, v) => Term.is_var v andalso
                              Type.is_vartype (Term.type_of v) andalso
                              String.isPrefix "a" (#1 (Term.dest_var v)))
      (#bindings c) andalso
    (case #model c of
         SOME {types, ...} =>
           List.exists (fn (ty, values, _) =>
             Type.is_vartype ty andalso length values >= 2) types
       | NONE => false)) andalso
  refute (mf |> cards [7]) ``(x : 'a) = y`` |> cex_where (fn c =>
    is_genuine c andalso uncertified c andalso scope_of c ``:'a`` = SOME 7))

val _ = mf_level2 "type variables share a scope" (fn () =>
  refute (mf |> cards [1, 2] |> upd_max_potential 0)
    ``(?g : 'b -> 'a. !u : 'a. g (f u) = u) ==>
      !v : 'b. ?u : 'a.
        inv (\x : 'a. \y : 'b. y = f x) v u /\
        (((\y : 'b. \z : 'b. y = z) O (\x : 'a. \y : 'b. y = f x)) u v)``
  |> cex_where (fn c => is_genuine c andalso scope_of c ``:'a`` = SOME 1
                        andalso scope_of c ``:'b`` = SOME 2))

val _ = mf_level2 "monotonicity is reported" (fn () =>
  let
    val base = mf |> cards [1, 2, 3] |> upd_tac_timeout 5.0 |> upd_quiet false
    val goal = ``p (x : 'a) /\ q (y : 'b)``
    val (_, smart) = capture 2 (fn () => refute base goal)
    val (_, forced) = capture 2 (fn () => refute (base |> mono) goal)
  in
    String.isSubstring "passed the monotonicity" smart andalso
    String.isSubstring "might be able to skip some scopes" smart andalso
    String.isSubstring "considered monotonic" forced
  end)

val _ = mf_level2 "max_genuine yields several distinct models" (fn () =>
  case refute (mf |> upd_card [(SOME ``:refute$rf3``, [3]), (NONE, [1])]
                  |> upd_max_potential 0 |> upd_max_genuine 3)
              ``(x : refute$rf3) = rf3_1`` of
      Counterexample cs =>
        length cs <= 3 andalso
        List.all (fn c => is_genuine c andalso Option.isSome (#cert c)) cs
        andalso
        length (Lib.op_mk_set Term.aconv
                  (List.mapPartial (fn c => Option.map #2 (List.find
                     (fn (v, _) => #1 (Term.dest_var v) = "x") (#bindings c)))
                   cs)) >= 2
    | _ => false)

val _ = mf_level2 "quantified goals get one certified model" (fn () =>
  refute (mf |> upd_card [(SOME ``:num``, [2]), (SOME ``:refute$rf3``, [3]),
                          (NONE, [1])]
             |> upd_max_potential 2 |> upd_max_genuine 1)
         ``?n : num. n <> n \/ (x : refute$rf3) = rf3_1``
  |> single_cex_where (fn c => is_genuine c andalso
                                Option.isSome (#cert c) andalso
                                tag_clean (valOf (#cert c))))

val _ = mf_level2 "a genuine model stops the potential search" (fn () =>
  case refute (mf |> upd_batch_size 1
                  |> upd_card [(SOME ``:num``, [2]),
                               (SOME ``:num list``, [1, 2]), (NONE, [1])]
                  |> upd_max_potential 2 |> upd_max_genuine 2)
              ``xs <> [] ==> HD (xs : num list) = 0`` of
      Counterexample cs =>
        length cs <= 2 andalso
        List.exists (fn c => is_genuine c andalso Option.isSome (#cert c)) cs
        andalso not (List.exists is_potential cs)
    | _ => false)

val _ = mf_level2 "a non-incremental solver is replaced with a warning"
  (fn () =>
    let
      val cfg = mf |> upd_card [(SOME ``:refute$rf3``, [3]), (NONE, [1])]
        |> upd_max_potential 0 |> upd_max_genuine 2 |> upd_quiet false
      val goal = ``(x : refute$rf3) = rf3_1``
      val (forced, forced_text) =
        capture 2 (fn () => refute (cfg |> upd_sat_solver "CryptoMiniSat_JNI")
                                   goal)
      val (_, smart_text) =
        capture 2 (fn () => refute (cfg |> upd_sat_solver "smart") goal)
    in
      is_cex forced andalso
      String.isSubstring
        "An incremental SAT solver is required: \"SAT4J\" will be used \
        \instead of \"CryptoMiniSat_JNI\"" forced_text andalso
      String.isSubstring "Using SAT solver \"SAT4J\"" smart_text andalso
      String.isSubstring "The following incremental solvers are configured:"
        smart_text
    end)

val _ = mf_level2 "cyclic codatatype countermodels" (fn () =>
  let val base = mf |> cards [2, 3] in
    refute (base |> upd_expect ExpectGenuine)
           ``(xs : num llist) <> llist$LCONS a xs``
    |> cex_where (fn c =>
         is_genuine c andalso
         List.exists (fn (_, v) =>
           String.isSubstring "\207\137" (Parse.term_to_string v))
           (#bindings c)) andalso
    List.all (fn goal => genuine (refute (base |> upd_expect ExpectGenuine)
                                         goal))
      [``t = lbtree$Nd (a : num) t t ==> t = lbtree$Lf``,
       ``lbtree$lbtree_case T (\(a : num) l r. F) t``,
       ``llist$llist_CASE (xs : num llist) T (\a tail. F)``,
       ``(p : (num, bool) path$path) <> path$pcons s l p``] andalso
    refute (base |> upd_bisim_depth [~1] |> upd_expect ExpectQuasiGenuine)
           bisim_goal
    |> cex_where (fn c =>
         case #certainty c of
             QuasiGenuine reasons =>
               List.exists (String.isSubstring "bisim_depth") reasons
           | _ => false)
  end)

val _ = mf_level2 "a registered codatatype gets cyclic countermodels"
  (fn () =>
    let
      val _ = register_codatatype
        {tyop = {Thy = "refuteTableZoo", Tyop = "zoo_stream"},
         case_const = ``zoo_stream_CASE``, constructors = [``zoo_scons``],
         witness = SOME zoo_stream_witness}
      val base = mf |> cards [2, 3]
      val eta = zoo_stream_eta |> Thm.INST_TYPE [Type.alpha |-> ``:num``]
        |> Thm.concl |> boolSyntax.strip_forall |> #2
    in
      genuine (refute (base |> upd_expect ExpectGenuine)
                      ``(s : num zoo_stream) <> zoo_scons a s``) andalso
      let val outcome = refute (base |> upd_expect ExpectUnknown) eta in
        bounds_clean outcome andalso
        unknown_with "card num zoo_stream" outcome
      end
    end)

val _ = mf_level2 "quotients and typedefs have countermodels" (fn () =>
  let
    val _ = register_quotient
      {qty = ``:zoo_bool_quot``, rty = ``:bool``, abs = ``zoo_bool_quot_abs``,
       rep = ``zoo_bool_quot_rep``, equiv_thm = zoo_bool_equiv}
    val cfg = mf |> upd_card [(SOME ``:zoo_bool_quot``, [2]),
                              (SOME ``:zoo_three``, [2]), (NONE, [2])]
  in
    genuine (refute cfg ``(x : zoo_bool_quot) = y``) andalso
    genuine (refute cfg ``zoo_three_abs (zoo_three_rep x) = (y : zoo_three)``)
  end)

val _ = mf_level2 "atoms can be named and lists finitized" (fn () =>
  let
    val atoms = [(SOME ``:'a``, ["scarlet", "azure"]), (NONE, [])]
    val named = mf |> upd_card [(SOME ``:'a``, [2]), (NONE, [1])]
      |> upd_atoms atoms |> upd_show_types true
    val lists = mf |> upd_card [(SOME ``:bool list``, [2]),
                                (SOME ``:bool``, [2]), (NONE, [1])]
  in
    #atoms (#mf named) = atoms andalso
    refute named ``(x : 'a) = y`` |> cex_where (fn c =>
      is_genuine c andalso Option.isSome (#cert c)) andalso
    is_cex (refute lists ``!xs : bool list. xs = []``) andalso
    is_cex (refute (lists |> upd_finitize [(SOME ``:bool list``, SOME true),
                                           (NONE, NONE)])
                   ``!xs : bool list. xs = []``)
  end)

val _ = mf_level2 "needed values are pinned into the model" (fn () =>
  let
    val base = mf |> upd_card [(SOME ``:num list``, [2]), (SOME ``:num``, [2]),
                               (NONE, [2])]
    val goal = ``(xs : num list) = []``
  in
    refute (base |> upd_need (SOME [``[1] : num list``])) goal
    |> cex_where (fn c =>
         case #model c of
             SOME {types, ...} =>
               List.exists (fn (ty, values, _) =>
                 ty = ``:num list`` andalso length values = 2 andalso
                 Term.aconv (List.nth (values, 1)) ``[1] : num list``) types
           | NONE => false) andalso
    unknown_with "no counterexample within the tested scopes"
      (refute (base |> upd_need (SOME [``[0] : num list``, ``[1] : num list``]))
              goal) andalso
    refute (mf |> upd_need (SOME [``SOME T``])) ``T`` == NoCounterexample
    andalso refute base ``(b : bool) \/ ~b`` == NoCounterexample andalso
    is_cex (refute base ``(xs : bool list) = []``)
  end)

val binary_ints_warning =
  "binary_ints\" will be ignored because of the presence of rationals"

val _ = mf_level2 "rat goals use the Frac encoding" (fn () =>
  let
    val (outcome, text) = capture 2 (fn () =>
      refute (mf |> binary |> cards [3] |> upd_quiet false)
             ``rat$rat_add x rat$rat_0 = rat$rat_0``)
  in
    outcome |> cex_where (fn c =>
      #backend c = "kodkod" andalso #substrate c = "kodkod" andalso
      List.exists (fn (_, v) => String.isSubstring " // "
                                  (Parse.term_to_string v)) (#bindings c))
    andalso String.isSubstring " // " text andalso
    String.isSubstring binary_ints_warning text
  end)

val _ = mf_level2 "real goals use the Frac encoding" (fn () =>
  let
    fun real_literal v =
      realSyntax.is_real_literal v orelse
      (realSyntax.is_div v andalso
       realSyntax.is_real_literal (#1 (realSyntax.dest_div v)) andalso
       realSyntax.is_real_literal (#2 (realSyntax.dest_div v)))
    val (outcome, text) = capture 2 (fn () =>
      refute (mf |> binary |> cards [3] |> upd_quiet false)
             ``realax$real_add x (0 : real) = (0 : real)``)
  in
    outcome |> cex_where (fn c =>
      #backend c = "kodkod" andalso
      List.exists (fn (v, x) =>
        real_literal x andalso
        String.isSubstring (Parse.term_to_string v ^ " = " ^
                            Parse.term_to_string x) text) (#bindings c))
    andalso String.isSubstring binary_ints_warning text
  end)

val _ = mf_level2 "real functions outside Frac are never Genuine" (fn () =>
  let
    val cfg = mf |> cards [2]
    val _ = refute (cfg |> upd_expect ExpectPotential)
                   ``real$sup (\r. r = (x : real)) = x + 1``
    val (_, text) = capture 2 (fn () =>
      refute (cfg |> upd_expect ExpectUnknown |> upd_quiet false)
             ``hreal_of_real (real_of_hreal h) = h``)
  in
    String.isSubstring "potentially spurious" text
  end)

val _ = mf_level2 "merge_type_vars trades scopes for coverage" (fn () =>
  let
    val base = mf |> cards (List.tabulate (71, fn _ => 1))
      |> upd_mono [(NONE, SOME false)] |> upd_finitize [(NONE, SOME false)]
      |> upd_need (SOME [``need_only : 'a``]) |> upd_max_potential 0
    val goal = ``(f : 'z -> 'z) x = f y ==> x = y``
  in
    unknown_with "scope limit reached; consider using \"mono\" or \
                 \\"merge_type_vars\" to prevent this"
      (refute (base |> upd_merge_type_vars false) goal) andalso
    unknown_with "no counterexample within the tested scopes"
      (refute (base |> upd_merge_type_vars true) goal)
  end)

val _ = mf_level2 "Num on atom-represented integers" (fn () =>
  let
    val cfg = mf |> unary |> cards [1, 2, 3, 4, 5, 6, 7, 8]
    fun sound goal =
      unknown_with "no counterexample within the tested scopes"
        (refute cfg goal)
  in
    is_cex (refute cfg ``!i : int. i < 0 ==> Num i = 0``) andalso
    sound ``!i : int. Num (-i) = Num i`` andalso
    sound ``!n : num. Num (&n) = n`` andalso
    sound ``Num (-1 : int) = 1`` andalso
    is_cex (refute cfg ``Num (-1 : int) = 2``)
  end)

val _ = mf_level2 "certificates replay at large and structured scopes"
  (fn () =>
    let
      val single = mf |> upd_batch_size 1 |> upd_max_potential 0
        |> upd_max_genuine 1
      fun replays cfg goal =
        refute cfg goal |> single_cex_where (clean_certificate goal)
    in
      replays (single |> upd_card [(SOME ``:num``, [32]), (NONE, [1])]
                 |> upd_need (SOME [``30 : num``, ``31 : num``]))
        ``(?x : num. p x) ==> !x. p x`` andalso
      refute (single |> upd_card [(SOME ``:num``, [7]), (NONE, [1])])
             ``(r : num -> num -> bool) x y ==> r y x``
      |> single_cex_where (fn c =>
           clean_certificate ``(r : num -> num -> bool) x y ==> r y x`` c
           andalso #backend c = "kodkod" andalso
           scope_of c ``:num`` = SOME 7 andalso
           List.exists (fn (_, v) =>
             List.exists (fn fv => #1 (Term.dest_var fv) = "?")
               (Term.free_vars v)) (#bindings c)) andalso
      replays (single |> upd_card [(SOME ``:num list``, [2]),
                                   (SOME ``:num``, [1]), (NONE, [1])]
                 |> upd_need (SOME [``[0] : num list``, ``[] : num list``]))
        ``(?xs : num list. xs = [0]) ==> !ys : num list. ys = [0]`` andalso
      replays (single |> upd_card [(SOME ``:zoo_tree``, [2]),
                                   (SOME ``:num``, [1]), (NONE, [1])]
                 |> upd_need (SOME [``ZooLeaf 0``,
                                    ``ZooNode (ZooLeaf 0) (ZooLeaf 0)``]))
        ``(?t : zoo_tree. t = ZooLeaf 0) ==> !u : zoo_tree. u = ZooLeaf 0``
    end)

(* ------------------------------------------------------------------- *)
(* Potential counterexamples and retries.  Registers a restricted       *)
(* ``:num list`` generator, so this stays last.                         *)
(* ------------------------------------------------------------------- *)

val _ = section "potential counterexamples"

val _ = register_generator ``:num list``
  {enumerate = SOME (fn _ => [``[] : num list``, ``[0] : num list``]),
   random = NONE}

val hd_if = ``HD (xs : num list) = if xs = [] then HD ys else HD xs``

val _ = test "a stuck evaluation is Potential only on request" (fn () =>
  not (is_cex (refute corpus_config hd_if)) andalso
  refute (corpus_config |> upd_abort_potential true) hd_if
  |> cex_where (fn c => is_potential c andalso uncertified c) andalso
  not (is_cex (refute (corpus_config |> upd_genuine_only true) hd_if)))

val _ = test "a certifiable hit is upgraded to Genuine" (fn () =>
  refute (corpus_config |> upd_expect ExpectGenuine)
         ``~(HD (MAP (f : num -> num) xs) = f (HD xs))``
  |> cex_where (fn c => is_genuine c andalso Option.isSome (#cert c)))

val _ = exit_count0 erc
