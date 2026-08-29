Theory refuteCvCleanPredComp
Ancestors
  refute_cv refuteTableZoo
Libs
  Refute

(* The predicate compiler added three new per-call translations: a
   negative-mode complement, a static-parameter-specialised enumerator,
   and a graph/inverting enumerator.  Only the specialised and graph
   translations compile through [Refute_EvalEnum.define]: for a
   pure-complement plan like the negation fixture's,
   [Refute_Eval.plan_uses_enum] is false, so
   [Refute_EvalCv.compile_card] routes it to
   [Refute_EvalCv.define_exhaustive_search]'s own, uninstrumented
   [TotalDefn.Define] instead -- see the comment above the negation
   fixture below.  That is true of *this* negation fixture, not of the
   complement translation in general: a goal with both a negated
   premise and a positive enumerator premise compiles to a plan
   carrying both a complement and an [Enum], [plan_uses_enum] is then
   true, and the [define] hook does fire for it.  That shape is not
   exercised anywhere in this theory.

   This theory demonstrates each translation that does reach [define] is
   inside the snapshot/revert bracket on the paths [exercise] below
   drives, over both the pre-registered builtin types the other fixtures
   use and a locally declared datatype, and through both the cv and
   compute substrates -- by exercising it against a fresh theory and
   letting the companion Check theory inspect what, if anything,
   survived.  A residue check on the persisted theory lives in
   [refuteCvCleanPredCompCheckScript]; its allow-list names every
   binding [predcomp_tree] and [predcomp_sg_listall] below introduce. *)

(* The only locally declared datatype any predicate-compiler fixture
   ranges over: every other fixture ranges over [num], [num list] or
   [num # num], which are all pre-registered in [refute_cv]'s builtin
   table, so none of them ever reaches
   [Refute_EvalCv.synthesise_generators] or
   [cv_typeLib.from_term_for]/[to_term_for].  [predcomp_sg_listall]
   mirrors [refuteTableZoo]'s [zoo_sg_listall] with the element type
   replaced by [predcomp_tree], so its enumerator plan compiles the
   same static-parameter-specialised shape but over a type Refute must
   synthesise a generator and a cv translation for from scratch. *)
Datatype:
  predcomp_tree = PredCompLeaf num | PredCompNode predcomp_tree predcomp_tree
End

Inductive predcomp_sg_listall:
  (!P. predcomp_sg_listall P []) /\
  (!P (t : predcomp_tree) ts. P t /\ predcomp_sg_listall P ts ==>
     predcomp_sg_listall P (t :: ts))
End

val neg_goal =
  ``~zoo_sg_duplicate (n : num) (p : num # num) ==> p = (n, n)``
val specialised_goal =
  ``zoo_sg_listall (\n:num. n = 500) (xs:num list) ==> LENGTH xs <= 2``
val graph_goal =
  ``(xs : num list) ++ ys = [1;2;3] ==> LENGTH xs <> 1``
val datatype_goal =
  ``predcomp_sg_listall (\t:predcomp_tree. t = PredCompLeaf 0)
      (ts:predcomp_tree list) ==> LENGTH ts <= 2``

val base_config =
  Refute.default_config
  |> Refute.upd_substrate Refute.Cv
  |> Refute.upd_sequential true
  |> Refute.upd_certify false
  |> Refute.upd_size 2
  |> Refute.upd_depth 2
val graph_config = Refute.upd_allow_function_inversion true base_config
val compute_config = Refute.upd_substrate Refute.Compute base_config

fun contains_complement plan =
  case plan of
      Refute_Eval.Guard {smart, cont, ...} =>
        smart orelse contains_complement cont
    | Refute_Eval.Gen (_, next) => contains_complement next
    | Refute_Eval.Bind (_, _, fallback, next) =>
        contains_complement next orelse
        Option.getOpt (Option.map contains_complement fallback, false)
    | Refute_Eval.Split (_, branches) =>
        List.exists (contains_complement o #3) branches
    | Refute_Eval.SmartGuard {cont, ...} => contains_complement cont
    | Refute_Eval.Enum {cont, ...} => contains_complement cont
    | _ => false

fun contains_fixed_output_enum plan =
  case plan of
      Refute_Eval.Enum
        {mode = Refute_SmartGen.Fun (Refute_SmartGen.Fixed _,
          Refute_SmartGen.Fun (Refute_SmartGen.Output, _)), ...} => true
    | Refute_Eval.Gen (_, next) => contains_fixed_output_enum next
    | Refute_Eval.Bind (_, _, fallback, next) =>
        contains_fixed_output_enum next orelse
        Option.getOpt (Option.map contains_fixed_output_enum fallback, false)
    | Refute_Eval.Split (_, branches) =>
        List.exists (contains_fixed_output_enum o #3) branches
    | Refute_Eval.Guard {cont, ...} => contains_fixed_output_enum cont
    | Refute_Eval.SmartGuard {cont, ...} => contains_fixed_output_enum cont
    | Refute_Eval.Enum {cont, ...} => contains_fixed_output_enum cont
    | _ => false

fun contains_graph_enum plan =
  case plan of
      Refute_Eval.Enum {rel = Refute_SmartGen.Graph _, ...} => true
    | Refute_Eval.Gen (_, next) => contains_graph_enum next
    | Refute_Eval.Bind (_, _, fallback, next) =>
        contains_graph_enum next orelse
        Option.getOpt (Option.map contains_graph_enum fallback, false)
    | Refute_Eval.Split (_, branches) =>
        List.exists (contains_graph_enum o #3) branches
    | Refute_Eval.Guard {cont, ...} => contains_graph_enum cont
    | Refute_Eval.SmartGuard {cont, ...} => contains_graph_enum cont
    | Refute_Eval.Enum {cont, ...} => contains_graph_enum cont
    | _ => false

fun plan_for shape_ok config goal =
  let val plan = Refute_QC.compile_plan config goal
  in
    if shape_ok plan then plan
    else raise Fail
      "predicate-compiler fixture did not compile to the expected shape"
  end

fun compile_with compile_fn label config plan =
  case compile_fn config Refute_Eval.Exhaustive
    (Refute_Eval.Plans [plan]) of
      Refute_Eval.Compiled test => test
    | Refute_Eval.Inapplicable reasons =>
        raise Fail (label ^
          " substrate refused a predicate-compiler fixture: " ^
          String.concatWith "; " reasons)

val compile_low = compile_with Refute_EvalCv.compile "cv"
val compile_low_compute = compile_with Refute_EvalCompute.compile "compute"

val run_input : Refute_Eval.run_input =
  {genuine_only = false, card = 1, size = 2, draws = 0, ignored = []}

(* Normal completion: compile, run to a verdict, close. *)
fun run_normal shape_ok config goal =
  let
    val plan = plan_for shape_ok config goal
    val test = compile_low config plan
  in
    Portable.finally (#close test) (fn () => ignore (#run test run_input)) ()
  end

(* The compute substrate's own [Refute_EvalEnum.define] call
   ([Refute_EvalCompute.exhaustive_compile]) is otherwise untested by any
   theory_tests script -- the selftest's own compute pins exercise it, but
   nothing checks it for residue.  This runs one fixture through it, under
   the same bracket, so compute-created definitions land inside this
   theory's residue check too. *)
fun run_normal_compute shape_ok config goal =
  let
    val plan = plan_for shape_ok config goal
    val test = compile_low_compute config plan
  in
    Portable.finally (#close test) (fn () => ignore (#run test run_input)) ()
  end

(* Compilation commits the per-call definition eagerly -- it has already
   landed once [compile_low] returns -- but the run itself never happens
   before the bracket closes.  This is NOT a deadline/interrupt test: a
   real deadline reaches [Refute_QC.bounded_close] from a different
   thread with an interrupt in flight, which is why [Refute_EvalEnum]
   uses an ownerless [Synchronized.var] and wraps [close_held_bracket] in
   [Thread_Attributes.uninterruptible].  This closes synchronously on the
   compiling thread instead, so the interrupt/timeout path is not covered
   here; only "compiled, never run, closed" is. *)
fun run_compiled_unrun shape_ok config goal =
  let
    val plan = plan_for shape_ok config goal
    val test = compile_low config plan
  in
    #close test ()
  end

exception ForcedPredCompCvFailure

(* Exception raised from inside a compiled enumerator's own
   post-definition step: [post_definition_failure_hook] fires only after
   the per-call definition (and its cv translation) has actually landed,
   so this exercises cleanup racing a mutation already committed.  On the
   path where the hook never fires, [compile_low] returns normally and
   the compiled test is closed explicitly, so the bracket is never left
   open regardless of which path is taken. *)
fun run_exception shape_ok config goal =
  let
    val hook = Refute_EvalEnum.post_definition_failure_hook
    val old_hook = !hook
    fun restore () = hook := old_hook
    fun fail _ = raise ForcedPredCompCvFailure
  in
    Portable.finally restore (fn () =>
      (hook := SOME fail;
       (let
          val test = compile_low config (plan_for shape_ok config goal)
        in
          Portable.finally (#close test) (fn () => ()) ();
          false
        end)
       handle ForcedPredCompCvFailure => true)) ()
  end

fun exercise name shape_ok config goal =
  let
    val _ = run_normal shape_ok config goal
    val _ = run_compiled_unrun shape_ok config goal
    val raised = run_exception shape_ok config goal
  in
    if raised then ()
    else raise Fail (name ^
      ": forced post-definition failure did not propagate")
  end

(* [negation_condition] (Refute_EvalEnum.sml) builds the complement as a
   raw term at plan-compile time and never calls [Refute_EvalEnum.define]:
   a pure-complement plan like [neg_goal]'s routes entirely through
   [Refute_EvalCv.define_exhaustive_search]'s own, uninstrumented
   [TotalDefn.Define] call for the generic bounded-search driver, so
   [post_definition_failure_hook] never fires for it -- confirmed
   empirically: arming the hook and running this goal completes without
   raising.  There is no predicate-compiler-specific per-call definition
   here to inject a fault into, so only the normal and compiled-but-unrun
   paths apply. *)
val _ = run_normal contains_complement base_config neg_goal
val _ = run_compiled_unrun contains_complement base_config neg_goal
val _ = exercise "static-parameter specialisation"
  contains_fixed_output_enum base_config specialised_goal
val _ = exercise "graph/inverting enumerator" contains_graph_enum
  graph_config graph_goal
val _ = exercise "user-datatype specialisation"
  contains_fixed_output_enum base_config datatype_goal
val _ = run_normal_compute contains_fixed_output_enum compute_config
  specialised_goal
