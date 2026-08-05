(* ===================================================================== *)
(*  HolRefute by example, 11: adding your own machinery                  *)
(*                                                                       *)
(*  The registries that let a library extend Refute rather than merely     *)
(*  configure it: a new backend, its certainty ceiling, the theorem sets   *)
(*  the model finder preprocesses with, and the ersatz table that swaps    *)
(*  one constant for another during translation.                          *)
(*                                                                       *)
(* ===================================================================== *)

Theory refuteExample11
Ancestors
  refute
Libs
  Refute

open Refute;

(* Extending Refute means touching the registries themselves, so this     *)
(* file reaches into implementation modules more often than the rest of   *)
(* the corpus does.  Noted once here rather than at each point of use:    *)
(* Refute_Core.refute_simp, Refute_Core.refute_psimp and                  *)
(* Refute_Core.refute_unfold (section 3), Refute_Eval.get_substrates      *)
(* (section 5), and Refute_Core.registered_backends,                      *)
(* Refute_QC.register_backends, Refute_QC_Narrow.register_backend and     *)
(* Refute_ModelFinder.register_backends (section 6) belong to             *)
(* implementation modules, not to Refute.sig.  The one other qualified    *)
(* name below, the type Refute_Core.instance in section 1, is not a       *)
(* reach: Refute.sig re-exports it as [instance].  Everything else used   *)
(* here is in Refute.sig.                                                 *)

(* --------------------------------------------------------------------- *)
(* 1.  A backend is a record                                             *)
(*                                                                       *)
(*   name        how it is selected by upd_backends and reported.         *)
(*   weight      tie-break order when two backends agree in strength.     *)
(*   configured  whether it can run at all in this session (an external   *)
(*               tool would check its installation here).                 *)
(*   requires    AnyGoal, ExecutableGoal, or ExecutableGoalUnless.        *)
(*   input       MonoInstances for monomorphised instances, PolyOriginal  *)
(*               to see the goal as written.                             *)
(*   run         config -> instance list -> outcome.                      *)
(*                                                                       *)
(* This toy backend refutes exactly one shape of goal — a variable        *)
(* equated to itself under negation — and declines everything else.       *)
(* --------------------------------------------------------------------- *)

fun trivial_run config instances =
  let
    fun refutes (instance : Refute_Core.instance) =
      Term.aconv (#goal instance) boolSyntax.F
  in
    if List.exists refutes instances then
      Counterexample
        [{backend = "demo", substrate = "demo", certainty = Genuine,
          bindings = [], evals = [], cert = NONE, scope = NONE,
          model = NONE, stats = [("tests", 1)]}]
    else
      Unknown ["demo backend: goal is not literally F"]
  end;

val demo_backend : backend =
  {name = "demo", weight = 5, configured = fn () => true,
   requires = AnyGoal, input = MonoInstances, run = trivial_run};

register_backend demo_backend;

(* The counterexample carries certainty Genuine with cert = NONE, so it   *)
(* is reported as uncertified: the core believes a backend that claims    *)
(* Genuine, it does not re-check the claim.                              *)
refute
  (!the_config
     |> upd_backends (SOME ["demo"])
     |> upd_expect ExpectGenuine)
  ``F``;
(* ==> Refute found a counterexample (backend: demo, substrate: demo)    *)
(* ==> Certification: uncertified                                        *)

refute
  (!the_config
     |> upd_backends (SOME ["demo"])
     |> upd_expect ExpectUnknown)
  ``(x : num) = x``;
(* ==> Unknown ["demo: demo backend: goal is not literally F"]           *)

(* Selecting a backend that was never registered is an error, not a       *)
(* silent no-op.                                                         *)
refute
  (!the_config
     |> upd_backends (SOME ["no-such-backend"])
     |> upd_expect ExpectUnknown)
  ``F``;
(* ==> Unknown ["unknown requested backend: no-such-backend"]            *)

(* The two fields the backend above leaves at their weakest settings,    *)
(* [requires] and [input], are what the rest of this section is about.   *)
(*                                                                       *)
(* [requires] is checked before [run] is ever called.  Preprocessing     *)
(* tags each instance with a gate: none when the instance is inside the  *)
(* executable fragment, otherwise the reasons it is not.  A backend      *)
(* requiring [ExecutableGoal] is dropped from the race unless every      *)
(* instance is ungated, and when that leaves nothing to run the answer   *)
(* is Unknown carrying the gate's own reasons — the backend never sees   *)
(* the goal at all.                                                      *)

fun executable_run config instances =
  Unknown ["exec-demo was invoked, so every instance was ungated"];

val exec_backend : backend =
  {name = "exec-demo", weight = 7, configured = fn () => true,
   requires = ExecutableGoal, input = MonoInstances, run = executable_run};

register_backend exec_backend;

(* Section 8 of example 03 uses this goal for the    *)
(* same reason: its inner existential survives quantifier expansion, so  *)
(* no instance is executable.                                            *)

val nested_goal = ``!xs : num list. ?ys. xs = ys ++ ys``;

refute
  (!the_config
     |> upd_backends (SOME ["exec-demo"])
     |> upd_expect ExpectUnknown)
  nested_goal;
(* ==> Unknown ["not executable: unexpanded binder"]                     *)

(* The demo backend of the opening asks for [AnyGoal], so on the same    *)
(* goal it is invoked and answers for itself.                            *)
refute
  (!the_config
     |> upd_backends (SOME ["demo"])
     |> upd_expect ExpectUnknown)
  nested_goal;
(* ==> Unknown ["demo: demo backend: goal is not literally F"]           *)

(* Given a goal inside the fragment, exec-demo runs like any other.      *)
refute
  (!the_config
     |> upd_backends (SOME ["exec-demo"])
     |> upd_expect ExpectUnknown)
  ``REVERSE (xs : num list) = xs``;
(* ==> Unknown ["exec-demo: exec-demo was invoked, so every instance     *)
(* ==>          was ungated"]                                            *)

(* [input] chooses which form of the goal the backend is handed.         *)
(* Preprocessing builds both: [MonoInstances] is one instance per        *)
(* monomorphising substitution, each type variable replaced by the rf    *)
(* type of one cardinality, while [PolyOriginal] is the single instance  *)
(* whose type variables are left standing.  The two backends below       *)
(* differ in nothing else, and report the types their instances gave     *)
(* the goal's first free variable.                                       *)

fun form_run config (instances : Refute_Core.instance list) =
  let
    fun variable_type (instance : Refute_Core.instance) =
      Parse.type_to_string
        (Term.type_of (hd (Term.free_vars_lr (#goal instance))))
  in
    Unknown
      [Int.toString (List.length instances) ^ " instance(s), xs : " ^
       String.concatWith ", " (map variable_type instances)]
  end;

val poly_backend : backend =
  {name = "poly-demo", weight = 8, configured = fn () => true,
   requires = AnyGoal, input = PolyOriginal, run = form_run};

val mono_backend : backend =
  {name = "mono-demo", weight = 9, configured = fn () => true,
   requires = AnyGoal, input = MonoInstances, run = form_run};

register_backend poly_backend;
register_backend mono_backend;

val poly_goal = ``(xs : 'a list) ++ ys = ys ++ xs``;

refute
  (!the_config
     |> upd_backends (SOME ["poly-demo"])
     |> upd_expect ExpectUnknown)
  poly_goal;
(* ==> Unknown ["poly-demo: 1 instance(s), xs : :'a list"]               *)

refute
  (!the_config
     |> upd_backends (SOME ["mono-demo"])
     |> upd_expect ExpectUnknown)
  poly_goal;
(* ==> Unknown ["mono-demo: 3 instance(s), xs : :rf1 list, :rf2 list,    *)
(* ==>          :rf3 list"]                                              *)

(* [ExecutableGoalUnless] carries the predicate that decides a waiver,   *)
(* config -> instance list -> bool, and is consulted only when the goal  *)
(* is outside the fragment.  This one waives the requirement whenever    *)
(* [genuine_only] is not set, so a single backend covers both regimes    *)
(* under the flag section 2 uses.                                        *)

fun lenient_run config instances =
  Unknown ["lenient-demo was invoked under the waiver"];

val lenient_backend : backend =
  {name = "lenient-demo", weight = 10, configured = fn () => true,
   requires = ExecutableGoalUnless
     (fn config : config => fn _ => not (#genuine_only config)),
   input = MonoInstances, run = lenient_run};

register_backend lenient_backend;

refute
  (!the_config
     |> upd_backends (SOME ["lenient-demo"])
     |> upd_expect ExpectUnknown)
  nested_goal;
(* ==> Unknown ["lenient-demo: lenient-demo was invoked under the        *)
(* ==>          waiver"]                                                 *)

refute
  (!the_config
     |> upd_backends (SOME ["lenient-demo"])
     |> upd_genuine_only true
     |> upd_expect ExpectUnknown)
  nested_goal;
(* ==> Unknown ["not executable: unexpanded binder"]                     *)

(* --------------------------------------------------------------------- *)
(* 2.  Declaring how strong a backend can get                            *)
(*                                                                       *)
(* A backend race stops as soon as a result reaches the best certainty     *)
(* any selected backend could still produce — the maximum of the declared  *)
(* ceilings of the backends actually selected.  [register_backend] assumes *)
(* the conservative ceiling Genuine; a backend that can only ever produce  *)
(* Potential results should say so with                                    *)
(* [register_backend_with_ceiling], which lets the race stop earlier.      *)
(* Overestimating the ceiling only forgoes an early stop, whereas          *)
(* underestimating it can hide a stronger result — so when in doubt,       *)
(* overestimate.                                                          *)
(*                                                                       *)
(* The ceiling changes when the race stops, not what a single backend      *)
(* returns, so the transcript below looks the same either way; what it     *)
(* does show is the contract being honoured, the declared ceiling          *)
(* Potential bounding the Potential result that [weak_run] returns.        *)
(* --------------------------------------------------------------------- *)

fun weak_run (config : config) instances =
  if #genuine_only config then
    (* [genuine_only] is passed through to the backends in the config; the *)
    (* core does not filter results by it, so a backend has to honour it   *)
    (* itself, as here.                                                   *)
    Unknown ["weak-demo: genuine_only is set and nothing here certifies"]
  else
    Counterexample
      [{backend = "weak-demo", substrate = "demo",
        certainty = Potential ["demo backend never certifies"],
        bindings = [], evals = [], cert = NONE, scope = NONE,
        model = NONE, stats = []}];

val weak_backend : backend =
  {name = "weak-demo", weight = 6, configured = fn () => true,
   requires = AnyGoal, input = MonoInstances, run = weak_run};

register_backend_with_ceiling weak_backend
  (fn _ => fn _ => Potential ["demo backend never certifies"]);

refute
  (!the_config
     |> upd_backends (SOME ["weak-demo"])
     |> upd_expect ExpectPotential)
  ``(x : num) = x``;
(* ==> Refute found a counterexample (backend: weak-demo, ...)           *)
(* ==> Potential counterexample:                                         *)
(* ==>   demo backend never certifies                                    *)
(* ==> …continuing search for a genuine counterexample                    *)
(*                                                                       *)
(* That last line is how any Potential result is rendered; it is not      *)
(* evidence about the race, which had only this one backend to run.       *)

(* With genuine_only set, this backend declines rather than offering a    *)
(* candidate it knows will be rejected.                                  *)
refute
  (!the_config
     |> upd_backends (SOME ["weak-demo"])
     |> upd_genuine_only true
     |> upd_expect ExpectUnknown)
  ``(x : num) = x``;
(* ==> Unknown ["weak-demo: weak-demo: genuine_only is set and nothing   *)
(* ==>          here certifies"]                                         *)

(* --------------------------------------------------------------------- *)
(* 3.  Theorem sets used by model-finder preprocessing                   *)
(*                                                                       *)
(* Three ThmSetData sets steer preprocessing: refute_simp (rewrites),     *)
(* refute_psimp (partial-function rewrites) and refute_unfold             *)
(* (definitions to unfold).  A theory exports into them by name, exactly  *)
(* as it would export a simpset fragment.                                *)
(*                                                                       *)
(* The support theory seeds two of the three, so the quickest way to see *)
(* what each is for is to read what it already holds.                    *)
(* --------------------------------------------------------------------- *)

#getDB Refute_Core.refute_psimp ();
(* ==> [|- P x ==> ~P y ==> $@ P = y ==> $@ P = x]                       *)

#getDB Refute_Core.refute_unfold ();
(* ==> [|- RC R x y <=> x = y \/ R x y, |- R^* = RC R^+,                 *)
(* ==>  |- num_CASE n z f = if n = 0 then z else f (n - 1),              *)
(* ==>  |- one_CASE u x = x]                                             *)

(* [refute_psimp] carries partial-function rewrites: conditional         *)
(* equations that pin an underspecified constant down where it is        *)
(* determined and say nothing where it is not.  The entry above is       *)
(* about [$@] on a predicate that holds at one point and fails at        *)
(* another.  [refute_unfold] carries definitional restatements —         *)
(* equations the translation can rewrite with instead of having to       *)
(* encode the constant structurally, as the two case constants and the   *)
(* two closure operators above show.                                     *)

val double_def = Define `double (n : num) = n + n`;

val double_alt = save_thm ("double_alt",
  prove (``!n. double n = 2 * n``, simp [double_def]));

export_refute_simp "double_alt";

(* The export is visible immediately, in this session, through the set's  *)
(* own accessor.                                                         *)
List.exists (fn theorem =>
    Term.aconv (Thm.concl theorem) (Thm.concl double_alt))
  (#getDB Refute_Core.refute_simp ());
(* ==> true                                                              *)

(* The model finder now has both the definition and the restatement to    *)
(* work with.  (This goal is easy enough that it would fall either way —  *)
(* the export is about which form the translation sees, not about         *)
(* reaching an answer at all.)                                           *)
refute
  (!the_config
     |> upd_backends (SOME ["kodkod"])
     |> upd_max_threads 1
     |> upd_card [(NONE, [3])]
     |> upd_expect ExpectGenuine)
  ``double n = n``;
(* ==> Refute found a counterexample (backend: kodkod, substrate:        *)
(*       kodkod):                                                        *)
(*       Scope: card unsigned_bit bitword = 3, card unsigned_bit = 2     *)
(*         n = 1                                                         *)
(*       Certified: |- ~!n. double n = n                                 *)
(*     The [upd_card] row bounds whatever types the translation builds,  *)
(*     which here are the bitword types a binary representation of :num  *)
(*     introduces rather than :num itself — the same substitution        *)
(*     section 9 of example 09 shows for :int.                  *)

(* The other two sets are exported into the same way.  [TL] is           *)
(* underspecified at the empty list exactly as [$@] is at a predicate    *)
(* with no witness, so a guarded equation against a total function is    *)
(* what [refute_psimp] wants.                                            *)

val tl_psimp = save_thm ("tl_psimp",
  prove (``!xs : 'a list. xs <> [] ==> TL xs = DROP 1 xs``,
         Cases_on `xs` >> simp []));

export_refute_psimp "tl_psimp";

List.exists (fn theorem =>
    Term.aconv (Thm.concl theorem) (Thm.concl tl_psimp))
  (#getDB Refute_Core.refute_psimp ());
(* ==> true                                                              *)

(* And a case constant restated as a conditional is what                 *)
(* [refute_unfold] wants — the option counterpart of the [num_CASE]      *)
(* and [one_CASE] entries the support theory already supplies.           *)

val option_case_unfold = save_thm ("option_case_unfold",
  prove (``option_CASE (opt : 'a option) (n : 'b) f =
             if opt = NONE then n else f (THE opt)``,
         Cases_on `opt` >> simp []));

export_refute_unfold "option_case_unfold";

List.exists (fn theorem =>
    Term.aconv (Thm.concl theorem) (Thm.concl option_case_unfold))
  (#getDB Refute_Core.refute_unfold ());
(* ==> true                                                              *)

(* --------------------------------------------------------------------- *)
(* 4.  Ersatz constants                                                  *)
(*                                                                       *)
(* An ersatz entry tells the model finder to translate one constant as if  *)
(* it were another — the mechanism behind the built-in rational encoding.  *)
(* Both names are given as Thy/Name records, so the substitution is exact  *)
(* rather than by printed name.                                          *)
(*                                                                       *)
(* Registering an entry asserts that the surrogate denotes the same      *)
(* function as the constant it replaces; nothing checks that.  A         *)
(* faithful substitution changes no model in either direction, so it     *)
(* holds back no verdict — break the contract and the answer is simply   *)
(* wrong, as the deliberate swap below shows.                            *)
(* --------------------------------------------------------------------- *)

val max_config =
  !the_config
    |> upd_backends (SOME ["kodkod"])
    |> upd_max_threads 1
    |> upd_card [(NONE, [3])];

refute (upd_expect ExpectNone max_config) ``!m n : num. m <= MAX m n``;
(* ==> NoCounterexample (the theorem is true)                            *)

register_ersatz
  {original = {Thy = "arithmetic", Name = "MAX"},
   replacement = {Thy = "arithmetic", Name = "MIN"}};

refute (upd_expect ExpectPotential max_config) ``!m n : num. m <= MAX m n``;
(* ==> Refute found a counterexample (backend: kodkod, substrate:        *)
(* ==>   kodkod):                                                        *)
(* ==>     Scope: card num = 3                                           *)
(* ==>     Skolem constants:                                             *)
(* ==>       m = 2                                                       *)
(* ==>       n = 1                                                       *)
(* ==>   Potential counterexample: evaluation stuck on: $<=              *)
(*     A true theorem now looks refutable, because the solver was        *)
(*     shown MIN where the goal says MAX.  The model's constants, which  *)
(*     [upd_show_consts true] would print, record MIN m n = 1.           *)
(*                                                                       *)
(* There is no deregistration hook: the entry above stays in force for    *)
(* the rest of this session (see section 6).  In particular, do not try   *)
(* to cancel it by registering the constant as its own replacement —      *)
(* that mapping is not recognised as an identity and the translation      *)
(* follows it until it gives up with TOO_LARGE.                          *)

(* --------------------------------------------------------------------- *)
(* 5.  Substrates are pluggable too                                     *)
(*                                                                       *)
(* [register_substrate] installs an alternative executor for QC test      *)
(* plans, which is how NativeSML, Cv and Compute are themselves added.    *)
(* Auto walks the registered substrates in priority order, and a          *)
(* replacement substrate may open a smart-generator gate only by          *)
(* compiling the smart plan itself.                                       *)
(* --------------------------------------------------------------------- *)

map (fn substrate => (#name substrate, #priority substrate))
  (Refute_Eval.get_substrates ());
(* ==> [("native", 10), ("cv", 20), ("compute", 30)]                     *)

(* A substrate record has five fields: the [name] every report will      *)
(* quote, the [priority] Auto orders by, [accepts] deciding which test   *)
(* plans it will take at all, an optional [preflight] and [compile].     *)
(* Borrowing the last three from an installed substrate gives an entry   *)
(* that executes exactly like Compute but answers to its own name and    *)
(* its own place in the order.                                           *)

val compute_substrate =
  valOf (List.find (fn substrate => #name substrate = "compute")
          (Refute_Eval.get_substrates ()));

val echo_substrate : substrate =
  {name = "echo", priority = 5, accepts = #accepts compute_substrate,
   preflight = #preflight compute_substrate,
   compile = #compile compute_substrate};

register_substrate echo_substrate;

map (fn substrate => (#name substrate, #priority substrate))
  (Refute_Eval.get_substrates ());
(* ==> [("echo", 5), ("native", 10), ("cv", 20), ("compute", 30)]        *)

(* Priority orders Auto, not registration time: 5 puts the newcomer      *)
(* ahead of native, which section 2 of example 04 *)
(* shows winning this same goal in a stock session.  Trace level 2 names *)
(* the substrate Auto settled on and every schedule entry it ran, and    *)
(* the counterexample's own substrate field carries the registered name, *)
(* so there is never any doubt about which executor answered.            *)

Feedback.set_trace "Refute" 2;
refute
  (!the_config
     |> upd_backends (SOME ["exhaustive"])
     |> upd_expect ExpectGenuine)
  ``REVERSE (xs : num list) = xs``;
(* ==> Refute: backend racing requested, but the session thread count    *)
(* ==>   is 1, so the backends run sequentially (--mt or                 *)
(* ==>   Multithreading.max_threads_update raises it)                    *)
(* ==> Refute backend started (weight 20): exhaustive                    *)
(* ==> Refute substrate selection: selected echo                         *)
(* ==> Refute schedule entry (backend: exhaustive, substrate: echo,      *)
(* ==>   card 1, size 1): 0ms                                            *)
(* ==> Refute schedule entry (backend: exhaustive, substrate: echo,      *)
(* ==>   card 1, size 2): 0ms                                            *)
(* ==> Refute schedule entry (backend: exhaustive, substrate: echo,      *)
(* ==>   card 1, size 3): 0ms                                            *)
(* ==> Refute found a counterexample (backend: exhaustive, substrate:    *)
(* ==>   echo, size 3):                                                  *)
(* ==>   xs = [0; 1]                                                     *)
(* ==> Certified: |- ~!xs. REVERSE xs = xs                               *)
(*     and the returned record has substrate = "echo".                   *)
Feedback.set_trace "Refute" 1;

(* echo now shadows native for every Auto run in this session, which is  *)
(* section 6's "no way back" in the small: registration is the only      *)
(* operation the substrate registry offers, so the only way to get       *)
(* native back at the head of the order is a fresh session.  That is     *)
(* why this demonstration sits at the end of the file.                   *)
(*                                                                       *)
(* See Refute_Eval.sig for the record a substrate has to supply, and     *)
(* Refute_EvalCompute.sml for the smallest complete implementation to    *)
(* copy from.                                                            *)

(* --------------------------------------------------------------------- *)
(* 6.  Putting a session back the way you found it                       *)
(*                                                                       *)
(* Every registry above is session-local ML state: no theory content was   *)
(* created, so a fresh session is a clean slate.  Within one session there *)
(* is no way back: registration is idempotent per name, so re-registering  *)
(* the built-ins refreshes their entries without duplicating them, but the *)
(* demo backends of sections 1 and 2 stay registered, the ersatz entry of  *)
(* section 4 stays in force, and the echo substrate of section 5 stays     *)
(* ahead of native in the Auto order.                                      *)
(*                                                                       *)
(* Backends are listed in weight order, so the demo backends of section  *)
(* 1 sort ahead of the built-ins rather than after them.                 *)
(* --------------------------------------------------------------------- *)

map #name (Refute_Core.registered_backends ());
(* ==> ["demo", "weak-demo", "exec-demo", "poly-demo", "mono-demo",      *)
(* ==>  "lenient-demo", "exhaustive", "random", "narrowing", "kodkod"]   *)

Refute_QC.register_backends ();
Refute_QC_Narrow.register_backend ();
Refute_ModelFinder.register_backends ();

map #name (Refute_Core.registered_backends ());
(* ==> ["demo", "weak-demo", "exec-demo", "poly-demo", "mono-demo",      *)
(* ==>  "lenient-demo", "exhaustive", "random", "narrowing", "kodkod"]   *)
(* ==> — the built-ins are back to their standard entries, the demo      *)
(* ==> backends are still there.                                         *)
