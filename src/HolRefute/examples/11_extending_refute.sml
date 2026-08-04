(* ===================================================================== *)
(*  HolRefute by example, 11: adding your own machinery                  *)
(*                                                                       *)
(*  The registries that let a library extend Refute rather than merely     *)
(*  configure it: a new backend, its certainty ceiling, the theorem sets   *)
(*  the model finder preprocesses with, and the ersatz table that swaps    *)
(*  one constant for another during translation.                          *)
(*                                                                       *)
(*      ../../bin/hol --holstate=refuteheap \                            *)
(*          < examples/11_extending_refute.sml                           *)
(* ===================================================================== *)

load "Refute";
open Refute;

(* Extending Refute means touching the registries themselves, so this     *)
(* file reaches into implementation modules more often than the rest of   *)
(* the corpus does.  Noted once here rather than at each point of use:    *)
(* Refute_Core.refute_simp (section 3), Refute_Eval.get_substrates        *)
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
(* --------------------------------------------------------------------- *)

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
(*     section 9 of 09_model_finder.sml shows for :int.                  *)

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
(* compiling the smart plan itself.  See Refute_Eval.sig for the record   *)
(* a substrate has to supply, and Refute_EvalCompute.sml for the          *)
(* smallest complete implementation to copy from.                        *)
(* --------------------------------------------------------------------- *)

map (fn substrate => (#name substrate, #priority substrate))
  (Refute_Eval.get_substrates ());
(* ==> [("native", 10), ("cv", 20), ("compute", 30)]                     *)

(* --------------------------------------------------------------------- *)
(* 6.  Putting a session back the way you found it                       *)
(*                                                                       *)
(* Every registry above is session-local ML state: no theory content was   *)
(* created, so a fresh session is a clean slate.  Within one session there *)
(* is no way back: registration is idempotent per name, so re-registering  *)
(* the built-ins refreshes their entries without duplicating them, but the *)
(* demo backends of sections 1 and 2 stay registered, and so does the      *)
(* ersatz entry of section 4.                                            *)
(* --------------------------------------------------------------------- *)

map #name (Refute_Core.registered_backends ());
(* ==> ["demo", "weak-demo", "exhaustive", "random", "narrowing",        *)
(* ==>  "kodkod"]                                                        *)

Refute_QC.register_backends ();
Refute_QC_Narrow.register_backend ();
Refute_ModelFinder.register_backends ();

map #name (Refute_Core.registered_backends ());
(* ==> ["demo", "weak-demo", "exhaustive", "random", "narrowing",        *)
(* ==>  "kodkod"] — the built-ins are back to their standard entries,    *)
(* ==> the demo backends are still there.                                *)
