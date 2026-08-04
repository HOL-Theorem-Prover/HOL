(* ===================================================================== *)
(*  HolRefute by example, 2: reading verdicts, driving the configuration *)
(*                                                                       *)
(*  What "Genuine", "Potential" and "Unknown" mean, what the certifying  *)
(*  theorem is for, and the configuration knobs you reach for most:      *)
(*  timeout, backends, evals, expectations, tags, and trace level.       *)
(*                                                                       *)
(*      ../../bin/hol --holstate=refuteheap \                            *)
(*          < examples/02_verdicts_and_config.sml                        *)
(* ===================================================================== *)

load "Refute";
open Refute;

(* --------------------------------------------------------------------- *)
(* 1.  Genuine means "checked by the HOL kernel"                         *)
(*                                                                       *)
(* Execution substrates are untrusted accelerators.  A QC candidate is   *)
(* promoted to Genuine only after Refute re-evaluates the instantiated   *)
(* proposition with computeLib and proves its negation, and that theorem *)
(* is handed back in the [cert] field.  Refute adds no oracle tag of its *)
(* own, so the certificate stands on its own: the tag below lists only   *)
(* DISK_THM, HOL4's marker for a dependence on theorems read from a      *)
(* theory file.                                                          *)
(* --------------------------------------------------------------------- *)

val _ = the_config := upd_expect ExpectGenuine (!the_config);

val certified = refute_def ``(n : num) DIV 2 * 2 = n``;
(* ==> n = 1                                                             *)
(*     Certified: |- ~!n. n DIV 2 * 2 = n                                *)

val _ = the_config := default_config;

case certified of
    Counterexample ({cert = SOME theorem, ...} :: _) =>
      (print (Parse.thm_to_string theorem ^ "\n");
       Tag.dest_tag (Thm.tag theorem))
  | _ => raise Fail "expected a certified counterexample";
(* ==> val it = (["DISK_THM"], []): string list * string list            *)

(* --------------------------------------------------------------------- *)
(* 2.  Opting out of certification                                       *)
(*                                                                       *)
(* [upd_certify false] keeps the verdict but drops the proof: the report *)
(* then says "Certification: uncertified" and [cert] is NONE.  It is a   *)
(* speed knob for exploratory work, not a way to strengthen a verdict —  *)
(* candidates that are only Potential stay Potential.                    *)
(* --------------------------------------------------------------------- *)

refute
  (!the_config
     |> upd_certify false
     |> upd_expect ExpectGenuine)
  ``(n : num) DIV 2 * 2 = n``;

(* --------------------------------------------------------------------- *)
(* 3.  The three certainty levels                                        *)
(*                                                                       *)
(*   Genuine       - a real counterexample.  [cert] may still be NONE:   *)
(*                   [certainty] records the semantic strength of the    *)
(*                   result and [cert] records whether a HOL theorem was *)
(*                   built, and the two are independent axes.  Section 4 *)
(*                   below produces a Genuine result with cert = NONE.   *)
(*   QuasiGenuine  - a counterexample under stated caveats.              *)
(*   Potential     - a candidate Refute could not confirm; the report    *)
(*                   lists why and the search continues.  A QC hit whose *)
(*                   instantiated proposition will not evaluate back     *)
(*                   lands here — see section 1 of                       *)
(*                   05_smart_generators.sml — as does a model the       *)
(*                   kernel got stuck on; 09_model_finder.sml is the     *)
(*                   full story.                                         *)
(*                                                                       *)
(* [upd_genuine_only true] suppresses everything weaker than Genuine,    *)
(* and [upd_abort_potential true] stops the race at the first candidate  *)
(* of any strength.  Both, and every other knob, are printed with their  *)
(* current values by [show_config].                                      *)
(* --------------------------------------------------------------------- *)

show_config ();

(* --------------------------------------------------------------------- *)
(* 4.  Inconclusive goals report Unknown, never a false verdict          *)
(*                                                                       *)
(* [:ind] is infinite and carries no TypeBase enumeration, so the QC     *)
(* backends decline; the reasons name the backend, the substrate it      *)
(* tried, and what stopped it.                                           *)
(*                                                                       *)
(* All three calls below share one pinned configuration: a single        *)
(* Kodkodi thread and a single cardinality row.  That is the corpus      *)
(* convention for model-finder calls — see the header of                 *)
(* 10_model_finder_advanced.sml — and it is what makes the scope and     *)
(* the model quoted here exact instead of whichever scope won a race.    *)
(* --------------------------------------------------------------------- *)

val ind_config =
  !the_config
    |> upd_max_threads 1
    |> upd_card [(NONE, [2])];

refute
  (ind_config
     |> upd_backends (SOME ["exhaustive", "random"])
     |> upd_expect ExpectUnknown)
  ``(f : ind -> ind) x = x``;
(* ==> Unknown, first reason: "exhaustive: native: no generator for      *)
(*     :ind - no TypeBase information; register a generator"             *)

(* The model finder does have something to say about [:ind]: it searches *)
(* finite scopes and reconstructs a model there.  Its verdict is decided *)
(* by the encoding rather than by whether a theorem was built, and the   *)
(* translation of this goal is sound and exact, so the model is Genuine. *)
(* Nothing about an uninterpreted [f] over [:ind] is computable, so no   *)
(* certificate accompanies it and the report ends "uncertified" — the    *)
(* two axes of section 3 pulling apart.  (This needs a Kodkodi           *)
(* component; without one the call reports                               *)
(* Unknown ["no configured backend"] — see 09_model_finder.sml.)         *)

refute (upd_expect ExpectGenuine ind_config) ``(f : ind -> ind) x = x``;
(* ==> Refute found a counterexample (backend: kodkod, substrate:        *)
(*     kodkod):                                                          *)
(*       Scope: card ind = 2                                             *)
(*         f = (K _)⦇a2 ↦ a1; a1 ↦ a1⦈                                   *)
(*         x = a2                                                        *)
(*       Certification: uncertified                                      *)

(* [upd_genuine_only true] from section 3 therefore keeps it: it filters *)
(* on certainty, not on cert, and this candidate is already Genuine.  It *)
(* is section 4 of 09_model_finder.sml, where an abstract type leaves    *)
(* the witness unevaluable, that shows a model the filter does drop.     *)

refute
  (ind_config
     |> upd_genuine_only true
     |> upd_expect ExpectGenuine)
  ``(f : ind -> ind) x = x``;
(* ==> the same Genuine, uncertified counterexample                      *)

(* --------------------------------------------------------------------- *)
(* 5.  Evaluated terms: printing more than the bindings                  *)
(*                                                                       *)
(* [upd_evals] names extra expressions to evaluate under the             *)
(* counterexample's assignment.  Handy when the interesting quantity is  *)
(* a function of the witnesses rather than a witness itself.             *)
(* --------------------------------------------------------------------- *)

refute
  (!the_config
     |> upd_evals [``LENGTH (xs : num list)``, ``REVERSE (xs : num list)``]
     |> upd_expect ExpectGenuine)
  ``REVERSE (xs : num list) = xs``;

(* --------------------------------------------------------------------- *)
(* 6.  More than one counterexample                                      *)
(*                                                                       *)
(* [upd_max_counterexamples] is a budget, not a demand for distinct      *)
(* witnesses: the race keeps collecting hits until it has that many or   *)
(* runs out of schedule.  Here the exhaustive backend contributes one    *)
(* per size, and they happen to differ.                                  *)
(* --------------------------------------------------------------------- *)

refute
  (!the_config
     |> upd_max_counterexamples 3
     |> upd_expect ExpectGenuine)
  ``(xs : num list) ++ ys = ys ++ xs``;
(* ==> three Genuine counterexamples: xs = [0] with ys = [1], [0; 1]     *)
(*     and [0; 0; 1]                                                     *)

(* --------------------------------------------------------------------- *)
(* 7.  Budget, racing, and volume                                        *)
(*                                                                       *)
(* [upd_timeout] is the whole-call budget in seconds; [upd_sequential    *)
(* true] runs backends one after another in registration order instead   *)
(* of racing them, which makes reports reproducible; [upd_quiet true]    *)
(* silences the report and leaves only the returned value.               *)
(* --------------------------------------------------------------------- *)

refute
  (!the_config
     |> upd_timeout 5.0
     |> upd_sequential true
     |> upd_quiet true
     |> upd_expect ExpectGenuine)
  ``(x : num) * y = x + y``;
(* ==> no report, just the returned Counterexample value                 *)

(* --------------------------------------------------------------------- *)
(* 8.  Expectations turn a call into an assertion                        *)
(*                                                                       *)
(* [upd_expect] makes Refute raise a HOL_ERR when the outcome is not the *)
(* one you predicted.  This is how the test suites pin behaviour, and it *)
(* is equally useful in a script that should fail loudly if a conjecture *)
(* it assumed was false suddenly stops being refutable.                  *)
(* --------------------------------------------------------------------- *)

refute (upd_expect ExpectGenuine (!the_config))
  ``(x : num) - y + y = x``;

(* Wrong prediction: the call raises Refute.expect.  The report is       *)
(* printed first, then the exception carries the mismatch.               *)
refute (upd_expect ExpectNone (!the_config)) ``(x : num) - y + y = x``
  handle e => (Feedback.HOL_MESG (Feedback.exn_to_string e);
               NoCounterexample);
(* ==> Exception raised at Refute.expect:                                *)
(*       expected ExpectNone, got ExpectGenuine                          *)

(* --------------------------------------------------------------------- *)
(* 9.  Tags and trace level                                             *)
(*                                                                       *)
(* [upd_tag] appends a marker to the end of every report, which helps    *)
(* when several configurations are being compared in one log.  The       *)
(* "Refute" trace controls verbosity: 0 silences reports, 1 (the         *)
(* default) prints them, 2 and above also announce each backend, the     *)
(* substrate selection and fallthrough, and every schedule entry.        *)
(* --------------------------------------------------------------------- *)

Feedback.set_trace "Refute" 2;

refute
  (!the_config
     |> upd_tag "  [attempt A]"
     |> upd_expect ExpectGenuine)
  ``REVERSE (xs : num list) = xs``;
(* ==> Refute: backend racing requested, but the session thread count    *)
(*     is 1, so the backends run sequentially (--mt or                   *)
(*     Multithreading.max_threads_update raises it)                      *)
(*     Refute backend started (weight 20): exhaustive                    *)
(*     Refute substrate selection: selected native                       *)
(*     ... Certified: |- ~!xs. REVERSE xs = xs  [attempt A]              *)
(*                                                                       *)
(* That first line is emitted on every trace-2 run of a session that was *)
(* not given [--mt], which is every session started the way this file's  *)
(* header shows.  It reports a schedule, not a problem: sequential and   *)
(* raced runs return the same result.  04_substrates_and_determinism.sml *)
(* is where scheduling is the subject.                                   *)

Feedback.set_trace "Refute" 1;

(* --------------------------------------------------------------------- *)
(* 10.  Changing the session default                                     *)
(*                                                                       *)
(* [the_config] is a ref holding the configuration used by [refute_def], *)
(* [quickcheck], [nitpick], [REFUTE_TAC] and [refute_top].  Update it    *)
(* once instead of threading a configuration through every call, and     *)
(* restore [default_config] when you are done.                           *)
(* --------------------------------------------------------------------- *)

the_config := (!the_config
                 |> upd_timeout 10.0
                 |> upd_size 6
                 |> upd_expect ExpectGenuine);
refute_def ``(xs : num list) <> [] ==> HD xs = 0``;
the_config := default_config;
