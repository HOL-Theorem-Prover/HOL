(* ===================================================================== *)
(*  HolRefute by example, 1: first steps                                 *)
(*                                                                       *)
(*  Every entry point that answers the question "is this conjecture      *)
(*  actually true?": refute, quickcheck, nitpick, REFUTE_TAC, and the    *)
(*  goal-stack and try_refute wrappers.                                  *)
(*                                                                       *)
(*  Run the whole file:                                                  *)
(*                                                                       *)
(*      cd src/HolRefute                                                 *)
(*      ../../bin/hol --holstate=refuteheap < examples/01_first_steps.sml *)
(*                                                                       *)
(*  or start the same session and paste the blocks one at a time.        *)
(* ===================================================================== *)

load "Refute";
open Refute;

(* --------------------------------------------------------------------- *)
(* 1.  A conjecture that is not a theorem                                *)
(*                                                                       *)
(* Natural subtraction truncates at zero, so adding y back does not      *)
(* undo it.  [refute_def] runs the default configuration: every          *)
(* registered backend, racing, 30-second budget.                         *)
(* --------------------------------------------------------------------- *)

refute_def ``(x : num) - y + y = x``;

(* ==> Counterexample [{backend = "exhaustive", substrate = "native",    *)
(*     bindings = [(x, 0), (y, 1)], certainty = Genuine,                 *)
(*     cert = SOME |- ~!x y. x - y + y = x, ...}]                        *)

(* --------------------------------------------------------------------- *)
(* 2.  A conjecture that survives                                        *)
(*                                                                       *)
(* Refute is a counterexample finder, not a prover: "no counterexample"  *)
(* is evidence, not proof, and the report says so.                       *)
(* --------------------------------------------------------------------- *)

refute_def ``(x : num) + y = y + x``;

(* ==> NoCounterexample, reported as "no counterexample found within the *)
(*     tested finite bounds" -- not "this is a theorem".                 *)

(* --------------------------------------------------------------------- *)
(* 3.  The outcome is an ML value                                        *)
(*                                                                       *)
(* [outcome] is Counterexample of counterexample list | NoCounterexample *)
(* | Unknown of string list, so a script can branch on it.  Each         *)
(* counterexample records the backend and substrate that found it, the   *)
(* variable bindings, and (by default) a HOL theorem certifying the      *)
(* negation of the instantiated conjecture.                              *)
(* --------------------------------------------------------------------- *)

val outcome = refute_def ``EVEN (x + y) ==> EVEN (x : num)``;

case outcome of
    Counterexample (cex :: _) =>
      (#backend cex, #substrate cex, #bindings cex, #cert cex)
  | _ => raise Fail "expected a counterexample";

(* ==> ("exhaustive", "native", [(x, 1), (y, 1)],                        *)
(*      SOME |- ~!x y. EVEN (x + y) ==> EVEN x)                          *)

(* --------------------------------------------------------------------- *)
(* 4.  Goals with assumptions                                            *)
(*                                                                       *)
(* [refute_goal] takes a (term list * term) goal.  Refute then looks for *)
(* an assignment that satisfies every assumption and still falsifies the *)
(* conclusion, so assumptions cut the search down.  [upd_no_assms true]  *)
(* drops them, which here exposes exactly the case the guard excluded.   *)
(* --------------------------------------------------------------------- *)

val guarded = ([``0 < (n : num)``], ``PRE n < n``);

refute_goal (!the_config) guarded;

(* ==> NoCounterexample: within the tested bounds every n satisfying     *)
(*     0 < n also satisfies PRE n < n.                                   *)

refute_goal (upd_no_assms true (!the_config)) guarded;

(* ==> Counterexample n = 0, certified |- ~!n. PRE n < n: PRE 0 = 0 and  *)
(*     0 < 0 is false, which is why the assumption was needed.           *)

(* --------------------------------------------------------------------- *)
(* 5.  REFUTE_TAC as a proof-time guard                                  *)
(*                                                                       *)
(* REFUTE_TAC fails, printing the counterexample, when the goal in front *)
(* of it is refutable, and behaves like ALL_TAC otherwise.  Put it at    *)
(* the head of a tactic you are unsure about instead of grinding away at *)
(* an unprovable subgoal.                                                *)
(* --------------------------------------------------------------------- *)

(* Fails: the goal is false for xs = [].  The handler prints the raised  *)
(* HOL_ERR -- the only exception this file expects -- and returns TRUTH  *)
(* so that the transcript can continue.                                  *)
TAC_PROOF (([], ``LENGTH (TL (xs : num list)) < LENGTH xs``), REFUTE_TAC)
  handle e => (Feedback.HOL_MESG (Feedback.exn_to_string e); TRUTH);

(* ==> "Exception raised at Refute.REFUTE_TAC: Refute found a            *)
(*     counterexample ... xs = []", then val it = |- T.                  *)

(* Succeeds: no counterexample, so the guard steps aside and the real    *)
(* tactic finishes the proof.  Truncating subtraction sinks section 1's  *)
(* conjecture but not this one.                                          *)
TAC_PROOF (([], ``(x : num) - y <= x``), REFUTE_TAC THEN simp []);

(* ==> |- x - y <= x                                                     *)

(* --------------------------------------------------------------------- *)
(* 6.  The interactive goal stack                                        *)
(*                                                                       *)
(* [refute_top ()] refutes whatever the proof manager currently shows,   *)
(* so a stuck subgoal can be tested without retyping it.  Here the case  *)
(* split disposes of the empty list and leaves a subgoal that no tactic  *)
(* could ever close, because the conjecture is false.                    *)
(* --------------------------------------------------------------------- *)

g `!xs : num list. xs <> [] ==> HD xs <= LENGTH xs`;
e (Cases_on `xs`);
e (simp []);
refute_top ();

(* ==> Counterexample h = 2, t = []: HD [2] = 2 exceeds LENGTH [2] = 1.  *)

drop ();

(* ==> "There are currently no proofs." -- the goal stack is clean again *)
(*     for whatever you do next.                                         *)

(* --------------------------------------------------------------------- *)
(* 7.  try_refute: quiet, deterministic, for automation                  *)
(*                                                                       *)
(* [try_refute] is the entry point for tools.  It forces a sequential,   *)
(* quiet, fixed-seed profile, ignores any expectation, and returns       *)
(* SOME (backend, outcome) only when it actually found something.  Its   *)
(* timeout is a whole-call budget, and a goal with no counterexample     *)
(* spends all of it, so five seconds is friendlier here than the         *)
(* default thirty.                                                       *)
(* --------------------------------------------------------------------- *)

try_refute (upd_timeout 5.0 (!the_config))
  ([], ``(xs : num list) ++ ys = ys ++ xs``);

(* ==> SOME ("exhaustive", Counterexample [{bindings = [(xs, [0]),       *)
(*     (ys, [1])], evals = [(xs ++ ys, [0; 1]), (ys ++ xs, [1; 0])],     *)
(*     ...}]).  Note that nothing was printed: try_refute is quiet.      *)

try_refute (upd_timeout 5.0 (!the_config))
  ([], ``(xs : num list) ++ [] = xs``);

(* ==> NONE, after the five seconds.  "Found nothing" and "found a       *)
(*     reason to stop looking" are the same answer here, which is why    *)
(*     try_refute is for tools and [refute] is for the reader at the     *)
(*     prompt.                                                           *)

(* --------------------------------------------------------------------- *)
(* 8.  Backend presets                                                   *)
(*                                                                       *)
(* [quickcheck] restricts the search to the executable QC backends;      *)
(* [nitpick] restricts it to the Kodkod model finder.  Both are just     *)
(* [refute] with a narrowed backend list, which you can also write out   *)
(* by hand with [upd_backends].                                          *)
(* --------------------------------------------------------------------- *)

quickcheck ``REVERSE (xs : num list) = xs``;

(* ==> Counterexample xs = [0; 1] from the exhaustive backend.           *)

refute (upd_backends (SOME ["exhaustive"]) (!the_config))
  ``REVERSE (xs : num list) = xs``;

(* ==> the same counterexample.  [quickcheck] is this call with all the  *)
(*     QC backend names filled in for you; here only one of them is      *)
(*     asked, and it is the one that answered above.                     *)

(* Needs a Kodkodi installation; see 09_model_finder.sml.                *)
nitpick ``(f : bool -> num) b = 0``;

(* ==> a Genuine kodkod counterexample, with the extra fields only the   *)
(*     model finder fills in: a cardinality scope for :num, a model      *)
(*     listing that type's atoms, and f as a finite update table.  The   *)
(*     chosen scope and table vary from run to run.  Without a Kodkodi   *)
(*     component this call reports Unknown instead; see examples/README. *)
