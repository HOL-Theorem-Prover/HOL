(* ===================================================================== *)
(*  HolRefute by example, 4: substrates, randomness, reproducibility     *)
(*                                                                       *)
(*  Exhaustive and random QC testing run on three interchangeable        *)
(*  execution substrates.  This file shows how to select one, what       *)
(*  happens when the one you asked for cannot run your goal, and how to  *)
(*  make a random search repeatable.                                     *)
(*                                                                       *)
(* ===================================================================== *)

Theory refuteExample04
Ancestors
  refute
Libs
  Refute

open Refute;

(* --------------------------------------------------------------------- *)
(* 1.  The three substrates                                              *)
(*                                                                       *)
(*   NativeSML  extracts the executable fragment to SML and compiles the *)
(*              test loop in process.  Fastest on Poly/ML, and the first *)
(*              choice of the default Auto policy.                       *)
(*   Cv         compiles a fuel-bounded HOL test loop and runs it with   *)
(*              Thm.compute.  Restricted to a first-order fragment.      *)
(*   Compute    interprets the test plan with computeLib.  The           *)
(*              compatibility substrate: slowest, but it supports        *)
(*              registered custom and abstract generators.               *)
(*                                                                       *)
(* Every counterexample records which one produced it, under the short   *)
(* registered names "native", "cv" and "compute".                        *)
(* --------------------------------------------------------------------- *)

fun substrate_of outcome =
  case outcome of
      Counterexample (cex :: _) => #substrate cex
    | _ => "none";

val goal = ``REVERSE (xs : num list) = xs``;

substrate_of (refute (upd_substrate NativeSML (upd_quiet true
  (upd_expect ExpectCex (!the_config)))) goal);
(* ==> val it = "native": string *)

substrate_of (refute (upd_substrate Cv (upd_quiet true
  (upd_expect ExpectCex (!the_config)))) goal);
(* ==> val it = "cv": string *)

substrate_of (refute (upd_substrate Compute (upd_quiet true
  (upd_expect ExpectCex (!the_config)))) goal);
(* ==> val it = "compute": string *)

(* --------------------------------------------------------------------- *)
(* 2.  Auto walks the substrates in priority order                       *)
(*                                                                       *)
(* Auto (the default) tries NativeSML, then Cv, then Compute, falling    *)
(* through whenever a substrate reports that it cannot handle the goal.  *)
(* At trace level 2 it names the substrate it settled on, and the reason *)
(* for every one it skipped.  This goal needs no skips: NativeSML, the   *)
(* first choice, runs it.  Section 3 shows a run with skips.             *)
(*                                                                       *)
(* Trace 2 opens by reporting that the backends will run sequentially:   *)
(* racing needs more than one session thread, which only the build's     *)
(* --mt flag (or Multithreading.max_threads_update) supplies.  A plain   *)
(* session therefore always degrades to a sequence; only the schedule    *)
(* differs, never the result.                                            *)
(* --------------------------------------------------------------------- *)

Feedback.set_trace "Refute" 2;
refute (upd_expect ExpectGenuine (upd_substrate Auto (!the_config))) goal;
(* ==> Refute: backend racing requested, but the session thread count    *)
(*      is 1, so the backends run sequentially (--mt or                  *)
(*      Multithreading.max_threads_update raises it)                     *)
(* ==> Refute substrate selection: selected native                       *)
(* ==> Counterexample xs = [0; 1], substrate = "native"                  *)
Feedback.set_trace "Refute" 1;

(* --------------------------------------------------------------------- *)
(* 3.  An explicitly chosen substrate never falls through                *)
(*                                                                       *)
(* This is the point of asking for one by name: if it cannot run the     *)
(* goal you get Unknown with the reason, not a silent switch to another  *)
(* substrate.  Compare the same goal under Auto.                         *)
(* --------------------------------------------------------------------- *)

val higher_order = ``(f : (num -> num) -> num) (\n. n) = 0``;

(* Restricting the backends to the two QC ones keeps the reported        *)
(* reasons about substrates; narrowing and the model finder have their   *)
(* own, unrelated verdicts on this goal.                                 *)

val qc = upd_backends (SOME ["exhaustive", "random"]) (!the_config);

refute (upd_expect ExpectUnknown (upd_substrate Cv qc)) higher_order;
(* ==> Unknown                                                          *)
(*      ["exhaustive: cv: :(num -> num) -> num - function type in data  *)
(*        position",                                                    *)
(*       "random: cv: :(num -> num) -> num - function type in data      *)
(*        position"]                                                    *)

Feedback.set_trace "Refute" 2;
refute (upd_expect ExpectGenuine (upd_substrate Auto qc)) higher_order;
(* ==> Refute: backend racing requested, but the session thread count   *)
(*      is 1, so the backends run sequentially (--mt or                 *)
(*      Multithreading.max_threads_update raises it)                    *)
(* ==> native is inapplicable: function equality has non-enumerable     *)
(*      domain :num                                                     *)
(* ==> cv is inapplicable: cv: :(num -> num) -> num - function type in  *)
(*      data position                                                   *)
(* ==> selected compute; Counterexample f = (\x. 1), substrate =        *)
(*      "compute"                                                       *)
Feedback.set_trace "Refute" 1;

(* --------------------------------------------------------------------- *)
(* 4.  Exhaustive and random backends                                    *)
(*                                                                       *)
(* "exhaustive" enumerates every candidate up to [size]; "random" draws  *)
(* [iterations] candidates under the same growing size schedule.  Both   *)
(* are bounded by [size], so a witness beyond that bound is invisible to *)
(* either: exhaustive then reports that the space was not exhausted      *)
(* rather than claiming the goal holds.                                  *)
(* --------------------------------------------------------------------- *)

val far_out = ``(x : num) MOD 64 <> 37``;

refute
  (!the_config
     |> upd_backends (SOME ["exhaustive"])
     |> upd_size 20
     |> upd_expect ExpectUnknown)
  far_out;
(* ==> Unknown ["exhaustive: search space not exhausted"]: the bound     *)
(*      never reaches x = 37                                             *)

refute
  (!the_config
     |> upd_backends (SOME ["exhaustive"])
     |> upd_size 40
     |> upd_expect ExpectGenuine)
  far_out;
(* ==> Counterexample x = 37, found at size 37                           *)

refute
  (!the_config
     |> upd_backends (SOME ["random"])
     |> upd_iterations 2000
     |> upd_size 200
     |> upd_expect ExpectGenuine)
  far_out;
(* ==> Counterexample x = 37, size 37, tests 1: the schedule climbs to   *)
(*      that size and the draw hits immediately                          *)

(* --------------------------------------------------------------------- *)
(* 5.  Reproducible random search                                        *)
(*                                                                       *)
(* All substrates share one 64-bit generator and one consumption order,  *)
(* so a fixed seed pins the candidate stream — the same counterexample   *)
(* comes back whichever substrate ran it.                                *)
(* --------------------------------------------------------------------- *)

fun bindings_of outcome =
  case outcome of
      Counterexample (cex :: _) =>
        map (Parse.term_to_string o #2) (#bindings cex)
    | _ => [];

fun stream_with seed substrate =
  bindings_of (refute
    (!the_config
       |> upd_backends (SOME ["random"])
       |> upd_substrate substrate
       |> upd_seed seed
       |> upd_iterations 500
       |> upd_quiet true
       |> upd_expect ExpectCex)
    ``(x : num) * y = y``);

fun seeded substrate = stream_with (SOME 271828) substrate;

val stream_native = seeded NativeSML;    (* ==> ["0", "1"] *)
val stream_cv = seeded Cv;               (* ==> ["0", "1"] *)
val stream_compute = seeded Compute;     (* ==> ["0", "1"] *)

stream_native = stream_cv andalso stream_cv = stream_compute;
(* ==> val it = true: bool *)

(* The seed pins the stream, not the verdict.  An unseeded run advances  *)
(* a session-level stream instead, but the size schedule still starts at *)
(* 1, so on a goal whose smallest witness is found straight away the     *)
(* reported binding does not move: both calls below came back ["0", "1"] *)
(* too.  Fix the seed when you want the search itself repeated, not      *)
(* merely the answer.                                                    *)

fun unseeded () = stream_with NONE Auto;

unseeded ();                             (* ==> ["0", "1"] *)
unseeded ();                             (* ==> ["0", "1"] *)

(* --------------------------------------------------------------------- *)
(* 6.  Statistics                                                        *)
(*                                                                       *)
(* The report header carries the tested size and elapsed milliseconds,   *)
(* and [#stats] exposes the same counters to a script — useful when      *)
(* comparing substrates on a goal of your own.  The counters ride on a   *)
(* counterexample, so a substrate that cannot run the goal yields [].    *)
(* --------------------------------------------------------------------- *)

fun stats_of substrate =
  case refute
    (!the_config
       |> upd_substrate substrate
       |> upd_backends (SOME ["exhaustive"])
       |> upd_size 8
       |> upd_quiet true
       |> upd_expect ExpectCex)
    ``REVERSE (xs : num list) = xs`` of
      Counterexample (cex :: _) => #stats cex
    | _ => [];

stats_of NativeSML;
(* ==> [("tests", 4), ("match_failures", 0), ("size", 3), ("card", 1),   *)
(*      ("msec", 0)]                                                     *)

stats_of Cv;
(* ==> the same, except ("tests", 0): cv reports no per-candidate count, *)
(*      so compare size, card and msec across substrates, not tests      *)

stats_of Compute;
(* ==> [("tests", 4), ("match_failures", 0), ("size", 3), ("card", 1),   *)
(*      ("msec", 0)]                                                     *)
