(* ===================================================================== *)
(*  HolRefute by example, 8: finding assumptions you do not need         *)
(*                                                                       *)
(*  A counterexample finder can also answer the opposite question: which  *)
(*  hypotheses of a theorem are dead weight?  Drop a premise, look for a  *)
(*  counterexample, and if none turns up the premise is a candidate for   *)
(*  removal.  That is exactly what this facade does, one theorem or one   *)
(*  whole theory at a time.                                              *)
(*                                                                       *)
(*      ../../bin/hol --holstate=refuteheap \                            *)
(*          < examples/08_unused_assumptions.sml                          *)
(* ===================================================================== *)

load "Refute";
open Refute;

(* --------------------------------------------------------------------- *)
(* 1.  Three theorems: one tight, two padded                             *)
(*                                                                       *)
(* Saving them puts them in the theory database, which is where the       *)
(* sweep in section 3 looks.  [save_thm] behaves the same way in an       *)
(* interactive session as in a script: the sweep below reports "3 total"  *)
(* theorems in the theory "scratch", so all three are visible.           *)
(* --------------------------------------------------------------------- *)

val tight = save_thm ("tight",
  prove (``!x y : num. x <= y ==> y <= x ==> x = y``,
         simp []));

val padded = save_thm ("padded",
  prove (``!x y : num. 0 < y ==> x <= x + y``,
         simp []));

val doubly_padded = save_thm ("doubly_padded",
  prove (``!x y : num. 0 < y ==> x < 100 ==> x <= x + y``,
         simp []));

(* --------------------------------------------------------------------- *)
(* 2.  Checking one theorem                                              *)
(*                                                                       *)
(* The first argument is a configuration option.  NONE derives a QC-only  *)
(* configuration, which cannot settle unbounded arithmetic — section 4    *)
(* shows exactly what that looks like — so the probes here are handed the *)
(* model finder instead.                                                 *)
(*                                                                       *)
(* The result is the theorem name paired with the maximal sets of         *)
(* premises that can be dropped together, indexed from zero.  NONE means  *)
(* the statement has no premises to consider at all.  SOME [] means no    *)
(* droppable premise was found, which is "every premise is pulling its    *)
(* weight" only when the probes were conclusive — the report in section 3 *)
(* is what tells you whether they were.                                  *)
(* --------------------------------------------------------------------- *)

val probes = !the_config |> upd_backends (SOME ["kodkod"]);

check_unused_assms (SOME probes) ("tight", tight);
(* ==> ("tight", SOME []) : both premises are needed                     *)

check_unused_assms (SOME probes) ("padded", padded);
(* ==> ("padded", SOME [[0]]) : the 0 < y premise is superfluous         *)

(* Both premises are superfluous, and they can go together.              *)
check_unused_assms (SOME probes) ("doubly_padded", doubly_padded);
(* ==> ("doubly_padded", SOME [[0, 1]])                                  *)

(* --------------------------------------------------------------------- *)
(* 3.  Sweeping a whole theory                                           *)
(*                                                                       *)
(* [find_unused_assms] returns one entry per saved theorem, sorted by     *)
(* name; [print_unused_assms] prints the same information as a report,    *)
(* with premises numbered from one, and says how many probes were         *)
(* inconclusive.  NONE means the current theory.                         *)
(* --------------------------------------------------------------------- *)

find_unused_assms (SOME probes) (Theory.current_theory ());
(* ==> [("doubly_padded", SOME [[0, 1]]), ("padded", SOME [[0]]),        *)
(*      ("tight", SOME [])]                                              *)

print_unused_assms (SOME probes) NONE;
(* ==> Found 2 theorems with (potentially) superfluous assumptions:      *)
(* ==>                                                                   *)
(* ==> doubly_padded: unnecessary assumption 1 and 2                     *)
(* ==> padded: unnecessary assumption 1                                  *)
(* ==>                                                                   *)
(* ==> Checked 3 theorems with assumptions (3 total) in the theory       *)
(* ==> "scratch"                                                         *)
(* ==> Skipped 0 inconclusive probes.                                    *)

(* --------------------------------------------------------------------- *)
(* 4.  Choosing the machinery behind the probes                          *)
(*                                                                       *)
(* Passing NONE derives a QC-only configuration from the session default: *)
(* fast, executable, no model finder.  The catch is that a premise counts *)
(* as droppable only when its probe answers NoCounterexample, and testing *)
(* never exhausts :num — the QC backends report "search space not         *)
(* exhausted" instead.  On the arithmetic of section 1 every such probe   *)
(* is therefore inconclusive, and a genuinely superfluous premise goes    *)
(* unreported.                                                           *)
(* --------------------------------------------------------------------- *)

check_unused_assms NONE ("padded", padded);
(* ==> ("padded", SOME []) : inconclusive, not "the premise is needed"   *)

print_unused_assms NONE NONE;
(* ==> Found 0 theorems with (potentially) superfluous assumptions:      *)
(* ==>                                                                   *)
(* ==>                                                                   *)
(* ==> Checked 3 theorems with assumptions (3 total) in the theory       *)
(* ==> "scratch"                                                         *)
(* ==> Skipped 3 inconclusive probes.                                    *)
(*                                                                       *)
(* The skipped count is the honest reading of the empty report: three of  *)
(* the five probes could not be settled at all.                          *)

(* Where the search space really is finite, the QC-only default is        *)
(* conclusive, and no model finder is needed.                            *)

val cases = prove (``!p q : bool. q ==> p \/ ~p``, simp []);

check_unused_assms NONE ("cases", cases);
(* ==> ("cases", SOME [[0]])                                             *)

(* Passing SOME cfg uses your configuration and keeps its backend         *)
(* selection — for example to spend more time per probe, or to bring in   *)
(* the model finder for goals the executable backends cannot test, as     *)
(* section 2 did.  Either way each probe is forced to run sequentially,   *)
(* quietly, aborting on the first potential counterexample, and with no   *)
(* expectation attached.                                                 *)

check_unused_assms
  (SOME (!the_config
           |> upd_backends (SOME ["exhaustive", "narrowing"])
           |> upd_timeout 5.0
           |> upd_size 12))
  ("cases", cases);
(* ==> ("cases", SOME [[0]])                                             *)

(* --------------------------------------------------------------------- *)
(* 5.  What a "yes" is worth                                             *)
(*                                                                       *)
(* A reported premise is a candidate, not a proof obligation discharged:  *)
(* the evidence is "no counterexample within the tested bounds".  The     *)
(* payoff is that it points at exactly which premise to try deleting, and *)
(* re-running the proof is the cheap confirmation.                        *)
(* --------------------------------------------------------------------- *)

prove (``!x y : num. x <= x + y``, simp []);
(* ==> |- !x y. x <= x + y : the premise reported for "padded" really     *)
(* was dead weight.                                                      *)
