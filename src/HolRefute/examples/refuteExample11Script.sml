(* HolRefute by example, 11: SML-level automation. *)

Theory refuteExample11
Ancestors
  refute
Libs
  Refute

open Refute

(* This is the one example for tooling authors who need structured results
   or per-call configuration.  Ordinary proof scripts should start with
   REFUTE_TAC and use a specialized tactic only when its search method
   matters, as shown in the other examples. *)

(* [quickcheck] and [model_refute] are convenient presets.  [refute_with]
   applies a local update list when an automation needs tighter control. *)

val quickcheck_outcome =
  quickcheck ``(n : num) DIV 2 * 2 = n``

val model_outcome =
  model_refute ``(f : bool -> bool) b = T``

val automation_updates =
  [upd_search (Only [Exhaustive]),
   upd_quiet true,
   upd_expect ExpectGenuine]

val configured_outcome =
  refute_with automation_updates ``REVERSE (xs : num list) = xs``

(* An exact configuration is preferable when a tool must be independent of
   the interactive [the_config].  Updates are applied from left to right. *)

val automation_config =
  default_config |> apply_updates automation_updates

(* REFUTE_TAC_WITH exposes the same local-update convention to a diagnostic
   tactic.  This deliberately false theorem remains buildable only because
   [cheat] follows the diagnostic. *)

Theorem advanced_per_call_narrowing:
  LENGTH (xs : num list) <> 2
Proof
  REFUTE_TAC_WITH
    [upd_search (Only [Narrowing]),
     upd_size 2] >>
  cheat
QED

(* Outcomes are datatypes, so automation can inspect bindings and optional
   kernel certificates without parsing the human-readable report. *)

val certified_counterexample =
  case configured_outcome of
      Counterexample ({cert = SOME thm, ...} :: _) => thm
    | Counterexample _ =>
        raise Fail "expected a certified counterexample"
    | NoCounterexample =>
        raise Fail "expected a counterexample, not bounded success"
    | Unknown reasons =>
        raise Fail ("refutation was inconclusive: " ^
                    String.concatWith "; " reasons)

(* Goals can be supplied as an assumption list and conclusion. *)

val goal_outcome =
  refute_goal_with automation_updates
    ([``0 < (n : num)``], ``PRE n = n``)

(* [try_refute] adds a formatted report and turns an inconclusive result
   into NONE, which is convenient for editor and batch integrations. *)

val formatted_result =
  try_refute automation_config
    ([``xs <> ([] : num list)``], ``HD xs = 0``)

Theorem padded_bound:
  0 < (y : num) ==> x < 100 ==> x <= x + y
Proof
  simp []
QED

(* The same API also supports tools that look for removable assumptions. *)

val unused_assumptions =
  check_unused_assms
    (SOME automation_config) ("padded_bound", padded_bound)
