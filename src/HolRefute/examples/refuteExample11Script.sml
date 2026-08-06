(* HolRefute by example, 11: SML-level automation. *)

Theory refuteExample11
Ancestors
  refute
Libs
  Refute

open Refute

(* This is the one example for tooling authors who need structured results.
   Ordinary proof scripts should use REFUTE_TAC, QUICKCHECK_TAC, or
   MODEL_REFUTE_TAC as shown in every other example. *)

(* [quickcheck] and [model_refute] are convenient presets.  [refute] takes
   an explicit configuration when an automation needs tighter control. *)

val quickcheck_outcome =
  quickcheck ``(n : num) DIV 2 * 2 = n``

val model_outcome =
  model_refute ``(f : bool -> bool) b = T``

val automation_config =
  default_config
    |> upd_backends (SOME ["exhaustive"])
    |> upd_quiet true
    |> upd_expect ExpectGenuine

val configured_outcome =
  refute automation_config ``REVERSE (xs : num list) = xs``

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
  refute_goal automation_config
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
