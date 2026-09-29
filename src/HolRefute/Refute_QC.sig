signature Refute_QC = sig
  type term = Term.term

  val record_candidate :
    {config : Refute_Core.config,
     counterexamples : Refute_Core.counterexample list ref,
     discarded : int ref,
     instance : Refute_Core.instance,
     pnf_prefix : (Refute_Eval.quant * term) list option,
     retain_replay_potential : Refute_Core.counterexample -> unit,
     retry : bool -> Refute_Eval.candidate list -> unit,
     retry_potential : bool -> Refute_Eval.candidate list -> unit,
     run_depth : int option,
     stats : (string * int) list,
     strategy : Refute_Eval.strategy,
     substrate : string} ->
    {case_tree : Refute_Eval.case_tree option,
     env : (term * term) list,
     genuine : bool,
     genuine_only : bool,
     ground_env : (term * term) list option,
     ignored : Refute_Eval.candidate list} ->
    unit
  val new_counter_totals :
    unit ->
    {absorb : (string * int) list -> unit,
     decorate : (string * int) list -> (string * int) list,
     reason : unit -> string option}
  val stats_for_entry :
    ((string * int) list -> (string * int) list) -> int ref ->
    (string * int) list ref -> int -> int -> int -> (string * int) list
  val add_reason : ''a -> ''a list ref -> unit
  val retain_potential :
    Refute_Core.counterexample option ref -> Refute_Core.counterexample ->
    unit
  val say_schedule_entry : string -> string -> int * int -> int -> unit
  val finish_outcome :
    string -> Refute_Core.counterexample list ->
    Refute_Core.counterexample option -> string option ->
    (unit -> Refute_Core.outcome) -> Refute_Core.outcome

  datatype selected_compile =
      Selected of string * Refute_Eval.compiled_test
    | SelectionFailed of string list

  val compile_selected :
    Refute_Core.config -> Refute_Eval.strategy -> Refute_Eval.qc_problem ->
    selected_compile
  val bounded_size : int -> int
  val close_tests : Refute_Eval.compiled_test list -> unit
  val strategy_run :
    Refute_Eval.strategy -> Refute_Core.config -> Refute_Core.instance list ->
    Refute_Core.outcome
  val qc_backend_names : unit -> string list
  val register_backends : unit -> unit
end
