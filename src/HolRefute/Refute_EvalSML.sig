signature Refute_EvalSML = sig
  type term = Term.term

  exception Stuck of string

  exception Hole of int list

  datatype extraction_mode = StrictExtraction | LazyExtraction

  val lazy_hole : int list -> 'a Susp.susp

  type reconstruction = unit -> term

  type generated_environment = (int * reconstruction) list

  type generated_hit =
    generated_environment * generated_environment option *
    Refute_Eval.case_tree option * bool

  type generated_answer =
    { hit : generated_hit option,
      complete : bool,
      state : IntInf.int,
      tests : int,
      match_failures : int,
      assumption_satisfied : int,
      conclusion_evaluated : int,
      candidates_generated : int }

  type generated_dispatch =
    int -> bool -> int -> int -> IntInf.int -> generated_answer

  val install_dispatch : generated_dispatch -> unit

  type term_tables

  datatype extraction_result =
      Extracted of {source : string, entry : string, table : term_tables}
    | ExtractionFailed of string list

  val term_tables : term list -> term list -> term_tables
  val check_deadline : unit -> unit
  val ignored_hit_now : generated_hit -> bool
  val raw_term : int -> term
  val con_term : int -> term list -> term
  val num_term : LargeInt.int -> term
  val int_term : LargeInt.int -> term
  val char_term : char -> term
  val string_term : string -> term
  val is_char_list_type : Type.hol_type -> bool
  val char_list_head_source : string -> string
  val char_list_tail_source : string -> string
  val hole_term : int -> term
  val replay_variable : int -> int list -> term
  val word_term : int -> LargeInt.int -> term
  val fun_term : term -> term -> (term * term) list -> term
  val update_term : term -> term -> term -> term
  val eval_term : int -> (int * (unit -> term)) list -> term
  val reconstruction_arg : int -> int -> (unit -> term) -> unit -> term
  val split_term : int -> int -> int -> (int * (unit -> term)) list -> term
  val register_substrate :
    {extract :
       extraction_mode -> Refute_Core.config -> Refute_Eval.strategy ->
       Refute_Eval.qc_problem -> extraction_result,
     preflight :
       Refute_Core.config -> Refute_Eval.strategy -> Refute_Eval.plan list ->
       term list -> string list} ->
    unit
end
