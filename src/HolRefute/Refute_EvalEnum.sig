signature Refute_EvalEnum = sig
  type term = Term.term
  type hol_type = Type.hol_type

  exception Invalid of string

  (* The literal forms clause patterns match by equality. *)
  val special_literal : term -> bool
  val same_program :
    Refute_SmartGen.enumerator -> Refute_SmartGen.enumerator -> bool
  val find_by_mode :
    ('a -> Refute_SmartGen.enumerator) -> Refute_SmartGen.relation_key ->
    Refute_SmartGen.mode -> 'a list -> 'a option
  val smart_guard_lookup :
    {relation : term, version : Refute_SmartGen.program_version} ->
    Refute_SmartGen.enumerator list ->
    (Refute_SmartGen.enumerator * term list) option
  val collect_programs :
    (string -> Refute_SmartGen.enumerator) ->
    (Refute_SmartGen.relation_key -> Refute_SmartGen.mode ->
     Refute_SmartGen.enumerator option) ->
    (Refute_SmartGen.relation_key -> Refute_SmartGen.mode ->
     Refute_SmartGen.program_version -> Refute_SmartGen.enumerator) ->
    (term -> Refute_SmartGen.program_version -> Refute_SmartGen.enumerator) ->
    Refute_Eval.plan -> Refute_SmartGen.enumerator list ->
    Refute_SmartGen.enumerator list
  val validate :
    (string -> 'a) -> Refute_SmartGen.enumerator list ->
    Refute_Eval.plan list -> unit
  val prepare :
    Refute_Eval.strategy -> Refute_Eval.plan list ->
    Refute_SmartGen.enumerator list
  val generator_types : Refute_SmartGen.enumerator list -> hol_type list
  val recursion_floor : bool list -> int list -> int
  val unpack_terms : hol_type list -> term -> term list
  val negation_condition : Refute_SmartGen.enumerator -> term list -> term
  val quiet_theory_work : (unit -> 'a) -> 'a

  type hol_enumerator =
    {program : Refute_SmartGen.enumerator, function : term,
     input_types : hol_type list, output_types : hol_type list}

  type definition =
    {theorem : Thm.thm, enumerators : hol_enumerator list,
     generator_types : hol_type list}

  val define :
    {after_define : Thm.thm -> unit,
     prefix : string,
     programs : Refute_SmartGen.enumerator list} ->
    {enumerators : hol_enumerator list,
     generator_types : hol_type list,
     theorem : Thm.thm}
  val enumerator_for :
    hol_enumerator list -> Refute_SmartGen.relation_key ->
    Refute_SmartGen.mode -> hol_enumerator
  val application : hol_enumerator -> term list -> term list -> int -> term
  val fresh_prefix : string -> string

  datatype 'a held_state =
      HeldIdle
    | HeldOpen
    | HeldReady of 'a

  datatype 'a held_bracket = HeldBracket of
    {state : 'a held_state ref, teardown : unit -> unit}

  val held_bracket : (unit -> unit) -> 'a held_bracket
  val close_held_bracket : 'a held_bracket -> unit
  val start_held_bracket : 'a held_bracket -> (unit -> 'a) -> 'a
end
