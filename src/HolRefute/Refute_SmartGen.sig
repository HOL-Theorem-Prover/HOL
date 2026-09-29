signature Refute_SmartGen = sig
  type term = Term.term

  type intro_triple =
    {variables : term list, side : term list,
     main : term list, conclusion : term}

  type inference_clause =
    {side : term list, main : term list, head : term,
     ordered : term list}

  val same_term : term -> term -> bool
  val same_constant : term -> term -> bool
  val horn_inference_clauses_for : term -> inference_clause list option

  datatype mode =
      Bool
    | Input
    | Output
    | Pair of mode * mode
    | Fun of mode * mode
    | Fixed of term

  datatype relation_key =
      Predicate of term
    | Graph of term

  val relation_term : relation_key -> term
  val relation_type : relation_key -> Type.hol_type
  val same_relation : relation_key -> relation_key -> bool
  val relation_string : relation_key -> string

  datatype mode_derivation =
      Mode_App of mode_derivation * mode_derivation
    | Context of mode
    | Mode_Pair of mode_derivation * mode_derivation
    | Term_Mode of mode

  datatype indprem =
      Prem of term
    | Sidecond of term
    | Generator of term
    | GraphPrem of term * term list

  type moded_clause =
    {arguments : term list,
     premises : (indprem * mode_derivation) list,
     needs_generator : bool}

  type relation_modes =
    {relation : relation_key,
     modes : (mode * moded_clause list * bool) list}

  datatype external_status =
      Compiled of
        {modes : (mode * bool) list,
         functional : mode list}
    | Uncompiled

  type relation_negative_modes = {relation : relation_key, modes : mode list}

  type inference_result =
    {relations : relation_modes list,
     negative : relation_negative_modes list}

  type premise_score =
    {missing : int,
     functional : bool,
     generator : bool,
     outputs : int,
     recursive : bool}

  val eq_mode : mode * mode -> bool
  val strip_mode : mode -> mode list
  val mode_string : mode -> string
  val predicate_mode_of : Type.hol_type -> mode option
  val compare_score : premise_score * premise_score -> order
  val lookup_assoc : term -> (term * 'a) list -> 'a option
  val split_arguments : mode -> term list -> term list * term list
  val infer_group :
    {clauses : inference_clause list,
     external : (term * external_status) list,
     members : term list,
     reorder_premises : bool} ->
    inference_result
  val scc_clauses :
    term list -> term list -> (term list -> term -> intro_triple option) ->
    inference_clause list option
  val infer_graph : bool -> bool -> term -> inference_result option
  val infer_fixed_argument :
    {clauses : inference_clause list,
     external : (term * external_status) list,
     members : term list,
     position : int,
     relation : term,
     reorder_premises : bool,
     value : term} ->
    inference_result option

  datatype cps_premise =
      CpsCall of {rel : relation_key, mode : mode, ins : term list,
                  outs : term list}
    | CpsGuard of term
    | CpsGenerate of term

  datatype cps_clause = CpsClause of
    {ins : term list, premises : cps_premise list, outs : term list}

  type program_version

  val same_program_version : program_version * program_version -> bool

  type enumerator =
    {relation : relation_key, mode : mode, version : program_version,
     clauses : cps_clause list}

  val first_order_mode : mode -> bool

  type enumerator_cache_entry =
    {relation : relation_key, mode : mode, program : enumerator}

  val cache_inference : inference_result -> unit
  val program_is_fresh : enumerator -> bool
  val enumerator_for_in :
    enumerator_cache_entry list -> relation_key -> mode -> enumerator option
  val enumerator_for : relation_key -> mode -> enumerator option
  val enumerator_snapshot : unit -> enumerator_cache_entry list
  val enumerator_gen_types : enumerator -> Type.hol_type list
  val enter_private_theory : unit -> unit
  val leave_private_theory : unit -> unit
  val complement_available : relation_key -> mode -> inference_result -> bool
  val top_level_parts : mode -> term list -> (term list * term list) option

  type goal_mode =
    {mode : mode, ins : term list, outs : term list,
     missing : term list, score : premise_score}

  val goal_modes_for_call :
    term list -> term -> inference_result ->
    {ins : term list,
     missing : term list,
     mode : mode,
     outs : term list,
     score : premise_score} list
  val graph_modes_for_call :
    term list -> term -> term list -> inference_result -> goal_mode list
end
