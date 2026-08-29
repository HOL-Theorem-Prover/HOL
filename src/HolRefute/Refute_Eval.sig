signature Refute_Eval = sig
  type term = Term.term

  type mode = Refute_SmartGen.mode
  type program_version = Refute_SmartGen.program_version
  type relation_key = Refute_SmartGen.relation_key

  datatype plan =
      Test of term
    | Gen of term * plan
    | Bind of term * term * plan option * plan
    | Split of term * (term * term list * plan) list
    | Guard of {condition : term, smart : bool, cont : plan}
      (* [smart] marks [condition] as the closed complement of a
         negated relational premise: true only when every admitted
         clause of the relation's negative mode is decided false.
         Evaluated with the same three-valued (true/false/stuck)
         discipline either way; a stuck evaluation must never be read
         as [false].  Marks [plan_uses_smart] so the executability
         gate can lift.

         A complement deliberately carries no [program_version],
         unlike [Enum] and [SmartGuard]: those name a program resolved
         from the mutable [Refute_SmartGen] enumerator cache at
         execution time, so a redefinition can silently replace the
         cache entry behind an old plan's back, and only the version
         stamp lets [Refute_QC.same_plan] tell a stale selection from
         a current one.  A complement is instead inlined whole into
         [condition] as a term value, with no deferred lookup that can
         go stale.  [Refute_QC.same_plan] compares that term with
         [Term.aconv]: if the relation is redefined and the
         re-derived complement differs, the comparison fails and the
         cached selection is not reused; if the redefinition
         re-derives an identical complement, the comparison succeeds
         and reuse is correct, because the term being tested is
         exactly the same value either way. *)
    | SmartGuard of {predicate : term, version : program_version,
                     cont : plan}
    | Enum of {rel : relation_key, mode : mode, version : program_version,
               ins : term list, outs : term list, cont : plan}
    | Prune

  datatype quant = Forall | Exists

  datatype qc_problem =
      Plans of plan list
    | Pnf of {prefix : (quant * term) list, body : term}

  (* Frozen narrowing-domain metadata.  [complete] is computed when the
     depth-indexed shape is built; replay additionally checks it against
     TypeBase rather than trusting this flag. *)
  datatype case_shape =
    CaseShape of
      {depth : int, complete : bool,
       constructors : case_constructor list}
  withtype case_constructor = {id : int, fields : case_shape list}

  datatype case_pattern =
      CaseVariable
    | CaseConstructor of int * case_pattern list

  (* A proof-oriented projection of the PNF refinement tree. *)
  datatype case_tree =
      CaseLeaf
    | CaseUniversal of
        {shape : case_shape, witness : term, subtree : case_tree}
    | CaseExistential of
        {shape : case_shape,
         branches : (case_pattern * term * case_tree) list}

  type candidate =
    {env : (term * term) list,
     ground_env : (term * term) list option,
     case_tree : case_tree option,
     genuine : bool,
     run_depth : int option}

  datatype verdict = Continue | Found of candidate

  datatype run_result =
      CexFound of candidate
    | Exhausted of {complete : bool}
    | GaveUp of string

  datatype strategy =
      Exhaustive
    | Random of {seed : IntInf.int}
    | Narrowing

  val ground_strategy :
    strategy ->
    {exhaustive : unit -> 'a, random : IntInf.int -> 'a} -> 'a
  val with_plans : qc_problem -> (plan list -> 'a) -> 'a

  type run_input =
    { genuine_only : bool,
      card : int,
      size : int,
      draws : int,
      ignored : candidate list }

  type compiled_test =
    { run : run_input -> run_result,
      close : unit -> unit,
      max_chunk : int option,
      last_stats : (string * int) list ref }

  datatype compile_result =
      Compiled of compiled_test
    | Inapplicable of string list

  type substrate =
    { name : string,
      priority : int,
      accepts : qc_problem -> bool,
      preflight :
        (Refute_Core.config -> strategy -> plan list -> term list ->
          string list) option,
      compile : Refute_Core.config -> strategy -> qc_problem ->
        compile_result }

  val rand_next : IntInf.int -> IntInf.int
  val rand_out : IntInf.int -> IntInf.int
  val rand_below : IntInf.int -> IntInf.int -> IntInf.int * IntInf.int
  val rand_below_limit : IntInf.int
  val checked_rand_below :
    IntInf.int -> IntInf.int -> IntInf.int * IntInf.int
  val normalize_seed : IntInf.int -> IntInf.int
  val take_session_seed : unit -> IntInf.int
  val session_seed : IntInf.int ref

  val plan_gen_types : plan -> Type.hol_type list
  (* Fuel-bounded and needs enumerator programs: [Enum] and
     [SmartGuard], whose terminal exhaustion cannot be certified.
     Excludes a smart [Guard], whose condition is an ordinary closed
     guard. *)
  val plan_uses_enum : plan -> bool
  (* Contains any smart construct -- [Enum], [SmartGuard] or a smart
     [Guard] -- that the executability gate must account for. *)
  val plan_uses_smart : plan -> bool
  val same_env : (term * term) list -> (term * term) list -> bool
  val same_case_tree : case_tree option -> case_tree option -> bool
  val ignored_candidate : candidate -> candidate list -> bool
  val fully_applied_constructor : term -> (term * term list) option

  val dump_plan : plan -> plan
  val dump_stream : compiled_test -> {size : int, count : int} ->
    term list list

  val register_substrate : substrate -> unit
  val get_substrates : unit -> substrate list
end
