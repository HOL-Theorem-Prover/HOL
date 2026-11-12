signature Refute_Narrow = sig
  type hol_type = Type.hol_type

  type position = int list

  datatype narrowing_type =
    Narrowing_sum_of_products of
      {depth : int, complete : bool, syntactic_complete : bool,
       depth_stable : bool,
       alternatives :
         {id : int, exact : Term.term option,
          arguments : narrowing_type list} list}
  type narrowing_alternative =
    {id : int, exact : Term.term option, arguments : narrowing_type list}

  datatype narrowing_term =
      Narrowing_variable of position * narrowing_type
    | Narrowing_constructor of int * narrowing_term list

  datatype evaluation =
      Known of {genuine : bool, result : bool}
    | NeedsRefinement of position

  datatype plain_result =
      PlainCounterexample of
        {genuine : bool, arguments : narrowing_term list, tests : int,
         decided : int}
    | PlainExhausted of {tests : int, decided : int, complete : bool}

  datatype engine_selection =
      PlainEngine
    | PnfEngine
    | PlainRefusal of string list

  datatype pnf_quantifier = Existential | Universal

  datatype truth =
      Eval of {result : bool, potential : bool}
    | Unevaluated
    | Unknown

  datatype tree =
      Leaf of truth
    | Variable of
        pnf_quantifier * truth * position * narrowing_type * tree
    | Constructor of
        pnf_quantifier * truth * position * narrowing_type *
        (int * int * tree) option * (int * tree) list

  datatype example =
      UnivExample of narrowing_type * narrowing_term * example
    | ExExample of
        narrowing_type * (narrowing_term * example) list
    | EmptyExample

  datatype pnf_result =
      PnfCounterexample of
        {genuine : bool, example : example, tree : tree, tests : int,
         decided : int}
    | PnfExhausted of
        {truth : truth, tree : tree, tests : int, decided : int,
         complete : bool}

  exception ShapeFailure of hol_type * string

  val first_completion :
    narrowing_type -> narrowing_term -> narrowing_term option
  val new_shape_memo : unit -> (int * hol_type, 'a) Redblackmap.dict ref
  val shape_of_with :
    (int * hol_type, narrowing_type) Redblackmap.dict ref -> int ->
    hol_type -> narrowing_type
  val inapplicable_message : hol_type -> string -> string
  val all_ground : narrowing_term list -> bool
  val refute_plain_avoiding :
    bool ->
    {accept : narrowing_term list -> bool -> bool,
     arguments : narrowing_term list,
     evaluate : bool -> narrowing_term list -> evaluation} ->
    plain_result
  val tree_of : (pnf_quantifier * narrowing_type) list -> tree
  val replay_of_example :
    (int -> narrowing_term -> Term.term) -> example -> Refute_Eval.case_tree
  val case_bindings :
    (Refute_Eval.quant * Term.term) list -> Refute_Eval.case_tree ->
    (Term.term * Term.term) list
  val leading_universals : int -> example -> narrowing_term list
  val refute_pnf_avoiding :
    bool -> int -> (bool -> narrowing_term list -> evaluation) ->
    ({example : example, genuine : bool, tree : tree} -> bool) -> tree ->
    pnf_result
  val prenex_conversion : Term.term -> Thm.thm
  val strip_quantifiers :
    Term.term -> (Refute_Eval.quant * Term.term) list * Term.term
  val finitize_functions :
    (Refute_Eval.quant * Term.term) list * Term.term ->
    (Refute_Eval.quant * Term.term) list * Term.term
  val eval_finite_functions_as : hol_type -> Term.term -> Term.term
  val contains_existentials : (Refute_Eval.quant * Term.term) list -> bool
  val select_for_config :
    Refute_Core.config -> Term.term ->
    engine_selection * Refute_Eval.qc_problem
end
