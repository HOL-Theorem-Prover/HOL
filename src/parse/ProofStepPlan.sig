signature ProofStepPlan =
sig

  datatype leaf_kind = TacticLeaf | ListTacticLeaf

  datatype 'a selector =
      SelectFirst
    | SelectMatchingFirst of 'a
    | SelectMatchingAll of 'a

  datatype select_mode = SelectSolve | SelectKeep

  datatype 'a step =
      Leaf of {kind : leaf_kind, tactic : 'a TacticParse.tac_expr}
    | Each of 'a step list
    | Select of {selector : 'a selector, mode : select_mode,
                 body : 'a step list}
    | Cases of 'a step list list
    | Choice of 'a step list list
    | Repeat of 'a step list
    | Try of 'a step list

  type 'a plan = 'a step list

  (* The standard plan is deliberately conservative about execution
     granularity.  In particular, tactic- and list-tactic-level repeats and
     goal reordering are leaves: an executor may not safely checkpoint inside
     them without also modelling their per-goal traversal and goal order.
     Thus the TacticParse encoding of REVERSE t as t THEN_LT REVERSE_LT is
     kept as one source-level tactic leaf. *)
  val fromTactic : 'a TacticParse.tac_expr -> 'a plan

  datatype path_component =
      PathStep of int
    | PathEach of int
    | PathSelect
    | PathCase of int
    | PathAlternative of int
    | PathTry
    | PathRepeat of int

  type path = path_component list

  val stepAtPath : 'a plan -> path -> 'a step option

  (* Canonical encodings omit source positions unless the caller includes
     them in its projections.  leaf must encode the semantic content of an
     opaque executable leaf; annotation encodes selector payloads. *)
  val canonicalPlan :
    {leaf : leaf_kind -> 'a TacticParse.tac_expr -> string,
     annotation : 'a -> string} -> 'a plan -> string

  val canonicalPrefix :
    {leaf : leaf_kind -> 'a TacticParse.tac_expr -> string,
     annotation : 'a -> string} -> 'a plan -> path -> string option

end
