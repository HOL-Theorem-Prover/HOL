signature TacticLeafSource =
sig

(* Converts tactic-expression leaves into SML source for execution.

   Verbatim source comes directly from a complete source span.
   Synthesised source is generated when a leaf cannot be executed
   verbatim and uses qualified names so that it does not depend on
   script-local opens.  Semantic no-ops produce NONE.

   Consumers of ProofStepPlan should use the tactic kind stored in
   each Leaf; fragmentLeafKind is for leaves obtained from tac_frag. *)

datatype source = Verbatim of string | Synthesised of string

val sourceText: source -> string

(* Returns NONE for a no-op, Verbatim for complete user source, and
   Synthesised for fully qualified source constructed by the lowering. *)
val leafSource: string -> (int * int) TacticParse.tac_expr -> source option

(* Classifies leaves extracted from tac_frag.  ProofStepPlan consumers
   should use the kind already stored in each Leaf. *)
val fragmentLeafKind:
  (int * int) TacticParse.tac_expr -> ProofStepPlan.leaf_kind

end
