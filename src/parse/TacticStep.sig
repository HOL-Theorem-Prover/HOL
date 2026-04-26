signature TacticStep =
sig

type 'a tac_expr = 'a TacticParse.tac_expr

(* Span extraction for FAtom types where topSpan returns NONE *)
val altSpan : (int * int) tac_expr -> (int * int) option

(* End offset for an FAtom fragment *)
val fragEnd : TacticParse.tac_frag -> int

(* Map fragment constructors to goalFrag function names *)
val openFragName  : TacticParse.tac_frag_open  -> string
val midFragName   : TacticParse.tac_frag_mid   -> string
val closeFragName : TacticParse.tac_frag_close -> string

(* Fragment classification: "expand", "open", "mid", "close", "select", "selects" *)
val frag_type : TacticParse.tac_frag -> string

(* Extract raw text from a fragment using the proofBody string for atom spans.
   Subgoal atoms with backtick-starting text get "sg " prefix. *)
val frag_text : string -> TacticParse.tac_frag -> string

(* Step plan: decompose a parsed tactic tree into (end_offset, type, text)
   triples for every navigable position. Select/selects steps are merged
   with their following bracket into single expand_list steps. *)
val step_plan : string -> (int * int) tac_expr -> (int * string * string) list

end
