signature rlMiniProve =
sig

  include Abbrev

  type situation = bool * rlMiniRules.board

  val log_eval : string -> string -> unit

  val p1_startpos : term -> situation
  val status_of : situation -> psMCTS.status
  val apply_move : rlMiniRules.move -> situation -> situation
  val string_of_move : rlMiniRules.move -> string
  val nntm_of_sit : situation -> term

  val wrap_rl_loop : int -> int -> term list -> rlMiniTrain.allex
  val wrap_rlknn_loop : int -> int -> term list -> rlMiniTrain.allex

end
