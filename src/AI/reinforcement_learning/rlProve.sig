signature rlProve =
sig

  include Abbrev

  type situation = bool * rlRules.board

  val log_eval : string -> string -> unit

  val p1_startpos : term -> situation
  val status_of : situation -> psMCTS.status
  val apply_move : rlRules.move -> situation -> situation
  val string_of_move : rlRules.move -> string
  val nntm_of_sit : situation -> term
  val fevalpoli : rlTrain.alltnn -> situation ->
    real * (rlRules.move * real) list

  val wrap_rl_loop : int -> rlTrain.allex * int

end
