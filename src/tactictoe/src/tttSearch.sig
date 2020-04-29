signature tttSearch =
sig

  include Abbrev

  datatype proof_status =
    ProofError | ProofSaturated | ProofTimeOut | Proof of string

  val search : (int -> goal -> string list) -> (goal -> string list) ->
    goal -> proof_status

  type move = string
  type board = goal list * move list
  val mk_game : (int -> goal -> string list) -> (goal -> string list) ->
     (board,move) psMCTS.game
  val alt_search : (int -> goal -> string list) -> (goal -> string list) ->
    goal -> proof_status

  val tree_glob : (board,move) psMCTS.tree list ref
  val print_tree : (board, string) psMCTS.tree -> string * psMCTS.id -> unit
  val extract_ex : 
    (board, string) psMCTS.tree ->
    psMCTS.id ->
    ((goal * string * (goal * goal list) * goal list) * bool) list

end
