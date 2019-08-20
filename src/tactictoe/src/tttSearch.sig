signature tttSearch =
sig

  include Abbrev

  datatype proof_status =
    ProofError | ProofSaturated | ProofTimeOut | Proof of string

  val search :
    (int -> goal -> string list) -> (goal -> string list) ->
    goal -> proof_status

end
