signature tttSearch =
sig

  include Abbrev

  type lbl = (string * real * goal * goal list)
  type fea = int list

  datatype proof_status_t =
    ProofError | ProofSaturated | ProofTimeOut | Proof of string

  val search :
    (int -> goal -> string list) -> (goal -> string list) ->
    goal -> proof_status_t

end
