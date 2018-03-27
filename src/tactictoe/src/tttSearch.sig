signature tttSearch =
sig

  include Abbrev

  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)

  val last_stac : string ref (* for debugging purpose *)

  datatype proof_status_t =
    ProofError | ProofSaturated | ProofTimeOut | Proof of string

  val search :
    (int -> goal -> string list) ->
    (goal -> string list) ->
    (goal list -> real) ->
    (int -> goal -> string option) ->
    goal -> proof_status_t

end
