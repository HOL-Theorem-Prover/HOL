signature hhsPrettify =
sig

include Abbrev

  datatype Proof = 
    Tactic of (string * goal)
  | Then   of (Proof * Proof)
  | Thenl  of (Proof * Proof list)

  val pretty_stac : string -> goal -> goal list -> string

  val prettify_proof : Proof -> Proof
  val minimize_proof : Proof -> Proof
  val minimize_tac   : Proof -> Proof
  val safe_hhs_reconstruct : goal -> Proof -> string

end
