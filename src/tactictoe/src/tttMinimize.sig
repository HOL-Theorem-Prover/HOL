signature tttMinimize =
sig

  include Abbrev

  datatype Proof =
    Tactic of (string * goal)
  | Then   of (Proof * Proof)
  | Thenl  of (Proof * Proof list)

  val minimize_stac : real -> string -> goal -> goal list -> string
  val minimize_proof : Proof -> Proof
  val reconstruct : goal -> Proof -> string

end
