signature psMinimize =
sig

  include Abbrev

  datatype proof =
    Tactic of (string * goal)
  | Then   of (proof * proof)
  | Thenl  of (proof * proof list)

  val mini_tactic_time : real ref
  val mini_proof_time : real ref

  val minimize_stac : real -> string -> goal -> goal list -> string
  val requote_sproof : string -> string
  val minimize_proof : proof -> proof
  val unsafe_sproof : proof -> string
  val reconstruct : goal -> proof -> string

end
