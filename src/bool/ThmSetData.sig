signature ThmSetData =
sig

  type data = Theory.LoadableThyData.t
  val new    : string ->
               (string list -> data) * (data -> (string * Thm.thm) list option)

end
