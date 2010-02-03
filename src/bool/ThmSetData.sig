signature ThmSetData =
sig

  type data = Theory.LoadableThyData.t
  val new    : string ->
               (string list -> data * (string * Thm.thm) list) *
               (data -> (string * Thm.thm) list option)

end
