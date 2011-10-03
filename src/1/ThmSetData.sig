signature ThmSetData =
sig

  type data = Theory.LoadableThyData.t
  val new    : string ->
               (string list -> data * (string * Thm.thm) list) *
               (data -> (string * Thm.thm) list option)
  val new_exporter : string ->
                     (Thm.thm list -> unit) ->
                     {dest : data -> (string * Thm.thm) list option,
                      export : string -> unit,
                      mk : string list -> data * (string * Thm.thm) list}

end
