signature ThmSetData =
sig

  type data = Theory.LoadableThyData.t
  val new_exporter : string ->
                     (string -> Thm.thm list -> unit) ->
                     {dest : data -> (string * Thm.thm) list option,
                      export : string -> unit,
                      mk : string list -> data * (string * Thm.thm) list}

  val current_data : string -> (string * Thm.thm) list
  val theory_data : {settype : string, thy: string} ->
                    (string * Thm.thm) list
  val all_data : string -> (string * (string * Thm.thm) list) list

  val all_set_types : unit -> string list

end
