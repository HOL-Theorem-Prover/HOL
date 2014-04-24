signature ThmSetData =
sig

  type data = Theory.LoadableThyData.t
  val new_exporter : string ->
                     (string -> Thm.thm list -> unit) ->
                     {dest : data -> (string * Thm.thm) list option,
                      export : string -> unit,
                      mk : string list -> data * (string * Thm.thm) list}

  val new_storage_attribute : string -> unit
  val store_attribute : {attribute: string, thm_name : string} -> unit

  val current_data : string -> (string * Thm.thm) list
  val theory_data : {settype : string, thy: string} ->
                    (string * Thm.thm) list
  val all_data : string -> (string * (string * Thm.thm) list) list
  val data_storefn : string -> (string -> unit) option
  val data_exportfn : string -> (string -> Thm.thm list -> unit) option

  val all_set_types : unit -> string list

end
