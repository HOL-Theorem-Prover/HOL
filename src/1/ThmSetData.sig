signature ThmSetData =
sig

  type data = Theory.LoadableThyData.t
  type thm = Thm.thm
  datatype setdelta = Addition of string * thm
                    | RemovalInstruction of string
  type exportfns =
       { add : {thy : string, named_thms : (string * thm) list} -> unit,
         remove : {thy : string, removes : string list} -> unit}
  val added_thms : setdelta list -> thm list

  val new_exporter :
      {settype : string, efns : exportfns} ->
      {export : string -> unit, delete : string -> unit}

  val current_data : {settype:string} -> setdelta list
  val theory_data : {settype : string, thy: string} -> setdelta list
  val all_data : {settype:string} -> (string * setdelta list) list
  val data_storefn : {settype:string} -> (string -> unit) option
  val data_exportfns : {settype:string} -> exportfns option

  val all_set_types : unit -> string list

end
