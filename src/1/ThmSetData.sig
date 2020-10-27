signature ThmSetData =
sig

  type data = Theory.LoadableThyData.t
  type thm = Thm.thm
  type thname = KernelSig.kernelname
  datatype setdelta = ADD of thname * thm | REMOVE of string
  type exportfns =
       { add : {thy : string, named_thm : thname * thm} -> unit,
         remove : {thy : string, remove : string} -> unit}
  val added_thms : setdelta list -> thm list
  val mk_add : string -> setdelta

  val new_exporter :
      {settype : string, efns : exportfns} ->
      {export : string -> unit, delete : string -> unit}

  val current_data : {settype:string} -> setdelta list
  val theory_data : {settype : string, thy: string} -> setdelta list
  val all_data : {settype:string} -> (string * setdelta list) list
  val data_exportfns : {settype:string} -> exportfns option

  val all_set_types : unit -> string list

  val export_with_ancestry:
      {settype : string,
       delta_ops : {apply_to_global : setdelta -> 'value -> 'value,
                    uptodate_delta : setdelta -> bool, initial_value : 'value,
                    apply_delta : setdelta -> 'value -> 'value}
      } ->
      (setdelta,'value) AncestryData.fullresult

end
