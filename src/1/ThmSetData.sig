signature ThmSetData =
sig

  type data = Theory.LoadableThyData.t
  type thm = Thm.thm
  type thname = KernelSig.kernelname
  val toKName : string -> thname
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

  type 'value ops = {apply_to_global : setdelta -> 'value -> 'value,
                     thy_finaliser : ({thyname:string} -> setdelta list ->
                                      'value -> 'value) option,
                     uptodate_delta : setdelta -> bool, initial_value : 'value,
                     apply_delta : setdelta -> 'value -> 'value}
  val export_with_ancestry:
      {settype : string, delta_ops : 'value ops} ->
      (setdelta,'value) AncestryData.fullresult

  type simple_dictionary = (string,thm) Binarymap.dict
  val simple_dictionary_ops : simple_dictionary -> simple_dictionary ops
  val export_simple_dictionary :
      {settype : string, initial : (string * thm) list} ->
      {merge : string list -> simple_dictionary option,
       DB : {thyname:string} -> simple_dictionary option,
       temp_exclude : string -> unit, exclude : string -> unit,
       export : string -> unit, temp_export : string -> unit,
       getDB : unit -> simple_dictionary,
       get_thms : unit -> thm list,
       temp_setDB : simple_dictionary -> unit}
  (* creates a dictionary that names theorems "0", "1", etc *)
  val sdict_withflag_thms : {getDB : unit -> simple_dictionary,
                             temp_setDB : simple_dictionary -> unit} *
                            thm list -> ('a -> 'b) -> ('a -> 'b)

  type alist = (string * thm) list
  val alist_ops : alist -> alist ops
  val export_alist :
      {settype : string, initial : (string * thm) list} ->
      {merge : string list -> alist option,
       DB : {thyname:string} -> alist option,
       temp_exclude : string -> unit, exclude : string -> unit,
       export : string -> unit, temp_export : string -> unit,
       getDB : unit -> alist,
       get_thms : unit -> thm list,
       temp_setDB : alist -> unit}
  (* creates alist that names theorems "0", "1", etc *)
  val alist_withflag_thms : {getDB : unit -> alist,
                             temp_setDB : alist -> unit} *
                            thm list -> ('a -> 'b) -> ('a -> 'b)

  val list_ops : thm list -> thm list ops
  val export_list :
      {settype : string, initial : thm list} ->
      {merge : string list -> thm list option,
       DB : {thyname:string} -> thm list option,
       export : string -> unit, temp_export : string -> unit,
       temp_exclude : thm -> unit, (* checks list with thm-concl-equality *)
       getDB : unit -> thm list,
       temp_setDB : thm list -> unit}



end
