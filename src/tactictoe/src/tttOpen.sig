signature tttOpen =
sig
  
  val theory_files : string -> string list
  val run_holmake : string -> unit
  val run_rm_script : string -> unit 
   
  val tactictoe_cleanval : unit -> unit
  val tactictoe_cleanstruct : string -> unit
  val tactictoe_export : string -> unit
  
  val export_struct : string -> string -> unit
  val import_struct : 
    string -> (string list * string list * string list * string list)
  val export_import_struct : 
    string -> string -> 
    (string list * string list * string list * string list)   
   
end
