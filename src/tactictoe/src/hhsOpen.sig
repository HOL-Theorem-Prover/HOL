signature hhsOpen =
sig

  val cthy_unfold_glob : string ref
  val debug_unfold : string -> unit
  
  val run_hol : string -> unit
  
  val read_open : 
    string -> (string list * string list * string list * string list)
  val export_struct :
    string -> (string list * string list * string list * string list) 
    
  val tactictoe_cleanval : unit -> unit
  val tactictoe_cleanstruct : string -> unit
  val tactictoe_export : string -> unit
  
end
