signature hhsThmData =
sig

include Abbrev
  
  type lbl_t = (string * real * goal * goal list)
 
  (* val metis_provable : int -> real -> goal -> bool : too slow *)
  val mk_metis_call : string list -> string
  
  (* mdict I/O *)    
  val import_mdict : unit -> unit
  val update_mdict : string -> unit
  val export_thmfea : string -> unit


end
