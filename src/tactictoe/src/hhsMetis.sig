signature hhsMetis =
sig

include Abbrev
  
  type lbl_t = (string * real * goal * goal list)
   
  
  (* depends on mdict *)
  val metis_provable : int -> real -> goal -> bool
  
  (* search *)
  val stactime_dict : (string, real) Redblackmap.dict ref
  val add_metis : 
    (string, tactic) Redblackmap.dict ref ->
    (int -> goal -> string list) ref -> 
    goal * (lbl_t * real) list -> 
    goal * (lbl_t * real) list
  val add_hammer : 
    goal * (lbl_t * real) list -> 
    goal * (lbl_t * real) list
    
    
  val import_mdict : unit -> unit
  val update_mdict : string -> unit
  val export_mdict : string -> unit


end
