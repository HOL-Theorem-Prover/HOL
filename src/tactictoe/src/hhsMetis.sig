signature hhsMetis =
sig

include Abbrev
  
  type lbl_t = (string * real * goal * goal list)
 
  (* external predictions *)
  val dependency_of_thm : string -> string list
  
  (* depends on mdict *)
  val theorem_predictor : bool -> int -> goal -> string list
  val metis_provable : bool -> int -> real -> goal -> bool
  
  (* search *)
  val stactime_dict : (string, real) Redblackmap.dict ref
  val add_metis : 
    (string, tactic) Redblackmap.dict ref ->
    (bool -> int -> goal -> string list) ref -> 
    goal * (lbl_t * real) list -> 
    goal * (lbl_t * real) list
  val add_hammer : 
    goal * (lbl_t * real) list -> 
    goal * (lbl_t * real) list
    
    
  val import_mdict : unit -> unit
  val update_mdict : string -> unit
  val export_mdict : string -> unit


end
