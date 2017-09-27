signature hhsMetis =
sig

include Abbrev
  
  type lbl_t = (string * real * goal * goal list)
  
  (* parameters *)
  val hhs_metis_flag  : bool ref
  val hhs_metis_time  : real ref
  val hhs_metis_npred : int ref
  val hhs_thmortho_flag : bool ref
  val hhs_stacpred_flag : bool ref
  val hh_stac_flag : bool ref
  
  
  (* external predictions *)
  val dependency_of_thm : string -> string list
  
  (* I/O *)
  val init_mdict   : unit -> unit
  val update_mdict : string -> unit
  val export_mdict : string -> unit
  
  (* depends on mdict *)
  val solved_by_metis : int -> real -> goal -> bool
  
  (* search *)
  val stactime_dict : (string, real) Redblackmap.dict ref
  val add_metis : 
    (string, tactic) Redblackmap.dict ref ->
    (goal -> string list) ref -> 
    goal * (lbl_t * real) list -> 
    goal * (lbl_t * real) list

  val init_thml_glob : unit -> unit
  val add_accept : 
    (string, tactic) Redblackmap.dict ref ->
    goal * (lbl_t * real) list -> 
    goal * (lbl_t * real) list
  
  val addpred_stac :
    (string, tactic) Redblackmap.dict ref ->
    (goal -> string list) ref -> 
    goal * (lbl_t * real) list -> 
    goal * (lbl_t * real) list

end
