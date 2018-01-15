signature hhsExec =
sig

  include Abbrev
  
  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)
  
  val hhs_bool_glob    : bool ref
  val hhs_tacticl_glob : tactic list ref
  val hhs_tactic_glob  : tactic ref
  val hhs_string_glob  : string ref
  val hhs_goal_glob    : goal ref
  
  val hh_stac_glob     : 
    (int -> (int, real) Redblackmap.dict * (string * fea_t) list ->
     int -> goal -> string option) ref
  val update_hh_stac   : unit -> unit
  val metis_tac_glob   : (thm list -> tactic) option ref
  val update_metis_tac : unit -> unit

  val exec_sml         : string -> string -> bool  
  
  val hhs_thm          : thm ref
  val is_thm           : string -> bool
  val thm_of_sml       : string -> (string * thm) option
  
  val smltype_of_value : 
    (string * PolyML.NameSpace.Values.value) list -> string -> string
  val is_thm_value     : 
    (string * PolyML.NameSpace.Values.value) list -> string -> bool
  
  val namespace_thms   : unit -> (string * thm) list
   
  val is_tactic        : string -> bool
  val is_string        : string -> bool
  val is_pointer_eq    : string -> string -> bool
  
  val hhs_invalid_flag : bool ref
  val tactic_of_sml    : string -> tactic
  val timed_tactic_of_sml : string -> tactic
  val tacticl_of_sml   : string list -> tactic list
  val string_of_sml    : string -> string
  val goal_of_sml      : string -> goal
  
  
  val app_tac    : real -> tactic -> goal -> goal list option
  val rec_stac   : real -> string -> goal -> goal list option
  val rec_sproof : string -> goal -> goal list option

end
