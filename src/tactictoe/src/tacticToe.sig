signature tacticToe =
sig
  
  include Abbrev
  
  val set_timeout : real -> unit
    
  
  val hhs_after_flag       : bool ref
  val hhs_aftersmall_flag  : bool ref
  val hhs_aftertac_flag    : bool ref
  val hhs_aftertoken_flag  : bool ref
  val hhs_afterthm_flag    : bool ref
  val hhs_afterstring_flag : bool ref
  val hhs_aftertactic_flag : bool ref
  val hhs_afterall_flag    : bool ref
  val hhs_afterall2_flag   : bool ref
  val hhs_afterthm2_flag   : bool ref
  val hhs_afterthmthm_flag : bool ref
  
  val hhs_eval_flag        : bool ref
  val hhs_internalthm_flag : bool ref
  val hhs_norecprove_flag  : bool ref
  val hhs_norecord_flag    : bool ref
  val hhs_nolet_flag       : bool ref
  val hhs_goalstep_flag    : bool ref
  
  val set_isearch_hook : (unit -> unit) ref
  val init_tactictoe : unit -> unit
  val eval_tactictoe : string -> goal -> unit
  
  val tactictoe : goal -> tactic 
  val tt_tac : tactic
  
  val next_tac_glob : tactic list ref
  val next_tac_number : int ref
  val next_tac : goal -> unit 
  val next : int -> tactic

end
