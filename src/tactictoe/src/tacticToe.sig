signature tacticToe =
sig
  
  include Abbrev
  
  val set_timeout : real -> unit
    
  val hhs_eval_flag       : bool ref
  val hhs_after_flag      : bool ref
  val hhs_aftersmall_flag : bool ref
  val hhs_aftertac_flag   : bool ref
  val hhs_aftertoken_flag : bool ref
  
  val hhs_norecprove_flag : bool ref
  val hhs_norecord_flag   : bool ref
  val hhs_nolet_flag      : bool ref
  
  val hhs_goalstep_flag   : bool ref

  val init_tactictoe : unit -> unit
  val eval_tactictoe : string -> goal -> unit
  
  val param_glob : (unit -> unit) ref
  val tactictoe : goal -> unit 
  val next_tac : int -> goal -> unit 
  
end
