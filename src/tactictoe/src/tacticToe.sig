signature tacticToe =
sig
  
  include Abbrev
  
  val set_timeout : real -> unit
  
  val predict_thm : int -> goal -> string list
  val metis_n : int -> tactic
  
  val hhs_eval_flag : bool ref
  val eval_tactictoe : goal -> unit
  
  val tactictoe : goal -> unit 
  val next_tac : int -> goal -> unit 
  
end
