signature tacticToe =
sig
  
  include Abbrev

  val set_timeout : real -> unit
  val eval_tactictoe : goal -> unit
  val tactictoe : goal -> unit 
  val next_tac : int -> goal -> unit 
  
end
