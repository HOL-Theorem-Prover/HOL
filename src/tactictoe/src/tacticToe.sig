signature tacticToe =
sig
  
  include Abbrev
  (* 
  val next_tac : int -> goal -> unit 
  val set_timeout : real -> unit
  val tactictoe : term -> unit
  val bare_tactictoe : term -> unit
  val nohide_tactictoe : term -> unit
  *)
  val eval_tactictoe : goal -> unit

end
