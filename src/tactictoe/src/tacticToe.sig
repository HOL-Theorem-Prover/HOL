signature tacticToe =
sig

  include Abbrev
 
  val set_timeout : real -> unit
  val ttt : tactic
  val tactictoe : term -> thm
 
end
