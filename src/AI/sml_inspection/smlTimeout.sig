signature smlTimeout =
sig

  exception TimeOut
  val timeOut : real -> ('a -> 'b) -> 'a -> 'b
  val timed_tactic : real -> tactic -> goal -> goal list option

end
