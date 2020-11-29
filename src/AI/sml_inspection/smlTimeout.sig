signature smlTimeout =
sig

  include Abbrev

  exception FunctionTimeout
  
  val interruptkill : Thread.thread -> unit
  val timeout : real -> ('a -> 'b) -> 'a -> 'b
  val timeout_tactic : real -> tactic -> goal -> goal list option

end
