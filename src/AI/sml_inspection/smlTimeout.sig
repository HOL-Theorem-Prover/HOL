signature smlTimeout =
sig

  include Abbrev

  exception FunctionTimeout

  val interruptkill : Thread.thread -> unit
  val timeout : real -> ('a -> 'b) -> 'a -> 'b

end
