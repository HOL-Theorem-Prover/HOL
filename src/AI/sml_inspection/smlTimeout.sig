signature smlTimeout =
sig

  include Abbrev

  exception FunctionTimeout
  datatype 'a result = Res of 'a | Exn of exn
  
  val interruptkill : Thread.thread -> unit
  val timeout : real -> ('a -> 'b) -> 'a -> 'b
  val timeout_tactic : real -> tactic -> goal -> goal list option
  
  val timeout_ext : real -> 
     (goal -> goal list option) -> goal -> goal list option
  val stop_global_worker : unit -> unit

end
