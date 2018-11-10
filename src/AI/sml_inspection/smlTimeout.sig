signature smlTimeout =
sig

  exception Timeout
  val timeout : real -> ('a -> 'b) -> 'a -> 'b
  val timeout_tactic : real -> tactic -> goal -> goal list option

end
