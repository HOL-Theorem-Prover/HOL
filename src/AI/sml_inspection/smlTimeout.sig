signature smlTimeout =
sig

  include Abbrev

  val timeout : real -> ('a -> 'b) -> 'a -> 'b
  val timeout_tactic : real -> tactic -> goal -> goal list option

end
