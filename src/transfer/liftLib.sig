signature liftLib =
sig

  include Abbrev
  val QtDB : unit -> thm list
  val liftdef : thm -> string -> thm * thm

end
