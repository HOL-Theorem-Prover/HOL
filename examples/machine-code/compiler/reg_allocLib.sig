signature reg_allocLib =
sig

  include Abbrev

  val allocate_registers  : int -> term -> thm

end
