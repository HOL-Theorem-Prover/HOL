signature m1_progLib =
sig

  include Abbrev;

  val decompile_m1    : string -> term quotation -> thm * thm

end
