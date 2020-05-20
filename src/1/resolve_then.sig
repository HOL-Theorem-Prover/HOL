signature resolve_then =
sig

  include Abbrev
  datatype match_position = datatype thmpos_dtype.match_position
  val resolve_then : match_position -> thm_tactic -> thm -> thm -> tactic

end
