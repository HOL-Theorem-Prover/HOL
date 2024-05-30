signature resolve_then =
sig

  include Abbrev
  datatype match_position = datatype thmpos_dtype.match_position
  val gen_resolve_then : match_position -> thm -> thm -> (thm -> 'a) -> 'a
  val resolve_then : match_position -> thm_tactic -> thm -> thm -> tactic

end
