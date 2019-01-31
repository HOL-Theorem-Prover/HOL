signature mp_then =
sig

  include Abbrev

  datatype match_position
    = Any
    | Pat of term quotation
    | Pos of (term list -> term)
    | Concl

  val mp_then : thm_tactic -> match_position -> thm -> thm -> tactic

end
