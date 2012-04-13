signature countableLib = sig
  include Abbrev
  val mk_count_aux_inj_rwt_ttac : hol_type list -> tactic option -> thm list
  val mk_count_aux_inj_rwt : hol_type list -> thm list
  val inj_rwt_to_countable : thm -> thm
end
