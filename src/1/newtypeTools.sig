signature newtypeTools =
sig

  include Abbrev
  val rich_new_type : string * thm ->
                      {absrep_id: thm,
                       newty: hol_type,
                       repabs_pseudo_id: thm,
                       termP: term,
                       termP_exists: thm,
                       termP_term_REP: thm,
                       term_ABS_t: term,
                       term_ABS_pseudo11: thm,
                       term_REP_t: term,
                       term_REP_11: thm}

end
