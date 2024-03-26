(*---------------------------------------------------------------------------*
 *       New routines supporting the definition of types                     *
 *                                                                           *
 * USAGE: rich_new_type {tyname, exthm, ABS, REP}                            *
 *                                                                           *
 * ARGUMENTS: tyname -- the name of the new type                             *
 *                                                                           *
 *            exthm --- the existence theorem of the new type (|- ?x. P x)   *
 *                                                                           *
 *            ABS  --- the name of the required abstraction function         *
 *                                                                           *
 *            REP  --- the name of the required representation function      *
 *---------------------------------------------------------------------------*)

signature newtypeTools =
sig

  include Abbrev
  val rich_new_type : {tyname: string,
                       exthm: thm,
                       ABS: string,
                       REP: string}
                       ->
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
