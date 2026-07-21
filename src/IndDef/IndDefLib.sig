signature IndDefLib =
sig
  include Abbrev
  type monoset = InductiveDefinition.monoset

  val term_of       : term quotation -> term * locn.locn list
  val term_of_absyn : Absyn.absyn -> term * locn.locn list

  val name_from_def : term -> string

  val Hol_reln      : term quotation -> thm * thm * thm
  val xHol_reln     : string -> term quotation -> thm * thm * thm
  val Hol_mono_reln : string -> monoset ->
                      (term * locn.locn list) -> thm * thm * thm

  val derive_mono_strong_induction : monoset -> thm * thm -> thm
  val derive_strong_induction : thm * thm -> thm

  val the_monoset   : monoset ref
  val add_mono_thm  : thm -> unit
  val export_mono   : string -> unit
  val thy_monos     : string -> thm list

  type keyed_thm_map = thm list KNametab.table
  type keyed_thm_set
  val export_keyed_thm_set :
    {settype : string, clause_key : term * term -> term,
     error_structure : string, error_function : string} -> keyed_thm_set
  val keyed_add : keyed_thm_set -> thm -> unit
  val keyed_export : keyed_thm_set -> string -> unit
  val keyed_thy_thms : keyed_thm_set -> string -> thm list
  val keyed_map : keyed_thm_set -> unit -> keyed_thm_map
  val keyed_map_by_theory : keyed_thm_set -> {thyname : string} ->
                            keyed_thm_map option

  type rule_induction_map = keyed_thm_map
  val thy_rule_inductions : string -> thm list
  val rule_induction_map : unit -> rule_induction_map
  val rule_induction_map_by_theory : {thyname : string} ->
                                     rule_induction_map option
  val add_rule_induction : thm -> unit
  val export_rule_induction : string -> unit

  val isolate_to_front : int -> term -> tactic

end
