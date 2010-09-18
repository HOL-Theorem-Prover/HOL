signature IndDefLib =
sig
  include Abbrev
  type monoset = InductiveDefinition.monoset

  val term_of       : term quotation -> term * locn.locn list
  val term_of_absyn : Absyn.absyn -> term * locn.locn list

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

  val thy_rule_inductions : string -> thm list
  val rule_induction_map : unit ->
                           ({Thy:string,Name:string},thm list) Binarymap.dict
  val add_rule_induction : thm -> unit
  val export_rule_induction : string -> unit

end
