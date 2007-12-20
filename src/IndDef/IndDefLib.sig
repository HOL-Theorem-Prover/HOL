signature IndDefLib =
sig
  include Abbrev
  type monoset = InductiveDefinition.monoset

  val term_of       : term quotation -> term * locn.locn list
  val term_of_absyn : Absyn.absyn -> term * locn.locn list

  val Hol_reln      : term quotation -> thm * thm * thm
  val Hol_mono_reln : monoset -> (term * locn.locn list) -> thm * thm * thm

  val derive_mono_strong_induction : monoset -> thm * thm -> thm
  val derive_strong_induction : thm * thm -> thm

  val the_monoset   : monoset ref
  val add_mono_thm  : thm -> unit
  val export_mono   : string -> unit

end
