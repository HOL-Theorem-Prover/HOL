signature CoIndDefLib =
sig
  include Abbrev
  type monoset = InductiveDefinition.monoset

  val Hol_coreln      : term quotation -> thm * thm * thm
  val xHol_coreln     : string -> term quotation -> thm * thm * thm
  val Hol_mono_coreln : string -> monoset ->
                        (term * locn.locn list) -> thm * thm * thm

  val new_coinductive_definition : monoset -> string ->
                                   term * locn.locn list->
                                   thm * thm * thm

  val derive_nonschematic_coinductive_relations : term -> thm
  (*val derive_mono_strong_coinduction            : monoset -> thm * thm -> thm
  val derive_strong_coinduction                 : thm * thm -> thm *)

end
