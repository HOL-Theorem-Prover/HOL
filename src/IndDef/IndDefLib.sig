signature IndDefLib =
sig
  include Abbrev
  type monoset = InductiveDefinition.monoset

  val Hol_reln      : term quotation -> thm * thm * thm
  val prim_Hol_reln : monoset -> term quotation -> thm * thm * thm

end
