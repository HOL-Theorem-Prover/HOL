signature IndDefLib =
sig
  include Abbrev

  val new_inductive_definition : term quotation -> thm * thm * thm

end
