signature IndDefLib =
sig
  include Abbrev

  val new_inductive_definition : term -> thm * thm * thm

end
