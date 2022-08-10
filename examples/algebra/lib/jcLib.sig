signature jcLib =
sig

  include Abbrev
  val stripDup : thm list -> tactic

end
