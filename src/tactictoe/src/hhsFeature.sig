signature hhsFeature =
sig

  include Abbrev
  val hhs_hofea_flag : bool ref
  val hhs_notopfea_flag : bool ref
  val fea_of_goal : goal -> string list

end
