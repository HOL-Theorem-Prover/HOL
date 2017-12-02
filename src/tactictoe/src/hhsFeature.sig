signature hhsFeature =
sig

  include Abbrev
  val fea_of_term : term -> string list
  val fea_of_goal : goal -> int list
  
end
