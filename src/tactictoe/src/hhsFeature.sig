signature hhsFeature =
sig

  include Abbrev
  val fea_of_goal : goal -> int list
  val fea_of_gl   : goal list -> int list
  
end
