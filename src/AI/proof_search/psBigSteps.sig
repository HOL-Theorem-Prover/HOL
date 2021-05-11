signature psBigSteps =
sig

  include Abbrev

  type 'a rlex = ('a * real list) list
  val temp_flag : bool ref
  val run_bigsteps : (bool * ('a,'b) psMCTS.mctsobj) -> 'a -> bool * 'a rlex

end
