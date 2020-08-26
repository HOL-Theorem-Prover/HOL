signature tttBigSteps =
sig

  include Abbrev

  type ex = (term * real) list

  val run_bigsteps : tttSearch.searchobj -> goal -> bool * (ex * ex * ex)

end
