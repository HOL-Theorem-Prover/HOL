signature tttSearch =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn
  type aty = tttToken.aty
  type token = tttToken.token

  datatype status = Proved | Saturated | Undecided
  datatype searchstatus = SearchProved | SearchSaturated | SearchTimeout
  datatype proofstatus = Proof of string | ProofSaturated | ProofTimeout

  datatype gtoken = 
    Token of token | 
    Goal of (goal * (goal list, unit) Redblackmap.dict)
  type searchrecord =
    {nvis : real, nsum : real, ncoeff : real, nstatus : status, 
     parentd : (goal, unit) Redblackmap.dict}
  type stacrecord =
    {gtoken : gtoken, atyl : aty list,
     svis : real, ssum : real, scoeff : real, spol : real, sstatus : status}

  datatype searchtree = SearchNode of searchrecord * stactree vector
  and stactree = 
     StacLeaf of stacrecord * searchtree option
   | StacNode of stacrecord * (stactree vector * token list) option

  val get_stacrecord : stactree -> stacrecord
  val dest_goal : gtoken -> goal

  val nocut_flag : bool ref
  val conttop_flag : bool ref  
  val contmid_flag : bool ref
  val softmax_flag : bool ref
  val looplimit : int option ref
  
  val eval_goal : tnn -> goal -> real

  type searchobj =
    {predtac : goal -> token list,
     predarg : string -> aty -> goal -> token list,
     atyd : (string, aty list) Redblackmap.dict,
     parsetoken : tttToken.parsetoken,
     vnno: tnn option, pnno: tnn option, anno: tnn option}

  val search : searchobj -> goal -> proofstatus * searchtree

end
