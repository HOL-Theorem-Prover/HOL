signature tttSearch =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn

  datatype status = Proved | Saturated | Undecided
  datatype searchstatus = SearchProved | SearchSaturated | SearchTimeout
  datatype proofstatus = Proof of string | ProofSaturated | ProofTimeout

  datatype gtoken = 
    Token of token | Goal of (goal * (goal list, unit) Redblackmap.dict)
  type searchrecord =
    {nvis : real, nsum : real, nstatus : status,
     parentd : (goal, unit) Redblackmap.dict}
  type stacrecord =
    {gtoken : gtoken, atyl : aty list,
     svis : real, ssum : real, spol : real, sstatus : status}

  datatype searchtree = SearchNode of searchrecord * stactree vector
  and stactree = 
     StacLeaf of stacrecord * searchtree option
   | StacNode of stacrecord * (stactree vector * stactree list) option


  val nocut_flag : bool ref
  val conttop_flag : bool ref  
  val contmid_flag ; bool ref

  val eval_goal : tnn -> goal -> real

  type searchobj =
    {predtac : goal -> tttToken.token list,
     predarg : string -> tttToken.aty -> goal -> tttToken.token list,
     parsetoken : tttToken.parsetoken,
     vnno: tnn option, pnno: tnn option, anno: tnn option}

  val search : searchobj -> goal -> proofstatus * tree

end
