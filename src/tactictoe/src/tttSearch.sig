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
    {nvis : real, nsum : real, nstatus : status,
     parentd : (goal, unit) Redblackmap.dict}
  type stacrecord =
    {gtoken : gtoken, atyl : aty list,
     svis : real, ssum : real, spol : real, sstatus : status}

  datatype searchtree = SearchNode of searchrecord * stactree vector
  and stactree =
     StacLeaf of stacrecord * searchtree option
   | StacNode of stacrecord * (stactree vector * token list) option

  val get_stacrecord : stactree -> stacrecord
  val dest_goal : gtoken -> goal

  (* global parameters *)
  val default_reward : real ref
  val nocut_flag : bool ref
  val conttop_flag : bool ref
  val contmid_flag : bool ref
  val looplimit : int option ref

  (* provability estimation *)
  val eval_goal : tnn -> goal -> real

  (* main function *)
  type searchobj =
    {predtac : goal -> token list,
     predarg : string -> aty -> goal -> token list,
     atyd : (string, aty list) Redblackmap.dict,
     parsetoken : tttToken.parsetoken,
     vnno: tnn option, pnno: tnn option, anno: tnn option}

  val search : searchobj -> goal -> proofstatus * searchtree

  (* suggested proof in case of failure *)
  val suggest_depth : int option ref
  val suggest_proof : searchtree -> string

  (* statistics *)
  datatype vistoken =
    VisGoal of goal | VisTac of string | VisArg of token
  datatype vistree =
    VisNode of vistoken * int * real * status * vistree list
  val vistreel_of_searchtree : searchtree -> vistree list
  val length_vistree : vistree -> int
  val print_vistree : vistree -> unit

end
