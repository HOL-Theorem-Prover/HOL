signature tttSearch =
sig

  include Abbrev

  type id = (int * int) list

  datatype stacstatus =
    StacProved |
    StacSaturated |
    StacUndecided of goal list |
    StacFail | StacLoop | StacPara |
    StacFresh
  datatype goalstatus = GoalProved | GoalSaturated | GoalUndecided
  datatype nodestatus = NodeProved | NodeSaturated | NodeUndecided
  datatype searchstatus = SearchProved | SearchSaturated | SearchTimeout
  datatype proofstatus =  Proof of string | ProofSaturated | ProofTimeout



  type stac_record =
    {stac : string, svis : real, ssum : real, stacstatus : stacstatus}
  type goal_record =
    {
    goal : goal, gvis : real, gsum  : real, goalstatus : goalstatus,
    stacv : stac_record vector,
    siblingd : (goal list, unit) Redblackmap.dict
    }
  type node =
    {
    nvis : real, nsum : real, nodestatus : nodestatus,
    goalv : goal_record vector,
    parentd : (goal, unit) Redblackmap.dict
    }
  type tree = ((int * int) list, node) Redblackmap.dict

  val search : (goal -> string list) * mlTreeNeuralNetwork.tnn option -> 
     goal -> proofstatus * tree

end
