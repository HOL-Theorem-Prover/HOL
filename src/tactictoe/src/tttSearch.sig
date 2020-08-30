signature tttSearch =
sig

  include Abbrev

  type tnn = mlTreeNeuralNetwork.tnn
  val predtac_time : real ref
  val reward_time : real ref
  val reorder_time : real ref

  datatype sstatus = StacProved | StacSaturated | StacUndecided | StacFresh
  datatype gstatus = GoalProved | GoalSaturated | GoalUndecided
  datatype nstatus = NodeProved | NodeSaturated | NodeUndecided
  datatype searchstatus = SearchProved | SearchSaturated | SearchTimeout
  datatype proofstatus =  Proof of string | ProofSaturated | ProofTimeout

  val string_of_sstatus : sstatus -> string

  type id = (int * int * int list) list
  val id_compare : id * id -> order
  type stac_record =
   {token : tttToken.token, atyl : tttToken.aty list,
    svis : real, ssum : real, sstatus : sstatus}
  type argtree = (int list, stac_record) Redblackmap.dict
  type goal_record =
   {goal : goal, gvis : real, gsum : real, gstatus : gstatus,
    stacv : argtree vector,
    siblingd : (goal list, unit) Redblackmap.dict}
  type node =
   {nvis : real, nsum : real, nstatus : nstatus,
    goalv : goal_record vector,
    parentd : (goal, unit) Redblackmap.dict}
  type tree = (id, node) Redblackmap.dict

  val backstatus_arg : sstatus list -> sstatus
  val backstatus_stacv : argtree vector -> gstatus
  val backstatus_goalv : goal_record vector -> nstatus

  type searchobj =
    {predtac : goal -> (string * tttToken.aty list) list,
     predarg : string -> tttToken.aty -> goal -> tttToken.token list,
     parsetoken : tttToken.parsetoken,
     vnno: tnn option, pnno: tnn option, anno: tnn option}

  val starttree_of_goal : searchobj -> goal -> tree
  val starttree_of_gstacarg : searchobj -> 
    goal * string * tttToken.token list -> tree

  val search_loop : searchobj -> int option -> tree -> searchstatus * tree
  val search : searchobj -> goal -> proofstatus * tree
  
end
