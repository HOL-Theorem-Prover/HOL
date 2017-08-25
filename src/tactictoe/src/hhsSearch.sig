signature hhsSearch =
sig

  include Abbrev
  
  type lbl_t = (string * real * goal * goal list)
  type fea_t = string list
  type feav_t = (lbl_t * fea_t)
  
  datatype proof_status_t = 
    ProofError | ProofSaturated | ProofTimeOut | Proof of string
  
  val hhs_cache_flag     : bool ref
  val hhs_astar_flag     : bool ref
  val hhs_timedepth_flag : bool ref
  val hhs_selflearn_flag : bool ref
  
  val imperative_search   : 
    (goal -> string list) ->
    (goal -> (lbl_t * real) list) ->
    (string, tactic) Redblackmap.dict ->
    (goal, feav_t list) Redblackmap.dict ->
    goal -> proof_status_t

end
