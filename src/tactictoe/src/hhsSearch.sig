signature hhsSearch =
sig

  include Abbrev
  
  type lbl_t = (string * real * goal * goal list)
  type fea_t = string list
  type feav_t = (lbl_t * fea_t)
  
  datatype proof_status_t = 
    ProofError | ProofSaturated | ProofTimeOut | Proof of string
  
  val hhs_search_time    : Time.time ref
  val hhs_tactic_time    : real ref
  val hhs_metis_time     : real ref
  val hhs_cache_flag     : bool ref
  val hhs_minimize_flag  : bool ref
  val hhs_astar_flag     : bool ref
  val hhs_succrate_flag  : bool ref
  val hhs_timedepth_flag : bool ref
  val hhs_selflearn_flag : bool ref
  
  val succ_cthy_dict : (string,(int * int)) Redblackmap.dict ref
  val succ_glob_dict : (string,(int * int)) Redblackmap.dict ref
  
  val imperative_search   : 
    (goal -> string list) ->
    (goal -> (lbl_t * real) list) ->
    (string, tactic) Redblackmap.dict ->
    (goal, feav_t list) Redblackmap.dict ->
    goal -> proof_status_t

end
