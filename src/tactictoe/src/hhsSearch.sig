signature hhsSearch =
sig

  include Abbrev
  
  type lbl_t = (string * real * goal * goal list)
  type fea_t = int list
  type feav_t = (lbl_t * fea_t)
  
  datatype proof_status_t = 
    ProofError | ProofSaturated | ProofTimeOut | Proof of string
  
  val hhs_cache_flag     : bool ref
  val hhs_astar_flag     : bool ref
  val hhs_astar_radius   : int ref
  val hhs_timedepth_flag : bool ref
  val hhs_diag_flag      : bool ref
  val hhs_visited_flag   : bool ref
  val hhs_width_coeff    : real ref
  val hhs_selflearn_flag : bool ref
  
  val imperative_search   : 
    (goal -> string list) ->
    (goal -> (lbl_t * real) list) ->
    (string, tactic) Redblackmap.dict ->
    (goal, real option) Redblackmap.dict ->
    goal -> proof_status_t

end
