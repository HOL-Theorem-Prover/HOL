signature hhsSearch =
sig

  include Abbrev

  val hhs_noscore       : bool ref
  val hhs_search_time   : Time.time ref
  val hhs_tactic_time   : real ref
  val hhs_metis_time    : real ref
  val hhs_depthpen_flag : bool ref
  val hhs_depthpen      : real ref
  val hhs_widthpen_flag : bool ref
  val hhs_widthpen      : real ref
  
  val hhs_cache_flag    : bool ref
  val hhs_metis_flag    : bool ref
  val hhs_debug_flag    : bool ref

  val imperative_search   : 
    (goal -> string list) ->
    (goal -> (string * real) list) ->
    int ->
    (string, real) Redblackmap.dict ->
    (string, tactic) Redblackmap.dict ->
    goal -> unit

end
