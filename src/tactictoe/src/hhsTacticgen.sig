signature hhsTacticgen =
sig

include Abbrev
  
  type lbl_t = (string * real * goal * goal list)
  
  val hhs_metis_flag  : bool ref
  val hhs_mutate_flag : bool ref
  
  val add_metis : 
    (string, tactic) Redblackmap.dict ref ->
    (goal -> string list) ref -> 
    goal * (lbl_t * real) list -> 
    goal * (lbl_t * real) list

  val add_mutate : 
    (string, tactic) Redblackmap.dict ref -> 
    goal * (lbl_t * real) list -> 
    goal * (lbl_t * real) list

end
