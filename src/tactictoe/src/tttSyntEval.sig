signature tttSyntEval =
sig

  include Abbrev
  
  val time_mprove: 
    (thm list -> tactic) ->
    real -> 
    term list -> term -> 
    (term * real) option
  
  val expprovel:  
    (term, term list option) Redblackmap.dict ->
    (thm list -> tactic) ->
    term list -> term list -> (term, term list option) Redblackmap.dict

  val calc_reward: 
    (term * term list) list ->
    (term, int) Redblackmap.dict


end
