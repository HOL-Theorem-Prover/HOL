signature RL_Goal_manager = sig

  type goal_term
  datatype goal_state = GOAL of goal_term
                      | ERROR of string
                      | SUCCESS of HolKernel.thm

  val initial_goal_state : Abbrev.goal -> goal_state
  val rotate_goal_state : goal_state -> goal_state option
  val apply_tactic : bossLib.tactic -> goal_state -> goal_state

  type observed_goal_state
  val get_observed_goal_state : goal_state -> observed_goal_state
  val observed_goal_state_to_string : observed_goal_state -> string
  val terms_of_current_goal : goal_state -> Abbrev.term list
end
