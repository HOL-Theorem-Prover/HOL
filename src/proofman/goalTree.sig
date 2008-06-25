signature goalTree =
sig

  include Abbrev

  datatype gtree 
     = vGoal of goal
     | vAtom of string * tactic
     | vThen of gtree * gtree
     | vThenl  of gtree * gtree list

  val new_gtree  : goal -> gtree
  val expand     : string * tactic -> gtree -> gtree
  val first_goal : gtree -> goal
  val expand_opt : string * tactic -> gtree -> gtree option
  val first_goal_opt  : gtree -> goal option
  val all_goals  : gtree -> goal list
  val tactic_of  : gtree -> tactic
  val pp_gtree   : ppstream -> gtree -> unit

end
