signature goalFrag =
sig
include Abbrev

type goalstate
type frag_tactic = goalstate -> goalstate

val new_goal_list : goal list -> goalstate
val new_goal      : goal -> goalstate
val finish_list   : goalstate -> thm list
val finish        : goalstate -> thm
val top_goal      : goalstate -> goal
val top_goals     : goalstate -> goal list

val expand          : tactic -> frag_tactic
val expandf         : tactic -> frag_tactic
val expand_list     : list_tactic -> frag_tactic
val expand_listf    : list_tactic -> frag_tactic
val open_paren      : frag_tactic
val open_first      : frag_tactic
val open_head_goal  : frag_tactic
val open_last_goal  : frag_tactic
val open_nth_goal   : int -> frag_tactic
val open_null_ok    : frag_tactic
val open_repeat     : frag_tactic
val open_select_lt  : frag_tactic
val open_split_lt   : int -> frag_tactic
val open_tacs_to_lt : frag_tactic
val open_then1      : frag_tactic
val next_select_lt  : frag_tactic
val next_first      : frag_tactic
val next_split_lt   : frag_tactic
val next_tacs_to_lt : frag_tactic
val close_first     : frag_tactic
val close_paren     : frag_tactic
val close_repeat    : frag_tactic

val pp_goalstate    : goalstate Parse.pprinter

end
