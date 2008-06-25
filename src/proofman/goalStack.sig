signature goalStack =
sig
   include Abbrev

   type gstk

   val chatting : bool ref

   val expand       : tactic -> gstk -> gstk
   val expandf      : tactic -> gstk -> gstk
   val extract_thm  : gstk -> thm
   val initial_goal : gstk -> goal
   val finalizer    : gstk -> thm -> thm
   val is_initial   : gstk -> bool
   val new_goal     : goal -> (thm -> thm) -> gstk
   val rotate       : gstk -> int -> gstk
   val top_goal     : gstk -> goal
   val top_goals    : gstk -> goal list
   val depth        : gstk -> int

   val std_pp_goal  : ppstream -> goal -> unit
   val pp_goal      : ppstream -> goal -> unit
   val pp_gstk      : ppstream -> gstk -> unit
   val set_goal_pp  : (ppstream -> goal -> unit) -> (ppstream -> goal -> unit)

 end
