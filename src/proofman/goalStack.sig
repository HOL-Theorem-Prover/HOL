signature goalStack =
sig
   include Abbrev

   type gstk

   val chatting : bool ref

   val expand       : tactic -> gstk -> gstk
   val expandf      : tactic -> gstk -> gstk
   val expand_list  : list_tactic -> gstk -> gstk
   val expand_listf : list_tactic -> gstk -> gstk
   val print_tac    : string -> tactic
   val extract_thm  : gstk -> thm
   val initial_goal : gstk -> goal
   val finalizer    : gstk -> thm -> thm
   val is_initial   : gstk -> bool
   val new_goal     : goal -> (thm -> thm) -> gstk
   val rotate       : gstk -> int -> gstk
   val flatn        : gstk -> int -> gstk
   val top_goal     : gstk -> goal
   val top_goals    : gstk -> goal list
   val depth        : gstk -> int
   val goal_size    : goal -> int
   val gstk_size    : gstk -> int

   val pr_goal      : goal -> unit term_pp_types.printer
   val std_pp_goal  : goal Parse.pprinter
   val pp_goal      : goal Parse.pprinter
   val pp_gstk      : gstk Parse.pprinter
   val set_goal_pp  : goal Parse.pprinter -> goal Parse.pprinter

end
