signature Bwd =
 sig
 type goal   = Abbrev.goal
 type tactic = Abbrev.tactic
 type gstk

      val expand : gstk -> tactic -> gstk
      val expandf : gstk -> tactic -> gstk
      val extract_thm : gstk -> Thm.thm
      val initial_goal : gstk -> goal
      val is_initial : gstk -> bool
      val new_goal : goal -> gstk
      val std_pp_goal : Portable.ppstream -> goal -> unit
      val pp_goal : Portable.ppstream -> goal -> unit
      val set_goal_pp : (Portable.ppstream -> goal -> unit)
                        -> (Portable.ppstream -> goal -> unit)
      val pp_gstk : Portable.ppstream -> gstk -> unit
      val rotate : gstk -> int -> gstk
      val top_goal : gstk -> goal
      val top_goals : gstk -> goal list
      val depth :gstk -> int
 end;
