signature GoalstackPure =
  sig
  type goal = Abbrev.goal
  type thm = Thm.thm
  datatype goalstack = GOALSTACK of Bwd.gstk History.history;
  datatype proofs = PRFS of goalstack list;
  exception NO_PROOFS

      (* Starting a proof *)
      val set_goal : goal -> goalstack
      val add : goalstack -> proofs -> proofs

      (* Undo *)
      val backup : goalstack -> goalstack
      val set_backup : int -> goalstack -> goalstack
      val restart   : goalstack -> goalstack
      val drop : proofs -> proofs

      (* Applying a tactic to a goal *)
      val expand  : Abbrev.tactic -> goalstack -> goalstack
      val expandf : Abbrev.tactic -> goalstack -> goalstack

      (* Seeing what the state of the proof manager is *)
      val current_goalstack : proofs -> goalstack
      val top_thm : goalstack -> thm
      val initial_goal : goalstack -> goal
      val top_goal  : goalstack -> goal
      val top_goals : goalstack -> goal list

      (* Switch focus to a different subgoal (or proof attempt) *)
      val rotate : int -> goalstack -> goalstack
      val rotate_proofs : int -> proofs -> proofs

      (* Operations on proof attempts *)
      val hd_opr : (goalstack -> goalstack) -> proofs -> proofs
      val hd_proj: (goalstack -> 'a) -> proofs -> 'a

      val initial_proofs : unit -> proofs
      val set_goal_pp :(Portable.ppstream -> goal -> unit)
                       -> (Portable.ppstream -> goal -> unit)
      val std_goal_pp : (Portable.ppstream -> goal -> unit)

      val pp_goalstack : Portable.ppstream -> goalstack -> unit
      val pp_proofs : Portable.ppstream -> proofs -> unit

    end
