signature Manager =
sig
 include Abbrev

  datatype proof
       = GOALSTACK of goalStack.gstk History.history
       | GOALTREE of goalTree.gtree History.history

  datatype proofs = PRFS of proof list
  exception NO_PROOFS

  (* Starting a proof *)
  val new_goalstack  : goal -> (thm->thm) -> proof
  val new_goaltree   : goal -> proof
  val set_goal       : goal -> proof
  val add            : proof -> proofs -> proofs

  (* Undo *)
  val backup         : proof -> proof
  val set_backup     : int -> proof -> proof
  val restore        : proof -> proof
  val save           : proof -> proof
  val forget_history : proof -> proof
  val restart        : proof -> proof
  val drop           : proofs -> proofs

  (* Applying a tactic to a goal *)
  val expand         : tactic -> proof -> proof
  val expandf        : tactic -> proof -> proof
  val expandv        : string * tactic -> proof -> proof

  (* Seeing what the state of the proof manager is *)
  val top_thm        : proof -> thm
  val initial_goal   : proof -> goal
  val finalizer      : proof -> (thm -> thm)
  val top_goal       : proof -> goal
  val top_goals      : proof -> goal list
  val current_proof  : proofs -> proof

  (* Switch focus to a different subgoal (or proof attempt) *)
  val rotate         : int -> proof -> proof
  val rotate_proofs  : int -> proofs -> proofs

  (* Operations on proof attempts *)
  val hd_opr         : (proof -> proof) -> proofs -> proofs
  val hd_proj        : (proof -> 'a) -> proofs -> 'a

  val initial_proofs : unit -> proofs
  val set_goal_pp    : (ppstream->goal->unit) -> (ppstream->goal->unit)
  val std_goal_pp    : ppstream -> goal -> unit

  val pp_proof       : ppstream -> proof -> unit
  val pp_proofs      : ppstream -> proofs -> unit

end
