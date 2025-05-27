signature Manager =
sig
 include Abbrev

  datatype proof0
       = GOALSTACK of goalStack.gstk History.history
       | GOALTREE of goalTree.gtree History.history
       | GOALFRAG of goalFrag.goalstate History.history
  type tacmodifier = {tacm: tactic -> tactic,
                      ltacm : list_tactic -> list_tactic}

  datatype proof = PF of proof0 * tacmodifier

  datatype proofs = PRFS of proof list
  exception NO_PROOFS
  val id_tacm : tacmodifier

  (* Starting a proof *)
  val new_goalstack  : goal -> tacmodifier -> (thm->thm) -> proof
  val new_goaltree   : goal -> tacmodifier -> proof
  val new_goalfrag   : goal -> tacmodifier -> proof
  val set_goal       : goal -> tacmodifier -> proof
  val add            : proof -> proofs -> proofs

  (* Undo *)
  val backup         : proof -> proof
  val set_backup     : int -> proof -> proof
  val redo           : proof -> proof
  val restore        : proof -> proof
  val save           : proof -> proof
  val forget_history : proof -> proof
  val restart        : proof -> proof
  val drop           : proofs -> proofs

  (* Applying a tactic to a goal *)
  val expand         : tactic -> proof -> proof
  val expandf        : tactic -> proof -> proof
  val expand_list    : list_tactic -> proof -> proof
  val expand_listf   : list_tactic -> proof -> proof
  val expand_frag    : goalFrag.frag_tactic -> proof -> proof
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
  val flatn          : int -> proof -> proof
  val rotate_proofs  : int -> proofs -> proofs

  (* Operations on proof attempts *)
  val hd_opr         : (proof -> proof) -> proofs -> proofs
  val hd_proj        : (proof -> 'a) -> proofs -> 'a

  val initial_proofs : unit -> proofs
  val set_goal_pp    : goal Parse.pprinter -> goal Parse.pprinter
  val std_goal_pp    : goal Parse.pprinter

  val pp_proof       : proof Parse.pprinter
  val pp_proofs      : proofs Parse.pprinter

end
