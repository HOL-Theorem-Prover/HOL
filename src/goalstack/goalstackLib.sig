signature goalstackLib =
sig
    include Abbrev
    type proofs    = GoalstackPure.proofs
    type goalstack = GoalstackPure.goalstack

    val chatting : bool ref 

    (* Starting a proof *)

    val g             : term quotation -> proofs
    val set_goal      : goal -> proofs
    val add           : goalstack -> proofs

    (* Undo *)

    val b             : unit -> goalstack
    val drop          : unit -> proofs
    val dropn         : int -> proofs
    val restart       : unit -> goalstack
    val backup        : unit -> goalstack
    val set_backup    : int -> unit

    (* Applying a tactic to the current goal *)

    val e             : tactic -> goalstack
    val expand        : tactic -> goalstack
    val expandf       : tactic -> goalstack

    (* Seeing what the state of the proof manager is *)

    val p             : unit -> goalstack
    val initial_goal  : unit -> goal
    val top_thm       : unit -> thm
    val top_goal      : unit -> goal
    val top_goals     : unit -> goal list
    val status        : unit -> proofs

    (* Switch focus to a different subgoal (or proof attempt) *)

    val r             : int -> goalstack
    val R             : int -> proofs
    val rotate        : int -> goalstack
    val rotate_proofs : int -> proofs

    (* Switch to a different prettyprinter for all goals *)

    val set_goal_pp   : (ppstream->goal->unit) -> (ppstream->goal->unit)

    (* Standard system prettyprinter for goals *)

    val std_goal_pp   : ppstream -> goal -> unit

    (* Prettyprinters for the state of the proof manager *)

    val pp_goalstack  : ppstream -> goalstack -> unit
    val pp_proofs     : ppstream -> proofs -> unit
end
