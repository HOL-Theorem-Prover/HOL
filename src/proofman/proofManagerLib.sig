signature proofManagerLib =
sig
    include Abbrev
    type proof = Manager.proof
    type proofs = Manager.proofs

    val chatting : bool ref

    (* Starting a proof *)

    val g             : term quotation -> proofs
    val gt            : term quotation -> proofs
    val set_goal      : goal -> proofs
    val set_goaltree  : goal -> proofs
    val new_goalstack : goal -> (thm -> thm) -> proofs
    val new_goaltree  : goal -> proofs
    val add           : proof -> proofs

    (* Undo *)

    val b             : unit -> proof
    val drop          : unit -> proofs
    val dropn         : int -> proofs
    val drop_all      : unit -> proofs
    val restart       : unit -> proof
    val backup        : unit -> proof
    val restore       : unit -> proof
    val save          : unit -> proof
    val set_backup    : int -> unit
    val forget_history: unit -> unit

    (* Applying a tactic to the current goal *)

    val e             : tactic -> proof
    val elt           : list_tactic -> proof
    val eall          : tactic -> proof
    val eta           : tactic -> proof
    val enth          : tactic -> int -> proof
    val et            : string * tactic -> proof
    val expand        : tactic -> proof
    val expandf       : tactic -> proof
    val expand_list   : list_tactic -> proof
    val expand_listf  : list_tactic -> proof
    val expandv       : string * tactic -> proof

    (* Seeing what the state of the proof manager is *)

    val p             : unit -> proof
    val initial_goal  : unit -> goal
    val top_thm       : unit -> thm
    val top_goal      : unit -> goal
    val top_goals     : unit -> goal list
    val status        : unit -> proofs

    (* Switch focus to a different subgoal (or proof attempt) *)

    val r             : int -> proof
    val R             : int -> proofs
    val rotate        : int -> proof
    val flatn         : int -> proof
    val rotate_proofs : int -> proofs

    (* Switch to a different prettyprinter for all goals *)

    val set_goal_pp   : goal Parse.pprinter -> goal Parse.pprinter

    (* Standard system prettyprinter for goals *)

    val std_goal_pp   : goal Parse.pprinter

    (* Prettyprinters for the state of the proof manager *)

    val pp_proof      : proof Parse.pprinter
    val pp_proofs     : proofs Parse.pprinter
end
