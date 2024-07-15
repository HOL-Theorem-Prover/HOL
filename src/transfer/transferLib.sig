signature transferLib =
sig

  include Abbrev
  type config = {cleftp:bool,force_imp:bool,hints:string list}
  val GEN_TYVARIFY : thm -> thm

  structure ruledb : sig
    type t
    val empty_rdb : t
    val addrule : thm -> t -> t
    val addsafe : thm -> t -> t
    val addbad : term -> t -> t
    val add_domrng : thm -> t -> t
    val lookup_rule : bool -> t -> term -> thm list
    val safenet : t -> thm Net.net
    val badnet : t -> term Net.net
    val domrngs : t -> thm list
    val atomic_termnet : t -> (string * term) Net.net
    val check_for_atom : t -> term -> bool
  end

  val prove_relation_thm : ruledb.t -> bool -> term -> term -> thm
  val resolve_relhyps : string list -> bool -> ruledb.t -> thm -> thm seq.seq
  val resolveN : int -> string list -> bool -> ruledb.t -> term -> thm seq.seq
  val check_constraints : bool -> ruledb.t -> thm -> thm seq.seq
  val mkrelsyms_eq : bool -> thm -> thm
  val eliminate_domrng : bool -> ruledb.t -> thm -> thm

  val build_skeleton : ruledb.t -> term -> term
  val transfer_skeleton : ruledb.t -> config -> term -> thm
  val transfer_phase1   : config -> ruledb.t -> term -> thm seq.seq
  val base_transfer     : config -> ruledb.t -> term -> thm seq.seq
  val transfer_tm : int -> config -> ruledb.t -> term -> thm
  val transfer_thm : int -> config -> ruledb.t -> thm -> thm

  val global_ruledb : unit -> ruledb.t
  val default_depth : int Sref.t

  val add_rule : string -> unit
  val add_safe : string -> unit
  val add_simp : string -> unit
  val add_atomic_term : string * term -> unit
  val temp_add_rule : thm -> unit
  val temp_add_safe : thm -> unit
  val temp_add_simp : thm -> unit
  val temp_add_atomic_term : string * term -> unit
  val atomic_terms : unit -> (string * term) list

  val xfer_back_tac : string list -> tactic
  val xfer_fwd_tac : string list -> tactic

end
