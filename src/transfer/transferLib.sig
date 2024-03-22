signature transferLib =
sig

  include Abbrev
  val GEN_TYVARIFY : thm -> thm

  structure ruledb : sig
    type t
    val empty_rdb : t
    val addrule : thm -> t -> t
    val addsafe : thm -> t -> t
    val addbad : term -> t -> t
    val add_domrng : thm -> t -> t
    val lookup_rule : bool -> t -> term -> thm list
  end

  val prove_relation_thm : bool -> term -> term -> thm
  val resolve_relhyps : string list -> bool -> ruledb.t -> thm -> thm seq.seq
  val resolveN : int -> string list -> bool -> ruledb.t -> term -> thm seq.seq
  val check_constraints : bool -> ruledb.t -> thm -> thm seq.seq
  val mkrelsyms_eq : bool -> thm -> thm
  val eliminate_domrng : bool -> ruledb.t -> thm -> thm

  val build_skeleton : term -> term
  val transfer_skeleton : bool -> term -> thm
  val transfer_phase1   : string list -> bool -> ruledb.t -> term -> thm seq.seq
  val base_transfer     : string list -> bool -> ruledb.t -> term -> thm seq.seq
  val transfer_tm : int -> string list -> bool -> ruledb.t -> term -> thm
  val transfer_thm : int -> string list -> bool -> ruledb.t -> thm -> thm

  val global_ruledb : unit -> ruledb.t
  val default_depth : int Sref.t

  val add_rule : string -> unit
  val add_safe : string -> unit
  val add_simp : string -> unit
  val temp_add_rule : thm -> unit
  val temp_add_safe : thm -> unit
  val temp_add_simp : thm -> unit

  val xfer_back_tac : string list -> tactic
  val xfer_fwd_tac : string list -> tactic

end
