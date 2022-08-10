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

  val resolve_relhyps : bool -> ruledb.t -> thm -> thm seq.seq
  val resolveN : int -> bool -> ruledb.t -> term -> thm seq.seq
  val check_constraints : bool -> ruledb.t -> thm -> thm seq.seq

  val transfer_skeleton : bool -> term -> thm
  val transfer_phase1   : bool -> ruledb.t -> term -> thm seq.seq
  val base_transfer     : bool -> ruledb.t -> term -> thm seq.seq
  val transfer_tm : int -> bool -> ruledb.t -> term -> thm
  val transfer_thm : int -> bool -> ruledb.t -> thm -> thm

  val global_ruledb : unit -> ruledb.t
  val default_depth : int Sref.t

  val add_rule : string -> unit
  val add_safe : string -> unit
  val add_simp : string -> unit
  val temp_add_rule : thm -> unit
  val temp_add_safe : thm -> unit
  val temp_add_simp : thm -> unit

  val xfer_back_tac : tactic


end
