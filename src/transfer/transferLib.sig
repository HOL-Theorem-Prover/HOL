signature transferLib =
sig

  include Abbrev

  structure ruledb : sig
    type t
    val empty_rdb : t
    val addrule : thm -> t -> t
    val addsafe : thm -> t -> t
    val addbad : term -> t -> t
    val add_domrng : thm -> t -> t
    val lookup_rule : bool -> t -> term -> thm list
  end

  val transfer_tm : int -> bool -> ruledb.t -> term -> thm
  val transfer_thm : int -> bool -> ruledb.t -> thm -> thm

  val global_ruledb : unit -> ruledb.t
  val default_depth : int Sref.t

  val add_rule : string -> unit
  val add_safe : string -> unit
  val temp_add_rule : thm -> unit
  val temp_add_safe : thm -> unit

  val xfer_back_tac : tactic


end
