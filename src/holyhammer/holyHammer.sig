signature holyHammer =
sig

  include Abbrev
  datatype prover = datatype hhConfig.prover

  (* set_timeout n is hhConfig.hh_set ("timeout", Int.toString n). *)
  val set_timeout : int -> unit
  val holyhammer  : term -> thm
  val hh          : tactic
  (* hh_fork goal runs hh's proof search on goal in a new thread, which
     prints the metis_tac call found or why the search failed. *)
  val hh_fork     : goal -> Thread.thread
  (* hh_pb dir provers premises: hh with the given provers and premises
     (names of the form "fooTheory.bar"), its problems below dir. *)
  val hh_pb  : string -> prover list -> string list -> goal -> tactic

  (* For developers: main_hh dir thmdata searches as hh_pb does, with the
     configured provers and premise selection from thmdata, and prints no
     tactic.  main_hh_lemmas gives the lemmas of the verified proof, NONE
     if the search fails. *)
  val main_hh : string -> mlThmData.thmdata -> goal -> tactic
  val main_hh_lemmas :
    string -> mlThmData.thmdata -> goal -> string list option

end
