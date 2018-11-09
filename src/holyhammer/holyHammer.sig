signature holyHammer =
sig

  include Abbrev
  datatype prover = Eprover | Z3 | Vampire

  (* main functions *)
  val holyhammer  : term -> thm
  val hh          : tactic
  val hh_fork     : goal -> Thread.thread
  val set_timeout : int -> unit
  
  (* caches  *)
    (* remembers how goals were proven *)
  val clean_goaltac_cache : int 
    (* remembers features of goals (shared with tactictoe) *)
  val clean_goalfea_cache : unit -> unit
  
end
