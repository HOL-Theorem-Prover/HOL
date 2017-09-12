signature hhsPrerecord = 
sig

include Abbrev

  val hhs_prerecord : string -> string -> tactic
  val hhs_record : (tactic * string) -> tactic
  
  val n_parse_glob : int ref
  val n_replay_glob : int ref
  val n_tactic_parse_glob : int ref
  val n_tactic_replay_glob : int ref

  val reset_profiling : unit -> unit
  val post_record : unit -> unit
  
  val mk_summary: string -> unit
  
end
