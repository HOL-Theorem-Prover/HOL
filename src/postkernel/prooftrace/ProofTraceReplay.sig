signature ProofTraceReplay = sig
  val print_statistics: bool ref
  val quiet: bool ref
  val debug: bool ref
  exception NeedsAncestor of string
  val replay: string -> unit  (* takes a path to a .tr.gz or .tr file *)
  val replay_sequence: string list -> unit  (* takes thynames, looks in cwd *)
  val skip_standard_axiom: unit -> string
  val replayed_thms: string -> (string, Thm.thm) Redblackmap.dict * Thm.thm list
end
