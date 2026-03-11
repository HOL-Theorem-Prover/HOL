signature ProofTraceReplay = sig
  val print_statistics: bool ref
  val quiet: bool ref
  val debug: bool ref
  exception NeedsAncestor of string
  val replay: string -> unit
  val replay_sequence: string list -> unit
  val skip_standard_axiom: unit -> string
  val replayed_thms: string -> (string, Thm.thm) Redblackmap.dict * Thm.thm list
end
