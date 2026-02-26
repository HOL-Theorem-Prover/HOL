signature ReplayTrace =
sig
  type replay_maps = {
    named : (string * string, Thm.thm) Redblackmap.dict,
    anon  : (string * int, Thm.thm) Redblackmap.dict
  }

  (* Replay a .pft file, returning exports and replay maps.
     replay_maps are built from F/G provenance lines (empty if none). *)
  val replay_file : string ->
    { exports : (string * Thm.thm) list,
      replay_maps : replay_maps }

  (* Find all *Theory.pft files under a directory.
     Returns (theory_name, path) pairs. *)
  val find_traces : string -> (string * string) list

  (* Utility functions used by MergeTrace *)
  val tokenize : string -> string list
  val unescape : string -> string
end
