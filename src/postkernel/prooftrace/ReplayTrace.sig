signature ReplayTrace =
sig
  (* Replay a .pft file, returning (name, thm) list of exports. *)
  val replay_file : string -> (string * Thm.thm) list

  (* Find all *Theory.pft files under a directory.
     Returns (theory_name, path) pairs. *)
  val find_traces : string -> (string * string) list

  (* Utility functions used by MergeTrace *)
  val tokenize : string -> string list
  val unescape : string -> string
end
