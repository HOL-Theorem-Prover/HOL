signature ReplayTrace =
sig
  (* Replay a .pft file, returning (name, thm) list of exports. *)
  val replay_file : string -> (string * Thm.thm) list

  (* Find all *Theory.pft[.zst|.gz] files under a directory.
     Returns (theory_name, path) pairs, preferring .zst > .gz > .pft. *)
  val find_traces : string -> (string * string) list

  (* Utility functions used by MergeTrace *)
  val tokenize : string -> string list
  val unescape : string -> string
  val shell_quote : string -> string
  val open_trace : string ->
    TextIO.instream * (TextIO.instream, TextIO.outstream) Unix.proc option
  val close_trace :
    TextIO.instream * (TextIO.instream, TextIO.outstream) Unix.proc option
    -> unit
end
