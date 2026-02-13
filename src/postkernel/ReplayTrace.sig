signature ReplayTrace =
sig
  val replay_debug : bool ref
  val first_fail : string option ref
  (* Replay a .pftrace file, returning a map from export name to thm.
     Raises Fail on verification errors. *)
  val replay_file : string -> (string * Thm.thm) list

  (* Replay and verify against actual theory theorems.
     Returns (n_ok, failures) where failures is list of
     {name, reason} records. *)
  val verify_file : string -> int * {name: string, reason: string} list

  (* Verify a single .pftrace file, printing progress. *)
  val verify_verbose : string -> bool

  (* Find all .pftrace files under a directory. *)
  val find_traces : string -> (string * string) list  (* (theory, path) *)

  (* Verify all .pftrace files under a directory. Returns (ok, fail) counts. *)
  val verify_all : string -> {ok: int, fail: int, errors: string list}
end
