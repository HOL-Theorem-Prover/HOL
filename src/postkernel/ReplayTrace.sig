signature ReplayTrace =
sig
  val replay_debug : bool ref
  val first_fail : string option ref

  (* Optional compute verifier: given an input term, return |- input = result.
     When set, COMPUTE steps are verified by evaluating the input term and
     checking the result matches the recorded conclusion. Unverified COMPUTE
     steps get oracle tag "REPLAY_COMPUTE". Set to e.g. EVAL for full
     verification. *)
  val compute_verifier : (Term.term -> Thm.thm) option ref
  (* Replay a .pftrace or .pftrace.gz file, returning export name→thm map.
     Raises Fail on verification errors. *)
  val replay_file : string -> (string * Thm.thm) list

  (* Replay with ancestor context. TRUST entries are resolved against
     ancestor_thms (keyed by conclusion, checked by hyps) instead of
     oracle thms. Returns exports as (name, thm) list. *)
  val replay_file_ctx :
    string -> (Term.term, Thm.thm list) Redblackmap.dict
    -> (string * Thm.thm) list

  (* Replay and verify against actual theory theorems.
     Returns (n_ok, failures) where failures is list of
     {name, reason} records. *)
  val verify_file : string -> int * {name: string, reason: string} list

  (* Verify a single .pftrace[.gz] file, printing progress. *)
  val verify_verbose : string -> bool

  (* Find all .pftrace[.gz] files under a directory. *)
  val find_traces : string -> (string * string) list  (* (theory, path) *)

  (* Verify all .pftrace[.gz] files under a directory. *)
  val verify_all : string -> {ok: int, fail: int, errors: string list}

  (* Verify a complete trace chain: replay root_theory and all its
     ancestors from .pftrace.gz files found under holdir.
     Returns (n_theories_ok, n_theories_fail, errors). *)
  val verify_chain :
    string -> string
    -> {ok: int, fail: int, errors: string list}
end
