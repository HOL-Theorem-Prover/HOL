signature ReplayTrace =
sig
  val replay_debug : bool ref
  val first_fail : string option ref

  (* Replay a .pftrace[.gz|.zst] file, returning export name→thm map.
     Raises Fail on verification errors. *)
  val replay_file : string -> (string * Thm.thm) list

  (* Replay with ancestor context. ORACLE DISK_THM entries are resolved
     against ancestor exports keyed by (theory, name) instead of creating
     oracle thms. Returns exports as (name, thm) list. *)
  val replay_file_ctx :
    string -> (string * string, Thm.thm) Redblackmap.dict
    -> (string * Thm.thm) list

  (* Replay and verify against actual theory theorems.
     Returns (n_ok, failures) where failures is list of
     {name, reason} records. *)
  val verify_file : string -> int * {name: string, reason: string} list

  (* Verify a single .pftrace[.gz|.zst] file, printing progress. *)
  val verify_verbose : string -> bool

  (* Find all *Theory.pftrace[.gz|.zst] files under a directory.
     Deduplicates by theory name, preferring .zst > .gz > .pftrace. *)
  val find_traces : string -> (string * string) list  (* (theory, path) *)

  (* Verify all .pftrace[.gz|.zst] files under a directory. *)
  val verify_all : string -> {ok: int, fail: int, errors: string list}

  (* Verify a complete trace chain: replay root_theory and all its
     ancestors from .pftrace[.gz|.zst] files found under holdir.
     Returns (n_theories_ok, n_theories_fail, errors). *)
  val verify_chain :
    string -> string
    -> {ok: int, fail: int, errors: string list}

  (* Parse a trace file (decompress + read + tokenize), returning
     the number of lines in each section. For benchmarking parse I/O. *)
  val parse_trace_stats :
    string -> {n_types: int, n_terms: int, n_steps: int, n_exports: int}

  (* Header type for parsed traces *)
  datatype header = Header of {
    version: int,
    theory: string,
    n_types: int,
    n_terms: int,
    n_steps: int
  }

  (* Utility functions (also used by MergeTrace) *)
  val tokenize : string -> string list
  val unescape : string -> string
  val read_trace_file : string -> {
    header : header,
    type_lines : string list,
    term_lines : string list,
    step_lines : string list,
    export_lines : string list
  }
  val parse_exports : string list -> (string * int) list

  (* Lazy type/term construction (exposed for debugging/testing) *)
  datatype ty_desc = TyVar of string | TyOp of string * string * int list
  datatype tm_desc = TmVar of string * int
                   | TmConst of string * string * int
                   | TmApp of int * int
                   | TmLam of int * int
  val parse_type_descs : int -> string list -> ty_desc Array.array
  val parse_term_descs : int -> string list -> tm_desc Array.array
  val make_lazy_types : ty_desc Array.array -> (int -> Type.hol_type)
  val make_lazy_terms : tm_desc Array.array -> (int -> Type.hol_type) ->
                        (int -> Term.term)
end
