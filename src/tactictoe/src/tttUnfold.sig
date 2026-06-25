signature tttUnfold =
sig

  include Abbrev

  (* tools *)
  val find_script : string -> string
  val load_sigobj : unit -> unit
  val ttt_rewrite_thy : string -> unit

  (* recording tactic data *)
  val ttt_record_thy  : string -> unit
  val ttt_clean_record : unit -> unit
  val ttt_record : unit -> unit

  datatype record_scope =
      CurrentAncestry
    | Ancestry of string
    | Theories of string list

  type record_config =
    { scope        : record_scope,
      parallel     : int,
      force        : bool,
      dry_run      : bool,
      max_lock_age : Time.time }

  datatype record_option =
      Scope of record_scope
    | Parallel of int
    | Force of bool
    | DryRun of bool
    | MaxLockAge of Time.time

  datatype reason =
      TierA_direct
    | TierB_cascade of string
    | TierC_global
    | TierC_format
    | TierC_holstate
    | Missing_data
    | Missing_manifest_line
    | Tampered_data
    | Forced

  type manifest_entry =
    { thy : string, data_sha256 : string, src_sha256 : string,
      anc_version : int, recorded_at : int, failed : bool }

  type record_worker_param =
    { force : bool, max_lock_age_seconds : int,
      format_hash : string, global_hash : string, hol_hash : string,
      src_hashes : (string * string) list, recorded_stale : string list }

  val default_record_config : record_config
  val ttt_record_opts : record_option list -> unit
  val ttt_record_cfg : record_config -> unit
  val ttt_record_plan : record_scope ->
    {stale : (string * reason) list, up_to_date : string list,
     out_of_scope_ancestors : string list}
  val read_manifest : unit -> manifest_entry list option
  val manifest_format_version : int

  (* Internal support for external parallel workers. *)
  val record_parallel_dir : string ref
  val record_extspec : unit ->
    (record_worker_param,string,string) smlParallel.extspec

  (* creating savestates before each proof
     (requires some flags see usage in tttEval) *)
  val ttt_clean_savestate : unit -> unit
  val ttt_record_savestate : unit -> unit

end
