signature hhProver =
sig
  datatype prover = datatype hhConfig.prover

  datatype szs =
      SzsTheorem
    | SzsCounterSat
    | SzsSatisfiable
    | SzsGaveUp
    | SzsTimeout
    | SzsResourceOut
    | SzsInappropriate
    | SzsUnknown of string
    | RunFailure of string

  type slice =
    {prover : prover, format : string, type_enc : string,
     lam_trans : string, nfacts : int, filter : string,
     extra_opts : string list, slice_size : int}

  type run_request =
    {timeout : int, format : string, problem : string, extra : string list,
     debug_dir : string option}

  type run_result =
    {szs : szs, used_axioms : string list option, time : real,
     version : string option, output_file : string}

  type running =
    {kill : unit -> unit,
     wait : unit -> run_result}

  (* name is the prover's spelling in configuration keys, installation
     directories and output files: prover_name for the built-in configs. *)
  type prover_config =
    {name : string,
     exec_names : string list,
     env_var : string,
     version_args : string list,
     parse_version : string -> string option,
     tested_versions : string list,
     supported_formats : string list,
     mk_command : string -> run_request -> string * string list,
     parse_output : string list -> szs * string list option,
     mono_instances : int,
     slices : unit -> slice list,
     legacy : bool}

  val same_slice : slice -> slice -> bool
  (* Wall-clock slack past a requested time limit: a prover process is
     killed this long after its own limit, and the scheduler extends its
     deadlines by the same amount. *)
  val grace_seconds : int
  (* The built-in slices in scheduling order; each built-in prover's
     slice table is its subsequence of this list. *)
  val portfolio : slice list

  (* The configs of all_provers, in that order. *)
  val all : unit -> prover_config list
  val config_of : prover -> prover_config
  val default_provers : unit -> prover list
  (* Test hook: with_override prover config f runs f with config in place
     of prover's. *)
  val with_override : prover -> prover_config -> (unit -> 'a) -> 'a

  (* Human-readable rendering, for progress output.  Not a wire format:
     szs_to_string/szs_of_string are the round-trippable encoding.
     status_of_word reads an SZS ontology word, so szs_name of every
     status other than SzsUnknown and RunFailure reads back. *)
  val szs_name : szs -> string
  val szs_to_string : szs -> string
  val szs_of_string : string -> szs
  val status_of_word : string -> szs
  val szs_of_line : string -> szs option
  val axioms_from_tstp : string list -> string list

  (* Executable discovery, version probing and a timed run of one problem. *)
  val find_exec : prover_config -> string option
  val probe : prover_config ->
    {path : string, version : string option, tested : bool} option
  (* Shared with the scheduler: lock discipline must have one definition. *)
  val with_mutex : Mutex.mutex -> (unit -> 'a) -> 'a
  val elapsed : Time.time -> real

  (* Test hook: counts every successful fork, including version probes. *)
  val spawn_count : unit -> int
  val reset_spawn_count : unit -> unit
  val run_async : prover_config -> run_request -> running
  val run : prover_config -> run_request -> run_result
end
