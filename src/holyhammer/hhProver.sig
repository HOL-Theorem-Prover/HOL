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
    {timeout : int, problem : string, extra : string list,
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
     slices : slice list,
     legacy : bool}

  val same_slice : slice -> slice -> bool
  (* mk_slice prover (format, type_enc, lam_trans) filter nfacts: the
     slice without extra options, of size 1. *)
  val mk_slice : prover -> string * string * string -> string -> int -> slice
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
  (* Why find_exec finds no executable, as advice to the user. *)
  val missing_prover : prover_config -> string
  (* The executable and its version, probed once per prover name; an
     untested or unknown version is reported on stderr. *)
  val probe : prover_config ->
    {path : string, version : string option, tested : bool} option
  (* with_mutex mutex f runs f holding mutex; the scheduler's locks use it
     too. *)
  val with_mutex : Mutex.mutex -> (unit -> 'a) -> 'a
  (* Runs a program to its end, killing it after the limit in seconds,
     through the spawn the provers use, and returns what it wrote to stdout;
     its stderr is the caller's.  Other modules start their programs this
     way too, so that no child inherits a prover's pipe. *)
  val read_stdout : string -> string list -> real ->
    {output : string, exec_failed : bool, killed : bool,
     status : Posix.Process.exit_status, time : real}
  val elapsed : Time.time -> real

  (* Test hook: counts every successful spawn, version probes included. *)
  val spawn_count : unit -> int
  val reset_spawn_count : unit -> unit
  (* run_async config request starts the prover on the request, killing
     it grace_seconds past its timeout; wait gives the result, saving the
     output in debug_dir if set. *)
  val run_async : prover_config -> run_request -> running
  val run : prover_config -> run_request -> run_result
end
