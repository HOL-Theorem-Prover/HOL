signature hhConfig =
sig
  (* The provers HolyHammer can call.  prover_name is the spelling in
     option values, configuration keys and installation directories. *)
  datatype prover = Eprover | Vampire | Zipperposition | Z3
  val all_provers : prover list
  val prover_name : prover -> string
  val prover_of_name : string -> prover option
  val prover_compare : prover * prover -> order

  type hh_options =
    {timeout : int,
     provers : prover list,
     slices : int,
     cores : int,
     export_workers : int,
     filter : string,
     max_facts : int option,
     format : string,
     type_enc : string,
     lam_trans : string,
     mono_iters : int,
     mono_instances : int option,
     minimize : bool,
     preplay_timeout : real,
     minimize_timeout : real,
     preplay_drop_one : bool,
     cache : bool,
     cache_dir : string,
     cache_max_entries : int,
     debug_dir : string option,
     verbose : bool}

  (* Small filesystem and string helpers, shared with hhProver and hhEval. *)
  val is_dir : string -> bool
  val ensure_dir : string -> unit
  val remove_tree : string -> unit
  (* write_atomically {open_out, close_out} path f opens a fresh sibling
     temporary of path, runs f on it, closes it and renames it over path
     (replacing an existing file whole).  On any error or interrupt the
     stream is closed, the temporary removed and the exception re-raised. *)
  val write_atomically :
    {open_out : string -> 'a, close_out : 'a -> unit} ->
    string -> ('a -> 'b) -> 'b
  (* stage_write is write_atomically without the rename: it returns the
     closed temporary, which the caller must commit or remove_quietly. *)
  val stage_write :
    {open_out : string -> 'a, close_out : 'a -> unit} ->
    string -> ('a -> 'b) -> string * 'b
  (* stage_to io temporary write is stage_write into a temporary chosen by
     the caller (see temp_path), so that the caller can remove it whatever
     happens to the writer, an interrupt included; the stream is opened and
     closed with interrupts deferred. *)
  val temp_path : string -> string
  val stage_to :
    {open_out : string -> 'a, close_out : 'a -> unit} ->
    string -> ('a -> 'b) -> 'b
  val commit : {temporary : string, final : string} -> unit
  val remove_quietly : string -> unit
  val directory_names : string -> string list
  val trim : string -> string
  val trim_left : string -> string
  val valid_filter : string -> bool

  val state_dir : unit -> string

  (* The built-in default of the export_workers option. *)
  val default_export_workers : int

  (* The built-in default of the preplay_timeout option, in CPU seconds
     of the replay's thread (smlTimeout.thread_timeout's clock). *)
  val default_preplay_timeout : real

  (* The built-in default of the minimize_timeout option, in CPU seconds
     of the attempt's thread (smlTimeout.thread_timeout's clock). *)
  val default_minimize_timeout : real

  val get : string -> string option
  val get_int : string -> int option
  val get_bool : string -> bool option
  val get_path : string -> string option
  val dump : unit -> (string * string) list

  val hh_set : string * string -> unit
  val hh_unset : string -> unit
  val hh_get : string -> string
  val hh_params : unit -> (string * string * string) list
  val print_params : unit -> unit
  val snapshot : unit -> hh_options
  val snapshot_with : (string * string) list -> hh_options

  val platform : unit -> string
  (* find_exec prover env_var names: the executable the config file's
     prover.<prover>.executable names, else env_var's, when either is set
     and not empty (NONE if it is no executable file; a name without a
     slash is looked up on PATH); otherwise the first of names on PATH,
     else the newest <prover>-<version>/<platform>/ holding one of names
     in the state directory's provers, then in ~/.hol4/hammer/provers. *)
  val find_exec : string -> string -> string list -> string option
end
