signature buildutils =
sig

  val help_mesg : string
  val normPath : string -> string
  val fullPath : string list -> string
  val quote : string -> string
  val die : string -> 'a
  val warn : string -> unit

  val SIGOBJ : string
  val EXECUTABLE : string
  val SYSTEML : string list -> bool
  val HOLMAKE : string

  val process_cline :
      (string -> string) ->
      {cmdline : string list, build_theory_graph : bool,
       do_selftests : int, SRCDIRS : (string * int) list}

  val map_dir : (string * string -> unit) -> string -> unit
                (* f gets dirname * filename *)
  val rem_file : string -> unit
  val copy : string -> string -> unit (* copy src dest *)
  val bincopy : string -> string -> unit (* bincopy src dest *)
  val update_copy : (string -> string -> unit) -> string -> string -> unit
                    (* copy fn. applied to args, but modTime on destination set
                       to be that of src *)
  val cp : bool -> string -> string -> unit
           (* if boolean is true, then update_copy bincopy,
              else update_copy copy *)

  val mv : bool -> string -> string -> unit
           (* if boolean is true, renames (/bin/mv) src to dest.  Otherwise
              does update_copy bincopy *)

  val clean_sigobj : unit -> unit

  val check_against : string -> string -> unit
    (* [check_against f1 f2] checks to see if file f1 is older than file f2
       and prints big warning if so *)

  val app_sml_files : (string -> unit) -> {dirname : string} -> unit
    (* applies function to every .sml and .sig file in given
       directory *)

  val transfer_file : (bool -> string -> string -> unit) -> string ->
                      (string * string) -> unit
      (* transfer_file opn dir (d,f)
           opn will be cp, mv or a symbolic link operation;
           dir is destination directory
           (d,f) is source file info (directory and file) *)

  val build_help : bool -> unit
    (* boolean says whether or not to build the theory graph *)

  val build_dir : (string -> unit) -> int -> (string * int) -> unit
      (* build_dir Holmake i (dir, j)
           Holmake calls Holmake in the provided directory argument;
           i is the user's specified selftest level
           dir is the directory to make
           j is the selftest level as given in the build sequence for dir *)

  val make_buildstamp : unit -> unit
  val setup_logfile : unit -> unit
  val finish_logging : bool -> unit

  val Holmake : (string -> string list -> 'a) -> ('a -> bool) ->
                (unit -> string list) ->
                ('a -> string) ->
                int -> string -> unit
      (* [Holmake sysl isSuccess extras analysis selftest dir] invokes
         Holmake, using function extras to generate extra commandline
         arguments, and function analysis to generate extra
         diagnostics from the exit code of the call to Holmake. The
         dir argument is also used for feedback; the assumption is
         that the current directory is already dir. The selftest
         parameter is the user's specification of the selftest level.
         The sysl function actually does the invocation (fork/exec,
         whatever), taking the path to the thing to run, and the
         additional arguments. The isSuccess parameter interprets
         whether or not the result of sysl constitutes a success. *)

end
