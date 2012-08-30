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

  val read_buildsequence :
      {kernelname : string} ->
      string -> (string * int) list

  val cline_selftest : string list -> (int * string list)

  val read_earlier_options : (TextIO.instream -> string option) ->
                             string list
  val write_options : string list -> unit

  datatype buildtype =
           Normal of {kernelspec : string, seqname : string,
                      build_theory_graph : bool, rest : string list}
         | Clean of string

  val get_cline : {default_seq : string} -> buildtype


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

  val clean : string -> string -> string list
  val cleanAll : string -> string -> string list
  val clean_dirs : {HOLDIR:string, action : string -> string -> string list} ->
                   string list -> unit
  val clean_sigobj : unit -> unit

  val check_against : string -> unit
       (* checks to see if string is newer than build executable *)

  val transfer_file : (bool -> string -> string -> unit) -> string ->
                      (string * string) -> unit
      (* transfer_file opn dir (d,f)
           opn will be cp, mv or a symbolic link operation;
           dir is destination directory
           (d,f) is source file info (directory and file) *)

  val build_dir : (string -> unit) -> int -> (string * int) -> unit
      (* build_dir Holmake i (dir, j)
           Holmake calls Holmake in the provided directory argument;
           i is the user's specified selftest level
           dir is the directory to make
           j is the selftest level as given in the build sequence for dir *)



end
