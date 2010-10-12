signature buildutils =
sig

  val help_mesg : string
  val normPath : string -> string
  val fullPath : string list -> string
  val quote : string -> string
  val die : string -> 'a
  val warn : string -> unit

  val read_buildsequence :
      { kernelpath : string } ->
      string -> (string * int) list

  val cline_selftest : string list -> (int * string list)

  val read_earlier_options : (TextIO.instream -> string option) ->
                             string list
  val write_options : string list -> unit

  datatype buildtype =
           Normal of {kernelspec : string, seqname : string, rest : string list}
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

end
