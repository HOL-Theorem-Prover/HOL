signature Feedback =
sig

    type origin =
      {origin_structure:string,
       origin_function:string,
       source_location : locn.locn}

    datatype hol_error =
      HOL_ERROR of
        {origins : origin list,
         message : string}

    val pp_hol_error      : hol_error -> HOLPP.pretty
    val mk_hol_error      : string -> string -> locn.locn -> string -> hol_error
    val wrap_hol_error    : string -> string -> locn.locn -> hol_error -> hol_error
    val empty_hol_error   : hol_error
    val top_structure_of  : hol_error -> string
    val top_function_of   : hol_error -> string
    val top_location_of   : hol_error -> locn.locn
    val origins_of        : hol_error -> origin list
    val message_of        : hol_error -> string
    val set_message       : string -> hol_error -> hol_error
    val set_top_function  : string -> hol_error -> hol_error

    exception HOL_ERR of hol_error

    val mk_HOL_ERR        : string -> string -> string -> exn
    val mk_HOL_ERRloc     : string -> string -> locn.locn -> string -> exn

    val render_exn        : string -> exn -> 'a
    val wrap_exn          : string -> string -> exn -> exn
    val wrap_exn_loc      : string -> string -> locn.locn -> exn -> exn

    val emit_ERR          : bool ref
    val emit_MESG         : bool ref
    val emit_WARNING      : bool ref
    val WARNINGs_as_ERRs  : bool ref

    val ERR_outstream     : (string -> unit) ref
    val MESG_outstream    : (string -> unit) ref
    val WARNING_outstream : (string -> unit) ref
    (* heeds emit_ERR, uses ERR_outstream *)
    val output_ERR        : string -> unit

    val format_ERR        : hol_error -> string
    val format_MESG       : string -> string
    val format_WARNING    : string -> string -> string -> string

    val quiet_warnings    : ('a -> 'b) -> ('a -> 'b)
    val quiet_messages    : ('a -> 'b) -> ('a -> 'b)

    val ERR_to_string     : (hol_error -> string) ref
    val MESG_to_string    : (string -> string) ref
    val WARNING_to_string : (string -> string -> string -> string) ref
    val exn_to_string     : exn -> string

    val Raise             : exn -> 'a
    val fail              : unit -> 'a
    val failwith          : string -> 'a
    val HOL_MESG          : string -> unit
    val HOL_PROGRESS_MESG : string * string -> ('a -> 'b) -> 'a -> 'b
    val HOL_WARNING       : string -> string -> string -> unit
    val HOL_WARNINGloc    : string -> string -> locn.locn -> string -> unit

    datatype trace_elt =
       TraceElt of
         {name : string, aliases : string list,
          trace_level : int, default : int, max : int}

    val pp_trace_elt      : trace_elt -> HOLPP.pretty
    val traces            : unit -> trace_elt list
    val register_trace    : (string * int ref * int) -> unit
    val create_trace      : {name:string,initial:int,max:int} ->
                            {get : unit -> int, set : int -> unit}

    val register_alias_trace : {original:string,alias:string} -> unit
    val register_ftrace   : (string * ((unit -> int) * (int -> unit)) * int)
                             -> unit
    val register_btrace   : (string * bool ref) -> unit
    val create_btrace     : string * bool ->
                            {get : unit -> bool, set : bool -> unit}

    val current_trace     : string -> int
    val get_tracefn       : string -> unit -> int
    val set_trace         : string -> int -> unit
    val reset_trace       : string -> unit
    val reset_traces      : unit -> unit
    val trace             : string * int -> ('a -> 'b) -> 'a -> 'b

end
