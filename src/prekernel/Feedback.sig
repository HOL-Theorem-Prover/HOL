signature Feedback =
sig
    type error_record = {origin_structure : string,
                         origin_function  : string,
                         source_location  : locn.locn,
                         message          : string}

    exception HOL_ERR of error_record
    val mk_HOL_ERR        : string -> string -> string -> exn
    val mk_HOL_ERRloc     : string -> string -> locn.locn -> string -> exn
    val wrap_exn          : string -> string -> exn -> exn
    val wrap_exn_loc      : string -> string -> locn.locn -> exn -> exn
    val set_origin_function : string -> error_record -> error_record
    val set_message       : string -> error_record -> error_record

    val emit_ERR          : bool ref
    val emit_MESG         : bool ref
    val emit_WARNING      : bool ref
    val WARNINGs_as_ERRs  : bool ref

    val ERR_outstream     : (string -> unit) ref
    val MESG_outstream    : (string -> unit) ref
    val WARNING_outstream : (string -> unit) ref
    (* heeds emit_ERR, uses ERR_outstream *)
    val output_ERR        : string -> unit

    val format_ERR        : error_record -> string
    val format_MESG       : string -> string
    val format_WARNING    : string -> string -> string -> string

    val quiet_warnings    : ('a -> 'b) -> ('a -> 'b)
    val quiet_messages    : ('a -> 'b) -> ('a -> 'b)

    val ERR_to_string     : (error_record -> string) ref
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

    val traces            : unit -> {name:string, max : int,
                                     aliases : string list,
                                     trace_level:int, default:int} list
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
