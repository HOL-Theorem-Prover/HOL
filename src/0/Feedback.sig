(* ===================================================================== *)
(* FILE          : Feedback.sig                                          *)
(* DESCRIPTION   : HOL exceptions, messages, warnings, and traces.       *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, Michael Norrish                     *)
(*                 University of Cambridge                               *)
(* DATE          : October 1, 2000                                       *)
(* ===================================================================== *)


signature Feedback =
sig
    type error_record = {origin_structure : string,
                         origin_function  : string,
                         message          : string}

    exception HOL_ERR of error_record

    val mk_HOL_ERR        : string -> string -> string -> exn
    val wrap_exn          : string -> string -> exn -> exn

    val emit_ERR          : bool ref
    val emit_MESG         : bool ref
    val emit_WARNING      : bool ref

    val ERR_outstream     : TextIO.outstream ref
    val MESG_outstream    : TextIO.outstream ref
    val WARNING_outstream : TextIO.outstream ref

    val format_ERR        : error_record -> string
    val format_MESG       : string -> string
    val format_WARNING    : string -> string -> string -> string
   
    val ERR_to_string     : (error_record -> string) ref
    val MESG_to_string    : (string -> string) ref
    val WARNING_to_string : (string -> string -> string -> string) ref
    val exn_to_string     : exn -> string

    val Raise             : exn -> 'a
    val fail              : unit -> 'a
    val failwith          : string -> 'a
    val HOL_MESG          : string -> unit
    val HOL_WARNING       : string -> string -> string -> unit

    val traces            : unit -> {name:string, 
                                     trace_level:int, default:int} list
    val register_trace    : string -> int ref -> unit
    val set_trace         : string -> int -> unit
    val reset_trace       : string -> unit
    val reset_traces      : unit -> unit
    val trace             : string * int -> ('a -> 'b) -> 'a -> 'b

end;
