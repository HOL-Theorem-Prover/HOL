signature FinalHOLFlags =
sig

    type trace_name = {group:string,name:string}
    val str2name          : string -> trace_name (* splits on first '.' char *)
    datatype trace_elt =
       TraceElt of
         {name : trace_name, aliases : trace_name list,
          trace_level : int, default : int, max : int}
    val pp_trace_elt      : trace_elt -> HOLPP.pretty

    type trace_map
    type ctxt
    type bflag
    type flag

    val set_flag          : flag * int -> unit
    val get_flag          : flag -> int
    val set_flagC         : flag * int -> ctxt -> ctxt
    val get_flagC         : ctxt -> flag -> int
    val flag_name         : flag -> string


    val set_bflag         : bflag * bool -> unit
    val get_bflag         : bflag -> bool
    val set_bflagC        : bflag * bool -> ctxt -> ctxt
    val get_bflagC        : ctxt -> bflag -> bool
    val bflag_name        : bflag -> string

    val flag_of_bflag     : bflag -> flag

    val traces            : unit -> trace_elt list
    val create_trace      : trace_name * {initial:int,max:int} ->
                            {get : unit -> int, set : int -> unit, flag:flag}

    val register_alias_trace : {original:trace_name,alias:trace_name} -> unit

    val create_btrace     : trace_name * bool ->
                            {get : unit -> bool, set : bool -> unit,
                             flag : bflag}
    val gen_set_trace_C   : trace_name * int -> ctxt -> ctxt
    val gen_get_trace_C   : ctxt -> trace_name -> int

    val current_trace     : string -> int
    val set_trace         : string -> int -> unit
    val reset_trace       : string -> unit
    val reset_traces      : unit -> unit
    val trace             : string * int -> ('a -> 'b) -> 'a -> 'b
    val with_traces       : (string * int) list -> ('a -> 'b) -> 'a -> 'b
    val with_bflags       : (bflag * bool) list -> ('a -> 'b) -> 'a -> 'b

    val show_tags         : bflag
    val linewidth         : unit -> int
    val set_linewidth     : int -> unit
    val show_axioms       : bflag
    val show_assums       : bflag
    val show_types        : bflag

end
