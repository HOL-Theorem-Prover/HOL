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

    val traces            : unit -> trace_elt list
    val create_trace      : trace_name * {initial:int,max:int} ->
                            {get : unit -> int, set : int -> unit}

    val register_alias_trace : {original:trace_name,alias:trace_name} -> unit

    val create_btrace     : trace_name * bool ->
                            {get : unit -> bool, set : bool -> unit}
    val gen_set_trace_C   : trace_name * int -> ctxt -> ctxt

    val current_trace     : string -> int
    val set_trace         : string -> int -> unit
    val reset_trace       : string -> unit
    val reset_traces      : unit -> unit
    val trace             : string * int -> ('a -> 'b) -> 'a -> 'b
    val with_traces       : (string * int) list -> ('a -> 'b) -> 'a -> 'b

    val show_tags         : unit -> bool
    val linewidth         : unit -> int
    val set_linewidth     : int -> unit
    val show_axioms       : unit -> bool
    val show_assums       : unit -> bool

end
