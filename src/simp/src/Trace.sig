signature Trace =
sig
  include Abbrev

    datatype action =
             LZ_TEXT             of unit -> string
           | TEXT                of string
           | REDUCE              of (string * term)
           | REWRITING           of (term * thm)
           | SIDECOND_ATTEMPT    of term
           | SIDECOND_SOLVED     of thm
           | SIDECOND_NOT_SOLVED of term
           | OPENING             of (term * thm)
           | PRODUCE             of (term * string * thm)
           | IGNORE              of (string * thm)
           | MORE_CONTEXT        of thm

   val trace_hook  : (int * action -> unit) ref;
   val trace       : int * action -> unit
   val trace_level : int ref
   val tty_trace   : action -> unit

end
