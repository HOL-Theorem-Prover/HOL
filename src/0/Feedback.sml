(* ===================================================================== *)
(* FILE          : Feedback.sml                                          *)
(* DESCRIPTION   : HOL exceptions, messages, warnings, and traces.       *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Cambridge             *)
(* DATE          : October 1, 2000 Konrad Slind                          *)
(* HISTORY       : Derived from Exception module, plus generalized       *)
(*                 tracing stuff from Michael Norrish.                   *)
(* ===================================================================== *)


structure Feedback :> Feedback =
struct

type error_record = {origin_structure : string,
                     origin_function  : string,
                     message          : string}

exception HOL_ERR of error_record;

(*---------------------------------------------------------------------------
     Curried version of HOL_ERR; can be more comfortable to use.
 ---------------------------------------------------------------------------*)

fun mk_HOL_ERR s1 s2 s3 = 
  HOL_ERR{origin_structure = s1, 
          origin_function = s2,
          message = s3};

val ERR = mk_HOL_ERR "Feedback";  (* local to this file *)


(*---------------------------------------------------------------------------
     Misc. utilities 
 ---------------------------------------------------------------------------*)

val output = Portable.output
val flush_out = Portable.flush_out;

fun quote s = String.concat ["\"",s,"\""];

fun assoc1 item =
 let fun assc ((e as (key,_))::rst) = if item=key then SOME e else assc rst
       | assc [] = NONE
 in assc
 end;

(*---------------------------------------------------------------------------*
 * Controlling the display of exceptions, messages, and warnings.            *
 *---------------------------------------------------------------------------*)

val emit_ERR     = ref true;
val emit_MESG    = ref true;
val emit_WARNING = ref true;

val ERR_outstream     = ref TextIO.stdErr;
val MESG_outstream    = ref TextIO.stdOut;
val WARNING_outstream = ref TextIO.stdOut;


(*---------------------------------------------------------------------------*
 * Formatting and output for exceptions, messages, and warnings.             *
 *---------------------------------------------------------------------------*)

fun format_ERR {message,origin_function,origin_structure} =
     String.concat["\nException raised at ", 
                   origin_structure,".", origin_function,
                   ":\n",message,"\n"];

fun format_MESG s = String.concat["<<HOL message: ", s, ".>>\n"];

fun format_WARNING structName fnName mesg =
  String.concat["HOL warning! ", 
                structName, ".", fnName, ":\n", mesg, "\n"];

val ERR_to_string     = ref format_ERR
val MESG_to_string    = ref format_MESG
val WARNING_to_string = ref format_WARNING;

fun output_ERR s =
  if !emit_ERR
  then (output(!ERR_outstream, s); flush_out (!ERR_outstream))
  else ()

(*---------------------------------------------------------------------------
    Makes an informative message from an exception. Subtlety: if we see 
    that the exception is an Interrupt, we raise it.
 ---------------------------------------------------------------------------*)

fun exn_to_string (HOL_ERR sss)     = !ERR_to_string sss
  | exn_to_string General.Interrupt = raise General.Interrupt
  | exn_to_string e                 = General.exnMessage e;

fun Raise e = (output_ERR (exn_to_string e); raise e)

fun fail() = raise (ERR "??" "fail");

fun failwith s = raise (ERR "failwith" s);

(*---------------------------------------------------------------------------
    Takes an exception, grabs its message as best as possible, then 
    make a HOL exception out of it. Subtlety: if we see that the 
    exception is an Interrupt, we raise it.
 ---------------------------------------------------------------------------*)

fun wrap_exn s f General.Interrupt = raise General.Interrupt
  | wrap_exn s f (HOL_ERR{origin_structure,origin_function,message}) =
        mk_HOL_ERR s f (origin_structure^"."^origin_function^" - "^message)
  | wrap_exn s f exn = mk_HOL_ERR s f (General.exnMessage exn);

fun HOL_MESG s =
  if !emit_MESG
  then (output(!MESG_outstream, !MESG_to_string s);
        flush_out (!MESG_outstream))
  else ()

fun HOL_WARNING s1 s2 s3 =
  if !emit_WARNING
  then (output(!WARNING_outstream, !WARNING_to_string s1 s2 s3);
        flush_out (!WARNING_outstream))
  else ()


(*---------------------------------------------------------------------------*
 * Traces, numeric flags; the higher setting, the more verbose the output.   *
 *---------------------------------------------------------------------------*)

val trace_list = ref ([]:(string * (int ref * int)) list)

fun register_trace nm r =
  case List.find (fn (s, _) => s = nm) (!trace_list) 
   of NONE   => trace_list := (nm, (r, !r))::(!trace_list)
    | SOME _ => raise ERR "register_trace"
                 ("Already a trace "^quote nm^" registered.");

fun traces() = 
   map (fn (n,(r,d)) => {name=n, trace_level = !r, default=d})
       (!trace_list);

fun set_trace nm newvalue =
 case assoc1 nm (!trace_list)
  of SOME(_,(r,_)) => r := newvalue
   | NONE => raise ERR "set_trace" ("No trace "^quote nm^" is registered");

fun reset_trace nm = 
  case assoc1 nm (!trace_list)
   of SOME(_,(r,d)) => r := d
    | NONE => raise ERR "reset_trace" 
                ("No trace "^quote nm^" is registered");

fun reset_traces () = List.app (fn (_, (r, d)) => r := d) (!trace_list)

fun trace (nm,i) f x =
  case assoc1 nm (!trace_list)
   of NONE => raise ERR "trace" ("No trace "^quote nm^" is registered")
    | SOME(_,(r,_)) => 
        let val init = !r
            val _ = r := i
            val y = f x handle e => (r := init; raise e)
            val _ = r := init
        in y
        end;

end  (* Feedback *)
