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

fun format_MESG s = String.concat["<<HOL message: ", s, ">>\n"];

fun format_WARNING structName fnName mesg =
  String.concat["<<HOL warning: ",
                structName, ".", fnName, ": ", mesg, ">>\n"];

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

local val err1 = mk_HOL_ERR "??" "??" "fail"
      val err2 = mk_HOL_ERR "??" "failwith"
in
fun fail() = raise err1
fun failwith s = raise (err2 s);
end;

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

datatype tracefns = TRFP of {get : unit -> int, set : int -> unit}
fun trfp_set (TRFP{set,...}) = set
fun trfp_get (TRFP{get,...}) = get()

fun ref2trfp r = TRFP {get = (fn () => !r), set = (fn i => r := i)}

type trace_record =
  {name : string, value : tracefns, default : int, maximum : int}

val trace_list = ref ([]: trace_record list);

fun find_record n = List.find (fn r => #name r = n) (!trace_list)

fun register_trace (nm, r, max) =
  if !r < 0 orelse max < 0 then
    raise ERR "register_trace" "Can't have trace values less than zero."
  else
    case find_record nm of
      NONE   => trace_list := {name = nm, value = ref2trfp r,
                               default =  !r, maximum = max}::(!trace_list)
    | SOME _ => raise ERR "register_trace"
        ("Already a trace "^quote nm^" registered.");

fun register_ftrace (nm, (get,set), max) = let
  val default = get()
in
  if default < 0 orelse max < 0 then
    raise ERR "register_ftrace" "Can't have trace values less than zero."
  else
    case find_record nm of
      NONE => trace_list := {name = nm, value = TRFP{get = get, set = set},
                             default = default, maximum = max}::(!trace_list)
    | SOME _ =>
        raise ERR "register_ftrace"
          ("Already a trace "^quote nm^" registered.")
end

fun register_btrace (nm, bref) =
  case find_record nm of
    NONE => trace_list := {name = nm,
                           value = TRFP{get= (fn () => if !bref then 1 else 0),
                                        set= (fn i => bref := (i > 0))},
                           default = if !bref then 1 else 0,
                           maximum = 1}::(!trace_list)
  | SOME _ =>
      raise ERR "register_btrace" ("Already a trace "^quote nm^" registered.");

fun traces() =
  Listsort.sort (fn (r1, r2) => String.compare (#name r1, #name r2))
  (map (fn {name = n, value, default = d,maximum} =>
        {name=n, trace_level = trfp_get value, default=d, max = maximum})
   (!trace_list));

fun set_trace nm newvalue =
 case find_record nm of
   SOME{value, maximum,...} =>
     if newvalue > maximum then
       raise ERR "set_trace" ("Trace "^quote nm^" can't be set that high.")
     else if newvalue < 0 then
       raise ERR "set_trace" ("Trace "^quote nm^" can't be set less than 0.")
     else
       trfp_set value newvalue
 | NONE => raise ERR "set_trace" ("No trace "^quote nm^" is registered");

fun reset_trace nm =
  case find_record nm
   of SOME{value, default,...} => trfp_set value default
    | NONE => raise ERR "reset_trace"
                ("No trace "^quote nm^" is registered");

fun reset_traces () =
  List.app (fn {value,default,...} => trfp_set value default) (!trace_list)

fun current_trace s =
  case find_record s of
    SOME {value,...} => trfp_get value
  | NONE => raise ERR "current_trace" ("No trace "^quote s^" is registered");

fun trace (nm,i) f x =
  case find_record nm of
    NONE => raise ERR "trace" ("No trace "^quote nm^" is registered")
  | SOME{value,maximum,...} =>
      if i > maximum then
        raise ERR "trace" ("Trace "^quote nm^" can't be set that high.")
      else if i < 0 then
        raise ERR "set_trace" ("Trace "^quote nm^" can't be set less than 0.")
      else let
        val init = trfp_get value
        val _ = trfp_set value i
        val y = f x handle e => (trfp_set value init; raise e)
        val _ = trfp_set value init
      in
        y
      end;

fun get_tracefn nm =
  case find_record nm of
    NONE => raise ERR "get_tracefn" ("No trace "^quote nm^" is registered")
  | SOME {value = TRFP{get,...},...} => get

val _ = register_btrace ("assumptions", Globals.show_assums);
val _ = register_btrace ("numeral types", Globals.show_numeral_types);

end  (* Feedback *)
