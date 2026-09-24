(* ===================================================================== *)
(* FILE          : Feedback.sml                                          *)
(* DESCRIPTION   : HOL exceptions, messages, warnings, and traces.       *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Cambridge             *)
(* DATE          : October 1, 2000 Konrad Slind                          *)
(* HISTORY       : Derived from Exception module, plus generalized       *)
(*                 tracing facility from Michael Norrish.                *)
(* ===================================================================== *)

structure Feedback :> Feedback =
struct

open Feedback_dtype

local open HOLPP in end

fun mk_origin s1 s2 loc =
  {origin_structure = s1,
   origin_function = s2,
   source_location = loc}

fun origins_of (HOL_ERROR {origins,...}) = origins
fun message_of (HOL_ERROR {message,...}) = message

fun mk_hol_error s1 s2 loc mesg =
  HOL_ERROR
    {origins = [mk_origin s1 s2 loc],
     message = mesg}

fun wrap_hol_error s f l (HOL_ERROR {origins,message}) =
  HOL_ERROR
     {origins = mk_origin s f l::origins,
      message = message}

val empty_hol_error =
  HOL_ERROR
    {origins = [], message = ""}

fun empty_origins_error sfn =
  HOL_ERROR
   {origins = [mk_origin "Feedback" sfn locn.Loc_Unknown],
    message = "no origin"}

val pp_hol_error =
  let open HOLPP
      fun pp_origin {origin_structure,origin_function,source_location} =
        block INCONSISTENT 2
          ([add_string "at ",
            add_string (origin_structure^"."^origin_function),add_string ":"]
           @
           (case source_location
            of locn.Loc_Unknown => []
             | _ => [add_break(1,0),
                     add_string (locn.toString source_location ^":")]))
  in
  fn (err as HOL_ERROR{origins,message}) =>
    if err = empty_hol_error then
        add_string "<empty-hol-error>"
     else
        block INCONSISTENT 0
          (pr_list pp_origin [NL] origins @
           (if message = "" then
               []
            else [add_break(1,2), add_string message]))
  end

fun format_hol_error lwidth holerr =
  HOLPP.pp_to_string lwidth pp_hol_error holerr

(*-------------------------------------------------------------------------*)
(* Exceptions used in HOL code.                                              *)
(*---------------------------------------------------------------------------*)

exception HOL_ERR of hol_error;

fun top_structure_of herr =
  case origins_of herr
   of [] => raise HOL_ERR (empty_origins_error "top_structure_of")
    | h::_ => #origin_structure h

fun top_function_of herr =
  case origins_of herr
   of [] => raise HOL_ERR (empty_origins_error "top_function_of")
    | h::_ => #origin_function h

fun top_location_of herr =
  case origins_of herr
   of [] => raise HOL_ERR (empty_origins_error "top_location_of")
    | h::_ => #source_location h

fun mk_HOL_ERRloc s1 s2 locn s3 = HOL_ERR (mk_hol_error s1 s2 locn s3)

fun mk_HOL_ERR s1 s2 s3 = HOL_ERR (mk_hol_error s1 s2 locn.Loc_Unknown s3)

fun set_top_function fnm (HOL_ERROR {origins,message}) =
  case origins
   of [] => raise HOL_ERR (empty_origins_error "set_top_function")
    | h::t => HOL_ERROR
      {origins = {origin_structure = #origin_structure h,
                  source_location = #source_location h,
                  origin_function = fnm} :: t,
       message = message}

fun set_message msg (HOL_ERROR {origins,message}) =
    HOL_ERROR {origins = origins, message = msg}

val ERR = mk_HOL_ERR "Feedback"  (* local to this file *)

(*---------------------------------------------------------------------------*
 * Controlling the display of exceptions, messages, and warnings.            *
 *---------------------------------------------------------------------------*)

val emit_ERR     = ref true
val emit_MESG    = ref true
val emit_WARNING = ref true
val emit_INFO    = ref true
val WARNINGs_as_ERRs = ref false

fun out strm s = (TextIO.output(strm, s); TextIO.flushOut strm)

val ERR_outstream     = ref (out TextIO.stdErr)
val MESG_outstream    = ref (out TextIO.stdOut)
val WARNING_outstream = ref (out TextIO.stdOut)
val INFO_outstream    = ref (out TextIO.stdOut)

fun quiet_warnings f = Portable.with_flag (emit_WARNING, false) f
fun quiet_messages f = Portable.with_flag (emit_MESG, false) f
fun quiet_info f     = Portable.with_flag (emit_INFO, false) f

(*---------------------------------------------------------------------------*
 * Formatting and output for exceptions, messages, and warnings.             *
 *---------------------------------------------------------------------------*)

fun format_ERR width holerr =
   String.concat ["\nException raised ", format_hol_error width holerr, "\n"]

fun format_MESG s = String.concat ["<<HOL message: ", s, ">>\n"]

fun format_WARNING structName fnName mesg =
   String.concat
      ["<<HOL warning: ", structName, ".", fnName, ": ", mesg, ">>\n"]

fun format_INFO s = s

val ERR_to_string     = ref (format_ERR 70)
val MESG_to_string    = ref format_MESG
val WARNING_to_string = ref format_WARNING
val INFO_to_string    = ref format_INFO

fun output_ERR s = if !emit_ERR then !ERR_outstream s else ()

(*---------------------------------------------------------------------------
    Makes an informative message from an exception. Subtlety: if we see
    that the exception is an Interrupt, we raise it.
 ---------------------------------------------------------------------------*)

fun exn_to_string (HOL_ERR herr) = !ERR_to_string herr
  | exn_to_string Portable.Interrupt = raise Portable.Interrupt
  | exn_to_string e = General.exnMessage e

(*---------------------------------------------------------------------------*)
(* Either raise the exception in the REPL (it gets printed by the installed  *)
(* prettyprinter) or print the error and exit to the OS.                     *)
(*---------------------------------------------------------------------------*)

fun render_exn e =
    if !Globals.interactive then
       Portable.reraise e
    else
      (output_ERR (exn_to_string e);
       OS.Process.exit OS.Process.failure)

(*---------------------------------------------------------------------------*)
(* System-dependent display of uncaught exceptions just before hitting the   *)
(* "Print" part of the REPL. In PolyML, just reraise the exn since it will   *)
(* be caught and the contents printed by the REPL. In MoscowML, the REPL     *)
(* "Print" function doesn't print the contents of uncaught exns, so one has  *)
(* handle the display of exn contents.                                       *)
(*---------------------------------------------------------------------------*)

fun display_uncaught e = Portable.display_exn (output_ERR o exn_to_string) e

(*---------------------------------------------------------------------------*)
(* Raise overlaps with display_uncaught but can also be useful for           *)
(* inspecting exn contents during the "Eval" part of the REPL.               *)
(*---------------------------------------------------------------------------*)

fun Raise e = (output_ERR (exn_to_string e); Portable.reraise e)

local
   val err1 = mk_HOL_ERR "??" "??" "fail"
   val err2 = mk_HOL_ERR "??" "failwith"
in
   fun fail () = raise err1
   fun failwith s = raise (err2 s)
end

(*---------------------------------------------------------------------------
    Support for backtracing exceptions, treating HOL_ERR specially.
    If we see that the exception is an Interrupt, we raise it.
 ---------------------------------------------------------------------------*)

fun wrap_exn_loc s f l e =
    case e
     of Portable.Interrupt => raise Portable.Interrupt
      | HOL_ERR holerr => HOL_ERR (wrap_hol_error s f l holerr)
      | exn => mk_HOL_ERRloc s f l (General.exnMessage exn)

fun wrap_exn s f = wrap_exn_loc s f locn.Loc_Unknown

fun HOL_MESG s =
  if !emit_MESG then !MESG_outstream (!MESG_to_string s) else ()

fun HOL_PROGRESS_MESG (start, finish) f x =
  if !emit_MESG then
    let in
       !MESG_outstream ("<<HOL message: " ^ start);
       f x before
       !MESG_outstream (finish ^ ">>\n")
     end
  else f x

fun HOL_WARNING s1 s2 s3 =
    if !WARNINGs_as_ERRs then raise mk_HOL_ERR s1 s2 s3
    else if !emit_WARNING then
      !WARNING_outstream (!WARNING_to_string s1 s2 s3)
    else ()

fun HOL_WARNINGloc s1 s2 locn s3 =
   HOL_WARNING s1 s2 (locn.toString locn ^ " :\n" ^ s3)

fun HOL_INFO s =
    if !emit_INFO then !INFO_outstream (!INFO_to_string s) else ()

(* Route Portable.pprint through HOL_INFO so its output participates
   in the INFO channel rather than escaping straight to OS stdout.
   Portable is more primitive than Feedback (built first), so it can't
   call HOL_INFO directly; here we patch its outstream ref now that
   the function exists. *)
val () = Portable.pprint_outstream := HOL_INFO

end  (* Feedback *)
