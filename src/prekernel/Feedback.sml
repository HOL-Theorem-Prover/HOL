(* ===================================================================== *)
(* FILE          : Feedback.sml                                          *)
(* DESCRIPTION   : HOL exceptions, messages, warnings, and traces.       *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Cambridge             *)
(* DATE          : October 1, 2000 Konrad Slind                          *)
(* HISTORY       : Derived from Exception module, plus generalized       *)
(*                 tracing facility from Michael Norrish.                *)
(* ===================================================================== *)

structure Feedback : Feedback =
struct

local open HOLPP in end

type origin =
  {origin_structure:string,
   origin_function:string,
   source_location : locn.locn}

fun mk_origin s1 s2 loc =
  {origin_structure = s1,
   origin_function = s2,
   source_location = loc}

datatype hol_error =
  HOL_ERROR of
     {origins : origin list,
      message : string}

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
        block INCONSISTENT 2
          (pr_list pp_origin [NL] origins @
           (if message = "" then
	       []
            else [NL, add_string message]))
  end

fun format_hol_error holerr =
  HOLPP.pp_to_string (!Globals.linewidth) pp_hol_error holerr

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

(*---------------------------------------------------------------------------
     Misc. utilities
 ---------------------------------------------------------------------------*)

fun quote s = String.concat ["\"", s, "\""]

fun assoc1 item =
   let
      fun assc ((e as (key, _)) :: rst) =
            if item = key then SOME e else assc rst
        | assc [] = NONE
   in
      assc
   end

(*---------------------------------------------------------------------------*
 * Controlling the display of exceptions, messages, and warnings.            *
 *---------------------------------------------------------------------------*)

val emit_ERR     = ref true
val emit_MESG    = ref true
val emit_WARNING = ref true
val WARNINGs_as_ERRs = ref false

fun out strm s = (TextIO.output(strm, s); TextIO.flushOut strm)

val ERR_outstream     = ref (out TextIO.stdErr)
val MESG_outstream    = ref (out TextIO.stdOut)
val WARNING_outstream = ref (out TextIO.stdOut)

fun quiet_warnings f = Portable.with_flag (emit_WARNING, false) f
fun quiet_messages f = Portable.with_flag (emit_MESG, false) f

(*---------------------------------------------------------------------------*
 * Formatting and output for exceptions, messages, and warnings.             *
 *---------------------------------------------------------------------------*)

fun format_ERR holerr =
   String.concat ["\nException raised ", format_hol_error holerr, "\n"]

fun format_MESG s = String.concat ["<<HOL message: ", s, ">>\n"]

fun format_WARNING structName fnName mesg =
   String.concat
      ["<<HOL warning: ", structName, ".", fnName, ": ", mesg, ">>\n"]

val ERR_to_string     = ref format_ERR
val MESG_to_string    = ref format_MESG
val WARNING_to_string = ref format_WARNING

fun output_ERR s = if !emit_ERR then !ERR_outstream s else ()

(*---------------------------------------------------------------------------
    Makes an informative message from an exception. Subtlety: if we see
    that the exception is an Interrupt, we raise it.
 ---------------------------------------------------------------------------*)

fun exn_to_string (HOL_ERR herr) = !ERR_to_string herr
  | exn_to_string Portable.Interrupt = raise Portable.Interrupt
  | exn_to_string e = General.exnMessage e

(*---------------------------------------------------------------------------*)
(* Either raise the exception, presumably a HOL_ERR, in the REPL (it gets    *)
(* printed by the installed prettyprinter) or print the error and raise      *)
(* BATCH_ERR with a message.                                                 *)
(*---------------------------------------------------------------------------*)

fun render_exn srcfn e =
    if !Globals.interactive then
       raise e
    else
      (output_ERR (exn_to_string e);
       raise Fail srcfn)

fun Raise e = (output_ERR (exn_to_string e); raise e)

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

(*---------------------------------------------------------------------------*
 * Traces, numeric flags; the higher setting, the more verbose the output.   *
 *---------------------------------------------------------------------------*)

datatype tracefns = TRFP of {get: unit -> int, set: int -> unit}
fun trfp_set (TRFP {set, ...}) = set
fun trfp_get (TRFP {get, ...}) = get ()

fun ref2trfp r = TRFP {get = (fn () => !r), set = (fn i => r := i)}

type trace_record = {
  aliases : string list,
  value: tracefns,
  default: int,
  maximum: int
}

datatype TI = TR of trace_record | ALIAS of string

val trace_map =
    ref (Binarymap.mkDict String.compare : (string,TI)Binarymap.dict)

fun find_record n =
  case Binarymap.peek (!trace_map, n) of
      NONE => NONE
    | SOME (TR tr) => SOME tr
    | SOME (ALIAS a) => find_record a

val WARN = HOL_WARNING "Feedback"

local
   fun err f l = raise ERR f (String.concat l)
in
   fun registered_err f nm = err f ["No trace ", quote nm, " is registered"]

   fun bound_check f nm maximum value =
      if value > maximum
         then err f ["Trace ", quote nm, " can't be set that high."]
      else if value < 0
         then err f ["Trace ", quote nm, " can't be set less than 0."]
      else ()
end

fun get_tracefn nm =
   case find_record nm of
      NONE => registered_err "get_tracefn" nm
    | SOME {value = TRFP {get, ...}, ...} => get

fun register_trace0 fnm (nm, r, max) =
   if !r < 0 orelse max < 0
      then raise ERR fnm "Can't have trace values less than zero."
   else
     let
       val trfns as TRFP recd = ref2trfp r
     in
       case Binarymap.peek (!trace_map, nm) of
           NONE => ()
         | SOME _ =>
           WARN fnm ("Replacing a trace with name " ^ quote nm);
       trace_map := Binarymap.insert
                      (!trace_map, nm, TR {value = trfns, default = !r,
                                           aliases = [], maximum = max});
       recd
     end
val register_trace = ignore o register_trace0 "register_trace"

fun create_trace {name, max, initial} =
    let val r = ref initial
    in
      register_trace0 "create_trace" (name, r, max)
    end

fun register_alias_trace {original, alias} =
  if original = alias then
    WARN "register_alias_trace" "original and alias are equal; doing nothing"
  else
    case find_record original of
        NONE => raise ERR "register_alias_trace"
                    ("Original trace: \""^original^"\" doesn't exist")
      | SOME {aliases,maximum,default,value} =>
        let
          val aliases' =
              if List.exists (fn s => s = alias) aliases then aliases
              else alias::aliases
          val recd = {aliases = aliases', maximum = maximum, default = default,
                     value = value}
          val record_alias = Binarymap.insert(!trace_map, original, TR recd)
          val mk_alias = Binarymap.insert(record_alias, alias, ALIAS original)
        in
          case Binarymap.peek (record_alias, alias) of
              NONE => ()
            | SOME (ALIAS a) =>
                if a = original then ()
                else WARN "register_alias_trace"
                          ("Replacing existing alias binding for \""^
                           alias ^ "\" |-> \"" ^ a ^"\"")
            | SOME (TR _) =>
                raise ERR "register_alias_trace"
                      ("Cannot replace existing genuine trace info for \""^
                       alias^"\"");
          trace_map := mk_alias
        end

fun register_ftrace (nm, (get, set), max) =
   let
      val default = get ()
   in
      if default < 0 orelse max < 0
         then raise ERR "register_ftrace"
                        "Can't have trace values less than zero."
      else (case Binarymap.peek (!trace_map, nm) of
               NONE => ()
             | SOME _ => WARN "register_ftrace"
                              ("Replacing a trace with name " ^ quote nm)
            ; trace_map :=
                  Binarymap.insert
                     (!trace_map, nm, TR {value = TRFP {get = get, set = set},
                                          default = default, aliases = [],
                                          maximum = max}))
   end

fun register_btrace0 fnm (nm, bref) =
    let
      fun get() = !bref
      fun set b = bref := b
    in
      case Binarymap.peek (!trace_map, nm) of
          NONE => ()
        | SOME _ => WARN fnm ("Replacing a trace with name "^ quote nm);
      trace_map :=
      Binarymap.insert
        (!trace_map, nm,
         TR {value = TRFP {get = (fn () => if !bref then 1 else 0),
                           set = (fn i => bref := (i > 0))},
             default = if !bref then 1 else 0, aliases = [],
             maximum = 1});
      {set = set, get = get}
    end
val register_btrace = ignore o register_btrace0 "register_btrace0"

fun create_btrace (nm, initb) =
    let val r = ref initb
    in
      register_btrace0 "create_btrace" (nm, r)
    end

datatype trace_elt =  (* for prettyprinting *)
  TraceElt of
    {name : string, aliases : string list,
     trace_level : int, default : int, max : int}

fun pp_trace_elt (TraceElt{name,aliases,trace_level,default,max}) =
    let open HOLPP
        val comma_space = [add_string",",add_break(1,0)]
        fun interval a b =
            map add_string ["[", Int.toString a, "..", Int.toString b, "]"]
        val alias_list = pr_list add_string comma_space aliases
        val name_plus_aliases =
            if null aliases then
               add_string name
            else block CONSISTENT 2
                   ([add_string name, add_break(0,0), add_string "["]
                    @ alias_list @ [add_string "]"])
    in block INCONSISTENT 2
         [name_plus_aliases, add_string ":", add_break(1,0),
          add_string (Int.toString trace_level), add_break(1,0),
          block CONSISTENT 0 (interval default max)]
    end

fun traces () =
   let
      fun foldthis (n, ti, acc) =
        case ti of
            ALIAS _ => acc
          | TR {value, default = d, maximum, aliases} =>
            {name = n, aliases = aliases,
             trace_level = trfp_get value,
             default = d,
             max = maximum} :: acc
   in
     List.map TraceElt
        (Binarymap.foldr foldthis [] (!trace_map))
   end

fun set_trace nm newvalue =
   case find_record nm of
      SOME {value, maximum, ...} =>
        (bound_check "set_trace" nm maximum newvalue; trfp_set value newvalue)
    | NONE => registered_err "set_trace" nm

fun reset_trace nm =
   case find_record nm of
      SOME {value, default, ...} => trfp_set value default
    | NONE => registered_err "reset_trace" nm

fun reset_traces () =
  let
    fun reset (TR{value,default,...}) = trfp_set value default
      | reset (ALIAS _) = ()
  in
    Binarymap.app (reset o #2) (!trace_map)
  end

fun current_trace nm =
   case find_record nm of
      SOME {value, ...} => trfp_get value
    | NONE => registered_err "current_trace" nm

fun trace (nm, i) f x =
   case find_record nm of
      NONE => registered_err "trace" nm
    | SOME {value, maximum, ...} =>
        (bound_check "trace" nm maximum i
         ; let
              val init = trfp_get value
              val _ = trfp_set value i
              val y = f x handle e => (trfp_set value init; raise e)
              val _ = trfp_set value init
           in
              y
           end)

val () = register_btrace ("assumptions", Globals.show_assums)
val () = register_btrace ("numeral types", Globals.show_numeral_types)

val () =
   let
      val v = Globals.show_types_verbosely
      val t = Globals.show_types
      fun get () = if !v then 2 else if !t then 1 else 0
      fun set i = if i = 0
                     then (v := false; t := false)
                  else if i = 1
                     then (v := false; t := true)
                  else (v := true; t := true)
   in
      register_ftrace ("types", (get, set), 2)
   end

val () = register_btrace ("PP.catch_withpp_err", OldPP.catch_withpp_err)

end  (* Feedback *)
