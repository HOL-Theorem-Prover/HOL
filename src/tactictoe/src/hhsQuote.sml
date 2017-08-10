(* ========================================================================== *)
(* FILE          : hhsQuote.sml                                               *)
(* DESCRIPTION   : Transforming term quotation into strings                   *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck             *)
(* DATE          : 2017                                                       *)
(* ========================================================================== *)

structure hhsQuote :> hhsQuote =
struct

open HolKernel boolLib

val ERR = mk_HOL_ERR "hhsQuote"

fun hhs_type_to_string t = 
  let val s = Lib.mlquote (Parse.type_to_string t) in
    "( Parse.Type [ HOLPP.QUOTE ( " ^ s ^ " ) ] )"
  end

fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             OS.Process.exit OS.Process.failure)
fun exndie e = die ("Exception raised " ^ General.exnMessage e)

fun mkBuffer () = let
  val buf = ref ([] : string list)
  fun push s = buf := s :: !buf
  fun read () = let
    val contents = String.concat (List.rev (!buf))
  in
    buf := [contents];
    contents
  end
  fun reset() = buf := []
in
  (push, read, reset)
end

val (QBpush, QBread, QBreset) = mkBuffer()

fun quoteString s =
  let
    val instrm = TextIO.openString s handle e => exndie e
    val qstate = filter.UserDeclarations.newstate(QBpush, fn () => ())
  in
    QBreset() ;
    filter.makeLexer (fn n => TextIO.input instrm) qstate ();
    TextIO.closeIn instrm;
    QBread()
  end

fun hhs_term_to_string (t,s) =
  if mem #"^" (explode s) then quoteString s else
  let val prev_show_types = !show_types in
    show_types := true;
    let val new_s = 
      Lib.mlquote (Parse.term_to_string t) 
    in
      (show_types := prev_show_types;
      "( Parse.Term [ HOLPP.QUOTE ( " ^ new_s ^ " ) ] )"
      )
    end
  end
  handle _ => raise ERR "hhs_term_to_string" s
  
end
