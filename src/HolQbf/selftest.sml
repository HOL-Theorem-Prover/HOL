(* Copyright (c) 2010 Tjark Weber. All rights reserved. *)

(* Unit tests for HolQbfLib *)

val _ = print "Testing HolQbfLib "

val _ = QbfTrace.trace := 0

(*****************************************************************************)
(* check whether Squolem is installed                                        *)
(*****************************************************************************)

val squolem_installed = Lib.can HolQbfLib.disprove ``?x. x /\ ~x``

val _ = if not squolem_installed then
          print "(Squolem not installed? Some tests will be skipped.) "
        else ()

(*****************************************************************************)
(* Utility functions                                                         *)
(*****************************************************************************)

fun die s =
  if !Globals.interactive then
    raise (Fail s)
  else (
    print ("\n" ^ s ^ "\n");
    OS.Process.exit OS.Process.failure
  )

fun read_after_write t =
let
  val path = FileSys.tmpName ()
  val dict = QDimacs.write_qdimacs_file path t
  val varfn = QDimacs.dict_to_varfn dict
in
  if Term.aconv t (QDimacs.read_qdimacs_file varfn path) then
    print "."
  else
    die "Term read not alpha-equivalent to original term."
end
handle Feedback.HOL_ERR {origin_structure, origin_function, message} =>
  die ("Read after write failed on term '" ^ Hol_pp.term_to_string t ^
    "': exception HOL_ERR (in " ^ origin_structure ^ "." ^ origin_function ^
    ", message: " ^ message ^ ")")

fun prove t =
  if squolem_installed then
    (HolQbfLib.prove t; print ".")
    handle Feedback.HOL_ERR {origin_structure, origin_function, message} =>
      die ("Prove failed on term '" ^ Hol_pp.term_to_string t ^
        "': exception HOL_ERR (in " ^ origin_structure ^ "." ^ origin_function ^
        ", message: " ^ message ^ ")")
  else ()

fun disprove t =
  if squolem_installed then
    (HolQbfLib.disprove t; print ".")
    handle Feedback.HOL_ERR {origin_structure, origin_function, message} =>
      die ("Disprove failed on term '" ^ Hol_pp.term_to_string t ^
        "': exception HOL_ERR (in " ^ origin_structure ^ "." ^ origin_function ^
        ", message: " ^ message ^ ")")
  else ()

(*****************************************************************************)
(* Test cases                                                                *)
(*****************************************************************************)

val _ = List.app read_after_write
  [
    ``(p \/ ~q) /\ r``,
    ``?p. (p \/ ~q) /\ r``,
    ``?q. (p \/ ~q) /\ r``,
    ``?r. (p \/ ~q) /\ r``,
    ``!p. ?q. (p \/ ~q) /\ r``,
    ``!p q. ?r. (p \/ ~q) /\ r``,
    ``!p. ?q r. (p \/ ~q) /\ r``,
    ``?p. !q. ?r. (p \/ ~q) /\ r``
  ]

val _ = List.app disprove
  [
    ``?x. x /\ ~x``,
    ``!x. ?y. x /\ y``,
    ``!x. ?y. (x \/ y) /\ ~y``
  ]

val _ = List.app prove
  [
    ``?x. x``,
    ``!x. ?y. x \/ y``,
    ``!x. ?y. (x \/ y) /\ (~x \/ y)``
  ]

(*****************************************************************************)

val _ = print " done, all tests successful.\n"

val _ = OS.Process.exit OS.Process.success
