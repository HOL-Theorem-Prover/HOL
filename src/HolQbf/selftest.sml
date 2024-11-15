(* Copyright (c) 2010-2011 Tjark Weber. All rights reserved. *)

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
  fun finish () = OS.FileSys.remove path handle SysErr _ => ()
  fun work() = let
    val dict = QDimacs.write_qdimacs_file path t
    val varfn = QDimacs.dict_to_varfn dict
    val t' = QDimacs.read_qdimacs_file varfn path
  in
    if Term.aconv t t' then print "."
    else
      (finish(); die "Term read not alpha-equivalent to original term.")
  end
in
  Portable.finally finish work ()
    handle e => die ("Exception: " ^ General.exnMessage e ^
                     " raised while attempting read of dimacs file")
end

fun prove t =
  if squolem_installed then
    (HolQbfLib.prove t; print ".")
    handle Feedback.HOL_ERR {origin_structure, origin_function, source_location, message} =>
      die ("Prove failed on term '" ^ Hol_pp.term_to_string t ^
        "': exception HOL_ERR (in " ^ origin_structure ^ "." ^ origin_function ^
        " " ^ locn.toString source_location ^ ", message: " ^ message ^ ")")
  else ()

fun disprove t =
  if squolem_installed then
    (HolQbfLib.disprove t; print ".")
    handle Feedback.HOL_ERR {origin_structure, origin_function, source_location, message} =>
      die ("Disprove failed on term '" ^ Hol_pp.term_to_string t ^
        "': exception HOL_ERR (in " ^ origin_structure ^ "." ^ origin_function ^
        " " ^ locn.toString source_location ^ ", message: " ^ message ^ ")")
  else ()

val thmeq = Lib.pair_eq (Lib.list_eq Term.aconv) Term.aconv
fun decide t =
  if squolem_installed then let
    val th = HolQbfLib.decide t
    val _ = if let open Thm Term boolSyntax
               in
                 concl th ~~ t orelse
                 thmeq (dest_thm th) ([list_mk_forall(free_vars t,t)],F)
               end
            then ()
            else die ("Decide proved bad theorem on term '" ^
              Hol_pp.term_to_string t ^ "'")
    in print "." end
    handle Feedback.HOL_ERR {origin_structure, origin_function, source_location, message} =>
      die ("Decide failed on term '" ^ Hol_pp.term_to_string t ^
        "': exception HOL_ERR (in " ^ origin_structure ^ "." ^ origin_function ^
        " " ^ locn.toString source_location ^ ", message: " ^ message ^ ")")
  else ()

local
  fun f n = Term.mk_var("v"^(Int.toString n),Type.bool)
  val r = QDimacs.read_qdimacs_file f
in
  val tm0 = r "tests/z4ml.blif_0.10_0.20_0_1_out_exact.qdimacs"
end

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
    ``!x. ?y. (x \/ y) /\ (~x \/ y)``,
    tm0
  ]

val _ = List.app decide
  [
    ``!y. (?x. x /\ y) \/ (!x. y ==> x)``,
    ``!x. x \/ ~x``,
    ``?p. (!q. (p \/ ~q)) /\ !q:bool. ?r. r``,
    ``!x y z. (x \/ y) /\ (x \/ z)``,
    ``x \/ ~x``,
    ``x /\ ~x``,
    ``(x /\ x) \/ !y. x ==> y``,
    tm0(*,
    TODO: remove and replace unused variables
    ``!x (y:bool). (x /\ (!y. y ==> x)) \/ (~x /\ (?y. y ==> x))``,
    ``!x (y:'a). (x /\ (!y. y ==> x)) \/ (~x /\ (?y. y ==> x))``
    *)
  ]

(*****************************************************************************)

val _ = print " done, all tests successful.\n"

val _ = OS.Process.exit OS.Process.success
