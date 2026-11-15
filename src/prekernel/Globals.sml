(* ===================================================================== *)
(* FILE          : Globals.sml                                           *)
(* DESCRIPTION   : Contains global flags for hol98.                      *)
(*                                                                       *)
(* AUTHOR        : (c) Konrad Slind, University of Calgary               *)
(* DATE          : August 26, 1991                                       *)
(*               : July 17, 1998                                         *)
(*                                                                       *)
(* ===================================================================== *)

structure Globals :> Globals =
struct

(*---------------------------------------------------------------------------*
 * Installation-specific information.                                        *
 *---------------------------------------------------------------------------*)

val HOLDIR = Systeml.HOLDIR

(*---------------------------------------------------------------------------*
 * Version information                                                       *
 *---------------------------------------------------------------------------*)

val release = Systeml.release
val version = Systeml.version

(*---------------------------------------------------------------------------*
 * For showing assumptions in theorems                                       *
 *---------------------------------------------------------------------------*)

val show_assums = ref false

(*---------------------------------------------------------------------------*
 * For showing oracles used to prove theorems.                               *
 *---------------------------------------------------------------------------*)

val show_tags = ref false

(*---------------------------------------------------------------------------*
 * For showing the axioms used in the proof of a theorem.                    *
 *---------------------------------------------------------------------------*)

val show_axioms = ref true

(*---------------------------------------------------------------------------*
 * For showing the time taken to "scrub" the current theory of out-of-date   *
 * items. For developers.                                                    *
 *---------------------------------------------------------------------------*)

val show_scrub = ref true

(*---------------------------------------------------------------------------*
 * Tells the prettyprinters how wide the page is.                            *
 *---------------------------------------------------------------------------*)

val linewidth = CoreReplVARS.linewidth

(*---------------------------------------------------------------------------*
 * Controls depth of printing for terms. Since the pp recursively decrements *
 * this value when traversing a term, and since printing stops when the      *
 * value is 0, the negative value means "print everything". Warning:         *
 * this will work to negmaxint, but no guarantees after that.                *
 *---------------------------------------------------------------------------*)

val max_print_depth = ref ~1

(*---------------------------------------------------------------------------*
 * Controls how many elements to print for list forms. Mirrors print depth.  *
 *---------------------------------------------------------------------------*)

val max_print_length = ref ~1

val goal_line = ref "------------------------------------"


(*---------------------------------------------------------------------------*
 * Whether or not to be strict about what name a type or constant has.       *
 * Checked in Theory.new_type and Theory.new_constant.                       *
 *---------------------------------------------------------------------------*)

val checking_type_names  = ref true
val checking_const_names = ref true

(* ----------------------------------------------------------------------
    The syntax used to highlight out-of-date constants in the
    prettyprinters for types and terms
   ---------------------------------------------------------------------- *)

fun  oldify n s = String.concat ["old", Int.toString n, "->", s, "<-old"]

val print_thy_loads = ref false

(* ----------------------------------------------------------------------
    Flag telling us whether or not we're interactive.

    If this is set, this allows for certain pieces of code to be a bit
    more verbose. It's set by tools/std.prelude (or
    tools-poly/prelude.ML), so theory scripts and the like that
    Holmake runs won't cause the printing of messages.
   ---------------------------------------------------------------------- *)

val interactive = ref false

(* ----------------------------------------------------------------------
    When a tactic fails during a non-interactive Holmake build, dump a
    Poly/ML heap (via PolyML.SaveState.saveChild on the Poly side; a
    no-op under Moscow ML) so the user can resume with
       bin/hol --holstate=<file>
    and explore the failing proof.  Flipped on by
    holmake_not_interactive; default false so the interactive REPL is
    unaffected.
   ---------------------------------------------------------------------- *)

val dumpheap_on_failure = ref false

val hol_clock = Timer.startCPUTimer ()

(*---------------------------------------------------------------------------*)
(* The default directory where ML extracted from theory files is written.    *)
(*---------------------------------------------------------------------------*)

val emitMLDir = ref (Path.concat(HOLDIR,"src/emit/ML/"))
val emitCAMLDir = ref (Path.concat(HOLDIR,"src/emit/Caml/"))

end (* Globals *)
