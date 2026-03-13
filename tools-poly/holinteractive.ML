(* holinteractive.ML - HOL_Interactive Structure for Poly/ML
   =========================================================

   This file defines the HOL_Interactive structure which provides:
   - toggle_quietdec() — Toggle quiet/verbose compilation mode
   - amquiet() — Check if in quiet mode
   - print_banner() — Print the HOL startup banner
   - setquietp(bool) — Set quiet mode explicitly
   - start_open/end_open/reset_open — Manage quietness during opens

   This is loaded by prelude.ML during interactive session startup.

   For Moscow ML, the equivalent HOL_Interactive structure is defined
   directly in tools/std.prelude.
*)

local
open Globals
in

(*---------------------------------------------------------------------------*
   Switch in and out of quiet mode
 *---------------------------------------------------------------------------*)

structure HOL_Interactive :>
  sig
    val toggle_quietdec : unit -> bool
    val amquiet : unit -> bool
    val print_banner : unit -> unit
    val setquietp : bool -> bool (* returns old value *)
    val start_open : unit -> unit
    val end_open : unit -> unit
    val reset_open : unit -> unit (* reset stack after compile failure *)
    val noisy_open : bool ref
  end =
struct
  infix ++
  val op ++ = OS.Path.concat
  val qd = ref true
  val noisy_open = ref false
  val quietp_stack = ref [true]
  fun toggle_quietdec () =
    if !qd then
      ( PolyML.Compiler.prompt1 := "> "
      ; PolyML.Compiler.prompt2 := "# "
      ; PolyML.print_depth 100
      ; qd := false
      ; false
      )
    else
      ( PolyML.Compiler.prompt1 := ""
      ; PolyML.Compiler.prompt2 := ""
      ; PolyML.print_depth 0
      ; qd := true
      ; true
      )
  fun amquiet () = !qd
  val build_stamp =
    let
      val stampstr = TextIO.openIn (HOLDIR ++ "tools" ++ "build-stamp")
      val stamp = TextIO.inputAll stampstr before TextIO.closeIn stampstr
    in
      stamp
    end
    handle _ => ""
  val id_string =
    "HOL4 [" ^ Globals.release ^ " " ^ Lib.int_to_string Globals.version ^
    " (" ^ Thm.kernelid ^ ", " ^ build_stamp ^ ")]\n\n"
  val exit_string =
    if Systeml.OS = "winNT" then
      "To exit type <Control>-Z <Return>  (*not* quit();)"
    else
      "To exit type <Control>-D"
  val line =
    "\n---------------------------------------------------------------------\n"

  fun print_banner () =
    TextIO.output (TextIO.stdOut,
      line ^
      "     " ^ id_string ^
      "     For introductory HOL help, type: help \"hol\";\n" ^
      "     " ^ exit_string ^
      line)

  fun setquietp b = if b = amquiet() then b else (toggle_quietdec(); not b)
  fun start_open () =
      let
        val old = amquiet()
        val verdict = old orelse not (!noisy_open)
      in
        ignore (setquietp verdict);
        quietp_stack := old :: (!quietp_stack)
      end
  fun end_open () = (
    setquietp (hd (!quietp_stack));
    quietp_stack := tl (!quietp_stack)
  )
  fun reset_open () = (
    (* Restore stack and quiet state after compile failure.
       This handles the case where start_open was called but the open failed
       before end_open could be called. Restores to non-quiet mode (normal REPL). *)
    quietp_stack := [true];
    ignore (setquietp false)
  )
end;

(* Connect reset_open to the REPL's compile-fail handler *)
val _ = HOL_REPL.resetOpenHook := HOL_Interactive.reset_open;

end (* local *)
