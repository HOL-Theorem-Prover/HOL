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
end;

end (* local *)
