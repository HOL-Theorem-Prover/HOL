use (Globals.HOLDIR ^ "/examples/separationLogic/src/holfoot/header.sml");

structure holfoot_command_line =
struct

val print_help =
let
  val s =   "Syntax: "^(CommandLine.name ())^" [Mode and printing options]... FILES+\n\n";
  val s = s^"Modes:\n";
  val s = s^"  -q   quiet mode, verify specifications automatically and just print end results\n";
  val s = s^"  -i   interactive mode, verify specifications step by step\n\n";
  val s = s^"Printing switches:\n";
  val s = s^"  -u   use unicode\n";
  val s = s^"  -r   raw output, disable VT100 specials\n\n";
  val s = s^"Help:\n";
  val s = s^"  -h   this help\n";
  val s = s^"  -hi  help on interactive mode\n\n";
in
   fn () => print s
end

val print_interactive_help =
let
  val s =   "In interactive mode you can use the following keys:\n"
  val s = s^"1-5 perform next step\n"
  val s = s^"    These 5 commands differ in the size of the step.\n";
  val s = s^"    '1' performs a large step whereas '5' performs a\n";
  val s = s^"    very small one. In detail:\n";
  val s = s^"       1   simulate next statement\n";
  val s = s^"       2   perform next frame computation step\n";
  val s = s^"       3   simulate next minor statement (like assumptions etc.)\n";
  val s = s^"       4   perform next minor step\n"
  val s = s^"       5   do the smallest step you can\n\n";
  val s = s^"s   solve the current goal\n";
  val s = s^"c   split the current goal into several goals\n";
  val s = s^"b   backup\n";
  val s = s^"p   print current goals\n";
  val s = s^"R   restart\n";
  val s = s^"q   quit\n";
  val s = s^"?   print this help\n\n\n";
in
   fn () => print s
end

fun interactive_verify file =
let
   val g = holfoot_set_goal file

   fun apply_step n =
      proofManagerLib.e (VC_STEP_TAC n)
   fun apply_solve () =
      proofManagerLib.e VC_SOLVE_TAC
   fun apply_strip () = proofManagerLib.e (REPEAT STRIP_TAC)
   val apply_restart = proofManagerLib.restart
   val apply_backup = proofManagerLib.b
   val out = Portable.stdOut_ppstream ()

   fun print_goal () =  let
       val proof = proofManagerLib.p ()
       val _ = proofManagerLib.pp_proof out proof;
       val _ = Portable.flush_ppstream out
       val _ = TextIO.output (TextIO.stdOut, "\n\n");
       val _ = TextIO.flushOut TextIO.stdOut
       in () end;
   fun print_goals () =  let
       val proofs = proofManagerLib.status ()
       val _ = proofManagerLib.pp_proofs out proofs;
       val _ = Portable.flush_ppstream out
       val _ = TextIO.output (TextIO.stdOut, "\n\n");
       val _ = TextIO.flushOut TextIO.stdOut
       in () end;

   val _ = print_goals ();

   fun loop () = let
      val c_opt = TextIO.input1 TextIO.stdIn   
      val _ = if isSome c_opt then () else loop();   
      val c = valOf c_opt;
   in
      (((case c of
          #"1" => (apply_step 1;print_goals())
        | #"2" => (apply_step 2;print_goals())
        | #"3" => (apply_step 3;print_goals())
        | #"4" => (apply_step 4;print_goals())
        | #"5" => (apply_step 5;print_goals())
        | #"s" => (apply_solve ();print_goals())
        | #"p" => (print_goals())
        | #"b" => (apply_backup ();print_goals())
        | #"R" => (apply_restart ();print_goals())
        | #"c" => (apply_strip ();print_goals())
        | #"q" => (Portable.exit ())
        | #"?" => (print_interactive_help ())
        | _ => ()
      ) handle Interrupt => raise Interrupt 
             | _ => ());loop())
   end;
in
   loop()
end;


fun holfoot_run () = let
   val _ = Feedback.set_trace "PPBackEnd use annotations" 0

   val args = CommandLine.arguments ();

   val args = ((Lib.pluck (fn x => x = "-h") args);print_help();[])
      handle _ => args;
   val args = ((Lib.pluck (fn x => x = "-hi") args);print_interactive_help();[])
      handle _ => args;

   val (quiet, args) = (true, Lib.snd (Lib.pluck (fn x => x = "-q") args)) 
      handle _ => (false, args);
   val (intera, args) = (true, Lib.snd (Lib.pluck (fn x => x = "-i") args)) 
      handle _ => (false, args);
   val (unicode, args) = (true, Lib.snd (Lib.pluck (fn x => x = "-u") args)) 
      handle _ => (false, args);
   val (raw_output, args) = (true, Lib.snd (Lib.pluck (fn x => x = "-r") args)) 
      handle _ => (false, args);

   val _ = Parse.current_backend := (if (raw_output) then PPBackEnd.raw_terminal else PPBackEnd.vt100_terminal);
   val _ = Feedback.set_trace "Unicode" (if unicode then 1 else 0)

   fun prover file = ((if intera then interactive_verify file else
                       ((holfootLib.holfoot_auto_verify_spec (not quiet) file);()));
                     (if quiet then () else (print "\n\n\n"; ())));

   fun check_file file =
      (prover file) handle
         _ => Parse.print_with_style [PPBackEnd.FG PPBackEnd.OrangeRed] "\nException raised!!!\n\n\n"

   val _ = if args = [] then print_help () else ();
in
   ((map check_file args);())
end



val _ = PolyML.export (Globals.HOLDIR ^ "/examples/separationLogic/src/holfoot/holfoot", holfoot_run)

end;

