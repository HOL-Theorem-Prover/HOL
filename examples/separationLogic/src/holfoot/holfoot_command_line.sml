(*
use (Globals.HOLDIR ^ "/examples/separationLogic/src/holfoot/header.sml");
*)

fun print_help () =
let
  open PPBackEnd Parse
  val s =   "Syntax: holfoot [options] INPUT-FILES\n\n";
  val _ = print s;

  val _ = print_with_style [Bold] "Modes:\n";
  val s =   "  -q     quiet mode, verify specifications automatically and just print end results\n";
  val s = s^"  -i     interactive mode, verify specifications step by step\n\n";
  val _ = print s;
  val _ = print_with_style [Bold] "Printing switches:\n";
  val s =   "  -u     use unicode\n";
  val s = s^"  -r     raw output, disable VT100 specials\n";
  val s = s^"  --html html output\n\n";
  val _ = print s;
  val _ = print_with_style [Bold] "Help:\n";
  val s =   "  -h     this help\n";
  val s = s^"  -hi    help on interactive mode\n\n";
  val _ = print s;
in
   ()
end

fun print_interactive_help () =
let
  open PPBackEnd Parse
  val _ = print "In interactive mode you can use the following keys:\n\n"
  val _ = print_with_style [Bold] "perform next step\n"
  val s =   "  1   simulate next statement\n";
  val s = s^"  2   perform next frame computation step\n";
  val s = s^"  3   simulate next minor statement (like assumptions etc.)\n";
  val s = s^"  4   perform next minor step\n"
  val s = s^"  5   do the smallest step you can\n\n";
  val _ = print s;
  val _ = print_with_style [Bold] "continue forward analysis\n";
  val s =   "  s   as far as you can\n";
  val s = s^"  w   till next while-loop\n";
  val s = s^"  i   till next if-then-else\n";
  val s = s^"  a   till next abstraction\n";
  val s = s^"  f   till a frame has to be calculated\n";
  val s = s^"  h   till there is a Hoare triple again\n\n";
  val _ = print s;
  val _ = print_with_style [Bold]"proof navigation\n";
  val s =   "  b   undo\n";
  val s = s^"  R   restart proof\n";
  val s = s^"  p   print current goals\n";
  val s = s^"  c   split the current goal\n\n";
  val _ = print s;
  val _ = print_with_style [Bold] "other options\n";
  val s =   "  q   quit\n";
  val s = s^"  ?   print this help\n\n\n";
  val _ = print s;
in
   ()
end

fun interactive_verify file =
let
   val g = holfoot_set_goal file

   fun apply_step n =
      proofManagerLib.e (xHF_STEP_TAC [generate_vcs] n)
   fun apply_solve () =
      proofManagerLib.e (xHF_SOLVE_TAC [generate_vcs])
   fun apply_strip () = proofManagerLib.e (REPEAT STRIP_TAC)
   val apply_restart = proofManagerLib.restart
   val apply_backup = proofManagerLib.b
   fun apply_solve_till sp = proofManagerLib.e 
       (xHF_SOLVE_TAC [generate_vcs, sp])
   val apply_restart = proofManagerLib.restart
   val apply_backup = proofManagerLib.b
   val out = Portable.stdOut_ppstream ()

   fun print_goal () =  let
       val proof = proofManagerLib.p ()
       val _ = proofManagerLib.pp_proof out proof;
       val _ = Portable.flush_ppstream out
       in () end;
   fun print_goals () =  let
       val proofs = proofManagerLib.status ()
       val _ = proofManagerLib.pp_proofs out proofs;
       val _ = Portable.flush_ppstream out
       in () end;
   val _ = print_goals ();
   
   fun print_error c = if (c = #"\n") then () else
      let
         open PPBackEnd Parse
         val _ = print_with_style [FG OrangeRed]
                      ("Unknown command '"^(Char.toString c)^"'! ");
         val _ = print "Press '?' for help ...\n";
      in
         ()
      end;

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
        | #"w" => (apply_solve_till stop_at_while;print_goals())
        | #"i" => (apply_solve_till stop_at_cond;print_goals())
        | #"a" => (apply_solve_till stop_at_abstraction;print_goals())
        | #"h" => (apply_solve_till stop_at_hoare_triple;print_goals())
        | #"f" => (apply_solve_till stop_at_frame_calc;print_goals())
        | #"p" => (print_goals())
        | #"b" => (apply_backup ();print_goals())
        | #"R" => (apply_restart ();print_goals())
        | #"c" => (apply_strip ();print_goals())
        | #"q" => (Portable.exit ())
        | #"?" => (print_interactive_help ())
        | _ => (print_error c)
      ) handle Interrupt => raise Interrupt 
             | _ => ());loop())
   end;
in
   loop()
end;


fun holfoot_run () = let
   val _ = Feedback.set_trace "PPBackEnd use annotations" 0

   val orgargs = CommandLine.arguments ();
   val args = orgargs;
   val (quiet, args) = (true, Lib.snd (Lib.pluck (fn x => x = "-q") args)) 
      handle _ => (false, args);
   val (intera, args) = (true, Lib.snd (Lib.pluck (fn x => x = "-i") args)) 
      handle _ => (false, args);
   val (unicode, args) = (true, Lib.snd (Lib.pluck (fn x => x = "-u") args)) 
      handle _ => (false, args);
   val (raw_output, args) = (true, Lib.snd (Lib.pluck (fn x => x = "-r") args)) 
      handle _ => (false, args);
   val (html_output, args) = (true, Lib.snd (Lib.pluck (fn x => x = "--html") args)) 
      handle _ => (false, args);

   val _ = Parse.current_backend := (if (raw_output) then PPBackEnd.raw_terminal else 
                                    (if (html_output) then PPBackEnd.html_terminal else PPBackEnd.vt100_terminal));
   val _ = Feedback.set_trace "Unicode" (if unicode then 1 else 0)
   val _ = Feedback.set_trace "holfoot print file" (if html_output then 0 else 1);

   val args = ((Lib.pluck (fn x => x = "-h") orgargs);print_help();[])
      handle _ => args;
   val args = ((Lib.pluck (fn x => x = "-hi") args);print_interactive_help();[])
      handle _ => args;

   fun prover file = ((if intera then interactive_verify file else
                       ((holfootLib.holfoot_auto_verify_spec (not quiet) file);()));
                     (if quiet then () else (print "\n\n\n"; ())));

   fun check_file file =
      (prover file) handle
         _ => Parse.print_with_style [PPBackEnd.FG PPBackEnd.OrangeRed] "\nException raised!!!\n\n\n"

   val _ = if orgargs = [] then print_help () else ();
in
   ((map check_file args);())
end




