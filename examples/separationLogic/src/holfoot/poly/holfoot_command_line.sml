(*
use (Globals.HOLDIR ^ "/examples/separationLogic/src/holfoot/poly/header.sml");
*)

val _ = load "DiskThms";

val build_date = Date.toString (Date.fromTimeLocal (Time.now()));

fun print_help full =
let
  open PPBackEnd Parse
  val s =   "Syntax: holfoot [options] INPUT-FILES\n\n";
  val _ = print s;

  val _ = print_with_style [Bold] "Modes:\n";
  val s =   "  -q      quiet mode, verify specifications automatically and just print end results\n";
  val s = s^"  -i      interactive mode, verify specifications step by step\n";
  val s = s^(if full then 
            "  -f      file mode, load files with interactive proofs\n\n" else "\n");
  val _ = print s;
  val _ = print_with_style [Bold] "Printing switches:\n";
  val s =   "  -nu     turn unicode off\n";
  val s = s^"  -r      raw output, disable VT100 specials\n";
  val s = s^"  --html  html output\n\n";
  val _ = print s;
  val _ = print_with_style [Bold] "External Tools:\n";
  val s =   "  --yices use the Yices SMT-solver (default off)\n\n";
  val _ = print s;
  val _ = print_with_style [Bold] "Debugging options:\n";
  val s =   "  -p      print profiling information\n";
  val s = s^"  -v      verbose level (values 1 - 5)\n";
  val s = s^"  -vt     verbose level try (values 1 - 5)\n\n";
  val _ = print s;
  val _ = print_with_style [Bold] "Help:\n";
  val s =   "  -h      this help\n";
  val s = s^"  -hi     help on interactive mode\n\n";
  val _ = print s;
  val _ = print_with_style [Bold] "Build time: ";
  val _ = print ("\n  "^build_date^"\n\n");
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
  val s = s^"  5   do the smallest step possible\n\n";
  val _ = print s;
  val _ = print_with_style [Bold] "continue forward analysis\n";
  val s =   "  s   as far as possible\n";
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
  val s = s^"  r   rotate subgoals\n\n";
  val s = s^"  c   split the current goal\n\n";
  val _ = print s;
  val _ = print_with_style [Bold] "other options\n";
  val s =   "  q   quit\n";
  val s = s^"  ?   print this help\n\n\n";
  val _ = print s;
in
   ()
end

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

fun interactive_verify file =
let
   val g = holfoot_set_goal file
   val out = Portable.stdOut_ppstream ()

   fun print_goal () =  let
       val proof = proofManagerLib.p ()
       val _ = print "\n";
       val _ = proofManagerLib.pp_proof out proof;
       val _ = Portable.flush_ppstream out
       val _ = print "\n";
       in () end;
   fun print_goals () =  let
       val proofs = proofManagerLib.status ()
       val _ = print "\n";
       val _ = proofManagerLib.pp_proofs out proofs;
       val _ = Portable.flush_ppstream out
       val _ = print "\n";
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
          #"1" => (apply_step 1;print_goal())
        | #"2" => (apply_step 2;print_goal())
        | #"3" => (apply_step 3;print_goal())
        | #"4" => (apply_step 4;print_goal())
        | #"5" => (apply_step 5;print_goal())
        | #"s" => (apply_solve ();print_goal())
        | #"w" => (apply_solve_till stop_at_while;print_goal())
        | #"i" => (apply_solve_till stop_at_cond;print_goal())
        | #"a" => (apply_solve_till stop_at_abstraction;print_goal())
        | #"h" => (apply_solve_till stop_at_hoare_triple;print_goal())
        | #"f" => (apply_solve_till stop_at_frame_calc;print_goal())
        | #"p" => (print_goals())
        | #"b" => (apply_backup ();print_goal())
        | #"R" => (apply_restart ();print_goal())
        | #"r" => (rotate 1;print_goal())
        | #"c" => (apply_strip ();print_goal())
        | #"q" => (Portable.exit ())
        | #"?" => (print_interactive_help ())
        | _ => (print_error c)
      ) handle Interrupt => raise Interrupt 
             | _ => ());loop())
   end;
in
   loop()
end;



fun web_interface_print_goals gL =
   let
      val nthmL = map (fn g => ("", mk_thm (valOf g))) (filter isSome gL);
      val _ = DiskThms.write_stream Portable.std_out nthmL;
      val _ = Portable.output (Portable.std_out, ("\n\n"));
      val out = Portable.stdOut_ppstream ();
      fun print_goal (SOME g) =
          (Portable.output (Portable.std_out, ("*************************************\n"));
           Portable.flush_out Portable.std_out;
           goalStack.pp_goal out g;
           Portable.flush_ppstream out)
        | print_goal NONE =
          (Portable.output (Portable.std_out, ("*SOLVED******************************\n"));
           Portable.flush_out Portable.std_out)

      val _ = map print_goal gL;
   in
      ()
   end;



fun holfoot_web_interface () = let
   val _ = Feedback.set_trace "PPBackEnd use annotations" 0
   val _ = Parse.current_backend := PPBackEnd.html_terminal;
   val _ = Feedback.set_trace "Unicode" 1
   val _ = Feedback.set_trace "goalstack chatting" 0
   val args = CommandLine.arguments ();
   val (unicode, args) = (false, Lib.snd (Lib.pluck (fn x => x = "-nu") args)) 
      handle _ => (true, args);
   val (yices, args) = (true, Lib.snd (Lib.pluck (fn x => x = "--yices") args)) 
      handle _ => (false, args);
   val _ = Feedback.set_trace "Unicode" (if unicode then 1 else 0)
   val _ = Feedback.set_trace "holfoot use Yices" (if yices then 1 else 0)
in
   if length args = 1 then
   let
      val spec_t = parse_holfoot_file (hd args);
      val _ = web_interface_print_goals [SOME ([], spec_t)]
   in () end else let
      val gL = map (fn (_,thm) => (hyp thm, concl thm)) 
           (DiskThms.read_stream Portable.stdin);
      val pos = valOf (Int.fromString (el 1 args))
      val command = String.sub ((el 2 args), 0)

      val (gLs, cg::gLe) = Lib.split_after pos gL;
      val _ = set_goal cg;
      val _ = ((case command of
                  #"1" => (apply_step 1)
                | #"2" => (apply_step 2)
                | #"3" => (apply_step 3)
                | #"4" => (apply_step 4)
                | #"5" => (apply_step 5)
                | #"X" => (proofManagerLib.e (HF_INIT_TAC))
                | #"s" => (apply_solve ())
                | #"c" => (apply_strip ())
                | #"w" => (apply_solve_till stop_at_while)
                | #"i" => (apply_solve_till stop_at_cond)
                | #"a" => (apply_solve_till stop_at_abstraction)
                | #"h" => (apply_solve_till stop_at_hoare_triple)
                | #"f" => (apply_solve_till stop_at_frame_calc)
                | _ => Feedback.fail());()) handle HOL_ERR _ => ();
      val cgL = map SOME (top_goals ()) handle HOL_ERR _ => [NONE];
      val gL' = Lib.flatten [map SOME gLs, cgL, map SOME gLe];
      val _ = web_interface_print_goals gL'
   in () end
end


fun holfoot_run (full, filemode_command) = let
   val _ = Feedback.set_trace "PPBackEnd use annotations" 0
   val _ = Feedback.set_trace "HolSmtLib" 0   
   val _ = Feedback.set_trace "meson" 0
   val _ = Feedback.set_trace "metis" 0
   val _ = Globals.interactive := false;

   fun pluck_num_arg a =
      let fun pl _ [] = raise ERR "pluck" "predicate not satisfied"
          | pl _ [h] = raise ERR "pluck" "predicate not satisfied"
          | pl A (h::n::t) = if (h = a) then (valOf (Int.fromString n), List.revAppend(A,t)) else pl (h::A) (n::t)
      in pl []
   end;


   val orgargs = CommandLine.arguments ();
   val args = orgargs;
   val (quiet, args) = (true, Lib.snd (Lib.pluck (fn x => x = "-q") args)) 
      handle _ => (false, args);
   val (intera, args) = (true, Lib.snd (Lib.pluck (fn x => x = "-i") args)) 
      handle _ => (false, args);
   val (file_mode, args) = (true, Lib.snd (Lib.pluck (fn x => x = "-f") args)) 
      handle _ => (false, args);
   val (unicode, args) = (false, Lib.snd (Lib.pluck (fn x => x = "-nu") args)) 
      handle _ => (true, args);
   val (yices, args) = (true, Lib.snd (Lib.pluck (fn x => x = "--yices") args)) 
      handle _ => (false, args);
   val (raw_output, args) = (true, Lib.snd (Lib.pluck (fn x => x = "-r") args)) 
      handle _ => (false, args);
   val (html_output, args) = (true, Lib.snd (Lib.pluck (fn x => x = "--html") args)) 
      handle _ => (false, args);
   val (do_profile, args) = (true, Lib.snd (Lib.pluck (fn x => x = "-p") args)) 
      handle _ => (false, args);
   fun print_profile () = if not do_profile then () else
      (print "\n\n";Profile.print_profile_results (Profile.results ()))

   val (vl, args) = pluck_num_arg "-v" args handle _ => (0, args);
   val (vlt, args) = pluck_num_arg "-vt" args handle _ => (0, args);

   val _ = Parse.current_backend := (if (raw_output) then PPBackEnd.raw_terminal else 
                                    (if (html_output) then PPBackEnd.html_terminal else PPBackEnd.vt100_terminal));
   val _ = Feedback.set_trace "Unicode" (if unicode then 1 else 0)
   val _ = Feedback.set_trace "holfoot print file" (if html_output then 0 else 1);
   val _ = Feedback.set_trace "holfoot use Yices" (if yices then 1 else 0)
   val _ = Feedback.set_trace "holfoot verbose level" vl;
   val _ = Feedback.set_trace "holfoot verbose level try" vlt;

   val args = ((Lib.pluck (fn x => x = "-h") orgargs);print_help full;[])
      handle _ => args;
   val args = ((Lib.pluck (fn x => x = "-hi") args);print_interactive_help();[])
      handle _ => args;

   fun prover file = if file_mode then filemode_command file else
                     ((if intera then interactive_verify file else
                       ((holfootLib.holfoot_interactive_verify_spec (not quiet) (not quiet) file (SOME [generate_vcs]) []);()));
                     (if quiet then () else (print "\n\n\n"; ())));

   fun check_file file =
      (prover file) handle
         _ => Parse.print_with_style [PPBackEnd.FG PPBackEnd.OrangeRed] "\nException raised!!!\n\n\n"
   val _ = Profile.reset_all ();
   val _ = if orgargs = [] then print_help full else ();
in
   ((map check_file args);print_profile())
end





