(* magic code to make SIGINT appear as an Interrupt exception
prim_val catch_interrupt : bool -> unit = 1 "sys_catch_break";
val _ = catch_interrupt true; *)

val _ = Version.register "$RCSfile$" "$Revision$" "$Date$";

val args = CommandLine.arguments()

val toStdOut = ref false  (* should output just go to stdout, rather than file? *)
val odir = ref "."        (* the directory to which output files are written *)

open testEval

fun fromSOME s (SOME x) = x
| fromSOME s NONE = raise (Fail s)

(* given a substring ss, searches for the next occurrence of a
   variable (\$[0-9] or \$[A-Za-z_][A-Za-z_0-9]* or \${[^}]*}).
   Returns SOME(ss0,v,ss1) where v is the variable name (without the
   dollar sign or braces), ss0 is the substring before the occurrence
   and ss1 is the substring after; or NONE if no variable occurrence
   exists. *)
fun varocc ss =
    let val (ss0,ss1) = Substring.position "$" ss
    in
    if Substring.size ss1 < 2 then
        NONE
    else
        let val (_,ss2) = fromSOME "varocc:1" (Substring.getc ss1)
        in
            let val (c,ss3) = fromSOME "varocc:2" (Substring.getc ss2)
            in
                if Char.isDigit c then
                    SOME (ss0, Substring.slice (ss2,0,SOME 1), ss3)
                else if c = #"{" then
                    let val (v,ss4) = Substring.splitl (fn c => c <> #"}") ss3
                    in
                        if Substring.isEmpty ss4 then
                            raise (Fail "Unterminated ${ variable reference")
                        else
                            let val (_,ss5) = fromSOME "varocc:3" (Substring.getc ss4)
                            in
                                SOME (ss0, v, ss5)
                            end
                    end
                else if Char.isAlpha c orelse c = #"_" then
                    let val (v,ss4) = Substring.splitl (fn c => Char.isAlphaNum c orelse c = #"_") ss2
                    in
                        SOME (ss0, v, ss4)
                    end
                else
                    NONE
            end
        end
    end

fun resolvevar f s =
    let fun go sss ss =
            case varocc ss of
                NONE => Substring.concat (List.rev (ss :: sss))
              | SOME(ss0,v,ss1) => go ([Substring.all(*full*) (f v), ss0] @ sss) ss1
    in
        go [] (Substring.all(*full*) s)
    end

fun lookup kvs k =
  case kvs of
    (k',v)::kvs' => if k' = k then v else lookup kvs' k
  | []           => raise (Fail ("variable not found: `"^k^"'"))

(* Dump a file, replacing all occurrences of ${VAR_NAME} with the
   value of that variable, as specified in an associative list passed
   as argument. *)
fun dump_string_template vs hnd s = let
  val s' = resolvevar (fn v => lookup vs (Substring.string v)) s
in
  TextIO.output(hnd,s')
end

fun output_and_print (hnd,s) =
  if !toStdOut then
      print s
  else
      (output (hnd,s); print s)

fun fileHead n f = let
  val istr = TextIO.openIn f
  val s = TextIO.inputLine istr ^ TextIO.inputLine istr
  val _ = TextIO.closeIn istr
in
  s
end

fun copy n x =
    if n <= 0 then [] else x :: copy (n-1) x

fun concatWith s sss =
    case sss of
        [] => ""
      | [ss] => Substring.string ss
      | (ss::sss) => Substring.string ss ^ s ^ concatWith s sss

fun relpath here there = let
in
    if not (String.sub (here,0) = #"/" andalso String.sub (there,0) = #"/") then
        "/BOGUSPATH/"^there
    else
        let fun loop hcs tcs =
                case (hcs,tcs) of
                    ((hc::hcs'),(tc::tcs')) => if Substring.string hc = Substring.string tc then loop hcs' tcs' else (hcs,tcs)
                  | _ => (hcs,tcs)
        in let val (hcs,tcs) = loop (Substring.tokens (fn c => c = #"/") (Substring.all(*full*) here))
                                    (Substring.tokens (fn c => c = #"/") (Substring.all(*full*) there))
           in
               (*Substring.*)concatWith "/" (copy (List.length hcs - 1) (Substring.all(*full*) "..") @ tcs)
           end
        end
end

fun do_one_file_body hnd fname = let
  val _ = htmlOutput hnd "<div id=\"thelist\">\n"
in
  try_finally (fn () => let
    val (host0, labels) = simp_hostlabels_from_file hnd fname
    val s = do_timed_trace hnd (host0, labels)
    val a_valid_trace = SOME (seq.hd s) handle Fail _ => NONE
  in
    a_valid_trace
  end
  ) (fn () => htmlOutput hnd "</div>\n"
  )
end

fun do_one_file h = let
    val basename = Path.file h
    val outfile = Path.concat (!odir,basename ^ ".out.html")
    val hnd = if !toStdOut then TextIO.stdOut else openOut outfile
    val datestr = Date.fmt "%Y-%m-%d T %H:%M:%S Z (%a)" (Date.fromTimeUniv (Time.now ()))
in
    (if !outputtingHtml then dump_string_template [("HEADING","HOL Trace: "^basename)] hnd strings.html_header else ());
    htmlOutput hnd "<div class=\"tracehead\">\n";
    altOutput hnd ("==Working on trace file <a href=\"" ^ relpath outfile h ^ ".html\">" ^ h ^ "</a> [<a href=\"" ^ relpath outfile h ^ "\">plain</a>] [<a href=\"" ^ relpath outfile h ^ ".ps.gz\">ps</a>]\n")
                  ("==Working on trace file " ^ h ^ "\n");
    htmlOutput hnd "<br>";
    output (hnd,("==Date: " ^ datestr ^ "\n"));
    htmlOutput hnd "<pre>\n";
    output (hnd,(fileHead 2 h handle _ => ""));
    htmlOutput hnd "</pre>\n";
    altOutput hnd ("<div class=\"verhead\" id=\"thever\">==Version numbers:\n<div class=\"vertab\">" ^ Version.getTable ()) ("==Versions:\n" ^ Version.getString ());
    htmlOutput hnd "</div></div></div>\n";
    TextIO.flushOut hnd;
    (case try_finally (fn () => do_one_file_body hnd h)
                      (fn () => htmlOutput hnd "<div class=\"tracetail\">\n") of
       NONE => output_and_print (hnd,"==Trace " ^ basename ^ " FAILED\n")
     | SOME ((_, host, ctxt), _) =>
       (output_and_print (hnd,"==Trace " ^ basename ^ " SUCCEEDED\n");
        htmlOutput hnd "<pre>\n";
        output (hnd, "==Final host:\n");
        output (hnd, Parse.term_to_string host);
        output (hnd, "\n==Final context:\n");
        appi (fn n => fn t => (output(hnd, Int.toString (n + 1)^". ");
                               output(hnd, Parse.term_to_string t);
                               output(hnd, "\n"))) ctxt;
        htmlOutput hnd "</pre>\n"))

      handle Interrupt => output_and_print (hnd,"==Trace " ^ basename ^ " INTERRUPTED\n")
           | CtxtTooComplicated csts =>
             (output_and_print (hnd,"==Trace " ^ basename ^ " TOO_COMPLICATED:\n");
              htmlOutput hnd "<pre>\n";
              appi (fn n => fn t => (output (hnd,(Int.toString (n + 1) ^ ". "));
                                     output (hnd,Parse.term_to_string t);
                                     output (hnd,"\n"))) csts;
              htmlOutput hnd "</pre>\n";
              output (hnd,"==Complicated constraint list ends\n"))
           | ExcessiveBackTracking =>
             output_and_print (hnd, "==Trace " ^basename ^
                                    " EXCESSIVE_BACKTRACKING\n")
           | HOL_ERR err =>
             (output_and_print (hnd,"==Trace " ^ basename ^ " INTERNAL_ERROR:\n");
              htmlOutput hnd "<pre>\n";
              output (hnd,Feedback.exn_to_string (HOL_ERR err));
              htmlOutput hnd "</pre>\n");
    htmlOutput hnd "</div>\n";
    (if !outputtingHtml then dump_string_template [] hnd strings.html_trailer else ());
    TextIO.flushOut hnd;
    (if !toStdOut then () else closeOut hnd)
end

fun do_many_files filenamelist =
    case filenamelist of
      [] => Process.exit Process.success
    | h :: t => (do_one_file h; do_many_files t)

(* accept files to process from stdin, terminated by EOF *)
(* a simple acknowledgement protocol is used *)
fun do_accept_files () =
    (output (stdOut, "\nReady.\n"); flushOut stdOut;
     let fun loop () =
         let val filename0 = inputLine stdIn in (* need to strip trailing newline always *)
             if filename0 = "" orelse filename0 = "quit\n" then
                 ()  (* EOF or quit means quit *)
             else
                 let val filename  = String.substring (filename0, 0, String.size filename0 - 1) in
                     output (stdOut, "Processing "^filename^"\n"); flushOut stdOut;
                     do_one_file filename;
                     output (stdOut, "\nReady.\n"); flushOut stdOut;
                     loop ()
                 end
         end
     in
         loop ()
     end;
     output (stdOut, "\nBye.\n"); flushOut stdOut)


fun the_or exn x = case x of
                     NONE => raise exn
                   | SOME x => x

fun die s = (TextIO.output(TextIO.stdErr, s^"\n");
             Process.exit Process.failure)
(* arguments:
   -s         output to stdout rather than to appropriately-named output files.
   -t         output in plain text (rather than HTML)
   -d dir     output files go to directory dir
   -a         accept trace files to process from stdin
              (using a simple protocol) rather than from the command line
   -bt directive
              control bracktracking with directives of form
                 <n>%   allow n% more steps than there are steps in the trace
                 <n>    allow n more steps
                 none   no limit on backtracking
   file1 ...  trace files to process
*)
fun parse_btdirective s =
    case s of
      "none" => testEval.btrack_control := NONE
    | _ => if String.sub(s, size s - 1) = #"%" then
             case Int.fromString (String.substring(s, 0, size s - 1)) of
               SOME i => testEval.btrack_control := SOME (PercentExtra i)
             | NONE => die "Mal-formed percentage for backtrack control"
           else
             case Int.fromString s of
               SOME i => testEval.btrack_control := SOME (AbsExtra i)
             | NONE => die "Mal-formed number for backtrack control"

fun do_args args =
    case args of
      "-s" :: args => (toStdOut := true; do_args args)
    | "-t" :: args => (outputtingHtml := false; do_args args)
    | "-d" :: dir :: args => (odir := dir; do_args args)
    | "-a" :: args => if null args then do_accept_files ()
                      else die "-a must be final argument"
    | ["-bt"] => die "-bt must be followed by back track control argument"
    | "-bt" :: dir :: args => (parse_btdirective dir; do_args args)
    | _            => do_many_files args

val _ = do_args args

