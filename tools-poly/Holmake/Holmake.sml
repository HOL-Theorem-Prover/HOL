(*---------------------------------------------------------------------------
     A special purpose version of make that "does the right thing" in
     single directories for building HOL theories, and accompanying
     SML libraries.
 ---------------------------------------------------------------------------*)

(* Copyright University of Cambridge, Michael Norrish, 1999-2001 *)
(* Author: Michael Norrish *)

structure Holmake =
struct

open Systeml Holmake_tools
structure FileSys = OS.FileSys
structure Path = OS.Path

infix //
fun p1 // p2 = OS.Path.concat(p1,p2)
val default_holstate = Systeml.DEFAULT_STATE

fun main () = let

val execname = OS.Path.file (CommandLine.name())
fun warn s = (TextIO.output(TextIO.stdErr, execname^": "^s^"\n");
              TextIO.flushOut TextIO.stdErr)


(* Global parameters, which get set at configuration time *)
val HOLDIR0 = Systeml.HOLDIR;
val POLYMLLIBDIR0 = Systeml.POLYMLLIBDIR;
val DEPDIR = ".HOLMK";
val DEFAULT_OVERLAY = "Overlay.ui";

val SYSTEML = Systeml.systeml



(*---------------------------------------------------------------------------
     Support for handling the preprocessing of files containing ``
 ---------------------------------------------------------------------------*)

fun fromFileNoSuf f =
  case f of
    UO c  => codeToString c
  | UI c  => codeToString c
  | SIG c => codeToString c
  | SML c => codeToString c
  | Unhandled s => s


(*** Construction of secondary dependencies *)

fun mk_depfile_name s = fullPath [DEPDIR, s^".d"]


(**** get_dependencies *)
(* figures out whether or not a dependency file is a suitable place to read
   information about current target or not, and then either does so, or makes
   the dependency file and then reads from it.

     f1 forces_update_of f2
     iff
     f1 exists /\ (f2 exists ==> f1 is newer than f2)
*)

infix forces_update_of
fun (f1 forces_update_of f2) = let
  open Time
in
  OS.FileSys.access(f1, []) andalso
  (not (OS.FileSys.access(f2, [])) orelse OS.FileSys.modTime f1 > OS.FileSys.modTime f2)
end

(**** get dependencies from file *)



(** Command line parsing *)

(*** list functions *)
fun member m [] = false
  | member m (x::xs) = if x = m then true else member m xs
fun set_union s1 s2 =
  case s1 of
    [] => s2
  | (e::es) => let
      val s' = set_union es s2
    in
      if member e s' then s' else e::s'
    end
fun delete m [] = []
  | delete m (x::xs) = if m = x then delete m xs else x::delete m xs
fun set_diff s1 s2 = foldl (fn (s2e, s1') => delete s2e s1') s1 s2
fun remove_duplicates [] = []
  | remove_duplicates (x::xs) = x::(remove_duplicates (delete x xs))
fun I x = x

(*** parse command line *)
fun parse_command_line list = let
  fun find_pairs0 tag rem inc [] = (List.rev rem, List.rev inc)
    | find_pairs0 tag rem inc [x] = (List.rev (x::rem), List.rev inc)
    | find_pairs0 tag rem inc (x::(ys as (y::xs))) = let
      in
        if x = tag then
          find_pairs0 tag rem (y::inc) xs
        else
          find_pairs0 tag (x::rem) inc ys
      end
  fun find_pairs tag = find_pairs0 tag [] []
  fun find_toggle tag [] = ([], false)
    | find_toggle tag (x::xs) = let
      in
        if x = tag then (delete tag xs, true)
        else let val (xs', b) = find_toggle tag xs in
          (x::xs', b)
        end
      end
  fun find_alternative_tags [] input = (input, false)
    | find_alternative_tags (t1::ts) input = let
        val (rem0, b0) = find_toggle t1 input
        val (rem1, b1) = find_alternative_tags ts rem0
      in
        (rem1, b0 orelse b1)
      end

  fun find_one_pairtag tag nov somev list = let
    val (rem, vals) = find_pairs tag list
  in
    case vals of
      [] => (rem, nov)
    | [x] => (rem, somev x)
    | _ => let
        open TextIO
      in
        output(stdErr,"Ignoring all but last "^tag^" spec.\n");
        flushOut stdErr;
        (rem, somev (List.last vals))
      end
  end

  val (rem, includes) = find_pairs "-I" list
  val (rem, dontmakes) = find_pairs "-d" rem
  val (rem, debug) = find_toggle "--d" rem
  val (rem, help) = find_alternative_tags  ["--help", "-h"] rem
  val (rem, rebuild_deps) = find_toggle "--rebuild_deps" rem
  val (rem, cmdl_HOLDIRs) = find_pairs "--holdir" rem
  val (rem, no_sigobj) = find_alternative_tags ["--no_sigobj", "-n"] rem
  val (rem, allfast) = find_toggle "--fast" rem
  val (rem, fastfiles) = find_pairs "-f" rem
  val (rem, qofp) = find_toggle "--qof" rem
  val (rem, ot) = find_toggle "--ot" rem
  val (rem, no_hmakefile) = find_toggle "--no_holmakefile" rem
  val (rem, no_prereqs) = find_toggle "--no_prereqs" rem
  val (rem, recursive) = find_toggle "-r" rem
  val (rem, user_hmakefile) =
    find_one_pairtag "--holmakefile" NONE SOME rem
  val (rem, no_overlay) = find_toggle "--no_overlay" rem
  val (rem, user_overlay) = find_one_pairtag "--overlay" NONE SOME rem
  val (rem, cmdl_POLYMLLIBDIRs) = find_pairs "--polymllibdir" rem
  val (rem, interactive_flag) = find_alternative_tags ["--interactive", "-i"]
                                rem
  val (rem, keep_going_flag) = find_alternative_tags ["-k", "--keep-going"] rem
  val (rem, quiet_flag) = find_toggle "--quiet" rem
  val (rem, do_logging_flag) = find_toggle "--logging" rem

  val (rem, POLY) = find_one_pairtag "--poly" Systeml.POLY (fn x => x) rem
  val (rem, cmdl_HOLSTATE) = find_one_pairtag "--holstate" NONE SOME rem
  val (rem, polynothol) = find_toggle "--poly_not_hol" rem
  val (rem, no_lastmakercheck) = find_toggle "--nolmbc" rem
in
  {targets=rem, debug=debug, show_usage=help,
   always_rebuild_deps=rebuild_deps,
   additional_includes=includes,
   dontmakes=dontmakes, no_sigobj = no_sigobj,
   quit_on_failure = qofp,
   no_prereqs = no_prereqs,
   cline_recursive = recursive,
   opentheory = ot, no_hmakefile = no_hmakefile,
   allfast = allfast, fastfiles = fastfiles,
   user_hmakefile = user_hmakefile,
   no_overlay = no_overlay,
   no_lastmakercheck = no_lastmakercheck,
   user_overlay = user_overlay,
   interactive_flag = interactive_flag,
   cmdl_HOLDIR =
     case cmdl_HOLDIRs of
       []  => NONE
     | [x] => SOME x
     |  _  => let
       in
         warn "Ignoring all but last --holdir spec.";
         SOME (List.last cmdl_HOLDIRs)
       end,
   cmdl_POLYMLLIBDIR =
     case cmdl_POLYMLLIBDIRs of
       [] => NONE
     | [x] => SOME x
     | _ => let
       in
         warn "Ignoring all but last --polymllibdir spec.";
         SOME (List.last cmdl_POLYMLLIBDIRs)
       end,
   POLY = POLY,
   cmdl_HOLSTATE = cmdl_HOLSTATE,
   polynothol = polynothol,
   keep_going_flag = keep_going_flag,
   quiet_flag = quiet_flag,
   do_logging_flag = do_logging_flag}
end


(* parameters which vary from run to run according to the command-line *)
val {targets, debug, dontmakes, show_usage, allfast, fastfiles,
     always_rebuild_deps, interactive_flag, opentheory,
     additional_includes = cline_additional_includes,
     cmdl_HOLDIR, cmdl_HOLSTATE, cmdl_POLYMLLIBDIR, POLY, polynothol,
     no_sigobj = cline_no_sigobj, no_prereqs,
     quit_on_failure, no_hmakefile, user_hmakefile, no_overlay,
     no_lastmakercheck, user_overlay, keep_going_flag, quiet_flag,
     do_logging_flag, cline_recursive} =
  parse_command_line (CommandLine.arguments())

val (outputfunctions as {warn,info,tgtfatal,diag}) =
    output_functions {quiet_flag = quiet_flag, debug = debug}

val _ = diag ("CommandLine.name() = "^CommandLine.name())
val _ = diag ("CommandLine.arguments() = "^
              String.concatWith ", " (CommandLine.arguments()))

(* call out to (exec) a different Holmake *)
fun has_clean [] = false
  | has_clean (h::t) =
      h = "clean" orelse h = "cleanAll" orelse h = "cleanDeps" orelse
      has_clean t
val _ = if has_clean targets then ()
        else
          do_lastmade_checks outputfunctions
                             {no_lastmakercheck = no_lastmakercheck}

(* set up logging *)
val logfilename = Systeml.make_log_file
val hostname = if Systeml.isUnix then
                 case Mosml.run "hostname" [] "" of
                   Mosml.Success s => String.substring(s,0,size s - 1) ^ "-"
                                      (* substring to drop \n in output *)
                 | _ => ""
               else "" (* what to do under windows? *)

fun finish_logging buildok = let
in
  if do_logging_flag andalso OS.FileSys.access(logfilename, []) then let
      open Date
      val timestamp = fmt "%Y-%m-%dT%H%M" (fromTimeLocal (Time.now()))
      val newname0 = hostname^timestamp
      val newname = (if buildok then "" else "bad-") ^ newname0
    in
      OS.FileSys.rename {old = logfilename, new = newname};
      buildok
    end
  else buildok
end handle IO.Io _ => (warn "Had problems making permanent record of make log";
                    buildok)

val _ = OS.Process.atExit (fn () => ignore (finish_logging false))


(* find HOLDIR and POLYMLDIR by first looking at command-line, then looking
   for a value compiled into the code.
*)
val HOLDIR    = case cmdl_HOLDIR of NONE => HOLDIR0 | SOME s => s
val POLYMLLIBDIR =  case cmdl_POLYMLLIBDIR of NONE => POLYMLLIBDIR0 | SOME s => s
val SIGOBJ    = normPath(OS.Path.concat(HOLDIR, "sigobj"));

  (*
fun compile debug args = let
  val _ = if debug then print ("  with command "^
                               spacify(MOSMLCOMP::args)^"\n")
          else ()
in
  SYSTEML (MOSMLCOMP::args)
end;
*)

(* turn a variable name into a list *)
fun envlist env id = let
  open Holmake_types
in
  map dequote (tokenize (perform_substitution env [VREF id]))
end

fun process_hypat_options s = let
  open Substring
  val ss = full s
  fun recurse (noecho, ignore_error, ss) =
      if noecho andalso ignore_error then
        (true, true, string (dropl (fn c => c = #"@" orelse c = #"-") ss))
      else
        case getc ss of
          NONE => (noecho, ignore_error, "")
        | SOME (c, ss') =>
          if c = #"@" then recurse (true, ignore_error, ss')
          else if c = #"-" then recurse (noecho, true, ss')
          else (noecho, ignore_error, string ss)
in
  recurse (false, false, ss)
end


(* directory specific stuff here *)
fun Holmake dirinfo cline_additional_includes targets = let
  val {dir, visited = visiteddirs} = dirinfo
  val _ = OS.FileSys.chDir (hmdir.toAbsPath dir)

(* prepare to do logging *)
val () = if do_logging_flag then
           if OS.FileSys.access (logfilename, []) then
             warn "Make log exists; new logging will concatenate on this file"
           else let
               (* touch the file *)
               val outs = TextIO.openOut logfilename
             in
               TextIO.closeOut outs
             end handle IO.Io _ => warn "Couldn't set up make log"
         else ()



val hmakefile =
  case user_hmakefile of
    NONE => "Holmakefile"
  | SOME s =>
      if exists_readable s then s
      else die_with ("Couldn't read/find makefile: "^s)

val mosml_indicator = "%%MOSCOWML_INDICATOR%%"

val base_env = let
  open Holmake_types
  val alist = [
    ("ISIGOBJ", [VREF "if $(findstring NO_SIGOBJ,$(OPTIONS)),,$(SIGOBJ)"]),
    ("MOSML_INCLUDES", [VREF ("patsubst %,-I %,"^
                              (if cline_no_sigobj then ""
                               else "$(ISIGOBJ)") ^
                              " $(INCLUDES) $(PREINCLUDES)")]),
    ("HOLMOSMLC", [VREF "MOSMLCOMP"]),
    ("HOLMOSMLC-C", [VREF "MOSMLCOMP", LIT " -c "]),
    ("MOSMLC",  [VREF "MOSMLCOMP"]),
    ("MOSMLCOMP", [LIT mosml_indicator]),
    ("POLY", [LIT (Systeml.protect Systeml.POLY)]),
    ("POLYMLLIBDIR", [LIT POLYMLLIBDIR]),
    ("POLY_LDFLAGS", [LIT (spacify (map Systeml.protect POLY_LDFLAGS))]),
    ("POLY_LDFLAGS_STATIC", [LIT (spacify (map Systeml.protect POLY_LDFLAGS_STATIC))])]
in
  List.foldl (fn (kv,acc) => Holmake_types.env_extend kv acc)
             Holmake_types.base_environment
             alist
end


val (hmakefile_env, extra_rules, first_target) =
  if exists_readable hmakefile andalso not no_hmakefile
  then let
      val () = if debug then
                print ("Reading additional information from "^hmakefile^"\n")
              else ()
    in
      ReadHMF.read hmakefile base_env
    end
  else (base_env, Holmake_types.empty_ruledb, NONE)

val envlist = envlist hmakefile_env

val hmake_includes = envlist "INCLUDES"
val hmake_options = envlist "OPTIONS"
val additional_includes =
  remove_duplicates (cline_additional_includes @ hmake_includes)

val hmake_preincludes = envlist "PRE_INCLUDES"
val hmake_no_overlay = member "NO_OVERLAY" hmake_options
val hmake_no_sigobj = member "NO_SIGOBJ" hmake_options
val hmake_qof = member "QUIT_ON_FAILURE" hmake_options
val hmake_noprereqs = member "NO_PREREQS" hmake_options
val extra_cleans = envlist "EXTRA_CLEANS"

val HOLSTATE = let
  val default =
      case cmdl_HOLSTATE of
        NONE => if polynothol then POLY else default_holstate
      | SOME s => s
in
  case envlist "HOLHEAP" of
    [] => default
  | [x] => x
  | xs => (warn ("Can't interpret "^String.concatWith " " xs ^
                 " as a HOL HEAP spec; using default hol.builder.");
           default)
end

val quit_on_failure = quit_on_failure orelse hmake_qof

val _ = if cline_recursive andalso no_prereqs then
          warn("-r forces recursion, taking precedence over --no_prereqs")
        else ()
val no_prereqs = (no_prereqs orelse hmake_noprereqs) andalso not cline_recursive

val _ =
  if quit_on_failure andalso allfast then
    warn "quit on (tactic) failure ignored for fast built theories"
  else
    ()

val no_sigobj = cline_no_sigobj orelse hmake_no_sigobj
val actual_overlay =
  if no_sigobj orelse no_overlay orelse hmake_no_overlay then NONE
  else
    case user_overlay of
      NONE => SOME DEFAULT_OVERLAY
    | SOME _ => user_overlay

val std_include_flags = if no_sigobj then [] else [SIGOBJ]

fun extra_deps t =
    Option.map #dependencies
               (Holmake_types.get_rule_info extra_rules hmakefile_env t)

fun extra_commands t =
    Option.map #commands
               (Holmake_types.get_rule_info extra_rules hmakefile_env t)

val extra_targets = Binarymap.foldr (fn (k,_,acc) => k::acc) [] extra_rules

fun extra_rule_for t = Holmake_types.get_rule_info extra_rules hmakefile_env t

(* treat targets as sets *)
infix in_target
fun (s in_target t) = case extra_deps t of NONE => false | SOME l => member s l

fun addPath I file =
  if OS.Path.isAbsolute file then
    file
  else let
      val p = List.find (fn p =>
                            FileSys.access (Path.concat (p, file ^ ".ui"), []))
                        (FileSys.getDir() :: I)
    in
      case p of
           NONE => OS.Path.concat (OS.FileSys.getDir(), file)
         | SOME p => OS.Path.concat (p, file)
    end;

fun poly_compile quietp file I deps = let
  val modName = fromFileNoSuf file
  fun mapthis (Unhandled _) = NONE
    | mapthis f = SOME (fromFileNoSuf f)
  val depMods = List.map (addPath I) (List.mapPartial mapthis deps)
  val say = if quietp then (fn s => ())
            else (fn s => TextIO.output(TextIO.stdOut, s ^ "\n"))
  val _ = say ("HOLMOSMLC -c " ^ fromFile file)
in
case file of
  SIG _ =>
    (let val outUi = TextIO.openOut (modName ^ ".ui")
     in
       TextIO.output (outUi, String.concatWith "\n" depMods);
       TextIO.output (outUi, "\n");
       TextIO.output (outUi, addPath [] (fromFile file) ^ "\n");
       TextIO.closeOut outUi;
       OS.Process.success
     end
     handle IO.Io _ => OS.Process.failure)
| SML _ =>
    (let val outUo = TextIO.openOut (modName ^ ".uo")
     in
       TextIO.output (outUo, String.concatWith "\n" depMods);
       TextIO.output (outUo, "\n");
       TextIO.output (outUo, addPath [] (fromFile file) ^ "\n");
       TextIO.closeOut outUo;
       (if OS.FileSys.access (modName ^ ".sig", []) then
          ()
        else
          let val outUi = TextIO.openOut (modName ^ ".ui")
          in
            TextIO.closeOut outUi
          end);
       OS.Process.success
     end
     handle IO.Io _ => OS.Process.failure)
| _ => raise Match
end

fun poly_link quietp result files =
let
  val _ = if not quietp then
            TextIO.output(TextIO.stdOut,
                          "HOLMOSMLC -o " ^ result ^ " " ^
                          String.concatWith " "
                                            (map (fn s => s ^ ".uo") files) ^
                          "\n")
          else ()
  val out = TextIO.openOut result
  fun p s =
      (TextIO.output (out, s); TextIO.output (out, "\n"))
in
  p "#!/bin/sh";
  p (protect(POLY) ^ " -q --gcthreads=1 " ^
     String.concatWith " " (envlist "POLY_CLINE_OPTIONS") ^
     " <<'__end-of-file__'");
  (if polynothol then
     (p "local";
      p "val dir = OS.FileSys.getDir();";
      p ("val _ = OS.FileSys.chDir (OS.Path.concat (\"" ^
                  String.toString Systeml.HOLDIR ^ "\", \"tools-poly\"));");
      p "val _ = use \"poly/poly-init2.ML\";";
      p "val _ = OS.FileSys.chDir dir;";
      p "in end;")
   else
     (p ("val _ = PolyML.SaveState.loadState \"" ^
         String.toString HOLSTATE ^ "\";\n")));
  p ("val _ = List.map load [" ^
                      String.concatWith ","
                                        (List.map (fn f => "\"" ^ f ^ "\"")
                                                  files) ^
                      "] handle x => ((case x of Fail s => print (s^\"\\n\") | _ => ()); OS.Process.exit OS.Process.failure);");
  p "__end-of-file__";
  TextIO.closeOut out;
  Systeml.mk_xable result;
  OS.Process.success
end
handle IO.Io _ => OS.Process.failure


datatype cmd_line = Mosml_compile of File list * string
                  | Mosml_link of string * File list
                  | Mosml_error

fun process_mosml_args c = let
  fun isSource t = OS.Path.ext t = SOME "sig" orelse OS.Path.ext t = SOME "sml"
  fun isObj t = OS.Path.ext t = SOME "uo" orelse OS.Path.ext t = SOME "ui"
  val toks = String.tokens (fn c => c = #" ") c
  val c = ref false
  val q = ref false
  val toplevel = ref false
  val obj = ref NONE
  val I = ref []
  val obj_files = ref []
  val src_file = ref NONE
  fun process_args [] = ()
    | process_args ("-c"::rest) = (c := true; process_args rest)
    | process_args ("-q"::rest) = (q := true; process_args rest)
    | process_args ("-toplevel"::rest) = (toplevel := true; process_args rest)
    | process_args ("-o"::arg::rest) = (obj := SOME arg; process_args rest)
    | process_args ("-I"::arg::rest) = (I := arg::(!I); process_args rest)
    | process_args (file::rest) = let
      in
        if file = mosml_indicator then ()
        else if isSource file then
          src_file := SOME file
        else if isObj file then
          obj_files := toFile file::(!obj_files)
        else ();
        process_args rest
      end
in
  process_args toks;
  ((case (!c, !src_file, !obj_files, !obj) of
         (true, SOME f, ofs, NONE) => Mosml_compile (List.rev ofs, f)
       | (false, NONE, ofs, SOME f) => Mosml_link (f, List.rev ofs)
       | _ => let
           fun ostring NONE = "NONE"
             | ostring (SOME s) = "SOME "^s
         in
           diag ("mosml error: c = "^Bool.toString (!c)^", src_file = "^
                 ostring (!src_file) ^ ", obj = "^ostring (!obj));
           Mosml_error
         end),
   List.rev (!I))
end;

fun run_extra_command tgt c deps = let
  open Holmake_types
  val (noecho, ignore_error, c) = process_hypat_options c
  val isHolmosmlcc =
    String.isPrefix "HOLMOSMLC-C" c orelse
    String.isPrefix (perform_substitution hmakefile_env [VREF "HOLMOSMLC-C"]) c
  val isHolmosmlc =
    String.isPrefix "HOLMOSMLC" c orelse
    String.isPrefix (perform_substitution hmakefile_env [VREF "HOLMOSMLC"]) c
  val isMosmlc =
    String.isPrefix "MOSMLC" c orelse
    String.isPrefix (perform_substitution hmakefile_env [VREF "MOSMLC"]) c
in
  if isHolmosmlcc orelse isHolmosmlc orelse isMosmlc then let
      val _ = diag ("Processing mosml build command: "^c)
    in
      case process_mosml_args (if isHolmosmlcc then " -c " ^ c else c) of
        (Mosml_compile (objs, src), I) =>
          poly_compile (noecho orelse quiet_flag) (toFile src) I (deps @ objs)
      | (Mosml_link (result, objs), I) => let
        in
          diag ("Moscow ML command is link -o "^result^" ["^
                String.concatWith ", " (map fromFile objs) ^ "]");
          poly_link (noecho orelse quiet_flag) result (map fromFileNoSuf objs)
        end
      | (Mosml_error, _) => (warn ("*** Couldn't interpret Moscow ML command: "^c);
                             OS.Process.failure)
    end
  else
    let
      fun vref_ify cmd s =
          if String.isPrefix cmd s then let
              val rest = String.extract(s, size cmd, NONE)
              val cmdq = perform_substitution hmakefile_env [VREF cmd]
            in
              SOME (cmdq ^ rest)
            end
          else NONE
      fun dovrefs cmds s =
          case cmds of
            [] => s
          | (c::cs) => (case vref_ify c s of NONE => dovrefs cs s | SOME s => s)
      (* make sure that cmds is in order of decreasing length so that
         we don't substitute for "foo", when we should be substituting for
         "foobar" *)
      val c = dovrefs ["HOLMOSMLC-C", "HOLMOSMLC", "MOSMLC", "MOSMLLEX",
                       "MOSMLYAC"] c
      val () =
          if not noecho andalso not quiet_flag then
            (TextIO.output(TextIO.stdOut, c ^ "\n");
             TextIO.flushOut TextIO.stdOut)
          else ()
      val result = Systeml.system_ps c
    in
      if not (OS.Process.isSuccess result) andalso ignore_error then
        (warn ("["^tgt^"] Error (ignored)");
         OS.Process.success)
      else result
    end
end

fun run_extra_commands tgt commands deps =
  case commands of
    [] => OS.Process.success
  | (c::cs) =>
      if OS.Process.isSuccess (run_extra_command tgt c deps) then
        run_extra_commands tgt cs deps
      else
        (tgtfatal ("*** ["^tgt^"] Error");
         OS.Process.failure)



val _ = if (debug) then let
in
  print ("HOLDIR = "^HOLDIR^"\n");
  print ("POLYMLLIBDIR = "^POLYMLLIBDIR^"\n");
  print ("Targets = [" ^ String.concatWith ", " targets ^ "]\n");
  print ("Additional includes = [" ^
         String.concatWith ", " additional_includes ^ "]\n");
  print ("Using HOL sigobj dir = "^Bool.toString (not no_sigobj) ^"\n")
end else ()

(** Top level sketch of algorithm *)
(*

   We have the following relationship --> where this arrow should be read
   "leads to the production of in one step"

    *.sml --> *.uo                          [ mosmlc -c ]
    *.sig --> *.ui                          [ mosmlc -c ]
    *Script.uo --> *Theory.sig *Theory.sml
       [ running the *Script that can be produced from the .uo file ]

   (where I have included the tool that achieves the production of the
   result in []s)

   However, not all productions can go ahead with just the one principal
   dependency present.  Sometimes other files are required to be present
   too.  We don't know which other files which are required, but we can
   find out by using Ken's holdep tool.  (This works as follows: given the
   name of the principal dependency for a production, it gives us the
   name of the other dependencies that exist in the current directory.)

   In theory, we could just run holdep everytime we were invoked, and
   with a bit of luck we'll design things so it does look as if really
   are computing the dependencies every time.  However, this is
   unnecessary work as we can cache this information in files and just
   read it in from these.  Of course, this introduces a sub-problem of
   knowing that the information in the cache files is up-to-date, so
   we will need to compare time-stamps in order to be sure that the
   cached dependency information is up to date.

   Another problem is that we might need to build a dependency DAG but
   in a situation where elements of the principal dependency chain
   were themselves out of date.
*)

fun get_implicit_dependencies incinfo (f: File) : File list = let
  val file_dependencies0 =
      get_direct_dependencies {incinfo=incinfo, extra_targets = extra_targets,
                               output_functions = outputfunctions,
                               DEPDIR=DEPDIR} f
  val file_dependencies =
      case actual_overlay of
        NONE => file_dependencies0
      | SOME s => if isSome (holdep_arg f) then
                    toFile (fullPath [SIGOBJ, s]) :: file_dependencies0
                  else
                    file_dependencies0
  fun is_thy_file (SML (Theory _)) = true
    | is_thy_file (SIG (Theory _)) = true
    | is_thy_file _                = false
in
  if is_thy_file f then let
      (* because we have to build an executable in order to build a
         theory, this build depends on all of the dependencies
         (meaning the transitive closure of the direct dependency
         relation) in their .UO form, not just .UI *)
      val get_direct_dependencies =
          get_direct_dependencies {incinfo=incinfo, extra_targets = extra_targets,
                                   output_functions = outputfunctions,
                                   DEPDIR=DEPDIR}
      fun collect_all_dependencies sofar tovisit =
          case tovisit of
            [] => sofar
          | (f::fs) => let
              val deps =
                  if OS.Path.dir (string_part f) <> "" then []
                  else
                    case f of
                      UI x => (get_direct_dependencies f @
                               get_direct_dependencies (UO x))
                    | _ => get_direct_dependencies f
              val newdeps = set_diff deps sofar
            in
              collect_all_dependencies (sofar @ newdeps)
                                       (set_union newdeps fs)
            end
      val tcdeps = collect_all_dependencies [] [f]
      val uo_deps =
          List.mapPartial (fn (UI x) => SOME (UO x) | _ => NONE) tcdeps
      val heap_deps = [Unhandled HOLSTATE]
      val alldeps = set_union (set_union tcdeps uo_deps)
                              (set_union file_dependencies heap_deps)
    in
      case f of
        SML x => let
          (* there may be theory files mentioned in the Theory.sml file that
             aren't mentioned in the script file.  If so, we are really
             dependent on these, and should add them.  They will be listed
             in the dependencies for UO (Theory x). *)
          val additional_theories =
              if exists_readable (fromFile f) then
                List.mapPartial
                  (fn (x as (UO (Theory s))) => SOME x | _ => NONE)
                  (get_implicit_dependencies incinfo (UO x))
              else []
        in
          set_union alldeps additional_theories
        end
      | _ => alldeps
    end
  else
    file_dependencies
end

fun posix_diagnostic stat = let
  open Posix.Process
in
  case fromStatus stat of
    W_EXITSTATUS w8 => "exited with code "^Word8.toString w8
  | W_EXITED => "exited normally"
  | W_SIGNALED sg => "with signal " ^
                     SysWord.toString (Posix.Signal.toWord sg)
  | W_STOPPED sg => "stopped with signal " ^
                    SysWord.toString (Posix.Signal.toWord sg)
end


fun get_explicit_dependencies (f : File) : File list =
    case (extra_deps (fromFile f)) of
      SOME deps => map toFile deps
    | NONE => []

(** Build graph *)

datatype buildcmds = Compile of File list
                   | BuildScript of string * File list

(*** Compilation of files *)
val failed_script_cache = ref (Binaryset.empty String.compare)

fun build_command (ii as {preincludes,includes}) c arg = let
  val include_flags = preincludes @ includes
  val overlay_stringl = case actual_overlay of NONE => [] | SOME s => [s]
  exception CompileFailed
  exception FileNotFound
in
  case c of
    Compile deps => let
      val file = fromFile arg
      val _ = exists_readable file orelse
              (print ("Wanted to compile "^file^", but it wasn't there\n");
               raise FileNotFound)
      val res = poly_compile true arg include_flags deps
    in
      OS.Process.isSuccess res
    end
  | BuildScript (s, deps) => let
      val _ = not (Binaryset.member(!failed_script_cache, s)) orelse
              (print ("Not re-running "^s^"Script; believe it will fail\n");
               raise CompileFailed)
      val scriptsml_file = SML (Script s)
      val scriptsml = fromFile scriptsml_file
      val script   = s^"Script"
      val scriptuo = script^".uo"
      val scriptui = script^".ui"
      open OS.Process
      (* first thing to do is to create the Script.uo file *)
      val b = build_command ii (Compile deps) scriptsml_file
      val _ = b orelse raise CompileFailed
      val _ = print ("Linking "^scriptuo^
                     " to produce theory-builder executable\n")
      val objectfiles0 =
          if allfast <> member s fastfiles
          then ["fastbuild.uo", scriptuo]
          else if quit_on_failure then [scriptuo]
          else ["holmakebuild.uo", scriptuo]
      val objectfiles0 =
        if opentheory then "loggingBossLib.uo" :: objectfiles0 else objectfiles0
      val objectfiles =
        if polynothol then
          objectfiles0
        else if interactive_flag then "holmake_interactive.uo" :: objectfiles0
        else "holmake_not_interactive.uo" :: objectfiles0
    in
      if isSuccess (poly_link true script (List.map OS.Path.base objectfiles))
      then let
        val thysmlfile = s^"Theory.sml"
        val thysigfile = s^"Theory.sig"
        fun safedelete s = FileSys.remove s handle OS.SysErr _ => ()
        val _ = app safedelete [thysmlfile, thysigfile]
        val res2 = systeml [fullPath [OS.FileSys.getDir(), script]];
        val () =
            if not (isSuccess res2) then
              (failed_script_cache := Binaryset.add(!failed_script_cache, s);
               warn ("Failed script build for "^script^" - "^
                     posix_diagnostic res2))
            else ()
        val _ = if isSuccess res2 orelse not debug then
                  app safedelete [script, scriptuo, scriptui]
                else ()
      in
        (isSuccess res2) andalso
        (exists_readable thysmlfile orelse
         (print ("Script file "^script^" didn't produce "^thysmlfile^"; \n\
                 \  maybe need export_theory() at end of "^scriptsml^"\n");
         false)) andalso
        (exists_readable thysigfile orelse
         (print ("Script file "^script^" didn't produce "^thysigfile^"; \n\
                 \  maybe need export_theory() at end of "^scriptsml^"\n");
         false))
      end
      else (print ("Failed to build script file, "^script^"\n"); false)
    end handle CompileFailed => false
             | FileNotFound => false
end

fun do_a_build_command incinfo target pdep secondaries =
  case (extra_commands (fromFile target)) of
    SOME (cs as _ :: _) =>
      OS.Process.isSuccess (run_extra_commands (fromFile target) cs secondaries)
  | _ (* i.e., NONE or SOME [] *) => let
      val build_command = build_command incinfo
    in
      case target of
         UO c           => build_command (Compile secondaries) pdep
       | UI c           => build_command (Compile secondaries) pdep
       | SML (Theory s) => build_command (BuildScript (s, secondaries)) pdep
       | SIG (Theory s) => build_command (BuildScript (s, secondaries)) pdep
       | x => raise Fail "Can't happen"
                    (* can't happen because do_a_build_command is only
                       called on targets that have primary_dependents,
                       and those are those targets of the shapes already
                       matched in the previous cases *)
    end


exception CircularDependency
exception BuildFailure
exception NotFound

fun no_full_extra_rule tgt =
    case extra_commands (fromFile tgt) of
      NONE => true
    | SOME cl => null cl

val done_some_work = ref false
val up_to_date_cache:(File, bool)Binarymap.dict ref =
  ref (Binarymap.mkDict file_compare);
fun cache_insert(f, b) =
  ((up_to_date_cache := Binarymap.insert (!up_to_date_cache, f, b));
   b)
fun make_up_to_date incinfo ctxt target = let
  val make_up_to_date = make_up_to_date incinfo
  fun print s =
    if debug then (nspaces TextIO.print (length ctxt);
                   TextIO.print s)
    else ()
  val _ = print ("Working on target: "^fromFile target^"\n")
  val pdep = primary_dependent target
  val _ = List.all (fn d => d <> target) ctxt orelse
    (warn (fromFile target ^
           " seems to depend on itself - failing to build it");
     raise CircularDependency)
  val cached_result =
    SOME (Binarymap.find (!up_to_date_cache,target))
    handle Binarymap.NotFound => NONE
  val termstr = if keep_going_flag then "" else "  Stop."
in
  if isSome cached_result then
    valOf cached_result
  else
    if OS.Path.dir (string_part target) <> "" andalso
       OS.Path.dir (string_part target) <> "." andalso
       no_full_extra_rule target
    then (* path outside of currDir *)
      if exists_readable (fromFile target) then
        (print (fromFile target ^
                " outside current directory; considered OK.\n");
         cache_insert (target, true))
      else
        (tgtfatal ("*** Remote dependency "^fromFile target^" doesn't exist."^
                   termstr);
         cache_insert (target, false))
    else if isSome pdep andalso no_full_extra_rule target then let
        val pdep = valOf pdep
      in
        if make_up_to_date (target::ctxt) pdep then let
            val secondaries =
                set_union (get_implicit_dependencies incinfo target)
                          (get_explicit_dependencies target)
            val _ =
                print ("Secondary dependencies for "^fromFile target^
                       " are: [" ^
                       String.concatWith ", " (map fromFile secondaries) ^ "\n")
          in
            if List.all (make_up_to_date (target::ctxt)) secondaries then let
                fun testthis dep =
                    fromFile dep forces_update_of fromFile target
              in
                case List.find testthis (pdep::secondaries) of
                  NONE => cache_insert (target, true)
                | SOME d => let
                  in
                    print ("Dependency: "^fromFile d^" forces rebuild\n");
                    done_some_work := true;
                    cache_insert
                        (target,
                         do_a_build_command incinfo target pdep secondaries)
                  end
              end
            else
              cache_insert (target, false)
          end
        else
          cache_insert (target, false)
      end
    else let
        val tgt_str = fromFile target
      in
        case extra_rule_for tgt_str of
          NONE => if exists_readable tgt_str then
                    (if null ctxt then
                       info ("Nothing to be done for `"^tgt_str^"'.")
                     else ();
                     cache_insert(target, true))
                  else let
                    in
                      case ctxt of
                        [] => tgtfatal ("*** No rule to make target `"^
                                        tgt_str^"'."^termstr)
                      | (f::_) => tgtfatal ("*** No rule to make target `"^
                                            tgt_str^"', needed by `"^
                                            fromFile f^"'."^termstr);
                      cache_insert(target, false)
                    end
        | SOME {dependencies, commands, ...} => let
            val _ =
                print ("Secondary dependencies for "^tgt_str^" are: [" ^
                       String.concatWith ", " dependencies ^ "]\n")
            val depfiles = map toFile dependencies
          in
            if List.all (make_up_to_date (target::ctxt)) depfiles
            then
              if not (exists_readable tgt_str) orelse
                 List.exists
                     (fn dep => dep forces_update_of tgt_str)
                     dependencies orelse
                     tgt_str in_target ".PHONY"
              then
                if null commands then
                  (if null ctxt andalso not (!done_some_work) then
                     info ("Nothing to be done for `"^tgt_str^"'.")
                   else ();
                   cache_insert(target, true))
                else let
                    val _ = done_some_work := true
                    val runresult =
                        run_extra_commands tgt_str commands
                                           (List.map toFile dependencies)
                  in
                    cache_insert(target, OS.Process.isSuccess runresult)
                  end
              else (* target is up-to-date wrt its dependencies already *)
                (if null ctxt then
                   if null commands then
                     info ("Nothing to be done for `"^tgt_str^ "'.")
                   else
                     info ("`"^tgt_str^"' is up to date.")
                 else ();
                 cache_insert(target, true))
            else (* failed to make a dependency *)
              cache_insert(target, false)
          end
      end
end handle CircularDependency => cache_insert (target, false)
         | Fail s => raise Fail s
         | OS.SysErr(s, _) => raise Fail ("Operating system error: "^s)
         | HolDepFailed => cache_insert(target, false)
         | IO.Io{function,name,cause = OS.SysErr(s,_)} =>
             raise Fail ("Got I/O exception for function "^function^
                         " with name "^name^" and cause "^s)
         | IO.Io{function,name,...} =>
               raise Fail ("Got I/O exception for function "^function^
                         " with name "^name)
         | x => raise Fail ("Got an "^exnName x^" exception, with message <"^
                            exnMessage x^"> in make_up_to_date")

(** Dealing with the command-line *)
fun do_target incinfo x = let

  fun clean_action () =
      (Holmake_tools.clean_dir {extra_cleans = extra_cleans}; true)
  fun clean_deps() = Holmake_tools.clean_depdir {depdirname = DEPDIR}
  val _ = done_some_work := false
in
  if not (member x dontmakes) then
    case extra_rule_for x of
      NONE => let
      in
        case x of
          "clean" => ((print "Cleaning directory of object files\n";
                       clean_action();
                       true) handle _ => false)
        | "cleanDeps" => clean_deps()
        | "cleanAll" => clean_action() andalso clean_deps()
        | _ => make_up_to_date incinfo [] (toFile x)
      end
    | SOME _ => make_up_to_date incinfo [] (toFile x)
  else true
end

fun stop_on_failure incinfo tgts =
    case tgts of
      [] => true
    | (t::ts) => do_target incinfo t andalso stop_on_failure incinfo ts
fun keep_going incinfo tgts = let
  fun recurse acc tgts =
      case tgts of
        [] => acc
      | (t::ts) => recurse (do_target incinfo t andalso acc) ts
in
  recurse true tgts
end
fun strategy incinfo tgts = let
  val tgts = if always_rebuild_deps then "cleanDeps" :: tgts else tgts
in
  if keep_going_flag then keep_going incinfo tgts else stop_on_failure incinfo tgts
end

val allincludes =
    cline_additional_includes @ hmake_includes

fun add_sigobj {includes,preincludes} =
    {includes = std_include_flags @ includes,
     preincludes = preincludes}

val dirinfo =
  {visited = visiteddirs,
   includes = allincludes,
   preincludes = hmake_preincludes}

val purelocal_incinfo =
    add_sigobj {includes = allincludes, preincludes = hmake_preincludes}

fun hm_recur ctgt k = let
  fun hm {dir, visited, targets} =
      Holmake {dir = dir, visited = visited} [] targets
in
  maybe_recurse
      {warn = warn,
       diag = diag,
       no_prereqs = no_prereqs, hm = hm,
       dirinfo = dirinfo,
       dir = dir,
       local_build = k, cleantgt = ctgt}
end

fun stdcont tgts ii = finish_logging (strategy (add_sigobj ii) tgts)

in
  case targets of
    [] => let
      val targets = generate_all_plausible_targets first_target
      val targets = map fromFile targets
      val _ =
        if debug then let
            val tgtstrings =
                map (fn s => if OS.FileSys.access(s, []) then s else s ^ "(*)")
                    targets
          in
            print("Generated targets are: [" ^
                  String.concatWith ", " tgtstrings ^ "]\n")
          end
        else ()
    in
      hm_recur NONE (stdcont targets)
    end
  | xs => let
      val cleanTarget_opt =
          List.find (fn x => member x ["clean", "cleanDeps", "cleanAll"]) xs
      fun canon i = hmdir.extendp {base = dir, extension = i}
    in
      if isSome cleanTarget_opt andalso not cline_recursive then
        if finish_logging (strategy purelocal_incinfo xs) then
          SOME {visited = visiteddirs,
                includes = map canon allincludes,
                preincludes = map canon hmake_preincludes}
        else NONE
      else
          hm_recur cleanTarget_opt (stdcont xs)
    end
end

in
  if show_usage then
    List.app print
    ["Holmake [targets]\n",
     "  special targets are:\n",
     "    clean                : remove all object code in directory\n",
     "    cleanDeps            : remove dependency information\n",
     "    cleanAll             : do all of above\n",
     "  additional command-line options are:\n",
     "    -I <file>            : include directory (can be repeated)\n",
     "    -d <file>            : ignore file (can be repeated)\n",
     "    -f <theory>          : toggles fast build (can be repeated)\n",
     "    -r                   : force recursion (even for cleans)\n",
     "    --d                  : print debugging information\n",
     "    --fast               : files default to fast build; -f toggles\n",
     "    --help | -h          : show this message\n",
     "    --holdir <directory> : use specified directory as HOL root\n",
     "    --holmakefile <file> : use file as Holmakefile\n",
     "    --holstate <file>    : use file as underlying \"heap\"\n",
     "    --interactive | -i   : run HOL with \"interactive\" flag set\n",
     "    --keep-going | -k    : don't stop on failure\n",
     "    --logging            : do per-theory time logging\n",
     "    --polymllibdir <dir> : use specified directory for Poly/ML's libraries\n",
     "    --poly file          : use specified file as the Poly/ML executable\n",
     "    --poly_not_hol       : Treat the Poly/ML executable as plain, not as a hol-augmented executable\n",
     "    --no_holmakefile     : don't use any Holmakefile\n",
     "    --no_overlay         : don't use an overlay file\n",
     "    --no_prereqs         : don't recursively build in INCLUDES\n",
     "    --no_sigobj | -n     : don't use any HOL files from sigobj\n",
     "    --overlay <file>     : use given .ui file as overlay\n",
     "    --ot                 : log an OpenTheory article for each theory\n",
     "    --qof                : quit on tactic failure\n",
     "    --quiet              : be quieter in operation\n",
     "    --rebuild_deps       : always rebuild dependency info files \n"]
  else let
      open OS.Process
      val result =
          Holmake {dir = hmdir.curdir(),
                   visited = Binaryset.empty hmdir.compare}
                  cline_additional_includes
                  targets
                  handle Fail s => (print ("Fail exception: "^s^"\n");
                                    exit failure)
    in
      if isSome result then exit success
      else exit failure
    end
end handle SML90.Interrupt => die_with "Holmake interrupted"
         | e => die_with ("Holmake failed with exception: "^
                          exnMessage e)

end (* struct *)

(** Local variable rubbish *)
(* local variables: *)
(* mode: sml *)
(* outline-regexp: " *(\\*\\*+" *)
(* end: *)
