(*---------------------------------------------------------------------------
     A special purpose version of make that "does the right thing" in
     single directories for building HOL theories, and accompanying
     SML libraries.
 ---------------------------------------------------------------------------*)

(* Copyright University of Cambridge, Michael Norrish, 1999-2001 *)
(* Author: Michael Norrish *)

structure Holmake =
struct

open Systeml;


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

fun normPath s = OS.Path.toString(OS.Path.fromString s)
fun itlist f L base =
   let fun it [] = base | it (a::rst) = f a (it rst) in it L end;
fun itstrings f [] = raise Fail "itstrings: empty list"
  | itstrings f [x] = x
  | itstrings f (h::t) = f h (itstrings f t);
fun fullPath slist = normPath
   (itstrings (fn chunk => fn path => OS.Path.concat (chunk,path)) slist);


val spacify =
   let fun enspace (x::(rst as _::_)) = x::" "::enspace rst
         | enspace l = l
   in String.concat o enspace
   end;

fun nspaces f n = if n <= 0 then () else (f " "; nspaces f (n - 1))

fun collapse_bslash_lines s = let
  val charlist = explode s
  fun trans [] = []
    | trans (#"\\"::(#"\n"::rest)) = trans rest
    | trans (x::xs) = x :: trans xs
in
  implode (trans charlist)
end

fun realspace_delimited_fields s = let
  open Substring
  fun inword cword words ss =
      case getc ss of
        NONE => List.rev (implode (List.rev cword) :: words)
      | SOME (c,ss') => let
        in
          case c of
            #" " => outword (implode (List.rev cword) :: words) ss'
          | #"\\" => let
            in
              case getc ss' of
                NONE => List.rev (implode (List.rev (c::cword)) :: words)
              | SOME (c',ss'') => inword (c'::cword) words ss''
            end
          | _ => inword (c::cword) words ss'
        end
  and outword words ss =
      case getc ss of
        NONE => List.rev words
      | SOME(c, ss') => let
        in
          case c of
            #" " => outword words ss'
          | _ => inword [] words ss
        end
in
  outword [] (full s)
end


local val expand_backslash =
        String.translate (fn #"\\" => "\\\\" | ch => Char.toString ch)
in
fun quote s = String.concat["\"", expand_backslash s, "\""]
end

fun exists_readable s = OS.FileSys.access(s, [OS.FileSys.A_READ])

(*---------------------------------------------------------------------------
     Support for handling the preprocessing of files containing ``
 ---------------------------------------------------------------------------*)

(* does the file have an occurrence of `` *)
fun has_dq filename = let
  val istrm = TextIO.openIn filename
  fun loop() =
    case TextIO.input1 istrm of
      NONE => false
    | SOME #"`" => (case TextIO.input1 istrm of
                      NONE => false
                    | SOME #"`" => true
                    | _ => loop())
    | _ => loop()
in
  loop() before TextIO.closeIn istrm
end

fun variant str =  (* get an unused file name in the current directory *)
 if OS.FileSys.access(str,[])
 then let fun vary i =
           let val s = str^Int.toString i
           in if OS.FileSys.access(s,[])  then vary (i+1) else s
           end
      in vary 0
      end
 else str;


(*
   Rather than continually have to deal with strings corresponding to
   file-names and mess with nasty suffixes and the like, we define a
   structured datatype into which file-names can be translated once
   and for all.
*)

(** Definition of structured file type *)

datatype CodeType
    = Theory of string
    | Script of string
    | Other of string

datatype File
    = SML of CodeType
    | SIG of CodeType
    | UO of CodeType
    | UI of CodeType
    | Unhandled of string

fun compareCodeType (Theory s1, Theory s2) = String.compare (s1, s2)
  | compareCodeType (Theory _, _) = LESS

  | compareCodeType (Script _, Theory _) = GREATER
  | compareCodeType (Script s1, Script s2) = String.compare (s1, s2)
  | compareCodeType (Script _, _) = LESS

  | compareCodeType (Other s1, Other s2) = String.compare (s1, s2)
  | compareCodeType (Other s1, _) = GREATER



fun compareFile (SML ct1, SML ct2) = compareCodeType (ct1, ct2)
  | compareFile (SML _, _) = LESS

  | compareFile (SIG _, SML _) = GREATER
  | compareFile (SIG ct1, SIG ct2) = compareCodeType (ct1, ct2)
  | compareFile (SIG _, _) = LESS

  | compareFile (UO _, SML _) = GREATER
  | compareFile (UO _, SIG _) = GREATER
  | compareFile (UO ct1, UO ct2) = compareCodeType (ct1, ct2)
  | compareFile (UO _, _) = LESS

  | compareFile (UI _, Unhandled _) = LESS
  | compareFile (UI ct1, UI ct2) = compareCodeType (ct1, ct2)
  | compareFile (UI _, _) = GREATER

  | compareFile (Unhandled s1, Unhandled s2) = String.compare (s1, s2)
  | compareFile (Unhandled _, _) = GREATER

fun string_part0 (Theory s) = s
  | string_part0 (Script s) = s
  | string_part0 (Other s) = s
fun string_part (UO c)  = string_part0 c
  | string_part (UI c)  = string_part0 c
  | string_part (SML c) = string_part0 c
  | string_part (SIG c) = string_part0 c
  | string_part (Unhandled s) = s

fun isProperSuffix s1 s2 = let
  val sz1 = size s1
  val sz2 = size s2
  open Substring
in
  if sz1 >= sz2 then NONE
  else let
    val (prefix, suffix) = splitAt(full s2, sz2 - sz1)
  in
    if string suffix = s1 then SOME (string prefix) else NONE
  end
end

fun split_file s = let
  open Substring
  val (base, ext) = splitr (fn c => c <> #".") (full s)
in
  if (size base <> 0) then
    (string (slice(base, 0, SOME (size base - 1))), string ext)
  else
    (s, "")
end

fun toCodeType s = let
  val possprefix = isProperSuffix "Theory" s
in
  if (isSome possprefix) then Theory (valOf possprefix)
  else let
    val possprefix = isProperSuffix "Script" s
  in
    if isSome possprefix then Script (valOf possprefix)
    else Other s
  end
end

fun toFile s0 =
  case split_file s0 of
    (s, "sml") => SML (toCodeType s)
  | (s, "sig") => SIG (toCodeType s)
  | (s, "uo")  => UO (toCodeType s)
  | (s, "ui")  => UI (toCodeType s)
  |    _       => Unhandled s0

fun codeToString c =
  case c of
    Theory s => s ^ "Theory"
  | Script s => s ^ "Script"
  | Other s  => s

fun fromFile f =
  case f of
    UO c  => codeToString c ^ ".uo"
  | UI c  => codeToString c ^ ".ui"
  | SIG c => codeToString c ^ ".sig"
  | SML c => codeToString c ^ ".sml"
  | Unhandled s => s

fun fromFileNoSuf f =
  case f of
    UO c  => codeToString c
  | UI c  => codeToString c
  | SIG c => codeToString c
  | SML c => codeToString c
  | Unhandled s => s


fun file_compare (f1, f2) = String.compare (fromFile f1, fromFile f2)

(*** Construct primary dependencies *)
(* Next, construct the primary dependency chain, for a given target *)
fun primary_dependent f =
    case f of
      UO c => SOME (SML c)
    | UI c => SOME (SIG c)
    | SML (Theory s) => SOME (SML (Script s))
    | SIG (Theory s) => SOME (SML (Script s))
    | _ => NONE

(*** Construction of secondary dependencies *)

fun mk_depfile_name s = fullPath [DEPDIR, s^".d"]


(* pull out a list of files that target depends on from depfile.  *)
(* All files on the right of a colon are assumed to be dependencies.
   This is despite the fact that holdep produces two entries when run
   on fooScript.sml files, one for fooScript.uo, and another for fooScript
   itself, we actually want all of those dependencies in one big chunk
   because the production of fooTheory.{sig,sml} is done as one
   atomic step from fooScript.sml. *)
fun first f [] = NONE
  | first f (x::xs) = case f x of NONE => first f xs | res => res

fun get_dependencies_from_file depfile = let
  fun get_whole_file s = let
    open TextIO
    val instr = openIn (normPath s)
  in
    inputAll instr before closeIn instr
  end
  fun parse_result s = let
    val lines = String.fields (fn c => c = #"\n") (collapse_bslash_lines s)
    fun process_line line = let
      val (lhs0, rhs0) = Substring.splitl (fn c => c <> #":")
                                          (Substring.full line)
      val lhs = Substring.string lhs0
      val rhs = Substring.string (Substring.slice(rhs0, 1, NONE))
        handle Subscript => ""
    in
      realspace_delimited_fields rhs
    end
    val result = List.concat (map process_line lines)
  in
    List.map toFile result
  end
in
  parse_result (get_whole_file depfile)
end

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

(* a function that given a product file, figures out the argument that
   should be passed to runholdep in order to get back secondary
   dependencies. *)

fun holdep_arg (UO c) = SOME (SML c)
  | holdep_arg (UI c) = SOME (SIG c)
  | holdep_arg (SML (Theory s)) = SOME (SML (Script s))
  | holdep_arg (SIG (Theory s)) = SOME (SML (Script s))
  | holdep_arg _ = NONE

(**** get dependencies from file *)



(** Command line parsing *)

(*** list functions *)
fun butlast0 _ [] = raise Fail "butlast - empty list"
  | butlast0 acc [x] = List.rev acc
  | butlast0 acc (h::t) = butlast0 (h::acc) t
fun butlast l = butlast0 [] l

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
fun alltrue [] = true
  | alltrue (x::xs) = x andalso alltrue xs
fun print_list0 [] = "]"
  | print_list0 [x] = x^"]"
  | print_list0 (x::xs) = x^", "^print_list0 xs
fun print_list l = "["^print_list0 l
fun I x = x

(*** parse command line *)
fun includify [] = []
  | includify (h::t) = "-I" :: h :: includify t

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
  val (rem, debug) = find_toggle "--debug" rem
  val (rem, help) = find_alternative_tags  ["--help", "-h"] rem
  val (rem, rebuild_deps) = find_alternative_tags ["--rebuild_deps","-r"] rem
  val (rem, cmdl_HOLDIRs) = find_pairs "--holdir" rem
  val (rem, no_sigobj) = find_alternative_tags ["--no_sigobj", "-n"] rem
  val (rem, allfast) = find_toggle "--fast" rem
  val (rem, fastfiles) = find_pairs "-f" rem
  val (rem, qofp) = find_toggle "--qof" rem
  val (rem, no_hmakefile) = find_toggle "--no_holmakefile" rem
  val (rem, no_prereqs) = find_toggle "--no_prereqs" rem
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

  val (rem, cmdl_POLYs) = find_pairs "--poly" rem
  val (rem, polynothol) = find_toggle "--poly_not_hol" rem
in
  {targets=rem, debug=debug, show_usage=help,
   always_rebuild_deps=rebuild_deps,
   additional_includes=includes,
   dontmakes=dontmakes, no_sigobj = no_sigobj,
   quit_on_failure = qofp, no_prereqs = no_prereqs,
   no_hmakefile = no_hmakefile,
   allfast = allfast, fastfiles = fastfiles,
   user_hmakefile = user_hmakefile,
   no_overlay = no_overlay,
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
   cmdl_POLY =
     case cmdl_POLYs of
       [] => NONE
     | [x] => SOME x
     | _ => let
       in
         warn "Ignoring all but last --poly spec.";
         SOME (List.last cmdl_POLYs)
       end,
   polynothol = polynothol,
   keep_going_flag = keep_going_flag,
   quiet_flag = quiet_flag,
   do_logging_flag = do_logging_flag}
end


(* parameters which vary from run to run according to the command-line *)
val {targets, debug, dontmakes, show_usage, allfast, fastfiles,
     always_rebuild_deps, interactive_flag,
     additional_includes = cline_additional_includes,
     cmdl_HOLDIR, cmdl_POLYMLLIBDIR, cmdl_POLY, polynothol,
     no_sigobj = cline_no_sigobj, no_prereqs,
     quit_on_failure, no_hmakefile, user_hmakefile, no_overlay,
     user_overlay, keep_going_flag, quiet_flag, do_logging_flag} =
  parse_command_line (CommandLine.arguments())

fun warn s = if not quiet_flag then
               (TextIO.output(TextIO.stdErr, execname^": "^s^"\n");
                TextIO.flushOut TextIO.stdErr)
             else ()
fun info s = if not quiet_flag then print (execname^": "^s^"\n") else ()
fun tgtfatal s = (TextIO.output(TextIO.stdErr, execname^": "^s^"\n");
                  TextIO.flushOut TextIO.stdErr)


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
val POLY =  case cmdl_POLY of NONE => fullPath [HOLDIR, "bin", "hol.builder"] | SOME s => s
(*val MOSMLCOMP = fullPath [HOLDIR, "tools-poly/polymlc"]*)
val SIGOBJ    = normPath(OS.Path.concat(HOLDIR, "sigobj"));

val UNQUOTER  = xable_string(fullPath [HOLDIR, "bin/unquote"])
fun has_unquoter() = OS.FileSys.access(UNQUOTER, [OS.FileSys.A_EXEC])
fun unquote_to file1 file2 = SYSTEML [UNQUOTER, file1, file2]

  (*
fun compile debug args = let
  val _ = if debug then print ("  with command "^
                               spacify(MOSMLCOMP::args)^"\n")
          else ()
in
  SYSTEML (MOSMLCOMP::args)
end;
*)

fun die_with message = let
  open TextIO
in
  output(stdErr, message ^ "\n");
  flushOut stdErr;
  OS.Process.exit OS.Process.failure
end

fun base_environment s = let
  open Holmake_types
  val p = Systeml.protect
in
  case s of
    "HOLDIR" => [LIT HOLDIR]
  | "SIGOBJ" => [VREF "HOLDIR", LIT "/sigobj"]
  | "POLYMLLIBDIR" => [LIT POLYMLLIBDIR]
(*  | "MOSMLCOMP" => [VREF "protect $(HOLDIR)/tools-poly/polymlc"]*)
  | "MOSMLLEX" => [VREF "protect $(POLYMLDIR)/mosmllex"]
  | "MOSMLYAC" => [VREF "protect $(POLYMLDIR)/mosmlyac"]
  | "UNQUOTE" => [VREF ("protect $(HOLDIR)/" ^ xable_string "/bin/unquote")]
  | "MV" => if Systeml.OS = "winNT" then [LIT "rename"] else [LIT "/bin/mv"]
  | "CP" => if Systeml.OS = "winNT" then [LIT "copy /b"] else [LIT "/bin/cp"]
  | _ => (case OS.Process.getEnv s of
            NONE => [LIT ""]
          | SOME v => [LIT v])
end

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
fun Holmake visiteddirs cline_additional_includes dir targets = let
  val _ = OS.FileSys.chDir dir


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

val hmakefile_toks =
  if exists_readable hmakefile andalso not no_hmakefile
  then let
      val () = if debug then
                print ("Reading additional information from "^hmakefile^"\n")
              else ()
    in
      ReadHMF.read hmakefile
    end
  else []

val hmakefile_env0 = Holmake_types.extend_env hmakefile_toks base_environment
val envlist = envlist hmakefile_env0

val hmake_includes = envlist "INCLUDES"
val hmake_options = envlist "OPTIONS"
val additional_includes =
  includify (remove_duplicates (cline_additional_includes @ hmake_includes))

val hmake_preincludes = includify (envlist "PRE_INCLUDES")
val hmake_no_overlay = member "NO_OVERLAY" hmake_options
val hmake_no_sigobj = member "NO_SIGOBJ" hmake_options
val hmake_qof = member "QUIT_ON_FAILURE" hmake_options
val hmake_noprereqs = member "NO_PREREQS" hmake_options
val extra_cleans = envlist "EXTRA_CLEANS"

val quit_on_failure = quit_on_failure orelse hmake_qof
val no_prereqs = no_prereqs orelse hmake_noprereqs
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

val std_include_flags = if no_sigobj then [] else ["-I", SIGOBJ]

val hmakefile_env = let
  open Holmake_types
  val addincludes = spacify (map Systeml.protect additional_includes)
  val stdincludes =
      spacify (map Systeml.protect (hmake_preincludes @ std_include_flags)) ^
      " " ^ addincludes
in
  (fn s =>
      case s of
        "HOLMOSMLC" => [VREF "MOSMLCOMP", LIT (" -q "^stdincludes)]
      | "HOLMOSMLC-C" => let
          val overlaystring = case actual_overlay of NONE => "" | SOME s => s
        in
          [VREF "MOSMLCOMP", LIT (" -q "^stdincludes^" -c "^overlaystring)]
        end
      | "MOSMLC" => [VREF "MOSMLCOMP", LIT (" "^addincludes)]
      | _ => hmakefile_env0 s)
end

val (first_target, extra_rules) =
    Holmake_types.mk_rules warn hmakefile_toks hmakefile_env

fun extra_deps t = Option.map #dependencies (Binarymap.peek(extra_rules, t))

fun extra_commands t = Option.map #commands (Binarymap.peek(extra_rules, t))

val extra_targets = Binarymap.foldr (fn (k,_,acc) => k::acc) [] extra_rules

fun extra_rule_for t = Binarymap.peek(extra_rules, t)

(* treat targets as sets *)
infix in_target
fun (s in_target t) = case extra_deps t of NONE => false | SOME l => member s l

fun addPath I file =
  if OS.Path.isAbsolute file then
    file
  else
    let val p = List.find (fn p =>
                            OS.FileSys.access (OS.Path.concat (p, file ^ ".ui"), []))
                          (OS.FileSys.getDir() :: I)
    in
      case p of
           NONE => OS.Path.concat (OS.FileSys.getDir(), file)
         | SOME p => OS.Path.concat (p, file)
    end;

fun poly_compile file I deps =
let val modName = fromFileNoSuf file
    val depMods = List.map (addPath I o fromFileNoSuf) deps
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
end

fun poly_link result files =
let val out = TextIO.openOut result
    fun p s =
      (TextIO.output (out, s); TextIO.output (out, "\n"))
in
  p "#!/bin/sh";
  p (POLY ^ "<<'__end-of-file__'");
  p "val _ = PolyML.Compiler.prompt1:=\"\";";
  p "val _ = PolyML.Compiler.prompt2:=\"\";";
  p "val _ = PolyML.print_depth 0;";
  (if polynothol then
     (p "local";
      p "val dir = OS.FileSys.getDir();";
      p ("val _ = OS.FileSys.chDir (OS.Path.concat (\"" ^
                  String.toString Systeml.HOLDIR ^ "\", \"tools-poly\"));");
      p "val _ = use \"poly/poly-init2.ML\";";
      p "val _ = OS.FileSys.chDir dir;";
      p "in end;")
   else
     ());
  p ("val _ = List.map load [" ^
                      String.concatWith ","
                                        (List.map (fn f => "\"" ^ f ^ "\"")
                                                  files) ^
                      "] handle x => ((case x of Fail s => print (s^\"\\n\") | _ => ()); OS.Process.exit OS.Process.failure);");
  p "__end-of-file__";
  TextIO.closeOut out;
  OS.Process.success
end
handle IO.Io _ => OS.Process.failure


datatype cmd_line = Mosml_compile of string list * string
                  | Mosml_link of string * string list
                  | Mosml_error

fun process_mosml_args c =
let fun isSource t = OS.Path.ext t = SOME "sig" orelse
                     OS.Path.ext t = SOME "sml";
    fun isObj t = OS.Path.ext t = SOME "uo" orelse
                  OS.Path.ext t = SOME "ui";
    val toks = String.tokens (fn c => c = #" ") c
    val c = ref false
    val q = ref false
    val toplevel = ref false
    val obj = ref NONE
    val I = ref []
    val obj_files = ref []
    val src_file = ref NONE;
    fun process_args [] = ()
      | process_args ("-c"::rest) =
          (c := true; process_args rest)
      | process_args ("-q"::rest) =
          (q := true; process_args rest)
      | process_args ("-toplevel"::rest) =
          (toplevel := true; process_args rest)
      | process_args ("-o"::arg::rest) =
          (obj := SOME arg; process_args rest)
      | process_args ("-I"::arg::rest) =
          (I := arg::(!I); process_args rest)
      | process_args (file::rest) =
          ((if isSource file then
              src_file := SOME file
            else if isObj file then
              obj_files := (OS.Path.base file)::(!obj_files)
            else
              ());
           process_args rest);
in
  process_args toks;
  ((case (!c, !src_file, !obj_files, !obj) of
         (true, SOME f, ofs, NONE) => Mosml_compile (List.rev ofs, f)
       | (false, NONE, ofs, SOME f) => Mosml_link (f, List.rev ofs)
       | _ => Mosml_error),
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
  if isHolmosmlcc orelse isHolmosmlc orelse isMosmlc then
    case process_mosml_args (if isHolmosmlcc then " -c " ^ c else c) of
         (Mosml_compile (objs, src), I) =>
           poly_compile (toFile src) I (deps@(List.map toFile objs))
       | (Mosml_link (result, objs), I) => poly_link result objs
       | (Mosml_error, _) => OS.Process.failure
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
  print ("Targets = "^print_list targets^"\n");
  print ("Additional includes = "^print_list additional_includes^"\n");
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

(** Construction of the dependency graph
    ------------------------------------

   The first thing to do is to define a type that will store our
   dependency graph:

*)

(**** runholdep *)
(* The primary dependency chain does not depend on anything in the
   file-system; it always looks the same.  However, additional
   dependencies depend on what holdep tells us.  This function that
   runs holdep, and puts the output into specified file, which will live
   in DEPDIR somewhere. *)

exception HolDepFailed
fun runholdep arg destination_file = let
  open Mosml
  val _ = print ("Analysing "^fromFile arg^"\n")
  fun buildables s = let
    val f = toFile s
    val files =
        case f of
          SML (ss as Script t) => [UI ss, UO ss, SML (Theory t),
                                   SIG (Theory t), UI (Theory t),
                                   UO (Theory t), f]
        | SML ss => [UI ss, UO ss, f]
        | SIG ss => [UI ss, f]
        | x => [x]
  in
    map fromFile files
  end
  val buildable_extras = List.concat (map buildables extra_targets)
  val result =
    Success(Holdep.main buildable_extras debug
                        (hmake_preincludes @ std_include_flags @
                         additional_includes @ [fromFile arg]))
    handle _ => (print "Holdep failed.\n"; Failure "")
  fun myopen s =
    if OS.FileSys.access(DEPDIR, []) then
      if OS.FileSys.isDir DEPDIR then TextIO.openOut s
      else die_with ("Want to put dependency information in directory "^
                     DEPDIR^", but it already exists as a file")
    else
     (print ("Trying to create directory "^DEPDIR^" for dependency files\n");
      OS.FileSys.mkDir DEPDIR;
      TextIO.openOut s
     )
  fun write_result_to_file s = let
    open TextIO
    val destin = normPath destination_file
    (* val _ = print ("destination: "^quote destin^"\n") *)
    val outstr = myopen destin
  in
    output(outstr, s);
    closeOut outstr
  end
in
  case result of
    Success s => write_result_to_file s
  | Failure s => raise HolDepFailed
end

fun get_direct_dependencies (f : File) : File list = let
  val fname = fromFile f
  val arg = holdep_arg f  (* arg is file to analyse for dependencies *)
in
  if isSome arg then let
    val arg = valOf arg
    val argname = fromFile arg
    val depfile = mk_depfile_name argname
    val _ =
      if argname forces_update_of depfile then
        runholdep arg depfile
      else ()
    val phase1 =
      (* circumstances can arise in which the dependency file won't be
         built, and won't exist; mainly because the file we're trying to
         compute dependencies for doesn't exist either.  In this case, we
         can only return the empty list *)
      if exists_readable depfile then
        get_dependencies_from_file depfile
      else
        []
  in
    case f of
      UO x =>
        if OS.FileSys.access(fromFile (SIG x), []) andalso
           List.all (fn f => f <> SIG x) phase1
        then
          UI x :: phase1
        else
          phase1
    | _ => phase1
  end
  else
    []
end

fun get_implicit_dependencies (f: File) : File list = let
  val file_dependencies0 = get_direct_dependencies f
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
      val alldeps = set_union (set_union tcdeps uo_deps) file_dependencies
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
                  (get_implicit_dependencies (UO x))
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

(*** Pre-processing of files that use `` *)


(*** Compilation of files *)
val failed_script_cache = ref (Binaryset.empty String.compare)

fun build_command c arg = let
  val include_flags = hmake_preincludes @ std_include_flags @
                      additional_includes
  val include_flags = List.filter (fn x => not (x = "-I")) include_flags
 (*  val include_flags = ["-I",SIGOBJ] @ additional_includes *)
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
      val _ = print ("Compiling "^file^"\n")
      open OS.Process
      val res =
          if has_unquoter() then let
              (* force to always use unquoter if present, so as to generate
                 location pragmas. Must test for existence, for bootstrapping.
              *)
              val clone = variant file
              val _ = OS.FileSys.rename {old=file, new=clone}
              fun revert() =
                  if OS.FileSys.access (clone, [OS.FileSys.A_READ]) then
                    (OS.FileSys.remove file handle _ => ();
                     OS.FileSys.rename{old=clone, new=file})
                  else ()
            in
              (if OS.Process.isSuccess (unquote_to clone file)
                  handle e => (revert();
                               print ("Unquoting "^file^
                                      " raised exception\n");
                               raise CompileFailed)
               then
                 poly_compile arg include_flags deps before revert()
               else (print ("Unquoting "^file^" ran and failed\n");
                     revert();
                     raise CompileFailed))
              handle CompileFailed => raise CompileFailed
                   | e => (revert();
                           print("Unable to compile: "^file^
                                 " - raised exception "^exnName e^"\n");
                           raise CompileFailed)
            end
          else poly_compile arg include_flags deps
     in
        isSuccess res
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
      val b = build_command (Compile deps) scriptsml_file
      val _ = b orelse raise CompileFailed
      val _ = print ("Linking "^scriptuo^
                     " to produce theory-builder executable\n")
      val objectfiles0 =
          if allfast andalso not (member s fastfiles) orelse
             not allfast andalso member s fastfiles
          then ["fastbuild.uo", scriptuo]
          else if quit_on_failure then [scriptuo]
          else ["holmakebuild.uo", scriptuo]
      val objectfiles =
        if polynothol then
          objectfiles0
        else if interactive_flag then "holmake_interactive.uo" :: objectfiles0
        else "holmake_not_interactive.uo" :: objectfiles0
    in
      if isSuccess (poly_link script (List.map OS.Path.base objectfiles))
      then let
        val script' = Systeml.mk_xable script
        val thysmlfile = s^"Theory.sml"
        val thysigfile = s^"Theory.sig"
        val _ =
          app (fn s => OS.FileSys.remove s handle OS.SysErr _ => ())
          [thysmlfile, thysigfile]
        val res2 = systeml [fullPath [OS.FileSys.getDir(), script']];
        val _ = app OS.FileSys.remove [script', scriptuo, scriptui]
        val () =
            if not (isSuccess res2) then
              (failed_script_cache := Binaryset.add(!failed_script_cache, s);
               warn ("Failed script build for "^script^" - "^
                     posix_diagnostic res2))
            else ()
      in
        (isSuccess res2) andalso
        (exists_readable thysmlfile orelse
         (print ("Script file "^script'^" didn't produce "^thysmlfile^"; \n\
                 \  maybe need export_theory() at end of "^scriptsml^"\n");
         false)) andalso
        (exists_readable thysigfile orelse
         (print ("Script file "^script'^" didn't produce "^thysigfile^"; \n\
                 \  maybe need export_theory() at end of "^scriptsml^"\n");
         false))
      end
      else (print ("Failed to build script file, "^script^"\n"); false)
    end handle CompileFailed => false
             | FileNotFound => false
end

fun do_a_build_command target pdep secondaries =
  case (extra_commands (fromFile target)) of
    SOME (cs as _ :: _) =>
      OS.Process.isSuccess (run_extra_commands (fromFile target) cs secondaries)
  | _ (* i.e., NONE or SOME [] *) => let
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
  ref (Binarymap.mkDict compareFile);
fun cache_insert(f, b) =
  ((up_to_date_cache := Binarymap.insert (!up_to_date_cache, f, b));
   b)
fun make_up_to_date ctxt target = let
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
in
  if isSome cached_result then
    valOf cached_result
  else
   if OS.Path.dir (string_part target) <> "" then (* path outside of currDir *)
     (print (fromFile target ^" outside current directory; considered OK.\n");
      cache_insert (target, true))
    else
      if isSome pdep andalso no_full_extra_rule target then let
        val pdep = valOf pdep
      in
        if make_up_to_date (target::ctxt) pdep then let
          val secondaries = set_union (get_implicit_dependencies target)
                                      (get_explicit_dependencies target)
          val _ =
            (print ("Secondary dependencies for "^fromFile target^" are: ");
             print (print_list (map fromFile secondaries) ^ "\n"))
        in
          if List.all (make_up_to_date (target::ctxt)) secondaries then
            if (List.exists
                (fn dep =>
                 (fromFile dep) forces_update_of (fromFile target))
                (pdep::secondaries))
            then
              (done_some_work := true;
               cache_insert (target,
                             do_a_build_command target pdep secondaries))
            else
              cache_insert (target, true)
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
                        val termstr = if keep_going_flag then ""
                                      else "  Stop."
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
                  (print ("Secondary dependencies for "^tgt_str^" are: ");
                   print (print_list dependencies ^ "\n"))
              val depfiles = map toFile dependencies
            in
              if List.all (make_up_to_date (target::ctxt)) depfiles
              then
                if not (exists_readable tgt_str) orelse
                   List.exists
                     (fn dep => dep forces_update_of tgt_str)
                     dependencies orelse
                   List.exists (not o exists_readable) dependencies orelse
                   tgt_str in_target ".PHONY"
                then
                  if null commands then
                    (if null ctxt andalso not (!done_some_work) then
                       info ("Nothing to be done for `"^tgt_str^"'.")
                     else ();
                     cache_insert(target, true))
                  else
                    cache_insert(target,
                                 (done_some_work := true;
                                  OS.Process.isSuccess (run_extra_commands tgt_str
                                                     commands
                                                     (List.map toFile
                                                     dependencies))))
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

exception DirNotFound

(** Dealing with the command-line *)
fun do_target x = let
  fun read_files ds P action =
     case OS.FileSys.readDir ds
      of NONE => OS.FileSys.closeDir ds
       | SOME nextfile =>
           (if P nextfile then action nextfile else ();
            read_files ds P action)

  fun clean_action () = let
    val cdstream = OS.FileSys.openDir "."
    fun to_delete f =
      case (toFile f) of
        UO _ => true
      | UI _ => true
      | SIG (Theory _) => true
      | SML (Theory _) => true
      | _ => false
    fun quiet_remove s = OS.FileSys.remove s handle e => ()
  in
    read_files cdstream to_delete quiet_remove;
    app quiet_remove extra_cleans;
    true
  end
  fun clean_deps() = let
    val depds = OS.FileSys.openDir DEPDIR handle
      OS.SysErr _ => raise DirNotFound
  in
    read_files depds
               (fn _ => true)
               (fn s => OS.FileSys.remove (fullPath [DEPDIR, s]));
    OS.FileSys.rmDir DEPDIR;
    true
  end handle OS.SysErr (mesg, _) => let
             in
                print ("make cleanDeps failed with message: "^mesg^"\n");
                false
             end
           | DirNotFound => true
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
        | _ => make_up_to_date [] (toFile x)
      end
    | SOME _ => make_up_to_date [] (toFile x)
  else true
end

fun generate_all_plausible_targets () = let
  val extra_targets = case first_target of NONE => [] | SOME s => [toFile s]
  fun find_files ds P =
    case OS.FileSys.readDir ds of
      NONE => (OS.FileSys.closeDir ds; [])
    | SOME fname => if P fname then fname::find_files ds P
                               else find_files ds P
  val cds = OS.FileSys.openDir "."
  fun not_a_dot f = not (String.isPrefix "." f)
  fun ok_file f =
    case (toFile f) of
      SIG _ => true
    | SML _ => true
    | _ => false
  val src_files = find_files cds (fn s => ok_file s andalso not_a_dot s)
  fun src_to_target (SIG (Script s)) = UO (Theory s)
    | src_to_target (SML (Script s)) = UO (Theory s)
    | src_to_target (SML s) = (UO s)
    | src_to_target (SIG s) = (UO s)
    | src_to_target _ = raise Fail "Can't happen"
  val initially = map (src_to_target o toFile) src_files @ extra_targets
  fun remove_sorted_dups [] = []
    | remove_sorted_dups [x] = [x]
    | remove_sorted_dups (x::y::z) = if x = y then remove_sorted_dups (y::z)
                                     else x :: remove_sorted_dups (y::z)
in
  remove_sorted_dups (Listsort.sort file_compare initially)
end


fun stop_on_failure tgts =
    case tgts of
      [] => true
    | (t::ts) => do_target t andalso stop_on_failure ts
fun keep_going tgts = let
  fun recurse acc tgts =
      case tgts of
        [] => acc
      | (t::ts) => recurse (do_target t andalso acc) ts
in
  recurse true tgts
end
fun strategy tgts = let
  val tgts = if always_rebuild_deps then "cleanDeps" :: tgts else tgts
in
  if keep_going_flag then keep_going tgts else stop_on_failure tgts
end

fun maybe_recurse k = let
  fun recurse visited (newdir,nm) =
      if Binaryset.member(visited, newdir) then SOME visited
      else let
          val _ = warn ("Recursively calling Holmake in "^nm)
        in
          Holmake visited [] newdir []
          before
          OS.FileSys.chDir dir
        end
  fun do_em accg [] = if k() then SOME accg else NONE
    | do_em accg (x::xs) = let
      in
        case recurse accg x of
          SOME g' => do_em g' xs
        | NONE => NONE
      end
  val visited = Binaryset.add(visiteddirs, dir)
in
  if no_prereqs then
    if k() then SOME visited else NONE
  else let
      fun foldthis (dir, m) =
          Binarymap.insert(m, OS.FileSys.fullPath dir, dir)
      val possible_calls = List.foldr foldthis
                                      (Binarymap.mkDict String.compare)
                                      (cline_additional_includes @
                                       envlist "PRE_INCLUDES" @
                                       hmake_includes)
    in
      do_em visited (Binarymap.listItems possible_calls)
    end
end

in
  case targets of
    [] => let
      val targets = generate_all_plausible_targets ()
      val _ =
        if debug then
        print("Generated targets are: "^print_list (map fromFile targets)^"\n")
        else ()
    in
      maybe_recurse
          (fn () => finish_logging (strategy  (map (fromFile) targets)))
    end
  | xs => let
      fun isPhony x = member x ["clean", "cleanDeps", "cleanAll"] orelse
                      x in_target ".PHONY"
    in
      if List.all isPhony xs then
        if finish_logging (strategy xs) then SOME visiteddirs else NONE
      else maybe_recurse (fn () => finish_logging (strategy xs))
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
     "    --debug              : print debugging information\n",
     "    --fast               : files default to fast build; -f toggles\n",
     "    --help | -h          : show this message\n",
     "    --holdir <directory> : use specified directory as HOL root\n",
     "    --holmakefile <file> : use file as Holmakefile\n",
     "    --interactive | -i   : run HOL with \"interactive\" flag set\n",
     "    --keep-going | -k    : don't stop on failure\n",
     "    --logging            : do per-theory time logging\n",
     "    --polymllibdir directory : use specified directory for Poly/ML's libraries\n",
     "    --poly file          : use specified file as the Poly/ML executable\n",
     "    --poly_not_hol       : Treat the Poly/ML executable as plain, not as a hol-augmented executable",
     "    --no_holmakefile     : don't use any Holmakefile\n",
     "    --no_overlay         : don't use an overlay file\n",
     "    --no_prereqs         : don't recursively build in INCLUDES\n",
     "    --no_sigobj | -n     : don't use any HOL files from sigobj\n",
     "    --overlay <file>     : use given .ui file as overlay\n",
     "    --qof                : quit on tactic failure\n",
     "    --quiet              : be quieter in operation\n",
     "    --rebuild_deps | -r  : always rebuild dependency info files \n"]
  else let
      open OS.Process
      val result =
          Holmake (Binaryset.empty String.compare)
                  cline_additional_includes
                  (OS.FileSys.getDir())
                  targets
                  handle Fail s => (print ("Fail exception: "^s^"\n");
                                    exit failure)
    in
      if isSome result then exit success
      else exit failure
    end
end

end (* struct *)

(** Local variable rubbish *)
(* local variables: *)
(* mode: sml *)
(* outline-regexp: " *(\\*\\*+" *)
(* end: *)
