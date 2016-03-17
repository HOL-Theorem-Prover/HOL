structure buildutils :> buildutils =
struct

structure Path = OS.Path
structure FileSys = OS.FileSys
structure Process = OS.Process


(* path manipulation functions *)
fun normPath s = Path.toString(Path.fromString s)
fun itstrings f [] = raise Fail "itstrings: empty list"
  | itstrings f [x] = x
  | itstrings f (h::t) = f h (itstrings f t);
fun fullPath slist = normPath
   (itstrings (fn chunk => fn path => Path.concat (chunk,path)) slist);

fun quote s = String.concat["\"", s, "\""];

(* message emission *)
fun die s =
    let open TextIO
    in
      output(stdErr, s ^ "\n");
      flushOut stdErr;
      Process.exit Process.failure
    end
fun warn s = let open TextIO in output(stdErr, s ^ "\n"); flushOut stdErr end;
fun I x = x

(* values from the Systeml structure, which is created at HOL configuration
   time *)
val OS = Systeml.OS;
val HOLDIR = Systeml.HOLDIR
val EXECUTABLE = Systeml.xable_string (fullPath [HOLDIR, "bin", "build"])
val DEPDIR = Systeml.DEPDIR
val GNUMAKE = Systeml.GNUMAKE
val DYNLIB = Systeml.DYNLIB

fun SYSTEML clist = Process.isSuccess (Systeml.systeml clist)

val dfltbuildseq = fullPath [HOLDIR, "tools", "build-sequence"]

val help_mesg = let
  val istrm = TextIO.openIn (fullPath [HOLDIR, "tools", "buildhelp.txt"])
in
  TextIO.inputAll istrm before TextIO.closeIn istrm
end handle IO.Io _ => "\n\n<Build help file missing in action>\n\n"

fun exit_with_help() =
    (print help_mesg ; Process.exit Process.success)

fun read_buildsequence {kernelname} bseq_fname = let
  val kernelpath = fullPath [HOLDIR, "src",
    case kernelname of
        "-stdknl" => "0"
      | "-expk" => "experimental-kernel"
      | "-otknl" => "logging-kernel"
      | _ => die ("Bad kernelname: "^kernelname)
    ]
  val readline = TextIO.inputLine
  fun read_file acc visitedincludes (f as (fstr,fname)) oldstreams =
      case readline fstr of
        NONE =>
        let
          val _ = TextIO.closeIn fstr
        in
          case oldstreams of
              h::t => read_file acc visitedincludes h t
            | [] => List.rev acc
        end
      | SOME s => let
          (* drop trailing and leading whitespace *)
          val ss = Substring.full s
          val ss = Substring.dropl Char.isSpace ss
          val ss = Substring.dropr Char.isSpace ss

          (* drop trailing comment *)
          val (hashpfx, hashsfx) = Substring.position "#" ss
          fun skip() = read_file acc visitedincludes f oldstreams
        in
          if Substring.size hashpfx = 0 then
            if Substring.isPrefix "#include " hashsfx then
              let
                val includefname =
                    Substring.string
                      (Substring.slice(hashsfx, size "#include ", NONE))
                val includefname_opt =
                    SOME (OS.Path.mkAbsolute
                            { path = includefname,
                              relativeTo = fullPath [HOLDIR, "tools"]})
                    handle OS.Path.Path => NONE
              in
                case includefname_opt of
                    NONE => (warn ("Ignoring bad #include: " ^ includefname);
                             skip())
                  | SOME includefname =>
                    let
                      val includefname = OS.Path.mkCanonical includefname
                        (* necessary if user specified a non-canonical absolute
                           path *)
                    in
                      if Binaryset.member(visitedincludes, includefname) then
                        die ("Recursive request to #include "^
                             includefname ^ "(in "^fname^")")
                      else let
                        val newstr_opt = SOME (TextIO.openIn includefname)
                                         handle IO.Io _ => NONE
                      in
                        case newstr_opt of
                            SOME strm =>
                            read_file acc
                                      (Binaryset.add(visitedincludes,
                                                     includefname))
                                      (strm,includefname)
                                      ((fstr,includefname)::oldstreams)
                          | NONE => die ("Couldn't open #include-d file "^
                                         includefname ^
                                         "(included from "^fname^")")
                      end
                    end
              end
            else skip()
          else
            let
              val s = Substring.string hashpfx
              fun extract_testcount (s,acc) =
                  if String.sub(s,0) = #"!" then
                    extract_testcount (String.extract(s,1,NONE), acc+1)
                  else (s,acc)
              fun extract_brackets name l r s =
                  if String.sub(s,0) = l then let
                      fun grabsys i =
                          if String.sub(s,i) = r then
                            (String.substring(s,1,i-1),
                             String.extract(s,i+1,NONE))
                          else grabsys (i + 1)
                    in
                      grabsys 1
                      handle Subscript =>
                             die ("Malformed "^name^" spec: "^s^
                                  "  (from "^fname^")")
                    end
                  else ("", s)
              val extract_mlsys = extract_brackets "system" #"[" #"]"
              val extract_kernel = extract_brackets "kernel" #"(" #")"
              val (mlsys,s) = extract_mlsys s
              val (knl,s) = extract_kernel s
              val (dirname0,testcount) = extract_testcount (s,0)
              val dirname =
                  if dirname0 = "**KERNEL**" then kernelpath
                  else if Path.isAbsolute dirname0 then dirname0
                  else fullPath [HOLDIR, dirname0]
              open FileSys
            in
              if (mlsys = "" orelse mlsys = Systeml.ML_SYSNAME) andalso
                 (knl = "" orelse ("-"^knl) = kernelname) then
                if access (dirname, [A_READ, A_EXEC]) then
                  if isDir dirname orelse mlsys <> "" then
                    read_file ((dirname,testcount)::acc)
                              visitedincludes
                              f
                              oldstreams
                  else
                    die ("** File "^dirname0^
                         " from build sequence file "^fname^
                         " is not a directory")
                else die ("** File "^s^" from build sequence file "^fname^
                          " does not \
                          \exist or is inacessible -- skipping it")
              else read_file acc visitedincludes f oldstreams
            end
        end
  val bseq_file =
      TextIO.openIn bseq_fname
      handle IO.Io _ => die ("Fatal error: couldn't open sequence file: "^
                             bseq_fname)
in
  read_file [] (Binaryset.empty String.compare) (bseq_file,bseq_fname) []
end

fun cline_selftest cmdline = let
  fun find_slftests (cmdline,counts,resulting_cmdline) =
      case cmdline of
        [] => (counts, List.rev resulting_cmdline)
      | h::t => if h = "-selftest" then
                  case t of
                    [] => (1::counts, List.rev resulting_cmdline)
                  | h'::t' => let
                    in
                      case Int.fromString h' of
                        NONE => find_slftests (t, 1::counts,
                                               resulting_cmdline)
                      | SOME i => if i < 0 then
                                    (warn("** Ignoring negative number spec\
                                          \ification of test level");
                                     find_slftests(t', counts,
                                                   resulting_cmdline))
                                  else
                                    find_slftests (t', i::counts,
                                                   resulting_cmdline)
                    end
                else find_slftests (t, counts, h::resulting_cmdline)
  val (selftest_counts, new_cmdline) = find_slftests (cmdline, [], [])
in
  case selftest_counts of
    [] => (0, new_cmdline)
  | [h] => (h, new_cmdline)
  | h::t => (warn ("** Ignoring all but last -selftest spec; result is \
                   \selftest level "^Int.toString h);
             (h, new_cmdline))
end



val option_filename = fullPath [HOLDIR, "tools", "lastbuildoptions"]

fun read_earlier_options reader = let
  val istrm = TextIO.openIn option_filename
  fun recurse acc =
      case reader istrm of
        NONE => List.rev acc
      | SOME s => recurse (String.substring(s,0,size s - 1)::acc)
in
  recurse [] before TextIO.closeIn istrm
end handle IO.Io _ => []

fun write_options args = let
  val ostrm = TextIO.openOut option_filename
in
  List.app (fn s => TextIO.output(ostrm, s ^ "\n")) args;
  TextIO.closeOut ostrm
end

fun mem x xs = List.exists (fn y => x = y) xs
fun delete x [] = []
  | delete x (h::t) = if x = h then delete x t else h::delete x t

fun inter [] _ = []
  | inter (h::t) l = if mem h l then h :: inter t l else inter t l

fun setdiff big small =
    case small of
      [] => big
    | h::t => setdiff (delete h big) t



fun delseq dflt numseen list = let
  fun maybewarn () =
      if numseen = 1 then
        warn "Multiple build-sequence options; taking last one\n"
      else ()
in
  case list of
    [] => (NONE, [])
  | ["-seq"] => (warn "Trailing -seq command-line option ignored";
                 (NONE, []))
  | "-seq"::fname::t => let
      val _ = maybewarn()
      val (optval, rest) = delseq dflt (numseen + 1) t
    in
      case optval of
        SOME v => (optval, rest)
      | NONE => (SOME fname, rest)
    end
  | "-fullbuild" :: t => let
      val _ = maybewarn()
      val (optval, rest) = delseq dflt (numseen + 1) t
    in
      case optval of
        SOME v => (optval, rest)
      | NONE => (SOME dflt, rest)
    end
  | h :: t => let val (optval, rest) = delseq dflt numseen t
              in
                (optval, h::rest)
              end
end

fun orlist slist =
    case slist of
      [] => ""
    | [x] => x
    | [x,y] => x ^ ", or " ^ y
    | x::xs => x ^ ", " ^ orlist xs

datatype cline_action =
         Clean of string
       | Normal of {kernelspec : string,
                    seqname : string,
                    rest : string list,
                    build_theory_graph : bool}
exception DoClean of string
fun get_cline kmod = let
  val reader = TextIO.inputLine
  (* handle -fullbuild vs -seq fname, and -expk vs -otknl vs -stdknl *)
  val oldopts = read_earlier_options reader
  val newopts = CommandLine.arguments()
  fun unary_toggle optname dflt f toggles opts =
      case inter toggles opts of
        [x] => (f x, delete x opts)
      | result as (x::y::_) =>
        (warn ("*** Specifying multiple "^optname^" options; using "^x);
         (f x, delete x opts))
      | [] => let
          val optvalue =
              case inter toggles oldopts of
                [] => dflt
              | [x] =>
                (warn ("*** Using "^optname^" option "^x^
                       " from earlier build command;\n\
                       \    use " ^ orlist toggles ^ " to override");
                 f x)
              | x::y::_ =>
                (warn ("Cached build options specify multiple "^optname^
                       " options; using "^x); f x)
        in
          (optvalue, opts)
        end
  val _ =
      if mem "cleanAll" newopts orelse mem "-cleanAll" newopts then
        raise DoClean "cleanAll"
      else if mem "cleanDeps" newopts orelse mem "-cleanDeps" newopts then
        raise DoClean "cleanDeps"
      else if mem "clean" newopts orelse mem "-clean" newopts then
        raise DoClean "clean"
      else if mem "-h" newopts orelse mem "-?" newopts orelse
              mem "--help" newopts orelse mem "-help" newopts
      then
        exit_with_help()
      else ()
  val (seqspec, newopts) =
      case delseq dfltbuildseq 0 newopts of
        (NONE, new') => let
        in
          case delseq dfltbuildseq 0 oldopts of
            (NONE, _) => (dfltbuildseq, new')
          | (SOME f, _) =>
            if f = dfltbuildseq then (f, new')
            else (warn ("*** Using build-sequence file "^f^
                        " from earlier build command; \n\
                        \    use -fullbuild option to override");
                  (f, new'))
        end
      | (SOME f, new') => (f, new')
  val (knlspec, newopts) =
      unary_toggle "kernel" "-stdknl" I ["-expk", "-otknl", "-stdknl"] newopts
  val knlspec = kmod knlspec
  val (buildgraph, newopts) =
      unary_toggle "theory-graph" true (fn x => x = "-graph")
                   ["-graph", "-nograph"] newopts
  val bgoption = if buildgraph then [] else ["-nograph"]
  val _ =
      if seqspec = dfltbuildseq then
        write_options (knlspec::bgoption)
      else
        write_options (knlspec::"-seq"::seqspec::bgoption)
in
  Normal {kernelspec = knlspec, seqname = seqspec, rest = newopts,
          build_theory_graph = buildgraph}
end handle DoClean s => Clean s

(* ----------------------------------------------------------------------
   Some useful file-system utility functions
   ---------------------------------------------------------------------- *)

(* map a function over the files in a directory *)
fun map_dir f dir =
  let val dstrm = OS.FileSys.openDir dir
      fun loop () =
        case OS.FileSys.readDir dstrm
         of NONE => []
          | SOME file => (dir,file)::loop()
      val files = loop()
      val _ = OS.FileSys.closeDir dstrm
  in List.app f files
     handle OS.SysErr(s, erropt)
       => die ("OS error: "^s^" - "^
              (case erropt of SOME s' => OS.errorMsg s' | _ => ""))
       | otherexn => die ("map_dir: "^General.exnMessage otherexn)
  end;

fun rem_file f =
  OS.FileSys.remove f
   handle _ => (warn ("Couldn't remove file "^f); ());

fun copy file path =  (* Dead simple file copy *)
 let open TextIO
     val (istrm,ostrm) = (openIn file, openOut path)
     fun loop() =
       case input1 istrm
        of SOME ch => (output1(ostrm,ch) ; loop())
         | NONE    => (closeIn istrm; flushOut ostrm; closeOut ostrm)
  in loop()
  end;

fun bincopy file path =  (* Dead simple file copy - binary version *)
 let open BinIO
     val (istrm,ostrm) = (openIn file, openOut path)
     fun loop() =
       case input1 istrm
        of SOME ch => (output1(ostrm,ch) ; loop())
         | NONE    => (closeIn istrm; flushOut ostrm; closeOut ostrm)
  in loop()
  end;

(* f is either bincopy or copy *)
fun update_copy f src dest = let
  val t0 = OS.FileSys.modTime src
in
  f src dest;
  OS.FileSys.setTime(dest, SOME t0)
end

fun cp b = if b then update_copy bincopy else update_copy copy

fun mv0 s1 s2 = let
  val s1' = normPath s1
  val s2' = normPath s2
in
  FileSys.rename{old=s1', new=s2'}
end

fun mv b = if b then mv0 else cp b

fun moveTo dir action = let
  val here = OS.FileSys.getDir()
  val b = (OS.FileSys.chDir dir; true) handle _ => false
  fun normalise s = OS.Path.mkAbsolute {path = s, relativeTo = dir}
in
  if b then (map normalise (action ()) before OS.FileSys.chDir here)
            handle e => (OS.FileSys.chDir here; raise e)
  else []
end

fun hmakefile_data HOLDIR =
    if OS.FileSys.access ("Holmakefile", [OS.FileSys.A_READ]) then let
        open Holmake_types
        fun base_env s =
            case s of
              "HOLDIR" => [LIT HOLDIR]
            | "SIGOBJ" => [VREF "HOLDIR", LIT "/sigobj"]
            | _ => (case OS.Process.getEnv s of
                      NONE => [LIT ""]
                    | SOME v => [LIT v])
        val (env, _, _) = ReadHMF.read "Holmakefile" base_environment
        fun envlist id =
            map dequote (tokenize (perform_substitution env [VREF id]))
      in
        {includes = envlist "PRE_INCLUDES" @ envlist "INCLUDES",
         extra_cleans = envlist "EXTRA_CLEANS"}
      end
    else {includes = [], extra_cleans = []}

fun clean0 HOLDIR = let
  val {includes,extra_cleans} = hmakefile_data HOLDIR
in
  Holmake_tools.clean_dir {extra_cleans = extra_cleans} ;
  includes
end

fun cleanAll0 HOLDIR = let
  val {includes,extra_cleans} = hmakefile_data HOLDIR
in
  Holmake_tools.clean_dir {extra_cleans = extra_cleans};
  Holmake_tools.clean_depdir {depdirname = ".HOLMK"};
  includes
end

fun clean HOLDIR dirname = moveTo dirname (fn () => clean0 HOLDIR)
fun cleanAll HOLDIR dirname = moveTo dirname (fn () => cleanAll0 HOLDIR)

fun clean_dirs {HOLDIR,action} dirs = let
  val seen = Binaryset.empty String.compare
  fun recurse sofar todo =
      case todo of
        [] => ()
      | d::ds => let
        in
          if Binaryset.member(sofar, d) then recurse sofar ds
          else let
              val newincludes = action HOLDIR d
            in
              recurse (Binaryset.add(sofar,d)) (newincludes @ ds)
            end
        end
in
  recurse seen dirs
end

(* ----------------------------------------------------------------------
    In clean_sigobj, we need to avoid removing the systeml stuff that
    will have been put into sigobj by the action of configure.sml
   ---------------------------------------------------------------------- *)

fun equal x y = (x=y);
fun mem x l = List.exists (equal x) l;
val SIGOBJ = fullPath [HOLDIR, "sigobj"];

fun clean_sigobj() = let
  open Systeml
  val _ = print ("Cleaning out "^SIGOBJ^"\n")
  val lowcase = String.map Char.toLower
  val sigobj_extras =
      if ML_SYSNAME = "mosml" then ["basis2002"] else []
  fun sigobj_rem_file s = let
    val f = Path.file s
    val n = lowcase (hd (String.fields (equal #".") f))
  in
    if mem n (["systeml", "readme"] @ sigobj_extras) then ()
    else rem_file s
  end
  val toolsuffix = if ML_SYSNAME = "poly" then "-poly" else ""
  fun write_initial_srcfiles () = let
    open TextIO
    val outstr = openOut (fullPath [HOLDIR,"sigobj","SRCFILES"])
  in
    output(outstr,
           fullPath [HOLDIR, "tools" ^ toolsuffix, "Holmake", "Systeml"]);
    output(outstr, "\n");
    closeOut(outstr)
  end
in
  map_dir (sigobj_rem_file o normPath o OS.Path.concat) SIGOBJ;
  write_initial_srcfiles ();
  print (SIGOBJ ^ " cleaned\n")
end;

val EXECUTABLE = Systeml.xable_string (fullPath [HOLDIR, "bin", "build"])

fun full_clean (SRCDIRS:(string*int) list)  f =
    clean_sigobj() before
    (* clean both kernel directories, regardless of which was actually built,
       the help src directory too, and all the src directories, including
       those with ! annotations  *)
    clean_dirs {HOLDIR=HOLDIR, action = f}
               (fullPath [HOLDIR, "help", "src-sml"] ::
                fullPath [HOLDIR, "src", "0"] ::
                fullPath [HOLDIR, "src", "experimental-kernel"] ::
                fullPath [HOLDIR, "src", "logging-kernel"] ::
                map #1 SRCDIRS)

fun app_sml_files f {dirname} =
  let
    open OS.FileSys OS.Path
    val dstrm = openDir dirname
    fun recurse () =
      case readDir dstrm of
          NONE => closeDir dstrm
        | SOME p => ((case ext p of
                          SOME "sml" => f (concat(dirname,p))
                        | SOME "sig" => f (concat(dirname,p))
                        | _ => ());
                     recurse())
  in
    recurse ()
  end

fun check_against executable s = let
  open Time
  val p = if OS.Path.isRelative s then fullPath [HOLDIR, s]
          else s
  val cfgtime = FileSys.modTime p
in
  if FileSys.modTime executable < cfgtime then
    (warn ("WARNING! WARNING!");
     warn ("  The executable "^executable^" is older than " ^ s ^ ";");
     warn ("  this suggests you should reconfigure the system.");
     warn ("  Press Ctl-C now to abort the build; <RETURN> to continue.");
     warn ("WARNING! WARNING!");
     if Systeml.POLY_VERSION = 551 orelse Systeml.POLY_VERSION = 552 then
       ignore(TextIO.inputLine TextIO.stdIn)
       (* see PolyML bug report at
            https://www.mail-archive.com/polyml@inf.ed.ac.uk/msg00982.html *)
     else ();
     ignore (TextIO.inputLine TextIO.stdIn))
  else ()
end handle OS.SysErr _ => die ("File "^s^" has disappeared.");


(* uploadfn is of type : bool -> string -> string -> unit
     the boolean is whether or not the arguments are binary files
     the strings are source and destination file-names, in that order
*)
fun transfer_file uploadfn targetdir (df as (dir,file)) = let
  fun transfer binaryp (dir,file1,file2) =
    uploadfn binaryp (fullPath [dir,file1]) (fullPath [targetdir,file2])
  fun idtransfer binaryp (dir,file) =
      case Path.base file of
        "selftest" => ()
      | _ => transfer binaryp (dir,file,file)
  fun digest_sig file =
      let val b = Path.base file
      in if (String.extract(b,String.size b -4,NONE) = "-sig"
             handle _ => false)
         then SOME (String.extract(b,0,SOME (String.size b - 4)))
         else NONE
      end
  fun augmentSRCFILES file = let
    open TextIO
    val ostrm = openAppend (Path.concat(SIGOBJ,"SRCFILES"))
  in
    output(ostrm,fullPath[dir,file]^"\n") ;
    closeOut ostrm
  end

in
  case Path.ext file of
    SOME"ui"     => idtransfer true df
  | SOME"uo"     => idtransfer true df
  | SOME"so"     => idtransfer true df   (* for dynlibs *)
  | SOME"xable"  => idtransfer true df   (* for executables *)
  | SOME"sig"    => (idtransfer false df; augmentSRCFILES (Path.base file))
  | SOME"sml"    => (case digest_sig file of
                       NONE => ()
                     | SOME file' =>
                       (transfer false (dir,file, file' ^".sig");
                        augmentSRCFILES file'))
  |    _         => ()
end;

fun Gnumake dir =
  if SYSTEML [GNUMAKE] then true
  else (warn ("Build failed in directory "^dir ^" ("^GNUMAKE^" failed).");
        false)

exception BuildExit
fun build_dir Holmake selftest_level (dir, regulardir) = let
  val _ = if selftest_level >= regulardir then ()
          else raise BuildExit
  val _ = OS.FileSys.chDir dir
  val truncdir = if String.isPrefix HOLDIR dir then
                   String.extract(dir, size HOLDIR + 1, NONE)
                   (* +1 to drop directory slash after holdir *)
                 else dir
  val now_d = Date.fromTimeLocal (Time.now())
  val now_s = Date.fmt "%d %b, %H:%M:%S" now_d
  val _ = print ("Building directory "^truncdir^" ["^now_s^"]\n")
in
  case #file(OS.Path.splitDirFile dir) of
    "muddyC" => let
    in
      case OS of
        "winNT" => bincopy (fullPath [HOLDIR, "tools", "win-binaries",
                                      "muddy.so"])
                           (fullPath [HOLDIR, "examples", "muddy", "muddyC",
                                      "muddy.so"])
      | other => if not (Gnumake dir) then
                   print(String.concat
                           ["\nmuddyLib has NOT been built!! ",
                            "(continuing anyway).\n\n"])
                 else ()
    end
  | "minisat" => let
    in case OS of
	   "winNT" => bincopy (fullPath [HOLDIR, "tools", "win-binaries",
					 "minisat.exe"])
                              (fullPath [HOLDIR, "src","HolSat","sat_solvers",
                                         "minisat", "DELTHISminisat.exe"])
	 | other => if not (Gnumake dir) then
			print(String.concat
				  ["\nMiniSat has NOT been built!! ",
				   "(continuing anyway).\n\n"])
                    else ()
    end
  | "zc2hs" => let
    in case OS of
	   "winNT" => bincopy (fullPath [HOLDIR, "tools", "win-binaries",
					 "zc2hs.exe"])
                              (fullPath [HOLDIR, "src","HolSat","sat_solvers","zc2hs", "zc2hs.exe"])
	 | other => if not (Gnumake dir) then
			print(String.concat
				  ["\nzc2hs has NOT been built!! ",
				   "(continuing anyway).\n\n"])
                    else ()
    end
  | _ => Holmake dir
end
handle OS.SysErr(s, erropt) =>
       die ("OS error: "^s^" - "^
            (case erropt of SOME s' => OS.errorMsg s' | _ => ""))
     | BuildExit => ()

fun write_theory_graph () = let
  val dotexec = Systeml.DOT_PATH
in
  if not (FileSys.access (dotexec, [FileSys.A_EXEC])) then
    (* of course, this will likely be the case on Windows *)
    warn ("*** Can't see dot executable at "^dotexec^"; not generating \
          \theory-graph\n\
          \*** You can try reconfiguring and providing an explicit path \n\
          \*** (val DOT_PATH = \"....\") in\n\
          \***    tools-poly/poly-includes.ML (Poly/ML)\n\
          \***  or\n\
          \***    config-override           (Moscow ML)\n\
          \***\n\
          \*** (Under Poly/ML you will have to delete bin/hol.state0 as \
          \well)\n***\n\
          \*** (Or: build with -nograph to stop this \
          \message from appearing again)\n")
  else let
      val _ = print "Generating theory-graph and HTML theory signatures; this may take a while\n"
      val _ = print "  (Use build's -nograph option to skip this step.)\n"
      val pfp = Systeml.protect o fullPath
      val result =
          OS.Process.system(pfp [HOLDIR, "bin", "hol"] ^ " < " ^
                            pfp [HOLDIR, "help", "src-sml", "DOT"])
    in
      if OS.Process.isSuccess result then ()
      else warn "*** Theory graph construction failed.\n"
    end
end

fun Poly_compilehelp() = let
  open Systeml
in
  system_ps (fullPath [HOLDIR, "tools", "mllex", "mllex.exe"] ^ " Lexer.lex");
  system_ps (fullPath [HOLDIR, "tools", "mlyacc", "src", "mlyacc.exe"] ^ " Parser.grm");
  system_ps (POLYC ^ " poly-makebase.ML -o makebase.exe");
  system_ps (POLYC ^ " poly-Doc2Html.ML -o Doc2Html.exe");
  system_ps (POLYC ^ " poly-Doc2Txt.ML -o Doc2Txt.exe");
  system_ps (POLYC ^ " poly-Doc2Tex.ML -o Doc2Tex.exe")
end

val HOLMAKE = fullPath [HOLDIR, "bin/Holmake"]
val ML_SYSNAME = Systeml.ML_SYSNAME

fun mosml_compilehelp () = ignore (SYSTEML [HOLMAKE, "all"])

fun build_adoc_files () = let
  val docdirs = let
    val instr = TextIO.openIn(fullPath [HOLDIR, "tools",
                                        "documentation-directories"])
    val wholefile = TextIO.inputAll instr before TextIO.closeIn instr
  in
    map normPath (String.tokens Char.isSpace wholefile)
  end handle _ => (print "Couldn't read documentation directories file\n";
                   [])
  val doc2txt = fullPath [HOLDIR, "help", "src-sml", "Doc2Txt.exe"]
  fun make_adocs dir = let
    val fulldir = fullPath [HOLDIR, dir]
  in
    if SYSTEML [doc2txt, fulldir, fulldir] then true
    else
      (print ("Generation of ASCII doc files failed in directory "^dir^"\n");
       false)
  end
in
  List.all make_adocs docdirs
end

fun build_help graph =
 let val dir = OS.Path.concat(OS.Path.concat (HOLDIR,"help"),"src-sml")
     val _ = OS.FileSys.chDir dir

     (* builds the documentation tools called below *)
     val _ = if ML_SYSNAME = "poly" then ignore (Poly_compilehelp())
             else if ML_SYSNAME = "mosml" then mosml_compilehelp()
             else raise Fail "Bogus ML_SYSNAME"

     val doc2html = fullPath [dir,"Doc2Html.exe"]
     val docpath  = fullPath [HOLDIR, "help", "Docfiles"]
     val htmlpath = fullPath [docpath, "HTML"]
     val _        = if (OS.FileSys.isDir htmlpath handle _ => false) then ()
                    else (print ("Creating directory "^htmlpath^"\n");
                          OS.FileSys.mkDir htmlpath)
     val cmd1     = [doc2html, docpath, htmlpath]
     val cmd2     = [fullPath [dir,"makebase.exe"]]
     val _ = print "Generating ASCII versions of Docfiles...\n"
     val _ = if build_adoc_files () then print "...ASCII Docfiles done\n"
             else ()
 in
   print "Generating HTML versions of Docfiles...\n"
 ;
   if SYSTEML cmd1 then print "...HTML Docfiles done\n"
   else die "Couldn't make html versions of Docfiles"
 ;
   if (print "Building Help DB\n"; SYSTEML cmd2) then ()
   else die "Couldn't make help database"
 ;
   if graph then write_theory_graph()
   else ()
 end

fun process_cline kmod =
    case get_cline kmod of
      Clean s => let
        val action = case s of
                       "-cleanAll" => cleanAll
                     | "cleanAll" => cleanAll
                     | "clean" => clean
                     | "-clean" => clean
                     | _ => die ("Clean action = "^s^"???")
        val SRCDIRS =
            read_buildsequence {kernelname = "-stdknl"} dfltbuildseq
      in
        (full_clean SRCDIRS action; Process.exit Process.success)
      end
    | Normal {kernelspec, seqname, rest, build_theory_graph} => let
        val (do_selftests, rest) = cline_selftest rest
        val SRCDIRS = read_buildsequence {kernelname = kernelspec} seqname
      in
        if mem "help" rest then
          (build_help build_theory_graph;
           Process.exit Process.success)
        else
          {cmdline=rest,build_theory_graph=build_theory_graph,
           do_selftests = do_selftests, SRCDIRS = SRCDIRS}
      end

fun make_buildstamp () =
 let open Path TextIO
     val stamp_filename = concat(HOLDIR, concat("tools","build-stamp"))
     val stamp_stream = openOut stamp_filename
     val date_string = Date.toString (Date.fromTimeLocal (Time.now()))
 in
    output(stamp_stream, "built "^date_string);
    closeOut stamp_stream
end

val logdir = Systeml.build_log_dir
val logfilename = Systeml.build_log_file
val hostname = if Systeml.isUnix then
                 case Mosml.run "hostname" [] "" of
                   Mosml.Success s => String.substring(s,0,size s - 1) ^ "-"
                                      (* substring to drop \n in output *)
                 | _ => ""
               else "" (* what to do under windows? *)

fun setup_logfile () = let
  open OS.FileSys
  fun ensure_dir () =
      if access (logdir, []) then
        isDir logdir
      else (mkDir logdir; true)
in
  if ensure_dir() then
    if access (logfilename, []) then
      warn "Build log exists; new logging will concatenate onto this file"
    else let
        (* touch the file *)
        val outs = TextIO.openOut logfilename
      in
        TextIO.closeOut outs
      end
  else warn "Couldn't make or use build-logs directory"
end handle IO.Io _ => warn "Couldn't set up build-logs"

fun finish_logging buildok = let
in
  if OS.FileSys.access(logfilename, []) then let
      open Date
      val timestamp = fmt "%Y-%m-%dT%H%M" (fromTimeLocal (Time.now()))
      val newname0 = hostname^timestamp
      val newname = (if buildok then "" else "bad-") ^ newname0
    in
      OS.FileSys.rename {old = logfilename, new = fullPath [logdir, newname]}
    end
  else ()
end handle IO.Io _ => warn "Had problems making permanent record of build log"

fun Holmake sysl isSuccess extra_args analyse_failstatus do_selftests dir = let
  val hmstatus = sysl HOLMAKE ("--qof" :: extra_args())
in
  if isSuccess hmstatus then
    if do_selftests > 0 andalso
       OS.FileSys.access("selftest.exe", [OS.FileSys.A_EXEC])
    then
      (print "Performing self-test...\n";
       if SYSTEML [dir ^ "/selftest.exe", Int.toString do_selftests]
       then
         print "Self-test was successful\n"
       else
         die ("Selftest failed in directory "^dir))
    else
      ()
  else let
      val info = analyse_failstatus hmstatus
    in
      die ("Build failed in directory "^dir^
           (if info <> "" then " ("^info^")" else ""))
    end
end

val () = OS.Process.atExit (fn () => finish_logging false)
        (* this will do nothing if finish_logging happened normally first;
           otherwise the log's bad version will be recorded *)




end (* struct *)
