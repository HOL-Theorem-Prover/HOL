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


val help_mesg =
    (* 80 characters ---------------------------------------------------------------| *)
    "Usage:\n\
    \  build [-stdknl|-expk|..] [-nograph|..] [-seq FNAME|-fullbuild] [-selftest N]\n\n\
    \    builds the system\n\n\
    \OR\n\n\
    \  build [clean|cleanAll]\n\n\
    \    \"cleans\" the system, removing built object files.\n\
    \    The \"cleanAll\" variant removes pre-calculated dependency information.\n\n\
    \OR\n\n\
    \  build help\n\n\
    \    builds the help system only\n\n\
    \OR\n\n\
    \  build [-h|--help|-help|-?]\n\n\
    \    shows this message\n\n\
    \Options to the first version of the command include\n\
    \  -dir DIR    : builds just the directory DIR instead of a provided sequence\n\
    \  -expk       : builds the \"experimental\" kernel\n\
    \  -fullbuild  : builds with the default \"full\" build-sequence\n\
    \  -graph      : requires the building of the help system's theory-graph\n\
    \  -nograph    : omits the building of the help system's theory-graph\n\
    \  -otknl      : builds the OpenTheory or \"logging\" kernel\n\
    \  -selftest N : builds include regression test level N\n\
    \  -seq FNAME  : builds using build-sequence file FNAME\n\
    \  -small      : moves object files to SIGOBJ rather than copying or linking\n\
    \  -stdknl     : builds the \"standard\" kernel\n\
    \  -symlink    : no useful effect (retained for backwards compatibility)\n\n\
    \Options clean, cleanAll can be given with leading hyphens.\n\
    \Options -small and -symlink can be given without their leading hyphens.\n\n"

fun exit_with_help() =
    (print help_mesg ; Process.exit Process.success)

fun read_buildsequence {kernelname} bseq_fname = let
  val kernelpath = fullPath [HOLDIR, "src",
    case kernelname of
        "stdknl" => "0"
      | "expk" => "experimental-kernel"
      | "otknl" => "logging-kernel"
      | _ => die ("Bad kernelname: "^kernelname)
    ]
  val readline = TextIO.inputLine
  fun read_file acc fstr =
      case readline fstr of
        NONE => List.rev acc
      | SOME s => let
          (* drop trailing and leading whitespace *)
          val ss = Substring.full s
          val ss = Substring.dropl Char.isSpace ss
          val ss = Substring.dropr Char.isSpace ss

          (* drop trailing comment *)
          val (ss, _) = Substring.position "#" ss
          val s = Substring.string ss
        in
          if s = "" then read_file acc fstr
          else let
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
                             die ("Malformed "^name^" spec: "^s)
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
                 (knl = "" orelse knl = kernelname) then
                if access (dirname, [A_READ, A_EXEC]) then
                  if isDir dirname orelse mlsys <> "" then
                    read_file ((dirname,testcount)::acc) fstr
                  else
                    die ("** File "^dirname0^
                         " from build sequence is not a directory")
                else die ("** File "^s^" from build sequence does not "^
                          "exist or is inacessible -- skipping it")
              else read_file acc fstr
            end
        end
  val bseq_file =
      TextIO.openIn bseq_fname
      handle IO.Io _ => die ("Fatal error: couldn't open sequence file: "^
                             bseq_fname)
in
  read_file [] bseq_file before TextIO.closeIn bseq_file
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


datatype buildtype =
         Normal of {kernelspec : string, seqname : string, build_theory_graph : bool, rest : string list}
       | Clean of string
exception QuickExit of buildtype
fun get_cline {default_seq} = let
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
        raise QuickExit (Clean "cleanAll")
      else if mem "cleanDeps" newopts orelse mem "-cleanDeps" newopts then
        raise QuickExit (Clean "cleanDeps")
      else if mem "clean" newopts orelse mem "-clean" newopts then
        raise QuickExit (Clean "clean")
      else if mem "-h" newopts orelse mem "-?" newopts orelse
              mem "--help" newopts orelse mem "-help" newopts
      then
        exit_with_help()
      else ()
  val (seqspec, newopts) =
      case delseq default_seq 0 newopts of
        (NONE, new') => let
        in
          case delseq default_seq 0 oldopts of
            (NONE, _) => (default_seq, new')
          | (SOME f, _) =>
            if f = default_seq then (f, new')
            else (warn ("*** Using build-sequence file "^f^
                        " from earlier build command; \n\
                        \    use -fullbuild option to override");
                  (f, new'))
        end
      | (SOME f, new') => (f, new')
  val (knlspec, newopts) =
      unary_toggle "kernel" "-stdknl" I ["-expk", "-otknl", "-stdknl"] newopts
  val (buildgraph, newopts) =
      unary_toggle "theory-graph" true (fn x => x = "-graph")
                   ["-graph", "-nograph"] newopts
  val bgoption = if buildgraph then [] else ["-nograph"]
  val _ =
      if seqspec = default_seq then
        write_options (knlspec::bgoption)
      else
        write_options (knlspec::"-seq"::seqspec::bgoption)
in
  Normal {kernelspec = knlspec, seqname = seqspec, rest = newopts,
          build_theory_graph = buildgraph}
end handle QuickExit bt => bt

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

fun check_against s = let
  open Time
  val cfgtime = FileSys.modTime (fullPath [HOLDIR, s])
in
  if FileSys.modTime EXECUTABLE < cfgtime then
    (warn ("WARNING! WARNING!");
     warn ("  The build file is older than " ^ s ^ ";");
     warn ("  this suggests you should reconfigure the system.");
     warn ("  Press Ctl-C now to abort the build; <RETURN> to continue.");
     warn ("WARNING! WARNING!");
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
                              (fullPath [HOLDIR, "src","HolSat","sat_solvers","minisat", "minisat.exe"])
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


end (* struct *)
