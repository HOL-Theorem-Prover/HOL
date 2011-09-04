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

(* values from the Systeml structure, which is created at HOL configuration
   time *)
val OS = Systeml.OS;
val HOLDIR = Systeml.HOLDIR
val EXECUTABLE = Systeml.xable_string (fullPath [HOLDIR, "bin", "build"])
val DEPDIR = Systeml.DEPDIR
val GNUMAKE = Systeml.GNUMAKE
val DYNLIB = Systeml.DYNLIB

val help_mesg = let
  val symlink_mesg =
      if OS = "winNT" then "Symbolic linking is necessarily OFF.\n"
      else "Symbolic linking is ON by default.\n"
in
  "Usage: build\n\
  \   or: build -symlink\n\
  \   or: build -small\n\
  \   or: build -dir <fullpath>\n\
  \   or: build -dir <fullpath> -symlink\n\
  \   or: build -clean\n\
  \   or: build -cleanAll\n\
  \   or: build symlink\n\
  \   or: build small\n\
  \   or: build clean\n\
  \   or: build cleanAll\n\
  \   or: build help.\n" ^ symlink_mesg ^
  "Add -expk to build an experimental kernel.\n\
  \Add -stdknl to force the standard kernel.\n\
  \Add -selftest to do self-tests, where defined.\n\
  \       Optionally follow -selftest with a number to indicate level\n\
  \       of testing, the higher the number the more testing\n\
  \       will be done.\n\
  \Add -seq <fname> to use fname as build-sequence\n\
  \Add -fullbuild to force full, default build sequence\n"
end


fun read_buildsequence {kernelpath} bseq_fname = let
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
              fun extract_mlsys s =
                  if String.sub(s,0) = #"[" then let
                      fun grabsys i =
                          if String.sub(s,i) = #"]" then
                            (String.substring(s,1,i-1),
                             String.extract(s,i+1,NONE))
                          else grabsys (i + 1)
                    in
                      grabsys 1
                      handle Subscript =>
                             die ("Malformed system spec: "^s)
                    end
                  else ("", s)
              val (mlsys,s) = extract_mlsys s
              val (dirname0,testcount) = extract_testcount (s,0)
              val dirname =
                  if dirname0 = "**KERNEL**" then kernelpath
                  else if Path.isAbsolute dirname0 then dirname0
                  else fullPath [HOLDIR, dirname0]
              open FileSys
            in
              if mlsys = "" orelse mlsys = Systeml.ML_SYSNAME then
                if access (dirname, [A_READ, A_EXEC]) then
                  if isDir dirname orelse mlsys <> "" then
                    read_file ((dirname,testcount)::acc) fstr
                  else
                    (warn ("** File "^dirname0^
                           " from build sequence is not a directory \
                           \-- skipping it");
                     read_file acc fstr)
                else (warn ("** File "^s^" from build sequence does not "^
                          "exist or is inacessible -- skipping it");
                    read_file acc fstr)
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


datatype buildtype =
         Normal of {kernelspec : string, seqname : string, rest : string list}
       | Clean of string
exception QuickExit of buildtype
fun get_cline {default_seq} = let
  val reader = TextIO.inputLine
  (* handle -fullbuild vs -seq fname, and -expk vs -stdknl *)
  val oldopts = read_earlier_options reader
  val newopts = CommandLine.arguments()
  val _ =
      if mem "cleanAll" newopts orelse mem "-cleanAll" newopts then
        raise QuickExit (Clean "cleanAll")
      else if mem "cleanDeps" newopts orelse mem "-cleanDeps" newopts then
        raise QuickExit (Clean "cleanDeps")
      else if mem "clean" newopts orelse mem "-clean" newopts then
        raise QuickExit (Clean "clean")
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
      case inter ["-expk", "-stdknl"] newopts of
        [x] => (x, delete x newopts)
      | (result as (x::y::_)) =>
        (warn ("Specifying multiple kernel options; using "^x);
         (x, setdiff newopts result))
      | [] => let
        in
          case inter ["-expk", "-stdknl"] oldopts of
            [] => ("-stdknl", newopts)
          | [x] => (warn ("*** Using kernel option "^x^
                          " from earlier build command; \n\
                          \    use -expk or -stdknl to override");
                    (x, newopts))
          | x::y::_ =>
            (warn ("Cached build options specify multiple kernel options; \
                   \using "^x); (x,newopts))
        end
  val _ = if seqspec = default_seq then write_options [knlspec]
          else write_options [knlspec, "-seq", seqspec]
in
  Normal {kernelspec = knlspec, seqname = seqspec, rest = newopts}
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
        val toks = ReadHMF.read "Holmakefile"
        val env = extend_env toks base_env
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

end (* struct *)
