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
fun warn s = let open TextIO in output(stdErr, s); flushOut stdErr end;

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
  \       Follow -selftest with a number to indicate level\n\
  \       of testing, the higher the number the more testing\n\
  \       will be done.\n\
  \Add -seq <fname> to use fname as build-sequence\n\
  \Add -fullbuild to force full, default build sequence\n"
end


fun read_buildsequence {ssfull,inputLine=readline,kernelpath} bseq_fname = let
  fun read_file acc fstr =
      case readline fstr of
        NONE => List.rev acc
      | SOME s => let
          (* drop trailing and leading whitespace *)
          val ss = ssfull s
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
                           \-- skipping it\n");
                     read_file acc fstr)
                else (warn ("** File "^s^" from build sequence does not "^
                          "exist or is inacessible -- skipping it\n");
                    read_file acc fstr)
              else read_file acc fstr
            end
        end
  val bseq_file = TextIO.openIn bseq_fname
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
                                          \ification of test level\n");
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
                   \selftest level "^Int.toString h^"\n");
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
  | ["-seq"] => (warn "Trailing -seq command-line option ignored\n";
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
fun get_cline {reader,default_seq} = let
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
                        \    use -fullbuild option to override\n");
                  (f, new'))
        end
      | (SOME f, new') => (f, new')
  val (knlspec, newopts) =
      case inter ["-expk", "-stdknl"] newopts of
        [x] => (x, delete x newopts)
      | (result as (x::y::_)) =>
        (warn ("Specifying multiple kernel options; using "^x^"\n");
         (x, setdiff newopts result))
      | [] => let
        in
          case inter ["-expk", "-stdknl"] oldopts of
            [] => ("-stdknl", newopts)
          | [x] => (warn ("*** Using kernel option "^x^
                          " from earlier build command; \n\
                          \    use -expk or -stdknl to override\n");
                    (x, newopts))
          | x::y::_ =>
            (warn ("Cached build options specify multiple kernel options; \
                   \using "^x^"\n"); (x,newopts))
        end
  val _ = if seqspec = default_seq then write_options [knlspec]
          else write_options [knlspec, "-seq", seqspec]
in
  Normal {kernelspec = knlspec, seqname = seqspec, rest = newopts}
end handle QuickExit bt => bt


end (* struct *)
