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



end (* struct *)
