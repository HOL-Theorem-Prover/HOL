structure buildutils :> buildutils =
struct

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

fun read_buildsequence ssall readline bseq_fname = let 
  fun read_file acc fstr =
      case readline fstr of
        NONE => List.rev acc
      | SOME s => let
          (* drop final \n char *)
          val s = String.substring(s, 0, size s - 1)
          val ss = ssall s
          val ss = Substring.dropl Char.isSpace ss
          (* drop leading w-space *)
          val (ss, _) = Substring.position "#" ss
          (* drop trailing comment *)
          val s = Substring.string ss
        in
          if s = "" then read_file acc fstr
          else let
              fun extract_testcount (s,acc) =
                  if String.sub(s,0) = #"!" then
                    extract_testcount (String.extract(s,1,NONE), acc+1)
                  else (s,acc)
              val (dirname0,testcount) = extract_testcount (s,0)
              val dirname = if Path.isAbsolute dirname0 then dirname0
                            else fullPath [HOLDIR, dirname0]
              open FileSys
            in if access (dirname, [A_READ, A_EXEC]) then
                 if isDir dirname then
                   read_file ((dirname,testcount)::acc) fstr
                 else
                   (warn ("** File "^dirname0^
                          " from build sequence is not a directory \
                          \-- skipping it\n");
                    read_file acc fstr)
               else (warn ("** File "^s^" from build sequence does not "^
                           "exist or is inacessible -- skipping it\n");
                     read_file acc fstr)
            end
        end
  val bseq_file = TextIO.openIn bseq_fname
in
  read_file [] bseq_file before TextIO.closeIn bseq_file
end
             
             

end (* struct *)
