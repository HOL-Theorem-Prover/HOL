structure generateBuildSummary =
struct

(* reads the output of bin/build on standard input, and turns it into a
   mail message *)

fun datestring t = let
  open Date
in
  fmt "%a, %d %b %Y %H:%M UT" (fromTimeUniv t)
end

fun standard_header from subject t =
    "To: hol-builds@lists.sourceforge.net\n\
    \From: "^from^"\n\
    \Date: "^datestring t^"\n\
    \Subject: "^subject^"\n\n"

fun usage() =
    (TextIO.output(TextIO.stdErr,
                   "Usage:\n  "^CommandLine.name()^
                   " from-address system-description\n");
     TextIO.flushOut TextIO.stdErr;
     OS.Process.exit OS.Process.failure)

fun main() = let
  val (from, sysdesc) = case CommandLine.arguments() of
               [f,s] => (f,s)
             | _ => usage()
  val buildlog = TextIO.inputAll TextIO.stdIn
  open TextIO
in
  if String.isSuffix "Hol built successfully.\n" buildlog then
    output(stdOut,
           standard_header from ("SUCCESS: "^sysdesc) (Time.now()) ^
           buildlog)
  else
    output(stdOut,
           standard_header from ("FAILURE: "^sysdesc) (Time.now()) ^
           buildlog)
end

end
