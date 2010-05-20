structure generateBuildSummary =
struct

(* reads the output of bin/build on standard input, and turns it into a
   mail message *)

val timezone_string = let
  val t = Date.localOffset()
  val secs = Time.toSeconds t
  val total_minutes = Int.abs secs div 60
  val hrs = total_minutes div 60
  val minpart = total_minutes mod 60
  val pad = StringCvt.padLeft #"0" 2
in
  (if secs <= 0 then "+" else "-") ^
  pad (Int.toString hrs) ^ pad (Int.toString minpart)
end

fun datestring t = let
  open Date
in
  fmt "%a, %d %b %Y %H:%M " (fromTimeLocal t) ^ timezone_string
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
