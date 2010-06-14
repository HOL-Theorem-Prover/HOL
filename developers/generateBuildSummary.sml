structure generateBuildSummary =
struct

(* reads the output of bin/build on standard input, and turns it into a
   mail message *)

fun die s = (TextIO.output(TextIO.stdErr, s);
             TextIO.flushOut TextIO.stdErr;
             OS.Process.exit OS.Process.failure)


fun usage() = die ("Usage:\n  "^CommandLine.name()^
                   " from-address system-description\n")


fun datestring () = let
  (* SML implementations have such broken time/date code that this seems
     best - now only works on Unixy systems *)
  val tmp = OS.FileSys.tmpName()
  val result = OS.Process.system ("date +\"%a, %d %b %Y %H:%M %z\" > "^tmp)
  val _ = OS.Process.isSuccess result orelse
          die "Couldn't run date"
  val istrm = TextIO.openIn tmp
in
  TextIO.inputAll istrm before TextIO.closeIn istrm
end

fun standard_header from subject =
    "To: hol-builds@lists.sourceforge.net\n\
    \From: "^from^"\n\
    \Date: "^datestring()^
    "Subject: "^subject^"\n\n"

fun main() = let
  val (from, sysdesc) = case CommandLine.arguments() of
               [f,s] => (f,s)
             | _ => usage()
  val buildlog0 = TextIO.inputAll TextIO.stdIn
  val buildlog = String.translate (fn #"\000" => "^@" | c => str c) buildlog0
  open TextIO
in
  if String.isSuffix "Hol built successfully.\n" buildlog then
    output(stdOut,
           standard_header from ("SUCCESS: "^sysdesc) ^
           buildlog)
  else
    output(stdOut,
           standard_header from ("FAILURE: "^sysdesc) ^
           buildlog)
end

end
