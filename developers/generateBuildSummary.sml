structure generateBuildSummary =
struct



(* reads the output of bin/build on standard input, and turns it into a
   mail message *)

infix |>
fun (x |> f) = f x

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
    \Date: "^datestring()^ (* datestring provides its own newline *)
    "Subject: "^subject^"\n"^
    "MIME-version: 1.0\n\
    \Content-Type: text/plain; charset=UTF-8\n\
    \Content-Transfer-Encoding: 8bit\n\n"

fun trunclast n s = let
  val sz = String.size s
in
  if n < 0 then "" else
  if n < sz then String.extract(s, sz - n, NONE)
  else s
end

val remove_nulls = String.translate (fn #"\000" => "^@" | c => str c)

fun newline_tidy s = let
  (* replace first line with ellipsis message -
     leave a string with no newlines alone *)
  open Substring
  val (pfx, rest) = position "\n" (full s)
in
  if size rest = 0 then s
  else "... content elided ..." ^ string rest
end

fun main() = let
  val (from, sysdesc) = case CommandLine.arguments() of
               [f,s] => (f,s)
             | _ => usage()
  val buildlog = TextIO.inputAll TextIO.stdIn
  open TextIO
in
  if String.isSuffix "Hol built successfully.\n" buildlog then
    output(stdOut,
           standard_header from ("SUCCESS: "^sysdesc) ^
           buildlog)
  else
    output(stdOut,
           standard_header from ("FAILURE: "^sysdesc) ^
           (buildlog |> trunclast 3000
                     |> newline_tidy
                     |> remove_nulls))
end

end
