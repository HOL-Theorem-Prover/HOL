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
  val result = OS.Process.system ("date +\"%a, %d %b %Y %H:%M:%S %z\" > "^tmp)
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
    "MIME-Version: 1.0\n\
    \Content-Type: text/plain; charset=UTF-8\n\
    \Content-Transfer-Encoding: 8bit\n\n"

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

fun trunclast n s = let
  val sz = String.size s
in
  if n < 0 then "" else
  if n < sz then newline_tidy (String.extract(s, sz - n, NONE))
  else s
end

val lastlines = 80

fun tidy_p2_lines linelist = let
  val maxlen = List.foldl (fn (l,acc) => Int.max(size l, acc)) 0 linelist
  val maxlen = Int.max(78, maxlen)
  fun make_maxlen s =
    if size s = maxlen then s
    else let
        fun findlbrack i =
            if String.sub(s, i) = #"[" then i else findlbrack (i - 1)
        val lbrack_i = findlbrack (size s - 1)
        val pfx = String.extract(s, 0, SOME lbrack_i)
        val spaces = CharVector.tabulate(maxlen - size s, (fn _ => #" "))
        val sfx = String.extract(s, lbrack_i, NONE)
      in
        pfx ^ spaces ^ sfx
      end
in
  map make_maxlen linelist
end

fun filter_input instr = let
  fun phase1 lines =
      case TextIO.inputLine instr of
        NONE => (lines, false)
      | SOME s => if s = "-- Configuration Description Ends --\n" then
                    ("\n"::s::lines, true)
                  else phase1 (s::lines)
  fun phase2 (lines, dirlines, cnt) =
      case TextIO.inputLine instr of
        NONE => (List.take(lines, lastlines), false)
      | SOME s => if s = "Hol built successfully.\n" then
                      (dirlines, true)
                  else let
                      val dirlines =
                          if String.isPrefix "Building directory" s then
                            s :: dirlines
                          else dirlines
                      val (lines, cnt) =
                          if cnt = lastlines * 2 then
                            (s :: List.take(lines, lastlines - 1), lastlines)
                          else
                            (s::lines, cnt + 1)
                    in
                      phase2 (lines, dirlines, cnt)
                    end
  val (p1_lines, p1_ok) = phase1 []
in
  if not p1_ok then (String.concat (List.rev p1_lines), false)
  else let
      val (p2_lines, p2_ok) = phase2 ([], [], 0)
      val p2_lines = tidy_p2_lines p2_lines
      val all_lines = String.concat (List.rev p1_lines @ List.rev p2_lines)
    in
      (all_lines, p2_ok)
    end
end


fun main() = let
  open TextIO
  val (from, sysdesc) = case CommandLine.arguments() of
               [f,s] => (f,s)
             | _ => usage()
  val (outputthis, succeeded) = filter_input stdIn
  val header =
      standard_header from
                      ((if succeeded then "SUCCESS: " else "FAILURE: ")^sysdesc)
in
  output(stdOut, header);
  output(stdOut, outputthis)
end

end
