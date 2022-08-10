structure generateBuildSummary =
struct



(* reads the output of bin/build on standard input, and turns it into a
   mail message *)

infix |>
fun (x |> f) = f x

fun die s = (TextIO.output(TextIO.stdErr, s^"\n");
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

val lastlines = 80

fun tidy_p2_lines linelist = let
  val maxlen = List.foldl (fn (l,acc) => Int.max(size l, acc)) 0 linelist
  val maxlen = Int.max(78, maxlen)
  fun make_maxlen s =
    if size s = maxlen then s
    else
      let
        val szs1 = size s - 1
        fun findldelim c i =
            if i < 0 orelse String.sub(s, i) = c then i
            else findldelim c (i - 1)
        val cutpoint =
            let
              val lpi = findldelim #"(" szs1
            in
              if lpi < 0 then findldelim #"[" szs1 else lpi
            end
      in
        if cutpoint < 0 then StringCvt.padRight #" " maxlen s
        else
          let
            val pfx = String.extract(s, 0, SOME cutpoint)
            val spaces = CharVector.tabulate(maxlen - size s, (fn _ => #" "))
            val sfx = String.extract(s, cutpoint, NONE)
          in
            pfx ^ spaces ^ sfx
          end
    end
in
  map (fn s => make_maxlen s ^ "\n") linelist
end

fun delete_trailing_wspace s =
    let
      open Substring
    in
      s |> full |> dropr Char.isSpace |> string
    end

fun filter_input instr = let
  fun phase1 lines =
      case TextIO.inputLine instr of
        NONE => (lines, false)
      | SOME s => if s = "-- Configuration Description Ends --\n" then
                    ("\n"::s::lines, true)
                  else phase1 (s::lines)
  fun phase2 (lines, dirlines, cnt) =
      case Option.map remove_nulls (TextIO.inputLine instr) of
        NONE => (if length lines > lastlines then List.take(lines, lastlines)
                 else lines, false)
      | SOME s0 =>
        let val s = s0 |> Holmake_tools.strip_codes
                       |> delete_trailing_wspace
        in
          if s = "Hol built successfully." then (dirlines, true)
          else let
            val dirlines =
                if String.isPrefix "Building directory" s orelse
                   String.isPrefix "Finished $(HOLDIR)" s
                then
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
        end
  val (p1_lines, p1_ok) = phase1 []
in
  if not p1_ok then (String.concat (List.rev p1_lines), false)
  else let
      val (p2_lines, p2_ok) = phase2 ([], [], 0)
      val p2_lines = if p2_ok then tidy_p2_lines p2_lines
                     else map (fn s => s ^ "\n") p2_lines
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
end handle e => die ("Unexpected exception: "^exnMessage e)

end
