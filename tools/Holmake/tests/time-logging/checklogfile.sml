(* use mosml -quietdec -P full , or poly -q *)
val verdictfile_strm = TextIO.openIn "verdict"

val verdict = case TextIO.inputLine verdictfile_strm of
                  SOME "ok\n" => true
                | SOME "bad\n" => false
                | _ => OS.Process.exit OS.Process.failure

val _ = TextIO.closeIn verdictfile_strm

val expected_pfx = if verdict then "hmlog-good-" else "hmlog-bad-"

val dir_strm = OS.FileSys.openDir "."

fun killit s = if not (OS.FileSys.isDir s) then
                 OS.FileSys.remove s handle _ => ()
               else ()


fun checkfiles files seenlog_status =
    case OS.FileSys.readDir dir_strm of
        NONE => (List.app killit files;
                 OS.Process.exit seenlog_status)
      | SOME s => if String.isPrefix expected_pfx s then
                    checkfiles (s::files) OS.Process.success
                  else if s = "testScript.sml" orelse s = "verdict" then
                    checkfiles files seenlog_status
                  else checkfiles (s::files) seenlog_status

val _ = checkfiles [] OS.Process.failure
