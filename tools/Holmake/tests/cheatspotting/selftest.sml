open testutils

val _ = OS.FileSys.chDir "testdir";

val _ = tprint "Calling Holmake in testdir"

fun hm s =
  let
    val res = OS.Process.system ("../../../../../bin/Holmake --noqof " ^ s)
  in
    if not (OS.Process.isSuccess res) then
      die ("Holmake "^s^" failed")
    else ()
  end

fun check_for_cheated () =
  let
    val istrm = TextIO.openIn "output"
    val outstr = TextIO.inputAll istrm before TextIO.closeIn istrm
  in
    String.isSubstring "CHEATED" outstr
  end

val _ =
    let
      val _ = hm "cleanAll"
      val _ = hm "> output"
    in
      if check_for_cheated () then OK()
      else die "cmp FAILED"
    end
