open testutils

val _ = OS.FileSys.chDir "testdir";

val _ = tprint "Calling Holmake in testdir"

fun hm s =
  let
    val res = OS.Process.system ("../../../../../bin/Holmake " ^ s)
  in
    if not (OS.Process.isSuccess res) then
      die ("Holmake "^s^" failed")
    else ()
  end

val _ =
    let
      val _ = hm "cleanAll"
      val _ = hm "> output"
      val res = OS.Process.system ("../../../../cmp/cmp.exe output expected")
    in
      if OS.Process.isSuccess res then OK()
      else die "cmp FAILED"
    end
