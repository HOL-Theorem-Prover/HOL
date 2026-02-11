open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"
val holstate_args =
    if Systeml.ML_SYSNAME = "poly" then
      ["--holstate", Globals.HOLDIR ++ "bin" ++ "hol.state0"]
    else []

val _ = HOLFileSys.chDir "subdir"

(* Test 1: --cachekey produces output *)
val _ = tprint "Checking --cachekey produces a hash"
val tmpfile1 = OS.FileSys.tmpName ()
val result1 =
    Systeml.systeml_out {outfile = tmpfile1}
      ([Holmake] @ holstate_args @ ["--cachekey", "fooTheory"])
fun read_line f =
    let val strm = TextIO.openIn f
        val result = case TextIO.inputLine strm of
                         SOME s => (String.substring(s, 0, size s - 1)
                                    handle Subscript => "")
                       | NONE => ""
    in TextIO.closeIn strm; result end
    handle IO.Io _ => ""

val line1 = if OS.Process.isSuccess result1 then read_line tmpfile1 else ""
val _ = OS.FileSys.remove tmpfile1 handle OS.SysErr _ => ()
val _ = if size line1 = 40 andalso
           CharVector.all Char.isHexDigit line1 then OK()
        else die ("Expected 40 hex chars, got: \"" ^ line1 ^ "\"")

(* Test 2: --cachekey is deterministic *)
val _ = tprint "Checking --cachekey is deterministic"
val tmpfile2 = OS.FileSys.tmpName ()
val result2 =
    Systeml.systeml_out {outfile = tmpfile2}
      ([Holmake] @ holstate_args @ ["--cachekey", "fooTheory"])
val line2 = if OS.Process.isSuccess result2 then read_line tmpfile2 else ""
val _ = OS.FileSys.remove tmpfile2 handle OS.SysErr _ => ()
val _ = if line1 = line2 then OK()
        else die ("Hashes differ: " ^ line1 ^ " vs " ^ line2)

(* Test 3: --cachekey fails on non-theory target *)
val _ = tprint "Checking --cachekey rejects non-theory target"
val tmpfile3 = OS.FileSys.tmpName ()
val result3 =
    Systeml.systeml_out {outfile = tmpfile3}
      ([Holmake] @ holstate_args @ ["--cachekey", "fooScript"])
val _ = OS.FileSys.remove tmpfile3 handle OS.SysErr _ => ()
val _ = if not (OS.Process.isSuccess result3) then OK()
        else die "Expected failure for non-theory target"
