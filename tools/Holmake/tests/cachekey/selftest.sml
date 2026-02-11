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

(* Tests 4-7: dependency chain scenarios *)
val _ = HOLFileSys.chDir "../depdir"

fun run_cachekey thy =
    let val tmp = OS.FileSys.tmpName ()
        val result =
            Systeml.systeml_out {outfile = tmp}
              ([Holmake] @ holstate_args @ ["--cachekey", thy])
        val line = if OS.Process.isSuccess result then read_line tmp else ""
    in
      OS.FileSys.remove tmp handle OS.SysErr _ => ();
      (OS.Process.isSuccess result, line)
    end

fun run_holmake args =
    Systeml.systeml ([Holmake] @ holstate_args @ args)

(* Test 4: --cachekey fails when ancestor is not built *)
val _ = tprint "Checking --cachekey fails when ancestor not built"
val _ = run_holmake ["cleanAll"]
val (ok4, _) = run_cachekey "childTheory"
val _ = if not ok4 then OK()
        else die "Expected failure when ancestor not built"

(* Test 5: build base, then --cachekey childTheory succeeds *)
val _ = tprint "Checking --cachekey succeeds after building ancestor"
val _ = run_holmake ["baseTheory"]
val (ok5, key5) = run_cachekey "childTheory"
val _ = if ok5 andalso size key5 = 40 then OK()
        else die ("Expected success with 40-char hash, got: \"" ^ key5 ^ "\"")

(* Test 6: modify a .ui file -> cachekey is unchanged
   (.ui files are excluded from the hash) *)
val _ = tprint "Checking --cachekey ignores .ui file changes"
val _ = let val uifile = ".hol/objs/baseTheory.ui"
        in
          if OS.FileSys.access(uifile, [OS.FileSys.A_WRITE]) then
            let val strm = TextIO.openAppend uifile
            in TextIO.output(strm, "extra junk\n");
               TextIO.closeOut strm
            end
          else die ("Cannot find " ^ uifile ^ " to modify")
        end
val (ok6, key6) = run_cachekey "childTheory"
val _ = if ok6 andalso key6 = key5 then OK()
        else die ("Expected same hash " ^ key5 ^ ", got: \"" ^ key6 ^ "\"")

(* Test 7: modify baseScript.sml without rebuilding -> same cachekey
   (the .dat file hasn't changed, so the cachekey shouldn't either) *)
val _ = tprint "Checking --cachekey unchanged when source modified but not rebuilt"
val _ = let val strm = TextIO.openOut "baseScript.sml"
        in TextIO.output(strm,
             "Theory base[bare]\n\
             \Ancestors bool\n\
             \Theorem base_thm = TRUTH\n\
             \Theorem base_thm2 = TRUTH\n");
           TextIO.closeOut strm
        end
val (ok7, key7) = run_cachekey "childTheory"
val _ = if ok7 andalso key7 = key5 then OK()
        else die ("Expected same hash " ^ key5 ^ ", got: \"" ^ key7 ^ "\"")

(* Test 8: rebuild base with modified source -> cachekey changes
   (the .dat file now contains a new theorem, so its hash differs) *)
val _ = tprint "Checking --cachekey changes after rebuilding modified ancestor"
val _ = run_holmake ["baseTheory"]
val (ok8, key8) = run_cachekey "childTheory"
val _ = if ok8 andalso size key8 = 40 andalso key8 <> key5 then OK()
        else die ("Expected different hash from " ^ key5 ^ ", got: \"" ^
                  key8 ^ "\"")

(* Clean up depdir and restore baseScript.sml *)
val _ = run_holmake ["cleanAll"]
val _ = let val strm = TextIO.openOut "baseScript.sml"
        in TextIO.output(strm,
             "Theory base[bare]\n\
             \Ancestors bool\n\
             \Theorem base_thm = TRUTH\n");
           TextIO.closeOut strm
        end
