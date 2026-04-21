open testutils

val op++ = OS.Path.concat
val Holmake = Globals.HOLDIR ++ "bin" ++ "Holmake"
val holstate_args =
    if Systeml.ML_SYSNAME = "poly" then
      ["--holstate", Globals.HOLDIR ++ "bin" ++ "hol.state0"]
    else []

fun read_all f =
    let val strm = TextIO.openIn f
        val s = TextIO.inputAll strm
    in TextIO.closeIn strm; s end
    handle IO.Io _ => ""

fun run_holmake args =
    Systeml.systeml ([Holmake] @ holstate_args @ args)

fun run_holmake_out args =
    let val tmp = OS.FileSys.tmpName ()
        val result =
            Systeml.systeml_out {outfile = tmp}
              ([Holmake] @ holstate_args @ args)
        val output = read_all tmp
    in
      OS.FileSys.remove tmp handle OS.SysErr _ => ();
      (result, output)
    end

(* Create a fresh temporary directory for use as a cache *)
fun fresh_cache () =
    let val base = OS.FileSys.tmpName ()
        (* tmpName gives us a filename; remove and recreate as dir *)
        val _ = OS.FileSys.remove base handle OS.SysErr _ => ()
        val _ = OS.FileSys.mkDir base
    in base end

fun rm_rf path =
    let
      fun rm p =
          if OS.FileSys.isDir p handle OS.SysErr _ => false then
            let val ds = OS.FileSys.openDir p
                fun loop () =
                    case OS.FileSys.readDir ds of
                        NONE => (OS.FileSys.closeDir ds;
                                 OS.FileSys.rmDir p)
                      | SOME f => (rm (p ++ f); loop ())
            in loop () end
          else
            OS.FileSys.remove p handle OS.SysErr _ => ()
    in rm path end

val _ = HOLFileSys.chDir "subdir"

(* ------------------------------------------------------------ *)
(* Test 1: --write-cache produces cache files after building     *)
(* ------------------------------------------------------------ *)
val _ = tprint "write-cache produces cache directory structure"
val _ = run_holmake ["cleanAll"]
val _ = run_holmake ["fooTheory"]
val cache_pop = fresh_cache ()
val (res1, _) = run_holmake_out ["--write-cache", cache_pop, "fooTheory"]
val _ =
    if OS.Process.isSuccess res1 andalso
       OS.FileSys.isDir (cache_pop ++ "data") andalso
       OS.FileSys.isDir (cache_pop ++ "key")
    then OK()
    else die "Expected cache/data and cache/key directories"

(* ------------------------------------------------------------ *)
(* Test 2: --use-cache fetches from a populated cache            *)
(* ------------------------------------------------------------ *)
val _ = tprint "use-cache fetches from populated cache"
val _ = run_holmake ["cleanAll"]
val (res2, out2) = run_holmake_out ["--use-cache", cache_pop, "fooTheory"]
val _ =
    if OS.Process.isSuccess res2 andalso
       String.isSubstring "CACHED" out2
    then OK()
    else die ("Expected success with cache hit, got: " ^ out2)

(* ------------------------------------------------------------ *)
(* Test 3: --use-cache with corrupt manifest falls back          *)
(* ------------------------------------------------------------ *)
val _ = tprint "use-cache falls back on corrupt manifest"
val _ = run_holmake ["cleanAll"]
val _ = run_holmake ["fooTheory"]
val cache_corrupt = fresh_cache ()
val _ = run_holmake_out ["--write-cache", cache_corrupt, "fooTheory"]
(* Corrupt every manifest in the key dir *)
val keydir = cache_corrupt ++ "key"
val ds = OS.FileSys.openDir keydir
fun corrupt_all () =
    case OS.FileSys.readDir ds of
        NONE => OS.FileSys.closeDir ds
      | SOME f =>
        let val path = keydir ++ f
            val strm = TextIO.openOut path
        in
          TextIO.output(strm, "THIS IS NOT JSON{{{");
          TextIO.closeOut strm;
          corrupt_all ()
        end
val _ = corrupt_all ()
val _ = run_holmake ["cleanAll"]
val (res3, out3) = run_holmake_out ["--use-cache", cache_corrupt, "fooTheory"]
val _ =
    if OS.Process.isSuccess res3 andalso
       HOLFileSys.access ("fooTheory.dat", [OS.FileSys.A_READ])
    then OK()
    else die ("Expected fallback after corrupt manifest, got: " ^ out3)

(* ------------------------------------------------------------ *)
(* Test 4: --use-cache with all data files missing falls back    *)
(* ------------------------------------------------------------ *)
val _ = tprint "use-cache falls back when all data files missing"
val _ = run_holmake ["cleanAll"]
val _ = run_holmake ["fooTheory"]
val cache_nodata = fresh_cache ()
val _ = run_holmake_out ["--write-cache", cache_nodata, "fooTheory"]
(* Delete all files under data/ so manifest points to nothing *)
val datadir4 = cache_nodata ++ "data"
val dds4 = OS.FileSys.openDir datadir4
fun delete_all () =
    case OS.FileSys.readDir dds4 of
        NONE => OS.FileSys.closeDir dds4
      | SOME f => (OS.FileSys.remove (datadir4 ++ f) handle OS.SysErr _ => ();
                   delete_all ())
val _ = delete_all ()
val _ = run_holmake ["cleanAll"]
val (res4, out4) = run_holmake_out ["--use-cache", cache_nodata, "fooTheory"]
val _ =
    if OS.Process.isSuccess res4 andalso
       HOLFileSys.access ("fooTheory.dat", [OS.FileSys.A_READ])
    then OK()
    else die ("Expected fallback after missing data, got: " ^ out4)

(* ------------------------------------------------------------ *)
(* Test 5: partial cache hit (one data file missing) falls back  *)
(* ------------------------------------------------------------ *)
val _ = tprint "use-cache falls back on partial cache hit"
val _ = run_holmake ["cleanAll"]
val _ = run_holmake ["fooTheory"]
val cache_partial = fresh_cache ()
val _ = run_holmake_out ["--write-cache", cache_partial, "fooTheory"]
(* Delete just the first data file so the manifest is valid but
   one fetch fails -- exercises the "partial cache hit" path *)
val datadir5 = cache_partial ++ "data"
val dds5 = OS.FileSys.openDir datadir5
val _ = case OS.FileSys.readDir dds5 of
            SOME f => OS.FileSys.remove (datadir5 ++ f)
          | NONE => ()
val _ = OS.FileSys.closeDir dds5
val _ = run_holmake ["cleanAll"]
val (res5, out5) = run_holmake_out ["--use-cache", cache_partial, "fooTheory"]
val _ =
    if OS.Process.isSuccess res5 andalso
       HOLFileSys.access ("fooTheory.dat", [OS.FileSys.A_READ])
    then OK()
    else die ("Expected fallback after partial cache hit, got: " ^ out5)

(* ------------------------------------------------------------ *)
(* Test 6: --write-cache to unwritable location fails gracefully *)
(* ------------------------------------------------------------ *)
val _ = tprint "write-cache fails gracefully on unwritable location"
val _ = run_holmake ["cleanAll"]
val _ = run_holmake ["fooTheory"]
val cache_ro = fresh_cache ()
(* Make the cache dir read-only *)
val _ = OS.Process.system ("chmod 444 " ^ cache_ro)
val (res6, _) = run_holmake_out ["--write-cache", cache_ro, "fooTheory"]
(* Restore perms for cleanup *)
val _ = OS.Process.system ("chmod 755 " ^ cache_ro)
val _ =
    if not (OS.Process.isSuccess res6) then OK()
    else die "Expected failure writing to read-only cache dir"

(* ------------------------------------------------------------ *)
(* Test 7: --use-cache on empty cache dir is a miss, not error   *)
(* ------------------------------------------------------------ *)
val _ = tprint "use-cache on empty cache dir is a clean miss"
val _ = run_holmake ["cleanAll"]
val cache_empty = fresh_cache ()
val (res7, out7) = run_holmake_out ["--use-cache", cache_empty, "fooTheory"]
val _ =
    if OS.Process.isSuccess res7 andalso
       HOLFileSys.access ("fooTheory.dat", [OS.FileSys.A_READ])
    then OK()
    else die ("Expected clean miss and local build, got: " ^ out7)

(* ------------------------------------------------------------ *)
(* Cleanup                                                       *)
(* ------------------------------------------------------------ *)
val _ = run_holmake ["cleanAll"]
val _ = List.app (fn c => rm_rf c handle _ => ())
        [cache_pop, cache_corrupt, cache_nodata, cache_partial,
         cache_ro, cache_empty]
