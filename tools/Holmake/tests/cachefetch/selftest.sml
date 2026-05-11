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
(* Test 1: --cache-dir populates cache after building            *)
(* ------------------------------------------------------------ *)
val _ = tprint "cache-dir populates cache directory structure"
val _ = run_holmake ["cleanAll"]
val cache_populates = fresh_cache ()
val (res1, _) = run_holmake_out ["--cache-dir", cache_populates, "fooTheory"]
val _ =
    if OS.Process.isSuccess res1 andalso
       OS.FileSys.isDir (cache_populates ++ "data") andalso
       OS.FileSys.isDir (cache_populates ++ "key")
    then OK()
    else die "Expected cache/data and cache/key directories"

(* ------------------------------------------------------------ *)
(* Test 2: clean and rebuild fetches from populated cache        *)
(* ------------------------------------------------------------ *)
val _ = tprint "cache-dir fetches from populated cache"
val _ = run_holmake ["cleanAll"]
val (res2, out2) = run_holmake_out ["--cache-dir", cache_populates, "fooTheory"]
val _ =
    if OS.Process.isSuccess res2 andalso
       String.isSubstring "CACHED" out2
    then OK()
    else die ("Expected success with cache hit, got: " ^ out2)

(* ------------------------------------------------------------ *)
(* Test 3: corrupt manifest falls back to local build            *)
(* ------------------------------------------------------------ *)
val _ = tprint "cache-dir falls back on corrupt manifest"
val _ = run_holmake ["cleanAll"]
val cache_corrupt = fresh_cache ()
val _ = run_holmake_out ["--cache-dir", cache_corrupt, "fooTheory"]
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
val (res3, out3) = run_holmake_out ["--cache-dir", cache_corrupt, "fooTheory"]
val _ =
    if OS.Process.isSuccess res3 andalso
       HOLFileSys.access ("fooTheory.dat", [OS.FileSys.A_READ])
    then OK()
    else die ("Expected fallback after corrupt manifest, got: " ^ out3)

(* ------------------------------------------------------------ *)
(* Test 4: missing data files falls back to local build          *)
(* ------------------------------------------------------------ *)
val _ = tprint "cache-dir falls back when all data files missing"
val _ = run_holmake ["cleanAll"]
val cache_nodata = fresh_cache ()
val _ = run_holmake_out ["--cache-dir", cache_nodata, "fooTheory"]
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
val (res4, out4) = run_holmake_out ["--cache-dir", cache_nodata, "fooTheory"]
val _ =
    if OS.Process.isSuccess res4 andalso
       HOLFileSys.access ("fooTheory.dat", [OS.FileSys.A_READ])
    then OK()
    else die ("Expected fallback after missing data, got: " ^ out4)

(* ------------------------------------------------------------ *)
(* Test 5: partial cache hit (one data file missing) falls back  *)
(* ------------------------------------------------------------ *)
val _ = tprint "cache-dir falls back on partial cache hit"
val _ = run_holmake ["cleanAll"]
val cache_partial = fresh_cache ()
val _ = run_holmake_out ["--cache-dir", cache_partial, "fooTheory"]
(* Delete just the first data file *)
val datadir5 = cache_partial ++ "data"
val dds5 = OS.FileSys.openDir datadir5
val _ = case OS.FileSys.readDir dds5 of
            SOME f => OS.FileSys.remove (datadir5 ++ f)
          | NONE => ()
val _ = OS.FileSys.closeDir dds5
val _ = run_holmake ["cleanAll"]
val (res5, out5) = run_holmake_out ["--cache-dir", cache_partial, "fooTheory"]
val _ =
    if OS.Process.isSuccess res5 andalso
       HOLFileSys.access ("fooTheory.dat", [OS.FileSys.A_READ])
    then OK()
    else die ("Expected fallback after partial cache hit, got: " ^ out5)

(* ------------------------------------------------------------ *)
(* Test 6: empty cache dir is a miss, not an error               *)
(* ------------------------------------------------------------ *)
val _ = tprint "cache-dir on empty cache dir is a clean miss"
val _ = run_holmake ["cleanAll"]
val cache_empty = fresh_cache ()
val (res6, out6) = run_holmake_out ["--cache-dir", cache_empty, "fooTheory"]
val _ =
    if OS.Process.isSuccess res6 andalso
       HOLFileSys.access ("fooTheory.dat", [OS.FileSys.A_READ])
    then OK()
    else die ("Expected clean miss and local build, got: " ^ out6)

(* ------------------------------------------------------------ *)
(* Test 7: --no-cache disables caching entirely                  *)
(* ------------------------------------------------------------ *)
val _ = tprint "--no-cache disables caching"
val _ = run_holmake ["cleanAll"]
val cache_nocache = fresh_cache ()
val (res7, _) = run_holmake_out ["--no-cache", "fooTheory"]
val _ =
    if OS.Process.isSuccess res7 andalso
       not (OS.FileSys.isDir (cache_nocache ++ "data") handle OS.SysErr _ => false)
    then OK()
    else die "Expected no cache directory to be created"

(* ------------------------------------------------------------ *)
(* Test 8: cached dependency doesn't break dependent build       *)
(*   Build fooTheory alone (populating cache), clean everything, *)
(*   then build barTheory (which depends on foo).  fooTheory     *)
(*   should come from cache; barTheory should still build.       *)
(* ------------------------------------------------------------ *)
val _ = tprint "cached dependency doesn't break dependent build"
val _ = run_holmake ["cleanAll"]
val cache_dep = fresh_cache ()
(* Build only fooTheory to populate the cache *)
val _ = run_holmake_out ["--cache-dir", cache_dep, "fooTheory"]
(* Clean everything so foo must come from cache *)
val _ = run_holmake ["cleanAll"]
(* Now build barTheory which depends on fooTheory *)
val (res8, out8) = run_holmake_out ["--cache-dir", cache_dep, "barTheory"]
val _ =
    if OS.Process.isSuccess res8 andalso
       HOLFileSys.access ("barTheory.dat", [OS.FileSys.A_READ])
    then OK()
    else die ("Expected cached foo + successful bar build, got: " ^ out8)

(* ------------------------------------------------------------ *)
(* Test 9: false cache hit from different directory              *)
(*   Build fooTheory in subdir (populating cache), then create   *)
(*   a sibling directory with an identical fooScript.sml and a   *)
(*   dependent barScript.sml.  The cache key matches (same       *)
(*   script content + same deps), but the cached fooTheory.sml   *)
(*   embeds a .dat path pointing back at subdir/, so loading it  *)
(*   in the sibling directory fails.                             *)
(* ------------------------------------------------------------ *)
val _ = tprint "cross-directory false cache hit is detected"
val _ = run_holmake ["cleanAll"]
val cache_crossdir = fresh_cache ()
(* Build fooTheory in subdir to populate the cache *)
val _ = run_holmake_out ["--cache-dir", cache_crossdir, "fooTheory"]
val _ = run_holmake ["cleanAll"]
(* Create a sibling directory with identical script + dependent *)
val sibling = OS.Path.concat(OS.Path.concat(OS.FileSys.getDir(), ".."),
                             "subdir2")
val _ = OS.FileSys.mkDir sibling handle OS.SysErr _ => ()
fun write_file path contents =
    let val strm = TextIO.openOut path
    in TextIO.output(strm, contents); TextIO.closeOut strm end
val _ = write_file (sibling ++ "fooScript.sml")
                   "Theory foo[bare]\nAncestors bool\nTheorem foo_thm = TRUTH\n"
val _ = write_file (sibling ++ "barScript.sml")
                   "Theory bar[bare]\nAncestors foo\nTheorem bar_thm = foo_thm\n"
val _ = HOLFileSys.chDir sibling
val (res9, out9) = run_holmake_out ["--cache-dir", cache_crossdir, "barTheory"]
val _ = HOLFileSys.chDir ".."
val _ = HOLFileSys.chDir "subdir"
val _ =
    if OS.Process.isSuccess res9 andalso
       HOLFileSys.access (sibling ++ "barTheory.dat", [OS.FileSys.A_READ])
    then OK()
    else die ("Cross-directory cache hit broke dependent build: " ^ out9)

(* ------------------------------------------------------------ *)
(* Cleanup                                                       *)
(* ------------------------------------------------------------ *)
val _ = run_holmake ["cleanAll"]
val _ = List.app (fn c => rm_rf c handle _ => ())
        [cache_populates, cache_corrupt, cache_nodata, cache_partial,
         cache_empty, cache_nocache, cache_dep, cache_crossdir]
val _ = rm_rf sibling handle _ => ()
