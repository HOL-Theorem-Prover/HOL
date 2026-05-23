structure HM_CacheFetch =
struct

(* The PID has to be sampled per call: Holmake is delivered as a
   polyc-compiled binary whose saved Poly heap freezes any top-level
   val.  A val pid_s computed at module load thus captures the build-
   time PID, and every Holmake invocation that loads the heap sees the
   same value -- so two concurrent Holmakes write to the same
   ".tmp.<pid>" path and race on rename. *)
fun pid_s () = SysWord.toString
                 (Posix.Process.pidToWord (Posix.ProcEnv.getpid()))

(* Byte-copy [src] to [dst]; returns true on success.  Used as a
   fallback when no reflink-capable cp is available, or when the
   reflink invocation fails (e.g. filesystem doesn't support it and
   the cp variant doesn't fall back internally). *)
fun byte_copy src dst =
    let val instr  = BinIO.openIn src
        val outstr = BinIO.openOut dst
        fun loop () =
            let val v = BinIO.inputN (instr, 1024)
            in  if Word8Vector.length v = 0
                then (BinIO.flushOut outstr; BinIO.closeOut outstr;
                      BinIO.closeIn instr; true)
                else (BinIO.output (outstr, v); loop ())
            end
    in loop () end
    handle _ => false

(* Stage [src]'s contents at [dst] with an independent inode.  Tries
   the platform's reflink-capable cp first (gives hardlink-style space
   efficiency on CoW filesystems like APFS/btrfs/XFS-with-reflink
   while keeping inodes separate); falls back to a byte-copy when
   no clone command is configured or it fails.

   Independent inodes matter for the Holmake product cache: a previous
   implementation hard-linked into the cache, so a subsequent
   setTime(dst, NONE) bumped the mtime on the *shared* inode, which
   propagated to any sibling repo whose local Theory.* was also hard-
   linked to the same cache entry.  The sibling would then see its
   local Theory.* as newer than its derived .ui/.uo and spuriously
   rebuild them. *)
fun clone_or_copy src dst =
    case Systeml.clone_cmd of
        SOME cmd =>
          if OS.Process.isSuccess
               (OS.Process.system (cmd ^ " " ^ Systeml.protect src ^
                                   " " ^ Systeml.protect dst))
          then true
          else byte_copy src dst
      | NONE => byte_copy src dst

(* Stage [src]'s contents at a per-pid temp file next to [dest] and
   return the temp path on success.  The caller is responsible for
   either committing the temp to [dest] via [commit_staged] or
   discarding it via [discard_staged]. *)
fun stage src dest =
    let
      val tmp = dest ^ ".tmp." ^ pid_s ()
      val _ = OS.FileSys.remove tmp handle _ => ()
    in
      if not (clone_or_copy src tmp) then
        (OS.FileSys.remove tmp handle _ => (); NONE)
      else
        (* Touch tmp's (independent) inode to "now" so the cache hit
           looks newer than any in-tree dependency to downstream
           timestamp-based rebuild checks. *)
        (OS.FileSys.setTime (tmp, NONE) handle _ => ();
         SOME tmp)
    end

fun commit_staged tmp dest =
    (OS.FileSys.rename {old = tmp, new = dest}; true)
    handle _ => (OS.FileSys.remove tmp handle _ => (); false)

fun discard_staged tmp =
    OS.FileSys.remove tmp handle _ => ()

(* Place [src]'s contents at [dest] atomically: stage then commit.
   Kept for upload's per-file copy into the cache's data/ directory
   where staged validation isn't needed. *)
fun copy src dest =
    case stage src dest of
        NONE => false
      | SOME tmp => commit_staged tmp dest

val mkDir = HOLFS_dtype.createDirIfNecessary

fun already_cached base key =
    OS.FileSys.access(OS.Path.concat(OS.Path.concat(base, "key"), key), [])

fun is_theory_output f =
    String.isSuffix "Theory.sml" f orelse
    String.isSuffix "Theory.sig" f orelse
    String.isSuffix "Theory.dat" f

(* --- Fetch-time parent-hash validation -------------------------------

   The cachekey can miss transitive theory parents (see GitHub #1980),
   so a cache hit may return a Theory.dat whose recorded parent hashes
   no longer match the current on-disk parents.  Loading that .dat
   would fail link_parents.  Detect and treat as a cache miss.

   The textual scan of the .dat header lives in core/HM_TheoryDat so
   that HM_Cachekey can use the same parser without picking up a
   dependency on this poly-only module. *)

(* Validate that the parent hashes recorded in [dat_path] match the
   hashes of the current on-disk parents.  An empty extracted-parents
   list means we couldn't parse the .dat header at all (every real
   theory has at least one parent in its .dat -- bool records "min"
   even though "min" has no .dat of its own) so we fail-safe and
   reject the cache. *)
fun validate_dat search_dirs dat_path =
    let
      val parents = HM_TheoryDat.extract_parents dat_path
      fun check (thy, recorded_hash) =
          case HM_TheoryDat.find_parent_dat search_dirs thy of
              NONE => false   (* can't locate current parent; fail-safe *)
            | SOME path =>
                (SHA1.sha1_file {filename = path} = recorded_hash
                 handle _ => false)
    in
      not (List.null parents) andalso List.all check parents
    end

fun upload base_url cachekey dir filenames (ofns : Holmake_tools.output_functions) =
    case cachekey of
        HM_Cachekey.Missing _ => false
      | HM_Cachekey.Key key =>
    if already_cached base_url key then true else
    if not (List.all is_theory_output filenames) then false else
    let
        val {info, warn, ...} = ofns
        val _ = mkDir base_url handle OS.SysErr _ => ()
        val obj_dir = OS.Path.concat(dir, OS.Path.concat(".hol", "objs"))
        fun find_file f =
            let val in_objs = OS.Path.concat(obj_dir, f)
                val in_dir = OS.Path.concat(dir, f)
                val path = if OS.FileSys.access(in_objs, []) then SOME in_objs
                           else if OS.FileSys.access(in_dir, []) then SOME in_dir
                           else NONE
            in
                Option.map (fn p => {name = f, path = p}) path
            end
        val files = List.mapPartial find_file filenames
        val data_dir = OS.Path.concat(base_url, "data")
        val _ = mkDir data_dir handle OS.SysErr _ => ()
        fun process {name, path} =
            let val hash = SHA1.sha1_file {filename = path}
                val ok = copy path (OS.Path.concat(data_dir, hash))
            in
                if ok then SOME (name, hash) else NONE
            end
        val all_found = length files = length filenames
        val results = List.mapPartial process files
        val all_processed = length results = length files
        val ok = all_found andalso all_processed
    in
        if ok then let
            val _ = mkDir (OS.Path.concat(base_url, "key"))
                    handle OS.SysErr _ => ()
            val manifest_path =
                OS.Path.concat(OS.Path.concat(base_url, "key"), key)
            fun entry_to_json (name, hash) =
                "{\"name\": \"" ^ name ^
                "\", \"url\": \"/data/" ^ hash ^ "\"}"
            val json = "{\"files\": [" ^
                       String.concatWith ", "
                         (map entry_to_json results) ^ "]}"
            val out = TextIO.openOut manifest_path
            val _ = TextIO.output(out, json)
            val _ = TextIO.closeOut out
        in true end
        else (warn "Cache upload: not all files found; skipping"; false)
    end handle _ => false

fun fetch base_url cachekey search_dirs (ofns : Holmake_tools.output_functions) =
    case cachekey of
        HM_Cachekey.Missing _ => false
      | HM_Cachekey.Key key =>
    let
        val {info, warn, ...} = ofns
        val fetch_to_file = copy
        val key_url = base_url ^ "/key/" ^ key
        val file = OS.FileSys.tmpName()
        fun cleanup() = (OS.FileSys.remove file handle OS.SysErr _ => ())
        val _ = info "Checking cache for prebuilt theory..."
        val hit = fetch_to_file key_url file
    in
        if not hit then let
            val _ = cleanup()
            val _ = info "Cache miss; theory will be built locally."
        in
            false
        end
        else
            let
                val src = JSONParser.openFile file
                val json = JSONParser.parse src before JSONParser.close src
                val _ = cleanup()
                val files = JSONUtil.arrayMap
                                (fn v => { name = JSONUtil.asString (JSONUtil.lookupField v "name"),
                                           url  = JSONUtil.asString (JSONUtil.lookupField v "url") })
                                (JSONUtil.lookupField json "files")
                fun to_dest_dir s =
                    case HFS_NameMunge.HOLtoFS s of
                        NONE => s
                      | SOME {fullfile, dir} =>
                        (mkDir dir handle _ => ();
                         fullfile)
                (* Stage all files to tmp paths first (NOT yet visible
                   at their dest paths).  Validate from tmp.  Only
                   commit (rename tmp -> dest) if validation passes.
                   This avoids exposing potentially-stale cache contents
                   to concurrent Holmake processes that might read the
                   dest paths while validation is still in progress. *)
                val staged = map (fn {name, url} =>
                                    let val dest = to_dest_dir name
                                        val tmp_opt = stage
                                                       (base_url ^ url) dest
                                    in {name = name, dest = dest,
                                        tmp = tmp_opt}
                                    end)
                                  files
                fun discard_all () =
                    List.app (fn {tmp = SOME t, ...} => discard_staged t
                               | _ => ())
                             staged
                val all_staged = List.all (fn {tmp, ...} => isSome tmp) staged
            in
                if not all_staged then
                  (discard_all ();
                   warn "Only managed a partial cache hit; theory will \
                        \be built locally.";
                   false)
                else
                  let
                    val all_valid =
                        List.all
                          (fn {name, tmp = SOME t, ...} =>
                              not (String.isSuffix "Theory.dat" name)
                              orelse validate_dat search_dirs t
                            | _ => false)
                          staged
                  in
                    if all_valid then
                      (List.app (fn {tmp = SOME t, dest, ...} =>
                                    ignore (commit_staged t dest)
                                  | _ => ())
                                staged;
                       info "Cache hit! local theory building can be skipped.";
                       true)
                    else
                      (discard_all ();
                       warn "Cache hit ignored: parent hashes do not match \
                            \current on-disk parents; theory will be built \
                            \locally.";
                       false)
                  end
            end
            handle _ => let
                val _ = warn "Something went wrong; theory will be built locally."
            in
                false
            end
    end

end
