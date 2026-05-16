structure HM_CacheFetch =
struct

val pid_s = SysWord.toString
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

(* Place [src]'s contents at [dest] atomically: stage at a per-pid
   temp file via clone_or_copy, then rename over [dest].  The rename
   is atomic, so a concurrent reader of [dest] sees either the
   previous contents or the new contents, never a partial write. *)
fun copy src dest =
    let
      val tmp = dest ^ ".tmp." ^ pid_s
      val _ = OS.FileSys.remove tmp handle _ => ()
      fun fail () = (OS.FileSys.remove tmp handle _ => (); false)
    in
      if not (clone_or_copy src tmp) then fail ()
      else
        (* Touch tmp's (independent) inode to "now" so the cache hit
           looks newer than any in-tree dependency to downstream
           timestamp-based rebuild checks. *)
        (OS.FileSys.setTime (tmp, NONE) handle _ => ();
         OS.FileSys.rename {old = tmp, new = dest}; true)
        handle _ => fail ()
    end

val mkDir = HOLFS_dtype.createDirIfNecessary

fun already_cached base key =
    OS.FileSys.access(OS.Path.concat(OS.Path.concat(base, "key"), key), [])

fun is_theory_output f =
    String.isSuffix "Theory.sml" f orelse
    String.isSuffix "Theory.sig" f orelse
    String.isSuffix "Theory.dat" f

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

fun fetch base_url cachekey (ofns : Holmake_tools.output_functions) =
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
                val ok = List.all
                             (fn {name, url} =>
                                 fetch_to_file (base_url ^ url) (to_dest_dir name))
                             files
                val _ = if ok
                        then info "Cache hit! local theory building can be skipped."
                        else warn "Only managed a partial cache hit; theory will be built locally."
            in
                ok
            end
            handle _ => let
                val _ = warn "Something went wrong; theory will be built locally."
            in
                false
            end
    end

end
