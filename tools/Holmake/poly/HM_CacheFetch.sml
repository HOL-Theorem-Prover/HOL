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

   We avoid adding HOLsexp to Holmake's mlb (the cleaner option) by
   doing a small textual scan of the .dat header.  The format is
   stable:
       (theory ("<thyname>" ("<parent1>" . "<hash1>") ... )
        (core-data ...) ...)
   Each parent is encoded as a sub-list ("<thy>" . "<hash>"), all
   inside the first sub-list of (theory ...).  We only scan the
   substring up to "(core-data" to avoid matching string pairs that
   might appear inside the theorem tables.

   HOLsexp pretty-prints with INCONSISTENT breaks, so the whitespace
   immediately after "theory" can be a space OR a newline depending on
   whether the thid+parents sublist fits on the same line: bool's tiny
   ("bool" ("min" . "")) fits, but any theory with a 40-char SHA-1
   parent hash typically doesn't and wraps.  We accept any whitespace. *)

fun read_file path =
    let val ins = TextIO.openIn path
        val s = TextIO.inputAll ins
        val _ = TextIO.closeIn ins
    in s end
    handle _ => ""

fun extract_parents dat_path =
    let
      val content = read_file dat_path
      val full = Substring.full content
      val (_, at_theory) = Substring.position "(theory" full
    in
      if Substring.size at_theory < 7 then []
      else
        let
          val after_theory =
              Substring.dropl Char.isSpace (Substring.triml 7 at_theory)
          val (header, _) = Substring.position "(core-data" after_theory
          fun loop ss acc =
              let val (_, rest) = Substring.position "(\"" ss
              in
                if Substring.size rest < 2 then List.rev acc
                else
                  let
                    val after_open = Substring.triml 2 rest
                    val (xss, ass) = Substring.position "\"" after_open
                  in
                    if Substring.size ass < 1 then List.rev acc
                    else
                      let val ass1 = Substring.triml 1 ass (* skip closing " *)
                      in
                        if Substring.isPrefix " . \"" ass1 then
                          let
                            val ass2 = Substring.triml 4 ass1
                            val (yss, ass3) = Substring.position "\"" ass2
                          in
                            if Substring.size ass3 >= 1 then
                              loop (Substring.triml 1 ass3)
                                   ((Substring.string xss,
                                     Substring.string yss) :: acc)
                            else List.rev acc
                          end
                        else loop ass1 acc
                      end
                  end
              end
        in loop header [] end
    end
    handle _ => []

(* Locate the current on-disk Theory.dat for [thy].  We look in sigobj
   first (where exported theories live, with .uo as a symlink to the
   source dir); if that resolves, the .dat sits next to the resolved
   .uo.  Returns NONE if we cannot locate a current .dat: the caller
   should treat that as a validation failure since we cannot verify
   the cached .dat's parent hash. *)
val SIGOBJ = OS.Path.concat (Systeml.HOLDIR, "sigobj")

(* Locate the current on-disk Theory.dat for [thy].  We try, in order:

   (a) Each directory in [search_dirs] (which the caller derives from
       the dep graph's known targets / deps -- so this covers downstream
       projects with their own theory hierarchies that are NOT
       linkToSigobj'd into core HOL's sigobj).  For each dir D we try
       D/.hol/objs/<thy>Theory.dat (the Poly/ML munged location) and
       D/<thy>Theory.dat (the Moscow ML / unmunged location).
   (b) sigobj/<thy>Theory.dat, falling back to following the
       sigobj/<thy>Theory.uo symlink via realPath and looking next to
       the resolved .uo -- handles core HOL where theories are
       linkToSigobj'd. *)
fun find_parent_dat search_dirs thy =
    let
      val basename = thy ^ "Theory"
      val datname = basename ^ ".dat"
      fun access p = OS.FileSys.access (p, [OS.FileSys.A_READ])
                     handle _ => false
      fun in_dir d =
          let val munged = OS.Path.concat (d,
                              OS.Path.concat (".hol",
                                 OS.Path.concat ("objs", datname)))
              val plain = OS.Path.concat (d, datname)
          in
            if access munged then SOME munged
            else if access plain then SOME plain
            else NONE
          end
      fun first f [] = NONE
        | first f (x :: xs) = case f x of SOME y => SOME y | NONE => first f xs
      val sigobj_uo = OS.Path.concat (SIGOBJ, basename ^ ".uo")
      val sigobj_dat = OS.Path.concat (SIGOBJ, datname)
    in
      case first in_dir search_dirs of
          SOME p => SOME p
        | NONE =>
          if access sigobj_dat then SOME sigobj_dat
          else if access sigobj_uo then
            let val real_uo = OS.FileSys.realPath sigobj_uo
                val real_dir = OS.Path.dir real_uo
                val candidate = OS.Path.concat (real_dir, datname)
            in
              if access candidate then SOME candidate else NONE
            end handle OS.SysErr _ => NONE
          else NONE
    end

(* Validate that the parent hashes recorded in [dat_path] match the
   hashes of the current on-disk parents.  An empty extracted-parents
   list means we couldn't parse the .dat header at all (every real
   theory has at least one parent in its .dat -- bool records "min"
   even though "min" has no .dat of its own) so we fail-safe and
   reject the cache. *)
fun validate_dat search_dirs dat_path =
    let
      val parents = extract_parents dat_path
      fun check (thy, recorded_hash) =
          case find_parent_dat search_dirs thy of
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
