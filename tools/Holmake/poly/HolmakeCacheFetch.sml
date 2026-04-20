structure HolmakeCacheFetch =
struct

open HolmakeCacheKey

fun copy src dest =
    let val instr  = BinIO.openIn src
        val outstr = BinIO.openOut dest
        fun loop () =
            let val v = BinIO.inputN (instr, 1024)
            in  if Word8Vector.length v = 0
                then (BinIO.flushOut outstr; BinIO.closeOut outstr; BinIO.closeIn instr)
                else (BinIO.output (outstr, v); loop ())
            end
    in  loop (); true end
    handle _ => false

fun upload base_url cachekey dir thyname info warn =
    let
        val _ = OS.FileSys.mkDir base_url handle OS.SysErr _ => ()
        val theory_exts = [".sig", ".sml", ".dat"]
        fun is_theory_file f =
            List.exists (fn ext => f = thyname ^ ext) theory_exts
        fun scan_dir d =
            let val ds = OS.FileSys.openDir d
                fun loop acc =
                    case OS.FileSys.readDir ds of
                        NONE => (OS.FileSys.closeDir ds; acc)
                      | SOME f =>
                        if is_theory_file f then
                            loop ({name = f, path = OS.Path.concat(d, f)} :: acc)
                        else loop acc
            in loop [] handle e => (OS.FileSys.closeDir ds; raise e) end
        val obj_dir = OS.Path.concat(dir, OS.Path.concat(".hol", "objs"))
        val files =
            scan_dir dir @
            (if OS.FileSys.isDir obj_dir handle OS.SysErr _ => false
             then scan_dir obj_dir
             else [])
        val data_dir = OS.Path.concat(base_url, "data")
        val _ = OS.FileSys.mkDir data_dir handle OS.SysErr _ => ()
        fun process {name, path} =
            let val hash = SHA1.sha1_file {filename = path}
                val ok = copy path (OS.Path.concat(data_dir, hash))
            in
                if ok then SOME (name, hash) else NONE
            end
        val _ = if null files then
                    raise Fail (thyname ^ " has no built theory files to cache")
                else ()
        val results = List.mapPartial process files
        val ok = length results = length files
        val _ = OS.FileSys.mkDir (OS.Path.concat(base_url, "key")) handle OS.SysErr _ => ()
        val manifest_path = OS.Path.concat(OS.Path.concat(base_url, "key"), cachekey)
        fun entry_to_json (name, hash) =
            "{\"name\": \"" ^ name ^ "\", \"url\": \"/data/" ^ hash ^ "\"}"
        val json = "{\"files\": [" ^ String.concatWith ", " (map entry_to_json results) ^ "]}"
        val out = TextIO.openOut manifest_path
        val _ = TextIO.output(out, json)
        val _ = TextIO.closeOut out
    in
        if ok then (info ("Cached " ^ thyname); true)
        else (warn ("Cache failed for " ^ thyname); false)
    end
    handle e => (warn ("Write failed: " ^ exnMessage e); false)

fun fetch base_url cachekey info warn =
    let
        val fetch_to_file = copy
        val key_url = base_url ^ "/key/" ^ cachekey
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
                      | SOME {fullfile, ...} => fullfile
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
