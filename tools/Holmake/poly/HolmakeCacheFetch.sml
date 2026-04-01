structure HolmakeCacheFetch =
struct

open HolmakeCacheKey

fun curl_get_to_file url dest =
    (* curl
       -s <silent mode; don't show progress meter etc.>
       -f <return nonzero status code for http errors (e.g. 404s from a cache miss)>
       -m <timeout in seconds>
       -o <destination file loc>
       <url to download from> *)
    OS.Process.isSuccess (Systeml.systeml ["curl", "-s", "-f", "-m", "5", "-o", dest, url])

fun fetch base_url cachekey talk =
    let
        val key_url = base_url ^ "/key/" ^ cachekey
        val tmpfile = OS.FileSys.tmpName()
        val _ = talk "checking cache for prebuilt theory"
        val hit = curl_get_to_file key_url tmpfile
    in
        if not hit then let
            val _ = OS.FileSys.remove tmpfile handle OS.SysErr _ => ()
            val _ = talk "cache miss; theory will be built locally."
        in
            false
        end
        else
            let
                val src = JSONParser.openFile tmpfile
                val json = JSONParser.parse src before JSONParser.close src
                val _ = OS.FileSys.remove tmpfile handle OS.SysErr _ => ()
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
                                 curl_get_to_file (base_url ^ url) (to_dest_dir name))
                             files
                val _ = if ok
                        then talk "cache hit! local theory building can be skipped."
                        else talk "only managed a partial cache hit. theory will be built locally."
            in
                ok
            end
            handle _ => let
                val _ = talk "something went wrong. theory will be built locally."
            in
                false
            end
    end

end
