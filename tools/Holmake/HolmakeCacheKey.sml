structure HolmakeCacheKey =
struct

open Holmake_tools Holmake_types

fun compute_deps (deps : dep list) =
    let fun dep_to_hashable dep =
            case hm_target.filepart dep of
                DAT _ => SOME dep
              | SML _ => SOME dep
              | SIG _ => SOME dep
              | ART _ => SOME dep
              | UO (Theory s) =>
                SOME (hm_target.setFile (DAT s) dep)
              | UI (Theory s) =>
                SOME (hm_target.setFile (DAT s) dep)
              | _ => NONE
        val depset =
            List.foldl
                (fn (dep, acc) =>
                    case dep_to_hashable dep of
                        SOME d => Binaryset.add(acc, d)
                      | NONE => acc)
                hm_target.empty_tgtset
                deps
        fun toFSpath s =
            case HFS_NameMunge.HOLtoFS s of
                NONE => s
              | SOME {fullfile, ...} => fullfile
    in
        map (fn dep =>
                let val p = tgt_toString dep
                    val fspath = toFSpath p
                    (* If this is a .dat converted from a .uo/.ui that
                       lives in sigobj (symlinked), the .dat won't exist
                       in sigobj. Resolve the .uo symlink to find the
                       real directory where the .dat lives. *)
                    val path =
                        if OS.FileSys.access(fspath, []) then fspath
                        else
                            case hm_target.filepart dep of
                                DAT s =>
                                (let
                                    val uoname = fromFile (UO (Theory s))
                                    val dir = OS.Path.dir p
                                    val uo_path =
                                        if dir = "" then uoname
                                        else OS.Path.concat(dir, uoname)
                                    val uo_fspath = toFSpath uo_path
                                    val real_uo = OS.FileSys.realPath uo_fspath
                                    val real_dir = OS.Path.dir real_uo
                                    val dat_name = fromFile (DAT s)
                                    val dat_fspath =
                                        OS.Path.concat(real_dir, dat_name)
                                in
                                    dat_fspath
                                end handle OS.SysErr _ => fspath)
                              | _ => fspath
                in { name = fromFile (hm_target.filepart dep),
                     path = path }
                end)
            (Binaryset.listItems depset)
    end

fun generate_cachekey deps =
    let val hashed_deps =
            map (fn {name, path} =>
                    (name, SHA1.sha1_file {filename = path}))
                deps
        val sorted_hashes =
            Listsort.sort (pair_compare (String.compare, String.compare))
                          hashed_deps
        val dep_hashes = map #2 sorted_hashes
        val tmpfile = OS.FileSys.tmpName ()
        val _ = let val out = TextIO.openOut tmpfile
                in
                    List.app (fn h => TextIO.output(out, h)) dep_hashes;
                    TextIO.closeOut out
                end
        val cachekey = SHA1.sha1_file {filename = tmpfile}
        val _ = OS.FileSys.remove tmpfile handle OS.SysErr _ => ()
    in
        cachekey
    end

val compute_deps_cachekey = generate_cachekey o compute_deps

end
