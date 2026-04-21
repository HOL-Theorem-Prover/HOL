structure HM_Cachekey :> HM_Cachekey =
struct

datatype rebuild_strategy = datatype HM_Cachekey_dtype.rebuild_strategy

datatype compute_result =
         Key of string
       | Missing of {name : string, path : string} list

open Holmake_tools
structure FileSys = HOLFileSys

(* --------------------------------------------------------------------
   Cachekey computation for a single theory-target node.

   The set of files that contribute to the hash is exactly the set the
   --cachekey CLI option uses: all direct dependencies of the target,
   with the following normalisations:
     - .uo/.ui of Theory files are replaced by the corresponding .dat
       (the actual theory content);
     - other .uo/.ui files and the holheap state are excluded.
   Each file is SHA1-hashed, pairs (filename, hash) are canonically
   sorted, and the concatenation of hashes is SHA1-hashed to produce
   the final key.
   -------------------------------------------------------------------- *)

fun dep_to_hashable dep =
    let open hm_target HOLFS_dtype
    in
      case filepart dep of
          DAT _        => SOME dep
        | SML _        => SOME dep
        | SIG _        => SOME dep
        | ART _        => SOME dep
        | UO (Theory s) => SOME (setFile (DAT s) dep)
        | UI (Theory s) => SOME (setFile (DAT s) dep)
        | _            => NONE
    end

fun toFSpath s =
    case HFS_NameMunge.HOLtoFS s of
        NONE => s
      | SOME {fullfile, ...} => fullfile

(* If this is a .dat for a theory whose .uo/.ui has been symlinked into
   sigobj, the .dat may not live next to the symlink.  Resolve the .uo
   symlink and look for the .dat in that directory. *)
fun resolve_dat_path dep holpath =
    let open hm_target HOLFS_dtype
        val fspath = toFSpath holpath
    in
      if OS.FileSys.access (fspath, []) then fspath
      else
        case filepart dep of
            DAT s =>
              (let
                 val uoname = fromFile (UO (Theory s))
                 val dir = OS.Path.dir holpath
                 val uo_path =
                     if dir = "" then uoname
                     else OS.Path.concat (dir, uoname)
                 val uo_fspath = toFSpath uo_path
                 val real_uo = OS.FileSys.realPath uo_fspath
                 val real_dir = OS.Path.dir real_uo
                 val dat_name = fromFile (DAT s)
               in
                 OS.Path.concat (real_dir, dat_name)
               end handle OS.SysErr _ => fspath)
          | _ => fspath
    end

fun compute_for_deps raw_deps =
    let
      val deps =
          let val depset =
                  List.foldl
                    (fn (dep, acc) =>
                        case dep_to_hashable dep of
                            SOME d => Binaryset.add (acc, d)
                          | NONE => acc)
                    hm_target.empty_tgtset
                    raw_deps
          in
            map (fn dep =>
                    let val p = tgt_toString dep
                        val path = resolve_dat_path dep p
                    in
                      { name = fromFile (hm_target.filepart dep),
                        path = path }
                    end)
                (Binaryset.listItems depset)
          end
      val missing =
          List.filter (fn {path, ...} =>
                          not (OS.FileSys.access (path, [OS.FileSys.A_READ])))
                      deps
    in
      case missing of
          _ :: _ => Missing missing
        | [] =>
          let
            val hashed_deps =
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
                      List.app (fn h => TextIO.output (out, h)) dep_hashes;
                      TextIO.closeOut out
                    end
            val key = SHA1.sha1_file {filename = tmpfile}
            val _ = OS.FileSys.remove tmpfile handle OS.SysErr _ => ()
          in
            Key key
          end
    end

fun compute_for_node depgraph node =
    case HM_DepGraph.peeknode depgraph node of
        NONE => raise Fail "HM_Cachekey.compute_for_node: node not found"
      | SOME nodeinfo => compute_for_deps (map #2 (#dependencies nodeinfo))

(* --------------------------------------------------------------------
   Stamp files.  For a theory-target foo, the stamp sits next to the
   .dat on disk (i.e. in the munged output directory, e.g. .hol/objs/
   under Poly/ML).  We accept the real FS path of the .dat and produce
   the real FS path of its stamp.
   -------------------------------------------------------------------- *)

fun stamp_path_for_datfile datpath =
    let val {base, ext=_} = OS.Path.splitBaseExt datpath
    in base ^ ".cachekey" end

fun read_stamp path =
    if OS.FileSys.access (path, [OS.FileSys.A_READ]) then
      let val strm = TextIO.openIn path
          val raw = TextIO.inputAll strm
          val _ = TextIO.closeIn strm
          (* strip trailing newline(s)/whitespace *)
          fun trim s =
              let val n = size s
                  fun findEnd i =
                      if i <= 0 then 0
                      else if Char.isSpace (String.sub (s, i-1)) then findEnd (i-1)
                      else i
              in String.substring (s, 0, findEnd n) end
      in SOME (trim raw) end handle _ => NONE
    else NONE

fun write_stamp path key =
    let val tmp = path ^ ".new"
        val strm = TextIO.openOut tmp
        val _ = TextIO.output (strm, key ^ "\n")
        val _ = TextIO.closeOut strm
    in
      OS.FileSys.rename {old = tmp, new = path}
    end handle _ => () (* non-fatal *)

fun remove_stamp path =
    OS.FileSys.remove path handle _ => ()

end
