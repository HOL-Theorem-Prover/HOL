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

fun compute_for_deps g raw_deps =
    let
      val deps0 =
          let
            (* Stop walking at theory nodes: a theory's .dat content
               (what gets hashed) already encodes the theory's
               parents transitively via the recorded parent-hash
               chain in its header, so pulling the parent theory's
               *script* into this target's hash would be wrong.
               Continue only through non-theory deps so the walk can
               cross into a library's source dir to find the theory
               parents that library brings in. *)
            val depset = ref hm_target.empty_tgtset
            val visited = ref hm_target.empty_tgtset
            fun is_theory_filepart fp =
                case fp of
                    UO (Theory _) => true
                  | UI (Theory _) => true
                  | SML (Theory _) => true
                  | SIG (Theory _) => true
                  | DAT _ => true
                  | _ => false
            fun visit d =
                if Binaryset.member (!visited, d) then ()
                else
                  (visited := Binaryset.add (!visited, d);
                   (case dep_to_hashable d of
                        SOME d' => depset := Binaryset.add (!depset, d')
                      | NONE => ());
                   if is_theory_filepart (hm_target.filepart d) then ()
                   else
                     case HM_DepGraph.target_node g d of
                         NONE => ()
                       | SOME n =>
                         (case HM_DepGraph.peeknode g n of
                              NONE => ()
                            | SOME nI =>
                              List.app (fn (_, d') => visit d')
                                       (#dependencies nI)))
            val _ = List.app visit raw_deps
          in
            map (fn dep =>
                    let val p = tgt_toString dep
                        val path = resolve_dat_path dep p
                    in
                      { dep = dep,
                        name = fromFile (hm_target.filepart dep),
                        path = path }
                    end)
                (Binaryset.listItems (!depset))
          end
      (* Drop a theory from the hash inputs if some other theory in
         the set transitively records it as a parent: the descendant's
         .dat already captures the ancestor's content via the
         recorded parent-hash chain, and hashing the ancestor as well
         only inflates the cachekey scope. *)
      val deps =
          let
            val theory_entries =
                List.mapPartial
                  (fn entry as {dep, ...} =>
                      case hm_target.filepart dep of
                          HOLFS_dtype.DAT s => SOME (s, entry)
                        | _ => NONE)
                  deps0
            val in_set : (string, {dep:hm_target.t, name:string, path:string})
                          Binarymap.dict =
                List.foldl
                  (fn ((s, e), m) => Binarymap.insert (m, s, e))
                  (Binarymap.mkDict String.compare)
                  theory_entries
            val search_dirs =
                List.foldl
                  (fn ({path, ...}, acc) =>
                      let val d = OS.Path.dir path
                      in if List.exists (fn x => x = d) acc
                         then acc else d :: acc end)
                  []
                  deps0
            val ancestor_names : string Binaryset.set ref =
                ref (Binaryset.empty String.compare)
            val visited : string Binaryset.set ref =
                ref (Binaryset.empty String.compare)
            fun walk_path path =
                List.app walk_name
                         (map #1 (HM_TheoryDat.extract_parents path))
            and walk_name pname =
                if Binaryset.member (!visited, pname) then ()
                else
                  (visited := Binaryset.add (!visited, pname);
                   ancestor_names := Binaryset.add (!ancestor_names, pname);
                   case Binarymap.peek (in_set, pname) of
                       SOME {path, ...} => walk_path path
                     | NONE =>
                       (case HM_TheoryDat.find_parent_dat
                               search_dirs pname of
                            SOME ppath => walk_path ppath
                          | NONE => ()))
            val _ = List.app (fn (_, {path, ...}) => walk_path path)
                             theory_entries
          in
            List.filter
              (fn {dep, ...} =>
                  case hm_target.filepart dep of
                      HOLFS_dtype.DAT s =>
                        not (Binaryset.member (!ancestor_names, s))
                    | _ => true)
              deps0
          end
      val missing =
          List.filter (fn {path, ...} =>
                          not (OS.FileSys.access (path, [OS.FileSys.A_READ])))
                      deps
    in
      case missing of
          _ :: _ =>
            (Missing (map (fn {name,path,...} => {name=name,path=path})
                          missing),
             g)
        | [] =>
          let
            (* Memoise per-dep file hashes on the graph: a shared
               parent (boolTheory.dat, optionTheory.dat, etc.) gets
               hashed once across all targets that reference it
               instead of once per target. *)
            fun hash_one ({dep, name, path}, (acc, g)) =
                case HM_DepGraph.peek_file_hash g dep of
                    SOME h => ((name, h) :: acc, g)
                  | NONE =>
                    let val h = SHA1.sha1_file {filename = path}
                    in ((name, h) :: acc,
                        HM_DepGraph.set_file_hash g dep h)
                    end
            val (hashed_deps_rev, g') = List.foldl hash_one ([], g) deps
            val hashed_deps = List.rev hashed_deps_rev
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
            (Key key, g')
          end
    end

fun compute_for_node depgraph node =
    case HM_DepGraph.peeknode depgraph node of
        NONE => raise Fail "HM_Cachekey.compute_for_node: node not found"
      | SOME nodeinfo =>
          compute_for_deps depgraph (map #2 (#dependencies nodeinfo))

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
