structure HMProject :> HMProject =
struct

type external_project = { id : string, path : string,
                          exclude : string list }

type config = {
  root : string,
  name : string option,
  exclude : string list,
  externals : external_project list,
  external_includes : string list
}

val PROJECT_FILE = "holproject.toml"
val LOCAL_FILE = "holproject.local.toml"

(* Directory names that are never followed during a tree scan, regardless
   of holproject.toml's [exclude].  These are version-control / build /
   tool-output directories whose contents are categorically not project
   sources. *)
val skip_dirs = ["..", ".", ".git", ".hg", ".svn", ".hol", ".claude"]

fun canonical_abs p =
    OS.Path.mkCanonical
      (if OS.Path.isAbsolute p then p
       else OS.Path.mkAbsolute { path = p,
                                 relativeTo = OS.FileSys.getDir() })

(* Substitute the literal token $(HOLDIR) in `s' with the configure-time
   HOLDIR path.  Matches the idiom users already use in Holmakefiles
   (e.g. `INCLUDES = $(HOLDIR)/src/integer'), letting external_includes
   in holproject.toml use the same syntax. *)
fun expand_holdir s =
    let
      val token = "$(HOLDIR)"
      val tlen = size token
      fun go i acc =
          if i > size s - tlen then
            acc ^ String.extract (s, i, NONE)
          else if String.substring (s, i, tlen) = token then
            go (i + tlen) (acc ^ Systeml.HOLDIR)
          else
            go (i + 1) (acc ^ String.substring (s, i, 1))
    in
      if size s < tlen then s else go 0 ""
    end

fun file_exists p =
    OS.FileSys.access (p, [OS.FileSys.A_READ])
    handle OS.SysErr _ => false

fun is_dir p =
    OS.FileSys.isDir p handle OS.SysErr _ => false

(* ----------------------------------------------------------------------
   find_root: ascending walk for holproject.toml, by string manipulation
   only (no chdir).  Stops when getParent yields the same path (root) or
   when the parent doesn't exist.
   ---------------------------------------------------------------------- *)
fun find_root { start } =
    let
      val start_abs = canonical_abs start
      fun walk d =
          if file_exists (OS.Path.concat (d, PROJECT_FILE)) then SOME d
          else
            let val parent = OS.Path.getParent d
            in if parent = d then NONE else walk parent
            end
    in
      walk start_abs
    end

(* ----------------------------------------------------------------------
   TOML helpers.  Each lookup returns NONE only when the key is
   absent; if the key is present but the value is the wrong variant,
   raise Fail with a message naming the offending key.  This catches
   schema typos at load time (e.g. `exclude = "foo"` when an array is
   expected) instead of silently treating them as missing.
   ---------------------------------------------------------------------- *)
fun key_name key = String.concatWith "." key

fun lookup_string tbl key =
    case TOML.lookupInTable tbl key of
        NONE => NONE
      | SOME (TOMLvalue_dtype.STRING s) => SOME s
      | SOME _ =>
          raise Fail ("key '" ^ key_name key ^ "' must be a string")

fun lookup_string_array tbl key =
    case TOML.lookupInTable tbl key of
        NONE => NONE
      | SOME (TOMLvalue_dtype.ARRAY xs) =>
          SOME (List.map
                  (fn TOMLvalue_dtype.STRING s => s
                    | _ =>
                      raise Fail ("key '" ^ key_name key ^
                                  "' must be an array of strings"))
                  xs)
      | SOME _ =>
          raise Fail ("key '" ^ key_name key ^
                      "' must be an array of strings")

fun lookup_table tbl key =
    case TOML.lookupInTable tbl key of
        NONE => NONE
      | SOME (TOMLvalue_dtype.TABLE svs) => SOME svs
      | SOME _ =>
          raise Fail ("key '" ^ key_name key ^ "' must be a table")

fun abs_relative_to base p =
    OS.Path.mkCanonical
      (if OS.Path.isAbsolute p then p
       else OS.Path.mkAbsolute { path = p, relativeTo = base })

(* Read [projects.<id>] sub-tables; capture each's `path` and (optional)
   `exclude` list.  Excludes are interpreted relative to that external's
   path (not the consumer's root). *)
fun externals_from_table tbl rel_to =
    case lookup_table tbl ["projects"] of
        NONE => []
      | SOME svs =>
          List.mapPartial
            (fn (id, TOMLvalue_dtype.TABLE inner) =>
                  (case lookup_string inner ["path"] of
                       NONE => NONE
                     | SOME p =>
                         let
                           val ext_path = abs_relative_to rel_to p
                           val ext_excl_rel =
                               Option.getOpt
                                 (lookup_string_array inner ["exclude"], [])
                           val ext_excl =
                               List.map (abs_relative_to ext_path) ext_excl_rel
                         in
                           SOME { id = id, path = ext_path,
                                  exclude = ext_excl }
                         end)
              | _ => NONE)
            svs

(* ----------------------------------------------------------------------
   load: parse holproject.toml and, if present, holproject.local.toml.
   ---------------------------------------------------------------------- *)
fun load { root } =
    let
      val root = canonical_abs root
      val proj_path = OS.Path.concat (root, PROJECT_FILE)
      val local_path = OS.Path.concat (root, LOCAL_FILE)
      val ptbl = TOML.fromFile proj_path
                 handle e =>
                        raise Fail ("Failed to parse " ^ proj_path ^ ": " ^
                                    General.exnMessage e)
      val ltbl_opt =
          if file_exists local_path then
            SOME (TOML.fromFile local_path
                  handle e =>
                         raise Fail ("Failed to parse " ^ local_path ^ ": " ^
                                     General.exnMessage e))
          else NONE

      val name = lookup_string ptbl ["name"]

      val exclude_rel = Option.getOpt (lookup_string_array ptbl ["exclude"], [])
      val exclude = List.map (abs_relative_to root) exclude_rel

      (* externals can be declared in either file; local overrides project. *)
      val proj_externals = externals_from_table ptbl root
      val local_externals =
          case ltbl_opt of
              NONE => []
            | SOME t => externals_from_table t root
      (* Dedup by id keeping the first occurrence in `local_externals
         @ proj_externals'.  Local entries come first, so a local
         file's [projects.<id>] overrides the same `<id>' in the
         committed file. *)
      val externals =
          List.foldl
            (fn (e, acc) =>
                if List.exists (fn x => #id x = #id e) acc then acc
                else acc @ [e])
            []
            (local_externals @ proj_externals)

      val ext_inc_rel =
          Option.getOpt (lookup_string_array ptbl ["external_includes"], [])
      val external_includes =
          List.map (abs_relative_to root o expand_holdir) ext_inc_rel

    in
      { root = root,
        name = name,
        exclude = exclude,
        externals = externals,
        external_includes = external_includes }
    end

(* ----------------------------------------------------------------------
   discover_dirs: DFS preorder under root and each external project,
   collecting absolute paths of directories.
   ---------------------------------------------------------------------- *)
fun list_subdirs dir =
    let
      val ds = OS.FileSys.openDir dir
      fun loop acc =
          case OS.FileSys.readDir ds of
              NONE => (OS.FileSys.closeDir ds; acc)
            | SOME nm =>
                if List.exists (fn s => s = nm) skip_dirs then loop acc
                else
                  let val full = OS.Path.concat (dir, nm)
                  in if is_dir full then loop (full :: acc) else loop acc
                  end
    in
      loop []
    end handle OS.SysErr _ => []

fun discover_under start excludes =
    let
      open OS.FileSys
      val excl_set = Binaryset.addList
                       (Binaryset.empty String.compare, excludes)
      fun hasProjFile p = access(OS.Path.concat(p, "holproject.toml"), [A_READ])
      fun excluded p = Binaryset.member (excl_set, p)
      fun walk acc worklist =
          case worklist of
              [] => acc
            | d :: ds =>
                if excluded d then walk acc ds
                else
                  let
                    val children = list_subdirs d
                    (* No per-child mkCanonical: `d` is canonical
                       (starting point is canonicalised once below,
                       and `OS.Path.concat` with a name component
                       preserves canonicity). *)
                  in
                    walk (d :: acc)
                         (List.filter (not o hasProjFile) children @ ds)
                  end
    in
      walk [] [OS.Path.mkCanonical start]
    end

fun discover_dirs (cfg : config) =
    let
      val roots =
          (#root cfg, #exclude cfg) ::
          List.map (fn e => (#path e, #exclude e)) (#externals cfg)
      val all = List.concat
                  (List.map (fn (r, excl) => discover_under r excl) roots)
      (* sort + dedup for determinism *)
      val set = Binaryset.addList (Binaryset.empty String.compare, all)
    in
      Binaryset.listItems set
    end

(* ----------------------------------------------------------------------
   Source-name clash detection across project dirs.

   Holdep resolves `open Foo' by searching the include path for
   `Foo.sml' / `Foo.sig' (`tools/Holmake/deps/Holdep.sml').  Two
   project dirs each carrying `Foo.sml' would silently let the
   alphabetically-first dir win; we instead detect and report so the
   user can fix it explicitly via [exclude].
   ---------------------------------------------------------------------- *)
fun source_files dir =
    let
      val ds = OS.FileSys.openDir dir
      fun loop acc =
          case OS.FileSys.readDir ds of
              NONE => (OS.FileSys.closeDir ds; acc)
            | SOME nm =>
                let val ext = OS.Path.ext nm
                in
                  if (ext = SOME "sml" orelse ext = SOME "sig") andalso
                     (not (is_dir (OS.Path.concat (dir, nm))))
                  then loop (nm :: acc)
                  else loop acc
                end
    in loop [] end
    handle OS.SysErr _ => []

fun find_name_clashes dirs =
    let
      val empty : (string, string list) Binarymap.dict =
          Binarymap.mkDict String.compare
      fun add_file (dir, file, m) =
          case Binarymap.peek (m, file) of
              NONE => Binarymap.insert (m, file, [dir])
            | SOME ds => Binarymap.insert (m, file, dir :: ds)
      fun add_dir (dir, m) =
          List.foldl (fn (f, m) => add_file (dir, f, m)) m (source_files dir)
      val all = List.foldl add_dir empty dirs
      val clashes =
          Binarymap.foldl
            (fn (file, dirs, acc) =>
                if length dirs > 1 then (file, List.rev dirs) :: acc
                else acc)
            []
            all
    in
      List.rev clashes (* foldl reverses; rev back to insertion order *)
    end

end (* struct *)
