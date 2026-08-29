structure HMProject :> HMProject =
struct

type external_project = { id : string, path : string,
                          exclude : string list }

type config = {
  root : string,
  name : string option,
  exclude : string list,
  externals : external_project list,
  external_includes : string list,
  holmake : bool,
  dead_keys : string list,
  unknown_keys : string list
}

(* Every key any reader of holproject.toml consults.  `name` and
   `holpath` are read here and by holpathdb's registration walk;
   `h4pedant` is read by tools/h4pedant, which owns that block's
   schema (so we never descend into it); the rest are `load`'s own.
   A key outside this set is a typo: TOML lookups answer NONE for an
   absent key and for a misspelled one alike, so `load` collects the
   strangers into `unknown_keys` rather than discarding them. *)
val recognised_keys =
    ["name", "holpath", "exclude", "external_includes", "holmake",
     "projects", "h4pedant"]

(* holproject.local.toml is the per-developer override file; only
   [projects.<id>] means anything in it. *)
val recognised_local_keys = ["projects"]

(* Keys of a [projects.<id>] sub-table.  A typo here (`paths = ".."`)
   drops the external as quietly as a top-level one drops its key. *)
val recognised_project_keys = ["path", "exclude"]

(* How `dead_keys` and `unknown_keys` label what they report, and how
   `recognised_keys_for` reads a label back.  Constructors and decoder
   live together so the convention has one definition: the decoder
   must test the `[projects.` prefix first, because an external's
   sub-table key in the local file carries both marks. *)
fun local_label s = s ^ " (local)"
fun ext_table_label id = "[projects." ^ id ^ "]"
fun ext_key_label id k = ext_table_label id ^ "." ^ k

fun recognised_keys_for k =
    if String.isPrefix "[projects." k then recognised_project_keys
    else if String.isSuffix " (local)" k then recognised_local_keys
    else recognised_keys

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

fun sorted_dedup ss =
    Binaryset.listItems
      (Binaryset.addList (Binaryset.empty String.compare, ss))

(* Path-prefix test, in canonicalised form.  Both arguments must be
   absolute and canonical.  `ancestor` is a prefix of `descendant`
   either if they are equal, or if descendant starts with ancestor
   followed by a path separator.  Curried so that a partial application
   computes the separator-terminated prefix once: callers test one
   ancestor against many paths. *)
fun is_path_under ancestor =
    let
      val pfx = if String.isSuffix "/" ancestor then ancestor
                else ancestor ^ "/"
    in
      fn descendant => ancestor = descendant orelse
                       String.isPrefix pfx descendant
    end

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

fun lookup_bool tbl key =
    case TOML.lookupInTable tbl key of
        NONE => NONE
      | SOME (TOMLvalue_dtype.BOOL b) => SOME b
      | SOME _ =>
          raise Fail ("key '" ^ key_name key ^ "' must be a boolean")

fun lookup_int tbl key =
    case TOML.lookupInTable tbl key of
        NONE => NONE
      | SOME (TOMLvalue_dtype.INTEGER i) =>
          (SOME (IntInf.toInt i)
           handle Overflow =>
             raise Fail ("key '" ^ key_name key ^ "' is out of range"))
      | SOME _ =>
          raise Fail ("key '" ^ key_name key ^ "' must be an integer")

(* Tag a `lookup_*'-raised Fail with the file path so users see which
   holproject.toml is malformed, not just the offending key name. *)
fun tag_path pf f = f () handle Fail s => raise Fail (pf ^ ": " ^ s)

fun abs_relative_to base p =
    OS.Path.mkCanonical
      (if OS.Path.isAbsolute p then p
       else OS.Path.mkAbsolute { path = p, relativeTo = base })

(* Reads the holproject.toml *at* `root' --- the at-root file of a
   referenced external project.  A [projects.<id>] reference is a
   positive claim that the directory is itself a project, so a missing
   or unparseable file is fatal: use external_includes for non-project
   directories. *)
fun read_external_decls root =
    let
      val pf = OS.Path.concat (root, PROJECT_FILE)
    in
      if not (file_exists pf) then
        raise Fail ("no " ^ PROJECT_FILE ^ " at " ^ root)
      else
        ((pf, TOML.fromFile pf)
         handle e => raise Fail ("Failed to parse " ^ pf ^ ": " ^
                                 General.exnMessage e))
    end

fun excludes_declared_at root =
    let
      val (pf, tbl) = read_external_decls root
      val rel = tag_path pf
                  (fn () => Option.getOpt
                              (lookup_string_array tbl ["exclude"], []))
    in
      List.map (abs_relative_to root) rel
    end

fun external_includes_declared_at root =
    let
      val (pf, tbl) = read_external_decls root
      val rel = tag_path pf
                  (fn () => Option.getOpt
                              (lookup_string_array tbl ["external_includes"], []))
    in
      List.map (abs_relative_to root o expand_holdir) rel
    end

(* The declared [projects.<id>] sub-tables as (id, table) pairs.  An
   entry whose value is not a table is dropped: `projects` is a table
   of tables by construction, so anything else is malformed rather
   than meaningful. *)
fun project_subtables tbl =
    case lookup_table tbl ["projects"] of
        NONE => []
      | SOME svs =>
          List.mapPartial
            (fn (id, TOMLvalue_dtype.TABLE inner) => SOME (id, inner)
              | _ => NONE)
            svs

(* Read [projects.<id>] sub-tables; capture each's `path` and (optional)
   `exclude` list, unioned (non-recursively) with whatever the external
   declares for itself in its own holproject.toml.  Excludes are
   interpreted relative to that external's path. *)
fun externals_from_table tbl rel_to =
    List.mapPartial
      (fn (id, inner) =>
          case lookup_string inner ["path"] of
              NONE => NONE
            | SOME p =>
                let
                  val ext_path = abs_relative_to rel_to p
                  val ext_excl_rel =
                      Option.getOpt
                        (lookup_string_array inner ["exclude"], [])
                  val consumer_excl =
                      List.map (abs_relative_to ext_path) ext_excl_rel
                  val inherited_excl = excludes_declared_at ext_path
                  val ext_excl =
                      sorted_dedup (consumer_excl @ inherited_excl)
                in
                  SOME { id = id, path = ext_path, exclude = ext_excl }
                end)
      (project_subtables tbl)

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

      val name = tag_path proj_path (fn () => lookup_string ptbl ["name"])

      val holmake =
          tag_path proj_path
            (fn () => Option.getOpt (lookup_bool ptbl ["holmake"], true))

      val exclude_rel =
          tag_path proj_path
            (fn () => Option.getOpt (lookup_string_array ptbl ["exclude"], []))
      val exclude = if holmake then List.map (abs_relative_to root) exclude_rel
                    else []

      (* externals can be declared in either file; local overrides project.
         Skipped entirely under holmake = false: [projects.<id>] tables
         carry no meaning outside project mode, so we don't read them or
         follow their paths. *)
      val externals =
          if holmake then
            let
              val proj_externals = externals_from_table ptbl root
              val local_externals =
                  case ltbl_opt of
                      NONE => []
                    | SOME t => externals_from_table t root
              (* Dedup by id keeping the first occurrence in
                 `local_externals @ proj_externals'.  Local entries come
                 first, so a local file's [projects.<id>] overrides the
                 same `<id>' in the committed file. *)
            in
              List.foldl
                (fn (e, acc) =>
                    if List.exists (fn x => #id x = #id e) acc then acc
                    else acc @ [e])
                []
                (local_externals @ proj_externals)
            end
          else []

      val ext_inc_rel =
          tag_path proj_path
            (fn () => Option.getOpt
                        (lookup_string_array ptbl ["external_includes"], []))
      val own_ext_inc =
          List.map (abs_relative_to root o expand_holdir) ext_inc_rel
      val inherited_ext_inc =
          List.concat
            (List.map (fn e => external_includes_declared_at (#path e))
                      externals)
      val external_includes = sorted_dedup (own_ext_inc @ inherited_ext_inc)

      (* Under holmake = false, project-mode-only keys are inert.  Collect
         the present-but-ignored ones so the caller can warn.  `name`,
         `holpath`, and `external_includes` stay live. *)
      fun proj_ids_in label tbl =
          List.map (label o ext_table_label o #1) (project_subtables tbl)
      val dead_keys =
          if holmake then []
          else
            (case exclude_rel of [] => [] | _ => ["exclude"]) @
            proj_ids_in (fn s => s) ptbl @
            (case ltbl_opt of NONE => []
                            | SOME t => proj_ids_in local_label t)

      (* Keys nobody understands, labelled for the caller's warning:
         `<key>`, `[projects.<id>].<key>`, and the same again with a
         ` (local)` suffix for holproject.local.toml.  Collected
         whether or not project mode is on -- a typo is a typo either
         way -- and never descending into [h4pedant]. *)
      fun strangers recognised tbl =
          List.filter (fn k => not (List.exists (fn r => r = k) recognised))
                      (List.map #1 tbl)
      fun unknown_in localp tbl =
          let
            val (label, top_keys) =
                if localp then (local_label, recognised_local_keys)
                else ((fn s => s), recognised_keys)
          in
            List.map label (strangers top_keys tbl) @
            List.concat
              (List.map
                 (fn (id, inner) =>
                     List.map (label o ext_key_label id)
                              (strangers recognised_project_keys inner))
                 (project_subtables tbl))
          end
      val unknown_keys =
          tag_path proj_path (fn () => unknown_in false ptbl) @
          (case ltbl_opt of
               NONE => []
             | SOME t => tag_path local_path (fn () => unknown_in true t))

    in
      { root = root,
        name = name,
        exclude = exclude,
        externals = externals,
        external_includes = external_includes,
        holmake = holmake,
        dead_keys = dead_keys,
        unknown_keys = unknown_keys }
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

(* Returns both the directories that join the scan and the child
   directories that were pruned because they carry their own project
   file.  The latter are the roots of nested projects; the caller
   decides whether to adopt them (see `discover`).  A nested root
   underneath an [exclude]d subtree is not reported: `excluded` is
   tested on pop, before that directory's children are ever listed. *)
fun discover_under start excludes =
    let
      open OS.FileSys
      val excl_set = Binaryset.addList
                       (Binaryset.empty String.compare, excludes)
      fun hasProjFile p = access(OS.Path.concat(p, "holproject.toml"), [A_READ])
      fun excluded p = Binaryset.member (excl_set, p)
      fun walk acc nested worklist =
          case worklist of
              [] => (acc, nested)
            | d :: ds =>
                if excluded d then walk acc nested ds
                else
                  let
                    val children = list_subdirs d
                    (* No per-child mkCanonical: `d` is canonical
                       (starting point is canonicalised once below,
                       and `OS.Path.concat` with a name component
                       preserves canonicity). *)
                    val (sub, own) = List.partition hasProjFile children
                  in
                    walk (d :: acc) (sub @ nested) (own @ ds)
                  end
    in
      walk [] [] [OS.Path.mkCanonical start]
    end

fun discover (cfg : config) =
    let
      val roots =
          (#root cfg, #exclude cfg) ::
          List.map (fn e => (#path e, #exclude e)) (#externals cfg)
      val walked = List.map (fn (r, excl) => discover_under r excl) roots
    in
      { dirs = sorted_dedup (List.concat (List.map #1 walked)),
        nested = sorted_dedup (List.concat (List.map #2 walked)) }
    end

fun discover_dirs cfg = #dirs (discover cfg)

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
