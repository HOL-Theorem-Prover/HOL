structure h4pedantConfig =
struct

(* Resolved per-directory style settings.  `linelen <= 0` means "no
   line-length check at all" for this dir; otherwise it's the
   inclusive limit. *)
type per_dir = { linelen : int, unicode_ok : bool }

(* A per-dir override out of the holproject.toml `[[h4pedant.dir]]`
   array: each setting is optional and inherits from the global
   default when absent. *)
type per_dir_partial = { linelen : int option, unicode_ok : bool option }

(* The whole loaded h4pedant config.  All paths are absolute and
   canonical.  `overrides` is the parsed `[[h4pedant.dir]]` array.
   `default` is the global `[h4pedant]` block, fallen back to the
   built-in default. *)
type config = {
  root : string,
  default : per_dir,
  excludes : string list,
  overrides : (string * per_dir_partial) list
}

(* Built-in defaults when [h4pedant] is absent or a key is missing. *)
val builtin_default : per_dir = { linelen = 80, unicode_ok = false }

val PROJECT_FILE = "holproject.toml"

(* Parse the global `[h4pedant]` block into a per_dir; missing keys
   fall back to the built-in default. *)
fun parse_default tbl : per_dir =
    { linelen = Option.getOpt (HMProject.lookup_int tbl ["linelen"],
                               #linelen builtin_default),
      unicode_ok = Option.getOpt (HMProject.lookup_bool tbl ["unicode_ok"],
                                  #unicode_ok builtin_default) }

(* Parse one `[[h4pedant.dir]]` table into (abs_path, partial). *)
fun parse_override root tbl : (string * per_dir_partial) option =
    case HMProject.lookup_string tbl ["path"] of
        NONE => NONE
      | SOME p =>
          SOME (HMProject.abs_relative_to root p,
                { linelen = HMProject.lookup_int tbl ["linelen"],
                  unicode_ok = HMProject.lookup_bool tbl ["unicode_ok"] })

(* Extract the [[h4pedant.dir]] array.  TOML's array-of-tables shape
   in the parser is an ARRAY whose elements are TABLE values. *)
fun parse_dir_array root tbl : (string * per_dir_partial) list =
    case TOML.lookupInTable tbl ["dir"] of
        NONE => []
      | SOME (TOMLvalue_dtype.ARRAY xs) =>
          List.mapPartial
            (fn TOMLvalue_dtype.TABLE t => parse_override root t
              | _ =>
                raise Fail "[[h4pedant.dir]] entries must be tables")
            xs
      | SOME _ =>
          raise Fail "`h4pedant.dir` must be an array of tables"

(* `tag_path proj_path` annotates any Fail raised inside the parse
   with the offending file path: inner helpers already name the key,
   but a user who has several holproject.toml files in scope needs
   the file to be named too. *)
fun parse_h4pedant_block proj_path root tbl =
    HMProject.tag_path proj_path
      (fn () =>
          let
            val default = parse_default tbl
            val exclude_rel =
                Option.getOpt (HMProject.lookup_string_array
                                 tbl ["exclude"], [])
            val excludes = List.map (HMProject.abs_relative_to root)
                                    exclude_rel
            val overrides = parse_dir_array root tbl
          in
            { default = default, excludes = excludes,
              overrides = overrides }
          end)

(* load { start } - walk up from `start` looking for a holproject.toml,
   parse out its [h4pedant] block (or fall back to built-in defaults
   when the block is absent), and return the assembled config.  NONE
   if no holproject.toml is found on the ancestor chain. *)
fun load { start : string } : config option =
    case HMProject.find_root { start = start } of
        NONE => NONE
      | SOME root =>
          let
            val proj_path = OS.Path.concat (root, PROJECT_FILE)
            val ptbl = TOML.fromFile proj_path
                       handle e =>
                              raise Fail ("Failed to parse " ^ proj_path ^
                                          ": " ^ General.exnMessage e)
            val { default, excludes, overrides } =
                case HMProject.lookup_table ptbl ["h4pedant"] of
                    NONE => { default = builtin_default,
                              excludes = [],
                              overrides = [] }
                  | SOME tbl => parse_h4pedant_block proj_path root tbl
          in
            SOME { root = root, default = default,
                   excludes = excludes, overrides = overrides }
          end

(* Path-prefix test, in canonicalised form.  Both arguments must be
   absolute and canonical.  `ancestor` is a prefix of `descendant`
   either if they are equal, or if descendant starts with ancestor
   followed by a path separator. *)
fun is_path_under ancestor descendant =
    ancestor = descendant orelse
    (String.isPrefix (ancestor ^ "/") descendant)

fun is_excluded (cfg : config) path =
    List.exists (fn ex => is_path_under ex path) (#excludes cfg)

(* Effective settings: collect every override whose path is an
   ancestor of `path`, sort shallow-to-deep, then fold them onto the
   global default so deeper overrides win key-by-key.

   The sort uses string length because, after filtering to ancestors
   of a common point, all matching paths are mutual ancestors of
   each other -- so shorter canonical path = shallower. *)
fun effective_for (cfg : config) path : per_dir =
    let
      val matching =
          List.filter (fn (p, _) => is_path_under p path) (#overrides cfg)
      val sorted =
          Listsort.sort
            (fn ((a, _), (b, _)) => Int.compare (size a, size b))
            matching
      fun step ((_, partial : per_dir_partial), acc : per_dir) =
          { linelen = Option.getOpt (#linelen partial, #linelen acc),
            unicode_ok = Option.getOpt (#unicode_ok partial,
                                        #unicode_ok acc) }
    in
      List.foldl step (#default cfg) sorted
    end

end
