signature HMProject =
sig

  (* External project, as named in holproject.local.toml or in the
     consumer's holproject.toml.  `id` is the [projects.<id>] label,
     useful for diagnostics.  `path` is an absolute, canonical
     filesystem path.  `exclude` is a list of absolute, canonical
     paths under `path` that the consumer wants kept out of scope. *)
  type external_project = { id : string, path : string,
                            exclude : string list }

  (* Parsed contents of holproject.toml (+ holproject.local.toml, if
     present).  All paths are absolute and canonical.  `exclude`
     entries are interpreted relative to `root` and stored canonicalised
     -- they apply only to the consumer's own tree, not to externals.
     External-tree excludes live on each external_project.

     `external_includes` is the list of directories that act as classic
     `INCLUDES =' for every project dir.  Projects linking to an
     already-built HOL get everything under `src/' for free via
     `sigobj/' and only need to mention sources outside `sigobj' here
     -- typically other `examples/...' subtrees.  Each entry is
     resolved at load time: `$(HOLDIR)` is substituted with the
     configure-time HOLDIR; non-absolute paths are resolved against
     `root`.

     `holmake` is the top-level `holmake = true|false` switch (default
     `true`).  `false` opts out of project mode while leaving
     `holpathdb` registration (via `name`/`holpath`) and
     `external_includes` inheritance intact -- the file acts as a
     lightweight inheritance shim rather than a project root.  Under
     `holmake = false` the project-mode-only keys `exclude` and
     `[projects.<id>]` are skipped during parsing and listed in
     `dead_keys` so the caller can warn the user.

     `unknown_keys` has the same shape as `dead_keys` -- human-readable
     key labels for the caller to warn about -- but a different cause:
     these are keys no reader of `holproject.toml` understands at all.
     A TOML lookup cannot tell a misspelled key from an absent one, so
     without this a typo (`[project.cakeml]` for `[projects.cakeml]`)
     is discarded in silence.  A label from `holproject.local.toml`
     carries the same ` (local)` suffix `dead_keys` uses, and a key of
     a `[projects.<id>]` sub-table is labelled `[projects.<id>].<key>`;
     `recognised_keys_for` maps a label back to the keys that were
     legal where it appeared. *)
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

  (* recognised_keys_for k - the keys that were legal where the
     `unknown_keys` entry `k` appeared: a `[projects.<id>].` prefix
     names an external's sub-table, a ` (local)` suffix names
     `holproject.local.toml`, and anything else is a top-level key of
     `holproject.toml`.  Callers warning about an unknown key use this
     to name the set the typo missed. *)
  val recognised_keys_for : string -> string list

  (* find_root {start} - walk upward from `start` looking for a
     `holproject.toml`.  Returns the directory holding it (absolute,
     canonical), or NONE if none found before the filesystem root. *)
  val find_root : { start : string } -> string option

  (* load {root} - parse `root/holproject.toml` and, if it exists,
     `root/holproject.local.toml`.  Local-file [projects.<id>.path]
     entries are made absolute relative to `root` if they are not
     already absolute.  Raises Fail on parse errors. *)
  val load : { root : string } -> config

  (* discover_dirs cfg - DFS preorder under cfg.root and each external
     project root, returning absolute paths of every directory that
     joins the project's scope: every directory below the project
     root (and each external's path) is included, regardless of
     whether it carries a Holmakefile -- so source-only dirs are
     full members of the project's include set and the user isn't
     required to scatter empty Holmakefiles for marker purposes.
     The consumer's `exclude` prunes subtrees rooted under cfg.root;
     each external's `exclude` prunes subtrees rooted under that
     external's path.  Always skips dot-directories (.git, .hol,
     .claude, .svn).  Result is sorted for determinism. *)
  val discover_dirs : config -> string list

  (* discover cfg - as `discover_dirs`, but also reporting the
     directories the walk pruned because they carry their own
     `holproject.toml`.  Those are the roots of *nested* projects:
     they are not part of this project's directory set, and it is the
     caller's job to decide whether to adopt them as projects in their
     own right.  A nested root underneath an [exclude]d subtree is not
     reported -- exclusion prunes before the subtree is examined.
     Both lists are sorted and duplicate-free;
     `discover_dirs cfg = #dirs (discover cfg)`. *)
  val discover : config -> { dirs : string list, nested : string list }

  (* find_name_clashes dirs - within `dirs`, look for filenames Holdep
     might resolve (`.sml` and `.sig` files, including theory scripts)
     and return any short-name that appears in more than one directory.
     Each entry is `(filename, dirs)` where `dirs` is the list of
     directories carrying that file.  Empty result means the project's
     source-name namespace is unambiguous.  Theory products under
     `.hol/objs/` are skipped because they are never traversed. *)
  val find_name_clashes : string list -> (string * string list) list

  (* source_files dir - list the bare names of `.sml` and `.sig` files
     directly under `dir` (no recursion).  Used by the incremental
     name-clash detector that runs as new project contexts get
     discovered.  Returns [] on a non-readable directory. *)
  val source_files : string -> string list

  (* Typed lookup helpers for `holproject.toml`-shaped TOML tables.
     Each returns NONE only when the key is absent; if the key is
     present but the value is the wrong variant, raises Fail with a
     message naming the offending key.  Exposed so other readers of
     `holproject.toml` (e.g. `h4pedant`) can reuse the same idiom. *)
  val lookup_string : TOML.table -> TOML.key -> string option
  val lookup_string_array : TOML.table -> TOML.key -> string list option
  val lookup_bool : TOML.table -> TOML.key -> bool option
  val lookup_int : TOML.table -> TOML.key -> int option
  val lookup_table : TOML.table -> TOML.key -> TOML.table option

  (* is_path_under ancestor - a test for whether a path lies at or below
     `ancestor`.  Both `ancestor` and the tested path must be absolute
     and canonical.  Curried: a partial application computes the
     separator-terminated prefix once, so testing one ancestor against
     many paths costs one string concatenation, not one per path. *)
  val is_path_under : string -> string -> bool

  (* tag_path pf f - run `f`; if it raises Fail, re-raise with `pf:` as
     a prefix so the message names the offending file.  Used to wrap
     top-level key lookups during `load`-style parsing. *)
  val tag_path : string -> (unit -> 'a) -> 'a

  (* abs_relative_to base p - canonicalise `p`, resolving against
     `base` if `p` is relative.  Exposed for path normalisation in
     other holproject.toml consumers. *)
  val abs_relative_to : string -> string -> string

end
