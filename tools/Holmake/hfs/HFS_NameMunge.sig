signature HFS_NameMunge =
sig

  val HOLOBJDIR : string (* for use in Holmakefiles' HOL_LNSIGOBJ *)
  val HOLtoFS : string -> {fullfile : string, dir : string} option
  val toFSfn : bool -> (string -> 'a) -> (string -> 'a)
  val clean_last : unit -> unit
  (* applies HFS-specific "cleaning" to the current directory, assuming
     all normal cleaning has been done *)

  (* Poly/ML artifact layout.  The legacy layout uses <dir>/.hol/objs
     for products, <dir>/.hol/make-deps for dependencies, etc.
     A configured layout maps source directories under srcroot to
     <objroot>/<kind>/<rel>, where rel is relative to srcroot.
     Directories outside srcroot retain the legacy layout.
     Both roots must be absolute and canonical.  Moscow ML retains
     its flat layout. *)
  type layout = {srcroot : string, objroot : string}
  val configure : layout option -> unit
  (* Replace the current layout; NONE selects the legacy layout. *)
  val current_layout : unit -> layout option
  (* Return the configured layout.  If configure has not been called,
     read and cache layout_from_env. *)
  val layout_from_env : unit -> layout option
  (* Read HOLOBJROOT and HOLSRCROOT.  Return NONE if neither is set;
     warn and return NONE if only one is set or the roots coincide. *)
  val owned_by_layout : string -> bool
  (* True for a path under srcroot and outside objroot.
     Relative paths are resolved against the current directory. *)

  (* Locate artifacts for a source directory.  Relative inputs produce
     relative legacy paths, or absolute paths in the configured layout.
     Directories already under objroot are returned unchanged. *)
  val objdir_for : string -> string
  val depdir_for : string -> string
  val logdir_for : string -> string
  val lockdir_for : string -> string
  val docsdir_for : string -> string
  val project_state_dir : string -> string
  (* project root -> <root>/.hol, or objroot when root is srcroot *)
  val holobjdir_var_for : string -> string
  (* value of $(HOLOBJDIR) in a Holmakefile in the given directory *)
  val artifact_dirs_for : string -> string list
  (* List the artifact directories for a mapped source directory.
     For srcroot, also include <objroot>/build-logs.  Return [] for
     directories outside the mapping or when no layout is configured. *)
  val FStoHOL : string -> string option
  (* Convert a physical product path from either layout to a logical
     path; return NONE if it does not match either layout. *)

  type dirstream
  exception DirNotFound
  val openDir : string -> dirstream
  val readDir : dirstream -> string option
  val closeDir : dirstream -> unit

  val read_files_with_objs :
      {dirname: string} -> (string -> bool) ->
      ({physdir:string,base:string} -> 'a -> 'a) ->
      'a ->
      'a
  (* Test each bare filename with the predicate, then call action with
     its name and physical directory.  For separate product directories,
     action runs with that directory as the current directory. *)

end
