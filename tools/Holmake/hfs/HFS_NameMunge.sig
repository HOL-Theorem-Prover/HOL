signature HFS_NameMunge =
sig

  val HOLOBJDIR : string (* for use in Holmakefiles' HOL_LNSIGOBJ *)
  val HOLtoFS : string -> {fullfile : string, dir : string} option
  val toFSfn : bool -> (string -> 'a) -> (string -> 'a)
  val clean_last : unit -> unit
  (* applies HFS-specific "cleaning" to the current directory, assuming
     all normal cleaning has been done *)

  (* Artifact layout.  With no layout, products live in <dir>/.hol/objs,
     depfiles in <dir>/.hol/make-deps, and so on (the legacy layout).
     With a layout, every directory under srcroot keeps its products
     under objroot instead: <objroot>/objs/<rel>, <objroot>/make-deps/<rel>
     etc., where <rel> is the directory relative to srcroot.  Both
     fields are absolute and canonical. *)
  type layout = {srcroot : string, objroot : string}
  val configure : layout option -> unit
  (* always assigns; NONE selects the legacy layout *)
  val current_layout : unit -> layout option
  (* the configured layout; if configure has never been called, the
     result of layout_from_env, computed once *)
  val layout_from_env : unit -> layout option
  (* from HOLOBJROOT and HOLSRCROOT; NONE (with a warning) if only one
     is set *)
  val owned_by_layout : string -> bool
  (* absolute path under srcroot but not under objroot *)

  (* Each takes a source directory (absolutised if relative) and returns
     the directory holding that kind of artifact for it.  A directory
     already under objroot is returned unchanged. *)
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
  (* the per-directory artifact directories when the directory is
     mapped by the layout; [] otherwise *)
  val FStoHOL : string -> string option
  (* physical product path (either layout) -> logical path *)

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
  (* test is on bare name; action/reducer can take side effects and is
     passed base name (which matches the predicate) as well as the
     directory the file physically lives in.  For files in a separate
     products directory, the action runs with that directory as the
     current directory. *)

end
