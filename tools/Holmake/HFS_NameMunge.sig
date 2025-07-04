signature HFS_NameMunge =
sig

  val HOLOBJDIR : string (* for use in Holmakefiles' HOL_LNSIGOBJ *)
  val HOLtoFS : string -> {fullfile : string, dir : string} option
  val toFSfn : bool -> (string -> 'a) -> (string -> 'a)
  val clean_last : unit -> unit
  (* applies HFS-specific "cleaning" to the current directory, assuming
     all normal cleaning has been done *)

  type dirstream
  exception DirNotFound
  val openDir : string -> dirstream
  val readDir : dirstream -> string option
  val closeDir : dirstream -> unit

  val read_files_with_objs :
      {dirname: string} -> (string -> bool) ->
      ({fakearcs:string list,base:string} -> 'a -> 'a) ->
      'a ->
      'a
  (* test is on bare name; action/reducer can take side effects and is
     passed base name (which matches the predicate) as well as
     a list of possible fake arcs that should be appended to the
     dirname in order to generate genuine path *)

end
