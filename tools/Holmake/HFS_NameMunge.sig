signature HFS_NameMunge =
sig

  val HOLOBJDIR : string (* for use in Holmakefiles' HOL_LNSIGOBJ *)
  val HOLtoFS : string -> {fullfile : string, dir : string} option
  val toFSfn : bool -> (string -> 'a) -> (string -> 'a)

  type dirstream
  val openDir : string -> dirstream
  val readDir : dirstream -> string option
  val closeDir : dirstream -> unit

end
