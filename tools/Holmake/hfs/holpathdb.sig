signature holpathdb =
sig

  (* pathdb implements a mapping from user-chosen variable names, e.g.,
     PROJDIR to directories.  Given the implementation in terms of
     files deposited in the relevant directories, it is necessarily 1-1 *)
  val lookup_holpath : {vname : string} -> string option
  val extend_db : {vname: string, path : string} -> unit
  val db_vnames : unit -> string Binaryset.set (* domain of map *)
  val db_dirs : unit -> string Binaryset.set (* range of map *)
  val fold : ({vname:string,path:string} -> 'a -> 'a) -> 'a -> 'a
  val owning_var : {path : string} -> {vname : string, rest : string} option
                  (* the registration whose directory contains the
                     argument, longest first, with rest the remainder of
                     the argument below that directory ("" when the two
                     are the same directory).  NONE when no registered
                     directory contains it. *)
  val reverse_lookup : {path : string} -> string
                  (* owning_var, written as "$(VNAME)/rest"; the
                     argument unchanged when there is no owning
                     registration. *)
  val subst_pathvars : string -> string
                  (* may complain to stdErr about malformed variable things *)


  (* pulls in contents of all "matching files" that can be found
     starting at starter_dirs and moving up in the file hierarchy.
     In addition, for every directory, generate fresh places to also consider
     using the function argument.  Any given directory will only be visited
     once.  All strings encoding directories must be absolute paths.

     Files are examined by looking for the names in the filenames list, the first that
     exists is used.

     Returns a map from directory name to filename * file-contents
  *)
  val files_upward_in_hierarchy :
      (string -> string list) -> {diag: (unit -> string) -> unit} ->
      {filenames : string list, starter_dirs : string list,
       skip : string Binaryset.set} ->
      (string, (string * string)) Binarymap.dict

  (* uses the above *)
  val search_for_extensions :
      (string -> string list) ->
      {starter_dirs : string list, skip : string Binaryset.set} ->
      {vname:string, path:string} list

end
