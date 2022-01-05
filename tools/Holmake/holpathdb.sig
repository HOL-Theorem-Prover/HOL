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
  val reverse_lookup : {path : string} -> string
  val subst_pathvars : string -> string
                  (* may complain to stdErr about malformed variable things *)


  (* pulls in contents of all the files with name filename that can be found
     starting at starter_dirs and moving up in the file hierarchy.
     In addition, for every directory, generate fresh places to also consider
     using the function argument.  Any given directory will only be visited
     once.  All strings encoding directories must be absolute paths.
     Returns a map from directory name to file contents *)
  val files_upward_in_hierarchy :
      (string -> string list) ->
      {filename : string, starter_dirs : string list,
       skip : string Binaryset.set} ->
      (string, string) Binarymap.dict

  (* uses the above *)
  val search_for_extensions :
      (string -> string list) ->
      {starter_dirs : string list, skip : string Binaryset.set} ->
      {vname:string, path:string} list

end
