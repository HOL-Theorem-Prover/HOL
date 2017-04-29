signature ReadHMF =
sig

  type env = Holmake_types.env
  type ruledb = Holmake_types.ruledb
  val read : string -> env -> env * ruledb * string option

  val find_includes : string -> string list

end;

(*

   [find_includes dirname] reads the Holmakefile (if any) in directory
   dirname, and returns the list of directories (in canonical form)
   that are pointed to by INCLUDES variable declarations. If there is
   no Holmakefile, the empty list is returned. The directory name in
   dirname must be a absolute filename.

*)
