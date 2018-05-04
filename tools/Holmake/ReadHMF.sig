signature ReadHMF =
sig

  type env = Holmake_types.env
  type ruledb = Holmake_types.ruledb
  val read : string -> env -> env * ruledb * string option

  val find_includes : string -> string list
  val extend_path_with_includes :
      {quietp : bool, lpref : string list ref} -> unit

end;

(*

   [find_includes dirname] reads the Holmakefile (if any) in directory
   dirname, and returns the list of directories (in canonical form)
   that are pointed to by INCLUDES variable declarations. If there is
   no Holmakefile, the empty list is returned. The directory name in
   dirname must be a absolute filename.

   [extend_path_with_includes {quietp, lpref}] reads the Holmakefile
   (if any) in the current directory and updates the string list
   pointed to by lpref to include the INCLUDES and PRE_INCLUDES
   specified in the Holmakefile. If quietp is false, there will be an
   informative message printed to standard out noting that this is
   happening (when there is an INCLUDES or PRE_INCLUDES line).

*)
