signature PFTRename = sig

  (* Rename binder variables in a PFT file to recover clean names.
  
     PFTEmit uses unique names of the form "name pft%N" for binder
     variables to avoid capture. This module renames them back to
     "name" where doing so preserves alpha-equivalence.
  
     Assumptions on the input PFT file (satisfied by PFTEmit output):
     1. Each binder VAR (first argument of ABS) has a unique name:
        no other VAR command in the file shares that name.
     2. Each binder VAR ID is referenced only within its ABS body
        and as the first argument of exactly one ABS command.
  
     The module is binary-only. *)
  val rename : {input: string, output: string} -> unit

end
