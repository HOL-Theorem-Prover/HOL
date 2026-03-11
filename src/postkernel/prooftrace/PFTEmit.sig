signature PFTEmit = sig

  (* Reference to a theorem within a theory *)
  datatype thm_ref = NamedThm of string    (* named export *)
                   | AnonThm of int        (* anonymous export by index *)

  (* A target theorem to prove and SAVE in the output.
     save_defs controls whether definitions of constants/types
     used by this target are also SAVEd. *)
  datatype target = ThyThm of string * string * bool  (* thy, name, save_defs *)
                  | ThyAll of string * bool            (* all named exports, save_defs *)

  (* Phase 1: Discover dependencies and topsort.
     Given search directories and targets, find the .tr.gz files needed
     to prove the targets and return them in topological order
     (dependencies first). For each file, return the list of theorem
     references needed from that theory.

     Searches for <thy>Theory.tr.gz in the given directories.
     Traces Disk references transitively to discover all dependencies. *)
  val resolve : { search_path : string list,
                  targets : target list }
                -> (string * thm_ref list) list

  (* Phase 2: Emit a PFT trace.
     Takes the topsorted output of resolve (or a manually constructed
     equivalent), the targets to SAVE, and produces a single PFT file.

     The output contains no LOAD commands — all cross-theory
     references are resolved inline. SAVE is emitted only for the
     explicit targets (and their definitions if save_defs is set).

     The header with peak counts is prepended after all commands
     are emitted. *)
  val emit : { resolved : (string * thm_ref list) list,
               targets : target list,
               output : string,
               binary : bool } -> unit

end
