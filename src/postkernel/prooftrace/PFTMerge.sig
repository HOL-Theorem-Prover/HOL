signature PFTMerge = sig

  (* Reference to a theorem to include in the merged output *)
  datatype thm_ref = NamedThm of string    (* named export: thy$name *)
                   | AnonThm of int        (* anonymous export by index *)

  (* A target theorem to prove and SAVE in the merged output.
     save_defs controls whether definitions of constants/types
     used by this target are also SAVEd. *)
  datatype target = ThyThm of string * string * bool  (* thy, name, save_defs *)
                  | ThyAll of string * bool            (* all named exports, save_defs *)

  (* Merge multiple per-theory .pft files into a single .pft file.

     Input: topsorted list of .pft file paths, plus target theorems
     to include and SAVE.

     The merger:
     - Reads each .pft file using PFTReader
     - Eliminates SAVE/LOAD pairs: replaces LOAD references with
       the original theorem's ID in the merged namespace
     - Renumbers all IDs into a single global namespace
     - Includes only theorems reachable from the targets
     - Recomputes DELs for tight memory usage
     - Emits SAVE only for the explicit targets (and optionally
       their constant/type definitions)
     - Writes correct footer with peak namespace counts *)
  val merge : { inputs : string list,      (* topsorted .pft files *)
                targets : target list,
                output : string,
                binary : bool } -> unit

end
