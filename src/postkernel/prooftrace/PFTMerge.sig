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
     - Renumbers IDs globally within each of the four namespaces
     - Includes only theorems reachable from the targets
     - Recomputes DELs after last use
     - Emits SAVE only for the explicit targets (and optionally
       their constant/type definitions)
     - Writes the footer with namespace bounds

     Inputs use version 1 and a single supported ruleset. Input IDs must
     never be reused, even after deletion. Output IDs are reused after last
     use, and footer bounds record their high-water counts. Candle type-definition
     results occupy consecutive theorem IDs.
     Malformed headers and unsupported dependency order fail before the
     output is opened. Named and anonymous cross-file references are
     resolved by their SAVE/LOAD names (e.g. thy$name and thy#0). *)
  val merge : { inputs : string list,      (* topsorted .pft files *)
                targets : target list,
                output : string,
                binary : bool } -> unit

end
