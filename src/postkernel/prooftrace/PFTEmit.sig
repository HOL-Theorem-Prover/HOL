signature PFTEmit = sig

  (* Convert a single theory's internal proof trace (.tr.gz) to PFT format.

     SAVEs all named and anonymous exports.
     LOADs all cross-theory dependencies (Disk references).
     DELs objects when their refcount reaches zero within the theory.

     The output .pft file can be replayed standalone if its dependencies
     are loaded first (via their own .pft files, in dependency order). *)
  val emit_theory : { trace : string,       (* input .tr.gz file *)
                      output : string,       (* output .pft file *)
                      binary : bool } -> unit

end
