signature PFTEmit = sig

  datatype ruleset = HOL4 | Candle

  (* When true, emit debug EXPECT records (opcode 0xEF) after each derived
     theorem, carrying its expected hypothesis term-ids and conclusion
     term-id. Downstream tools that do not understand EXPECT (merge, replay,
     transcode) will reject input files that contain them. *)
  val emit_expect : bool ref

  (* Convert a single theory's internal proof trace (.tr.gz) to PFT format.

     SAVEs all named and anonymous exports.
     LOADs all cross-theory dependencies (Disk references).
     DELs objects when no subsequent command references them.

     The output .pft file can be replayed standalone if its dependencies
     are loaded first (via their own .pft files, in dependency order).

     ID allocation: IDs are allocated monotonically (0, 1, 2, ...) in each
     namespace and are never reused. DEL commands are emitted to inform the
     replayer when objects are no longer needed, but the emitted ID range
     always spans 0..n-1 where n is the total number of objects allocated
     in that namespace. The footer reports these totals.

     This means the output may have a larger ID space than the peak live
     set. A downstream tool (e.g., PFTMerge) can compact the ID space by
     renumbering and reusing IDs, producing a trace with tighter limits.

     ruleset controls the output format:
       HOL4   - hol4 ruleset (original behaviour)
       Candle - candle ruleset (uses pro-formas from PFTCandlePreamble,
                translates names for core boolean constants/types) *)
  val emit_theory : { trace : string,       (* input .tr.gz file *)
                      output : string,       (* output .pft file *)
                      binary : bool,
                      ruleset : ruleset } -> unit

end
