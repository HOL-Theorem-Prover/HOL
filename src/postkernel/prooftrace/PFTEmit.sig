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

     The output .pft file can be replayed standalone if its dependencies
     are loaded first (via their own .pft files, in dependency order).

     IDs are allocated monotonically in each namespace and are never reused.
     The footer gives the resulting array bounds. PFTMerge can select the
     target dependency closure and reuse slots after their final uses. Its
     footer gives allocation high-water marks, including consecutive result
     blocks required by implicit multi-result commands.

     The raw producer must use the current kernel identifier layout and the
     six-field identity-aware envelope; older raw traces must be regenerated.
     Exported side-file proofs and deleted/NoTrace proofs are unsupported.
     Candle compute consumers need the standalone compute preamble first.

     ruleset controls the output format:
       HOL4   - hol4 ruleset (original behaviour)
       Candle - candle ruleset (uses pro-formas from PFTCandlePreamble,
                translates names for core boolean constants/types) *)
  val emit_theory : { trace : string,       (* input .tr.gz file *)
                      output : string,       (* output .pft file *)
                      binary : bool,
                      ruleset : ruleset } -> unit

end
