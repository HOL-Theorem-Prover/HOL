(* Self-contained Candle pipeline demo.

   Given HOL4 proof-trace dumps *Theory.tr.gz
   in the current directory, produces a single merged Candle-ruleset
   proof trace, for a targets, in both encodings:
     merged.candle.pft.bin
     merged.candle.pft.jsonl

   Pipeline:
     1. Emit candle-preamble.pft.bin          (PFTCandlePreamble.emit)
     2. Emit {...}.candle.pft.bin             (PFTEmit.emit_theory)
     3. Rename binders in each theory PFT     (PFTRename.rename)
     4. Merge into merged.candle.pft.bin      (PFTMerge.merge)
     5. Transcode bin -> jsonl                (PFTTranscode.transcode)

   Note: PFTRename runs BEFORE merge because its uniqueness assumptions
   are satisfied per-file by PFTEmit, but would be violated after merge
   (different files may reuse the same binder counter values). The
   preamble uses plain variable names and does not need renaming.
*)

val theories = ["bool", "marker", "num", "sat", "combin", "relation",
                "prim_rec", "quotient", "pair", "arithmetic", "numeral"]

val targets =
    (* everything
    List.map (fn s => PFTMerge.ThyAll (s, false)) theories
    *)
    [PFTMerge.ThyThm ("arithmetic", "X_LE_DIV", true),
     PFTMerge.ThyThm ("num", "INDUCTION", true)]

val preamble_bin = "candle-preamble.pft.bin"
fun theory_in  s = s ^ "Theory.tr.gz"
fun theory_raw s = s ^ ".candle.raw.pft.bin"
fun theory_pft s = s ^ ".candle.pft.bin"
fun log s = print (s ^ "\n")

(* 1. Preamble — uses plain variable names, no rename needed *)
val () = log "Emitting candle preamble..."
val () = PFTCandlePreamble.emit
  {output = preamble_bin, binary = true}

(* 2. Per-theory PFTs.
   EXPECT records are debug-only and downstream tools (merge/rename/
   replay/transcode) don't handle opcode 0xEF, so turn them off. *)
val () = PFTEmit.emit_expect := false
val () = log "Emitting per-theory Candle PFTs..."
val () = List.app (fn s =>
  (log ("  " ^ s);
   PFTEmit.emit_theory {
     trace   = theory_in s,
     output  = theory_raw s,
     binary  = true,
     ruleset = PFTEmit.Candle
   }))
  theories

(* 3. Rename binders in each theory PFT *)
val () = log "Renaming binders..."
val () = List.app (fn s =>
  (log ("  " ^ s);
   PFTRename.rename {input = theory_raw s, output = theory_pft s};
   OS.FileSys.remove (theory_raw s)))
  theories

(* 4. Merge *)
val merged_bin = "merged.candle.pft.bin"
val () = log "Merging..."
val () = PFTMerge.merge {
  inputs  = preamble_bin :: List.map theory_pft theories,
  targets = targets,
  output  = merged_bin,
  binary  = true
}

(* 5. Transcode to JSON Lines *)
val merged_jsonl = "merged.candle.pft.jsonl"
val () = log "Transcoding to JSON Lines..."
val () = PFTTranscode.transcode {
  input = merged_bin, input_binary = true,
  output = merged_jsonl, output_binary = false
}

val () = log ("Done.\n"
  ^ "  " ^ merged_bin ^ "\n"
  ^ "  " ^ merged_jsonl)
