(* Self-contained Candle pipeline demo.

   Given HOL4 proof-trace dumps boolTheory.tr.gz and markerTheory.tr.gz
   in the current directory, produces a single merged Candle-ruleset
   proof trace in both encodings:
     merged.candle.pft.bin
     merged.candle.pft.jsonl

   Pipeline:
     1. Emit candle-preamble.pft.bin          (PFTCandlePreamble.emit)
     2. Emit {bool,marker}.candle.pft.bin     (PFTEmit.emit_theory)
     3. Merge into merged.candle.raw.pft.bin  (PFTMerge.merge)
     4. Rename binders                        (PFTRename.rename)
     5. Transcode bin -> jsonl                (PFTTranscode.transcode)
*)

val theories = ["bool", "marker"]

val preamble_bin = "candle-preamble.pft.bin"
fun theory_in  s = s ^ "Theory.tr.gz"
fun theory_pft s = s ^ ".candle.pft.bin"
fun log s = print (s ^ "\n")

(* 1. Preamble *)
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
     output  = theory_pft s,
     binary  = true,
     ruleset = PFTEmit.Candle
   }))
  theories

(* 3. Merge *)
val merged_raw = "merged.candle.raw.pft.bin"
val () = log "Merging..."
val () = PFTMerge.merge {
  inputs  = preamble_bin :: List.map theory_pft theories,
  targets = List.map (fn s => PFTMerge.ThyAll (s, false)) theories,
  output  = merged_raw,
  binary  = true
}

(* 4. Rename binders *)
val merged_bin = "merged.candle.pft.bin"
val () = log "Renaming binders..."
val () = PFTRename.rename {input = merged_raw, output = merged_bin}
val () = OS.FileSys.remove merged_raw

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
