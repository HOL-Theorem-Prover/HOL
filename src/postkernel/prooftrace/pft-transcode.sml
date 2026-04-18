(* Usage:
     pft-transcode <input.pft.bin>   <output.pft.jsonl>   (bin -> jsonl)
     pft-transcode <input.pft.jsonl> <output.pft.bin>     (jsonl -> bin)
   Encodings are inferred from the file extensions (.bin vs anything else). *)

fun is_bin s = String.isSuffix ".bin" s

val () =
  case CommandLine.arguments () of
    [i, o'] =>
      PFTTranscode.transcode
        {input = i, input_binary = is_bin i,
         output = o', output_binary = is_bin o'}
  | _ => (TextIO.output (TextIO.stdErr,
           "usage: pft-transcode <input> <output>\n"); OS.Process.exit OS.Process.failure)
