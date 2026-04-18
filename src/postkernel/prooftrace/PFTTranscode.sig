signature PFTTranscode = sig

  (* Transcode a PFT file between encodings.
     The abstract command stream is preserved verbatim: IDs, names, and
     command order are identical; only the physical encoding changes.

     Currently input_binary = true only (PFTReader does not yet parse
     JSON). output_binary selects the output encoding. *)
  val transcode : {input: string, input_binary: bool,
                   output: string, output_binary: bool} -> unit

end
