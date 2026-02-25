signature TraceCompress =
sig
  (* Compress a .pft file in-place. Returns the final path
     (with compression extension, or unchanged if compression
     disabled or tool not found). *)
  val compress : string -> string

  (* Open a trace file for reading. Probes for the base path
     and compressed variants (.zst, .gz, .zip). Decompresses
     to a temp file if needed. Returns (instream, cleanup_fn)
     where cleanup_fn closes the stream and removes any temp
     file. *)
  val open_trace : string -> TextIO.instream * (unit -> unit)

  (* Find a trace file. Given a base path (without compression
     extension), returns SOME of the actual path that exists
     (possibly with compression extension), or NONE. *)
  val find_trace : string -> string option

  (* File suffixes to search for when scanning directories,
     e.g. ["Theory.pft", "Theory.pft.zst", ...] *)
  val trace_suffixes : string list
end
