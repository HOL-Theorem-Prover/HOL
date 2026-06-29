signature QUse =
sig

val use : string -> unit
val useScript : string -> unit
val prim_use : {quietOpen : bool} -> string -> unit

(* True if any HOLSource parse error has been reported since this
   structure was loaded.  Consulted by the `bin/hol run` driver to
   translate silent parse errors into a non-zero process exit. *)
val hadError : unit -> bool

(* When true, `use` / `useScript` exit the process with failure as
   soon as a top-level dec finishes compiling under a parse error
   that has set the `hadError` flag.  The non-interactive `bin/hol`
   drivers (`run`, `buildheap`) flip this on; the interactive ones
   (`repl`, `lsp`) leave it off so a single parse failure doesn't
   abort the whole session. *)
val failOnError : bool ref

end
