signature QUse =
sig

val use : string -> unit
val useScript : string -> unit
val prim_use : {quietOpen : bool} -> string -> unit

(* True if any HOLSource parse error has been reported since this
   structure was loaded.  Consulted by the `bin/hol run` driver to
   translate silent parse errors into a non-zero process exit. *)
val hadError : unit -> bool

end
