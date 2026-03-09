signature QUse =
sig

val use : string -> unit
val useScript : string -> unit
val prim_use : {quietOpen : bool, canBindStr : bool} -> string -> unit

end
