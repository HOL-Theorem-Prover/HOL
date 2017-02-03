signature regexpMisc = 
sig
 val succeed : unit -> 'a
 val fail    : unit -> 'a

 val stdOut_print : string -> unit
 val stdErr_print : string -> unit

 val spread : 'a -> 'a list -> 'a list
 val spreadln : string -> int -> int -> string list -> string list

end