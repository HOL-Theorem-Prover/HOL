signature regexpMisc =
sig
 val succeed : unit -> 'a
 val fail    : unit -> 'a

 val stdOut_print : string -> unit
 val stdErr_print : string -> unit

 val spread : 'a -> 'a list -> 'a list
 val spreadln : {sep:string, ln:string, width:int}
                -> string list -> string list

end