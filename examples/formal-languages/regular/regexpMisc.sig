signature regexpMisc =
sig
 val succeed : unit -> 'a
 val fail    : unit -> 'a

 val stdOut_print : string -> unit
 val stdErr_print : string -> unit

 val spread : 'a -> 'a list -> 'a list
 val spreadlnWith : {sep:string, ln:string, width:int}
                    -> ('a -> string)
		    -> 'a list -> string list

 val bigUpto : IntInf.int -> IntInf.int -> IntInf.int list

end