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
 val bigIntervals : IntInf.int list -> (IntInf.int * IntInf.int) list
 val intervals : int list -> (int * int) list

 val twoE : int -> IntInf.int

 val ntimes : ('a -> 'a) -> int -> 'a -> 'a
 val cross  : 'a list -> 'b list -> ('a * 'b) list
 val transpose  : 'a list list -> 'a list list

end
