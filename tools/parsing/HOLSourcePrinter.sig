signature HOLSourcePrinter = sig

type printer = {token: string -> unit, startSpan: int * int -> unit, stopSpan: unit -> unit}
val mkPrinter: (int -> int) ->
  {str: string -> unit, startSpan: int * int -> unit, stopSpan: unit -> unit} -> printer

val printDec: (int * int -> string -> unit) -> HOLSourceAST.dec -> printer -> unit
val printDecs: (int * int -> string -> unit) -> HOLSourceAST.dec list -> printer -> unit

end
