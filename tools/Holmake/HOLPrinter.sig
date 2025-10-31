signature HOLPrinter = sig

type printer = {token: string -> unit, startSpan: int * int -> unit, stopSpan: unit -> unit}
val mkPrinter:
  {str: string -> unit, startSpan: int * int -> unit, stopSpan: unit -> unit} -> printer

val printDecs: (int * int -> string -> unit) -> HOLAst.dec list -> printer -> unit

end
