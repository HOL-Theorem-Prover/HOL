signature HOLToSML = sig

val expandDec:
  { fileline: int -> HOLAst.fileline,
    parseError: int * int -> string -> unit,
    quietOpen: bool } ->
  HOLAst.dec -> HOLAst.dec list -> HOLAst.dec list

end
