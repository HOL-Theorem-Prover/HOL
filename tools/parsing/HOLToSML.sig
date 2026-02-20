signature HOLToSML = sig

val mkSemi: HOLAst.dec list -> HOLAst.dec list

val expandDec:
  { fileline: int -> HOLAst.fileline,
    parseError: int * int -> string -> unit,
    quietOpen: bool } ->
  HOLAst.dec -> HOLAst.dec

end
