signature HOLSourceExpand = sig

val mkSemi: HOLSourceAST.dec list -> HOLSourceAST.dec list

val expandDec:
  { fileline: int -> HOLSourceAST.fileline,
    parseError: int * int -> string -> unit,
    quietOpen: bool, canBindStr: bool } ->
  HOLSourceAST.dec -> HOLSourceAST.dec

end
