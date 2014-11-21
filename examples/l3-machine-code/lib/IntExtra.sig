signature IntExtra =
sig
 val fromBinString : string -> int option
 val fromBool : bool -> int
 val fromHexString : string -> int option
 val fromLit : string -> int option
 val fromString : string -> int option
 val toBinString : int -> string
 val toHexString : int -> string
end
