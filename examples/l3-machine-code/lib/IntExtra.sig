signature IntExtra =
sig
 val fromBinString : string -> IntInf.int option
 val fromBool : bool -> IntInf.int
 val fromHexString : string -> IntInf.int option
 val fromLit : string -> IntInf.int option
 val fromString : string -> IntInf.int option
 val pow : IntInf.int * IntInf.int -> IntInf.int
 val toBinString : IntInf.int -> string
 val toHexString : IntInf.int -> string
end
