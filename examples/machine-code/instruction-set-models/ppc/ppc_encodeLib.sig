signature ppc_encodeLib =
sig

    val ppc_encode                   : string -> string
    val ppc_supported_instructions   : unit -> string list

end
