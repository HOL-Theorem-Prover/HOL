signature x86_encodeLib =
sig

    val x86_encode                   : string -> string
    val x86_supported_instructions   : unit -> string list

end
