signature DBSearchParser =
sig
    type regexp
    val compile_pattern : string -> regexp
    val matches : regexp -> string -> bool
end
