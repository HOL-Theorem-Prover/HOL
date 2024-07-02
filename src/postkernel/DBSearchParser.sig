signature DBSearchParser =
sig
    type search_regexp
    val parse_regexp : string -> search_regexp
    val translate_regexp : search_regexp -> regexpMatch.regexp
    val contains_regexp : string -> string -> bool
end
