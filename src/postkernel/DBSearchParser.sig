signature DBSearchParser =
sig
    datatype search_regexp = Optional of search_regexp
                | Or of search_regexp * search_regexp
                | Twiddle of search_regexp * search_regexp
                | Seq of search_regexp * search_regexp
                | Char of char
                | Many of search_regexp
                | Empty
                | Any
    val parse_regexp : string -> search_regexp
    val translate_regexp : search_regexp -> regexpMatch.regexp
    val contains_regexp : string -> string -> bool
end
