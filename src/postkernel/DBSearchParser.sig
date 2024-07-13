signature DBSearchParser =
sig
    datatype search_regexp = Optional of search_regexp
                | Or of search_regexp * search_regexp
                | Twiddle of search_regexp * search_regexp
                | Seq of search_regexp * search_regexp
                | Word of char list
                | Many of search_regexp
                | Any
    val parse_regexp : string -> search_regexp
    val translate_regexp : search_regexp -> regexpMatch.regexp
    val contains : regexpMatch.regexp -> regexpMatch.regexp
end
