signature parse_glob =
sig

  datatype t = RE of regexpMatch.regexp | CHAR of char

  val parse_glob : string -> regexpMatch.regexp
  val parse_glob_components : string -> t list
  val toRegexp : t list -> regexpMatch.regexp

end

(* [parse_glob s] returns the regular expression corresponding to the
   shell glob-expression s. Glob-expressions use the ?, [ and *
   meta-characters and are documented in shell manual pages.

   All strings generate a regular expression in this syntax. For
   example, the superficially malformed "[a-" is the regular expression
   that matches the one string "[a-".
*)
