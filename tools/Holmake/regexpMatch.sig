signature regexpMatch =
sig

  val MAX_ORD : int
  val ALPHABET_SIZE : int

  exception regexpErr of string * string

  val debug : bool ref

  datatype regexp
    = Epsilon
    | Symbs of char Binaryset.set
    | Not of regexp
    | Sum of regexp * regexp
    | And of regexp * regexp
    | Dot of regexp * regexp
    | Star of regexp

  val empty_cset : char Binaryset.set
  val univ_cset : char Binaryset.set
  val regexp_compare : regexp * regexp -> order
  val regexpEqual : regexp -> regexp -> bool

  val regexp_to_dfa_arrays
      : regexp -> {delta : int vector vector,
                   start : int,
                   final : bool vector}

  val match : regexp -> string -> bool

end
