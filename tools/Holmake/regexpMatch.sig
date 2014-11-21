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
  val pred_to_set : (char -> bool) -> char Binaryset.set

  structure POSIX : sig
    val alnum_set  : char Binaryset.set
    val alpha_set  : char Binaryset.set
    val ascii_set  : char Binaryset.set
    val blank_set  : char Binaryset.set
    val cntrl_set  : char Binaryset.set
    val digit_set  : char Binaryset.set
    val graph_set  : char Binaryset.set
    val lower_set  : char Binaryset.set
    val print_set  : char Binaryset.set
    val punct_set  : char Binaryset.set
    val space_set  : char Binaryset.set
    val upper_set  : char Binaryset.set
    val xdigit_set : char Binaryset.set
    val word_set   : char Binaryset.set
  end

  val regexp_compare : regexp * regexp -> order
  val regexpEqual : regexp -> regexp -> bool

  val regexp_to_dfa_arrays
      : regexp -> {delta : int vector vector,
                   start : int,
                   final : bool vector}

  val match : regexp -> string -> bool

end
