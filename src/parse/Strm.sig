signature Strm =
sig

  datatype 'a item = CH of Char.char
                   | AQ of 'a
  type 'a strm

  val get     : 'a strm -> ('a item * 'a strm) option
  val strm_of : 'a frag list -> 'a strm
  val dropl   : (Char.char -> bool) -> 'a strm -> 'a strm
  val splitl  : (Char.char -> bool) -> 'a strm -> Substring.substring * 'a strm
  val base    : 'a strm -> String.string * int * int
  val string_of : 'a strm -> String.string
  val MLcomment : 'a strm -> 'a strm option

end