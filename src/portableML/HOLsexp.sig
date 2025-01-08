signature HOLsexp =
sig

  datatype t = datatype HOLsexp_dtype.t
  type 'a encoder = 'a -> t
  type 'a decoder = t -> 'a option

  val Nil : t
  val Quote : t
  val List : t list -> t
  val strip_list : t -> t list * t option
  val dest_tagged : string -> t -> t option

  val tagged_encode : string -> 'a encoder -> 'a encoder
  val list_encode : 'a encoder -> 'a list encoder
  val pair_encode : ('a encoder * 'b encoder) -> ('a * 'b) encoder
  val pair3_encode : ('a encoder * 'b encoder * 'c encoder) ->
                     ('a * 'b * 'c) encoder
  val pair4_encode : ('a encoder * 'b encoder * 'c encoder * 'd encoder) ->
                     ('a * 'b * 'c * 'd) encoder


  val int_decode : int decoder
  val symbol_decode : string decoder
  val string_decode : string decoder
  val pair_decode : 'a decoder * 'b decoder -> ('a * 'b) decoder
  val pair3_decode : 'a decoder * 'b decoder * 'c decoder ->
                     ('a * 'b * 'c) decoder
  val pair4_decode : 'a decoder * 'b decoder * 'c decoder * 'd decoder ->
                     ('a * 'b * 'c * 'd) decoder
  val list_decode : 'a decoder -> 'a list decoder
  val tagged_decode : string -> 'a decoder -> 'a decoder
  val map_decode : ('a -> 'b) -> 'a decoder -> 'b decoder
  val bind_decode : 'a decoder -> ('a -> 'b option) -> 'b decoder


  val printer : t HOLPP.pprinter
  val scan : (char, 'a) StringCvt.reader -> (t, 'a) StringCvt.reader
  val fromString : string -> t option
  val fromStream : TextIO.instream -> t
  val fromFile : string -> t (* various possible failure to read exceptions *)

end
