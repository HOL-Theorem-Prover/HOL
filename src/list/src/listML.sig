signature listML =
sig

  val cons    : 'a * 'a list -> 'a list
  val null    : 'a list -> bool
  val hd      : 'a list -> 'a
  val tl      : 'a list -> 'a list
  val append  : 'a list -> 'a list -> 'a list
  val flat    : 'a list list -> 'a list
  val length  : 'a list -> numML.num
  val map     : ('a -> 'b) -> 'a list -> 'b list
  val map2    : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val mem     : ''a -> ''a list -> bool
  val filter  : ('a -> bool) -> 'a list -> 'a list
  val foldr   : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b
  val foldl   : ('b -> 'a -> 'b) -> 'b -> 'a list -> 'b
  val every   : ('a -> bool) -> 'a list -> bool
  val exists  : ('a -> bool) -> 'a list -> bool
  val el      : numML.num -> 'a list -> 'a
  val zip     : 'a list * 'b list -> ('a * 'b) list
  val unzip   : ('a * 'b) list -> 'a list * 'b list
  val sum     : numML.num list -> numML.num
  val reverse : 'a list -> 'a list
  val last    : 'a list -> 'a
  val front   : 'a list -> 'a list
  val all_distinct : ''a list -> bool

end
