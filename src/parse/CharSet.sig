signature CharSet =
sig

  type CharSet
  val empty : CharSet
  val singleton : char -> CharSet
  val add : (CharSet * char) -> CharSet
  val addList : (CharSet * char list) -> CharSet
  val addString : (CharSet * string) -> CharSet
  val member : CharSet * char -> bool
  val isEmpty : CharSet -> bool

  val union : CharSet * CharSet -> CharSet
  val intersect : CharSet * CharSet -> CharSet

  val listItems : CharSet -> char list

end;
