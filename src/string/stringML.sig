signature stringML =
sig

  val chr         : Arbnum.num -> char
  val emptystring : string
  val explode     : string -> char list
  val implode     : char list -> string
  val strlen      : string -> Arbnum.num
  val strcat      : string -> string -> string
  val is_prefix   : string -> string -> bool

end
