signature fcpML =
sig

  exception IndexUndefined

  datatype holtype = Tyvar of string
                   | Tyop of string * holtype list

  type ('a, 'b) cart
  type 'a itself = holtype

  val dimindex   : holtype -> numML.num
  val index_type : Int.int -> holtype 
  val INT_MIN    : holtype -> numML.num
  val dimword    : holtype -> numML.num

end
