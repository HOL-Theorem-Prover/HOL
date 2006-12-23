structure fcpML :> fcpML =
struct

open numML

exception IndexUndefined

datatype holtype = Tyvar of string
                 | Tyop of string * holtype list

datatype ('a, 'b) cart = FCP of ('b -> 'a)

type 'a itself = holtype

fun dimindex t =
  case t of
    Tyvar _ => raise IndexUndefined
  | Tyop ("one", [])  => numML.ONE
  | Tyop ("bool", []) => numML.TWO
  | Tyop ("option", [a])  => numML.SUC (dimindex a)
  | Tyop ("sum", [a, b])  => numML.+ (dimindex a) (dimindex b)
  | Tyop ("prod", [a, b]) => numML.* (dimindex a) (dimindex b)
  | _ => raise IndexUndefined;

fun index_type n =
  let val bool = Tyop ("bool", []) open Int in
    if n mod 2 = 0 then
      if n = 0 then
        raise raise IndexUndefined
      else if n = 2 then
        bool
      else
        Tyop("prod", [bool, index_type (n div 2)])
    else
      if n = 1 then
        Tyop("one", [])
      else if n = 3 then
        Tyop("option", [bool])
      else
        Tyop("option", [Tyop("prod", [bool, index_type ((n - 1) div 2)])])
  end;

local
  fun compare (a, b) =
    case (a, b) of
      (Tyvar x, Tyvar y) => String.compare(x,y)
    | (Tyvar _, Tyop _)  => LESS
    | (Tyop _, Tyvar _)  => GREATER
    | (Tyop (x, []), Tyop (y, [])) => String.compare(x,y)
    | (Tyop (x, [a, b]), Tyop (y, [c, d])) =>
        (case String.compare(x,y) of
           EQUAL => (case compare(a, c) of
                       EQUAL => compare (b, d)
                     | z => z)
         | w => w)
    | _ => raise IndexUndefined

  val dict_INT_MIN:(holtype, num) Redblackmap.dict = Redblackmap.mkDict compare
  val dict_dimword:(holtype, num) Redblackmap.dict = Redblackmap.mkDict compare
in
  fun INT_MIN t = Redblackmap.find(dict_INT_MIN,t)
    handle NotFound =>
      let val n = EXP TWO (PRE (dimindex t))
          val _ = Redblackmap.insert(dict_INT_MIN,t,n)
      in n end

  fun dimword t = Redblackmap.find(dict_dimword,t)
    handle NotFound =>
      let val n = EXP TWO (dimindex t)
          val _ = Redblackmap.insert(dict_dimword,t,n)
      in n end
end

end
