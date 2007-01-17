structure fcpML :> fcpML =
struct

exception IndexUndefined

datatype holtype = Tyop of string * holtype list

datatype ('a, 'b) cart = FCP of ('b -> 'a)

type 'a itself = holtype

fun dimindex t =
  case t of
    Tyop ("one", [])      => numML.ONE
  | Tyop ("bit0", [a])    => numML.iDUB (dimindex a)
  | Tyop ("bit1", [a])    => numML.BIT1 (dimindex a)
  | Tyop ("sum", [a, b])  => numML.+ (dimindex a) (dimindex b)
  | Tyop ("prod", [a, b]) => numML.* (dimindex a) (dimindex b)
  | Tyop (x, [])          => (if String.sub(x,0) = #"i" then
                                numML.fromString(String.extract(x,1,NONE))
                              else
                                raise IndexUndefined)
  | _ => raise IndexUndefined

fun index_type n = Tyop("i" ^ Int.toString n, []);

local
  open numML Redblackmap
  val index_list = [2, 3, 4, 5, 6, 7, 8, 12, 16, 20, 24, 28, 30, 32, 64]
  
  fun index_dict f =
         List.foldl (fn (n, d) => insert(d,"i" ^ Int.toString n, f n))
                    (mkDict String.compare) index_list

  val dict_INT_MIN = index_dict (fn n => EXP TWO (fromInt (Int.-(n, 1))))
  val dict_dimword = index_dict (fn n => EXP TWO (fromInt n))
in
  fun INT_MIN (t as Tyop(s, [])) =
        (find(dict_INT_MIN,s) handle NotFound => EXP TWO (PRE (dimindex t)))
    | INT_MIN t = EXP TWO (PRE (dimindex t))

  fun dimword (t as Tyop(s, [])) =
        (find(dict_dimword,s) handle NotFound => EXP TWO (dimindex t))
    | dimword t = EXP TWO (dimindex t)
end

end
