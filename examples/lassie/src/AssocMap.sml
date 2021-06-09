structure AssocMap =
struct

  datatype ('a, 'b) tree =
    Leaf
    | Node of 'a * 'b * ('a, 'b) tree * ('a, 'b) tree;

  fun append (kN:'a) (vN:'b) (tr:('a, 'b) tree) (cmp:'a * 'a -> order) =
    case tr of
    Leaf => Node (kN, vN, Leaf, Leaf)
    | Node (k, v, tr1, tr2) =>
      case cmp (kN, k) of
      LESS => Node (k, v, append kN vN tr1 cmp, tr2)
      | _ => Node (k, v, tr1, append kN vN tr2 cmp);

  fun lookup (k1:'a) (tr:('a, 'b) tree) (cmp:'a * 'a -> order) :'b option =
    case tr of
    Leaf => NONE
    | Node (k2, v, tr1, tr2) =>
      case cmp (k1,k2) of
      EQUAL => SOME v
      | LESS => lookup k1 tr1 cmp
      | GREATER => lookup k1 tr2 cmp;

end;
