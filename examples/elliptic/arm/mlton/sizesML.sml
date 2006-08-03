structure sizesML :> sizesML =
struct

val index_list = [2, 3, 4, 5, 6, 7, 8, 12, 16, 20, 24, 28, 30, 32, 64];

val dict_INT_MIN = let open numML in
  foldl (fn (n, d) => Redblackmap.insert
           (d,"i" ^ Int.toString n,EXP TWO (fromInt (Int.-(n, 1)))))
    (Redblackmap.mkDict String.compare) index_list
end;

val dict_dimword = let open numML in
  foldl (fn (n, d) => Redblackmap.insert
           (d,"i" ^ Int.toString n,EXP TWO (fromInt n)))
    (Redblackmap.mkDict String.compare) index_list
end;

fun lookup_index f g (fcpML.Tyvar s) = raise fcpML.IndexUndefined
  | lookup_index f g (fcpML.Tyop (s, l)) =
      if null l then
        f s handle _ => raise fcpML.IndexUndefined
      else if s = "sum" andalso length l = 2 then
        g (lookup_index f g (hd l)) (lookup_index f g (hd (tl l)))
      else
        raise fcpML.IndexUndefined;

fun to_dimindex s =
  if String.sub(s,0) = #"i" then
    numML.fromString(String.extract(s,1,NONE))
  else
    raise fcpML.IndexUndefined;

val lookup_INT_MIN =
  let fun f s = Redblackmap.find(dict_INT_MIN,s) handle NotFound =>
        numML.EXP numML.TWO (numML.PRE (to_dimindex s))
  in
    lookup_index f numML.*
  end;

val lookup_dimword =
  let fun f s = Redblackmap.find(dict_dimword,s) handle NotFound =>
        numML.EXP numML.TWO (to_dimindex s)
  in
    lookup_index f numML.*
  end;

val lookup_dimindex = lookup_index to_dimindex numML.+;

fun sizes() =
  let val _ = wordsML.lookup_INT_MIN := lookup_INT_MIN;
      val _ = wordsML.lookup_dimword := lookup_dimword;
      val _ = fcpML.lookup_dimindex := lookup_dimindex;
  in () end;

end
