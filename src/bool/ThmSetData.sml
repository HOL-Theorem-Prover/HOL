structure ThmSetData :> ThmSetData =
struct

open DB LoadableThyData Lib

val compare = pair_compare (String.compare,
                            inv_img_cmp Thm.concl Term.compare)

fun read s = let
  val names = String.fields Char.isSpace s
  fun foldthis (nm,acc) = HOLset.add(acc, (nm, DB.fetch "-" nm))
in
  foldl foldthis (HOLset.empty compare) names
end

fun write slist = String.concatWith " " slist

fun writeset set = let
  fun foldthis ((nm,th), acc) = let
    val _ = DB.fetch "-" nm
  in
    nm::acc
  end
  val list = HOLset.foldl foldthis [] set
in
  String.concatWith " " list
end

val {mk,dest} = LoadableThyData.make {merge = HOLset.union,
                                      read_update = read,
                                      write_update = writeset}

fun mkData names = let
  fun foldthis (nm,set) = HOLset.add(set, (nm, DB.fetch "-" nm))
in
  mk (foldl foldthis (HOLset.empty compare) names)
end

val destData = dest

val nullset = mkData []

end (* struct *)
