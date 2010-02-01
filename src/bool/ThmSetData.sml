structure ThmSetData :> ThmSetData =
struct

open DB LoadableThyData Lib

fun splitnm nm = let
  val comps = String.fields (equal #".") nm
in
  (hd comps, hd (tl comps))
end

fun lookup nm = uncurry DB.fetch (splitnm nm)

fun read s =
  map (fn n => (n, lookup n)) (String.fields Char.isSpace s)

fun write slist = String.concatWith " " slist

fun writeset set = let
  fun foldthis ((nm,th), acc) = let
    val _ = lookup nm
  in
    nm::acc
  end
  val list = List.foldr foldthis [] set
in
  String.concatWith " " list
end

val {mk,dest} = LoadableThyData.make {merge = op@,
                                      read_update = read,
                                      write_update = writeset}

fun mkData names = let
  fun foldthis (nm,set) = (nm, lookup nm) :: set
in
  mk (foldl foldthis [] names)
end

val destData = dest

val nullset = mkData []

end (* struct *)
