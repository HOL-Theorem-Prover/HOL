structure UTF8Set :> UTF8Set =
struct

datatype t = N of bool * t Inttab.table

open UTF8

val empty = N(false, Inttab.empty)

fun add(N (b,m), s) =
    case getChar s of
      NONE => N(true, m)
    | SOME ((c,i), rest) => let
      in
        case Inttab.lookup m i of
          NONE => N(b, Inttab.update (i, add(empty, rest)) m)
        | SOME t => N(b, Inttab.update (i, add(t, rest)) m)
      end

fun addList (t, slist) = List.foldl (fn (s,t) => add(t,s)) t slist

fun isEmpty (N(b,m)) = not b andalso Inttab.size m = 0

fun listItems set = let
  fun listItems' pfx acc (N(b,m)) = let
    fun foldthis (i,set) acc =
        listItems' (pfx ^ chr i) acc set
    val acc' = if b then pfx :: acc else acc
  in
    Inttab.fold foldthis m acc'
  end
in
  listItems' "" [] set
end

fun member(N(b,m),s) =
    case getChar s of
      NONE => b
    | SOME((_,i), rest) => let
      in
        case Inttab.lookup m i of
          NONE => false
        | SOME s' => member (s', rest)
      end

fun longest_pfx_member(set, s) = let
  fun recurse best curpfx s (N(b,m)) = let
    val best = if b then SOME {pfx=curpfx,rest=s} else best
  in
    case getChar s of
      NONE => best
    | SOME ((_, i), rest) => let
      in
        case Inttab.lookup m i of
          NONE => best
        | SOME set => recurse best (curpfx ^ chr i) rest set
      end
  end
in
  recurse NONE "" s set
end



end (* struct *)
