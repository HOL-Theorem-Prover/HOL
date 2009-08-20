structure CharSet :> CharSet =
struct

  type CharSet = Word8Vector.vector  (* all of length 32 *)

  open Word8Vector

  val word0 = Word8.fromInt 0
  val word1 = Word8.fromInt 1
  val << = Word8.<<
  val orb = Word8.orb
  val andb = Word8.andb

  val empty = tabulate(32, fn _ => word0)


  fun coords c = (ord c div 8, ord c mod 8)

  fun singleton c = let
    val (d, m) = coords c
    val cword = <<(word1, Word.fromInt m)
  in
    tabulate(32, fn i => if i = d then cword else Word8.fromInt 0)
  end

  fun add (cs, c) = let
    val (d, m) = coords c
    val cword = <<(word1, Word.fromInt m)
    fun update(i,w) = if i = d then orb(w, cword) else w
  in
    mapi update cs
  end

  fun addList (cs, clist) = List.foldl (fn (c, cs) => add(cs, c)) cs clist

  fun addString (cs, s) =
    Substring.foldl (fn (c, cs) => add(cs, c)) cs (Substring.full s)

  fun member(cs, c) = let
    val (d, m) = coords c
    val cword = <<(word1, Word.fromInt m)
  in
    andb(cword, sub(cs, d)) <> word0
  end

  fun isEmpty cs = let
    fun recurse i = if i = 32 then true
                    else Word8.toInt (sub(cs, i)) = 0 andalso recurse (i + 1)
  in
    recurse 0
  end

  fun union(cs1, cs2) = let
    fun update(i, w) = orb(w, sub(cs2, i))
  in
    mapi update cs1
  end

  fun intersect(cs1, cs2) = let
    fun update(i, w) = andb(w, sub(cs2, i))
  in
    mapi update cs1
  end

  fun setbits_fold f acc w = let
    fun recurse w0 i acc =
        if i <= 7 then
          if andb(w0,w) <> word0 then
            recurse (<<(w0, Word.fromInt 1)) (i + 1) (f (i, acc))
          else
            recurse (<<(w0, Word.fromInt 1)) (i + 1) acc
        else
          acc
  in
    recurse word1 0 acc
  end

  fun listItems cs = let
    fun f(d,w,acc) = let
      fun g(m, acc) = Char.chr(d * 8 + m) :: acc
    in
      setbits_fold g acc w
    end
  in
    foldri f [] cs
  end

end;

