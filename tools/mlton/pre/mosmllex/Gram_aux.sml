(* Auxiliaries for the parser. *)

structure Gram_aux =
struct

fun regexp_for_string s =
    let open CharVector infix 9 sub
	val len = length s
	fun re_string n =
	  if n >= len then Syntax.Epsilon
	  else if n+1 = len then Syntax.Characters([s sub n])
	  else Syntax.Sequence(Syntax.Characters([s sub n]), re_string (n+1))
     in re_string 0
    end


fun char_class c1 c2 =
    let val n2 = Char.ord c2
        fun class n =
	  if n > n2 then []
	  else (Char.chr n) :: class(n+1)
     in class (Char.ord c1)
    end


val all_chars = char_class #"\001" #"\255"

fun subtract (xs: char list, []: char list) = xs
  | subtract (xs,ys) =
    let fun notmember (k: char,[]: char list) = true
          | notmember (k,(x :: xs)) =
              if k = x then false else notmember(k,xs)
     in List.filter (fn x => notmember(x,ys)) xs
    end


end (* structure Gram_aux *)
