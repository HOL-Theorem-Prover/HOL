structure Coding :> Coding =
struct

open optmonad
infix >- >> ++ >->

val || = op++

type 'a reader = string -> string * 'a option

fun getc s = if s = "" then (s, NONE)
             else (String.extract(s,1,NONE), SOME (String.sub(s,0)))

fun literal s1 s2 = if String.isPrefix s1 s2 then
                      (String.extract(s2,size s1,NONE), SOME s1)
                    else (s2, NONE)

fun takeP P s = let
  fun recurse i = if i >= size s then i
                  else if P (String.sub(s,i)) then recurse (i + 1)
                  else i
  val p = recurse 0
in
  (String.extract(s,p,NONE), SOME (String.extract(s,0,SOME p)))
end

fun eof s = if s = "" then (s, SOME ()) else (s, NONE)
fun chop i s = if i <= size s then (String.extract(s,i,NONE),
                                    SOME (String.extract(s,0,SOME i)))
               else (s,NONE)

fun lift df s = case df s of ("", SOME r) => SOME r
                           | _ => NONE

infix >*
fun (f >* g) = f >- (fn x => g >- (fn y => return (x,y)))
fun map f m = m >- (return o f)

structure IntData =
struct


fun encode i = Int.toString i ^ "."
val reader =
   (((literal "~" >> return ~1) ++ (literal "-" >> return ~1) ++
     return 1) >- (fn sign =>
    takeP Char.isDigit >- (fn digits =>
    if digits = "" then fail
    else literal "." >> return (sign * valOf (Int.fromString digits))))) ++
  fail

val decode = lift reader


end;

fun length_encoded df = let
  open IntData
in
  reader >- (fn len =>
  chop len >- (fn pfx =>
    case df pfx of
      NONE => fail
    | SOME r => return r))
end


structure StringData =
struct

fun encode s = let
  val s' = String.toString s
  val sz = size s'
in
  IntData.encode sz ^ s'
end

val reader = length_encoded String.fromString

val decode = lift reader

fun encodel slist = let
  val dlist = List.map encode slist
in
  String.concat dlist
end

val decodel = lift (many reader)

end (* string struct *)

structure BoolData =
struct

  fun encode true = "T"
    | encode false = "F"
  val reader = (literal "T" >> return true) ++ (literal "F" >> return false)
  val decode = lift reader
end

end (* struct *)
