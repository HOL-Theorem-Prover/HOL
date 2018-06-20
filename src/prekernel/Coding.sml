structure Coding :> Coding =
struct

open optmonad
infix >- >> ++ >->

val || = op++

type 'a reader = (string*int,'a) optmonad

fun getc (s,i) = if i >= size s then NONE
                 else SOME ((s, i + 1), String.sub(s,i))

fun present_at (s,i) s2 =
  if size s2 + i > size s then false
  else
    let
      fun recurse d =
        d < 0 orelse
        String.sub(s, i + d) = String.sub(s2, d) andalso
        recurse (d - 1)
    in
      recurse (size s2 - 1)
    end

fun literal s (si as (s0,i)) =
  if present_at si s then SOME ((s0, i + size s), s)
  else NONE

fun takeP P (s,i) = let
  fun recurse i = if i >= size s then i
                  else if P (String.sub(s,i)) then recurse (i + 1)
                  else i
  val p = recurse i
in
  SOME ((s,p), String.substring(s,i,p-i))
end

fun eof (si as (s,i)) = if i >= size s then SOME (si, ()) else NONE
fun chop j (si as (s,i)) =
  if i + j <= size s then
    SOME ((s, i + j), String.substring(s,i,j))
  else NONE

fun lift df s =
  case df (s,0) of
      SOME ((s',i), r) => if i = size s' then SOME r else NONE
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
    else literal "." >> let
      val n = (sign * valOf (Int.fromString digits))
    in return n end handle Option => fail))) ++
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


structure CharData =
struct
  fun encode c = IntData.encode (ord c)
  fun i2c i = return (chr i) handle Chr => fail
  val reader = IntData.reader >- i2c
  val decode = lift reader
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

structure OptionData =
struct

  fun encode f NONE = "N"
    | encode f (SOME x) = "S" ^ f x
  fun reader f = (literal "N" >> return NONE) ++ (literal "S" >> f >- (return o SOME))
  fun decode f = lift (reader f)
end

structure PairData =
struct
   fun encode (af, bf) (a,b) = af a ^ "," ^ bf b
   fun reader (af, bf) = af >* (literal "," >> bf)
   fun decode (af, bf) = lift (reader (af, bf))
end

structure KernelNameData =
struct
   fun encode {Name,Thy} =
       PairData.encode (StringData.encode, StringData.encode) (Thy,Name)
   val reader = PairData.reader (StringData.reader, StringData.reader) >-
                (fn (Thy,Name) => return {Thy = Thy, Name = Name})
   val decode = lift reader
end

end (* struct *)
