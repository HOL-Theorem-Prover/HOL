structure stmonad :> stmonad =
struct
type ('a, 'b) stmonad = 'a -> ('a * 'b)

infix >> >-

fun (f >- g) s0 = let
  val (s1, res) = f s0
in
  g res s1
end

fun (f >> g) = f >- (fn _ => g)

fun return v s = (s, v)
fun ok s = return () s


fun mmap f list =
  case list of
    [] => return []
  | (x::xs) => f x >- (fn x' => mmap f xs >- (fn xs' => return (x'::xs')))
end
