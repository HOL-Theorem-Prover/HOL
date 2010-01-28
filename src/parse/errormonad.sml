structure errormonad :> errormonad =
struct

datatype ('a,'b) fs = Some of 'a | Error of 'b
type ('a, 'b, 'c) t = 'a -> ('a * ('b,'c) fs)

fun error e env = (env, Error e)
fun fail s = error s

fun return x env = (env, Some x)

fun ok env = (env, Some ())

infix >- ++ >> >-> +++

fun (m1 >- f) env = let
  val (env0, res0) = m1 env
in
  case res0 of
    Error e => (env0, Error e)
  | Some res => f res env0
end
fun (m1 >> m2) = (m1 >- (fn _ => m2))

fun (m1 ++ m2) env = let
  val m1res as (env0, res) = m1 env
in
  case res of
    Error _ => m2 env
  | x => m1res
end

fun mmap f [] =  return []
  | mmap f (x::xs) = let
    in
      f x >-            (fn x' =>
      mmap f xs >-      (fn xs' =>
      return (x'::xs')))
    end

local
  fun repeatn' 0 f = ok
    | repeatn' n f = f >> repeatn' (n - 1) f
in
  fun repeatn n f = if n < 0 then raise Fail "repeatn: n < 0"
                    else repeatn' n f
end

fun repeat p env = ((p >> repeat p) ++ ok) env

end



