(* Author: Michael Norrish *)

structure optmonad :> optmonad =
struct

type ('a, 'b) optmonad = 'a -> ('a * 'b option)

fun fail env = (env, NONE)

fun return x env = (env, SOME x)

fun ok env = (env, SOME ())

infix >- ++ >> >-> +++

fun (m1 >- f) env = let
  val (env0, res0) = m1 env
in
  case res0 of
    NONE => (env0, NONE)
  | SOME res => f res env0
end
fun (m1 >> m2) = (m1 >- (fn _ => m2))

fun (m1 ++ m2) env = let
  val (env0, res) = m1 env
in
  case res of
    NONE => m2 env
  | x => (env0, res)
end

val op+++ = op++

fun (m1 >-> m2) = m1 >- (fn x => m2 >> return x)
fun optional p = (p >- return o SOME) ++ (return NONE)
fun mmap f [] =  return []
  | mmap f (x::xs) = let
    in
      f x >-            (fn x' =>
      mmap f xs >-      (fn xs' =>
      return (x'::xs')))
    end

fun tryall f [] = fail
  | tryall f (x::xs) = f x ++ tryall f xs

local
  fun repeatn' 0 f = ok
    | repeatn' n f = f >> repeatn' (n - 1) f
in
  fun repeatn n f = if n < 0 then fail else repeatn' n f
end

fun repeat p env = ((p >> repeat p) ++ ok) env

fun many p =
  (p >- (fn i => many p >- (fn rest => return (i::rest)))) +++
  (return [])

fun many1 p =
  p >- (fn i => many p >- (fn rest => return (i::rest)))

end
