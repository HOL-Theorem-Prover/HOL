(* Author: Michael Norrish *)

structure optmonad :> optmonad =
struct

type ('a, 'b) optmonad = 'a -> ('a * 'b) option

fun fail env = NONE

fun return x env = SOME (env, x)

fun ok env = return () env

infix >- ++ >> >-> +++

fun (m1 >- f) env0 =
  case m1 env0 of
      NONE => NONE
    | SOME(env1, res1) => f res1 env1
fun (m1 >> m2) = (m1 >- (fn _ => m2))

fun (m1 ++ m2) env0 =
  case m1 env0 of
      NONE => m2 env0
    | x => x

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

fun lift f m = m >- (fn a => return (f a))
fun lift2 f m1 m2 = m1 >- (fn a => m2 >- (fn b => return (f a b)))

fun addState s m s0 =
  case m (s0,s) of
      NONE => NONE
    | SOME((s0',s'), x) => SOME(s0',(s',x))

end
