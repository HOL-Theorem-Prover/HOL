structure errormonad :> errormonad =
struct

datatype ('a,'b) fs = Some of 'a | Error of 'b
type ('s, 'a, 'error) t = 's -> ('s * 'a,'error) fs

fun error (e:'error) : ('s,'a,'error) t = fn env => Error e
fun fail s = error s

fun return x env = Some (env, x)

fun ok e = return () e (* eta-expanded b/c of value restriction *)

infix >- ++ >> >-> +++ ++?

fun bind (m1,f) env0 =
  case m1 env0 of
      Some (env1, res1) => f res1 env1
    | Error e => Error e (* pat and rhs have different types *)
val op >- = bind
fun (m1 >> m2) = (m1 >- (fn _ => m2))

fun (m1 ++ m2) env =
  case m1 env of
      Error _ => m2 env
    | Some x => Some x

fun (m1 ++? fm2) env =
  case m1 env of
      Error e => fm2 e env
    | Some x => Some x

fun mmap f [] =  return []
  | mmap (f:'a -> ('s,'b,'error) t) ((x:'a)::xs) = let
    in
      f x >-            (fn (x':'b) =>
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

fun lift f m = m >- (fn a => return (f a))
fun lift2 f m1 m2 =
  m1 >- (fn x => m2 >- (fn y => return (f x y)))

fun fromOpt optm errv s0 =
  case optm s0 of
      NONE => Error errv
    | SOME (s, r) => Some (s, r)

fun toOpt errm s0 =
  case errm s0 of
      Error _ => NONE
    | Some res => SOME res

fun addState s m s0 =
  case m (s0,s) of
      Error e => Error e
    | Some((s0',s'), result) => Some(s0',(s',result))

fun foldlM f a list =
  case list of
      [] => return a
    | h::t => f (h,a) >- (fn a' => foldlM f a' t)

fun with_flagM (r,v) (m : ('a,'b,'c)t) : ('a,'b,'c)t = fn (s:'a) =>
  Portable.with_flag (r,v) m s



end
