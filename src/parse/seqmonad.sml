structure seqmonad :> seqmonad = struct
type ('a,'b) seqmonad = 'a -> ('a * 'b) seq.seq
fun fail env = seq.empty
fun return x env = seq.result (env, x)
fun ok env = seq.result (env, ())

infix >- ++ >> >-> +++
fun (m1 >- f) env =
    seq.delay (fn () => let val res0 = m1 env
                        in
                          seq.flatten (seq.map (fn (e, v) => f v e) res0)
                        end)
fun (m1 >> m2) = (m1 >- (fn _ => m2))
fun (m1 ++ m2) env =
  seq.append (seq.delay (fn () => m1 env)) (seq.delay (fn () => m2 env))
fun (m1 >-> m2) = m1 >- (fn x => m2 >> return x)

fun (m1 +++ m2) env =
    seq.delay (fn () => let val batch1 = m1 env
                        in
                          case (seq.cases batch1) of
                            NONE => m2 env
                          | SOME _ => batch1
                        end)

fun pair1 pm (a, b) = seq.map (fn (a',res) => ((a',b), res)) (pm a)
fun pair2 pm (a, b) = seq.map (fn (b',res) => ((a,b'), res)) (pm b)

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

fun tryall_seq f s = let
  open seq
in
  case (cases s) of
    NONE => fail
  | SOME (x, xs) => f x ++ tryall_seq f xs
end

local
  fun repeatn' 0 f = ok
    | repeatn' n f = f >> repeatn' (n - 1) f
in
  fun repeatn n f = if n < 0 then fail else repeatn' n f
end

fun repeat p env = ((p >> repeat p) ++ ok) env
end
