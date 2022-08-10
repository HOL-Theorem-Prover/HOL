structure smpp :> smpp =
struct

infix >- >>

type ('a,'b) t =
     'a * HOLPP.pretty list -> ('b * ('a * HOLPP.pretty list)) option

open HOLPP
val fint = FixedInt.fromInt

fun consP p (st,ps) = SOME ((), (st, p::ps))
fun add_string s = consP (HOLPP.PrettyStringWithWidth(s, fint (UTF8.size s)))
fun add_break b = consP (HOLPP.add_break b)
fun add_stringsz (s,i) = consP (HOLPP.PrettyStringWithWidth (s, fint i))
fun add_newline x = consP HOLPP.NL x
fun nothing stps = SOME ((),stps)
fun fail aps = NONE

fun op>>(p1, p2) stps =
  case p1 stps of
      SOME (_, stps1) => p2 stps1
    | NONE => NONE

fun op>- (p1, fp2) aps =
  case p1 aps of
      SOME (b, stps1) => fp2 b stps1
    | NONE => NONE

fun op|| (p1,p2) apps =
    case p1 apps of
      NONE => p2 apps
    | x => x

fun op||| (p1,fps) apps =
    case p1 apps of
      NONE => fps()apps
    | x => x

fun return x y = SOME (x,y)

fun bs2b bs = bs = HOLPP.CONSISTENT

fun block bs i p (a,ps) =
  case p (a,[]) of
      NONE => NONE
    | SOME(res, (a1,ps1)) =>
        SOME(res, (a1, PrettyBlock(fint i, bs2b bs, [], List.rev ps1) :: ps))

fun fupdate f (a,pps) = SOME (a, (f a, pps))

infix >>

fun mapp f [] = nothing
  | mapp f (e::es) = f e >> mapp f es

fun mmap f [] = return []
  | mmap f (e::es) = f e >- (fn h => mmap f es >- (fn t => return (h::t)))

fun pr_list fpp brk list =
    case list of
      [] => nothing
    | [b] => fpp b
    | b::bs => fpp b >> brk >> pr_list fpp brk bs

fun cons x xs = x::xs

fun mappr_list fpp brk list =
    case list of
      [] => return []
    | [b] => fpp b >- (fn bres => return [bres])
    | b::bs => let
        fun afterb bres = brk >> mappr_list fpp brk bs >- return o cons bres
      in
        fpp b >- afterb
      end

fun lift pf x =
  let val pty = pf x in (fn (st,pps) => SOME ((), (st, pty :: pps))) end
fun lower m st0 =
  let
    fun mapthis (a, (st,ps)) = (HOLPP.block CONSISTENT 0 (List.rev ps), a, st)
  in
    Option.map mapthis (m (st0, []))
  end

end (* struct *)
