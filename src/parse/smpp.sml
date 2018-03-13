structure smpp :> smpp =
struct

type ('a,'b) t = ('a,'b) term_pp_types.smppt

open HOLPP

fun add_string s (st,ps) = SOME ((), (st, PrettyString s :: ps))
fun add_break x (st,ps) = SOME ((), (st, PrettyBreak x :: ps))
(* value restriction forces eta-expansion; ugh *)
fun add_newline x = add_break(10000, 0) x
fun nothing stps = SOME ((),st)
fun fail aps = NONE

fun op>>(p1, p2) stps =
  case p1 st of
      SOME (_, stps1) => p2 stps1
    | NONE => NONE

fun op>- (p1, fp2) (a,ps) =
  case p1 (a,ps) of
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
        SOME(res, (a1, PrettyBlock(i, bs2b bs, [], List.rev ps1) :: ps))

fun fupdate f (a,pps) = SOME (a, (f a, pps))

infix >>
fun pr_list fpp brk list =
    case list of
      [] => nothing
    | [b] => fpp b
    | b::bs => fpp b >> brk >> pr_list fpp brk bs

fun mappr_list fpp brk list =
    case list of
      [] => return []
    | [b] => fpp b >- (fn bres => return [bres])
    | b::bs => let
        fun afterb bres = brk >> mappr_list fpp brk bs >- return o Lib.cons bres
      in
        fpp b >- afterb
      end

end (* struct *)
