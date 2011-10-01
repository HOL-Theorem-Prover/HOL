structure smpp :> smpp =
struct

type ('a,'b) t = ('a * HOLPP.ppstream) -> ('b * ('a * HOLPP.ppstream)) option

fun lift f (a,pps) = (f pps; SOME ((),(a,pps)))
fun lift1 f x (a,pps) = (f pps x; SOME ((),(a,pps)))

(* value restriction forces eta-expansion; ugh *)
fun add_string s = lift1 HOLPP.add_string s
fun add_newline x = lift HOLPP.add_newline x
fun add_break x = lift1 HOLPP.add_break x
fun flush x = lift HOLPP.flush_ppstream x
fun nothing (a,pps) = SOME ((),(a,pps))
fun fail apps = NONE

fun op>>(p1, p2) (a,pps) =
  case p1 (a,pps) of
    SOME (_, (a',pps)) => p2 (a',pps)
  | NONE => NONE

fun op>- (p1, fp2) (a,pps) =
    case p1 (a,pps) of
      SOME (b, (a',_)) => fp2 b (a',pps)
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

fun block0 begin finish bs i p (a,pps) = let
  val _ = begin pps bs i
in
  p (a,pps) before
  finish pps
end

fun block x = block0 HOLPP.begin_block HOLPP.end_block x

fun style0 begin finish styles p (a, pps) = let
  val _ = begin pps styles
in
  p (a,pps) before
  finish pps
end

fun fupdate f (a,pps) = SOME (a, (f a, pps))

fun liftpp ppf (a,pps) = (SOME (ppf pps, (a,pps)))

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

fun from_backend (b:PPBackEnd.t) = let
  val {add_string,add_xstring,add_newline,add_break,
       begin_block,end_block,begin_style,end_style,...} = b
in
  {add_string  = lift1 add_string,
   add_xstring = lift1 add_xstring,
   add_newline = lift add_newline,
   add_break = lift1 add_break,
   flush = flush,
   ublock = block0 begin_block end_block,
   ustyle = style0 begin_style end_style}
end

fun backend_block (b:PPBackEnd.t) = block0 (#begin_block b) (#end_block b)
fun backend_style (b:PPBackEnd.t) = style0 (#begin_style b) (#end_style b)



end (* struct *)
