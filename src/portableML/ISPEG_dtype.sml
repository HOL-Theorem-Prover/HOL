structure ISPEG_dtype =
struct

datatype locrel = lrEQ | lrGE | lrGT | lrOK


(* HOL locations and regions, mimicking what's in
     examples/formal-languages/context-free/
*)
datatype hlocn = UNKNOWNpt | EOFpt | POSN of (int * int)
datatype hlocs = Locs of (hlocn * hlocn)

fun locnle l1 l2 =
    case (l1,l2) of
        (UNKNOWNpt, _) => true
      | (_, EOFpt) => true
      | (_, UNKNOWNpt) => false
      | (EOFpt, _) => false
      | (POSN(r1,c1), POSN (r2,c2)) =>
        r1 < r2 orelse (r1 = r2 andalso c1 <= c2)
fun locsle (Locs (b1, _)) (Locs(b2, _)) = locnle b1 b2

val EOF = Locs(EOFpt,EOFpt)

(*
     'a  type of token being consumed, e.g., char
     'b  type of name of non-terminal, e.g., string
     'c  type of output value
     'e  type of error
*)
datatype ('a,'b,'c,'e) ispegsym =
         empty of 'c
       | any  of ('a * hlocs -> 'c)
       | tok of (('a -> bool) * ('a * hlocs -> 'c) * locrel)
       | nt of 'b * ('c -> 'c) * locrel
       | seq of (('a,'b,'c,'e) ispegsym * ('a,'b,'c,'e) ispegsym *
                 ('c  -> 'c -> 'c))
       | choice of ('a,'b,'c,'e) ispegsym * ('a,'b,'c,'e) ispegsym *
                   ('c -> 'c) * ('c -> 'c)
       | rpt of (('a,'b,'c,'e) ispegsym * ('c list -> 'c))
       | not of (('a,'b,'c,'e) ispegsym * 'c)
       | error of 'e


type ('a,'b,'c,'e) ispeg = {
  start : ('a,'b,'c,'e) ispegsym,
  anyEOF : 'e ,
  tokFALSE : 'e,
  tokEOF : 'e,
  notFAIL : 'e,
  iFAIL : 'e,
  rules : 'b -> ('a,'b,'c,'e) ispegsym
}

(* a locpred encodes a predicate that is true of an indentation;
 *)
datatype locpred = lpIval of int * int | lpBOT | lpxGE of int

datatype ('a,'b,'c,'e) kont =
  ksym of (('a,'b,'c,'e) ispegsym) * ('a,'b,'c,'e) kont * ('a,'b,'c,'e) kont
| appf1 of ('c -> 'c) * ('a,'b,'c,'e) kont
| appf2 of ('c -> 'c -> 'c) * ('a,'b,'c,'e) kont
| lpcomp of locpred * locrel * ('a,'b,'c,'e) kont * ('a,'b,'c,'e) kont
| genIFAIL of ('a,'b,'c,'e) kont
| setlps of locpred * ('a,'b,'c,'e) kont
| dropErr of ('a,'b,'c,'e) kont
| addErr of hlocs * 'e * ('a,'b,'c,'e) kont
| cmpErrs of ('a,'b,'c,'e) kont
| cmpEO of ((hlocs * 'e) option) * ('a,'b,'c,'e) kont
| returnTo of (('a* hlocs) list) * ('c option list) * ('a,'b,'c,'e) kont
| restoreEO of ((hlocs * 'e) option) * ('a,'b,'c,'e) kont
| poplist of ('c list -> 'c) * ('a,'b,'c,'e) kont
| listsym of (('a,'b,'c,'e) ispegsym) *
             ('c list -> 'c) *
             ('a,'b,'c,'e) kont
| done
| failed

datatype ('toks,'val,'err) ispegresult =
         Success of ('toks * 'val * (hlocs * 'err) option * locpred)
       | Failure of (hlocs * 'err)



end
