structure pegML =
struct

(* A concrete-continuation-passing implementation of PEG-parsing.

   "Concrete" because the continuations are not closures but rather
   data structures encoding all the possible continuation forms. Being
   concrete in this way makes it easier to encode the parser as a HOL
   function, though I expect this will still be non-trivial because
   the termination argument is difficult. In fact, my expectation is
   that I will try to encode this with HOL's WHILE. (The use of WHILE
   is what requires the implementation to be tail-recursive. The fact
   that there is an analogue of exception handling requires the use of
   two continuations.)
*)

fun I x = x

datatype ('tok,'value) pegsym =
  empty of 'value
| any of 'tok -> 'value
| tok of 'tok * 'value
| nt of string * ('value -> 'value)
| seq of ('tok,'value) pegsym * ('tok,'value)pegsym * ('value * 'value -> 'value)
| choice of ('tok,'value) pegsym * ('tok,'value)pegsym * ('value -> 'value)
| rpt of ('tok,'value) pegsym * ('value list -> 'value)
| not of ('tok,'value) pegsym * 'value

datatype ('tok,'value) kont =
         sym of ('tok,'value) pegsym * ('tok,'value) kont * ('tok,'value)kont
       | applyf of ('value option list -> 'value option list) * ('tok,'value)kont
       | returnTo of 'tok list * 'value option list * ('tok,'value)kont
       | poplist of ('value list -> 'value) * ('tok,'value)kont
       | listsym of ('tok,'value) pegsym * ('value list -> 'value) * ('tok,'value) kont
       | done
       | failed

fun binary2list f k =
    applyf ((fn vl => case vl of
                         SOME h1::SOME h2::t => SOME (f(h2, h1)) :: t
                       | _ => raise Fail "binary f - with short list"),
            k)

fun unary2list f k =
    applyf ((fn vl => case vl of
                          SOME h::t => SOME (f h) :: t
                        | _ => raise Fail "unary f with bad list"),
            k)

fun poplistval (f:'v list -> 'v) (l:'v option list) = let
  fun recurse acc l =
      case l of
          [] => raise Fail "poplistval failure"
        | SOME h::t => recurse (h::acc) t
        | NONE::t => (acc,t)
  val (values,rest) = recurse [] l
in
  SOME (f values) :: rest
end

fun eval G (e:(''i,'v)pegsym) input (results:'v option list) k fk =
    case e of
        empty v => apply G k input (SOME v::results)
      | any tf => (case input of
                       [] => apply G fk input results
                     | h::t => apply G k t (SOME (tf h)::results))
      | tok (t,v) => (case input of
                          [] => apply G fk input results
                        | x::xs => if x = t then apply G k xs (SOME v::results)
                                   else apply G fk input results)
      | seq(e1,e2,f) =>
        eval G e1 input results
             (sym(e2,binary2list f k,returnTo(input,results,fk)))
             fk
      | choice(e1,e2,f) => eval G e1
                                input results
                                (unary2list f k)
                                (returnTo(input,results,
                                          sym(e2,unary2list f k,fk)))
      | not(e,v) =>
          eval G e input results
               (returnTo(input,results,fk))
               (returnTo(input,SOME v::results,k))
      | rpt(e,f) =>
          eval G e input (NONE::results) (listsym(e,f,k)) (poplist(f,k))
      | nt(n,f) => eval G (G n) input results k fk
and apply G (k:(''i,'v)kont) input (results:'v option list) =
    case k of
        done => SOME (valOf (hd results), input)
      | failed => NONE
      | sym(e,k,f) => eval G e input results k f
      | applyf(f, k) => apply G k input (f results)
      | returnTo(i,r,k) => apply G k i r
      | listsym(e,f,k) =>
          eval G e input results (listsym(e,f,k)) (poplist(f, k))
      | poplist(f,k) => apply G k input (poplistval f results : 'v option list)

datatype PT = XN of int | Plus of PT * PT | Times of PT * PT
              | PTL of PT list

fun leftassoc f leftlist last =
    case leftlist of
        [] => last
      | h::t => f (List.foldl (fn (a,b) => f(b,a)) h t, last)

fun testG s =
    case s of
        "E" => seq(rpt (seq(nt("F", I), tok("+", XN 0), #1), PTL),
                   nt("F", I),
                   (fn (PTL tlist,t) => leftassoc Plus tlist t))
      | "F" => seq(rpt (seq(nt("T", I), tok("*", XN 0), #1), PTL),
                   nt("T", I),
                   (fn (PTL tlist,t) => leftassoc Times tlist t))
      | "T" => choice(seq(seq(tok("(", XN 0), nt("E", I), #2), tok(")", XN 0),
                          #1),
                      nt("N", I),
                      I)
      | "N" => choice(tok("1", XN 1), choice(tok("2", XN 2), tok ("3", XN 3),
                                             I),
                      I)

val mk = map str o explode

val results = [
  eval testG (nt("E",I)) (mk "1+2*3") [] done failed,
  eval testG (nt("E",I)) (mk "(1+2)*3") [] done failed,
  eval testG (nt("E",I)) (mk "(1+2)*(3*1)") [] done failed,
  eval testG (nt("E",I)) (mk "2*3*1") [] done failed,
  eval testG (nt("E",I)) (mk "2+3+1") [] done failed,
  eval testG (nt("E",I)) (mk "2+3+1+2+1") [] done failed,
  eval testG (nt("E",I)) (mk "(1+2)*(3+1)*(1+2+1)") [] done failed,
  eval testG (nt("E",I)) (mk "(1+2)*(3+1)*(1+2+1") [] done
       (sym(empty (XN 0), done, done))]
end (* struct *)
