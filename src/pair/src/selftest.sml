open HolKernel Parse boolTheory boolLib pairTheory

val _ = set_trace "Unicode" 0

fun tprint s = print (StringCvt.padRight #" " 65 (s ^ " ... "))
fun die () = (print "FAILED!\n"; Process.exit Process.failure)
fun sdie s = (print ("FAILED!\n  "^s^"\n"); Process.exit Process.failure)

fun tpp s = let
  val t = Parse.Term [QUOTE s]
  val _ = tprint ("Testing printing of `"^s^"`")
  val res = term_to_string t
in
  if res = s then print "OK\n"
  else die ()
end


val _ = app tpp ["\\(x,y). x /\\ y",
                 "\\(x,y,z). x /\\ y /\\ z",
                 "\\((x,y),z). x /\\ y /\\ z",
                 "(\\(x,y,z). x /\\ y /\\ z) p",
                 "case x of (y,z) => y /\\ z"]

(* check LET_INTRO *)

val _ = let
  val _ = tprint "Testing pairTools.LET_INTRO"
  val _ = pairTools.LET_INTRO (ASSUME ``((x,y) = (zw)) ==> (ARB x y):bool``)
  val _ = pairTools.LET_INTRO (ASSUME ``((x,y) = (z,w)) ==> (ARB x y):bool``)
  val _ = print "OK\n"
in
  ()
end handle e => die()

val _ = print "**** More Inductive Definition tests ****\n"
open IndDefLib
fun checkhyps th = if null (hyp th) then ()
                   else sdie "FAILED - Hyps in theorem!"

(* emulate the example in examples/monosetScript.sml *)
val _ = print "*** Testing monoset example\n"
val _ = new_type ("t", 0)
val _ = new_type ("list", 1)
val _ = new_type ("num", 0)
val _ = new_constant ("v", ``:num -> t``)
val _ = new_constant ("app", ``:t list -> t``)
val _ = new_constant ("EVERY", ``:('a -> bool) -> 'a list -> bool``)
val _ = new_constant ("MEM", ``:'a -> 'a list -> bool``)
val _ = new_constant ("ZIP", ``:('a list # 'b list) -> ('a # 'b) list``)

val MONO_EVERY = mk_thm([], ``(!x:'a. P x ==> Q x) ==>
                              (EVERY P l ==> EVERY Q l)``)
val _ = add_mono_thm MONO_EVERY

val (red_rules, red_ind, red_cases) = Hol_reln `
  (!n. red f (v n) (v (f n))) /\
  (!t0s ts. EVERY (\ (t0,t). red f t0 t) (ZIP (t0s, ts)) ==>
            red f (app t0s) (app ts))
`;
val _ = checkhyps red_rules

(* emulate Peter's example *)
val _ = print "*** Testing Peter's example\n"
val _ = new_constant ("nil", ``:'a list``)
val _ = new_constant ("SUC", ``:num -> num``)
val _ = new_constant ("cons", ``:'a -> 'a list -> 'a list``)
val _ = new_constant ("HD", ``:'a list -> 'a``)
val _ = new_constant ("TL", ``:'a list -> 'a list``)
val (ph_rules, ph_ind, ph_cases) = Hol_reln`
  (WF_CX nil) /\
  (!s ty cx. WF_CX cx /\ WF_TYPE cx ty ==> WF_CX (cons (s,ty) cx)) /\

  (!n cx. WF_CX cx ==> WF_TYPE cx (v n)) /\
  (!ts cx s. WF_CX cx /\ MEM (s, HD ts) cx /\ EVERY (\t. WF_TYPE cx t) ts /\
             red SUC (HD ts) (HD (TL ts)) ==>
             WF_TYPE cx (app ts))
`
val _ = checkhyps ph_rules

(* UNCURRY with more than two arguments *)
val _ = new_constant ("Z", ``:num``)
val _ = new_constant ("ONE", ``:num``)
val _ = new_constant ("TWO", ``:num``)
val _ = print "*** Testing UNCURRY with more than two arguments\n"
val (u3_rules, u3_ind, u3_cases) = Hol_reln`
  u3 (Z,ONE,TWO) /\
  (!x y z. (\ ((x,y), z). u3 (x,y,z)) ((y,x),z) ==> u3 (x,y,z))
`
val _ = checkhyps u3_rules

(* single rule *)
val _ = print "*** Testing strong principle for singleton rule\n"
val _ = new_constant ("+", ``:num -> num -> num``)
val _ = set_fixity "+" (Infixl 500)
val (single_rules, single_ind, single_cases) = Hol_reln`
  (!x y. RTC single x y \/ (x = y + TWO) ==> single x y)
`;
val _ = checkhyps single_rules

val _ = Process.exit Process.success
