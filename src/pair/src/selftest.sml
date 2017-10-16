open HolKernel Parse boolTheory boolLib pairTheory

open testutils

val _ = set_trace "Unicode" 0

val die = fn () => die "FAILED!\n"
fun sdie s = testutils.die ("FAILED!\n  "^s^"\n")

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
  val _ = OK()
in
  ()
end handle e => die()

(* parsing of case expressions with conditionals as arms *)
val _ = tprint "Parsing case expressions with conditional arms"
val t1 = ``case p:'a#'b of (x,y) => if y = a then x else f x y``
val t2 = ``pair_CASE (p:'a # 'b) (\x y. if y = a then x else f x y)``
val _ = if aconv t1 t2 then OK() else die()

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

val _ = print "*** Overloading case constant (pairs)\n"
val _ = overload_on ("foo", ``\p. case p of (x,y) => x /\ y``)
val _ = tpp "foo z"
val _ = set_trace "types" 1
val _ = trace ("types", 1) tpp  "case (p :'a # 'b) of (x,y) => x"

val _ = print "*** Overloading case constant (booleans)\n"
val _ = overload_on ("bar", ``\b. if b then T else F``)
val _ = tpp "bar T"
val _ = trace ("types", 1) tpp "if (b :bool) then (x :'a) else (y :'a)"

(* pairLib conversions etc *)
val _ = List.app convtest [
  ("PairRules.PBETA_CONV(1)", PairRules.PBETA_CONV,
   “(\ (a:'a,b:'b). f (a,b) (c:'c) : 'd) x”, “(f:'a # 'b -> 'c -> 'd) x c”),
  ("PairRules.PETA_CONV(1)", PairRules.PETA_CONV,
   “(\ (a:'a,b:'b). f (a,b) : 'c)”, “f : 'a # 'b -> 'c”)
]

local open pairLib in
val _ = print "*** new_specification with existential definition\n"
val th = metisLib.METIS_PROVE[]``?x y z. x ==> z /\ z ==> y``;
val _ = tprint "Testing 0 constants"
val nothing_def = new_specification("nothing_def",[],th);
val _ = OK()
val _ = tprint "Testing 1 constant"
val a_def = new_specification("a_def",["a"],th);
val _ = OK()
val _ = tprint "Testing 2 constants"
val pq_def = new_specification("pq_def",["p","q"],th);
val _ = OK()
val _ = tprint "Testing 3 constants"
val rst_def = new_specification("rst_def",["r","s","t"],th);
val _ = OK()
end

(* split_pair_case_tac *)
open pairLib
val _ = app (ignore o hide) ["aa", "bb", "xx", "pp", "qq"]
val _ = tprint "split_pair_case_tac (case in goal)"
val g = ([] : term list, ``case xx of (aa,bb) => aa /\ bb``)
val (sgs, vfn) = split_pair_case_tac g handle HOL_ERR _ => die ()
val _ = case sgs of
            [([a], g')] => if aconv (#2 g) g' andalso
                              aconv a ``xx = (aa:bool,bb:bool)``
                           then OK()
                           else die ()
          | _ => die ()

val _ = tprint "split_pair_case_tac (case in assumptions)"
val a = ``case xx of (aa,bb) => aa /\ bb``
val g = ``pp /\ qq``
val (sgs, vfn) = split_pair_case_tac ([a], ``pp /\ qq``)
                 handle HOL_ERR _ => die()
val _ = case sgs of
            [([a1, a2], g')] => if aconv g' g andalso
                                   aconv a1 ``xx = (aa:bool, bb:bool)`` andalso
                                   aconv a2 a
                                then OK()
                                else die()
          | _ => die()


val _ = Process.exit Process.success
