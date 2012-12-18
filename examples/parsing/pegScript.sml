open HolKernel Parse boolLib bossLib
open boolSimps

open grammarTheory finite_mapTheory

val _ = new_theory "peg"

(* Based on
     Koprowski and Binzstok, "TRX: A Formally Verified Parser Interpreter".
     LMCS vol 7, no. 2. 2011.
     DOI: 10.2168/LMCS-7(2:18)2011
*)

val _ = Hol_datatype `pegsym =
    empty of 'c
  | any of ('a tok -> 'e -> 'c)
  | tok of 'a tok => ('e -> 'c)
  | nt of 'b inf => ('c -> 'c)
  | seq of pegsym => pegsym => ('c -> 'c -> 'c)
  | choice of pegsym => pegsym => ('c + 'c -> 'c)
  | rpt of pegsym => ('c list -> 'c)
  | not of pegsym => 'c
`

val _ = Hol_datatype`
  peg = <| start : 'b inf ; rules : 'b inf |-> ('a,'b,'c,'e) pegsym ;
           cf : 'e -> 'a tok |>
`

val (peg_eval_rules, peg_eval_ind, peg_eval_cases) = Hol_reln`
  (∀s c. peg_eval G (empty c, s) (SOME(s, c))) ∧
  (∀n r s f.
       n ∈ FDOM G.rules ∧ peg_eval G (G.rules ' n, s) (SOME(r,c)) ⇒
       peg_eval G (nt n f, s) (SOME(r, f c))) ∧
  (∀h t f. peg_eval G (any f, h::t) (SOME (t, f (G.cf h) h))) ∧
  (∀f. peg_eval G (any f, []) NONE) ∧
  (∀h e t f. G.cf e = h ⇒ peg_eval G (tok h f, e::t) (SOME(t, f e))) ∧
  (∀h e t f. G.cf e ≠ h ⇒ peg_eval G (tok h f, e::t) NONE) ∧
  (∀h f. peg_eval G (tok h f, []) NONE) ∧
  (∀e s c. peg_eval G (e, s) NONE ⇒ peg_eval G (not e c, s) (SOME(s,c))) ∧
  (∀e s s' c. peg_eval G (e, s) (SOME s') ⇒ peg_eval G (not e c, s) NONE)  ∧
  (∀e1 e2 s f. peg_eval G (e1, s) NONE ⇒ peg_eval G (seq e1 e2 f, s) NONE)  ∧
  (∀e1 e2 s0 s1 c1 f.
     peg_eval G (e1, s0) (SOME (s1, c1)) ∧ peg_eval G (e2, s1) NONE ⇒
     peg_eval G (seq e1 e2 f, s0) NONE) ∧
  (∀e1 e2 s0 s1 s2 c1 c2 f.
     peg_eval G (e1, s0) (SOME(s1, c1)) ∧
     peg_eval G (e2, s1) (SOME(s2, c2)) ⇒
     peg_eval G (seq e1 e2 f, s0) (SOME(s2, f c1 c2))) ∧
  (∀e1 e2 s f.
     peg_eval G (e1, s) NONE ∧ peg_eval G (e2, s) NONE ⇒
     peg_eval G (choice e1 e2 f, s) NONE) ∧
  (∀e1 e2 s s' f c.
     peg_eval G (e1, s) (SOME(s',c)) ⇒
     peg_eval G (choice e1 e2 f, s) (SOME(s', f (INL c)))) ∧
  (∀e1 e2 s s' f c.
     peg_eval G (e1, s) NONE ∧ peg_eval G (e2, s) (SOME(s',c)) ⇒
     peg_eval G (choice e1 e2 f, s) (SOME(s',f (INR c))))  ∧
  (∀e f s s1 list.
     peg_eval_list G (e, s) (SOME(s1,list)) ⇒
     peg_eval G (rpt e f, s) (SOME(s1, f list))) ∧
  (∀e s. peg_eval G (e, s) NONE ⇒ peg_eval_list G (e, s) (SOME(s,[]))) ∧
  (∀e s0 s1 s2 c cs.
     peg_eval G (e, s0) (SOME(s1,c)) ∧
     peg_eval_list G (e, s1) (SOME(s2,cs)) ⇒
     peg_eval_list G (e, s0) (SOME(s2,c::cs)))
`;

val _ = Hol_datatype`ftok = Plus | Times | Number | LParen | RParen`

val _ = Hol_datatype`etok = EPlus | ETimes | ENumber of num | ELParen | ERParen`

val categorise_def = Define`
  categorise EPlus = Plus ∧
  categorise ETimes = Times ∧
  categorise (ENumber n) = Number ∧
  categorise ELParen = LParen ∧
  categorise ERParen = RParen
`;

local open stringTheory in end

val _ = Hol_datatype `expr = XN of num | XPlus of expr => expr | XTimes of expr => expr`

val _ = overload_on("mkTok", ``mk_finite_image``)


val nrule =
  ``tok (mkTok Number) (\e. case e of ENumber n => XN n)``
val paren_rule =
  ``seq (tok (mkTok LParen) (K (XN 0)))
        (seq (nt (INL "expr") I) (tok (mkTok RParen) (K (XN 0))) (\a b. a))
        (\a b. b)``


val rules = ``FEMPTY |+ ("term", choice ^nrule ^paren_rule (\s. case s of INL e => e | INR e => e))``





val _ = export_theory()
