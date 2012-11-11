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
  empty | any | tok of 'a tok | nt of 'b inf |
  seq of pegsym => pegsym |
  choice of pegsym => pegsym |
  rpt of pegsym |
  not of pegsym
`

val _ = Hol_datatype`
  peg = <| start : 'b inf ; rules : 'b inf |-> ('a,'b) pegsym |>
`

val (peg_eval_rules, peg_eval_ind, peg_eval_cases) = Hol_reln`
  (∀s. peg_eval G (empty, s) (SOME s)) ∧
  (∀n r s.
       n ∈ FDOM G.rules ∧ peg_eval G (G.rules ' n, s) (SOME r) ⇒
       peg_eval G (nt n, s) (SOME r)) ∧
  (∀h t. peg_eval G (any, h::t) (SOME t)) ∧
  peg_eval G (any, []) NONE ∧
  (∀h t. peg_eval G (tok h, h::t) (SOME t)) ∧
  (∀h. peg_eval G (tok h, []) NONE) ∧
  (∀h1 h2 t. h1 ≠ h2 ⇒ peg_eval G (tok h1, h2::t) NONE) ∧
  (∀e s. peg_eval G (e, s) NONE ⇒ peg_eval G (not e, s) (SOME s)) ∧
  (∀e s s'. peg_eval G (e, s) (SOME s') ⇒ peg_eval G (not e, s) NONE)  ∧
  (∀e1 e2 s. peg_eval G (e1, s) NONE ⇒ peg_eval G (seq e1 e2, s) NONE)  ∧
  (∀e1 e2 s s' r.
     peg_eval G (e1, s) (SOME s') ∧ peg_eval G (e2, s') r ⇒
     peg_eval G (seq e1 e2, s) r) ∧
  (∀e1 e2 s r.
     peg_eval G (e1, s) NONE ∧ peg_eval G (e2, s) r ⇒
     peg_eval G (choice e1 e2, s) r) ∧
  (∀e1 e2 s s'.
     peg_eval G (e1, s) (SOME s') ⇒ peg_eval G (choice e1 e2, s) (SOME s')) ∧
  (∀e s s1 s2.
     peg_eval G (e, s) (SOME s1) ∧ peg_eval G (rpt e, s) (SOME s2) ⇒
     peg_eval G (rpt e, s) (SOME s2)) ∧
  (∀e s. peg_eval G (e, s) NONE ⇒ peg_eval G (rpt e, s) (SOME s))
`;



val _ = export_theory()
