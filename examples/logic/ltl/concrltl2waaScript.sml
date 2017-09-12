open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory relationTheory

open alterATheory sptreeTheory ltlTheory generalHelpersTheory concrRepTheory

val _ = new_theory "concrltl2waa"

val tempDNF_concr_def = Define`
    (tempDNF_concr (VAR a) = [[VAR a]])
  ∧ (tempDNF_concr (N_VAR a) = [[N_VAR a]])
  ∧ (tempDNF_concr (DISJ f1 f2) = (tempDNF_concr f1) ++ (tempDNF_concr f2))
  ∧ (tempDNF_concr (CONJ f1 f2) =
       let tDNF1 = tempDNF_concr f1 in
           let tDNF2 = tempDNF_concr f2 in
               FOLDL (\_ l. MAP (($++) l) tDNF2) [] tDNF1)
  ∧ (tempDNF_concr (X f)= [[X f]])
  ∧ (tempDNF_concr (U f1 f2) = [[U f1 f2]])
  ∧ (tempDNF_concr (R f1 f2) = [[R f1 f2]])`;

(* val subListsOf_def = Define` *)
(*     (subListsOf [] = [[]]) *)
(*   ∧ (subListsOf (x::xs) = *)
(*      (MAP (\l. x::l) (subListsOf xs)) ++ (subListsOf xs))`; *)


(* val char_concr_def = Define` *)
(*   char_concr aP p = *)
(*     FILTER (\l. MEM p l) (subListsOf aP)`; *)

(* val char_concr_neg_def = Define` *)
(*   char_concr_neg aP p = *)
(*    FILTER (\l. ~MEM p l) (subListsOf aP)`; *)

val d_conj_concr_def = Define`
  d_conj_concr d1 d2 =
      FOLDL
      (\_ e1. MAP (λe2. <| pos := e1.pos++e2.pos ;
                           neg := e1.neg++e2.neg ;
                           sucs := e1.sucs++e2.sucs |> ) d2)
      []
      d1`;

val trans_concr_def = Define`
    (trans_concr aP (VAR a) = [<| pos := [a]; neg := []; sucs := [] |> ])
  ∧ (trans_concr aP (N_VAR a) = [<| pos := []; neg := [a]; sucs := [] |> ])
  ∧ (trans_concr aP (CONJ f1 f2) =
     d_conj_concr (trans_concr aP f1) (trans_concr aP f2))
  ∧ (trans_concr aP (DISJ f1 f2) =
       (trans_concr aP f1) ++ (trans_concr aP f2))
  ∧ (trans_concr aP (X f) =
       MAP (\e. <| pos := [] ; neg := [] ; sucs := e |> ) (tempDNF_concr f))
  ∧ (trans_concr aP (U f1 f2) =
       (trans_concr aP f2) ++
         (d_conj_concr (trans_concr aP f1)
                       [<| pos := [] ; neg := [] ; sucs := [U f1 f2] |>]))
  ∧ (trans_concr aP (R f1 f2) =
     d_conj_concr (trans_concr aP f2)
       (<| pos := [] ; neg := [] ; sucs := [U f1 f2] |> ::
                                           (trans_concr aP f1)))`;

val expandAuto_def = Define`
   (expandAuto [] aut = aut)
 ∧ (expandAuto (f::fs) (concrAA g init aP) =
     let a1 = addFrmlToAut (concrAA g init aP) f
     in let trans = trans_concr aP f
     in let allSucs = FOLDL (\pr e. e.sucs ++ pr) [] trans
     in let a2 = FOLDL (\g p. addFrmlToAut g p) a1 allSucs
     in let a3 = FOLDL (\a e. addEdgeToAut f e a) a2 trans
     in let restNodes = FILTER (\s. ~ (inAuto (concrAA g init aP) s)) allSucs
     in expandAuto (restNodes++fs) a3)`;

val NoNodeProcessedTwice_def = Define`
  NoNodeProcessedTwice g (ns,a) (ns2,a2) =
    (({x | inAuto a2 x } ⊂ {x | inAuto a x })
        ∧ ({x | inAuto a x } ⊆ tempSubForms g))`;

val NNPT_WF = store_thm
 ("NNPT_WF",
  ``!g. WF (NoNodeProcessedTwice g)``,
  fs[WF_DEF] >> rpt strip_tac
  >> CCONTR_TAC >> fs[NoNodeProcessedTwice_def]


)






(* val concrLtl2Waa_def = Define` *)





