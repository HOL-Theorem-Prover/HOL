open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory relationTheory pred_setTheory prim_recTheory pairTheory

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

val props_concr_def = Define`
    (props_concr (VAR a) = [a])
  ∧ (props_concr (N_VAR a) = [a])
  ∧ (props_concr (DISJ f1 f2) = props_concr f1 ++ props_concr f2)
  ∧ (props_concr (CONJ f1 f2) = props_concr f1 ++ props_concr f2)
  ∧ (props_concr (X f) = props_concr f)
  ∧ (props_concr (U f1 f2) = props_concr f1 ++ props_concr f2)
  ∧ (props_concr (R f1 f2) = props_concr f1 ++ props_concr f2)`;

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
   (* (expandAuto φ = *)
   (*    let initForms = tempDNF_concr φ *)
   (*    in let a0 = concrAA empty [] (props_concr φ) *)
   (*    in let a1 = FOLDL (\a s. addFrmlToAut a s) a0 (FLAT initForms) *)
   (*    in let init_concr = *)
   (*             MAP *)
   (*                 (λ l. *)
   (*                    MAP (\s. THE (findNode (λ(_,l). l.frml = s) a1.graph)) l) *)
   (*                 initForms *)
   (*    in let a_init = a1 with <| init := init_concr |> *)
   (*    in expandAuto_step (FLAT initForms) a_init) *)
 (expandAuto_step [] aut = aut)
 ∧ (expandAuto_step (f::fs) (concrAA g init aP) =
     let a1 = addFrmlToAut (concrAA g init aP) f
     in let trans = trans_concr aP f
     in let allSucs = FOLDL (\pr e. e.sucs ++ pr) [] trans
     in let a2 = FOLDL (\g p. addFrmlToAut g p) a1 allSucs
     in let a3 = FOLDL (\a e. addEdgeToAut f e a) a2 trans
     in let restNodes = FILTER (\s. ~ (inAuto (concrAA g init aP) s)) allSucs
     in expandAuto_step (restNodes++fs) a3)`;
  (qexists_tac `λ(ls,a) (ls2,a2).
          NoNodeProcessedTwice (HD ls) (a,ls) (a2,ls2)`
   >> rpt strip_tac
    >- (`!g. WF (NoNodeProcessedTwice g)` suffices_by (
           qabbrev_tac `f = 
)

[NNPT_WF])
 )

;

val NoNodeProcessedTwice_def = Define`
  NoNodeProcessedTwice g (a,ns) (a2,ns2) =
    ((tempSubForms g DIFF {x | inAuto a x }
                  ⊂ tempSubForms g DIFF {x | inAuto a2 x })
         \/ ((tempSubForms g DIFF {x | inAuto a x }
              = tempSubForms g DIFF {x | inAuto a2 x })
              ∧ ((list_size (\x. 1) ns)
                  < (list_size (\x. 1) ns2))))`;

val NNPT_WF = store_thm
 ("NNPT_WF",
  ``!g. WF (NoNodeProcessedTwice g)``,
   rpt strip_tac
   >> `WF (λ(s:α ltl_frml -> bool) t. s ⊂ t
         ∧ s ⊆ tempSubForms g
         ∧ t ⊆ tempSubForms g)` by (
       `FINITE (tempSubForms g)` by metis_tac[TSF_FINITE]
       >> metis_tac[PSUBSET_WF]
   )
   >> `WF ($<)` by metis_tac[WF_LESS]
   >> `WF (λ(x:num list) y.
            list_size (\n. n) x < list_size (\n. n) y)` by (
       qabbrev_tac `f = \x:num list. list_size (\n. n) x`
       >> `inv_image ($<) f =
            (λx:num list y.
              list_size (λn. n) x < list_size (λn. n) y)` by (
           simp[inv_image_def]
       )
       >> `WF (inv_image ($<) f)` suffices_by fs[]
       >> metis_tac[WF_inv_image]
   )
   >> qabbrev_tac `P = (λs t. s ⊂ t ∧ s ⊆ tempSubForms g ∧ t ⊆ tempSubForms g)`
   >> qabbrev_tac
         `Q = (λ x y.
                list_size (λn. n) x < list_size (λn. n) y)`
   >> qabbrev_tac `f = λ a. tempSubForms g DIFF {x | inAuto a x }`
   >> `inv_image P f = λ a a2.
                        (tempSubForms g DIFF {x | inAuto a x }
                         ⊂ tempSubForms g DIFF {x | inAuto a2 x })` by (
      qunabbrev_tac `P`
      >> fs[inv_image_def]
      >> `(\x y. f x ⊂ f y) = (λa a2. f a ⊂ f a2)`
         suffices_by (
          fs[] >> qunabbrev_tac `f` >> simp[inv_image_def]
      )
      >> metis_tac[]
   )
   >> `WF (inv_image P f)` by metis_tac[WF_inv_image]
   >> `WF (P LEX Q)` by metis_tac[WF_LEX]
   >> qabbrev_tac
        `j = λ(a,l:num list). (tempSubForms g DIFF {x | inAuto a x},l)`
   >> `WF (inv_image (P LEX Q) j)` by metis_tac[WF_inv_image]
   >> `!x y. (NoNodeProcessedTwice g) x y ==> (inv_image (P LEX Q) j) x y` by (
       fs[inv_image_def,LEX_DEF] >> rpt strip_tac
         >> Cases_on `x` >> Cases_on `y` >> fs[NoNodeProcessedTwice_def]
         >> qunabbrev_tac `f` >> qunabbrev_tac `P` >> qunabbrev_tac `Q`
         >> simp[] >> simp[EQ_IMP_THM] >> rpt strip_tac
         >> (qunabbrev_tac `j` >> simp[])
   )
   >> metis_tac[WF_SUBSET]
 );





(* val concrLtl2Waa_def = Define` *)





