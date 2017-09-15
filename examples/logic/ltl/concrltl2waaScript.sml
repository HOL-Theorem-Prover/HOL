open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory relationTheory pred_setTheory prim_recTheory pairTheory bagTheory

open alterATheory sptreeTheory ltlTheory generalHelpersTheory concrRepTheory ltl2waaTheory

val _ = new_theory "concrltl2waa"

val tempDNF_concr_def = Define`
    (tempDNF_concr (VAR a) = [[VAR a]])
  ∧ (tempDNF_concr (N_VAR a) = [[N_VAR a]])
  ∧ (tempDNF_concr (DISJ f1 f2) = (tempDNF_concr f1) ++ (tempDNF_concr f2))
  ∧ (tempDNF_concr (CONJ f1 f2) =
       let tDNF1 = tempDNF_concr f1 in
           let tDNF2 = tempDNF_concr f2 in
               FOLDR (\l _. MAP (($++) l) tDNF2) [] tDNF1)
  ∧ (tempDNF_concr (X f)= [[X f]])
  ∧ (tempDNF_concr (U f1 f2) = [[U f1 f2]])
  ∧ (tempDNF_concr (R f1 f2) = [[R f1 f2]])`;

val FOLDR_LEMM = store_thm
  ("FOLDR_LEMM",
  ``!m2 m1 p. MEM p (FOLDR (λq _. MAP ($++ q) m1) [] m2)
  ==> (?l1 l2. (MEM l1 m1 ∧ MEM l2 m2) ∧ (p = (l2 ++ l1)))``,
  Induct_on `m2` >> fs[]
  >> rpt strip_tac >> fs[MEM_MAP] >> rw[] >> simp[EQ_IMP_THM]
  >> rpt strip_tac >> metis_tac[]
  );

val FOLDR_LEMM2 = store_hm
  ("FOLDR_LEMM2",
   ``!m1 m2 l1 l2. MEM l1 m1 ∧ MEM l2 m2
  ==> MEM (l1 ++ l2) (FOLDR (λl _. MAP ($++ l) m1) [] m2)``,
   Induct_on `l1`
    >- Induct_on `m2`
       >> fs[] >> rpt strip_tac >> fs[MEM_MAP]
    >- (Induct_on `m2` >> fs[])


)


val TEMPDNF_CONCR_LEMM = store_thm
  ("TEMPDNF_CONCR_LEMM",
   ``!f. set (MAP set (tempDNF_concr f)) = tempDNF f``,
   Induct_on `f` >> simp[tempDNF_concr_def,tempDNF_def]
   >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
    >- (fs[MEM_MAP]
        >> `∃l1 l2. (MEM l1 (tempDNF_concr f') ∧ MEM l2 (tempDNF_concr f))
               ∧ (y = l2 ⧺ l1)` by (
             HO_MATCH_MP_TAC FOLDR_LEMM >> fs[]
         )
        >> `set l1 ∈ tempDNF f'` by (
             `set l1 ∈ set (MAP set (tempDNF_concr f'))` suffices_by fs[]
             >> simp[MEM_MAP] >> metis_tac[]
         )
        >> `set l2 ∈ tempDNF f` by (
             `set l2 ∈ set (MAP set (tempDNF_concr f))` suffices_by fs[]
             >> simp[MEM_MAP] >> metis_tac[]
         )
        >> qexists_tac `set l2` >> qexists_tac `set l1` >> fs[]
       )
    >- (fs[MEM_MAP]
        >> `?l1. (MEM l1 (tempDNF_concr f)) ∧ (set l1 = f'')` by (
             `?l1. (MEM (set l1) (MAP set (tempDNF_concr f))) ∧ (set l1 = f'')`
              suffices_by (fs[MEM_MAP] >> metis_tac[])
             >> fs[SET_EQ_SUBSET] >> fs[SUBSET_DEF,MEM_MAP] >> metis_tac[]
             )
        >> `?l2. (MEM l2 (tempDNF_concr f')) ∧ (set l2 = f''')` by (
             `?l2. (MEM (set l2) (MAP set (tempDNF_concr f'))) ∧ (set l2 = f''')`
               suffices_by (fs[MEM_MAP] >> metis_tac[])
             >> fs[SET_EQ_SUBSET] >> fs[SUBSET_DEF,MEM_MAP] >> metis_tac[]
         )
        >> qexists_tac `l2 ++ l1` >> fs[UNION_DEF]
        >> rpt strip_tac >> fs[]
          >- (simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> metis_tac[])
          >- ()

)


)


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

val tempSubfCl_def = Define`
  tempSubfCl l = BIGUNION { tempSubForms f | MEM f l }`;


val NoNodeProcessedTwice_def = Define`
  NoNodeProcessedTwice g (a,ns) (a2,ns2) =
    ((g DIFF (LIST_TO_SET (autoStates a))
                  ⊂ g DIFF (LIST_TO_SET (autoStates a2)))
         \/ ((g DIFF (LIST_TO_SET (autoStates a))
              = g DIFF (LIST_TO_SET (autoStates a2)))
              ∧ (LENGTH ns) < (LENGTH ns2)))`;

val NNPT_WF = store_thm
 ("NNPT_WF",
  ``!g. FINITE g ==> WF (NoNodeProcessedTwice g)``,
   rpt strip_tac
   >> `WF (λs t. s ⊂ t
         ∧ s ⊆ g ∧ t ⊆ g)` by metis_tac[PSUBSET_WF]
   >> `WF ($<)` by metis_tac[WF_LESS]
   >> `WF (λ (x:β list) (y:β list).
            LENGTH x < LENGTH y)` by (
       `inv_image ($<) LENGTH
              = (λ(x:β list) (y:β list).
                  LENGTH x < LENGTH y)` by simp[inv_image_def]
       >> `WF (inv_image ($<) (LENGTH:(β list -> num)))` suffices_by fs[]
       >> metis_tac[WF_inv_image]
   )
   >> qabbrev_tac `P = (λs t. s ⊂ t ∧ s ⊆ g ∧ t ⊆ g)`
   >> qabbrev_tac `Q = (λ(x:β list) (y:β list). LENGTH x < LENGTH y)`
   >> qabbrev_tac `f = λ a. g DIFF (LIST_TO_SET (autoStates a))`
   >> `inv_image P f = λ a a2.
                        (g DIFF (LIST_TO_SET (autoStates a))
                         ⊂ g DIFF (LIST_TO_SET (autoStates a2)))` by (
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
        `j = λ(a,(l:β list)). (g DIFF (LIST_TO_SET (autoStates a)),l)`
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

val list_to_bag_def = Define`
  (list_to_bag [] = K 0)
  ∧ (list_to_bag (x::xs) = (list_to_bag xs) ⊎ {|x|})`;

val LST_TO_BAG_FINITE = store_thm
  ("LST_TO_BAG_FINITE",
  ``!l. FINITE_BAG (list_to_bag l)``,
  simp[FINITE_BAG] >> Induct_on `l`
   >- (fs[list_to_bag_def,EMPTY_BAG])
   >- (rpt strip_tac >> simp[list_to_bag_def]
       >> `P (list_to_bag l)` by metis_tac[]
       >> `P (BAG_INSERT h (list_to_bag l))` by metis_tac[]
       >> `P (EL_BAG h ⊎ (list_to_bag l))` by metis_tac[BAG_INSERT_UNION]
       >> fs[EL_BAG] >> metis_tac[COMM_BAG_UNION]
      )
  );

val LST_TO_BAG_APPEND_UNION = store_thm
  ("LST_TO_BAG_APPEND_UNION",
   ``!l k. list_to_bag (l ++ k) = list_to_bag l ⊎ list_to_bag k``,
   gen_tac >> Induct_on `l`
     >- (simp[list_to_bag_def] >> fs[EMPTY_BAG])
     >- (simp[list_to_bag_def] >> rpt strip_tac
         >> metis_tac[COMM_BAG_UNION,ASSOC_BAG_UNION])
  );

val IN_LST_TO_BAG = store_thm
 ("IN_LST_TO_BAG",
  ``!x l. (x ⋲ list_to_bag l) = (x ∈ set l)``,
  gen_tac >> Induct_on `l`
   >- (simp[list_to_bag_def] >> metis_tac[NOT_IN_EMPTY_BAG,EMPTY_BAG])
   >- (rpt strip_tac >> simp[list_to_bag_def] >> metis_tac[])
 );


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
 (expandAuto_step aut [] = SOME aut)
 ∧ (expandAuto_step (concrAA g init aP) (f::fs)  =
     let a1 = addFrmlToAut (concrAA g init aP) f
     in let trans = trans_concr aP f
     in let allSucs = FOLDR (\e pr. e.sucs ++ pr) [] trans
     in let a2 = FOLDR (\p g. addFrmlToAut g p) a1 allSucs
     in let a3 =
            FOLDR
                (\e a_opt. monad_bind a_opt (addEdgeToAut f e))
                (SOME a2) trans
     in let restNodes = FILTER (\s. ~(inAuto (concrAA g init aP) s)) allSucs
     in case a3 of
         | NONE => NONE
         | SOME aut => expandAuto_step aut (restNodes++fs))`;
  (WF_REL_TAC `inv_image
               (mlt1 (\f1 f2. f1 ∈ tempSubForms f2 ∧ ~(f1 = f2)))
               (list_to_bag o SND)`
   >- (metis_tac[STRICT_TSF_WF,WF_mlt1])
   >- (simp[mlt1_def,list_to_bag_def] >> rpt strip_tac
       >> fs[LST_TO_BAG_FINITE] >> rpt strip_tac
       >> qexists_tac `f`
       >> qabbrev_tac
           `newNodes = FILTER (λs. ¬inAuto (concrAA g init aP) s)
                   (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr aP f))`
       >> qexists_tac `list_to_bag newNodes`
       >> qexists_tac `list_to_bag fs` >> fs[LST_TO_BAG_APPEND_UNION]
       >> rpt strip_tac >> `f1 ∈ set newNodes` by metis_tac[IN_LST_TO_BAG]
       >> qunabbrev_tac `newNodes` >> fs[MEM_FILTER]
       >> fs[trans_concr_def]
)


(* ) *)


(*   (WF_REL_TAC `inv_image *)
(*                ((measure (CARD o tempSubfCl)) *)
(*                     LEX ((λ(t,l) (t1,l2). *)
(*                           ((CARD o tempSubfCl) t = (CARD o tempSubfCl) t1) *)
(*                           ∧ (LENGTH t1 < LENGTH t) *)
(*                           ∧ (LENGTH t1 <= (CARD o tempSubfCl) t)) *)
(*                     LEX (measure LENGTH)))) *)
(*                (λ(a,ls). ((autoStates a) ++ ls,(autoStates a) ++ ls,ls))` *)
(*    >> rpt strip_tac >> qabbrev_tac `a0 = concrAA g init aP` *)
(*    >> qabbrev_tac `a1 = addFrmlToAut a0 f` *)
(*    >> qabbrev_tac ` *)
(*         restnodes = FILTER (λs. ¬inAuto a0 s) *)
(*                            (FOLDR (λe pr. e.sucs ++ pr) [] (trans_concr aP f)) *)
(*                            ++ fs` *)
(*    >> Cases_on `LENGTH ((autoStates aut) ++ restnodes) < *)
(*                     LENGTH ((autoStates a0) ++ (f::fs))` >> fs[] *)
(*    >> `autoStates aut ++ restnodes = autoStates a0 ++ [f] ++ fs` by ( *)
(*         POP_ASSUM mp_tac >> simp[LENGTH] *)

(* ) *)

(*    >> rw[] *)

(* ) *)













(*   (WF_REL_TAC `λ(a,ls) (a2,ls2). *)
(*                (tempSubfCl ((autoStates a) ++ ls) *)
(*                 = tempSubfCl ((autoStates a2) ++ ls2)) *)
(*           ∧ NoNodeProcessedTwice *)
(*                (tempSubfCl ((autoStates a) ++ls)) *)
(*                (a,ls) *)
(*                (a2,ls2)` *)
(*     >- (qabbrev_tac *)
(*          `b:(α concrAA # (α ltl_frml) list *)
(*              -> (α ltl_frml -> bool)) *)
(*                     = λ(a,l). tempSubfCl ((autoStates a) ++ l)` *)
(*         >> qabbrev_tac *)
(*             `P = NoNodeProcessedTwice:((α ltl_frml -> bool) *)
(*                                        -> α concrAA # (α ltl_frml) list *)
(*                                        -> α concrAA # (α ltl_frml) list *)
(*                                        -> bool)` *)
(*         >> `!(a l:(α ltl_frml) list) . FINITE (b (a,l))` by ( *)
(*              rpt strip_tac >> qunabbrev_tac `b` *)
(*              >> rw[tempSubfCl_def] *)
(*               >-( `FINITE (IMAGE tempSubForms *)
(*                                {f | MEM f (autoStates a) ∨ MEM f l })` *)
(*                      suffices_by simp[IMAGE_DEF] *)
(*                >> `FINITE {f | MEM f (autoStates a) ∨ MEM f l}` suffices_by *)
(*                     metis_tac[IMAGE_FINITE] *)
(*                >> `{f | MEM f (autoStates a) ∨ MEM f l} *)
(*                      = LIST_TO_SET (autoStates a) ∪ (LIST_TO_SET l)` by ( *)
(*                    simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac *)
(*                     ) *)
(*                >> `(FINITE (set (autoStates a))) ∧ (FINITE (set l))` *)
(*                     suffices_by  metis_tac[FINITE_UNION] *)
(*                >> rpt strip_tac >> metis_tac[FINITE_LIST_TO_SET]) *)
(*               >- metis_tac[TSF_FINITE] *)
(*               >- metis_tac[TSF_FINITE] *)
(*          ) *)
(*         >> `∀g. FINITE g ⇒ WF (P g)` by metis_tac[NNPT_WF] *)
(*         >> imp_res_tac WF_LEMM *)
(*         >> first_x_assum (qspec_then `b` mp_tac) >> simp[] >> rpt strip_tac *)
(*         >> `∀k. FINITE (b k)` by (rpt strip_tac >> Cases_on `k` >> fs[]) *)
(*         >> fs[LAMBDA_PROD] >> qunabbrev_tac `P` >> qunabbrev_tac `b` *)
(*         >> fs[] *)
(*        ) *)
(*     >- (rpt strip_tac >> fs[] *)
(*      >- (simp[tempSubfCl_def,BIGUNION,SET_EQ_SUBSET] >> rpt strip_tac *)
(*       >- (fs[inAuto_def,SUBSET_DEF] >> rpt strip_tac *)
(*        >- (qexists_tac `s` >> fs[] >> rename[`MEM f_new _`] *)
(*            >> qexists_tac `f_new` >> fs[] *)
(*            >> `MEM f_new (autoStates (concrAA g init aP))` suffices_by fs[] *)
(*            >> `set (autoStates (concrAA g init aP)) *)
(*                 ⊆ set (autoStates (FOLDR (λp g. addFrmlToAut g p) *)
(*                    (addFrmlToAut (concrAA g init aP) f) *)
(*                    (FOLDR (λe pr. e.sucs ++ pr) [] (trans_concr aP f))))` by ( *)
(*               `set (autoStates (concrAA g init aP)) *)
(*                 ⊆ set (autoStates (addFrmlToAut (concrAA g init aP) f)) *)
(*                        ∧ wfg (addFrmlToAut (concrAA g init aP) f).graph` by ( *)
(*                   `(concrAA g init aP).graph = g` by fs[] *)
(*                   >> metis_tac[ADDFRML_LEMM]) *)
(*               >> metis_tac[ADDFRML_FOLDR_LEMM,SUBSET_TRANS] *)
(*             ) *)
(*            >> `set *)
(*                 (autoStates *)
(*                      (FOLDR (λp g. addFrmlToAut g p) *)
(*                         (addFrmlToAut (concrAA g init aP) f) *)
(*                         (FOLDR (λe pr. e.sucs ++ pr) [] (trans_concr aP f)))) *)
(*               = set (autoStates aut)` by ( *)
(*                 Induct_on `trans_concr aP f` >> rpt strip_tac >> fs[] *)
(*                 >- (`trans_concr aP f = []` by simp[] >> fs[]) *)
(*                 >- (`trans_concr aP f = h::v` by simp[] >> fs[] >> rw[] *)
(*                     >> Cases_on ` *)
(*                          FOLDR *)
(*                         (λe a_opt. *)
(*                          case a_opt of *)
(*                              NONE => NONE *)
(*                            | SOME a => addEdgeToAut f e a) *)
(*                         (SOME *)
(*                          (FOLDR (λp g. addFrmlToAut g p) *)
(*                                 (addFrmlToAut (concrAA g init aP) f) *)
(*                                 (h.sucs ++ FOLDR (λe pr. e.sucs ++ pr) [] v) *)
(*                         )) v` >> fs[] *)
                    
(* ) *)




