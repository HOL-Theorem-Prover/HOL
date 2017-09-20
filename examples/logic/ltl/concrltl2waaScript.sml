open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory relationTheory pred_setTheory prim_recTheory pairTheory bagTheory set_relationTheory

open alterATheory sptreeTheory ltlTheory generalHelpersTheory concrRepTheory ltl2waaTheory waaSimplTheory optionTheory

val _ = new_theory "concrltl2waa"

val tempDNF_concr_def = Define`
    (tempDNF_concr (VAR a) = [[VAR a]])
  ∧ (tempDNF_concr (N_VAR a) = [[N_VAR a]])
  ∧ (tempDNF_concr (DISJ f1 f2) = (tempDNF_concr f1) ++ (tempDNF_concr f2))
  ∧ (tempDNF_concr (CONJ f1 f2) =
       let tDNF1 = tempDNF_concr f1 in
           let tDNF2 = tempDNF_concr f2 in
               FOLDR (\l sofar. (MAP (($++) l) tDNF2) ++ sofar) [] tDNF1)
  ∧ (tempDNF_concr (X f)= [[X f]])
  ∧ (tempDNF_concr (U f1 f2) = [[U f1 f2]])
  ∧ (tempDNF_concr (R f1 f2) = [[R f1 f2]])`;

val FOLDR_LEMM1 = store_thm
  ("FOLDR_LEMM1",
  ``!m2 m1 p. MEM p (FOLDR (λq l. (MAP ($++ q) m1) ++l) [] m2)
  ==> (?l1 l2. (MEM l1 m1 ∧ MEM l2 m2) ∧ (p = (l2 ++ l1)))``,
  Induct_on `m2` >> fs[]
  >> rpt strip_tac >> fs[MEM_MAP] >> rw[] >> simp[EQ_IMP_THM]
  >> rpt strip_tac >> metis_tac[]
  );

val FOLDR_LEMM2 = store_thm
  ("FOLDR_LEMM2",
   ``!m2 m1 p. MEM p (FOLDR (λq l. (MAP ($++ q) m1) ++l) [] m2)
  = (?l1 l2. (MEM l1 m1 ∧ MEM l2 m2) ∧ (p = (l2 ++ l1)))``,
   Induct_on `m2` >> fs[]
   >> rpt strip_tac >> fs[MEM_MAP] >> rw[] >> simp[EQ_IMP_THM]
   >> rpt strip_tac >> metis_tac[]
  );

val FOLDR_LEMM3 = store_thm
  ("FOLDR_LEMM3",
   ``!f m2 m1 a b. MEM (f a b)
                     (FOLDR (λa1 l. (MAP (\b1. f a1 b1) m2) ++l) [] m1)
     = (?a' b'. MEM a' m1 ∧ MEM b' m2 ∧ (f a b = f a' b'))``,
   Induct_on `m1` >> fs[]
   >> rpt strip_tac >> fs[MEM_MAP] >> rw[] >> simp[EQ_IMP_THM]
   >> rpt strip_tac >> metis_tac[]
  );

val FOLDR_LEMM4 = store_thm
  ("FOLDR_LEMM4",
   ``!f m2 m1 x. MEM x
                     (FOLDR (λa1 l. (MAP (\b1. f a1 b1) m2) ++l) [] m1)
     = (?a' b'. MEM a' m1 ∧ MEM b' m2 ∧ (x = f a' b'))``,
   Induct_on `m1` >> fs[]
   >> rpt strip_tac >> fs[MEM_MAP] >> rw[] >> simp[EQ_IMP_THM]
   >> rpt strip_tac >> metis_tac[]
  );

val FOLDR_LEMM5 = store_thm
  ("FOLDR_LEMM5",
   ``!l1 l2 l3 l4 f1 f2 s.
     (FOLDR (λa sofar. f1 a ∩ sofar)
            (FOLDR (λa sofar. f2 a ∩ sofar) s (l1++l2)) (l3++l4))
     = ((FOLDR (λa sofar. f1 a ∩ sofar)
             (FOLDR (λa sofar. f2 a ∩ sofar) s l1) l3)
       ∩ ((FOLDR (λa sofar. f1 a ∩ sofar)
             (FOLDR (λa sofar. f2 a ∩ sofar) s l2) l4)))``,
   Induct_on `l3` >> simp[SET_EQ_SUBSET,SUBSET_DEF]
   >> rpt strip_tac >> fs[]
   >> Induct_on `l4`
   >> Induct_on `l1` >> fs[] >> Induct_on `l2` >> fs[]
  );


val TEMPDNF_CONCR_LEMM = store_thm
  ("TEMPDNF_CONCR_LEMM",
   ``!f. set (MAP set (tempDNF_concr f)) = tempDNF f``,
   Induct_on `f` >> simp[tempDNF_concr_def,tempDNF_def]
   >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
    >- (fs[MEM_MAP]
        >> `∃l1 l2. (MEM l1 (tempDNF_concr f') ∧ MEM l2 (tempDNF_concr f))
               ∧ (y = l2 ⧺ l1)` by (
             HO_MATCH_MP_TAC FOLDR_LEMM1 >> fs[]
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
        >> qexists_tac `l1 ++ l2` >> fs[UNION_DEF]
        >> rpt strip_tac >> fs[]
          >- (simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> metis_tac[])
          >- (metis_tac[FOLDR_LEMM2])
       )
  );

val props_concr_def = Define`
    (props_concr (VAR a) = [a])
  ∧ (props_concr (N_VAR a) = [a])
  ∧ (props_concr (DISJ f1 f2) = props_concr f1 ++ props_concr f2)
  ∧ (props_concr (CONJ f1 f2) = props_concr f1 ++ props_concr f2)
  ∧ (props_concr (X f) = props_concr f)
  ∧ (props_concr (U f1 f2) = props_concr f1 ++ props_concr f2)
  ∧ (props_concr (R f1 f2) = props_concr f1 ++ props_concr f2)`;

val d_conj_concr_def = Define`
  d_conj_concr d1 d2 =
      FOLDR
      (\e1 sofar. (MAP (λe2. <| pos := e1.pos++e2.pos ;
                               neg := e1.neg++e2.neg ;
                               sucs := e1.sucs++e2.sucs |> ) d2) ++ sofar)
      []
      d1`;

val trans_concr_def = Define`
    (trans_concr (VAR a) = [<| pos := [a]; neg := []; sucs := [] |> ])
  ∧ (trans_concr (N_VAR a) = [<| pos := []; neg := [a]; sucs := [] |> ])
  ∧ (trans_concr (CONJ f1 f2) =
       d_conj_concr (trans_concr f1) (trans_concr f2))
  ∧ (trans_concr (DISJ f1 f2) =
       (trans_concr f1) ++ (trans_concr f2))
  ∧ (trans_concr (X f) =
       MAP (\e. <| pos := [] ; neg := [] ; sucs := e |> ) (tempDNF_concr f))
  ∧ (trans_concr (U f1 f2) =
       (trans_concr f2) ++
         (d_conj_concr (trans_concr f1)
                       [<| pos := [] ; neg := [] ; sucs := [U f1 f2] |>]))
  ∧ (trans_concr (R f1 f2) =
     d_conj_concr (trans_concr f2)
       (<| pos := [] ; neg := [] ; sucs := [R f1 f2] |> ::
                                           (trans_concr f1)))`;

val TRANS_CONCR_LEMM = store_thm
  ("TRANS_CONCR_LEMM",
   ``!aP f. set (MAP (concr2AbstractEdge aP) (trans_concr f))
                       = trans (POW aP) f``,
   gen_tac >> Induct_on `f`
   >> simp[trans_concr_def,trans_def,char_def] >> rpt strip_tac
     >- (`<|pos := [a]; neg := []; sucs := []|> = concrEdge [a] [] []`
             by rw[concrEdge_component_equality]
         >> rw[] >> simp[concr2AbstractEdge_def]
         >> simp[props_def,char_def,subForms_def] >> rw[INTER_DEF]
         >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> metis_tac[]
        )
     >- (`<|pos := []; neg := [a]; sucs := []|> = concrEdge [] [a] []`
             by rw[concrEdge_component_equality]
         >> rw[] >> simp[concr2AbstractEdge_def]
         >> simp[props_def,char_neg_def,subForms_def] >> rw[INTER_DEF]
         >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
         >> fs[char_def]
        )
     >- (simp[d_conj_def,d_conj_concr_def,SET_EQ_SUBSET,SUBSET_DEF]
         >> rpt strip_tac
         >> qabbrev_tac `g = (λe1 e2.
                           <|pos := e1.pos ⧺ e2.pos;
                             neg := e1.neg ⧺ e2.neg;
                             sucs := e1.sucs ⧺ e2.sucs|>)`
         >> fs[MEM_MAP]
          >- (`MEM y (FOLDR
                             (λe1 sofar. (MAP (λe2. g e1 e2) (trans_concr f'))
                                  ++ sofar)
                             [] (trans_concr f))` by fs[]
              >> `∃a' b'. MEM a' (trans_concr f) ∧ MEM b' (trans_concr f')
                       ∧ y = g a' b'` by metis_tac[FOLDR_LEMM4]
              >> `concr2AbstractEdge aP a' ∈ trans (POW aP) f` by (
                   `MEM (concr2AbstractEdge aP a')
                     (MAP (concr2AbstractEdge aP) (trans_concr f))`
                       by (fs[MEM_MAP] >> metis_tac[])
                   >> metis_tac[]
               )
              >> `concr2AbstractEdge aP b' ∈ trans (POW aP) f'` by (
                   `MEM (concr2AbstractEdge aP b')
                     (MAP (concr2AbstractEdge aP) (trans_concr f'))`
                       by (fs[MEM_MAP] >> metis_tac[])
                   >> metis_tac[]
               )
              >> qunabbrev_tac `g` >> rw[]
              >> qexists_tac `FST (concr2AbstractEdge aP a')`
              >> qexists_tac `FST (concr2AbstractEdge aP b')`
              >> qexists_tac `SND (concr2AbstractEdge aP a')`
              >> qexists_tac `SND (concr2AbstractEdge aP b')` >> fs[]
              >> `<|pos := a'.pos ⧺ b'.pos; neg := a'.neg ⧺ b'.neg;
                    sucs := a'.sucs ⧺ b'.sucs|> =
                            concrEdge (a'.pos ++ b'.pos) (a'.neg ++ b'.neg)
                                      (a'.sucs ++ b'.sucs)`
                  by rw[concrEdge_component_equality]
              >> simp[concr2AbstractEdge_def] >> Cases_on `a'`
              >> Cases_on `b'` >> simp[concr2AbstractEdge_def]
              >> metis_tac[FOLDR_LEMM5]
             )
          >- (`MEM (a1,e1) (MAP (concr2AbstractEdge aP) (trans_concr f))`
                by fs[]
              >> `MEM (a2,e2) (MAP (concr2AbstractEdge aP) (trans_concr f'))`
                  by fs[]
              >> fs[MEM_MAP]
              >> qexists_tac `g y y'` >> rpt strip_tac
               >- (qunabbrev_tac `g`
                  >> `<|pos := y.pos ⧺ y'.pos; neg := y.neg ⧺ y'.neg;
                    sucs := y.sucs ⧺ y'.sucs|> =
                            concrEdge (y.pos ++ y'.pos) (y.neg ++ y'.neg)
                                      (y.sucs ++ y'.sucs)`
                    by rw[concrEdge_component_equality]
                  >> simp[concr2AbstractEdge_def] >> rw[]
                  >> Cases_on `y` >> Cases_on `y'` >> fs[concr2AbstractEdge_def]
                  >> metis_tac[FOLDR_LEMM5]
                  )
               >- (rw[FOLDR_LEMM3] >> metis_tac[])
             )
        )
     >- (simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[MEM_MAP]
          >- (`(set e) ∈ tempDNF f` by (
                       `set (MAP set (tempDNF_concr f)) = tempDNF f`
                         by fs[TEMPDNF_CONCR_LEMM]
                       >> `MEM (set e) (MAP set (tempDNF_concr f))`
                           suffices_by fs[]
                       >> simp[MEM_MAP] >> metis_tac[]
                    )
                  >> qexists_tac `set e`
                  >> `<|pos := []; neg := []; sucs := e|>
                      = concrEdge [] [] e` by rw[concrEdge_component_equality]
                  >> simp[concr2AbstractEdge_def]
                  )
          >- (`set (MAP set (tempDNF_concr f)) = tempDNF f`
                     by fs[TEMPDNF_CONCR_LEMM]
                   >> `MEM e (MAP set (tempDNF_concr f))` by fs[]
                   >> fs[MEM_MAP]
                   >> qexists_tac `concrEdge [] [] y`
                   >> simp[concr2AbstractEdge_def]
                   >> qexists_tac `y` >> fs[concrEdge_component_equality]
             )
        )
     >- (simp[d_conj_def,d_conj_concr_def,SET_EQ_SUBSET,SUBSET_DEF]
          >> rpt strip_tac >> fs[MEM_MAP]
          >> qabbrev_tac `g = (λe1 sofar. (<|pos := e1.pos;
                                      neg := e1.neg;
                                      sucs := e1.sucs ⧺ [U f f']|>)::sofar)`
           >- (Cases_on `concr2AbstractEdge aP y ∈ trans (POW aP) f'` >> fs[]
               >> `!ls. MEM y (FOLDR g [] ls)
                    ==> ?k. (MEM k ls) ∧
                        (y = <|pos := k.pos; neg := k.neg;
                              sucs := k.sucs ⧺ [U f f']|>)` by (
                    Induct_on `ls` >> fs[]
                    >> rpt strip_tac >> fs[] >> Cases_on `MEM y (FOLDR g [] ls)`
                     >- metis_tac[]
                     >- (qexists_tac `h` >> fs[] >> qunabbrev_tac `g` >> fs[])
                )
               >> first_x_assum (qspec_then `trans_concr f` mp_tac)
               >> simp[] >> rpt strip_tac
               >> `?p. (p ∈ trans (POW aP) f)
                        ∧ (concr2AbstractEdge aP k = p)` by (
                    `MEM (concr2AbstractEdge aP k)
                       (MAP (concr2AbstractEdge aP) (trans_concr f))`
                       by (fs[MEM_MAP] >> metis_tac[])
                    >> metis_tac[]
                )
               >> Cases_on `p` >> qexists_tac `q` >> qexists_tac `POW aP`
               >> qexists_tac `r` >> qexists_tac `{U f f'}` >> simp[]
               >> `<|pos := k.pos; neg := k.neg; sucs := k.sucs ⧺ [U f f']|>
                   = concrEdge k.pos k.neg (k.sucs ++ [U f f'])`
                   by rw[concrEdge_component_equality]
               >> simp[concr2AbstractEdge_def] >> Cases_on `k`
               >> fs[concr2AbstractEdge_def]
               >> metis_tac[TRANS_ALPH_LEMM,INTER_SUBSET_EQN]
              )
           >- (Cases_on `(a1 ∩ a2,e1 ∪ e2) ∈ trans (POW aP) f'` >> fs[]
               >> `MEM (a1,e1) (MAP (concr2AbstractEdge aP) (trans_concr f))`
                  by fs[]
               >> fs[MEM_MAP]
               >> qexists_tac `concrEdge y.pos y.neg (y.sucs ++ [U f f'])`
               >> qunabbrev_tac `g` >> Cases_on `y`
               >> fs[concr2AbstractEdge_def] >> rpt strip_tac
                >- (`a2 = (POW aP)`
                      by (simp[SET_EQ_SUBSET,SUBSET_DEF] >> metis_tac[])
                    >> rw[]
                    >> qabbrev_tac `c = λa sofar. char (POW aP) a ∩ sofar`
                    >> qabbrev_tac `c_n = λa sofar. char_neg (POW aP) a ∩ sofar`
                    >> rw[]
                    >> `!ls ls0.
                           (FOLDR c (FOLDR c_n (POW aP) ls0) ls ∩ (POW aP))
                               = (FOLDR c (FOLDR c_n (POW aP) ls0) ls)` by (
                          Induct_on `ls` >> fs[]
                           >- (Induct_on `ls0` >> fs[] >> rpt strip_tac
                              >> qunabbrev_tac `c_n` >> fs[]
                              >> `(FOLDR (λa sofar. char_neg (POW aP) a ∩ sofar)
                                   (POW aP) ls0 ∩ POW aP)
                                = (FOLDR (λa sofar. char_neg (POW aP) a ∩ sofar)
                                         (POW aP) ls0)` suffices_by (
                                 rpt strip_tac >> simp[SET_EQ_SUBSET,SUBSET_DEF]
                                 >> rpt strip_tac >> fs[char_neg_def])
                              >> metis_tac[])
                          >- (rpt strip_tac >> qunabbrev_tac `c` >> fs[]
                             >> `(FOLDR (λa sofar. char (POW aP) a ∩ sofar)
                                   (FOLDR c_n (POW aP) ls0) ls ∩ (POW aP))
                               = (FOLDR (λa sofar. char (POW aP) a ∩ sofar)
                                   (FOLDR c_n (POW aP) ls0) ls)` suffices_by (
                               rpt strip_tac >> simp[SET_EQ_SUBSET,SUBSET_DEF]
                               >> rpt strip_tac >> fs[char_def]
                          )
                             >> metis_tac[])
                     )
                    >> metis_tac[]
                   )
                >- (simp[SET_EQ_SUBSET,SUBSET_DEF] >> metis_tac[])
                >- (qabbrev_tac
                     `g = (λe1 sofar. (<|pos := e1.pos;
                                        neg := e1.neg;
                                        sucs := e1.sucs ⧺ [U f f']|>)::sofar)`
                    >> `!y ls k. (MEM k ls) ∧
                            (y = <|pos := k.pos; neg := k.neg;
                                   sucs := k.sucs ⧺ [U f f']|>)
                            ==> MEM y (FOLDR g [] ls)` by (
                         gen_tac >> Induct_on `ls` >> fs[] >> rpt strip_tac
                         >> fs[] >> Cases_on `MEM k ls
                                      ∧ y = <|pos := k.pos;
                                              neg := k.neg;
                                              sucs := k.sucs ⧺ [U f f']|>`
                         >> fs[] >> qunabbrev_tac `g` >> fs[]
                     )
                    >> (first_x_assum
                            (qspec_then `concrEdge l l0 (l1 ⧺ [U f f'])` mp_tac)
                        >> rpt strip_tac
                        >> first_x_assum (qspec_then `trans_concr f` mp_tac)
                        >> rpt strip_tac
                        >> first_x_assum (qspec_then `concrEdge l l0 l1` mp_tac)
                        >> rpt strip_tac >> POP_ASSUM mp_tac
                        >> simp[concrEdge_component_equality]
                        >> `(concrEdge l l0 (l1 ⧺ [U f f']))
                                 = <|pos := l;
                                     neg := l0;
                                     sucs := l1 ⧺ [U f f']|>`
                            by rw[concrEdge_component_equality]
                        >> metis_tac[]
                       )
                   )
              )
        )
     >- (simp[d_conj_def,d_conj_concr_def,SET_EQ_SUBSET,SUBSET_DEF]
         >> rpt strip_tac >> fs[MEM_MAP]
         >> qabbrev_tac `g1 = (λe1 e2.
                                   <|pos := e1.pos ⧺ e2.pos;
                                     neg := e1.neg ⧺ e2.neg;
                                     sucs := e1.sucs ⧺ e2.sucs|>)`
         >> qabbrev_tac `g2 = (λls2 e1 sofar.
                                   <|pos := e1.pos; neg := e1.neg;
                                     sucs := e1.sucs ⧺ [R f f']|> ::
                                     ((MAP (λe2. g1 e1 e2) ls2)
                                         ++ sofar))`
          >- (`MEM y (FOLDR (g2 (trans_concr f)) [] (trans_concr f'))` by (
              qunabbrev_tac `g1` >> qunabbrev_tac `g2` >> fs[]
          )
             >> `!ls1 ls2. (MEM y (FOLDR (g2 ls2) [] ls1)) ==>
               ?c1. (MEM c1 ls1)
                  ∧ ((y =  <|pos := c1.pos; neg := c1.neg;
                            sucs := c1.sucs ⧺ [R f f']|>)
                  \/ (?c2. (MEM c2 ls2)
                        ∧ (y = g1 c1 c2)))` by (
              Induct_on `ls1` >> rpt strip_tac >> fs[]
              >> qunabbrev_tac `g2` >> qunabbrev_tac `g1` >> fs[MEM_MAP]
              >> metis_tac[]
          )
             >> first_x_assum (qspec_then `trans_concr f'` mp_tac)
             >> rpt strip_tac
             >> first_x_assum (qspec_then `trans_concr f` mp_tac) >> simp[]
             >> rpt strip_tac
             >> `(concr2AbstractEdge aP) c1 ∈ trans (POW aP) f'` by (
                  `MEM (concr2AbstractEdge aP c1)
                   (MAP (concr2AbstractEdge aP) (trans_concr f'))`
                    by (simp[MEM_MAP] >> metis_tac[])
                  >> metis_tac[]
          )
              >- (Cases_on `concr2AbstractEdge aP c1`
                 >> qexists_tac `q` >> qexists_tac `POW aP`
                 >> qexists_tac `r` >> qexists_tac `{R f f'}`
                 >> rpt strip_tac >> fs[]
                 >> `<|pos := c1.pos;
                       neg := c1.neg;
                       sucs := c1.sucs ⧺ [R f f']|>
                     = concrEdge c1.pos c1.neg (c1.sucs ++ [R f f'])`
                    by rw[concrEdge_component_equality]
                 >> simp[concr2AbstractEdge_def] >> rpt strip_tac
                 >> Cases_on `c1` >> fs[concr2AbstractEdge_def]
                 >> metis_tac[TRANS_ALPH_LEMM,INTER_SUBSET_EQN])
              >- (`(concr2AbstractEdge aP) c2 ∈ trans (POW aP) f` by (
                    `MEM (concr2AbstractEdge aP c2)
                     (MAP (concr2AbstractEdge aP) (trans_concr f))`
                    by (simp[MEM_MAP] >> metis_tac[])
                    >> metis_tac[])
                   >> Cases_on `concr2AbstractEdge aP c1`
                   >> Cases_on `concr2AbstractEdge aP c2`
                   >> qexists_tac `q` >> qexists_tac `q'`
                   >> qexists_tac `r` >> qexists_tac `r'`
                   >> rpt strip_tac >> fs[]
                   >> qunabbrev_tac `g1` >> fs[]
                   >> `<|pos := c1.pos ⧺ c2.pos;
                         neg := c1.neg ⧺ c2.neg;
                         sucs := c1.sucs ⧺ c2.sucs|>
                      = concrEdge (c1.pos ++ c2.pos)
                                  (c1.neg ++ c2.neg) (c1.sucs ++ c2.sucs)`
                      by rw[concrEdge_component_equality]
                   >> simp[concr2AbstractEdge_def] >> rpt strip_tac
                   >> Cases_on `c1` >> Cases_on `c2`
                   >> fs[concr2AbstractEdge_def]
                   >> metis_tac[FOLDR_LEMM5]
                 )
             )
          >- (`MEM (a1,e1) (MAP (concr2AbstractEdge aP) (trans_concr f'))`
                 by fs[]
              >> `MEM (a2,e2) (MAP (concr2AbstractEdge aP) (trans_concr f))`
                 by fs[]
              >> fs[MEM_MAP] >> Cases_on `y` >> Cases_on `y'`
              >> qexists_tac `concrEdge (l++l') (l0++l0') (l1++l1')`
              >> rpt strip_tac >> fs[]
               >- (fs[concr2AbstractEdge_def] >> rpt strip_tac >> fs[]
                   >> metis_tac[FOLDR_LEMM5])
               >- (`!ls1 ls2 x y. MEM x ls1 ∧ MEM y ls2
                        ==> MEM (concrEdge (x.pos ++ y.pos)
                                           (x.neg ++ y.neg)
                                           (x.sucs ++ y.sucs))
                        (FOLDR (λe1 sofar. g2 ls2 e1 sofar) [] ls1)` by (
                          Induct_on `ls1` >> fs[] >> rpt strip_tac
                          >> qunabbrev_tac `g1` >> qunabbrev_tac `g2`
                          >> fs[MEM_MAP] >> disj2_tac >> disj1_tac
                          >> qexists_tac `y`
                          >> fs[concrEdge_component_equality])
                       >> first_x_assum (qspec_then `trans_concr f'` mp_tac)
                       >> rpt strip_tac
                       >> first_x_assum (qspec_then `trans_concr f` mp_tac)
                       >> rpt strip_tac
                       >> first_x_assum (qspec_then `concrEdge l l0 l1` mp_tac)
                       >> simp[] >> rpt strip_tac
                       >> first_x_assum
                             (qspec_then `concrEdge l' l0' l1'` mp_tac)
                       >> simp[] >> rpt strip_tac
                  )
             )
          >- (`MEM (a1,e1) (MAP (concr2AbstractEdge aP) (trans_concr f'))`
                 by fs[]
              >> fs[MEM_MAP] >> Cases_on `y`
              >> qexists_tac `concrEdge l l0 (l1 ++ [R f f'])`
              >> rpt strip_tac >> fs[]
               >- (fs[concr2AbstractEdge_def] >> rpt strip_tac >> fs[]
                    >- (`a1 ∩ a2 = a1` suffices_by rw[]
                       >> `a2 = POW aP` by simp[SET_EQ_SUBSET,SUBSET_DEF]
                       >> `a1 ∩ POW aP = a1` suffices_by rw[]
                       >> metis_tac[TRANS_ALPH_LEMM,INTER_SUBSET_EQN]
                       )
                    >- simp[SET_EQ_SUBSET,SUBSET_DEF,UNION_DEF]
                  )
               >- (`!ls1 ls2 x. MEM x ls1
                       ==> MEM (concrEdge x.pos x.neg (x.sucs ++ [R f f']))
                            (FOLDR (λe1 sofar. g2 ls2 e1 sofar) [] ls1)` by (
                     Induct_on `ls1` >> fs[] >> rpt strip_tac
                     >> qunabbrev_tac `g1` >> qunabbrev_tac `g2`
                     >> fs[MEM_MAP] >> disj1_tac
                     >> fs[concrEdge_component_equality]
                   )
                   >> first_x_assum (qspec_then `trans_concr f'` mp_tac)
                   >> rpt strip_tac
                   >> first_x_assum (qspec_then `trans_concr f` mp_tac)
                   >> rpt strip_tac
                   >> first_x_assum (qspec_then `concrEdge l l0 l1` mp_tac)
                   >> simp[]
                  )
             )
        )
  );

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

val expandAuto_def = tDefine "expandAuto"
 `(expandAuto aut [] = SOME aut)
 ∧ (expandAuto (concrAA g init aP) (f::fs)  =
     let a1 = addFrmlToAut (concrAA g init aP) f
     in let trans = trans_concr f
     in let allSucs = FOLDR (\e pr. e.sucs ++ pr) [] trans
     in let a2 = FOLDR (\p g. addFrmlToAut g p) a1 allSucs
     in let a3 =
            FOLDR
                (\e a_opt. monad_bind a_opt (addEdgeToAut f e))
                (SOME a2) trans
     in let restNodes = FILTER (\s. ~(inAuto a1 s)) allSucs
     in case a3 of
         | NONE => NONE
         | SOME aut => expandAuto aut (restNodes++fs))`
  (WF_REL_TAC `inv_image
               (mlt1 (\f1 f2. f1 ∈ tempSubForms f2 ∧ ~(f1 = f2)))
               (list_to_bag o SND)`
   >- metis_tac[STRICT_TSF_WF,WF_mlt1]
   >- (simp[mlt1_def,list_to_bag_def] >> rpt strip_tac
       >> fs[LST_TO_BAG_FINITE] >> rpt strip_tac
       >> qexists_tac `f`
       >> qabbrev_tac
           `newNodes = FILTER
                       (λs. ¬inAuto (addFrmlToAut (concrAA g init aP) f) s)
                        (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f))`
       >> qexists_tac `list_to_bag newNodes`
       >> qexists_tac `list_to_bag fs` >> fs[LST_TO_BAG_APPEND_UNION]
       >> rpt strip_tac >> `f1 ∈ set newNodes` by metis_tac[IN_LST_TO_BAG]
       >> qunabbrev_tac `newNodes` >> fs[MEM_FILTER]
       >> `!l. MEM f1 (FOLDR (λ e pr. e.sucs ++ pr) [] l)
                ==> ?e. (MEM e l) ∧ (MEM f1 e.sucs)` by (
            Induct_on `l` >> rpt strip_tac >> fs[] >> metis_tac[]
        )
       >> `?e. (MEM e (trans_concr f)) ∧ (MEM f1 e.sucs)` by fs[]
       >> `concr2AbstractEdge (set aP) e ∈ trans (POW (set aP)) f` by (
            `MEM (concr2AbstractEdge (set aP) e)
               (MAP (concr2AbstractEdge (set aP)) (trans_concr f))`
               by (fs[MEM_MAP] >> metis_tac[])
             >> metis_tac[TRANS_CONCR_LEMM]
        )
       >- (Cases_on `concr2AbstractEdge (set aP) e`
          >> `f1 ∈ r` by (Cases_on `e` >> fs[concr2AbstractEdge_def])
          >> metis_tac[TRANS_REACHES_SUBFORMS,TSF_def,IN_DEF])
       >- (rw[] >> metis_tac[ADDFRML_LEMM])
      )
  );

val EXP_AUTO_WFG_AND_SOME = store_thm
  ("EXP_AUTO_WFG_AND_SOME",
   ``!aut fs. wfg aut.graph
        ==> (?aut2. (expandAuto aut fs = SOME aut2)
              ∧ (wfg aut2.graph)
              ∧ (set (autoStates aut) ⊆ set (autoStates aut2)))``,
   HO_MATCH_MP_TAC (theorem "expandAuto_ind")
   >> rpt strip_tac >> fs[expandAuto_def]
   >> Q.HO_MATCH_ABBREV_TAC
       `?aut2. ((case A of
              | NONE => NONE
              | SOME aut => (E aut)) = SOME aut2)
          ∧ wfg aut2.graph
          ∧ A0 ⊆ (A2 aut2)`
   >> `wfg (addFrmlToAut (concrAA g init aP) f).graph` by (
       Cases_on `inAuto (concrAA g init aP) f`
       >> Cases_on `f` >> fs[addFrmlToAut_def]
   )
   >> `?aut. (A = SOME aut) ∧ wfg aut.graph
       ∧ A0 ⊆ A2 aut` by (
      qunabbrev_tac `A`
      >> `!ls fs. ?x.
         (FOLDR (λe a_opt. monad_bind a_opt (addEdgeToAut f e))
           (SOME
                (FOLDR (λp g. addFrmlToAut g p)
                       (addFrmlToAut (concrAA g init aP) f)
                       fs)) ls = SOME x)
         ∧ wfg x.graph ∧ inAuto x f
         ∧ A0 ⊆ A2 x` by (
       Induct_on `ls` >> fs[] >> rpt strip_tac
        >- metis_tac[ADDFRML_FOLDR_LEMM]
        >- (`set (autoStates (addFrmlToAut (concrAA g init aP) f))
              ⊆ set (autoStates
                         (FOLDR (λp g. addFrmlToAut g p)
                                (addFrmlToAut (concrAA g init aP) f) fs'))`
                by metis_tac[ADDFRML_FOLDR_LEMM,SUBSET_UNION]
             >> simp[inAuto_def]
             >> `MEM f (autoStates (addFrmlToAut (concrAA g init aP) f))`
                 suffices_by metis_tac[SUBSET_DEF]
             >> metis_tac[inAuto_def,ADDFRML_LEMM]
           )
        >- (qunabbrev_tac `A0` >> qunabbrev_tac `A2` >> fs[]
            >> `set (autoStates (concrAA g init aP))
                 ⊆ set (autoStates (addFrmlToAut (concrAA g init aP) f))`
               suffices_by (
                 rpt strip_tac
                 >> `set (autoStates (addFrmlToAut (concrAA g init aP) f))
                      ⊆ set
                      (autoStates
                           (FOLDR (λp g. addFrmlToAut g p)
                                  (addFrmlToAut (concrAA g init aP) f) fs'))`
                    by metis_tac[ADDFRML_FOLDR_LEMM,SUBSET_UNION]
                 >> metis_tac[SUBSET_TRANS])
            >> `(concrAA g init aP).graph = g`
                suffices_by metis_tac[ADDFRML_LEMM2]
            >> fs[]
           )
        >- (simp[] >> Q.HO_MATCH_ABBREV_TAC `?x1. (?x2. P x1 x2) ∧ Q x1`
            >> `?x2 x1. P x1 x2 ∧ Q x1` suffices_by metis_tac[]
            >> qunabbrev_tac `P` >> qunabbrev_tac `Q`
            >> first_x_assum (qspec_then `fs'` mp_tac) >> rpt strip_tac
            >> simp[]
            >> `∃a2. addEdgeToAut f h x = SOME a2 ∧ wfg a2.graph
                  ∧ x.graph.nodeInfo = a2.graph.nodeInfo`
                by metis_tac[ADDEDGE_LEMM2,IS_SOME_EXISTS]
            >> simp[]
            >> qunabbrev_tac `A2`
            >> fs[inAuto_def] >> Cases_on `a2` >> Cases_on `x`
            >> fs[autoStates_def]
           )
   )
   >> metis_tac[]
   )
   >> first_x_assum (qspec_then `aut` mp_tac) >> simp[]
   >> rpt strip_tac >> metis_tac[SUBSET_TRANS]
  );

val EXP_AUTO_REACHABLE = store_thm
  ("EXP_AUTO_REACHABLE",
   ``!f aut ls.
            (!a2.
              (!x. MEM x ls
                   ==> x ∈ reachRelFromSet (ltl2waa f) (set (autoStates aut)))
            ∧ (!x. MEM x (autoStates aut)
                   ==> x ∈ reachRelFromSet
                           (ltl2waa f) (BIGUNION (ltl2waa f).initial))
            ∧ (set (autoStates aut) ⊆ tempSubForms f)
            ∧ (expandAuto aut ls = SOME a2)
            ∧ (wfg aut.graph)
         ==> (!x. MEM x (autoStates a2)
                  ==> ((x ∈ reachRelFromSet (ltl2waa f)
                             (BIGUNION (ltl2waa f).initial))
                    ∧ (x ∈ tempSubForms f))))``,
   gen_tac
   >> HO_MATCH_MP_TAC (theorem "expandAuto_ind")
   >> strip_tac >> strip_tac >> strip_tac >> strip_tac
   >> strip_tac >> strip_tac
    >- (strip_tac
        >> `aut = a2` by fs[expandAuto_def]
        >> rw[] >> metis_tac[MEM,SUBSET_DEF]
       )
    >- (strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> fs[]
        >> qabbrev_tac `addedNodesAut =
            FOLDR (λp g. addFrmlToAut g p)
                   (addFrmlToAut (concrAA g init aP) f')
                   (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f'))`
        >> `set (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f'))
              ⊆ set (autoStates addedNodesAut)
              ∧ (wfg addedNodesAut.graph)
              ∧  set (autoStates (addFrmlToAut (concrAA g init aP) f'))
                   ⊆ set (autoStates addedNodesAut)
              ∧ inAuto addedNodesAut f'` by (
             fs[] >> qunabbrev_tac `addedNodesAut`
             >> `wfg (addFrmlToAut (concrAA g init aP) f').graph`
                  by (`wfg (concrAA g init aP).graph`
                         suffices_by metis_tac[ADDFRML_LEMM2]
                       >> fs[])
             >> rpt strip_tac
             >- metis_tac[ADDFRML_FOLDR_LEMM2]
             >- metis_tac[ADDFRML_FOLDR_LEMM]
             >- metis_tac[ADDFRML_FOLDR_LEMM,SUBSET_UNION]
             >- (`inAuto (addFrmlToAut (concrAA g init aP) f') f'`
                   by metis_tac[ADDFRML_LEMM]
                 >> `set (autoStates (addFrmlToAut (concrAA g init aP) f'))
                      ⊆ set (autoStates
                            (FOLDR (λp g. addFrmlToAut g p)
                               (addFrmlToAut (concrAA g init aP) f')
                               (FOLDR (λe pr. e.sucs ⧺ pr)
                                      [] (trans_concr f'))))`
                    by metis_tac[ADDFRML_FOLDR_LEMM,SUBSET_UNION]
                 >> metis_tac[inAuto_def,SUBSET_DEF,MEM]
                )
         )
        >> `!ls. ?aut.
              (FOLDR (λe a_opt. monad_bind a_opt (addEdgeToAut f' e))
              (SOME addedNodesAut) ls = SOME aut)
              ∧ (wfg aut.graph)
              ∧ (addedNodesAut.graph.nodeInfo = aut.graph.nodeInfo)` by (
             Induct_on `ls` >> fs[] >> rpt strip_tac
             >> HO_MATCH_MP_TAC ADDEDGE_LEMM2 >> Cases_on `aut`
             >> simp[inAuto_def,autoStates_def]
             >> `MEM f' (MAP ((λl. l.frml) ∘ SND)
                             (toAList (addedNodesAut.graph).nodeInfo))`
                suffices_by fs[]
             >> Cases_on `addedNodesAut` >> fs[inAuto_def,autoStates_def]
         )
        >> first_x_assum (qspec_then `trans_concr f'` mp_tac) >> strip_tac
        >> first_x_assum (qspec_then `aut` mp_tac) >> simp[] >> strip_tac
        >> first_x_assum (qspec_then `a2` mp_tac) >> simp[]
        >> Q.HO_MATCH_ABBREV_TAC `(A ==> B) ==> C`
        >> `B ==> C` by (
             qunabbrev_tac `B` >> qunabbrev_tac `C` >> metis_tac[]
         )
        >> `A` suffices_by fs[]
        >> qunabbrev_tac `A` >> rpt strip_tac
        >- (`inAuto aut f'` by (
              Cases_on `addedNodesAut` >> Cases_on `aut`
              >> fs[inAuto_def,autoStates_def])
            >> `reachRel (ltl2waa f) f' x'` suffices_by (
                  simp[reachRelFromSet_def] >> metis_tac[inAuto_def]
            )
            >> fs[MEM_FILTER]
            >> `!ls. MEM x' (FOLDR (λe pr. e.sucs ++ pr) [] ls)
                  ==> ?t. (MEM t ls) ∧ (MEM x' t.sucs)` by (
               Induct_on `ls` >> fs[] >> rpt strip_tac
               >> metis_tac[])
            >> first_x_assum (qspec_then `trans_concr f'` mp_tac) >> simp[]
            >> rpt strip_tac >> simp[reachRel_def]
            >> `oneStep (ltl2waa f) f' x'` suffices_by fs[]
            >> simp[oneStep_def,ltl2waa_def,ltl2waa_free_alph_def]
            >> `(concr2AbstractEdge (props f) t) ∈ trans (POW (props f)) f'` by (
                 `MEM (concr2AbstractEdge (props f) t)
                      (MAP (concr2AbstractEdge (props f)) (trans_concr f'))`
                     by (simp[MEM_MAP] >> metis_tac[])
                 >> fs[TRANS_CONCR_LEMM]
            )
            >> Cases_on `concr2AbstractEdge (props f) t`
            >> qexists_tac `q` >> qexists_tac `r` >> simp[]
            >> Cases_on `t` >> fs[concr2AbstractEdge_def]
            >> `f' ∈
                  reachRelFromSet (ltl2waa f)
                  (set (autoStates (concrAA g init aP)))` by metis_tac[]
            >> metis_tac[REACHREL_LEMM]
           )
        >- (`x' ∈
               reachRelFromSet (ltl2waa f)
               (set (autoStates (concrAA g init aP)))` by metis_tac[]
            >> fs[reachRelFromSet_def] >> qexists_tac `x''`
            >> simp[]
            >> `MEM x'' (autoStates addedNodesAut)` by (
               `wfg (concrAA g init aP).graph`
                  suffices_by metis_tac[ADDFRML_LEMM2,inAuto_def,MEM,SUBSET_DEF]
               >> fs[]
            )
            >> Cases_on `aut` >> Cases_on `addedNodesAut`
            >> fs[autoStates_def] >> metis_tac[]
           )
        >- (`MEM x' (autoStates addedNodesAut)` by (
              POP_ASSUM mp_tac >> Cases_on `aut`
              >> Cases_on `addedNodesAut` >> simp[autoStates_def,MEM_MAP]
              >> fs[])
            >> `set (autoStates addedNodesAut) =
                 set (autoStates (addFrmlToAut (concrAA g init aP) f'))
                    ∪ set (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f'))` by (
                  qunabbrev_tac `addedNodesAut`
                  >> `wfg (addFrmlToAut (concrAA g init aP) f').graph`
                     suffices_by metis_tac[ADDFRML_FOLDR_LEMM]
                  >> `(concrAA g init aP).graph = g`
                     suffices_by metis_tac[ADDFRML_LEMM2]
                  >> fs[]
            )
            >> `x' ∈ set (autoStates (addFrmlToAut (concrAA g init aP) f')) ∪
                   set (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f'))`
                by metis_tac[MEM]
            >> POP_ASSUM mp_tac >> rw[UNION_DEF]
            >- (`x' ∈ set (autoStates (concrAA g init aP)) ∪ {f'}` by (
                 `wfg (concrAA g init aP).graph`
                   suffices_by metis_tac[ADDFRML_LEMM3,MEM]
                  >> fs[]
                )
                >> POP_ASSUM mp_tac >> rw[UNION_DEF]
                 >- metis_tac[]
                 >- (`f' ∈ reachRelFromSet (ltl2waa f)
                            (set (autoStates (concrAA g init aP)))` by fs[]
                     >> fs[reachRelFromSet_def]
                     >> first_x_assum (qspec_then `x'` mp_tac) >> simp[]
                     >> rpt strip_tac >> metis_tac[RTC_RTC,reachRel_def]
                    )
               )
            >- (`!ls. MEM x' (FOLDR (λe pr. e.sucs ++ pr) [] ls)
                   ==> ?t. (MEM t ls) ∧ (MEM x' t.sucs)` by (
                     Induct_on `ls` >> fs[] >> rpt strip_tac
                     >> metis_tac[]
                )
                >> first_x_assum (qspec_then `trans_concr f'` mp_tac)
                >> simp[] >> rpt strip_tac
                >> `f' ∈
                      reachRelFromSet (ltl2waa f)
                      (set (autoStates (concrAA g init aP)))` by fs[]
                >> `f' ∈ tempSubForms f` by metis_tac[REACHREL_LEMM]
                >> fs[reachRelFromSet_def]
                >> first_x_assum (qspec_then `x''` mp_tac) >> simp[]
                >> rpt strip_tac >> qexists_tac `x'''` >> simp[]
                >> rpt strip_tac >> fs[]
                 >- (fs[reachRel_def]
                     >> `oneStep (ltl2waa f) f' x'` by (
                         `MEM (concr2AbstractEdge (props f) t)
                              (MAP (concr2AbstractEdge (props f))
                                   (trans_concr f'))` by (
                             fs[MEM_MAP] >> metis_tac[])
                         >> `concr2AbstractEdge (props f) t
                              ∈ trans (POW (props f)) f'` by (
                             metis_tac[TRANS_CONCR_LEMM,MEM]
                         )
                         >> Cases_on `concr2AbstractEdge (props f) t`
                         >> simp[oneStep_def] >> qexists_tac `q`
                         >> qexists_tac `r`
                         >> simp[ltl2waa_def,ltl2waa_free_alph_def]
                         >> Cases_on `t` >> fs[concr2AbstractEdge_def]
                      )
                     >> metis_tac[RTC_SUBSET,RTC_RTC]
                    )
                 >- metis_tac[]
               )
           )
        >- (`set (autoStates aut) = set (autoStates addedNodesAut)` by (
               Cases_on `aut` >> Cases_on `addedNodesAut`
               >> simp[autoStates_def] >> fs[]
            )
            >> `set (autoStates addedNodesAut) =
                 set (autoStates (addFrmlToAut (concrAA g init aP) f'))
                  ∪ set (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f'))` by (
                 qunabbrev_tac `addedNodesAut`
                 >> `wfg (addFrmlToAut (concrAA g init aP) f').graph`
                     suffices_by metis_tac[ADDFRML_FOLDR_LEMM]
                 >> `(concrAA g init aP).graph = g`
                     suffices_by metis_tac[ADDFRML_LEMM2]
                 >> fs[]
            )
            >> `f' ∈ tempSubForms f` by metis_tac[REACHREL_LEMM]
            >> `set (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f'))
                 ⊆ tempSubForms f` suffices_by (
                fs[UNION_DEF,SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[]
                >> `MEM x' (autoStates (addFrmlToAut (concrAA g init aP) f'))
                    \/ MEM x' (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f'))`
                    by metis_tac[]
                >- (`x' ∈ set (autoStates (concrAA g init aP)) ∪ {f'}` by (
                       `(concrAA g init aP).graph = g`
                         suffices_by metis_tac[ADDFRML_LEMM3]
                       >> fs[]
                    )
                    >> POP_ASSUM mp_tac >> rw[UNION_DEF] >> metis_tac[]
                   )
                >- (`!ls. MEM x' (FOLDR (λe pr. e.sucs ++ pr) [] ls)
                       ==> ?t. (MEM t ls) ∧ (MEM x' t.sucs)` by (
                        Induct_on `ls` >> fs[] >> rpt strip_tac
                        >> metis_tac[]
                    )
                    >> first_x_assum (qspec_then `trans_concr f'` mp_tac)
                    >> simp[] >> rpt strip_tac
                   )
            )
            >> simp[SUBSET_DEF] >> rpt strip_tac
            >> `!ls. MEM x' (FOLDR (λe pr. e.sucs ++ pr) [] ls)
                 ==> ?t. (MEM t ls) ∧ (MEM x' t.sucs)` by (
                   Induct_on `ls` >> fs[] >> rpt strip_tac
                   >> metis_tac[]
            )
            >> first_x_assum (qspec_then `trans_concr f'` mp_tac)
            >> simp[] >> rpt strip_tac
            >> `MEM (concr2AbstractEdge (props f) t)
                 (MAP (concr2AbstractEdge (props f))
                      (trans_concr f'))` by (
                   fs[MEM_MAP] >> metis_tac[])
            >> `concr2AbstractEdge (props f) t
                 ∈ trans (POW (props f)) f'` by (
                 metis_tac[TRANS_CONCR_LEMM,MEM]
            )
            >> Cases_on `concr2AbstractEdge (props f) t`
            >> `!j. j ∈ r ==> (j,f') ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
            >> `x' ∈ r` by (Cases_on `t` >> fs[concr2AbstractEdge_def])
            >> `(x',f') ∈ TSF ∧ (f',f) ∈ TSF` by metis_tac[TSF_def,IN_DEF]
            >> `(x',f) ∈ TSF` by metis_tac[TSF_TRANS_LEMM,transitive_def]
            >> metis_tac[TSF_TRANS_LEMM,transitive_def,TSF_def,IN_DEF]
           )
        >- (fs[expandAuto_def])
       )
  );


val expandAuto_init_def = Define`
  expandAuto_init φ =
    let initForms = tempDNF_concr φ
    in let a0 = concrAA empty [] (props_concr φ)
    in let a1 = FOLDR (\s a. addFrmlToAut a s) a0 (FLAT initForms)
    in let init_concr =
           MAP
            (λl. CAT_OPTIONS
                 (MAP (\s. findNode (λ(_,l). l.frml = s) a1.graph) l))
            initForms
    in let a_init = a1 with <| init := init_concr |>
    in expandAuto a_init (FLAT initForms)`;

(* val EXP_WAA_CORRECT = store_thm *)
(*   ("EXP_WAA_CORRECT", *)
(*    ``!φ. case expandAuto_init φ of *)
(*           | NONE => F *)
(*           | SOME concrA => *)
(*             concr2AbstrAA concrA = removeStatesSimpl (ltl2waa φ)``, *)
(*    rpt strip_tac >> Cases_on `expandAuto_init φ` >> fs[] *)
(*     >- (fs[expandAuto_init_def] >> POP_ASSUM mp_tac *)
(*         >> Q.HO_MATCH_ABBREV_TAC `(expandAuto aut fs = NONE) ==> F` *)
(*         >> `wfg aut.graph` *)
(*              suffices_by metis_tac[EXP_AUTO_WFG_AND_SOME,NOT_SOME_NONE] *)
(*         >> qunabbrev_tac `aut` >> fs[] *)
(*         >> `wfg (concrAA empty [] (props_concr φ)).graph` *)
(*              suffices_by metis_tac[ADDFRML_FOLDR_LEMM] *)
(*         >> fs[empty_is_wfg] *)
(*        ) *)
(*     >- (Cases_on `x` >> simp[concr2AbstrAA_def] *)
(*         >> simp[removeStatesSimpl_def,ltl2waa_def,ltl2waa_free_alph_def] *)
(*         >> rpt strip_tac *)
(*         >- (fs[expandAuto_init_def] >> POP_ASSUM mp_tac *)
(*             >> Q.HO_MATCH_ABBREV_TAC *)
(*                  `expandAuto a0 (FLAT (tempDNF_concr φ)) *)
(*                    = SOME (concrAA g l l0) ==> A` *)
(*             >> qunabbrev_tac `A` *)
(*             >> !ls. *)
(*                 (set ls ⊆ set (trans_concr f')) *)
(*                 ==> ?aut. *)
(*                   (FOLDR (λe a_opt. monad_bind a_opt (addEdgeToAut f' e)) *)
(*                    (SOME *)
(*                       (FOLDR (λp g. addFrmlToAut g p) *)
(*                              (addFrmlToAut (concrAA g init aP) f') *)
(*                              (FOLDR (λe pr. e.sucs ⧺ pr) [] ls))) *)
(*                    ls = SOME aut) *)
(*                   ∧ (g.nodeInfo = aut.) *)
                



(* simp[SET_EQ_SUBSET] >> strip_tac) *)
(*  ) *)


