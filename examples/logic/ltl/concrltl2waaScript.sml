open HolKernel Parse bossLib boolLib gfgTheory listTheory optionTheory relationTheory pred_setTheory prim_recTheory pairTheory bagTheory set_relationTheory rich_listTheory

open alterATheory sptreeTheory ltlTheory generalHelpersTheory concrRepTheory ltl2waaTheory waaSimplTheory optionTheory

val _ = monadsyntax.temp_add_monadsyntax();
val _ = overload_on("monad_bind",``OPTION_BIND``);

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

val FOLDR_LEMM6 = store_thm
  ("FOLDR_LEMM6",
   ``!g l x. MEM x (FOLDR (λe pr. (g e) ⧺ pr) [] l)
                  = (?a. MEM a l ∧ MEM x (g a))``,
   Induct_on `l` >> rpt strip_tac >> fs[]
   >> simp[EQ_IMP_THM] >> rpt strip_tac >> metis_tac[]
  );

val FOLDR_CONCR_EDGE = store_thm
  ("FOLDR_CONCR_EDGE",
   ``!l. FOLDR
           (λsF e.
                <|pos := sF.pos ⧺ e.pos; neg := sF.neg ⧺ e.neg;
                  sucs := sF.sucs ⧺ e.sucs|>) (concrEdge [] [] [])
           l =
         concrEdge
             (FOLDR (λe pr. e.pos ++ pr) [] l)
             (FOLDR (λe pr. e.neg ++ pr) [] l)
             (FOLDR (λe pr. e.sucs ++ pr) [] l)``,
   Induct_on `l` >> fs[concrEdge_component_equality]
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

val PROPS_CONCR_LEMM = store_thm
  ("PROPS_CONCR_LEMM",
  ``!φ. set (props_concr φ) = (props φ)``,
  Induct_on `φ` >> rpt strip_tac >> fs[props_concr_def,props_def,subForms_def]
  >> simp[SET_EQ_SUBSET,UNION_DEF,SUBSET_DEF] >> rpt strip_tac
  >> metis_tac[]
  );

val d_conj_concr_def = Define`
  d_conj_concr d1 d2 =
      FOLDR
      (\e1 sofar. (MAP (λe2. <| pos := nub (e1.pos++e2.pos) ;
                               neg := nub (e1.neg++e2.neg) ;
                               sucs := nub (e1.sucs++e2.sucs) |> ) d2) ++ sofar)
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

(* val TRANS_CONCR_SUCS_AP = store_thm *)
(*   ("TRANS_CONCR_SUCS_AP", *)
(*    ``!f ce s. (MEM ce (trans_concr f)) *)
(*             ∧ (MEM s ce.sucs) *)
(*             ==> (props s ⊆ (props f))``, *)
(*    Induct_on `f` >> rpt strip_tac >> fs[trans_concr_def,props_def,subForms_def] *)
(*    >> fs[SUBSET_DEF] >> rpt strip_tac >> fs[concrEdge_component_equality] *)
(*    >- metis_tac[MEM] *)
(*    >- metis_tac[MEM] *)
(*    >- metis_tac[MEM] *)
(*    >- metis_tac[MEM] *)
(*    >- metis_tac[MEM] *)
(*    >- metis_tac[MEM] *)
(*    >- metis_tac[MEM] *)
(*    >- metis_tac[MEM] *)
(*    >- (fs[d_conj_concr_def,FOLDR_LEMM4,concrEdge_component_equality] *)
(*        >> `MEM s (e1.sucs ++ e2.sucs)` by metis_tac[nub_set] *)
(*        >> fs[] >> metis_tac[] *)
(*       ) *)
(*    >- (fs[d_conj_concr_def,FOLDR_LEMM4,concrEdge_component_equality] *)
(*          >> `MEM s (e1.sucs ++ e2.sucs)` by metis_tac[nub_set] *)
(*          >> fs[] >> metis_tac[] *)
(*       ) *)
(*    >- (fs[MEM_MAP,concrEdge_component_equality,tempDNF_concr_def] >> metis_tac[MEM]) *)

val TRANS_CONCR_AP = store_thm
  ("TRANS_CONCR_AP",
   ``!f ce. MEM ce (trans_concr f)
            ==> ((set ce.pos ⊆ (props f))
               ∧ (set ce.neg ⊆ (props f)))``,
   Induct_on `f` >> rpt strip_tac >> fs[trans_concr_def,props_def,subForms_def]
   >> fs[SUBSET_DEF] >> rpt strip_tac
   >- metis_tac[]
   >- metis_tac[]
   >- metis_tac[]
   >- metis_tac[]
   >- (fs[d_conj_concr_def,FOLDR_LEMM4,concrEdge_component_equality]
       >> `MEM x (e1.pos ++ e2.pos)` by metis_tac[nub_set]
       >> fs[] >> metis_tac[]
      )
   >- (fs[d_conj_concr_def,FOLDR_LEMM4,concrEdge_component_equality]
         >> `MEM x (e1.neg ++ e2.neg)` by metis_tac[nub_set]
         >> fs[] >> metis_tac[]
      )
   >- (fs[MEM_MAP,concrEdge_component_equality] >> metis_tac[MEM])
   >- (fs[MEM_MAP,concrEdge_component_equality] >> metis_tac[MEM])
   >- metis_tac[]
   >- (fs[d_conj_concr_def,concrEdge_component_equality]
       >> qabbrev_tac `g =
               λe1.
                 <|pos := nub e1.pos; neg := nub e1.neg;
                   sucs := nub (e1.sucs ⧺ [U f f'])|>`
       >> `MEM ce (FOLDR (λx l. g x::l) [] (trans_concr f))` by (
            fs[]
        )
       >> `MEM ce (MAP g (trans_concr f))` by metis_tac[MAP_FOLDR]
       >> fs[MEM_MAP] >> qunabbrev_tac `g` >> fs[concrEdge_component_equality]
       >> `MEM x ce.pos` by metis_tac[nub_set] >> metis_tac[]
      )
   >- metis_tac[]
   >- (fs[d_conj_concr_def,concrEdge_component_equality]
       >> qabbrev_tac `g =
              λe1.
                  <|pos := nub e1.pos; neg := nub e1.neg;
                    sucs := nub (e1.sucs ⧺ [U f f'])|>`
       >> `MEM ce (FOLDR (λx l. g x::l) [] (trans_concr f))`
            by fs[]
       >> `MEM ce (MAP g (trans_concr f))` by metis_tac[MAP_FOLDR]
       >> fs[MEM_MAP] >> qunabbrev_tac `g` >> fs[concrEdge_component_equality]
       >> `MEM x ce.neg` by metis_tac[nub_set] >> metis_tac[]
      )
   >- (qabbrev_tac `r = <|pos := []; neg := []; sucs := [R f f']|>`
       >> `!l1 l2 c. (MEM c (d_conj_concr l2 (r::l1)))
                   ∧ (MEM_SUBSET l1 (trans_concr f))
                   ∧ (MEM_SUBSET l2 (trans_concr f'))
             ==> ((!p. MEM p c.pos ==> (p ∈ (props f ∪ props f')))
                ∧ (!n. MEM n c.neg ==> (n ∈ (props f ∪ props f'))))` by (
            Induct_on `l2` >> fs[d_conj_concr_def]
            >> rpt strip_tac >> qunabbrev_tac `r`
            >> fs[concrEdge_component_equality,MEM_SUBSET_SET_TO_LIST]
            >> simp[props_def]
            >- metis_tac[nub_set]
            >- metis_tac[nub_set]
            >- (fs[MEM_MAP,concrEdge_component_equality]
                >> `MEM p (h.pos ++ e2.pos)` by metis_tac[nub_set]
                >> fs[] >> metis_tac[SUBSET_DEF]
               )
            >- (fs[MEM_MAP,concrEdge_component_equality]
                  >> `MEM n (h.neg ++ e2.neg)` by metis_tac[nub_set]
                  >> fs[] >> metis_tac[SUBSET_DEF]
               )
            >- (first_x_assum (qspec_then `l1` mp_tac) >> simp[]
                >> rpt strip_tac
                >> first_x_assum (qspec_then `c` mp_tac) >> simp[]
                >> rpt strip_tac >> fs[props_def]
               )
            >- (first_x_assum (qspec_then `l1` mp_tac) >> simp[]
                >> rpt strip_tac
                >> first_x_assum (qspec_then `c` mp_tac) >> simp[]
                >> rpt strip_tac >> fs[props_def]
               )
        )
       >> first_x_assum (qspec_then `trans_concr f` mp_tac)
       >> simp[MEM_SUBSET_SET_TO_LIST] >> rpt strip_tac
       >> first_x_assum (qspec_then `trans_concr f'` mp_tac)
       >> simp[MEM_SUBSET_SET_TO_LIST] >> rpt strip_tac
       >> first_x_assum (qspec_then `ce` mp_tac) >> simp[]
       >> simp[props_def] >> rpt strip_tac >> metis_tac[]
      )
   >- (qabbrev_tac `r = <|pos := []; neg := []; sucs := [R f f']|>`
       >> `!l1 l2 c. (MEM c (d_conj_concr l2 (r::l1)))
                   ∧ (MEM_SUBSET l1 (trans_concr f))
                   ∧ (MEM_SUBSET l2 (trans_concr f'))
             ==> ((!p. MEM p c.pos ==> (p ∈ (props f ∪ props f')))
                ∧ (!n. MEM n c.neg ==> (n ∈ (props f ∪ props f'))))` by (
            Induct_on `l2` >> fs[d_conj_concr_def]
            >> rpt strip_tac >> qunabbrev_tac `r`
            >> fs[concrEdge_component_equality,MEM_SUBSET_SET_TO_LIST]
            >> simp[props_def]
            >- metis_tac[nub_set]
            >- metis_tac[nub_set]
            >- (fs[MEM_MAP,concrEdge_component_equality]
                >> `MEM p (h.pos ++ e2.pos)` by metis_tac[nub_set]
                >> fs[] >> metis_tac[SUBSET_DEF]
               )
            >- (fs[MEM_MAP,concrEdge_component_equality]
                  >> `MEM n (h.neg ++ e2.neg)` by metis_tac[nub_set]
                  >> fs[] >> metis_tac[SUBSET_DEF]
               )
            >- (first_x_assum (qspec_then `l1` mp_tac) >> simp[]
                >> rpt strip_tac
                >> first_x_assum (qspec_then `c` mp_tac) >> simp[]
                >> rpt strip_tac >> fs[props_def]
               )
            >- (first_x_assum (qspec_then `l1` mp_tac) >> simp[]
                >> rpt strip_tac
                >> first_x_assum (qspec_then `c` mp_tac) >> simp[]
                >> rpt strip_tac >> fs[props_def]
               )
        )
       >> first_x_assum (qspec_then `trans_concr f` mp_tac)
       >> simp[MEM_SUBSET_SET_TO_LIST] >> rpt strip_tac
       >> first_x_assum (qspec_then `trans_concr f'` mp_tac)
       >> simp[MEM_SUBSET_SET_TO_LIST] >> rpt strip_tac
       >> first_x_assum (qspec_then `ce` mp_tac) >> simp[]
       >> simp[props_def] >> rpt strip_tac >> metis_tac[]
      )
  );


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
         >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
         >> fs[transformLabel_def,char_def]
        )
     >- (`<|pos := []; neg := [a]; sucs := []|> = concrEdge [] [a] []`
             by rw[concrEdge_component_equality]
         >> rw[] >> simp[concr2AbstractEdge_def]
         >> simp[props_def,char_neg_def,subForms_def] >> rw[INTER_DEF]
         >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
         >> fs[char_def,transformLabel_def,char_neg_def]
         >> metis_tac[]
        )
     >- (simp[d_conj_def,d_conj_concr_def,SET_EQ_SUBSET,SUBSET_DEF]
         >> rpt strip_tac
         >> qabbrev_tac `g = (λe1 e2.
                           <|pos := nub (e1.pos ⧺ e2.pos);
                             neg := nub (e1.neg ⧺ e2.neg);
                             sucs := nub (e1.sucs ⧺ e2.sucs)|>)`
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
              >> `<|pos := nub (a'.pos ⧺ b'.pos); neg := nub (a'.neg ⧺ b'.neg);
                    sucs := nub (a'.sucs ⧺ b'.sucs)|> =
                            concrEdge (nub (a'.pos ++ b'.pos))
                                      (nub (a'.neg ++ b'.neg))
                                      (nub (a'.sucs ++ b'.sucs))`
                  by rw[concrEdge_component_equality]
              >> simp[concr2AbstractEdge_def] >> Cases_on `a'`
              >> Cases_on `b'`
              >> simp[concr2AbstractEdge_def,transformLabel_def]
              >> metis_tac[FOLDR_LEMM5,nub_set,FOLDR_INTER_MEMEQUAL]
             )
          >- (`MEM (a1,e1) (MAP (concr2AbstractEdge aP) (trans_concr f))`
                by fs[]
              >> `MEM (a2,e2) (MAP (concr2AbstractEdge aP) (trans_concr f'))`
                  by fs[]
              >> fs[MEM_MAP]
              >> qexists_tac `g y y'` >> rpt strip_tac
               >- (qunabbrev_tac `g`
                  >> `<|pos := nub (y.pos ⧺ y'.pos);
                        neg := nub (y.neg ⧺ y'.neg);
                        sucs := nub (y.sucs ⧺ y'.sucs)|> =
                            concrEdge (nub (y.pos ++ y'.pos))
                                      (nub (y.neg ++ y'.neg))
                                      (nub (y.sucs ++ y'.sucs))`
                    by rw[concrEdge_component_equality]
                  >> simp[concr2AbstractEdge_def] >> rw[]
                  >> Cases_on `y` >> Cases_on `y'` >> fs[concr2AbstractEdge_def]
                  >> simp[transformLabel_def]
                  >> metis_tac[FOLDR_LEMM5,nub_set,FOLDR_INTER_MEMEQUAL]
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
                  >> simp[concr2AbstractEdge_def,transformLabel_def]
                  )
          >- (`set (MAP set (tempDNF_concr f)) = tempDNF f`
                     by fs[TEMPDNF_CONCR_LEMM]
                   >> `MEM e (MAP set (tempDNF_concr f))` by fs[]
                   >> fs[MEM_MAP]
                   >> qexists_tac `concrEdge [] [] y`
                   >> simp[concr2AbstractEdge_def,transformLabel_def]
                   >> qexists_tac `y` >> fs[concrEdge_component_equality]
             )
        )
     >- (simp[d_conj_def,d_conj_concr_def,SET_EQ_SUBSET,SUBSET_DEF]
          >> rpt strip_tac >> fs[MEM_MAP]
          >> qabbrev_tac `g = (λe1 sofar. (<|pos := nub e1.pos;
                                             neg := nub e1.neg;
                                             sucs := nub (e1.sucs ⧺ [U f f'])|>
                                          )::sofar)`
           >- (Cases_on `concr2AbstractEdge aP y ∈ trans (POW aP) f'` >> fs[]
               >> `!ls. MEM y (FOLDR g [] ls)
                    ==> ?k. (MEM k ls) ∧
                        (y = <|pos := nub k.pos; neg := nub k.neg;
                              sucs := nub (k.sucs ⧺ [U f f'])|>)` by (
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
               >> `<|pos := nub k.pos;
                     neg := nub k.neg;
                     sucs := nub (k.sucs ⧺ [U f f'])|>
                             = concrEdge (nub k.pos)
                                         (nub k.neg)
                                         (nub (k.sucs ++ [U f f']))`
                   by rw[concrEdge_component_equality]
               >> simp[concr2AbstractEdge_def] >> Cases_on `k`
               >> fs[concr2AbstractEdge_def,transformLabel_def]
                >> metis_tac[TRANS_ALPH_LEMM,INTER_SUBSET_EQN,FOLDR_INTER_MEMEQUAL,nub_set]
              )
           >- (Cases_on `(a1 ∩ a2,e1 ∪ e2) ∈ trans (POW aP) f'` >> fs[]
               >> `MEM (a1,e1) (MAP (concr2AbstractEdge aP) (trans_concr f))`
                  by fs[]
               >> fs[MEM_MAP]
               >> qexists_tac `concrEdge
                                 (nub y.pos)
                                 (nub y.neg)
                                 (nub (y.sucs ++ [U f f']))`
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
                    >> simp[transformLabel_def] >> qunabbrev_tac `c`
                    >> qunabbrev_tac `c_n`
                    >> metis_tac[FOLDR_INTER_MEMEQUAL,nub_set]
                   )
                >- (simp[SET_EQ_SUBSET,SUBSET_DEF] >> metis_tac[])
                >- (qabbrev_tac
                     `g = (λe1 sofar. (<|pos := nub e1.pos;
                                        neg := nub e1.neg;
                                        sucs := nub (e1.sucs ⧺ [U f f'])|>
                                      )::sofar)`
                    >> `!y ls k. (MEM k ls) ∧
                            (y = <|pos := nub k.pos; neg := nub k.neg;
                                   sucs := nub (k.sucs ⧺ [U f f'])|>)
                            ==> MEM y (FOLDR g [] ls)` by (
                         gen_tac >> Induct_on `ls` >> fs[] >> rpt strip_tac
                         >> fs[] >> Cases_on `MEM k ls
                                      ∧ y = <|pos := nub k.pos;
                                              neg := nub k.neg;
                                              sucs := nub (k.sucs ⧺ [U f f'])|>`
                         >> fs[] >> qunabbrev_tac `g` >> fs[]
                     )
                    >> (first_x_assum
                            (qspec_then `concrEdge
                                          (nub l)
                                          (nub l0)
                                          (nub (l1 ⧺ [U f f']))` mp_tac)
                        >> rpt strip_tac
                        >> first_x_assum (qspec_then `trans_concr f` mp_tac)
                        >> rpt strip_tac
                        >> first_x_assum
                              (qspec_then `concrEdge
                                            l l0 l1` mp_tac)
                        >> rpt strip_tac >> POP_ASSUM mp_tac
                        >> simp[concrEdge_component_equality]
                       )
                   )
              )
        )
     >- (simp[d_conj_def,d_conj_concr_def,SET_EQ_SUBSET,SUBSET_DEF]
         >> rpt strip_tac >> fs[MEM_MAP]
         >> qabbrev_tac `g1 = (λe1 e2.
                                   <|pos := nub (e1.pos ⧺ e2.pos);
                                     neg := nub (e1.neg ⧺ e2.neg);
                                     sucs := nub (e1.sucs ⧺ e2.sucs)|>)`
         >> qabbrev_tac `g2 = (λls2 e1 sofar.
                                   <|pos := nub e1.pos; neg := nub e1.neg;
                                     sucs := nub (e1.sucs ⧺ [R f f'])|> ::
                                     ((MAP (λe2. g1 e1 e2) ls2)
                                         ++ sofar))`
          >- (`MEM y (FOLDR (g2 (trans_concr f)) [] (trans_concr f'))` by (
              qunabbrev_tac `g1` >> qunabbrev_tac `g2` >> fs[]
             )
             >> `!ls1 ls2. (MEM y (FOLDR (g2 ls2) [] ls1)) ==>
               ?c1. (MEM c1 ls1)
                  ∧ ((y =  <|pos := nub c1.pos; neg := nub c1.neg;
                            sucs := nub (c1.sucs ⧺ [R f f'])|>)
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
                 >> `<|pos := nub c1.pos;
                       neg := nub c1.neg;
                       sucs := nub (c1.sucs ⧺ [R f f'])|>
                     = concrEdge (nub c1.pos)
                                 (nub c1.neg)
                                 (nub (c1.sucs ++ [R f f']))`
                    by rw[concrEdge_component_equality]
                 >> simp[concr2AbstractEdge_def] >> rpt strip_tac
                 >> Cases_on `c1` >> fs[concr2AbstractEdge_def]
                 >> `transformLabel aP (nub l) (nub l0) = q` by (
                       fs[transformLabel_def]
                       >> metis_tac[FOLDR_INTER_MEMEQUAL,nub_set]
                   )
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
                   >> `<|pos := nub (c1.pos ⧺ c2.pos);
                         neg := nub (c1.neg ⧺ c2.neg);
                         sucs := nub (c1.sucs ⧺ c2.sucs)|>
                      = concrEdge (nub (c1.pos ++ c2.pos))
                                  (nub (c1.neg ++ c2.neg))
                                  (nub (c1.sucs ++ c2.sucs))`
                      by rw[concrEdge_component_equality]
                   >> simp[concr2AbstractEdge_def] >> rpt strip_tac
                   >> Cases_on `c1` >> Cases_on `c2`
                   >> fs[concr2AbstractEdge_def,transformLabel_def]
                   >> metis_tac[FOLDR_LEMM5,FOLDR_INTER_MEMEQUAL,
                                nub_set,nub_append]
                 )
             )
          >- (`MEM (a1,e1) (MAP (concr2AbstractEdge aP) (trans_concr f'))`
                 by fs[]
              >> `MEM (a2,e2) (MAP (concr2AbstractEdge aP) (trans_concr f))`
                 by fs[]
              >> fs[MEM_MAP] >> Cases_on `y` >> Cases_on `y'`
              >> qexists_tac `
                  concrEdge (nub (l++l')) (nub (l0++l0')) (nub (l1++l1'))`
              >> rpt strip_tac >> fs[]
               >- (fs[concr2AbstractEdge_def] >> rpt strip_tac >> fs[]
                   >> simp[transformLabel_def]
                   >> metis_tac[FOLDR_LEMM5,FOLDR_INTER_MEMEQUAL,nub_set])
               >- (`!ls1 ls2 x y. MEM x ls1 ∧ MEM y ls2
                        ==> MEM (concrEdge (nub (x.pos ++ y.pos))
                                           (nub (x.neg ++ y.neg))
                                           (nub (x.sucs ++ y.sucs)))
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
              >> qexists_tac `concrEdge (nub l) (nub l0) (nub (l1 ++ [R f f']))`
              >> rpt strip_tac >> fs[]
               >- (fs[concr2AbstractEdge_def] >> rpt strip_tac >> fs[]
                    >- (`transformLabel aP l l0 =
                          transformLabel aP (nub l) (nub l0)`
                         by metis_tac[transformLabel_def,
                                      FOLDR_INTER_MEMEQUAL,nub_set]
                       >> `a1 ∩ a2 = a1` suffices_by rw[]
                       >> `a2 = POW aP` by simp[SET_EQ_SUBSET,SUBSET_DEF]
                       >> `a1 ∩ POW aP = a1` suffices_by rw[]
                       >> metis_tac[TRANS_ALPH_LEMM,INTER_SUBSET_EQN]
                       )
                    >- simp[SET_EQ_SUBSET,SUBSET_DEF,UNION_DEF]
                  )
               >- (`!ls1 ls2 x. MEM x ls1
                       ==> MEM (concrEdge
                                    (nub x.pos)
                                    (nub x.neg)
                                    (nub (x.sucs ++ [R f f'])))
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

val ONE_STEP_TRANS_CONCR = store_thm
  ("ONE_STEP_TRANS_CONCR",
   ``!f x y. (x ∈ tempSubForms f)
              ==> (oneStep (ltl2vwaa f) x y)
                    = (y ∈ BIGUNION
                         (set (MAP (SND o (concr2AbstractEdge (props f)))
                                   (trans_concr x))))``,
   rpt strip_tac
   >> `(y ∈ BIGUNION (set (MAP (SND ∘ concr2AbstractEdge (props f))
                               (trans_concr x))))
         = ?a e. (a,e) ∈ (trans (POW (props f)) x) ∧ (y ∈ e)` by (
       fs[BIGUNION,EQ_IMP_THM] >> rpt strip_tac
       >- (`?p. MEM p (MAP (concr2AbstractEdge (props f)) (trans_concr x))
             ∧ (s = SND p)` by (
           fs[MAP_o,MEM_MAP] >> metis_tac[])
           >> `p ∈ trans (POW (props f)) x` by metis_tac[TRANS_CONCR_LEMM]
           >> Cases_on `p` >> fs[] >> metis_tac[])
       >- (`MEM (a,e) (MAP (concr2AbstractEdge (props f)) (trans_concr x))`
             by metis_tac[TRANS_CONCR_LEMM]
           >> fs[MEM_MAP,MAP_o] >> qexists_tac `e` >> fs[] >> metis_tac[SND]
          )
   )
   >> simp[oneStep_def,ltl2vwaa_def,ltl2vwaa_free_alph_def]
  );

val tempSubfCl_def = Define`
  tempSubfCl l = BIGUNION { tempSubForms f | MEM f l }`;

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

val expandGraph_def = tDefine "expandGraph"
 `(expandGraph g [] = SOME g)
 ∧ (expandGraph g1 (f::fs)  =
     let trans = trans_concr f
     in let allSucs = nub (FOLDR (\e pr. e.sucs ++ pr) [] trans)
     in let g2 = FOLDR (\p g. addFrmlToGraph g p) g1 allSucs
     in let g3 =
            FOLDR
                (\e g_opt. monad_bind g_opt (addEdgeToGraph f e))
                (SOME g2) trans
     in let restNodes =
              FILTER (\s. ~(MEM s (graphStates g1))
                       ∧ ~(s = f)
                       ∧ ~(MEM s fs)) allSucs
     in case g3 of
         | NONE => NONE
         | SOME g => expandGraph g (restNodes++fs))`
  (WF_REL_TAC `inv_image
               (mlt1 (\f1 f2. f1 ∈ tempSubForms f2 ∧ ~(f1 = f2)))
               (list_to_bag o SND)`
   >- metis_tac[STRICT_TSF_WF,WF_mlt1]
   >- (simp[mlt1_def,list_to_bag_def] >> rpt strip_tac
       >> fs[LST_TO_BAG_FINITE] >> rpt strip_tac
       >> qexists_tac `f`
       >> qabbrev_tac
           `newNodes = FILTER
                        (λs. ~MEM s (graphStates g1) ∧ ~(s = f) ∧ ~(MEM s fs))
                        (nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f)))`
       >> qexists_tac `list_to_bag newNodes`
       >> qexists_tac `list_to_bag fs` >> fs[LST_TO_BAG_APPEND_UNION]
       >> rpt strip_tac >> `f1 ∈ set newNodes` by metis_tac[IN_LST_TO_BAG]
       >> qunabbrev_tac `newNodes` >> fs[MEM_FILTER]
       >> `!l. MEM f1 (nub (FOLDR (λ e pr. e.sucs ++ pr) [] l))
                ==> ?e. (MEM e l) ∧ (MEM f1 e.sucs)` by (
            Induct_on `l` >> rpt strip_tac >> fs[]
            >- metis_tac[]
            >- (fs[nub_set,MEM] >> metis_tac[])
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
      )
  );

val EXP_GRAPH_AP = store_thm
  ("EXP_GRAPH_AP",
   ``!aP g fs g2.
        (wfg g)
      ∧ (!f. MEM f fs ==> (props f ⊆ set aP))
      ∧ (expandGraph g fs = SOME g2)
      ∧ (∀id fls.
         (id ∈ domain g.nodeInfo ∧ lookup id g.followers = SOME fls)
         ==> (∀e. MEM e (MAP FST fls)
               ⇒ MEM_SUBSET e.pos_lab aP ∧ MEM_SUBSET e.neg_lab aP)
        )
      ∧ (!id nL.
         (lookup id g.nodeInfo = SOME nL)
         ==> (!e. MEM e nL.true_labels
                   ==> MEM_SUBSET e.pos_lab aP ∧ MEM_SUBSET e.neg_lab aP
             )
        )
      ==>
      (∀id fls.
        (id ∈ domain g2.nodeInfo ∧ lookup id g2.followers = SOME fls)
        ==> (∀e. MEM e (MAP FST fls)
              ⇒ MEM_SUBSET e.pos_lab aP ∧ MEM_SUBSET e.neg_lab aP)
      )
      ∧ (!id nL.
             (lookup id g2.nodeInfo = SOME nL)
             ==> (!e. MEM e nL.true_labels
                       ==> MEM_SUBSET e.pos_lab aP ∧ MEM_SUBSET e.neg_lab aP
                 )
        )``,
   gen_tac
   >> Q.HO_MATCH_ABBREV_TAC `
       !g fs g2.
         wfg g ∧ (!f. MEM f fs ==> props f ⊆ set aP)
         ∧ (expandGraph g fs = SOME g2)
         ∧ P g ∧ C g
         ==> (P g2 ∧ C g2)`
   >> HO_MATCH_MP_TAC (theorem "expandGraph_ind")
   >> fs[expandGraph_def]
   >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> strip_tac
   >> `P g` by (qunabbrev_tac `P` >> fs[] >> metis_tac[])
       >> Cases_on `
          FOLDR (λe g_opt. monad_bind g_opt (addEdgeToGraph f e))
          (SOME
           (FOLDR (λp g. addFrmlToGraph g p) g
            (nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f)))))
          (trans_concr f)` >> fs[]
       >> qabbrev_tac `G =
            (FOLDR (λp g. addFrmlToGraph g p) g
               (nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f))))`
       >> `!ls fs m.
            (!e. MEM e ls
                 ==> (MEM_SUBSET e.pos aP ∧ MEM_SUBSET e.neg aP))
            ∧ (FOLDR (λe g_opt. monad_bind g_opt (addEdgeToGraph f e))
               (SOME G) ls = SOME m)
            ==> (P m ∧ wfg m ∧ C m)` by (
            Induct_on `ls` >> fs[] >> strip_tac
            >- (rw[] >> fs[] >> qunabbrev_tac `P` >> fs[]
                >> rpt gen_tac >> strip_tac >> strip_tac >> strip_tac
                >> Cases_on `id ∈ domain g.nodeInfo`
                >- (
                `IS_SOME (lookup id g.nodeInfo)` by (
                   Cases_on `lookup id g.nodeInfo`
                   >> fs[domain_lookup,IS_SOME_DEF]
                )
                >> `lookup id g.followers = SOME fls` by (
                      qunabbrev_tac `G`
                      >> metis_tac[ADDFRML_FOLDR_LEMM]
                ) >> metis_tac[]
                 )
                >- (
                `!n FS. ~(n ∈ domain g.nodeInfo)
                     ∧ (n ∈ domain
                            (FOLDR (λp g. addFrmlToGraph g p) g FS).nodeInfo)
                    ==> (lookup n
                           (FOLDR (λp g. addFrmlToGraph g p) g FS).followers
                              = SOME [])` by (
                  gen_tac >> Induct_on `FS` >> fs[] >> rpt strip_tac >> fs[]
                  >> Cases_on
                      `n ∈ domain
                           (FOLDR (λp g. addFrmlToGraph g p) g FS).nodeInfo`
                  >- (`IS_SOME
                         (lookup n
                           (FOLDR (λp g. addFrmlToGraph g p) g FS).nodeInfo)`
                        by fs[IS_SOME_DEF,domain_lookup]
                      >> metis_tac[ADDFRML_LEMM2,ADDFRML_FOLDR_LEMM]
                     )
                  >- (qabbrev_tac `G1 = (FOLDR (λp g. addFrmlToGraph g p) g FS)`
                      >> `wfg G1` by (
                          qunabbrev_tac `G1`
                          >> metis_tac[ADDFRML_FOLDR_LEMM,ADDFRML_WFG]
                       )
                      >> `n = G1.next` by (
                         Cases_on
                           `~(MEM h (MAP ((λl. l.frml) ∘ SND)
                                        (toAList G1.nodeInfo)))`
                         >> Cases_on `h` >> fs[addFrmlToGraph_def]
                         >> fs[addNode_def]
                       )
                      >> Cases_on
                           `~(MEM h (MAP ((λl. l.frml) ∘ SND)
                                         (toAList G1.nodeInfo)))`
                      >> Cases_on `h` >> fs[addFrmlToGraph_def]
                      >> fs[addNode_def]
                     )
                )
              >> first_x_assum (qspec_then `id` mp_tac) >> strip_tac
              >> first_x_assum (qspec_then `
                  nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f))` mp_tac)
              >> simp[] >> strip_tac
              >> fs[MEM_MAP]
           )
               )
            >- (`wfg G` by (qunabbrev_tac `G` >> metis_tac[ADDFRML_FOLDR_LEMM])
                >> fs[] >> qunabbrev_tac `C` >> fs[] >> rpt gen_tac >> strip_tac
                >> strip_tac >> strip_tac
                >> Cases_on `id ∈ domain g.nodeInfo`
                >- (`IS_SOME (lookup id g.nodeInfo)` by (
                      Cases_on `lookup id g.nodeInfo`
                      >> fs[domain_lookup,IS_SOME_DEF]
                    )
                    >> `lookup id g.nodeInfo = SOME nL` by (
                        qunabbrev_tac `G` >> metis_tac[ADDFRML_FOLDR_LEMM]
                    ) >> metis_tac[]
                   )
                >- (
                 `!n FS nL. ~(n ∈ domain g.nodeInfo)
                          ∧ (lookup n
                              (FOLDR (λp g. addFrmlToGraph g p) g FS).nodeInfo
                             = SOME nL)
                ==> (nL.true_labels = [])` by (
                     gen_tac >> Induct_on `FS` >> fs[] >> rpt strip_tac >> fs[]
                     >- fs[domain_lookup]
                     >- (
                       qabbrev_tac `G1 = FOLDR (λp g. addFrmlToGraph g p) g FS`
                       >> Cases_on `n ∈ domain G1.nodeInfo`
                       >- (
                         `IS_SOME (lookup n G1.nodeInfo)`
                            by fs[IS_SOME_DEF,domain_lookup]
                         >> metis_tac[ADDFRML_LEMM2,ADDFRML_FOLDR_LEMM]
                       )
                       >- (
                        `n ∈ domain (addFrmlToGraph G1 h).nodeInfo`
                          by fs[domain_lookup]
                          >> `wfg G1` by (
                            qunabbrev_tac `G1`
                            >> metis_tac[ADDFRML_FOLDR_LEMM,ADDFRML_WFG]
                        )
                        >> `n = G1.next` by (
                            Cases_on
                             `~(MEM h (MAP ((λl. l.frml) ∘ SND)
                                           (toAList G1.nodeInfo)))`
                            >> Cases_on `h` >> fs[addFrmlToGraph_def]
                            >> fs[addNode_def] >> metis_tac[]
                      )
                     >> Cases_on
                        `~(MEM h (MAP ((λl. l.frml) ∘ SND)
                                      (toAList G1.nodeInfo)))`
                     >> Cases_on `h` >> fs[addFrmlToGraph_def]
                     >> fs[addNode_def,nodeLabelAA_component_equality]
                       )
                     )
                 )
                 >> first_x_assum (qspec_then `id` mp_tac) >> strip_tac
                 >> first_x_assum (qspec_then `
                    nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f))` mp_tac)
                 >> simp[] >> strip_tac
                 >> fs[MEM_MAP]
               )
               )
            >- (strip_tac >> strip_tac
                >> `P x'` by metis_tac[]
                >> Cases_on `h` >> fs[addEdgeToGraph_def]
                >> Cases_on `l1` >> fs[]
                >- (
                 rename[`findNode _ x = SOME x1`]
                 >> Cases_on `x1` >> fs[]
                 >> `wfg m` by metis_tac[updateNode_preserves_wfg]
                 >> `P m` by metis_tac[updateNode_preserves_edges,
                                       updateNode_preserves_domain,
                                       updateNode_preserves_wfg]
                 >> fs[] >> qunabbrev_tac `C` >> fs[] >> rpt gen_tac
                 >> strip_tac >> strip_tac >> strip_tac
                 >> Cases_on `id = q` >> fs[updateNode_def]
                 >- (fs[gfg_component_equality]
                     >> `nL =
                          (nodeLabelAA r.frml r.is_final
                            (edgeLabelAA 0 l l0::r.true_labels))`
                        by metis_tac[lookup_insert,SOME_11]
                     >> fs[]
                     >- (first_x_assum (qspec_then `concrEdge l l0 []` mp_tac)
                         >> simp[]
                        )
                     >- (`lookup id x.nodeInfo = SOME r` by (
                           fs[findNode_def]
                           >> metis_tac[FIND_LEMM2,MEM_toAList,SOME_11]
                         )
                         >> metis_tac[]
                        )
                    )
                 >- (fs[gfg_component_equality]
                     >> `lookup id x.nodeInfo = SOME nL`
                           by metis_tac[lookup_insert,SOME_11]
                     >> metis_tac[]
                    )
                 )
                >- (
                 rename[`findNode _ x = SOME x1`]
                 >> Cases_on `x1` >> fs[]
                 >> `!es. (!e. MEM e (MAP FST es)
                               ==> (MEM_SUBSET e.pos_lab aP)
                                 ∧ (MEM_SUBSET e.neg_lab aP)
                          )
                        ∧ (!s. MEM s (MAP SND es)
                               ==> (s ∈ domain x.nodeInfo)
                          )
                      ==>
                      ?G_next.
                      (FOLDR
                          (λe g_opt.
                             do
                             g_int <- g_opt;
                             newGraph <- addEdge q e g_int;
                             SOME newGraph
                             od) (SOME x) es = SOME G_next)
                      ∧ P G_next
                      ∧ (G_next.nodeInfo = x.nodeInfo)
                      ∧ (wfg G_next)
                     ` by (
                   Induct_on `es` >> fs[] >> rpt strip_tac
                   >> `(∀e.
                        MEM e (MAP FST es) ⇒
                        MEM_SUBSET e.pos_lab aP ∧ MEM_SUBSET e.neg_lab aP)
                     ∧ (∀s. MEM s (MAP SND es) ⇒ s ∈ domain x.nodeInfo)`
                      by metis_tac[]
                   >> fs[]
                   >> rename[`addEdge q h G_next`] >> Cases_on `h`
                   >> rename[`addEdge q (eL,suc) G_next`]
                   >> `q ∈ domain G_next.nodeInfo` by (
                       fs[findNode_def]
                       >> metis_tac[FIND_LEMM2,MEM_toAList,domain_lookup]
                   )
                   >> `?G_next2. addEdge q (eL,suc) G_next = SOME G_next2` by (
                       simp[addEdge_def] >> metis_tac[wfg_def,domain_lookup]
                   )
                   >> fs[addEdge_def]
                   >> `G_next2.nodeInfo = x.nodeInfo`
                      by fs[gfg_component_equality]
                   >> `wfg G_next2` by (
                       fs[wfg_def,gfg_component_equality,wfAdjacency_def]
                       >> Q.HO_MATCH_ABBREV_TAC `A ∧ B ∧ H`
                       >> `A ∧ (A ==> B) ∧ H` suffices_by fs[]
                       >> qunabbrev_tac `A` >> qunabbrev_tac `B`
                       >> qunabbrev_tac `H` >> rpt strip_tac
                       >- (`q INSERT (domain G_next.followers) =
                               domain x.nodeInfo`
                             suffices_by metis_tac[domain_insert]
                           >> fs[INSERT_DEF] >> simp[SET_EQ_SUBSET,SUBSET_DEF]
                           >> metis_tac[]
                          )
                       >- (Cases_on `q = k` >> fs[] >> rw[]
                         >- (`nl = ((eL,suc)::followers_old)`
                              by (metis_tac[lookup_insert,SOME_11])
                             >> fs[] >> metis_tac[]
                            )
                         >- (`lookup k G_next.followers = SOME nl`
                               by metis_tac[lookup_insert,SOME_11]
                             >> metis_tac[]
                            )
                          )
                       >- metis_tac[]
                   )
                 >> fs[]
                 >> qunabbrev_tac `P` >> fs[] >> rpt gen_tac >> strip_tac
                 >> strip_tac >> strip_tac
                 >> Cases_on `id = q` >> fs[]
                 >- (`fls = (eL,suc)::followers_old` by (rw[] >> fs[])
                     >> fs[MEM_MAP] >> metis_tac[]
                    )
                 >- (`lookup id G_next.followers = SOME fls`
                      by (rw[] >> fs[] >> metis_tac[lookup_insert,SOME_11])
                     >> metis_tac[]
                    )
                 )
               >> first_x_assum (qspec_then `
                    MAP
                    (λi.
                         (<|edge_grp :=
                          (if oldSucPairs = [] then 1
                           else (HD (MAP FST oldSucPairs)).edge_grp) + 1;
                          pos_lab := l; neg_lab := l0|>,i))
                    (MAP FST
                         (CAT_OPTIONS
                              (findNode (λ(n,l). l.frml = h) x::
                               MAP (λs. findNode (λ(n,l). l.frml = s) x) t)))`
                 mp_tac)
               >> simp[]
               >> Q.HO_MATCH_ABBREV_TAC `(A ==> (P m ∧ (m.nodeInfo = x.nodeInfo)
                                                ∧ wfg m))
                                          ==> P m ∧ wfg m ∧ C m`
               >> `m.nodeInfo = x.nodeInfo ==> C m` by (
                     qunabbrev_tac `C` >> fs[] >> metis_tac[]
                 )
               >> `A` suffices_by metis_tac[] >> qunabbrev_tac `A` >> conj_tac
               >- (strip_tac >> strip_tac >> fs[MEM_MAP,CAT_OPTIONS_MEM]
                   >- (first_x_assum (qspec_then `concrEdge l l0 (h::t)` mp_tac)
                       >> simp[]
                      )
                   >- (first_x_assum (qspec_then `concrEdge l l0 (h::t)` mp_tac)
                                     >> simp[]
                      )
                  )
               >- (strip_tac >> strip_tac >> fs[MEM_MAP,CAT_OPTIONS_MEM]
                   >> fs[findNode_def] >> rename[`SOME y = FIND _ _`]
                   >> Cases_on `y` >> simp[]
                   >> metis_tac[FIND_LEMM2,MEM_toAList,SOME_11,domain_lookup]
                  )
               )
            )
        )
       >> first_x_assum (qspec_then `trans_concr f` mp_tac) >> simp[]
       >> `∀e. MEM e (trans_concr f)
            ⇒ MEM_SUBSET e.pos aP ∧ MEM_SUBSET e.neg aP` by (
            rpt strip_tac >> IMP_RES_TAC TRANS_CONCR_AP
            >> fs[MEM_SUBSET_SET_TO_LIST] >> metis_tac[SUBSET_TRANS]
        )
       >> simp[] >> strip_tac
       >> `(∀f'.
             MEM f'
             (FILTER (λs. ¬MEM s (graphStates g) ∧ s ≠ f ∧ ¬MEM s fs)
                     (nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f)))) ∨
             MEM f' fs ⇒
             props f' ⊆ set aP)` suffices_by metis_tac[]
       >> rpt strip_tac >> fs[MEM_FILTER,FOLDR_LEMM6]
       >> `(concr2AbstractEdge (set aP) a) ∈ (trans (POW (set aP)) f)` by (
            metis_tac[MEM_MAP,TRANS_CONCR_LEMM]
        )
       >> Cases_on `a` >> fs[concr2AbstractEdge_def]
       >> `(f',f) ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
       >> `f' ∈ subForms f` by metis_tac[TSF_def,IN_DEF,TSF_IMPL_SF]
       >> fs[props_def,subForms_def,SUBSET_DEF] >> rpt strip_tac
       >> metis_tac[SUBFORMS_TRANS]
  );

(* val EXP_GRAPH_FRMLS_AD = store_thm *)
(*   ("EXP_GRAPH_FRMLS_AD", *)
(*   ``!aP g fs g2. *)
(*   (wfg g) ∧ (expandGraph g fs = SOME g2) *)
(*   ∧ (!i n. i ∈ (domain g.nodeInfo) ∧ (lookup i g.nodeInfo = SOME n) *)
(*          ==> ALL_DISTINCT n.frmls *)
(*     ) *)
(*   ==> *)
(*   (!i n. i ∈ (domain g2.nodeInfo) ∧ (lookup i g2.nodeInfo = SOME n) *)
(*       ==> ALL_DISTINCT n.frmls *)
(*   )``, *)


(* ) *)


val EXP_GRAPH_WFG_AND_SOME = store_thm
  ("EXP_GRAPH_WFG_AND_SOME",
   ``!g fs. wfg g
          ∧ (unique_node_formula g)
          (* ∧ (first_flw_has_max_counter g) *)
          ∧ (flws_sorted g)
          ∧ (!f. MEM f fs ==> MEM f (graphStates g))
        ==> (?g2. (expandGraph g fs = SOME g2)
              ∧ (wfg g2)
              ∧ (set (graphStates g) ⊆ set (graphStates g2))
              ∧ (set (graphStatesWithId g) ⊆ set (graphStatesWithId g2))
              ∧ (until_iff_final g ==> until_iff_final g2)
              ∧ (unique_node_formula g2)
              ∧ (flws_sorted g2)
              (* ∧ (first_flw_has_max_counter g2) *))``,
   HO_MATCH_MP_TAC (theorem "expandGraph_ind")
   >> rpt strip_tac >> fs[expandGraph_def]
   >> Q.HO_MATCH_ABBREV_TAC
       `?g2. ((case A of
              | NONE => NONE
              | SOME g => (E g)) = SOME g2)
          ∧ wfg g2
          ∧ A0 ⊆ (A2 g2)
          ∧ C g2
          ∧ M g2`
      >> `!ls fs.
           (!e. MEM e ls ==> (!suc. MEM suc e.sucs ==> MEM suc fs))
           ==> ?x.
         (FOLDR (λe g_opt. monad_bind g_opt (addEdgeToGraph f e))
           (SOME
                (FOLDR (λp g. addFrmlToGraph g p) g
                       fs)) ls = SOME x)
         ∧ wfg x ∧ MEM f (graphStates x) ∧ A0 ⊆ A2 x
         ∧ C x ∧ (A2 x = A0 ∪ set fs)
         ∧ M x` by (
       Induct_on `ls` >> fs[] >> rpt strip_tac
        >- metis_tac[ADDFRML_FOLDR_LEMM]
        >- metis_tac[ADDFRML_LEMM,SUBSET_DEF,ADDFRML_FOLDR_LEMM,SUBSET_UNION]
        >- (qunabbrev_tac `A0` >> qunabbrev_tac `A2` >> fs[]
            >> metis_tac[ADDFRML_FOLDR_LEMM,SUBSET_UNION]
           )
        >- (qunabbrev_tac `C` >> simp[] >> rpt strip_tac
            >> simp[SUBSET_DEF] >> rpt strip_tac >> fs[]
            >> fs[graphStatesWithId_def,MEM_MAP] >> qexists_tac `y`
            >> fs[] >> Cases_on `y` >> fs[]
            >> `lookup q g.nodeInfo = SOME r` by metis_tac[MEM_toAList,IS_SOME_DEF]
            >> `lookup q g.nodeInfo = lookup q (addFrmlToGraph g f).nodeInfo`
               by metis_tac[ADDFRML_LEMM2,IS_SOME_DEF]
            >> metis_tac[ADDFRML_FOLDR_LEMM,MEM_toAList,IS_SOME_DEF]
           )
        >- (
         qunabbrev_tac `A0` >> qunabbrev_tac `A2` >> fs[]
         >> Q.HO_MATCH_ABBREV_TAC `Q = P`
         >> `Q = set (graphStates g) ∪ (set fs')` by (
             metis_tac[ADDFRML_FOLDR_LEMM]
         )
         >> qunabbrev_tac `Q` >> qunabbrev_tac `P` >> fs[]
         >> metis_tac[INSERT_SING_UNION,UNION_ASSOC]
       )
        >- (qunabbrev_tac `M` >> fs[] >> rpt strip_tac
            >> metis_tac[ADDFRML_FOLDR_LEMM]
           )
        >- (simp[] >> Q.HO_MATCH_ABBREV_TAC `?x1. (?x2. P x1 x2) ∧ Q x1`
            >> `?x2 x1. P x1 x2 ∧ Q x1` suffices_by metis_tac[]
            >> qunabbrev_tac `P` >> qunabbrev_tac `Q`
            >> first_x_assum (qspec_then `fs'` mp_tac) >> rpt strip_tac
            >> simp[] >> POP_ASSUM mp_tac
            >> `(∀e. MEM e ls ⇒ ∀suc. MEM suc e.sucs ⇒ MEM suc fs')`
               by metis_tac[]
            >> Q.HO_MATCH_ABBREV_TAC `(Q ==> Z) ==> P`
            >> `Z ==> P` suffices_by fs[] >> qunabbrev_tac `Z`
            >> qunabbrev_tac `P`
            >> simp[] >> qunabbrev_tac `M` >> fs[] >> rpt strip_tac
            >> `∀q. MEM q h.sucs ⇒ MEM q (graphStates x)` by (
                 rpt strip_tac
                 >> `∀suc. MEM suc h.sucs ⇒ MEM suc fs'` by metis_tac[]
                 >> qunabbrev_tac `A2` >> fs[]
             ) >> simp[]
            >> `∃g2. addEdgeToGraph f h x = SOME g2 ∧ wfg g2
                  ∧ set (graphStatesWithId x) = set (graphStatesWithId g2)
                  ∧ unique_node_formula g2
                  (* ∧ (flws_sorted g2) *)
                 (* ∧ first_flw_has_max_counter g2 *)`
                by metis_tac[ADDEDGE_LEMM,IS_SOME_EXISTS]
            >> `flws_sorted g2` by metis_tac[ADDEDGE_COUNTER_LEMM]
            >> qexists_tac `g2`  >> simp[] >> qunabbrev_tac `A2`
            >> `C g2` by metis_tac[] >> simp[] >> rpt strip_tac
            >> qunabbrev_tac `A0`
            >> `set (graphStates g) ⊆ set (graphStates g2)` by (
                 simp[SUBSET_DEF] >> rpt strip_tac
                 >> `MEM x' (graphStates x)` by metis_tac[SUBSET_DEF]
                 >> POP_ASSUM mp_tac >> simp[graphStates_def,MEM_MAP]
                 >> rpt strip_tac >> Cases_on `y`
                 >> `MEM (q,r.frml) (graphStatesWithId g2)`
                    by metis_tac[GRAPH_STATES_WITH_ID_LEMM]
                 >> POP_ASSUM mp_tac >> simp[graphStatesWithId_def,MEM_MAP]
                 >> rpt strip_tac >> qexists_tac `y` >> Cases_on `y` >> fs[]
             )
            >> rpt strip_tac
            >- (fs[]
                >> `MEM f (graphStates g)` by metis_tac[]
                >> metis_tac[MEM,SUBSET_DEF]
               )
            >- (`set (graphStates x) = set (graphStates g2)`
                 by metis_tac[GRAPH_STATES_ID_IMP_GRAPH_STATES]
                >> fs[]
               )
            >- metis_tac[ADDEDGE_FINAL_LEMM]
           )
   )
   >> first_x_assum (qspec_then `trans_concr f` mp_tac) >> rpt strip_tac
   >> first_x_assum
       (qspec_then `nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f))` mp_tac)
   >> rpt strip_tac >> POP_ASSUM mp_tac
   >> `∀e.
         MEM e (trans_concr f) ⇒
         ∀suc.
         MEM suc e.sucs ⇒
         MEM suc (nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f)))` by (
      rpt strip_tac >> fs[] >> metis_tac[FOLDR_LEMM6,nub_set,MEM]
      ) >> Q.HO_MATCH_ABBREV_TAC `(Q ==> H) ==> P`
   >> `H ==> P` suffices_by fs[] >> qunabbrev_tac `H` >> qunabbrev_tac `P`
   >> rpt strip_tac >> fs[]
   >> qunabbrev_tac `M` >> fs[] >> qunabbrev_tac `A` >> rw[]
   >> qunabbrev_tac `E` >> fs[] >> POP_ASSUM mp_tac >> simp[]
   >> Q.HO_MATCH_ABBREV_TAC `(P ==> Q) ==> H`
   >> `P` by (
       qunabbrev_tac `P` >> rpt strip_tac >> qunabbrev_tac `A2`
       >> fs[MEM_FILTER]
       )
   >> `Q ==> H` suffices_by fs[] >> qunabbrev_tac `Q` >> qunabbrev_tac `H`
   >> rpt strip_tac >> qexists_tac `g2` >> fs[]
   >> qunabbrev_tac `C` >> fs[] >> metis_tac[SUBSET_TRANS]
   );

val EXP_GRAPH_REACHABLE = store_thm
  ("EXP_GRAPH_REACHABLE",
   ``!f g ls.
            (!g2.
              (!x. MEM x ls
                   ==> x ∈ reachRelFromSet (ltl2vwaa f) (set (graphStates g)))
            ∧ (!x. MEM x (graphStates g)
                   ==> x ∈ reachRelFromSet
                           (ltl2vwaa f) (BIGUNION (ltl2vwaa f).initial))
            ∧ (!x. MEM x ls ==> MEM x (graphStates g))
            ∧ (unique_node_formula g)
            (* ∧ (first_flw_has_max_counter g) *)
            ∧ (flws_sorted g)
            ∧ (set (graphStates g) ⊆ tempSubForms f)
            ∧ (expandGraph g ls = SOME g2)
            ∧ (wfg g)
         ==> (!x. MEM x (graphStates g2)
                  ==> ((x ∈ reachRelFromSet (ltl2vwaa f)
                             (BIGUNION (ltl2vwaa f).initial))
                    ∧ (x ∈ tempSubForms f))))``,
   gen_tac
   >> HO_MATCH_MP_TAC (theorem "expandGraph_ind")
   >> strip_tac >> strip_tac >> strip_tac >> strip_tac
   >> strip_tac >> strip_tac
    >- (strip_tac
        >> `g = g2` by fs[expandGraph_def]
        >> rw[] >> metis_tac[MEM,SUBSET_DEF]
       )
    >- (strip_tac >> strip_tac >> strip_tac >> fs[]
        >> qabbrev_tac `addedNodesG =
            FOLDR (λp g. addFrmlToGraph g p) g
                   (nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f')))`
        >> `set (nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f')))
              ⊆ set (graphStates addedNodesG)
              ∧ (wfg addedNodesG)
              ∧  set (graphStates g(* (addFrmlToGraph g f') *))
                   ⊆ set (graphStates addedNodesG)
              ∧ MEM f' (graphStates addedNodesG)` by (
             metis_tac[ADDFRML_FOLDR_LEMM,SUBSET_UNION,
                          MEM,ADDFRML_LEMM,SUBSET_DEF]
         )
        >> `!ls. ?g.
              (!e suc. MEM e ls ∧ MEM suc e.sucs
                  ==> MEM suc (graphStates addedNodesG))
              ==> ((FOLDR (λe g_opt. monad_bind g_opt (addEdgeToGraph f' e))
              (SOME addedNodesG) ls = SOME g)
              ∧ (wfg g)
              ∧ set (graphStatesWithId addedNodesG) = set (graphStatesWithId g)
              ∧ unique_node_formula g
              ∧ flws_sorted g(* first_flw_has_max_counter g *))
              ` by (
             `flws_sorted addedNodesG
              ∧ unique_node_formula addedNodesG`
               by metis_tac[ADDFRML_FOLDR_LEMM]
             >> metis_tac[ADDEDGE_FOLDR_LEMM]
                )
        >> first_x_assum (qspec_then `trans_concr f'` mp_tac)
        >> `∀e suc.
              MEM e (trans_concr f') ∧ MEM suc e.sucs ⇒
              MEM suc (graphStates addedNodesG)` by (
           rpt strip_tac >> qunabbrev_tac `addedNodesG` >> fs[]
           >> Q.HO_MATCH_ABBREV_TAC `
               MEM suc (graphStates (FOLDR (λp g. addFrmlToGraph g p) g L))`
           >> `suc ∈ (set L)`
               suffices_by metis_tac[ADDFRML_FOLDR_LEMM,IN_UNION]
           >> qunabbrev_tac `L` >> metis_tac[FOLDR_LEMM6,nub_set,MEM]
         )
        >> strip_tac
        >> POP_ASSUM mp_tac >> Q.HO_MATCH_ABBREV_TAC `(A ==> B) ==> C`
        >> `B ==> C` suffices_by fs[]
        >> qunabbrev_tac `B` >> qunabbrev_tac `C` >> qunabbrev_tac `A`
        >> strip_tac
        >> first_x_assum (qspec_then `g'` mp_tac) >> simp[] >> strip_tac
        >> first_x_assum (qspec_then `g2` mp_tac) >> simp[]
        >> Q.HO_MATCH_ABBREV_TAC `(A ==> B) ==> C`
        >> `B ==> C` by (
             qunabbrev_tac `B` >> qunabbrev_tac `C` >> metis_tac[]
         )
        >> `set (graphStates addedNodesG) = set (graphStates g')`
             by metis_tac[GRAPH_STATES_ID_IMP_GRAPH_STATES]
        >> `A` suffices_by fs[]
        >> qunabbrev_tac `A` >> rpt strip_tac
        >- (`MEM f' (graphStates g')` by fs[]
            >> `reachRel (ltl2vwaa f) f' x'` suffices_by (
                  simp[reachRelFromSet_def] >> metis_tac[inAuto_def]
            )
            >> fs[MEM_FILTER]
            >> `!ls. MEM x' (nub (FOLDR (λe pr. e.sucs ++ pr) [] ls))
                  ==> ?t. (MEM t ls) ∧ (MEM x' t.sucs)`
               by metis_tac[FOLDR_LEMM6,nub_set,MEM]
            >> first_x_assum (qspec_then `trans_concr f'` mp_tac) >> simp[]
            >> rpt strip_tac >> simp[reachRel_def]
            >> `oneStep (ltl2vwaa f) f' x'` suffices_by fs[]
            >> simp[oneStep_def,ltl2vwaa_def,ltl2vwaa_free_alph_def]
            >> `(concr2AbstractEdge (props f) t) ∈ trans (POW (props f)) f'` by (
                 `MEM (concr2AbstractEdge (props f) t)
                      (MAP (concr2AbstractEdge (props f)) (trans_concr f'))`
                     by (simp[MEM_MAP] >> metis_tac[])
                 >> fs[TRANS_CONCR_LEMM]
            )
            >> Cases_on `concr2AbstractEdge (props f) t`
            >> qexists_tac `q` >> qexists_tac `r` >> simp[]
            >> Cases_on `t` >> fs[concr2AbstractEdge_def]
            >> `f' ∈ reachRelFromSet (ltl2vwaa f) (set (graphStates g))`
               by metis_tac[]
            >> metis_tac[REACHREL_LEMM]
           )
        >- (`x' ∈ reachRelFromSet (ltl2vwaa f) (set (graphStates g))`
               by metis_tac[]
            >> fs[reachRelFromSet_def] >> qexists_tac `x''` >> simp[]
            >> `MEM x'' (graphStates addedNodesG)`
               by metis_tac[ADDFRML_LEMM2,SET_EQ_SUBSET,MEM,
                            SUBSET_DEF,ADDFRML_WFG,SUBSET_UNION]
            >> fs[graphStates_def] >> metis_tac[]
           )
        >- (`MEM x' (graphStates addedNodesG)`
              by metis_tac[graphStates_def,MEM_MAP]
            >> `set (graphStates addedNodesG) =
                 set (graphStates g)
                  ∪ set (nub (FOLDR
                              (λe pr. e.sucs ⧺ pr)
                              []
                              (trans_concr f')))` by (
                  qunabbrev_tac `addedNodesG`
                  >> metis_tac[ADDFRML_FOLDR_LEMM,ADDFRML_WFG]
            )
            >> `x' ∈ set (graphStates g)
                   ∪ set (nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f')))`
                by metis_tac[MEM]
            >> POP_ASSUM mp_tac >> rw[UNION_DEF]
            >- (metis_tac[])
            >- (`!ls. MEM x' (nub (FOLDR (λe pr. e.sucs ++ pr) [] ls))
                   ==> ?t. (MEM t ls) ∧ (MEM x' t.sucs)`
                   by metis_tac[FOLDR_LEMM6,nub_set,MEM]
                >> first_x_assum (qspec_then `trans_concr f'` mp_tac)
                >> simp[] >> rpt strip_tac
                >> `f' ∈
                      reachRelFromSet (ltl2vwaa f)
                      (set (graphStates g))` by fs[]
                >> `f' ∈ tempSubForms f` by metis_tac[REACHREL_LEMM]
                >> fs[reachRelFromSet_def]
                >> `∃x'''.
                      reachRel (ltl2vwaa f) x''' x'' ∧
                      ∃s. x''' ∈ s ∧ s ∈ (ltl2vwaa f).initial` by fs[]
                >> rpt strip_tac >> qexists_tac `x'''` >> simp[]
                >> (fs[reachRel_def]
                     >> `oneStep (ltl2vwaa f) f' x'` by (
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
                         >> simp[ltl2vwaa_def,ltl2vwaa_free_alph_def]
                         >> Cases_on `t` >> fs[concr2AbstractEdge_def]
                      )
                     >> metis_tac[RTC_SUBSET,RTC_RTC]
                    )
               )
           )
        >- (`MEM x' (graphStates addedNodesG)` suffices_by metis_tac[]
            >> POP_ASSUM mp_tac
            >> PURE_REWRITE_TAC[MEM_FILTER,FOLDR_LEMM6,nub_set,MEM]
            >> fs[]
           )
        >- (`MEM x' (graphStates addedNodesG)` suffices_by metis_tac[]
            >> metis_tac[SUBSET_DEF]
           )
        >- (`set (graphStates addedNodesG) =
                 set (graphStates g)
                  ∪ set
                    (nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f')))` by (
                 qunabbrev_tac `addedNodesG`
                 >> metis_tac[ADDFRML_FOLDR_LEMM,ADDFRML_WFG]
            )
            >> `f' ∈ tempSubForms f` by metis_tac[REACHREL_LEMM]
            >> `set (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f'))
                 ⊆ tempSubForms f` suffices_by (
                fs[UNION_DEF,SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac >> fs[] >> metis_tac[]
            )
            >> simp[SUBSET_DEF] >> rpt strip_tac
            >> `!ls. MEM x' (FOLDR (λe pr. e.sucs ++ pr) [] ls)
                 ==> ?t. (MEM t ls) ∧ (MEM x' t.sucs)` by (
                   Induct_on `ls` >> fs[] >> rpt strip_tac
                   >> metis_tac[nub_set,MEM]
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
        >- fs[expandGraph_def]
       )
  );

val EXP_AUTO_ALL_REACHABLE = store_thm
  ("EXP_AUTO_ALL_REACHABLE",
   ``!f g ls g2 x. (!x. MEM x (graphStates g) ∧ ~ MEM x ls
                            ==> (!y. oneStep (ltl2vwaa f) x y
                                     ==> MEM y (graphStates g)))
                     ∧ (expandGraph g ls = SOME g2)
                     ∧ (!x. MEM x ls ==> x ∈ tempSubForms f)
                     ∧ (!x. MEM x ls ==> MEM x (graphStates g))
                     ∧ (wfg g)
                     ∧ (unique_node_formula g)
                     ∧ (flws_sorted g)
                   ==> (!x. MEM x (graphStates g2)
                          ==> (!y. oneStep (ltl2vwaa f) x y
                                ==> (MEM y (graphStates g2))))``,
   gen_tac >> HO_MATCH_MP_TAC (theorem "expandGraph_ind") >> rpt strip_tac
   >> fs[]
    >- (fs[expandGraph_def] >> rw[] >> metis_tac[])
    >- (qabbrev_tac `addedNodesG =
                 FOLDR (λp g. addFrmlToGraph g p)
                       g
                       (nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f')))`
        >> `set (graphStates g)
            ∪ set (nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f')))
              = set (graphStates addedNodesG)
              ∧ (wfg addedNodesG)
              ∧ MEM f' (graphStates addedNodesG)` by (
             metis_tac[ADDFRML_FOLDR_LEMM,SUBSET_UNION,
                          MEM,ADDFRML_LEMM,SUBSET_DEF]
         )
        >> `!ls. ?g.
              (!e suc. MEM e ls ∧ MEM suc e.sucs
                  ==> MEM suc (graphStates addedNodesG))
             ==> ((FOLDR (λe g_opt. monad_bind g_opt (addEdgeToGraph f' e))
                  (SOME addedNodesG) ls = SOME g)
              ∧ (wfg g)
              ∧ (flws_sorted g)
              ∧ (unique_node_formula g)
              ∧ (set (graphStatesWithId addedNodesG) =
                   set (graphStatesWithId g)))` by (
           `flws_sorted addedNodesG
            ∧ unique_node_formula addedNodesG` by metis_tac[ADDFRML_FOLDR_LEMM]
           >> metis_tac[ADDEDGE_FOLDR_LEMM]
         )
        >> first_x_assum (qspec_then `trans_concr f'` mp_tac) >> strip_tac
        >> POP_ASSUM mp_tac
        >> `∀e suc.
              MEM e (trans_concr f') ∧ MEM suc e.sucs ⇒
              MEM suc (graphStates addedNodesG)` by (
            rpt strip_tac >> fs[]
            >> metis_tac[FOLDR_LEMM6,SUBSET_UNION,SUBSET_DEF,nub_set,MEM]
         )
        >> Q.HO_MATCH_ABBREV_TAC `(A ==> B) ==> C` >> `B ==> C` suffices_by fs[]
        >> qunabbrev_tac `B` >> qunabbrev_tac `A` >> qunabbrev_tac `C`
        >> rpt strip_tac
        >> first_x_assum (qspec_then `g'` mp_tac) >> simp[] >> strip_tac
        >> first_x_assum (qspec_then `g2` mp_tac) >> simp[]
        >> Q.HO_MATCH_ABBREV_TAC `(A ==> B) ==> C`
        >> `B ==> C` by (qunabbrev_tac `B` >> qunabbrev_tac `C` >> metis_tac[nub_set,MEM])
        >> `A` suffices_by metis_tac[] >> qunabbrev_tac `A`
        >> `set (graphStates addedNodesG) = set (graphStates g')`
           by metis_tac[GRAPH_STATES_ID_IMP_GRAPH_STATES]
        >> rpt strip_tac
        >- (`MEM x' (graphStates addedNodesG)` by fs[graphStates_def]
             >> `x' ∈ set (graphStates g)
                      ∪ set (nub
                             (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f')))`
                by metis_tac[SET_EQ_SUBSET,SUBSET_DEF]
             >> POP_ASSUM mp_tac >> simp[]
             >> `(MEM x' (graphStates g)  ∨
                      (MEM x' ((FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f')))
                   ∧ ~ MEM x'(graphStates g )))
                      ⇒ MEM y' (graphStates g')` suffices_by metis_tac[]
             >> rw[]
              >- (Cases_on `~(x' = f')` >> rw[]
                   >- (`MEM y' (graphStates g)` by metis_tac[]
                       >> `set (graphStates g) ⊆ set (graphStates addedNodesG)`
                            by metis_tac[SET_EQ_SUBSET,SUBSET_TRANS,
                                         SUBSET_UNION,ADDFRML_LEMM2]
                       >> `set (graphStates g')
                             = set (graphStates addedNodesG)` by fs[graphStates_def]
                       >> metis_tac[SUBSET_DEF]
                      )
                   >- (`y' ∈ BIGUNION
                              (set
                               (MAP (SND ∘ concr2AbstractEdge (props f))
                                    (trans_concr f')))` by (
                         metis_tac[ONE_STEP_TRANS_CONCR]
                       )
                       >> POP_ASSUM mp_tac >> simp[BIGUNION,MEM_MAP,MAP_o]
                       >> rpt strip_tac >> fs[MEM_FILTER]
                       >> `MEM y' ((FOLDR (λe pr. e.sucs ⧺ pr)
                                         [] (trans_concr f')))` by (
                          Cases_on `y''` >> fs[concr2AbstractEdge_def]
                          >> fs[FOLDR_LEMM6,nub_set,MEM]
                          >> `(concrEdge l l0 l1).sucs = l1` by simp[]
                          >> metis_tac[]
                       )
                       >> `MEM y' (graphStates addedNodesG)`
                           suffices_by fs[graphStates_def]
                       >> metis_tac[SET_EQ_SUBSET,UNION_SUBSET,MEM,SUBSET_DEF]
                      )
                 )
              >- (fs[MEM_FILTER,inAuto_def] >> rw[] >> metis_tac[])
            )
         >- fs[expandGraph_def]
         >- (fs[MEM_FILTER]
             >> `∃a. MEM a (trans_concr f') ∧ MEM x' a.sucs`
                 by metis_tac[FOLDR_LEMM6,nub_set,MEM]
             >> `?s e. ((s,e) ∈ trans (POW (props f)) f') ∧ (x' ∈ e)` by (
                  `concr2AbstractEdge (props f) a
                    ∈ set (MAP (concr2AbstractEdge (props f)) (trans_concr f'))`
                    by (fs[MEM_MAP] >> metis_tac[])
                  >> `concr2AbstractEdge (props f) a ∈ trans (POW (props f)) f'`
                      by metis_tac[TRANS_CONCR_LEMM]
                  >> Cases_on `concr2AbstractEdge (props f) a`
                  >> `set a.sucs = r` by (
                      Cases_on `a` >> fs[concr2AbstractEdge_def]
                  )
                  >> metis_tac[]
              )
             >> `(x',f') ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
             >> metis_tac[TSF_def,TSF_TRANS_LEMM,IN_DEF,transitive_def]
            )
         >- fs[]
         >- (fs[MEM_FILTER] >> fs[SET_EQ_SUBSET,SUBSET_DEF])
         >- (fs[SET_EQ_SUBSET,SUBSET_DEF])
       )
  );

val EXP_GRAPH_TRANS_LEMM = store_thm
  ("EXP_GRAPH_TRANS_LEMM",
   ``!f g ls g2 x.
      (!x. MEM x (graphStates g) ∧ ~ MEM x ls
           ==> (!y. concrTrans g (props f) x
                = trans (POW (props f)) x))
    ∧ (expandGraph g ls = SOME g2)
    ∧ (!x. MEM x ls ==> x ∈ tempSubForms f)
    ∧ (!x. MEM x ls ==> MEM x (graphStates g))
    ∧ (!x. MEM x ls ==> empty_followers g x)
    ∧ (ALL_DISTINCT ls)
    ∧ (wfg g)
    ∧ unique_node_formula g
    ∧ flws_sorted g
    ==> (!x. MEM x (graphStates g2)
           ==> (!y. concrTrans g2 (props f) x
                     = trans (POW (props f)) x))``,
   gen_tac >> HO_MATCH_MP_TAC (theorem "expandGraph_ind") >> rpt strip_tac
   >> fs[]
   >- (fs[expandGraph_def] >> rw[] >> metis_tac[])
   >- (
    qabbrev_tac `addedNodesG =
                 FOLDR (λp g. addFrmlToGraph g p)
                       g
                       (nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f')))`
    >> `set (graphStates g)
          ∪ set (nub (FOLDR (λe pr. e.sucs ⧺ pr) [] (trans_concr f')))
           = set (graphStates addedNodesG)
        ∧ (wfg addedNodesG)
        ∧ MEM f' (graphStates addedNodesG)` by (
        metis_tac[ADDFRML_FOLDR_LEMM,SUBSET_UNION,
                  MEM,ADDFRML_LEMM,SUBSET_DEF]
    )
    >> `!ls. ?g.
        (!e suc. MEM e ls ∧ MEM suc e.sucs
            ==> MEM suc (graphStates addedNodesG))
        ==>
        ((FOLDR (λe g_opt. monad_bind g_opt (addEdgeToGraph f' e))
               (SOME addedNodesG) ls = SOME g)
        ∧ (wfg g)
        ∧ (flws_sorted g)
        ∧ (unique_node_formula g)
        ∧ (set (graphStatesWithId addedNodesG)
             = set (graphStatesWithId g)))
        ∧ (!h. if h = f'
                then IMAGE SND (extractTrans g h) =
                     IMAGE SND (extractTrans addedNodesG h)
                           ∪ { (e.pos,e.neg,set e.sucs) | MEM e ls}
                else extractTrans g h = extractTrans addedNodesG h)` by (
      `flws_sorted addedNodesG
       ∧ unique_node_formula addedNodesG` by metis_tac[ADDFRML_FOLDR_LEMM]
      >> metis_tac[ADDEDGE_FOLDR_LEMM]
    )
    >> first_x_assum (qspec_then `trans_concr f'` mp_tac) >> strip_tac
    >> POP_ASSUM mp_tac
    >> `∀e suc.
        MEM e (trans_concr f') ∧ MEM suc e.sucs ⇒
        MEM suc (graphStates addedNodesG)` by (
        rpt strip_tac >> fs[]
        >> metis_tac[FOLDR_LEMM6,SUBSET_UNION,SUBSET_DEF,nub_set,MEM]
    )
    >> Q.HO_MATCH_ABBREV_TAC `(A ==> B) ==> C` >> `B ==> C` suffices_by fs[]
    >> qunabbrev_tac `B` >> qunabbrev_tac `A` >> qunabbrev_tac `C`
    >> rpt strip_tac
    >> first_x_assum (qspec_then `g'` mp_tac) >> simp[] >> strip_tac
    >> first_x_assum (qspec_then `g2` mp_tac) >> simp[]
    >> Q.HO_MATCH_ABBREV_TAC `(A ==> B) ==> C`
    >> `B ==> C` by (
        qunabbrev_tac `B` >> qunabbrev_tac `C` >> metis_tac[]
    )
    >> `set (graphStates addedNodesG) = set (graphStates g')`
       by metis_tac[GRAPH_STATES_ID_IMP_GRAPH_STATES]
    >> `A` suffices_by fs[]
    >> qunabbrev_tac `A` >> strip_tac
    >- (rpt strip_tac
        >> `(~(x' = f') ∧ MEM x' (graphStates g)) \/ (x' = f')` by (
             Cases_on `x' = f'` >> fs[]
             >> fs[MEM_FILTER,SET_EQ_SUBSET,UNION_DEF,SUBSET_DEF]
             >> metis_tac[]
         )
        >- (`concrTrans g' (props f) x' = concrTrans g (props f) x'`
             suffices_by metis_tac[]
            >> PURE_REWRITE_TAC[concrTrans_def]
            >> `extractTrans g x' = extractTrans addedNodesG x'`
               suffices_by metis_tac[]
            >> metis_tac[ADDFRML_FOLDR_LEMM]
           )
        >- (rw[] >> PURE_REWRITE_TAC[concrTrans_def]
            >> `IMAGE SND (extractTrans addedNodesG f')= {}` suffices_by (
                 first_x_assum (qspec_then `f'` mp_tac) >> simp[]
                 >> rpt strip_tac
                 >> `IMAGE SND (extractTrans g' f') =
                     {(e.pos,e.neg,set e.sucs) | MEM e (trans_concr f')}`
                     by fs[]
                 >> `IMAGE (λ(i,p,n,e). (transformLabel (props f) p n,e))
                                (extractTrans g' f') =
                     IMAGE (λ(p,n,e). (transformLabel (props f) p n,e))
                             (IMAGE SND (extractTrans g' f'))` by (
                     simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                     >- (qexists_tac `SND x''` >> fs[] >> rpt strip_tac >> fs[]
                       >- (Cases_on `x''` >> Cases_on `r` >> Cases_on `r'`
                           >> fs[])
                       >- metis_tac[])
                     >- (qexists_tac `x'''` >> fs[] >> Cases_on `x'''`
                         >> Cases_on `r` >> Cases_on `r'` >> fs[])
                 )
                 >> rw[] >> Q.HO_MATCH_ABBREV_TAC `A = trans (POW (props f)) f'`
                 >> `A = set (MAP (concr2AbstractEdge (props f))
                                  (trans_concr f'))`
                    suffices_by metis_tac[TRANS_CONCR_LEMM]
                 >> qunabbrev_tac `A` >> simp[SET_EQ_SUBSET,SUBSET_DEF]
                 >> rpt strip_tac
                 >- (simp[MEM_MAP,concr2AbstractEdge_def] >> qexists_tac `e`
                     >> Cases_on `e` >> simp[concr2AbstractEdge_def]
                    )
                 >- (POP_ASSUM mp_tac >> simp[MEM_MAP,concr2AbstractEdge_def]
                     >> rpt strip_tac >> Cases_on `y`
                     >> fs[concr2AbstractEdge_def]
                     >> qexists_tac `(l,l0,set l1)` >> fs[]
                     >> qexists_tac `concrEdge l l0 l1` >> fs[]
                    )
             )
            >> fs[MEM_FILTER]
            >> `extractTrans g f' = {}` suffices_by metis_tac[ADDFRML_FOLDR_LEMM]
            >> metis_tac[EMPTY_FLWS_LEMM]
           )
       )
    >- (fs[expandGraph_def,MEM_FILTER]
        >> Q.HO_MATCH_ABBREV_TAC `B1 ∧ B2 ∧ B3 ∧ B4`
        >> `(B1 ∧ B2) ∧ B3 ∧ B4` suffices_by fs[]
        >> conj_tac
        >- (qunabbrev_tac `B1` >> qunabbrev_tac `B2` >> rpt strip_tac
            >> fs[MEM_FILTER] >> fs[SET_EQ_SUBSET,SUBSET_DEF]
            >> `∃a. MEM a (trans_concr f') ∧ MEM x' a.sucs`
             by metis_tac[FOLDR_LEMM6,nub_set,MEM]
           >> `?s e. ((s,e) ∈ trans (POW (props f)) f') ∧ (x' ∈ e)` by (
               `concr2AbstractEdge (props f) a
                  ∈ set (MAP (concr2AbstractEdge (props f)) (trans_concr f'))`
               by (fs[MEM_MAP] >> metis_tac[])
           >> `concr2AbstractEdge (props f) a ∈ trans (POW (props f)) f'`
               by metis_tac[TRANS_CONCR_LEMM]
           >> Cases_on `concr2AbstractEdge (props f) a`
           >> `set a.sucs = r` by (
              Cases_on `a` >> fs[concr2AbstractEdge_def]
               )
           >> metis_tac[]
          )
           >> `(x',f') ∈ TSF` by metis_tac[TRANS_REACHES_SUBFORMS]
           >> metis_tac[TSF_def,TSF_TRANS_LEMM,IN_DEF,transitive_def]
          )
       >- (conj_tac
        >- (qunabbrev_tac `B3` >> rpt strip_tac
           >> fs[MEM_FILTER] >> fs[SET_EQ_SUBSET,SUBSET_DEF]
           >> fs[empty_followers_def] >> strip_tac >> strip_tac >> strip_tac
           >> qabbrev_tac `addEdges =
                λls.
                    FOLDR (λe g_opt. monad_bind g_opt (addEdgeToGraph f' e))
                    (SOME addedNodesG) ls`
           >> `addEdges (trans_concr f') = SOME g'` by fs[]
           >> `!ls G. (addEdges ls = SOME G)
                ==> (lookup id G.nodeInfo =
                      lookup id addedNodesG.nodeInfo)
                  ∧ (lookup id G.followers =
                      lookup id addedNodesG.followers)` by (
                Induct_on `ls` >> fs[] >> qunabbrev_tac `addEdges` >> fs[]
                >> strip_tac >>  strip_tac >> strip_tac
                >> first_x_assum (qspec_then `x''` mp_tac) >> simp[]
                >> strip_tac >> Cases_on `h` >> fs[addEdgeToGraph_def]
                >> `?q r. findNode (λ(n,l). l.frml = f') x'' = SOME (q,r)` by (
                    Cases_on `l1 = []` >> fs[] >> Cases_on `x'''` >> simp[]
                )
                >> `(λ(n,l). l.frml = f') (q,r)
                  ∧ (lookup q x''.nodeInfo = SOME r)`
                    by metis_tac[findNode_def,FIND_LEMM2,MEM_toAList]
                >> fs[]
                >> `~(q = id)` by (
                    CCONTR_TAC >> fs[]
                    >> `MEM (id,r) (toAList addedNodesG.nodeInfo)`
                     by metis_tac[MEM_toAList]
                    >> `MEM (id,r.frml) (graphStatesWithId g')`
                     by metis_tac[GRAPH_STATES_WITH_ID_LEMM]
                    >> POP_ASSUM mp_tac >> simp[graphStatesWithId_def]
                    >> simp[MEM_MAP] >> rpt strip_tac
                    >> Cases_on `MEM y (toAList g'.nodeInfo)` >> fs[]
                    >> Cases_on `y` >> fs[] >> CCONTR_TAC >> rw[] >> fs[]
                    >> rw[] >> `r' = node` by metis_tac[MEM_toAList,SOME_11]
                    >> fs[]
                )
                >> Cases_on `l1 = []` >> fs[]
                >- (fs[updateNode_def,gfg_component_equality]
                     >> metis_tac[lookup_insert]
                   )
                >- (qabbrev_tac `addSingleEdge =
                      (λ(e:(α edgeLabelAA # num))
                        (g_opt:(α nodeLabelAA, α edgeLabelAA) gfg option).
                          do
                           g_int <- g_opt;
                           newGraph <- addEdge q e g_int;
                           SOME newGraph
                                od)`
                    >> `!ks G2. SOME G2 = (FOLDR addSingleEdge (SOME x'') ks)
                              ==>
                              (lookup id G2.nodeInfo
                                 = lookup id x''.nodeInfo)
                           ∧ (lookup id G2.followers
                                 = lookup id x''.followers)` by (
                         Induct_on `ks` >> fs[] >> strip_tac >> strip_tac
                         >> qunabbrev_tac `addSingleEdge` >> fs[]
                         >> strip_tac
                         >> first_x_assum (qspec_then `g_int` mp_tac) >> simp[]
                         >> rpt strip_tac >> Cases_on `h`
                         >- metis_tac[addEdge_preserves_nodeInfo]
                         >- (fs[addEdge_def,gfg_component_equality]
                            >> metis_tac[lookup_insert])
                     )
                    >> metis_tac[]
                   )
            )
           >> first_x_assum (qspec_then `trans_concr f'` mp_tac)
           >> simp[] >> strip_tac
           >- (`empty_followers addedNodesG x'` by (
                metis_tac[ADDFRML_EMPTYFLW_LEMM,empty_followers_def,nub_set,MEM]
                )
               >> fs[empty_followers_def]
               >> first_x_assum (qspec_then `id` mp_tac)
               >> strip_tac >> first_x_assum (qspec_then `node` mp_tac) >> fs[]
              )
           >- (`empty_followers g x'`
                 by metis_tac[ADDFRML_EMPTYFLW_LEMM,empty_followers_def]
               >> `?id1 n1. lookup id1 g.nodeInfo = SOME n1 ∧ n1.frml = x'` by (
                  `MEM x' (graphStates g)` by metis_tac[]
                  >> POP_ASSUM mp_tac >> PURE_REWRITE_TAC[graphStates_def]
                  >> simp[MEM_MAP] >> rpt strip_tac >> Cases_on `y` >> fs[]
                  >> metis_tac[MEM_toAList]
               )
               >> `lookup id1 addedNodesG.nodeInfo = SOME n1
                   ∧ lookup id1 addedNodesG.followers = lookup id1 g.followers`
                   by metis_tac[ADDFRML_FOLDR_LEMM,IS_SOME_DEF]
               >> `MEM (id,node.frml) (graphStatesWithId g')`
                   by metis_tac[GRAPH_STATES_WITH_ID_LEMM, MEM_toAList]
               >> `MEM (id1,node.frml) (graphStatesWithId g')`
                   by metis_tac[GRAPH_STATES_WITH_ID_LEMM, MEM_toAList]
               >> `id = id1` by metis_tac[unique_node_formula_def] >> rw[]
               >> metis_tac[SOME_11]
              )
           )
      >- (qunabbrev_tac `B4` >> fs[MEM_FILTER] >> fs[SET_EQ_SUBSET,SUBSET_DEF]
          >> Q.HO_MATCH_ABBREV_TAC `ALL_DISTINCT (D ++ fs)`
          >> `ALL_DISTINCT D ∧ ALL_DISTINCT fs ∧ ∀e. MEM e D ⇒ ¬MEM e fs`
             suffices_by metis_tac[ALL_DISTINCT_APPEND] >> rpt strip_tac
          >- metis_tac[FILTER_ALL_DISTINCT,all_distinct_nub]
          >- fs[]
          >- (qunabbrev_tac `D` >> fs[MEM_FILTER])
         )
          )
       )
   )
  );

val expandAuto_init_def = Define`
  expandAuto_init φ =
    let initForms = tempDNF_concr φ
    in let flat_initForms = nub (FLAT initForms)
    in let g1 = FOLDR (\s g. addFrmlToGraph g s) empty flat_initForms
    in let init_concr =
           MAP
            (λl. CAT_OPTIONS
                 (MAP
                  (OPTION_MAP FST o (\s. findNode (λ(_,l). l.frml = s) g1)) l))
            initForms
    in do g2 <- expandGraph g1 flat_initForms;
          SOME (concrAA g2 init_concr (props_concr φ))
          od`;

(* val EXPAUTO_INIT = store_thm *)
(*   ("EXPAUTO_INIT", *)
(*    ``!f g_AA init aP. *)
(*   (expandAuto_init f = SOME (concrAA g_AA init aP)) *)
(*   ==> (!i. MEM i init ==> ALL_DISTINCT i)``, *)
(*    rpt strip_tac >> fs[expandAuto_init_def] *)
(*    >> rw[] >> fs[MEM_MAP,CAT_OPTIONS_MEM] *)
(*    >> Q.HO_MATCH_ABBREV_TAC `ALL_DISTINCT (CAT_OPTIONS L)` *)
(*    >> `!ls:(num option) list. *)
(*           ALL_DISTINCT ls *)
(*           ==> ALL_DISTINCT (CAT_OPTIONS ls)` by ( *)
(*        Induct_on `ls` >> fs[CAT_OPTIONS_def] >> rpt strip_tac *)
(*        >> Cases_on `h` >> simp[CAT_OPTIONS_def] *)
(*        >> simp[CAT_OPTIONS_MEM] *)
(*    ) *)
(*    >> `ALL_DISTINCT L` suffices_by metis_tac[] *)
(*    >> qunabbrev_tac `L` *)
(*    >> Q.HO_MATCH_ABBREV_TAC `ALL_DISTINCT (MAP g l)` *)
(*    >> `!ls. MEM ls (tempDNF_concr f) *)
(*           ==> ALL_DISTINCT (MAP g ls)` by ( *)
(*        Induct_on `ls` >> fs[ALL_DISTINCT] >> rpt strip_tac *)
(*                  >- () *)

(* ) *)

(* ) *)


val EXP_WAA_CORRECT_LEMM = store_thm
  ("EXP_WAA_CORRECT_LEMM",
   ``!φ. case expandAuto_init φ of
          | NONE => F
          | SOME concrA =>
            concr2AbstrAA concrA = removeStatesSimpl (ltl2vwaa φ)``,
   rpt strip_tac >> Cases_on `expandAuto_init φ` >> fs[]
    >- (fs[expandAuto_init_def] >> POP_ASSUM mp_tac
        >> Q.HO_MATCH_ABBREV_TAC `(expandGraph G FS = NONE) ==> F`
        >> `wfg G
            ∧ (wfg G
                ==> (unique_node_formula G ∧ flws_sorted G
                  ∧ (!f. MEM f FS ==> MEM f (graphStates G))))`
             suffices_by metis_tac[EXP_GRAPH_WFG_AND_SOME,NOT_SOME_NONE]
        >> qunabbrev_tac `G` >> rpt strip_tac >> fs[]
        >- metis_tac[empty_is_wfg,ADDFRML_FOLDR_LEMM]
        >- metis_tac[UNIQUE_NODE_FORM_EMPTY,ADDFRML_FOLDR_LEMM,empty_is_wfg]
        >- metis_tac[FLWS_SORTED_EMPTY,ADDFRML_FOLDR_LEMM,empty_is_wfg]
        >- (Q.HO_MATCH_ABBREV_TAC `MEM f (graphStates G)`
            >> `set (graphStates G) = set FS ∪ {}`
                by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,GRAPHSTATES_EMPTY,
                             LIST_TO_SET,UNION_COMM]
            >> fs[]
           )
       )
    >- (rename [‘concr2AbstrAA x’] >> Cases_on `x` >> simp[concr2AbstrAA_def]
        >> simp[removeStatesSimpl_def,ltl2vwaa_def,ltl2vwaa_free_alph_def]
        >> Q.HO_MATCH_ABBREV_TAC `STATES ∧ INIT ∧ FINAL ∧ ALPH ∧ TRANS`
        >> `(INIT ==> STATES) ∧ INIT ∧ (STATES ==> FINAL) ∧ ALPH
           ∧ (ALPH ∧ STATES ==> TRANS)`
             suffices_by fs[]
        >> rpt strip_tac
        >- (qunabbrev_tac `STATES` >> qunabbrev_tac `INIT`
            >> qunabbrev_tac `TRANS` >> qunabbrev_tac `ALPH`
            >> qunabbrev_tac `FINAL`
            >> fs[expandAuto_init_def] >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
            >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
            >> Q.HO_MATCH_ABBREV_TAC
                 `expandGraph G0 (nub (FLAT (tempDNF_concr φ)))
                   = SOME g ==> A`
            >> qunabbrev_tac `A` >> strip_tac >> simp[SET_EQ_SUBSET]
            >> strip_tac >> strip_tac >> strip_tac >> strip_tac
            >- (simp[SUBSET_DEF,concr2Abstr_states_def] >> rpt strip_tac
               >> `!x. MEM x (nub (FLAT (tempDNF_concr φ)))
                   ==> x ∈ reachRelFromSet (ltl2vwaa φ) (set (graphStates G0))`
                     by (qunabbrev_tac `G0` >> rpt strip_tac
                         >> simp[reachRelFromSet_def] >> qexists_tac `x''`
                         >> simp[reachRel_def,RTC_REFL]
                         >> metis_tac[ADDFRML_FOLDR_LEMM,SUBSET_DEF,MEM,
                                      UNION_SUBSET,empty_is_wfg]
                        )
               >> `(∀x.
                    MEM x (graphStates G0) ⇒
                    x ∈ reachRelFromSet
                            (ltl2vwaa φ)
                            (BIGUNION (ltl2vwaa φ).initial))
                   ∧ (set (graphStates G0) = set (nub (FLAT (tempDNF_concr φ))))` by (
                     qunabbrev_tac `G0` >> simp[reachRelFromSet_def]
                     >> Q.HO_MATCH_ABBREV_TAC
                         `(!x. MEM x (graphStates G) ==> B x) ∧ C`
                     >> rpt strip_tac
                     >> simp[reachRelFromSet_def]
                    >- (rename [`MEM q _`]
                       >> qunabbrev_tac `G`
                       >> `MEM q (nub (FLAT (tempDNF_concr φ)))`
                             by metis_tac[ADDFRML_FOLDR_LEMM,SUBSET_DEF,MEM,
                                          UNION_SUBSET,empty_is_wfg,
                                          GRAPHSTATES_EMPTY]
                       >> qunabbrev_tac `B` >> rpt strip_tac >> fs[]
                       >> qexists_tac `q` >> simp[reachRel_def,RTC_REFL]
                       >> `?l. MEM l (tempDNF_concr φ) ∧ MEM q l`
                           by metis_tac[MEM_FLAT,nub_set,MEM]
                       >> `(set l') ∈ set (MAP set (tempDNF_concr φ))`
                           by (fs[MEM_MAP] >> metis_tac[])
                       >> `(set l') ∈ tempDNF φ`
                           by metis_tac[TEMPDNF_CONCR_LEMM]
                       >> qexists_tac `set l'`
                       >> fs[ltl2vwaa_def,ltl2vwaa_free_alph_def,initForms_def])
                    >- (qunabbrev_tac `C`
                        >> `set (graphStates (empty:(α nodeLabelAA, α edgeLabelAA) gfg))
                          ∪ set (nub (FLAT (tempDNF_concr φ)))
                                = set (graphStates G)`
                             by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg]
                        >> qunabbrev_tac `G`
                        >> fs[GRAPHSTATES_EMPTY,UNION_EMPTY]
                       )
                 )
               >> `set (graphStates G0) ⊆ tempSubForms φ` by (
                     simp[SUBSET_DEF] >> rpt strip_tac
                     >> fs[MEM_FLAT,nub_set,MEM]
                     >> `set l' ∈ tempDNF φ`
                        by metis_tac[MEM_MAP,TEMPDNF_CONCR_LEMM]
                     >> metis_tac[TEMPDNF_TEMPSUBF,SUBSET_DEF,MEM]
                 )
               >> `wfg G0` by (
                     qunabbrev_tac `G0` >> simp[]
                     >> metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg]
                 )
               >> `MEM x (graphStates g)` by (
                   simp[graphStates_def,MEM_MAP] >> qexists_tac `(n,x')`
                   >> simp[] >> metis_tac[MEM_toAList]
                 )
               >> `flws_sorted G0` by (
                     metis_tac[ADDFRML_FOLDR_LEMM,FLWS_SORTED_EMPTY,empty_is_wfg]
                 )
               >> `unique_node_formula G0` by (
                     metis_tac[ADDFRML_FOLDR_LEMM,UNIQUE_NODE_FORM_EMPTY,
                               empty_is_wfg]
                 )
               >> `!x. MEM x (nub (FLAT (tempDNF_concr φ)))
                       ==> MEM x (graphStates G0)` by (
                     rpt strip_tac
                     >> `set (graphStates G0)
                          = set (nub (FLAT (tempDNF_concr φ))) ∪ {}`
                         by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                                      GRAPHSTATES_EMPTY,LIST_TO_SET,UNION_COMM]
                     >> fs[]
                 )
               >> imp_res_tac EXP_GRAPH_REACHABLE
               >> fs[ltl2vwaa_def,ltl2vwaa_free_alph_def,initForms_def]
               >> rw[]
               )
            >- (simp[SUBSET_DEF] >> rpt strip_tac
                >> fs[reachRelFromSet_def,reachRel_def]
                >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                >> `!x' x. (oneStep
                             (ALTER_A (tempSubForms φ) (initForms φ) (finalForms φ)
                                      (POW (props φ))
                                      (trans (POW (props φ)))))^* x' x ⇒
                       (x' ∈ s ⇒
                        s ∈ initForms φ ⇒
                        x ∈ concr2Abstr_states g)` suffices_by metis_tac[]
                >> HO_MATCH_MP_TAC RTC_INDUCT_RIGHT1 >> rpt strip_tac
                 >- (rename[`q ∈ s`,`s ∈ initForms φ`]
                     >> `s ∈ concr2Abstr_init l g` by fs[SUBSET_DEF]
                     >> POP_ASSUM mp_tac >> simp[concr2Abstr_init_def,MEM_MAP]
                     >> rpt strip_tac
                     >> `?node. (node.frml = q)
                              ∧ (MEM node (CAT_OPTIONS
                                           (MAP (λn. lookup n g.nodeInfo) l')))`
                        by (rw[] >> fs[] >> metis_tac[])
                     >> rename[`MEM i l`,`concr2Abstr_init l g ⊆ initForms φ`]
                     >> `?nid. MEM nid i ∧ SOME node = lookup nid g.nodeInfo`
                          by (fs[CAT_OPTIONS_MAP_LEMM] >> metis_tac[])
                     >> simp[concr2Abstr_states_def] >> qexists_tac `node`
                     >> simp[] >> metis_tac[domain_lookup]
                    )
                 >- (rename[`q_0 ∈ s ==> s ∈ initForms φ ==> q_n ∈ _`,
                            `q_n' ∈ _ g`]
                     >> `!x. MEM x (graphStates G0)
                           ∧ ~ MEM x (nub (FLAT (tempDNF_concr φ)))
                           ==> (!y. oneStep (ltl2vwaa φ) x y
                                    ==> MEM y (graphStates G0))` by (
                          rpt strip_tac >> qunabbrev_tac `G0`
                          >> `MEM x' (nub (FLAT (tempDNF_concr φ)))` suffices_by fs[]
                          >> `x' ∈
                              (set (graphStates
                                     (empty:(α nodeLabelAA, α edgeLabelAA) gfg))
                              ∪ set (nub (FLAT (tempDNF_concr φ))))`
                              by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,MEM]
                          >> fs[] >> metis_tac[GRAPHSTATES_EMPTY,MEM]
                      )
                     >> `wfg G0` by (
                          qunabbrev_tac `G0`
                          >> metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg]
                      )
                     >> `!x. MEM x (nub (FLAT (tempDNF_concr φ)))
                           ==> x ∈ tempSubForms φ` by (
                          simp[MEM_FLAT,nub_set,MEM] >> rpt strip_tac
                          >> `MEM (set l') (MAP set (tempDNF_concr φ))` by (
                              simp[MEM_MAP] >> metis_tac[]
                          )
                          >> `set l' ∈ tempDNF φ`
                              by metis_tac[TEMPDNF_CONCR_LEMM]
                          >> `(set l') ⊆ tempSubForms φ`
                              by metis_tac[TEMPDNF_TEMPSUBF]
                          >> metis_tac[MEM,SUBSET_DEF]
                      )
                     >> `unique_node_formula G0` by (
                          qunabbrev_tac `G0`
                          >> metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                                       UNIQUE_NODE_FORM_EMPTY]
                      )
                     >> `flws_sorted G0` by (
                          metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                                    FLWS_SORTED_EMPTY]
                      )
                     >> `!x. MEM x (nub (FLAT (tempDNF_concr φ)))
                           ==> MEM x (graphStates G0)` by (
                          rpt strip_tac
                           >> `set (graphStates G0)
                               = set (nub (FLAT (tempDNF_concr φ))) ∪ {}`
                              by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                                           GRAPHSTATES_EMPTY,LIST_TO_SET,
                                           UNION_COMM]
                              >> fs[]
                      )
                     >> IMP_RES_TAC EXP_AUTO_ALL_REACHABLE
                     >> `MEM q_n (graphStates g)`
                           by metis_tac[MEM,GRAPHSTATES_CONCR_LEMM]
                     >> first_x_assum (qspec_then `q_n` mp_tac) >> simp[]
                     >> rpt strip_tac
                     >> first_x_assum (qspec_then `q_n'` mp_tac)
                     >> simp[ltl2vwaa_def,ltl2vwaa_free_alph_def]
                     >> metis_tac[GRAPHSTATES_CONCR_LEMM,MEM]
                    )
               )
           )
        >- (qunabbrev_tac `INIT` >> fs[expandAuto_init_def]
            >> simp[concr2Abstr_init_def, initForms_def]
            >> qabbrev_tac `P = λl.
               (λx.
                 MEM x
                 (CAT_OPTIONS
                   (MAP (λn. lookup n g.nodeInfo)
                     (CAT_OPTIONS
                       (MAP
                         (OPTION_MAP FST o
                         (λs.
                           findNode (λ(_,l). l.frml = s)
                           (FOLDR (λs g. addFrmlToGraph g s)
                                  (empty:(α nodeLabelAA, α edgeLabelAA) gfg)
                                  (nub (FLAT (tempDNF_concr φ)))))) l)))))`
            >> `!l f. MEM l (tempDNF_concr φ)
                  ==> ((?x. P l x ∧ (f = x.frml)) = MEM f l)` by (
                 rpt strip_tac
                 >> simp[EQ_IMP_THM] >> rpt strip_tac >> qunabbrev_tac `P`
                 >> fs[]
                  >- (IMP_RES_TAC CAT_OPTIONS_MAP_LEMM
                      >> rename[`SOME node = _ nid`]
                      >> IMP_RES_TAC CAT_OPTIONS_MAP_LEMM >> fs[]
                      >> `node.frml = x` by (
                           fs[findNode_def]
                           >> IMP_RES_TAC FIND_LEMM2 >> Cases_on `z`
                           >> fs[] >> rw[]
                           >> `SOME node = lookup nid g.nodeInfo` by fs[]
                           >> qabbrev_tac `
                                (g0:(α nodeLabelAA,α edgeLabelAA) gfg)
                                 = FOLDR (λs g. addFrmlToGraph g s) empty
                                           (nub (FLAT (tempDNF_concr φ)))`
                           >> `wfg g0`
                               by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg]
                           >> `unique_node_formula g0`
                               by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                                           UNIQUE_NODE_FORM_EMPTY]
                           >> `flws_sorted g0`
                               by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                                           FLWS_SORTED_EMPTY]
                           >> `!f. MEM f (nub (FLAT (tempDNF_concr φ)))
                                    ==> (MEM f (graphStates g0))` by (
                               `set (graphStates g0) =
                                 set (nub (FLAT (tempDNF_concr φ))) ∪ {}`
                               by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                                            GRAPHSTATES_EMPTY,LIST_TO_SET,
                                            UNION_COMM]
                                >> fs[]
                           )
                           >> `∃g2.
                                expandGraph g0 (nub (FLAT (tempDNF_concr φ)))
                                    = SOME g2
                                ∧ wfg g2
                                ∧ set (graphStates g0) ⊆ set (graphStates g2)
                                ∧ set (graphStatesWithId g0)
                                     ⊆ set (graphStatesWithId g2)`
                               by metis_tac[EXP_GRAPH_WFG_AND_SOME,empty_is_wfg]
                           >> `g = g2` by fs[] >> rw[] >> fs[MEM_toAList]
                           >> `MEM (nid,r.frml) (graphStatesWithId g0)` by (
                               metis_tac[MEM_toAList,GRAPH_STATES_WITH_ID_LEMM]
                           )
                           >> `MEM (nid,r.frml) (graphStatesWithId g)`
                              by fs[SUBSET_DEF]
                           >> POP_ASSUM mp_tac >> simp[graphStatesWithId_def,MEM_MAP]
                           >> rpt strip_tac >> Cases_on `y` >> fs[] >> rw[]
                           >> `node = r'` by metis_tac[MEM_toAList,SOME_11] >> fs[]
                       )
                      >> fs[]
                     )
                  >- (qabbrev_tac
                       `G = FOLDR (λs g. addFrmlToGraph g s)
                                  (empty:(α nodeLabelAA, α edgeLabelAA) gfg)
                                  (nub (FLAT (tempDNF_concr φ)))`
                      >> `MEM f (graphStates G)` by (
                          qunabbrev_tac `G`
                          >> `MEM f (nub (FLAT (tempDNF_concr φ)))`
                               by metis_tac[MEM_FLAT,nub_set,MEM]
                          >> metis_tac[UNION_SUBSET,SUBSET_DEF,MEM,
                                       ADDFRML_FOLDR_LEMM,empty_is_wfg,
                                       SET_EQ_SUBSET]
                      )
                      >> `wfg G` by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg]
                      >> `unique_node_formula G`
                           by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                                        UNIQUE_NODE_FORM_EMPTY]
                      >> `flws_sorted G`
                           by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                                        FLWS_SORTED_EMPTY]
                      >> `!f. MEM f (nub (FLAT (tempDNF_concr φ)))
                                  ==> (MEM f (graphStates G))` by (
                          `set (graphStates G) =
                             set (nub (FLAT (tempDNF_concr φ))) ∪ {}`
                          by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                                       GRAPHSTATES_EMPTY,LIST_TO_SET,
                                       UNION_COMM]
                          >> fs[]
                       )
                      >> `?g2. expandGraph G (nub (FLAT (tempDNF_concr φ)))
                                   = SOME g2
                             ∧ wfg g2
                             ∧ set (graphStates G) ⊆ set (graphStates g2)
                             ∧ set (graphStatesWithId G)
                                ⊆ set (graphStatesWithId g2)`
                         by metis_tac[EXP_GRAPH_WFG_AND_SOME]
                      >> `g = g2` by metis_tac[SOME_11] >> rw[]
                      >> simp[findNode_def]
                      >> `?z. FIND (λ(_,l). l.frml = f) (toAList G.nodeInfo)
                                = SOME z
                            ∧ ((λ(_,l). l.frml = f) z)` by (
                           HO_MATCH_MP_TAC FIND_LEMM
                           >> fs[graphStates_def,MEM_MAP]
                           >> qexists_tac `y` >> simp[]
                           >> Cases_on `y` >> simp[]
                       )
                      >> `MEM z (toAList G.nodeInfo)` by metis_tac[FIND_LEMM2]
                      >> Cases_on `z`
                      >> `MEM (q,r.frml) (graphStatesWithId G)`
                         by metis_tac[GRAPH_STATES_WITH_ID_LEMM]
                      >> `MEM (q,r.frml) (graphStatesWithId g)`
                         by fs[SUBSET_DEF]
                      >> POP_ASSUM mp_tac >> simp[graphStatesWithId_def,MEM_MAP]
                      >> rpt strip_tac >> Cases_on `y` >> qexists_tac `r'`
                      >> fs[CAT_OPTIONS_MAP_LEMM,CAT_OPTIONS_MEM] >> rw[]
                      >> qexists_tac `q` >> fs[] >> strip_tac
                      >- (qexists_tac `r.frml` >> fs[])
                      >- metis_tac[MEM_toAList]
                     )
             )
            >> simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
            >- (fs[MEM_MAP] >> rw[] >> fs[MEM_MAP]
                >> rw[] >> rename [‘MEM ll (tempDNF_concr φ)’]
                >> `{ f | ?x. P ll x ∧ f = x.frml} ∈ tempDNF φ` suffices_by (
                      `{ f | ?x. P ll x ∧ f = x.frml} = {x.frml | P ll x }`
                         by (simp[SET_EQ_SUBSET,SUBSET_DEF] >> rpt strip_tac
                             >> metis_tac[])
                       >> fs[])
                >> `set ll ∈ tempDNF φ` by (
                     `MEM (set ll) (MAP set (tempDNF_concr φ))` by (
                        fs[MEM_MAP] >> metis_tac[]
                     )
                     >> metis_tac[TEMPDNF_CONCR_LEMM]
                 )
                >> fs[]
               )
            >- (simp[MEM_MAP]
                >> `MEM x (MAP set (tempDNF_concr φ))`
                    by metis_tac[TEMPDNF_CONCR_LEMM,MEM]
                >> fs[MEM_MAP]
                >> qabbrev_tac `
                     Q = λl.
                         CAT_OPTIONS
                         (MAP (OPTION_MAP FST o
                           (λs.
                             findNode (λ(_,l). l.frml = s)
                             (FOLDR (λs g. addFrmlToGraph g s)
                                    (empty:(α nodeLabelAA, α edgeLabelAA) gfg)
                                    (nub (FLAT (tempDNF_concr φ)))))) l)`
                >> qexists_tac `Q y` >> rpt strip_tac >> fs[MEM_MAP]
                 >- (qunabbrev_tac `Q` >> simp[SET_EQ_SUBSET,SUBSET_DEF]
                     >> metis_tac[]
                    )
                 >- (metis_tac[MEM_MAP])
               )
           )
        >- (qunabbrev_tac `STATES` >> fs[expandAuto_init_def]
            >> qabbrev_tac `G0 =
                  (FOLDR (λf g. addFrmlToGraph g f)
                         (empty:(α nodeLabelAA,α edgeLabelAA) gfg)
                         (nub (FLAT (tempDNF_concr φ))))`
            >> qabbrev_tac `L = (nub (FLAT (tempDNF_concr φ)))`
            >> `wfg G0` by (
                 qunabbrev_tac `G0`
                 >> metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg]
             )
            >> `until_iff_final G0` by (
                 qunabbrev_tac `G0`
                 >> `until_iff_final (empty:(α nodeLabelAA, α edgeLabelAA) gfg)`
                     by (
                     simp[empty_def,until_iff_final_def] >> rpt strip_tac
                     >> metis_tac[lookup_def,NOT_SOME_NONE]
                 )
                 >> metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg]
             )
            >> `unique_node_formula G0`
                by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                             UNIQUE_NODE_FORM_EMPTY]
            >> `flws_sorted G0`
                by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                             FLWS_SORTED_EMPTY]
            >> `!f. MEM f (nub (FLAT (tempDNF_concr φ)))
                     ==> (MEM f (graphStates G0))` by (
                  `set (graphStates G0) =
                    set (nub (FLAT (tempDNF_concr φ))) ∪ {}`
                  by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                               GRAPHSTATES_EMPTY,LIST_TO_SET,
                               UNION_COMM]
                  >> fs[]
             )
            >> `∃g2.
                 expandGraph G0 L = SOME g2 ∧ wfg g2
               ∧ set (graphStates G0) ⊆ set (graphStates g2)
               ∧ set (graphStatesWithId G0)
                  ⊆ set (graphStatesWithId g2)
               ∧ (until_iff_final G0 ⇒ until_iff_final g2)`
                by metis_tac[EXP_GRAPH_WFG_AND_SOME]
            >> `g = g2` by metis_tac[SOME_11] >> rw[]
            >> qunabbrev_tac `FINAL`
            >> simp[finalForms_def, concr2Abstr_final_def]
            >> simp[SET_EQ_SUBSET,SUBSET_DEF]
            >> `until_iff_final g` by fs[]
            >> rpt strip_tac
             >- (`?f1 f2. x'.frml = U f1 f2` by metis_tac[until_iff_final_def]
                 >> qexists_tac `f1` >> qexists_tac `f2` >> simp[]
                 >> `MEM x'.frml (graphStates g)` by (
                      simp[graphStates_def,MEM_MAP] >> qexists_tac `(n,x')`
                      >> simp[] >> metis_tac[MEM_toAList]
                 )
                 >> `x'.frml ∈ concr2Abstr_states g`
                     by metis_tac[GRAPHSTATES_CONCR_LEMM]
                 >> metis_tac[SET_EQ_SUBSET,SUBSET_DEF,IN_INTER]
                )
             >- (`MEM x (graphStates g)` by (
                     simp[graphStates_def,MEM_MAP]
                     >> qexists_tac `(n,x')` >> simp[] >> metis_tac[MEM_toAList]
                 )
                 >> `x ∈ concr2Abstr_states g`
                    by metis_tac[GRAPHSTATES_CONCR_LEMM]
                 >> fs[finalForms_def] >> rw[] >> fs[SET_EQ_SUBSET,SUBSET_DEF]
                )
             >- (fs[finalForms_def] >> rw[]
                 >> `U f1 f2 ∈ concr2Abstr_states g` by metis_tac[IN_INTER]
                 >> `MEM (U f1 f2) (graphStates g)`
                     by metis_tac[GRAPHSTATES_CONCR_LEMM]
                 >> fs[graphStates_def,MEM_MAP,until_iff_final_def]
                 >> qexists_tac `SND y` >> simp[]
                 >> Cases_on `y` >> fs[MEM_toAList]
                 >> metis_tac[domain_lookup]
                )
           )
        >- (qunabbrev_tac `ALPH` >> fs[expandAuto_init_def]
            >> metis_tac[PROPS_CONCR_LEMM]
           )
        >- (qunabbrev_tac `TRANS` >> qunabbrev_tac `STATES`
            >> qunabbrev_tac `ALPH`
            >> fs[expandAuto_init_def]
            >> qabbrev_tac `G0 =
                (FOLDR (λf g. addFrmlToGraph g f)
                     (empty:(α nodeLabelAA,α edgeLabelAA) gfg)
                     (nub (FLAT (tempDNF_concr φ))))`
            >> `wfg G0` by (
                 qunabbrev_tac `G0`
                 >> metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg]
             )
            >> `unique_node_formula G0`
                 by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                              UNIQUE_NODE_FORM_EMPTY]
            >> `flws_sorted G0`
                 by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                              FLWS_SORTED_EMPTY]
            >> `!f. MEM f (nub (FLAT (tempDNF_concr φ)))
                        = (MEM f (graphStates G0))` by (
                  `set (graphStates G0) =
                   set (nub (FLAT (tempDNF_concr φ))) ∪ {}`
                by metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg,
                             GRAPHSTATES_EMPTY,LIST_TO_SET,
                             UNION_COMM]
                >> fs[]
             )
            >> `(∀x.
                MEM x (graphStates G0) ∧ ¬MEM x (nub (FLAT (tempDNF_concr φ)))
                ==> ∀y. concrTrans G0 (props φ) x = trans (POW (props φ)) x)`
                by (rpt strip_tac >> metis_tac[])
            >> `ALL_DISTINCT (nub (FLAT (tempDNF_concr φ)))`
                by metis_tac[all_distinct_nub]
            >> `!x. MEM x (nub (FLAT (tempDNF_concr φ)))
                        ==> empty_followers G0 x` by (
                 rpt strip_tac
                 >> `empty_followers
                      (empty:(α nodeLabelAA, α edgeLabelAA) gfg) x` suffices_by (
                     qunabbrev_tac `G0` >> strip_tac
                     >> HO_MATCH_MP_TAC ADDFRML_EMPTYFLW_LEMM
                     >> fs[empty_is_wfg] >> disj2_tac >> fs[]
                 )
                 >> fs[GRAPHSTATES_EMPTY,LIST_TO_SET,EMPTY_FLWS_GRAPHSTATES]
             )
            >> `!f. MEM f (nub (FLAT (tempDNF_concr φ)))
                  ==> (MEM f (graphStates G0))` by fs[]
            >> qabbrev_tac `L = (nub (FLAT (tempDNF_concr φ)))`
            >> `!x. MEM x (nub (FLAT (tempDNF_concr φ)))
                        ==> x ∈ tempSubForms φ` by (
                   simp[MEM_FLAT,nub_set,MEM] >> rpt strip_tac
                   >> `MEM (set l') (MAP set (tempDNF_concr φ))` by (
                   simp[MEM_MAP] >> metis_tac[]
                 )
                 >> `set l' ∈ tempDNF φ`
                     by metis_tac[TEMPDNF_CONCR_LEMM]
                 >> `(set l') ⊆ tempSubForms φ`
                     by metis_tac[TEMPDNF_TEMPSUBF]
                 >> metis_tac[MEM,SUBSET_DEF]
             )
            >> `∀x.
                MEM x (graphStates g) ⇒
                ∀y. concrTrans g (props φ) x = trans (POW (props φ)) x`
               by metis_tac[EXP_GRAPH_TRANS_LEMM]
            >> Q.HO_MATCH_ABBREV_TAC `concrTrans g (set l0) = (λq. M q)`
            >> `!q. concrTrans g (set l0) q = M q` suffices_by metis_tac[]
            >> strip_tac
            >> Cases_on `MEM q (graphStates g)`
            >- (qunabbrev_tac `M` >> fs[] >> rw[]
               >- metis_tac[PROPS_CONCR_LEMM]
               >- (`q ∈ (concr2Abstr_states g)` by (
                     PURE_REWRITE_TAC[concr2Abstr_states_def]
                     >> simp[] >> POP_ASSUM mp_tac >> POP_ASSUM mp_tac
                     >> simp[graphStates_def,MEM_MAP] >> strip_tac
                     >> strip_tac >> Cases_on `y` >> qexists_tac `r`
                     >> fs[] >> metis_tac[MEM_toAList,domain_lookup]
                   )
                  >> `F` suffices_by metis_tac[]
                  >> fs[SET_EQ_SUBSET,SUBSET_DEF,IN_INTER] >> metis_tac[]
                  )
               )
            >- (qunabbrev_tac `M` >> fs[] >> simp[concrTrans_def]
                >> `extractTrans g q = {}`
                    by metis_tac[EMPTY_FLWS_GRAPHSTATES,EMPTY_FLWS_LEMM]
                >> rw[]
                >> `q ∈ (concr2Abstr_states g)` by (
                    POP_ASSUM mp_tac
                    >> Q.HO_MATCH_ABBREV_TAC `q ∈ B ==> q ∈ concr2Abstr_states g`
                    >> metis_tac[IN_INTER,SET_EQ_SUBSET,SUBSET_DEF]
                 )
                >> `F` suffices_by fs[]
                >> fs[concr2Abstr_states_def,graphStates_def,MEM_MAP]
                >> `MEM (n,x) (toAList g.nodeInfo)` by metis_tac[MEM_toAList]
                >> `(SND (n,x)).frml = q` by fs[] >> metis_tac[]
               )
           )
       )
  );

val EXP_WAA_CORRECT = store_thm
  ("EXP_WAA_CORRECT",
   ``!φ. ?concrA.
     (expandAuto_init φ = SOME concrA)
     ∧ (concr2AbstrAA concrA = removeStatesSimpl (ltl2vwaa φ))``,
   rpt strip_tac
   >> `case expandAuto_init φ of
             NONE => F
           | SOME concrA =>
              concr2AbstrAA concrA = removeStatesSimpl (ltl2vwaa φ)`
        by metis_tac[EXP_WAA_CORRECT_LEMM]
   >> Cases_on `expandAuto_init φ` >> fs[]
  );

val EXP_WAA_AP = store_thm
  ("EXP_WAA_AP",
   ``!f g_AA init aP.
      (expandAuto_init f = SOME (concrAA g_AA init aP))
      ==>
      ((∀id fls.
      (id ∈ domain g_AA.nodeInfo) ∧ (lookup id g_AA.followers = SOME fls)
      ⇒
      ∀e.
      MEM e (MAP FST fls) ⇒
      (MEM_SUBSET e.pos_lab aP ∧ MEM_SUBSET e.neg_lab aP))
   ∧ (!id nL.
        (lookup id g_AA.nodeInfo = SOME nL)
        ==> (!e. MEM e nL.true_labels
                 ==> MEM_SUBSET e.pos_lab aP ∧ MEM_SUBSET e.neg_lab aP
            )
      ))``,
   rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
   >> gen_tac >> strip_tac
   >> `!φ. case expandAuto_init φ of
             | NONE => F
             | SOME concrA =>
               concr2AbstrAA concrA = removeStatesSimpl (ltl2vwaa φ)`
      by metis_tac[EXP_WAA_CORRECT_LEMM]
   >> first_x_assum (qspec_then `f` mp_tac) >> simp[] >> strip_tac
   >> `set aP = props f` by (
       fs[ltl2vwaa_def,ltl2vwaa_free_alph_def,removeStatesSimpl_def]
         >> fs[concr2AbstrAA_def] >> metis_tac[POW_11]
   )
   >> fs[expandAuto_init_def]
   >> qabbrev_tac `FS = nub (FLAT (tempDNF_concr f))`
   >> qabbrev_tac `G1 = FOLDR (λs g. addFrmlToGraph g s)
                              (empty:(α nodeLabelAA, α edgeLabelAA) gfg)
                              FS`
   >> `(∀f. MEM f FS ⇒ props f ⊆ set aP)` by (
       qunabbrev_tac `FS` >> rpt strip_tac >> rename[`props f1 ⊆ set aP`]
       >> `?m. MEM f1 m ∧ MEM m (tempDNF_concr f)`
           by metis_tac[nub_set,MEM_FLAT]
       >> `set m ∈ tempDNF f` by metis_tac[MEM_MAP,TEMPDNF_CONCR_LEMM]
       >> `set m ⊆ tempSubForms f` by metis_tac[TEMPDNF_TEMPSUBF]
       >> simp[props_def,SUBSET_DEF] >> rpt strip_tac
       >> metis_tac[SUBSET_DEF,TSF_IMPL_SF,SUBFORMS_TRANS]
   )
   >> `!ls G. (FOLDR (λs g. addFrmlToGraph g s)
                     (empty:(α nodeLabelAA, α edgeLabelAA) gfg)
                     ls = G)
            ==> (!id nL. (lookup id G.nodeInfo = SOME nL)
                      ==> ((lookup id G.followers = SOME [])
                         ∧ (nL.true_labels = []))
                )` by (
       Induct_on `ls`
       >- (rpt strip_tac >> fs[empty_def,gfg_component_equality]
           >> `id ∈ {}` by metis_tac[domain_lookup,domain_def]
           >> fs[]
          )
       >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> fs[]
           >> qabbrev_tac `G_int = FOLDR (λs g. addFrmlToGraph g s)
                                      (empty:(α nodeLabelAA, α edgeLabelAA) gfg)
                                      ls`
           >> `id ∈ domain G.nodeInfo` by metis_tac[domain_lookup]
           >> rename[`id ∈ domain G.nodeInfo`]
           >> Cases_on `id ∈ domain G_int.nodeInfo`
           >- (`IS_SOME (lookup id G_int.nodeInfo)`
                 by metis_tac[IS_SOME_DEF,domain_lookup]
               >> `wfg G_int` by (
                   qunabbrev_tac `G_int`
                   >> metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg]
               )
               >> metis_tac[ADDFRML_LEMM2]
              )
           >- (`wfg G_int` by (
                  qunabbrev_tac `G_int`
                  >> metis_tac[ADDFRML_FOLDR_LEMM,empty_is_wfg]
                )
                >> `wfg G` by metis_tac[ADDFRML_WFG]
                >> `id = G_int.next` by (
                   `~(G.next <= id)` by metis_tac[wfg_def]
                   >> `domain G.nodeInfo =
                         G_int.next INSERT domain G_int.nodeInfo` by (
                       Cases_on
                        `~(MEM h (MAP ((λl. l.frml) ∘ SND)
                             (toAList G_int.nodeInfo)))`
                       >> Cases_on `h`
                       >> fs[addFrmlToGraph_def,gfg_component_equality]
                       >> fs[addNode_def] >> metis_tac[domain_insert]
                   )
                   >> rw[] >> fs[IN_INSERT]
                )
                >> Cases_on
                     `~(MEM h (MAP ((λl. l.frml) ∘ SND)
                       (toAList G_int.nodeInfo)))`
                >> Cases_on `h` >> fs[addFrmlToGraph_def]
                >> fs[addNode_def,gfg_component_equality,lookup_insert]
                >> `!b l. (<|frml := l;
                           is_final := b;
                           true_labels := []|>).true_labels = []` by fs[]
                >> metis_tac[lookup_insert,SOME_11]
              )
          )
   )
   >> `(∀id fls.
         (id ∈ domain g_AA.nodeInfo) ∧ (lookup id g_AA.followers = SOME fls) ⇒
         ∀e.
         MEM e (MAP FST fls) ⇒
         (MEM_SUBSET e.pos_lab aP ∧ MEM_SUBSET e.neg_lab aP))
     ∧ (∀id nL.
         (lookup id g_AA.nodeInfo = SOME nL)
         ⇒ ∀e.
         MEM e nL.true_labels ⇒
         MEM_SUBSET e.pos_lab aP ∧ MEM_SUBSET e.neg_lab aP)
    ` by (
       HO_MATCH_MP_TAC EXP_GRAPH_AP
       >> qexists_tac `G1` >> qexists_tac `FS` >> simp[]
       >> `wfg G1` by metis_tac[empty_is_wfg,ADDFRML_FOLDR_LEMM]
       >> simp[] >> rpt strip_tac
       >> first_x_assum (qspec_then `FS` mp_tac) >> rpt strip_tac
       >> first_x_assum (qspec_then `G1` mp_tac) >> simp[]
       >> strip_tac >> first_x_assum (qspec_then `id` mp_tac)
       >> simp[] >> strip_tac >> fs[]
       >> `?nL.lookup id G1.nodeInfo = SOME nL` by metis_tac[domain_lookup]
       >> first_x_assum (qspec_then `nL` mp_tac) >> simp[]
       >> rpt strip_tac >> fs[MEM_MAP]
   )
   >> metis_tac[]
  );


val _ = export_theory();
