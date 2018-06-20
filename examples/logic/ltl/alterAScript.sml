open HolKernel Parse boolLib bossLib pred_setTheory arithmeticTheory relationTheory set_relationTheory pairTheory

open generalHelpersTheory wordTheory

val _ = new_theory "alterA"

val _ = Datatype
  `ALTER_A = <| states      : 's set;
               alphabet     : 'a set;
               trans        : 's -> (('a set # 's set) set);
               initial      : ('s set) set;
               final        : 's set
               |>`;

val isValidAlterA_def =
    Define `isValidAlterA (A: ('s,'a) ALTER_A) =
             (A.initial ⊆ POW A.states)
          /\ (A.final ⊆ A.states)
          /\ (!s a d. (s ∈ A.states) /\ ((a, d) ∈ (A.trans s))
                 ==> (d ⊆ A.states ∧ a ⊆ A.alphabet))`;

(* An alternating automata is very weak if there is a partial order po on
   the states s.t. for every state s all states appearing in trans(s)
   are lower or equal to s
*)

val isVeryWeakWithOrder_def = Define
   `isVeryWeakWithOrder A ord =
      partial_order ord A.states
      /\ !s a d. (s ∈ A.states) /\ ((a,d) ∈ (A.trans s))
                   ==> (!s'. (s' ∈ d) ==> ((s',s) ∈ ord))`;

val isVeryWeakAlterA_def =
    Define `isVeryWeakAlterA A = ?ord. isVeryWeakWithOrder A ord`;

val FINITE_LEMM = store_thm
  ("FINITE_LEMM",
  ``!aut. FINITE aut.alphabet ∧ FINITE aut.states ∧ isValidAlterA aut
       ==> (!q. q ∈ aut.states ==> FINITE (aut.trans q))``,
  rpt strip_tac
  >> `aut.trans q ⊆ ((POW aut.alphabet) × (POW aut.states))` by (
      fs[isValidAlterA_def] >> simp[SUBSET_DEF] >> rpt strip_tac
        >- (Cases_on `x` >> metis_tac[IN_POW,FST])
        >- (Cases_on `x` >> metis_tac[IN_POW,SND])
  )
  >> metis_tac[FINITE_CROSS, FINITE_POW,PSUBSET_DEF,PSUBSET_FINITE]
  );

(*
   RUNs over the alternating automaton
*)

val _ = Hol_datatype
   `ALTERA_RUN = <| V : num -> 's set;
                    E : (num # 's) -> 's set
                                         |>`;

(*
  validity condition for runs over a given word
*)

val validAARunFor_def = Define
`validAARunFor aut run word =
             (run.V 0 ∈ aut.initial)
             /\ (!i. run.V i ⊆ aut.states)
             /\ (!i q. (q ∈ run.V i)
                           ==> ?a. (a,run.E (i,q)) ∈ aut.trans q /\ (at word i ∈ a))
             /\ (!i q. run.E (i,q) ⊆ run.V (i+1))
             /\ (!i q. (q ∈ run.V i)
                    ==> ((i = 0) \/ ?q'. (q ∈ run.E (i-1,q')) /\ (q' ∈ run.V (i-1))))`;


(*
  infinite branches of the run
*)

val infBranchOf_def = Define
  `infBranchOf run b = (b 0 ∈ run.V 0) /\ !i. (b (i+1) ∈ run.E (i, b i))`;

val branchFixP_def = Define
`branchFixP b x = ?i. (b i = x) /\ !m. (m >= i) ==> (b m = x)`;

val branchRange_def = Define
`branchRange b = { x | ?i. b i = x }`

val BRANCH_V_LEMM = store_thm
  ("BRANCH_V_LEMM",
  ``!run b aut w. validAARunFor aut run w /\ infBranchOf run b
        ==> !i. (b i ∈ run.V i)``,
   rpt gen_tac >> strip_tac >> Induct_on `i` >> fs[infBranchOf_def]
   >> `SUC i = (i+1)` by simp[]
   >> `b (i+1) ∈ run.E (i, b i)` by metis_tac[]
   >> fs[validAARunFor_def]
   >> `run.E (i, b i) ⊆ run.V (i+1)` by metis_tac[]
   >> `SUC i = (i+1)` by simp[] >> metis_tac[SUBSET_DEF]
  );

val BRANCHRANGE_LEMM = store_thm
  ("BRANCHRANGE_LEMM",
  ``!b aut run w. validAARunFor aut run w /\ infBranchOf run b
                                        ==> (branchRange b ⊆ aut.states)``,
    rpt strip_tac
    >> `!i. (b i ∈ run.V i)` by metis_tac[BRANCH_V_LEMM]
    >> fs[validAARunFor_def, branchRange_def, SUBSET_DEF] >> rpt strip_tac
    >> metis_tac[]
  );

val BRANCHRANGE_NONEMPTY = store_thm
  ("BRANCHRANGE_NONEMPTY",
   ``!b run. infBranchOf run b ==> ~(branchRange b = {})``,
    rpt strip_tac
    >> `~(?x. x ∈ branchRange b)` by metis_tac[MEMBER_NOT_EMPTY]
    >> fs[]
    >> `?x. x ∈ branchRange b` suffices_by metis_tac[]
    >> qexists_tac `b 0` >> fs[branchRange_def]
  );

(*
  acceptance condition for a run over a given automaton (CO-BÜCHI condition)
*)

val acceptingAARun_def = Define
`acceptingAARun aut run =
    !b. infBranchOf run b ==> FINITE {i | b i ∈ aut.final }`

(*
  the language of the automaton
*)

val runForAA_def = Define
`runForAA aut run word =
             validAARunFor aut run word /\ acceptingAARun aut run`;

val alterA_lang_def = Define
`alterA_lang aut = { w | ?run. runForAA aut run w
                       /\ (word_range w ⊆ aut.alphabet) }`;

(*
  Some properties of weak alternating automata
*)

val BRANCH_WAA_LEMM = store_thm
  ("BRANCH_WAA_LEMM",
  ``!b run aut w ord. validAARunFor aut run w /\ infBranchOf run b
                      /\ isVeryWeakWithOrder aut ord
            ==> !i. (b (i+1), b i) ∈ ord``,
   rpt strip_tac
   >> `!i. b i ∈ run.V i` by metis_tac[BRANCH_V_LEMM]
   >> fs[isVeryWeakWithOrder_def, infBranchOf_def, validAARunFor_def]
   >> `(b (i + 1) ∈ run.V (i+1)) /\ (b i ∈ run.V i)` by metis_tac[]
   >> `b (i + 1) ∈ run.E(i, b i)` by metis_tac[]
   >> `∃a. (a,run.E (i,b i)) ∈ aut.trans (b i)` by metis_tac[]
   >> `b i ∈ aut.states` by metis_tac[SUBSET_DEF]
   >> `∀s'. (s' ∈ run.E (i, b i)) ⇒ (s',b i) ∈ ord` by metis_tac[]
   >> metis_tac[]
  );

val BRANCH_LIN_ORD = store_thm
  ("BRANCH_LIN_ORD",
   ``!b run aut w ord. infBranchOf run b /\ validAARunFor aut run w
                     /\ isVeryWeakWithOrder aut ord
      ==> linear_order (rrestrict ord (branchRange b)) (branchRange b)``,
   rpt strip_tac
   >> `!i. b i ∈ run.V i` by metis_tac[BRANCH_V_LEMM]
   >> `!i. (b (i+1), b i) ∈ ord` by metis_tac[BRANCH_WAA_LEMM]
   >> fs[linear_order_def, branchRange_def, infBranchOf_def, validAARunFor_def]
   >> fs[isVeryWeakWithOrder_def]
   >> fs[domain_def, partial_order_def,range_def, in_rrestrict,SUBSET_DEF,branchRange_def]
   >> rpt strip_tac
     >- (qexists_tac `i` >> fs[])
     >- (qexists_tac `i'` >> fs[])
     >- metis_tac[RRESTRICT_TRANS]
     >- metis_tac[RRESTRICT_ANTISYM]
     >- (`(x,y) ∈ ord \/ (y,x) ∈ ord` suffices_by metis_tac[]
         >> Cases_on `i > i'`
           >- (`!n. (n > i') ==> ((b n,y) ∈ ord)` suffices_by metis_tac[]
               >> Induct_on `n` >> fs[] >> rpt strip_tac
               >> Cases_on `n = i'` >> fs[reflexive_def]
                  >- (`SUC i' = i' + 1` by simp[]
                      >> `(b (i'+1), b i') ∈ ord` suffices_by metis_tac[]
                      >> metis_tac[]
                      )
                  >- (`(b (SUC n), b n) ∈ ord` suffices_by metis_tac[transitive_def]
                      >> `SUC n = n + 1` by simp[]
                      >> `(b (n+1), b n) ∈ ord` suffices_by metis_tac[] >> metis_tac[])
              )
           >- (Cases_on `i = i'` >> fs[reflexive_def]
               >- (`b  i' ∈ run.V i'` by metis_tac[]
                   >> `b i' ∈ aut.states` by metis_tac[] >> metis_tac[])
               >- (`i' > i` by simp[]
               >> `!n. (n > i) ==> ((b n,x) ∈ ord)` suffices_by metis_tac[]
               >> Induct_on `n` >> fs[] >> rpt strip_tac
               >> Cases_on `n = i` >> fs[reflexive_def]
                  >- (`SUC i = i + 1` by simp[]
                      >> `(b (i+1), b i) ∈ ord` suffices_by metis_tac[] >> metis_tac[]
                      )
                  >- (`(b (SUC n), b n) ∈ ord` suffices_by metis_tac[transitive_def]
                      >> `SUC n = n + 1` by simp[]
                      >> `(b (n + 1), b n) ∈ ord` suffices_by metis_tac[] >> metis_tac[])
                  )
              )
        )
  );

val BRANCH_FIXP = store_thm
  ("BRANCH_FIXP",
    ``∀b run aut w ord.
      infBranchOf run b ∧ validAARunFor aut run w ∧ isVeryWeakAlterA aut /\ FINITE aut.states ⇒
              ∃x. branchFixP b x``,
    `∀b run aut w ord.
     infBranchOf run b ∧ validAARunFor aut run w ∧ isVeryWeakWithOrder aut ord
                  /\ FINITE aut.states ⇒
     ∃x. branchFixP b x` suffices_by metis_tac[isVeryWeakAlterA_def]
   >> rpt strip_tac
   >> `linear_order (rrestrict ord (branchRange b)) (branchRange b)`
       by metis_tac[BRANCH_LIN_ORD]
   >> qabbrev_tac `ord' = rrestrict ord (branchRange b)`
   >> `FINITE (branchRange b)` by metis_tac[BRANCHRANGE_LEMM,SUBSET_FINITE]
   >> `~(branchRange b = {})` by metis_tac[BRANCHRANGE_NONEMPTY]
   >> `∃x. x ∈ minimal_elements (branchRange b) ord'`
       by metis_tac[finite_linear_order_has_minimal]
   >> qexists_tac `x`
   >> fs[minimal_elements_def, branchFixP_def, branchRange_def]
   >> qexists_tac `i` >> fs[] >> rpt strip_tac
   >> fs[linear_order_def]
   >> `!n. (n >= i) ==> (b n = x)` suffices_by metis_tac[]
   >> Induct_on `n`
     >- (Cases_on `i = 0` >> fs[])
     >- (rpt strip_tac
         >> Cases_on `SUC n = i` >> fs[]
         >> `n >= i` by simp[] >> fs[]
         >> `b (SUC n) = b n` suffices_by metis_tac[]
         >> `(b (SUC n),b n) ∈ ord' ∨ (b n,b (SUC n)) ∈ ord'` by metis_tac[]
           >- metis_tac[]
           >- (`SUC n = n + 1` by simp[]
               >> `(b n, b (n+1)) ∈ ord'` by metis_tac[]
               >> `(b (n+1), b n) ∈ ord` by metis_tac[BRANCH_WAA_LEMM]
               >> `(b (n+1),b n) ∈ ord'` suffices_by metis_tac[antisym_def]
               >> metis_tac[in_rrestrict]
              )
        )
  );

val BRANCH_ACC_LEMM = store_thm
  ("BRANCH_ACC_LEMM",
   ``!run w aut. validAARunFor aut run w /\ isVeryWeakAlterA aut
                      /\ FINITE aut.states
        ==> (acceptingAARun aut run =
            (!b x. infBranchOf run b /\ branchFixP b x ==> ~(x ∈ aut.final)))``,
   rpt strip_tac >> rw[EQ_IMP_THM]
      >- (CCONTR_TAC >> fs[acceptingAARun_def, branchFixP_def]
          >> `FINITE {i | b i ∈ aut.final}` by metis_tac[]
          >> `INFINITE 𝕌(:num)` by metis_tac[INFINITE_NUM_UNIV]
          >> `!x y. ((\x. x+i) x = (\x. x+i) y) ==> (x = y)`
               by metis_tac[ADD_N_INJ_LEMM]
          >> `INFINITE (IMAGE (\x. x+i) 𝕌(:num))` by rw[IMAGE_11_INFINITE]
          >> `INFINITE { x | x >= i }` by metis_tac[ADD_N_IMAGE_LEMM]
          >> `!m. (m ∈ { x | x >= i }) ==> (b m = x)` by simp[]
          >> `{ x | x >= i } ⊆ { m | b m = x }` by simp[SUBSET_DEF]
          >> `{ x | x >= i } ⊆ { i | b i ∈ aut.final }` by simp[SUBSET_DEF]
          >> `{ x | x >= i } ⊆ { i | b i ∈ aut.final }` by simp[]
          >> metis_tac[IN_INFINITE_NOT_FINITE,SUBSET_DEF]
         )
      >- (simp[acceptingAARun_def] >> rpt strip_tac
          >> `∃x. branchFixP b x` by metis_tac[BRANCH_FIXP]
          >> `~(x ∈ aut.final)` by metis_tac[]
          >> fs[branchFixP_def]
          >> `{i | b i ∈ aut.final} ⊆ (count i)`
              suffices_by metis_tac[FINITE_COUNT,SUBSET_FINITE]
          >> fs[SUBSET_DEF] >> rpt strip_tac
          >> CCONTR_TAC >> `x' >= i` by simp[] >> metis_tac[]
         )
  );

(*
  infinite run suffixes
*)

val infBranchSuffOf_def = Define
  `infBranchSuffOf run i b =
             (b 0 ∈ run.V i) /\ !j. (b (j+1) ∈ run.E (j + i, b j))`;

val appendToBranchSuff_def = Define
  `appendToBranchSuff b q = \n. if n = 0 then q else b (n-1)`;

val APPEND_LEMMA = store_thm
  ("APPEND_LEMMA",
   ``!r b q i aut w. infBranchSuffOf r i b /\ validAARunFor aut r w /\ ~(i=0)
                  /\ q ∈ r.V (i-1) /\ (b 0 ∈ r.E (i-1,q))
        ==> infBranchSuffOf r (i-1) (appendToBranchSuff b q)``,
   rpt strip_tac >> fs[appendToBranchSuff_def, infBranchSuffOf_def, validAARunFor_def]
   >> rpt strip_tac
   >> Induct_on `j` >> fs[]
   >> `b (j + 1) ∈ r.E (i + j,b j)` by metis_tac[]
   >> `SUC j = j + 1` by simp[] >> rw[]
  );

val BRANCH_SUFF_LEMM = store_thm
  ("BRANCH_SUFF_LEMM",
   ``!i q run aut w b. validAARunFor aut run w /\ infBranchSuffOf run i b
         ==> ?b'. infBranchOf run b' /\ !j. (b j = b' (j+i))``,
   Induct_on `i` >> rpt strip_tac
     >- (qexists_tac `b`
         >> fs[infBranchSuffOf_def, infBranchOf_def])
     >- (`!q. ~(SUC i = 0) /\ q ∈ run.V ((SUC i) − 1) ∧ b 0 ∈ run.E ((SUC i) − 1,q) ⇒
           infBranchSuffOf run ((SUC i) − 1) (appendToBranchSuff b q)`
         by metis_tac[APPEND_LEMMA]
         >> `!b. infBranchSuffOf run i b
           ⇒ ∃b'. infBranchOf run b' ∧ ∀j. (b j = b' (j + i))`
         by metis_tac[]
         >> fs[validAARunFor_def, infBranchSuffOf_def] >> rpt strip_tac
         >> `((SUC i) = 0) ∨ ∃q'. b 0 ∈ run.E ((SUC i) − 1,q')
            ∧ (q' ∈ run.V ((SUC i) − 1))`
            by metis_tac[]
         >> fs[]
         >> `appendToBranchSuff b q' 0 ∈ run.V i ∧
             ∀j.
               appendToBranchSuff b q' (j + 1) ∈
               run.E (i + j,appendToBranchSuff b q' j)`
             by metis_tac[]
         >> qabbrev_tac `b_new = appendToBranchSuff b q'`
         >> `∃b'. infBranchOf run b' ∧ ∀j. (b_new j = b' (i + j))`
             by metis_tac[]
         >> qexists_tac `b'` >> fs[appendToBranchSuff_def]
         >> rpt strip_tac
         >> `SUC i <= j ==> i <= (SUC j)` by simp[]
         >> `(b_new (SUC j) = b' (i + (SUC j)))` by metis_tac[]
         >> fs[]
         >> `~(SUC j = 0) ==> (b_new (SUC j) = b (SUC j - 1))` by metis_tac[]
         >> fs[]
         >> `(i + SUC j) = (j + SUC i)` by simp[]
         >> metis_tac[]
       )
  );

(* reachable states *)

val oneStep_def = Define`
  oneStep aut = \x y. ?a qs. (a,qs) ∈ aut.trans x ∧ y ∈ qs ∧ x ∈ aut.states`;

val reachRel_def = Define`
  reachRel aut = (oneStep aut)^*`;

val reachRelFromSet_def = Define`
  reachRelFromSet aut s = { y | ?x. reachRel aut x y ∧ x ∈ s }`;

(*TODO rewrite using different reach rel*)

(* val nStepReachable_def = Define` *)
(*    (nStepReachable trans init 0 = init) *)
(*  ∧ (nStepReachable trans init (SUC i) = *)
(*      {s | ?a qs s'. (a, qs) ∈ trans s' ∧ s' ∈ nStepReachable trans init i *)
(*            ∧ s ∈ qs})`; *)

(* val reachable_def = Define` *)
(*   (reachable trans init = {s | ?n. s ∈ nStepReachable trans init n })`; *)

(* val reachableRel_def = Define` *)
(*   reachableRel aut = *)
(*      { (s, s') | s ∈ reachable aut.trans {s'} *)
(*                    ∧ s ∈ aut.states ∧ s' ∈ aut.states}`; *)

(* val REACHABLE_LEMM = store_thm *)
(*   ("REACHABLE_LEMM", *)
(*    ``!aut x. isValidAlterA aut ∧ (x ∈ aut.states) *)
(*             ==> (reachable aut.trans {x} ⊆ aut.states)``, *)
(*    rpt strip_tac *)
(*    >> `!n. nStepReachable aut.trans {x} n ⊆ aut.states` by ( *)
(*        Induct_on `n` >> fs[nStepReachable_def] *)
(*        >> simp[SUBSET_DEF] >> rpt strip_tac *)
(*        >> metis_tac[isValidAlterA_def,SUBSET_DEF] *)
(*    ) *)
(*    >> simp[reachable_def,SUBSET_DEF] >> rpt strip_tac *)
(*    >> metis_tac[SUBSET_DEF] *)
(*   ); *)

(* val WAA_REACH_IS_PO = store_thm *)
(*   ("WAA_REACH_IS_PO", *)
(*    ``!aut. isWeakAlterA aut ∧ isValidAlterA aut *)
(*              ==> isWeakWithOrder aut (reachableRel aut)``, *)
(*    fs[isWeakAlterA_def] >> simp[isWeakWithOrder_def] >> rpt strip_tac *)
(*     >- (fs[partial_order_def] >> rpt strip_tac *)
(*         >- (simp[reachableRel_def,domain_def,SUBSET_DEF] >> rpt strip_tac) *)
(*         >- (simp[reachableRel_def,range_def,SUBSET_DEF] >> rpt strip_tac) *)
(*         >- (simp[reachableRel_def,transitive_def] >> rpt strip_tac *)
(*             >> fs[reachable_def] >> qexists_tac `n + n'` *)
(*             >> `!j1 j2 p q r. *)
(*                   p ∈ nStepReachable aut.trans {q} j1 ∧ *)
(*                   r ∈ nStepReachable aut.trans {p} j2 *)
(*                   ==> r ∈ nStepReachable aut.trans {q} (j1 + j2)` by ( *)
(*                  Induct_on `j2` >> rpt strip_tac >> fs[nStepReachable_def] *)
(*                  >> `r ∈ nStepReachable aut.trans {q} (SUC (j1 + j2))` *)
(*                     suffices_by metis_tac[SUC_ADD_SYM,ADD_COMM] *)
(*                  >> simp[nStepReachable_def] >> metis_tac[] *)
(*              ) *)
(*             >> metis_tac[ADD_COMM] *)
(*            ) *)
(*         >- (fs[reflexive_def,reachableRel_def,reachable_def] >> rpt strip_tac *)
(*             >> qexists_tac `0` >> fs[nStepReachable_def] *)
(*            ) *)
(*         >- (fs[antisym_def,reachableRel_def,reachable_def] >> rpt strip_tac *)
(*             >> `!i p q. p ∈ aut.states ∧ q ∈ aut.states *)
(*         ∧ p ∈ nStepReachable aut.trans {q} i ==> (p,q) ∈ ord` by ( *)
(*                  Induct_on `i` >> rpt strip_tac *)
(*                   >- fs[reflexive_def,nStepReachable_def] *)
(*                   >- (fs[nStepReachable_def] *)
(*                       >> `s' ∈ aut.states` by ( *)
(*                            `s' ∈ reachable aut.trans {q}` *)
(*                             by (simp[reachable_def] >> metis_tac[]) *)
(*                           >> metis_tac[SUBSET_DEF,REACHABLE_LEMM]) *)
(*                       >> `(s',q) ∈ ord` by metis_tac[] *)
(*                       >> fs[transitive_def] >> metis_tac[] *)
(*                      ) *)
(*              ) *)
(*             >> metis_tac[] *)
(*            ) *)
(*        ) *)
(*     >- (fs[reachableRel_def,reachable_def] >> strip_tac *)
(*           >- (qexists_tac `SUC 0` >> simp[nStepReachable_def] >> metis_tac[]) *)
(*           >- (fs[isValidAlterA_def] >> metis_tac[SUBSET_DEF]) *)
(*        ) *)
(*   ); *)


(*
  restricting a run to a subset of its initial states
*)

val run_restr_V_def = Define `
    (run_restr_V init r_old (SUC i) =
            BIGUNION { e | ?q. (e = r_old.E (i,q)) /\ (q ∈ run_restr_V init r_old i) })
 /\ (run_restr_V init r_old 0       = init)`;

val run_restr_E_def = Define `
    (run_restr_E init r_old (i,q) =
           if q ∈ run_restr_V init r_old i then r_old.E (i,q) else {})`;

val run_restr_def = Define `
   (run_restr init r_old = ALTERA_RUN (run_restr_V init r_old) (run_restr_E init r_old))`;

val RUN_RESTR_LEMM = store_thm
  ("RUN_RESTR_LEMM",
   ``!r init aut w. (validAARunFor aut r w) /\ (init ⊆ r.V 0)
                  ==> !i. run_restr_V init r i ⊆ r.V i``,
   rpt strip_tac >> Induct_on `i` >> fs[run_restr_V_def]
   >> fs[validAARunFor_def, SUBSET_DEF] >> rpt strip_tac
   >> `(s = r.E (i,q)) ∧ q ∈ run_restr_V init r i` by metis_tac[]
   >> `x ∈ r.E (i,q)` by metis_tac[]
   >> `x ∈ r.V (i + 1)` by metis_tac[]
   >> `x ∈ r.V (i + 1)` suffices_by simp[SUC_ONE_ADD] >> fs[]
  );

val RUN_RESTR_FIXP_LEMM = store_thm
  ("RUN_RESTR_FIXP_LEMM",
   ``!r init aut w b. (validAARunFor aut r w) /\ (init ⊆ r.V 0)
                   /\ (infBranchOf (run_restr init r) b)
                       ==> infBranchOf r b``,
   rpt strip_tac >> fs[infBranchOf_def] >> rpt strip_tac
   >> fs[run_restr_def, run_restr_V_def]
    >- (metis_tac[SUBSET_DEF])
    >- (fs[run_restr_E_def] >> Cases_on `b i ∈ (run_restr_V init r i)` >> fs[]
        >- metis_tac[]
        >- (metis_tac[NOT_IN_EMPTY])
       )
  );

(*
 conjoining two runs
*)

val conj_run_branch_cond_def = Define `
  conj_run_branch_cond r1 r2 s q i =
      if q ∈ s
      then (if q ∈ r1.V i
            then r1.E (i,q)
            else if q ∈ r2.V i
                 then r2.E (i,q)
                 else {})
      else {}`;

val conj_run_V_def = Define `
     (conj_run_V r1 r2 (SUC i) =
          BIGUNION { e | ?q. (e = conj_run_branch_cond r1 r2 (conj_run_V r1 r2 i) q i)
                          /\ (q ∈ conj_run_V r1 r2 i)})
  /\ (conj_run_V r1 r2 0       = r1.V 0 ∪ r2.V 0)`;

val conj_run_E_def = Define `
  (conj_run_E r1 r2 (i,q) =
       conj_run_branch_cond r1 r2 (conj_run_V r1 r2 i) q i)`;

val conj_run_def = Define `
  conj_run r1 r2 = ALTERA_RUN (conj_run_V r1 r2) (conj_run_E r1 r2)`;

val CONJ_RUN_V_LEMM = store_thm
  ("CONJ_RUN_V_LEMM",
   ``!r1 r2 i w1 w2 a1 a2. validAARunFor a1 r1 w1 /\ validAARunFor a2 r2 w2
       ==> conj_run_V r1 r2 i ⊆ (r1.V i ∪ r2.V i)``,
   rpt strip_tac >> Induct_on `i` >> fs[conj_run_V_def]
   >> fs[SUBSET_DEF, BIGUNION, conj_run_V_def]
   >> rpt strip_tac >> fs[conj_run_E_def, conj_run_branch_cond_def]
   >> Cases_on `q ∈ r1.V i`
     >- (fs[validAARunFor_def] >> `SUC i = i +1` by simp[]
         >> metis_tac[SUBSET_DEF])
     >- (Cases_on `q ∈ r2.V i`
          >- (fs[validAARunFor_def] >> `SUC i = i +1` by simp[]
              >> metis_tac[SUBSET_DEF])
          >- (fs[])
        )
  );

val CONJ_RUN_FIXP_LEMM = store_thm
  ("CONJ_RUN_FIXP_LEMM",
   ``!r1 r2 b x a1 a2 w. (validAARunFor a1 r1 w) /\ (validAARunFor a2 r2 w)
        /\ (infBranchOf (conj_run r1 r2) b) /\ (branchFixP b x)
        ==> (?b'. (infBranchOf r1 b' \/ infBranchOf r2 b') /\ branchFixP b' x)``,
   rpt strip_tac
   >> `!i. conj_run_V r1 r2 i ⊆ (r1.V i ∪ r2.V i)` by metis_tac[CONJ_RUN_V_LEMM]
   >> fs[infBranchOf_def]
   >> `!i. b (i+1) ∈ (conj_run r1 r2).E (i, b i)` by metis_tac[]
   >> fs[conj_run_def, conj_run_E_def, conj_run_branch_cond_def]
   >> `!i. b i ∈ conj_run_V r1 r2 i` by metis_tac[NOT_IN_EMPTY]
   >> `!i. b i ∈ r1.V i \/ b i ∈ r2.V i` by fs[SUBSET_DEF, UNION_DEF]
   >> fs[branchFixP_def]
   >> `(?a. a >= i /\ b a ∈ r1.V a) \/ (!a. (a >= i) ==> ~(b a ∈ r1.V a) /\ (b a ∈ r2.V a))`
        by metis_tac[]
     >- (dsimp[]
         >> `(∃b' i.
             (b' 0 ∈ r1.V 0 ∧ ∀i. b' (i + 1) ∈ r1.E (i,b' i))
             ∧ (b' i = x) /\ !m. (m >= i) ==> (b' m = x))`
              suffices_by metis_tac[]
         >> qabbrev_tac `b_suff = \j. b (a + j)`
         >> SUBGOAL_THEN ``infBranchSuffOf r1 a b_suff`` mp_tac
           >- (fs[infBranchSuffOf_def] >> rpt strip_tac >> fs[]
                 >- (`b_suff 0 = b (a+0)` by simp[]
                     >> `a + 0 = a` by simp[] >> metis_tac[]
                    )
                 >- (`!j. (a+j) >= i` by simp[]
                     >> `b_suff (j+1) = b (a + j)` by metis_tac[]
                     >> `b (a + j) = x` by metis_tac[]
                     >> fs[conj_run_V_def, conj_run_branch_cond_def]
                     >> SUBGOAL_THEN ``!n. (b (a + n) ∈ r1.V (a+n))`` mp_tac
                        >- (Induct_on `n` >> fs[]
                            >- (`b_suff 0 = b (a + 0)` by metis_tac[]
                                >> fs[] >> `b a = x` by simp[] >> metis_tac[])
                            >- (`b (a + n + 1) ∈ r1.E (a+n, b (a+n))` by metis_tac[]
                                >> fs[validAARunFor_def]
                                >> `b (a + n + 1) ∈ r1.V (a + n + 1)`
                                    by metis_tac[SUBSET_DEF]
                                >> fs[]
                                >> `b (a + (n + 1)) = b_suff (n + 1)` by metis_tac[]
                                >> `b_suff (SUC n) ∈ r1.V (a + (SUC n))`
                                    by metis_tac[SUC_ONE_ADD, ADD_SYM]
                               )
                           )
                        >- (rpt strip_tac
                            >> `b (a + j) ∈ r1.V (a + j)` by metis_tac[]
                            >> `b ((a + j) + 1) ∈ r1.E (a + j, b (a + j))` by metis_tac[]
                            >> `b (a + j + 1) = x` by simp[]
                            >> fs[]
                            >> `b_suff j = b (a + j)` by metis_tac[] >> metis_tac[]
                           )
                    )
              )
           >- (rpt strip_tac
               >> `∃b'. infBranchOf r1 b' ∧ ∀j. (b_suff j = b' (j + a))`
                   by metis_tac[BRANCH_SUFF_LEMM]
               >>  qexists_tac `b'` >> qexists_tac `a` >> rpt strip_tac >> fs[infBranchOf_def]
                  >- (`a + 0 = a` by simp[]
                      >> `b_suff 0 = x` suffices_by metis_tac[]
                      >> `b_suff 0 = b a` by metis_tac[]
                      >> fs[]
                     )
                  >- (`a <= m` by simp[]
                       >> `?p. p + a = m` by metis_tac[LESS_EQ_ADD_EXISTS]
                       >> `b_suff p = b' m` by metis_tac[ADD_COMM]
                       >> `b_suff p = b (a + p)` by metis_tac[ADD_COMM]
                       >> `a + p >= i` by simp[] >> metis_tac[]
                     )
              )
        )
     >- (dsimp[]
         >> `(∃b' i.
             (b' 0 ∈ r2.V 0 ∧ ∀i. b' (i + 1) ∈ r2.E (i,b' i))
             ∧ (b' i = x) /\ !m. (m >= i) ==> (b' m = x))`
              suffices_by metis_tac[]
         >> `i >= i` by simp[] >> `b i ∈ r2.V i` by metis_tac[]
         >> qabbrev_tac `b_suff = \j. b (i + j)`
         >> SUBGOAL_THEN ``infBranchSuffOf r2 i b_suff`` mp_tac
           >- (fs[infBranchSuffOf_def] >> rpt strip_tac >> fs[]
                 >- (`b_suff 0 = b (i+0)` by simp[]
                     >> `i + 0 = i` by simp[] >> metis_tac[]
                    )
                 >- (`!j. (i+j) >= i` by simp[]
                     >> `b_suff (j+1) = b (i + j)` by metis_tac[]
                     >> `b (i + j) = x` by metis_tac[]
                     >> fs[conj_run_V_def, conj_run_branch_cond_def]
                     >> rpt strip_tac
                     >> `i + j >= i` by simp[]
                     >> `b (i + j) ∈ r2.V (i + j)` by metis_tac[]
                     >> `b ((i + j) + 1) ∈ r2.E (i + j, b (i + j))` by metis_tac[]
                     >> `b (i + j + 1) = x` by simp[]
                     >> fs[]
                     >> `b_suff j = b (i + j)` by metis_tac[] >> metis_tac[]
                    )
              )
           >- (rpt strip_tac
               >> `∃b'. infBranchOf r2 b' ∧ ∀j. (b_suff j = b' (j + i))`
                   by metis_tac[BRANCH_SUFF_LEMM]
               >>  qexists_tac `b'` >> qexists_tac `i` >> rpt strip_tac
               >> fs[infBranchOf_def]
                  >- (`i + 0 = i` by simp[]
                      >> `b_suff 0 = x` suffices_by metis_tac[]
                      >> `b_suff 0 = b i` by metis_tac[]
                      >> fs[]
                     )
                  >- (`i <= m` by simp[]
                       >> `?p. p + i = m` by metis_tac[LESS_EQ_ADD_EXISTS]
                       >> `b_suff p = b' m` by metis_tac[ADD_COMM]
                       >> `b_suff p = b (i + p)` by metis_tac[ADD_COMM]
                       >> `i + p >= i` by simp[] >> metis_tac[]
                     )
              )
        )
  );

(*
  suffix run with replaced initial states
*)

val REPL_RUN_CONSTR_LEMM = store_thm
  ("REPL_RUN_CONSTR_LEMM",
  ``!aut run w e h j.
  let run_int =
        ALTERA_RUN (\i. if i = 0 then e else run.V (i + j))
            (λ(i,q). if i = 0 then h q else run.E (i + j,q))
  in
  validAARunFor aut run w /\ (!q. q ∈ e ==> h q ⊆ run.V (j + 1))
    ==> !i. (run_restr e run_int).V (i+1) ⊆ run.V (i+j+1)``,
  fs[] >> rpt gen_tac >> rpt conj_tac >> strip_tac
  >> Induct_on `i` >> fs[run_restr_def, run_restr_V_def, run_restr_E_def, validAARunFor_def]
    >- (fs[SUBSET_DEF] >> rpt strip_tac
        >> `1 = SUC 0` by simp[]
        >> `x ∈
              run_restr_V e
              (ALTERA_RUN (λi. if i = 0 then e else run.V (i + j))
                (λ(i,q). if i = 0 then h q else run.E (i + j,q))) (SUC 0)` by fs[]
        >> fs[run_restr_V_def]
        >> metis_tac[]
       )
    >- (fs[SUBSET_DEF] >> rpt strip_tac
        >> `SUC i + 1 = SUC (i + 1)` by simp[]
        >> `x ∈
               run_restr_V e
               (ALTERA_RUN (λi. if i = 0 then e else run.V (i + j))
               (λ(i,q). if i = 0 then h q else run.E (i + j,q))) (SUC (i + 1))`
           by metis_tac[]
        >> fs[run_restr_V_def]
        >> `x ∈ run.V ((i + (j + 1)) + 1)` by metis_tac[]
        >> `j + (SUC i + 1) = i + (j + 1) + 1` by simp[]
        >> metis_tac[]
       )
  );

val REPL_LEMM_1 = store_thm
  ("REPL_LEMM_1",
   ``!aut run w e h b x j.
      let run_int =
          ALTERA_RUN (\i. if i = 0 then e else run.V (i + j))
              (λ(i,q). if i = 0 then h q else run.E (i + j,q))
      in
          validAARunFor aut run w /\ (!q. q ∈ e ==> h q ⊆ run.V (1 + j))
          /\ infBranchOf (run_restr e run_int) b /\ branchFixP b x
              ==> infBranchSuffOf run (1 + j) (\i. b (i + 1))``,
   fs[infBranchSuffOf_def] >> rpt strip_tac
     >- (fs[infBranchOf_def, run_restr_def]
           >> fs[run_restr_E_def]
           >> `b 0 ∈ e` by metis_tac[run_restr_V_def]
           >> `b (0 + 1) ∈ h (b 0)` by metis_tac[run_restr_E_def, run_restr_V_def]
           >> fs[]
           >> `h (b 0) ⊆ run.V (1+j)` by fs[]
           >> metis_tac[SUBSET_DEF]
        )
     >- (rename [‘b (i + 2) ∈ run.E _’] >> Induct_on `i` >> fs[]
          >- (fs[infBranchOf_def, run_restr_def, run_restr_E_def, run_restr_V_def]
              >> `b (1 + 1) ∈ run.E (j + 1, b 1)` suffices_by simp[]
              >> `b (1 + 1) ∈
                   if
                       b 1 ∈
                         run_restr_V e
                         (ALTERA_RUN (λi. if i = 0 then e else run.V (i + j))
                              (λ(i,q). if i = 0 then h q else run.E (i + j,q))) 1
                   then
                       if 1 = 0 then h (b 0) else run.E (1+j,b 1)
                   else ∅` by fs[]
              >> fs[]
              >> Cases_on `b 1 ∈
                         run_restr_V e
                         (ALTERA_RUN (λi. if i = 0 then e else run.V (i + j))
                              (λ(i,q). if i = 0 then h q else run.E (i + j,q))) 1`
              >> fs[])
          >- (fs[infBranchOf_def, run_restr_def, run_restr_E_def, run_restr_V_def]
              >> `SUC i + 2 = (i + 2) + 1` by simp[]
              >> `b (i + 2 + 1) ∈ run.E (j + (SUC i + 1),b (SUC i + 1))`
                   suffices_by metis_tac[]
              >> `b ((i + 2) + 1) ∈
                     if
                         b (i + 2) ∈
                           run_restr_V e
                           (ALTERA_RUN (λi. if i = 0 then e else run.V (i + j))
                                (λ(i,q). if i = 0 then h q else run.E (i + j,q))) (i + 2)
                     then
                         if (i + 2) = 0 then h (b 0) else run.E ((i + 2) + j,b (i + 2))
                     else ∅` by fs[]
              >> qabbrev_tac `r' = (ALTERA_RUN (λi. if i = 0 then e else run.V (i + j))
                                        (λ(i,q). if i = 0 then h q else run.E (i+j,q)))`
              >> Cases_on `b (i + 2) ∈ run_restr_V e r' (i + 2)`
                 >- (fs[] >> `SUC (i + 1) = i + 2` by simp[] >> fs[]
                     >> `b (i + 3) ∈ run.E (j + (1 + i) + 1, b ((1 + i) + 1))`
                         suffices_by simp[SUC_ONE_ADD]
                     >> simp[])
                 >- metis_tac[NOT_IN_EMPTY]
             )
        )
  );

val REPL_RUN_CONSTR_LEMM2 = store_thm
  ("REPL_RUN_CONSTR_LEMM2",
  ``!aut run w e h b x j.
      let run_int =
          ALTERA_RUN (\i. if i = 0 then e else run.V (i + j))
              (λ(i,q). if i = 0 then h q else run.E (i + j,q))
      in
          validAARunFor aut run w /\ (!q. q ∈ e ==> h q ⊆ run.V (1 + j))
       /\ infBranchOf (run_restr e run_int) b /\ branchFixP b x
            ==> ?b'. infBranchOf run b' /\ branchFixP b' x``,
  fs[] >> rpt strip_tac
  >> `(let run_int =
           ALTERA_RUN (λi. if i = 0 then e else run.V (i + j))
               (λ(i,q). if i = 0 then h q else run.E (i + j,q))
       in
           validAARunFor aut run w ∧ (∀q. q ∈ e ⇒ h q ⊆ run.V (1+j)) ∧
                      infBranchOf (run_restr e run_int) b ∧ branchFixP b x ⇒
                       infBranchSuffOf run (1+j) (λi. b (i + 1)))`
       by metis_tac[REPL_LEMM_1]
  >> fs[] >> `infBranchSuffOf run (j + 1) (λi. b (i + 1))` by metis_tac[]
  >> qabbrev_tac `b_new = \i. b (i + 1)`
  >> `∃b'. infBranchOf run b' ∧ ∀n. b_new n = b' (n + (j + 1))`
      by metis_tac[BRANCH_SUFF_LEMM]
  >> qexists_tac `b'` >> fs[]
  >> fs[branchFixP_def]
  >> qunabbrev_tac `b_new`
  >> qexists_tac `j + (i+1)` >> rpt strip_tac
    >- (`(i + 1) >= i` by simp[]
        >> `b (i + 1) = x` by metis_tac[]
        >> fs[] >> metis_tac[ADD_ASSOC, ADD_COMM]
       )
    >- (`m >= i` by simp[]
        >> `b m = x` by simp[]
        >> `m >= j + 1` by simp[]
        >> `?k. m = j + k + 1` by
                 (`?p. p + (j + 1) = m` by simp[LESS_EQ_ADD_EXISTS]
                  >> qexists_tac `p` >> fs[])
        >> `k + 1 >= i` by simp[]
        >> `b (k + 1) = x` by metis_tac[]
        >> rw[] >> metis_tac[]
       )
  );


(*
  step function of a run
*)

val step_def = Define
  `step run (v,i) = (BIGUNION {run.E (i,q) | q ∈ v }, i+1)`;

val STEP_THM = store_thm
  ("STEP_THM",
  ``!aut run. (?w. validAARunFor aut run w)
      ==> !i. (FUNPOW (step run) i (run.V 0,0) = (run.V i,i))``,
  strip_tac >> strip_tac >> strip_tac
  >> Induct_on `i` >> fs[FUNPOW]
  >> fs[validAARunFor_def]
  >> `FUNPOW (step run) (SUC i) (run.V 0, 0)
       = FUNPOW (step run) i (step run (run.V 0, 0))` by metis_tac[FUNPOW]
  >> `FUNPOW (step run) (SUC i) (run.V 0,0) = step run (FUNPOW (step run) i (run.V 0,0))`
       by metis_tac[FUNPOW_SUC]
  >> `FUNPOW (step run) (SUC i) (run.V 0,0) = step run (run.V i,i)` by metis_tac[]
  >> `step run (run.V i, i) = (run.V (SUC i), SUC i)` suffices_by metis_tac[]
  >> rw[step_def] >> fs[validAARunFor_def]
  >> `(BIGUNION {run.E (i,q) | q | q ∈ run.V i} ⊆ run.V (SUC i))
   /\ (run.V (SUC i) ⊆ BIGUNION {run.E (i,q) | q | q ∈ run.V i})`
        suffices_by metis_tac[SET_EQ_SUBSET]
  >> rpt strip_tac
     >- (simp[SUBSET_DEF, BIGUNION] >> rpt strip_tac
         >> `run.E (i,q) ⊆ run.V (i + 1)` by metis_tac[]
         >> fs[SUBSET_DEF] >> `x ∈ run.V (i+1)` by metis_tac[]
         >> `(SUC i) = (i + 1)` suffices_by metis_tac[] >> simp[]
        )
     >- (simp[SUBSET_DEF, BIGUNION] >> rpt strip_tac
         >> `((SUC i) = 0) ∨ ∃q'. x ∈ run.E ((SUC i) − 1,q') ∧ q' ∈ run.V ((SUC i) − 1)`
            by metis_tac[] >> fs[]
         >> qexists_tac `run.E (i,q')` >> rpt strip_tac >> fs[]
         >> qexists_tac `q'` >> simp[]
        )
  );


(* An example alternating automata *)

val A1_def = Define `A1 = ALTER_A {1;2} {T;F} (\_. {({T;F}, {1;2})}) {{1}} {2}`;

val AUT_EX_1 = store_thm
  ("AUT_EX_1",
   ``isValidAlterA A1``,
   simp[isValidAlterA_def, A1_def, POW_DEF]
  );

val AUT_EX_2 = store_thm
  ("AUT_EX_2",
   ``~(isVeryWeakAlterA A1)``,
   simp[A1_def, isVeryWeakAlterA_def, isVeryWeakWithOrder_def] >> rw[] >>
   `partial_order ord {1;2}
      ==> (?s. ((s = 1) \/ (s = 2)) /\ ?s'. ((s' = 1) \/ (s' = 2)) /\ ~((s, s') ∈ ord))`
      suffices_by metis_tac[]
      >> rw[] >> CCONTR_TAC >> fs[] >> `((1,2) ∈ ord) /\ ((2,1) ∈ ord)` by metis_tac[]
      >> `1 <> 2 /\ {1;2} 1 /\ {1;2} 2`
         suffices_by metis_tac[partial_order_def, antisym_def] >> simp[]
  );

val _ = export_theory();
