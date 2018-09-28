open HolKernel Parse boolLib bossLib;
open listTheory rich_listTheory combinTheory;
open pred_setTheory;

val _ = new_theory "regexMarked";


open regexSemanticsTheory;
open regexExecutableTheory;



(* definitions *)
(* ----------------------------------------------------------------------------- *)
val _ = Datatype regexDatatypes.MReg_datatype_quot;

(* this could possibly part of the theory file *)
val MReg_rws = type_rws ``:'a MReg``; (*fetch "-" "MReg_distinct"*)
val MReg_rw  = LIST_CONJ MReg_rws;
val MReg_ss  = rewrites MReg_rws;


val MARK_REG_def = Define `
         (MARK_REG (Eps)     = MEps                          ) /\
         (MARK_REG (Sym c)   = MSym F c                      ) /\
         (MARK_REG (Alt p q) = MAlt (MARK_REG p) (MARK_REG q)) /\
         (MARK_REG (Seq p q) = MSeq (MARK_REG p) (MARK_REG q)) /\
         (MARK_REG (Rep r)   = MRep (MARK_REG r)             )
`;
val UNMARK_REG_def = Define `
         (UNMARK_REG (MEps)     = Eps                              ) /\
         (UNMARK_REG (MSym _ c) = Sym c                            ) /\
         (UNMARK_REG (MAlt p q) = Alt (UNMARK_REG p) (UNMARK_REG q)) /\
         (UNMARK_REG (MSeq p q) = Seq (UNMARK_REG p) (UNMARK_REG q)) /\
         (UNMARK_REG (MRep r)   = Rep (UNMARK_REG r)               )
`;



val empty_def = Define `
         (empty (MEps)     = T                     ) /\
         (empty (MSym _ _) = F                     ) /\
         (empty (MAlt p q) = (empty p) \/ (empty q)) /\
         (empty (MSeq p q) = (empty p) /\ (empty q)) /\
         (empty (MRep r)   = T                     )
`;

val final_def = Define `
         (final (MEps)     = F                                    ) /\
         (final (MSym b _) = b                                    ) /\
         (final (MAlt p q) =  (final p) \/ (final q)              ) /\
         (final (MSeq p q) = ((final p) /\ (empty q)) \/ (final q)) /\
         (final (MRep r)   = final r                              )
`;

val shift_def = Define `
         (shift _ (MEps)     _ = MEps                                                        ) /\
         (shift m (MSym _ x) c = MSym (m /\ (x = c)) x                                       ) /\
         (shift m (MAlt p q) c = MAlt (shift m p c) (shift m q c)                            ) /\
         (shift m (MSeq p q) c = MSeq (shift m p c) (shift ((m /\ (empty p)) \/ final p) q c)) /\
         (shift m (MRep r)   c = MRep (shift (m \/ (final r)) r c)                           )
`;



val acceptM_def = Define `
         (acceptM r []      = empty r                                 ) /\
         (acceptM r (c::cs) = final (FOLDL (shift F) (shift T r c) cs))
`;










(* rewrite theorems *)
(* ----------------------------------------------------------------------------- *)
(* rewrites for MARK_REG *)
val MARK_REG_DEFs = store_thm ("MARK_REG_DEFs", ``
         (      MARK_REG (Eps)     = MEps                          ) /\
         (!c.   MARK_REG (Sym c)   = MSym F c                      ) /\
         (!p q. MARK_REG (Alt p q) = MAlt (MARK_REG p) (MARK_REG q)) /\
         (!p q. MARK_REG (Seq p q) = MSeq (MARK_REG p) (MARK_REG q)) /\
         (!r.   MARK_REG (Rep r)   = MRep (MARK_REG r)             )
``,

  REWRITE_TAC [MARK_REG_def]
);

(* rewrites for UNMARK_REG *)
val UNMARK_REG_DEFs = store_thm ("UNMARK_REG_DEFs", ``
         (      UNMARK_REG (MEps)     = Eps                              ) /\
         (!b c. UNMARK_REG (MSym b c) = Sym c                            ) /\
         (!p q. UNMARK_REG (MAlt p q) = Alt (UNMARK_REG p) (UNMARK_REG q)) /\
         (!p q. UNMARK_REG (MSeq p q) = Seq (UNMARK_REG p) (UNMARK_REG q)) /\
         (!r.   UNMARK_REG (MRep r)   = Rep (UNMARK_REG r)               )
``,

  REWRITE_TAC [UNMARK_REG_def]
);

(* rewrites for empty *)
val empty_DEFs = store_thm ("empty_DEFs", ``
         (      empty (MEps)     = T                     ) /\
         (!b c. empty (MSym b c) = F                     ) /\
         (!p q. empty (MAlt p q) = (empty p) \/ (empty q)) /\
         (!p q. empty (MSeq p q) = (empty p) /\ (empty q)) /\
         (!r.   empty (MRep r)   = T                     )
``,

  REWRITE_TAC [empty_def]
);

(* rewrites for final *)
val final_DEFs = store_thm ("final_DEFs", ``
         (      final (MEps)     = F                                    ) /\
         (!b c. final (MSym b c) = b                                    ) /\
         (!p q. final (MAlt p q) =  (final p) \/ (final q)              ) /\
         (!p q. final (MSeq p q) = ((final p) /\ (empty q)) \/ (final q)) /\
         (!r.   final (MRep r)   = final r                              )
``,

  REWRITE_TAC [final_def]
);

(* rewrites for shift *)
val shift_DEFs = store_thm ("shift_DEFs", ``
         (!m c.     shift m (MEps)     c = MEps                                                        ) /\
         (!m b x c. shift m (MSym b x) c = MSym (m /\ (x = c)) x                                       ) /\
         (!m p q c. shift m (MAlt p q) c = MAlt (shift m p c) (shift m q c)                            ) /\
         (!m p q c. shift m (MSeq p q) c = MSeq (shift m p c) (shift ((m /\ (empty p)) \/ final p) q c)) /\
         (!m r c.   shift m (MRep r)   c = MRep (shift (m \/ (final r)) r c)                           )
``,

  REWRITE_TAC [shift_def]
);

(* rewrites for acceptM *)
val acceptM_DEFs = store_thm ("acceptM_DEFs", ``
         (!r.      acceptM r []      = empty r                                 ) /\
         (!r c cs. acceptM r (c::cs) = final (FOLDL (shift F) (shift T r c) cs))
``,

  REWRITE_TAC [acceptM_def]
);









(* sanity and helper lemmata *)
(* ----------------------------------------------------------------------------- *)
(* --------------------- MARK_REG and UNMARK_REG *)
(* generate nodelist helper definition *)
val EXP_NODELIST_def = Define `
         (EXP_NODELIST (MEps) = [MEps]) /\
         (EXP_NODELIST (MSym b x) = [MSym b x]) /\
         (EXP_NODELIST (MAlt p q) = (EXP_NODELIST p) ++ (EXP_NODELIST q)) /\
         (EXP_NODELIST (MSeq p q) = (EXP_NODELIST p) ++ (EXP_NODELIST q)) /\
         (EXP_NODELIST (MRep r) = (EXP_NODELIST r))
`;

val HAS_MARKS_def = Define `
         HAS_MARKS mr = ?x. MEM (MSym T x) (EXP_NODELIST mr)
`;

val HAS_MARKS_ALT_DEF = store_thm ("HAS_MARKS_ALT_DEF", ``
         (       HAS_MARKS (MEps)     = F                              ) /\
         (!b x. (HAS_MARKS (MSym b x) = b)                             ) /\
         (!p q. (HAS_MARKS (MAlt p q) = (HAS_MARKS p) \/ (HAS_MARKS q))) /\
         (!p q. (HAS_MARKS (MSeq p q) = (HAS_MARKS p) \/ (HAS_MARKS q))) /\
         (!r.   (HAS_MARKS (MRep r)   = (HAS_MARKS r))                 )
``,

  SIMP_TAC (list_ss++MReg_ss) [HAS_MARKS_def, EXP_NODELIST_def, EXISTS_OR_THM]
);

(* MARK_REG: afterwards all Sym c are MSym F c <=> !r. ~HAS_MARKS (MARK_REG r) *)
val MARK_REG_NOT_HAS_MARKS_thm = store_thm ("MARK_REG_NOT_HAS_MARKS_thm", ``
         (!r. ~HAS_MARKS (MARK_REG r))
``,

  Induct_on `r` >> (
    FULL_SIMP_TAC (list_ss++MReg_ss) [HAS_MARKS_ALT_DEF, MARK_REG_DEFs]
  )
);

(* UNMARK_MARK reverses if MSyms are F *)
val UNMARK_MARK_thm = store_thm ("UNMARK_MARK_thm", ``
         (!mr. (~HAS_MARKS mr) ==> (mr = MARK_REG (UNMARK_REG mr)))
``,
				 
  Induct_on `mr` >> (
    FULL_SIMP_TAC (list_ss++MReg_ss) [HAS_MARKS_ALT_DEF, UNMARK_REG_DEFs, MARK_REG_DEFs]
  )
);

(* MARK_UNMARK reverses always *)
val MARK_UNMARK_thm = store_thm ("MARK_UNMARK_thm", ``
         (!r. UNMARK_REG (MARK_REG r) = r)
``,

  Induct_on `r` >> (
    METIS_TAC [MARK_REG_DEFs, UNMARK_REG_DEFs]
  )
);


(* --------------------- empty *)
(* accepts the empty language? i.e., <=> accept r [], or, [] IN (language_of r) *)
val empty_accept_thm = store_thm ("empty_accept_thm", ``
         (!mr. (empty mr) <=> (accept (UNMARK_REG mr) []))
``,

  Induct_on `mr` >> (
    ASM_SIMP_TAC list_ss [empty_DEFs, UNMARK_REG_DEFs, accept_DEFs, split_DEFs, parts_DEFs]
  )
);

val empty_sem_thm = store_thm ("empty_sem_thm", ``
         (!mr. (empty mr) <=> [] IN (language_of (UNMARK_REG mr)))
``,

  REWRITE_TAC [empty_accept_thm, accept_correctness_thm]
);



(* restregexes helper definition *)
(* represents a set of regular expressions without marking *)
(* each of the regular expressions stands for how to finish matching the input MReg, starting from a T mark *)
val lang_of_MF_def = Define `
         (lang_of_MF (MEps)     = {}                                                                          ) /\
         (lang_of_MF (MSym b _) = if b then {[]} else {}                                                      ) /\
         (lang_of_MF (MAlt p q) = (lang_of_MF p) UNION (lang_of_MF q)                                             ) /\
         (lang_of_MF (MSeq p q) = { u ++ v | u IN (lang_of_MF p) /\ v IN (language_of (UNMARK_REG q))} UNION (lang_of_MF q)) /\
         (lang_of_MF (MRep r)   = { FLAT (u::l) | u IN (lang_of_MF r) /\ EVERY (\w. w IN (language_of (UNMARK_REG r))) l })
`;

val lang_of_M_def  = Define `
         lang_of_M m mr = (if m then (language_of (UNMARK_REG mr)) else {}) UNION (lang_of_MF mr)
`;

(* this rewrite lemma helps to simplify and clarify the proof of lang_of_M_shift_m_thm *)
val lang_of_M_REWRS = store_thm ("lang_of_M_REWRS", ``
         (!w m.     w IN (lang_of_M m  MEps     ) <=> (m /\ (w = []))) /\
         (!w m b x. w IN (lang_of_M m (MSym b x)) <=> (m /\ (w = [x])) \/ (b /\ (w = []))) /\
         (!w m p q. w IN (lang_of_M m (MAlt p q)) <=> (w IN lang_of_M m p) \/ (w IN lang_of_M m q)) /\

         (!w m p q. w IN (lang_of_M m (MSeq p q)) <=> (w IN lang_of_MF q) \/ (?w1 w2. (w1 IN lang_of_M m p) /\ (w2 IN ( language_of (UNMARK_REG q))) /\ (w = w1 ++ w2))) /\

         (!w m r.   w IN (lang_of_M m (MRep r)  ) <=> (?w' wl.
            (w = APPEND w' (FLAT wl)) /\
            ((m /\ (w' = [])) \/ (w' IN lang_of_MF r)) /\
            (!w'. MEM w' wl ==> (w' IN (language_of (UNMARK_REG r))))))
``,

  SIMP_TAC
  (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)
  [lang_of_M_def, UNMARK_REG_DEFs, language_of_DEFs, lang_of_MF_def, UNION_EMPTY, EVERY_MEM] >>

  REPEAT STRIP_TAC >- (
    Cases_on `m` >> METIS_TAC[]
  ) >>

  EQ_TAC >> STRIP_TAC >|
  [
    rename1 `w = FLAT wl` >>
    Q.EXISTS_TAC `[]` >>
    Q.EXISTS_TAC `wl` >>
    ASM_SIMP_TAC list_ss []
  ,
    METIS_TAC[]
  ,
    DISJ1_TAC >>
    FULL_SIMP_TAC list_ss [] >>
    METIS_TAC[]
  ,
    DISJ2_TAC >>
    METIS_TAC[]
  ]
);

val lang_of_MF_NOT_HAS_MARKS_thm = store_thm ("lang_of_MF_NOT_HAS_MARKS_thm", ``
         (!mr. (~HAS_MARKS mr) ==> ((lang_of_MF mr) = {}))
``,

  Induct_on `mr` >> (
    ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [lang_of_MF_def, HAS_MARKS_ALT_DEF, EXTENSION]
  )
);



(* --------------------- final *)
(* what is a state and what means a mark, what does this mean for final (how to interpret final) *)
(* state is a set of positions, a mark is a potential matching, final says wether the end of such a matching is marked, whether one of the nondeterministic "sub"states accepts *)
(* !!! if the regular expression after a mark accepts [] *)
val final_sem_thm = store_thm ("final_sem_thm", ``
         (!mr. (final mr) <=> [] IN lang_of_MF mr)
``,

  Induct_on `mr` >> (
    ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss) [final_DEFs, lang_of_MF_def, language_of_DEFs, empty_sem_thm, boolTheory.EQ_IMP_THM]
  ) >>

  REPEAT STRIP_TAC >>
  Q.EXISTS_TAC `[]` >>
  SIMP_TAC (list_ss) []
);

val final_NOT_HAS_MARKS_thm = store_thm ("final_NOT_HAS_MARKS_thm", ``
         (!mr. (~HAS_MARKS mr) ==> ((final mr) <=> F))
``,

  Induct_on `mr` >> (
    FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss) [final_sem_thm, HAS_MARKS_ALT_DEF, lang_of_MF_def]
  )
);



(* --------------------- shift *)
(* how to create marks, relation to the input state, m and c *)
(* m means whether to shift marks in from the left, and c says which "next positions" are to be marked *)
(* recursively, m says whether to start, c says what to match, this should be right for all marks that are already there and the virtual mark m *)
(* !!! if (in r) the regular expression after a mark (and the virtual mark m) accepts [c] *)
(* final (shift m r c) <=> ? *)

val shift_F_NOT_HAS_MARKS_thm = store_thm ("shift_F_NOT_HAS_MARKS_thm", ``
         (!mr c. (~HAS_MARKS mr) ==> ((shift F mr c) = mr))
``,

  Induct_on `mr` >> (
    ASM_SIMP_TAC std_ss [HAS_MARKS_ALT_DEF, shift_DEFs, final_NOT_HAS_MARKS_thm]
  )
);

val UNMARK_REG_shift_thm = store_thm ("UNMARK_REG_shift_thm", ``
         (!mr m c. ((UNMARK_REG (shift m mr c)) = (UNMARK_REG mr)))
``,

  Induct_on `mr` >> (
    FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss) [HAS_MARKS_ALT_DEF, shift_DEFs, final_NOT_HAS_MARKS_thm, UNMARK_REG_DEFs]
  )
);


val lang_of_MF_lang_of_M_F_thm = store_thm ("lang_of_MF_lang_of_M_F_thm", ``
         (!mr. (lang_of_MF mr) = lang_of_M F mr)
``,

  SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [lang_of_M_def]
);

val FLAT_splitup_thm = store_thm ("FLAT_splitup_thm", ``
         (!c cs l. (c::cs = FLAT l) ==> (?ht tl.
                              (FLAT l = FLAT ((c::ht)::tl)) /\
                              (!x. MEM x ((c::ht)::tl) ==> MEM x l)
         ))
``,

  Induct_on `l` >- SIMP_TAC list_ss [] >>

  REPEAT STRIP_TAC >>
  Cases_on `h` >> (FULL_SIMP_TAC list_ss [] >> METIS_TAC [])  
);


val lang_of_MF_shift_m_thm = store_thm ("lang_of_MF_shift_m_thm", ``
         (!mr c cs m. (cs IN (lang_of_MF (shift m mr c))) <=>
                    ((c::cs) IN (lang_of_M m mr)))
``,

  Induct_on `mr` >|
  [
    SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)
      [shift_DEFs, lang_of_M_def, lang_of_MF_def, UNMARK_REG_DEFs, language_of_DEFs]
  ,
    SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)
      [shift_DEFs, lang_of_M_def, lang_of_MF_def, UNMARK_REG_DEFs, language_of_DEFs]
  ,
    ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)
      [shift_DEFs, lang_of_M_def, lang_of_MF_def, UNMARK_REG_DEFs, language_of_DEFs]
  ,

    FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)
      [shift_DEFs, lang_of_M_REWRS, lang_of_MF_def, UNMARK_REG_DEFs, language_of_DEFs, UNMARK_REG_shift_thm] >>

    POP_ASSUM (K ALL_TAC) >>
    POP_ASSUM (K ALL_TAC) >>

    REWRITE_TAC [boolTheory.EQ_IMP_THM] >>
    REPEAT STRIP_TAC >|
    [
      DISJ2_TAC >>
      Q.EXISTS_TAC `(c::u)` >>
      Q.EXISTS_TAC `v` >>
      ASM_SIMP_TAC (list_ss++QI_ss) []
    ,
      Cases_on `(m /\ empty mr \/ final mr) = F` >- (
        DISJ1_TAC >> FULL_SIMP_TAC (pure_ss) [lang_of_MF_lang_of_M_F_thm]
      ) >>

      FULL_SIMP_TAC (list_ss) [lang_of_M_def, empty_sem_thm, final_sem_thm] >> (
        DISJ2_TAC >>
        Q.EXISTS_TAC `[]` >>
        Q.EXISTS_TAC `(c::cs)` >>
        ASM_SIMP_TAC (list_ss) []
      )
    ,
      Cases_on `(m /\ empty mr \/ final mr) = F` >- (
        DISJ2_TAC >> FULL_SIMP_TAC (pure_ss) [lang_of_MF_lang_of_M_F_thm]
      ) >>

      FULL_SIMP_TAC (list_ss) [lang_of_M_def, empty_sem_thm, final_sem_thm] >> (
        DISJ2_TAC >>
        Q.EXISTS_TAC `[]` >>
        Q.EXISTS_TAC `(c::cs)` >>
        ASM_SIMP_TAC (list_ss) []
      )
    ,
      Cases_on `w1` >- (
        DISJ2_TAC >>
        Cases_on `m` >- (
          FULL_SIMP_TAC (list_ss) [final_sem_thm, empty_sem_thm, lang_of_M_def]
        ) >>

        FULL_SIMP_TAC (list_ss) [final_sem_thm, empty_sem_thm, lang_of_M_def]
      ) >>

      DISJ1_TAC >>
      Q.EXISTS_TAC `t` >>
      Q.EXISTS_TAC `w2` >>
      FULL_SIMP_TAC (list_ss) []
    ]

  ,

    FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)
      [shift_DEFs, lang_of_M_REWRS, lang_of_MF_def, UNMARK_REG_DEFs, language_of_DEFs, UNMARK_REG_shift_thm] >>

    POP_ASSUM (K ALL_TAC) >>

    REWRITE_TAC [boolTheory.EQ_IMP_THM] >>
    REPEAT STRIP_TAC >|
    [
      FULL_SIMP_TAC list_ss [lang_of_M_def, EVERY_MEM] >- (
        Cases_on `~(m \/ final mr)` >> FULL_SIMP_TAC list_ss []  >> (
          (* handles both cases: m, final mr *)
          Q.EXISTS_TAC `[]` >>
          Q.EXISTS_TAC `(c::u)::l` >>
          FULL_SIMP_TAC (list_ss) [final_sem_thm] >>
          METIS_TAC []
        )
      ) >>
      Q.EXISTS_TAC `c::u` >>
      Q.EXISTS_TAC `l` >>
      FULL_SIMP_TAC list_ss []
    ,
      FULL_SIMP_TAC (list_ss) [] >>

      ASSUME_TAC (Q.SPECL [`c`,`cs`,`wl`] FLAT_splitup_thm) >>
      REV_FULL_SIMP_TAC (list_ss) [] >>

      Q.EXISTS_TAC `ht` >>
      Q.EXISTS_TAC `tl` >>
      FULL_SIMP_TAC (list_ss) [lang_of_M_def, EVERY_MEM]
    ,
      Cases_on `w'` >- (
        Cases_on `~final mr` >> FULL_SIMP_TAC (list_ss) [final_sem_thm] >>

        ASSUME_TAC (Q.SPECL [`c`,`cs`,`wl`] FLAT_splitup_thm) >>
        REV_FULL_SIMP_TAC (list_ss) [] >>

        Q.EXISTS_TAC `ht` >>
        Q.EXISTS_TAC `tl` >>
        FULL_SIMP_TAC (list_ss) [lang_of_M_def, EVERY_MEM]
      ) >>
      Q.EXISTS_TAC `t` >>
      Q.EXISTS_TAC `wl` >>
      FULL_SIMP_TAC (list_ss) [lang_of_M_def, EVERY_MEM]
    ]
  ]
);

val lang_of_MF_shift_T_thm = store_thm ("lang_of_MF_shift_T_thm", ``
         (!mr c cs. (~HAS_MARKS mr) ==> (
           (cs IN (lang_of_MF (shift T mr c)) <=>
           (c::cs) IN (language_of (UNMARK_REG mr)))
         ))
``,

  SIMP_TAC std_ss [lang_of_MF_shift_m_thm, lang_of_M_def, lang_of_MF_NOT_HAS_MARKS_thm, UNION_EMPTY]
);

val final_FOLDL_shift_F_thm = store_thm ("final_FOLDL_shift_F_thm", ``
         (!mr w. (final (FOLDL (shift F) mr w)) <=> (w IN (lang_of_MF mr)))
``,

  Induct_on `w` >> (
    FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss) [final_sem_thm, lang_of_MF_shift_m_thm, lang_of_M_def]
  )
);


(* --------------------- acceptM *)
(* just rewrites *)
(* should be enough, essentially recurses the shifting with initialization first and is therefore just an inductive extension of the things before *)
(*
         (acceptM r []           = empty r                                 ) /\
         (acceptM r ((c:'a)::cs) = final (FOLDL (shift F) (shift T r c) cs))
*)








(* correctness of definition *)
(* ----------------------------------------------------------------------------- *)
val acceptM_correctness_thm = store_thm("acceptM_correctness_thm", ``!r w. acceptM (MARK_REG r) w <=> w IN (language_of r)``,

  Cases_on `w` >> (
    REWRITE_TAC [acceptM_DEFs, empty_sem_thm, MARK_UNMARK_thm] >>
    SIMP_TAC list_ss [MARK_REG_NOT_HAS_MARKS_thm, lang_of_MF_shift_T_thm, MARK_UNMARK_thm, final_FOLDL_shift_F_thm]
  )
);

val acceptM_accept_thm = store_thm("acceptM_accept_thm", ``!r w. acceptM (MARK_REG r) w <=> accept r w``,

  REWRITE_TAC [acceptM_correctness_thm, accept_correctness_thm]
);








val _ = export_theory();
