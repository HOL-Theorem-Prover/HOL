open HolKernel boolLib Parse bossLib

open finite_mapTheory

val _ = new_theory "hol_dpll"

val _ = set_fixity "satisfies_clause" (Infixl 500)
val satisfies_clause_def = Define`
  sigma satisfies_clause (c:('a # bool) list) =
    EXISTS (\ (a,v). FLOOKUP sigma a = SOME v) c
`;

val satisfies_clause_thm = store_thm(
  "satisfies_clause_thm",
  ``(s satisfies_clause [] = F) /\
    (s satisfies_clause (h :: t) =
        (FLOOKUP s (FST h) = SOME (SND h)) \/
        s satisfies_clause t)``,
  SRW_TAC [][satisfies_clause_def] THEN Cases_on `h` THEN
  SRW_TAC [][]);

val _ = set_fixity "satisfies" (Infixl 500)
val satisfies_def = Define`
  sigma satisfies (cset : ('a # bool) list list) =
    EVERY (\c. sigma satisfies_clause c) cset
`;

val satisfies_thm = store_thm(
  "satisfies_thm",
  ``(s satisfies [] = T) /\
    (s satisfies (c::cs) = s satisfies_clause c /\ s satisfies cs)``,
  SRW_TAC [][satisfies_def]);

val binds_def = Define`binds a p = (a = FST p)`

val rewrite_def = Define`
  (rewrite a v [] = []) /\
  (rewrite a v (c::cs) = if MEM (a,v) c then
                             rewrite a v cs
                         else
                             FILTER ($~ o binds a) c :: rewrite a v cs)
`;

val catom_def = Define`
  (catom a [] = F) /\
  (catom a (h :: t) = (a = FST h) \/ catom a t)
`;

val atom_appears_def = Define`
  atom_appears a cset = EXISTS (catom a) cset
`;

val LENGTH_FILTER_1 = prove(
  ``LENGTH (FILTER P l) <= LENGTH l``,
  Induct_on `l` THEN SRW_TAC [][] THEN DECIDE_TAC);

val rewrite_noincrease = store_thm(
  "rewrite_noincrease",
  ``list_size LENGTH (rewrite a v cset) <= list_size LENGTH cset``,
  Induct_on `cset` THEN
  SRW_TAC [][rewrite_def, listTheory.list_size_def] THENL [
    DECIDE_TAC,
    Q_TAC SUFF_TAC `LENGTH (FILTER ($~ o binds a) h) <= LENGTH h`
          THEN1 DECIDE_TAC THEN
    SRW_TAC [][LENGTH_FILTER_1]
  ]);

val lemma = prove(
  ``catom a h ==> LENGTH (FILTER ($~ o binds a) h) < LENGTH h``,
  Induct_on `h` THEN
  SRW_TAC [][catom_def, binds_def, DECIDE ``x < SUC y = x <= y``,
             LENGTH_FILTER_1] THEN
  FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) []);

val rewrite_reduces_size = store_thm(
  "rewrite_reduces_size",
  ``atom_appears a cset ==> (list_size LENGTH (rewrite a v cset) <
                             list_size LENGTH cset)``,
  Induct_on `cset` THEN SRW_TAC [][atom_appears_def] THENL [
    SRW_TAC [][listTheory.list_size_def, rewrite_def] THENL [
      ASSUME_TAC rewrite_noincrease THEN DECIDE_TAC,
      ASSUME_TAC rewrite_noincrease THEN
      Q_TAC SUFF_TAC `LENGTH (FILTER ($~ o binds a) h) < LENGTH h`
            THEN1 DECIDE_TAC THEN
      SRW_TAC [][lemma]
    ],

    SRW_TAC [][listTheory.list_size_def, rewrite_def] THENL [
      FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [atom_appears_def],
      Q_TAC SUFF_TAC `LENGTH (FILTER ($~ o binds a) h) <= LENGTH h`
            THEN1 FULL_SIMP_TAC (srw_ss() ++ ARITH_ss) [atom_appears_def] THEN
      SRW_TAC [][LENGTH_FILTER_1]
    ]
  ]);

val find_uprop_def = Define`
  (find_uprop [] = NONE) /\
  (find_uprop (c::cs) = if LENGTH c = 1 then SOME (HD c)
                        else find_uprop cs)
`;

val find_uprop_works = store_thm(
  "find_uprop_works",
  ``(find_uprop cset = SOME (v',b)) ==> atom_appears v' cset``,
  Induct_on `cset` THEN SRW_TAC [][find_uprop_def] THENL [
    SRW_TAC [][atom_appears_def] THEN Cases_on `h` THEN
    FULL_SIMP_TAC (srw_ss()) [catom_def],
    FULL_SIMP_TAC (srw_ss()) [atom_appears_def]
  ]);

val choose_def = Define`
  choose cset = FST (HD (HD cset))
`;

val choose_works = store_thm(
  "choose_works",
  ``~(cset = []) /\ ~MEM [] cset ==> atom_appears (choose cset) cset``,
  Cases_on `cset` THEN SRW_TAC [][] THEN
  Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [choose_def] THEN
  SRW_TAC [][atom_appears_def, catom_def]);

val dpll_defn = Hol_defn "dpll" `
  dpll cset =
    if cset = [] then SOME FEMPTY
    else if MEM [] cset then NONE
    else
      case find_uprop cset of
        NONE -> (let splitv = choose cset
                 in
                   case dpll (rewrite splitv T cset) of
                      NONE -> (case dpll (rewrite splitv F cset) of
                                  NONE -> NONE
                               || SOME fm -> SOME (fm |+ (splitv,F)))
                   || SOME fm -> SOME (fm |+ (splitv,T)))
     || SOME (v,b) ->
          case dpll (rewrite v b cset) of
             NONE -> NONE
          || SOME fm -> SOME (fm |+ (v,b))
`;



val (dpll_def, dpll_ind) = Defn.tprove(
  dpll_defn,
  WF_REL_TAC `measure (\cset. list_size LENGTH cset)` THEN
  SRW_TAC [][] THENL [
    SRW_TAC [][rewrite_reduces_size, choose_works],
    SRW_TAC [][rewrite_reduces_size, choose_works],
    METIS_TAC [find_uprop_works, rewrite_reduces_size]
  ]);

val induct =
    (SIMP_RULE (srw_ss()) [prim_recTheory.WF_measure,
                           prim_recTheory.measure_thm] o
     Q.ISPEC `measure (\cset. list_size LENGTH cset)`)
             relationTheory.WF_INDUCTION_THM

val exrwt_lemma = prove(
  ``!c v b fm. fm satisfies_clause FILTER ($~ o binds v) c ==>
               fm |+ (v,b) satisfies_clause c``,
  Induct THEN1 SRW_TAC [][satisfies_clause_thm] THEN
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss)
               [pairTheory.FORALL_PROD, satisfies_clause_thm,
                binds_def, finite_mapTheory.FLOOKUP_DEF,
                finite_mapTheory.FAPPLY_FUPDATE_THM] THEN
  SRW_TAC [][satisfies_clause_thm, finite_mapTheory.FLOOKUP_DEF,
             finite_mapTheory.FAPPLY_FUPDATE_THM] THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN
  POP_ASSUM MP_TAC THEN SRW_TAC [][]);

val extend_rewrite = store_thm(
  "extend_rewrite",
  ``!fm v b.
       fm satisfies rewrite v b cset ==> (fm |+ (v,b)) satisfies cset``,
  Induct_on `cset` THEN SRW_TAC [][satisfies_thm, rewrite_def] THENL [
    Induct_on `h` THEN1 SRW_TAC [][] THEN
    ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss)
                 [pairTheory.FORALL_PROD, satisfies_clause_thm] THEN
    SRW_TAC [][finite_mapTheory.FLOOKUP_DEF],
    SRW_TAC [][exrwt_lemma]
  ]);

val dpll_satisfies = store_thm(
  "dpll_satisfies",
  ``!cset fm. (dpll cset = SOME fm) ==> fm satisfies cset``,
  HO_MATCH_MP_TAC dpll_ind THEN SRW_TAC [][] THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [dpll_def] THEN
  SRW_TAC [][] THEN1 SRW_TAC [][satisfies_def] THEN
  Cases_on `find_uprop cset` THENL [
    FULL_SIMP_TAC (srw_ss()) [LET_THM] THEN
    Cases_on `dpll (rewrite (choose cset) T cset)` THEN
    FULL_SIMP_TAC (srw_ss()) [] THENL [
      Cases_on `dpll (rewrite (choose cset) F cset)` THEN
      FULL_SIMP_TAC (srw_ss()) [] THEN
      SRW_TAC [][] THEN SRW_TAC [][extend_rewrite],
      SRW_TAC [][extend_rewrite]
    ],
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `dpll (rewrite q r cset)` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][extend_rewrite]
  ]);

val empty_clause_unsatisfiable = prove(
  ``!cset. MEM [] cset ==> !fm. ~(fm satisfies cset)``,
  Induct THEN SRW_TAC [][satisfies_thm] THEN
  SRW_TAC [][satisfies_clause_thm]);

val option_cond = prove(
  ``((if p then SOME x else NONE) = SOME y) = p /\ (x = y)``,
  SRW_TAC [][]);

val fm_gives_value = prove(
  ``!cset fm v.
       fm satisfies cset /\ v IN FDOM fm ==>
       fm satisfies (rewrite v (fm ' v) cset)``,
  Induct THEN SRW_TAC [][satisfies_thm, rewrite_def] THEN
  Induct_on `h` THEN1 SRW_TAC [][] THEN
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss)
               [pairTheory.FORALL_PROD, binds_def, option_cond,
                satisfies_clause_thm, finite_mapTheory.FLOOKUP_DEF] THEN
  SRW_TAC [][satisfies_clause_thm, finite_mapTheory.FLOOKUP_DEF] THEN
  METIS_TAC []);

val cpos_fm_gives_value = prove(
  ``v IN FDOM fm /\ ~(fm satisfies (rewrite v (fm ' v) cset)) ==>
    ~(fm satisfies cset)``,
  METIS_TAC [fm_gives_value]);

val novbind_lemma = prove(
  ``~MEM (v,T) h /\ ~MEM (v,F) h ==> (FILTER ($~ o binds v) h = h)``,
  Induct_on `h` THEN1 SRW_TAC [][] THEN
  ASM_SIMP_TAC (srw_ss() ++ boolSimps.DNF_ss)
               [pairTheory.FORALL_PROD, binds_def]);

val partial_clause_1 = prove(
  ``!h. fm satisfies_clause h /\
        ~(fm satisfies_clause FILTER ($~ o binds v) h) ==>
        ?b. MEM (v,b) h``,
  Induct THEN
  ASM_SIMP_TAC (srw_ss()) [pairTheory.FORALL_PROD, binds_def] THEN
  SRW_TAC [][satisfies_clause_thm, finite_mapTheory.FLOOKUP_DEF] THEN
  METIS_TAC []);

val partial_clause_sat = prove(
  ``!h v b fm.
       fm satisfies_clause h /\
       ~(fm satisfies_clause FILTER ($~ o binds v) h) /\
       MEM (v,b) h /\ ~MEM (v,~b) h ==>
       v IN FDOM fm /\ (fm ' v = b)``,
  Induct_on `h` THEN1 SRW_TAC [][] THEN
  ASM_SIMP_TAC (srw_ss())
               [pairTheory.FORALL_PROD, binds_def, satisfies_clause_thm,
                finite_mapTheory.FLOOKUP_DEF] THEN
  SRW_TAC [][satisfies_clause_thm, finite_mapTheory.FLOOKUP_DEF] THEN
  TRY (METIS_TAC []) THEN
  IMP_RES_TAC partial_clause_1 THEN
  `b = b'` by (Cases_on `b` THEN SRW_TAC [][] THEN
               Cases_on `b'` THEN SRW_TAC [][] THEN
               FULL_SIMP_TAC (srw_ss()) []) THEN
  SRW_TAC [][] THEN METIS_TAC []);

val not_sat_case_split = prove(
  ``!cset fm. ~(fm satisfies (rewrite v T cset)) /\
              ~(fm satisfies (rewrite v F cset)) ==>
              ~(fm satisfies cset)``,
  Induct THEN SRW_TAC [][rewrite_def, satisfies_thm] THEN
  TRY (METIS_TAC [novbind_lemma]) THEN
  Cases_on `fm satisfies_clause h` THEN SRW_TAC [][] THENL [
    `v IN FDOM fm /\ (fm ' v = T)`
       by (MATCH_MP_TAC partial_clause_sat THEN SRW_TAC [][] THEN
           METIS_TAC []) THEN
    MATCH_MP_TAC cpos_fm_gives_value THEN SRW_TAC [][],
    `v IN FDOM fm /\ (fm ' v = F)`
       by (MATCH_MP_TAC partial_clause_sat THEN SRW_TAC [][] THEN
           METIS_TAC []) THEN
    MATCH_MP_TAC cpos_fm_gives_value THEN SRW_TAC [][]
  ]);

val case_split_unsat = prove(
  ``!cset. (!fm. ~(fm satisfies rewrite v F cset)) /\
           (!fm. ~(fm satisfies rewrite v T cset)) ==>
           !fm. ~(fm satisfies cset)``,
  Induct THEN SRW_TAC [][rewrite_def, satisfies_thm] THEN
  Cases_on `fm satisfies_clause h` THEN SRW_TAC [][] THENL [
    Cases_on `fm satisfies_clause FILTER ($~ o binds v) h` THENL [
      `~(fm satisfies rewrite v T cset)` by METIS_TAC [] THEN
      MATCH_MP_TAC not_sat_case_split THEN SRW_TAC [][],
      `v IN FDOM fm /\ (fm ' v = F)`
         by (MATCH_MP_TAC partial_clause_sat THEN SRW_TAC [][] THEN
             METIS_TAC []) THEN
      MATCH_MP_TAC cpos_fm_gives_value THEN SRW_TAC [][]
    ],
    Cases_on `fm satisfies_clause FILTER ($~ o binds v) h` THENL [
      `~(fm satisfies rewrite v F cset)` by METIS_TAC [] THEN
      MATCH_MP_TAC not_sat_case_split THEN SRW_TAC [][],
      `v IN FDOM fm /\ (fm ' v = T)`
         by (MATCH_MP_TAC partial_clause_sat THEN SRW_TAC [][] THEN
             METIS_TAC []) THEN
      MATCH_MP_TAC cpos_fm_gives_value THEN SRW_TAC [][]
    ],
    `FILTER ($~ o binds v) h = h` by METIS_TAC [novbind_lemma] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [not_sat_case_split]
  ]);

val find_uprop_forces = prove(
  ``!cset. (find_uprop cset = SOME (q, r)) ==>
           !fm. ~(fm satisfies rewrite q (~r) cset)``,
  Induct THEN SRW_TAC [][find_uprop_def, satisfies_thm, rewrite_def] THENL [
    Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THENL [
      METIS_TAC [],
      Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) []
    ],
    Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    SRW_TAC [][binds_def] THEN
    Cases_on `t` THEN FULL_SIMP_TAC (srw_ss()) [satisfies_clause_thm]
  ]);

val dpll_unsatisfied = store_thm(
  "dpll_unsatisfied",
  ``!cset. (dpll cset = NONE) ==> !fm. ~(fm satisfies cset)``,
  HO_MATCH_MP_TAC dpll_ind THEN GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC [dpll_def] THEN
  SRW_TAC [][empty_clause_unsatisfiable] THEN
  Cases_on `find_uprop cset` THENL [
    FULL_SIMP_TAC (srw_ss()) [LET_THM] THEN
    Cases_on `dpll (rewrite (choose cset) T cset)` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `dpll (rewrite (choose cset) F cset)` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [case_split_unsat],
    FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `x` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    Cases_on `dpll (rewrite q r cset)` THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN
    IMP_RES_TAC find_uprop_forces THEN
    Cases_on `r` THEN FULL_SIMP_TAC (srw_ss()) [] THEN
    METIS_TAC [case_split_unsat]
  ]);

val _ = EVAL ``dpll [[(1,T); (2,F); (3,T)]; [(1,F); (2,T)]]``

val _ = export_theory();
