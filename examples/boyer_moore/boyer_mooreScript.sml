open HolKernel boolLib bossLib Parse;

open boolTheory;
open pred_setTheory;
open pairTheory;

open arithmeticTheory;
open numTheory;

open prim_recTheory;

open listTheory;
open rich_listTheory;

open stringTheory;

open set_lemmasTheory;
open helper_funcsTheory;
open boyer_moore_specTheory;

val _ = new_theory"boyer_moore";

(* -- IMPLICIT CHARACTER MISMATCH TABLE CONSTRUCTION -- *)
(* Assess potential shift based on character mismatch rule *)
val checkDeltaC_def =
    Define
    `
    checkDeltaC pat all_chars j a d =
        ((d = j+1) \/ (EL (j-d) pat = EL a all_chars))
    `;

(* Relationship between checkDeltaC function
   and valid_cha_shift specification *)
val CHECK_DELTAC_THM = store_thm(
    "CHECK_DELTAC_THM",
    ``!pat all_chars j a d . d IN valid_cha_shifts pat all_chars j a
                 <=> (1 <= d /\ d <= j+1 /\ checkDeltaC pat all_chars j a d)``,
    rw[valid_cha_shifts_def,checkDeltaC_def]
    >> Cases_on `d=j+1`
    >- simp[]
    >- (`(d <= j) <=> (d <= j + 1)`
            suffices_by metis_tac[]
        >> simp[])
    );

(* Check Delta C in terms of set comprehensions *)
val CHECK_DELTAC_SET = store_thm(
    "CHECK_DELTAC_SET",
    ``valid_cha_shifts pat all_chars j a = {d | 1 <= d /\ d <= j+1
                        /\ checkDeltaC pat all_chars j a d}``,
    rw [CHECK_DELTAC_THM, EXTENSION]
    );

(* Find minimum valid character mismatch based shift *)
val cmRecur_def =
    tDefine "cmRecur"
    `
    cmRecur pat all_chars j a d =
        if (j+1 < d) then d
        else if (checkDeltaC pat all_chars j a d) then d
        else (cmRecur pat all_chars j a (d+1))
    `
    (WF_REL_TAC `measure (\(p, c, j, a, d). SUC j - d)`
    >> fs[ADD1,checkDeltaC_def]);

(* Intermediate lemmas to reason about recursive function bounds *)
val CMRECUR_LEM = store_thm(
    "CMRECUR_LEM",
    ``!pat all_chars j a d. d <= cmRecur pat all_chars j a d``,
    Induct_on `j + 2 - d`
    >> rpt STRIP_TAC
    >> ONCE_REWRITE_TAC[cmRecur_def]
    >> fs[]
    >> `v = j + 2 - (d+1)` by fs[ADD_CLAUSES]
    >> `(d+1) <= cmRecur pat all_chars j a (d+1)` by metis_tac[]
    >> Cases_on `checkDeltaC pat all_chars j a d`
    >> fs[]);

val CMRECUR_BND_THM = store_thm(
    "CMRECUR_BND_THM",
    ``!pat all_chars j a d . d IN valid_cha_shifts pat all_chars j a
        ==> (!x. x <= d ==> cmRecur pat all_chars j a x <= d)``,
    rpt STRIP_TAC
    >> Induct_on `d - x`
    >- (fs[]
        >> rpt STRIP_TAC
        >> `x=d` by rw[]
        >> fs[valid_cha_shifts_def]
        >> ONCE_REWRITE_TAC [cmRecur_def]
        >> simp[checkDeltaC_def])
    >- (fs[]
        >> rpt STRIP_TAC
        >> `cmRecur pat all_chars j a (SUC x) <= d` by fs[ADD_CLAUSES]
        >> `cmRecur pat all_chars j a x <= cmRecur pat all_chars j a (SUC x)` suffices_by fs[]
        >> qabbrev_tac `L = cmRecur pat all_chars j a (SUC x)`
        >> Cases_on `j + 1 < x`
        >- (`cmRecur pat all_chars j a x = x` by (ONCE_REWRITE_TAC[cmRecur_def] >> fs[])
            >> simp[]
            >> `(SUC x) <= cmRecur pat all_chars j a (SUC x)` suffices_by simp[Abbr `L`]
            >> metis_tac[CMRECUR_LEM])
        >- (Cases_on `checkDeltaC pat all_chars j a x`
            >> ONCE_REWRITE_TAC[cmRecur_def]
            >> simp[ADD1,Abbr `L`]
            >> `(x + 1) <= cmRecur pat all_chars j a (x + 1)` by metis_tac[CMRECUR_LEM]
            >> fs[])
        )
    );

(* Confirming we only get valid values *)
val CMRECUR_COR_THM = store_thm(
    "CMRECUR_COR_THM",
    ``! pat all_chars j a d . 1 <= cmRecur pat all_chars j a d
                             /\ cmRecur pat all_chars j a d <= j + 1
                                ==> cmRecur pat all_chars j a d
                                        IN valid_cha_shifts pat all_chars j a``,
    rpt STRIP_TAC
    >> `d <= j + 1`
        by (CCONTR_TAC
            >> `cmRecur pat all_chars j a d > j + 1` suffices_by simp[]
            >> ONCE_REWRITE_TAC [cmRecur_def]
            >> fs[])
    >> Induct_on `j + 1 - d`
    >- (rpt STRIP_TAC
        >> ONCE_REWRITE_TAC[cmRecur_def]
        >> fs[checkDeltaC_def,valid_cha_shifts_def])
    >- (rpt STRIP_TAC
        >> `v = j + 1 - SUC d` by fs[]
        >> `SUC d <= j + 1` by fs[]
        >> `SUC d <= cmRecur pat all_chars j a (SUC d)`
                by metis_tac[CMRECUR_LEM,LESS_EQ_TRANS]
        >> `cmRecur pat all_chars j a (SUC d) <= j + 1`
                by (`j + 1 IN valid_cha_shifts pat all_chars j a` by fs[valid_cha_shifts_def]
                    >> metis_tac[CMRECUR_BND_THM])
        >> `cmRecur pat all_chars j a (SUC d) IN valid_cha_shifts pat all_chars j a`
                by (first_x_assum (qspec_then `j` (qspec_then `SUC d` mp_tac)) >> fs[])
        >> ONCE_REWRITE_TAC[cmRecur_def]
        >> Cases_on `j + 1 < d`
        >> fs[]
        >> `checkDeltaC pat all_chars j a d ==> d IN valid_cha_shifts pat all_chars j a`
                suffices_by (Cases_on `checkDeltaC pat all_chars j a d` >> fs[ADD1])
        >> `checkDeltaC pat all_chars j a d ==> 1 <= d`
                suffices_by simp[checkDeltaC_def, valid_cha_shifts_def]
        >> STRIP_TAC
        >> `cmRecur pat all_chars j a d = d`
                by (ONCE_REWRITE_TAC[cmRecur_def] >> fs[])
        >> fs[])
    );

(* initiate recursion *)
val cmVal_def =
    Define
    `
    cmVal pat all_chars j a = cmRecur pat all_chars j a 1
    `;

(* Relationship between cmVal function and valid_cha_shift specification *)
val CMVAL_THM = store_thm(
    "CMVAL_THM",
    ``cmVal pat all_chars j a = MIN_SET (valid_cha_shifts pat all_chars j a)``,
    simp[cmVal_def]
    >> `! d. d IN valid_cha_shifts pat all_chars j a ==> cmRecur pat all_chars j a 1 <= d`
            by (rpt STRIP_TAC
                >> `1 <= d` by fs[valid_cha_shifts_def]
                >> simp[CMRECUR_BND_THM])
    >> `cmRecur pat all_chars j a 1 IN valid_cha_shifts pat all_chars j a`
            by (`1 <= cmRecur pat all_chars j a 1` by simp[CMRECUR_LEM]
                >> `cmRecur pat all_chars j a 1 <= j + 1` by fs[valid_cha_shifts_def]
                >> simp[CMRECUR_COR_THM])
    >> fs[LOWER_BOUND_IS_MIN_SET]
    );

(* Proving bounds on cmVal function with valid input *)
val CMVAL_BND = store_thm(
    "CMVAL_BND",
    ``!j a. j < LENGTH pat ∧ a < LENGTH all_chars
           ==> 0 < cmVal pat all_char j a
               /\ cmVal pat all_char j a <= LENGTH pat``,
    simp[CMVAL_THM]
    >> REPEAT strip_tac
    >- (`0 <> MIN_SET (valid_cha_shifts pat all_char j a)`
            suffices_by rw[]
        >> `~(0 IN valid_cha_shifts pat all_char j a)`
            suffices_by metis_tac[CHA_SHIFT_EXISTS_THM,MIN_SET_LEM]
        >> simp[valid_cha_shifts_def])
    >- (`?x. (x IN valid_cha_shifts pat all_char j a) /\ (x <= LENGTH pat)`
            suffices_by metis_tac[MIN_SET_LEM, LESS_EQ_TRANS, MEMBER_NOT_EMPTY]
        >> simp[valid_cha_shifts_def]
        >> qexists_tac `j+1`
        >> simp[])
    );

(* -- IMPLICIT SUFFIX MATCH TABLE CONSTRUCTION -- *)
(* Assess potential shift based on suffix mismatch rule *)
val checkDeltaS_def =
    Define
    `
    checkDeltaS pat j d <=>
        ((d >= SUC j) \/ ~(EL (j-d) pat = EL j pat)) /\
        (extract (MAX (SUC j) d,LENGTH pat) pat
            = extract ((MAX (SUC j) d) - d,LENGTH pat - d) pat)
    `;

(* Relationship between checkDeltaS function
   and valid_suf_shift specification *)
val CHECK_DELTAS_THM = store_thm(
    "CHECK_DELTAS_THM",
    ``! pat j d . d IN valid_suf_shifts pat j
                 <=> 1 <= d /\ d <= LENGTH pat /\ checkDeltaS pat j d``,
    ONCE_REWRITE_TAC [EQ_SYM_EQ]
    >> simp[valid_suf_shifts_def,checkDeltaS_def,EXTRACT_THM,LIST_EQ_REWRITE]
    >> rw[EQ_IMP_THM]
    >> simp[]
    >- (`MAX (SUC j) d = d`
            by simp[MAX_DEF]
        >> fs[]
        >> first_x_assum(qspec_then `i-d` mp_tac)
        >> simp[])
    >- (qabbrev_tac `M = MAX (SUC j) d`
        >> `d <= M`
                by rw[MAX_DEF,Abbr `M`]
        >> Q.UNDISCH_THEN `d<= LENGTH pat` assume_tac
        >> fs[]
        >> first_x_assum(qspec_then `i-M` mp_tac)
        >> simp[]
        >> `M <= i`
                by simp[MAX_DEF, Abbr `M`]
        >> simp[])
    >- (simp[MAX_DEF])
    >- (qabbrev_tac `M = MAX (SUC j) d`
        >> `d <= M`
                by rw[MAX_DEF,Abbr `M`]
        >> simp[])
    >- (simp[MAX_DEF])
    >- (qabbrev_tac `M = MAX (SUC j) d`
        >> `d <= M`
                by rw[MAX_DEF,Abbr `M`]
        >> simp[]
        >> `(j + 1) <= (M + x)`
                by rw[MAX_DEF,Abbr `M`]
        >> `d <= (M + x)`
                by rw[MAX_DEF,Abbr `M`]
        >> first_x_assum(qspec_then `M + x` mp_tac)
        >> simp[])
    );

(* Check Delta S in terms of set comprehensions *)
val CHECK_DELTAS_SET = store_thm(
    "CHECK_DELTAS_SET",
    ``valid_suf_shifts pat j = { d | 1 <= d
                                    /\ d <= LENGTH pat
                                    /\ checkDeltaS pat j d}``,
    rw [CHECK_DELTAS_THM, EXTENSION]
    );

val smRecur_def =
    tDefine "smRecur"
    `
    smRecur pat j d =
        if (LENGTH pat < d) then d
        else if (checkDeltaS pat j d) then d
        else (smRecur pat j (d+1))
    `
    (WF_REL_TAC `measure (\(p, j, d). SUC (LENGTH p) - d)`);

(* Find minimum valid suffix mismatch based shift *)
val smVal_def =
    Define
    `
    smVal pat j = smRecur pat j 1
    `;

(* Intermediate lemmas to reason about recursive function bounds *)
val SMRECUR_LEM = store_thm(
    "SMRECUR_LEM",
    ``!pat j d. d <= smRecur pat j d``,
    Induct_on `LENGTH pat + 1 - d`
    >> rpt STRIP_TAC
    >> ONCE_REWRITE_TAC[smRecur_def]
    >> fs[]
    >> `v = LENGTH pat + 1 - (d+1)` by fs[ADD_CLAUSES]
    >> `(d+1) <= smRecur pat j (d+1)` by metis_tac[]
    >> Cases_on `checkDeltaS pat j d`
    >> fs[]);

val SMRECUR_BND_THM = store_thm(
    "SMRECUR_BND_THM",
    ``!pat j d . d IN valid_suf_shifts pat j
        ==> (!x. x <= d ==> smRecur pat j x <= d)``,
    rpt STRIP_TAC
    >> Induct_on `d - x`
    >- (fs[]
        >> rpt STRIP_TAC
        >> `x=d` by rw[]
        >> ONCE_REWRITE_TAC [smRecur_def]
        >> fs[CHECK_DELTAS_SET])
    >- (fs[]
        >> rpt STRIP_TAC
        >> `smRecur pat j (SUC x) <= d` by fs[ADD_CLAUSES]
        >> `smRecur pat j x <= smRecur pat j (SUC x)` suffices_by fs[]
        >> qabbrev_tac `L = smRecur pat j (SUC x)`
        >> Cases_on `LENGTH pat < x`
        >- (`smRecur pat j x = x` by (ONCE_REWRITE_TAC[smRecur_def] >> fs[])
            >> simp[]
            >> `(SUC x) <= smRecur pat j (SUC x)` suffices_by simp[Abbr `L`]
            >> metis_tac[SMRECUR_LEM])
        >- (Cases_on `checkDeltaS pat j x`
            >> ONCE_REWRITE_TAC[smRecur_def]
            >> simp[ADD1,Abbr `L`]
            >> `(x + 1) <= smRecur pat j (x + 1)` by metis_tac[SMRECUR_LEM]
            >> fs[])
        )
    );

(* Confirming we only get valid values *)
val SMRECUR_COR_THM = store_thm(
    "SMRECUR_COR_THM",
    ``! pat all_chars j a d . pat <> []
                             /\ j < LENGTH pat
                             /\ 1 <= smRecur pat j d
                             /\ smRecur pat j d <= LENGTH pat
                                ==> smRecur pat j d
                                        IN valid_suf_shifts pat j``,
    rpt STRIP_TAC
    >> `d <= LENGTH pat`
        by (CCONTR_TAC
            >> `d <= smRecur pat j d` by metis_tac[SMRECUR_LEM]
            >> fs[])
    >> Induct_on `LENGTH pat - d`
    >- (rpt STRIP_TAC
        >> `d = LENGTH pat` by simp[]
        >> `LENGTH pat = smRecur pat j d` by fs[SMRECUR_LEM, LESS_EQUAL_ANTISYM]
        >> `LENGTH pat IN valid_suf_shifts pat j` suffices_by fs[]
        >> `checkDeltaS pat j (LENGTH pat)`
                by (qpat_x_assum `LENGTH pat = smRecur pat j d` mp_tac
                    >> ONCE_REWRITE_TAC[smRecur_def]
                    >> simp[]
                    >> rpt STRIP_TAC
                    >> CCONTR_TAC
                    >> fs[]
                    >> `LENGTH pat + 1 <= smRecur pat j (LENGTH pat + 1)` by simp[SMRECUR_LEM]
                    >> `LENGTH pat <> smRecur pat j (LENGHT pat + 1)` by simp[]
                    >> fs[])
        >> ONCE_REWRITE_TAC[CHECK_DELTAS_THM]
        >> fs[])
    >- (rpt STRIP_TAC
        >> `v = LENGTH pat - SUC d` by fs[]
        >> `SUC d <= LENGTH pat` by fs[]
        >> `SUC d <= smRecur pat j (SUC d)`
                by metis_tac[SMRECUR_LEM,LESS_EQ_TRANS]
        >> `smRecur pat j (SUC d) <= LENGTH pat`
                by (`LENGTH pat IN valid_suf_shifts pat j`
                        by rw[valid_suf_shifts_def]
                    >> metis_tac[SMRECUR_BND_THM])
        >> `smRecur pat j (SUC d) IN valid_suf_shifts pat j`
                by (first_x_assum (qspec_then `pat` (qspec_then `SUC d` mp_tac)) >> fs[])
        >> ONCE_REWRITE_TAC[smRecur_def]
        >> Cases_on `LENGTH pat < d`
        >> fs[]
        >> `checkDeltaS pat j d ==> d IN valid_suf_shifts pat j`
                suffices_by (Cases_on `checkDeltaS pat j d` >> fs[ADD1])
        >> `checkDeltaS pat j d ==> 1 <= d`
                suffices_by (ONCE_REWRITE_TAC[CHECK_DELTAS_THM] >> simp[])
        >> STRIP_TAC
        >> `smRecur pat j d = d`
                by (ONCE_REWRITE_TAC[smRecur_def] >> fs[])
        >> fs[])
    );

(* Relationship between smVal function and valid_suf_shift specification *)
val SMVAL_THM = store_thm(
    "SMVAL_THM",
    ``(pat <> []) /\ (j < LENGTH pat)
     ==> (smVal pat j = MIN_SET (valid_suf_shifts pat j))``,
    STRIP_TAC
    >> simp[smVal_def]
    >> `! d. d IN valid_suf_shifts pat j ==> smRecur pat j 1 <= d`
            by (rpt STRIP_TAC
                >> `1 <= d`
                    by (first_assum mp_tac
                        >> ONCE_REWRITE_TAC[CHECK_DELTAS_THM]
                        >> simp[])
                >> simp[SMRECUR_BND_THM])
    >> `smRecur pat j 1 IN valid_suf_shifts pat j`
            by (`1 <= smRecur pat j 1` by simp[SMRECUR_LEM]
                >> `smRecur pat j 1 <= LENGTH pat` by fs[valid_suf_shifts_def]
                >> simp[SMRECUR_COR_THM])
    >> fs[LOWER_BOUND_IS_MIN_SET]
    );

(* Proving bounds on smVal function with valid input *)
val SMVAL_BND = store_thm(
    "SMVAL_BND",
    ``!j . j < LENGTH pat
            ==> 0 < smVal pat j
                /\ smVal pat j <= LENGTH pat``,
    Cases_on `pat = []`
    >- simp[LENGTH]
    >- (simp[SMVAL_THM]
        >> REPEAT strip_tac
        >- (`0 <> MIN_SET (valid_suf_shifts pat j)`
                    suffices_by rw[]
            >> `~(0 IN valid_suf_shifts pat j)`
                    suffices_by metis_tac[SUF_SHIFT_EXISTS_THM,MIN_SET_LEM]
            >> simp[valid_suf_shifts_def])
        >- (`?x. (x IN valid_suf_shifts pat j) /\ (x <= LENGTH pat)`
                suffices_by metis_tac[MIN_SET_LEM, LESS_EQ_TRANS,
                                      MEMBER_NOT_EMPTY]
            >> simp[valid_suf_shifts_def]
            >> qexists_tac `LENGTH pat`
            >> simp[])
        )
    );


(* -- ACTUAL MISMATCH TABLE CONSTRUCTION --  *)
(* Find mismatch table value at particular point based
   on best shift available between suffix mismatch table
   and character mismatch table *)
val mVal_def =
    Define
    `
    mVal calc_smVal pat all_chars j a =
        MAX calc_smVal (cmVal pat all_chars j a)
    `;

(* Generate a row of mismatch table *)
val mSubTab_def =
    Define
    `
    mSubTab pat all_chars j =
        GENLIST (mVal (smVal pat j) pat all_chars j) (LENGTH all_chars)
    `;

(* Generate mismatch table *)
val mTab_def =
    Define
    `
    mTab pat all_chars =
        GENLIST (mSubTab pat all_chars) (LENGTH pat)
    `;

(* Dimensional properties of mTab *)
val MTAB_DIM = store_thm(
    "MTAB_DIM",
    ``(LENGTH (mTab pat all_chars) = LENGTH pat)
     /\ (!j. j < LENGTH pat
             ==> (LENGTH (EL j (mTab pat all_chars))
                  = LENGTH all_chars))``,
    simp[mTab_def,mSubTab_def]
    );

(* Bounds on mTab values for valid inputs *)
val MTAB_BND = store_thm(
    "MTAB_BND",
    ``!a j.  (j < LENGTH pat) /\ (a < LENGTH all_chars)
            ==> 0 < EL a (EL j (mTab pat all_chars))
                /\ EL a (EL j (mTab pat all_chars)) <= LENGTH pat``,
    simp[mTab_def,mSubTab_def,mVal_def]
    >> metis_tac[SMVAL_BND,CMVAL_BND]
    );

(* Important solution skipping capacity of mTab *)
val MTAB_THM = store_thm(
    "MTAB_THM",
    ``!search j k a. ((pat <> [])
      /\ (k <= LENGTH search - LENGTH pat)
      /\ (j < LENGTH pat)
      /\ (!i. (j<i /\ i < LENGTH pat)
              ==> (EL i pat = EL (k+i) search))
      /\ (EL j pat <> EL (k+j) search)
      /\ (a < LENGTH all_chars)
      /\ (EL (k+j) search = EL a all_chars))
      ==>(!d. d < (EL a (EL j (mTab pat all_chars)))
              ==> ~((k+d) IN solutions pat search))``,
    strip_tac
    >> strip_tac
    >> strip_tac
    >> strip_tac
    >> strip_tac
    >> `(EL a (EL j (mTab pat all_chars)) = (smVal pat j)) \/
        (EL a (EL j (mTab pat all_chars)) = (cmVal pat all_chars j a))`
            by rw[mTab_def,mSubTab_def,mVal_def,EL_GENLIST,MAX_DEF]
    >- (fs[]
        >> fs[SMVAL_THM]
        >> `EL j pat <> EL (k+j) search`
                by rw[EQ_SYM_EQ]
        >> drule SUF_SKIP_NOT_SOL
        >> fs[])
    >- (fs[]
        >> fs[CMVAL_THM]
        >> `EL j pat <> EL (k+j) search`
                by rw[EQ_SYM_EQ]
        >> drule CHA_SKIP_NOT_SOL
        >> fs[])
    );



(* -- BOYER-MOORE SEARCH IMPLEMENTATION -- *)
(* Checks to see if pat is prefix of search and skips verified bad alignments
   based on patTab and all_chars if not to recursively find the minimum
   solution. Returning LENGTH search indicates no substrings, returning
   LENGTH search + 1 indicates there's been an error likely due to a malformed
   patTab *)
val bmRecur_def =
    tDefine "bmRecur"
    `
    (bmRecur [] _ _ _ = 0) /\
    (bmRecur _ _ _ [] = 0) /\
    (bmRecur pat patTab all_chars search =
        if
            ~(LENGTH pat <= LENGTH search)
        then
            (LENGTH search)
        else
            let
                (j = checkPrefixRL pat search)
            in
                if
                    ~(j < LENGTH patTab)
                then
                    0
                else
                    let
                        (a = findElem all_chars (EL j search))
                    in
                        if
                            ~(a < LENGTH (EL j patTab))
                        then
                            (LENGTH search + 1)
                        else
                            let
                                (d = EL a (EL j patTab))
                            in
                                if
                                    ~(0 < d)
                                then
                                    (LENGTH search + 1)
                                else
                                    (d + (bmRecur pat patTab
                                            all_chars (DROP d search)))
    )
    `
    (WF_REL_TAC `measure (LENGTH ∘ SND ∘ SND ∘ SND)`
    >> rw[DROP]);

(* Simple theorem for cleaness enforcing one definition
   of bmRecur for non-null lists *)
val BMRECUR_NON_EMPTY_DEF = store_thm(
    "BMRECUR_NON_EMPTY_DEF",
    ``(pat <> []) /\ (search <> [])
    ==>
    (bmRecur pat patTab all_chars search =
     if ¬(LENGTH pat ≤ LENGTH search) then LENGTH search
     else
       (let
          j = checkPrefixRL pat search
        in
          if ¬(j < LENGTH patTab) then 0
          else
            (let
               a = findElem all_chars (EL j search)
             in
               if ¬(a < LENGTH (EL j patTab)) then LENGTH search + 1
               else
                 (let
                    d = EL a (EL j patTab)
                  in
                    if ¬(0 < d) then LENGTH search + 1
                    else
                      d +
                      bmRecur pat patTab all_chars
                        (DROP d search))))
    )``,
    Cases_on `pat`
    >> Cases_on `search`
    >> fs[bmRecur_def]
    );

(* Proves that bmRecur returns correct solutions with valid inputs
   for patTab and all_chars *)
val BMRECUR_THM = store_thm(
    "BMRECUR_THM",
    ``(LENGTH patTab = LENGTH pat)
     /\ (!j. j < LENGTH pat
             ==> (LENGTH (EL j patTab) = LENGTH all_chars))
     /\ (!a j. j < LENGTH pat /\ a < LENGTH all_chars
               ==> 0 < EL a (EL j patTab)
                   /\ EL a (EL j patTab) <= LENGTH pat)
     /\ (!search j k a. (pat <> [])
                         /\ k <= LENGTH search - LENGTH pat
                         /\ j < LENGTH pat
                         /\ (!i. j < i /\ i < LENGTH pat
                                 ==> (EL i pat = EL (k+i) search))
                         /\ (EL j pat <> EL (k+j) search)
                         /\ a < LENGTH all_chars
                         /\ (EL (k+j) search = EL a all_chars)
                         ==> !d. d < EL a (EL j patTab)
                                 ==> ~((k+d) IN solutions pat search))
     ==> (!j. j < LENGTH search ==> MEM (EL j search) all_chars)
         ==> (bmRecur pat patTab all_chars search = solution pat search)``,
    strip_tac
    >> completeInduct_on `LENGTH search`
    >> fs[PULL_FORALL]
    >> rw[]
    >> Cases_on `pat =[]`
    >- (fs[bmRecur_def,solution_def,solutions_def]
        >> rw[IN_INSERT, MIN_SET_LEM,DECIDE ``(a <= 0) ==> (a = 0)``])
    >- (Cases_on `search = []`
        >- (Cases_on `pat`
            >> fs[bmRecur_def,solution_def,solutions_def,MIN_SET_THM])
        >- (rw[BMRECUR_NON_EMPTY_DEF]
            >> qabbrev_tac `j_i = checkPrefixRL pat search`
            >> qabbrev_tac `a_i = findElem all_chars (EL j_i search)`
            >> qabbrev_tac `d_i = EL a_i (EL j_i patTab)`
            >- (rename [`~(LENGTH pat <= LENGTH search)`]
                >> rw[solution_def,solutions_def,MIN_SET_THM])
            >- (rename [`~(j_i < LENGTH pat)`]
                >> `j_i <= LENGTH pat`
                        by rw[Abbr `j_i`, CHECK_PREFIX_RL_BND]
                >> `pat = TAKE (LENGTH pat) search`
                        by metis_tac[DECIDE ``(x<=y) /\ ~(x<y) ==> (x=y)``,
                                     CHECK_PREFIX_RL_MATCH]
                >> pop_assum mp_tac
                >> simp[LIST_EQ_REWRITE,EL_TAKE]
                >> strip_tac
                >> simp[solution_def]
                >> `0 IN solutions pat search`
                        suffices_by metis_tac[DECIDE ``(a <= 0) ==> (a=0)``,
                                              MEMBER_NOT_EMPTY, MIN_SET_LEM,
                                              IN_INSERT]
                >> simp[solutions_def])
            >- (rename [`~(a_i < LENGTH all_chars)`]
                >> `MEM (EL j_i search) all_chars`
                        by rw[]
                >> `a_i = LENGTH all_chars`
                        by rw[Abbr `a_i`,
                              DECIDE ``(x<=y) /\ ~(x<y) ==> (x=y)``,
                              FIND_ELEM_BND]
                >> metis_tac[FIND_ELEM_NO_MATCH])
            >- (rename [`d_i = 0`]
                >> `0 < d_i`
                        by rw[Abbr `d_i`]
                >> fs[])
            >- (rename [`d_i <> 0`]
                >> `bmRecur pat patTab all_chars (DROP d_i search)
                    = solution pat (DROP d_i search)`
                        by fs[LENGTH_DROP,EL_DROP]
                >> simp[]
                >> `(LENGTH pat <= LENGTH search) /\ (d_i <= LENGTH search)
                    /\ (!x. x < d_i ==> ~(x IN solutions pat search))`
                        suffices_by metis_tac[SOL_SHF_THM]
                >> simp[]
                >> strip_tac
                >- (first_x_assum (qspecl_then [`a_i`,`j_i`] mp_tac)
                    >> fs[LESS_EQ_TRANS])
                >- (strip_tac
                    >> first_x_assum (qspecl_then [`search`,`j_i`,`0`,`a_i`,`x`]
                                                  mp_tac)
                    >> fs[Abbr `a_i`, Abbr `j_i`,Abbr `d_i`,
                          CHECK_PREFIX_RL_THM,FIND_ELEM_THM])
                )
            )
        )
    );

(* Calculates lookup table and all_chars to call bmRecur for the first time.
   That is: this implements the boyer-moore substring search algorithm to look
   for the first appearance of a substring in a string *)
val bmSearch_def =
    Define
    `
    bmSearch pat search =
        let
            all_chars = uniqueElems search
        in
            bmRecur pat (mTab pat all_chars) all_chars search
    `;

(* Final proof that the bmSearch function correctly searches
   for the first substring *)
val BMSEARCH_THM = store_thm(
    "BMSEARCH_THM",
    ``bmSearch pat search = solution pat search``,
    simp[bmSearch_def]
    >> irule BMRECUR_THM
    >> rpt conj_tac
    >- metis_tac [MTAB_THM]
    >- rw [MTAB_BND]
    >- rw [MTAB_DIM]
    >- rw [UNIQUE_ELEMS_THM]
    >- rw [MTAB_DIM]
    );

(* STRING SPECIALISATION *)

(* Generate an alphabet with all the characters *)
val alphabet_def =
    Define
    `
    alphabet = GENLIST CHR 256
    `;

val ALPHABET_THM = store_thm(
    "ALPHABET_THM",
    ``! c:char. MEM c alphabet``,
    STRIP_TAC
    >> `? n. (c = CHR n) /\ (n < 256)`
            by rw[ranged_char_nchotomy]
    >> rw[]
    >> ONCE_REWRITE_TAC[alphabet_def]
    >> rw[MEM_GENLIST]
    >> qexists_tac `n`
    >> simp[]);

val ALPHABET_FIND_THM = store_thm(
    "ALPHABET_FIND_THM",
    ``!c. findElem alphabet c = ORD c``,
    STRIP_TAC
    >> `? n. (c = CHR n) /\ (n < 256)`
            by rw[ranged_char_nchotomy]
    >> `MEM c alphabet`
            by (`MEM (EL (ORD c) alphabet) alphabet`
                    suffices_by rw[ALPHABET_THM]
                >> `ORD c < LENGTH alphabet`
                    suffices_by rw[EL_MEM]
                >> `LENGTH alphabet = 256`
                        by (rw[alphabet_def,LENGTH]
                            >> EVAL_TAC)
                >> rw[ORD_CHR])
    >> `findElem alphabet c < LENGTH alphabet`
            by (`findElem alphabet c <> LENGTH alphabet`
                    suffices_by rw[FIND_ELEM_BND, DECIDE ``a <= b /\ a <> b ==> a < b``]
                >> CCONTR_TAC
                >> rw[FIND_ELEM_NO_MATCH])
    >> `EL (findElem alphabet c) alphabet = c`
            by rw[FIND_ELEM_THM]
    >> `EL (findElem alphabet c) alphabet = CHR (findElem alphabet c)`
            by (ONCE_REWRITE_TAC[alphabet_def]
                >> `findElem (GENLIST CHR 256) c < LENGTH (GENLIST CHR 256)`
                        suffices_by rw[EL_GENLIST]
                >> qpat_assum `findElem a c < STRLEN a` mp_tac
                >> ONCE_REWRITE_TAC[alphabet_def]
                >> simp[])
    >> `c = CHR (findElem alphabet c)`
            by fs[]
    >> `ORD (CHR (findElem alphabet c)) = findElem alphabet c`
            by (`findElem alphabet c < 256`
                    suffices_by rw[ORD_CHR_RWT]
                >> `STRLEN alphabet = 256`
                        suffices_by rw[]
                >> ONCE_REWRITE_TAC[alphabet_def]
                >> rw[LENGTH_GENLIST])
    >> `ORD (CHR (findElem alphabet c)) = ORD c`
            suffices_by rw[]
    >> `CHR (findElem alphabet c) = c`
            suffices_by EVAL_TAC
    >> fs[]);

(* Build up a bmRecur specialised to strings *)
val bmRecurString_def =
    tDefine "bmRecurString"
    `
    (bmRecurString [] _ _ = 0) /\
    (bmRecurString  _ _ [] = 0) /\
    (bmRecurString pat patTab search =
        if
            ~(LENGTH pat <= LENGTH search)
        then
            (LENGTH search)
        else
            let
                (j = checkPrefixRL pat search)
            in
                if
                    ~(j < LENGTH patTab)
                then
                    0
                else
                    let
                        (a = ORD (EL j search))
                    in
                        if
                            ~(a < LENGTH (EL j patTab))
                        then
                            (LENGTH search + 1)
                        else
                            let
                                (d = EL a (EL j patTab))
                            in
                                if
                                    ~(0 < d)
                                then
                                    (LENGTH search + 1)
                                else
                                    (d + (bmRecurString pat patTab (DROP d search)))
    )
    `
    (WF_REL_TAC `measure (\(p, t, s). LENGTH s)`
    >> rw[DROP]);

val BMRECUR_STRING_THM = store_thm(
    "BMRECUR_STRING_THM",
    ``bmRecur pat patTab alphabet search = bmRecurString pat patTab search``,
    Cases_on `pat`
    >> ONCE_REWRITE_TAC[bmRecur_def, bmRecurString_def]
    >> simp[]
    >> completeInduct_on `LENGTH search`
    >> rpt STRIP_TAC
    >> Cases_on `search`
    >> ONCE_REWRITE_TAC[bmRecur_def, bmRecurString_def]
    >> simp[ALPHABET_FIND_THM]);

(* Calls bmRecurString instead of bmRecur.
   That is: this implements the boyer-moore substring search algorithm to look
   for the first appearance of a substring in a string - but in ACTUAL string
   types *)
val bmSearchString_def =
    Define
    `
    bmSearchString (pat : string) (search : string) =
        bmRecurString pat (mTab pat alphabet) search
    `;

(* Final proof that the bmSearchString function correctly searches
   for the first substring *)
val BMSEARCH_STRING_THM = store_thm(
    "BMSEARCH_STRING_THM",
    ``bmSearchString pat search = solution pat search``,
    simp[bmSearchString_def]
    >> `bmRecur pat (mTab pat alphabet) alphabet search = solution pat search`
            suffices_by rw[BMRECUR_STRING_THM]
    >> irule BMRECUR_THM
    >> rpt conj_tac
    >- metis_tac[MTAB_THM]
    >- rw[MTAB_BND]
    >- rw[MTAB_DIM]
    >- rw[ALPHABET_THM]
    >- rw[MTAB_DIM]
    );

val _ = export_theory();
