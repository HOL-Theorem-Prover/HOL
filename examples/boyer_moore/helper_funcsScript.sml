open HolKernel boolLib bossLib Parse;

open listTheory;
open rich_listTheory;
open prim_recTheory;
open arithmeticTheory;
open pred_setTheory;
open pairTheory;
open boolTheory;


val _ = new_theory"helper_funcs";

(* -- EXTRACT FUNCTION -- *)
(* General Purpose Sublist extract function *)
val extract_def =
    Define
    `
    (extract _ [] = []) /\
    (extract (0,0) (x::xs) = []) /\
    (extract (SUC n, 0) (x::xs) = []) /\
    (extract (0,SUC m) (x::xs) =
        x::(extract (0,m) xs)
    ) /\
    (extract (SUC n, SUC m) (x::xs) =
        extract (n,m) xs
    )
    `;

(* Basic Extract Properties *)
val EXTRACT_THM = store_thm(
    "EXTRACT_THM",
    ``!i j. j <= LENGTH l
           ==> (extract (i,j) l = GENLIST (\a. EL (a+i) l) (j-i))``,
    Induct_on `l`
    >- rw[extract_def]
    >> map_every Cases_on [`i`,`j`]
    >> rw[extract_def]
    >> rw[GENLIST_CONS]
    >> simp[combinTheory.o_DEF]
    >> simp[ADD_CLAUSES]
    );

val EXTRACT_BIG_THM = store_thm(
    "EXTRACT_BIG_THM",
    ``! i j. j >= LENGTH l
            ==> (extract (i,j) l = GENLIST (\a. EL (a+i) l) (LENGTH l - i))``,
    Induct_on `l`
    >- rw[extract_def]
    >> map_every Cases_on [`i`,`j`]
    >> rw[extract_def,GENLIST_CONS]
    >> simp[combinTheory.o_DEF,ADD_CLAUSES,EL]
    );

val EXTRACT_GEN_THM = store_thm(
    "EXTRACT_GEN_THM",
    ``! i j. extract (i,j) l = GENLIST (\a. EL (a+i) l) (MIN (j - i) (LENGTH l - i))``,
    rpt STRIP_TAC
    >> Cases_on `j<= LENGTH l`
    >- (`MIN (j - i) (LENGTH l - i) = j - i` by simp[MIN_DEF]
        >> rw[EXTRACT_THM])
    >- (`MIN (j - i) (LENGTH l - i) = LENGTH l - i` by simp[MIN_DEF]
        >> rw[EXTRACT_BIG_THM])
    );

(* -- UNIQUE ELEMS FUNCTION -- *)
(* Find all unqiue elements in a list *)
val uniqueElems_def =
    Define
    `
    (uniqueElems [] = []) /\
    (uniqueElems (x::rst) =
        let
            uniTail = uniqueElems rst
        in
            if
                MEM x uniTail
            then
                uniTail
            else
                x::uniTail
    )
    `;

(* Confirming uniqueElems contains everything in the list *)
val UNIQUE_ELEMS_THM = store_thm(
    "UNIQUE_ELEMS_THM",
    ``!i inString. i < LENGTH inString
                  ==> MEM (EL i inString) (uniqueElems inString)``,
    Induct_on `inString`
    >- simp[uniqueElems_def]
    >- (rw[LENGTH]
        >> Cases_on `i`
        >- (simp[EL,uniqueElems_def]
            >> Cases_on `MEM h (uniqueElems inString)`
            >- simp[]
            >- simp[MEM])
        >- (simp[uniqueElems_def]
            >> Cases_on `MEM h (uniqueElems inString)`
            >- simp[EL,uniqueElems_def]
            >- simp[])
        )
    );

(* -- FIND ELEMS FUNCTION -- *)
(* Find first index of element in list. Returns past end of list if no elem *)
val findElem_def =
    Define
    `
    (findElem [] _ = 0) /\
    (findElem (x::rst) e =
        if
            x = e
        then
            0
        else
            1 + findElem rst e
    )
    `;

(* Confirming findElem checks lst for element e and
   find an occurrence *)
val FIND_ELEM_THM = store_thm(
    "FIND_ELEM_THM",
    ``((findElem lst e) < LENGTH lst)
      ==> ((EL (findElem lst e) lst) = e)``,
    strip_tac
    >> Induct_on `lst`
    >- simp[findElem_def]
    >- (strip_tac
        >> ONCE_REWRITE_TAC [findElem_def]
        >> Cases_on `h=e`
        >- simp[]
        >- (simp[]
            >> strip_tac
            >> `EL (SUC (findElem lst e)) (h::lst) = e`
                    suffices_by metis_tac[ADD1]
            >> rw[EL]
            )
        )
    );

(* Confirming findElem returns end of list if and only
   if element not present in list *)
val FIND_ELEM_NO_MATCH = store_thm(
    "FIND_ELEM_NO_MATCH",
    ``((findElem lst e) = LENGTH lst)
     <=> ~(MEM e lst)``,
    Induct_on `lst`
    >- simp[findElem_def,MEM]
    >- (strip_tac
        >> ONCE_REWRITE_TAC [findElem_def, MEM]
        >> Cases_on `h=e`
        >> simp[ADD1]
        )
    );

(* Placing a bound on findElem value *)
val FIND_ELEM_BND = store_thm(
    "FIND_ELEM_BND",
    ``(findElem lst e) <= LENGTH lst``,
    Induct_on `lst`
    >> rw[findElem_def]
    );

(* -- CHECK PAIRS FUNCTION -- *)
(* check if pat is prefix of search from left to right and return failure point.
   Returns LENGTH pat if perfect match *)
val checkPairs_def =
    Define
    `
    (checkPairs [] = 0) /\
    (checkPairs (p::ps) =
        if
            FST p = SND p
        then
            1 + checkPairs ps
        else
            0
    )
    `;

(* Checking that checkPairs correctly finds first point of mismatch *)
val CHECK_PAIRS_THM = store_thm(
    "CHECK_PAIRS_THM",
    ``(checkPairs ps < LENGTH ps)
     ==> ((!i. i < checkPairs ps
               ==> (FST (EL i ps) = SND (EL i ps)))
          /\ (FST (EL (checkPairs ps) ps)
              <> SND (EL (checkPairs ps) ps)))``,
    Induct_on `ps`
    >- fs[checkPairs_def,LENGTH_NIL]
    >- (strip_tac
        >> strip_tac
        >> Cases_on `FST h = SND h`
        >- (`checkPairs ps < LENGTH ps`
                by fs[ADD1,checkPairs_def,LENGTH,LESS_MONO_REV]
            >> `checkPairs (h::ps) = SUC (checkPairs ps)`
                    by fs[checkPairs_def,ADD1]
            >> strip_tac
            >-(strip_tac
               >> Cases_on `i=0`
               >> fs[]
               >> strip_tac
               >> `i < SUC (checkPairs ps)`
                       by fs[]
               >> `PRE i < checkPairs ps`
                       by fs[INV_PRE_LESS,SUC_PRE]
               >> simp[EL_CONS]
               )
            >- simp[PRE,EL_CONS])
        >- (`checkPairs (h::ps) = 0`
                by fs[checkPairs_def]
            >> fs[]))
    );

(* Checking that checkPairs returns end of ps if and only if all pairs match *)
val CHECK_PAIRS_MATCH = store_thm(
    "CHECK_PAIRS_MATCH",
    ``(checkPairs ps = LENGTH ps)
     <=> (!i. (i < LENGTH ps) ==> (FST (EL i ps) = SND (EL i ps)))``,
    Induct_on `ps`
    >- simp[LENGTH_NIL,checkPairs_def]
    >- (strip_tac
        >> rw[EQ_IMP_THM]
        >- (`FST h = SND h`
                by (CCONTR_TAC >> fs[checkPairs_def])
            >> Cases_on `i`
            >- rw[EL]
            >- (`checkPairs ps = LENGTH ps`
                    by fs[checkPairs_def,ADD1]
                >> fs[])
            )
            >- (simp[checkPairs_def]
                >> `FST (EL 0 (h::ps)) = SND (EL 0 (h::ps))` by rw[]
                >> `FST h = SND h` by fs[EL]
                >> simp[]
                >> `!i. i < LENGTH ps
                        ==> (FST (EL (SUC i) (h::ps))
                             = SND (EL (SUC i) (h::ps)))`
                        by fs[EL]
                >> `!i. i < LENGTH ps
                        ==> (FST (EL i ps) = SND (EL i ps))`
                        by fs[EL]
                >> `checkPairs ps = LENGTH ps`
                        by rw[]
                >> simp[ADD1])
        )
    );

(* Placing a bound on checkPairs value *)
val CHECK_PAIRS_BND = store_thm(
    "CHECK_PAIRS_BND",
    ``checkPairs ps <= LENGTH ps``,
    Induct_on `ps`
    >- fs[checkPairs_def]
    >- (strip_tac
        >> Cases_on `FST h = SND h`
        >> fs[checkPairs_def])
    );

(* -- CHECK PREFIX RL FUNCTION -- *)
(* check if pat is prefix of search from right to left and return failure point.
   Returns LENGTH pat if perfect match. Returns LENGTH pat + 1 if search string
   is too short. *)
val checkPrefixRL_def =
    Define
    `
    checkPrefixRL pat search =
        let
            (L = LENGTH pat);
            (S = LENGTH search)
        in
            if
                S < L
            then
                L + 1
            else
                let
                    jLR = checkPairs (ZIP ((REVERSE pat),
                                           (REVERSE (TAKE L search))))
                in
                    if
                        jLR >= L
                    then
                        L
                    else
                        L - (1 + jLR)
    `;

(* Confirming checkPrefixRL checks pat matches search from right
   to left correctly returning first point of failure *)
val CHECK_PREFIX_RL_THM = store_thm(
    "CHECK_PREFIX_RL_THM",
    ``checkPrefixRL pat search < LENGTH pat
     ==> (!i. ((checkPrefixRL pat search) < i
                /\ i < LENGTH pat)
              ==> (EL i pat = EL i search))
         /\ (EL (checkPrefixRL pat search) pat
             <> EL (checkPrefixRL pat search) search)``,
    fs[checkPrefixRL_def]
    >> strip_tac
    >> Cases_on `LENGTH search < LENGTH pat`
    >> fs[]
    >> Cases_on `LENGTH pat = 0`
    >> fs[]
    >> qabbrev_tac `patR = REVERSE pat`
    >> qabbrev_tac `searchPR = REVERSE (TAKE (LENGTH pat) search)`
    >> Cases_on `checkPairs (ZIP (patR,searchPR)) < (LENGTH pat)`
    >> rw[CHECK_PAIRS_BND]
    >> fs[]
    >- (qabbrev_tac `q = LENGTH pat - SUC i`
        >> `PRE (LENGTH pat - q) = i`
                by fs[PRE, Abbr `q`]
        >> `EL i pat = EL q patR`
                by rw[EL_REVERSE,Abbr `patR`]
        >> `EL i search = EL q searchPR`
                by rw[EL_TAKE, EL_REVERSE,Abbr `searchPR`]
        >> `EL q patR = EL q searchPR`
                suffices_by rw[]
        >> `LENGTH patR = LENGTH searchPR`
                by rw[Abbr `patR`, Abbr `searchPR`]
        >> `q < LENGTH patR`
                by (`LENGTH patR = LENGTH pat`
                        by metis_tac[Abbr `patR`, LENGTH_REVERSE]
                    >> `q < LENGTH pat`
                            suffices_by rw[]
                    >> rw[Abbr `q`])
        >> `EL q (ZIP (patR,searchPR)) = (EL q patR,EL q searchPR)`
                by rw[EL_ZIP]
        >> qabbrev_tac `ps = ZIP(patR,searchPR)`
        >> `FST (EL q ps) = SND (EL q ps)`
                suffices_by rw[FST,SND]
        >> `(checkPairs ps < LENGTH ps) /\ (q < checkPairs ps)`
                suffices_by rw[CHECK_PAIRS_THM]
        >> `LENGTH ps = LENGTH pat`
                by metis_tac[Abbr `ps`, Abbr `patR`,
                             LENGTH_REVERSE, LENGTH_ZIP]
        >> fs[])
    >- (qabbrev_tac `ps = ZIP(patR,searchPR)`
        >> qabbrev_tac `q = checkPairs ps`
        >> `PRE (LENGTH pat - q) = LENGTH pat - (q + 1)`
                by fs[PRE,ADD1]
        >> `EL q patR = EL (PRE (LENGTH pat - q)) pat`
                by rw[REVERSE_REVERSE,EL_REVERSE, Abbr `patR`]
        >> `EL q (REVERSE (TAKE (LENGTH pat) search))
            = EL (PRE (LENGTH pat - q)) (TAKE (LENGTH pat) search)`
                by rw[REVERSE_REVERSE,EL_REVERSE]
        >> `EL (PRE (LENGTH pat - q)) (TAKE (LENGTH pat) search)
            = EL (PRE (LENGTH pat - q)) search`
                by rw[EL_TAKE]
        >> `EL q searchPR = EL (PRE (LENGTH pat - q)) search`
                by rw[Abbr `searchPR`]
        >> `EL q patR <> EL q searchPR`
                suffices_by rw[]
        >> `LENGTH patR = LENGTH searchPR`
                by rw[Abbr `patR`, Abbr `searchPR`]
        >> `q < LENGTH patR`
                by (`LENGTH patR = LENGTH pat`
                        by metis_tac[Abbr `patR`, LENGTH_REVERSE]
                    >> `q < LENGTH pat`
                            suffices_by rw[]
                    >> rw[Abbr `q`])
        >> `EL q ps = (EL q patR,EL q searchPR)`
                by rw[Abbr `ps`, EL_ZIP]
        >> `FST (EL q ps) <> SND (EL q ps)`
                suffices_by rw[FST,SND]
        >> `(checkPairs ps < LENGTH ps)`
                suffices_by rw[Abbr `q`, CHECK_PAIRS_THM]
        >> `LENGTH ps = LENGTH pat`
                by metis_tac[Abbr `ps`, Abbr `patR`,
                             LENGTH_REVERSE, LENGTH_ZIP]
        >> fs[])
    );

(* Confirming checkPrefixRL returns end of string if and only
   if no point of failure *)
val CHECK_PREFIX_RL_MATCH = store_thm(
    "CHECK_PREFIX_RL_MATCH",
    ``(checkPrefixRL pat search = LENGTH pat)
     <=> (pat = TAKE (LENGTH pat) search)``,
    rw[EQ_IMP_THM]
    >- (qabbrev_tac `ps = ZIP ((REVERSE pat),
                               (REVERSE (TAKE (LENGTH pat) search)))`
        >> `LENGTH pat <= LENGTH search`
                by fs[checkPrefixRL_def]
        >> `LENGTH pat = LENGTH ps`
                by rw[Abbr `ps`, LENGTH_ZIP,LENGTH_REVERSE,LENGTH_TAKE]
        >> `checkPairs ps = LENGTH ps`
                by fs[Abbr `ps`, checkPrefixRL_def,
                      CHECK_PAIRS_BND, LESS_EQUAL_ANTISYM]
        >> `REVERSE pat = REVERSE (TAKE (LENGTH pat) search)`
                suffices_by rw[REVERSE]
        >> `LENGTH (REVERSE pat) = LENGTH (REVERSE (TAKE (LENGTH pat) search))`
                by rw[LENGTH_REVERSE,LENGTH_TAKE]
        >> `!i. i < LENGTH (REVERSE pat)
                ==> (EL i (REVERSE pat)
                     = EL i (REVERSE (TAKE (LENGTH pat) search)))`
                suffices_by metis_tac[LIST_EQ]
        >> `!i. i < LENGTH ps
                ==> (FST (EL i ps) = SND (EL i ps))`
                suffices_by rw[Abbr `ps`, EL_ZIP]
        >> metis_tac[CHECK_PAIRS_MATCH]
        )
    >-  (rw[checkPrefixRL_def]
        >- (`LENGTH pat <= LENGTH search`
                suffices_by rw[DECIDE ``(a <= b) /\ (b < a) ==> F``,
                               LESS_EQ_TRANS]
            >> Cases_on `LENGTH pat <= LENGTH search`
            >- simp[]
            >- (`LENGTH pat = LENGTH search`
                    by metis_tac[LENGTH_TAKE_EQ]
                >> simp[])
            )
        >- (qabbrev_tac `ps = ZIP ((REVERSE pat),
                                   (REVERSE (TAKE (LENGTH pat) search)))`
            >> `LENGTH pat = LENGTH ps`
                    by rw[Abbr `ps`, LENGTH_REVERSE, LENGTH_ZIP]
            >> `checkPairs ps <> LENGTH ps`
                    by rw[]
            >> `REVERSE pat = REVERSE (TAKE (LENGTH pat) search)`
                    by rw[REVERSE]
            >> `LENGTH (REVERSE pat)
                = LENGTH (REVERSE (TAKE (LENGTH pat) search))`
                    by metis_tac[]
            >> `LENGTH (REVERSE pat) = LENGTH ps`
                    by rw[Abbr `ps`, LENGTH_ZIP]
            >> `!i. i < LENGTH ps ==> (FST (EL i ps) = SND (EL i ps))`
                    by metis_tac[Abbr `ps`,LIST_EQ,EL_ZIP,FST,SND]
            >> fs[CHECK_PAIRS_MATCH]
            )
        )
    );

(* Confirming checkPrefixRL returns one past end of string if and only
   length search < length pattern making prefix check non-sensical *)
val CHECK_PREFIX_RL_ERROR = store_thm(
    "CHECK_PREFIX_RL_ERROR",
    ``(checkPrefixRL pat search = SUC (LENGTH pat))
     <=> (LENGTH search < LENGTH pat)``,
    fs[checkPrefixRL_def]
    );

(* Placing a total bound on checkPrefixRL value *)
val CHECK_PREFIX_RL_ABS_BND = store_thm(
    "CHECK_PREFIX_RL_ABS_BND",
    ``checkPrefixRL pat search <= SUC (LENGTH pat)``,
    fs[checkPrefixRL_def,CHECK_PAIRS_BND]
    );

(* Placing a bound on normal values of checkPrefixRL
   for sensible inputs *)
val CHECK_PREFIX_RL_BND = store_thm(
    "CHECK_PREFIX_RL_BND",
    ``(LENGTH pat <= LENGTH search)
     ==> (checkPrefixRL pat search <= LENGTH pat)``,
    strip_tac
    >> `checkPrefixRL pat search <> SUC (LENGTH pat)`
            by rw[CHECK_PREFIX_RL_ERROR]
    >> `checkPrefixRL pat search <= SUC (LENGTH pat)`
            by rw[CHECK_PREFIX_RL_ABS_BND]
    >> fs[]
    );

val _ = export_theory();