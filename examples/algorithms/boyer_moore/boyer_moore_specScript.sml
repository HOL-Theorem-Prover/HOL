open HolKernel boolLib bossLib Parse;

open listTheory;
open rich_listTheory;
open prim_recTheory;
open arithmeticTheory;
open pred_setTheory;
open pairTheory;
open boolTheory;
open set_lemmasTheory;

val _ = new_theory"boyer_moore_spec";

(*
    SOLUTION DEFINITION AND BEHAVIOUR
    ---------------------------------
                                        *)
(* -- SOLUTION SET -- *)
(* Formal Definition of potential solutions. *)
Definition solutions_def:
  solutions pat search =
  if ~(LENGTH pat <= LENGTH search)
  then
    {}
  else
    {k| k <= LENGTH search - LENGTH pat
        /\ (!i. i < LENGTH pat
                ==> (EL (i+k) search = EL i pat)
           )
    }
End

(* The capacity to skip and produce the same solution set *)
Theorem SOLS_SHF_THM[local]:
  (m <= LENGTH search) /\
  (!d. d < m ==> ~(d IN solutions pat search))
  ==> (!x. x IN solutions pat (DROP m search)
           <=> (m+x) IN solutions pat search)
Proof
    Cases_on `LENGTH search = 0`
    >- (strip_tac
        >> `m=0`
                by simp[]
        >> simp[])
    >- (rw[solutions_def]
        >- fs[]
        >- (rw[EQ_IMP_THM]
            >> `EL (i+x) (DROP m search) = EL ((i+x)+m) search`
                    suffices_by rw[ADD_CLAUSES]
            >> `((i + x) + m) < LENGTH search`
                    suffices_by metis_tac[EL_DROP]
            >> `i + x + m <= i + (LENGTH search - (m + LENGTH pat)) + m`
                    by rw[]
            >> `i + (LENGTH search - (m + LENGTH pat)) + m
                < LENGTH pat + (LENGTH search - (m + LENGTH pat)) + m`
                    by rw[]
            >> `LENGTH pat + (LENGTH search - (m + LENGTH pat)) + m
                = LENGTH search`
                    suffices_by rw[LESS_EQ_LESS_TRANS]
            >> simp[])
        )
QED

(* Shifting capacity of the minimum of the solution set *)
Theorem SOLS_MIN_SHF[local]:
  (m <= LENGTH search) /\
  (!d. d < m ==> ~(d IN solutions pat search)) /\
  (solutions pat (DROP m search) <> {}) /\
  (solutions pat search <> {})
  ==> (m + MIN_SET (solutions pat (DROP m search))
       = MIN_SET (solutions pat search))
Proof
    REPEAT STRIP_TAC
    >> qabbrev_tac `sols_d = solutions pat (DROP m search)`
    >> qabbrev_tac `sols = solutions pat search`
    >> `!x. x IN sols_d <=> m + x IN sols`
            by rw[SOLS_SHF_THM, Abbr `sols`, Abbr `sols_d`]
    >> `(m + MIN_SET sols_d <= MIN_SET sols) /\
        (MIN_SET sols <= m + MIN_SET sols_d)`
            suffices_by rw[LESS_EQUAL_ANTISYM]
    >> STRIP_TAC
    >- (`MIN_SET sols IN sols`
            by fs[MIN_SET_LEM]
        >> `m <= MIN_SET sols`
                by (CCONTR_TAC
                    >> (`?d. (d < m) /\ (d IN sols)`
                            suffices_by metis_tac[])
                    >> qexists_tac `MIN_SET sols`
                    >> fs[])
        >> `(MIN_SET sols - m) IN sols_d`
                by rw[ADD_CLAUSES]
        >> `MIN_SET sols_d <= MIN_SET sols - m`
                by rw[MIN_SET_LEM]
        >> fs[MIN_SET_LEM])
    >- (`MIN_SET sols_d IN sols_d`
            by fs[MIN_SET_LEM]
        >> `m + (MIN_SET sols_d) IN sols`
                by metis_tac[]
        >> fs[MIN_SET_LEM])
QED

(* Shifting a solution set appropriately does not change
   its nullness *)
Theorem SOLS_NULL_EQ[local]:
  m <= LENGTH search /\ (!d. d < m ==> d ∉ solutions pat search)
    ==>
  (solutions pat (DROP m search) = {} <=> solutions pat search = {})
Proof
    REPEAT STRIP_TAC
    >> rw[EQ_IMP_THM]
    >> qabbrev_tac `sols_d = solutions pat (DROP m search)`
    >> qabbrev_tac `sols = solutions pat search`
    >> `!x. x IN sols_d <=> m + x IN sols`
            by rw[SOLS_SHF_THM, Abbr `sols`, Abbr `sols_d`]
    >- (CCONTR_TAC
        >> `?y. y IN sols` by metis_tac[MEMBER_NOT_EMPTY]
        >> `m<=y`
                by (CCONTR_TAC
                    >> `?d. (d < m) /\ (d IN sols)`
                            suffices_by metis_tac[]
                    >> qexists_tac `y`
                    >> fs[])
        >> `(y - m) IN sols_d`
                by rw[ADD_CLAUSES]
        >> `?z. z IN sols_d`
                suffices_by metis_tac[MEMBER_NOT_EMPTY]
        >> qexists_tac `y-m`
        >> fs[])
    >- (CCONTR_TAC
        >> `?y. y IN sols_d`
                by metis_tac[MEMBER_NOT_EMPTY]
        >> `m + y IN sols`
                by metis_tac[ADD_CLAUSES]
        >> `?z. z IN sols`
                suffices_by metis_tac[MEMBER_NOT_EMPTY]
        >> qexists_tac `m + y`
        >> fs[])
QED







(* -- FIRST SOLUTION -- *)
(* The actual solution we want is the minimum of all
   solutions. We include past the end of
   the search string a 'solution'. It is the failure indicator. *)
Definition solution_def:
  solution pat search = MIN_SET ((LENGTH search) INSERT solutions pat search)
End

(* Shifting capacity of the solution*)
val SOL_SHF_THM = store_thm(
    "SOL_SHF_THM",
    ``(LENGTH pat <= LENGTH search) /\
     (m <= LENGTH search) /\
     (!d. d < m ==> ~(d IN solutions pat search))
     ==> (m + solution pat (DROP m search)
          = solution pat search)``,
    rw[solution_def]
    >> Cases_on `solutions pat search = {}`
    >- (`solutions pat (DROP m search) = {}`
            by rw[SOLS_NULL_EQ]
         >> simp[MIN_SET_THM])
    >-  (qabbrev_tac `sols_d = solutions pat (DROP m search)`
         >> qabbrev_tac `sols = solutions pat search`
         >> qabbrev_tac `L = LENGTH search`
         >> qabbrev_tac `P = LENGTH pat`
         >> `sols_d <> {}`
                 by rw[SOLS_NULL_EQ, Abbr `sols`, Abbr `sols_d`]
         >> `MIN_SET (L - m INSERT sols_d) = MIN (L-m) (MIN_SET sols_d)`
                 by (Cases_on `sols_d` >> metis_tac[MIN_SET_THM])
         >> `MIN_SET (L INSERT sols) = MIN L (MIN_SET sols)`
                 by (Cases_on `sols` >> metis_tac[MIN_SET_THM])
         >> `MIN_SET sols <= L`
                 by rw[Abbr `sols`, Abbr `L`, solutions_def,
                       MIN_SET_UPPER_BOUND, DECIDE ``a <= b - c ==> a <= b``]
         >> fs[MIN_DEF,SOLS_MIN_SHF, Abbr `sols_d`, Abbr `sols`])
    );




(* -- CHARACTER MISMATCH SHIFTS -- *)
(* Formal Definition of Valid Character Shifts *)
val valid_cha_shifts_def =
   Define
   `
   valid_cha_shifts pat all_chars j a =
        (j+1) INSERT {d | 1 <= d /\ d <= j
                          /\ (EL (j-d) pat = EL a all_chars)}
   `;

(* Confirmation that a valid character shift exists *)
val CHA_SHIFT_EXISTS_THM = store_thm(
    "CHA_SHIFT_EXISTS_THM",
    ``valid_cha_shifts pat all_chars j a <> {}``,
    rw[valid_cha_shifts_def]
    );

(* Confirmation that skipped shifts not in valid_cha_shifts give
   invalid alignments *)
Theorem CHA_SKIP_NOT_SOL:
  k <= LENGTH search - LENGTH pat
  /\ j < LENGTH pat
  /\ EL j pat <> EL (k+j) search
  /\ EL (k+j) search = EL a all_chars

  ==> !d. d < MIN_SET (valid_cha_shifts pat all_chars j a) ==>
          (k+d) ∉ solutions pat search
Proof
  DISCH_TAC >> fs[] >> rw[]
  >> `d NOTIN valid_cha_shifts pat all_chars j a`
    by metis_tac[CHA_SHIFT_EXISTS_THM, MIN_SET_LEM,
                 DECIDE ``a < b /\ b <= a ==> F``]
  >> `d < j + 1`
    by (irule MIN_SET_IS_LOWER_BOUND
        >> rpt conj_tac
        >> qexists_tac `valid_cha_shifts pat all_chars j a`
        >> rw[valid_cha_shifts_def])
  >> fs[valid_cha_shifts_def]
  >> Cases_on ‘d = 0’
  >- (rw[solutions_def] >> metis_tac[])
  >- (fs[] >> rw[solutions_def] >> DISJ2_TAC >> qexists_tac `j - d` >>
      simp[ADD_CLAUSES])
QED

(* -- SUFFIX MATCH SHIFTS -- *)
(* Formal Definition of Valid Suffix Shifts *)
val valid_suf_shifts_def =
    Define
    `
    valid_suf_shifts pat j  =
        {d | 1 <= d /\ d <= LENGTH pat
            /\ (!i. (MAX (j+1) d <= i) /\ (i <= LENGTH pat - 1)
                    ==> (EL (i-d) pat = EL i pat))
            /\ ((d >= j+1) \/ (EL (j-d) pat <> EL j pat))
        }
    `;

(* Confirmation that a valid suffix shift exists in correct circumstances *)
val SUF_SHIFT_EXISTS_THM = store_thm(
    "SUF_SHIFT_EXISTS_THM",
    ``j < LENGTH pat ==> valid_suf_shifts pat j <> {}``,
    rw[valid_suf_shifts_def]
    >> Cases_on `pat`
    >- fs[]
    >-(simp[EXTENSION]
       >> qexists_tac `SUC (LENGTH t)`
       >> simp[]
       >> fs[])
    );

(* Confirmation that skipped shifts not in valid_suf_shifts give
   invalid alignments *)
val SUF_SKIP_NOT_SOL = store_thm(
    "SUF_SKIP_NOT_SOL",
    ``((k <= LENGTH search - LENGTH pat) /\
      (j < LENGTH pat)
    /\ (!i. (j<i /\ i < LENGTH pat)
           ==> (EL i pat = EL (k+i) search))
    /\ (EL j pat <> EL (k+j) search)
    )
    ==> (!d. d < MIN_SET (valid_suf_shifts pat j)
           ==> ~((k+d) IN solutions pat search)
        )
    ``,
    rw[solutions_def]
    >> Cases_on `d = 0`
    >- (simp[] >> metis_tac[])
    >- (`d > 0`
            by rw[NOT_ZERO_LT_ZERO]
        >> Cases_on `(d < j+1) /\ (EL (j- d) pat = EL j pat)`
        >- (qabbrev_tac `q = j - d`
            >> `q < LENGTH pat`
                    by simp[ADD_CLAUSES, Abbr `q`]
            >> `EL (q + d) pat <> EL (d + (q + k)) search`
                    by rw[Abbr `q`]
            >> `EL q pat = EL (q + d) pat`
                    by rw[Abbr `q`]
            >> Cases_on `d + k <= LENGTH search - LENGTH pat`
            >> fs[]
            >> `EL (d + (k + q)) search = EL (d + (q + k)) search`
                    by rw[ADD_CLAUSES]
            >> `EL q pat <> EL (d + (q + k)) search`
                    by metis_tac[]
            >> qexists_tac `q`
            >> rw[])
        >- (`d NOTIN valid_suf_shifts pat j`
                by metis_tac[SUF_SHIFT_EXISTS_THM,
                             MIN_SET_LEM,
                            DECIDE ``a < b /\ b <= a
                                     ==> F``]
            >> pop_assum mp_tac
            >> simp[valid_suf_shifts_def]
            >> reverse (rw [])
            >- fs[]
            >- (DISJ2_TAC
                >> qexists_tac `i - d`
                >> simp[])
            >-(`MIN_SET (valid_suf_shifts pat j) <= LENGTH pat`
                    suffices_by simp[]
                >> irule MIN_SET_UPPER_BOUND
                >> rpt conj_tac
                >- rw[valid_suf_shifts_def]
                >- simp[SUF_SHIFT_EXISTS_THM])
            )
        )
    );

val _ = export_theory();
