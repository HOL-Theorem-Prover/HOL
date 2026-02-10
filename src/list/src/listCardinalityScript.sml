Theory listCardinality[bare]
Ancestors pair cardinal list pred_set
Libs
  HolKernel Parse boolLib BasicProvers QLib metisLib
  TotalDefn simpLib boolSimps pred_setLib

fun simp ths = ASM_SIMP_TAC (srw_ss()) ths
val metis_tac = METIS_TAC
fun gvs ths =
  global_simp_tac{elimvars = true, droptrues = true, strip = true,
                  oldestfirst = false} (srw_ss()) ths
fun rw ths = SRW_TAC[]ths


(* ----------------------------------------------------------------------
    cardinality type results
   ---------------------------------------------------------------------- *)

Definition list_def:
  list A = { l | !e. MEM e l ==> e IN A }
End

Theorem list_EMPTY[simp]: list {} = { [] }
Proof
  simp[list_def, EXTENSION] >> Cases >> simp[SF DNF_ss]
QED

Theorem list_SING: list {e} =~ univ(:num)
Proof
  simp[cardeq_def] >> qexists_tac `LENGTH` >>
  simp[list_def, BIJ_IFF_INV] >>
  qexists_tac `GENLIST (K e)` >> simp[MEM_GENLIST, SF DNF_ss] >>
  Induct >> simp[GENLIST_CONS]
QED

Theorem UNIV_list:
  univ(:'a list) = list (univ(:'a))
Proof simp[EXTENSION, list_def]
QED

Theorem list_BIGUNION_EXP:
  list A =~ BIGUNION (IMAGE (\n. {n} CROSS (A ** count n)) univ(:num))
Proof
  match_mp_tac cardleq_ANTISYM >> simp[cardleq_def] >> conj_tac
  >- (simp[INJ_DEF, list_def, SF DNF_ss] >>
      qexists ‘\l. (LENGTH l, (λn. if n < LENGTH l then EL n l else ARB))’ >>
      simp[] >>
      conj_tac
      >- (qx_gen_tac `l` >> strip_tac >>
          simp[set_exp_def] >> metis_tac[MEM_EL]) >>
      simp[FUN_EQ_THM, LIST_EQ_REWRITE] >>
      metis_tac[numLib.DECIDE ``(x = y) <=> ~(x < y) /\ ~(y < x)``]) >>
  qexists ‘λ(n,f). GENLIST f n’ >>
  simp[INJ_DEF, set_exp_def, FORALL_PROD, PULL_EXISTS] >> conj_tac
  >- simp[list_def, MEM_GENLIST, PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  disch_then (fn th => assume_tac th >> mp_tac (Q.AP_TERM ‘LENGTH’ th)) >>
  simp_tac (srw_ss()) [] >> strip_tac >> gvs[] >>
  gvs[LIST_EQ_REWRITE] >> metis_tac[]
QED

Theorem set_exp_count:
  A ** count n =~ { l | (LENGTH l = n) /\ !e. MEM e l ==> e IN A }
Proof
  simp[cardeq_def, BIJ_IFF_INV] >>
  qexists `\f. GENLIST f n` >> simp[MEM_GENLIST] >>
  conj_tac
  >- (qx_gen_tac `f` >> simp[set_exp_def, SF DNF_ss] >> rpt strip_tac >>
      res_tac >> simp[]) >>
  qexists ‘λl m. if m < n then EL m l else ARB’ >> rpt conj_tac
  >- (simp[] >> qx_gen_tac `l` >> strip_tac >>
      simp[set_exp_def] >> metis_tac [MEM_EL])
  >- (qx_gen_tac `f` >> rw[set_exp_def] >> simp[FUN_EQ_THM] >>
      qx_gen_tac `m` >> rw[] >> res_tac >> simp[]) >>
  simp[combinTheory.o_ABS_R] >> qx_gen_tac `l` >> strip_tac >>
  match_mp_tac LIST_EQ >> simp[]
QED

Theorem INFINITE_A_list_BIJ_A:
  INFINITE A ==> list A =~ A
Proof
  strip_tac >>
  assume_tac list_BIGUNION_EXP >>
  `BIGUNION (IMAGE (\n. {n} CROSS (A ** count n)) univ(:num)) =~ A`
    suffices_by metis_tac[cardeq_TRANS] >>
  match_mp_tac cardleq_ANTISYM >> reverse conj_tac
  >- (simp[cardleq_def] >>
      qexists_tac ‘\e. (1, λn. if n = 0 then e else ARB)’ >>
      simp[INJ_DEF, set_exp_def, PULL_EXISTS] >>
      simp[FUN_EQ_THM] >> metis_tac[]) >>
  match_mp_tac CARD_BIGUNION >> simp[SF DNF_ss] >> conj_tac
  >- simp[IMAGE_cardleq_rwt, GSYM INFINITE_Unum] >>
  qx_gen_tac `n` >> Cases_on `0 < n` >> gvs[]
  >- metis_tac[CARDEQ_SUBSET_CARDLEQ, exp_count_cardeq, cardeq_SYM,
               CARDEQ_CROSS_1, cardeq_TRANS] >>
  simp[EMPTY_set_exp, INFINITE_cardleq_INSERT]
QED

Theorem finite_subsets_bijection:
    INFINITE A ==> A =~ { s | FINITE s /\ s SUBSET A }
Proof
  strip_tac >> match_mp_tac cardleq_ANTISYM >> conj_tac
  >- (simp[cardleq_def] >> qexists_tac `\a. {a}` >>
      simp[INJ_DEF]) >>
  `{s | FINITE s /\ s SUBSET A} <<= list A`
    suffices_by metis_tac[CARDEQ_CARDLEQ, INFINITE_A_list_BIJ_A, cardeq_REFL] >>
  simp[cardleq_SURJ] >> disj1_tac >> qexists_tac `LIST_TO_SET` >>
  simp[SURJ_DEF, list_def] >> conj_tac >- simp[SUBSET_DEF] >>
  qx_gen_tac `s` >> strip_tac >> qexists_tac `SET_TO_LIST s` >>
  simp[SET_TO_LIST_INV] >> gvs[SUBSET_DEF]
QED

(* cf. INFINITE_LIST_UNIV |- INFINITE univ(:'a list) *)
Theorem COUNTABLE_LIST_UNIV :
  countable univ(:'a) ==> countable univ(:'a list)
Proof
  rw [UNIV_list] >>
  qspec_then ‘univ(:'a)’ mp_tac (GEN_ALL list_BIGUNION_EXP) >>
  qmatch_abbrev_tac ‘list univ(:'a) =~ s ==> _’ >>
  strip_tac >>
  ‘countable s’ suffices_by metis_tac[CARD_EQ_COUNTABLE] >>
  qunabbrev_tac ‘s’ >>
  irule COUNTABLE_BIGUNION >> rw [] >>
  irule COUNTABLE_CROSS >>
  rw [countable_setexp]
QED

Theorem COUNTABLE_LIST_UNIV' :
  FINITE univ(:'a) ==> countable univ(:'a list)
Proof
  simp[FINITE_IMP_COUNTABLE, COUNTABLE_LIST_UNIV]
QED
