open HolKernel boolLib bossLib BasicProvers;
open pred_setTheory arithmeticTheory listTheory rich_listTheory optionTheory
     pairTheory relationTheory sortingTheory;
open alistTheory;

val _ = new_theory "vec_map";

val _ = temp_tight_equality ();

val every_case_tac = BasicProvers.EVERY_CASE_TAC;

Definition alist_to_vec_def :
  (alist_to_vec l default 0 max = []) /\
  (alist_to_vec [] default (SUC n) max = default :: alist_to_vec [] default n max) /\
  (alist_to_vec ((x,y)::t) default (SUC n) max =
    if SUC n <= max then
       if x = max - SUC n then
          y :: alist_to_vec t default n max
       else if x < max - SUC n then
         alist_to_vec t default (SUC n) max
       else
         default :: alist_to_vec ((x,y)::t) default n max
    else
      [])
End

val alist_to_vec_ind = fetch "-" "alist_to_vec_ind";

Theorem alist_to_vec_correct[local] :
 !l default cur max v.
  SORTED $<= (MAP FST l) /\
  cur <= max /\
  alist_to_vec l default cur max = v
  ==>
  LENGTH v = cur /\
  (!n x. n < cur /\ ALOOKUP l (max - cur + n) = SOME x ==> EL n v = x) /\
  (!n. n < cur /\ ALOOKUP l (max - cur + n) = NONE ==>  EL n v = default)
Proof
 ho_match_mp_tac alist_to_vec_ind
 >> rw [alist_to_vec_def]
 >> `transitive $<=` by srw_tac [ARITH_ss] [transitive_def]
 >> rw []
 >> full_simp_tac (srw_ss()++ARITH_ss) [SORTED_EQ]
 >> Cases_on `n` >> rw [EL_CONS] >> fs []
    >- (FIRST_X_ASSUM match_mp_tac >> rw []
        >> `max - SUC cur <> max + SUC n' - SUC cur` by decide_tac
        >> `max + SUC n' - SUC cur = max + n' - cur` by decide_tac
        >> metis_tac[])
    >- (FIRST_X_ASSUM match_mp_tac >> rw []
        >> `max - SUC cur <> max + SUC n' - SUC cur` by decide_tac
        >> `max + SUC n' - SUC cur = max + n' - cur` by decide_tac
        >> metis_tac[])
    >- (ntac 2 (pop_assum mp_tac) >> rw []
        >> imp_res_tac ALOOKUP_MEM
        >> `MEM (max - SUC cur) (MAP FST l)` by (rw[MEM_MAP] >> metis_tac[FST])
        >> res_tac
        >> full_simp_tac (srw_ss()++ARITH_ss) [])
    >- (FIRST_X_ASSUM match_mp_tac >> rw []
        >> full_simp_tac (srw_ss()++ARITH_ss) []
        >> `max + SUC n' - SUC cur  = max + n' - cur` by decide_tac
        >> metis_tac[])
    >- (FIRST_X_ASSUM match_mp_tac >> rw []
        >> full_simp_tac (srw_ss()++ARITH_ss) []
        >> `max + SUC n' - SUC cur = max + n' - cur` by decide_tac
        >> metis_tac[])
QED

Theorem alist_to_vec_thm :
 !l default max v.
  SORTED $<= (MAP FST l) /\
  alist_to_vec l default max max = v
  ==>
  LENGTH v = max /\
  (!n x. n < max /\ ALOOKUP l n = SOME x ==> EL n v = x) /\
  (!n. n < max /\ ALOOKUP l n = NONE ==>  EL n v = default)
Proof
 rw [] >>
 imp_res_tac alist_to_vec_correct >>
 fs []
QED

Theorem dense_alist_to_vec_correct[local] :
 !y l n.
  MAP FST l = MAP (\x. x + y) (COUNT_LIST (LENGTH l)) /\
  n < LENGTH l
  ==>
  ALOOKUP l (n + y) = SOME (EL n (MAP SND l))
Proof
 Induct_on `n` >>
 rw [] >>
 Cases_on `l` >>
 fs [COUNT_LIST_def] >>
 PairCases_on `h` >>
 fs [MAP_MAP_o, combinTheory.o_DEF] >>
 rw [] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 rw [] >>
 FIRST_X_ASSUM (mp_tac o Q.SPECL [`SUC h0`,`t`]) >>
 rw [] >>
 `!h0 x. h0 + SUC x = x + SUC h0` by decide_tac >>
 full_simp_tac bool_ss []
QED

Theorem dense_alist_to_vec_thm :
 !l n. MAP FST l = COUNT_LIST (LENGTH l) /\ n < LENGTH l
        ==>
       ALOOKUP l n = SOME (EL n (MAP SND l))
Proof
 metis_tac [SIMP_RULE (srw_ss()) [] (Q.SPEC `0` dense_alist_to_vec_correct)]
QED

val _ = export_theory ();
