open HolKernel Parse boolLib bossLib;
open arithmeticTheory
open logrootTheory
open listTheory
open alistTheory
open pred_setTheory
open dep_rewrite

val _ = new_theory "sptree";

(* A log-time random-access, extensible array implementation with union.

   The "array" can be gappy: there doesn't have to be an element at
   any particular index, and, being a finite thing, there is obviously
   a maximum index past which there are no elements at all. It is
   possible to update at an index past the current maximum index. It
   is also possible to delete values at any index.

   Should EVAL well.

   The insert, delete and union operations all preserve a
   well-formedness condition ("wf") that ensures there is only one
   possible representation for any given finite-map.

   It is tricky to traverse the array and extract a list of elements.
   There are three array->list operations defined:
   - toSortedAList: produces an assocation list in index order.
   - toAList: produces an association list in a mixed-up order. Defined via
     foldi, and related to foldi and mapi by theorems. Slowest to EVAL.
   - toList: roughly equals MAP SND (toAList t), although in a different mixed
     up order. By far the fastest to EVAL.
*)

val _ = Datatype`spt = LN | LS 'a | BN spt spt | BS spt 'a spt`
(* Leaf-None, Leaf-Some, Branch-None, Branch-Some *)

Type num_map[pp] = “:'a spt”
Type num_set[pp] = “:unit spt”

val _ = overload_on ("isEmpty", ``\t. t = LN``)

val wf_def = Define`
  (wf LN <=> T) /\
  (wf (LS a) <=> T) /\
  (wf (BN t1 t2) <=> wf t1 /\ wf t2 /\ ~(isEmpty t1 /\ isEmpty t2)) /\
  (wf (BS t1 a t2) <=> wf t1 /\ wf t2 /\ ~(isEmpty t1 /\ isEmpty t2))
`;

Definition lookup_def[nocompute]:
  (lookup k LN = NONE) /\
  (lookup k (LS a) = if k = 0 then SOME a else NONE) /\
  (lookup k (BN t1 t2) =
     if k = 0 then NONE
     else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2)) /\
  (lookup k (BS t1 a t2) =
     if k = 0 then SOME a
     else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2))
Termination WF_REL_TAC `measure FST` >> simp[DIV_LT_X]
End

Theorem lookup_rwts[simp]:
  lookup k LN = NONE /\
  lookup 0 (LS a) = SOME a /\
  lookup 0 (BN t1 t2) = NONE /\
  lookup 0 (BS t1 a t2) = SOME a
Proof
  simp[lookup_def]
QED

Definition insert_def[nocompute]:
  (insert k a LN = if k = 0 then LS a
                     else if EVEN k then BN (insert ((k-1) DIV 2) a LN) LN
                     else BN LN (insert ((k-1) DIV 2) a LN)) /\
  (insert k a (LS a') =
     if k = 0 then LS a
     else if EVEN k then BS (insert ((k-1) DIV 2) a LN) a' LN
     else BS LN a' (insert ((k-1) DIV 2) a LN)) /\
  (insert k a (BN t1 t2) =
     if k = 0 then BS t1 a t2
     else if EVEN k then BN (insert ((k - 1) DIV 2) a t1) t2
     else BN t1 (insert ((k - 1) DIV 2) a t2)) /\
  (insert k a (BS t1 a' t2) =
     if k = 0 then BS t1 a t2
     else if EVEN k then BS (insert ((k - 1) DIV 2) a t1) a' t2
     else BS t1 a' (insert ((k - 1) DIV 2) a t2))
Termination
  WF_REL_TAC `measure FST` >> simp[DIV_LT_X]
End

val insert_ind = theorem "insert_ind";

val mk_BN_def = Define `
  (mk_BN LN LN = LN) /\
  (mk_BN t1 t2 = BN t1 t2)`;

val mk_BS_def = Define `
  (mk_BS LN x LN = LS x) /\
  (mk_BS t1 x t2 = BS t1 x t2)`;

val delete_def = zDefine`
  (delete k LN = LN) /\
  (delete k (LS a) = if k = 0 then LN else LS a) /\
  (delete k (BN t1 t2) =
     if k = 0 then BN t1 t2
     else if EVEN k then
       mk_BN (delete ((k - 1) DIV 2) t1) t2
     else
       mk_BN t1 (delete ((k - 1) DIV 2) t2)) /\
  (delete k (BS t1 a t2) =
     if k = 0 then BN t1 t2
     else if EVEN k then
       mk_BS (delete ((k - 1) DIV 2) t1) a t2
     else
       mk_BS t1 a (delete ((k - 1) DIV 2) t2))
`;

val fromList_def = Define`
  fromList l = SND (FOLDL (\(i,t) a. (i + 1, insert i a t)) (0,LN) l)
`;

Definition size_def[simp]:
  (size LN = 0) /\
  (size (LS a) = 1) /\
  (size (BN t1 t2) = size t1 + size t2) /\
  (size (BS t1 a t2) = size t1 + size t2 + 1)
End

Theorem insert_notEmpty[simp]: ~isEmpty (insert k a t)
Proof
  Cases_on `t` >> rw[Once insert_def]
QED

val wf_insert = store_thm(
  "wf_insert",
  ``!k a t. wf t ==> wf (insert k a t)``,
  ho_match_mp_tac (theorem "insert_ind") >>
  rpt strip_tac >>
  simp[Once insert_def] >> rw[wf_def, insert_notEmpty] >> fs[wf_def]);

val mk_BN_thm = prove(
  ``!t1 t2. mk_BN t1 t2 =
            if isEmpty t1 /\ isEmpty t2 then LN else BN t1 t2``,
  REPEAT Cases >> EVAL_TAC);

val mk_BS_thm = prove(
  ``!t1 t2. mk_BS t1 x t2 =
            if isEmpty t1 /\ isEmpty t2 then LS x else BS t1 x t2``,
  REPEAT Cases >> EVAL_TAC);

val wf_delete = store_thm(
  "wf_delete",
  ``!t k. wf t ==> wf (delete k t)``,
  Induct >> rw[wf_def, delete_def, mk_BN_thm, mk_BS_thm] >>
  rw[wf_def] >> rw[] >> fs[] >> metis_tac[]);

Theorem lookup_insert1[simp]: !k a t. lookup k (insert k a t) = SOME a
Proof
  ho_match_mp_tac (theorem "insert_ind") >> rpt strip_tac >>
  simp[Once insert_def] >> rw[lookup_def]
QED

val DIV2_EQ_DIV2 = prove(
  ``(m DIV 2 = n DIV 2) <=>
      (m = n) \/
      (n = m + 1) /\ EVEN m \/
      (m = n + 1) /\ EVEN n``,
  `0 < 2` by simp[] >>
  map_every qabbrev_tac [`nq = n DIV 2`, `nr = n MOD 2`] >>
  qspec_then `2` mp_tac DIVISION >> asm_simp_tac bool_ss [] >>
  disch_then (qspec_then `n` mp_tac) >> asm_simp_tac bool_ss [] >>
  map_every qabbrev_tac [`mq = m DIV 2`, `mr = m MOD 2`] >>
  qspec_then `2` mp_tac DIVISION >> asm_simp_tac bool_ss [] >>
  disch_then (qspec_then `m` mp_tac) >> asm_simp_tac bool_ss [] >>
  rw[] >> markerLib.RM_ALL_ABBREVS_TAC >>
  simp[EVEN_ADD, EVEN_MULT] >>
  `!p. p < 2 ==> (EVEN p <=> (p = 0))`
    by (rpt strip_tac >> `(p = 0) \/ (p = 1)` by decide_tac >> simp[]) >>
  simp[]);

val EVEN_PRE = prove(
  ``x <> 0 ==> (EVEN (x - 1) <=> ~EVEN x)``,
  Induct_on `x` >> simp[] >> Cases_on `x` >> fs[] >>
  simp_tac (srw_ss()) [EVEN]);

val lookup_insert = store_thm(
  "lookup_insert",
  ``!k2 v t k1. lookup k1 (insert k2 v t) =
                if k1 = k2 then SOME v else lookup k1 t``,
  ho_match_mp_tac (theorem "insert_ind") >> rpt strip_tac >>
  simp[Once insert_def] >> rw[lookup_def] >> simp[] >| [
    fs[lookup_def] >> pop_assum mp_tac >> Cases_on `k1 = 0` >> simp[] >>
    COND_CASES_TAC >> simp[lookup_def, DIV2_EQ_DIV2, EVEN_PRE],
    fs[lookup_def] >> pop_assum mp_tac >> Cases_on `k1 = 0` >> simp[] >>
    COND_CASES_TAC >> simp[lookup_def, DIV2_EQ_DIV2, EVEN_PRE] >>
    rpt strip_tac >> metis_tac[EVEN_PRE],
    fs[lookup_def] >> COND_CASES_TAC >>
    simp[lookup_def, DIV2_EQ_DIV2, EVEN_PRE],
    fs[lookup_def] >> COND_CASES_TAC >>
    simp[lookup_def, DIV2_EQ_DIV2, EVEN_PRE] >>
    rpt strip_tac >> metis_tac[EVEN_PRE],
    simp[DIV2_EQ_DIV2, EVEN_PRE],
    simp[DIV2_EQ_DIV2, EVEN_PRE] >> COND_CASES_TAC
    >- metis_tac [EVEN_PRE] >> simp[],
    simp[DIV2_EQ_DIV2, EVEN_PRE],
    simp[DIV2_EQ_DIV2, EVEN_PRE] >> COND_CASES_TAC
    >- metis_tac [EVEN_PRE] >> simp[]
  ])

val union_def = Define`
  (union LN t = t) /\
  (union (LS a) t =
     case t of
       | LN => LS a
       | LS b => LS a
       | BN t1 t2 => BS t1 a t2
       | BS t1 _ t2 => BS t1 a t2) /\
  (union (BN t1 t2) t =
     case t of
       | LN => BN t1 t2
       | LS a => BS t1 a t2
       | BN t1' t2' => BN (union t1 t1') (union t2 t2')
       | BS t1' a t2' => BS (union t1 t1') a (union t2 t2')) /\
  (union (BS t1 a t2) t =
     case t of
       | LN => BS t1 a t2
       | LS a' => BS t1 a t2
       | BN t1' t2' => BS (union t1 t1') a (union t2 t2')
       | BS t1' a' t2' => BS (union t1 t1') a (union t2 t2'))
`;

Theorem isEmpty_union[simp]:
  isEmpty (union m1 m2) <=> isEmpty m1 /\ isEmpty m2
Proof
  map_every Cases_on [`m1`, `m2`] >> simp[union_def]
QED

val wf_union = store_thm(
  "wf_union",
  ``!m1 m2. wf m1 /\ wf m2 ==> wf (union m1 m2)``,
  Induct >> simp[wf_def, union_def] >>
  Cases_on `m2` >> simp[wf_def,isEmpty_union] >>
  metis_tac[]);

val optcase_lemma = prove(
  ``(case opt of NONE => NONE | SOME v => SOME v) = opt``,
  Cases_on `opt` >> simp[]);

val lookup_union = store_thm(
  "lookup_union",
  ``!m1 m2 k. lookup k (union m1 m2) =
              case lookup k m1 of
                NONE => lookup k m2
              | SOME v => SOME v``,
  Induct >> simp[lookup_def] >- simp[union_def] >>
  Cases_on `m2` >> simp[lookup_def, union_def] >>
  rw[optcase_lemma]);

val inter_def = Define`
  (inter LN t = LN) /\
  (inter (LS a) t =
     case t of
       | LN => LN
       | LS b => LS a
       | BN t1 t2 => LN
       | BS t1 _ t2 => LS a) /\
  (inter (BN t1 t2) t =
     case t of
       | LN => LN
       | LS a => LN
       | BN t1' t2' => mk_BN (inter t1 t1') (inter t2 t2')
       | BS t1' a t2' => mk_BN (inter t1 t1') (inter t2 t2')) /\
  (inter (BS t1 a t2) t =
     case t of
       | LN => LN
       | LS a' => LS a
       | BN t1' t2' => mk_BN (inter t1 t1') (inter t2 t2')
       | BS t1' a' t2' => mk_BS (inter t1 t1') a (inter t2 t2'))
`;

val inter_eq_def = Define`
  (inter_eq LN t = LN) /\
  (inter_eq (LS a) t =
     case t of
       | LN => LN
       | LS b => if a = b then LS a else LN
       | BN t1 t2 => LN
       | BS t1 b t2 => if a = b then LS a else LN) /\
  (inter_eq (BN t1 t2) t =
     case t of
       | LN => LN
       | LS a => LN
       | BN t1' t2' => mk_BN (inter_eq t1 t1') (inter_eq t2 t2')
       | BS t1' a t2' => mk_BN (inter_eq t1 t1') (inter_eq t2 t2')) /\
  (inter_eq (BS t1 a t2) t =
     case t of
       | LN => LN
       | LS a' => if a' = a then LS a else LN
       | BN t1' t2' => mk_BN (inter_eq t1 t1') (inter_eq t2 t2')
       | BS t1' a' t2' =>
           if a' = a then
             mk_BS (inter_eq t1 t1') a (inter_eq t2 t2')
           else mk_BN (inter_eq t1 t1') (inter_eq t2 t2'))`;

val difference_def = Define`
  (difference LN t = LN) /\
  (difference (LS a) t =
     case t of
       | LN => LS a
       | LS b => LN
       | BN t1 t2 => LS a
       | BS t1 b t2 => LN) /\
  (difference (BN t1 t2) t =
     case t of
       | LN => BN t1 t2
       | LS a => BN t1 t2
       | BN t1' t2' => mk_BN (difference t1 t1') (difference t2 t2')
       | BS t1' a t2' => mk_BN (difference t1 t1') (difference t2 t2')) /\
  (difference (BS t1 a t2) t =
     case t of
       | LN => BS t1 a t2
       | LS a' => BN t1 t2
       | BN t1' t2' => mk_BS (difference t1 t1') a (difference t2 t2')
       | BS t1' a' t2' => mk_BN (difference t1 t1') (difference t2 t2'))`;

val wf_mk_BN = prove(
  ``!t1 t2. wf (mk_BN t1 t2) <=> wf t1 /\ wf t2``,
  map_every Cases_on [`t1`,`t2`] >> fs [mk_BN_def,wf_def]);

val wf_mk_BS = prove(
  ``!t1 x t2. wf (mk_BS t1 x t2) <=> wf t1 /\ wf t2``,
  map_every Cases_on [`t1`,`t2`] >> fs [mk_BS_def,wf_def]);

val wf_inter = store_thm(
  "wf_inter[simp]",
  ``!m1 m2. wf (inter m1 m2)``,
  Induct >> simp[wf_def, inter_def] >>
  Cases_on `m2` >> simp[wf_def,wf_mk_BS,wf_mk_BN]);

val lookup_mk_BN = prove(
  ``lookup k (mk_BN t1 t2) = lookup k (BN t1 t2)``,
  map_every Cases_on [`t1`,`t2`] >> fs [mk_BN_def,lookup_def]);

val lookup_mk_BS = prove(
  ``lookup k (mk_BS t1 x t2) = lookup k (BS t1 x t2)``,
  map_every Cases_on [`t1`,`t2`] >> fs [mk_BS_def,lookup_def]);

val lookup_inter = store_thm(
  "lookup_inter",
  ``!m1 m2 k. lookup k (inter m1 m2) =
              case (lookup k m1,lookup k m2) of
              | (SOME v, SOME w) => SOME v
              | _ => NONE``,
  Induct >> simp[lookup_def] >> Cases_on `m2` >>
  simp[lookup_def, inter_def, lookup_mk_BS, lookup_mk_BN] >>
  rw[optcase_lemma] >> BasicProvers.CASE_TAC);

val lookup_inter_eq = store_thm(
  "lookup_inter_eq",
  ``!m1 m2 k. lookup k (inter_eq m1 m2) =
              case lookup k m1 of
              | NONE => NONE
              | SOME v => (if lookup k m2 = SOME v then SOME v else NONE)``,
  Induct >> simp[lookup_def] >> Cases_on `m2` >>
  simp[lookup_def, inter_eq_def, lookup_mk_BS, lookup_mk_BN] >>
  rw[optcase_lemma] >> REPEAT BasicProvers.CASE_TAC >>
  fs [lookup_def, lookup_mk_BS, lookup_mk_BN]);

val lookup_inter_EQ = store_thm("lookup_inter_EQ",
  ``((lookup x (inter t1 t2) = SOME y) <=>
       (lookup x t1 = SOME y) /\ lookup x t2 <> NONE) /\
    ((lookup x (inter t1 t2) = NONE) <=>
       (lookup x t1 = NONE) \/ (lookup x t2 = NONE))``,
  fs [lookup_inter] \\ BasicProvers.EVERY_CASE_TAC);

val lookup_inter_assoc = store_thm("lookup_inter_assoc",
  ``lookup x (inter t1 (inter t2 t3)) =
    lookup x (inter (inter t1 t2) t3)``,
  fs [lookup_inter] \\ BasicProvers.EVERY_CASE_TAC)

val lookup_difference = store_thm(
  "lookup_difference",
  ``!m1 m2 k. lookup k (difference m1 m2) =
              if lookup k m2 = NONE then lookup k m1 else NONE``,
  Induct >> simp[lookup_def] >> Cases_on `m2` >>
  simp[lookup_def, difference_def, lookup_mk_BS, lookup_mk_BN] >>
  rw[optcase_lemma] >> REPEAT BasicProvers.CASE_TAC >>
  fs [lookup_def, lookup_mk_BS, lookup_mk_BN])

Definition lrnext_def[nocompute]:
  lrnext n = if n = 0 then 1 else 2 * lrnext ((n - 1) DIV 2)
Termination
  WF_REL_TAC `measure I` \\ fs [DIV_LT_X] \\ REPEAT STRIP_TAC \\ DECIDE_TAC
End

Triviality silly:
  NUMERAL (SUC x) = SUC x /\
  ZERO + ZERO = 0 /\
  BIT2 n <> 0 /\
  (x + x) DIV 2 = x /\
  (BIT2 n - 1) DIV 2 = n
Proof
  reverse (rpt conj_tac)
  >- (simp_tac bool_ss [BIT2, SimpL “$DIV”, ONE, ADD_CLAUSES,
                        SUB_MONO_EQ, SUB_0] >>
      simp[ADD_DIV_RWT, ADD1] >>
      metis_tac[MULT_DIV, DECIDE “0 < 2”, MULT_COMM])
  >- simp_tac (srw_ss()) [DECIDE “n + n = n * 2”, MULT_DIV]
  >- REWRITE_TAC[BIT2, ADD_CLAUSES, numTheory.NOT_SUC] >>
  simp[NUMERAL_DEF, ALT_ZERO]
QED
Theorem lrnext_thm[compute]:
  (lrnext ZERO = 1) /\
  (!n. lrnext (BIT1 n) = 2 * lrnext n) /\
  (!n. lrnext (BIT2 n) = 2 * lrnext n) /\
  (!a. lrnext 0 = 1) /\
  (!n a. lrnext (NUMERAL n) = lrnext n)
Proof
  REPEAT STRIP_TAC
  THEN1 simp[ALT_ZERO, Once lrnext_def]
  THEN1 (simp[Once lrnext_def, SimpLHS] >>
         REWRITE_TAC[BIT1, ADD_CLAUSES, numTheory.NOT_SUC,
                     SUB_MONO_EQ, SUB_0, silly])
  THEN1 (simp[Once lrnext_def, SimpLHS] >> REWRITE_TAC [silly])
  THEN1 simp[Once lrnext_def]
  THEN1 simp[NUMERAL_DEF]
QED

Theorem lrnext_eq:
  !n. sptree$lrnext n = 2 ** (LOG 2 (n + 1))
Proof
  strip_tac >> completeInduct_on `n` >> rw[] >>
  rw[Once lrnext_def] >>
  first_x_assum $ qspec_then `(n - 1) DIV 2` mp_tac >>
  impl_tac >> rw[] >- simp[DIV_LT_X] >>
  simp[GSYM EXP] >> Cases_on `EVEN n` >>
  gvs[GSYM ODD_EVEN] >> imp_res_tac EVEN_ODD_EXISTS >> gvs[]
  >- (`(2 * m - 1) DIV 2 = m - 1` by simp[DIV_EQ_X] >> simp[LOG_add_digit])
  >- simp[Once LOG_RWT, SimpRHS, ADD1]
QED

Definition domain_def[simp,nocompute]:
  domain LN = {} /\
  domain (LS _) = {0} /\
  domain (BN t1 t2) =
     IMAGE (\n. 2 * n + 2) (domain t1) UNION
     IMAGE (\n. 2 * n + 1) (domain t2) /\
  domain (BS t1 _ t2) =
     {0} UNION IMAGE (\n. 2 * n + 2) (domain t1) UNION
     IMAGE (\n. 2 * n + 1) (domain t2)
End

Theorem FINITE_domain[simp]: FINITE (domain t)
Proof Induct_on `t` >> simp[]
QED

val DIV2 = DIVISION |> Q.SPEC `2` |> REWRITE_RULE [DECIDE ``0 < 2``]

val even_lem = Q.prove(
  `EVEN k /\ k <> 0 ==> (2 * ((k - 1) DIV 2) + 2 = k)`,
  qabbrev_tac `k0 = k - 1`  >>
  strip_tac >> `k = k0 + 1` by simp[Abbr`k0`] >>
  pop_assum SUBST_ALL_TAC >> qunabbrev_tac `k0` >>
  fs[EVEN_ADD] >>
  assume_tac (Q.SPEC `k0` DIV2) >>
  map_every qabbrev_tac [`q = k0 DIV 2`, `r = k0 MOD 2`] >>
  markerLib.RM_ALL_ABBREVS_TAC >>
  fs[EVEN_ADD, EVEN_MULT] >>
  `(r = 0) \/ (r = 1)` by simp[] >> fs[])

val odd_lem = Q.prove(
  `~EVEN k /\ k <> 0 ==> (2 * ((k - 1) DIV 2) + 1 = k)`,
  qabbrev_tac `k0 = k - 1`  >>
  strip_tac >> `k = k0 + 1` by simp[Abbr`k0`] >>
  pop_assum SUBST_ALL_TAC >> qunabbrev_tac `k0` >>
  fs[EVEN_ADD] >>
  assume_tac (Q.SPEC `k0` DIV2) >>
  map_every qabbrev_tac [`q = k0 DIV 2`, `r = k0 MOD 2`] >>
  markerLib.RM_ALL_ABBREVS_TAC >>
  fs[EVEN_ADD, EVEN_MULT] >>
  `(r = 0) \/ (r = 1)` by simp[] >> fs[])

val even_lem' = CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ])) even_lem
val odd_lem' = CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ])) odd_lem

val even_imposs = Q.prove(
  ‘EVEN n ==> !m. n <> 2 * m + 1’,
  rpt strip_tac >> fs[EVEN_ADD, EVEN_MULT]);
val odd_imposs = Q.prove(
  ‘~EVEN n ==> !m. n <> 2 * m + 2’,
  rpt strip_tac >> fs[EVEN_ADD, EVEN_MULT]);

fun writeL th = CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))

Theorem IN_domain:
  !n x t1 t2.
      (n IN domain LN <=> F) /\
      (n IN domain (LS x) <=> (n = 0)) /\
      (n IN domain (BN t1 t2) <=>
         n <> 0 /\ (if EVEN n then ((n-1) DIV 2) IN domain t1
                    else ((n-1) DIV 2) IN domain t2)) /\
      (n IN domain (BS t1 x t2) <=>
         (n = 0) \/ (if EVEN n then ((n-1) DIV 2) IN domain t1
                     else ((n-1) DIV 2) IN domain t2))
Proof
  simp[domain_def] >> rpt strip_tac >> Cases_on ‘n = 0’ >> simp[] >>
  Cases_on ‘EVEN n’ >> simp[] >>
  (drule_then assume_tac even_imposs ORELSE drule_then assume_tac odd_imposs) >>
  simp[] >>
  (drule_all_then writeL even_lem' ORELSE drule_all_then writeL odd_lem') >>
  simp[]
QED

val size_insert = Q.store_thm(
  "size_insert",
  `!k v m. size (insert k v m) = if k IN domain m then size m else size m + 1`,
  ho_match_mp_tac insert_ind >> rpt conj_tac >> simp[] >>
  rpt strip_tac >> simp[Once insert_def]
  >- rw[]
  >- rw[]
  >- (Cases_on `k = 0` >> simp[] >> fs[] >> Cases_on `EVEN k` >> fs[]
      >- (`!n. k <> 2 * n + 1` by (rpt strip_tac >> fs[EVEN_ADD, EVEN_MULT]) >>
          qabbrev_tac `k2 = (k - 1) DIV 2` >>
          `k = 2 * k2 + 2` suffices_by rw[] >>
          simp[Abbr`k2`, even_lem]) >>
      `!n. k <> 2 * n + 2` by (rpt strip_tac >> fs[EVEN_ADD, EVEN_MULT]) >>
      qabbrev_tac `k2 = (k - 1) DIV 2` >>
      `k = 2 * k2 + 1` suffices_by rw[] >>
      simp[Abbr`k2`, odd_lem])
  >- (Cases_on `k = 0` >> simp[] >> fs[] >> Cases_on `EVEN k` >> fs[]
      >- (`!n. k <> 2 * n + 1` by (rpt strip_tac >> fs[EVEN_ADD, EVEN_MULT]) >>
          qabbrev_tac `k2 = (k - 1) DIV 2` >>
          `k = 2 * k2 + 2` suffices_by rw[] >>
          simp[Abbr`k2`, even_lem]) >>
      `!n. k <> 2 * n + 2` by (rpt strip_tac >> fs[EVEN_ADD, EVEN_MULT]) >>
      qabbrev_tac `k2 = (k - 1) DIV 2` >>
      `k = 2 * k2 + 1` suffices_by rw[] >>
      simp[Abbr`k2`, odd_lem]))

val lookup_fromList = store_thm(
  "lookup_fromList",
  ``lookup n (fromList l) = if n < LENGTH l then SOME (EL n l)
                            else NONE``,
  simp[fromList_def] >>
  `!i n t. lookup n (SND (FOLDL (\ (i,t) a. (i+1,insert i a t)) (i,t) l)) =
           if n < i then lookup n t
           else if n < LENGTH l + i then SOME (EL (n - i) l)
           else lookup n t`
    suffices_by (simp[] >> strip_tac >> simp[lookup_def]) >>
  Induct_on `l` >> simp[] >> pop_assum kall_tac >>
  rw[lookup_insert] >>
  full_simp_tac (srw_ss() ++ ARITH_ss) [] >>
  `0 < n - i` by simp[] >>
  Cases_on `n - i` >> fs[] >>
  qmatch_assum_rename_tac `n - i = SUC nn` >>
  `nn = n - (i + 1)` by decide_tac >> simp[]);

val bit_cases = prove(
  ``!n. (n = 0) \/ (?m. n = 2 * m + 1) \/ (?m. n = 2 * m + 2)``,
  Induct >> simp[] >> fs[]
  >- (disj2_tac >> qexists_tac `m` >> simp[])
  >- (disj1_tac >> qexists_tac `SUC m` >> simp[]))

val oddevenlemma = prove(
  ``2 * y + 1 <> 2 * x + 2``,
  disch_then (mp_tac o AP_TERM ``EVEN``) >>
  simp[EVEN_ADD, EVEN_MULT]);

val MULT2_DIV' = prove(
  ``(2 * m DIV 2 = m) /\ ((2 * m + 1) DIV 2 = m)``,
  simp[DIV_EQ_X]);

val domain_lookup = store_thm(
  "domain_lookup",
  ``!t k. k IN domain t <=> ?v. lookup k t = SOME v``,
  Induct >> simp[domain_def, lookup_def] >> rpt gen_tac >>
  qspec_then `k` STRUCT_CASES_TAC bit_cases >>
  simp[oddevenlemma, EVEN_ADD, EVEN_MULT,
       EQ_MULT_LCANCEL, MULT2_DIV']);

val lookup_inter_alt = store_thm("lookup_inter_alt",
  ``lookup x (inter t1 t2) =
      if x IN domain t2 then lookup x t1 else NONE``,
  fs [lookup_inter,domain_lookup]
  \\ Cases_on `lookup x t2` \\ fs [] \\ Cases_on `lookup x t1` \\ fs []);

val lookup_NONE_domain = store_thm(
  "lookup_NONE_domain",
  ``(lookup k t = NONE) <=> k NOTIN domain t``,
  simp[domain_lookup] >> Cases_on `lookup k t` >> simp[]);

Theorem domain_union[simp]:
  domain (union t1 t2) = domain t1 UNION domain t2
Proof
  simp[EXTENSION, domain_lookup, lookup_union] >>
  qx_gen_tac `k` >> Cases_on `lookup k t1` >> simp[]
QED

Theorem domain_inter[simp]:
  domain (inter t1 t2) = domain t1 INTER domain t2
Proof
  simp[EXTENSION, domain_lookup, lookup_inter] >>
  rw [] >> Cases_on `lookup x t1` >> fs[] >>
  BasicProvers.CASE_TAC
QED

Theorem domain_insert[simp]:
  domain (insert k v t) = k INSERT domain t
Proof
  simp[domain_lookup, EXTENSION, lookup_insert] >>
  metis_tac[]
QED

Theorem domain_difference[simp]:
  !t1 t2 . domain (difference t1 t2) = (domain t1) DIFF (domain t2)
Proof
  simp[EXTENSION, domain_lookup, lookup_difference] >>
  rw [] >> Cases_on `lookup x t1` >> fs[] >> Cases_on `lookup x t2` >> rw[]
QED

val domain_sing = save_thm(
  "domain_sing",
  domain_insert |> Q.INST [`t` |-> `LN`] |> SIMP_RULE bool_ss [domain_def]);

val domain_fromList = store_thm(
  "domain_fromList",
  ``domain (fromList l) = count (LENGTH l)``,
  simp[fromList_def] >>
  `!i t. domain (SND (FOLDL (\ (i,t) a. (i + 1, insert i a t)) (i,t) l)) =
         domain t UNION IMAGE ((+) i) (count (LENGTH l))`
    suffices_by (simp[] >> strip_tac >> simp[EXTENSION]) >>
  Induct_on `l` >> simp[EXTENSION, EQ_IMP_THM] >>
  rpt strip_tac >> simp[DECIDE ``(x = x + y) <=> (y = 0)``] >>
  qmatch_assum_rename_tac `nn < SUC (LENGTH l)` >>
  Cases_on `nn` >> fs[] >> metis_tac[ADD1]);

val size_domain = Q.store_thm("size_domain",
  `!t. size t = CARD (domain t)`,
  Induct_on `t`
  >- rw[size_def, domain_def]
  >- rw[size_def, domain_def]
  >> rw[CARD_UNION_EQN, CARD_INJ_IMAGE]
  >-
   (`IMAGE (\n. 2 * n + 2) (domain t) INTER
     IMAGE (\n. 2 * n + 1) (domain t') = {}`
      by (rw[GSYM DISJOINT_DEF, IN_DISJOINT]
          >> Cases_on `ODD x`
          >> fs[ODD_EXISTS, ADD1, oddevenlemma])
    >> simp[]) >>
  `(({0} INTER IMAGE (\n. 2 * n + 2) (domain t)) = {}) /\
   (({0} UNION (IMAGE (\n. 2 * n + 2) (domain t)))
        INTER (IMAGE (\n. 2 * n + 1) (domain t')) = {})`
  by (rw[GSYM DISJOINT_DEF, IN_DISJOINT]
      >> Cases_on `ODD x`
      >> fs[ODD_EXISTS, ADD1, oddevenlemma])
  >> simp[]);

val ODD_IMP_NOT_ODD = prove(
  ``!k. ODD k ==> ~(ODD (k-1))``,
  Cases >> fs [ODD]);

val lookup_delete = store_thm(
  "lookup_delete",
  ``!t k1 k2.
      lookup k1 (delete k2 t) = if k1 = k2 then NONE
                                else lookup k1 t``,
  Induct >> simp[delete_def, lookup_def]
  >> rw [lookup_def,lookup_mk_BN,lookup_mk_BS]
  >> sg `(k1 - 1) DIV 2 <> (k2 - 1) DIV 2`
  >> simp[DIV2_EQ_DIV2, EVEN_PRE]
  >> fs [] >> CCONTR_TAC >> fs [] >> srw_tac [] []
  >> fs [EVEN_ODD] >> imp_res_tac ODD_IMP_NOT_ODD);

val domain_delete = store_thm(
  "domain_delete[simp]",
  ``domain (delete k t) = domain t DELETE k``,
  simp[EXTENSION, domain_lookup, lookup_delete] >>
  metis_tac[]);

val foldi_def = Define`
  (foldi f i acc LN = acc) /\
  (foldi f i acc (LS a) = f i a acc) /\
  (foldi f i acc (BN t1 t2) =
     let inc = lrnext i
     in
       foldi f (i + inc) (foldi f (i + 2 * inc) acc t1) t2) /\
  (foldi f i acc (BS t1 a t2) =
     let inc = lrnext i
     in
       foldi f (i + inc) (f i a (foldi f (i + 2 * inc) acc t1)) t2)
`;

Definition spt_acc_def:
  (spt_acc i 0 = i) /\
  (spt_acc i (SUC k) =
     spt_acc (i + if EVEN (SUC k) then 2 * lrnext i else lrnext i) (k DIV 2))
Termination WF_REL_TAC`measure SND` \\ simp[DIV_LT_X]
End

val spt_acc_thm = Q.store_thm("spt_acc_thm",
  `spt_acc i k = if k = 0 then i else spt_acc (i + if EVEN k then 2 * lrnext i else lrnext i) ((k-1) DIV 2)`,
  rw[spt_acc_def] \\ Cases_on`k` \\ fs[spt_acc_def]);

val lemmas = prove(
    ``(!x. EVEN (2 * x + 2)) /\
      (!x. ODD (2 * x + 1))``,
    conj_tac >- (
      simp[EVEN_EXISTS] >> rw[] >>
      qexists_tac`SUC x` >> simp[] ) >>
    simp[ODD_EXISTS,ADD1] >>
    metis_tac[] )

val bit_induction = prove(
  ``!P. P 0 /\ (!n. P n ==> P (2 * n + 1)) /\
        (!n. P n ==> P (2 * n + 2)) ==>
        !n. P n``,
  gen_tac >> strip_tac >> completeInduct_on `n` >> simp[] >>
  qspec_then `n` strip_assume_tac bit_cases >> simp[]);

val lrnext212 = prove(
  ``(lrnext (2 * m + 1) = 2 * lrnext m) /\
    (lrnext (2 * m + 2) = 2 * lrnext m)``,
  conj_tac >| [
    `2 * m + 1 = BIT1 m` suffices_by simp[lrnext_thm] >>
    simp_tac bool_ss [BIT1, TWO, ONE, MULT_CLAUSES, ADD_CLAUSES],
    `2 * m + 2 = BIT2 m` suffices_by simp[lrnext_thm] >>
    simp_tac bool_ss [BIT2, TWO, ONE, MULT_CLAUSES, ADD_CLAUSES]
  ]);

val lrlemma1 = prove(
  ``lrnext (i + lrnext i) = 2 * lrnext i``,
  qid_spec_tac `i` >> ho_match_mp_tac bit_induction >>
  simp[lrnext212, lrnext_thm] >> conj_tac
  >- (gen_tac >>
      `2 * i + (2 * lrnext i + 1) = 2 * (i + lrnext i) + 1`
         by decide_tac >> simp[lrnext212]) >>
  qx_gen_tac `i` >>
  `2 * i + (2 * lrnext i + 2) = 2 * (i + lrnext i) + 2`
    by decide_tac >>
  simp[lrnext212]);

val lrlemma2 = prove(
  ``lrnext (i + 2 * lrnext i) = 2 * lrnext i``,
  qid_spec_tac `i` >> ho_match_mp_tac bit_induction >>
  simp[lrnext212, lrnext_thm] >> conj_tac
  >- (qx_gen_tac `i` >>
      `2 * i + (4 * lrnext i + 1) = 2 * (i + 2 * lrnext i) + 1`
        by decide_tac >> simp[lrnext212]) >>
  gen_tac >>
  `2 * i + (4 * lrnext i + 2) = 2 * (i + 2 * lrnext i) + 2`
     by decide_tac >> simp[lrnext212])

val spt_acc_eqn = Q.store_thm("spt_acc_eqn",
  `!k i. spt_acc i k = lrnext i * k + i`,
  ho_match_mp_tac bit_induction
  \\ rw[]
  >- rw[spt_acc_def]
  >- (
    rw[Once spt_acc_thm]
    >- fs[EVEN_ODD,lemmas]
    \\ simp[MULT2_DIV']
    \\ simp[lrlemma1] )
  >- (
    ONCE_REWRITE_TAC[spt_acc_thm]
    \\ simp[]
    \\ reverse(rw[])
    >- fs[EVEN_ODD,lemmas]
    \\ simp[MULT2_DIV']
    \\ simp[lrlemma2]));

val spt_acc_0 = Q.store_thm("spt_acc_0",
  `!k. spt_acc 0 k = k`, rw[spt_acc_eqn,lrnext_thm]);

val set_foldi_keys = store_thm(
  "set_foldi_keys",
  ``!t a i. foldi (\k v a. k INSERT a) i a t =
            a UNION IMAGE (\n. i + lrnext i * n) (domain t)``,
  Induct_on `t` >> simp[foldi_def, GSYM IMAGE_COMPOSE,
                        combinTheory.o_ABS_R]
  >- simp[Once INSERT_SING_UNION, UNION_COMM]
  >- (simp[EXTENSION] >> rpt gen_tac >>
      Cases_on `x IN a` >> simp[lrlemma1, lrlemma2, LEFT_ADD_DISTRIB]) >>
  simp[EXTENSION] >> rpt gen_tac >>
  Cases_on `x IN a'` >> simp[lrlemma1, lrlemma2, LEFT_ADD_DISTRIB])

val domain_foldi = save_thm(
  "domain_foldi",
  set_foldi_keys |> SPEC_ALL |> Q.INST [`i` |-> `0`, `a` |-> `{}`]
                 |> SIMP_RULE (srw_ss()) [lrnext_thm]
                 |> SYM);
val _ = computeLib.add_persistent_funs ["domain_foldi"]

Definition mapi0_def[simp]:
  (mapi0 f i LN = LN) /\
  (mapi0 f i (LS a) = LS (f i a)) /\
  (mapi0 f i (BN t1 t2) =
   let inc = lrnext i in
     mk_BN (mapi0 f (i + 2 * inc) t1) (mapi0 f (i + inc) t2)) /\
  (mapi0 f i (BS t1 a t2) =
   let inc = lrnext i in
     mk_BS (mapi0 f (i + 2 * inc) t1) (f i a) (mapi0 f (i + inc) t2))
End

Definition mapi_def: mapi f pt = mapi0 f 0 pt
End

val lookup_mapi0 = Q.store_thm("lookup_mapi0",
  `!pt i k.
   lookup k (mapi0 f i pt) =
   case lookup k pt of NONE => NONE
   | SOME v => SOME (f (spt_acc i k) v)`,
  Induct \\ rw[mapi0_def,lookup_def,lookup_mk_BN,lookup_mk_BS] \\ fs[]
  \\ TRY (simp[spt_acc_eqn] \\ NO_TAC)
  \\ CASE_TAC \\ simp[Once spt_acc_thm,SimpRHS]);

val lookup_mapi = Q.store_thm("lookup_mapi",
  `lookup k (mapi f pt) = OPTION_MAP (f k) (lookup k pt)`,
  rw[mapi_def,lookup_mapi0,spt_acc_0]
  \\ CASE_TAC \\ fs[]);

val toAList_def = Define `
  toAList = foldi (\k v a. (k,v)::a) 0 []`

val set_toAList_lemma = prove(
  ``!t a i. set (foldi (\k v a. (k,v) :: a) i a t) =
            set a UNION IMAGE (\n. (i + lrnext i * n,
                    THE (lookup n t))) (domain t)``,
  Induct_on `t`
  \\ fs [foldi_def,GSYM IMAGE_COMPOSE,lookup_def]
  THEN1 fs [Once INSERT_SING_UNION, UNION_COMM]
  THEN1 (simp[EXTENSION] \\ rpt gen_tac \\
         Cases_on `MEM x a` \\ simp[lrlemma1, lrlemma2, LEFT_ADD_DISTRIB]
         \\ fs [MULT2_DIV',EVEN_ADD,EVEN_DOUBLE])
  \\ simp[EXTENSION] \\ rpt gen_tac
  \\ Cases_on `MEM x a'` \\ simp[lrlemma1, lrlemma2, LEFT_ADD_DISTRIB]
  \\ fs [MULT2_DIV',EVEN_ADD,EVEN_DOUBLE])
  |> Q.SPECL [`t`,`[]`,`0`] |> GEN_ALL
  |> SIMP_RULE (srw_ss()) [GSYM toAList_def,lrnext_thm,MEM,LIST_TO_SET,
       UNION_EMPTY,EXTENSION,
       pairTheory.FORALL_PROD]

val MEM_toAList = store_thm("MEM_toAList",
  ``!t k v. MEM (k,v) (toAList t) <=> (lookup k t = SOME v)``,
  fs [set_toAList_lemma,domain_lookup]  \\ REPEAT STRIP_TAC
  \\ Cases_on `lookup k t` \\ fs []
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ fs []);

val ALOOKUP_toAList = store_thm("ALOOKUP_toAList",
  ``!t x. ALOOKUP (toAList t) x = lookup x t``,
  strip_tac>>strip_tac>>Cases_on `lookup x t` >-
    simp[ALOOKUP_FAILS,MEM_toAList] >>
  Cases_on`ALOOKUP (toAList t) x`>-
    fs[ALOOKUP_FAILS,MEM_toAList] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_toAList])

val insert_union = store_thm("insert_union",
  ``!k v s. insert k v s = union (insert k v LN) s``,
  completeInduct_on`k` >> simp[Once insert_def] >> rw[] >>
  simp[Once union_def] >>
  Cases_on`s`>>simp[Once insert_def] >>
  simp[Once union_def] >>
  first_x_assum match_mp_tac >>
  simp[arithmeticTheory.DIV_LT_X])

val domain_empty = store_thm("domain_empty",
  ``!t. wf t ==> ((t = LN) <=> (domain t = EMPTY))``,
  simp[] >> Induct >> simp[wf_def] >> metis_tac[])

val toAList_append = prove(
  ``!t n ls.
      foldi (\k v a. (k,v)::a) n ls t =
      foldi (\k v a. (k,v)::a) n [] t ++ ls``,
  Induct
  >- simp[foldi_def]
  >- simp[foldi_def]
  >- (
    simp_tac std_ss [foldi_def,LET_THM] >> rpt gen_tac >>
    first_assum(fn th =>
      CONV_TAC(LAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV th))))) >>
    first_assum(fn th =>
      CONV_TAC(LAND_CONV(REWR_CONV th))) >>
    first_assum(fn th =>
      CONV_TAC(RAND_CONV(LAND_CONV(REWR_CONV th)))) >>
    metis_tac[APPEND_ASSOC] ) >>
  simp_tac std_ss [foldi_def,LET_THM] >> rpt gen_tac >>
  first_assum(fn th =>
    CONV_TAC(LAND_CONV(RATOR_CONV(RAND_CONV(RAND_CONV(REWR_CONV th)))))) >>
  first_assum(fn th =>
    CONV_TAC(LAND_CONV(REWR_CONV th))) >>
  first_assum(fn th =>
    CONV_TAC(RAND_CONV(LAND_CONV(REWR_CONV th)))) >>
  metis_tac[APPEND_ASSOC,APPEND] )

val toAList_inc = prove(
  ``!t n.
      foldi (\k v a. (k,v)::a) n [] t =
      MAP (\(k,v). (n + lrnext n * k,v)) (foldi (\k v a. (k,v)::a) 0 [] t)``,
  Induct
  >- simp[foldi_def]
  >- simp[foldi_def]
  >- (
    simp_tac std_ss [foldi_def,LET_THM] >> rpt gen_tac >>
    CONV_TAC(LAND_CONV(REWR_CONV toAList_append)) >>
    CONV_TAC(RAND_CONV(RAND_CONV(REWR_CONV toAList_append))) >>
    first_assum(fn th =>
      CONV_TAC(LAND_CONV(LAND_CONV(REWR_CONV th)))) >>
    first_assum(fn th =>
      CONV_TAC(LAND_CONV(RAND_CONV(REWR_CONV th)))) >>
    first_assum(fn th =>
      CONV_TAC(RAND_CONV(RAND_CONV(LAND_CONV(REWR_CONV th))))) >>
    first_assum(fn th =>
      CONV_TAC(RAND_CONV(RAND_CONV(RAND_CONV(REWR_CONV th))))) >>
    rpt(pop_assum kall_tac) >>
    simp[MAP_MAP_o,combinTheory.o_DEF,APPEND_11_LENGTH] >>
    simp[MAP_EQ_f] >>
    simp[lrnext_thm,pairTheory.UNCURRY,pairTheory.FORALL_PROD] >>
    simp[lrlemma1,lrlemma2] )
  >- (
    simp_tac std_ss [foldi_def,LET_THM] >> rpt gen_tac >>
    CONV_TAC(LAND_CONV(REWR_CONV toAList_append)) >>
    CONV_TAC(RAND_CONV(RAND_CONV(REWR_CONV toAList_append))) >>
    first_assum(fn th =>
      CONV_TAC(LAND_CONV(LAND_CONV(REWR_CONV th)))) >>
    first_assum(fn th =>
      CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV(REWR_CONV th))))) >>
    first_assum(fn th =>
      CONV_TAC(RAND_CONV(RAND_CONV(LAND_CONV(REWR_CONV th))))) >>
    first_assum(fn th =>
      CONV_TAC(RAND_CONV(RAND_CONV(RAND_CONV(RAND_CONV(REWR_CONV th)))))) >>
    rpt(pop_assum kall_tac) >>
    simp[MAP_MAP_o,combinTheory.o_DEF,APPEND_11_LENGTH] >>
    simp[MAP_EQ_f] >>
    simp[lrnext_thm,pairTheory.UNCURRY,pairTheory.FORALL_PROD] >>
    simp[lrlemma1,lrlemma2] ))

val ALL_DISTINCT_MAP_FST_toAList = store_thm("ALL_DISTINCT_MAP_FST_toAList",
  ``!t. ALL_DISTINCT (MAP FST (toAList t))``,
  simp[toAList_def] >>
  Induct >> simp[foldi_def] >- (
    CONV_TAC(RAND_CONV(RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV toAList_inc))))) >>
    CONV_TAC(RAND_CONV(RAND_CONV(REWR_CONV toAList_append))) >>
    CONV_TAC(RAND_CONV(RAND_CONV(LAND_CONV(REWR_CONV toAList_inc)))) >>
    simp[MAP_MAP_o,combinTheory.o_DEF,pairTheory.UNCURRY,lrnext_thm] >>
    simp[ALL_DISTINCT_APPEND] >>
    rpt conj_tac >- (
      qmatch_abbrev_tac`ALL_DISTINCT (MAP f ls)` >>
      `MAP f ls = MAP (\x. 2 * x + 1) (MAP FST ls)` by (
        simp[MAP_MAP_o,combinTheory.o_DEF,Abbr`f`] ) >>
      pop_assum SUBST1_TAC >> qunabbrev_tac`f` >>
      match_mp_tac ALL_DISTINCT_MAP_INJ >>
      simp[] )
    >- (
      qmatch_abbrev_tac`ALL_DISTINCT (MAP f ls)` >>
      `MAP f ls = MAP (\x. 2 * x + 2) (MAP FST ls)` by (
        simp[MAP_MAP_o,combinTheory.o_DEF,Abbr`f`] ) >>
      pop_assum SUBST1_TAC >> qunabbrev_tac`f` >>
      match_mp_tac ALL_DISTINCT_MAP_INJ >>
      simp[] ) >>
    simp[MEM_MAP,PULL_EXISTS,pairTheory.EXISTS_PROD] >>
    metis_tac[ODD_EVEN,lemmas] ) >>
  gen_tac >>
  CONV_TAC(RAND_CONV(RAND_CONV(RATOR_CONV(RAND_CONV(RAND_CONV(REWR_CONV toAList_inc)))))) >>
  CONV_TAC(RAND_CONV(RAND_CONV(REWR_CONV toAList_append))) >>
  CONV_TAC(RAND_CONV(RAND_CONV(LAND_CONV(REWR_CONV toAList_inc)))) >>
  simp[MAP_MAP_o,combinTheory.o_DEF,pairTheory.UNCURRY,lrnext_thm] >>
  simp[ALL_DISTINCT_APPEND] >>
  rpt conj_tac >- (
    qmatch_abbrev_tac`ALL_DISTINCT (MAP f ls)` >>
    `MAP f ls = MAP (\x. 2 * x + 1) (MAP FST ls)` by (
      simp[MAP_MAP_o,combinTheory.o_DEF,Abbr`f`] ) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac`f` >>
    match_mp_tac ALL_DISTINCT_MAP_INJ >>
    simp[] )
  >- ( simp[MEM_MAP] )
  >- (
    qmatch_abbrev_tac`ALL_DISTINCT (MAP f ls)` >>
    `MAP f ls = MAP (\x. 2 * x + 2) (MAP FST ls)` by (
      simp[MAP_MAP_o,combinTheory.o_DEF,Abbr`f`] ) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac`f` >>
    match_mp_tac ALL_DISTINCT_MAP_INJ >>
    simp[] ) >>
  simp[MEM_MAP,PULL_EXISTS,pairTheory.EXISTS_PROD] >>
  metis_tac[ODD_EVEN,lemmas] )

Theorem LENGTH_toAList[simp]:
  LENGTH (toAList t) = size t
Proof
  `LENGTH (toAList t) = LENGTH (MAP FST (toAList t))` by simp[]>>
  pop_assum SUBST_ALL_TAC>>
  DEP_REWRITE_TAC[GSYM ALL_DISTINCT_CARD_LIST_TO_SET]>>
  simp[ALL_DISTINCT_MAP_FST_toAList,size_domain]>>
  AP_TERM_TAC>>
  rw[pred_setTheory.EXTENSION]>>
  simp[MEM_MAP,pairTheory.EXISTS_PROD,MEM_toAList,domain_lookup]
QED

val _ = remove_ovl_mapping "lrnext" {Name = "lrnext", Thy = "sptree"}

val foldi_FOLDR_toAList_lemma = prove(
  ``!t n a ls. foldi f n (FOLDR (UNCURRY f) a ls) t =
               FOLDR (UNCURRY f) a (foldi (\k v a. (k,v)::a) n ls t)``,
  Induct >> simp[foldi_def] >>
  rw[] >> pop_assum(assume_tac o GSYM) >> simp[])

val foldi_FOLDR_toAList = store_thm("foldi_FOLDR_toAList",
  ``!f a t. foldi f 0 a t = FOLDR (UNCURRY f) a (toAList t)``,
  simp[toAList_def,GSYM foldi_FOLDR_toAList_lemma])

val toListA_def = Define`
  (toListA acc LN = acc) /\
  (toListA acc (LS a) = a::acc) /\
  (toListA acc (BN t1 t2) = toListA (toListA acc t2) t1) /\
  (toListA acc (BS t1 a t2) = toListA (a :: toListA acc t2) t1)
`;

local open listTheory rich_listTheory in
val toListA_append = store_thm("toListA_append",
  ``!t acc. toListA acc t = toListA [] t ++ acc``,
  Induct >> REWRITE_TAC[toListA_def]
  >> metis_tac[APPEND_ASSOC,CONS_APPEND,APPEND])
end

val isEmpty_toListA = store_thm("isEmpty_toListA",
  ``!t acc. wf t ==> ((t = LN) <=> (toListA acc t = acc))``,
  Induct >> simp[toListA_def,wf_def] >>
  rw[] >> fs[] >> Cases_on ‘t = LN’ >> fs[] >>
  fs[Once toListA_append] >>
  simp[Once toListA_append,SimpR``$++``])

val toList_def = Define`toList m = toListA [] m`

val isEmpty_toList = store_thm("isEmpty_toList",
  ``!t. wf t ==> ((t = LN) <=> (toList t = []))``,
  rw[toList_def,isEmpty_toListA]);

val lem2 =
  SIMP_RULE (srw_ss()) [] (Q.SPECL[`2`,`1`]DIV_MULT);

fun tac () = (
  (disj2_tac >> qexists_tac`0` >> simp[] >> NO_TAC) ORELSE
  (disj2_tac >>
   qexists_tac`2*k+1` >> simp[] >>
   REWRITE_TAC[Once MULT_COMM] >> simp[MULT_DIV] >>
   rw[] >> `F` suffices_by rw[] >> pop_assum mp_tac >>
   simp[lemmas,GSYM ODD_EVEN] >> NO_TAC) ORELSE
  (disj2_tac >>
   qexists_tac`2*k+2` >> simp[] >>
   REWRITE_TAC[Once MULT_COMM] >> simp[lem2] >>
   rw[] >> `F` suffices_by rw[] >> pop_assum mp_tac >>
   simp[lemmas] >> NO_TAC) ORELSE
  (metis_tac[]));

val MEM_toListA = prove(
  ``!t acc x. MEM x (toListA acc t) <=> (MEM x acc \/ ?k. lookup k t = SOME x)``,
  Induct >> simp[toListA_def,lookup_def] >- metis_tac[] >>
  rw[EQ_IMP_THM] >> rw[] >> pop_assum mp_tac >> rw[]
  >- (tac())
  >- (tac())
  >- (tac())
  >- (tac())
  >- (tac())
  >- (tac())
  >- (tac())
  >- (tac())
  >- (tac()));

val MEM_toList = store_thm("MEM_toList",
  ``!x t. MEM x (toList t) <=> ?k. lookup k t = SOME x``,
  rw[toList_def,MEM_toListA]);

val div2_even_lemma = prove(
  ``!x. ?n. (x = (n - 1) DIV 2) /\ EVEN n /\ 0 < n``,
  Induct >- ( qexists_tac`2` >> simp[] ) >> fs[] >>
  qexists_tac`n+2` >>
  simp[ADD1,EVEN_ADD] >>
  Cases_on`n`>>fs[EVEN,EVEN_ODD,ODD_EXISTS,ADD1] >>
  simp[] >> rw[] >>
  qspec_then`2`mp_tac ADD_DIV_ADD_DIV >> simp[] >>
  disch_then(qspecl_then[`m`,`3`]mp_tac) >>
  simp[] >> disch_then kall_tac >>
  qspec_then`2`mp_tac ADD_DIV_ADD_DIV >> simp[] >>
  disch_then(qspecl_then[`m`,`1`]mp_tac) >>
  simp[]);

val div2_odd_lemma = prove(
  ``!x. ?n. (x = (n - 1) DIV 2) /\ ODD n /\ 0 < n``,
  Induct >- ( qexists_tac`1` >> simp[] ) >> fs[] >>
  qexists_tac`n+2` >>
  simp[ADD1,ODD_ADD] >>
  fs[ODD_EXISTS,ADD1] >>
  simp[] >> rw[] >>
  qspec_then`2`mp_tac ADD_DIV_ADD_DIV >> simp[] >>
  disch_then(qspecl_then[`m`,`2`]mp_tac) >>
  simp[] >> disch_then kall_tac >>
  qspec_then`2`mp_tac ADD_DIV_ADD_DIV >> simp[] >>
  disch_then(qspecl_then[`m`,`0`]mp_tac) >>
  simp[]);

val spt_eq_thm = store_thm("spt_eq_thm",
  ``!t1 t2. wf t1 /\ wf t2 ==>
            ((t1 = t2) <=> !n. lookup n t1 = lookup n t2)``,
  Induct >> simp[wf_def,lookup_def]
  >- (
    rw[EQ_IMP_THM] >> rw[lookup_def] >>
    `domain t2 = {}` by (
      simp[EXTENSION] >>
      metis_tac[lookup_NONE_domain] ) >>
    Cases_on`t2`>>fs[domain_def,wf_def] >>
    metis_tac[domain_empty] )
  >- (
    rw[EQ_IMP_THM] >> rw[lookup_def] >>
    Cases_on`t2`>>fs[lookup_def]
    >- (first_x_assum(qspec_then`0`mp_tac)>>simp[])
    >- (first_x_assum(qspec_then`0`mp_tac)>>simp[]) >>
    fs[wf_def] >> Cases_on ‘s = LN’ >>
    rfs[domain_empty] >>
    fs[GSYM MEMBER_NOT_EMPTY] >>
    fs[domain_lookup] >|
      [ qspec_then`x`strip_assume_tac div2_odd_lemma,
        qspec_then`x`strip_assume_tac div2_even_lemma
      ] >>
    first_x_assum(qspec_then`n`mp_tac) >>
    fs[ODD_EVEN] >> simp[] )
  >- (
    rw[EQ_IMP_THM] >> rw[lookup_def] >> Cases_on ‘t1 = LN’ >>
    rfs[domain_empty] >>
    fs[GSYM MEMBER_NOT_EMPTY] >>
    fs[domain_lookup] >>
    Cases_on`t2`>>fs[] >>
    TRY (
      first_x_assum(qspec_then`0`mp_tac) >>
      simp[lookup_def] >> NO_TAC) >>
    TRY (
      qspec_then`x`strip_assume_tac div2_even_lemma >>
      first_x_assum(qspec_then`n`mp_tac) >> fs[] >>
      simp[lookup_def] >> NO_TAC) >>
    TRY (
      qspec_then`x`strip_assume_tac div2_odd_lemma >>
      first_x_assum(qspec_then`n`mp_tac) >> fs[ODD_EVEN] >>
      simp[lookup_def] >> NO_TAC) >>
    qmatch_assum_rename_tac`wf (BN s1 s2)` >>
    `wf s1 /\ wf s2` by fs[wf_def] >>
    first_x_assum(qspec_then`s2`mp_tac) >>
    first_x_assum(qspec_then`s1`mp_tac) >>
    simp[] >> ntac 2 strip_tac >>
    fs[lookup_def] >> rw[] >>
    metis_tac[prim_recTheory.LESS_REFL,div2_even_lemma,div2_odd_lemma
             ,EVEN_ODD] )
  >- (
    rw[EQ_IMP_THM] >> rw[lookup_def] >> Cases_on ‘t1 = LN’ >>
    rfs[domain_empty] >>
    fs[GSYM MEMBER_NOT_EMPTY] >>
    fs[domain_lookup] >>
    Cases_on`t2`>>fs[] >>
    TRY (
      first_x_assum(qspec_then`0`mp_tac) >>
      simp[lookup_def] >> NO_TAC) >>
    TRY (
      qspec_then`x`strip_assume_tac div2_even_lemma >>
      first_x_assum(qspec_then`n`mp_tac) >> fs[] >>
      simp[lookup_def] >> NO_TAC) >>
    TRY (
      qspec_then`x`strip_assume_tac div2_odd_lemma >>
      first_x_assum(qspec_then`n`mp_tac) >> fs[ODD_EVEN] >>
      simp[lookup_def] >> NO_TAC) >>
    qmatch_assum_rename_tac`wf (BS s1 z s2)` >>
    `wf s1 /\ wf s2` by fs[wf_def] >>
    first_x_assum(qspec_then`s2`mp_tac) >>
    first_x_assum(qspec_then`s1`mp_tac) >>
    simp[] >> ntac 2 strip_tac >>
    fs[lookup_def] >> rw[] >>
    metis_tac[prim_recTheory.LESS_REFL,div2_even_lemma,div2_odd_lemma
             ,EVEN_ODD,optionTheory.SOME_11] ))

val mk_wf_def = Define `
  (mk_wf LN = LN) /\
  (mk_wf (LS x) = LS x) /\
  (mk_wf (BN t1 t2) = mk_BN (mk_wf t1) (mk_wf t2)) /\
  (mk_wf (BS t1 x t2) = mk_BS (mk_wf t1) x (mk_wf t2))`;

Theorem wf_mk_wf[simp]: !t. wf (mk_wf t)
Proof Induct \\ fs [wf_def,mk_wf_def,wf_mk_BS,wf_mk_BN]
QED

Theorem wf_mk_id[simp]: !t. wf t ==> (mk_wf t = t)
Proof
  Induct \\ srw_tac [] [wf_def,mk_wf_def,mk_BS_thm,mk_BN_thm]
QED

Theorem lookup_mk_wf[simp]:
  !x t. lookup x (mk_wf t) = lookup x t
Proof
  Induct_on `t` \\ fs [mk_wf_def,lookup_mk_BS,lookup_mk_BN]
  \\ srw_tac [] [lookup_def]
QED

Theorem domain_mk_wf[simp]: !t. domain (mk_wf t) = domain t
Proof fs [EXTENSION,domain_lookup]
QED

Theorem mk_wf_eq[simp]:
  !t1 t2. (mk_wf t1 = mk_wf t2) <=> !x. lookup x t1 = lookup x t2
Proof
  metis_tac [spt_eq_thm,wf_mk_wf,lookup_mk_wf]
QED

val inter_eq = store_thm("inter_eq[simp]",
  ``!t1 t2 t3 t4.
       (inter t1 t2 = inter t3 t4) <=>
       !x. lookup x (inter t1 t2) = lookup x (inter t3 t4)``,
  metis_tac [spt_eq_thm,wf_inter]);

Theorem union_mk_wf[simp]:
  !t1 t2. union (mk_wf t1) (mk_wf t2) = mk_wf (union t1 t2)
Proof
  REPEAT STRIP_TAC
  \\ `union (mk_wf t1) (mk_wf t2) = mk_wf (union (mk_wf t1) (mk_wf t2))` by
        metis_tac [wf_union,wf_mk_wf,wf_mk_id]
  \\ POP_ASSUM (fn th => once_rewrite_tac [th])
  \\ ASM_SIMP_TAC std_ss [mk_wf_eq] \\ fs [lookup_union]
QED

Theorem inter_mk_wf[simp]:
  !t1 t2. inter (mk_wf t1) (mk_wf t2) = mk_wf (inter t1 t2)
Proof
  REPEAT STRIP_TAC
  \\ `inter (mk_wf t1) (mk_wf t2) = mk_wf (inter (mk_wf t1) (mk_wf t2))` by
        metis_tac [wf_inter,wf_mk_wf,wf_mk_id]
  \\ POP_ASSUM (fn th => once_rewrite_tac [th])
  \\ ASM_SIMP_TAC std_ss [mk_wf_eq] \\ fs [lookup_inter]
QED

Theorem insert_mk_wf[simp]:
  !x v t. insert x v (mk_wf t) = mk_wf (insert x v t)
Proof
  REPEAT STRIP_TAC
  \\ `insert x v (mk_wf t) = mk_wf (insert x v (mk_wf t))` by
        metis_tac [wf_insert,wf_mk_wf,wf_mk_id]
  \\ POP_ASSUM (fn th => once_rewrite_tac [th])
  \\ ASM_SIMP_TAC std_ss [mk_wf_eq] \\ fs [lookup_insert]
QED

Theorem delete_mk_wf[simp]:
  !x t. delete x (mk_wf t) = mk_wf (delete x t)
Proof
  REPEAT STRIP_TAC
  \\ `delete x (mk_wf t) = mk_wf (delete x (mk_wf t))` by
        metis_tac [wf_delete,wf_mk_wf,wf_mk_id]
  \\ POP_ASSUM (fn th => once_rewrite_tac [th])
  \\ ASM_SIMP_TAC std_ss [mk_wf_eq] \\ fs [lookup_delete]
QED

Theorem union_LN[simp]:
  !t. (union t LN = t) /\ (union LN t = t)
Proof Cases \\ fs [union_def]
QED

Theorem inter_LN[simp]: !t. (inter t LN = LN) /\ (inter LN t = LN)
Proof Cases \\ fs [inter_def]
QED

val union_assoc = store_thm("union_assoc",
  ``!t1 t2 t3. union t1 (union t2 t3) = union (union t1 t2) t3``,
  Induct \\ Cases_on `t2` \\ Cases_on `t3` \\ fs [union_def]);

val inter_assoc = store_thm("inter_assoc",
  ``!t1 t2 t3. inter t1 (inter t2 t3) = inter (inter t1 t2) t3``,
  fs [lookup_inter] \\ REPEAT STRIP_TAC
  \\ Cases_on `lookup x t1` \\ fs []
  \\ Cases_on `lookup x t2` \\ fs []
  \\ Cases_on `lookup x t3` \\ fs []);

val numeral_div0 = prove(
  ``(BIT1 n DIV 2 = n) /\
    (BIT2 n DIV 2 = SUC n) /\
    (SUC (BIT1 n) DIV 2 = SUC n) /\
    (SUC (BIT2 n) DIV 2 = SUC n)``,
  REWRITE_TAC[GSYM DIV2_def, numeralTheory.numeral_suc,
              REWRITE_RULE [NUMERAL_DEF]
                           numeralTheory.numeral_div2])
val BIT0 = prove(
  ``BIT1 n <> 0  /\ BIT2 n <> 0``,
  REWRITE_TAC[BIT1, BIT2,
              ADD_CLAUSES, numTheory.NOT_SUC]);

val PRE_BIT1 = prove(
  ``BIT1 n - 1 = 2 * n``,
  REWRITE_TAC [BIT1, NUMERAL_DEF,
               ALT_ZERO, ADD_CLAUSES,
               BIT2, SUB_MONO_EQ,
               MULT_CLAUSES, SUB_0]);

val PRE_BIT2 = prove(
  ``BIT2 n - 1 = 2 * n + 1``,
  REWRITE_TAC [BIT1, NUMERAL_DEF,
               ALT_ZERO, ADD_CLAUSES,
               BIT2, SUB_MONO_EQ,
               MULT_CLAUSES, SUB_0]);

val BITDIV = prove(
  ``((BIT1 n - 1) DIV 2 = n) /\ ((BIT2 n - 1) DIV 2 = n)``,
  simp[PRE_BIT1, PRE_BIT2] >> simp[DIV_EQ_X]);

fun computerule th q =
    th
      |> CONJUNCTS
      |> map SPEC_ALL
      |> map (Q.INST [`k` |-> q])
      |> map (CONV_RULE
                (RAND_CONV (SIMP_CONV bool_ss
                                      ([numeral_div0, BIT0, PRE_BIT1,
                                       numTheory.NOT_SUC, BITDIV,
                                       EVAL ``SUC 0 DIV 2``,
                                       numeralTheory.numeral_evenodd,
                                       EVEN]) THENC
                            SIMP_CONV bool_ss [ALT_ZERO])))

val lookup_compute = save_thm(
  "lookup_compute",
    LIST_CONJ (prove (``lookup (NUMERAL n) t = lookup n t``,
                      REWRITE_TAC [NUMERAL_DEF]) ::
               computerule lookup_def `0` @
               computerule lookup_def `ZERO` @
               computerule lookup_def `BIT1 n` @
               computerule lookup_def `BIT2 n`))
val _ = computeLib.add_persistent_funs ["lookup_compute"]

val insert_compute = save_thm(
  "insert_compute",
    LIST_CONJ (prove (``insert (NUMERAL n) a t = insert n a t``,
                      REWRITE_TAC [NUMERAL_DEF]) ::
               computerule insert_def `0` @
               computerule insert_def `ZERO` @
               computerule insert_def `BIT1 n` @
               computerule insert_def `BIT2 n`))
val _ = computeLib.add_persistent_funs ["insert_compute"]

val delete_compute = save_thm(
  "delete_compute",
    LIST_CONJ (
      prove(``delete (NUMERAL n) t = delete n t``,
            REWRITE_TAC [NUMERAL_DEF]) ::
      computerule delete_def `0` @
      computerule delete_def `ZERO` @
      computerule delete_def `BIT1 n` @
      computerule delete_def `BIT2 n`))
val _ = computeLib.add_persistent_funs ["delete_compute"]

Definition fromAList_def[simp]:
  (fromAList [] = LN) /\
  (fromAList ((x,y)::xs) = insert x y (fromAList xs))
End

val lookup_fromAList = store_thm("lookup_fromAList",
  ``!ls x.lookup x (fromAList ls) = ALOOKUP ls x``,
  ho_match_mp_tac fromAList_ind >>
  rw[fromAList_def,lookup_def] >>
  fs[lookup_insert]>> simp[EQ_SYM_EQ])

val domain_fromAList = store_thm("domain_fromAList",
  ``!ls. domain (fromAList ls) = set (MAP FST ls)``,
  simp[EXTENSION,domain_lookup,lookup_fromAList,
       MEM_MAP,pairTheory.EXISTS_PROD]>>
  metis_tac[ALOOKUP_MEM,ALOOKUP_FAILS,
            optionTheory.option_CASES,
            optionTheory.NOT_SOME_NONE])

val lookup_fromAList_toAList = store_thm("lookup_fromAList_toAList",
  ``!t x. lookup x (fromAList (toAList t)) = lookup x t``,
  simp[lookup_fromAList,ALOOKUP_toAList])

val wf_fromAList = store_thm("wf_fromAList",
  ``!ls. wf (fromAList ls)``,
  Induct >>
    rw[fromAList_def,wf_def]>>
  Cases_on`h`>>
  rw[fromAList_def]>>
    simp[wf_insert])

val fromAList_toAList = store_thm("fromAList_toAList",
  ``!t. wf t ==> (fromAList (toAList t) = t)``,
  metis_tac[wf_fromAList,lookup_fromAList_toAList,spt_eq_thm])

Theorem union_insert_LN:
  !x y t2. union (insert x y LN) t2 = insert x y t2
Proof
  recInduct insert_ind
   \\ rw[]
   \\ rw[Once insert_def]
   \\ rw[Once insert_def,SimpRHS]
   \\ rw[union_def]
QED

Theorem fromAList_append:
  !l1 l2. fromAList (l1 ++ l2) = union (fromAList l1) (fromAList l2)
Proof
  recInduct fromAList_ind
  \\ rw[fromAList_def]
  \\ rw[Once insert_union]
  \\ rw[union_assoc]
  \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ rw[union_insert_LN]
QED

Definition map_def[simp]:
  (map f LN = LN) /\
  (map f (LS a) = (LS (f a))) /\
  (map f (BN t1 t2) = BN (map f t1) (map f t2)) /\
  (map f (BS t1 a t2) = BS (map f t1) (f a) (map f t2))
End

val toList_map = store_thm("toList_map",
  ``!s. toList (map f s) = MAP f (toList s)``,
  Induct >>
  fs[toList_def,map_def,toListA_def] >>
  simp[Once toListA_append] >>
  simp[Once toListA_append,SimpRHS])

Theorem domain_map[simp]: !s. domain (map f s) = domain s
Proof Induct >> simp[map_def]
QED

val lookup_map = store_thm("lookup_map",
  ``!s x. lookup x (map f s) = OPTION_MAP f (lookup x s)``,
  Induct >> simp[map_def,lookup_def] >> rw[])

Theorem map_LN[simp]: !t. (map f t = LN) <=> (t = LN)
Proof Cases \\ EVAL_TAC
QED

Theorem wf_map[simp]: !t f. wf (map f t) = wf t
Proof
  Induct \\ fs [wf_def,map_def]
QED

val map_map_o = store_thm("map_map_o",
  ``!t f g. map f (map g t) = map (f o g) t``,
  Induct >> fs[map_def])

val map_insert = store_thm("map_insert",
  ``!f x y z.
  map f (insert x y z) = insert x (f y) (map f z)``,
  completeInduct_on`x`>>
  Induct_on`z`>>
  rw[]>>
  simp[Once map_def,Once insert_def]>>
  simp[Once insert_def,SimpRHS]>>
  BasicProvers.EVERY_CASE_TAC>>fs[map_def]>>
  `(x-1) DIV 2 < x` by
    (`0 < (2:num)` by fs[] >>
    imp_res_tac DIV_LT_X>>
    first_x_assum match_mp_tac>>
    DECIDE_TAC)>>
  fs[map_def]);

Theorem map_fromAList:
  map f (fromAList ls) = fromAList (MAP (\ (k,v). (k, f v)) ls)
Proof
  Induct_on`ls` >> simp[fromAList_def] >>
   Cases >> simp[fromAList_def] >>
   simp[wf_fromAList,map_insert]
QED

val insert_insert = store_thm("insert_insert",
  ``!x1 x2 v1 v2 t.
      insert x1 v1 (insert x2 v2 t) =
      if x1 = x2 then insert x1 v1 t else insert x2 v2 (insert x1 v1 t)``,
  rpt strip_tac
  \\ qspec_tac (`x1`,`x1`)
  \\ qspec_tac (`v1`,`v1`)
  \\ qspec_tac (`t`,`t`)
  \\ qspec_tac (`v2`,`v2`)
  \\ qspec_tac (`x2`,`x2`)
  \\ recInduct insert_ind \\ rpt strip_tac \\
    (Cases_on `k = 0` \\ fs [] THEN1
     (once_rewrite_tac [insert_def] \\ fs [] \\ rw []
      THEN1 (once_rewrite_tac [insert_def] \\ fs [])
      \\ once_rewrite_tac [insert_def] \\ fs [] \\ rw [])
    \\ once_rewrite_tac [insert_def] \\ fs [] \\ rw []
    \\ simp [Once insert_def]
    \\ once_rewrite_tac [EQ_SYM_EQ]
    \\ simp [Once insert_def]
    \\ Cases_on `x1` \\ fs [ADD1]
    \\ Cases_on `k` \\ fs [ADD1]
    \\ rw [] \\ fs [EVEN_ADD]
    \\ fs [GSYM ODD_EVEN]
    \\ fs [EVEN_EXISTS,ODD_EXISTS] \\ rpt BasicProvers.var_eq_tac
    \\ fs [ADD1,DIV_MULT|>ONCE_REWRITE_RULE[MULT_COMM],
                MULT_DIV|>ONCE_REWRITE_RULE[MULT_COMM]]));

val insert_shadow = store_thm("insert_shadow",
  ``!t a b c. insert a b (insert a c t) = insert a b t``,
  once_rewrite_tac [insert_insert] \\ simp []);

(* the sub-map relation, a partial order *)

val spt_left_def = Define `
  (spt_left LN = LN) /\
  (spt_left (LS x) = LN) /\
  (spt_left (BN t1 t2) = t1) /\
  (spt_left (BS t1 x t2) = t1)`

val spt_right_def = Define `
  (spt_right LN = LN) /\
  (spt_right (LS x) = LN) /\
  (spt_right (BN t1 t2) = t2) /\
  (spt_right (BS t1 x t2) = t2)`

val spt_center_def = Define `
  (spt_center (LS x) = SOME x) /\
  (spt_center (BS t1 x t2) = SOME x) /\
  (spt_center _ = NONE)`

Definition subspt_eq:
  (subspt LN t <=> T) /\
  (subspt (LS x) t <=> (spt_center t = SOME x)) /\
  (subspt (BN t1 t2) t <=>
     subspt t1 (spt_left t) /\ subspt t2 (spt_right t)) /\
  (subspt (BS t1 x t2) t <=>
     (spt_center t = SOME x) /\
     subspt t1 (spt_left t) /\ subspt t2 (spt_right t))
End

val subspt_lookup_lemma = Q.prove(
  `(!x y. ((if x = 0:num then SOME a else f x) = SOME y) ==> p x y)
   <=>
   p 0 a /\ (!x y. x <> 0 /\ (f x = SOME y) ==> p x y)`,
  metis_tac [optionTheory.SOME_11]);

val subspt_lookup = Q.store_thm("subspt_lookup",
  `!t1 t2.
     subspt t1 t2 <=>
     !x y. (lookup x t1 = SOME y) ==> (lookup x t2 = SOME y)`,
  Induct
  \\ fs [lookup_def,subspt_eq]
  THEN1 (Cases_on `t2` \\ fs [lookup_def,spt_center_def])
  \\ rw []
  THEN1
   (Cases_on `t2`
    \\ fs [lookup_def,spt_center_def,spt_left_def,spt_right_def]
    \\ eq_tac \\ rw []
    \\ TRY (pop_assum mp_tac >> srw_tac[][] >> NO_TAC)
    \\ TRY (first_x_assum (fn th => qspec_then `2 * x + 1` mp_tac th THEN
                                    qspec_then `(2 * x + 1) + 1` mp_tac th))
    \\ fs [MULT_DIV |> ONCE_REWRITE_RULE [MULT_COMM],
           DIV_MULT |> ONCE_REWRITE_RULE [MULT_COMM]]
    \\ fs [EVEN_ADD,EVEN_DOUBLE])
  \\ Cases_on `spt_center t2` \\ fs []
  THEN1
   (qexists_tac `0` \\ fs []
    \\ Cases_on `t2` \\ fs [spt_center_def,lookup_def])
  \\ reverse (Cases_on `x = a`) \\ fs []
  THEN1
   (qexists_tac `0` \\ fs []
    \\ Cases_on `t2` \\ fs [spt_center_def,lookup_def])
  \\ BasicProvers.var_eq_tac
  \\ fs [subspt_lookup_lemma]
  \\ `lookup 0 t2 = SOME a` by
       (Cases_on `t2` \\ fs [spt_center_def,lookup_def])
  \\ fs []
  \\ Cases_on `t2`
  \\ fs [lookup_def,spt_center_def,spt_left_def,spt_right_def]
  \\ eq_tac \\ rw []
  \\ TRY (pop_assum mp_tac >> srw_tac[][] >> NO_TAC)
  \\ TRY (first_x_assum (fn th => qspec_then `2 * x + 1` mp_tac th THEN
                                  qspec_then `(2 * x + 1) + 1` mp_tac th))
  \\ fs [MULT_DIV |> ONCE_REWRITE_RULE [MULT_COMM],
         DIV_MULT |> ONCE_REWRITE_RULE [MULT_COMM]]
  \\ fs [EVEN_ADD,EVEN_DOUBLE]);

val subspt_domain = Q.store_thm("subspt_domain",
  `!t1 (t2:unit spt).
     subspt t1 t2 <=> domain t1 SUBSET domain t2`,
  fs [subspt_lookup,domain_lookup,SUBSET_DEF]);

val subspt_def = Q.store_thm("subspt_def",
  `!sp1 sp2.
     subspt sp1 sp2 <=>
     !k. k IN domain sp1 ==> k IN domain sp2 /\
         (lookup k sp2 = lookup k sp1)`,
  fs [subspt_lookup,domain_lookup]
  \\ metis_tac [optionTheory.SOME_11]);

Theorem subspt_refl[simp]: subspt sp sp
Proof simp[subspt_def]
QED

val subspt_trans = Q.store_thm(
  "subspt_trans",
  `subspt sp1 sp2 /\ subspt sp2 sp3 ==> subspt sp1 sp3`,
  simp [subspt_lookup]);

Theorem subspt_LN[simp]:
  (subspt LN sp <=> T) /\ (subspt sp LN <=> (domain sp = {}))
Proof
  simp[subspt_def, EXTENSION]
QED

Theorem subspt_union[simp]: subspt s (union s t)
Proof fs[subspt_lookup,lookup_union]
QED

Theorem subspt_FOLDL_union:
  !ls t. subspt t (FOLDL union t ls)
Proof
  Induct \\ rw[] \\ metis_tac[subspt_union,subspt_trans]
QED

Theorem domain_mapi[simp]:
  domain (mapi f x) = domain x
Proof fs [domain_lookup,EXTENSION,lookup_mapi]
QED

Theorem lookup_FOLDL_union:
  lookup k (FOLDL union t ls) =
  FOLDL OPTION_CHOICE (lookup k t) (MAP (lookup k) ls)
Proof
  qid_spec_tac‘t’ >> Induct_on‘ls’ >> rw[lookup_union] >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Theorem map_union:
  !t1 t2. map f (union t1 t2) = union (map f t1) (map f t2)
Proof
  Induct >> rw[map_def,union_def] >>
  BasicProvers.TOP_CASE_TAC >> rw[map_def,union_def]
QED

Theorem domain_eq:
  !t1 t2. (domain t1 = domain t2) <=>
          !k. (lookup k t1 = NONE) <=> (lookup k t2 = NONE)
Proof
  rw [domain_lookup,EXTENSION] \\ eq_tac \\ rw []
  >- (pop_assum (qspec_then `k` mp_tac)
      \\ Cases_on `lookup k t1` \\ fs []
      \\ Cases_on `lookup k t2` \\ fs [])
  >- (pop_assum (qspec_then `x` mp_tac)
     \\ Cases_on `lookup x t1` \\ fs []
     \\ Cases_on `lookup x t2` \\ fs [])
QED

(* filter values stored in sptree *)

Definition filter_v_def:
  (filter_v f LN = LN) /\
  (filter_v f (LS x) = if f x then LS x else LN) /\
  (filter_v f (BN l r) = mk_BN (filter_v f l) (filter_v f r)) /\
  (filter_v f (BS l x r) =
    if f x then mk_BS (filter_v f l) x (filter_v f r)
           else mk_BN (filter_v f l) (filter_v f r))
End

val lookup_filter_v = store_thm("lookup_filter_v",
  ``!k t f. lookup k (filter_v f t) = case lookup k t of
      | SOME v => if f v then SOME v else NONE
      | NONE => NONE``,
  ho_match_mp_tac (theorem "lookup_ind") \\ rpt strip_tac \\
  rw [filter_v_def, lookup_mk_BS, lookup_mk_BN] \\ rw [lookup_def] \\ fs []);

val wf_filter_v = store_thm("wf_filter_v",
  ``!t f. wf t ==> wf (filter_v f t)``,
  Induct \\ rw [filter_v_def, wf_def, mk_BN_thm, mk_BS_thm] \\ fs []);

val wf_mk_BN = Q.store_thm(
  "wf_mk_BN",
  `wf t1 /\ wf t2 ==> wf (mk_BN t1 t2)`,
  map_every Cases_on [`t1`, `t2`] >> simp[mk_BN_def, wf_def])

val wf_mk_BS = Q.store_thm(
  "wf_mk_BS",
  `wf t1 /\ wf t2 ==> wf (mk_BS t1 a t2)`,
  map_every Cases_on [`t1`, `t2`] >> simp[mk_BS_def, wf_def])

val wf_mapi = Q.store_thm(
  "wf_mapi",
  `wf (mapi f pt)`,
  simp[mapi_def] >>
  `!n. wf (mapi0 f n pt)` suffices_by simp[] >> Induct_on `pt` >>
  simp[wf_def, wf_mk_BN, wf_mk_BS]);

val ALOOKUP_MAP_lemma = Q.prove(
  `ALOOKUP (MAP (\kv. (FST kv, f (FST kv) (SND kv))) al) n =
   OPTION_MAP (\v. f n v) (ALOOKUP al n)`,
  Induct_on `al` >> simp[pairTheory.FORALL_PROD] >> rw[]);

val lookup_mk_BN = Q.store_thm(
  "lookup_mk_BN",
  `lookup i (mk_BN t1 t2) =
    if i = 0 then NONE
    else lookup ((i - 1) DIV 2) (if EVEN i then t1 else t2)`,
  map_every Cases_on [`t1`, `t2`] >> simp[mk_BN_def, lookup_def]);

val MAP_foldi = Q.store_thm(
  "MAP_foldi",
  `!n acc. MAP f (foldi (\k v a. (k,v)::a) n acc pt) =
             foldi (\k v a. (f (k,v)::a)) n (MAP f acc) pt`,
  Induct_on `pt` >> simp[foldi_def]);

val mapi_Alist = Q.store_thm(
  "mapi_Alist",
  `mapi f pt =
    fromAList (MAP (\kv. (FST kv,f (FST kv) (SND kv))) (toAList pt))`,
  simp[spt_eq_thm, wf_mapi, wf_fromAList, lookup_fromAList] >>
  srw_tac[boolSimps.ETA_ss][lookup_mapi, ALOOKUP_MAP_lemma, ALOOKUP_toAList]);

val num_set_domain_eq = Q.store_thm("num_set_domain_eq",
  `!t1 t2:unit spt.
     wf t1 /\ wf t2 ==>
     ((domain t1 = domain t2) <=> (t1 = t2))`,
  rw[] >> EQ_TAC >> rw[spt_eq_thm] >>
  fs[EXTENSION, domain_lookup] >>
  pop_assum (qspec_then `n` mp_tac) >> strip_tac >>
  Cases_on `lookup n t1` >> fs[] >> Cases_on `lookup n t2` >> fs[]);

val union_num_set_sym = Q.store_thm ("union_num_set_sym",
  `!(t1:unit spt) t2. union t1 t2 = union t2 t1`,
  Induct >> fs[union_def] >> rw[] >> CASE_TAC >> fs[union_def]);

Theorem union_disjoint_sym:
  !t1 t2.
  wf t1 /\ wf t2 /\ DISJOINT (domain t1) (domain t2) ==>
  union t1 t2 = union t2 t1
Proof
  Induct
  >- rw[]
  >- (
    rw[union_def]
    \\ CASE_TAC \\ rw[union_def]
    \\ fs[] )
  \\ rw[wf_def] \\ fs[]
  \\ rw[Once union_def]
  \\ CASE_TAC \\ rw[Once union_def, SimpRHS] \\ fs[]
  \\ first_x_assum irule \\ fs[wf_def]
  \\ gs[pred_setTheory.DISJOINT_IMAGE]
  \\ simp[pred_setTheory.DISJOINT_SYM]
QED

Theorem difference_sub:
  (difference a b = LN) ==> (domain a SUBSET domain b)
Proof
  disch_then (assume_tac o Q.AP_TERM ‘domain’) >>
  gs[EXTENSION, SUBSET_DEF] >> metis_tac[]
QED

val wf_difference = Q.store_thm("wf_difference",
  `!t1 t2. wf t1 /\ wf t2 ==> wf (difference t1 t2)`,
  Induct >> rw[difference_def, wf_def] >> CASE_TAC >> fs[wf_def]
  >> rw[wf_def, wf_mk_BN, wf_mk_BS]);

val delete_fail = Q.store_thm ("delete_fail",
  `!n t. wf t ==> (~(n IN domain t) <=> (delete n t = t))`,
  simp[domain_lookup] >>
  recInduct (fetch "-" "lookup_ind") >>
  rw[lookup_def, wf_def, delete_def, mk_BN_thm, mk_BS_thm]);

val size_delete = Q.store_thm ( "size_delete",
  `!n t . size (delete n t) =
          if lookup n t = NONE then size t else size t - 1`,
  rw[size_def] >> fs[lookup_NONE_domain] >>
  TRY (qpat_assum `n NOTIN d` (qspecl_then [] mp_tac)) >>
  rfs[delete_fail, size_def] >>
  fs[size_domain,lookup_NONE_domain,size_domain]);

val lookup_fromList_outside = Q.store_thm("lookup_fromList_outside",
  `!k. LENGTH args <= k ==> (lookup k (fromList args) = NONE)`,
  SIMP_TAC std_ss [lookup_fromList] \\ DECIDE_TAC);

val lemmas = Q.prove(
  `(2 + 2 * n - 1 = 2 * n + 1:num) /\
    ((2 + 2 * n' = 2 * n'' + 2) <=> (n' = n'':num)) /\
    ((2 * m = 2 * n) <=> (m = n)) /\
    ((2 * n'' + 1) DIV 2 = n'') /\
    ((2 * n) DIV 2 = n) /\
    (2 + 2 * n' <> 2 * n'' + 1) /\
    (2 * m + 1 <> 2 * n' + 2)`,
  REPEAT STRIP_TAC \\ SIMP_TAC std_ss [] \\ fs []
  \\ full_simp_tac(srw_ss())[ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
  \\ full_simp_tac(srw_ss())[ONCE_REWRITE_RULE [MULT_COMM] DIV_MULT]
  \\ IMP_RES_TAC (METIS_PROVE [] ``(m = n) ==> (m MOD 2 = n MOD 2)``)
  \\ POP_ASSUM MP_TAC \\ SIMP_TAC std_ss []
  \\ ONCE_REWRITE_TAC [MATCH_MP (GSYM MOD_PLUS) (DECIDE ``0 < 2:num``)]
  \\ EVAL_TAC \\ fs[MOD_EQ_0,ONCE_REWRITE_RULE [MULT_COMM] MOD_EQ_0]);

val spt_fold_def = Define `
  (spt_fold f acc LN = acc) /\
  (spt_fold f acc (LS a) = f a acc) /\
  (spt_fold f acc (BN t1 t2) = spt_fold f (spt_fold f acc t1) t2) /\
  (spt_fold f acc (BS t1 a t2) = spt_fold f (f a (spt_fold f acc t1)) t2)`

val IMP_size_LESS_size = store_thm("IMP_size_LESS_size",
  ``!x y. subspt x y /\ domain x <> domain y ==> size x < size y``,
  fs [size_domain,domain_difference] \\ rw []
  \\ `?t. (domain y = domain x UNION t) /\ t <> EMPTY /\
          (domain x INTER t = EMPTY)` by
   (qexists_tac `domain y DIFF domain x`
    \\ fs [EXTENSION]
    \\ qsuff_tac `domain x SUBSET domain y`
    THEN1 (fs [EXTENSION,SUBSET_DEF] \\ metis_tac [])
    \\ fs [domain_lookup,subspt_lookup,SUBSET_DEF]
    \\ rw [] \\ res_tac \\ fs [])
  \\ asm_rewrite_tac []
  \\ `FINITE (domain y)` by fs [FINITE_domain]
  \\ `FINITE t` by metis_tac [FINITE_UNION]
  \\ fs [CARD_UNION_EQN]
  \\ `CARD t <> 0` by metis_tac [CARD_EQ_0] \\ fs []);

val size_diff_less = store_thm("size_diff_less",
  ``!x y z t.
      domain z SUBSET domain y /\ t IN domain y /\
      ~(t IN domain z) /\ t IN domain x ==>
      size (difference x y) < size (difference x z)``,
  rw []
  \\ match_mp_tac IMP_size_LESS_size
  \\ fs [domain_difference,EXTENSION]
  \\ reverse conj_tac THEN1 metis_tac []
  \\ fs [subspt_lookup,lookup_difference]
  \\ rw [] \\ fs [SUBSET_DEF,domain_lookup,PULL_EXISTS]
  \\ CCONTR_TAC
  \\ Cases_on `lookup x' z` \\ fs []
  \\ res_tac \\ fs []);

val inter_eq_LN = store_thm("inter_eq_LN",
  ``!x y. (inter x y = LN) <=> DISJOINT (domain x) (domain y)``,
  fs [spt_eq_thm,wf_inter,wf_def,lookup_def,lookup_inter_alt]
  \\ fs [domain_lookup,IN_DISJOINT]
  \\ metis_tac [optionTheory.NOT_SOME_NONE,optionTheory.SOME_11,
                optionTheory.option_CASES]);

val list_to_num_set_def = Define `
  (list_to_num_set [] = LN) /\
  (list_to_num_set (n::ns) = insert n () (list_to_num_set ns))`;

val list_insert_def = Define `
  (list_insert [] t = t) /\
  (list_insert (n::ns) t = list_insert ns (insert n () t))`;

Theorem domain_list_to_num_set:
  !xs. x IN domain (list_to_num_set xs) <=> MEM x xs
Proof
   Induct \\ full_simp_tac(srw_ss())[list_to_num_set_def]
QED

Theorem domain_list_insert:
  !xs x t.
      x IN domain (list_insert xs t) <=> MEM x xs \/ x IN domain t
Proof
   Induct \\ full_simp_tac(srw_ss())[list_insert_def] \\ METIS_TAC []
QED

Theorem domain_FOLDR_delete:
  !ls live. domain (FOLDR delete live ls) = (domain live) DIFF (set ls)
Proof
  Induct>> full_simp_tac(srw_ss())[DIFF_INSERT,EXTENSION]>> metis_tac[]
QED

Theorem lookup_list_to_num_set:
  !xs. lookup x (list_to_num_set xs) = if MEM x xs then SOME () else NONE
Proof
  Induct \\ srw_tac [] [list_to_num_set_def,lookup_def,lookup_insert] \\
  full_simp_tac(srw_ss())[]
QED

Theorem list_to_num_set_append:
  !l1 l2. list_to_num_set (l1 ++ l2) =
          union (list_to_num_set l1) (list_to_num_set l2)
Proof
  Induct \\ rw[list_to_num_set_def]
  \\ rw[Once insert_union]
  \\ rw[Once insert_union,SimpRHS]
  \\ rw[union_assoc]
QED

Theorem map_map_K[simp]:
  !t. map (K a) (map f t) = map (K a) t
Proof    Induct \\ fs[map_def]
QED

Theorem lookup_map_K:
  !t n. lookup n (map (K x) t) = if n IN domain t then SOME x else NONE
Proof
   Induct >> fs[IN_domain,map_def,lookup_def] >>
   rpt strip_tac >> Cases_on `n = 0` >> fs[] >>
   Cases_on `EVEN n` >> fs[]
QED

Definition alist_insert_def:
  alist_insert [] xs t = t /\
  alist_insert vs [] t = t /\
  alist_insert (v::vs) (x::xs) t = insert v x (alist_insert vs xs t)
End

Theorem lookup_alist_insert:
  !x y t z.
    (LENGTH x = LENGTH y) ==>
    (lookup z (alist_insert x y t) =
     case ALOOKUP (ZIP(x,y)) z of SOME a => SOME a | NONE => lookup z t)
Proof
   ho_match_mp_tac alist_insert_ind >>
   srw_tac[][] >- fs[LENGTH,alist_insert_def] >>
   Cases_on`z=x`>> srw_tac[][lookup_def,alist_insert_def]>>
   full_simp_tac(srw_ss())[lookup_insert]
QED

Theorem domain_alist_insert:
  !a b locs. (LENGTH a = LENGTH b) ==>
              (domain (alist_insert a b locs) = domain locs UNION set a)
Proof
   Induct_on`a`>>Cases_on`b`>>full_simp_tac(srw_ss())[alist_insert_def]>>
   srw_tac[][]>> metis_tac[INSERT_UNION_EQ,UNION_COMM]
QED

Theorem alist_insert_append:
  !a1 a2 s b1 b2.
     (LENGTH a1 = LENGTH a2) ==>
     (alist_insert (a1++b1) (a2++b2) s =
      alist_insert a1 a2 (alist_insert b1 b2 s))
Proof
  ho_match_mp_tac alist_insert_ind
  \\ simp[alist_insert_def,LENGTH_NIL_SYM]
QED

Theorem wf_LN[simp]: wf LN
Proof rw[wf_def]
QED

Theorem wf_fromList[simp]:
  wf (fromList ls)
Proof
  rw[fromList_def]
  \\ qmatch_goalsub_abbrev_tac`FOLDL f (0,LN) ls`
  \\ qho_match_abbrev_tac`P (FOLDL f (0,LN) ls)`
  \\ `FOLDL f (0,LN) ls = FOLDL f (0,LN) ls /\ P (FOLDL f (0,LN) ls)`
  suffices_by rw[]
  \\ irule rich_listTheory.FOLDL_CONG_invariant
  \\ simp[Abbr`P`, Abbr`f`, pairTheory.FORALL_PROD]
  \\ rw[wf_insert]
QED

Theorem wf_list_to_num_set[simp]:
  !ls. wf (list_to_num_set ls)
Proof
  Induct \\ rw[list_to_num_set_def, wf_insert]
QED

Theorem mapi_fromList:
  mapi f (fromList ls) = fromList (MAPi f ls)
Proof
  DEP_REWRITE_TAC[spt_eq_thm]
  \\ simp[wf_mapi]
  \\ rw[lookup_fromList, lookup_mapi]
QED

Theorem insert_fromList_IN_domain:
  !ls k v.
  k < LENGTH ls ==>
  insert k v (fromList ls) =
  fromList (TAKE k ls ++ [v] ++ DROP (SUC k) ls)
Proof
  simp[fromList_def]
  \\ ho_match_mp_tac SNOC_INDUCT
  \\ rw[FOLDL_SNOC, rich_listTheory.TAKE_SNOC]
  \\ Cases_on`k = LENGTH ls` \\ gs[]
  >- (
    rw[rich_listTheory.DROP_LENGTH_NIL_rwt]
    \\ gs[GSYM fromList_def, pairTheory.UNCURRY]
    \\ qmatch_goalsub_abbrev_tac`FST (FOLDL f e ls)`
    \\ `!ls e. FST (FOLDL f e ls) = FST e + LENGTH ls`
    by ( Induct \\ rw[Abbr`f`, pairTheory.UNCURRY] )
    \\ rw[Abbr`e`, insert_shadow]
    \\ simp[fromList_def, rich_listTheory.FOLDL_APPEND]
    \\ simp[Abbr`f`, pairTheory.UNCURRY] )
  \\ gs[GSYM fromList_def, pairTheory.UNCURRY, rich_listTheory.DROP_SNOC]
  \\ simp[SNOC_APPEND]
  \\ qmatch_goalsub_abbrev_tac`FST (FOLDL f e ls)`
  \\ `!ls e. FST (FOLDL f e ls) = FST e + LENGTH ls`
  by ( Induct \\ rw[Abbr`f`, pairTheory.UNCURRY] )
  \\ simp[Abbr`e`]
  \\ simp[Once insert_insert]
  \\ simp[fromList_def]
  \\ simp[Once rich_listTheory.FOLDL_APPEND, SimpRHS]
  \\ simp[Abbr`f`, pairTheory.UNCURRY]
  \\ simp[ADD1]
QED

val splem1 = Q.prove(`
  a <> 0 ==> (a-1) DIV 2 < a`,
  simp[DIV_LT_X]);

val DIV2_P_UNIV =
  DIV_P_UNIV |> SPEC_ALL |> Q.INST [`n` |-> `2`] |> SIMP_RULE (srw_ss()) []
             |> EQ_IMP_RULE |> #2 |> Q.GENL [`P`, `m`]

val splem3 = Q.prove(
  `(EVEN c /\ EVEN a \/ ODD a /\ ODD c) /\ a <> c /\ a <> 0 /\ c <> 0 ==>
   (a-1) DIV 2 <> (c-1) DIV 2`,
  map_every Cases_on [`a`, `c`] >>
  simp[DIV_LT_X, EVEN, ODD] >> DEEP_INTRO_TAC DIV2_P_UNIV >> rpt gen_tac >>
  rw[] >> fs[EVEN_ADD, EVEN_MULT, ODD_ADD, ODD_MULT] >>
  DEEP_INTRO_TAC DIV2_P_UNIV >> rw[] >>
  fs[EVEN_ADD, EVEN_MULT, ODD_ADD, ODD_MULT] >>
  rpt (rename [‘x < 2’] >> ‘(x = 0) \/ (x = 1)’ by simp[] >> fs[]));

Theorem insert_swap:
  !t a b c d.
    a <> c ==> (insert a b (insert c d t) = insert c d (insert a b t))
Proof
  completeInduct_on`a`>>
  completeInduct_on`c`>>
  Induct>>
  rw[]>>
  simp[Once insert_def,SimpRHS]>>
  simp[Once insert_def]>>
  ntac 2 IF_CASES_TAC>>
  fs[]>>
  rw[]>>
  simp[Once insert_def,SimpRHS]>>
  simp[Once insert_def]>>
  imp_res_tac splem1>>
  imp_res_tac splem3>>
  metis_tac[EVEN_ODD]
QED

Theorem alist_insert_pull_insert:
  !xs ys z. ~MEM x xs ==>
             (alist_insert xs ys (insert x y z) =
              insert x y (alist_insert xs ys z))
Proof
  ho_match_mp_tac alist_insert_ind
  \\ simp[alist_insert_def] \\ rw[] \\ fs[]
  \\ metis_tac[insert_swap]
QED

Theorem alist_insert_REVERSE:
  !xs ys s.
    ALL_DISTINCT xs /\ (LENGTH xs = LENGTH ys) ==>
    (alist_insert (REVERSE xs) (REVERSE ys) s = alist_insert xs ys s)
Proof
  Induct \\ simp[alist_insert_def]
  \\ gen_tac \\ Cases \\ simp[alist_insert_def]
  \\ simp[alist_insert_append,alist_insert_def]
  \\ rw[] \\ simp[alist_insert_pull_insert]
QED

Theorem insert_unchanged:
  !t x.
    (lookup x t = SOME y) ==> (insert x y t = t)
Proof
  completeInduct_on`x`>> Induct>> fs[lookup_def]>>rw[]>>
  simp[Once insert_def,SimpRHS]>> simp[Once insert_def]>> imp_res_tac splem1>>
  metis_tac[]
QED

Triviality delete_mk_BN:
  (delete 0 (mk_BN t1 t2) = mk_BN t1 t2) /\
  (k <> 0 ==> delete k (mk_BN t1 t2) = delete k (BN t1 t2))
Proof
  Cases_on `t1` \\ Cases_on `t2` \\ fs [mk_BN_def]
  \\ fs [delete_def,mk_BN_def]
QED

Triviality delete_mk_BS:
  (delete 0 (mk_BS t1 s t2) = mk_BN t1 t2) /\
  (k <> 0 ==> delete k (mk_BS t1 s t2) = delete k (BS t1 s t2))
Proof
  Cases_on `t1` \\ Cases_on `t2` \\ fs [mk_BS_def]
  \\ fs [delete_def,mk_BS_def,mk_BN_def]
QED

Triviality DIV_2_lemma:
  n DIV 2 = m DIV 2 /\ EVEN m = EVEN n ==> m = n
Proof
  rw []
  \\ `0 < 2n` by fs [] \\ drule DIVISION
  \\ fs [EVEN_MOD2]
  \\ disch_then (fn th => once_rewrite_tac [th]) \\ fs []
  \\ Cases_on `m MOD 2 = 0` \\ fs []
  \\ `n MOD 2 < 2` by fs [MOD_LESS]
  \\ `m MOD 2 < 2` by fs [MOD_LESS]
  \\ decide_tac
QED

Theorem delete_delete:
  !f n k.
    delete n (delete k f) =
    if n = k then delete n f else delete k (delete n f)
Proof
  Induct \\ fs [delete_def]
  \\ rw [] \\ fs [delete_def]
  \\ simp [delete_mk_BN,delete_mk_BS]
  \\ rpt (qpat_x_assum `!x. _` (mp_tac o GSYM)) \\ rw [] \\ fs [delete_def]
  \\ rpt (qpat_x_assum `!x. _` (fn th => simp [Once (GSYM th)])) \\ rw []
  \\ rpt (rename [`kk <> 0`] \\ Cases_on `kk` \\ fs [])
  \\ drule DIV_2_lemma \\ fs [EVEN]
QED

Theorem size_zero_empty:
  !x. size x = 0 <=> domain x = EMPTY
Proof
  Induct \\ fs [size_def]
QED

Theorem list_size_APPEND:
  list_size f (xs ++ ys) = list_size f xs + list_size f ys
Proof
  Induct_on `xs` \\ fs [list_size_def]
QED

Theorem size_map[simp]:
  size (map f t) = size t
Proof
  rw[size_domain]
QED

Theorem size_mapi[simp]:
  size (mapi f t) = size t
Proof
  rw[size_domain]
QED

val spt_size_def = definition "spt_size_def";

Theorem SUM_MAP_same_LE:
  EVERY (\x. f x <= g x) xs
  ==>
  SUM (MAP f xs) <= SUM (MAP g xs)
Proof
  Induct_on `xs` \\ rw [] \\ fs []
QED

Theorem SUM_MAP_same_LESS:
  EVERY (\x. f x <= g x) xs /\ EXISTS (\x. f x < g x) xs
  ==>
  SUM (MAP f xs) < SUM (MAP g xs)
Proof
  Induct_on `xs` \\ rw [] \\ imp_res_tac SUM_MAP_same_LE \\ fs []
QED

Theorem lookup_0_spt_center:
  !spt. lookup 0 spt = spt_center spt
Proof
  Cases \\ EVAL_TAC
QED

Theorem lookup_spt_right:
  lookup i (spt_right spt) = lookup ((i * 2) + 1) spt
Proof
  ASSUME_TAC (Q.SPEC `2` MULT_DIV)
  \\ Cases_on `spt` \\ fs [spt_right_def, lookup_def]
  \\ fs [EVEN_MULT, EVEN_ADD]
QED

Theorem lookup_spt_left:
  lookup i (spt_left spt) = lookup ((i * 2) + 2) spt
Proof
  ASSUME_TAC (Q.SPEC `2` MULT_DIV)
  \\ Cases_on `spt` \\ fs [spt_left_def, lookup_def]
  \\ fs [EVEN_MULT, EVEN_ADD, ADD_DIV_RWT]
QED

Definition spts_to_alist_add_pause_def:
  spts_to_alist_add_pause j q = (case q of
    | [] => [(j, LN)]
    | ((i, spt) :: q) => ((i + j, spt) :: q)
  )
End

val _ = temp_overload_on("add_pause", ``spts_to_alist_add_pause``);

Triviality SUM_add_pause:
  SUM (MAP FST (add_pause j q)) = j + SUM (MAP FST q)
Proof
  simp [spts_to_alist_add_pause_def]
  \\ BasicProvers.every_case_tac
  \\ simp []
QED

Definition spts_to_alist_aux_def:
  spts_to_alist_aux i xs acc_cent acc_right acc_left repeat =
    case xs of
      | [] => (i, REVERSE acc_right ++ REVERSE acc_left, acc_cent, repeat)
      | (j, spt) :: ys =>
      if isEmpty spt then spts_to_alist_aux (i + j) ys acc_cent
        (add_pause j acc_right) (add_pause j acc_left)
        repeat
      else spts_to_alist_aux (i + j) ys
        ((case spt_center spt of NONE => [] | SOME c => [(i, c)]) ++ acc_cent)
        ((j, spt_right spt) :: acc_right) ((j, spt_left spt) :: acc_left)
        T
End

Theorem spts_to_alist_aux_size:
  ! i xs acc_cent acc_right acc_left repeat.
  ! j ys acc2 repeat2.
    spts_to_alist_aux i xs acc_cent acc_right acc_left repeat = (j, ys, acc2, repeat2) ==>
    let sz = (SUM o MAP (spt_size (K 0) o SND)) in
      sz ys <= sz (xs ++ acc_right ++ acc_left) /\
      (repeat2 ==> ~ repeat ==> sz ys < sz (xs ++ acc_right ++ acc_left))
Proof
  ho_match_mp_tac spts_to_alist_aux_ind
  \\ rpt strip_tac
  \\ pop_assum mp_tac
  \\ simp [Once spts_to_alist_aux_def]
  \\ simp [CaseEq "list", CaseEq "prod", CaseEq "bool"]
  \\ strip_tac
  >- (
    gvs [MAP_REVERSE, SUM_APPEND, rich_listTheory.SUM_REVERSE]
  )
  >- (
    fs [spts_to_alist_add_pause_def]
    \\ BasicProvers.every_case_tac
    \\ fs [spt_size_def, SUM_APPEND]
  )
  >- (
    rename [`~ isEmpty spt`] \\ Cases_on `spt`
    \\ fs [spt_left_def, spt_right_def, spt_size_def, SUM_APPEND]
  )
QED

Definition spts_to_alist_def:
  spts_to_alist i xs acc_cent =
    let (i, xs, acc_cent, repeat) =
      spts_to_alist_aux i xs acc_cent [] [] F in
    if repeat then spts_to_alist i xs acc_cent
    else REVERSE acc_cent
Termination
  WF_REL_TAC `measure (\(_, xs, _). SUM (MAP (spt_size (K 0) o SND) xs))`
  \\ rw []
  \\ first_x_assum (assume_tac o GSYM)
  \\ drule_then mp_tac spts_to_alist_aux_size
  \\ simp [combinTheory.o_DEF]
End

Definition gather_inclist_offsets_def:
  gather_inclist_offsets [] = [] /\
  gather_inclist_offsets ((inc, x) :: xs) =
    (0, x) :: MAP ((+) inc ## I) (gather_inclist_offsets xs)
End

Theorem gather_inclist_offsets_append:
  gather_inclist_offsets (xs ++ ys) =
  gather_inclist_offsets xs ++ MAP ((+) (SUM (MAP FST xs)) ## I) (gather_inclist_offsets ys)
Proof
  Induct_on `xs`
  \\ simp [gather_inclist_offsets_def, pairTheory.FORALL_PROD]
  \\ simp [Q.prove (`(+) 0 = I`, simp [FUN_EQ_THM])]
  \\ rw [MAP_MAP_o]
  \\ irule MAP_CONG
  \\ simp [pairTheory.FORALL_PROD]
QED

Theorem MAP_SND_gather_inclist_offsets:
  MAP SND (gather_inclist_offsets xs) = MAP SND xs
Proof
  Induct_on `xs`
  \\ simp [gather_inclist_offsets_def, pairTheory.FORALL_PROD]
  \\ simp [MAP_MAP_o, Q.prove (`SND o (f ## g) = g o SND`, simp [FUN_EQ_THM])]
QED

val _ = temp_overload_on("inclist_stable",
  `` \xs. FILTER ((~) o isEmpty o SND) (gather_inclist_offsets xs) ``)

Triviality gather_add_pause:
  inclist_stable (REVERSE (add_pause j xs)) =
  inclist_stable (REVERSE xs)
Proof
  simp [spts_to_alist_add_pause_def] \\ BasicProvers.every_case_tac
  \\ fs [gather_inclist_offsets_append, gather_inclist_offsets_def]
QED

Theorem spts_to_alist_aux_properties:
  ! i xs acc_cent acc_right acc_left repeat.
  ! j ys acc2 repeat2.
    spts_to_alist_aux i xs acc_cent acc_right acc_left repeat = (j, ys, acc2, repeat2) ==>
    j = i + SUM (MAP FST xs) /\
    SUM (MAP FST ys) = SUM (MAP FST (acc_right ++ acc_left ++ xs ++ xs)) /\
    inclist_stable ys = inclist_stable (REVERSE acc_right ++
            MAP (I ## spt_right) xs ++ REVERSE acc_left ++ MAP (I ## spt_left) xs) /\
    acc2 = REVERSE (FLAT (MAP (\(j, spt). case spt_center spt of
      | NONE => [] | SOME v => [(i + j, v)]) (inclist_stable xs))) ++ acc_cent /\
    repeat2 = (repeat \/ ~ NULL (inclist_stable xs))
Proof
  ho_match_mp_tac spts_to_alist_aux_ind
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ pop_assum mp_tac
  \\ simp [Once spts_to_alist_aux_def]
  \\ simp [CaseEq "list", CaseEq "prod", CaseEq "bool"]
  \\ strip_tac
  >- (
    fs [gather_inclist_offsets_def]
    \\ gvs [SUM_APPEND, MAP_REVERSE, rich_listTheory.SUM_REVERSE]
  )
  >- (
    gs []
    \\ simp [gather_inclist_offsets_def]
    \\ simp [gather_inclist_offsets_append, SUM_APPEND, gather_inclist_offsets_def,
        MAP_REVERSE, rich_listTheory.SUM_REVERSE]
    \\ simp [SUM_add_pause, gather_add_pause, FILTER_APPEND_DISTRIB,
        spt_left_def, spt_right_def, rich_listTheory.FILTER_MAP,
        Q.prove (`SND o (f ## g) = g o SND`, simp [FUN_EQ_THM])]
    \\ simp [Q.prove(`NULL (MAP f xs) = NULL xs`, simp [NULL_EQ])]
    \\ simp [MAP_MAP_o, combinTheory.o_DEF]
    \\ simp [pairTheory.ELIM_UNCURRY]
  )
  >- (
    gs []
    \\ simp [gather_inclist_offsets_def, rich_listTheory.FILTER_MAP]
    \\ simp [SUM_APPEND, MAP_REVERSE, rich_listTheory.SUM_REVERSE]
    \\ simp [MAP_MAP_o, combinTheory.o_DEF]
    \\ simp [pairTheory.ELIM_UNCURRY]
    \\ BasicProvers.every_case_tac \\ fs []
  )
QED

Triviality MEM_case = (TypeBase.case_pred_disj_of ``: 'z option``
  |> Q.ISPEC `MEM (x : 'z)` |> SIMP_RULE std_ss [])

Triviality gather_inclist_offsets_MAP_I:
  gather_inclist_offsets (MAP (I ## f) xs) =
  MAP (I ## f) (gather_inclist_offsets xs)
Proof
  Induct_on `xs`
  \\ simp [gather_inclist_offsets_def, pairTheory.FORALL_PROD, MAP_MAP_o, MAP_CONG]
QED

Triviality spts_to_alist_aux_MEM:
  ! i xs acc_cent repeat.
  ! j ys acc2 repeat2.
    spts_to_alist_aux i xs acc_cent [] [] repeat = (j, ys, acc2, repeat2) ==>
  ! k v.
    (MEM (k, v) acc2 \/ (?j1 j2 spt. MEM (j1, spt) (inclist_stable ys) /\
        k = j + j1 + (j2 * SUM (MAP FST ys)) /\ lookup j2 spt = SOME v)) <=>
    (MEM (k, v) acc_cent \/ (?j1 j2 spt. MEM (j1, spt) (inclist_stable xs) /\
        k = i + j1 + (j2 * SUM (MAP FST xs)) /\ lookup j2 spt = SOME v))
Proof
  rw []
  \\ drule spts_to_alist_aux_properties
  \\ rw []
  \\ simp [MEM_FLAT, MEM_MAP, PULL_EXISTS,
            pairTheory.ELIM_UNCURRY, pairTheory.EXISTS_PROD, MEM_case,
            GSYM lookup_0_spt_center, gather_inclist_offsets_append,
            MEM_FILTER, gather_inclist_offsets_MAP_I, MEM_MAP]
  \\ Cases_on `MEM (k, v) acc_cent` \\ fs []
  \\ EQ_TAC \\ disch_tac
  >- (
    gs [lookup_spt_right, lookup_spt_left]
    \\ qpat_assum `lookup _ _ = SOME _` (irule_at Any)
    \\ qpat_assum `MEM _ _` (irule_at Any)
    \\ simp [SUM_APPEND]
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, Q.ISPEC `FST` ETA_THM]
    \\ imp_res_tac (Q.prove (`lookup x spt = SOME y ==> ~ isEmpty spt`,
        CCONTR_TAC \\ gs []))
  )
  >- (
    fs []
    \\ simp [RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR, EXISTS_OR_THM, PULL_EXISTS]
    \\ simp [lookup_spt_right, lookup_spt_left]
    \\ qspec_then `j2` assume_tac bit_cases
    \\ CCONTR_TAC
    \\ gs []
    \\ first_x_assum (drule_at (Pat `lookup _ _ = _`))
    \\ simp []
    \\ qpat_assum `MEM _ _` (irule_at Any)
    \\ simp [SUM_APPEND]
    \\ simp [MAP_MAP_o, combinTheory.o_DEF, Q.ISPEC `FST` ETA_THM]
    \\ irule (Q.prove (`lookup x spt = SOME y ==> ~ isEmpty spt`,
        CCONTR_TAC \\ gs []))
    \\ simp [lookup_spt_right, lookup_spt_left]
    \\ first_x_assum (irule_at Any)
  )
QED

Triviality MEM_spts_to_alist:
  ! i xs acc_cent.
  ! k v. (MEM (k, v) (spts_to_alist i xs acc_cent) <=>
    MEM (k, v) acc_cent \/
    (?j1 j2 spt. MEM (j1, spt) (inclist_stable xs) /\
        k = i + j1 + (j2 * SUM (MAP FST xs)) /\ lookup j2 spt = SOME v))
Proof
  ho_match_mp_tac spts_to_alist_ind
  \\ rw []
  \\ simp [Once spts_to_alist_def]
  \\ pairarg_tac \\ fs []
  \\ drule_then assume_tac spts_to_alist_aux_properties
  \\ drule_then assume_tac spts_to_alist_aux_MEM
  \\ fs []
  \\ rw []
  \\ fs [NULL_EQ]
QED

Triviality spts_to_alist_aux_SORTED:
  ! i xs acc_cent acc_right acc_left repeat.
  ! j ys acc2 repeat2.
    spts_to_alist_aux i xs acc_cent acc_right acc_left repeat = (j, ys, acc2, repeat2) ==>
    EVERY ((\i. 0 < i) o FST) xs /\
    EVERY ((\i. 0 < i) o FST) acc_right /\
    EVERY ((\i. 0 < i) o FST) acc_left /\
    SORTED (<) (REVERSE (i :: MAP FST acc_cent)) ==>
    EVERY ((\i. 0 < i) o FST) ys /\
    SORTED (<) (REVERSE (j :: MAP FST acc2))
Proof
  ho_match_mp_tac spts_to_alist_aux_ind
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ simp_tac bool_ss [Once spts_to_alist_aux_def]
  \\ simp_tac bool_ss [CaseEq "list", CaseEq "prod", CaseEq "bool"]
  \\ strip_tac
  >- (
    gvs []
  )
  >- (
    gvs []
    \\ disch_tac \\ first_x_assum irule
    \\ fs []
    \\ fs [sortingTheory.SORTED_APPEND_GEN, spts_to_alist_add_pause_def]
    \\ BasicProvers.every_case_tac \\ fs []
  )
  >- (
    gvs []
    \\ disch_tac \\ first_x_assum irule
    \\ fs []
    \\ simp [REVERSE_APPEND]
    \\ BasicProvers.every_case_tac \\ fs []
    \\ fs [sortingTheory.SORTED_APPEND_GEN]
  )
QED

Triviality SORTED_spts_to_alist:
  ! i xs acc_cent.
  SORTED (<) (REVERSE (i :: MAP FST acc_cent)) /\
  EVERY ((\i. 0 < i) o FST) xs
  ==>
  SORTED (<) (MAP FST (spts_to_alist i xs acc_cent))
Proof
  ho_match_mp_tac spts_to_alist_ind
  \\ rw []
  \\ simp [Once spts_to_alist_def]
  \\ pairarg_tac \\ fs []
  \\ drule spts_to_alist_aux_SORTED
  \\ simp []
  \\ rw []
  \\ fs [MAP_REVERSE, sortingTheory.SORTED_APPEND_GEN]
QED

Definition toSortedAList_def:
  toSortedAList spt = spts_to_alist 0 [(1, spt)] []
End

Theorem MEM_toSortedAList:
  MEM (i, x) (toSortedAList spt) = (lookup i spt = SOME x)
Proof
  rw [toSortedAList_def, MEM_spts_to_alist,
    gather_inclist_offsets_def]
  \\ simp [lookup_def]
QED

Theorem SORTED_toSortedAList:
  SORTED (<) (MAP FST (toSortedAList spt))
Proof
  simp [toSortedAList_def, SORTED_spts_to_alist]
QED

Theorem ALOOKUP_toSortedAList:
  ALOOKUP (toSortedAList spt) i = lookup i spt
Proof
  Cases_on `lookup i spt`
  >- (
    Cases_on `ALOOKUP (toSortedAList spt) i`
    \\ simp []
    \\ imp_res_tac ALOOKUP_MEM
    \\ rfs [MEM_toSortedAList]
  )
  \\ irule ALOOKUP_ALL_DISTINCT_MEM
  \\ simp [MEM_toSortedAList]
  \\ irule sortingTheory.SORTED_ALL_DISTINCT
  \\ qexists_tac `(<)`
  \\ simp [SORTED_toSortedAList, relationTheory.irreflexive_def]
QED

Theorem toSortedAList_fromList:
  toSortedAList (fromList ls) = ZIP (COUNT_LIST (LENGTH ls),ls)
Proof
  mp_tac (sortingTheory.SORTED_ALL_DISTINCT_LIST_TO_SET_EQ
          |> INST_TYPE [alpha |-> ``:num # 'a``]
          |> Q.SPEC`(\x y. FST x < FST y)`)>>
  impl_keep_tac >-
    fs[relationTheory.transitive_def,relationTheory.antisymmetric_def]>>
  disch_then match_mp_tac>>
  CONJ_ASM1_TAC
  >- (
    match_mp_tac sortingTheory.SORTED_weaken>>
    irule_at Any (SORTED_toSortedAList |> SIMP_RULE std_ss [sortingTheory.sorted_map])>>
    simp[])>>
  CONJ_ASM1_TAC
  >- (
    match_mp_tac sortingTheory.SORTED_FST_ZIP>>
    simp[rich_listTheory.LENGTH_COUNT_LIST,sortingTheory.sorted_lt_count_list])>>
  rw[]
  >- (
    irule sortingTheory.SORTED_ALL_DISTINCT>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    simp[relationTheory.irreflexive_def])
  >- (
    irule sortingTheory.SORTED_ALL_DISTINCT>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    simp[relationTheory.irreflexive_def])
  >- (
    rw[pred_setTheory.EXTENSION]>>
    Cases_on`x`>>
    DEP_REWRITE_TAC[MEM_ZIP]>>
    simp[rich_listTheory.LENGTH_COUNT_LIST,MEM_toSortedAList,lookup_fromList]>>
    metis_tac[rich_listTheory.EL_COUNT_LIST])
QED

Theorem fromList_fromAList:
  !l. fromList l = fromAList (ZIP (COUNT_LIST (LENGTH l), l))
Proof
  ho_match_mp_tac SNOC_INDUCT
  \\ conj_tac >- rw[fromList_def, fromAList_def,
                    rich_listTheory.COUNT_LIST_def]
  \\ rw[fromList_def, rich_listTheory.COUNT_LIST_def]
  \\ rw[FOLDL_SNOC, pairTheory.UNCURRY]
  \\ rw[GSYM rich_listTheory.COUNT_LIST_def]
  \\ rw[rich_listTheory.COUNT_LIST_SNOC,
        rich_listTheory.ZIP_SNOC,
        rich_listTheory.LENGTH_COUNT_LIST]
  \\ rw[SNOC_APPEND, fromAList_append]
  \\ DEP_ONCE_REWRITE_TAC[union_disjoint_sym]
  \\ simp[union_insert_LN]
  \\ simp[wf_fromAList, wf_insert, domain_fromAList,
          MAP_ZIP, rich_listTheory.LENGTH_COUNT_LIST,
          rich_listTheory.MEM_COUNT_LIST]
  \\ AP_THM_TAC \\ AP_THM_TAC
  \\ AP_TERM_TAC
  \\ qmatch_goalsub_abbrev_tac`FOLDL f e l`
  \\ `!l e. FST (FOLDL f e l) = FST e + LENGTH l` suffices_by simp[Abbr`e`]
  \\ Induct \\ rw[Abbr`f`, pairTheory.UNCURRY]
QED

Theorem ALL_DISTINCT_MAP_FST_toSortedAList:
  ALL_DISTINCT (MAP FST (toSortedAList t))
Proof
  irule sortingTheory.SORTED_ALL_DISTINCT>>
  irule_at Any (SORTED_toSortedAList)>>
  simp[relationTheory.irreflexive_def]
QED

Theorem LENGTH_toSortedAList[simp]:
  LENGTH (toSortedAList t) = size t
Proof
  `LENGTH (toSortedAList t) =
    LENGTH (MAP FST (toSortedAList t))` by simp[]>>
  pop_assum SUBST_ALL_TAC>>
  DEP_REWRITE_TAC[GSYM ALL_DISTINCT_CARD_LIST_TO_SET]>>
  simp[ALL_DISTINCT_MAP_FST_toSortedAList,size_domain]>>
  AP_TERM_TAC>>
  rw[pred_setTheory.EXTENSION]>>
  simp[MEM_MAP,pairTheory.EXISTS_PROD,MEM_toSortedAList,domain_lookup]
QED

Theorem set_MAP_FST_toAList_domain:
  set (MAP FST (toAList t)) = domain t
Proof
  rw[EXTENSION]
  \\ `(ALOOKUP (toAList t) x <> NONE) <=> x IN domain t`
  suffices_by metis_tac[ALOOKUP_NONE]
  \\ simp[ALOOKUP_toAList, lookup_NONE_domain]
QED

Theorem size_fromList[simp]:
  size (fromList ls) = LENGTH ls
Proof
  rw[size_domain, domain_fromList]
QED

val _ = let
  open sptreepp
in
  add_ML_dependency "sptreepp";
  add_user_printer ("sptreepp.sptreepp", “x : 'a spt”)
end

val _ = export_theory();
