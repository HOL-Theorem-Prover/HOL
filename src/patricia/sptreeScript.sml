open HolKernel Parse boolLib bossLib;
open lcsymtacs
open arithmeticTheory
open logrootTheory
open listTheory
open alistTheory

val _ = new_theory "sptree";

(* A log-time random-access, extensible array implementation with union.

   The "array" can be gappy: there don't have to be elements at any
   particular index, and, being a finite thing, there is obviously a
   maximum index past which there are no elements at all. It is
   possible to update at an index past the current maximum index. It
   is also possible to delete values at an index.

   Should EVAL well. Big drawback is that there doesn't seem to be an
   efficient way (i.e., O(n)) to do an in index-order traversal of the
   elements. There is an O(n) fold function that gives you access to
   all the key-value pairs, but these will come out in an inconvenient
   order. If you iterate over the keys with an increment, you will get
   O(n log n) performance.

   The insert, delete and union operations all preserve a
   well-formedness condition ("wf") that ensures there is only one
   possible representation for any given finite-map.
*)

val _ = Datatype`spt = LN | LS 'a | BN spt spt | BS spt 'a spt`
(* Leaf-None, Leaf-Some, Branch-None, Branch-Some *)

val _ = overload_on ("isEmpty", ``\t. t = LN``)

val wf_def = Define`
  (wf LN <=> T) /\
  (wf (LS a) <=> T) /\
  (wf (BN t1 t2) <=> wf t1 /\ wf t2 /\ ~(isEmpty t1 /\ isEmpty t2)) /\
  (wf (BS t1 a t2) <=> wf t1 /\ wf t2 /\ ~(isEmpty t1 /\ isEmpty t2))
`

fun tzDefine s q = Lib.with_flag (computeLib.auto_import_definitions,false) (tDefine s q)
val lookup_def = tzDefine "lookup" `
  (lookup k LN = NONE) /\
  (lookup k (LS a) = if k = 0 then SOME a else NONE) /\
  (lookup k (BN t1 t2) =
     if k = 0 then NONE
     else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2)) /\
  (lookup k (BS t1 a t2) =
     if k = 0 then SOME a
     else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2))
` (WF_REL_TAC `measure FST` >> simp[DIV_LT_X])

val insert_def = tzDefine "insert" `
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
` (WF_REL_TAC `measure FST` >> simp[DIV_LT_X]);

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

val size_def = Define`
  (size LN = 0) /\
  (size (LS a) = 1) /\
  (size (BN t1 t2) = size t1 + size t2) /\
  (size (BS t1 a t2) = size t1 + size t2 + 1)
`;
val _ = export_rewrites ["size_def"]

val insert_notEmpty = store_thm(
  "insert_notEmpty",
  ``~isEmpty (insert k a t)``,
  Cases_on `t` >> rw[Once insert_def]);

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

val lookup_insert1 = store_thm(
  "lookup_insert1[simp]",
  ``!k a t. lookup k (insert k a t) = SOME a``,
  ho_match_mp_tac (theorem "insert_ind") >> rpt strip_tac >>
  simp[Once insert_def] >> rw[lookup_def]);

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

val isEmpty_union = store_thm(
  "isEmpty_union",
  ``isEmpty (union m1 m2) <=> isEmpty m1 /\ isEmpty m2``,
  map_every Cases_on [`m1`, `m2`] >> simp[union_def]);

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

val lookup_difference = store_thm(
  "lookup_difference",
  ``!m1 m2 k. lookup k (difference m1 m2) =
              if lookup k m2 = NONE then lookup k m1 else NONE``,
  Induct >> simp[lookup_def] >> Cases_on `m2` >>
  simp[lookup_def, difference_def, lookup_mk_BS, lookup_mk_BN] >>
  rw[optcase_lemma] >> REPEAT BasicProvers.CASE_TAC >>
  fs [lookup_def, lookup_mk_BS, lookup_mk_BN])

val lrnext_def = new_specification(
  "lrnext_def", ["lrnext"],
  numeralTheory.bit_initiality
      |> INST_TYPE [alpha |-> ``:num``]
      |> Q.SPECL [`1`, `\n r. 2 * r`,
                  `\n r. 2 * r`]
      |> SIMP_RULE bool_ss []);
val lrnext' = prove(
  ``(!a. lrnext 0 = 1) /\ (!n a. lrnext (NUMERAL n) = lrnext n)``,
  simp[NUMERAL_DEF, GSYM ALT_ZERO, lrnext_def])
val lrnext_thm = save_thm(
  "lrnext_thm",
  LIST_CONJ (CONJUNCTS lrnext' @ CONJUNCTS lrnext_def))
val _ = computeLib.add_persistent_funs ["lrnext_thm"]

val domain_def = zDefine`
  (domain LN = {}) /\
  (domain (LS _) = {0}) /\
  (domain (BN t1 t2) =
     IMAGE (\n. 2 * n + 2) (domain t1) UNION
     IMAGE (\n. 2 * n + 1) (domain t2)) /\
  (domain (BS t1 _ t2) =
     {0} UNION IMAGE (\n. 2 * n + 2) (domain t1) UNION
     IMAGE (\n. 2 * n + 1) (domain t2))
`;
val _ = export_rewrites ["domain_def"]

val FINITE_domain = store_thm(
  "FINITE_domain[simp]",
  ``FINITE (domain t)``,
  Induct_on `t` >> simp[]);

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
  qmatch_assum_rename_tac `n - i = SUC nn` [] >>
  `nn = n - (i + 1)` by decide_tac >> simp[]);

val bit_cases = prove(
  ``!n. (n = 0) \/ (?m. n = 2 * m + 1) \/ (?m. n = 2 * m + 2)``,
  Induct >> simp[] >> fs[]
  >- (disj1_tac >> qexists_tac `0` >> simp[])
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

val lookup_NONE_domain = store_thm(
  "lookup_NONE_domain",
  ``(lookup k t = NONE) <=> k NOTIN domain t``,
  simp[domain_lookup] >> Cases_on `lookup k t` >> simp[]);

val domain_union = store_thm(
  "domain_union",
  ``domain (union t1 t2) = domain t1 UNION domain t2``,
  simp[pred_setTheory.EXTENSION, domain_lookup, lookup_union] >>
  qx_gen_tac `k` >> Cases_on `lookup k t1` >> simp[]);

val domain_inter = store_thm(
  "domain_inter",
  ``domain (inter t1 t2) = domain t1 INTER domain t2``,
  simp[pred_setTheory.EXTENSION, domain_lookup, lookup_inter] >>
  rw [] >> Cases_on `lookup x t1` >> fs[] >>
  BasicProvers.CASE_TAC);

val domain_insert = store_thm(
  "domain_insert[simp]",
  ``domain (insert k v t) = k INSERT domain t``,
  simp[domain_lookup, pred_setTheory.EXTENSION, lookup_insert] >>
  metis_tac[]);

val domain_sing = save_thm(
  "domain_sing",
  domain_insert |> Q.INST [`t` |-> `LN`] |> SIMP_RULE bool_ss [domain_def]);

val domain_fromList = store_thm(
  "domain_fromList",
  ``domain (fromList l) = count (LENGTH l)``,
  simp[fromList_def] >>
  `!i t. domain (SND (FOLDL (\ (i,t) a. (i + 1, insert i a t)) (i,t) l)) =
         domain t UNION IMAGE ((+) i) (count (LENGTH l))`
    suffices_by (simp[] >> strip_tac >> simp[pred_setTheory.EXTENSION]) >>
  Induct_on `l` >> simp[pred_setTheory.EXTENSION, EQ_IMP_THM] >>
  rpt strip_tac >> simp[DECIDE ``(x = x + y) <=> (y = 0)``] >>
  qmatch_assum_rename_tac `nn < SUC (LENGTH l)` [] >>
  Cases_on `nn` >> fs[] >> metis_tac[ADD1]);

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
  >> `(k1 - 1) DIV 2 <> (k2 - 1) DIV 2`
        by simp[DIV2_EQ_DIV2, EVEN_PRE]
  >> fs [] >> CCONTR_TAC >> fs [] >> srw_tac [] []
  >> fs [EVEN_ODD] >> imp_res_tac ODD_IMP_NOT_ODD);

val domain_delete = store_thm(
  "domain_delete[simp]",
  ``domain (delete k t) = domain t DELETE k``,
  simp[pred_setTheory.EXTENSION, domain_lookup, lookup_delete] >>
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

val lrnext212 = prove(
  ``(lrnext (2 * m + 1) = 2 * lrnext m) /\
    (lrnext (2 * m + 2) = 2 * lrnext m)``,
  conj_tac >| [
    `2 * m + 1 = BIT1 m` suffices_by simp[lrnext_thm] >>
    simp_tac bool_ss [BIT1, TWO, ONE, MULT_CLAUSES, ADD_CLAUSES],
    `2 * m + 2 = BIT2 m` suffices_by simp[lrnext_thm] >>
    simp_tac bool_ss [BIT2, TWO, ONE, MULT_CLAUSES, ADD_CLAUSES]
  ]);

val bit_induction = prove(
  ``!P. P 0 /\ (!n. P n ==> P (2 * n + 1)) /\
        (!n. P n ==> P (2 * n + 2)) ==>
        !n. P n``,
  gen_tac >> strip_tac >> completeInduct_on `n` >> simp[] >>
  qspec_then `n` strip_assume_tac bit_cases >> simp[]);

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

val set_foldi_keys = store_thm(
  "set_foldi_keys",
  ``!t a i. foldi (\k v a. k INSERT a) i a t =
            a UNION IMAGE (\n. i + lrnext i * n) (domain t)``,
  Induct_on `t` >> simp[foldi_def, GSYM pred_setTheory.IMAGE_COMPOSE,
                        combinTheory.o_ABS_R]
  >- simp[Once pred_setTheory.INSERT_SING_UNION, pred_setTheory.UNION_COMM]
  >- (simp[pred_setTheory.EXTENSION] >> rpt gen_tac >>
      Cases_on `x IN a` >> simp[lrlemma1, lrlemma2, LEFT_ADD_DISTRIB]) >>
  simp[pred_setTheory.EXTENSION] >> rpt gen_tac >>
  Cases_on `x IN a'` >> simp[lrlemma1, lrlemma2, LEFT_ADD_DISTRIB])

val domain_foldi = save_thm(
  "domain_foldi",
  set_foldi_keys |> SPEC_ALL |> Q.INST [`i` |-> `0`, `a` |-> `{}`]
                 |> SIMP_RULE (srw_ss()) [lrnext_thm]
                 |> SYM);
val _ = computeLib.add_persistent_funs ["domain_foldi"]

val toAList_def = Define `
  toAList = foldi (\k v a. (k,v)::a) 0 []`

val set_toAList_lemma = prove(
  ``!t a i. set (foldi (\k v a. (k,v) :: a) i a t) =
            set a UNION IMAGE (\n. (i + lrnext i * n,
                    THE (lookup n t))) (domain t)``,
  Induct_on `t`
  \\ fs [foldi_def,GSYM pred_setTheory.IMAGE_COMPOSE,lookup_def]
  THEN1 fs [Once pred_setTheory.INSERT_SING_UNION, pred_setTheory.UNION_COMM]
  THEN1 (simp[pred_setTheory.EXTENSION] \\ rpt gen_tac \\
         Cases_on `MEM x a` \\ simp[lrlemma1, lrlemma2, LEFT_ADD_DISTRIB]
         \\ fs [MULT2_DIV',EVEN_ADD,EVEN_DOUBLE])
  \\ simp[pred_setTheory.EXTENSION] \\ rpt gen_tac
  \\ Cases_on `MEM x a'` \\ simp[lrlemma1, lrlemma2, LEFT_ADD_DISTRIB]
  \\ fs [MULT2_DIV',EVEN_ADD,EVEN_DOUBLE])
  |> Q.SPECL [`t`,`[]`,`0`] |> GEN_ALL
  |> SIMP_RULE (srw_ss()) [GSYM toAList_def,lrnext_thm,MEM,LIST_TO_SET,
       pred_setTheory.UNION_EMPTY,pred_setTheory.EXTENSION,
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

val _ = remove_ovl_mapping "lrnext" {Name = "lrnext", Thy = "sptree"}

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
  rw[] >> fs[] >>
  fs[Once toListA_append] >>
  simp[Once toListA_append,SimpR``$++``])

val toList_def = Define`toList m = toListA [] m`

val isEmpty_toList = store_thm("isEmpty_toList",
  ``!t. wf t ==> ((t = LN) <=> (toList t = []))``,
  rw[toList_def,isEmpty_toListA])

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
  simp[])

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
  simp[])

val spt_eq_thm = store_thm("spt_eq_thm",
  ``!t1 t2. wf t1 /\ wf t2 ==>
    ((t1 = t2) <=> !n. lookup n t1 = lookup n t2)``,
  Induct >> simp[wf_def,lookup_def]
  >- (
    rw[EQ_IMP_THM] >> rw[lookup_def] >>
    `domain t2 = {}` by (
      simp[pred_setTheory.EXTENSION] >>
      metis_tac[lookup_NONE_domain] ) >>
    Cases_on`t2`>>fs[domain_def,wf_def] >>
    metis_tac[domain_empty] )
  >- (
    rw[EQ_IMP_THM] >> rw[lookup_def] >>
    Cases_on`t2`>>fs[lookup_def]
    >- (first_x_assum(qspec_then`0`mp_tac)>>simp[])
    >- (first_x_assum(qspec_then`0`mp_tac)>>simp[]) >>
    fs[wf_def] >>
    rfs[domain_empty] >>
    fs[GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
    fs[domain_lookup] >|
      [ qspec_then`x`strip_assume_tac div2_even_lemma
      , qspec_then`x`strip_assume_tac div2_odd_lemma
      ] >>
    first_x_assum(qspec_then`n`mp_tac) >>
    fs[ODD_EVEN] >> simp[] )
  >- (
    rw[EQ_IMP_THM] >> rw[lookup_def] >>
    rfs[domain_empty] >>
    fs[GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
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
    qmatch_assum_rename_tac`wf (BN s1 s2)`[] >>
    `wf s1 /\ wf s2` by fs[wf_def] >>
    first_x_assum(qspec_then`s2`mp_tac) >>
    first_x_assum(qspec_then`s1`mp_tac) >>
    simp[] >> ntac 2 strip_tac >>
    fs[lookup_def] >> rw[] >>
    metis_tac[prim_recTheory.LESS_REFL,div2_even_lemma,div2_odd_lemma
             ,EVEN_ODD] )
  >- (
    rw[EQ_IMP_THM] >> rw[lookup_def] >>
    rfs[domain_empty] >>
    fs[GSYM pred_setTheory.MEMBER_NOT_EMPTY] >>
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
    qmatch_assum_rename_tac`wf (BS s1 z s2)`[] >>
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

val wf_mk_wf = store_thm("wf_mk_wf[simp]",
  ``!t. wf (mk_wf t)``,
  Induct \\ fs [wf_def,mk_wf_def,wf_mk_BS,wf_mk_BN]);

val wf_mk_id = store_thm("wf_mk_id[simp]",
  ``!t. wf t ==> (mk_wf t = t)``,
  Induct \\ srw_tac [] [wf_def,mk_wf_def,mk_BS_thm,mk_BN_thm]);

val lookup_mk_wf = store_thm("lookup_mk_wf[simp]",
  ``!x t. lookup x (mk_wf t) = lookup x t``,
  Induct_on `t` \\ fs [mk_wf_def,lookup_mk_BS,lookup_mk_BN]
  \\ srw_tac [] [lookup_def]);

val domain_mk_wf = store_thm("domain_mk_wf[simp]",
  ``!t. domain (mk_wf t) = domain t``,
  fs [pred_setTheory.EXTENSION,domain_lookup]);

val mk_wf_eq = store_thm("mk_wf_eq[simp]",
  ``!t1 t2. (mk_wf t1 = mk_wf t2) <=> !x. lookup x t1 = lookup x t2``,
  metis_tac [spt_eq_thm,wf_mk_wf,lookup_mk_wf]);

val inter_eq = store_thm("inter_eq[simp]",
  ``!t1 t2 t3 t4.
       (inter t1 t2 = inter t3 t4) <=>
       !x. lookup x (inter t1 t2) = lookup x (inter t3 t4)``,
  metis_tac [spt_eq_thm,wf_inter]);

val union_mk_wf = store_thm("union_mk_wf[simp]",
  ``!t1 t2. union (mk_wf t1) (mk_wf t2) = mk_wf (union t1 t2)``,
  REPEAT STRIP_TAC
  \\ `union (mk_wf t1) (mk_wf t2) = mk_wf (union (mk_wf t1) (mk_wf t2))` by
        metis_tac [wf_union,wf_mk_wf,wf_mk_id]
  \\ POP_ASSUM (fn th => once_rewrite_tac [th])
  \\ ASM_SIMP_TAC std_ss [mk_wf_eq] \\ fs [lookup_union]);

val inter_mk_wf = store_thm("union_mk_wf[simp]",
  ``!t1 t2. inter (mk_wf t1) (mk_wf t2) = mk_wf (inter t1 t2)``,
  REPEAT STRIP_TAC
  \\ `inter (mk_wf t1) (mk_wf t2) = mk_wf (inter (mk_wf t1) (mk_wf t2))` by
        metis_tac [wf_inter,wf_mk_wf,wf_mk_id]
  \\ POP_ASSUM (fn th => once_rewrite_tac [th])
  \\ ASM_SIMP_TAC std_ss [mk_wf_eq] \\ fs [lookup_inter]);

val insert_mk_wf = store_thm("insert_mk_wf[simp]",
  ``!x v t. insert x v (mk_wf t) = mk_wf (insert x v t)``,
  REPEAT STRIP_TAC
  \\ `insert x v (mk_wf t) = mk_wf (insert x v (mk_wf t))` by
        metis_tac [wf_insert,wf_mk_wf,wf_mk_id]
  \\ POP_ASSUM (fn th => once_rewrite_tac [th])
  \\ ASM_SIMP_TAC std_ss [mk_wf_eq] \\ fs [lookup_insert]);

val delete_mk_wf = store_thm("delete_mk_wf[simp]",
  ``!x t. delete x (mk_wf t) = mk_wf (delete x t)``,
  REPEAT STRIP_TAC
  \\ `delete x (mk_wf t) = mk_wf (delete x (mk_wf t))` by
        metis_tac [wf_delete,wf_mk_wf,wf_mk_id]
  \\ POP_ASSUM (fn th => once_rewrite_tac [th])
  \\ ASM_SIMP_TAC std_ss [mk_wf_eq] \\ fs [lookup_delete]);

val union_LN = store_thm("union_LN[simp]",
  ``!t. (union t LN = t) /\ (union LN t = t)``,
  Cases \\ fs [union_def]);

val inter_LN = store_thm("inter_LN[simp]",
  ``!t. (inter t LN = LN) /\ (inter LN t = LN)``,
  Cases \\ fs [inter_def]);

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

val fromAList_def = Define `
  (fromAList [] = LN) /\
  (fromAList ((x,y)::xs) = insert x y (fromAList xs))`;

val lookup_fromAList = store_thm("lookup_fromAList",
  ``!ls x.lookup x (fromAList ls) = ALOOKUP ls x``,
  ho_match_mp_tac (fetch "-" "fromAList_ind")>>
  rw[fromAList_def,lookup_def]>>
  fs[lookup_insert]>> simp[EQ_SYM_EQ])

val domain_fromAList = store_thm("domain_fromAList",
  ``!ls. domain (fromAList ls) = set (MAP FST ls)``,
  simp[pred_setTheory.EXTENSION,domain_lookup,lookup_fromAList,
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

val _ = export_theory();
