open HolKernel Parse boolLib bossLib;
open lcsymtacs
open arithmeticTheory
open logrootTheory

val _ = new_theory "sptree";

(* A log-time random-access, extensible array implementation with union.

   The "array" can be gappy: there don't have to be elements at any
   particular index, and, being a finite thing, there is obviously a
   maximum index past which there are no elements at all. It is
   possible to update at an index past the current maximum index. It
   is also possible to delete values at an index.

   Should EVAL well. Big drawback is that there doesn't seem to be an
   efficient way to do an in index-order traversal of the elements.
   There is a fold function that gives you access to all the key-value
   pairs, but these will come out in an inconvenient order.

   The insert, delete and union operations all preserve a
   well-formedness condition ("wf") that ensures there is only one
   possible representation for any given finite-map.
*)

val _ = Datatype`spt = LN | LS 'a | BN spt spt | BS spt 'a spt`
(* Leaf-None, Leaf-Some, Branch-None, Branch-Some *)
val isEmpty_def = Define`
  (isEmpty LN <=> T) /\
  (isEmpty _ <=> F)
`;

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

val delete_def = zDefine`
  (delete k LN = LN) /\
  (delete k (LS a) = if k = 0 then LN else LS a) /\
  (delete k (BN t1 t2) =
     if k = 0 then BN t1 t2
     else if EVEN k then
       let t1' = delete ((k - 1) DIV 2) t1
       in
         if isEmpty t1' /\ isEmpty t2 then LN
         else BN t1' t2
     else
       let t2' = delete ((k - 1) DIV 2) t2
       in
         if isEmpty t1 /\ isEmpty t2' then LN
         else BN t1 t2') /\
  (delete k (BS t1 a t2) =
     if k = 0 then BN t1 t2
     else if EVEN k then
       let t1' = delete ((k - 1) DIV 2) t1
       in
         if isEmpty t1' /\ isEmpty t2 then LS a
         else BS t1' a t2
     else
       let t2' = delete ((k - 1) DIV 2) t2
       in
         if isEmpty t1 /\ isEmpty t2' then LS a
         else BS t1 a t2')
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

val insert_notEmpty = store_thm(
  "insert_notEmpty",
  ``~isEmpty (insert k a t)``,
  Cases_on `t` >> rw[Once insert_def, isEmpty_def]);

val wf_insert = store_thm(
  "wf_insert",
  ``!k a t. wf t ==> wf (insert k a t)``,
  ho_match_mp_tac (theorem "insert_ind") >>
  rpt strip_tac >>
  simp[Once insert_def] >> rw[wf_def, insert_notEmpty] >> fs[wf_def]);

val wf_delete = store_thm(
  "wf_delete",
  ``!t k. wf t ==> wf (delete k t)``,
  Induct >> rw[wf_def, delete_def] >>
  rw[wf_def] >> rw[] >> fs[] >> metis_tac[]);

val lookup_insert1 = store_thm(
  "lookup_insert1",
  ``!k a t. lookup k (insert k a t) = SOME a``,
  ho_match_mp_tac (theorem "insert_ind") >> rpt strip_tac >>
  simp[Once insert_def] >> rw[lookup_def]);

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
  map_every Cases_on [`m1`, `m2`] >> simp[union_def, isEmpty_def]);

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

val domain_def = Define`
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
  "FINITE_domain",
  ``FINITE (domain t)``,
  Induct_on `t` >> simp[]);
val _ = export_rewrites ["FINITE_domain"]

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

(*
val lookup_delete = store_thm(
  "lookup_delete",
  ``!t k1 k2.
      lookup k1 (delete k2 t) = if k1 = k2 then NONE
                                else lookup k1 t``,
  Induct >> simp[delete_def, lookup_def]
  >- rw[lookup_def]
  >- (map_every qx_gen_tac [`k1`, `k2`] >>
      rw[lookup_def]
*)

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

val insert_union = store_thm("insert_union",
  ``∀k v s. insert k v s = union (insert k v LN) s``,
  completeInduct_on`k` >> simp[Once insert_def] >> rw[] >>
  simp[Once union_def] >>
  Cases_on`s`>>simp[Once insert_def] >>
  simp[Once union_def] >>
  first_x_assum match_mp_tac >>
  simp[arithmeticTheory.DIV_LT_X])

val domain_sing = store_thm("domain_sing",
  ``∀k v. domain (insert k v LN) = {k}``,
  completeInduct_on`k` >>
  simp[Once insert_def] >> rw[] >>
  `(k - 1) DIV 2 < k` by (
    fsrw_tac[ARITH_ss][DIV_LT_X] ) >> fs[] >>
  ONCE_REWRITE_TAC[MULT_COMM] >>
  `0 < 2` by simp[] >>
  qmatch_abbrev_tac`a + b = k` >>
  (qsuff_tac`a + (b-1) + 1 = k` >- simp[Abbr`b`]) >>
  `(k - 1) MOD 2 = b - 1` by (
    simp[MOD_2] >>
    Cases_on`k`>>fs[EVEN,Abbr`b`] ) >>
  pop_assum(SUBST1_TAC o SYM) >>
  unabbrev_all_tac >>
  (DIVISION |> Q.SPEC`2` |> UNDISCH |> Q.SPEC`k-1` |> CONJUNCT1 |> SYM |> SUBST1_TAC) >>
  simp[])

val domain_insert = store_thm("domain_insert",
  ``∀k v t. domain (insert k v t) = k INSERT domain t``,
  rw[Once pred_setTheory.EXTENSION] >>
  rw[domain_lookup] >>
  Cases_on`x = k` >> rw[lookup_insert1] >>
  rw[Once insert_union] >>
  rw[lookup_union] >>
  BasicProvers.CASE_TAC >>
  `x ∈ domain (insert k v LN)` by metis_tac[domain_lookup] >>
  fs[domain_sing])

val _ = remove_ovl_mapping "lrnext" {Name = "lrnext", Thy = "sptree"}

val toListA_def = Define`
  (toListA acc LN = acc) /\
  (toListA acc (LS a) = a::acc) /\
  (toListA acc (BN t1 t2) = toListA (toListA acc t2) t1) /\
  (toListA acc (BS t1 a t2) = toListA (a :: toListA acc t2) t1)
`;
val toList_def = Define`toList m = toListA [] m`

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

val _ = export_theory();
