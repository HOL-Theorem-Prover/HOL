open HolKernel Parse boolLib bossLib;
open lcsymtacs

val _ = new_theory "sptree";


val _ = Datatype`pspt = pLN | pLS 'a | pBN pspt pspt | pBS pspt 'a pspt`
val pisEmpty_def = Define`
  (pisEmpty pLN <=> T) /\
  (pisEmpty _ <=> F)
`;

val wf_def = Define`
  (wf pLN <=> T) /\
  (wf (pLS a) <=> T) /\
  (wf (pBN t1 t2) <=> wf t1 /\ wf t2 /\ ~(pisEmpty t1 /\ pisEmpty t2)) /\
  (wf (pBS t1 a t2) <=> wf t1 /\ wf t2 /\ ~(pisEmpty t1 /\ pisEmpty t2))
`

val plookup_def = zDefine`
  (plookup n pLN = NONE) /\
  (plookup n (pLS a) = if n = 0 then SOME a else NONE) /\
  (plookup n (pBN t1 t2) =
     if n = 0 then NONE
     else plookup (n DIV 2) (if EVEN n then t1 else t2)) /\
  (plookup n (pBS t1 a t2) =
     if n = 0 then SOME a
     else plookup (n DIV 2) (if EVEN n then t1 else t2))
`;

val pinsert_def = zDefine`
  (pinsert k a pLN = if k = 0 then pLS a
                     else if EVEN k then pBN (pinsert (k DIV 2) a pLN) pLN
                     else pBN pLN (pinsert (k DIV 2) a pLN)) /\
  (pinsert k a (pLS a') =
     if k = 0 then pLS a
     else if EVEN k then pBS (pinsert (k DIV 2) a pLN) a' pLN
     else pBS pLN a' (pinsert (k DIV 2) a pLN)) /\
  (pinsert k a (pBN t1 t2) =
     if k = 0 then pBS t1 a t2
     else if EVEN k then pBN (pinsert (k DIV 2) a t1) t2
     else pBN t1 (pinsert (k DIV 2) a t2)) /\
  (pinsert k a (pBS t1 a' t2) =
     if k = 0 then pBS t1 a t2
     else if EVEN k then pBS (pinsert (k DIV 2) a t1) a' t2
     else pBS t1 a' (pinsert (k DIV 2) a t2))
`;

val pdelete_def = zDefine`
  (pdelete k pLN = pLN) /\
  (pdelete k (pLS a) = if k = 0 then pLN else pLS a) /\
  (pdelete k (pBN t1 t2) =
     if k = 0 then pBN t1 t2
     else if EVEN k then
       let t1' = pdelete (k DIV 2) t1
       in
         if pisEmpty t1' /\ pisEmpty t2 then pLN
         else pBN t1' t2
     else
       let t2' = pdelete (k DIV 2) t2
       in
         if pisEmpty t1 /\ pisEmpty t2' then pLN
         else pBN t1 t2') /\
  (pdelete k (pBS t1 a t2) =
     if k = 0 then pBN t1 t2
     else if EVEN k then
       let t1' = pdelete (k DIV 2) t1
       in
         if pisEmpty t1' /\ pisEmpty t2 then pLS a
         else pBS t1' a t2
     else
       let t2' = pdelete (k DIV 2) t2
       in
         if pisEmpty t1 /\ pisEmpty t2' then pLS a
         else pBS t1 a t2')
`;

val psize_def = Define`
  (psize pLN = 0) /\
  (psize (pLS a) = 1) /\
  (psize (pBN t1 t2) = psize t1 + psize t2) /\
  (psize (pBS t1 a t2) = psize t1 + psize t2 + 1)
`;

val wfEQ_def = Define`
  wfEQ t1 t2 <=> (t1 = t2) /\ wf t1
`;

val wfEQ_equiv = prove(
  ``(?t:'a pspt. wfEQ t t) /\
    (!x y:'a pspt. wfEQ x y <=> wfEQ x x /\ wfEQ y y /\ (wfEQ x = wfEQ y))``,
  simp[wfEQ_def, FUN_EQ_THM] >> conj_tac >-
    (qexists_tac `pLN` >> simp[wf_def]) >>
  metis_tac[]);

val pinsert_notEmpty = prove(
  ``~pisEmpty (pinsert k a t)``,
  Cases_on `t` >> rw[Once pinsert_def, pisEmpty_def]);

val wf_pisEmpty = prove(
  ``wfEQ t1 t2 ==> (pisEmpty t1 <=> pisEmpty t2)``,
  simp[wfEQ_def]);

val wf_insert = prove(
  ``!t1 t2. wfEQ t1 t2 ==> wfEQ (pinsert k a t1) (pinsert k a t2)``,
  simp[wfEQ_def] >> map_every qid_spec_tac [`a`, `k`] >>
  ho_match_mp_tac (theorem "pinsert_ind") >>
  rpt strip_tac >>
  simp[Once pinsert_def] >> rw[wf_def, pinsert_notEmpty] >> fs[wf_def]);

val wf_delete = prove(
  ``!t1 t2 k. wfEQ t1 t2 ==> wfEQ (pdelete k t1) (pdelete k t2)``,
  simp[wfEQ_def] >> Induct >> rw[wf_def, pdelete_def] >>
  rw[wf_def] >> rw[] >> fs[] >> metis_tac[]);

val wf_plookup = prove(
  ``wfEQ t1 t2 ==> (k1 = k2) ⇒ (plookup k1 t1 = plookup k2 t2)``,
  simp[wfEQ_def]);

val lookup_insert1 = prove(
  ``!k a t. plookup k (pinsert k a t) = SOME a``,
  ho_match_mp_tac (theorem "pinsert_ind") >> rpt strip_tac >>
  simp[Once pinsert_def] >> rw[plookup_def]);

val punion_def = Define`
  (punion pLN t = t) /\
  (punion (pLS a) t =
     case t of
       | pLN => pLS a
       | pLS b => pLS a
       | pBN t1 t2 => pBS t1 a t2
       | pBS t1 _ t2 => pBS t1 a t2) /\
  (punion (pBN t1 t2) t =
     case t of
       | pLN => pBN t1 t2
       | pLS a => pBS t1 a t2
       | pBN t1' t2' => pBN (punion t1 t1') (punion t2 t2')
       | pBS t1' a t2' => pBS (punion t1 t1') a (punion t2 t2')) /\
  (punion (pBS t1 a t2) t =
     case t of
       | pLN => pBS t1 a t2
       | pLS a' => pBS t1 a t2
       | pBN t1' t2' => pBS (punion t1 t1') a (punion t2 t2')
       | pBS t1' a' t2' => pBS (punion t1 t1') a (punion t2 t2'))
`;

val numeral_div0 = prove(
  ``(BIT1 n DIV 2 = n) /\
    (BIT2 n DIV 2 = SUC n) /\
    (SUC (BIT1 n) DIV 2 = SUC n) /\
    (SUC (BIT2 n) DIV 2 = SUC n)``,
  REWRITE_TAC[GSYM arithmeticTheory.DIV2_def, numeralTheory.numeral_suc,
              REWRITE_RULE [arithmeticTheory.NUMERAL_DEF]
                           numeralTheory.numeral_div2])
val BIT0 = prove(
  ``BIT1 n <> 0  /\ BIT2 n <> 0``,
  REWRITE_TAC[arithmeticTheory.BIT1, arithmeticTheory.BIT2,
              arithmeticTheory.ADD_CLAUSES, numTheory.NOT_SUC]);

fun computerule rwts th q =
    th
      |> CONJUNCTS
      |> map SPEC_ALL
      |> map (Q.INST [`k` |-> q])
      |> map (CONV_RULE
                (RAND_CONV (SIMP_CONV bool_ss
                                      ([numeral_div0, BIT0,
                                       numTheory.NOT_SUC,
                                       EVAL ``SUC 0 DIV 2``,
                                       numeralTheory.numeral_evenodd,
                                       arithmeticTheory.EVEN] @ rwts))))

val pinsert_compute = save_thm(
  "pinsert_compute",
  let val zeroes = computerule [] pinsert_def `0`
  in
    LIST_CONJ (zeroes @
               computerule [] pinsert_def `BIT1 n` @
               computerule [] pinsert_def `BIT2 n` @
               computerule zeroes pinsert_def `SUC 0` @
               computerule [] pinsert_def `SUC (BIT1 n)` @
               computerule [] pinsert_def `SUC (BIT2 n)`)
  end)

val pdelete_compute = save_thm(
  "pdelete_compute",
  let val zeroes = computerule [] pdelete_def `0`
  in
    LIST_CONJ (zeroes @
             computerule [] pdelete_def `BIT1 n` @
             computerule [] pdelete_def `BIT2 n` @
             computerule zeroes pdelete_def `SUC 0` @
             computerule [] pdelete_def `SUC (BIT1 n)` @
             computerule [] pdelete_def `SUC (BIT2 n)`)
  end);

val _ = export_theory();
