open HolKernel boolLib bossLib BasicProvers;
open pred_setTheory arithmeticTheory listTheory rich_listTheory optionTheory
     pairTheory relationTheory sortingTheory;
open permLib;
open lcsymtacs;

val _ = new_theory "mergesort";

val _ = temp_tight_equality ();

val every_case_tac = BasicProvers.EVERY_CASE_TAC;

val last_reverse = Q.prove (
`!l. l <> [] ==> LAST (REVERSE l) = HD l`,
 Induct_on `l` >>
 rw []);

val mem_sorted_append = Q.prove (
`!R l1 l2 x y.
  transitive R /\
  SORTED R (l1 ++ l2) /\
  MEM x l1 /\
  MEM y l2
  ==>
  R x y`,
 Induct_on `l1` >>
 rw [] >>
 REV_FULL_SIMP_TAC (srw_ss()) [SORTED_EQ] >>
 metis_tac []);

val stable_def = Define `
stable R l1 l2 =
  !p. (!x y. p x /\ p y ==> R x y) ==> FILTER p l1 = FILTER p l2`;

val sort2_def = Define `
sort2 R x y =
  if R x y then
    [x;y]
  else
    [y;x]`;

val sort3_def = Define `
sort3 R x y z =
  if R x y then
    if R y z then
      [x;y;z]
    else if R x z then
      [x;z;y]
    else
      [z;x;y]
  else if R y z then
    if R x z then
      [y;x;z]
    else
      [y;z;x]
  else
    [z;y;x]`;

val merge_def = Define `
(merge R [] [] = []) /\
(merge R l [] = l) /\
(merge R [] l = l) /\
(merge R (x::l1) (y::l2) =
  if R x y then
    x::merge R l1 (y::l2)
  else
    y::merge R (x::l1) l2)`;

val merge_ind = fetch "-" "merge_ind";

val mergesortN_def = tDefine "mergesortN" `
(mergesortN R 0 l = []) /\
(mergesortN R 1 (x::l) = [x]) /\
(mergesortN R 1 [] = []) /\
(mergesortN R 2 (x::y::l) = sort2 R x y) /\
(mergesortN R 2 [x] = [x]) /\
(mergesortN R 2 [] = []) /\
(mergesortN R 3 (x::y::z::l) = sort3 R x y z) /\
(mergesortN R 3 [x;y] = sort2 R x y) /\
(mergesortN R 3 [x] = [x]) /\
(mergesortN R 3 [] = []) /\
(mergesortN R n l =
  let len1 = DIV2 n in
    merge R (mergesortN R (DIV2 n) l) (mergesortN R (n - len1) (DROP len1 l)))`
 (WF_REL_TAC `measure (\(R,n,l). n)` >>
  rw [DIV2_def, X_LT_DIV]
  >- (match_mp_tac DIV_LESS >>
      decide_tac) >>
  decide_tac);

val mergesortN_ind = fetch "-" "mergesortN_ind";

val mergesort_def = Define `
mergesort R l = mergesortN R (LENGTH l) l`;

(* A mergesort using tail recursive merging. This is what OCaml's standard
 * library does, but instead of parameterizing with negate, it just copies the
 * code for merge_rev sort. *)

val sort2_tail_def = Define `
sort2_tail (neg:bool) R x y =
  if R x y <> neg then
    [x;y]
  else
    [y;x]`;

val sort3_tail_def = Define `
sort3_tail (neg:bool) R x y z =
  if R x y <> neg then
    if R y z <> neg then
      [x;y;z]
    else if R x z <> neg then
      [x;z;y]
    else
      [z;x;y]
  else if R y z <> neg then
    if R x z <> neg then
      [y;x;z]
    else
      [y;z;x]
  else
    [z;y;x]`;

val merge_tail_def = Define `
(merge_tail (negate:bool) R [] [] acc = acc) /\
(merge_tail negate R l [] acc = REV l acc) /\
(merge_tail negate R [] l acc = REV l acc) /\
(merge_tail negate R (x::l1) (y::l2) acc =
  if R x y <> negate then
    merge_tail negate R l1 (y::l2) (x::acc)
  else
    merge_tail negate R (x::l1) l2 (y::acc))`;

val merge_tail_ind = fetch "-" "merge_tail_ind";

val mergesortN_tail_def = tDefine "mergesortN_tail" `
(mergesortN_tail (negate :bool) R 0 l = []) /\
(mergesortN_tail negate R 1 (x::l) = [x]) /\
(mergesortN_tail negate R 1 [] = []) /\
(mergesortN_tail negate R 2 (x::y::l) = sort2_tail negate R x y) /\
(mergesortN_tail negate R 2 [x] = [x]) /\
(mergesortN_tail negate R 2 [] = []) /\
(mergesortN_tail negate R 3 (x::y::z::l) = sort3_tail negate R x y z) /\
(mergesortN_tail negate R 3 [x;y] = sort2_tail negate R x y) /\
(mergesortN_tail negate R 3 [x] = [x]) /\
(mergesortN_tail negate R 3 [] = []) /\
(mergesortN_tail negate R n l =
  let len1 = DIV2 n in
  let neg = ~negate in
    merge_tail neg R (mergesortN_tail neg R (DIV2 n) l)
                     (mergesortN_tail neg R (n - len1) (DROP len1 l))
                     [])`
 (WF_REL_TAC `measure (\(neg,R,n,l). n)` >>
  rw [DIV2_def] >>
  rw [DIV2_def, X_LT_DIV]
  >- (match_mp_tac DIV_LESS >>
      decide_tac) >>
  decide_tac);

val mergesortN_tail_ind = fetch "-" "mergesortN_tail_ind";

val mergesort_tail_def = Define `
mergesort_tail R l = mergesortN_tail F R (LENGTH l) l`;


(* ------------------------- proofs ----------------------- *)

(* mergesort permutes its input *)

val sort2_perm = Q.store_thm ("sort2_perm",
`!R x y. PERM [x;y] (sort2 R x y)`,
 srw_tac [PERM_ss] [sort2_def]);

val sort3_perm = Q.store_thm ("sort3_perm",
`!R x y z. PERM [x;y;z] (sort3 R x y z)`,
 srw_tac [PERM_ss] [sort3_def]);

val merge_perm = Q.store_thm ("merge_perm",
`!R l1 l2. PERM (l1++l2) (merge R l1 l2)`,
 ho_match_mp_tac merge_ind >>
 rw [merge_def] >>
 full_simp_tac (srw_ss()++PERM_ss) []);

val mergesortN_perm = Q.store_thm ("mergesortN_perm",
`!R n l. PERM (TAKE n l) (mergesortN R n l)`,
 ho_match_mp_tac mergesortN_ind >>
 rw [] >>
 ONCE_REWRITE_TAC [mergesortN_def] >>
 rw [sort2_perm, sort3_perm]
 >- (every_case_tac >>
     fs [])
 >- (every_case_tac >>
     fs [sort2_perm] >>
     metis_tac [])
 >- (every_case_tac >>
     fs [sort2_perm, sort3_perm] >>
     metis_tac []) >>
 `len1 <= n`
             by (UNABBREV_ALL_TAC >>
                 fs [DIV2_def, DIV_LESS_EQ]) >>
 metis_tac [take_drop_partition, PERM_TRANS, PERM_CONG, merge_perm]);

val mergesort_perm = Q.store_thm ("mergesort_perm",
`!R l. PERM l (mergesort R l)`,
 rw [mergesort_def] >>
 metis_tac [TAKE_LENGTH_ID, mergesortN_perm]);

(* mergesort's output is sorted *)

val sort2_sorted = Q.store_thm ("sort2_sorted",
`!R x y.
  total R
  ==>
  SORTED R (sort2 R x y)`,
 rw [sort2_def, SORTED_DEF, total_def] >>
 metis_tac []);

val sort3_sorted = Q.store_thm ("sort3_sorted",
`!R x y z.
  total R
  ==>
  SORTED R (sort3 R x y z)`,
 rw [sort3_def, SORTED_DEF, total_def] >>
 metis_tac []);

val merge_sorted = Q.store_thm ("merge_sorted",
`!R l1 l2.
  transitive R /\ total R /\ SORTED R l1 /\ SORTED R l2
  ==>
  SORTED R (merge R l1 l2)`,
 ho_match_mp_tac merge_ind >>
 rw [merge_def] >>
 REV_FULL_SIMP_TAC (srw_ss()) [SORTED_EQ] >>
 rw [] >>
 fs [transitive_def, total_def]
 >- (`PERM (l1++(y::l2)) (merge R l1 (y::l2))` by metis_tac [merge_perm] >>
     imp_res_tac MEM_PERM >>
     fs [] >>
     metis_tac [])
 >- (`PERM ((x::l1)++l2) (merge R (x::l1) l2)` by metis_tac [merge_perm] >>
     imp_res_tac MEM_PERM >>
     fs [] >>
     metis_tac []));

val mergesortN_sorted = Q.store_thm ("mergesortN_sorted",
`!R n l.
  total R /\ transitive R
  ==>
  SORTED R (mergesortN R n l)`,
 ho_match_mp_tac mergesortN_ind >>
 rw [] >>
 ONCE_REWRITE_TAC [mergesortN_def] >>
 rw [SORTED_EQ, SORTED_DEF, sort2_sorted, sort3_sorted]
 >- (Cases_on `l` >>
     rw [])
 >- (Cases_on `l` >>
     rw [] >>
     Cases_on `t` >>
     rw [sort2_sorted])
 >- (Cases_on `l` >>
     rw [] >>
     Cases_on `t` >>
     rw [sort2_sorted] >>
     Cases_on `t'` >>
     rw [sort2_sorted, sort3_sorted])
 >- metis_tac [merge_sorted]);

val mergesort_sorted = Q.store_thm ("mergesort_sorted",
`!R l. transitive R /\ total R ==> SORTED R (mergesort R l)`,
 metis_tac [mergesort_def, mergesortN_sorted]);

(* mergesort is stable *)

val stable_cong = Q.store_thm ("stable_cong",
`!R l1 l2 l3 l4.
  stable R l1 l2 /\ stable R l3 l4
  ==>
  stable R (l1++l3) (l2++l4)`,
 rw [stable_def, FILTER_APPEND]);

val stable_trans = Q.store_thm ("stable_trans",
`!R l1 l2 l3.
  stable R l1 l2 /\ stable R l2 l3
  ==>
  stable R l1 l3`,
 rw [stable_def]);

val sort2_stable = Q.store_thm ("sort2_stable",
`!R x y. stable R [x;y] (sort2 R x y)`,
 rw [stable_def, sort2_def] >>
 every_case_tac >>
 rw [] >>
 metis_tac []);

val sort3_stable = Q.store_thm ("sort3_stable",
`!R x y z.
  total R /\ transitive R
  ==>
  stable R [x;y;z] (sort3 R x y z)`,
 rw [sort3_def, stable_def] >>
 every_case_tac >>
 rw [] >>
 metis_tac [total_def, transitive_def]);

val filter_merge = Q.store_thm ("filter_merge",
`!P R l1 l2.
  transitive R /\
  (!x y. P x /\ P y ==> R x y) /\
  SORTED R l1
  ==>
  FILTER P (merge R l1 l2) = FILTER P (l1 ++ l2)`,
 gen_tac >>
 ho_match_mp_tac merge_ind >>
 rw [merge_def, SORTED_EQ] >>
 rw [merge_def, FILTER_APPEND] >>
 REV_FULL_SIMP_TAC (srw_ss()) [SORTED_EQ, FILTER_APPEND]
 >- metis_tac []
 >- metis_tac []
 >- (`FILTER P l1 = []`
           by (rw [FILTER_EQ_NIL] >>
               CCONTR_TAC >>
               fs [EXISTS_MEM] >>
               metis_tac [transitive_def]) >>
     rw []));

val merge_stable = Q.store_thm ("merge_stable",
`!R l1 l2.
  transitive R /\
  SORTED R l1
  ==>
  stable R (l1 ++ l2) (merge R l1 l2)`,
 rw [stable_def, filter_merge]);

val mergesortN_stable = Q.store_thm ("mergesortN_stable",
`!R n l.
  total R /\ transitive R
  ==>
  stable R (TAKE n l) (mergesortN R n l)`,
 ho_match_mp_tac mergesortN_ind >>
 rw [] >>
 ONCE_REWRITE_TAC [mergesortN_def] >>
 rw [sort2_stable, sort3_stable] >>
 TRY (rw [stable_def] >> NO_TAC)
 >- (Cases_on `l` >>
     rw [stable_def])
 >- (Cases_on `l` >>
     rw [] >>
     TRY (rw [stable_def] >> NO_TAC) >>
     Cases_on `t` >>
     rw [sort2_stable] >>
     rw [stable_def])
 >- (Cases_on `l` >>
     rw [] >>
     TRY (rw [stable_def] >> NO_TAC) >>
     Cases_on `t` >>
     rw [sort2_stable] >>
     TRY (rw [stable_def] >> NO_TAC) >>
     Cases_on `t'` >>
     rw [sort2_stable, sort3_stable])
 >- (`len1 <= n`
             by (UNABBREV_ALL_TAC >>
                 fs [DIV2_def, DIV_LESS_EQ]) >>
     metis_tac [stable_cong, merge_stable, take_drop_partition, stable_trans, mergesortN_sorted]));

val mergesort_stable = Q.store_thm ("mergesort_stable",
`!R l. transitive R /\ total R ==> stable R l (mergesort R l)`,
 metis_tac [mergesortN_stable, mergesort_def, TAKE_LENGTH_ID]);

(* packaging things up *)

val mergesort_STABLE_SORT = Q.store_thm ("mergesort_STABLE_SORT",
`!R.  transitive R /\ total R ==> STABLE mergesort R`,
 rw [STABLE_DEF, SORTS_DEF] >>
 metis_tac [mergesort_perm, mergesort_sorted, mergesort_stable, stable_def]);

val mergesort_mem = Q.store_thm ("mergesort_mem",
`!R L x. MEM x (mergesort R L) <=> MEM x L`,
 metis_tac [mergesort_perm, MEM_PERM]);

(* On to mergesort_tail *)

val sort2_tail_correct = Q.store_thm ("sort2_tail_correct",
`!neg R x y.
  sort2_tail neg R x y = if neg then REVERSE (sort2 R x y) else sort2 R x y`,
 rw [sort2_def, sort2_tail_def] >>
 fs []);

val sort3_tail_correct = Q.store_thm ("sort3_tail_correct",
`!neg R x y z.
  sort3_tail neg R x y z = if neg then REVERSE (sort3 R x y z) else sort3 R x y z`,
 rw [sort3_def, sort3_tail_def] >>
 fs []);

val merge_tail_correct1 = Q.store_thm ("merge_tail_correct1",
`!neg R l1 l2 acc.
  (neg = F)
  ==>
  merge_tail neg R l1 l2 acc = REVERSE (merge R l1 l2) ++ acc`,
 ho_match_mp_tac merge_tail_ind >>
 rw [merge_tail_def, merge_def, REV_REVERSE_LEM]);

val merge_empty = Q.store_thm ("merge_empty",
`!R l acc.
  merge R l [] = l /\
  merge R [] l = l`,
 Cases_on `l` >>
 rw [merge_def]);

val merge_last_lem1 = Q.prove (
`!R l1 l2 x.
  (!y. MEM y l2 ==> ~R x y)
  ==>
  merge R (l1 ++ [x]) l2 = merge R l1 l2 ++ [x]`,
 ho_match_mp_tac merge_ind >>
 rw [merge_def, merge_empty] >>
 Induct_on `v5` >>
 rw [merge_empty, merge_def] >>
 metis_tac []);

val merge_last_lem2 = Q.prove (
`!R l1 l2 y.
  (!x. MEM x l1 ==> R x y)
  ==>
  merge R l1 (l2 ++ [y]) = merge R l1 l2 ++ [y]`,
 ho_match_mp_tac merge_ind >>
 rw [merge_def, merge_empty] >>
 Induct_on `v9` >>
 rw [merge_empty, merge_def] >>
 metis_tac []);

val merge_tail_correct2 = Q.store_thm ("merge_tail_correct2",
`!neg R l1 l2 acc.
  (neg = T) /\
  transitive R /\
  SORTED R (REVERSE l1) /\
  SORTED R (REVERSE l2)
  ==>
  merge_tail neg R l1 l2 acc = (merge R (REVERSE l1) (REVERSE l2)) ++ acc`,
 ho_match_mp_tac merge_tail_ind >>
 rw [merge_tail_def, merge_def, REV_REVERSE_LEM, merge_empty] >>
 fs [] >>
 `SORTED R (REVERSE l1) /\ SORTED R (REVERSE l2)`
        by metis_tac [SORTED_transitive_APPEND_IFF] >>
 fs []
 >- (match_mp_tac (GSYM merge_last_lem1) >>
     rw [] >>
     rw [] >>
     CCONTR_TAC >>
     fs [] >>
     `R y' y` by metis_tac [mem_sorted_append, MEM_REVERSE, MEM] >>
     metis_tac [transitive_def])
 >- (match_mp_tac (GSYM merge_last_lem2) >>
     rw [] >>
     rw [] >>
     `R x' x` by metis_tac [mem_sorted_append, MEM_REVERSE, MEM] >>
     metis_tac [transitive_def]));

val mergesortN_tail_correct = Q.store_thm ("mergesortN_correct",
`!negate R n l.
  total R /\
  transitive R
  ==>
  mergesortN_tail negate R n l =
    (if negate then REVERSE (mergesortN R n l) else mergesortN R n l)`,
 ho_match_mp_tac mergesortN_tail_ind >>
 rw [] >>
 ONCE_REWRITE_TAC [mergesortN_tail_def, mergesortN_def] >>
 rw [sort2_tail_correct, sort3_tail_correct] >>
 fs [] >>
 every_case_tac >>
 fs [] >>
 UNABBREV_ALL_TAC >>
 rw [merge_tail_correct1] >>
 metis_tac [merge_tail_correct2, mergesortN_sorted, REVERSE_REVERSE, APPEND_NIL]);

val mergesort_tail_correct = Q.store_thm ("mergesort_tail_correct",
`!R l.
  total R /\
  transitive R
  ==>
  mergesort_tail R l = mergesort R l`,
 rw [mergesort_tail_def, mergesort_def, mergesortN_tail_correct]);


 (*
(* Timings *)

load "intLib";

val mergesortN'_def = tDefine "mergesortN'" `
(mergesortN' R 0 l = []) /\
(mergesortN' R 1 (x::l) = [x]) /\
(mergesortN' R 1 [] = []) /\
(mergesortN' R 2 (x::y::l) = sort2 R x y) /\
(mergesortN' R 2 [x] = [x]) /\
(mergesortN' R 2 [] = []) /\
(mergesortN' R n l =
  let len1 = DIV2 n in
    merge R (mergesortN' R (DIV2 n) l) (mergesortN' R (n - len1) (DROP len1 l)))`
 (WF_REL_TAC `measure (\(R,n,l). n)` >>
  rw [DIV2_def] >>
  COOPER_TAC);

val mergesortN''_def = tDefine "mergesortN''" `
(mergesortN'' R 0 l = []) /\
(mergesortN'' R 1 (x::l) = [x]) /\
(mergesortN'' R 1 [] = []) /\
(mergesortN'' R n l =
  let len1 = DIV2 n in
    merge R (mergesortN'' R (DIV2 n) l) (mergesortN'' R (n - len1) (DROP len1 l)))`
 (WF_REL_TAC `measure (\(R,n,l). n)` >>
  rw [DIV2_def] >>
  COOPER_TAC);

val rand_list_def = Define `
(rand_list 0 seed = []) /\
(rand_list (SUC n) seed =
  let v = (1664525 * seed + 1013904223) MOD 4294967296 in
    v::rand_list n v)`;

val l = (time EVAL ``rand_list 10000 353``) |> concl |> rand;
val len_l = ``10000:num``;

val l' = (time EVAL ``MAP (\x. x MOD 65536) ^l``) |> concl |> rand;


time (fn x => (EVAL x; ())) ``LENGTH (COUNT_LIST 10000)``;
time (fn x => (EVAL x; ())) ``COUNT_LIST 10000``;

time (fn x => (EVAL x; ())) ``mergesortN $<= 10000 (COUNT_LIST 10000)``;
>runtime: 10.905s,    gctime: 0.29495s,     systime: 0.06740s.
time (fn x => (EVAL x; ())) ``mergesortN $<= ^len_l ^l``;
> runtime: 27.618s,    gctime: 1.106s,     systime: 0.24801s.
time (fn x => (EVAL x; ())) ``mergesortN $<= ^len_l ^l'``;
> runtime: 18.192s,    gctime: 0.76859s,     systime: 0.16917s.

time (fn x => (EVAL x; ())) ``mergesortN' $<= 10000 (COUNT_LIST 10000)``;
> runtime: 11.322s,    gctime: 0.33336s,     systime: 0.07988s
time (fn x => (EVAL x; ())) ``mergesortN' $<= ^len_l ^l``;
> runtime: 28.974s,    gctime: 1.162s,     systime: 0.31028s.
time (fn x => (EVAL x; ())) ``mergesortN' $<= ^len_l ^l'``;
> runtime: 18.985s,    gctime: 0.94506s,     systime: 0.22901s.

time (fn x => (EVAL x; ())) ``mergesortN'' $<= 10000 (COUNT_LIST 10000)``;
> runtime: 11.977s,    gctime: 0.34678s,     systime: 0.08751s.
time (fn  => (EVAL x; ())) ``mergesortN'' $<= ^len_l ^l``;
> runtime: 29.934s,    gctime: 1.386s,     systime: 0.38797s.
time (fn x => (EVAL x; ())) ``mergesortN'' $<= ^len_l ^l'``;
> runtime: 20.251s,    gctime: 1.180s,     systime: 0.26435s.

time (fn x => (EVAL x; ())) ``mergesort_tail $<= (COUNT_LIST 10000)``;
> runtime: 13.388s,    gctime: 0.59262s,     systime: 0.15220s.
time (fn x => (EVAL x; ())) ``mergesort_tail $<= ^l``;
> runtime: 30.701s,    gctime: 1.878s,     systime: 0.68566s.
time (fn x => (EVAL x; ())) ``mergesort_tail $<= ^l'``;
> runtime: 20.488s,    gctime: 0.64356s,     systime: 0.59357s.

time (fn x => (EVAL x; ())) ``QSORT3 $<= (COUNT_LIST 500)``;
> runtime: 31.436s,    gctime: 0.97548s,     systime: 0.23698s.
time (fn x => (EVAL x; ())) ``QSORT3 $<= ^l``;
> runtime: 1m23s,    gctime: 6.614s,     systime: 2.108s.
time (fn x => (EVAL x; ())) ``QSORT3 $<= ^l'``;
> runtime: 55.361s,    gctime: 5.010s,     systime: 2.373s.

time (fn x => (EVAL x; ())) ``QSORT $<= (COUNT_LIST 500)``;
> runtime: 10.795s,    gctime: 0.80040s,     systime: 0.11975s.
time (fn x => (EVAL x; ())) ``QSORT $<= ^l``;
> runtime: 33.837s,    gctime: 1.495s,     systime: 0.33714s.
time (fn x => (EVAL x; ())) ``QSORT $<= ^l'``;
> runtime: 21.398s,    gctime: 1.040s,     systime: 0.22661s.

*)

val _ = export_theory ();
