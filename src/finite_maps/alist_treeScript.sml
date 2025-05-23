(*
  Definitions and theorems that support automation (the Lib file) for
  fast insertion and lookup into association lists (alists).
*)
open HolKernel bossLib boolLib boolSimps rich_listTheory

local open alistTheory in end

val _ = new_theory "alist_tree";

(* key property: a partial function f can be represented by an assoc list
   al which is known to be sorted according to R *)
val sorted_alist_repr_def = Define `
  sorted_alist_repr R al f <=>
    SORTED R (MAP FST al) /\ irreflexive R /\ transitive R /\ (f = ALOOKUP al)`;

(* inserts on sorted alists *)

val count_append_def = Define `
  count_append (n : num) xs ys = APPEND xs ys`;

val is_insert_def = Define `
  is_insert frame_l frame_r R k x al al' <=>
     irreflexive R /\ transitive R ==>
        SORTED R (MAP FST al) ==>
         (ALOOKUP al' = ALOOKUP ((k, x) :: al)) /\
         (frame_l ==> al <> [] /\ (FST (HD al') = FST (HD al))) /\
         (frame_r ==> al <> [] /\ (FST (LAST al') = FST (LAST al))) /\
         SORTED R (MAP FST al')`;

Theorem HD_APPEND:
  HD (xs ++ ys) = (if xs = [] then HD ys else HD xs)
Proof  Induct_on `xs` \\ fs []
QED

Theorem LAST_APPEND:
  LAST (xs ++ ys) = (if ys = [] then LAST xs else LAST ys)
Proof  Cases_on `ys` \\ fs []
QED

Theorem HD_MAP:
  xs <> [] ==> (HD (MAP f xs) = f (HD xs))
Proof  Cases_on `xs` \\ fs []
QED

Theorem HD_MEM:
  xs <> []  ==> MEM (HD xs) xs
Proof Cases_on `xs` \\ fs []
QED

Theorem is_insert_l:
  !n. is_insert fl T R k x l l' ==>
    is_insert fl T R k x (count_append n l r) (count_append ARB l' r)
Proof
  fs [is_insert_def, count_append_def, sortingTheory.SORTED_APPEND_GEN,
    alistTheory.ALOOKUP_APPEND, FUN_EQ_THM, HD_APPEND, LAST_APPEND,
    listTheory.LAST_MAP]
  \\ (Cases_on `l'` \\ fs [] >- metis_tac [optionTheory.option_CLAUSES])
  \\ (Cases_on `l = []` \\ fs [])
  \\ fs [listTheory.LAST_MAP]
  \\ (rpt strip_tac \\ fs [] \\ CASE_TAC)
QED

Theorem insert_fl_R:
  is_insert fl fr R k x al al' ==> fl ==> SORTED R (MAP FST al)
    ==> irreflexive R /\ transitive R
    ==> (k = FST (HD al)) \/ R (HD (MAP FST al)) k
Proof
  fs [is_insert_def, FUN_EQ_THM]
  \\ rpt strip_tac
  \\ fs []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`)
  \\ fs []
  \\ strip_tac
  \\ FIRST_X_ASSUM (MP_TAC o MATCH_MP alistTheory.ALOOKUP_MEM)
  \\ (Cases_on `al'` \\ fs [sortingTheory.SORTED_EQ])
  \\ fs [listTheory.MEM_MAP, pairTheory.EXISTS_PROD, HD_MAP]
  \\ metis_tac [pairTheory.FST]
QED

Theorem insert_fl_R_append:
  is_insert T fr R k x r r'
    ==> SORTED R (MAP FST (l ++ r))
    ==> irreflexive R /\ transitive R
    ==> ~ MEM k (MAP FST l)
Proof
  strip_tac
  \\ FIRST_ASSUM (MP_TAC o MATCH_MP insert_fl_R)
  \\ fs [METIS_PROVE [] ``b \/ c <=> ~b ==> c``]
  \\ rpt strip_tac
  \\ fs [sortingTheory.SORTED_APPEND, is_insert_def]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `k`)
  \\ fs []
  \\ (Cases_on `HD r` \\ Cases_on `r` \\ fs [])
  \\ metis_tac [relationTheory.transitive_def, relationTheory.irreflexive_def]
QED

Theorem is_insert_r:
  !n. is_insert T fr R k x r r' ==>
    is_insert T fr R k x (count_append n l r) (count_append ARB l r')
Proof
  rpt strip_tac
  \\ MP_TAC insert_fl_R_append
  \\ fs [is_insert_def, count_append_def, sortingTheory.SORTED_APPEND_GEN,
    alistTheory.ALOOKUP_APPEND, FUN_EQ_THM, HD_APPEND, LAST_APPEND, HD_MAP]
  \\ ((Cases_on `r'` \\ fs []) >- metis_tac [optionTheory.option_CLAUSES])
  \\ (rpt strip_tac \\ rpt (CHANGED_TAC (rfs [HD_MAP] \\ fs [])))
  \\ rpt (CASE_TAC \\ fs [])
  \\ FIRST_ASSUM (MP_TAC o MATCH_MP alistTheory.ALOOKUP_MEM)
  \\ metis_tac [listTheory.MEM_MAP, pairTheory.FST]
QED

Theorem is_insert_to_empty:
  !R k x. is_insert F F R k x [] [(k, x)]
Proof   fs [is_insert_def]
QED

Theorem is_insert_overwrite:
  !R k x v. (FST v = k) ==> is_insert T T R k x [v] [(k, x)]
Proof
  Cases_on `v` \\ fs [is_insert_def, FUN_EQ_THM]
QED

Theorem sorted_fst_insert_centre:
  !k. SORTED R (MAP FST l ++ MAP FST r) ==>
    (~ (l = []) ==> R (FST (LAST l)) k) ==>
    (~ (r = []) ==> R k (FST (HD r))) ==>
    SORTED R (MAP FST l ++ (k :: MAP FST r))
Proof
  Cases_on `r` \\ Cases_on `l` \\
  fs [sortingTheory.SORTED_APPEND_GEN, sortingTheory.SORTED_DEF,
      listTheory.LAST_MAP, HD_MAP]
QED

Theorem is_insert_centre_rule:
  (fl ==> ~ (l = [])) ==> (~ (l = []) ==> R (FST (LAST l)) k) ==>
    (fr ==> ~ (r = [])) ==> (~ (r = []) ==> R k (FST (HD r))) ==>
    is_insert fl fr R k x (count_append n l r)
        (count_append ARB l (count_append ARB [(k, x)] r))
Proof
  fs [is_insert_def, count_append_def, HD_APPEND, LAST_APPEND,
      listTheory.LAST_CONS_cond]
  \\ rpt disch_tac
  \\ FIRST_X_ASSUM (MP_TAC o MATCH_MP (Q.SPEC `k` sorted_fst_insert_centre))
  \\ fs [sortingTheory.SORTED_APPEND]
  \\ fs [FUN_EQ_THM, alistTheory.ALOOKUP_APPEND]
  \\ rpt (strip_tac \\ fs [])
  \\ rpt (CASE_TAC \\ fs [])
  \\ FIRST_ASSUM (MP_TAC o MATCH_MP alistTheory.ALOOKUP_MEM)
  \\ fs [listTheory.MEM_MAP, pairTheory.EXISTS_PROD]
  \\ metis_tac [relationTheory.irreflexive_def]
QED

Theorem is_insert_centre =
  is_insert_centre_rule |> Q.GENL [`fl`, `fr`, `R`, `n`, `k`, `x`]
    |> SPECL [T, T] |> CONV_RULE (SIMP_CONV bool_ss []);

Theorem is_insert_far_left:
  !R k x xs. ~ (xs = []) ==> R k (FST (HD xs)) ==>
    is_insert F T R k x xs (count_append ARB [(k, x)] xs)
Proof
  Cases_on `xs` \\
  fs [is_insert_def, count_append_def, sortingTheory.SORTED_DEF]
QED

Theorem is_insert_far_right:
  !R k x xs. ~ (xs = []) ==> R (FST (LAST xs)) k ==>
    is_insert T F R k x xs (count_append ARB xs [(k, x)])
Proof
  rpt strip_tac
  \\ MP_TAC (Q.GENL [`fl`, `fr`, `r`, `l`, `x`] is_insert_centre_rule
    |> Q.SPECL [`T`, `F`, `[]`, `xs`, `x`])
  \\ fs [is_insert_def, count_append_def]
QED

(* bookkeeping and balancing count_append trees *)

Theorem count_append_HD_LAST:
  (HD (count_append i (count_append j xs ys) zs)
    = HD (count_append 0 xs (count_append 0 ys zs))) /\
  (HD (count_append i (x :: xs) ys) = x) /\
  (HD (count_append i [] ys) = HD ys) /\
  (LAST (count_append i xs (count_append j ys zs))
      = LAST (count_append 0 (count_append 0 xs ys) zs)) /\
  (LAST (count_append i xs (y :: ys)) = LAST (y :: ys)) /\
  (LAST (count_append i xs []) = LAST xs) /\
  (HD (x :: xs) = x) /\
  (LAST (x :: y :: zs) = LAST (y :: zs)) /\
  (LAST [x] = x) /\
  ((count_append i (count_append j xs ys) zs = []) =
      (count_append 0 xs (count_append 0 ys zs) = [])) /\
  ((count_append i [] ys = []) = (ys = [])) /\
  ((count_append i (x :: xs) ys = []) = F) /\
  ((x :: xs = []) = F)
Proof fs [count_append_def]
QED

Theorem balance_r:
  count_append i (count_append j xs ys) zs
     = count_append ARB xs (count_append ARB ys zs)
Proof
  fs [count_append_def]
QED

Theorem balance_l:
  count_append i xs (count_append j ys zs)
     = count_append ARB (count_append ARB xs ys) zs
Proof fs [count_append_def]
QED

Theorem set_count:
  !j. count_append i xs ys = count_append j xs ys
Proof
  fs [count_append_def]
QED

(* reprs of various partial function constructions *)
val option_choice_f_def = Define `
  option_choice_f f g = (\x. OPTION_CHOICE (f x) (g x))`;

Theorem alookup_append_option_choice_f:
  ALOOKUP (xs ++ ys) = option_choice_f (ALOOKUP xs) (ALOOKUP ys)
Proof
  rpt (strip_tac ORELSE CASE_TAC ORELSE
       fs [option_choice_f_def, alistTheory.ALOOKUP_APPEND, FUN_EQ_THM])
QED

Theorem alookup_empty_option_choice_f:
  (option_choice_f (ALOOKUP []) f = f)
    /\ (option_choice_f f (ALOOKUP []) = f)
Proof
  fs [FUN_EQ_THM, option_choice_f_def]
QED

Theorem option_choice_f_assoc:
  option_choice_f (option_choice_f f g) h
    = option_choice_f f (option_choice_f g h)
Proof
  fs [option_choice_f_def, FUN_EQ_THM] \\ Cases_on `f x` \\ fs []
QED

Theorem empty_is_ALOOKUP: (\x. NONE) = ALOOKUP []
Proof    fs [FUN_EQ_THM]
QED

Theorem repr_insert:
  sorted_alist_repr R al f /\ is_insert fl fr R k x al al' ==>
    sorted_alist_repr R al' (option_choice_f (ALOOKUP [(k, x)]) f)
Proof
  fs [sorted_alist_repr_def, is_insert_def,
      GSYM alookup_append_option_choice_f]
QED

Theorem alookup_to_option_choice:
  (ALOOKUP (x :: y :: zs) = option_choice_f (ALOOKUP [x]) (ALOOKUP (y :: zs)))
    /\ (option_choice_f (ALOOKUP []) g = g)
Proof
  fs [GSYM alookup_append_option_choice_f]
    \\ fs [FUN_EQ_THM, option_choice_f_def]
QED

Theorem alist_repr_choice_trans_left:
  sorted_alist_repr R al f /\
    sorted_alist_repr R al' (option_choice_f (ALOOKUP al) g) ==>
    sorted_alist_repr R al' (option_choice_f f g)
Proof
  fs [sorted_alist_repr_def]
QED

Theorem alist_repr_refl:
  !al. irreflexive R /\ transitive R ==> SORTED R (MAP FST al) ==>
    sorted_alist_repr R al (ALOOKUP al)
Proof   fs [sorted_alist_repr_def]
QED

(* lookups on sorted alists *)
val is_lookup_def = Define `
  is_lookup fl fr R al x r = (!xs ys. (fl \/ (xs = [])) ==>
    (fr \/ (ys = [])) ==> irreflexive R /\ transitive R ==>
    SORTED R (MAP FST (xs ++ al ++ ys)) ==>
    (ALOOKUP (xs ++ al ++ ys) x = r))`;

Theorem lookup_repr:
  sorted_alist_repr R al f /\ is_lookup fl fr R al x r ==> (f x = r)
Proof
  fs [is_lookup_def, sorted_alist_repr_def]
  \\ metis_tac [APPEND_NIL, MAP]
QED

Theorem is_lookup_l:
  !n. is_lookup fl T R l x res
    ==> is_lookup fl T R (count_append n l r) x res
Proof
  fs [is_lookup_def, count_append_def]
  \\ metis_tac [APPEND_ASSOC, MAP_APPEND]
QED

Theorem is_lookup_r:
  !n. is_lookup T fr R r x res
    ==> is_lookup T fr R (count_append n l r) x res
Proof
  fs [is_lookup_def, count_append_def]
  \\ metis_tac [APPEND_ASSOC, MAP_APPEND]
QED

Theorem is_lookup_far_left:
  !R k k' v. R k k' ==> is_lookup F T R [(k', v)] k NONE
Proof
  fs [is_lookup_def, sortingTheory.SORTED_EQ, listTheory.MEM_MAP,
      pairTheory.EXISTS_PROD,alistTheory.ALOOKUP_NONE,PULL_EXISTS]
  \\ rpt strip_tac
  \\ metis_tac [ relationTheory.irreflexive_def,
     relationTheory.transitive_def]
QED

Theorem is_lookup_far_right:
  !R k k' v. R k' k ==> is_lookup T F R [(k', v)] k NONE
Proof
  fs [is_lookup_def, sortingTheory.SORTED_APPEND, listTheory.MEM_MAP,
      pairTheory.EXISTS_PROD, alistTheory.ALOOKUP_APPEND]
  \\ rpt strip_tac
  \\ Cases_on `ALOOKUP xs k` \\ CASE_TAC \\ fs []
  \\ metis_tac [alistTheory.ALOOKUP_MEM, relationTheory.irreflexive_def,
                relationTheory.transitive_def]
QED

Theorem is_lookup_hit:
  !R k k' v. (k' = k) ==> is_lookup T T R [(k', v)] k (SOME v)
Proof
  fs [is_lookup_def, sortingTheory.SORTED_APPEND, listTheory.MEM_MAP,
      pairTheory.EXISTS_PROD, alistTheory.ALOOKUP_APPEND]
  \\ rpt strip_tac
  \\ rpt (CASE_TAC \\ fs [])
  \\ metis_tac [alistTheory.ALOOKUP_MEM, relationTheory.irreflexive_def,
                relationTheory.transitive_def]
QED

Theorem DISJ_EQ_IMP: (P \/ Q) = (~ P ==> Q)
Proof metis_tac []
QED

val sorted_fst_insert_centre2 = sorted_fst_insert_centre
  |> Q.GENL [`l`, `r`] |> Q.SPECL [`lxs ++ lys`, `rxs ++ rys`]
  |> SIMP_RULE list_ss []

Theorem is_lookup_centre:
  !R n l r k.
     l <> [] ==> R (FST (LAST l)) k ==> r <> [] ==> R k (FST (HD r)) ==>
     is_lookup T T R (count_append n l r) k NONE
Proof
  fs [is_lookup_def, listTheory.MEM_MAP,
      pairTheory.EXISTS_PROD, alistTheory.ALOOKUP_APPEND, count_append_def]
  \\ rpt strip_tac
  \\ FIRST_X_ASSUM (MP_TAC o MATCH_MP (Q.SPEC `k` sorted_fst_insert_centre2))
  \\ fs [LAST_APPEND, HD_APPEND]
  \\ fs [sortingTheory.SORTED_APPEND, sortingTheory.SORTED_EQ,
    listTheory.MEM_MAP, pairTheory.EXISTS_PROD]
  \\ rpt strip_tac
  \\ (Cases_on `ALOOKUP ys k` \\ rpt (CASE_TAC \\ fs [])
    \\ metis_tac [alistTheory.ALOOKUP_MEM, relationTheory.irreflexive_def,
                  relationTheory.transitive_def])
QED

Theorem is_lookup_empty:
  !R k al. (al = []) ==> is_lookup F F R al k NONE
Proof
  fs [is_lookup_def]
QED

val _ = export_theory ();
