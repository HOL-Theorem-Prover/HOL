(*
  Apply cv translator to standard theories list, pair, sptree, etc.
*)
open HolKernel Parse boolLib bossLib dep_rewrite;
open cv_typeTheory cvTheory cv_typeLib cv_repLib;
open arithmeticTheory wordsTheory cv_repTheory cv_primTheory cv_transLib;
open pairTheory listTheory optionTheory sumTheory alistTheory indexedListsTheory;
open rich_listTheory sptreeTheory finite_setTheory;

val _ = new_theory "cv_std";

(*----------------------------------------------------------*
   pair
 *----------------------------------------------------------*)

val _ = cv_rep_for [] “(x:'a, y:'b)”

Theorem cv_FST[cv_rep]:
  f_a (FST v) = cv_fst ((from_pair f_a f_b) (v: 'a # 'b))
Proof
  Cases_on ‘v’ \\ gvs [from_pair_def]
QED

Theorem cv_SND[cv_rep]:
  f_b (SND v) = cv_snd ((from_pair f_a f_b) (v: 'a # 'b))
Proof
  Cases_on ‘v’ \\ gvs [from_pair_def]
QED

(*----------------------------------------------------------*
   option
 *----------------------------------------------------------*)

val _ = cv_rep_for [] “SOME (x:'a)”

Theorem cv_THE[cv_rep]:
  v <> NONE ==> f_a (THE v) = cv_snd ((from_option f_a) (v:'a option))
Proof
  Cases_on ‘v’ \\ gvs [from_option_def]
QED

Theorem cv_IS_SOME[cv_rep]:
  b2c (IS_SOME v) = cv_ispair ((from_option f_a) (v:'a option))
Proof
  Cases_on ‘v’ \\ gvs [from_option_def]
QED

Theorem cv_IS_NONE[cv_rep]:
  b2c (IS_NONE v) = cv_sub (Num 1) (cv_ispair ((from_option f_a) (v:'a option)))
Proof
  Cases_on ‘v’ \\ gvs [from_option_def]
QED

(*----------------------------------------------------------*
   sum
 *----------------------------------------------------------*)

val res = cv_trans ISL;
val res = cv_trans ISR;

val res = cv_trans_pre OUTL;

Theorem OUTL_pre[cv_pre]:
  OUTL_pre x <=> ISL x
Proof
  Cases_on ‘x’ \\ fs [res]
QED

val res = cv_trans_pre OUTR;

Theorem OUTR_pre[cv_pre]:
  OUTR_pre x <=> ISR x
Proof
  Cases_on ‘x’ \\ fs [res]
QED

(*----------------------------------------------------------*
   list
 *----------------------------------------------------------*)

Theorem cv_HD[cv_rep]:
  v <> [] ==> f_a (HD v) = cv_fst ((from_list f_a) (v:'a list))
Proof
  Cases_on ‘v’ \\ fs [from_list_def]
QED

Theorem cv_TL[cv_rep]:
  (from_list f_a) (TL v) = cv_snd ((from_list f_a) (v:'a list))
Proof
  Cases_on ‘v’ \\ fs [from_list_def]
QED

val res = cv_trans oHD_def;
val res = cv_trans NULL_DEF;
val res = cv_trans oEL_def;

val res = cv_trans SNOC;
val res = cv_trans APPEND;

val res = cv_trans FLAT;

val res = cv_trans TAKE_def;

val res = cv_trans DROP_def;

val res = cv_trans_pre EL;

Theorem EL_pre[cv_pre]:
  !n xs. EL_pre n xs <=> n < LENGTH xs
Proof
  Induct \\ rw [] \\ simp [Once res] \\ Cases_on ‘xs’ \\ gvs []
QED

val res = cv_trans LEN_DEF;
val res = cv_trans LENGTH_LEN;

val res = cv_trans REV_DEF;
val res = cv_trans REVERSE_REV;

val res = cv_trans SUM_ACC_DEF;
val res = cv_trans SUM_SUM_ACC;

Theorem FRONT[local]:
  FRONT (x::xs) = case xs of [] => [] | _ => x :: FRONT xs
Proof
  Cases_on ‘xs’ \\ gvs [FRONT_DEF]
QED

val res = cv_trans_pre FRONT;

Theorem FRONT_pre[cv_pre]:
  !xs. FRONT_pre xs <=> xs <> []
Proof
  Induct_on ‘xs’
  \\ once_rewrite_tac [res] \\ gvs []
  \\ Cases_on ‘xs’ \\ gvs []
QED

Theorem LAST[local]:
  LAST (x::xs) = case xs of [] => x | _ => LAST xs
Proof
  Cases_on ‘xs’ \\ gvs [LAST_DEF]
QED

val res = cv_trans_pre LAST;

Theorem LAST_pre[cv_pre]:
  !xs. LAST_pre xs <=> xs <> []
Proof
  Induct_on ‘xs’
  \\ once_rewrite_tac [res] \\ gvs []
  \\ Cases_on ‘xs’ \\ gvs []
QED

Definition list_mem_def:
  list_mem y [] = F /\
  list_mem y (x::xs) = if x = y then T else list_mem y xs
End

val res = cv_trans list_mem_def;

val lemma = cv_rep_for [] “list_mem x xs” |> DISCH_ALL

Theorem cv_rep_MEM[cv_rep]:
  from_to f_a t_a ==>
  cv_rep T (cv_list_mem (f_a x) (from_list f_a xs)) b2c (MEM (x:'a) xs)
Proof
  qsuff_tac ‘MEM x xs = list_mem x xs’
  >- (simp [] \\ mp_tac lemma \\ fs [])
  \\ Induct_on ‘xs’ \\ gvs [list_mem_def] \\ metis_tac []
QED

Triviality conj_eq_if:
  x /\ y <=> if x then y else F
Proof
  Cases_on ‘x’ \\ gvs []
QED

Triviality if_not:
  (if ~b then x else y) = if b then y else x
Proof
  Cases_on ‘b’ \\ gvs []
QED

val all_distinct =
  ALL_DISTINCT |> DefnBase.one_line_ify NONE |> PURE_REWRITE_RULE [conj_eq_if,if_not]

val res = cv_trans all_distinct;

val is_prefix =
  isPREFIX |> DefnBase.one_line_ify NONE |> PURE_REWRITE_RULE [conj_eq_if,if_not]

val res = cv_trans is_prefix;

val res = cv_trans LUPDATE_DEF;

Triviality index_of:
  INDEX_OF x [] = NONE /\
  INDEX_OF x (y::ys) =
    if x = y then SOME 0 else
      case INDEX_OF x ys of
      | NONE => NONE
      | SOME n => SOME (n+1)
Proof
  gvs [INDEX_OF_def,INDEX_FIND_def]
  \\ rw [] \\ gvs []
  \\ simp [Once listTheory.INDEX_FIND_add]
  \\ Cases_on ‘INDEX_FIND 0 ($= x) ys’ \\ gvs []
  \\ rename [‘_ = SOME y’] \\ PairCases_on ‘y’ \\ gvs []
QED

val res = cv_trans_pre index_of;

Definition replicate_acc_def:
  replicate_acc n x acc =
    if n = 0:num then acc else replicate_acc (n-1) x (x::acc)
End

val res = cv_trans replicate_acc_def;

Theorem REPLICATE:
  REPLICATE n c = replicate_acc n c []
Proof
  qsuff_tac ‘!n c acc. replicate_acc n c acc = REPLICATE n c ++ acc’ >- gvs []
  \\ Induct \\ gvs [] \\ simp [Once replicate_acc_def]
  \\ rewrite_tac [GSYM SNOC_APPEND,SNOC_REPLICATE] \\ gvs []
QED

val res = cv_trans REPLICATE;
val res = cv_trans (PAD_LEFT |> REWRITE_RULE [GSYM REPLICATE_GENLIST]);
val res = cv_trans (PAD_RIGHT |> REWRITE_RULE [GSYM REPLICATE_GENLIST]);

val res = cv_trans nub_def;

val res = cv_trans ALOOKUP_def

val res = cv_trans findi_def (* TODO: improve *)

val res = cv_trans ZIP_def;

Theorem UNZIP_eq:
  UNZIP ts =
    case ts of
    | [] => ([],[])
    | (x::xs) => let (t1,t2) = UNZIP xs in (FST x :: t1, SND x :: t2)
Proof
  Cases_on ‘ts’ \\ gvs []
  \\ gvs [UNZIP] \\ Cases_on ‘UNZIP t’ \\ gvs []
QED

val res = cv_trans UNZIP_eq

Definition genlist_def:
  genlist i f 0 = [] /\
  genlist i f (SUC n) = f i :: genlist (i+1:num) f n
End

Theorem genlist_eq_GENLIST[cv_inline]:
  GENLIST = genlist 0
Proof
  qsuff_tac ‘!i f n. genlist i f n = GENLIST (f o (λk. k + i)) n’
  >- (gvs [FUN_EQ_THM] \\ rw [] \\ AP_THM_TAC \\ AP_TERM_TAC \\ gvs [FUN_EQ_THM])
  \\ Induct_on ‘n’ \\ gvs [genlist_def]
  \\ rewrite_tac [listTheory.GENLIST_CONS] \\ gvs []
  \\ rw [] \\ AP_THM_TAC \\ AP_TERM_TAC \\ gvs [FUN_EQ_THM,arithmeticTheory.ADD1]
QED

Definition count_loop_def:
  count_loop n k = if n = 0:num then [] else k::count_loop (n-1) (k+1:num)
End

val res = cv_trans count_loop_def;

Theorem cv_COUNT_LIST[cv_inline]:
  COUNT_LIST n = count_loop n 0
Proof
  qsuff_tac `!n k. count_loop n k = MAP (\i. i + k) (COUNT_LIST n)` >>
  simp[] >>
  Induct \\ rw[] \\ simp [rich_listTheory.COUNT_LIST_def,Once count_loop_def]
  \\ gvs [MAP_MAP_o,combinTheory.o_DEF,ADD1] \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ gvs [FUN_EQ_THM]
QED

Theorem K_THM[cv_inline] = combinTheory.K_THM;
Theorem I_THM[cv_inline] = combinTheory.I_THM;
Theorem o_THM[cv_inline] = combinTheory.o_THM;

Definition list_mapi_def:
  list_mapi i f [] = [] /\
  list_mapi i f (x::xs) = f i x :: list_mapi (i + 1n) f xs
End

Theorem MAPi_eq_list_mapi[cv_inline]:
  MAPi = list_mapi 0
Proof
  qsuff_tac `!l i f. list_mapi i f l = MAPi (f o (λn. n + i)) l`
  >- gvs[FUN_EQ_THM, combinTheory.o_DEF, SF ETA_ss] >>
  Induct >> rw[list_mapi_def] >> gvs[combinTheory.o_DEF, ADD1]
QED

Definition cv_map_fst_def:
  cv_map_fst cv =
    cv_if (cv_ispair cv)
      (Pair (cv_fst (cv_fst cv)) (cv_map_fst (cv_snd cv)))
      (Num 0)
Termination
  WF_REL_TAC ‘measure cv_size’ >> cv_termination_tac
End

Theorem cv_MAP_FST[cv_rep]:
  from_list a (MAP FST l) = cv_map_fst (from_list (from_pair a b) l)
Proof
  Induct_on `l` >> rw[from_list_def] >>
  simp[Once cv_map_fst_def, SimpRHS] >>
  Cases_on `h` >> gvs[from_pair_def]
QED

Definition cv_map_snd_def:
  cv_map_snd cv =
    cv_if (cv_ispair cv)
      (Pair (cv_snd (cv_fst cv)) (cv_map_snd (cv_snd cv)))
      (Num 0)
Termination
  WF_REL_TAC ‘measure cv_size’ >> cv_termination_tac
End

Theorem cv_MAP_SND[cv_rep]:
  from_list b (MAP SND l) = cv_map_snd (from_list (from_pair a b) l)
Proof
  Induct_on `l` >> rw[from_list_def] >>
  simp[Once cv_map_snd_def, SimpRHS] >>
  Cases_on `h` >> gvs[from_pair_def]
QED

(*----------------------------------------------------------*
   sptree / num_map / num_set
 *----------------------------------------------------------*)

val res = cv_trans sptreeTheory.insert_def;
val res = cv_trans sptreeTheory.lookup_def;

val def = sptreeTheory.fromList_def;
val res = cv_auto_trans sptreeTheory.fromList_def;

val res = cv_trans sptreeTheory.mk_BN_def;
val res = cv_trans sptreeTheory.mk_BS_def;
val res = cv_trans sptreeTheory.delete_def;

val res = cv_trans sptreeTheory.union_def;
val res = cv_trans sptreeTheory.inter_def;
val res = cv_trans sptreeTheory.difference_def;

val res = cv_auto_trans sptreeTheory.toList_def;
val res = cv_auto_trans sptreeTheory.mk_wf_def;
val res = cv_auto_trans sptreeTheory.size_def;

val res = cv_trans sptreeTheory.list_to_num_set_def;
val res = cv_trans sptreeTheory.list_insert_def;
val res = cv_trans sptreeTheory.alist_insert_def;

val res = cv_trans sptreeTheory.lrnext_def;

val res = cv_trans sptreeTheory.spt_center_def

val res = cv_trans sptreeTheory.spt_left_def
val res = cv_trans sptreeTheory.spt_right_def

val res = cv_trans sptreeTheory.subspt_eq;

val lam = sptreeTheory.toAList_def |> SPEC_ALL |> concl |> find_term is_abs;

Definition toAList_foldi_def:
  toAList_foldi = foldi ^lam
End

val toAList_foldi_eq = sptreeTheory.foldi_def
                  |> CONJUNCTS |> map (ISPEC lam)
                  |> LIST_CONJ |> REWRITE_RULE [GSYM toAList_foldi_def]
                  |> SIMP_RULE std_ss [];

val res = cv_trans_pre toAList_foldi_eq;

Theorem toAList_foldi_pre[cv_pre]:
  !a0 a1 a2. toAList_foldi_pre a0 a1 a2
Proof
  Induct_on ‘a2’ \\ gvs [] \\ simp [Once res] \\ gvs []
QED

val res = cv_trans
  (sptreeTheory.toAList_def |> REWRITE_RULE [GSYM toAList_foldi_def,FUN_EQ_THM]);

Definition cv_right_depth_def:
  cv_right_depth (Num _) = 0:num /\
  cv_right_depth (Pair x y) = cv_right_depth y + 1
End

val res = cv_trans spts_to_alist_add_pause_def;
val res = cv_trans spts_to_alist_aux_def;
val res = cv_trans spts_to_alist_def;

val res = cv_trans toSortedAList_def;

(*----------------------------------------------------------*
   num |-> 'a
 *----------------------------------------------------------*)

Definition from_fmap_def:
  from_fmap (f:'a -> cv) (m: num |-> 'a) =
    from_sptree_sptree_spt f (fromAList (fmap_to_alist m))
End

Definition to_fmap_def:
  to_fmap (t:cv -> 'a) m =
    alist_to_fmap (toAList (to_sptree_spt t m))
End

Theorem from_to_fmap[cv_from_to]:
  from_to (f0:'a -> cv) t0 ==>
  from_to (from_fmap f0) (to_fmap t0)
Proof
  strip_tac
  \\ drule (fetch "-" "from_sptree_to_sptree_spt_thm")
  \\ gvs [from_fmap_def,to_fmap_def,from_to_def] \\ rw []
  \\ gvs [finite_mapTheory.TO_FLOOKUP]
  \\ gvs [FUN_EQ_THM,sptreeTheory.ALOOKUP_toAList,sptreeTheory.lookup_fromAList]
QED

Theorem cv_rep_FEMPTY[cv_rep]:
  from_fmap f FEMPTY = Num 0
Proof
  EVAL_TAC \\ gvs [] \\ EVAL_TAC
QED

Theorem cv_rep_FLOOKUP[cv_rep]:
  from_option f (FLOOKUP m n) = cv_lookup (Num n) (from_fmap f m)
Proof
  gvs [from_fmap_def,GSYM $ fetch "-" "cv_lookup_thm",sptreeTheory.lookup_fromAList]
QED

Theorem cv_rep_FUPDATE[cv_rep]:
  from_fmap f (m |+ (k,v)) = cv_insert (Num k) (f v) (from_fmap f m)
Proof
  gvs [from_fmap_def,GSYM $ fetch "-" "cv_insert_thm"] \\ AP_TERM_TAC
  \\ dep_rewrite.DEP_REWRITE_TAC [sptreeTheory.spt_eq_thm,sptreeTheory.wf_insert]
  \\ gvs [wf_fromAList,lookup_insert,lookup_fromAList,finite_mapTheory.FLOOKUP_SIMP]
  \\ rw []
QED

(*----------------------------------------------------------*
   num fset
 *----------------------------------------------------------*)

val from_to_num_set = from_to_thm_for “:num_set”;
val to_num_set = from_to_num_set |> concl |> rand;
val from_num_set = from_to_num_set |> concl |> rator |> rand;

Definition to_num_fset_def:
  to_num_fset cv = fromSet (domain (^to_num_set cv))
End

Definition from_num_fset_def:
  from_num_fset fs = ^from_num_set $ list_to_num_set $ fset_REP fs
End

Theorem from_to_num_fset[cv_from_to]:
  from_to from_num_fset to_num_fset
Proof
  rw[from_to_def, from_num_fset_def, to_num_fset_def]
  \\ rw[GSYM toSet_11, toSet_fromSet]
  \\ mp_tac from_to_num_set
  \\ gs[from_to_def, pred_setTheory.EXTENSION,
        GSYM fIN_IN, domain_list_to_num_set, fIN_def]
QED

val from_sptree_sptree_spt_def = definition "from_sptree_sptree_spt_def";
val cv_insert_thm = theorem "cv_insert_thm";
val cv_lookup_thm = theorem "cv_lookup_thm";
val cv_union_thm = theorem "cv_union_thm";
val cv_list_to_num_set_thm = theorem "cv_list_to_num_set_thm";

Theorem fEMPTY_num_cv_rep[cv_rep]:
  from_num_fset fEMPTY = Num 0
Proof
  rw[from_num_fset_def,
     Q.ISPEC`from_unit`(CONJUNCT1(GSYM from_sptree_sptree_spt_def))]
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[spt_eq_thm]
  \\ rw[lookup_list_to_num_set, wf_list_to_num_set, MEM_fset_REP]
QED

Theorem fINSERT_num_cv_rep[cv_rep]:
  from_num_fset (fINSERT e s) =
  cv_insert (Num e) (Num 0) (from_num_fset s)
Proof
  rw[from_num_fset_def, GSYM cv_insert_thm, GSYM from_unit_def]
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[spt_eq_thm]
  \\ rw[wf_insert, wf_list_to_num_set,
        lookup_list_to_num_set, lookup_insert,
        MEM_fset_REP]
  \\ gs[]
QED

Theorem fIN_num_cv_rep[cv_rep]:
  b2c (fIN e s) =
  cv_ispair $ (cv_lookup (Num e) (from_num_fset s))
Proof
  rw[from_num_fset_def, GSYM cv_lookup_thm, from_option_def,
     lookup_list_to_num_set, MEM_fset_REP]
QED

Theorem fUNION_num_cv_rep[cv_rep]:
  from_num_fset (fUNION s1 s2) =
  cv_union (from_num_fset s1) (from_num_fset s2)
Proof
  rw[from_num_fset_def, GSYM cv_union_thm]
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[spt_eq_thm]
  \\ simp[wf_list_to_num_set, wf_union,
          lookup_list_to_num_set, lookup_union]
  \\ rw[fUNION_def, MEM_fset_REP] \\ gs[]
QED

Theorem fset_ABS_num_cv_rep[cv_rep]:
  from_num_fset (fset_ABS l) =
  cv_list_to_num_set (from_list Num l)
Proof
  rw[from_num_fset_def, GSYM cv_list_to_num_set_thm]
  \\ AP_TERM_TAC
  \\ DEP_REWRITE_TAC[spt_eq_thm]
  \\ simp[wf_list_to_num_set, lookup_list_to_num_set, MEM_fset_REP]
  \\ simp[GSYM fromSet_set, IN_fromSet]
QED

(*----------------------------------------------------------*
   Misc.
 *----------------------------------------------------------*)

val _ = cv_trans v2n_custom_def;

val _ = export_theory();
