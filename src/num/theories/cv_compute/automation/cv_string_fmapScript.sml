(*
  Set up cv translator for string |-> 'a
*)
Theory cv_string_fmap
Ancestors
  cv cv_type arithmetic words cv_rep cv_prim pair list option sum
  alist indexedLists rich_list sptree finite_set cv_std
Libs
  dep_rewrite cv_typeLib cv_repLib cv_transLib

Overload Num[local] = “cv$Num”
Overload Pair[local] = “cv$Pair”

(*----------------------------------------------------------*
   string trie
 *----------------------------------------------------------*)

Datatype:
  str_trie = Nothing
           | Just 'a
           | Branch char str_trie str_trie
End

val _ = (cv_memLib.use_long_names := false);
val from_to_str_trie = cv_typeLib.from_to_thm_for “:'a str_trie”;
val _ = (cv_memLib.use_long_names := true);

Definition st_get_nil_def:
  st_get_nil (Branch _ _ rest) = st_get_nil rest ∧
  st_get_nil (Just x) = SOME x ∧
  st_get_nil Nothing = NONE
End

Definition st_get_def:
  st_get t [] = st_get_nil t ∧
  st_get t (x::xs) = st_get_cons t x xs ∧
  st_get_cons Nothing x xs = NONE ∧
  st_get_cons (Just _) x xs = NONE ∧
  st_get_cons (Branch c subtrie rest) x xs =
    if c < x then NONE else
    if c > x then st_get_cons rest x xs else
      st_get subtrie xs
End

Definition st_make_def:
  st_make [] y = Just y ∧
  st_make (x::xs) y = Branch x (st_make xs y) Nothing
End

Definition st_set_nil_def:
  st_set_nil (Branch c t rest) y = Branch c t (st_set_nil rest y) ∧
  st_set_nil _ y = Just y
End

Definition st_set_cons_def:
  st_set_cons Nothing x xs y = Branch x (st_make xs y) Nothing ∧
  st_set_cons (Just z) x xs y = Branch x (st_make xs y) (Just z) ∧
  st_set_cons (Branch c subtrie rest) x xs y =
    if c < x then
      Branch x (st_make xs y) (Branch c subtrie rest)
    else if c > x then
      Branch c subtrie (st_set_cons rest x xs y)
    else
      Branch c (case xs of
                | [] => st_set_nil subtrie y
                | (x::xs) => st_set_cons subtrie x xs y) rest
End

Definition st_set_def:
  st_set t [] y = st_set_nil t y ∧
  st_set t (x::xs) y = st_set_cons t x xs y
End

Definition st_sets_def:
  st_sets t [] = t ∧
  st_sets t ((s,a)::rest) = st_set (st_sets t rest) s a
End

Definition st_del_nil_def:
  st_del_nil (Branch x y rest) = Branch x y (st_del_nil rest) ∧
  st_del_nil _ = Nothing
End

Definition mk_Branch_def:
  mk_Branch x t1 t2 = if t1 = Nothing then t2 else Branch x t1 t2
End

Definition st_del_cons_def:
  st_del_cons Nothing x xs = Nothing ∧
  st_del_cons (Just z) x xs = Just z ∧
  st_del_cons (Branch c subtrie rest) x xs =
    if c < x then
      Branch c subtrie rest
    else if c > x then
      Branch c subtrie (st_del_cons rest x xs)
    else
      mk_Branch c (case xs of
                   | [] => st_del_nil subtrie
                   | (x::xs) => st_del_cons subtrie x xs) rest
End

Definition st_del_def:
  st_del t [] = st_del_nil t ∧
  st_del t (x::xs) = st_del_cons t x xs
End

(* verification *)

Definition st_flat_def:
  st_flat Nothing = [] ∧
  st_flat (Just a) = [("",a)] ∧
  st_flat (Branch c t1 t2) = MAP (λ(k,v). (c::k,v)) (st_flat t1) ++ st_flat t2
End

Definition st_sorted_def:
  st_sorted Nothing = T ∧
  st_sorted (Just x) = T ∧
  st_sorted (Branch c t1 t2) = (st_sorted t1 ∧
                                st_sorted t2 ∧
                                ∀c' t1' t2'. t2 = Branch c' t1' t2' ⇒ c < c')
End

Theorem st_get_Nothing:
  ∀xs. st_get Nothing xs = NONE
Proof
  Cases \\ fs [st_get_def, st_get_nil_def]
QED

Theorem st_del_Nothing:
  ∀xs. st_del Nothing xs = Nothing
Proof
  Cases \\ fs [st_del_def, st_del_nil_def, st_del_cons_def]
QED

Theorem st_sorted_st_sets:
  st_sorted t ⇒ st_sorted (st_sets t xs)
Proof
  cheat
QED

Theorem ALOOKUP_st_flat:
  st_sorted t ⇒ ALOOKUP (st_flat t) n = st_get t n
Proof
  cheat
QED

Theorem st_get_st_sets:
  st_get (st_sets t xs) n = case ALOOKUP xs n of NONE => st_get t n | res => res
Proof
  cheat
QED

Theorem st_sets_eq:
  ALOOKUP xs = ALOOKUP ys ⇒ st_sets t xs = st_sets t ys
Proof
  cheat
QED

Theorem st_del_st_set:
  st_del (st_set t n x) m = if m = n then st_del t m else st_set (st_del t m) n x
Proof
  cheat
QED

Theorem st_del_st_sets:
  st_del (st_sets t xs) n = st_sets (st_del t n) (FILTER (λ(k,v). k ≠ n) xs)
Proof
  Induct_on ‘xs’
  \\ fs [st_sets_def,FORALL_PROD,st_del_st_set]
  \\ rpt gen_tac \\ IF_CASES_TAC \\ simp []
  \\ simp [st_sets_def]
QED

val _ = cv_trans st_get_nil_def;
val _ = cv_trans st_get_def;
val _ = cv_trans st_make_def;
val _ = cv_trans st_set_nil_def;
val _ = cv_trans st_set_cons_def;
val _ = cv_trans st_set_def;
val _ = cv_trans st_del_nil_def;
val _ = cv_trans mk_Branch_def;
val _ = cv_trans st_del_cons_def;
val _ = cv_trans st_del_def;

(*----------------------------------------------------------*
   string |-> 'a
 *----------------------------------------------------------*)

Definition from_string_fmap_def:
  from_string_fmap (f:'a -> cv) (m: string |-> 'a) =
    from_cv_string_fmap_str_trie f (st_sets Nothing (fmap_to_alist m))
End

Definition to_string_fmap_def:
  to_string_fmap (t:cv -> 'a) m =
    alist_to_fmap (st_flat (to_str_trie t m))
End

Theorem from_to_string_fmap[cv_from_to]:
  from_to (f0:'a -> cv) t0 ==>
  from_to (from_string_fmap f0) (to_string_fmap t0)
Proof
  strip_tac
  \\ drule (DISCH_ALL from_to_str_trie)
  \\ gvs [from_string_fmap_def,to_string_fmap_def,from_to_def] \\ rw []
  \\ gvs [finite_mapTheory.TO_FLOOKUP]
  \\ simp [FUN_EQ_THM] \\ gen_tac
  \\ DEP_REWRITE_TAC [ALOOKUP_st_flat]
  \\ irule_at Any st_sorted_st_sets \\ simp [st_sorted_def]
  \\ gvs [st_get_st_sets,st_get_def,st_get_Nothing]
  \\ rename [‘FLOOKUP x y’] \\ Cases_on ‘FLOOKUP x y’ \\ fs []
QED

Theorem cv_rep_string_FEMPTY[cv_rep]:
  from_string_fmap f FEMPTY = Num 0
Proof
  EVAL_TAC \\ gvs [] \\ EVAL_TAC
QED

Theorem cv_rep_string_FLOOKUP[cv_rep]:
  from_option f (FLOOKUP m n) = cv_st_get (from_string_fmap f m) (from_list from_char n)
Proof
  gvs [from_string_fmap_def, GSYM $ fetch "-" "cv_st_get_thm"]
  \\ simp [st_get_st_sets, st_get_Nothing]
  \\ rename [‘FLOOKUP x y’] \\ Cases_on ‘FLOOKUP x y’ \\ fs []
QED

Theorem cv_rep_string_FUPDATE[cv_rep]:
  from_string_fmap f (m |+ (k,v)) = cv_st_set (from_string_fmap f m) (from_list from_char k) (f v)
Proof
  gvs [from_string_fmap_def,GSYM $ fetch "-" "cv_st_set_thm"] \\ AP_TERM_TAC
  \\ simp [GSYM st_sets_def]
  \\ irule st_sets_eq \\ fs [finite_mapTheory.FLOOKUP_SIMP, FUN_EQ_THM]
QED

val FUPDATE_LIST_pre_def = finite_mapTheory.FUPDATE_LIST_THM
 |> SRULE [FORALL_PROD]
 |> INST_TYPE [alpha |-> “:string”]
 |> cv_trans_pre "FUPDATE_LIST_pre";

Theorem FUPDATE_LIST_pre[cv_pre]:
  ∀f ls. FUPDATE_LIST_pre f ls
Proof
  Induct_on`ls`
  \\ rw[Once FUPDATE_LIST_pre_def]
QED

Theorem cv_rep_string_DOMSUB[cv_rep]:
  from_to f t ⇒
  from_string_fmap f (m \\ k) = cv_st_del (from_string_fmap f m) (from_list from_char k)
Proof
  rw[from_string_fmap_def]
  \\ drule (GSYM (theorem "cv_st_del_thm" |> DISCH_ALL))
  \\ simp [] \\ disch_then kall_tac
  \\ AP_TERM_TAC
  \\ simp [st_del_st_sets, st_del_Nothing]
  \\ irule st_sets_eq \\ fs [finite_mapTheory.FLOOKUP_SIMP, FUN_EQ_THM]
  \\ gvs [ALOOKUP_FILTER,finite_mapTheory.DOMSUB_FLOOKUP_THM]
  \\ rw []
QED
