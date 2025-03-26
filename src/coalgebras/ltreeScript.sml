(*
  This file defines a rose tree data structure as a co-inductive
  datatype called 'a ltree, which is short for lazy tree. This
  co-datatype has one constructor, called Branch that has type:

      Branch : 'a -> 'a ltree llist -> 'a ltree

  Note that this tree data structure allows for both infinite depth
  and infinite breadth.
*)
open HolKernel Parse boolLib bossLib;

open arithmeticTheory listTheory rich_listTheory llistTheory alistTheory optionTheory
     pred_setTheory relationTheory pairTheory combinTheory set_relationTheory
     hurdUtils iterateTheory tautLib;

open monadsyntax;
val _ = enable_monadsyntax ();
val _ = enable_monad "option";

val _ = new_theory "ltree";

(* make type definition *)
Type ltree_rep[local] = ``:num list -> 'a # num option``;

Overload NOTHING[local] = ``(ARB:'a, SOME (0:num))``;

Definition ltree_rep_ok_def:
  ltree_rep_ok f <=>
    !path x n.
      f path = (x, SOME n) ==>
      !pos rest. f (path ++ pos::rest) <> NOTHING ==> pos < n
End

Theorem type_inhabited[local]:
  ?f. ltree_rep_ok f
Proof
  qexists_tac `\p. NOTHING` \\ fs [ltree_rep_ok_def] \\ rw []
QED

val ltree_tydef = new_type_definition ("ltree", type_inhabited);

val repabs_fns = define_new_type_bijections
  { name = "ltree_absrep",
    ABS  = "ltree_abs",
    REP  = "ltree_rep",
    tyax = ltree_tydef};

(* prove basic theorems about rep and abs functions *)
val ltree_absrep = CONJUNCT1 repabs_fns
val ltree_repabs = CONJUNCT2 repabs_fns

Theorem ltree_rep_ok_ltree_rep[local,simp]:
  ltree_rep_ok (ltree_rep f)
Proof
  fs [ltree_repabs, ltree_absrep]
QED

Theorem ltree_abs_11[local]:
  ltree_rep_ok r1 /\ ltree_rep_ok r2 ==>
  (ltree_abs r1 = ltree_abs r2 <=> r1 = r2)
Proof
  fs [ltree_repabs, EQ_IMP_THM] \\ metis_tac []
QED

Theorem ltree_rep_11[local]:
  (ltree_rep t1 = ltree_rep t2) = (t1 = t2)
Proof
  fs [EQ_IMP_THM] \\ metis_tac [ltree_absrep]
QED

Theorem every_ltree_rep_ok[local]:
  !ts. every ltree_rep_ok (LMAP ltree_rep ts)
Proof
  rw [] \\ qspec_then `ts` strip_assume_tac fromList_fromSeq
  \\ rw [LMAP_fromList,every_fromList_EVERY,EVERY_MEM,MEM_MAP]
  \\ fs [ltree_rep_ok_ltree_rep]
QED

Theorem LMAP_ltree_rep_11[local]:
  LMAP ltree_rep ts1 = LMAP ltree_rep ts2 <=> ts1 = ts2
Proof
  rw []
  \\ qspec_then `ts1` strip_assume_tac fromList_fromSeq \\ rw []
  \\ qspec_then `ts2` strip_assume_tac fromList_fromSeq \\ rw []
  \\ fs [LMAP_fromList]
  \\ fs [Once FUN_EQ_THM,ltree_rep_11] \\ fs [FUN_EQ_THM]
  \\ rename [`MAP _ l1 = MAP _ l2`]
  \\ qid_spec_tac `l1`
  \\ qid_spec_tac `l2`
  \\ Induct \\ Cases_on `l1` \\ fs [ltree_rep_11]
QED

Theorem LMAP_ltree_rep_ltree_abs[local]:
  every ltree_rep_ok ts ==>
  LMAP ltree_rep (LMAP ltree_abs ts) = ts
Proof
  rw [] \\ qspec_then `ts` strip_assume_tac fromList_fromSeq
  \\ fs [LMAP_fromList,every_fromList_EVERY,MEM_MAP,
         LMAP_fromList,MAP_MAP_o]
  \\ rw [ltree_repabs,FUN_EQ_THM] \\ fs [ltree_repabs]
  \\ Induct_on `l` \\ fs [ltree_repabs]
QED

(* define the only constructor: Branch *)
Definition Branch_rep_def:
  Branch_rep (x:'a) (xs:('a ltree_rep) llist) =
    \path. case path of
           | [] => (x, LLENGTH xs)
           | (n::rest) => case LNTH n xs of SOME t => t rest | NONE => NOTHING
End

Definition Branch:
  Branch a ts = ltree_abs (Branch_rep a (LMAP ltree_rep ts))
End

Theorem ltree_rep_ok_Branch_rep_every[local]:
  ltree_rep_ok (Branch_rep a ts) = every ltree_rep_ok ts
Proof
  fs [Branch_rep_def,ltree_rep_ok_def]
  \\ rw [] \\ reverse (qspec_then `ts` strip_assume_tac fromList_fromSeq)
  \\ rw [ltree_rep_ok_def]
  \\ eq_tac \\ rpt strip_tac
  THEN1
   (first_x_assum (qspecl_then [`i::path`,`x`,`n`] mp_tac)
    \\ fs [] \\ disch_then drule \\ fs [])
  THEN1
   (fs[AllCaseEqs()] >> rfs[] >> first_x_assum (drule_then irule) >>
    RULE_ASSUM_TAC (REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >> metis_tac[])
  \\ fs [every_fromList_EVERY,LNTH_fromList]
  THEN1
   (rw [EVERY_EL,ltree_rep_ok_def]
    \\ first_x_assum (qspec_then `n::path` mp_tac) \\ fs []
    \\ disch_then drule \\ fs [])
  \\ fs [EVERY_EL,ltree_rep_ok_def]
  \\ Cases_on `path` \\ fs []
  \\ rw [] \\ fs [AllCaseEqs()]
  \\ res_tac \\ fs [] >> metis_tac[]
QED

Theorem ltree_rep_ok_Branch_rep[local]:
  every ltree_rep_ok ts ==> ltree_rep_ok (Branch_rep a ts)
Proof
  fs [ltree_rep_ok_Branch_rep_every]
QED

Theorem ltree_rep_ok_Branch_rep_IMP[local]:
  ltree_rep_ok (Branch_rep a ts) ==> every ltree_rep_ok ts
Proof
  fs [ltree_rep_ok_Branch_rep_every]
QED

(* prove injectivity *)
Theorem Branch_rep_11[local]:
  !a1 a2 ts1 ts2. Branch_rep a1 ts1 = Branch_rep a2 ts2 <=> a1 = a2 /\ ts1 = ts2
Proof
  fs [Branch_rep_def,FUN_EQ_THM]
  \\ rpt gen_tac \\ eq_tac \\ simp []
  \\ strip_tac
  \\ first_assum (qspec_then `[]` assume_tac) \\ fs [] \\ rw []
  \\ reverse (qspec_then `ts1` strip_assume_tac fromList_fromSeq) \\ rw []
  \\ reverse (qspec_then `ts2` strip_assume_tac fromList_fromSeq) \\ rw []
  \\ fs [LLENGTH_fromSeq,LLENGTH_fromList]
  THEN1
   (fs [FUN_EQ_THM] \\ rw []
    \\ first_x_assum (qspec_then `x::x'` mp_tac) \\ fs [])
  \\ fs [LNTH_fromList]
  \\ fs [LIST_EQ_REWRITE] \\ rw []
  \\ rw [FUN_EQ_THM]
  \\ first_x_assum (qspec_then `x::x'` mp_tac) \\ fs []
QED

Theorem Branch_11:
  !a1 a2 ts1 ts2. Branch a1 ts1 = Branch a2 ts2 <=> a1 = a2 /\ ts1 = ts2
Proof
  rw [Branch] \\ eq_tac \\ strip_tac \\ fs []
  \\ qspec_then `ts1` assume_tac every_ltree_rep_ok
  \\ drule ltree_rep_ok_Branch_rep
  \\ qspec_then `ts2` assume_tac every_ltree_rep_ok
  \\ drule ltree_rep_ok_Branch_rep
  \\ strip_tac \\ strip_tac
  \\ fs [ltree_abs_11]
  \\ fs [LMAP_ltree_rep_11,Branch_rep_11]
QED

(* prove cases theorem *)
Theorem Branch_rep_exists[local]:
  ltree_rep_ok f ==> ?a ts. f = Branch_rep a ts
Proof
  fs [ltree_rep_ok_def] \\ rw []
  \\ Cases_on `f []` \\ fs []
  \\ rename [`_ = (a,ts)`]
  \\ qexists_tac `a`
  \\ qexists_tac `LGENLIST (\n path. f (n::path)) ts`
  \\ fs [Branch_rep_def,FUN_EQ_THM]
  \\ Cases \\ fs [LNTH_LGENLIST]
  \\ Cases_on `f (h::t)` \\ fs []
  \\ Cases_on `ts` \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ first_x_assum drule \\ fs []
  \\ disch_then (qspecl_then [`h`,`t`] mp_tac) \\ fs []
QED

Theorem ltree_cases:
  !t. ?a ts. t = Branch a ts
Proof
  fs [Branch] \\ fs [GSYM ltree_rep_11] \\ rw []
  \\ qspec_then `ts1` assume_tac every_ltree_rep_ok
  \\ qabbrev_tac `f = ltree_rep t`
  \\ `ltree_rep_ok f` by fs [Abbr`f`]
  \\ drule Branch_rep_exists \\ rw []
  \\ qexists_tac `a` \\ qexists_tac `LMAP ltree_abs ts`
  \\ imp_res_tac ltree_rep_ok_Branch_rep_IMP
  \\ fs [LMAP_ltree_rep_ltree_abs,ltree_repabs]
QED

(* define ltree_CASE constant *)
Definition dest_Branch_rep_def:
  dest_Branch_rep (l:'a ltree_rep) =
    let (x,len) = l [] in
      (x, LGENLIST (\n path. l (n::path)) len)
End

Theorem dest_Branch_rep_Branch_rep[local]:
  dest_Branch_rep (Branch_rep x xs) = (x,xs)
Proof
  fs [Branch_rep_def,dest_Branch_rep_def]
  \\ qspec_then `xs` strip_assume_tac fromList_fromSeq \\ fs []
  \\ fs [LGENLIST_EQ_fromSeq,FUN_EQ_THM,LGENLIST_EQ_fromList]
  \\ fs [LNTH_fromList]
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM GENLIST_ID]))
  \\ fs [GENLIST_FUN_EQ,FUN_EQ_THM]
QED

Definition ltree_CASE[nocompute]:
  ltree_CASE t f =
    let (a,ts) = dest_Branch_rep (ltree_rep t) in
      f a (LMAP ltree_abs ts)
End

Theorem ltree_CASE[compute,allow_rebind]:
  ltree_CASE (Branch a ts) f = f a ts
Proof
  fs [ltree_CASE,Branch]
  \\ qspec_then `ts` assume_tac every_ltree_rep_ok
  \\ drule ltree_rep_ok_Branch_rep
  \\ fs [ltree_repabs,dest_Branch_rep_Branch_rep]
  \\ fs [LMAP_MAP] \\ rw [] \\ AP_TERM_TAC
  \\ qspec_then `ts` strip_assume_tac fromList_fromSeq
  \\ fs [LMAP_fromList,LMAP_fromSeq,FUN_EQ_THM,ltree_absrep]
  \\ rpt (pop_assum kall_tac)
  \\ Induct_on `l` \\ fs [ltree_absrep]
QED

Theorem ltree_CASE_eq:
  ltree_CASE t f = v <=> ?a ts. t = Branch a ts /\ f a ts = v
Proof
  qspec_then `t` strip_assume_tac ltree_cases \\ rw []
  \\ fs [Branch_11,ltree_CASE]
QED

Theorem ltree_CASE_elim:
  !f'. f'(ltree_CASE t f) <=> ?a ts. t = Branch a ts /\ f'(f a ts)
Proof
  qspec_then `t` strip_assume_tac ltree_cases \\ rw []
  \\ fs [Branch_11,ltree_CASE]
QED

(* ltree generator *)
Definition path_ok_def:
  path_ok path f <=>
    !xs n ys k a.
      path = xs ++ n::ys /\ f xs = (a,SOME k) ==> n < k
End

Definition make_ltree_rep_def:
  make_ltree_rep f =
    \path. if path_ok path f then f path else NOTHING
End

Theorem ltree_rep_ok_make_ltree_rep[local]:
  !f. ltree_rep_ok (make_ltree_rep f)
Proof
  fs [ltree_rep_ok_def,make_ltree_rep_def] \\ rw []
  THEN1
   (fs [AllCaseEqs()] \\ fs []
    \\ fs [path_ok_def] \\ metis_tac [])
  \\ fs [AllCaseEqs()] \\ fs []
  \\ CCONTR_TAC \\ fs [] \\ fs []
  \\ fs [path_ok_def] \\ rw []
  \\ first_x_assum (qspecl_then [`xs`,`n`,`ys ++ pos::rest`] mp_tac)
  \\ fs []
QED

Definition gen_ltree_def[nocompute]:
  gen_ltree f = ltree_abs (make_ltree_rep f)
End

Theorem gen_ltree:
  gen_ltree f =
    let (a,len) = f [] in
      Branch a (LGENLIST (\n. gen_ltree (\path. f (n::path))) len)
Proof
  fs [UNCURRY,gen_ltree_def,Branch,o_DEF]
  \\ qspec_then `f` assume_tac ltree_rep_ok_make_ltree_rep
  \\ fs [REWRITE_RULE [ltree_rep_ok_make_ltree_rep]
          (Q.SPEC `make_ltree_rep f` ltree_repabs)]
  \\ AP_TERM_TAC \\ Cases_on `f []` \\ fs []
  \\ fs [Branch_rep_def,FUN_EQ_THM]
  \\ Cases \\ fs []
  THEN1 fs [make_ltree_rep_def,path_ok_def]
  \\ Cases_on `r` \\ fs []
  \\ fs [LNTH_LGENLIST]
  THEN1
   (fs [make_ltree_rep_def]
    \\ AP_THM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ fs [path_ok_def]
    \\ rw [] \\ eq_tac \\ rw []
    THEN1
     (first_x_assum match_mp_tac
      \\ goal_assum (first_assum o mp_then.mp_then mp_then.Any mp_tac)
      \\ qexists_tac `ys` \\ fs [])
    \\ Cases_on `xs` \\ fs [] \\ rw []
    \\ metis_tac [])
  \\ fs [make_ltree_rep_def]
  \\ reverse (Cases_on `h < x`) \\ fs []
  THEN1 (rw [] \\ fs [path_ok_def] \\ metis_tac [APPEND])
  \\ AP_THM_TAC \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ fs [path_ok_def]
  \\ rw [] \\ eq_tac \\ rw []
  THEN1
   (first_x_assum match_mp_tac
    \\ goal_assum (first_assum o mp_then.mp_then mp_then.Any mp_tac)
    \\ qexists_tac `ys` \\ fs [])
  \\ Cases_on `xs` \\ fs [] \\ rw []
  \\ metis_tac []
QED

Theorem gen_ltree_LNIL:
  gen_ltree f = Branch a LNIL <=> f [] = (a, SOME 0)
Proof
  simp [Once gen_ltree,UNCURRY]
  \\ Cases_on `f []` \\ fs [Branch_11]
QED


(* ltree unfold *)
Definition make_unfold_def:
  make_unfold f seed [] =
    (let (a,seeds) = f seed in (a,LLENGTH seeds)) /\
  make_unfold f seed (n::path) =
    let (a,seeds) = f seed in
       make_unfold f (THE (LNTH n seeds)) path
End

Definition ltree_unfold:
  ltree_unfold f seed =
    gen_ltree (make_unfold f seed)
End

Theorem ltree_unfold[allow_rebind]:
  ltree_unfold f seed =
    let (a,seeds) = f seed in
      Branch a (LMAP (ltree_unfold f) seeds)
Proof
  fs [ltree_unfold]
  \\ once_rewrite_tac [gen_ltree]
  \\ simp [Once make_unfold_def]
  \\ Cases_on `f seed`
  \\ fs [Branch_11]
  \\ reverse (qspec_then `r` strip_assume_tac fromList_fromSeq)
  \\ fs [LGENLIST_EQ_fromSeq]
  THEN1
   (fs [FUN_EQ_THM,ltree_unfold] \\ rw []
    \\ AP_TERM_TAC \\ fs [FUN_EQ_THM] \\ rw []
    \\ fs [make_unfold_def])
  \\ fs [LGENLIST_EQ_fromList,LMAP_fromList]
  \\ fs [LIST_EQ_REWRITE,EL_MAP] \\ rw []
  \\ rw [ltree_unfold] \\ rw []
  \\ AP_TERM_TAC \\ fs [FUN_EQ_THM] \\ rw []
  \\ fs [make_unfold_def,LNTH_fromList]
QED

(* ltree_el returns the tree node (with the number of children) at given path *)
Definition ltree_el_def:
  ltree_el t [] =
    ltree_CASE t (\a ts. SOME (a, LLENGTH ts)) /\
  ltree_el t (n::ns) =
    ltree_CASE t (\a ts.
       case LNTH n ts of
       | NONE => NONE
       | SOME t => ltree_el t ns)
End

Theorem ltree_el_def[allow_rebind]:
  ltree_el (Branch a ts) [] = SOME (a, LLENGTH ts) /\
  ltree_el (Branch a ts) (n::ns) =
    case LNTH n ts of
    | NONE => NONE
    | SOME t => ltree_el t ns
Proof
  qspec_then `t` strip_assume_tac ltree_cases
  \\ fs [ltree_el_def,ltree_CASE]
QED

Theorem ltree_el_eqv:
  !t1 t2. t1 = t2 <=> !path. ltree_el t1 path = ltree_el t2 path
Proof
  rw [] \\ eq_tac \\ rw []
  \\ fs [GSYM ltree_rep_11,FUN_EQ_THM] \\ rw []
  \\ pop_assum mp_tac
  \\ qid_spec_tac `t1` \\ qid_spec_tac `t2`
  \\ Induct_on `x` \\ rw []
  \\ `ltree_rep_ok (ltree_rep t1) /\ ltree_rep_ok (ltree_rep t2)`
        by fs [ltree_rep_ok_ltree_rep]
  \\ qspec_then `t1` strip_assume_tac ltree_cases
  \\ qspec_then `t2` strip_assume_tac ltree_cases
  \\ rpt BasicProvers.var_eq_tac \\ simp [Branch]
  \\ `ltree_rep_ok (Branch_rep a (LMAP ltree_rep ts)) /\
      ltree_rep_ok (Branch_rep a' (LMAP ltree_rep ts'))` by
   (rw [ltree_rep_ok_Branch_rep_every]
    \\ rename [`LMAP _ ts2`]
    \\ qspec_then `ts2` strip_assume_tac fromList_fromSeq \\ fs []
    \\ fs [LMAP_fromList,every_fromList_EVERY,EVERY_MEM]
    \\ fs [MEM_MAP,PULL_EXISTS])
  \\ fs [ltree_repabs]
  \\ simp [Branch_rep_def,LLENGTH_MAP]
  \\ last_assum (qspec_then `[]` mp_tac)
  \\ rewrite_tac [ltree_el_def] \\ fs [] \\ rw []
  \\ Cases_on `LNTH h ts` \\ Cases_on `LNTH h ts'` \\ fs []
  THEN1 (qspec_then `ts` strip_assume_tac fromList_fromSeq
         \\ qspec_then `ts'` strip_assume_tac fromList_fromSeq
         \\ rw [] \\ fs [LNTH_fromList])
  THEN1 (qspec_then `ts` strip_assume_tac fromList_fromSeq
         \\ qspec_then `ts'` strip_assume_tac fromList_fromSeq
         \\ rw [] \\ fs [LNTH_fromList])
  \\ last_x_assum match_mp_tac \\ rw []
  \\ last_x_assum (qspec_then `h::path` mp_tac)
  \\ fs [ltree_el_def]
QED

Definition ltree_rel_def:
  ltree_rel R x y <=>
    !path.
      OPTREL (\x y. R (FST x) (FST y) /\ SND x = SND y)
        (ltree_el x path) (ltree_el y path)
End

Theorem ltree_rel:
  ltree_rel R (Branch a ts) (Branch b us) <=>
  R a b /\ llist_rel (ltree_rel R) ts us
Proof
  fs [ltree_rel_def,llist_rel_def] \\ rw [] \\ eq_tac \\ rw []
  THEN1 (first_x_assum (qspec_then `[]` mp_tac) \\ fs [ltree_el_def])
  THEN1 (first_x_assum (qspec_then `[]` mp_tac) \\ fs [ltree_el_def])
  THEN1 (first_x_assum (qspec_then `i::path` mp_tac) \\ fs [ltree_el_def])
  \\ Cases_on `path` \\ fs [ltree_el_def]
  \\ Cases_on `LNTH h ts` \\ fs []
  \\ Cases_on `LNTH h us` \\ fs []
  \\ qspec_then `ts` strip_assume_tac fromList_fromSeq
  \\ qspec_then `us` strip_assume_tac fromList_fromSeq
  \\ rw [] \\ fs [LNTH_fromList] \\ metis_tac []
QED

Theorem ltree_rel_eq:
  ltree_rel (=) x y <=> x = y
Proof
  fs [ltree_rel_def,ltree_el_eqv] \\ eq_tac \\ rw []
  \\ first_x_assum (qspec_then `path` mp_tac)
  \\ Cases_on `ltree_el x path` \\ Cases_on `ltree_el y path` \\ fs []
  \\ fs [UNCURRY]
  \\ rename [`FST y = FST z`]
  \\ Cases_on `y` \\ Cases_on `z` \\ fs []
QED

Theorem ltree_bisimulation:
  !t1 t2.
    t1 = t2 <=>
    ?R. R t1 t2 /\
        !a ts a' ts'.
          R (Branch a ts) (Branch a' ts') ==>
          a = a' /\ llist_rel R ts ts'
Proof
  rw [] \\ eq_tac \\ rw []
  THEN1 (qexists_tac `(=)` \\ fs [Branch_11,llist_rel_def] \\ rw [] \\ fs [])
  \\ simp [ltree_el_eqv]
  \\ strip_tac
  \\ last_x_assum mp_tac \\ qid_spec_tac `t1` \\ qid_spec_tac `t2`
  \\ Induct_on `path` \\ rw []
  \\ qspec_then `t1` strip_assume_tac ltree_cases
  \\ qspec_then `t2` strip_assume_tac ltree_cases
  \\ fs []
  THEN1 (fs [ltree_el_def] \\ res_tac \\ fs [llist_rel_def])
  \\ rw [] \\ fs [ltree_el_def]
  \\ res_tac \\ rw []
  \\ fs [llist_rel_def]
  \\ pop_assum (qspec_then `h` mp_tac)
  \\ Cases_on `LNTH h ts` \\ fs []
  \\ Cases_on `LNTH h ts'` \\ fs []
  \\ qspec_then `ts` strip_assume_tac fromList_fromSeq
  \\ qspec_then `ts'` strip_assume_tac fromList_fromSeq
  \\ rw [] \\ fs [LNTH_fromList]
QED

(* ltree_lookup returns the subtree after passing the given path, cf. ltree_el *)
Definition ltree_lookup_def:
  ltree_lookup t [] = SOME t /\
  ltree_lookup t (n::ns) =
    ltree_CASE t (\a ts.
       case LNTH n ts of
       | NONE => NONE
       | SOME t => ltree_lookup t ns)
End

Theorem ltree_lookup_def[allow_rebind]:
  ltree_lookup t [] = SOME t /\
  ltree_lookup (Branch a ts) (n::ns) =
    case LNTH n ts of
    | NONE => NONE
    | SOME t => ltree_lookup t ns
Proof
  qspec_then `t` strip_assume_tac ltree_cases
  \\ fs [ltree_lookup_def,ltree_CASE]
QED

Definition subtrees_def:
  subtrees t = { u | ?path. ltree_lookup t path = SOME u }
End

Theorem subtrees:
  subtrees (Branch a ts) =
    Branch a ts INSERT BIGUNION (IMAGE subtrees (LSET ts))
Proof
  fs [subtrees_def,Once EXTENSION,PULL_EXISTS] \\ rw []
  \\ qspec_then `x` strip_assume_tac ltree_cases
  \\ fs [Branch_11] \\ rw [] \\ reverse eq_tac \\ rw []
  THEN1 (qexists_tac `[]` \\ fs [ltree_lookup_def])
  THEN1 (fs [LSET_def,IN_DEF] \\ qexists_tac `n::path` \\ fs [ltree_lookup_def])
  \\ Cases_on `path` \\ fs []
  \\ fs [ltree_lookup_def,Branch_11]
  \\ Cases_on `LNTH h ts` \\ fs [] \\ disj2_tac
  \\ fs [LSET_def,IN_DEF,PULL_EXISTS]
  \\ rpt (goal_assum (first_assum o mp_then Any mp_tac))
QED

Definition ltree_set_def:
  ltree_set t = { a | ?ts. Branch a ts IN subtrees t }
End

Theorem ltree_set:
  ltree_set (Branch a ts) =
    a INSERT BIGUNION (IMAGE ltree_set (LSET ts))
Proof
  fs [ltree_set_def,subtrees,Once EXTENSION,Branch_11]
  \\ rw [] \\ Cases_on `a = x` \\ fs [] \\ fs [PULL_EXISTS] \\ metis_tac []
QED

Definition ltree_map_def:
  ltree_map f = ltree_unfold (\t. ltree_CASE t (\a ts. (f a,ts)))
End

Theorem ltree_map:
  ltree_map f (Branch a xs) = Branch (f a) (LMAP (ltree_map f) xs)
Proof
  fs [ltree_map_def,ltree_unfold,ltree_CASE]
QED

Theorem ltree_map_id:
  ltree_map I t = t
Proof
  fs [ltree_el_eqv] \\ qid_spec_tac `t`
  \\ Induct_on `path` \\ rw [] \\ fs [ltree_el_def]
  \\ qspec_then `t` strip_assume_tac ltree_cases
  \\ fs [ltree_map,ltree_el_def,LLENGTH_MAP]
  \\ rw [] \\ Cases_on `LNTH h ts` \\ fs []
QED

Theorem ltree_map_map:
  ltree_map f (ltree_map g t) = ltree_map (f o g) t
Proof
  fs [ltree_el_eqv] \\ qid_spec_tac `t`
  \\ Induct_on `path` \\ rw [] \\ fs [ltree_el_def]
  \\ qspec_then `t` strip_assume_tac ltree_cases
  \\ fs [ltree_map,ltree_el_def,LLENGTH_MAP]
  \\ rw [] \\ Cases_on `LNTH h ts` \\ fs []
QED

Triviality ltree_lookup_map:
  ltree_lookup (ltree_map f t) path =
  case ltree_lookup t path of
  | NONE => NONE
  | SOME t => ltree_CASE t (\a ts. SOME (Branch (f a) (LMAP (ltree_map f) ts)))
Proof
  qid_spec_tac `t` \\ Induct_on `path` \\ fs [ltree_lookup_def] \\ rw []
  \\ qspec_then `t` strip_assume_tac ltree_cases
  \\ fs [ltree_map,ltree_el_def,LLENGTH_MAP,ltree_CASE]
  \\ fs [ltree_lookup_def]
  \\ Cases_on `LNTH h ts` \\ fs []
QED

Theorem ltree_set_map:
  ltree_set (ltree_map f t) = IMAGE f (ltree_set t)
Proof
  fs [EXTENSION,ltree_set_def,subtrees_def]
  \\ fs [ltree_lookup_map,AllCaseEqs(),ltree_CASE_eq,PULL_EXISTS,Branch_11]
  \\ metis_tac []
QED

Theorem ltree_rel_O:
  ltree_rel R1 O ltree_rel R2 RSUBSET ltree_rel (R1 O R2)
Proof
  fs [ltree_rel_def,RSUBSET,O_DEF,PULL_EXISTS]
  \\ rw [] \\ rpt (first_x_assum (qspec_then `path` mp_tac)) \\ rw []
  \\ Cases_on `ltree_el x path` \\ Cases_on `ltree_el y path` \\ fs [OPTREL_def]
  \\ fs [UNCURRY] \\ metis_tac []
QED

(* update TypeBase *)
Theorem ltree_CASE_cong:
  !M M' f f'.
    M = M' /\
    (!a ts. M' = Branch a ts ==> f a ts = f' a ts) ==>
    ltree_CASE M f = ltree_CASE M' f'
Proof
  rw [] \\ qspec_then `M` strip_assume_tac ltree_cases
  \\ rw [] \\ fs [ltree_CASE]
QED

Overload "case" = “ltree_CASE”

val _ = TypeBase.export
  [TypeBasePure.mk_datatype_info
    { ax = TypeBasePure.ORIG TRUTH,
      induction = TypeBasePure.ORIG ltree_bisimulation,
      case_def = ltree_CASE,
      case_cong = ltree_CASE_cong,
      case_eq = ltree_CASE_eq,
      case_elim = ltree_CASE_elim,
      nchotomy = ltree_cases,
      size = NONE,
      encode = NONE,
      lift = NONE,
      one_one = SOME Branch_11,
      distinct = NONE,
      fields = [],
      accessors = [],
      updates = [],
      destructors = [],
      recognizers = [] } ]

Theorem datatype_ltree:
  DATATYPE ((ltree Branch):bool)
Proof
  rw [boolTheory.DATATYPE_TAG_THM]
QED

(* prove that every finite ltree is an inductively defined rose tree *)
Inductive ltree_finite:
  EVERY ltree_finite ts ==> ltree_finite (Branch a (fromList ts))
End

fun tidy_up ind = ind
  |> Q.SPEC `P` |> UNDISCH |> Q.SPEC `t` |> Q.GEN `t` |> DISCH_ALL |> Q.GEN `P`;

Theorem ltree_finite_ind[allow_rebind] = tidy_up ltree_finite_ind;
Theorem ltree_finite_strongind[allow_rebind] = tidy_up ltree_finite_strongind;

Theorem ltree_finite:
  ltree_finite (Branch a ts) <=>
  LFINITE ts /\ !t. t IN LSET ts ==> ltree_finite t
Proof
  simp [Once ltree_finite_cases]
  \\ qspec_then `ts` strip_assume_tac fromList_fromSeq
  \\ fs [IN_LSET,LNTH_fromList,PULL_EXISTS,LFINITE_fromList,EVERY_EL]
QED

(* ltree created by finite steps of unfolding is finite

   If the ltree is generated from a seed, whose resulting seeds after one-step
   unfolding is finite with smaller "measure", then there must be only finite
   steps of the unfolding process and the resulting ltree is finite.
 *)
Theorem ltree_finite_by_unfolding :
    !P f. (?(m :'a -> num).
           !seed. P seed ==>
                  let (a,seeds) = f seed in
                    LFINITE seeds /\
                    every (\e. P e /\ m e < m seed) seeds) ==>
          !seed. P seed ==> ltree_finite (ltree_unfold f seed)
Proof
    NTAC 3 STRIP_TAC
 >> measureInduct_on ‘m seed’
 >> DISCH_TAC
 >> LAST_X_ASSUM (drule o Q.SPEC ‘seed’)
 >> rw [Once ltree_unfold]
 >> qabbrev_tac ‘t = f seed’
 >> Cases_on ‘t’ >> fs []
 >> rw [Once ltree_finite, IN_LSET]
 >> FIRST_X_ASSUM irule
 >> fs [every_LNTH]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘n’ >> art []
QED

(* |- !f. (?m. !seed.
             (let
                (a,seeds) = f seed
              in
                LFINITE seeds /\ every (\e. m e < m seed) seeds)) ==>
          !seed. ltree_finite (ltree_unfold f seed)
 *)
Theorem ltree_finite_by_unfolding' =
        ltree_finite_by_unfolding |> Q.SPEC ‘\x. T’ |> SRULE []

CoInductive ltree_every :
    P a ts /\ every (ltree_every P) ts ==> (ltree_every P (Branch a ts))
End

Theorem ltree_every_rewrite[simp] :
    ltree_every P (Branch a ts) <=> P a ts /\ every (ltree_every P) ts
Proof
    SIMP_TAC std_ss [Once ltree_every_cases]
 >> EQ_TAC >> rw []
QED

Definition finite_branching_def :
    finite_branching = ltree_every (\a ts. LFINITE ts)
End

Theorem finite_branching_rules :
    !a ts. EVERY finite_branching ts ==>
           finite_branching (Branch a (fromList ts))
Proof
    rw [finite_branching_def, EVERY_MEM]
 >> qabbrev_tac ‘P = \(a :'a) (ts :'a ltree llist). LFINITE ts’
 >> rw [Once ltree_every_cases]
 >> rw [every_fromList_EVERY, EVERY_MEM]
QED

(* The "primed" version uses ‘every’ (and ‘LFINITE’) instead of ‘EVERY’ *)
Theorem finite_branching_rules' :
    !a ts. LFINITE ts /\ every finite_branching ts ==>
           finite_branching (Branch a ts)
Proof
    rw [finite_branching_def]
QED

Theorem ltree_finite_imp_finite_branching :
    !t. ltree_finite t ==> finite_branching t
Proof
    HO_MATCH_MP_TAC ltree_finite_ind
 >> rw [finite_branching_rules]
QED

(* cf. ltree_cases *)
Theorem finite_branching_cases :
    !t. finite_branching t <=>
        ?a ts. t = Branch a (fromList ts) /\ EVERY finite_branching ts
Proof
    rw [finite_branching_def, Once ltree_every_cases]
 >> EQ_TAC >> rw [LFINITE_fromList, every_fromList_EVERY]
 >> ‘?l. ts = fromList l’ by METIS_TAC [LFINITE_IMP_fromList]
 >> fs [every_fromList_EVERY]
QED

Theorem finite_branching_cases' :
    !t. finite_branching t <=>
        ?a ts. t = Branch a ts /\ LFINITE ts /\ every finite_branching ts
Proof
    rw [finite_branching_def, Once ltree_every_cases]
QED

(* |- (!a0. P a0 ==> ?a ts. a0 = Branch a ts /\ LFINITE ts /\ every P ts) ==>
      !a0. P a0 ==> finite_branching a0
 *)
val lemma = ltree_every_coind
         |> (Q.SPEC ‘\(a :'a) (ts :'a ltree llist). LFINITE ts’)
         |> (Q.SPEC ‘P’) |> BETA_RULE
         |> REWRITE_RULE [GSYM finite_branching_def];

Theorem finite_branching_coind :
    !P. (!t. P t ==> ?a ts. t = Branch a (fromList ts) /\ EVERY P ts) ==>
         !t. P t ==> finite_branching t
Proof
    NTAC 2 STRIP_TAC
 >> MATCH_MP_TAC lemma
 >> Q.X_GEN_TAC ‘t’
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!t. P t ==> _’ (drule_then STRIP_ASSUME_TAC)
 >> qexistsl_tac [‘a’, ‘fromList ts’]
 >> rw [LFINITE_fromList, every_fromList_EVERY]
QED

Theorem finite_branching_coind' :
    !P. (!t. P t ==> ?a ts. t = Branch a ts /\ LFINITE ts /\ every P ts) ==>
         !t. P t ==> finite_branching t
Proof
    NTAC 2 STRIP_TAC
 >> MATCH_MP_TAC lemma >> rw []
QED

Theorem finite_branching_rewrite[simp] :
    finite_branching (Branch a ts) <=> LFINITE ts /\ every finite_branching ts
Proof
    SIMP_TAC std_ss [finite_branching_cases]
 >> EQ_TAC >> rw []
 >- rw [LFINITE_fromList]
 >- rw [every_fromList_EVERY]
 >> ‘?l. ts = fromList l’ by METIS_TAC [LFINITE_IMP_fromList]
 >> fs [every_fromList_EVERY]
QED

(*---------------------------------------------------------------------------*
 *  More ltree operators
 *---------------------------------------------------------------------------*)

Definition ltree_node_def[simp] :
    ltree_node (Branch a ts) = a
End

Definition ltree_children_def[simp] :
    ltree_children (Branch a ts) = ts
End

Theorem ltree_node_children_reduce[simp] :
    Branch (ltree_node t) (ltree_children t) = t
Proof
   ‘?a ts. t = Branch a ts’ by METIS_TAC [ltree_cases]
 >> rw []
QED

Definition ltree_paths_def :
    ltree_paths t = {p | ltree_lookup t p <> NONE}
End

Theorem IN_ltree_paths :
    !p t. p IN ltree_paths t <=> ltree_lookup t p <> NONE
Proof
    rw [ltree_paths_def]
QED

Theorem NIL_IN_ltree_paths[simp] :
    [] IN ltree_paths t
Proof
    rw [ltree_paths_def, ltree_lookup_def]
QED

Theorem ltree_paths_inclusive :
    !l1 l2 t. l1 <<= l2 /\ l2 IN ltree_paths t ==> l1 IN ltree_paths t
Proof
    Induct_on ‘l1’
 >> rw [] (* only one goal left *)
 >> Cases_on ‘l2’ >> fs []
 >> rename1 ‘l1 <<= l2’
 >> Q.PAT_X_ASSUM ‘h = h'’ K_TAC
 >> rename1 ‘h::l1 IN ltree_paths t’
 >> POP_ASSUM MP_TAC
 >> ‘?a ts. t = Branch a ts’ by METIS_TAC [ltree_cases]
 >> POP_ORW
 >> simp [ltree_paths_def, ltree_lookup_def]
 >> Cases_on ‘LNTH h ts’ >> rw []
 >> fs [GSYM IN_ltree_paths]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘l2’ >> rw []
QED

Theorem ltree_el :
    ltree_el t [] = SOME (ltree_node t,LLENGTH (ltree_children t)) /\
    ltree_el t (n::ns) =
      case LNTH n (ltree_children t) of
        NONE => NONE
      | SOME a => ltree_el a ns
Proof
   ‘?a ts. t = Branch a ts’ by METIS_TAC [ltree_cases]
 >> simp [ltree_el_def]
QED

Theorem ltree_lookup :
    ltree_lookup t [] = SOME t /\
    ltree_lookup t (n::ns) =
      case LNTH n (ltree_children t) of
        NONE => NONE
      | SOME a => ltree_lookup a ns
Proof
   ‘?a ts. t = Branch a ts’ by METIS_TAC [ltree_cases]
 >> simp [ltree_lookup_def]
QED

Theorem ltree_lookup_iff_ltree_el[local] :
    !p t. ltree_lookup t p <> NONE <=> ltree_el t p <> NONE
Proof
    Induct_on ‘p’
 >- rw [ltree_lookup, ltree_el]
 >> rw [Once ltree_lookup, Once ltree_el]
 >> Cases_on ‘LNTH h (ltree_children t)’ >> fs []
QED

Theorem ltree_paths_alt_ltree_el :
    !t. ltree_paths t = {p | ltree_el t p <> NONE}
Proof
    rw [ltree_paths_def, Once EXTENSION, ltree_lookup_iff_ltree_el]
QED

Theorem ltree_el_valid :
    !p t. p IN ltree_paths t <=> ltree_el t p <> NONE
Proof
    rw [ltree_paths_alt_ltree_el]
QED

Theorem ltree_el_valid_inclusive :
    !p t. p IN ltree_paths t <=> !p'. p' <<= p ==> ltree_el t p' <> NONE
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC >> STRIP_TAC
 >- (POP_ASSUM (MP_TAC o (Q.SPEC ‘p’)) \\
     rw [ltree_el_valid])
 >> rw [GSYM ltree_el_valid]
 >> MATCH_MP_TAC ltree_paths_inclusive
 >> Q.EXISTS_TAC ‘p’ >> art []
QED

Theorem ltree_lookup_valid :
    !p t. p IN ltree_paths t <=> ltree_lookup t p <> NONE
Proof
    rw [ltree_lookup_iff_ltree_el, ltree_el_valid]
QED

Theorem ltree_lookup_valid_inclusive :
    !p t. p IN ltree_paths t <=> !p'. p' <<= p ==> ltree_lookup t p' <> NONE
Proof
    rw [ltree_lookup_iff_ltree_el, ltree_el_valid_inclusive]
QED

(* ltree_lookup returns more information (the entire subtree), thus can be
   used to construct the return value of ltree_el.
 *)
Theorem ltree_el_alt_ltree_lookup :
    !p t. p IN ltree_paths t ==>
          ltree_el t p =
            do
              t' <- ltree_lookup t p;
              return (ltree_node t',LLENGTH (ltree_children t'))
            od
Proof
    Induct_on ‘p’
 >- (Q.X_GEN_TAC ‘t’ \\
     STRIP_ASSUME_TAC (Q.SPEC ‘t’ ltree_cases) >> POP_ORW \\
     rw [ltree_el_def, ltree_lookup_def])
 >> qx_genl_tac [‘h’, ‘t’]
 >> STRIP_ASSUME_TAC (Q.SPEC ‘t’ ltree_cases) >> POP_ORW
 >> fs [ltree_paths_def]
 >> rw [ltree_el_def, ltree_lookup_def]
 >> qabbrev_tac ‘t' = LNTH h ts’
 >> Cases_on ‘t' = NONE’ >- rw []
 >> gs [GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
QED

Theorem ltree_paths_map_cong[simp] :
    !f t. ltree_paths (ltree_map f t) = ltree_paths t
Proof
    rw [ltree_paths_def, Once EXTENSION]
 >> Q.ID_SPEC_TAC ‘t’
 >> Q.SPEC_TAC (‘x’, ‘p’)
 >> Induct_on ‘p’
 >- rw [ltree_lookup_def]
 >> rpt GEN_TAC
 >> Cases_on ‘t’
 >> rw [ltree_lookup_def, ltree_map]
 >> Cases_on ‘LNTH h ts’ >> rw []
QED

Theorem ltree_lookup_append :
    !l1 l2 t. ltree_lookup t l1 <> NONE ==>
              ltree_lookup t (l1 ++ l2) =
              ltree_lookup (THE (ltree_lookup t l1)) l2
Proof
    Induct_on ‘l1’
 >- rw [ltree_lookup_def]
 >> rpt GEN_TAC
 >> ‘h::l1 ++ l2 = h::(l1 ++ l2)’ by rw [] >> POP_ORW
 >> Cases_on ‘t’ >> simp [ltree_lookup_def]
 >> Cases_on ‘LNTH h ts’ >> simp []
QED

Theorem ltree_lookup_SNOC :
    !t x xs. ltree_lookup t xs <> NONE ==>
             ltree_lookup t (SNOC x xs) =
             ltree_lookup (THE (ltree_lookup t xs)) [x]
Proof
    rpt STRIP_TAC
 >> ‘SNOC x xs = xs ++ [x]’ by rw [] >> POP_ORW
 >> MATCH_MP_TAC ltree_lookup_append >> art []
QED

Theorem gen_ltree_unchanged :
    !t. gen_ltree (\p. THE (ltree_el t p)) = t
Proof
    Q.X_GEN_TAC ‘t’
 >> rw [ltree_bisimulation]
 >> Q.EXISTS_TAC ‘\x y. x = gen_ltree (\p. THE (ltree_el y p))’
 >> simp []
 >> rpt STRIP_TAC
 >- fs [Once gen_ltree, ltree_el_def]
 >> rw [llist_rel_def]
 >- fs [Once gen_ltree, ltree_el_def]
 >> fs [Once gen_ltree, ltree_el_def, LNTH_EQ, LNTH_LGENLIST]
 >> Q.PAT_X_ASSUM ‘!n. P’ (MP_TAC o Q.SPEC ‘i’)
 >> simp []
 >> Cases_on ‘y’ >> simp [ltree_el_def]
 >> Cases_on ‘LLENGTH ts'’ >> simp []
 >- (DISCH_THEN (fs o wrap) \\
     simp [Once gen_ltree, ltree_el_def])
 >> rw []
 >> simp [Once gen_ltree, ltree_el_def]
QED

Theorem gen_ltree_unchanged_extra :
    !t f. gen_ltree (\p. if ltree_el t p <> NONE then THE (ltree_el t p)
                         else f p) = t
Proof
    rw [ltree_bisimulation]
 >> Q.EXISTS_TAC ‘\x y. ?f. x = gen_ltree (\p. if ltree_el y p <> NONE then
                                                 THE (ltree_el y p)
                                               else f p)’
 >> CONJ_TAC
 >- (simp [] >> Q.EXISTS_TAC ‘f’ >> simp [])
 >> rpt STRIP_TAC
 >- fs [Once gen_ltree, ltree_el_def]
 >> rw [llist_rel_def]
 >- fs [Once gen_ltree, ltree_el_def]
 >> fs [Once gen_ltree, ltree_el_def, LNTH_EQ, LNTH_LGENLIST]
 >> Q.PAT_X_ASSUM ‘!n. P’ (MP_TAC o Q.SPEC ‘i’)
 >> simp []
 >> Cases_on ‘y’ >> simp [ltree_el_def]
 >> Cases_on ‘LLENGTH ts'’ >> simp []
 >- (DISCH_THEN (fs o wrap) \\
     simp [Once gen_ltree, ltree_el_def] \\
     Q.EXISTS_TAC ‘\p. f (i::p)’ >> simp [])
 >> rw []
 >> simp [Once gen_ltree, ltree_el_def]
 >> Q.EXISTS_TAC ‘\p. f (i::p)’ >> simp []
QED

Theorem ltree_el_lemma[local] :
    !path. (\(d,len). (d,len)) (THE (ltree_el x path)) = THE (ltree_el x path)
Proof
    rw [FUN_EQ_THM]
 >> qabbrev_tac ‘t0 = THE (ltree_el x path)’
 >> Cases_on ‘t0’ >> simp []
QED

(* This is the number of children at certain ltree node (NONE means infinite).
   NOTE: It makes the statements of the [ltree_insert_delete], slightly nicer.
 *)
Definition ltree_branching_def :
    ltree_branching t p = SND (THE (ltree_el t p))
End

Theorem ltree_branching_alt_ltree_lookup :
    !p t. p IN ltree_paths t ==>
          ltree_branching t p = LLENGTH (ltree_children (THE (ltree_lookup t p)))
Proof
    Induct_on ‘p’
 >- rw [ltree_branching_def, ltree_el, ltree_lookup]
 >> rpt STRIP_TAC
 >> ‘ltree_lookup t (h::p) <> NONE’ by fs [ltree_paths_def]
 >> ‘ltree_el     t (h::p) <> NONE’ by fs [ltree_paths_alt_ltree_el]
 >> Cases_on ‘t’
 >> fs [ltree_branching_def, ltree_el, ltree_lookup]
 >> qabbrev_tac ‘t0 = LNTH h ts’
 >> Cases_on ‘t0’ >> fs []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> rw [ltree_paths_def]
QED

Theorem ltree_branching_NIL :
    !a ts. ltree_branching (Branch a ts) [] = LLENGTH ts
Proof
    rw [ltree_branching_def, ltree_el_def]
QED

Theorem ltree_branching_CONS :
    !h p a ts. h::p IN ltree_paths (Branch a ts) ==>
               ltree_branching (Branch a ts) (h::p) =
               ltree_branching (THE (LNTH h ts)) p
Proof
    rpt GEN_TAC
 >> rw [ltree_paths_alt_ltree_el, ltree_el_def, ltree_branching_def]
 >> Cases_on ‘LNTH h ts’ >> fs []
QED

Theorem ltree_branching_ltree_paths :
    !p t m. p IN ltree_paths t /\ ltree_branching t p = SOME m ==>
            !h. h < m <=> SNOC h p IN ltree_paths t
Proof
    Induct_on ‘p’
 >- (rpt GEN_TAC \\
     Cases_on ‘t’ \\
     rw [ltree_el_def, ltree_branching_NIL, ltree_paths_alt_ltree_el] \\
     Cases_on ‘LNTH h ts’ >> simp [ltree_el] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
      ‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
       Know ‘~IS_SOME (LNTH h ts)’ >- rw [IS_SOME_EQ_NOT_NONE] \\
       ASM_SIMP_TAC bool_ss [LFINITE_LNTH_IS_SOME] \\
       simp [],
       (* goal 2 (of 2) *)
      ‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
       Know ‘IS_SOME (LNTH h ts)’ >- rw [IS_SOME_EXISTS] \\
       ASM_SIMP_TAC bool_ss [LFINITE_LNTH_IS_SOME] \\
       simp [] ])
 >> rpt STRIP_TAC
 >> Cases_on ‘t’
 >> POP_ASSUM MP_TAC
 >> simp [ltree_branching_CONS]
 >> POP_ASSUM MP_TAC
 >> simp [ltree_paths_alt_ltree_el, ltree_el_def]
 >> Cases_on ‘LNTH h ts’ >> simp []
 >> rpt STRIP_TAC
 >> fs [ltree_paths_alt_ltree_el]
QED

(*---------------------------------------------------------------------------*
 *  ltree_delete: delete the rightmost children at a subtree
 *---------------------------------------------------------------------------*)

(* NOTE: Here p is the path of the parent node whose rightmost children node
   is going to be deleted. f can be used to update the parent node for the
   removal of rightmost child (subtree), otherwise use I.
 *)
Definition ltree_delete_def :
    ltree_delete f t p =
    gen_ltree (\ns. let (d,len) = THE (ltree_el t ns); m = THE len in
                    if ns = p /\ len <> NONE /\ 0 < m then
                      (f d,SOME (m - 1))
                    else
                      (d,len))
End
Overload ltree_delete' = “ltree_delete I”

Theorem ltree_delete_NIL :
    !f a ts.
         ltree_delete f (Branch a ts) [] =
         if LFINITE ts /\ 0 < THE (LLENGTH ts) then
            Branch (f a)
               (LGENLIST (\i. THE (LNTH i ts)) (SOME (THE (LLENGTH ts) - 1)))
         else
            Branch a ts
Proof
    rw [ltree_delete_def]
 >- (rw [Once gen_ltree, ltree_el_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       rw [LNTH_EQ, LNTH_LGENLIST] \\
       gs [LFINITE_LLENGTH] \\
       rename1 ‘0 < N’ \\
       Cases_on ‘n < N - 1’ >> simp [] \\
      ‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
       Know ‘IS_SOME (LNTH n ts)’ >- rw [LFINITE_LNTH_IS_SOME] \\
       rw [IS_SOME_EXISTS] >> simp [] \\
       rw [ltree_el_lemma, gen_ltree_unchanged],
       (* goal 2 (of 3) *)
       gs [LFINITE_LLENGTH],
       (* goal 3 (of 3) *)
       gs [LFINITE_LLENGTH] ])
 >> fs [] (* 2 subgoals *)
 >| [ (* goal 1 (of 2) *)
      rw [Once gen_ltree, ltree_el_def]
      >- (Cases_on ‘LLENGTH ts’ >> fs [LFINITE_LLENGTH])
      >- (Cases_on ‘LLENGTH ts’ >> fs [LFINITE_LLENGTH]) \\
      POP_ASSUM K_TAC \\
      rw [LNTH_EQ, LNTH_LGENLIST] \\
     ‘!n. ?x. LNTH n ts = SOME x’ by METIS_TAC [infinite_lnth_some] \\
      POP_ASSUM (MP_TAC o Q.SPEC ‘n’) >> rw [] \\
      simp [] \\
      fs [LFINITE_LLENGTH] \\
      Cases_on ‘LLENGTH ts’ >> fs [] \\
      Know ‘!path. (\(d,len). (d,len)) (THE (ltree_el x path)) =
                   THE (ltree_el x path)’
      >- (rw [FUN_EQ_THM] \\
          qabbrev_tac ‘t0 = THE (ltree_el x path)’ \\
          Cases_on ‘t0’ >> simp []) >> Rewr' \\
      rw [gen_ltree_unchanged],
      (* goal 2 (of 2) *)
      rw [Once gen_ltree, ltree_el_def] \\
      rw [LNTH_EQ, LNTH_LGENLIST] \\
      Cases_on ‘LLENGTH ts’ >> simp []
      >- (‘~LFINITE ts’ by rw [LFINITE_LLENGTH] \\
          ‘!n. ?x. LNTH n ts = SOME x’ by METIS_TAC [infinite_lnth_some] \\
          POP_ASSUM (MP_TAC o Q.SPEC ‘n’) >> rw [] \\
          simp [] \\
          rw [ltree_el_lemma, gen_ltree_unchanged]) \\
     ‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
      rename1 ‘LLENGTH ts = SOME N’ \\
      rfs [] ]
QED

Theorem ltree_delete_CONS :
    !f a ts h p t.
         LNTH h ts = SOME t /\ ltree_el t p <> NONE ==>
         ltree_delete f (Branch a ts) (h::p) =
         Branch a (LGENLIST (\i. if i = h then
                                     ltree_delete f (THE (LNTH h ts)) p
                                 else
                                     THE (LNTH i ts))
                            (LLENGTH ts))
Proof
    rpt STRIP_TAC
 >> rw [Once ltree_delete_def]
 >> rw [Once gen_ltree, ltree_el_def]
 >> rw [LNTH_EQ, LNTH_LGENLIST]
 >> Cases_on ‘LLENGTH ts’ >> simp []
 >- (Cases_on ‘n = h’ >> simp []
     >- rw [ltree_delete_def] \\
     Know ‘~LFINITE ts’ >- rw [LFINITE_LLENGTH] \\
     rw [infinite_lnth_some] \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘n’) >> rw [] \\
     simp [] \\
     Know ‘!path. (\(d,len). (d,len)) (THE (ltree_el x path)) =
                  THE (ltree_el x path)’
     >- (rw [FUN_EQ_THM] \\
         qabbrev_tac ‘t0 = THE (ltree_el x path)’ \\
         Cases_on ‘t0’ >> simp []) >> Rewr' \\
     rw [gen_ltree_unchanged])
 >> Cases_on ‘n < x’ >> simp []
 >> Cases_on ‘n = h’ >> simp []
 >- rw [ltree_delete_def]
 >> Know ‘IS_SOME (LNTH n ts)’ >- rw [LNTH_IS_SOME]
 >> rw [IS_SOME_EXISTS]
 >> simp []
 >> Know ‘!path. (\(d,len). (d,len)) (THE (ltree_el x' path)) =
                 THE (ltree_el x' path)’
 >- (rw [FUN_EQ_THM] \\
     qabbrev_tac ‘t0 = THE (ltree_el x' path)’ \\
     Cases_on ‘t0’ >> simp [])
 >> Rewr'
 >> rw [gen_ltree_unchanged]
QED

(* NOTE: “ltree_delete” does not remove the parent branch no matter what *)
Theorem ltree_delete_path_stable :
    !f p t. p IN ltree_paths t ==> p IN ltree_paths (ltree_delete f t p)
Proof
    Q.X_GEN_TAC ‘f’
 >> Induct_on ‘p’ >- rw []
 >> rpt STRIP_TAC
 >> fs [ltree_paths_alt_ltree_el]
 >> POP_ASSUM MP_TAC
 >> Cases_on ‘t’ >> simp [ltree_el_def]
 >> Cases_on ‘LNTH h ts’ >> simp []
 >> STRIP_TAC
 (* applying ltree_delete_CONS *)
 >> MP_TAC (Q.SPECL [‘f’, ‘a’, ‘ts’, ‘h’, ‘p’, ‘x’] ltree_delete_CONS)
 >> simp []
 >> DISCH_THEN K_TAC
 >> rw [ltree_el_def, LNTH_LGENLIST]
 >> Cases_on ‘LLENGTH ts’ >> simp []
 >> rename1 ‘LLENGTH ts = SOME n’
 >> Know ‘IS_SOME (LNTH h ts)’ >- rw [IS_SOME_EXISTS]
 >> rw [LNTH_IS_SOME, LFINITE_LLENGTH]
QED

Theorem ltree_el_ltree_delete :
    !f p t. ltree_el t p = SOME (a,SOME (SUC n)) ==>
            ltree_el (ltree_delete f t p) p = SOME (f a,SOME n)
Proof
    Q.X_GEN_TAC ‘f’
 >> Induct_on ‘p’
 >- (rpt STRIP_TAC \\
     Cases_on ‘t’ >> fs [ltree_el_def, ltree_delete_NIL] \\
    ‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
     simp [ltree_el_def])
 >> rpt STRIP_TAC
 >> Cases_on ‘t’ >> fs [ltree_el_def]
 >> Cases_on ‘LNTH h ts’ >> fs []
 >> MP_TAC (Q.SPECL [‘f’, ‘a'’, ‘ts’, ‘h’, ‘p’, ‘x’] ltree_delete_CONS)
 >> simp []
 >> DISCH_THEN K_TAC
 >> rw [ltree_el_def, LNTH_LGENLIST]
 >> Cases_on ‘LLENGTH ts’ >> simp []
 >> rename1 ‘LLENGTH ts = SOME N’
 >> Know ‘IS_SOME (LNTH h ts)’ >- rw [IS_SOME_EXISTS]
 >> rw [LNTH_IS_SOME, LFINITE_LLENGTH]
QED

(* |- !p t.
        ltree_el t p = SOME (a,SOME (SUC n)) ==>
        ltree_el (ltree_delete' t p) p = SOME (a,SOME n)
 *)
Theorem ltree_el_ltree_delete' =
        ltree_el_ltree_delete |> Q.SPEC ‘I’ |> SRULE []

(* NOTE: “ltree_el t p = SOME (a,SOME (SUC n)” indicates that “SNOC n p” is the
   subtree to be deleted.
 *)
Theorem ltree_delete_paths_lemma[local] :
    !f p t a n.
       ltree_el t p = SOME (a,SOME (SUC n)) ==>
       ltree_paths (ltree_delete f t p) =
       ltree_paths t DIFF
         (IMAGE (\q. SNOC n p ++ q) (ltree_paths (THE (ltree_lookup t (SNOC n p)))))
Proof
    Q.X_GEN_TAC ‘f’
 >> Induct_on ‘p’
 >- (rw [ltree_paths_alt_ltree_el] \\
     Cases_on ‘t’ \\
     fs [ltree_el_def, ltree_lookup_def] \\
     Q.PAT_X_ASSUM ‘a' = a’ K_TAC \\
    ‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
     MP_TAC (Q.SPECL [‘f’, ‘a’, ‘ts’] ltree_delete_NIL) >> simp [] \\
     DISCH_THEN K_TAC \\
     rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       Cases_on ‘x’ >> fs [ltree_el_def, LNTH_LGENLIST] \\
       Cases_on ‘LNTH h ts’ >> simp []
       >- (Know ‘~IS_SOME (LNTH h ts)’ >- rw [] \\
           rw [LFINITE_LNTH_IS_SOME] \\
           CCONTR_TAC \\
          ‘~(h < n)’ by rw [] \\
           fs []) \\
       Cases_on ‘h < n’ >> fs [],
       (* goal 2 (of 3) *)
       fs [ltree_el_def, LNTH_LGENLIST],
       (* goal 3 (of 3) *)
       Cases_on ‘x’ >> fs [ltree_el_def, LNTH_LGENLIST] \\
       Cases_on ‘h < n’ >> simp []
       >- (Know ‘IS_SOME (LNTH h ts)’ >- rw [LFINITE_LNTH_IS_SOME] \\
           rw [IS_SOME_EXISTS] \\
           POP_ASSUM (fs o wrap)) \\
      ‘n <= h’ by rw [] \\
      ‘SUC n <= h \/ h = n’ by rw []
       >- (Know ‘~IS_SOME (LNTH h ts)’
           >- (ASM_SIMP_TAC bool_ss [LFINITE_LNTH_IS_SOME] \\
               simp []) >> DISCH_TAC \\
           fs []) \\
       POP_ASSUM (fs o wrap) \\
       Cases_on ‘LNTH n ts’ >> fs [] ])
 (* stage work *)
 >> rpt STRIP_TAC
 >> ‘!q. SNOC n (h::p) ++ q = h::(SNOC n p ++ q)’ by rw []
 >> POP_ORW
 >> ‘SNOC n (h::p) = h::SNOC n p’ by rw []
 >> POP_ORW
 >> Cases_on ‘t’
 >> POP_ASSUM MP_TAC
 >> simp [ltree_el_def, ltree_lookup_def]
 >> Cases_on ‘LNTH h ts’ >> simp []
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘f’, ‘a'’, ‘ts’, ‘h’, ‘p’, ‘x’] ltree_delete_CONS)
 >> simp []
 >> DISCH_THEN K_TAC
 >> simp [Once ltree_paths_alt_ltree_el]
 >> simp [Once EXTENSION]
 >> Q.X_GEN_TAC ‘ns’
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 3) *)
      Cases_on ‘ns’ >> fs [ltree_el_def, LNTH_LGENLIST] \\
      POP_ASSUM MP_TAC \\
      Cases_on ‘LLENGTH ts’ >> simp []
      >- (Cases_on ‘h' = h’ >> simp []
          >- (POP_ASSUM K_TAC \\
              DISCH_TAC \\
              Know ‘t IN ltree_paths (ltree_delete f x p)’
              >- rw [ltree_paths_alt_ltree_el] \\
              Q.PAT_X_ASSUM ‘!t a n. P’ (MP_TAC o Q.SPECL [‘x’, ‘a’, ‘n’]) \\
              simp [] >> DISCH_THEN K_TAC \\
              rw [ltree_paths_alt_ltree_el, ltree_el_def]) \\
          rw [ltree_paths_alt_ltree_el, ltree_el_def] \\
          Cases_on ‘LNTH h' ts’ >> simp []
          >- (Know ‘~LFINITE ts’ >- rw [LFINITE_LLENGTH] \\
              DISCH_TAC \\
              fs [infinite_lnth_some] \\
              POP_ASSUM (MP_TAC o Q.SPEC ‘h'’) >> rw []) \\
          fs []) \\
      rename1 ‘LLENGTH ts = SOME N’ \\
      Cases_on ‘h' < N’ >> simp [] \\
      Cases_on ‘h' = h’ >> simp []
      >- (POP_ASSUM (fs o wrap) \\
          DISCH_TAC \\
          Know ‘t IN ltree_paths (ltree_delete f x p)’
          >- rw [ltree_paths_alt_ltree_el] \\
          Q.PAT_X_ASSUM ‘!t a n. P’ (MP_TAC o Q.SPECL [‘x’, ‘a’, ‘n’]) \\
          simp [] >> DISCH_THEN K_TAC \\
          rw [ltree_paths_alt_ltree_el, ltree_el_def]) \\
      rw [ltree_paths_alt_ltree_el, ltree_el_def] \\
      Cases_on ‘LNTH h' ts’ >> simp []
      >- (‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
          Know ‘IS_SOME (LNTH h' ts)’ >- rw [LFINITE_LNTH_IS_SOME] \\
          rw [IS_SOME_EXISTS]) \\
      fs [],
      (* goal 2 (of 3) *)
      POP_ASSUM MP_TAC \\
      simp [ltree_el_def, LNTH_LGENLIST] \\
      Cases_on ‘LLENGTH ts’ >> simp []
      >- (DISCH_TAC \\
          Know ‘p ++ [n] ++ q IN ltree_paths (ltree_delete f x p)’
          >- rw [ltree_paths_alt_ltree_el] \\
          Q.PAT_X_ASSUM ‘!t a n. P’ (MP_TAC o Q.SPECL [‘x’, ‘a’, ‘n’]) \\
          simp []) \\
      rename1 ‘LLENGTH ts = SOME N’ \\
      Cases_on ‘h < N’ >> simp [] \\
      DISCH_TAC \\
      Know ‘p ++ [n] ++ q IN ltree_paths (ltree_delete f x p)’
      >- rw [ltree_paths_alt_ltree_el] \\
      Q.PAT_X_ASSUM ‘!t a n. P’ (MP_TAC o Q.SPECL [‘x’, ‘a’, ‘n’]) \\
      simp [],
      (* goal 3 (of 3) *)
      Cases_on ‘ns’ >> fs []
      >- (simp [ltree_el_def, LNTH_LGENLIST]) \\
      simp [ltree_el_def, LNTH_LGENLIST] \\
      Cases_on ‘LLENGTH ts’ >> simp []
      >- (Cases_on ‘h' = h’ >> simp []
          >- (POP_ASSUM (fs o wrap) \\
              Know ‘ltree_el (ltree_delete f x p) t <> NONE <=>
                    t IN ltree_paths (ltree_delete f x p)’
              >- rw [ltree_paths_alt_ltree_el] >> Rewr' \\
              Q.PAT_X_ASSUM ‘!t a n. P’ (MP_TAC o Q.SPECL [‘x’, ‘a’, ‘n’]) \\
              simp [] >> DISCH_THEN K_TAC \\
              Q.PAT_X_ASSUM ‘h::t IN ltree_paths (Branch a' ts)’ MP_TAC \\
              simp [ltree_paths_alt_ltree_el, ltree_el_def]) \\
          fs [] \\
          Q.PAT_X_ASSUM ‘h'::t IN ltree_paths (Branch a' ts)’ MP_TAC \\
          simp [ltree_paths_alt_ltree_el, ltree_el_def] \\
          Cases_on ‘LNTH h' ts’ >> simp []) \\
      rename1 ‘LLENGTH ts = SOME N’ \\
      Cases_on ‘h' < N’ >> simp []
      >- (Cases_on ‘h' = h’ >> simp []
          >- (POP_ASSUM (fs o wrap) \\
              Know ‘ltree_el (ltree_delete f x p) t <> NONE <=>
                    t IN ltree_paths (ltree_delete f x p)’
              >- rw [ltree_paths_alt_ltree_el] >> Rewr' \\
              Q.PAT_X_ASSUM ‘!t a n. P’ (MP_TAC o Q.SPECL [‘x’, ‘a’, ‘n’]) \\
              simp [] >> DISCH_THEN K_TAC \\
              Q.PAT_X_ASSUM ‘h::t IN ltree_paths (Branch a' ts)’ MP_TAC \\
              rw [ltree_paths_alt_ltree_el, ltree_el_def]) \\
          fs [] \\
          Q.PAT_X_ASSUM ‘h'::t IN ltree_paths (Branch a' ts)’ MP_TAC \\
          simp [ltree_paths_alt_ltree_el, ltree_el_def] \\
          Cases_on ‘LNTH h' ts’ >> simp []) \\
     ‘N <= h'’ by rw [] \\
      Q.PAT_X_ASSUM ‘h'::t IN ltree_paths (Branch a' ts)’ MP_TAC \\
      simp [ltree_paths_alt_ltree_el, ltree_el_def] \\
      Cases_on ‘LNTH h' ts’ >> simp [] \\
     ‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
      Know ‘IS_SOME (LNTH h' ts)’ >- rw [IS_SOME_EXISTS] \\
      simp [LFINITE_LNTH_IS_SOME] ]
QED

Theorem ltree_delete_paths :
    !f p t n.
       p IN ltree_paths t /\ ltree_branching t p = SOME (SUC n) ==>
       ltree_paths (ltree_delete f t p) =
       ltree_paths t DIFF
       IMAGE (\q. SNOC n p ++ q) (ltree_paths (THE (ltree_lookup t (SNOC n p))))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC ltree_delete_paths_lemma
 >> Cases_on ‘t’
 >> fs [ltree_paths_alt_ltree_el, ltree_branching_def]
 >> Cases_on ‘p’ >> fs [ltree_el_def]
 >> Cases_on ‘LNTH h ts’ >> fs []
 >> Cases_on ‘ltree_el x t’ >> fs []
 >> rename1 ‘SND y = SOME (SUC n)’
 >> Cases_on ‘y’ >> fs []
QED

(* NOTE: “ltree_insert f t p t0” inserts t0 as the right-most children of the
   ltree node “ltree_lookup t p”.
 *)
Definition ltree_insert_def :
    ltree_insert f t p t0 =
    gen_ltree (\ns. if ltree_el t ns <> NONE then
                       let (d,len) = THE (ltree_el t ns); m = THE len in
                       if ns = p /\ len <> NONE then
                         (f d,SOME (m + 1))
                       else
                         (d,len)
                    else
                       THE (ltree_el t0 (DROP (LENGTH p + 1) ns)))
End
Overload ltree_insert' = “ltree_insert I”

Theorem ltree_insert_NIL :
    !f a ts t0.
         ltree_insert f (Branch a ts) [] t0 =
         if LFINITE ts then
            Branch (f a)
               (LGENLIST (\i. if i < THE (LLENGTH ts) then THE (LNTH i ts)
                              else t0)
                         (SOME (THE (LLENGTH ts) + 1)))
         else
            Branch a ts
Proof
    rw [ltree_insert_def]
 >- (rw [Once gen_ltree, ltree_el_def] >| (* 3 subgoals *)
     [ (* goal 1 (of 3) *)
       rw [LNTH_EQ, LNTH_LGENLIST] \\
       gs [LFINITE_LLENGTH] \\
       rename1 ‘LLENGTH ts = SOME N’ \\
       Cases_on ‘n < N + 1’ >> simp [] \\
      ‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
       Cases_on ‘LNTH n ts’ >> simp []
       >- (Know ‘~IS_SOME (LNTH n ts)’ >- rw [] \\
           POP_ASSUM K_TAC \\
           ASM_SIMP_TAC bool_ss [LFINITE_LNTH_IS_SOME] \\
           simp [] \\
           rw [gen_ltree_unchanged]) \\
       Know ‘IS_SOME (LNTH n ts)’ >- rw [] \\
       rw [LFINITE_LNTH_IS_SOME] \\
       simp [ltree_el_lemma] \\
       rw [gen_ltree_unchanged_extra],
       (* goal 2 (of 3) *)
       gs [LFINITE_LLENGTH],
       (* goal 3 (of 3) *)
       gs [LFINITE_LLENGTH] ])
 >> rw [Once gen_ltree, ltree_el_def]
 >- (Cases_on ‘LLENGTH ts’ >> fs [LFINITE_LLENGTH])
 >- (Cases_on ‘LLENGTH ts’ >> fs [LFINITE_LLENGTH])
 >> rw [LNTH_EQ, LNTH_LGENLIST]
 >> ‘!n. ?x. LNTH n ts = SOME x’ by METIS_TAC [infinite_lnth_some]
 >> POP_ASSUM (MP_TAC o Q.SPEC ‘n’) >> rw []
 >> simp []
 >> simp [ltree_el_lemma]
 >> rw [gen_ltree_unchanged_extra]
QED

Theorem ltree_insert_CONS :
    !f a ts h p t t0.
         LNTH h ts = SOME t /\ ltree_el t p <> NONE ==>
         ltree_insert f (Branch a ts) (h::p) t0 =
         Branch a (LGENLIST (\i. if i = h then
                                     ltree_insert f (THE (LNTH h ts)) p t0
                                 else
                                     THE (LNTH i ts))
                            (LLENGTH ts))
Proof
    rpt STRIP_TAC
 >> rw [Once ltree_insert_def]
 >> rw [Once gen_ltree, ltree_el_def]
 >> rw [LNTH_EQ, LNTH_LGENLIST]
 >> Cases_on ‘LLENGTH ts’ >> simp []
 >- (Cases_on ‘n = h’ >> simp []
     >- rw [ltree_insert_def, ADD1] \\
     Know ‘~LFINITE ts’ >- rw [LFINITE_LLENGTH] \\
     rw [infinite_lnth_some] \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘n’) >> rw [] \\
     simp [] \\
     Know ‘!path. (\(d,len). (d,len)) (THE (ltree_el x path)) =
                  THE (ltree_el x path)’
     >- (rw [FUN_EQ_THM] \\
         qabbrev_tac ‘t0 = THE (ltree_el x path)’ \\
         Cases_on ‘t0’ >> simp []) >> Rewr' \\
     rw [gen_ltree_unchanged_extra])
 >> Cases_on ‘n < x’ >> simp []
 >> Cases_on ‘n = h’ >> simp []
 >- rw [ltree_insert_def, ADD1]
 >> Know ‘IS_SOME (LNTH n ts)’ >- rw [LNTH_IS_SOME]
 >> rw [IS_SOME_EXISTS]
 >> simp []
 >> Know ‘!path. (\(d,len). (d,len)) (THE (ltree_el x' path)) =
                 THE (ltree_el x' path)’
 >- (rw [FUN_EQ_THM] \\
     qabbrev_tac ‘t0 = THE (ltree_el x' path)’ \\
     Cases_on ‘t0’ >> simp [])
 >> Rewr'
 >> rw [gen_ltree_unchanged_extra]
QED

Theorem ltree_finite_ltree_insert_lemma[local] :
    !f p t t0 d len.
       ltree_finite t /\ ltree_el t p = SOME (d,len) /\
       ltree_finite t0 ==> ltree_finite (ltree_insert f t p t0)
Proof
    Q.X_GEN_TAC ‘f’
 >> Induct_on ‘p’
 >- (rw [ltree_el] \\
     Cases_on ‘t’ >> rw [ltree_insert_NIL] \\
     rw [ltree_finite, IN_LSET, LNTH_LGENLIST] \\
     gs [LFINITE_LLENGTH] \\
     rename1 ‘n < N + 1’ \\
     Cases_on ‘n < N’ >> simp [] \\
    ‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
     Know ‘IS_SOME (LNTH n ts)’ >- rw [LFINITE_LNTH_IS_SOME] \\
     rw [IS_SOME_EXISTS] \\
     simp [] \\
     Q.PAT_X_ASSUM ‘ltree_finite (Branch a ts)’
        (MP_TAC o REWRITE_RULE [ltree_finite]) \\
     rw [IN_LSET] \\
     POP_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘n’ >> art [])
 >> rpt STRIP_TAC
 >> Cases_on ‘t’ >> fs [ltree_el_def]
 >> Cases_on ‘LNTH h ts’ >> fs []
 >> MP_TAC (Q.SPECL [‘f’, ‘a’, ‘ts’, ‘h’, ‘p’, ‘x’, ‘t0’] ltree_insert_CONS)
 >> simp []
 >> DISCH_THEN K_TAC
 >> rw [ltree_finite, IN_LSET, LNTH_LGENLIST]
 >- (Q.PAT_X_ASSUM ‘ltree_finite (Branch a ts)’
       (MP_TAC o REWRITE_RULE [ltree_finite]) \\
     rw [LFINITE_LLENGTH, IN_LSET, GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS])
 >> Q.PAT_X_ASSUM ‘ltree_finite (Branch a ts)’
       (MP_TAC o REWRITE_RULE [ltree_finite])
 >> rw [LFINITE_LLENGTH, IN_LSET, GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
 >> rename1 ‘LLENGTH ts = SOME N’
 >> fs []
 >> Cases_on ‘n = h’ >> fs []
 >- (Q.PAT_X_ASSUM ‘ltree_insert f x p t0 = t’ (REWRITE_TAC o wrap o SYM) \\
     LAST_X_ASSUM MATCH_MP_TAC >> art [] \\
     qexistsl_tac [‘d’, ‘len’] >> art [] \\
     FIRST_X_ASSUM MATCH_MP_TAC \\
     Q.EXISTS_TAC ‘h’ >> art [])
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘n’ >> simp []
 >> ‘LFINITE ts’ by rw [LFINITE_LLENGTH]
 >> Know ‘IS_SOME (LNTH n ts)’ >- rw [LFINITE_LNTH_IS_SOME]
 >> rw [IS_SOME_EXISTS]
 >> simp []
QED

Theorem ltree_finite_ltree_insert :
    !f p t t0.
       ltree_finite t /\ p IN ltree_paths t /\ ltree_finite t0 ==>
       ltree_finite (ltree_insert f t p t0)
Proof
    rw [ltree_paths_alt_ltree_el, GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
 >> rename1 ‘ltree_el t p = SOME y’
 >> Cases_on ‘y’
 >> MATCH_MP_TAC ltree_finite_ltree_insert_lemma
 >> qexistsl_tac [‘q’, ‘r’] >> art []
QED

Theorem ltree_insert_path_stable :
    !f p t t0. p IN ltree_paths t ==> p IN ltree_paths (ltree_insert f t p t0)
Proof
    Q.X_GEN_TAC ‘f’
 >> Induct_on ‘p’ >- rw []
 >> rpt STRIP_TAC
 >> fs [ltree_paths_alt_ltree_el]
 >> POP_ASSUM MP_TAC
 >> Cases_on ‘t’ >> simp [ltree_el_def]
 >> Cases_on ‘LNTH h ts’ >> simp []
 >> STRIP_TAC
 (* applying ltree_delete_CONS *)
 >> MP_TAC (Q.SPECL [‘f’, ‘a’, ‘ts’, ‘h’, ‘p’, ‘x’, ‘t0’] ltree_insert_CONS)
 >> simp []
 >> DISCH_THEN K_TAC
 >> rw [ltree_el_def, LNTH_LGENLIST]
 >> Cases_on ‘LLENGTH ts’ >> simp []
 >> rename1 ‘LLENGTH ts = SOME n’
 >> Know ‘IS_SOME (LNTH h ts)’ >- rw [IS_SOME_EXISTS]
 >> rw [LNTH_IS_SOME, LFINITE_LLENGTH]
QED

Theorem ltree_el_ltree_insert :
    !f p t t0. ltree_el t p = SOME (a,SOME n) ==>
               ltree_el (ltree_insert f t p t0) p = SOME (f a,SOME (SUC n))
Proof
    Q.X_GEN_TAC ‘f’
 >> Induct_on ‘p’
 >- (rpt STRIP_TAC \\
     Cases_on ‘t’ >> fs [ltree_el_def, ltree_insert_NIL] \\
    ‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
     simp [ltree_el_def])
 >> rpt STRIP_TAC
 >> Cases_on ‘t’ >> fs [ltree_el_def]
 >> Cases_on ‘LNTH h ts’ >> fs []
 >> MP_TAC (Q.SPECL [‘f’, ‘a'’, ‘ts’, ‘h’, ‘p’, ‘x’, ‘t0’] ltree_insert_CONS)
 >> simp []
 >> DISCH_THEN K_TAC
 >> rw [ltree_el_def, LNTH_LGENLIST]
 >> Cases_on ‘LLENGTH ts’ >> simp []
 >> rename1 ‘LLENGTH ts = SOME N’
 >> Know ‘IS_SOME (LNTH h ts)’ >- rw [IS_SOME_EXISTS]
 >> rw [LNTH_IS_SOME, LFINITE_LLENGTH]
QED

(* |- !p t t0.
        ltree_el t p = SOME (a,SOME n) ==>
        ltree_el (ltree_insert I t p t0) p = SOME (a,SOME (SUC n))
 *)
Theorem ltree_el_ltree_insert' =
        ltree_el_ltree_insert |> Q.SPEC ‘I’ |> SRULE []

Theorem ltree_insert_paths_lemma[local] :
    !f p t a n.
       ltree_el t p = SOME (a,SOME n) ==>
       ltree_paths (ltree_insert f t p t0) =
       ltree_paths t UNION (IMAGE (\q. SNOC n p ++ q) (ltree_paths t0))
Proof
    Q.X_GEN_TAC ‘f’
 >> Induct_on ‘p’
 >- (rw [ltree_paths_alt_ltree_el] \\
     Cases_on ‘t’ >> fs [ltree_el_def, ltree_lookup_def] \\
     Q.PAT_X_ASSUM ‘a' = a’ K_TAC \\
    ‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
     MP_TAC (Q.SPECL [‘f’, ‘a’, ‘ts’, ‘t0’] ltree_insert_NIL) >> simp [] \\
     DISCH_THEN K_TAC \\
     rw [Once EXTENSION] \\
     EQ_TAC >> rw [] >| (* 2 subgoals *)
     [ (* goal 1 (of 2) *)
       Cases_on ‘x’ >> fs [ltree_el_def, LNTH_LGENLIST] \\
       Cases_on ‘h < n + 1’ >> fs [] \\
      ‘h = n \/ h < n’ by rw [] >- fs [] \\
       fs [] \\
       Know ‘IS_SOME (LNTH h ts)’ >- rw [LFINITE_LNTH_IS_SOME] \\
       REWRITE_TAC [IS_SOME_EXISTS] \\
       rw [] \\
       CCONTR_TAC >> fs [],
       (* goal 2 (of 2) *)
       Cases_on ‘x’ >> fs [ltree_el_def, LNTH_LGENLIST] \\
       Cases_on ‘LNTH h ts’ >> fs [] \\
       Know ‘IS_SOME (LNTH h ts)’ >- rw [] \\
       rw [LFINITE_LNTH_IS_SOME] \\
       CCONTR_TAC >> fs [] ])
 (* stage work *)
 >> rpt STRIP_TAC
 >> ‘!q. SNOC n (h::p) ++ q = h::(SNOC n p ++ q)’ by rw []
 >> POP_ORW
 >> ‘SNOC n (h::p) = h::SNOC n p’ by rw []
 >> POP_ORW
 >> Cases_on ‘t’
 >> POP_ASSUM MP_TAC
 >> simp [ltree_el_def, ltree_lookup_def]
 >> Cases_on ‘LNTH h ts’ >> simp []
 >> DISCH_TAC
 >> MP_TAC (Q.SPECL [‘f’, ‘a'’, ‘ts’, ‘h’, ‘p’, ‘x’, ‘t0’] ltree_insert_CONS)
 >> simp []
 >> DISCH_THEN K_TAC
 >> simp [Once ltree_paths_alt_ltree_el]
 >> simp [Once EXTENSION]
 >> Q.X_GEN_TAC ‘ns’
 >> EQ_TAC >> rw []
 >| [ (* goal 1 (of 3) *)
      Cases_on ‘ns’ >> fs [ltree_el_def, LNTH_LGENLIST] \\
      POP_ASSUM MP_TAC \\
      Cases_on ‘LLENGTH ts’ >> simp []
      >- (Cases_on ‘h' = h’ >> simp []
          >- (POP_ASSUM K_TAC \\
              DISCH_TAC \\
              Know ‘t IN ltree_paths (ltree_insert f x p t0)’
              >- rw [ltree_paths_alt_ltree_el] \\
              Q.PAT_X_ASSUM ‘!t a n. P’ (MP_TAC o Q.SPECL [‘x’, ‘a’, ‘n’]) \\
              simp [] >> DISCH_THEN K_TAC \\
              rw [ltree_paths_alt_ltree_el, ltree_el_def]) \\
          rw [ltree_paths_alt_ltree_el, ltree_el_def] \\
          Cases_on ‘LNTH h' ts’ >> simp []
          >- (Know ‘~LFINITE ts’ >- rw [LFINITE_LLENGTH] \\
              DISCH_TAC \\
              fs [infinite_lnth_some] \\
              POP_ASSUM (MP_TAC o Q.SPEC ‘h'’) >> rw []) \\
          fs []) \\
      rename1 ‘LLENGTH ts = SOME N’ \\
      Cases_on ‘h' < N’ >> simp [] \\
      Cases_on ‘h' = h’ >> simp []
      >- (POP_ASSUM (fs o wrap) \\
          DISCH_TAC \\
          Know ‘t IN ltree_paths (ltree_insert f x p t0)’
          >- rw [ltree_paths_alt_ltree_el] \\
          Q.PAT_X_ASSUM ‘!t a n. P’ (MP_TAC o Q.SPECL [‘x’, ‘a’, ‘n’]) \\
          simp [] >> DISCH_THEN K_TAC \\
          rw [ltree_paths_alt_ltree_el, ltree_el_def]) \\
      rw [ltree_paths_alt_ltree_el, ltree_el_def] \\
      Cases_on ‘LNTH h' ts’ >> simp []
      >- (‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
          Know ‘IS_SOME (LNTH h' ts)’ >- rw [LFINITE_LNTH_IS_SOME] \\
          rw [IS_SOME_EXISTS]) \\
      fs [],
      (* goal 2 (of 3) *)
      Cases_on ‘ns’ >> fs []
      >- (simp [ltree_el_def, LNTH_LGENLIST]) \\
      simp [ltree_el_def, LNTH_LGENLIST] \\
      Cases_on ‘LLENGTH ts’ >> simp []
      >- (Cases_on ‘h' = h’ >> simp []
          >- (POP_ASSUM (fs o wrap) \\
              Know ‘ltree_el (ltree_insert f x p t0) t <> NONE <=>
                    t IN ltree_paths (ltree_insert f x p t0)’
              >- rw [ltree_paths_alt_ltree_el] >> Rewr' \\
              Q.PAT_X_ASSUM ‘!t a n. P’ (MP_TAC o Q.SPECL [‘x’, ‘a’, ‘n’]) \\
              simp [] >> DISCH_THEN K_TAC \\
              Q.PAT_X_ASSUM ‘h::t IN ltree_paths (Branch a' ts)’ MP_TAC \\
              simp [ltree_paths_alt_ltree_el, ltree_el_def]) \\
          fs [] \\
          Q.PAT_X_ASSUM ‘h'::t IN ltree_paths (Branch a' ts)’ MP_TAC \\
          simp [ltree_paths_alt_ltree_el, ltree_el_def] \\
          Cases_on ‘LNTH h' ts’ >> simp []) \\
      rename1 ‘LLENGTH ts = SOME N’ \\
      Cases_on ‘h' < N’ >> simp []
      >- (Cases_on ‘h' = h’ >> simp []
          >- (POP_ASSUM (fs o wrap) \\
              Know ‘ltree_el (ltree_insert f x p t0) t <> NONE <=>
                    t IN ltree_paths (ltree_insert f x p t0)’
              >- rw [ltree_paths_alt_ltree_el] >> Rewr' \\
              Q.PAT_X_ASSUM ‘!t a n. P’ (MP_TAC o Q.SPECL [‘x’, ‘a’, ‘n’]) \\
              simp [] >> DISCH_THEN K_TAC \\
              Q.PAT_X_ASSUM ‘h::t IN ltree_paths (Branch a' ts)’ MP_TAC \\
              rw [ltree_paths_alt_ltree_el, ltree_el_def]) \\
          fs [] \\
          Q.PAT_X_ASSUM ‘h'::t IN ltree_paths (Branch a' ts)’ MP_TAC \\
          simp [ltree_paths_alt_ltree_el, ltree_el_def] \\
          Cases_on ‘LNTH h' ts’ >> simp []) \\
     ‘N <= h'’ by rw [] \\
      Q.PAT_X_ASSUM ‘h'::t IN ltree_paths (Branch a' ts)’ MP_TAC \\
      simp [ltree_paths_alt_ltree_el, ltree_el_def] \\
      Cases_on ‘LNTH h' ts’ >> simp [] \\
     ‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
      Know ‘IS_SOME (LNTH h' ts)’ >- rw [IS_SOME_EXISTS] \\
      simp [LFINITE_LNTH_IS_SOME],
      (* goal 3 (of 3) *)
      simp [ltree_el_def, LNTH_LGENLIST] \\
      Cases_on ‘LLENGTH ts’ >> simp []
      >- (Know ‘ltree_el (ltree_insert f x p t0) (p ++ [n] ++ q) <> NONE <=>
                p ++ [n] ++ q IN ltree_paths (ltree_insert f x p t0)’
          >- rw [ltree_paths_alt_ltree_el] >> Rewr' \\
          Q.PAT_X_ASSUM ‘!t a n. P’ (MP_TAC o Q.SPECL [‘x’, ‘a’, ‘n’]) \\
          simp []) \\
      rename1 ‘LLENGTH ts = SOME N’ \\
      Cases_on ‘h < N’ >> simp []
      >- (Know ‘ltree_el (ltree_insert f x p t0) (p ++ [n] ++ q) <> NONE <=>
                p ++ [n] ++ q IN ltree_paths (ltree_insert f x p t0)’
          >- rw [ltree_paths_alt_ltree_el] >> Rewr' \\
          Q.PAT_X_ASSUM ‘!t a n. P’ (MP_TAC o Q.SPECL [‘x’, ‘a’, ‘n’]) \\
          simp []) \\
     ‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
      Know ‘IS_SOME (LNTH h ts)’ >- rw [IS_SOME_EXISTS] \\
      ASM_SIMP_TAC bool_ss [LFINITE_LNTH_IS_SOME] \\
      simp [] ]
QED

Theorem ltree_insert_paths :
    !f p t n t0.
       p IN ltree_paths t /\ ltree_branching t p = SOME n ==>
       ltree_paths (ltree_insert f t p t0) =
       ltree_paths t UNION (IMAGE (\q. SNOC n p ++ q) (ltree_paths t0))
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC ltree_insert_paths_lemma
 >> Cases_on ‘t’
 >> fs [ltree_paths_alt_ltree_el, ltree_branching_def]
 >> Cases_on ‘p’ >> fs [ltree_el_def]
 >> Cases_on ‘LNTH h ts’ >> fs []
 >> Cases_on ‘ltree_el x t’ >> fs []
 >> rename1 ‘SND y = SOME n’
 >> Cases_on ‘y’ >> fs []
QED

Theorem ltree_insert_delete :
    !n p t t0 f g d len.
       ltree_branching t p = SOME (SUC n) /\
       ltree_lookup t (SNOC n p) = SOME t0 /\
       ltree_el t p = SOME (d,len) /\ f (g d) = d ==>
       ltree_insert f (ltree_delete g t p) p t0 = t
Proof
    rpt STRIP_TAC
 (* initial preparation (for induction) *)
 >> Know ‘p IN ltree_paths t’
 >- (MATCH_MP_TAC ltree_paths_inclusive \\
     Q.EXISTS_TAC ‘SNOC n p’ \\
     rw [isPREFIX_SNOC, ltree_paths_def])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘ltree_lookup t (SNOC n p) = SOME t0’ MP_TAC
 >> Know ‘ltree_lookup t (SNOC n p) =
          ltree_lookup (THE (ltree_lookup t p)) [n]’
 >- (MATCH_MP_TAC ltree_lookup_SNOC \\
     fs [ltree_paths_def])
 >> Rewr'
 >> POP_ASSUM MP_TAC
 >> simp [ltree_paths_def]
 >> simp [GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
 >> STRIP_TAC
 >> Cases_on ‘x’
 >> simp [ltree_lookup_def]
 >> Cases_on ‘LNTH n ts’ >> simp []
 >> DISCH_THEN (fs o wrap)
 >> fs [ltree_branching_def]
 >> MP_TAC (Q.SPECL [‘p’, ‘t’] ltree_el_alt_ltree_lookup)
 >> rw [ltree_paths_def]
 >> POP_ASSUM (ASSUME_TAC o SYM) (* LLENGTH ts = SOME (SUC n) *)
 >> Q.PAT_X_ASSUM ‘ltree_el t p = _’ K_TAC
 (* stage work *)
 >> rpt (POP_ASSUM MP_TAC)
 >> qid_spec_tac ‘t0’
 >> qid_spec_tac ‘t’
 >> qid_spec_tac ‘a’
 >> qid_spec_tac ‘ts’
 >> qid_spec_tac ‘n’
 >> qid_spec_tac ‘p’
 >> Induct_on ‘p’
 >- (rw [ltree_lookup] \\
  (* 1. eliminating ltree_delete *)
     simp [ltree_delete_def] \\
     simp [Once gen_ltree, ltree_el_def] \\
     qmatch_abbrev_tac ‘ltree_insert f t' [] t0 = _’ \\
     Know ‘t' = Branch (g a) (LGENLIST (\i. THE (LNTH i ts)) (SOME n))’
     >- (simp [Abbr ‘t'’, LNTH_EQ, LNTH_LGENLIST] \\
         Q.X_GEN_TAC ‘i’ \\
         Cases_on ‘i < n’ >> simp [] \\
         Cases_on ‘LNTH i ts’ >> simp []
         >- (Know ‘IS_SOME (LNTH i ts)’
             >- (MATCH_MP_TAC LNTH_IS_SOME_MONO \\
                 Q.EXISTS_TAC ‘n’ >> simp [IS_SOME_EXISTS]) \\
             rw [IS_SOME_EXISTS]) \\
         simp [ltree_el_lemma, gen_ltree_unchanged]) >> Rewr' \\
     qunabbrev_tac ‘t'’ \\
  (* 2. eliminating ltree_insert *)
     simp [ltree_insert_def] \\
     simp [Once gen_ltree, ltree_el_def, LNTH_LGENLIST] \\
  (* applying LNTH_EQ again *)
     simp [LNTH_EQ, LNTH_LGENLIST, GSYM ADD1] \\
     Q.X_GEN_TAC ‘i’ \\
    ‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
     reverse (Cases_on ‘i < SUC n’ >> simp [])
     >- (MATCH_MP_TAC LNTH_LLENGTH_NONE \\
         Q.EXISTS_TAC ‘SUC n’ >> rw []) \\
    ‘i = n \/ i < n’ by rw [] >> simp [] >- rw [gen_ltree_unchanged] \\
  (* so far so good ... *)
     qabbrev_tac ‘t1 = THE (LNTH i ts)’ \\
     simp [ltree_el_lemma] \\
  (* so far so good ... *)
    ‘IS_SOME (LNTH i ts)’ by rw [LFINITE_LNTH_IS_SOME] \\
     fs [IS_SOME_EXISTS, Abbr ‘t1’] \\
     rw [gen_ltree_unchanged_extra])
 (* stage work *)
 >> rpt GEN_TAC
 >> Cases_on ‘t’ >> simp [ltree_lookup_def]
 >> Cases_on ‘LNTH h ts'’ >> rw []
 (* applying ltree_delete_CONS *)
 >> Know ‘ltree_delete g (Branch a' ts') (h::p) =
          Branch a' (LGENLIST (\i. if i = h then
                                      ltree_delete g (THE (LNTH h ts')) p
                                   else
                                      THE (LNTH i ts'))
                              (LLENGTH ts'))’
 >- (MATCH_MP_TAC ltree_delete_CONS \\
     Q.EXISTS_TAC ‘x’ >> art [] \\
     Know ‘p IN ltree_paths x’ >- rw [ltree_paths_def] \\
     rw [ltree_paths_alt_ltree_el])
 >> Rewr'
 >> simp []
 >> qmatch_abbrev_tac ‘ltree_insert f (Branch a' ts1) (h::p) t0 = _’
 (* applying ltree_insert_CONS *)
 >> Know ‘ltree_insert f (Branch a' ts1) (h::p) t0 =
          Branch a' (LGENLIST (\i. if i = h then
                                      ltree_insert f (THE (LNTH h ts1)) p t0
                                   else
                                      THE (LNTH i ts1)) (LLENGTH ts1))’
 >- (MATCH_MP_TAC ltree_insert_CONS \\
     simp [Abbr ‘ts1’, LNTH_LGENLIST] \\
     Cases_on ‘LLENGTH ts'’ >> simp []
     >- (MP_TAC (Q.SPECL [‘g’, ‘p’, ‘x’] ltree_delete_path_stable) \\
         simp [ltree_paths_alt_ltree_el, GSYM ltree_lookup_iff_ltree_el]) \\
     STRONG_CONJ_TAC
     >- (Know ‘IS_SOME (LNTH h ts')’ >- rw [IS_SOME_EXISTS] \\
         simp [LNTH_IS_SOME] \\
         impl_tac >- rw [LFINITE_LLENGTH] >> simp []) >> DISCH_TAC \\
     rename1 ‘h < N’ \\
     MP_TAC (Q.SPECL [‘g’, ‘p’, ‘x’] ltree_delete_path_stable) \\
     simp [ltree_paths_alt_ltree_el, GSYM ltree_lookup_iff_ltree_el])
 >> Rewr'
 >> simp [LNTH_EQ, LNTH_LGENLIST, Abbr ‘ts1’]
 >> Q.X_GEN_TAC ‘i’
 >> Cases_on ‘LLENGTH ts'’ >> simp []
 >- (Cases_on ‘i = h’ >> simp [] \\
     Know ‘~LFINITE ts'’ >- rw [LFINITE_LLENGTH] \\
     rw [infinite_lnth_some] \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘i’) >> rw [] \\
     simp [])
 >> reverse (Cases_on ‘i < x'’) >> simp []
 >- (‘x' <= i’ by rw [] \\
     MATCH_MP_TAC LNTH_LLENGTH_NONE \\
     Q.EXISTS_TAC ‘x'’ >> art [])
 >> Cases_on ‘i = h’ >> simp []
 >> Suff ‘IS_SOME (LNTH i ts')’ >- (rw [IS_SOME_EXISTS] >> simp [])
 >> rw [LNTH_IS_SOME]
QED

Theorem ltree_insert_delete' :
    !n p t t0.
       ltree_branching t p = SOME (SUC n) /\
       ltree_lookup t (SNOC n p) = SOME t0 ==>
       ltree_insert' (ltree_delete' t p) p t0 = t
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC ltree_insert_delete >> simp []
 >> Know ‘p IN ltree_paths t’
 >- (MATCH_MP_TAC ltree_paths_inclusive \\
     Q.EXISTS_TAC ‘SNOC n p’ \\
     simp [isPREFIX_SNOC, ltree_paths_def])
 >> rw [ltree_paths_alt_ltree_el, GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
 >> rename1 ‘ltree_el t p = SOME y’
 >> Cases_on ‘y’
 >> qexistsl_tac [‘q’, ‘r’] >> rw []
QED

(*---------------------------------------------------------------------------*
 *  ltree_finite and (finite) ltree_paths
 *---------------------------------------------------------------------------*)

Theorem ltree_finite_imp_finite_ltree_paths :
    !t. ltree_finite t ==> FINITE (ltree_paths t)
Proof
    HO_MATCH_MP_TAC ltree_finite_ind
 >> rw [ltree_paths_alt_ltree_el, EVERY_EL]
 >> qabbrev_tac ‘k = LENGTH ts’
 >> Know ‘{p | ltree_el (Branch a (fromList ts)) p <> NONE} =
           [] INSERT
              BIGUNION (IMAGE (\i. {i::q | q | ltree_el (EL i ts) q <> NONE})
                              (count k))’
 >- (rw [Once EXTENSION, IN_BIGUNION_IMAGE] \\
     Cases_on ‘x’ >> simp [ltree_el_def, LNTH_fromList] \\
     Cases_on ‘h < k’ >> rw [])
 >> Rewr'
 >> REWRITE_TAC [FINITE_INSERT]
 >> MATCH_MP_TAC FINITE_BIGUNION
 >> CONJ_TAC >- (MATCH_MP_TAC IMAGE_FINITE >> rw [FINITE_COUNT])
 >> rw []
 >> Know ‘{i::q | q | ltree_el (EL i ts) q <> NONE} =
           IMAGE (\q. i::q) {q | q | ltree_el (EL i ts) q <> NONE}’
 >- rw [Once EXTENSION]
 >> Rewr'
 >> MATCH_MP_TAC IMAGE_FINITE
 >> FIRST_X_ASSUM MATCH_MP_TAC >> art []
QED

Theorem finite_ltree_paths_imp_ltree_finite_lemma[local] :
    !n s t. s HAS_SIZE n /\ ltree_paths t = s ==> ltree_finite t
Proof
    Induct_on ‘n’ >> rw [HAS_SIZE]
 >- (‘ltree_paths t = {}’ by PROVE_TAC [CARD_EQ_0] \\
     ‘[] IN ltree_paths t’ by PROVE_TAC [NIL_IN_ltree_paths] \\
     ASM_SET_TAC [])
 >> qabbrev_tac ‘s = ltree_paths t’
 >> Know ‘s <> {}’
 >- (rw [Abbr ‘s’, GSYM MEMBER_NOT_EMPTY] \\
     Q.EXISTS_TAC ‘[]’ >> rw [NIL_IN_ltree_paths])
 >> DISCH_TAC
 >> qabbrev_tac ‘R = SHORTLEX ($< :num -> num -> bool)’
 (* applying finite_acyclic_has_maximal *)
 >> qabbrev_tac ‘r = rel_to_reln R’
 >> Know ‘?x. x IN maximal_elements s r’
 >- (irule finite_acyclic_has_maximal >> art [] \\
     MATCH_MP_TAC WF_acyclic >> rw [Abbr ‘r’] \\
     rw [Abbr ‘R’, WF_SHORTLEX])
 >> rw [maximal_elements_def, Abbr ‘r’, in_rel_to_reln]
 >> Cases_on ‘x = []’
 >- (fs [Abbr ‘R’] \\
     Know ‘!x. x IN s ==> x = []’
     >- (Q.X_GEN_TAC ‘z’ >> Cases_on ‘z’ >> rw [] \\
         rename1 ‘h::tl NOTIN s’ \\
         Q.PAT_X_ASSUM ‘!x. x IN s /\ _ ==> x = []’ (MP_TAC o Q.SPEC ‘h::tl’) \\
         simp []) >> DISCH_TAC \\
     Know ‘s = {[]}’
     >- (rw [Once EXTENSION] >> EQ_TAC >> rw []) >> DISCH_TAC \\
     fs [Abbr ‘s’] \\
     Q.PAT_X_ASSUM ‘!t. P’ K_TAC \\
     Cases_on ‘t’ >> gs [ltree_paths_alt_ltree_el, Once EXTENSION] \\
     Suff ‘ts = LNIL’ >- simp [ltree_finite] \\
     CCONTR_TAC >> Cases_on ‘ts’ >> gs [] \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘[0]’) >> rw [ltree_el])
 >> qabbrev_tac ‘s' = s DELETE x’
 >> ‘s' HAS_SIZE n’ by rw [Abbr ‘s'’, HAS_SIZE]
 >> qabbrev_tac ‘p = FRONT x’
 >> qabbrev_tac ‘i = LAST x’
 >> qabbrev_tac ‘t' = ltree_delete' t p’
 >> Know ‘ltree_lookup t x <> NONE’
 >- (Q.PAT_X_ASSUM ‘x IN s’ MP_TAC \\
     simp [Abbr ‘s’, ltree_paths_def])
 >> DISCH_TAC
 >> qabbrev_tac ‘t0 = THE (ltree_lookup t x)’
 (* stage work *)
 >> Know ‘ltree_children t0 = LNIL’
 >- (CCONTR_TAC \\
     Cases_on ‘t0’ >> fs [] \\
     Cases_on ‘ts’ >> gs [] \\
     Know ‘SNOC 0 x IN s’
     >- (simp [Abbr ‘s’, ltree_paths_def] \\
         simp [ltree_lookup_SNOC, ltree_lookup_def]) >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!y. y IN s /\ R x y ==> x = y’ (MP_TAC o Q.SPEC ‘SNOC 0 x’) \\
     simp [Abbr ‘R’] \\
     MATCH_MP_TAC LENGTH_LT_SHORTLEX >> simp [])
 >> DISCH_TAC
 >> Cases_on ‘t0’ >> gs []
 >> POP_ASSUM K_TAC
 >> qabbrev_tac ‘t0 = Branch a LNIL’
 >> Know ‘ltree_paths t0 = {[]}’
 >- (rw [Abbr ‘t0’, ltree_paths_def] \\
     simp [Once EXTENSION] \\
     Q.X_GEN_TAC ‘y’ \\
     reverse EQ_TAC >- rw [ltree_lookup_def] \\
     Cases_on ‘y’ >> simp [] \\
     rw [ltree_lookup_def])
 >> DISCH_TAC
 >> ‘SNOC i p = x’ by ASM_SIMP_TAC std_ss [Abbr ‘p’, Abbr ‘i’, SNOC_LAST_FRONT]
 (* calculate “ltree_el t p” *)
 >> MP_TAC (Q.SPECL [‘t’, ‘i’, ‘p’] ltree_lookup_SNOC) >> simp []
 >> Know ‘p IN ltree_paths t’
 >- (MATCH_MP_TAC ltree_paths_inclusive \\
     Q.EXISTS_TAC ‘x’ \\
     reverse CONJ_TAC >- rw [ltree_paths_def] \\
     Q.PAT_X_ASSUM ‘SNOC i p = x’ (REWRITE_TAC o wrap o SYM) \\
     rw [isPREFIX_SNOC])
 >> REWRITE_TAC [ltree_paths_def] >> simp [] >> DISCH_TAC
 >> Cases_on ‘ltree_lookup t p’ >> FULL_SIMP_TAC std_ss []
 >> rename1 ‘ltree_lookup t p = SOME t1’
 >> Cases_on ‘t1’
 >> simp [ltree_lookup_def]
 >> Cases_on ‘LNTH i ts’ >> simp []
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap o SYM)
 >> MP_TAC (Q.SPECL [‘p’, ‘t’] ltree_el_alt_ltree_lookup)
 >> REWRITE_TAC [ltree_paths_def] >> simp [] >> DISCH_TAC
 >> Cases_on ‘LLENGTH ts’ >> simp []
 >- (MP_TAC (Q.SPECL [‘t’, ‘SUC i’, ‘p’] ltree_lookup_SNOC) \\
     simp [ltree_lookup_def] \\
     Know ‘~LFINITE ts’ >- rw [LFINITE_LLENGTH] \\
     simp [infinite_lnth_some] >> STRIP_TAC \\
     POP_ASSUM (MP_TAC o Q.SPEC ‘SUC i’) >> STRIP_TAC \\
     POP_ORW >> simp [] >> DISCH_TAC \\
     Q.PAT_X_ASSUM ‘!y. y IN s /\ R x y ==> P’
       (MP_TAC o Q.SPEC ‘SNOC (SUC i) p’) \\
     simp [Abbr ‘s’, ltree_paths_def] \\
     rw [Abbr ‘R’] \\
     Suff ‘SHORTLEX $< (SNOC i p) (SNOC (SUC i) p)’ >- rw [] \\
     MATCH_MP_TAC SHORTLEX_SNOC >> simp [])
 >> rename1 ‘LLENGTH ts = SOME N’
 >> Know ‘N = SUC i’
 >- (MATCH_MP_TAC LESS_EQUAL_ANTISYM \\
     reverse CONJ_TAC
     >- (‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
         Know ‘IS_SOME (LNTH i ts)’ >- rw [IS_SOME_EQ_NOT_NONE] \\
         rw [LFINITE_LNTH_IS_SOME]) \\
     CCONTR_TAC \\
    ‘SUC i < N’ by rw [] \\
     MP_TAC (Q.SPECL [‘t’, ‘SUC i’, ‘p’] ltree_lookup_SNOC) \\
     simp [ltree_lookup_def] \\
    ‘LFINITE ts’ by rw [LFINITE_LLENGTH] \\
     Know ‘IS_SOME (LNTH (SUC i) ts)’ >- rw [LFINITE_LNTH_IS_SOME] \\
     rw [IS_SOME_EXISTS] \\
     POP_ORW >> simp [] \\
     CCONTR_TAC >> fs [] \\
     Q.PAT_X_ASSUM ‘!y. y IN s /\ R (SNOC i p) y ==> P’
        (MP_TAC o Q.SPEC ‘SNOC (SUC i) p’) \\
     simp [Abbr ‘s’, ltree_paths_def] \\
     qunabbrev_tac ‘R’ \\
     MATCH_MP_TAC SHORTLEX_SNOC >> simp [])
 >> DISCH_THEN (FULL_SIMP_TAC std_ss o wrap)
 >> Cases_on ‘ltree_lookup t x’ >> FULL_SIMP_TAC std_ss []
 >> rename1 ‘ltree_lookup t x = SOME t1’
 >> rpt (Q.PAT_X_ASSUM ‘T’ K_TAC)
 (* applying ltree_delete_paths *)
 >> MP_TAC (Q.SPECL [‘I’, ‘p’, ‘t’, ‘a'’, ‘i’] ltree_delete_paths_lemma)
 >> simp []
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘!t. ltree_paths t HAS_SIZE n ==> ltree_finite t’
      (MP_TAC o Q.SPEC ‘t'’)
 >> impl_tac
 >- (simp [HAS_SIZE, CARD_DIFF] \\
    ‘s INTER {x} = {x}’ by ASM_SET_TAC [] >> POP_ORW \\
     simp [])
 >> DISCH_TAC (* ltree_finite t' *)
 (* applying ltree_insert_delete' *)
 >> Know ‘t = ltree_insert' t' p t0’
 >- (simp [Abbr ‘t'’, Once EQ_SYM_EQ] \\
     MATCH_MP_TAC ltree_insert_delete' \\
     Q.EXISTS_TAC ‘i’ >> simp [] \\
     simp [ltree_branching_def])
 >> Rewr'
 (* final goal: ltree_finite t' ==> ltree_finite (ltree_insert' t' p t0) *)
 >> ‘ltree_finite t0’ by simp [ltree_finite, Abbr ‘t0’]
 >> irule ltree_finite_ltree_insert_lemma >> art []
 >> qexistsl_tac [‘a'’, ‘SOME i’]
 >> qunabbrev_tac ‘t'’
 >> MATCH_MP_TAC ltree_el_ltree_delete' >> art []
QED

Theorem finite_ltree_paths_imp_ltree_finite[local] :
    !t. FINITE (ltree_paths t) ==> ltree_finite t
Proof
    rpt STRIP_TAC
 >> irule finite_ltree_paths_imp_ltree_finite_lemma
 >> qabbrev_tac ‘s = ltree_paths t’
 >> qexistsl_tac [‘CARD s’, ‘s’]
 >> rw [HAS_SIZE]
QED

Theorem ltree_finite_alt_ltree_paths :
    !t. ltree_finite t <=> FINITE (ltree_paths t)
Proof
    METIS_TAC [ltree_finite_imp_finite_ltree_paths,
               finite_ltree_paths_imp_ltree_finite]
QED

(*---------------------------------------------------------------------------*
 *  Rose tree is a finite variant of ltree, defined inductively.
 *---------------------------------------------------------------------------*)

Datatype:
  rose_tree = Rose 'a (rose_tree list)
End

Definition rose_node_def[simp] :
    rose_node (Rose a ts) = a
End

Definition rose_children_def[simp] :
    rose_children (Rose a ts) = ts
End

Definition from_rose_def:
  from_rose (Rose a ts) = Branch a (fromList (MAP from_rose ts))
Termination
  WF_REL_TAC `measure (rose_tree_size (K 0))` \\ rw []
End

Theorem from_rose_def[allow_rebind] :
    !ts a. from_rose (Rose a ts) = Branch a (fromList (MAP from_rose ts))
Proof
    rw [from_rose_def, LIST_EQ_REWRITE, EL_MAP]
QED

Theorem from_rose :
    !t. from_rose t =
        Branch (rose_node t) (fromList (MAP from_rose (rose_children t)))
Proof
    rpt GEN_TAC
 >> Cases_on ‘t’
 >> simp [Once from_rose_def]
QED

Theorem rose_tree_induction[allow_rebind] = from_rose_ind;

Theorem from_rose_11 :
    !r1 r2. from_rose r1 = from_rose r2 <=> r1 = r2
Proof
    rpt GEN_TAC
 >> reverse EQ_TAC >- simp []
 >> qid_spec_tac ‘r2’
 >> qid_spec_tac ‘r1’
 >> HO_MATCH_MP_TAC rose_tree_induction
 >> rpt STRIP_TAC
 >> Cases_on ‘r2’
 >> fs [from_rose_def]
 >> POP_ASSUM MP_TAC
 >> rw [LIST_EQ_REWRITE, EL_MAP]
 >> rename1 ‘n < LENGTH l’
 >> Q.PAT_X_ASSUM ‘!r1. MEM r1 ts ==> P’ (MP_TAC o Q.SPEC ‘EL n ts’)
 >> rw [EL_MEM, EL_MAP]
QED

Theorem ltree_finite_from_rose:
  ltree_finite t <=> ?r. from_rose r = t
Proof
  eq_tac \\ qid_spec_tac `t` THEN1
   (ho_match_mp_tac ltree_finite_ind \\ fs [EVERY_MEM] \\ rw []
    \\ qsuff_tac `?rs. ts = MAP from_rose rs` THEN1
     (strip_tac \\ qexists_tac `Rose a rs` \\ fs [from_rose_def]
      \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
    \\ Induct_on `ts` \\ fs [] \\ rw []
    \\ first_assum (qspec_then `h` assume_tac) \\ fs []
    \\ qexists_tac `r::rs` \\ fs [])
  \\ fs [PULL_EXISTS]
  \\ ho_match_mp_tac from_rose_ind \\ rw []
  \\ once_rewrite_tac [ltree_finite_cases]
  \\ fs [from_rose_def,Branch_11]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS]
QED

(* The previous theorem induces a new constant “to_rose” for finite ltrees *)
local
  val thm = Q.prove (‘!t. ltree_finite t ==> ?r. from_rose r = t’,
                     METIS_TAC [ltree_finite_from_rose]);
in
  (* |- !t. ltree_finite t ==> from_rose (to_rose t) = t *)
  val to_rose_def = new_specification
    ("to_rose_def", ["to_rose"],
      SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] thm);
end;

Theorem to_rose_thm :
    !r. to_rose (from_rose r) = r
Proof
    Q.X_GEN_TAC ‘r’
 >> qabbrev_tac ‘t = from_rose r’
 >> ‘ltree_finite t’ by METIS_TAC [ltree_finite_from_rose]
 >> rw [GSYM from_rose_11, to_rose_def]
QED

Theorem rose_node_to_rose :
    !t. ltree_finite t ==> rose_node (to_rose t) = ltree_node t
Proof
    rw [ltree_finite_from_rose]
 >> rw [to_rose_thm]
 >> Cases_on ‘r’
 >> rw [rose_node_def, from_rose_def, ltree_node_def]
QED

Theorem rose_children_to_rose :
    !t. ltree_finite t ==>
        rose_children (to_rose t) = MAP to_rose (THE (toList (ltree_children t)))
Proof
    rw [ltree_finite_from_rose]
 >> rw [to_rose_thm]
 >> Cases_on ‘r’
 >> rw [rose_node_def, from_rose_def, ltree_node_def]
 >> simp [from_toList, MAP_MAP_o]
 >> simp [o_DEF, to_rose_thm]
QED

Theorem rose_children_to_rose' :
    !t. ltree_finite t ==>
        rose_children (to_rose t) = THE (toList (LMAP to_rose (ltree_children t)))
Proof
    rpt STRIP_TAC
 >> ‘finite_branching t’ by PROVE_TAC [ltree_finite_imp_finite_branching]
 >> Suff ‘LFINITE (ltree_children t)’
 >- (DISCH_TAC >> simp [GSYM MAP_toList] \\
     MATCH_MP_TAC rose_children_to_rose >> art [])
 >> Suff ‘finite_branching (Branch (ltree_node t) (ltree_children t))’ >- rw []
 >> ASM_REWRITE_TAC [ltree_node_children_reduce]
QED

(* This is a general recursive reduction function for rose trees. The type of
   f is “:'a -> 'b list -> 'b”, where 'b is the type of reductions of trees.

   See examples/lambda/barendregt/lameta_complateTheory.rose_to_term_def for
   an application.
 *)
Definition rose_reduce_def :
    rose_reduce f ((Rose a ts) :'a rose_tree) = f a (MAP (rose_reduce f) ts)
Termination
    WF_REL_TAC ‘measure (rose_tree_size (K 0) o SND)’
End

Theorem rose_reduce_def[allow_rebind] :
    !f a ts. rose_reduce f (Rose a ts) = f a (MAP (rose_reduce f) ts)
Proof
    rw [rose_reduce_def]
 >> AP_TERM_TAC
 >> rw [LIST_EQ_REWRITE, EL_MAP]
QED

Theorem rose_reduce :
    !f t. rose_reduce f t = f (rose_node t) (MAP (rose_reduce f) (rose_children t))
Proof
    rpt GEN_TAC
 >> Cases_on ‘t’
 >> simp [Once rose_reduce_def]
QED

(*---------------------------------------------------------------------------*
 *  index function of ltree paths
 *---------------------------------------------------------------------------*)

Overload ltree_path_lt = “SHORTLEX ($< :num -> num -> bool)”

Theorem ltree_path_lt =
        SHORTLEX_THM |> Q.GEN ‘R’ |> ISPEC “($< :num -> num -> bool)”

(* The first two properties are required by TOPOLOGICAL_SORT' *)
Theorem ltree_path_lt_transitive :
    transitive ltree_path_lt
Proof
    rw [SHORTLEX_transitive]
QED

Theorem ltree_path_lt_antisymmetric :
    antisymmetric ltree_path_lt
Proof
    MATCH_MP_TAC SHORTLEX_antisymmetric
 >> rw [relationTheory.irreflexive_def,
        relationTheory.antisymmetric_def]
QED

Theorem ltree_path_lt_irreflexive :
    irreflexive ltree_path_lt
Proof
    MATCH_MP_TAC SHORTLEX_irreflexive
 >> rw [relationTheory.irreflexive_def]
QED

(* “path_index” sorts the ltree paths set and index it from smaller elements *)
Theorem path_index_exists[local] :
    !s. FINITE s ==>
        ?f. s = IMAGE f (count (CARD s)) /\
            !j k. j < CARD s /\ k < CARD s /\ j < k ==> ~ltree_path_lt (f k) (f j)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC TOPOLOGICAL_SORT'
 >> rw [HAS_SIZE, ltree_path_lt_transitive, ltree_path_lt_antisymmetric]
QED

(* |- !s. FINITE s ==>
          s = IMAGE (path_index s) (count (CARD s)) /\
          !j k.
            j < CARD s /\ k < CARD s /\ j < k ==>
            ~ltree_path_lt (path_index s k) (path_index s j)
 *)
val path_index_def = new_specification
  ("path_index_def", ["path_index"],
    SIMP_RULE std_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM] path_index_exists);

Theorem path_index_in_paths :
    !s i. FINITE s /\ i < CARD s ==> path_index s i IN s
Proof
    rpt STRIP_TAC
 >> drule path_index_def >> rw []
 >> Suff ‘path_index s i IN IMAGE (path_index s) (count (CARD s))’
 >- (Q.PAT_X_ASSUM ‘s = _’ (REWRITE_TAC o wrap o SYM))
 >> rw []
 >> Q.EXISTS_TAC ‘i’ >> simp []
QED

Overload ltree_path_le = “RC ltree_path_lt”

Theorem ltree_path_le_total :
    total ltree_path_le
Proof
    MATCH_MP_TAC SHORTLEX_total
 >> rw [total_def, RC_DEF]
QED

(* NOTE: A more complete picture of ‘path_index’. Now SHORTLEX_total is involved
   in addition to transitive and antisymmetric.
 *)
Theorem path_index_thm :
    !s n. s HAS_SIZE n ==>
          BIJ (path_index s) (count n) s /\
         !j k. j < n /\ k < n ==>
              (ltree_path_lt (path_index s j) (path_index s k) <=> j < k)
Proof
    rpt GEN_TAC >> simp [HAS_SIZE]
 >> STRIP_TAC
 >> MP_TAC (Q.SPEC ‘s’ path_index_def) >> simp []
 >> STRIP_TAC
 >> STRONG_CONJ_TAC (* BIJ *)
 >- (rw [BIJ_ALT, IN_FUNSET, path_index_in_paths] \\
     rw [EXISTS_UNIQUE_ALT] \\
     qabbrev_tac ‘n = CARD s’ \\
     Know ‘y IN IMAGE (path_index s) (count n)’ >- METIS_TAC [] \\
     rw [IN_IMAGE] \\
     Q.PAT_X_ASSUM ‘s = IMAGE _ _’ (ASSUME_TAC o SYM) \\
     Q.EXISTS_TAC ‘x’ >> art [] \\
     Q.X_GEN_TAC ‘y’ \\
     reverse EQ_TAC >- rw [] \\
     rpt STRIP_TAC \\
     CCONTR_TAC \\
  (* In this case, we found at least one duplicated index (x or y), thus
     it should be CARD s < n, conflicting with CARD = n.
   *)
     Know ‘s = IMAGE (path_index s) (count n DELETE y)’
     >- (Q.PAT_X_ASSUM ‘_ = s’ (fn th => REWRITE_TAC [Once (SYM th)]) \\
         rw [Once EXTENSION] \\
         EQ_TAC >> rw [] >| (* 2 subgoals *)
         [ (* goal 1 (of 2) *)
           rename1 ‘i < n’ \\
           Cases_on ‘i = y’ >- (Q.EXISTS_TAC ‘x’ >> art []) \\
           Q.EXISTS_TAC ‘i’ >> art [],
           (* goal 2 (of 2) *)
           rename1 ‘i <> y’ \\
           Q.EXISTS_TAC ‘i’ >> art [] ]) \\
     DISCH_THEN (MP_TAC o AP_TERM “CARD :num list set -> num”) \\
     simp [] \\
     Suff ‘CARD (IMAGE (path_index s) (count n DELETE y)) < n’ >- rw [] \\
     MATCH_MP_TAC LESS_EQ_LESS_TRANS \\
     Q.EXISTS_TAC ‘CARD (count n DELETE y)’ >> simp [CARD_IMAGE])
 >> rw [BIJ_DEF, INJ_DEF]
 >> qabbrev_tac ‘n = CARD s’
 (* applying ltree_path_le_total *)
 >> MP_TAC ltree_path_le_total
 >> simp [total_def, RC_DEF]
 >> simp [Once EQ_SYM_EQ, GSYM DISJ_ASSOC]
 >> simp [TAUT ‘P \/ Q \/ P \/ R <=> Q \/ R \/ P’]
 >> STRIP_TAC
 >> reverse EQ_TAC
 >- (Q.PAT_X_ASSUM ‘!j k. j < n /\ k < n /\ j < k ==> _’
      (MP_TAC o Q.SPECL [‘j’, ‘k’]) >> rw [] \\
    ‘j <> k’ by rw [] \\
     METIS_TAC [])
 >> STRIP_TAC
 >> CCONTR_TAC
 >> fs [NOT_LESS]
 >> ‘k = j \/ k < j’ by rw []
 >- (ASSUME_TAC ltree_path_lt_irreflexive \\
     gs [relationTheory.irreflexive_def])
 >> Q.PAT_X_ASSUM ‘!j k. j < n /\ k < n /\ j < k ==> _’ (MP_TAC o Q.SPECL [‘k’, ‘j’])
 >> rw []
QED

Definition parent_inclusive_def :
    parent_inclusive (s :num list set) <=>
    !p q. p IN s /\ q <<= p ==> q IN s
End

Definition sibling_inclusive_def :
    sibling_inclusive (s :num list set) <=>
    !p q. p IN s /\ p <> [] /\ q <> [] /\
          FRONT q = FRONT p /\ LAST q < LAST p ==> q IN s
End

Theorem parent_inclusive_ltree_paths :
    !t. parent_inclusive (ltree_paths t)
Proof
    rw [parent_inclusive_def]
 >> MATCH_MP_TAC ltree_paths_inclusive
 >> Q.EXISTS_TAC ‘p’ >> art []
QED

Theorem parent_inclusive_union :
    !s1 s2. parent_inclusive s1 /\ parent_inclusive s2 ==>
            parent_inclusive (s1 UNION s2)
Proof
    rw [parent_inclusive_def, IN_UNION]
 >| [ (* goal 1 (of 2) *)
      DISJ1_TAC \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘p’ >> art [],
      (* goal 2 (of 2) *)
      DISJ2_TAC \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘p’ >> art [] ]
QED

Theorem sibling_inclusive_ltree_paths_lemma[local] :
    !p t. p IN ltree_paths t /\ p <> [] ==>
         !q. q <> [] /\ FRONT q = FRONT p /\ LAST q < LAST p ==>
             q IN ltree_paths t
Proof
    rpt STRIP_TAC
 >> qabbrev_tac ‘xs = FRONT p’
 >> qabbrev_tac ‘x = LAST p’
 >> ‘p = SNOC x xs’ by METIS_TAC [SNOC_LAST_FRONT]
 >> ‘xs <<= p’ by METIS_TAC [isPREFIX_SNOC]
 >> Know ‘xs IN ltree_paths t’
 >- (MATCH_MP_TAC ltree_paths_inclusive \\
     Q.EXISTS_TAC ‘p’ >> art [])
 >> DISCH_TAC
 >> Q.PAT_X_ASSUM ‘p IN ltree_paths t’ MP_TAC
 >> Q.PAT_X_ASSUM ‘p = SNOC x xs’ (REWRITE_TAC o wrap)
 >> qabbrev_tac ‘y = LAST q’
 >> ‘q = SNOC y xs’ by METIS_TAC [SNOC_LAST_FRONT]
 >> POP_ORW
 >> fs [ltree_paths_def]
 >> simp [ltree_lookup_SNOC]
 >> Q.PAT_X_ASSUM ‘ltree_lookup t xs <> NONE’
      (MP_TAC o REWRITE_RULE [GSYM IS_SOME_EQ_NOT_NONE])
 >> simp [IS_SOME_EXISTS]
 >> DISCH_THEN (Q.X_CHOOSE_THEN ‘t0’ STRIP_ASSUME_TAC)
 >> simp []
 >> Cases_on ‘t0’
 >> simp [ltree_lookup_def]
 >> Cases_on ‘LNTH x ts’ >> simp []
 >> Know ‘IS_SOME (LNTH y ts)’
 >- (MATCH_MP_TAC LNTH_IS_SOME_MONO \\
     Q.EXISTS_TAC ‘x’ >> rw [IS_SOME_EXISTS])
 >> rw [IS_SOME_EXISTS]
 >> simp []
QED

Theorem sibling_inclusive_ltree_paths :
    !t. sibling_inclusive (ltree_paths t)
Proof
    rw [sibling_inclusive_def]
 >> irule sibling_inclusive_ltree_paths_lemma >> art []
 >> Q.EXISTS_TAC ‘p’ >> art []
QED

Theorem sibling_inclusive_union :
    !s1 s2. sibling_inclusive s1 /\ sibling_inclusive s2 ==>
            sibling_inclusive (s1 UNION s2)
Proof
    rw [sibling_inclusive_def, IN_UNION]
 >| [ (* goal 1 (of 2) *)
      DISJ1_TAC \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘p’ >> art [],
      (* goal 2 (of 2) *)
      DISJ2_TAC \\
      FIRST_X_ASSUM MATCH_MP_TAC \\
      Q.EXISTS_TAC ‘p’ >> art [] ]
QED

Theorem ltree_path_lt_sibling :
    !p q. p <> [] /\ q <> [] /\ FRONT p = FRONT q /\ LAST p < LAST q ==>
          ltree_path_lt p q
Proof
    Induct_on ‘p’ >> rw []
 >> Cases_on ‘q’ >> gs []
 >> Know ‘LENGTH p = LENGTH t’
 >- (Q.PAT_X_ASSUM ‘FRONT (h::p) = FRONT (h'::t)’
       (MP_TAC o AP_TERM “LENGTH :num list -> num”) \\
     simp [])
 >> rw []
 >> Know ‘h <= h'’
 >- (Cases_on ‘p’ >> gs [] \\
     Cases_on ‘t’ >> gs [])
 >> DISCH_TAC
 >> ‘h < h' \/ h = h'’ by rw []
 >> simp []
 >> Cases_on ‘p = []’ >> gs []
 >> Cases_on ‘t = []’ >> gs []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Cases_on ‘p’ >> gs []
 >> Cases_on ‘t’ >> gs []
QED

Theorem ltree_path_lt_sibling' :
    !x y xs. x < y ==> ltree_path_lt (SNOC x xs) (SNOC y xs)
Proof
    rpt STRIP_TAC
 >> MATCH_MP_TAC ltree_path_lt_sibling
 >> REWRITE_TAC [FRONT_SNOC, LAST_SNOC]
 >> simp []
QED

Theorem finite_branching_ltree_el_cases :
    !p t. finite_branching t /\ p IN ltree_paths t ==>
          ?d m. ltree_el t p = SOME (d,SOME m)
Proof
    Induct_on ‘p’
 >- (Q.X_GEN_TAC ‘t’ >> Cases_on ‘t’ \\
     rw [ltree_el_def, ltree_paths_alt_ltree_el] \\
     fs [LFINITE_LLENGTH])
 >> rw [ltree_paths_alt_ltree_el]
 >> Cases_on ‘t’ >> fs [ltree_el_def]
 >> Cases_on ‘LNTH h ts’ >> fs []
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> simp [ltree_paths_alt_ltree_el]
 >> fs [every_LNTH]
 >> FIRST_X_ASSUM MATCH_MP_TAC
 >> Q.EXISTS_TAC ‘h’ >> art []
QED

(* tidy up theory exports *)

val _ = List.app Theory.delete_binding
  ["Branch_rep_def", "dest_Branch_rep_def", "make_ltree_rep_def",
   "make_unfold_def", "path_ok_def", "ltree_absrep", "ltree_absrep",
   "gen_ltree_def", "ltree_rep_ok_def", "Branch",
   "from_rose_def_primitive", "ltree_finite_def"];

val _ = export_theory();
