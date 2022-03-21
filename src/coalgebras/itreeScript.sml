(*
  This file defines a type for potentially infinite interaction
  trees. We take inspiration from the itree type of Xia et al.'s
  POPL'20 paper titled "Interaction Trees".

  Interaction trees are interesting because they can both represent a
  program's observable I/O behaviour and also model of the I/O
  behaviour of the external world.

  Our version of the type for interaction trees, itree, has the
  following constructors.  Here Ret ends an interaction tree with a
  return value; Div is internal silent divergence (an infinite run of
  Taus); Vis is a visible event that returns a value that the rest of
  the interaction tree can depend on.

    ('a,'e,'r) itree  =
       Ret 'r                          -- termination with result 'r
    |  Div                             -- end in silent divergence
    |  Vis 'e ('a -> ('a,'e,'r) itree) -- visible event 'e with answer 'a,
                                          then continue based on answer

  The POPL paper includes a silent Tau action:

    |  Tau (('a,'e,'r) itree)          --  a silent action, then continue

  We omit Tau since it makes reasoning about intereaction trees
  messy. It causes a mess because one then has to deal with equality
  up to deletion of finite runs of Tau actions, ugh. We model an
  infinite run of Taus using Div.
*)
open HolKernel Parse boolLib bossLib dep_rewrite;
open listTheory combinTheory;

val _ = new_theory "itree";

val _ = set_grammar_ancestry ["list"];

(* make type definition *)

Datatype:
  itree_el = Event 'e | Return 'r | Stuck
End

Type itree_rep[local] = ``:'a list -> ('e,'r) itree_el``;
val f = ``(f: ('a,'e,'r) itree_rep)``

Definition path_ok_def:
  path_ok path ^f <=>
    !xs y ys.
      path = xs ++ y::ys ==>
      f xs <> Stuck /\ !z. f xs <> Return z (* a path cannot continue past a Stuck/Return *)
End

Definition itree_rep_ok_def:
  itree_rep_ok ^f <=>
    (* every bad path leads to the Return ARB element *)
    !path. ~path_ok path f ==> f path = Return ARB
End

Theorem type_inhabited[local]:
  ?f. itree_rep_ok ^f
Proof
  qexists_tac `\p. Return ARB` \\ fs [itree_rep_ok_def]
QED

val itree_tydef = new_type_definition ("itree", type_inhabited);

val repabs_fns = define_new_type_bijections
  { name = "itree_absrep",
    ABS  = "itree_abs",
    REP  = "itree_rep",
    tyax = itree_tydef};


(* prove basic theorems about rep and abs fucntions *)

val itree_absrep = CONJUNCT1 repabs_fns
val itree_repabs = CONJUNCT2 repabs_fns

Theorem itree_rep_ok_itree_rep[local,simp]:
  !t. itree_rep_ok (itree_rep t)
Proof
  fs [itree_repabs, itree_absrep]
QED

Theorem itree_abs_11[local]:
  itree_rep_ok r1 /\ itree_rep_ok r2 ==> ((itree_abs r1 = itree_abs r2) = (r1 = r2))
Proof
  fs [itree_repabs, EQ_IMP_THM] \\ metis_tac []
QED

Theorem itree_rep_11[local]:
  (itree_rep t1 = itree_rep t2) = (t1 = t2)
Proof
  fs [EQ_IMP_THM] \\ metis_tac [itree_absrep]
QED


(* define constructors *)

Definition Ret_rep_def:
  Ret_rep (x:'r) =
    \path. if path = [] then Return x else Return ARB
End

Definition Div_rep_def:
  Div_rep =
    \path. if path = [] then Stuck else Return ARB
End

Definition Vis_rep_def:
  Vis_rep e g =
    \path. case path of
           | [] => Event e
           | (a::rest) => g a rest
End

Definition Ret_def:
  Ret x = itree_abs (Ret_rep x)
End

Definition Div_def:
  Div = itree_abs Div_rep
End

Definition Vis_def:
  Vis e g = itree_abs (Vis_rep e (itree_rep o g))
End

Theorem itree_rep_ok_Ret[local]:
  !x. itree_rep_ok (Ret_rep x : ('a,'b,'c) itree_rep)
Proof
  fs [itree_rep_ok_def,Ret_rep_def]
  \\ rw [] \\ fs [path_ok_def]
QED

Theorem itree_rep_ok_Div[local]:
  itree_rep_ok (Div_rep : ('a,'b,'c) itree_rep)
Proof
  fs [itree_rep_ok_def,Div_rep_def]
  \\ rw [] \\ fs [path_ok_def]
QED

Theorem itree_rep_ok_Vis[local]:
  !a g. (!a. itree_rep_ok (g a)) ==>
        itree_rep_ok (Vis_rep e g  : ('a,'b,'c) itree_rep)
Proof
  fs [itree_rep_ok_def,Vis_rep_def]
  \\ rw [] \\ CCONTR_TAC \\ fs [AllCaseEqs()]
  \\ Cases_on `path` \\ fs [] THEN1 fs [path_ok_def]
  \\ qpat_x_assum `~(path_ok _ _)` mp_tac \\ fs []
  \\ simp [path_ok_def] \\ rw [] \\ rename [‘h::t = path ++ [y] ++ ys’]
  \\ Cases_on `path` \\ fs [] \\ rw []
  \\ CCONTR_TAC \\ fs []
  \\ rename [`xs ++ [y] ++ ys`] \\ fs []
  \\ first_x_assum (qspecl_then [`h`,`xs ++ [y] ++ ys`] mp_tac)
  \\ fs [] \\ rw [] \\ fs [path_ok_def]
  \\ metis_tac []
QED


(* prove injectivity *)

Theorem Ret_rep_11[local]:
  !x y. Ret_rep x = Ret_rep y <=> x = y
Proof
  fs [Ret_rep_def,FUN_EQ_THM]
  \\ rpt gen_tac \\ eq_tac \\ rw []
  \\ first_x_assum (qspec_then `[]` mp_tac) \\ fs []
QED

Theorem Ret_11:
  !x y. Ret x = Ret y <=> x = y
Proof
  rw [Ret_def] \\ eq_tac \\ strip_tac \\ fs []
  \\ metis_tac [itree_rep_ok_Ret,itree_abs_11,Ret_rep_11]
QED

Theorem Vis_rep_11[local]:
  !x y g g'. Vis_rep x g = Vis_rep y g' <=> x = y /\ g = g'
Proof
  fs [Vis_rep_def,Once FUN_EQ_THM]
  \\ rpt gen_tac \\ eq_tac \\ simp [] \\ strip_tac
  \\ first_assum (qspec_then `[]` assume_tac) \\ fs []
  \\ fs [FUN_EQ_THM] \\ rw []
  \\ rename [`g x1 x2 = _`]
  \\ first_x_assum (qspec_then `x1 :: x2` mp_tac) \\ fs []
QED

Theorem Vis_11:
  !x f y g. Vis x f = Vis y g <=> x = y /\ f = g
Proof
  rw [Vis_def] \\ eq_tac \\ strip_tac \\ fs []
  \\ qmatch_asmsub_abbrev_tac `_ x1 = _ x2`
  \\ `itree_rep_ok x1 /\ itree_rep_ok x2` by
      (unabbrev_all_tac \\ rw [] \\ match_mp_tac itree_rep_ok_Vis \\ fs [])
  \\ fs [itree_abs_11] \\ unabbrev_all_tac \\ fs [Vis_rep_11]
  \\ fs [FUN_EQ_THM,itree_rep_11]
  \\ fs [GSYM itree_rep_11] \\ fs [FUN_EQ_THM]
QED

Theorem itree_11 = LIST_CONJ [Ret_11, Vis_11];


(* distinctness theorem *)

Theorem itree_all_distinct[local]:
  !x e g. ALL_DISTINCT [Ret x; Div; Vis e g :('a,'b,'c) itree]
Proof
  rw [Ret_def,Div_def,Vis_def]
  \\ assume_tac itree_rep_ok_Div
  \\ qspec_then `x` assume_tac itree_rep_ok_Ret
  \\ qspec_then `t` assume_tac itree_rep_ok_itree_rep
  \\ qspecl_then [`e`,`itree_rep o g`] mp_tac itree_rep_ok_Vis
  \\ impl_tac THEN1 fs []
  \\ rw [] \\ simp [itree_abs_11]
  \\ rw [] \\ fs [FUN_EQ_THM]
  \\ qexists_tac `[]` \\ fs [Ret_rep_def,Div_rep_def,Vis_rep_def]
QED

Theorem itree_distinct = itree_all_distinct
  |> SIMP_RULE std_ss [ALL_DISTINCT,MEM,GSYM CONJ_ASSOC] |> SPEC_ALL |>
  CONJUNCTS |> map GEN_ALL |> LIST_CONJ;


(* prove cases theorem *)

Theorem rep_exists[local]:
  itree_rep_ok f ==>
    (?x. f = Ret_rep x) \/
    (f = Div_rep) \/
    ?a g. f = Vis_rep a g /\ !v. itree_rep_ok (g v)
Proof
  fs [itree_rep_ok_def] \\ rw []
  \\ reverse (Cases_on `f []`)
  THEN1
   (disj2_tac \\ disj1_tac
    \\ fs [FUN_EQ_THM]
    \\ Cases \\ fs [Div_rep_def]
    \\ first_x_assum match_mp_tac
    \\ fs [path_ok_def]
    \\ qexists_tac `[]` \\ fs [])
  THEN1
   (disj1_tac
    \\ qexists_tac ‘r’ \\ fs []
    \\ fs [FUN_EQ_THM]
    \\ Cases \\ fs [Ret_rep_def]
    \\ first_x_assum match_mp_tac
    \\ fs [path_ok_def]
    \\ qexists_tac `[]` \\ fs [])
  \\ rpt disj2_tac
  \\ fs [Vis_rep_def,FUN_EQ_THM]
  \\ qexists_tac `e`
  \\ qexists_tac `\a path. f (a::path)`
  \\ rw [] THEN1 (Cases_on `x` \\ fs [])
  \\ first_x_assum match_mp_tac
  \\ fs [path_ok_def]
  \\ metis_tac [APPEND,APPEND_ASSOC]
QED

Theorem itree_cases:
  !t. (?x. t = Ret x) \/ (t = Div) \/ (?a g. t = Vis a g)
Proof
  fs [GSYM itree_rep_11,Ret_def,Div_def,Vis_def] \\ gen_tac
  \\ qabbrev_tac `f = itree_rep t`
  \\ `itree_rep_ok f` by fs [Abbr`f`]
  \\ drule rep_exists \\ strip_tac \\ fs [] \\ rw []
  \\ imp_res_tac itree_repabs \\ fs []
  THEN1 metis_tac []
  \\ rpt disj2_tac
  \\ qexists_tac `a`
  \\ qexists_tac `itree_abs o g`
  \\ qsuff_tac `itree_rep o itree_abs o g = g` THEN1 fs []
  \\ fs [o_DEF,Once FUN_EQ_THM]
  \\ metis_tac [itree_repabs]
QED


(* itree_CASE constant *)

Definition itree_CASE[nocompute]:
  itree_CASE (t:('a,'e,'r) itree) ret div vis =
    case itree_rep t [] of
    | Return r => ret r
    | Stuck    => div
    | Event e  => vis e (\a. (itree_abs (\path. itree_rep t (a::path))))
End

Theorem itree_CASE[compute]:
  itree_CASE (Ret r)   ret div vis = ret r /\
  itree_CASE Div       ret div vis = div /\
  itree_CASE (Vis a g) ret div vis = vis a g
Proof
  rw [itree_CASE,Ret_def,Div_def,Vis_def]
  \\ qmatch_goalsub_abbrev_tac `itree_rep (itree_abs xx)`
  THEN1
   (`itree_rep_ok xx` by fs [Abbr`xx`,itree_rep_ok_Ret]
    \\ fs [itree_repabs] \\ unabbrev_all_tac
    \\ fs [Ret_rep_def])
  THEN1
   (`itree_rep_ok xx` by fs [Abbr`xx`,itree_rep_ok_Div]
    \\ fs [itree_repabs] \\ unabbrev_all_tac
    \\ fs [Div_rep_def])
  THEN1
   (`itree_rep_ok xx` by
      (fs [Abbr`xx`] \\ match_mp_tac itree_rep_ok_Vis \\ fs [])
    \\ fs [itree_repabs] \\ unabbrev_all_tac
    \\ fs [Vis_rep_def]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [itree_absrep]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
QED

Theorem itree_CASE_eq:
  itree_CASE t ret div vis = v <=>
    (?r. t = Ret r /\ ret r = v) \/
    (t = Div /\ div = v) \/
    (?a g. t = Vis a g /\ vis a g = v)
Proof
  qspec_then `t` strip_assume_tac itree_cases \\ rw []
  \\ fs [itree_CASE,itree_11,itree_distinct]
QED


(* itree unfold *)

Datatype:
  itree_next = Ret' 'r
          | Div'
          | Vis' 'e ('a -> 'seed)
End

Definition itree_unfold_path_def:
  (itree_unfold_path f seed [] =
     case f seed of
     | Ret' r   => Return r
     | Div'     => Stuck
     | Vis' e g => Event e) /\
  (itree_unfold_path f seed (n::rest) =
     case f seed of
     | Ret' r   => Return ARB
     | Div'     => Return ARB
     | Vis' e g => itree_unfold_path f (g n) rest)
End

Definition itree_unfold:
  itree_unfold f seed = itree_abs (itree_unfold_path f seed)
End

Theorem itree_rep_abs_itree_unfold_path[local]:
  itree_rep (itree_abs (itree_unfold_path f s)) = itree_unfold_path f s
Proof
  fs [GSYM itree_repabs] \\ fs [itree_rep_ok_def]
  \\ qid_spec_tac `s`
  \\ Induct_on `path` THEN1 fs [path_ok_def]
  \\ fs [itree_unfold_path_def]
  \\ rw [] \\ Cases_on `f s` \\ fs [] \\ rw []
  \\ first_x_assum match_mp_tac
  \\ fs [path_ok_def]
  \\ Cases_on `xs` \\ fs [] \\ rw []
  \\ fs [itree_unfold_path_def] \\ metis_tac []
QED

Theorem itree_unfold:
  itree_unfold f seed =
    case f seed of
    | Ret' r   => Ret r
    | Div'     => Div
    | Vis' e g => Vis e (itree_unfold f o g)
Proof
  Cases_on `f seed` \\ fs []
  THEN1
   (fs [itree_unfold,Ret_def] \\ AP_TERM_TAC \\ fs [FUN_EQ_THM]
    \\ Cases \\ fs [itree_unfold_path_def,Ret_rep_def]
    \\ Cases_on `h` \\ fs [itree_unfold_path_def,Ret_rep_def])
  THEN1
   (fs [itree_unfold,Div_def] \\ AP_TERM_TAC \\ fs [FUN_EQ_THM]
    \\ Cases \\ fs [itree_unfold_path_def,Div_rep_def]
    \\ Cases_on `h` \\ fs [itree_unfold_path_def,Div_rep_def])
  \\ fs [itree_unfold,Vis_def] \\ AP_TERM_TAC \\ fs [FUN_EQ_THM]
  \\ Cases \\ fs [itree_unfold_path_def,Vis_rep_def]
  \\ fs [itree_unfold_path_def,Vis_rep_def]
  \\ fs [itree_unfold,itree_rep_abs_itree_unfold_path]
QED


(* itree_unfold with errors - i.e. the environment can return an error *)

Definition itree_unfold_err_path_def:
  (itree_unfold_err_path f (rel, err_f, err) seed [] =
     case f seed of
     | Ret' r   => Return r
     | Div'     => Stuck
     | Vis' e g => Event e) /\
  (itree_unfold_err_path f (rel, err_f, err) seed (n::rest) =
     case f seed of
     | Ret' r   => Return ARB
     | Div'     => Return ARB
     | Vis' e g =>
        case n of
        | INL x => if rest = [] then Return (err_f e x) else Return ARB
        | INR y =>
            if rel e y then itree_unfold_err_path f (rel, err_f, err) (g y) rest
            else if rest = [] then Return $ err e else Return ARB)
End

Definition itree_unfold_err:
  itree_unfold_err f err seed =
    itree_abs (itree_unfold_err_path f err seed)
End

Theorem itree_rep_abs_itree_unfold_err_path[local]:
  itree_rep (itree_abs (itree_unfold_err_path f err s)) =
  itree_unfold_err_path f err s
Proof
  gvs[GSYM itree_repabs, itree_rep_ok_def] >>
  qid_spec_tac `s` >> Induct_on `path` >- gvs[path_ok_def] >>
  PairCases_on `err` >> gvs[itree_unfold_err_path_def] >> rw[] >>
  Cases_on ‘f s’ >> fs [] >>
  rename [‘h::path’] >> Cases_on ‘h’ >> fs []
  >- gvs[path_ok_def, APPEND_EQ_CONS, itree_unfold_err_path_def] >>
  reverse IF_CASES_TAC >> fs []
  >- gvs[path_ok_def, APPEND_EQ_CONS, itree_unfold_err_path_def] >>
  first_x_assum irule >>
  gvs [path_ok_def] >>
  gvs[path_ok_def, APPEND_EQ_CONS, itree_unfold_err_path_def] >>
  metis_tac []
QED

Theorem itree_unfold_err:
  itree_unfold_err f (rel, err_f, err) seed =
    case f seed of
    | Ret' r   => Ret r
    | Div'     => Div
    | Vis' e g =>
        Vis e
          (λa. case a of
                  INL x => Ret $ err_f e x
                | INR y =>
                    if rel e y then itree_unfold_err f (rel, err_f, err) (g y)
                    else Ret $ err e)
Proof
  Cases_on ‘f seed’ >> once_rewrite_tac [itree_unfold_err] >>
  gvs[Ret_def, Div_def, Vis_def] >> AP_TERM_TAC >> simp[FUN_EQ_THM] >>
  Cases >> gvs[itree_unfold_err_path_def, Ret_rep_def, Div_rep_def, Vis_rep_def] >>
  Cases_on ‘h’ >> gvs[itree_rep_abs_itree_unfold_err_path] >>
  TRY IF_CASES_TAC >> Cases_on ‘t’ >> gvs[itree_rep_abs_itree_unfold_err_path] >>
  Cases_on ‘f (f' y)’ >> gvs [] >>
  once_rewrite_tac [itree_unfold_err] >> gvs [] >>
  once_rewrite_tac [GSYM itree_unfold_err] >> gvs [] >>
  gvs[Ret_def, Div_def, Vis_def, Ret_rep_def, Div_rep_def, Vis_rep_def] >>
  DEP_REWRITE_TAC[iffLR itree_repabs] >> simp[] >>
  gvs[itree_rep_ok_def, path_ok_def, PULL_EXISTS]
QED


(* proving equivalences *)

Definition itree_el_def:
  itree_el t [] =
    itree_CASE t (\r. Return r) Stuck (\e g. Event e) /\
  itree_el t (a::ns) =
    itree_CASE t (\r. Return ARB) (Return ARB) (\e g. itree_el (g a) ns)
End

Theorem itree_el_def:
  itree_el (Ret r) []   = Return r /\
  itree_el Div []       = Stuck /\
  itree_el (Vis e g) [] = Event e /\
  itree_el (Ret r) (a::ns)   = Return ARB /\
  itree_el Div (a::ns)       = Return ARB /\
  itree_el (Vis e g) (a::ns) = itree_el (g a) ns
Proof
  fs [itree_el_def,itree_CASE]
QED

Theorem itree_el_eqv:
  !t1 t2. t1 = t2 <=> !path. itree_el t1 path = itree_el t2 path
Proof
  rw [] \\ eq_tac \\ rw []
  \\ fs [GSYM itree_rep_11,FUN_EQ_THM] \\ rw []
  \\ pop_assum mp_tac
  \\ qid_spec_tac `t1` \\ qid_spec_tac `t2`
  \\ Induct_on `x` \\ rw []
  \\ `itree_rep_ok (itree_rep t1) /\ itree_rep_ok (itree_rep t2)`
        by fs [itree_rep_ok_itree_rep]
  \\ qspec_then `t1` strip_assume_tac itree_cases
  \\ qspec_then `t2` strip_assume_tac itree_cases
  \\ rpt BasicProvers.var_eq_tac
  \\ TRY (first_x_assum (qspec_then `[]` mp_tac)
          \\ fs [itree_el_def] \\ NO_TAC)
  \\ first_assum (qspec_then `[]` mp_tac)
  \\ rewrite_tac [itree_el_def] \\ rw []
  \\ fs [Vis_def]
  \\ qmatch_abbrev_tac
      `itree_rep (itree_abs t1) _ = itree_rep (itree_abs t2) _`
  \\ `itree_rep_ok t1 /\ itree_rep_ok t2` by
   (rw [] \\ unabbrev_all_tac
    \\ TRY (match_mp_tac itree_rep_ok_Vis) \\ fs [])
  \\ fs [itree_repabs]
  \\ TRY (unabbrev_all_tac \\ fs [Vis_rep_def] \\ NO_TAC)
  \\ unabbrev_all_tac \\ fs [GSYM Vis_def]
  \\ fs [Vis_rep_def] \\ fs []
  \\ first_x_assum (qspecl_then [`g h`,`g' h`] mp_tac)
  \\ impl_tac THEN1
   (rw [] \\ first_x_assum (qspec_then `h::path` mp_tac) \\ fs [itree_el_def])
  \\ fs [Vis_rep_def]
QED

Theorem itree_bisimulation:
  !t1 t2.
    t1 = t2 <=>
    ?R. R t1 t2 /\
        (!x t. R (Ret x) t ==> t = Ret x) /\
        (!t. R Div t ==> t = Div) /\
        (!a f t. R (Vis a f) t ==> ?b g. t = Vis a g /\ !s. R (f s) (g s))
Proof
  rw [] \\ eq_tac \\ rw []
  THEN1 (qexists_tac `(=)` \\ fs [itree_11])
  \\ simp [itree_el_eqv] \\ strip_tac
  \\ last_x_assum mp_tac \\ qid_spec_tac `t1` \\ qid_spec_tac `t2`
  \\ Induct_on `path` \\ rw []
  \\ qspec_then `t1` strip_assume_tac itree_cases
  \\ qspec_then `t2` strip_assume_tac itree_cases
  \\ fs [itree_el_def]
  \\ res_tac \\ fs [itree_11,itree_distinct] \\ rw []
  \\ Cases_on `h` \\ fs [itree_el_def]
QED


(* register with TypeBase *)

Theorem itree_CASE_cong:
  !M M' ret div vis ret' div' vis'.
    M = M' /\
    (!x. M' = Ret x ==> ret x = ret' x) /\
    (M' = Div ==> div = div') /\
    (!a g. M' = Vis a g ==> vis a g = vis' a g) ==>
    itree_CASE M ret div vis = itree_CASE M' ret' div' vis'
Proof
  rw [] \\ qspec_then `M` strip_assume_tac itree_cases
  \\ rw [] \\ fs [itree_CASE]
QED

Theorem datatype_itree:
  DATATYPE ((itree
    (Ret : 'r -> ('a, 'e, 'r) itree)
    (Div : ('a, 'e, 'r) itree)
    (Vis : 'e -> ('a -> ('a, 'e, 'r) itree) -> ('a, 'e, 'r) itree)):bool)
Proof
  rw [boolTheory.DATATYPE_TAG_THM]
QED

val _ = TypeBase.export
  [TypeBasePure.mk_datatype_info
    { ax = TypeBasePure.ORIG TRUTH,
      induction = TypeBasePure.ORIG itree_bisimulation,
      case_def = itree_CASE,
      case_cong = itree_CASE_cong,
      case_eq = itree_CASE_eq,
      nchotomy = itree_cases,
      size = NONE,
      encode = NONE,
      lift = NONE,
      one_one = SOME itree_11,
      distinct = SOME itree_distinct,
      fields = [],
      accessors = [],
      updates = [],
      destructors = [],
      recognizers = [] } ]


(* tidy up theory exports *)

val _ = List.app Theory.delete_binding
  ["Ret_rep_def", "Ret_def",
   "Div_rep_def", "Div_def",
   "Vis_rep_def", "Vis_def",
   "path_ok_def", "itree_rep_ok_def",
   "itree_unfold_path_def", "itree_unfold_path_ind",
   "itree_unfold_err_path_def", "itree_unfold_err_path_ind",
   "itree_el_TY_DEF", "itree_absrep", "itree_next_TY_DEF"];

val _ = export_theory();
