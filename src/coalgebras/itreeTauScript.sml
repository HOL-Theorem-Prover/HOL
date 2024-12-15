(*
  This file defines a type for potentially infinite interaction
  trees. We take inspiration from the itree type of Xia et al.'s
  POPL'20 paper titled "Interaction Trees".

  Interaction trees are interesting because they can both represent a
  program's observable I/O behaviour and also model of the I/O
  behaviour of the external world.

  Our version of the type for interaction trees, itree, has the
  following constructors.  Here Ret ends an interaction tree with a
  return value; Tau is the silent action; Vis is a visible event that
  returns a value that the rest of the interaction tree can depend on.

    ('a,'e,'r) itree  =
       Ret 'r                           --  termination with result 'r
    |  Tau (('a,'e,'r) itree)           --  a silent action, then continue
    |  Vis 'e ('a -> ('a,'e,'r) itree)  --  visible event 'e with answer 'a,
                                            then continue based on answer
*)
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory llistTheory alistTheory optionTheory;
open mp_then pred_setTheory relationTheory pairTheory combinTheory;
open itreeTheory;

val _ = new_theory "itreeTau";


(* make type definition *)

Datatype:
  itree_el = Event 'e | Return 'r | Silence
End

Type itree_rep[local] = “:('a option) list -> ('e,'r) itree_el”;
val f = “(f: ('a,'e,'r) itree_rep)”

Definition path_ok_def:
  path_ok path ^f <=>
    !xs y ys.
      path = xs ++ y::ys ==>
      case f xs of
      | Return _ => F         (* a path cannot continue past a Return *)
      | Silence  => y = NONE  (* Silence consumes no input *)
      | Event e  => IS_SOME y (* the next element must be an input *)
End

Definition itree_rep_ok_def:
  itree_rep_ok ^f <=>
    (* every bad path leads to the Silence element *)
    !path. ~path_ok path f ==> f path = Silence
End

Theorem type_inhabited[local]:
  ?f. itree_rep_ok ^f
Proof
  qexists_tac ‘\p. Silence’ \\ fs [itree_rep_ok_def]
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
  itree_rep_ok r1 /\ itree_rep_ok r2 ==>
  (itree_abs r1 = itree_abs r2 <=> r1 = r2)
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
    \path. if path = [] then Return x else Silence
End

Definition Tau_rep_def:
  Tau_rep ^f =
    \path. case path of
           | (NONE::rest) => f rest
           | _ => Silence
End

Definition Vis_rep_def:
  Vis_rep e g =
    \path. case path of
           | [] => Event e
           | (NONE::rest) => Silence
           | (SOME a::rest) => g a rest
End

Definition Ret_def:
  Ret x = itree_abs (Ret_rep x)
End

Definition Tau_def:
  Tau t = itree_abs (Tau_rep (itree_rep t))
End

Definition Vis_def:
  Vis e g = itree_abs (Vis_rep e (itree_rep o g))
End

Theorem itree_rep_ok_Ret[local]:
  !x. itree_rep_ok (Ret_rep x : ('a,'e,'r) itree_rep)
Proof
  fs [itree_rep_ok_def,Ret_rep_def]
  \\ rw [] \\ fs [path_ok_def]
QED

Theorem itree_rep_ok_Tau[local]:
  !f. itree_rep_ok f ==> itree_rep_ok (Tau_rep ^f)
Proof
  fs [itree_rep_ok_def,Tau_rep_def]
  \\ rw [] \\ CCONTR_TAC \\ fs [AllCaseEqs()]
  \\ Cases_on ‘path’ \\ fs []
  \\ Cases_on ‘h’ \\ fs [] \\ rw []
  \\ qpat_x_assum ‘~(path_ok _ _)’ mp_tac \\ fs []
  \\ simp [path_ok_def] \\ rw []
  \\ rename [‘NONE :: t = path ++ [y] ++ ys’]
  \\ Cases_on ‘path’ \\ fs [] \\ rw []
  \\ rename [‘xs ++ [y] ++ ys’]
  \\ first_x_assum (qspec_then ‘xs ++ [y] ++ ys’ mp_tac)
  \\ fs [] \\ rw [] \\ fs [path_ok_def]
QED

Theorem itree_rep_ok_Vis[local]:
  !a g. (!a. itree_rep_ok (g a)) ==> itree_rep_ok (Vis_rep e g)
Proof
  fs [itree_rep_ok_def,Vis_rep_def]
  \\ rw [] \\ CCONTR_TAC \\ fs [AllCaseEqs()]
  \\ Cases_on ‘path’ \\ fs [] THEN1 fs [path_ok_def]
  \\ Cases_on ‘h’ \\ fs [] \\ rw []
  \\ qpat_x_assum ‘~(path_ok _ _)’ mp_tac \\ fs []
  \\ simp [path_ok_def] \\ rw []
  \\ rename [‘SOME _ :: _ = path ++ [y] ++ ys’]
  \\ Cases_on ‘path’ \\ fs [] \\ rw []
  \\ rename [‘xs ++ [y] ++ ys’]
  \\ first_x_assum (qspecl_then [‘x’,‘xs ++ [y] ++ ys’] mp_tac)
  \\ fs [] \\ rw [] \\ fs [path_ok_def]
QED


(* prove injectivity *)

Theorem Ret_rep_11[local]:
  !x y. Ret_rep x = Ret_rep y <=> x = y
Proof
  fs [Ret_rep_def,FUN_EQ_THM]
  \\ rpt gen_tac \\ eq_tac \\ rw []
  \\ first_x_assum (qspec_then ‘[]’ mp_tac) \\ fs []
QED

Theorem Ret_11:
  !x y. Ret x = Ret y <=> x = y
Proof
  rw [Ret_def] \\ eq_tac \\ strip_tac \\ fs []
  \\ metis_tac [itree_rep_ok_Ret,itree_abs_11,Ret_rep_11]
QED

Theorem Tau_rep_11[local]:
  !x y. Tau_rep x = Tau_rep y <=> x = y
Proof
  fs [Tau_rep_def,Once FUN_EQ_THM]
  \\ rpt gen_tac \\ eq_tac \\ rw []
  \\ fs [FUN_EQ_THM] \\ strip_tac
  \\ rename [‘_ path = _’]
  \\ first_x_assum (qspec_then ‘NONE::path’ mp_tac) \\ fs []
QED

Theorem Tau_11:
  !x y. Tau x = Tau y <=> x = y
Proof
  rw [Tau_def] \\ eq_tac \\ strip_tac \\ fs []
  \\ qspec_then ‘x’ assume_tac itree_rep_ok_itree_rep
  \\ drule itree_rep_ok_Tau
  \\ qspec_then ‘y’ assume_tac itree_rep_ok_itree_rep
  \\ drule itree_rep_ok_Tau \\ rw []
  \\ fs [itree_abs_11,Tau_rep_11,itree_rep_11]
QED

Theorem Vis_rep_11[local]:
  !x y g g'. Vis_rep x g = Vis_rep y g' <=> x = y /\ g = g'
Proof
  fs [Vis_rep_def,Once FUN_EQ_THM]
  \\ rpt gen_tac \\ eq_tac \\ simp [] \\ strip_tac
  \\ first_assum (qspec_then ‘[]’ assume_tac) \\ fs []
  \\ fs [FUN_EQ_THM] \\ rw []
  \\ rename [‘g x1 x2 = _’]
  \\ first_x_assum (qspec_then ‘SOME x1 :: x2’ mp_tac) \\ fs []
QED

Theorem Vis_11:
  !x f y g. Vis x f = Vis y g <=> x = y /\ f = g
Proof
  rw [Vis_def] \\ eq_tac \\ strip_tac \\ fs []
  \\ qmatch_assum_abbrev_tac ‘_ x1 = _ x2’
  \\ ‘itree_rep_ok x1 /\ itree_rep_ok x2’ by
      (unabbrev_all_tac \\ rw [] \\ match_mp_tac itree_rep_ok_Vis \\ fs [])
  \\ fs [itree_abs_11] \\ unabbrev_all_tac \\ fs [Vis_rep_11]
  \\ fs [FUN_EQ_THM,itree_rep_11]
  \\ fs [GSYM itree_rep_11] \\ fs [FUN_EQ_THM]
QED

Theorem itree_11 = LIST_CONJ [Ret_11, Tau_11, Vis_11];


(* distinctness theorem *)

Theorem itree_distinct_lemma[local]:
  ALL_DISTINCT [Ret x; Tau t; Vis e g]
Proof
  fs [ALL_DISTINCT,Ret_def,Tau_def,Vis_def]
  \\ qpat_abbrev_tac ‘xx = Ret_rep x’
  \\ ‘itree_rep_ok xx’ by fs [Abbr‘xx’,itree_rep_ok_Ret]
  \\ fs [Abbr‘xx’]
  \\ qspec_then ‘x’ assume_tac itree_rep_ok_Ret
  \\ qspec_then ‘t’ assume_tac itree_rep_ok_itree_rep
  \\ drule itree_rep_ok_Tau
  \\ qspecl_then [‘e’,‘itree_rep o g’] mp_tac itree_rep_ok_Vis
  \\ impl_tac THEN1 fs []
  \\ rpt (disch_then assume_tac)
  \\ simp [itree_abs_11]
  \\ rw [] \\ fs [FUN_EQ_THM]
  \\ qexists_tac ‘[]’ \\ fs [Ret_rep_def,Tau_rep_def,Vis_rep_def]
QED

Theorem itree_distinct =
  itree_distinct_lemma |> SIMP_RULE std_ss [ALL_DISTINCT,MEM,GSYM CONJ_ASSOC];


(* prove cases theorem *)

Theorem rep_exists[local]:
  itree_rep_ok f ==>
    (?x. f = Ret_rep x) \/
    (?u. f = Tau_rep u /\ itree_rep_ok u) \/
    ?a g. f = Vis_rep a g /\ !v. itree_rep_ok (g v)
Proof
  fs [itree_rep_ok_def] \\ rw []
  \\ reverse (Cases_on ‘f []’)
  THEN1
   (disj2_tac \\ disj1_tac
    \\ fs [Tau_rep_def,FUN_EQ_THM]
    \\ qexists_tac ‘\path. f (NONE::path)’
    \\ rw [] THEN1
     (Cases_on ‘x’ \\ fs []
      \\ Cases_on ‘h’ \\ fs []
      \\ first_x_assum match_mp_tac
      \\ fs [path_ok_def]
      \\ qexists_tac ‘[]’ \\ fs [])
    \\ first_x_assum match_mp_tac
    \\ fs [path_ok_def] \\ rw []
    \\ metis_tac [APPEND,APPEND_ASSOC])
  THEN1
   (disj1_tac
    \\ fs [Ret_rep_def,FUN_EQ_THM]
    \\ qexists_tac ‘r’ \\ rw []
    \\ first_x_assum match_mp_tac
    \\ fs [path_ok_def] \\ rw []
    \\ Cases_on ‘x'’ \\ fs []
    \\ qexists_tac ‘[]’ \\ fs [])
  \\ rpt disj2_tac
  \\ fs [Vis_rep_def,FUN_EQ_THM]
  \\ qexists_tac ‘e’
  \\ qexists_tac ‘\a path. f (SOME a::path)’
  \\ rw [] THEN1
   (Cases_on ‘x’ \\ fs []
    \\ Cases_on ‘h’ \\ fs []
    \\ first_x_assum match_mp_tac
    \\ fs [path_ok_def]
    \\ qexists_tac ‘[]’ \\ fs [])
  \\ first_x_assum match_mp_tac
  \\ fs [path_ok_def]
  \\ metis_tac [APPEND,APPEND_ASSOC]
QED

Theorem itree_cases:
  !t. (?x. t = Ret x) \/ (?u. t = Tau u) \/ (?a g. t = Vis a g)
Proof
  fs [GSYM itree_rep_11,Ret_def,Tau_def,Vis_def] \\ gen_tac
  \\ qabbrev_tac ‘f = itree_rep t’
  \\ ‘itree_rep_ok f’ by fs [Abbr‘f’]
  \\ drule rep_exists \\ strip_tac \\ fs [] \\ rw []
  \\ imp_res_tac itree_repabs \\ fs []
  THEN1 metis_tac [] THEN1 metis_tac []
  \\ rpt disj2_tac
  \\ qexists_tac ‘a’
  \\ qexists_tac ‘itree_abs o g’
  \\ qsuff_tac ‘itree_rep o itree_abs o g = g’ THEN1 fs []
  \\ fs [o_DEF,Once FUN_EQ_THM]
  \\ metis_tac [itree_repabs]
QED


(* itree_CASE constant *)

Definition itree_CASE[nocompute]:
  itree_CASE (t:('a,'e,'r) itree) ret tau vis =
    case itree_rep t [] of
    | Return r => ret r
    | Silence => tau (itree_abs (\path. itree_rep t (NONE::path)))
    | Event e => vis e (\a. (itree_abs (\path. itree_rep t (SOME a::path))))
End

Theorem itree_CASE[compute,allow_rebind]:
  itree_CASE (Ret r) ret tau vis = ret r /\
  itree_CASE (Tau t) ret tau vis = tau t /\
  itree_CASE (Vis a g) ret tau vis = vis a g
Proof
  rw [itree_CASE,Ret_def,Vis_def,Tau_def]
  \\ qmatch_goalsub_abbrev_tac ‘itree_rep (itree_abs xx)’
  THEN1
   (‘itree_rep_ok xx’ by fs [Abbr‘xx’,itree_rep_ok_Ret]
    \\ fs [itree_repabs] \\ unabbrev_all_tac
    \\ fs [Ret_rep_def])
  THEN1
   (‘itree_rep_ok xx’ by
      (fs [Abbr‘xx’] \\ match_mp_tac itree_rep_ok_Tau \\ fs [])
    \\ fs [itree_repabs] \\ unabbrev_all_tac
    \\ fs [Tau_rep_def]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [itree_absrep])
  THEN1
   (‘itree_rep_ok xx’ by
      (fs [Abbr‘xx’] \\ match_mp_tac itree_rep_ok_Vis \\ fs [])
    \\ fs [itree_repabs] \\ unabbrev_all_tac
    \\ fs [Vis_rep_def]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [itree_absrep]
    \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
QED

Theorem itree_CASE_eq:
  itree_CASE t ret tau vis = v <=>
    (?r. t = Ret r /\ ret r = v) \/
    (?u. t = Tau u /\ tau u = v) \/
    (?a g. t = Vis a g /\ vis a g = v)
Proof
  qspec_then ‘t’ strip_assume_tac itree_cases \\ rw []
  \\ fs [itree_CASE,itree_11,itree_distinct]
QED

Theorem itree_CASE_elim:
  !f.
  f(itree_CASE t ret tau vis) <=>
    (?r. t = Ret r /\ f(ret r)) \/
    (?u. t = Tau u /\ f(tau u)) \/
    (?a g. t = Vis a g /\ f(vis a g))
Proof
  qspec_then ‘t’ strip_assume_tac itree_cases \\ rw []
  \\ fs [itree_CASE,itree_11,itree_distinct]
QED

(* itree unfold *)

Datatype:
  itree_next = Ret' 'r
             | Tau' 'seed
             | Vis' 'e ('a -> 'seed)
End

Definition itree_unfold_path_def:
  (itree_unfold_path f seed [] =
     case f seed of
     | Ret' r => Return r
     | Tau' s => Silence
     | Vis' e g => Event e) /\
  (itree_unfold_path f seed (NONE::rest) =
     case f seed of
     | Ret' r => Silence
     | Tau' s => itree_unfold_path f s rest
     | Vis' e g => Silence) /\
  (itree_unfold_path f seed (SOME n::rest) =
     case f seed of
     | Ret' r => Silence
     | Tau' s => Silence
     | Vis' e g => itree_unfold_path f (g n) rest)
End

Definition itree_unfold:
  itree_unfold f seed = itree_abs (itree_unfold_path f seed)
End

Theorem itree_rep_abs_itree_unfold_path[local]:
  itree_rep (itree_abs (itree_unfold_path f s)) = itree_unfold_path f s
Proof
  fs [GSYM itree_repabs] \\ fs [itree_rep_ok_def]
  \\ qid_spec_tac ‘s’
  \\ Induct_on ‘path’ THEN1 fs [path_ok_def]
  \\ Cases_on ‘h’ \\ fs [itree_unfold_path_def]
  THEN1
   (rw [] \\ Cases_on ‘f s’ \\ fs [] \\ rw []
    \\ first_x_assum match_mp_tac
    \\ fs [path_ok_def]
    \\ Cases_on ‘xs’ \\ fs [] \\ rw []
    THEN1 (rfs [itree_unfold_path_def])
    \\ fs [itree_unfold_path_def] \\ metis_tac [])
  \\ rw [] \\ Cases_on ‘f s’ \\ fs [] \\ rw []
  \\ first_x_assum match_mp_tac
  \\ fs [path_ok_def]
  \\ Cases_on ‘xs’ \\ fs [] \\ rw []
  THEN1 (rfs [itree_unfold_path_def])
  \\ fs [itree_unfold_path_def] \\ metis_tac []
QED

Theorem itree_unfold[allow_rebind]:
  itree_unfold f seed =
    case f seed of
    | Ret' r   => Ret r
    | Tau' s   => Tau (itree_unfold f s)
    | Vis' e g => Vis e (itree_unfold f o g)
Proof
  Cases_on ‘f seed’ \\ fs []
  THEN1
   (fs [itree_unfold,Ret_def] \\ AP_TERM_TAC \\ fs [FUN_EQ_THM]
    \\ Cases \\ fs [itree_unfold_path_def,Ret_rep_def]
    \\ Cases_on ‘h’ \\ fs [itree_unfold_path_def,Ret_rep_def])
  THEN1
   (fs [itree_unfold,Tau_def] \\ AP_TERM_TAC \\ fs [FUN_EQ_THM]
    \\ Cases \\ fs [itree_unfold_path_def,Tau_rep_def]
    \\ Cases_on ‘h’ \\ fs [itree_unfold_path_def,Tau_rep_def]
    \\ fs [itree_rep_abs_itree_unfold_path])
  \\ fs [itree_unfold,Vis_def] \\ AP_TERM_TAC \\ fs [FUN_EQ_THM]
  \\ Cases \\ fs [itree_unfold_path_def,Vis_rep_def]
  \\ Cases_on ‘h’ \\ fs [itree_unfold_path_def,Vis_rep_def]
  \\ fs [itree_unfold,itree_rep_abs_itree_unfold_path]
QED

(* proving equivalences *)

Definition itree_el_def[nocompute]:
  itree_el t [] =
    itree_CASE t (\r. Return r) (\t. Silence) (\e g. Event e) /\
  itree_el t (NONE::ns) =
    itree_CASE t (\r. Silence) (\t. itree_el t ns) (\e g. Silence) /\
  itree_el t (SOME a::ns) =
    itree_CASE t (\r. Silence) (\t. Silence) (\e g. itree_el (g a) ns)
End

Theorem itree_el_thm[simp,compute]:
  itree_el (Ret r) [] = Return r /\
  itree_el (Tau t) [] = Silence /\
  itree_el (Vis e g) [] = Event e /\
  itree_el (Ret r) (NONE::ns) = Silence /\
  itree_el (Tau t) (NONE::ns) = itree_el t ns /\
  itree_el (Vis e g) (NONE::ns) = Silence /\
  itree_el (Ret r) (SOME a::ns) = Silence /\
  itree_el (Tau t) (SOME a::ns) = Silence /\
  itree_el (Vis e g) (SOME a::ns) = itree_el (g a) ns
Proof
  fs [itree_el_def,itree_CASE]
QED

Theorem itree_el_eqv:
  !t1 t2. t1 = t2 <=> !path. itree_el t1 path = itree_el t2 path
Proof
  rw [] \\ eq_tac \\ rw []
  \\ fs [GSYM itree_rep_11,FUN_EQ_THM] \\ rw []
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘t1’ \\ qid_spec_tac ‘t2’
  \\ Induct_on ‘x’ \\ rw []
  \\ ‘itree_rep_ok (itree_rep t1) /\ itree_rep_ok (itree_rep t2)’
        by fs [itree_rep_ok_itree_rep]
  \\ qspec_then ‘t1’ strip_assume_tac itree_cases
  \\ qspec_then ‘t2’ strip_assume_tac itree_cases
  \\ rpt BasicProvers.var_eq_tac
  \\ TRY (first_x_assum (qspec_then ‘[]’ mp_tac)
          \\ fs [] \\ NO_TAC)
  \\ first_assum (qspec_then ‘[]’ mp_tac)
  \\ rewrite_tac [itree_el_thm] \\ rw []
  \\ fs [Tau_def,Vis_def]
  \\ qmatch_abbrev_tac
      ‘itree_rep (itree_abs t1) _ = itree_rep (itree_abs t2) _’
  \\ ‘itree_rep_ok t1 /\ itree_rep_ok t2’ by
   (rw [] \\ unabbrev_all_tac
    \\ TRY (match_mp_tac itree_rep_ok_Tau) \\ fs []
    \\ TRY (match_mp_tac itree_rep_ok_Vis) \\ fs [])
  \\ fs [itree_repabs]
  \\ TRY (unabbrev_all_tac \\ fs [Tau_rep_def,Vis_rep_def] \\ NO_TAC)
  THEN1
   (unabbrev_all_tac \\ fs [GSYM Tau_def]
    \\ first_x_assum (qspecl_then [‘u’,‘u'’] mp_tac)
    \\ impl_tac THEN1
     (rw [] \\ first_x_assum (qspec_then ‘NONE::path’ mp_tac) \\ fs [])
    \\ fs [Tau_rep_def])
  \\ unabbrev_all_tac \\ fs [GSYM Vis_def]
  \\ fs [Vis_rep_def]
  \\ Cases_on ‘h’ \\ fs []
  \\ first_x_assum (qspecl_then [‘g x'’,‘g' x'’] mp_tac)
  \\ impl_tac THEN1
   (rw [] \\ first_x_assum (qspec_then ‘SOME x'::path’ mp_tac) \\ fs [])
  \\ fs [Vis_rep_def]
QED

Theorem itree_bisimulation:
  !t1 t2.
    t1 = t2 <=>
    ?R. R t1 t2 /\
        (!x t. R (Ret x) t ==> t = Ret x) /\
        (!u t. R (Tau u) t ==> ?v. t = Tau v /\ R u v) /\
        (!a f t. R (Vis a f) t ==> ?g. t = Vis a g /\ !s. R (f s) (g s))
Proof
  rw [] \\ eq_tac \\ rw []
  THEN1 (qexists_tac ‘(=)’ \\ fs [itree_11])
  \\ simp [itree_el_eqv] \\ strip_tac
  \\ last_x_assum mp_tac \\ qid_spec_tac ‘t1’ \\ qid_spec_tac ‘t2’
  \\ Induct_on ‘path’ \\ rw []
  \\ qspec_then ‘t1’ strip_assume_tac itree_cases
  \\ qspec_then ‘t2’ strip_assume_tac itree_cases
  \\ fs []
  \\ res_tac \\ fs [itree_11,itree_distinct] \\ rw []
  \\ Cases_on ‘h’ \\ fs []
QED

Theorem itree_strong_bisimulation:
  !t1 t2.
    t1 = t2 <=>
    ?R. R t1 t2 /\
        (!x t. R (Ret x) t ==> t = Ret x) /\
        (!u t. R (Tau u) t ==> ?v. t = Tau v /\ (R u v \/ u = v)) /\
        (!a f t. R (Vis a f) t ==> ?g. t = Vis a g /\
                                       !s. R (f s) (g s) \/ f s = g s)
Proof
  rpt strip_tac >>
  EQ_TAC
  >- (strip_tac >> first_x_assum $ irule_at $ Pos hd >> metis_tac[]) >>
  strip_tac >>
  ONCE_REWRITE_TAC[itree_bisimulation] >>
  qexists_tac ‘\x y. R x y \/ x = y’ >>
  metis_tac[]
QED

(* register with TypeBase *)

Theorem itree_CASE_cong:
  !M M' ret tau vis ret' tau' vis'.
    M = M' /\
    (!x. M' = Ret x ==> ret x = ret' x) /\
    (!t. M' = Tau t ==> tau t = tau' t) /\
    (!a g. M' = Vis a g ==> vis a g = vis' a g) ==>
    itree_CASE M ret tau vis = itree_CASE M' ret' tau' vis'
Proof
  rw [] \\ qspec_then ‘M’ strip_assume_tac itree_cases
  \\ rw [] \\ fs [itree_CASE]
QED

Theorem datatype_itree:
  DATATYPE ((itree
    (Ret : 'r -> ('a, 'e, 'r) itree)
    (Tau : ('a, 'e, 'r) itree -> ('a, 'e, 'r) itree)
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
      case_elim = itree_CASE_elim,
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

Overload "case" = “itree_CASE”

(* itree combinators *)

Definition itree_bind_def:
  itree_bind t k =
  itree_unfold
        (λx.
           case x of
             INL(Ret r) =>
               (case k r of
                  Ret s =>
                    Ret' s
                | Tau t =>
                    Tau' (INR t)
                | Vis e g =>
                     Vis' e (INR o g))
           | INL(Vis e g) => Vis' e (INL o g)
           | INL(Tau t) => Tau' (INL t)
           | INR(Ret r) => Ret' r
           | INR(Vis e g) => Vis' e (INR o g)
           | INR(Tau t) => Tau' (INR t)
        )
        (INL t)
End

Triviality itree_unfold_bind_INR:
  itree_unfold
  (λx.
     case x of
       INL (Ret r) =>
         itree_CASE (k r) (λs. Ret' s) (λt. Tau' (INR t))
                    (λe g. Vis' e (INR o g))
     | INL (Tau t) => Tau' (INL t)
     | INL (Vis e g) => Vis' e (INL o g)
     | INR (Ret r') => Ret' r'
     | INR (Tau t') => Tau' (INR t')
     | INR (Vis e' g') => Vis' e' (INR o g')) (INR u) =
  u
Proof
  rw[Once itree_bisimulation] >>
  qexists_tac ‘λx y. (x =
                      itree_unfold (λx.
                         case x of
                           INL (Ret r) =>
                             itree_CASE (k r) (λs. Ret' s) (λt. Tau' (INR t))
                                        (λe g. Vis' e (INR o g))
                         | INL (Tau t) => Tau' (INL t)
                         | INL (Vis e g) => Vis' e (INL o g)
                         | INR (Ret r') => Ret' r'
                         | INR (Tau t') => Tau' (INR t')
                         | INR (Vis e' g') => Vis' e' (INR o g')) (INR y))’ >>
  rw[] >>
  Cases_on ‘t’ >>
  first_x_assum (strip_assume_tac o ONCE_REWRITE_RULE[itree_unfold]) >>
  gvs[] >>
  rw[Once itree_unfold] >>
  gvs[]
QED

Theorem itree_bind_thm[simp]:
  itree_bind (Ret r) k = k r /\
  itree_bind (Tau t) k = Tau (itree_bind t k) /\
  itree_bind (Vis e k') k = Vis e (λx. itree_bind (k' x) k)
Proof
  rw[itree_bind_def]
  >- (rw[Once itree_unfold] >>
      Cases_on ‘k r’ >> rw[] >>
      rw[itree_unfold_bind_INR,FUN_EQ_THM]) >>
  rw[Once itree_unfold,FUN_EQ_THM]
QED

Theorem itree_bind_right_identity[simp]:
  itree_bind t Ret = t
Proof
  rw[Once itree_bisimulation] >>
  qexists_tac ‘λx y. (x = itree_bind y Ret)’ >>
  rw[] >>
  Cases_on ‘t’ >>
  gvs[itree_bind_thm]
QED

Theorem itree_bind_assoc:
  itree_bind (itree_bind t k) k' =
  itree_bind t (λx. itree_bind (k x) k')
Proof
  rw[Once itree_bisimulation] >>
  qexists_tac ‘λx y. (?t. ((x = itree_bind (itree_bind t k) k') /\
                           (y = itree_bind t (λx. itree_bind (k x) k')))) \/
                     x = y’ >>
  rw[]
  >- metis_tac[] >>
  rename1 ‘itree_bind (itree_bind t _)’ >> Cases_on ‘t’ >>
  gvs[itree_bind_thm] >> metis_tac[]
QED

Definition itree_iter_def:
  itree_iter body seed =
    itree_unfold
        (λx.
           case x of
             Ret(INL seed') => Tau'(body seed')
           | Ret(INR v) => Ret' v
           | Tau u => Tau' u
           | Vis e g => Vis' e g)
     (body seed)
End

Theorem itree_iter_thm:
  itree_iter body seed =
    itree_bind (body seed)
               (λx. case x of INL a => Tau(itree_iter body a)
                           |  INR b => Ret b)
Proof
  rw[Once itree_bisimulation] >>
  (* TODO: bisimulation up-to context would probably help here *)
  qexists_tac
  ‘λx y.
     (?t. x = itree_unfold (λx.
                              case x of
                                Ret(INL seed') => Tau'(body seed')
                              | Ret(INR v) => Ret' v
                              | Tau u => Tau' u
                              | Vis e g => Vis' e g)
                           t /\
          y = itree_bind t ((λx. case x of INL a => Tau (itree_iter body a)
                                        | INR b => Ret b))) \/ x = y
              ’ >>
  rw[itree_iter_def]
  >- metis_tac[] >>
  first_x_assum (strip_assume_tac o ONCE_REWRITE_RULE[itree_unfold]) >>
  gvs[AllCaseEqs(),itree_bind_thm] >>
  metis_tac[]
QED

Definition itree_loop_def:
  itree_loop body seed =
  itree_iter (λx.
          itree_bind (body x)
                     (λcb. case cb of INL c => Ret (INL(INL c))
                                   |  INR b => Ret (INR b)))
                     (INR seed)
End

(* weak termination-sensitive bisimulation *)

Inductive strip_tau:
  (strip_tau t t' ==> strip_tau (Tau t) t') /\
  (strip_tau (Vis e k) (Vis e k)) /\
  (strip_tau (Ret v) (Ret v))
End

Theorem strip_tau_simps[simp]:
  (strip_tau t' (Tau t) = F) /\
  (strip_tau (Ret v) (Vis e k) = F) /\
  (strip_tau (Vis e k) (Ret v)  = F) /\
  (strip_tau (Tau t) t' = strip_tau t t')
Proof
  conj_tac
  THEN1 (‘!t t'. strip_tau t t' ==> (?t''. t' = Tau t'') ==> F’
           by(Induct_on ‘strip_tau’ \\ rw[]) \\ metis_tac[]) \\
  rw[EQ_IMP_THM] \\ TRY $ spose_not_then strip_assume_tac \\
  qhdtm_x_assum ‘strip_tau’
                (strip_assume_tac o ONCE_REWRITE_RULE[strip_tau_cases]) \\
  gvs[] \\
  metis_tac[strip_tau_cases]
QED

Theorem strip_tau_simps2[simp]:
  strip_tau (Ret v) (Ret v') = (v = v')
Proof
  rw[Once strip_tau_cases] \\ rw[EQ_IMP_THM]
QED

Theorem strip_tau_simps3[simp]:
  strip_tau (Vis e k) (Vis e' k') = (e = e' /\ k = k')
Proof
  rw[Once strip_tau_cases] \\ rw[EQ_IMP_THM]
QED

Theorem strip_tau_inj:
  !t t' t''. strip_tau t t' /\ strip_tau t t'' ==> t' = t''
Proof
  Induct_on ‘strip_tau’ \\
  rw[] \\ gvs[Once strip_tau_cases]
QED

CoInductive itree_wbisim:
  (itree_wbisim t t' ==> itree_wbisim (Tau t) (Tau t')) /\
  (strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\
   (!r. itree_wbisim (k r) (k' r)) ==>
   itree_wbisim t t') /\
  (strip_tau t (Ret r) /\ strip_tau t' (Ret r) ==> itree_wbisim t t')
End

Theorem itree_wbisim_refl:
  itree_wbisim t (t:('a,'b,'c) itree)
Proof
  ‘!t:('a,'b,'c) itree t'. t = t' ==> itree_wbisim t t'’
    suffices_by metis_tac[] \\
  ho_match_mp_tac itree_wbisim_coind \\ Cases \\ rw[] \\
  metis_tac[strip_tau_rules]
QED

Theorem itree_wbisim_sym:
  !t t'. itree_wbisim t t' ==> itree_wbisim t' t
Proof
  CONV_TAC SWAP_FORALL_CONV \\
  ho_match_mp_tac itree_wbisim_coind \\
  Cases \\ rw[] \\
  pop_assum (strip_assume_tac o ONCE_REWRITE_RULE[itree_wbisim_cases]) \\
  gvs[] \\
  metis_tac[strip_tau_rules,itree_wbisim_rules]
QED

Theorem itree_wbisim_tau_eq:
  itree_wbisim (Tau t) t
Proof
  ‘!t t'. t = Tau t' \/ t = t' ==> itree_wbisim t t'’ suffices_by metis_tac[] \\
  ho_match_mp_tac itree_wbisim_coind \\ ntac 2 Cases \\ rw[] \\
  metis_tac[strip_tau_rules]
QED

Theorem itree_wbisim_strong_coind:
  !R.
    (!t t'.
       R t t' ==>
       (?t2 t3. t = Tau t2 /\ t' = Tau t3 /\ (R t2 t3 \/ itree_wbisim t2 t3)) \/
       (?e k k'.
          strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\
          !r. R (k r) (k' r) \/ itree_wbisim (k r) (k' r)) \/
       ?r. strip_tau t (Ret r) /\ strip_tau t' (Ret r)) ==>
    !t t'. R t t' ==> itree_wbisim t t'
Proof
  rpt strip_tac \\
  Q.SUBGOAL_THEN ‘R t t' \/ itree_wbisim t t'’ mp_tac THEN1 simp[] \\
  pop_assum kall_tac \\
  MAP_EVERY qid_spec_tac [‘t'’,‘t’] \\
  ho_match_mp_tac itree_wbisim_coind \\
  rw[] \\
  res_tac \\
  gvs[] \\
  pop_assum (strip_assume_tac o ONCE_REWRITE_RULE[itree_wbisim_cases]) \\
  metis_tac[]
QED

Triviality itree_wbisim_coind_upto_equiv:
  !R t t'.
    itree_wbisim t t' ==>
    (?t2 t3. t = Tau t2 /\ t' = Tau t3 /\ (R t2 t3 \/ itree_wbisim t2 t3)) \/
    (?e k k'.
       strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\
       !r. R (k r) (k' r) \/ itree_wbisim (k r) (k' r)) \/
    ?r. strip_tau t (Ret r) /\ strip_tau t' (Ret r)
Proof
  metis_tac[itree_wbisim_cases]
QED

Theorem itree_wbisim_coind_upto:
  !R.
    (!t t'.
       R t t' ==>
       (?t2 t3. t = Tau t2 /\ t' = Tau t3 /\ (R t2 t3 \/ itree_wbisim t2 t3)) \/
       (?e k k'.
          strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\
          !r. R (k r) (k' r) \/ itree_wbisim (k r) (k' r)) \/
       (?r. strip_tau t (Ret r) /\ strip_tau t' (Ret r))
       \/ itree_wbisim t t')
    ==> !t t'. R t t' ==> itree_wbisim t t'
Proof
  rpt strip_tac >>
  irule itree_wbisim_strong_coind >>
  qexists_tac ‘R’ >>
  fs[] >>
  pop_assum kall_tac >>
  metis_tac[itree_wbisim_coind_upto_equiv]
QED

Theorem itree_wbisim_vis:
  !e k1 k2. (!r. itree_wbisim (k1 r) (k2 r)) ==> itree_wbisim (Vis e k1) (Vis e k2)
Proof
  metis_tac[strip_tau_cases, itree_wbisim_cases]
QED

Theorem itree_wbisim_tau:
  !t t'. itree_wbisim (Tau t) t' ==> itree_wbisim t t'
Proof
  ho_match_mp_tac itree_wbisim_strong_coind \\ rw[] \\
  qhdtm_x_assum ‘itree_wbisim’
                (strip_assume_tac o ONCE_REWRITE_RULE[itree_wbisim_cases]) \\
  gvs[] \\
  metis_tac[itree_wbisim_cases]
QED

Theorem itree_wbisim_tau_eqn0[local]:
  !t t'. (?t0. t = Tau t0 /\ itree_wbisim t0 t') ==> itree_wbisim t t'
Proof
  ho_match_mp_tac itree_wbisim_strong_coind >> rw[] >>
  pop_assum (strip_assume_tac o ONCE_REWRITE_RULE [itree_wbisim_cases]) >>
  gvs[] >> metis_tac[]
QED

Theorem itree_wbisim_tau_eqn[simp]:
  (itree_wbisim (Tau t1) t2 <=> itree_wbisim t1 t2) /\
  (itree_wbisim t1 (Tau t2) <=> itree_wbisim t1 t2)
Proof
  metis_tac[itree_wbisim_sym, itree_wbisim_tau_eqn0, itree_wbisim_tau]
QED

Theorem itree_wbisim_strip_tau:
  !t t' t''. itree_wbisim t t' /\ strip_tau t t'' ==> itree_wbisim t'' t'
Proof
  Induct_on ‘strip_tau’ \\
  rw[] \\ imp_res_tac itree_wbisim_tau \\
  res_tac
QED

Theorem itree_wbisim_strip_tau_sym:
  !t t' t''. itree_wbisim t t' /\ strip_tau t' t'' ==> itree_wbisim t t''
Proof
  metis_tac[itree_wbisim_sym,itree_wbisim_strip_tau]
QED

Theorem itree_wbisim_strip_tau_Ret:
  !t t' v. itree_wbisim t t' /\ strip_tau t (Ret v) ==> strip_tau t' (Ret v)
Proof
  Induct_on ‘strip_tau’ \\
  rw[] \\ imp_res_tac itree_wbisim_tau \\
  res_tac \\
  gvs[Once itree_wbisim_cases]
QED

Theorem itree_wbisim_strip_tau_Vis:
  !t t' e k. itree_wbisim t t' /\ strip_tau t (Vis e k)
           ==> ?k'. strip_tau t' (Vis e k') /\ !r. itree_wbisim (k r) (k' r)
Proof
  Induct_on ‘strip_tau’ \\
  rw[] \\ imp_res_tac itree_wbisim_tau \\
  res_tac \\
  gvs[Once itree_wbisim_cases] \\
  first_x_assum $ irule_at Any \\
  simp[]
QED

Theorem itree_wbisim_trans:
  !t t' t''. itree_wbisim t t' /\ itree_wbisim t' t'' ==> itree_wbisim t t''
Proof
  CONV_TAC $ QUANT_CONV $ SWAP_FORALL_CONV \\
  Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] \\
  ho_match_mp_tac itree_wbisim_coind \\
  Cases \\ rw[] \\
  last_x_assum (strip_assume_tac o ONCE_REWRITE_RULE[itree_wbisim_cases]) \\
  gvs[]
  >- (imp_res_tac itree_wbisim_strip_tau_Ret)
  >- (last_x_assum (strip_assume_tac o ONCE_REWRITE_RULE[itree_wbisim_cases]) \\
         gvs[] \\
         metis_tac[itree_wbisim_strip_tau_Vis,
                   itree_wbisim_strip_tau_Ret,
                   itree_wbisim_sym]) \\
  metis_tac[itree_wbisim_strip_tau_Vis,
            itree_wbisim_strip_tau_Ret,
            itree_wbisim_sym]
QED

(* common bind base case *)
Theorem itree_bind_ret_inv:
  itree_bind t k = Ret r ==> ?r'. t = Ret r' /\ (k r') = Ret r
Proof
  Cases_on ‘t’ >> fs[itree_bind_thm]
QED

(* combinators respect weak bisimilarity *)
Theorem itree_bind_strip_tau_wbisim:
  !u u' k. strip_tau u u' ==> itree_wbisim (itree_bind u k) (itree_bind u' k)
Proof
  Induct_on ‘strip_tau’ >>
  rw[] >>
  metis_tac[itree_wbisim_refl, itree_wbisim_tau_eq, itree_wbisim_trans]
QED

Theorem itree_bind_vis_strip_tau:
  !u k k' e. strip_tau u (Vis e k') ==>
             strip_tau (itree_bind u k) (Vis e (λx. itree_bind (k' x) k))
Proof
  rpt strip_tac >>
  pop_assum mp_tac >>
  Induct_on ‘strip_tau’ >>
  rpt strip_tac >>
  rw[itree_bind_thm]
QED

Triviality itree_bind_vis_tau_wbisim:
  itree_wbisim (Vis a g) (Tau u) ==>
  ?e k' k''.
    strip_tau (itree_bind (Vis a g) k) (Vis e k') /\
    strip_tau (itree_bind (Tau u) k) (Vis e k'') /\
    !r. (?t1 t2. itree_wbisim t1 t2 /\
                 k' r = itree_bind t1 k /\ k'' r = itree_bind t2 k) \/
        itree_wbisim (k' r) (k'' r)
Proof
  rpt strip_tac >>
  fs[Once itree_wbisim_cases, itree_bind_thm] >>
  fs[Once $ GSYM itree_wbisim_cases] >>
  qexists_tac ‘λx. itree_bind (k' x) k’ >>
  rw[itree_bind_vis_strip_tau] >>
  metis_tac[]
QED

Theorem itree_bind_resp_t_wbisim:
  !a b k. itree_wbisim a b ==> itree_wbisim (itree_bind a k) (itree_bind b k)
Proof
  rpt strip_tac >>
  qspecl_then [‘λa b. ?t1 t2. itree_wbisim t1 t2 /\
                              a = itree_bind t1 k /\ b = itree_bind t2 k’]
              strip_assume_tac itree_wbisim_coind_upto >>
  pop_assum irule >>
  rw[] >-
   (last_x_assum kall_tac >>
    Cases_on ‘t1’ >>
    Cases_on ‘t2’ >-
     (fs[Once itree_wbisim_cases, itree_bind_thm] >>
      Cases_on ‘k x’ >> rw[itree_wbisim_refl]) >-
     (disj2_tac >> disj2_tac >> disj2_tac >>
      irule itree_wbisim_sym >>
      irule itree_bind_strip_tau_wbisim >>
      fs[Once itree_wbisim_cases]) >-
     (fs[Once itree_wbisim_cases]) >-
     (disj2_tac >> disj2_tac >> disj2_tac >>
      irule itree_bind_strip_tau_wbisim >>
      fs[Once itree_wbisim_cases]) >-
     (rw[itree_bind_thm] >>
      ‘itree_wbisim u u'’ by metis_tac[itree_wbisim_tau, itree_wbisim_sym] >>
      metis_tac[]) >-
     (metis_tac[itree_wbisim_sym, itree_bind_vis_tau_wbisim]) >-
     (fs[Once itree_wbisim_cases]) >-
     (metis_tac[itree_wbisim_sym, itree_bind_vis_tau_wbisim]) >-
     (fs[itree_bind_thm, Once itree_wbisim_cases] >> metis_tac[]))
  >- metis_tac[]
QED

Theorem itree_bind_resp_k_wbisim:
  !t k1 k2. (!r. itree_wbisim (k1 r) (k2 r)) ==>
            itree_wbisim (itree_bind t k1) (itree_bind t k2)
Proof
  rpt strip_tac >>
  qspecl_then [‘λa b. ?t. a = itree_bind t k1 /\ b = itree_bind t k2’]
              strip_assume_tac itree_wbisim_coind_upto >>
  pop_assum irule >>
  rw[] >-
   (Cases_on ‘t''’ >> rw[itree_bind_thm] >> metis_tac[]) >-
   metis_tac[]
QED

Theorem itree_bind_resp_wbisim:
  !a b k1 k2. itree_wbisim a b /\ (!r. itree_wbisim (k1 r) (k2 r)) ==>
              itree_wbisim (itree_bind a k1) (itree_bind b k2)
Proof
  metis_tac[itree_bind_resp_t_wbisim, itree_bind_resp_k_wbisim, itree_wbisim_trans]
QED

Theorem itree_iter_ret_tau_wbisim[local]:
  itcb1 = (λx. case x of INL a => Tau (itree_iter k1 a) | INR b => Ret b) /\
  itcb2 = (λx. case x of INL a => Tau (itree_iter k2 a) | INR b => Ret b) /\
  itree_wbisim (Ret x) (Tau u) /\ (!r. itree_wbisim (k1 r) (k2 r))
  ==>
  (?t2 t3.
     itree_bind (Ret x) itcb1 = Tau t2 /\ itree_bind (Tau u) itcb2 = Tau t3 /\
     ((?sa sb. itree_wbisim sa sb /\
               t2 = itree_bind sa itcb1 /\ t3 = itree_bind sb itcb2)
      \/ itree_wbisim t2 t3)) \/
  (?e k k'.
     strip_tau (itree_bind (Ret x) itcb1) (Vis e k) /\
     strip_tau (itree_bind (Tau u) itcb2) (Vis e k') /\
     !r. (?sa sb. itree_wbisim sa sb /\
                  k r = itree_bind sa itcb1 /\ k' r = itree_bind sb itcb2)
         \/ itree_wbisim (k r) (k' r)) \/
  ?r. strip_tau (itree_bind (Ret x) itcb1) (Ret r) /\
      strip_tau (itree_bind (Tau u) itcb2) (Ret r)
Proof
  rpt strip_tac >>
  rw[itree_bind_thm] >>
  qabbrev_tac ‘itcb1 = (λx. case x of INL a => Tau (itree_iter k1 a)
                                   | INR b => Ret b)’ >>
  qabbrev_tac ‘itcb2 = (λx. case x of INL a => Tau (itree_iter k2 a)
                                   | INR b => Ret b)’ >>
  fs[Once itree_wbisim_cases] >> fs[Once $ GSYM itree_wbisim_cases] >>
  qpat_x_assum ‘strip_tau _ _’ mp_tac >>
  Induct_on ‘strip_tau’ >>
  rw[itree_bind_thm] >-
   (disj1_tac >>
    metis_tac[itree_bind_thm,
              itree_wbisim_tau_eq, itree_wbisim_trans, itree_wbisim_sym]) >-
   (disj1_tac >>
    metis_tac[itree_wbisim_tau_eq, itree_wbisim_trans, itree_wbisim_sym]) >-
   (disj2_tac >> disj1_tac >> metis_tac[]) >-
   (disj2_tac >> disj2_tac >> metis_tac[]) >-
   (Cases_on ‘v’ >-
     (qunabbrev_tac ‘itcb1’ >> qunabbrev_tac ‘itcb2’ >>
      rw[] >>
      disj1_tac >> disj1_tac >>
      qexistsl_tac [‘k1 x’, ‘Tau (k2 x)’] >>
      simp[Once itree_iter_thm] >>
      simp[Once itree_iter_thm, itree_bind_thm] >>
      metis_tac[itree_wbisim_tau_eq, itree_wbisim_sym, itree_wbisim_trans]) >-
     (qunabbrev_tac ‘itcb1’ >> qunabbrev_tac ‘itcb2’ >>
      rw[]))
QED

Theorem itree_iter_resp_wbisim:
  !t k1 k2. (!r. itree_wbisim (k1 r) (k2 r)) ==>
            itree_wbisim (itree_iter k1 t) (itree_iter k2 t)
Proof
  rpt strip_tac >>
  qabbrev_tac ‘itcb1 = (λx. case x of INL a => Tau (itree_iter k1 a)
                                   | INR b => Ret b)’ >>
  qabbrev_tac ‘itcb2 = (λx. case x of INL a => Tau (itree_iter k2 a)
                                   | INR b => Ret b)’ >>
  qspecl_then [‘λia ib. ?sa sb x. itree_wbisim sa sb /\
                                  ia = itree_bind sa itcb1 /\
                                  ib = itree_bind sb itcb2’]
              strip_assume_tac itree_wbisim_strong_coind >>
  pop_assum irule >>
  rw[] >-
   (Cases_on ‘sa’ >>
    Cases_on ‘sb’ >-
     (‘x' = x’ by fs[Once itree_wbisim_cases] >>
      gvs[] >>
      Cases_on ‘x’ >-
       (disj1_tac >> (* Ret INL by wbisim *)
        qexistsl_tac [‘itree_bind (k1 x') itcb1’, ‘itree_bind (k2 x') itcb2’] >>
        qunabbrev_tac ‘itcb1’ >> qunabbrev_tac ‘itcb2’ >>
        simp[Once itree_iter_thm, itree_bind_thm] >>
        simp[Once itree_iter_thm, itree_bind_thm] >>
        metis_tac[]) >-
       (disj2_tac >> disj2_tac >> (* Ret INR by equality *)
        qunabbrev_tac ‘itcb1’ >> qunabbrev_tac ‘itcb2’ >>
        rw[Once itree_iter_thm, itree_bind_thm])) >-
     (irule itree_iter_ret_tau_wbisim >> metis_tac[]) >-
     (fs[Once itree_wbisim_cases]) >-
     (‘itree_wbisim (Ret x) (Tau u)’ by fs[itree_wbisim_sym] >>
      rpt $ qpat_x_assum ‘Abbrev _’
          $ assume_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def] >>
      pop_assum mp_tac >>
      drule itree_iter_ret_tau_wbisim >>
      rpt strip_tac >>
      first_x_assum drule >>
      disch_then drule >>
      impl_tac >> metis_tac[itree_wbisim_sym]) >-
     (disj1_tac >>
      rw[itree_bind_thm] >>
      metis_tac[itree_wbisim_tau_eq, itree_wbisim_sym, itree_wbisim_trans]) >-
     (rw[itree_bind_thm] >>
      fs[Once itree_wbisim_cases] >> fs[Once $ GSYM itree_wbisim_cases] >>
      qexists_tac ‘(λx. itree_bind (k x) itcb1)’ >>
      metis_tac[itree_bind_vis_strip_tau]) >-
     (fs[Once itree_wbisim_cases]) >-
     (rw[itree_bind_thm] >>
      fs[Once itree_wbisim_cases] >> fs[Once $ GSYM itree_wbisim_cases] >>
      qexists_tac ‘(λx. itree_bind (k' x) itcb2)’ >>
      metis_tac[itree_bind_vis_strip_tau]) >-
     (disj2_tac >> disj1_tac >>
      simp[itree_bind_thm] >>
      fs[Once itree_wbisim_cases] >> fs[GSYM $ Once itree_wbisim_cases] >>
      metis_tac[]))
  >- (qexistsl_tac [‘k1 t’, ‘k2 t’] >> rw[itree_iter_thm])
QED

(* coinduction upto stripping finite taus, useful for iter and friends *)
Inductive after_taus:
[~rel:]
  (R x y ==> after_taus R x y)
[~tauL:]
  (after_taus R x y ==> after_taus R (Tau x) y)
[~tauR:]
  (after_taus R x y ==> after_taus R x (Tau y))
[~vis:]
  ((!r. after_taus R (k r) (k' r)) ==> after_taus R (Vis e k) (Vis e k'))
End

Theorem itree_coind_after_taus:
  !R. (!t t'.
         R t t' ==>
         (?t2 t3.
           t = Tau t2 /\ t' = Tau t3 /\
             (after_taus R t2 t3 \/ itree_wbisim t2 t3)) \/
         (?e k k'.
            strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\
            !r. after_taus R (k r) (k' r) \/ itree_wbisim (k r) (k' r)) \/
         (?r. strip_tau t (Ret r) /\ strip_tau t' (Ret r)) \/
         itree_wbisim t t') ==>
      !t t'. R t t' ==> itree_wbisim t t'
Proof
  rpt strip_tac >>
  irule itree_wbisim_coind_upto >>
  qexists ‘after_taus R’ >>
  reverse conj_tac
  >- rw[after_taus_rel] >>
  Induct_on ‘after_taus’ >>
  rw[] >>
  metis_tac[after_taus_rules]
QED

(* misc *)

Definition spin:
  spin = itree_unfold (K (Tau' ())) ()
End

Theorem spin[allow_rebind]:
  spin = Tau spin  (* an infinite sequence of silent actions *)
Proof
  fs [spin] \\ simp [Once itree_unfold]
QED

(* relation to tauless itrees *)

Theorem strip_tau_spin:
  (!t'. ~strip_tau t t') ==> t = spin
Proof
  rw[Once itree_bisimulation] \\
  qexists_tac ‘λt t'. (!t'. ~strip_tau t t') /\ t' = spin’ \\
  rw[GSYM spin] \\
  metis_tac[strip_tau_simps2,strip_tau_simps3]
QED

Definition untau_def:
  untau = itree$itree_unfold
          (λt. case some t'. strip_tau t t' of
                 NONE => Div'
               | SOME(Tau t') => Div' (* impossible *)
               | SOME(Ret v) => Ret' v
               | SOME(Vis e k) => Vis' e k)
End

Theorem spin_strip_tau:
  !t. strip_tau spin t ==> F
Proof
  Induct_on ‘strip_tau’ \\
  rw[] \\
  metis_tac[spin,itree_distinct,itree_11]
QED

Theorem untau_spin[simp]:
  untau spin = Div
Proof
  rw[untau_def,Once itreeTheory.itree_unfold] \\
  DEEP_INTRO_TAC some_intro \\
  rw[] \\
  imp_res_tac spin_strip_tau
QED

Theorem untau_IMP_wbisim:
  !t t'. untau t = untau t' ==> itree_wbisim t t'
Proof
  ho_match_mp_tac itree_wbisim_strong_coind \\
  rw[] \\
  gvs[untau_def] \\
  pop_assum (strip_assume_tac o ONCE_REWRITE_RULE[itreeTheory.itree_unfold]) \\
  gvs[AllCaseEqs()] \\
  rpt(pop_assum mp_tac) \\
  ntac 2 (DEEP_INTRO_TAC some_intro \\ simp[]) \\
  rw[]
  THEN1 metis_tac[]
  THEN1 metis_tac[strip_tau_spin,spin,itree_wbisim_refl]
  THEN1 metis_tac[combinTheory.o_DEF]
QED

Theorem wbisim_IMP_untau:
  !t t'. itree_wbisim t t' ==> untau t = untau t'
Proof
  rw[Once itreeTheory.itree_bisimulation] \\
  qexists_tac
    ‘λt t1. (?t2 t3. itree_wbisim t2 t3 /\ t = untau t2 /\ t1 = untau t3)’ \\
  gvs[] \\
  conj_tac THEN1 metis_tac[] \\
  pop_assum kall_tac \\
  rw[untau_def] \\
  pop_assum (strip_assume_tac o ONCE_REWRITE_RULE[itreeTheory.itree_unfold]) \\
  gvs[AllCaseEqs()] \\
  rpt(pop_assum mp_tac) \\
  DEEP_INTRO_TAC some_intro \\ simp[] \\
  rw[]
  THEN1
   (imp_res_tac itree_wbisim_strip_tau_Ret \\
    simp[Once itreeTheory.itree_unfold] \\
    DEEP_INTRO_TAC some_intro \\ simp[] \\
    reverse conj_tac THEN1 first_x_assum $ irule_at Any \\
    rw[] \\
    dxrule_all_then strip_assume_tac strip_tau_inj \\
    gvs[])
  THEN1
    (rename [‘itree_wbisim t1 t2’] \\
     ‘!x. ~strip_tau t2 x’
       by(Cases \\ gvs[] \\ spose_not_then strip_assume_tac \\
          metis_tac[itree_wbisim_strip_tau_Ret,
                    itree_wbisim_strip_tau_Vis,
                    itree_wbisim_sym]) \\
     imp_res_tac strip_tau_spin \\
     simp[GSYM untau_def]) \\
  drule_all_then strip_assume_tac itree_wbisim_strip_tau_Vis \\
  simp[Once itreeTheory.itree_unfold] \\
  DEEP_INTRO_TAC some_intro \\
  reverse $ rw[] THEN1 metis_tac[] \\
  dxrule_all_then strip_assume_tac strip_tau_inj \\
  gvs[] \\
  metis_tac[]
QED

(** FUNPOW **)

Theorem Tau_INJ[simp]:
  INJ Tau UNIV UNIV
Proof
  simp[INJ_DEF]
QED

Theorem FUNPOW_Tau_neq[simp]:
  Ret x <> FUNPOW Tau n (Vis a g) /\
  Vis a g <> FUNPOW Tau n (Ret x)
Proof
  MAP_EVERY qid_spec_tac [‘x’,‘a’,‘g’,‘n’]>>
  Induct>>rw[FUNPOW_SUC]
QED

Theorem FUNPOW_Tau_neq2[simp]:
  FUNPOW Tau n' (Ret x) <> FUNPOW Tau n (Vis a g)
Proof
  Cases_on ‘n < n'’>>fs[NOT_LESS]>>strip_tac
  >- (imp_res_tac (GSYM LESS_ADD)>>fs[FUNPOW_ADD]>>
      fs[FUNPOW_eq_elim,Tau_INJ])>>
  gvs[FUNPOW_min_cancel,Tau_INJ]
QED

Theorem strip_tau_FUNPOW:
  !t1 t2. strip_tau t1 t2 ==>
        ?n. t1 = FUNPOW Tau n $ t2
Proof
  Induct_on ‘strip_tau’ >>
  rw[]
  >- (qrefine ‘SUC _’ >>
      rw[FUNPOW_SUC] >>
      metis_tac[]
     ) >>
  qexists ‘0’ >>
  rw[]
QED

Theorem FUNPOW_Tau_wbisim:
  itree_wbisim (FUNPOW Tau n x) x
Proof
  Induct_on ‘n’ >>
  rw[itree_wbisim_refl,FUNPOW_SUC]
QED

Theorem FUNPOW_Tau_wbisim_intro:
  itree_wbisim x y ==>
  itree_wbisim (FUNPOW Tau n x) (FUNPOW Tau n' y)
Proof
  metis_tac[FUNPOW_Tau_wbisim,itree_wbisim_trans,itree_wbisim_refl,itree_wbisim_sym]
QED

Theorem strip_tau_vis_wbisim:
  !e k k'. strip_tau t (Vis e k) /\ strip_tau t' (Vis e k') /\
           (!r. itree_wbisim (k r) (k' r)) ==>
          itree_wbisim t t'
Proof
  rpt strip_tac >>
  imp_res_tac strip_tau_FUNPOW >>
  gvs[] >>
  irule FUNPOW_Tau_wbisim_intro >>
  rw[Once itree_wbisim_cases]
QED

Theorem itree_wbisim_Ret_FUNPOW:
  itree_wbisim t (Ret x) ==> ?n. t = FUNPOW Tau n $ Ret x
Proof
  rw[Once itree_wbisim_cases] >>
  drule_then irule strip_tau_FUNPOW
QED

Theorem FUNPOW_Tau_imp_wbisim:
  t = FUNPOW Tau n $ t' ==> itree_wbisim t t'
Proof
  strip_tac >>
  irule itree_wbisim_trans >>
  irule_at Any FUNPOW_Tau_wbisim>>fs[]>>
  irule_at Any itree_wbisim_refl
QED

Theorem itree_wbisim_Vis_FUNPOW:
  itree_wbisim t (Vis a g) ==>
  ?n k. t = FUNPOW Tau n $ Vis a k /\ (!r. itree_wbisim (k r) (g r))
Proof
  simp[Once itree_wbisim_cases] >> rw[] >>
  imp_res_tac strip_tau_FUNPOW>>
  pop_assum $ irule_at Any>>fs[]
QED

Theorem wbisim_FUNPOW_Tau:
  (itree_wbisim t (FUNPOW Tau n ht) <=> itree_wbisim t ht) /\
  (itree_wbisim (FUNPOW Tau n ht) t <=> itree_wbisim ht t)
Proof
  rw[EQ_IMP_THM]>>
  TRY (irule itree_wbisim_trans>>
       irule_at Any FUNPOW_Tau_wbisim>>
       fs[]>>metis_tac[]>>NO_TAC)>>
  irule itree_wbisim_trans>>
  first_assum $ irule_at Any>>
  irule itree_wbisim_sym>>
  irule FUNPOW_Tau_wbisim
QED

Theorem FUNPOW_Tau_bind:
  itree_bind (FUNPOW Tau n t)g = FUNPOW Tau n (itree_bind t g)
Proof
  MAP_EVERY qid_spec_tac [‘t’,‘n’]>>
  Induct_on ‘n’>>rw[]>>
  simp[FUNPOW]
QED

Theorem strip_tau_FUNPOW_cancel:
  (!u. t <> Tau u) ==>
  strip_tau (FUNPOW Tau n t) t
Proof
  Induct_on ‘n’>>rw[]
  >- (Cases_on ‘t’>>rw[])>>
  Cases_on ‘t’>>rw[FUNPOW_SUC]
QED

Theorem FUNPOW_Tau_Vis_eq:
  FUNPOW Tau n (Vis a g) = FUNPOW Tau m (Vis e k) ==>
  n = m /\ a = e /\ g = k
Proof
  strip_tac>>
  Cases_on ‘n < m’>>fs[NOT_LESS]
  >- (fs[FUNPOW_min_cancel,Tau_INJ]>>
      Cases_on ‘m - n’>>fs[FUNPOW_SUC])>>
  last_x_assum $ assume_tac o GSYM>>
  rfs[FUNPOW_min_cancel,Tau_INJ]>>
  Cases_on ‘n - m’>>fs[FUNPOW_SUC]
QED

Theorem FUNPOW_Tau_Ret_eq:
  FUNPOW Tau n (Ret x) = FUNPOW Tau m (Ret y) ==>
  n = m /\ x = y
Proof
  strip_tac>>
  Cases_on ‘n < m’>>fs[NOT_LESS]
  >- (fs[FUNPOW_min_cancel,Tau_INJ]>>
      Cases_on ‘m - n’>>fs[FUNPOW_SUC])>>
  last_x_assum $ assume_tac o GSYM>>
  rfs[FUNPOW_min_cancel,Tau_INJ]>>
  Cases_on ‘n - m’>>fs[FUNPOW_SUC]
QED

(* more on spin *)

Theorem spin_bind:
  itree_bind spin k = spin
Proof
  simp[Once itree_bisimulation]>>
  qexists ‘CURRY {(itree_bind spin k, spin)}’>>
  simp[]>>rw[]
  >- fs[Once spin]
  >- irule (GSYM spin)
  >- fs[Once spin,itree_bind_thm]>>
  fs[Once spin]
QED

Theorem spin_FUNPOW_Tau:
  !n. spin = FUNPOW Tau n spin
Proof
  Induct>>rw[]>>fs[FUNPOW_SUC]>>
  irule (GSYM spin)
QED

Theorem wbisim_spin_eq:
  itree_wbisim t spin <=> t = spin
Proof
  rw[EQ_IMP_THM]
  >- (simp[Once itree_bisimulation]>>
      qexists ‘CURRY {(t,spin)|t|itree_wbisim t spin}’>>
      rw[]
      >- fs[Once itree_wbisim_cases,spin_strip_tau]
      >- irule (GSYM spin)>>
      fs[Once itree_wbisim_cases,spin_strip_tau])>>
  irule itree_wbisim_refl
QED

(* tidy up theory exports *)

val _ = List.app Theory.delete_binding
  ["Ret_rep_def", "Ret_def",
   "Tau_rep_def", "Tau_def",
   "Vis_rep_def", "Vis_def",
   "path_ok_def", "itree_rep_ok_def",
   "itree_unfold_path_def", "itree_unfold_path_ind",
   "itree_el_TY_DEF", "itree_absrep", "itree_next_TY_DEF"];

val _ = export_theory();
