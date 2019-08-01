open HolKernel Parse boolLib simpLib BasicProvers numSimps TotalDefn metisLib

open combinTheory pred_setTheory relationTheory arithmeticTheory
     set_relationTheory numpairTheory listTheory rich_listTheory;

val _ = new_theory "nlist";

val _ = Defn.SUC_TO_NUMERAL_DEFN_CONV_hook := numLib.SUC_TO_NUMERAL_DEFN_CONV

fun simp ths = simpLib.ASM_SIMP_TAC (srw_ss()++numSimps.ARITH_ss) ths
fun fs ths = simpLib.FULL_SIMP_TAC (srw_ss()++numSimps.ARITH_ss) ths
fun rw ths = SRW_TAC[numSimps.ARITH_ss]ths
val metis_tac = METIS_TAC
val qspec_then = Q.SPEC_THEN

(* ----------------------------------------------------------------------
    lists of naturals encoded as naturals
   ---------------------------------------------------------------------- *)

val _ = overload_on ("nnil", ``0``);
val _ = overload_on ("0", ``0``);

Definition ncons_def:
  ncons h t = h *, t + 1
End

Theorem ncons_11[simp]:     ncons x y = ncons h t <=> x = h /\ y = t
Proof SRW_TAC [][ncons_def]
QED

Theorem ncons_not_nnil[simp]:
  ncons x y <> nnil
Proof
  SRW_TAC [ARITH_ss][ncons_def]
QED

Theorem lt_ncons1[simp]:   h < ncons h t
Proof simp[ncons_def, GSYM LE_LT1]
QED

Theorem lt_ncons2[simp]:   t < ncons h t
Proof simp[ncons_def, npair_def]
QED

(* nlistrec -------------------------------------------------------- *)
Definition nlistrec_def:
  nlistrec n f l = if l = 0 then n
                   else f (nfst (l - 1)) (nsnd (l - 1))
                          (nlistrec n f (nsnd (l - 1)))
Termination
  WF_REL_TAC `measure (SND o SND)` THEN
  STRIP_TAC THEN ASSUME_TAC (Q.INST [`n` |-> `l - 1`] nsnd_le) THEN
  simp[]
End

Theorem nlistrec_thm[simp]:
  nlistrec n f nnil = n /\
  nlistrec n f (ncons h t) = f h t (nlistrec n f t)
Proof
  CONJ_TAC THEN1 SRW_TAC [][Once nlistrec_def] THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [nlistrec_def])) THEN
  SRW_TAC [ARITH_ss][ncons_def]
QED

(* allows an induction principle *)
Theorem nlist_ind:
  !P. P 0 /\ (!h t. P t ==> P (ncons h t)) ==> !n. P n
Proof
  GEN_TAC THEN STRIP_TAC THEN
  Q_TAC SUFF_TAC `!(n:'a) (f:num -> num -> 'a -> 'a) l. P l`
    THEN1 METIS_TAC [] THEN
  HO_MATCH_MP_TAC nlistrec_ind THEN REPEAT STRIP_TAC THEN
  Cases_on `l` THEN SRW_TAC [][] THEN
  `SUC n = ncons (nfst n) (nsnd n)` by SRW_TAC [][ncons_def, ADD1] THEN
  SRW_TAC [][]
QED

Theorem nlist_cases:
  !n. (n = nnil) \/ ?h t. n = ncons h t
Proof
  Cases_on `n` THEN SRW_TAC [][ncons_def, GSYM ADD1] THEN
  Q.MATCH_ABBREV_TAC `?h t. n = h *, t` THEN
  MAP_EVERY Q.EXISTS_TAC [`nfst n`, `nsnd n`] THEN SRW_TAC [][]
QED

(* nlist_of ------------------------------------------------------- *)
Definition nlist_of_def[simp]:
  (nlist_of [] = 0) /\
  (nlist_of (h::t) = ncons h (nlist_of t))
End

Theorem nlist_of_EQ0[simp]:
  (nlist_of l = 0 <=> l = []) /\
  (0 = nlist_of l <=> l = [])
Proof
  Cases_on ‘l’ >> simp[]
QED

(* listOfN -------------------------------------------------------- *)
Definition listOfN_def:
  listOfN = nlistrec [] (\h tn t. h :: t)
End

Theorem listOfN_zero[simp]:
  listOfN 0 = []
Proof simp[listOfN_def]
QED

Theorem listOfN_ncons[simp]:
  listOfN (ncons h t) = h :: listOfN t
Proof
  simp[listOfN_def]
QED

Theorem listOfN_EQ_NIL[simp]:
  (listOfN l = [] <=> l = 0) /\ ([] = listOfN l <=> l = 0)
Proof
  qspec_then ‘l’ strip_assume_tac nlist_cases >> simp[]
QED

Theorem listOfN_EQ_CONS:
  listOfN n = h :: t <=> ?tn. n = ncons h tn /\ listOfN tn = t
Proof
  rw[listOfN_def] >> Q.SPEC_THEN ‘n’ strip_assume_tac nlist_cases >> rw[]
QED

(* nlist_of and listOfN are inverse, bijection results follow *)
Theorem nlist_listOfN[simp]:
  !l. nlist_of (listOfN l) = l
Proof
  ho_match_mp_tac nlist_ind >> simp[]
QED

Theorem listOfN_nlist[simp]:
  !l. listOfN (nlist_of l) = l
Proof
  Induct_on `l` >> simp[]
QED

Theorem listOfN_SURJ:
  !l. ?n. listOfN n = l
Proof
  METIS_TAC[listOfN_nlist]
QED

Theorem listOfN_INJ[simp]:
  !l1 l2. listOfN l1 = listOfN l2 <=> l1 = l2
Proof
  METIS_TAC[nlist_listOfN]
QED

Theorem nlist_of_INJ[simp]:
  !n1 n2. nlist_of n1 = nlist_of n2 <=> n1 = n2
Proof
  METIS_TAC[listOfN_nlist]
QED

Theorem nlist_of_SURJ:
  !l. ?n. nlist_of n = l
Proof
  METIS_TAC[nlist_listOfN]
QED

(* copy various functions on maps across to number land *)
val _ = overload_on ("nlen", “\n. LENGTH (listOfN n)”)
val _ = overload_on ("napp", “\n1 n2. nlist_of (listOfN n1 ++ listOfN n2)”)
val _ = overload_on ("nfoldl", “\f a n. FOLDL f a (listOfN n)”)
val _ = overload_on ("nmap", “\f n. nlist_of (MAP f (listOfN n))”)

(* some functions are partial over general lists, but can be made total
   here by using 0 as default values *)

(* nhd ------------------------------------------------------------ *)
Definition nhd_def: nhd nl = nfst (nl - 1)
End

Theorem nhd0[simp]:
  nhd 0 = 0
Proof
  simp[nhd_def]
QED

Theorem nhd_thm[simp]: nhd (ncons h t) = h
Proof SRW_TAC [][ncons_def, nhd_def]
QED

(* ntl ------------------------------------------------------------ *)
Definition ntl_def: ntl nlist = nsnd (nlist - 1)
End

Theorem ntl_zero[simp]:
  ntl 0 = 0
Proof
  simp[ntl_def]
QED

Theorem ntl_thm[simp]:  ntl (ncons h t) = t
Proof simp[ncons_def, ntl_def]
QED

Theorem ntl_LT:
  0 < n ==> ntl n < n
Proof
  rw[ntl_def] >> Induct_on `n` >- (strip_tac >> fs[]) >>
  rw[nsnd_def]
QED

Theorem ncons_nhd_ntl:
  !l. l <> 0 ==> ncons (nhd l) (ntl l) = l
Proof
  Cases_on `l` >- simp[] >> simp[ncons_def,nhd_def,ntl_def]
QED

Theorem ntl_zero_empty_OR_ncons:
  ntl l = 0 <=> l = 0 \/ ?x. l = ncons x 0
Proof
  eq_tac >- METIS_TAC[ncons_nhd_ntl] >>
  simp[DISJ_IMP_THM, PULL_EXISTS] >>
  rw[ntl_def]
QED

(* ndrop ---------------------------------------------------------- *)
val _ = overload_on ("ndrop", “\n l. nlist_of (DROP n (listOfN l))”)

Theorem ndrop_SUC[simp]:
  !l n. ndrop (SUC n) l = ntl (ndrop n l)
Proof
  ho_match_mp_tac nlist_ind >> rw[] >>
  Cases_on ‘n’ >> simp[]
QED

Theorem ntl_ndrop:
  !l. ntl (ndrop n l) = ndrop n (ntl l)
Proof     Induct_on `n` >> simp[]
QED

(* nel ------------------------------------------------------------ *)
Definition nel_def:         nel n nlist = nhd (ndrop n nlist)
End

Theorem nel_nnil[simp]:     nel x 0 = 0
Proof simp[nel_def]
QED

Theorem nel0_ncons[simp]:   nel 0 (ncons h t) = h
Proof simp[nel_def]
QED

Theorem nel_nhd:            nel 0 l = nhd l
Proof simp[nel_def]
QED

Theorem nel_SUC_CONS[simp]: !n h t. nel (SUC n) (ncons h t) = nel n t
Proof simp[nel_def] >> Induct >> simp[]
QED

(* nlast ---------------------------------------------------------- *)
Definition nlast_def:
  nlast = nlistrec 0 (\h tn rn. if tn = 0 then h else rn)
End

Theorem nlast_nnil[simp]:   nlast 0 = 0
Proof simp[nlast_def]
QED

Theorem nlast_ncons[simp]:
  nlast (ncons h tn) = if tn = 0 then h else nlast tn
Proof
  simp[nlast_def]
QED

Theorem nlast_nel:
  !l. nlast l = nel (nlen l - 1) l
Proof
  ho_match_mp_tac nlist_ind >> simp[] >> rw[] >>
  Q.SPEC_THEN ‘l’ strip_assume_tac nlist_cases >> rw[]
QED

(* nfront --------------------------------------------------------- *)
Definition nfront_def:
  nfront = nlistrec 0 (\h tn rn. if tn = 0 then 0 else ncons h rn)
End

Theorem nfront_nnil[simp]:  nfront 0 = 0
Proof
  simp[nfront_def]
QED

Theorem nfront_nsingl[simp]:  nfront (ncons x 0) = 0
Proof simp[nfront_def]
QED

Theorem nfront_thm:
  nfront 0 = 0 /\
  nfront (ncons h t) = if t = 0 then 0 else ncons h (nfront t)
Proof
  simp[nfront_def]
QED

Theorem nhd_nfront:
  !l. l <> 0 /\ ntl l <> 0 ==> nhd (nfront l) = nhd l
Proof
  ho_match_mp_tac nlist_ind >> simp[] >> rw[] >>
  simp[Once nfront_def]
QED

Theorem LENGTH_nfront:
  !t. t <> 0 ==> nlen (nfront t) = nlen t - 1
Proof
  ho_match_mp_tac nlist_ind >> simp[nfront_thm] >> rw[] >>
  ‘nlen t <> 0’ suffices_by numLib.ARITH_TAC >>
  simp[]
QED

Theorem ncons_x_0_LENGTH_1:
  nlen l = 1 <=> ?n. l = ncons n 0
Proof
  qspec_then ‘l’ strip_assume_tac nlist_cases >> simp[]
QED

Theorem ndrop_nsingl:
  m <> 0 ==> ndrop m (ncons x 0) = 0
Proof
  Cases_on ‘m’ >> simp[ntl_ndrop]
QED

Theorem ntl_DROP:
  !l m. ntl (nlist_of (DROP m l)) = ndrop m (ntl (nlist_of l))
Proof
  Induct >> rw[] >> Cases_on ‘m’ >> simp[] >> Cases_on ‘l’ >> simp[]
QED

Theorem nel_nfront:
  !t. m < nlen (nfront t) ==> nel m (nfront t) = nel m t
Proof
  simp[nel_def] >> Induct_on `m` >> simp[] >> gen_tac >>
  Q.SPEC_THEN `t` STRUCT_CASES_TAC nlist_cases >> simp[nfront_thm] >> rw[] >>
  simp[ntl_DROP]
QED

Theorem nsnoc_cases:
  !t. t = 0 \/ ?f l. t = napp f (ncons l 0)
Proof
  ho_match_mp_tac nlist_ind >> simp[] >> rw[]
  >- (Q.RENAME_TAC [‘ncons h 0’] >> MAP_EVERY Q.EXISTS_TAC [‘0’, ‘h’] >>
      simp[]) >>
  simp[GSYM nlist_of_def, Excl "nlist_of_def"] >>
  Q.RENAME_TAC [‘h1::(listOfN f ++ [h2])’] >>
  MAP_EVERY Q.EXISTS_TAC [‘ncons h1 f’, ‘h2’] >> simp[]
QED

Theorem nhd_napp:
  !l1 l2. l1 <> 0 ==> nhd (napp l1 l2) = nhd l1
Proof
  rpt gen_tac >> Q.SPEC_THEN ‘l1’ strip_assume_tac nlist_cases >> simp[]
QED

Theorem nel_napp:
  !l1 l2. n < nlen l1 ==> nel n (napp l1 l2) = nel n l1
Proof
  Induct_on `n` >> simp[]
  >- (rpt gen_tac >> qspec_then `l1` STRUCT_CASES_TAC nlist_cases >> simp[]) >>
  rpt gen_tac >> qspec_then `l1` STRUCT_CASES_TAC nlist_cases >> simp[]
QED

Theorem nfront_napp_sing[simp]:
  !pfx. nfront (napp pfx (ncons e 0)) = pfx
Proof
  ho_match_mp_tac nlist_ind >> simp[nfront_def]
QED

Theorem nel_napp2:
  !y n x. nlen x <= n ==> (nel n (napp x y) = nel (n - nlen x) y)
Proof
  Induct_on `n` >> simp[] >>
  rpt strip_tac >> qspec_then `x` FULL_STRUCT_CASES_TAC nlist_cases >>
  fs[]
QED

Theorem nel_ncons_nonzero:
  0 < n ==> (nel n (ncons h t) = nel (n - 1) t)
Proof
  Cases_on ‘n’ >> simp[]
QED


Theorem napp_nsnoc_lt:
  !l. l < napp l (ncons x 0)
Proof
  ho_match_mp_tac nlist_ind >> rpt strip_tac >> simp[] >>
  fs[ncons_def]
QED

Theorem napp_sing_eq[simp]:
  napp l1 (ncons l 0) = ncons x 0 <=> l1 = 0 /\ x = l
Proof
  qspec_then `l1` STRUCT_CASES_TAC nlist_cases >> simp[]
QED

Theorem nel_correct:
  !l i. i < nlen l ==> EL i (listOfN l) = nel i l
Proof
  ho_match_mp_tac nlist_ind >> simp [] >> rw[] >> Cases_on ‘i’ >> simp[]
QED


Theorem nel_eq_nlist:
  !l1 l2. l1 = l2 <=>
            nlen l1 = nlen l2 /\
            !m. m < nlen l1 ==> nel m l1 = nel m l2
Proof
  rw[] >>
  ‘(?L1. l1 = nlist_of L1) /\ (?L2. l2 = nlist_of L2)’
     by metis_tac[nlist_of_SURJ] >>
  simp[GSYM nel_correct, LIST_EQ_REWRITE, EQ_IMP_THM]
QED

Theorem nlast_napp:
  !l1 l2. l2 <> 0 ==> nlast (napp l1 l2) = nlast l2
Proof
  ho_match_mp_tac nlist_ind >> simp[]
QED

Theorem napp_ndrop_l1_empty[simp]:
  !l1 l2. ndrop (nlen l1) (napp l1 l2) = l2
Proof
  simp[DROP_LENGTH_APPEND]
QED

Theorem ntl_LE :
!n. ntl n <= n
Proof
rw[ntl_def,ncons_def] >> `nsnd (n - 1) <= n - 1` by fs[nsnd_le] >> fs[]
QED

Theorem ntl_nonzero_LESS :
!n. n <> 0 ==> ntl n < n
Proof
rw[ntl_def,ncons_def] >> `nsnd (n - 1) <= n - 1` by fs[nsnd_le] >>
`n - 1 < n` by fs[] >> fs[]
QED


Theorem MEM_listOfN_LESS :
  !l e. MEM e (listOfN l) ==> e < l
Proof
  ho_match_mp_tac nlist_ind >> simp[DISJ_IMP_THM, FORALL_AND_THM] >> rw[] >>
  res_tac >> irule LESS_TRANS >> Q.EXISTS_TAC ‘l’ >> simp[]
QED




val _ = export_theory();
