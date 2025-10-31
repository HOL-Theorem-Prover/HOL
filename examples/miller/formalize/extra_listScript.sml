Theory extra_list
Ancestors
  list num arithmetic pred_set subtype extra_num rich_list pair
Libs
  hurdUtils

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

Definition prod_def:   (prod [] = (1:num)) /\ (prod (n :: ns) = n * prod ns)
End

Definition list_def:   list = (EVERY : ('a -> bool) -> 'a list -> bool)
End

Definition gtlist_def:   gtlist n l <=> n < LENGTH l
End

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val MEM_NIL = store_thm
  ("MEM_NIL",
   ``!l. (!(x:'a). ~MEM x l) <=> (l = [])``,
   Cases >- RW_TAC std_ss [MEM]
   >> RW_TAC std_ss [MEM]
   >> PROVE_TAC []);

val MEM_NIL_MAP_CONS = store_thm
  ("MEM_NIL_MAP_CONS",
   ``!(x:'a) l. ~MEM [] (MAP (CONS x) l)``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [MEM]
   >> RW_TAC list_ss [MEM]);

val LENGTH_FILTER = store_thm
  ("LENGTH_FILTER",
   ``!P (l:'a list). LENGTH (FILTER P l) <= LENGTH l``,
   GEN_TAC
   >> Induct_on `l`
   >> RW_TAC list_ss [FILTER]);

Theorem FILTER_MEMP = MEM_FILTER |> iffLR |> cj 1
Theorem MEM_FILTER_MEM = MEM_FILTER |> iffLR |> cj 2

val FILTER_OUT_ELT = store_thm
  ("FILTER_OUT_ELT",
   ``!(x:'a) l. MEM x l \/ (FILTER (\y. ~(y = x)) l = l)``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [FILTER]
   >> (RW_TAC list_ss [MEM, FILTER]
         >> PROVE_TAC []));

val IS_PREFIX_LENGTH = store_thm
  ("IS_PREFIX_LENGTH",
   ``!(x:'a list) y. IS_PREFIX y x ==> LENGTH x <= LENGTH y``,
   Induct >- RW_TAC list_ss [LENGTH]
   >> Cases_on `y` >- RW_TAC list_ss [IS_PREFIX_NIL]
   >> RW_TAC list_ss [IS_PREFIX, LENGTH]);

val IS_PREFIX_LENGTH_ANTI = store_thm
  ("IS_PREFIX_LENGTH_ANTI",
   ``!(x:'a list) y. IS_PREFIX y x /\ (LENGTH x = LENGTH y) ==> (x = y)``,
   Induct >- PROVE_TAC [LENGTH_NIL]
   >> Cases_on `y` >- RW_TAC list_ss [LENGTH_NIL]
   >> RW_TAC list_ss [IS_PREFIX, LENGTH]);

val IS_PREFIX_SNOC = store_thm
  ("IS_PREFIX_SNOC",
   ``!(x:'a) y z. IS_PREFIX (SNOC x y) z <=> IS_PREFIX y z \/ (z = SNOC x y)``,
   Induct_on `y`
     >- (Cases_on `z`
         >> RW_TAC list_ss [SNOC, IS_PREFIX_NIL, IS_PREFIX]
         >> PROVE_TAC [])
   >> Cases_on `z` >- RW_TAC list_ss [IS_PREFIX]
   >> RW_TAC list_ss [SNOC, IS_PREFIX]
   >> PROVE_TAC []);

val FOLDR_MAP = store_thm
  ("FOLDR_MAP",
   ``!(f :'b -> 'c -> 'c) (e :'c) (g :'a -> 'b) (l :'a list).
         FOLDR f e (MAP g l) = FOLDR (\x y. f (g x) y) e l``,
   RW_TAC list_ss []
   >> Induct_on `l` >- RW_TAC list_ss [MAP, FOLDR]
   >> RW_TAC list_ss [MAP, FOLDR]);

val LAST_MEM = store_thm
  ("LAST_MEM",
   ``!(h:'a) t. MEM (LAST (h::t)) (h::t)``,
   Induct_on `t` >- RW_TAC list_ss [MEM, LAST_CONS]
   >> RW_TAC std_ss [LAST_CONS]
   >> ONCE_REWRITE_TAC [MEM]
   >> RW_TAC std_ss []);

val LAST_MAP_CONS = store_thm
  ("LAST_MAP_CONS",
   ``!(b:bool) h t. ?x. LAST (MAP (CONS b) (h::t)) = b::x``,
   Induct_on `t` >- RW_TAC list_ss [LAST_CONS]
   >> POP_ASSUM MP_TAC
   >> RW_TAC list_ss [LAST_CONS]);

val EXISTS_LONGEST = store_thm
  ("EXISTS_LONGEST",
   ``!(x:'a list) y. ?z. MEM z (x::y)
                    /\ (!w. MEM w (x::y) ==> LENGTH w <= LENGTH z)``,
   Induct_on `y` >- RW_TAC list_ss [MEM]
   >> ONCE_REWRITE_TAC [MEM]
   >> REPEAT STRIP_TAC
   >> POP_ASSUM (MP_TAC o SPEC ``h:'a list``)
   >> STRIP_TAC
   >> EXISTS_TAC ``if LENGTH z <= LENGTH x then x else (z:'a list)``
   >> ZAP_TAC std_ss [LESS_EQ_TRANS]);

Theorem SUM_CONST:
  !l c. (!x. MEM x l ==> (x = c)) ==> (SUM l = LENGTH l * c)
Proof Induct >> simp[SUM, MULT_CLAUSES] >> PROVE_TAC [MULT_COMM]
QED

val IN_LIST = store_thm
  ("IN_LIST",
   ``!(h:'a) t p.
       ([] IN list p) /\ ((h::t) IN list p <=> h IN p /\ t IN list p)``,
   RW_TAC std_ss [list_def, SPECIFICATION, EVERY_DEF]);

val IN_GTLIST = store_thm
  ("IN_GTLIST",
   ``!n (l:'a list). l IN gtlist n <=> n < LENGTH l``,
   RW_TAC std_ss [gtlist_def, SPECIFICATION]);

val LIST_UNIV = store_thm
  ("LIST_UNIV",
   ``list (UNIV : 'a -> bool) = UNIV``,
   SET_EQ_TAC
   >> Induct >- RW_TAC std_ss [IN_LIST, IN_UNIV]
   >> RW_TAC std_ss [IN_LIST, IN_UNIV]);

val LIST_SUBSET = store_thm
  ("LIST_SUBSET",
   ``!p q. p SUBSET q ==> list p SUBSET list q``,
   RW_TAC std_ss [SUBSET_DEF]
   >> Induct_on `x` >- RW_TAC std_ss [IN_LIST]
   >> RW_TAC std_ss [IN_LIST]);

val NIL_SUBTYPE = store_thm
  ("NIL_SUBTYPE",
   ``!(x : 'a -> bool). [] IN list x``,
   RW_TAC std_ss [IN_LIST, LENGTH, IN_INTER]);

val CONS_SUBTYPE = store_thm
  ("CONS_SUBTYPE",
   ``!(x : 'a -> bool).
       CONS IN ((x -> list x -> list x) INTER (UNIV -> UNIV -> gtlist 0) INTER
                (UNIV -> gtlist 0 -> gtlist 1))``,
   RW_TAC arith_ss [IN_FUNSET, IN_LIST, IN_GTLIST, LENGTH, IN_INTER]);

val MAP_SUBTYPE = store_thm
  ("MAP_SUBTYPE",
   ``!(x:'a->bool) (y:'b->bool) n.
       MAP IN (((x -> y) -> list x -> list y) INTER
               (UNIV -> gtlist n -> gtlist n))``,
   RW_TAC std_ss [IN_FUNSET, IN_INTER, IN_GTLIST, LENGTH_MAP]
   >> Induct_on `x''` >- RW_TAC std_ss [MAP, IN_LIST]
   >> RW_TAC std_ss [MAP, IN_LIST]);

val HD_SUBTYPE = store_thm
  ("HD_SUBTYPE",
   ``!x.  HD IN ((gtlist 0 INTER list x) -> x)``,
   RW_TAC std_ss [IN_FUNSET, IN_INTER, IN_GTLIST]
   >> Cases_on `x'`
   >- (Q.PAT_X_ASSUM `0 < LENGTH []` MP_TAC
       >> RW_TAC arith_ss [LENGTH])
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [IN_LIST, HD]);

val TL_SUBTYPE = store_thm
  ("TL_SUBTYPE",
   ``!x.  TL IN (((gtlist 0 INTER list x) -> list x) INTER
                 (gtlist 1 -> gtlist 0))``,
   RW_TAC std_ss [IN_FUNSET, IN_INTER, IN_GTLIST] >|
   [Cases_on `x'`
   >- (Q.PAT_X_ASSUM `0 < LENGTH []` MP_TAC
       >> RW_TAC arith_ss [LENGTH])
    >> POP_ASSUM MP_TAC
    >> RW_TAC std_ss [IN_LIST, TL],
    POP_ASSUM MP_TAC
    >> Cases_on `x` >- RW_TAC arith_ss [LENGTH]
    >> Cases_on `t` >- RW_TAC arith_ss [LENGTH]
    >> RW_TAC arith_ss [LENGTH, TL]]);

val LENGTH_SUBTYPE = store_thm
  ("LENGTH_SUBTYPE",
   ``LENGTH IN ((gtlist 0 -> gtnum 0) INTER (gtlist 1 -> gtnum 1))``,
   RW_TAC std_ss [IN_FUNSET, IN_INTER, IN_GTLIST, IN_GTNUM]);

val GTLIST0_SUBTYPE_REWRITE = store_thm
  ("GTLIST0_SUBTYPE_REWRITE",
   ``!l. l IN gtlist 0 ==> ~(l = []) /\ ~([] = l)``,
   Cases
   >> RW_TAC arith_ss [IN_GTLIST, LENGTH]);

val GTLIST1_SUBTYPE_REWRITE = store_thm
  ("GTLIST1_SUBTYPE_REWRITE",
   ``!l h. l IN gtlist 1 ==> ~(l = [h]) /\ ~([h] = l)``,
   Cases >- RW_TAC arith_ss [IN_GTLIST, LENGTH]
   >> Cases_on `t`
   >> RW_TAC arith_ss [IN_GTLIST, LENGTH]);

val GTLIST0_SUBTYPE_JUDGEMENT = store_thm
  ("GTLIST0_SUBTYPE_JUDGEMENT",
   ``!l m.
       LENGTH l IN gtnum 0 \/ ~([] = l) \/ ~(l = []) ==> l IN gtlist 0``,
   Cases
   >> RW_TAC std_ss [IN_GTLIST, IN_GTNUM, LENGTH]
   >> DECIDE_TAC);

val GTLIST1_SUBTYPE_JUDGEMENT = store_thm
  ("GTLIST1_SUBTYPE_JUDGEMENT",
   ``!l m. LENGTH l IN gtnum 1 ==> l IN gtlist 1``,
   RW_TAC std_ss [IN_GTLIST, IN_GTNUM]
   >> DECIDE_TAC);

val GTLIST1_SUBSET_GTLIST0 = store_thm
  ("GTLIST1_SUBSET_GTLIST0",
   ``gtlist 1 SUBSET gtlist 0``,
   RW_TAC std_ss [SUBSET_DEF, IN_GTLIST]
   >> DECIDE_TAC);

Definition LIST_COMBS_def:
   (LIST_COMBS [] _ = []) /\
   (LIST_COMBS (x::xs) l = (MAP (\y. (x, y)) l) ++ (LIST_COMBS xs l))
End

Theorem MEM_LIST_COMBS :
    !l l' x. MEM x (LIST_COMBS l l') <=> (MEM (FST x) l /\ MEM (SND x) l')
Proof
    Induct
 >> RW_TAC list_ss [LIST_COMBS_def]
 >> `?f s. x = (f, s)` by METIS_TAC [pair_CASES]
 >> RW_TAC list_ss [MEM_MAP, FST, SND]
 >> DECIDE_TAC
QED

Theorem LENGTH_LIST_COMBS :
    !x y. LENGTH (LIST_COMBS x y) = LENGTH x * LENGTH y
Proof
    Induct
 >> rw[LENGTH, LIST_COMBS_def, LENGTH_APPEND, LENGTH_MAP]
 >> `LENGTH y + LENGTH x * LENGTH y =
       1 * LENGTH y + LENGTH x * LENGTH y`
    by RW_TAC arith_ss []
 >> POP_ORW
 >> RW_TAC arith_ss [GSYM RIGHT_ADD_DISTRIB, ADD1]
QED

Theorem LIST_COMBS_EQ_NIL :
    !x y. (LIST_COMBS x y = []) <=> ((x = []) \/ (y = []))
Proof
    Induct >> RW_TAC list_ss [LIST_COMBS_def]
 >> DECIDE_TAC
QED

Theorem ALL_DISTINCT_APPEND :
    !l l'. ALL_DISTINCT l /\ ALL_DISTINCT l' /\ (!x. ~(MEM x l /\ MEM x l')) ==>
           ALL_DISTINCT (l ++ l')
Proof
    Induct
 >- RW_TAC std_ss [APPEND_NIL]
 >> RW_TAC std_ss [APPEND, ALL_DISTINCT, MEM, MEM_APPEND]
 >> METIS_TAC [APPEND, ALL_DISTINCT, MEM, MEM_APPEND]
QED

Theorem ALL_DISTINCT_MAP :
    !l f. ALL_DISTINCT l /\ (!x y. (f x = f y) = (x = y)) ==>
          ALL_DISTINCT (MAP f l)
Proof
    Induct
 >> RW_TAC std_ss [MAP, ALL_DISTINCT, MEM_MAP]
QED

Theorem ALL_DISTINCT_MAP2 :
    !l f. ALL_DISTINCT l /\ (!x y. MEM x l /\ MEM y l /\ (f x = f y) ==> (x = y)) ==>
          ALL_DISTINCT (MAP f l)
Proof
    Induct >> RW_TAC std_ss [MAP, ALL_DISTINCT, MEM_MAP, MEM]
 >> METIS_TAC []
QED

Theorem ALL_DISTINCT_LIST_COMBS :
    !l l'. ALL_DISTINCT l /\ ALL_DISTINCT l' ==> ALL_DISTINCT (LIST_COMBS l l')
Proof
    Induct
 >> RW_TAC std_ss [LIST_COMBS_def, ALL_DISTINCT]
 >> MATCH_MP_TAC ALL_DISTINCT_APPEND
 >> CONJ_TAC >- (MATCH_MP_TAC ALL_DISTINCT_MAP >> RW_TAC std_ss [])
 >> RW_TAC std_ss [MEM_MAP, MEM_LIST_COMBS]
 >> (ASSUME_TAC o Q.SPEC `x`) pair_CASES
 >> FULL_SIMP_TAC std_ss []
 >> Cases_on `q = h` >> RW_TAC std_ss []
QED
