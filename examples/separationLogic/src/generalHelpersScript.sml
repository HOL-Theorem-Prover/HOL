
Theory generalHelpers
Ancestors
  finite_map relation pred_set list rich_list arithmetic combin
  container bag sorting
Libs
  stringLib boolSimps ConseqConv quantHeuristicsLib

(*
quietdec := true;
loadPath :=
            (Globals.HOLDIR ^ "/examples/decidable_separationLogic/src") ::
            !loadPath;

map load ["finite_mapTheory", "relationTheory", "congLib", "sortingTheory",
   "rich_listTheory", "operatorTheory", "containerTheory", "bagTheory"];
show_assums := true;
*)

(*
quietdec := false;
*)

val _ = ParseExtras.temp_loose_equality()


(******************************************************************
 BOOL
 ******************************************************************)

Theorem COND_EXISTS:
  !P Q c. (?v. if c then P v else Q v) = if c then ?v. P v else ?v. Q v
Proof
METIS_TAC[]
QED

Definition BOOL_TO_NUM_def:
(BOOL_TO_NUM T = 1:num) /\
(BOOL_TO_NUM F = 0)
End

Theorem BOOL_TO_NUM_REWRITE:
   ((BOOL_TO_NUM c = 0) = ~c) /\
   ((BOOL_TO_NUM c = 1) = c) /\
   (BOOL_TO_NUM T = 1:num) /\
   (BOOL_TO_NUM F = 0) /\
   ((BOOL_TO_NUM c = BOOL_TO_NUM d) = (c = d))
Proof

Cases_on `c` THEN Cases_on `d` THEN
SIMP_TAC std_ss [BOOL_TO_NUM_def]
QED


Definition IS_BOOL_TO_NUM_def:
  IS_BOOL_TO_NUM n = (n = 0:num) \/ (n = 1)
End

Theorem IS_BOOL_TO_NUM_REWRITE:
    (IS_BOOL_TO_NUM 0) /\ (IS_BOOL_TO_NUM 1) /\
    (!n. ~(n = 0) ==> (IS_BOOL_TO_NUM n = (n = 1))) /\
    (!n. ~(n = 1) ==> (IS_BOOL_TO_NUM n = (n = 0)))
Proof
SIMP_TAC std_ss [IS_BOOL_TO_NUM_def]
QED


(******************************************************************
  Arithmetic
 ******************************************************************)

Theorem FORALL_LESS_SUC:
     !P m. ((!n. n < SUC m ==> P n) =
            (P 0 /\ (!n. n < m ==> P (SUC n))))
Proof

   REPEAT GEN_TAC THEN
   EQ_TAC THEN REPEAT STRIP_TAC THENL [
      ASM_SIMP_TAC arith_ss [],
      ASM_SIMP_TAC arith_ss [],

      Cases_on `n` THENL [
         ASM_REWRITE_TAC[],
         ASM_SIMP_TAC arith_ss []
      ]
   ]
QED

Theorem MIN_EQ:
  (!n1 n2. (MIN n1 n2 = n1) = (n1 <= n2)) /\
  (!n1 n2. (MIN n1 n2 = n2) = (n2 <= n1))
Proof
SIMP_TAC arith_ss [arithmeticTheory.MIN_DEF,
   COND_RAND, COND_RATOR]
QED

(******************************************************************
  PAIRS
 ******************************************************************)

Theorem PAIR_BETA_THM:
  !f. (\x. f x (FST x) (SND x)) = (\(x1,x2). f (x1,x2) x1 x2)
Proof

   SIMP_TAC std_ss [FUN_EQ_THM] THEN
   Cases_on `x` THEN
   SIMP_TAC std_ss []
QED


(******************************************************************
  LISTS
 ******************************************************************)


Theorem HD_LUPDATE:
  !n e l. (HD (LUPDATE e n l) =
      if (n = 0) /\ (0 < LENGTH l) then e else HD l)
Proof
SIMP_TAC std_ss [GSYM EL, EL_LUPDATE] THEN
METIS_TAC[]
QED


Theorem EL_LUPDATE___NO_COND:
  (!n e l. n < LENGTH l ==> (EL n (LUPDATE e n l) = e)) /\
  (!n1 n2 e l. ~(n1 = n2) ==> (EL n1 (LUPDATE e n2 l) = EL n1 l))
Proof
SIMP_TAC std_ss [EL_LUPDATE]
QED


Theorem TAKE_LUPDATE___SIMPLE:
  !n1 n2 e l. TAKE n1 (LUPDATE e n2 l) =
  LUPDATE e n2 (TAKE n1 l)
Proof
Induct_on `n1` THEN Cases_on `n2` THEN Cases_on `l` THEN
ASM_SIMP_TAC list_ss [LUPDATE_def]
QED

Theorem LUPDATE_APPEND1:
  !n l1 l2. n < LENGTH l1 ==> (
     LUPDATE e n (l1 ++ l2) =
     (LUPDATE e n l1) ++ l2)
Proof

SIMP_TAC list_ss [LIST_EQ_REWRITE, EL_LUPDATE,
   LENGTH_LUPDATE] THEN
REPEAT STRIP_TAC THEN
Cases_on `x < LENGTH l1` THEN (
   ASM_SIMP_TAC list_ss [EL_APPEND1, EL_APPEND2, LENGTH_LUPDATE,
     EL_LUPDATE]
)
QED


Theorem LUPDATE_APPEND2:
  !n l1 l2. LENGTH l1 <= n ==> (
     LUPDATE e n (l1 ++ l2) =
     l1 ++ (LUPDATE e (n - LENGTH l1) l2))
Proof

SIMP_TAC list_ss [LIST_EQ_REWRITE, EL_LUPDATE,
   LENGTH_LUPDATE] THEN
REPEAT STRIP_TAC THEN
Cases_on `x < LENGTH l1` THEN (
   ASM_SIMP_TAC list_ss [EL_APPEND1, EL_APPEND2, LENGTH_LUPDATE,
     EL_LUPDATE]
) THEN
`(x - LENGTH l1 = n - LENGTH l1) = (x = n)` by DECIDE_TAC THEN
PROVE_TAC[]
QED


Theorem LENGTH_TAKE_MIN:
  !n l. LENGTH (TAKE n l) = MIN n (LENGTH l)
Proof
Induct_on `l` THEN
Induct_on `n` THEN
ASM_SIMP_TAC list_ss [arithmeticTheory.MIN_DEF]
QED


Theorem LENGTH_TAKE_LESS_EQ:
  !n l. LENGTH (TAKE n l) <= n
Proof
SIMP_TAC std_ss [LENGTH_TAKE_MIN]
QED


Theorem LIST_NOT_NIL___HD_EXISTS:
  !l. ~(l = []) = ?e l'. l = e::l'
Proof
GEN_TAC THEN
Cases_on `l` THEN
SIMP_TAC list_ss []
QED


Theorem EL_DISJOINT_FILTER:

     !n1 n2 P l. (~(n1 = n2) /\ (n1 < LENGTH l) /\ (n2 < LENGTH l) /\
                   (EL n1 l = EL n2 l) /\ (P (EL n2 l))) ==>
                 ?n1' n2'. ~(n1' = n2') /\
                           (n1' < LENGTH (FILTER P l)) /\
                           (n2' < LENGTH (FILTER P l)) /\
                           (EL n1' (FILTER P l) = EL n2 l) /\
                           (EL n2' (FILTER P l) = EL n2 l)
Proof

   HO_MATCH_MP_TAC (prove (``((!n1 n2. P n1 n2 = P n2 n1) /\ (!n1 n2. (n1 <= n2) ==> P n1 n2)) ==>
                             (!n1 n2. P n1 n2)``,
                    METIS_TAC[arithmeticTheory.LESS_EQ_CASES])) THEN
   CONJ_TAC THEN1 METIS_TAC[] THEN
   REPEAT STRIP_TAC THEN

   `l = (TAKE (SUC n1) l) ++ (LASTN (LENGTH l - (SUC n1)) l)` by (
      MATCH_MP_TAC (GSYM APPEND_TAKE_LASTN) THEN
      ASM_SIMP_TAC arith_ss []
   ) THEN
   Q.ABBREV_TAC `l1 = (TAKE (SUC n1) l)` THEN
   Q.ABBREV_TAC `l2 = (LASTN (LENGTH l - (SUC n1)) l)` THEN
   `(n1 < LENGTH l1) /\ (LENGTH l1 <= n2)` by (
      bossLib.UNABBREV_ALL_TAC THEN
      ASM_SIMP_TAC list_ss [LENGTH_TAKE]
   ) THEN
   FULL_SIMP_TAC list_ss [EL_APPEND2, EL_APPEND1] THEN
   `n2 - LENGTH l1 < LENGTH l2` by DECIDE_TAC THEN
   `MEM (EL n1 l1) (FILTER P l1)` by METIS_TAC[MEM_FILTER, MEM_EL] THEN
   `MEM (EL n1 l1) (FILTER P l2)` by METIS_TAC[MEM_FILTER, MEM_EL] THEN
   FULL_SIMP_TAC list_ss [MEM_EL, FILTER_APPEND] THEN
   Q.EXISTS_TAC `n` THEN
   Q.EXISTS_TAC `LENGTH (FILTER P l1) + n'` THEN
   FULL_SIMP_TAC list_ss [EL_APPEND1, EL_APPEND2]
QED


Theorem DROP_LENGTH_LESS:
  !l n. (LENGTH l <= n) ==> (DROP n l = [])
Proof
Induct_on `n` THEN Induct_on `l` THEN
ASM_SIMP_TAC list_ss []
QED


Definition EVERY_PAIR_def:
   (EVERY_PAIR P [] = T) /\
   (EVERY_PAIR P (e::l) = (EVERY (P e) l /\ EVERY_PAIR P l))
End


Theorem ALL_DISTINCT_EVERY_PAIR:
  !l. ALL_DISTINCT l = EVERY_PAIR (\x y. ~(x = y)) l
Proof
Induct_on `l` THEN ASM_SIMP_TAC list_ss [EVERY_PAIR_def, EVERY_MEM]
QED


Theorem EVERY_PAIR_APPEND:
  !P l1 l2. EVERY_PAIR P (l1 ++ l2) =
            EVERY_PAIR P l1 /\ EVERY_PAIR P l2 /\
            (!e1 e2. MEM e1 l1 /\ MEM e2 l2 ==> P e1 e2)
Proof

GEN_TAC THEN Induct_on `l1` THEN
ASM_SIMP_TAC (list_ss++EQUIV_EXTRACT_ss)
  [EVERY_PAIR_def, EVERY_MEM, RIGHT_AND_OVER_OR, DISJ_IMP_THM,
   FORALL_AND_THM]
QED


Theorem EVERY_PAIR_SING:
  !P e. EVERY_PAIR P [e]
Proof
SIMP_TAC std_ss [EVERY_PAIR_def, EVERY_DEF]
QED


Theorem EVERY_PAIR_EL_DEF:
  !P l. EVERY_PAIR P l =
        (!n1 n2. n1 < n2 /\ n2 < LENGTH l ==>
            (P (EL n1 l) (EL n2 l)))
Proof
GEN_TAC THEN Induct_on `l` THEN
ASM_SIMP_TAC list_ss [EVERY_PAIR_def, EVERY_MEM] THEN
GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
   Cases_on `n1` THEN Cases_on `n2` THEN FULL_SIMP_TAC list_ss [] THEN
   `MEM (EL n l) l` by (SIMP_TAC list_ss [MEM_EL] THEN PROVE_TAC[]) THEN
   PROVE_TAC[],

   FULL_SIMP_TAC std_ss [MEM_EL] THEN
   Q.PAT_X_ASSUM `!n1 n2. X n1 n2` (MP_TAC o Q.SPECL [`0`, `SUC n`]) THEN
   ASM_SIMP_TAC list_ss [],

   Q.PAT_X_ASSUM `!n1 n2. X n1 n2` (MP_TAC o Q.SPECL [`SUC n1`, `SUC n2`]) THEN
   ASM_SIMP_TAC list_ss []
]
QED


Theorem EVERY_PAIR_EL_DEF_symmetric:
  !P. symmetric P ==>
  !l. EVERY_PAIR P l =
        (!n1 n2. n1 < LENGTH l /\ n2 < LENGTH l /\ ~(n1 = n2) ==>
            (P (EL n1 l) (EL n2 l)))
Proof
SIMP_TAC std_ss [relationTheory.symmetric_def, EVERY_PAIR_EL_DEF] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
   `n1 < n2 \/ n2 < n1` by DECIDE_TAC THEN
   PROVE_TAC[],

   `(n1 < LENGTH l) /\ ~(n1 = n2)` by DECIDE_TAC THEN
   PROVE_TAC[]
]
QED

Theorem FILTER_EVERY_PAIR:
  !P1 P2 l. EVERY_PAIR P1 l ==> EVERY_PAIR P1 (FILTER P2 l)
Proof
Induct_on `l` THEN
SIMP_TAC (list_ss++COND_elim_ss) [EVERY_PAIR_def] THEN
REPEAT STRIP_TAC THEN
ASM_SIMP_TAC list_ss [EVERY_FILTER_IMP]
QED


Theorem EVERY_PAIR_SNOC:
  !P e l. EVERY_PAIR P (SNOC e l) =
          (EVERY (\x. P x e) l /\ EVERY_PAIR P l)
Proof
Induct_on `l` THEN (
   ASM_SIMP_TAC (list_ss++EQUIV_EXTRACT_ss) [EVERY_PAIR_SING, SNOC, EVERY_PAIR_def,
                     ALL_EL_SNOC]
)
QED


Theorem EVERY_PAIR_PERM:
  !P. symmetric P ==>
  !l1 l2. PERM l1 l2 ==> (EVERY_PAIR P l1 = EVERY_PAIR P l2)
Proof
GEN_TAC THEN STRIP_TAC THEN
HO_MATCH_MP_TAC PERM_lifts_equalities THEN
FULL_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [EVERY_PAIR_APPEND, MEM_APPEND,
   RIGHT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM, relationTheory.symmetric_def] THEN
METIS_TAC[]
QED


Theorem HD_DROP:
  !l n. (n < LENGTH l) ==>
   (HD (DROP n l) = EL n l)
Proof

Induct_on `n` THEN1 (
  SIMP_TAC list_ss [EL]
) THEN
REPEAT STRIP_TAC THEN
Cases_on `l` THEN
FULL_SIMP_TAC list_ss []
QED


Theorem FIRSTN_LENGTH_ID_EVAL:
  !l n. (LENGTH l = n) ==> (TAKE n l = l)
Proof
METIS_TAC[rich_listTheory.FIRSTN_LENGTH_ID]
QED

Theorem BUTFIRSTN_LENGTH_NIL_EVAL:
  !l n. (LENGTH l = n) ==> (DROP n l = [])
Proof
METIS_TAC[rich_listTheory.BUTFIRSTN_LENGTH_NIL]
QED


Theorem DROP_LUPDATE:
  !l n m e. (n <= LENGTH l) /\ (m < n) ==>
   (DROP n (LUPDATE e m l) =
    DROP n l)
Proof

Induct_on `n` THEN1 (
   SIMP_TAC list_ss []
) THEN
REPEAT STRIP_TAC THEN
Cases_on `l` THEN1 (
   SIMP_TAC list_ss [LUPDATE_def]
) THEN
Cases_on `m` THEN (
   FULL_SIMP_TAC list_ss [LUPDATE_def]
)
QED

Theorem TAKE_EQ_APPEND_REWRITE:
  !n l l1. (LENGTH l1 = n) ==> ((TAKE n l = l1) = (?l2. l = l1 ++ l2))
Proof

Induct_on `n` THEN (
   SIMP_TAC (list_ss++CONJ_ss) [TAKE, LENGTH_EQ_NUM]
) THEN
REPEAT STRIP_TAC THEN
Cases_on `l` THEN (
   ASM_SIMP_TAC list_ss [GSYM LEFT_EXISTS_AND_THM,
      GSYM RIGHT_EXISTS_AND_THM]
)
QED


Theorem TAKE_LUPDATE:
  !l n m e. (n <= LENGTH l) /\ (n <= m) ==>
   (TAKE n (LUPDATE e m l) =
    TAKE n l)
Proof

Induct_on `n` THEN1 (
   SIMP_TAC list_ss []
) THEN
REPEAT STRIP_TAC THEN
Cases_on `l` THEN1 (
   SIMP_TAC list_ss [LUPDATE_def]
) THEN
Cases_on `m` THEN (
   FULL_SIMP_TAC list_ss [LUPDATE_def]
)
QED


Definition ALL_DISJOINT_def:   ALL_DISJOINT = EVERY_PAIR DISJOINT
End

Theorem ALL_DISJOINT_THM:
   (ALL_DISJOINT []) /\ (!e. ALL_DISJOINT [e]) /\
   (!e1 l. (ALL_DISJOINT (e1::l) = (EVERY (\e2. DISJOINT e1 e2) l) /\ ALL_DISJOINT l)) /\
   (!e1 l. (ALL_DISJOINT (SNOC e1 l) = (EVERY (\e2. DISJOINT e1 e2) l) /\ ALL_DISJOINT l)) /\
   (!l1 l2. ALL_DISJOINT (l1++l2) =
            ALL_DISJOINT l1 /\ ALL_DISJOINT l2 /\
            (!e1 e2. MEM e1 l1 /\ MEM e2 l2 ==> DISJOINT e1 e2))
Proof

REWRITE_TAC[ALL_DISJOINT_def, EVERY_PAIR_APPEND, EVERY_PAIR_SING,
            EVERY_PAIR_def, EVERY_PAIR_SNOC] THEN
SIMP_TAC (std_ss ++ EQUIV_EXTRACT_ss) [EVERY_MEM] THEN
METIS_TAC[DISJOINT_SYM]
QED


Theorem EL_ALL_DISJOINT_EQ:
     !l. ALL_DISJOINT l =
         (!n1 n2. n1 < LENGTH l /\ n2 < LENGTH l ==>
         (DISJOINT (EL n1 l) (EL n2 l) = (~(n1 = n2) \/ (EL n1 l = EMPTY))))
Proof

   GEN_TAC THEN
   `symmetric DISJOINT` by SIMP_TAC std_ss [DISJOINT_SYM, relationTheory.symmetric_def] THEN
   ASM_SIMP_TAC std_ss [EVERY_PAIR_EL_DEF_symmetric, ALL_DISJOINT_def] THEN
   REDEPTH_CONSEQ_CONV_TAC (K FORALL_EQ___CONSEQ_CONV) THEN
   SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
   REPEAT STRIP_TAC THEN
   Cases_on `n1 = n2` THEN ASM_REWRITE_TAC[GSYM DISJOINT_EMPTY_REFL]
QED



Theorem ALL_DISJOINT_PERM:
     !l1 l2. PERM l1 l2 ==> (ALL_DISJOINT l1 = ALL_DISJOINT l2)
Proof
   REWRITE_TAC[ALL_DISJOINT_def] THEN
   MATCH_MP_TAC EVERY_PAIR_PERM THEN
   SIMP_TAC std_ss [relationTheory.symmetric_def, DISJOINT_SYM]
QED




Definition FIRST_OCCURENCE_def:
  (FIRST_OCCURENCE n P [] = NONE) /\
  (FIRST_OCCURENCE n P (x::L) = if (P x) then SOME (n,x)
                                else FIRST_OCCURENCE (SUC n) P L)
End

Theorem FIRST_OCCURENCE_EQ_REWRITES:
  (!n P L. (FIRST_OCCURENCE n P L = NONE) = (EVERY ($~ o P) L)) /\
  (!n m x P L. (FIRST_OCCURENCE n P L = (SOME (m,x))) =
               (EXISTS P L /\ (n <= m) /\ (EL (m-n) L = x) /\ P x /\
                !m'. m' < (m - n) ==> ~(P (EL m' L))))
Proof
  CONJ_TAC THENL [
    Induct_on `L` THEN
    ASM_SIMP_TAC list_ss [FIRST_OCCURENCE_def, COND_RAND, COND_RATOR],

    Induct_on `L` THEN
    ASM_SIMP_TAC list_ss [FIRST_OCCURENCE_def, COND_RAND, COND_RATOR] THEN
    SIMP_TAC std_ss [COND_EXPAND_IMP, FORALL_AND_THM] THEN
    CONJ_TAC THENL [
        REPEAT STRIP_TAC THEN
        Cases_on `n = m` THEN ASM_SIMP_TAC list_ss [] THENL [
          PROVE_TAC[],

          Cases_on `n <= m` THEN ASM_REWRITE_TAC[] THEN
          STRIP_TAC THEN DISJ2_TAC THEN
          Q.EXISTS_TAC `0` THEN
          ASM_SIMP_TAC list_ss []
        ],

        SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
        REPEAT STRIP_TAC THEN
        Cases_on `n <= m` THEN ASM_SIMP_TAC arith_ss [] THEN
        Cases_on `n = m` THEN1 (
          ASM_SIMP_TAC list_ss [] THEN PROVE_TAC[]
          ) THEN
        ASM_SIMP_TAC arith_ss [] THEN
        Q.ABBREV_TAC `n' = m - SUC n` THEN
        `m - n = SUC n'` by (
          Q.UNABBREV_TAC `n'` THEN DECIDE_TAC
          ) THEN
        ASM_SIMP_TAC (list_ss++EQUIV_EXTRACT_ss) [FORALL_LESS_SUC]
      ]
  ]
QED

Theorem IS_SOME___FIRST_OCCURENCE:
  !n P L. IS_SOME (FIRST_OCCURENCE n P L) = EXISTS P L
Proof
REPEAT GEN_TAC THEN
Cases_on `FIRST_OCCURENCE n P L` THENL [
   FULL_SIMP_TAC std_ss [FIRST_OCCURENCE_EQ_REWRITES, NOT_EXISTS],

   Cases_on `x` THEN
   FULL_SIMP_TAC std_ss [FIRST_OCCURENCE_EQ_REWRITES]
]
QED


Theorem FIRST_OCCURENCE___ALL_DISTINCT:
  !n m L. (ALL_DISTINCT L /\ (n < LENGTH L)) ==>
          (FIRST_OCCURENCE m ($= (EL n L)) L = SOME (n+m, (EL n L)))
Proof

SIMP_TAC list_ss [FIRST_OCCURENCE_EQ_REWRITES, ALL_DISTINCT_EL_IMP] THEN
SIMP_TAC std_ss [EXISTS_MEM, MEM_EL] THEN PROVE_TAC[]
QED




val MEM_COMPLETE_NUM_LIST___SORTED = prove (``
!l. SORTED (\n m. m <= n) l ==>
((!e. MEM e l ==> (e < LENGTH l) /\ ALL_DISTINCT l) ==>
(!e. MEM e l = (e < LENGTH l)))``,

Induct_on `l` THENL [
   SIMP_TAC list_ss [],

   REPEAT STRIP_TAC THEN
   MP_TAC (ISPECL [``\n:num m:num. m <= n``, ``l:num list``, ``h:num``] SORTED_EQ) THEN
   ASM_SIMP_TAC list_ss [transitive_def] THEN
   STRIP_TAC THEN
   FULL_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
   `!e. MEM e l ==> e < LENGTH l` by (
      REPEAT STRIP_TAC THEN
      RES_TAC THEN
      `~(e = h)` by PROVE_TAC[] THEN
      DECIDE_TAC
   ) THEN
   RES_TAC THEN
   `h = LENGTH l` by (
      CCONTR_TAC THEN
      `h < LENGTH l` by DECIDE_TAC THEN
      METIS_TAC[]
   ) THEN
   ASM_SIMP_TAC arith_ss []
]);



Theorem MEM_COMPLETE_NUM_LIST:
  !l.
(!e. MEM e l ==> (e < LENGTH l) /\ ALL_DISTINCT l) ==>
(!e. MEM e l = (e < LENGTH l))
Proof


GEN_TAC THEN
`?l'. l' = QSORT (\n m. m <= n) l` by METIS_TAC[] THEN
`PERM l l'` by ASM_REWRITE_TAC[QSORT_PERM] THEN
`SORTED (\n m. m <= n) l'` by (
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC QSORT_SORTED THEN
   SIMP_TAC arith_ss [transitive_def, total_def]
) THEN
METIS_TAC[PERM_MEM_EQ, PERM_LENGTH, ALL_DISTINCT_PERM,
          MEM_COMPLETE_NUM_LIST___SORTED]
QED

Theorem ZIP_APPEND:
  !l1 l2 l3 l4. (LENGTH l1 = LENGTH l3) ==>
(ZIP (l1++l2,l3++l4) = ZIP (l1,l3)++ZIP(l2,l4))
Proof

Induct_on `l3` THENL [
   SIMP_TAC list_ss [LENGTH_NIL],

   Cases_on `l1` THEN
   ASM_SIMP_TAC list_ss []
]
QED


Theorem MEM_ZIP_EQ:
  !x l. MEM x (ZIP (l,l)) = (?x'. (x = (x',x')) /\ MEM x' l)
Proof
Induct_on `l` THEN
ASM_SIMP_TAC list_ss [] THEN
METIS_TAC[]
QED


Theorem MAP_ZIP_EQ:
  !f l. MAP f (ZIP (l,l)) = (MAP (\x. f (x,x)) l)
Proof
Induct_on `l` THEN ASM_SIMP_TAC list_ss []
QED


Definition LIST_ZIP_def:
  LIST_ZIP L = if NULL (HD L) \/ NULL L then []
               else (MAP HD L)::LIST_ZIP (MAP TL L)
Termination
  Q.EXISTS_TAC `measure (\l. LENGTH (HD l))` THEN
  REWRITE_TAC[prim_recTheory.measure_thm, prim_recTheory.WF_measure] THEN
  Cases_on `L` THEN SIMP_TAC list_ss [] THEN
  Cases_on `h` THEN SIMP_TAC list_ss []
End


Theorem LIST_ZIP_REWRITE:
  (LIST_ZIP [] = []) /\
  (LIST_ZIP ([]::L) = []) /\
  (LIST_ZIP ((e::es)::L) = (e::(MAP HD L))::(LIST_ZIP (es::(MAP TL L))))
Proof

REPEAT CONJ_TAC THEN (
   CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [LIST_ZIP_def])) THEN
   SIMP_TAC list_ss []
)
QED



Theorem LENGTH_LIST_ZIP:
  (LENGTH (LIST_ZIP []) = 0) /\
  !e es. (LENGTH (LIST_ZIP (e::es)) = LENGTH e)
Proof

SIMP_TAC list_ss [LIST_ZIP_REWRITE] THEN
Induct_on `e` THEN (
   ASM_SIMP_TAC list_ss [LIST_ZIP_REWRITE]
)
QED


Theorem LENGTH_EL_LIST_ZIP:
  !L. EVERY (\l. LENGTH l = LENGTH L) (LIST_ZIP L)
Proof
Cases_on `L` THEN SIMP_TAC list_ss [LIST_ZIP_REWRITE] THEN
Q.SPEC_TAC (`t`, `t`) THEN
Induct_on `h` THEN SIMP_TAC list_ss [LIST_ZIP_REWRITE] THEN
METIS_TAC[LENGTH_MAP]
QED


Theorem LIST_ZIP_CONS_REWRITE:

!l L n. (~NULL L /\ EVERY (\l. LENGTH l = n) (l::L)) ==>
      (LIST_ZIP (l::L) =
       MAP (\ (L',l'). l'::L') (ZIP (LIST_ZIP L, l)))
Proof

Cases_on `L` THEN SIMP_TAC list_ss [] THEN
Q.SPEC_TAC (`t`, `ts`) THEN
Q.SPEC_TAC (`h`, `t`) THEN
Induct_on `l` THENL [
   SIMP_TAC list_ss [LENGTH_NIL, LIST_ZIP_REWRITE],

   Cases_on `t` THEN
   SIMP_TAC list_ss [LIST_ZIP_REWRITE] THEN
   REPEAT STRIP_TAC THEN
   Q.PAT_X_ASSUM `!t ts. X t ts` MATCH_MP_TAC THEN
   FULL_SIMP_TAC std_ss [EVERY_MEM, MEM_MAP, GSYM LEFT_FORALL_IMP_THM] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   Cases_on `y` THEN FULL_SIMP_TAC list_ss []
]
QED

Theorem LIST_ZIP_SING_REWRITE:
  !l. LIST_ZIP [l] = MAP (\e. [e]) l
Proof
Induct_on `l` THEN ASM_SIMP_TAC list_ss [LIST_ZIP_REWRITE]
QED



Theorem MAP_HD_LIST_ZIP:
  !e es. MAP HD (LIST_ZIP (e::es)) = e
Proof
Induct_on `e` THEN ASM_SIMP_TAC list_ss [LIST_ZIP_REWRITE]
QED

Theorem LIST_ZIP_MAP_CONS:
  !l1 l2. ((LENGTH l1 = LENGTH l2) /\ (~(NULL l2) \/ ~(NULL l1))) ==>
((LIST_ZIP (MAP (\ (L',l'). l'::L') (ZIP (l1,l2)))) =
l2::(LIST_ZIP l1))
Proof

Induct_on `l2` THEN
SIMP_TAC (list_ss++QUANT_INST_ss[list_qp]) [LIST_ZIP_REWRITE, MAP_MAP_o, combinTheory.o_DEF,
                  PAIR_BETA_THM] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN
`((MAP (\ (x1,x2). x2) (ZIP (l',l2)) = l2) /\
                    (MAP (\ (x1,x2). x1) (ZIP (l',l2)) = l'))` suffices_by (STRIP_TAC THEN
   ASM_REWRITE_TAC[]
) THEN
POP_ASSUM MP_TAC THEN
Q.SPEC_TAC (`l2`, `l2`) THEN
Q.SPEC_TAC (`l'`, `l1`) THEN
REPEAT (POP_ASSUM (K ALL_TAC)) THEN
Induct_on `l1` THEN
ASM_SIMP_TAC (list_ss++QUANT_INST_ss[list_qp]) []
QED

Theorem LIST_ZIP___LIST_ZIP:
  !L n. EVERY (\l. LENGTH l = SUC n) L ==>
        (LIST_ZIP (LIST_ZIP L) = L)
Proof

Cases_on `L` THEN SIMP_TAC list_ss [LIST_ZIP_REWRITE] THEN
Cases_on `h` THEN SIMP_TAC list_ss [] THEN
Q.SPEC_TAC (`t`, `t`) THEN
Q.SPEC_TAC (`h'`, `h`) THEN
Q.SPEC_TAC (`t'`, `hs`) THEN
Induct_on `t` THENL [
   SIMP_TAC list_ss [LIST_ZIP_SING_REWRITE] THEN
   Induct_on `hs` THEN ASM_SIMP_TAC list_ss [LIST_ZIP_REWRITE] THEN
   REPEAT (POP_ASSUM (K ALL_TAC))THEN
   Induct_on `hs` THEN ASM_SIMP_TAC list_ss [],

   REPEAT STRIP_TAC THEN
   MP_TAC (Q.SPECL [`h'::hs`, `h::t`, `SUC (LENGTH hs)`] LIST_ZIP_CONS_REWRITE) THEN
   ASM_SIMP_TAC list_ss [] THEN
   DISCH_TAC THEN (POP_ASSUM (K ALL_TAC)) THEN
   MP_TAC (Q.SPECL [`LIST_ZIP (h::t)`, `h'::hs`] LIST_ZIP_MAP_CONS) THEN
   FULL_SIMP_TAC list_ss [LENGTH_LIST_ZIP] THEN
   DISCH_TAC THEN (POP_ASSUM (K ALL_TAC)) THEN
   Cases_on `h` THEN FULL_SIMP_TAC list_ss []
]
QED


Theorem ZIP___LIST_ZIP:
  !l1 l2. (LENGTH l1 = LENGTH l2) ==>
(ZIP (l1,l2) = MAP (\l. (EL 0 l, EL 1 l)) (LIST_ZIP [l1;l2]))
Proof

Induct_on `l2` THEN
ASM_SIMP_TAC (list_ss++QUANT_INST_ss[list_qp]) [LIST_ZIP_REWRITE]
QED

val _ = type_abbrev ("label", ``:ind``);

Definition LIST_UNROLL_GIVEN_ELEMENT_NAMES_def:
    LIST_UNROLL_GIVEN_ELEMENT_NAMES l1 (l2:label list) =
    (LENGTH l1 = LENGTH l2)
End


Theorem LIST_UNROLL_GIVEN_ELEMENT_NAMES_REWRITE:
  (LIST_UNROLL_GIVEN_ELEMENT_NAMES [] []) /\
  (LIST_UNROLL_GIVEN_ELEMENT_NAMES (x::xs) (y::ys) =
   LIST_UNROLL_GIVEN_ELEMENT_NAMES xs ys) /\
  ~(LIST_UNROLL_GIVEN_ELEMENT_NAMES [] (y::ys)) /\
  ~(LIST_UNROLL_GIVEN_ELEMENT_NAMES (x::xs) [])
Proof

SIMP_TAC list_ss [LIST_UNROLL_GIVEN_ELEMENT_NAMES_def]
QED




Theorem LIST_UNROLL_GIVEN_ELEMENT_NAMES___UNROLL:
  (!x. (LIST_UNROLL_GIVEN_ELEMENT_NAMES x [] = (x = []))) /\
  (!x h L. (LIST_UNROLL_GIVEN_ELEMENT_NAMES x (h::L) =
   ?h' L'. (x = h'::L') /\ (LIST_UNROLL_GIVEN_ELEMENT_NAMES L' L)))
Proof

REPEAT STRIP_TAC THEN
Cases_on `x` THEN
SIMP_TAC list_ss [LIST_UNROLL_GIVEN_ELEMENT_NAMES_def]
QED



Theorem LIST_UNROLL_GIVEN_ELEMENT_NAMES___MAP:
  LIST_UNROLL_GIVEN_ELEMENT_NAMES (MAP f L) L' =
  LIST_UNROLL_GIVEN_ELEMENT_NAMES L L'
Proof

SIMP_TAC list_ss [LIST_UNROLL_GIVEN_ELEMENT_NAMES_def]
QED




Definition LIST_TO_FUN_def:
(LIST_TO_FUN [] = \x. ARB) /\
(LIST_TO_FUN (x::L) = (FST x =+ SND x) (LIST_TO_FUN L))
End


Theorem LIST_TO_FUN_THM:
  (!x L. LIST_TO_FUN (x::L) (FST x) = (SND x)) /\
  (!x y L. ~(y = FST x) ==> (LIST_TO_FUN (x::L) y = LIST_TO_FUN L y))
Proof
SIMP_TAC list_ss [LIST_TO_FUN_def, combinTheory.UPDATE_def]
QED


Theorem LIST_TO_FUN_DISTINCT_THM:
  !x L.
(ALL_DISTINCT (MAP FST L) /\ (MEM x L)) ==>
(LIST_TO_FUN L (FST x) = (SND x))
Proof

Induct_on `L` THEN1 SIMP_TAC list_ss [] THEN
SIMP_TAC list_ss [LEFT_AND_OVER_OR, DISJ_IMP_THM, FORALL_AND_THM,
   LIST_TO_FUN_THM] THEN
REPEAT STRIP_TAC THEN
`~(FST h = FST x)` by (
   FULL_SIMP_TAC std_ss [MEM_MAP] THEN
   PROVE_TAC[]
) THEN
ASM_SIMP_TAC std_ss [LIST_TO_FUN_THM]
QED


Theorem NULL_DROP:
    !n l. NULL (DROP n l) = (LENGTH l <= n)
Proof
  Induct_on `l` >> simp[] >> Cases_on `n` >> simp[]
QED


Theorem DROP_TAKE_PRE_LENGTH:
  !xs. ~(xs = []) ==> ((DROP (LENGTH xs - 1) xs = [LAST xs]) /\
                       (TAKE (LENGTH xs - 1) xs = FRONT xs))
Proof
Induct_on `xs` THEN1 REWRITE_TAC [] THEN
Cases_on `xs` THEN (
   FULL_SIMP_TAC bool_ss [LENGTH, DROP_0, LAST_CONS,
      FRONT_CONS, TAKE_0, NOT_CONS_NIL, DROP_def, TAKE_def,
      arithmeticTheory.SUC_SUB1, numTheory.NOT_SUC]
)
QED

Theorem LAST_DROP_THM:
   !x xs. (if xs = [] then [x] else DROP (LENGTH xs - 1) xs) = [LAST (x::xs)]
Proof
SIMP_TAC std_ss [DROP_TAKE_PRE_LENGTH, LAST_DEF, COND_RAND, COND_RATOR]
QED

Theorem LAST_DROP_THM2:
   !x xs. DROP (LENGTH xs) (x::xs) = [LAST (x::xs)]
Proof
Induct_on `xs` THEN ASM_SIMP_TAC list_ss []
QED

Theorem FRONT_TAKE_THM:
   !x xs. (if xs = [] then [] else (x::(TAKE (LENGTH xs - 1) xs))) = FRONT (x::xs)
Proof
SIMP_TAC std_ss [DROP_TAKE_PRE_LENGTH, FRONT_DEF]
QED

Theorem FRONT_TAKE_THM2:
   !x xs. TAKE (LENGTH xs) (x::xs) = FRONT (x::xs)
Proof
Induct_on `xs` THEN ASM_SIMP_TAC list_ss []
QED

Definition SWAP_ELEMENTS_def:
SWAP_ELEMENTS n m l =
  (LUPDATE (EL n l) m
      (LUPDATE (EL m l) n l))
End

Theorem SWAP_ELEMENTS_INTRO:
  !n m l e1 e2.
  (EL n l = e1) /\ (EL m l = e2) ==>
  ((LUPDATE e1 m (LUPDATE e2 n l)) =
  SWAP_ELEMENTS n m l)
Proof
SIMP_TAC std_ss [SWAP_ELEMENTS_def]
QED


Theorem LENGTH_SWAP_ELEMENTS:
  LENGTH (SWAP_ELEMENTS n m l) = LENGTH l
Proof
SIMP_TAC std_ss [SWAP_ELEMENTS_def, LUPDATE_SEM]
QED


Theorem SWAP_ELEMENTS_SYM:
    SWAP_ELEMENTS n m l = SWAP_ELEMENTS m n l
Proof
SIMP_TAC std_ss [LIST_EQ_REWRITE, LUPDATE_SEM,
   SWAP_ELEMENTS_def, EL_LUPDATE] THEN
METIS_TAC[]
QED


Theorem LUPDATE___NO_REPLACE:
  !e n l. ~(n < LENGTH l) ==> (LUPDATE e n l = l)
Proof
Induct_on `n` THEN (
   Cases_on `l` THEN
   ASM_SIMP_TAC list_ss [LUPDATE_def]
)
QED


Theorem LUPDATE___ALTERNATIVE_DEF:
  !e n l. (n < LENGTH l) ==> (LUPDATE e n l = (TAKE n l) ++ [e] ++ (DROP (SUC n) l))
Proof
Induct_on `n` THEN (
   Cases_on `l` THEN
   ASM_SIMP_TAC list_ss [LUPDATE_def]
)
QED


Theorem LUPDATE___REPLACE_ID:
  !n l. LUPDATE (EL n l) n l = l
Proof
Induct_on `n` THEN (
   Cases_on `l` THEN
   ASM_SIMP_TAC list_ss [LUPDATE_def]
)
QED


Theorem SWAP_ELEMENTS_EQ:
  !n l. SWAP_ELEMENTS n n l = l
Proof

SIMP_TAC std_ss [SWAP_ELEMENTS_def] THEN
Induct_on `n` THEN (
   Cases_on `l` THEN
   ASM_SIMP_TAC list_ss [SWAP_ELEMENTS_def, LUPDATE_def]
)
QED


Theorem EL_SWAP_ELEMENTS:
  !x n m l.
  EL x (SWAP_ELEMENTS n m l) =
  if (x < LENGTH l) then
    (if (x = m) then EL n l else
     (if (x = n) then EL m l else EL x l))
  else EL x l
Proof

SIMP_TAC std_ss [SWAP_ELEMENTS_def, EL_LUPDATE, LENGTH_LUPDATE] THEN
REPEAT GEN_TAC THEN
Cases_on `x < LENGTH l` THEN
PROVE_TAC[]
QED


val PERM_SWAP_ELEMENTS___helper = prove (
``!n1 n2 l. ((n1 + n2) < LENGTH l) ==>
  (PERM l (SWAP_ELEMENTS n1 (n1+n2) l))``,

SIMP_TAC std_ss [SWAP_ELEMENTS_def] THEN
Tactical.REVERSE (Induct_on `n1`) THEN1 (
   Cases_on `l` THEN
   ASM_SIMP_TAC std_ss [ADD_CLAUSES, LUPDATE_def, PERM_REFL,
      PERM_CONS_IFF, EL, TL, LENGTH]
) THEN
Cases_on `n2` THEN (
   Cases_on `l` THEN
   FULL_SIMP_TAC list_ss [LUPDATE_def, PERM_REFL]
) THEN
SIMP_TAC std_ss [LUPDATE___ALTERNATIVE_DEF] THEN
REPEAT STRIP_TAC THEN
`t = TAKE n t ++ (EL n t::(DROP (SUC n) t))` by (
   ASM_SIMP_TAC arith_ss [GSYM DROP_CONS_EL, APPEND_FIRSTN_BUTFIRSTN]
) THEN
POP_ASSUM (fn thm => CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV [thm])))) THEN
SIMP_TAC (std_ss++permLib.PERM_ss) []);


Theorem PERM_SWAP_ELEMENTS:
  !n1 n2 l. (n1 < LENGTH l) /\ (n2 < LENGTH l) ==>
   PERM l (SWAP_ELEMENTS n1 n2 l)
Proof

REPEAT STRIP_TAC THEN
`n1 <= n2 \/ n2 <= n1` by PROVE_TAC[LESS_EQ_CASES] THEN (
   IMP_RES_TAC LESS_EQUAL_ADD THEN
   METIS_TAC [PERM_SWAP_ELEMENTS___helper, ADD_COMM,
      SWAP_ELEMENTS_SYM]
)
QED


Definition LIST_NUM_STAR_def:
   (LIST_NUM_STAR 0 l = []) /\
   (LIST_NUM_STAR (SUC n) l = l++(LIST_NUM_STAR n l))
End

Definition LIST_STAR_def:
   LIST_STAR l l' = ?n. l' = LIST_NUM_STAR n l
End


Theorem LIST_STAR_REWRITE:
  (LIST_STAR l []) /\
  (~(t = []) ==> (LIST_STAR l t = ?t'. (t = l++t') /\ LIST_STAR l t'))
Proof

SIMP_TAC std_ss [LIST_STAR_def] THEN
REPEAT STRIP_TAC THENL [
   Q.EXISTS_TAC `0` THEN
   SIMP_TAC std_ss [LIST_NUM_STAR_def],

   EQ_TAC THENL [
      STRIP_TAC THEN
      Cases_on `n` THEN (
         FULL_SIMP_TAC std_ss [LIST_NUM_STAR_def]
      ) THEN
      METIS_TAC[],

      STRIP_TAC THEN
      Q.EXISTS_TAC `SUC n` THEN
      ASM_SIMP_TAC std_ss [LIST_NUM_STAR_def]
   ]
]
QED




Theorem LIST_NUM_STAR_SYM:
   (LIST_NUM_STAR 0 l = []) /\
   (LIST_NUM_STAR (SUC n) l = (LIST_NUM_STAR n l)++l)
Proof

SIMP_TAC std_ss [LIST_NUM_STAR_def] THEN
Induct_on `n` THENL [
   SIMP_TAC list_ss [LIST_NUM_STAR_def],

   ASM_SIMP_TAC std_ss [LIST_NUM_STAR_def,
      APPEND_ASSOC]
]
QED



Definition LIST_NUM_SET_STAR_def:
   (LIST_NUM_SET_STAR 0 ls = {[]}) /\
   (LIST_NUM_SET_STAR (SUC n) ls =
      {l++t | (l IN ls) /\ (t IN (LIST_NUM_SET_STAR n ls))})
End

Definition LIST_SET_STAR_def:
   LIST_SET_STAR ls = \l'. ?n. l' IN LIST_NUM_SET_STAR n ls
End


Theorem LIST_NUM_SET_STAR___SING:
  !l n. LIST_NUM_SET_STAR n {l} = {LIST_NUM_STAR n l}
Proof

Induct_on `n` THENL [
   SIMP_TAC std_ss [LIST_NUM_SET_STAR_def, LIST_NUM_STAR_def],

   ASM_SIMP_TAC std_ss [LIST_NUM_SET_STAR_def, LIST_NUM_STAR_def, IN_SING,
      EXTENSION, GSPECIFICATION, pairTheory.EXISTS_PROD]
]
QED


Theorem LIST_SET_STAR___SING:
  !l. LIST_SET_STAR {l} = LIST_STAR l
Proof

SIMP_TAC std_ss [FUN_EQ_THM, LIST_SET_STAR_def, LIST_STAR_def,
   LIST_NUM_SET_STAR___SING, IN_SING]
QED


Theorem LIST_SET_NUM_STAR___EMPTY:
  !n. LIST_NUM_SET_STAR (SUC n) {} = {}
Proof

SIMP_TAC std_ss [LIST_NUM_SET_STAR_def, NOT_IN_EMPTY,
   EXTENSION, GSPECIFICATION, PAIR_BETA_THM, GSYM pairTheory.PFORALL_THM,
   GSYM pairTheory.PEXISTS_THM]
QED


Theorem IN_LIST_NUM_SET_STAR:
        (x IN LIST_NUM_SET_STAR 0 ls = (x = [])) /\
   ((x IN LIST_NUM_SET_STAR (SUC n) ls) =
      ?l t. (x = l ++ t) /\ l IN ls /\ (t IN (LIST_NUM_SET_STAR n ls)))
Proof

SIMP_TAC std_ss [LIST_NUM_SET_STAR_def, IN_SING, GSPECIFICATION,
   pairTheory.EXISTS_PROD]
QED



Theorem LIST_SET_STAR___EMPTY:
  LIST_SET_STAR {} = {[]}
Proof

SIMP_TAC std_ss [LIST_SET_STAR_def, EXTENSION, IN_ABS, IN_SING] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
   Cases_on `n` THENL [
      FULL_SIMP_TAC std_ss [LIST_NUM_SET_STAR_def, IN_SING],
      FULL_SIMP_TAC std_ss [LIST_SET_NUM_STAR___EMPTY, NOT_IN_EMPTY]
   ],

   Q.EXISTS_TAC `0` THEN
   ASM_SIMP_TAC std_ss [LIST_NUM_SET_STAR_def, IN_SING]
]
QED



Theorem LIST_SET_STAR___EMPTY_LIST:
  !l. [] IN (LIST_SET_STAR l)
Proof
SIMP_TAC std_ss [LIST_SET_STAR_def, IN_ABS] THEN
GEN_TAC THEN
Q.EXISTS_TAC `0` THEN
SIMP_TAC std_ss [LIST_NUM_SET_STAR_def, IN_SING]
QED


Theorem LIST_NUM_SET_STAR___SUBSET:
     !L1 L2 n. (L1 SUBSET L2) ==> (LIST_NUM_SET_STAR n L1 SUBSET LIST_NUM_SET_STAR n L2)
Proof

Induct_on `n` THENL [
   SIMP_TAC std_ss [LIST_NUM_SET_STAR_def, SUBSET_REFL],

   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   SIMP_TAC std_ss [SUBSET_DEF, GSPECIFICATION, pairTheory.EXISTS_PROD,
      LIST_NUM_SET_STAR_def] THEN
   METIS_TAC[SUBSET_DEF]
]
QED



Theorem LIST_SET_STAR___SUBSET:
     !L1 L2. (L1 SUBSET L2) ==> (LIST_SET_STAR L1 SUBSET LIST_SET_STAR L2)
Proof

SIMP_TAC std_ss [LIST_SET_STAR_def, SUBSET_DEF, IN_ABS] THEN
METIS_TAC[LIST_NUM_SET_STAR___SUBSET, SUBSET_DEF]
QED




Theorem LIST_NUM_STAR_APPEND:
     (!n1 n2 l. (LIST_NUM_STAR n1 l) ++ (LIST_NUM_STAR n2 l) = LIST_NUM_STAR (n1 + n2) l)
Proof

   Induct_on `n1` THENL [
      SIMP_TAC list_ss [LIST_NUM_STAR_def],
      ASM_SIMP_TAC std_ss [LIST_NUM_STAR_def, ADD_CLAUSES, GSYM APPEND_ASSOC]
   ]
QED


(******************************************************************
  PRED SET
 ******************************************************************)


Theorem IMAGE_ABS2:
  IMAGE f P = (\x. ?y. (x = f y) /\ y IN P)
Proof
SIMP_TAC std_ss [EXTENSION, IN_IMAGE, IN_ABS]
QED

Theorem IN_ABS2:
          (!t. (t IN X = Q t)) = (X = \t. Q t)
Proof
SIMP_TAC std_ss [EXTENSION, IN_ABS]
QED


Theorem IN_ABS3:
          (\t. (t IN X)) = X
Proof
SIMP_TAC std_ss [EXTENSION, IN_ABS]
QED


Theorem IN_ABS_SING:
          (\t. (t = X)) = {X}
Proof
SIMP_TAC std_ss [EXTENSION, IN_ABS, IN_SING]
QED


Theorem INTER_ABS:
  $INTER = \a b x. x IN a /\ x IN b
Proof

ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
SIMP_TAC std_ss [EXTENSION, IN_INTER] THEN
SIMP_TAC std_ss [IN_DEF]
QED


Theorem IMAGE_ABS:
  IMAGE f X = \x. (?e. (x = f e) /\ e IN X)
Proof

SIMP_TAC std_ss [EXTENSION, IN_IMAGE] THEN
SIMP_TAC std_ss [IN_DEF]
QED


Theorem BIGINTER_ABS:
  BIGINTER P = \x. !s. s IN P ==> x IN s
Proof

SIMP_TAC std_ss [EXTENSION, IN_BIGINTER] THEN
SIMP_TAC std_ss [IN_DEF]
QED



Theorem SUBSET_SING:
  !s x. s SUBSET {x} = ((s = {x}) \/ (s = EMPTY))
Proof

REPEAT STRIP_TAC THEN
SIMP_TAC std_ss [EXTENSION, IN_SING, NOT_IN_EMPTY, SUBSET_DEF] THEN
PROVE_TAC[]
QED


Theorem INSERT_DELETE_2:
  v INSERT (s DELETE v) = v INSERT s
Proof
SIMP_TAC std_ss [EXTENSION, IN_INSERT, IN_DELETE] THEN PROVE_TAC[]
QED



(******************************************************************
  COND_REWRITES
 ******************************************************************)

Theorem COND_NONE_SOME_REWRITES:
  (((if C then NONE else (SOME X)) = (SOME Y)) = (~C /\ (X = Y))) /\
   (((if C then (SOME X) else NONE) = (SOME Y)) = (C /\ (X = Y))) /\
   (((if C then NONE else (SOME X)) = NONE) = C) /\
   (((if C then (SOME X) else NONE) = NONE) = ~C) /\
   ((if C1 then NONE else (if C2 then NONE else Z)) =
    (if C1 \/ C2 then NONE else Z)) /\
   ((if C1 then NONE else (if C2 then Z else NONE)) =
    (if C1 \/ ~C2 then NONE else Z)) /\
   ((if C1 then (if C2 then NONE else Z) else NONE) =
    (if ~C1 \/ C2 then NONE else Z)) /\
   ((if C1 then (if C2 then Z else NONE) else NONE) =
    (if C1 /\ C2 then Z else NONE)) /\
    (IS_SOME (if C then NONE else (SOME X)) = ~C) /\
    (IS_SOME (if C then (SOME X) else NONE) = C) /\
    (IS_NONE (if C then NONE else (SOME X)) = C) /\
    (IS_NONE (if C then (SOME X) else NONE) = ~C) /\
   ((if C then SOME X else SOME Y) =
    SOME (if C then X else Y))
Proof

Cases_on `C` THEN Cases_on `C1` THEN Cases_on `C2` THEN
SIMP_TAC std_ss []
QED



Theorem COND_NONE_SOME_REWRITES2:

  (((if C then NONE else X) = (SOME Y)) = (~C /\ (X = SOME Y))) /\
   (((if C then X else NONE) = (SOME Y)) = (C /\ (X = SOME Y))) /\
   (((if C then NONE else X) = NONE) = C \/ (X = NONE)) /\
   (((if C then X else NONE) = NONE) = ~C \/ (X = NONE))
Proof

Cases_on `C` THEN Cases_on `X` THEN
SIMP_TAC std_ss []
QED

Theorem COND_NONE_SOME_REWRITES3:

  (((if C then (SOME Y) else X) = NONE) = (~C /\ (X = NONE))) /\
   (((if C then X else (SOME Y)) = NONE) = (C /\ (X = NONE)))
Proof

Cases_on `C` THEN Cases_on `X` THEN
SIMP_TAC std_ss []
QED



Theorem COND_REWRITES:

   (FST (if C then X else Y) =
    if C then FST X else FST Y) /\

   (SND (if C then X else Y) =
    if C then SND X else SND Y) /\

   ((IS_SOME (if C then X' else Y')) =
     if C then (IS_SOME X') else (IS_SOME Y')) /\

   ((IS_NONE (if C then X' else Y')) =
     if C then (IS_NONE X') else (IS_NONE Y')) /\

   (((if C then v1 else v2) = v1) =
    (~C ==> (v2 = v1))) /\

   (((if C then v2 else v1) = v1) =
    (C ==> (v2 = v1)))
Proof

Cases_on `C` THEN
SIMP_TAC std_ss []
QED



Theorem COND_EQ_REWRITE:

   ((if C then X else Y) = (if C then X' else Y')) =
   ((C ==> (X = X')) /\ (~C ==> (Y = Y')))
Proof

Cases_on `C` THEN
SIMP_TAC std_ss []
QED



Theorem COND_NONE_SOME_REWRITES_EQ:

   (((if C1 then NONE else (SOME X)) =
    (if C2 then (SOME Y) else NONE)) = ((~C1 = C2) /\ (C2 ==> (X = Y)))) /\

   (((if C1 then (SOME X) else NONE) =
    (if C2 then (SOME Y) else NONE)) = ((C1 = C2) /\ (C2 ==> (X = Y)))) /\


   (((if C1 then NONE else (SOME X)) =
    (if C2 then NONE else (SOME Y))) = ((C1 = C2) /\ (~C2 ==> (X = Y)))) /\

   (((if C1 then (SOME X) else NONE) =
    (if C2 then NONE else (SOME Y))) = ((C1 = ~C2) /\ (~C2 ==> (X = Y))))
Proof

Cases_on `C1` THEN Cases_on `C2` THEN
SIMP_TAC std_ss []
QED











(******************************************************************
  OPTIONS
 ******************************************************************)


Theorem SOME_THE_EQ:
  (X = SOME (THE X)) = (IS_SOME X)
Proof Cases_on `X` THEN SIMP_TAC std_ss []
QED


Theorem IS_SOME_EXISTS:
  IS_SOME x = ?y. x = SOME y
Proof
Cases_on `x` THEN SIMP_TAC std_ss []
QED


Theorem NOT_NONE_IS_SOME:
  (~(x = NONE) = (IS_SOME x)) /\
   (~(NONE = x) = (IS_SOME x))
Proof
Cases_on `x` THEN SIMP_TAC std_ss []
QED


Theorem NONE_IS_NOT_SOME:
  ((x = NONE) = ~(IS_SOME x)) /\
   ((NONE = x) = ~(IS_SOME x))
Proof
Cases_on `x` THEN SIMP_TAC std_ss []
QED



Theorem EQ_SOME_THM:
  ((SOME x = Y) = ((x = THE Y) /\ (IS_SOME Y))) /\
   ((Y = SOME x) = ((x = THE Y) /\ (IS_SOME Y)))
Proof
Cases_on `Y` THEN SIMP_TAC std_ss [] THEN
METIS_TAC[]
QED


Theorem IN_THE_COND_REWRITE:
  x IN THE (if c then X else Y) =
               (c ==> x IN THE X) /\ (~c ==> x IN THE Y)
Proof
Cases_on `c` THEN SIMP_TAC std_ss []
QED





(******************************************************************
  FINITE_MAPS
 ******************************************************************)

Theorem FUPDATE_LIST_APPEND:
    !f L1 L2. (f |++ (L1 ++ L2) = f |++ L1 |++ L2)
Proof
Induct_on `L1` THEN
ASM_SIMP_TAC list_ss [FUPDATE_LIST_THM]
QED


Theorem FUPDATE_LIST_SUBSUME:
  !f L1 L2. LIST_TO_SET (MAP FST L1) SUBSET LIST_TO_SET (MAP FST L2) ==>
   (f |++ L1 |++ L2 = f |++ L2)
Proof
GEN_TAC THEN
SIMP_TAC std_ss [GSYM fmap_EQ_THM, FDOM_FUPDATE_LIST] THEN
REPEAT STRIP_TAC THEN1 (
   FULL_SIMP_TAC std_ss [EXTENSION, SUBSET_DEF, IN_UNION] THEN
   METIS_TAC[]
) THEN
Tactical.REVERSE (Cases_on `MEM x (MAP FST L2)`) THEN1 (
   `~(MEM x (MAP FST L1))` by (
       FULL_SIMP_TAC std_ss [SUBSET_DEF] THEN
       PROVE_TAC[]
   ) THEN
   ASM_SIMP_TAC std_ss [FUPDATE_LIST_APPLY_NOT_MEM]
) THEN
REPEAT (POP_ASSUM MP_TAC) THEN
Tactical.REVERSE (
sg `!L1 L2 x. MEM x (MAP FST L2) ==>
   ((f |++ L1 |++ (REVERSE L2)) ' x =  (f |++ (REVERSE L2)) ' x)`) THEN1 (
  REPEAT STRIP_TAC THEN
  Q.PAT_X_ASSUM `!L1 L2. X` (MP_TAC o Q.SPECL [`L1`, `REVERSE L2`, `x`]) THEN
  ASM_SIMP_TAC std_ss [MAP_REVERSE, MEM_REVERSE, REVERSE_REVERSE]
) THEN

Induct_on `L2` THEN SIMP_TAC list_ss [] THEN
REPEAT GEN_TAC THEN Cases_on `h` THEN
SIMP_TAC list_ss [FUPDATE_LIST_APPEND, FUPDATE_LIST_THM,
   FAPPLY_FUPDATE_THM] THEN
Cases_on `x = q` THEN ASM_SIMP_TAC std_ss []
QED



Theorem FUPDATE_LIST_IDEMPOT:
  !f L. (f |++ L |++ L = f |++ L)
Proof
PROVE_TAC[SUBSET_REFL, FUPDATE_LIST_SUBSUME]
QED


Definition LIST_TO_FMAP_def:
   LIST_TO_FMAP L = FEMPTY |++ (REVERSE L)
End


Theorem LIST_TO_FMAP_THM:
   (LIST_TO_FMAP [] = FEMPTY) /\
   ((LIST_TO_FMAP (h::L)) = (LIST_TO_FMAP L) |+ h)
Proof
SIMP_TAC list_ss [LIST_TO_FMAP_def, FUPDATE_LIST_THM,
   FUPDATE_LIST_APPEND]
QED


Theorem FDOM_LIST_TO_FMAP:
  !L. (FDOM (LIST_TO_FMAP L) = LIST_TO_SET (MAP FST L))
Proof
SIMP_TAC std_ss [LIST_TO_FMAP_def, FDOM_FUPDATE_LIST, FDOM_FEMPTY,
   UNION_EMPTY, MAP_REVERSE, LIST_TO_SET_REVERSE]
QED


Theorem FEVERY_FUPDATE_LIST:
  !f P L. FEVERY P f /\ EVERY P L ==> FEVERY P (f |++ L)
Proof
Induct_on `L` THEN (
   SIMP_TAC std_ss [FUPDATE_LIST_THM]
) THEN
REPEAT STRIP_TAC THEN
Q.PAT_X_ASSUM `!f P. X f P` MATCH_MP_TAC THEN
Cases_on `h` THEN
FULL_SIMP_TAC std_ss [listTheory.EVERY_DEF, FEVERY_STRENGTHEN_THM]
QED


Theorem FEVERY_LIST_TO_FMAP:
  !P L. EVERY P L ==> FEVERY P (LIST_TO_FMAP L)
Proof
REWRITE_TAC [LIST_TO_FMAP_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC FEVERY_FUPDATE_LIST THEN
ASM_REWRITE_TAC [FEVERY_FEMPTY, ALL_EL_REVERSE]
QED


Theorem o_f_FUPDATE_WEAK:
  ((f o_f fm) |+ (k,f v)) = (f o_f (fm |+ (k,v)))
Proof
SIMP_TAC std_ss [GSYM fmap_EQ_THM] THEN
SIMP_TAC std_ss [o_f_DEF, FDOM_FUPDATE, IN_INSERT] THEN
GEN_TAC THEN Cases_on `x = k` THEN (
   ASM_SIMP_TAC std_ss [FAPPLY_FUPDATE_THM, o_f_FAPPLY]
)
QED

Theorem o_f_FUPDATE_LIST:
  !f fm L. f o_f (fm |++ L) =
        (f o_f fm) |++ (MAP (\x. (FST x, f (SND x))) L)
Proof

GEN_TAC THEN Induct_on `L` THEN1 (
   SIMP_TAC list_ss [FUPDATE_LIST_THM]
) THEN
Cases_on `h` THEN
ASM_SIMP_TAC list_ss [FUPDATE_LIST_THM, o_f_FUPDATE_WEAK]
QED


Theorem o_f_LIST_TO_FMAP:
  !f L. f o_f (LIST_TO_FMAP L) =
        LIST_TO_FMAP (MAP (\x. (FST x, f (SND x))) L)
Proof
SIMP_TAC std_ss [LIST_TO_FMAP_def, o_f_FUPDATE_LIST, o_f_FEMPTY,
   MAP_REVERSE]
QED


Theorem FUPDATE_LIST_APPLY_MEM:
  !kvl f v k. (FILTER (\x. FST x = k) kvl = [(k,v)]) ==>
              ((f |++ kvl) ' k = v)
Proof
Induct_on `kvl` THEN1 (
   SIMP_TAC list_ss []
) THEN
Cases_on `h` THEN
SIMP_TAC list_ss [FUPDATE_LIST_THM] THEN
REPEAT STRIP_TAC THEN
Cases_on `q = k` THENL [
   ALL_TAC,
   FULL_SIMP_TAC std_ss []
] THEN
FULL_SIMP_TAC list_ss [FILTER_EQ_NIL] THEN
`~(MEM k (MAP FST kvl))` by (
      Q.PAT_X_ASSUM `EVERY X Y` MP_TAC THEN
      REPEAT (POP_ASSUM (K ALL_TAC)) THEN
      Induct_on `kvl` THEN
      ASM_SIMP_TAC list_ss []
) THEN
ASM_SIMP_TAC std_ss [FUPDATE_LIST_APPLY_NOT_MEM, FAPPLY_FUPDATE_THM]
QED




Theorem FUPDATE_LIST_APPLY___ALL_DISTINCT:
  !f x y L. (ALL_DISTINCT (MAP FST L) /\ MEM (x,y) L) ==>
((f |++ L) ' x = y)
Proof

REPEAT STRIP_TAC THEN
MATCH_MP_TAC FUPDATE_LIST_APPLY_MEM THEN
Induct_on `L` THEN
FULL_SIMP_TAC list_ss [AND_IMP_INTRO] THEN
GEN_TAC THEN
Cases_on `h = (x,y)` THEN1 (
   ASM_SIMP_TAC list_ss [FILTER_EQ_NIL, EVERY_MEM,
      MEM_MAP] THEN
   PROVE_TAC[]
) THEN
ASM_SIMP_TAC list_ss [COND_RAND, COND_RATOR] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [MEM_MAP] THEN
METIS_TAC[pairTheory.FST]
QED



Theorem LIST_TO_FMAP___ALL_DISTINCT:
  !x y L. (ALL_DISTINCT (MAP FST L) /\ MEM (x,y) L) ==>
((LIST_TO_FMAP L) ' x = y)
Proof

SIMP_TAC std_ss [LIST_TO_FMAP_def] THEN
REPEAT STRIP_TAC THEN
MATCH_MP_TAC FUPDATE_LIST_APPLY___ALL_DISTINCT THEN
ASM_SIMP_TAC std_ss [MAP_REVERSE, MEM_REVERSE,
   ALL_DISTINCT_REVERSE]
QED


Theorem FEVERY_LIST_TO_FMAP_EQ:
  !P L. ALL_DISTINCT (MAP FST L) ==> (FEVERY P (LIST_TO_FMAP L) = EVERY P L)
Proof
REPEAT STRIP_TAC THEN EQ_TAC THEN
SIMP_TAC std_ss [FEVERY_LIST_TO_FMAP] THEN
ASM_SIMP_TAC std_ss [FEVERY_DEF,
   FDOM_LIST_TO_FMAP, MEM_MAP,
   GSYM RIGHT_EXISTS_AND_THM, GSYM LEFT_EXISTS_AND_THM,
   GSYM LEFT_FORALL_IMP_THM, EVERY_MEM] THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN
Cases_on `e` THEN FULL_SIMP_TAC std_ss [] THEN
`LIST_TO_FMAP L ' q = r` suffices_by (STRIP_TAC THEN
   FULL_SIMP_TAC std_ss []
) THEN
MATCH_MP_TAC LIST_TO_FMAP___ALL_DISTINCT THEN
ASM_REWRITE_TAC[]
QED


Theorem FMERGE_DRESTRICT_COMPL:
  !f b s. (FMERGE f (DRESTRICT b (COMPL s)) (DRESTRICT b s) = b) /\
          (FMERGE f (DRESTRICT b s) (DRESTRICT b (COMPL s)) = b)
Proof

SIMP_TAC (std_ss++CONJ_ss) [FMERGE_DEF, GSYM fmap_EQ_THM] THEN
SIMP_TAC std_ss [EXTENSION, DRESTRICT_DEF, IN_INTER, IN_COMPL, IN_UNION] THEN
PROVE_TAC[]
QED




