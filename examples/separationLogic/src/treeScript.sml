Theory tree
Ancestors
  relation pred_set combin arithmetic list
Libs
  boolSimps ConseqConv

val _ = ParseExtras.temp_loose_equality()

Datatype: tree =
    leaf
  | node 'a (tree list)
End


val tree_11 = DB.fetch "-" "tree_11";
val tree_distinct = DB.fetch "-" "tree_distinct";
val tree_size_def = DB.fetch "-" "tree_size_def";


Definition IS_LEAF_def:   (IS_LEAF leaf = T) /\
                          (IS_LEAF (node _ _) = F)
End

Theorem IS_LEAF_REWRITE:
  IS_LEAF t = (t = leaf)
Proof
Cases_on `t` THEN SIMP_TAC std_ss [IS_LEAF_def, tree_distinct]
QED


Definition IS_NODE_def:   (IS_NODE leaf = F) /\
                          (IS_NODE (node _ _) = T)
End

Theorem IS_NODE_REWRITE:
  IS_NODE t = ?d tL. (t = node d tL)
Proof
Cases_on `t` THEN SIMP_TAC std_ss [IS_NODE_def, tree_distinct, tree_11]
QED

Definition IS_PROPER_NODE_def:   (IS_PROPER_NODE leaf = F) /\
                                 (IS_PROPER_NODE (node v tL) = ~(NULL tL))
End

Theorem IS_PROPER_NODE_REWRITE:
  IS_PROPER_NODE t = ?d tL. (t = node d tL) /\ ~(NULL tL)
Proof
Cases_on `t` THEN SIMP_TAC std_ss [IS_PROPER_NODE_def, tree_distinct,
   tree_11]
QED

Definition DIRECT_SUBTREES_def:
(DIRECT_SUBTREES leaf = EMPTY) /\
(DIRECT_SUBTREES (node v tL) = set tL)
End

Theorem DIRECT_SUBTREES_REWRITE:
  (!t:'a tree. ~(DIRECT_SUBTREES leaf t)) /\
  (!t:'a tree v tL. (DIRECT_SUBTREES (node v tL) t = MEM t tL))
Proof
SIMP_TAC std_ss [DIRECT_SUBTREES_def, EMPTY_DEF, IN_DEF]
QED

Theorem DIRECT_SUBTREES_EXISTS:
  !t1 t2. t1 IN DIRECT_SUBTREES t2 =
          (?v tL. (t2 = node v tL) /\ MEM t1 tL)
Proof

Cases_on `t2` THEN
SIMP_TAC std_ss [DIRECT_SUBTREES_def, NOT_IN_EMPTY, tree_distinct, tree_11]
QED


val DIRECT_SUBTREES_EXISTS2 = save_thm ("DIRECT_SUBTREES_EXISTS2",
SIMP_RULE std_ss [IN_DEF, SimpLHS] DIRECT_SUBTREES_EXISTS);


Definition PSUBTREES_def:   PSUBTREES = TC DIRECT_SUBTREES
End
Definition SUBTREES_def:   SUBTREES = RTC DIRECT_SUBTREES
End


Theorem PSUBTREES_THM:
  (PSUBTREES (leaf:'a tree) = EMPTY) /\
  (!v:'a tL. PSUBTREES (node v tL) =
             (set tL) UNION BIGUNION (set (MAP PSUBTREES tL)))
Proof

SIMP_TAC std_ss [PSUBTREES_def, EXTENSION, NOT_IN_EMPTY] THEN
SIMP_TAC list_ss [IN_BIGUNION, IN_INSERT,
                 LEFT_AND_OVER_OR, EXISTS_OR_THM, MEM_MAP,
                 GSYM RIGHT_EXISTS_AND_THM, IN_UNION] THEN
REPEAT CONJ_TAC THEN1 (
  SIMP_TAC std_ss [IN_DEF, TC_eq_NRC, NRC, DIRECT_SUBTREES_def,
                   EMPTY_DEF]
) THEN
SIMP_TAC list_ss [EQ_IMP_THM, FORALL_AND_THM, DISJ_IMP_THM,
                 GSYM LEFT_FORALL_IMP_THM, IN_DEF] THEN
REPEAT CONJ_TAC THENL [
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC TC_CASES1 THEN
   FULL_SIMP_TAC std_ss [DIRECT_SUBTREES_REWRITE, IN_DEF] THEN
   PROVE_TAC[],

   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC (el 1 (BODY_CONJUNCTS TC_RULES)) THEN
   ASM_SIMP_TAC std_ss [DIRECT_SUBTREES_REWRITE, IN_DEF],

   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC (el 2 (BODY_CONJUNCTS TC_RULES)) THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC (el 1 (BODY_CONJUNCTS TC_RULES)) THEN
   ASM_SIMP_TAC std_ss [DIRECT_SUBTREES_REWRITE, IN_DEF]
]
QED


Theorem PSUBTREES_REWRITE:
  (!t:'a tree. ~(PSUBTREES leaf t)) /\
  (!t:'a tree v tL. (PSUBTREES (node v tL) t =
                     (MEM t tL \/ ?t'. MEM t' tL /\ PSUBTREES t' t)))
Proof

SIMP_TAC std_ss [PSUBTREES_THM, EMPTY_DEF,
                 (CONV_RULE (STRIP_QUANT_CONV (LHS_CONV (SIMP_CONV std_ss [IN_DEF]))) IN_UNION)] THEN
SIMP_TAC list_ss [MEM_MAP, LEFT_AND_OVER_OR, EXISTS_OR_THM,
                  GSYM RIGHT_EXISTS_AND_THM, IN_BIGUNION] THEN
SIMP_TAC std_ss [IN_DEF] THEN PROVE_TAC[]
QED


Theorem SUBTREES_THM:
  !t. SUBTREES t = t INSERT PSUBTREES t
Proof
SIMP_TAC std_ss [SUBTREES_def, PSUBTREES_def] THEN
REWRITE_TAC [GSYM (el 1 (BODY_CONJUNCTS TC_RC_EQNS))] THEN
SIMP_TAC std_ss [EXTENSION, IN_INSERT] THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [IN_DEF, RC_DEF]
QED


Theorem SUBTREES_REWRITE:
  !t1 t2. SUBTREES t1 t2 = (t1 = t2) \/ (PSUBTREES t1 t2)
Proof
REWRITE_TAC[SIMP_RULE std_ss [IN_DEF] IN_INSERT, SUBTREES_THM] THEN
PROVE_TAC[]
QED



Definition tree_size0_def:   tree_size0 = tree_size (K 0)
End

Theorem DIRECT_SUBTREES_size:
  !t1 t2. t1 IN DIRECT_SUBTREES t2 ==> (tree_size0 t1 < tree_size0 t2)
Proof
Cases_on `t2` THEN
SIMP_TAC std_ss [DIRECT_SUBTREES_def, NOT_IN_EMPTY,
                 tree_size0_def, tree_size_def] THEN
Induct_on `l` THEN (
   ASM_SIMP_TAC list_ss [DISJ_IMP_THM, tree_size_def]
) THEN
REPEAT STRIP_TAC THEN
RES_TAC THEN
DECIDE_TAC
QED

Theorem PSUBTREES_size:
  !t2 t1. t1 IN PSUBTREES t2 ==> (tree_size0 t1 < tree_size0 t2)
Proof
SIMP_TAC std_ss [PSUBTREES_def, IN_DEF] THEN
HO_MATCH_MP_TAC (ISPECL [``tree_size0``] (GEN_ALL TC_lifts_transitive_relations)) THEN
SIMP_TAC arith_ss [DIRECT_SUBTREES_size, IN_DEF, transitive_def]
QED


Theorem SUBTREES_size:
  !t2 t1. t1 IN SUBTREES t2 ==> (tree_size0 t1 <= tree_size0 t2)
Proof
SIMP_TAC arith_ss [SUBTREES_THM, IN_INSERT,
                   DISJ_IMP_THM, PSUBTREES_size,
                   LESS_IMP_LESS_OR_EQ]
QED



Theorem WF_DIRECT_SUBTREES:
    WF (inv DIRECT_SUBTREES)
Proof

MATCH_MP_TAC WF_SUBSET THEN
Q.EXISTS_TAC `measure tree_size0` THEN
REWRITE_TAC[prim_recTheory.WF_measure] THEN
SIMP_TAC std_ss [prim_recTheory.measure_thm,
                 SIMP_RULE std_ss [IN_DEF] DIRECT_SUBTREES_size,
                 inv_DEF]
QED

Theorem WF_PSUBTREES:
    WF (inv PSUBTREES)
Proof

MATCH_MP_TAC WF_SUBSET THEN
Q.EXISTS_TAC `measure tree_size0` THEN
REWRITE_TAC[prim_recTheory.WF_measure] THEN
SIMP_TAC std_ss [prim_recTheory.measure_thm,
                 SIMP_RULE std_ss [IN_DEF] PSUBTREES_size,
                 inv_DEF]
QED


Theorem tree_STRONG_INDUCT:
  !P. (!t. (!t'. t' IN PSUBTREES t ==> P t') ==> P t) ==>
      (!t. P t)
Proof
REPEAT STRIP_TAC THEN
completeInduct_on `tree_size0 t` THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
PROVE_TAC [PSUBTREES_size]
QED

Theorem tree_INDUCT:
  !P. ((P leaf) /\
       (!n tL. EVERY P tL ==> P (node n tL))) ==>
      (!t. P t)
Proof

GEN_TAC THEN STRIP_TAC THEN
MATCH_MP_TAC tree_STRONG_INDUCT THEN
REPEAT STRIP_TAC THEN
Cases_on `t` THEN ASM_REWRITE_TAC[] THEN
Q.PAT_ASSUM `!n tL. EVERY P tL ==> X` MATCH_MP_TAC THEN
FULL_SIMP_TAC list_ss [PSUBTREES_THM, IN_UNION, EVERY_MEM]
QED


Definition DEPTH_def:
 (DEPTH leaf 0 = T) /\
 (DEPTH leaf (SUC n) = F) /\
 (DEPTH (node _ x) 0 = (x = [])) /\
 (DEPTH (node _ x) (SUC n) = EXISTS (\t. DEPTH t n) x)
End


Theorem DEPTH_THM:
  (DEPTH (leaf:'a tree) = {0}) /\
  (DEPTH (node (v:'a) []) = {0}) /\
  (DEPTH (node (v:'a) tL) = if NULL tL then {0} else
      IMAGE SUC (BIGUNION (LIST_TO_SET (MAP DEPTH tL))))
Proof

`!n t. n IN DEPTH t = DEPTH t n` by SIMP_TAC std_ss [IN_DEF] THEN
ASM_SIMP_TAC std_ss [EXTENSION, IN_IMAGE, IN_SING] THEN
REPEAT STRIP_TAC THEN (
   Cases_on `x` THEN
   SIMP_TAC list_ss [DEPTH_def, COND_RAND, COND_RATOR, IN_SING, IN_IMAGE, NULL_EQ,
                     IN_BIGUNION, MEM_MAP, GSYM RIGHT_EXISTS_AND_THM, EXISTS_MEM]
) THEN
CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV) THEN
SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [] THEN
Cases_on `tL` THEN ASM_SIMP_TAC list_ss []
QED

Theorem FINITE_DEPTH:
  !t. FINITE (DEPTH t)
Proof
HO_MATCH_MP_TAC tree_INDUCT THEN
SIMP_TAC std_ss [DEPTH_THM, FINITE_SING] THEN
Induct_on `tL` THEN (
   SIMP_TAC list_ss [DEPTH_THM, FINITE_SING]
) THEN
REPEAT STRIP_TAC THEN
CONSEQ_REWRITE_TAC ([], [IMAGE_FINITE], []) THEN
ASM_SIMP_TAC std_ss [FINITE_BIGUNION_EQ, FINITE_INSERT,
                     FINITE_LIST_TO_SET, IN_INSERT,
                     DISJ_IMP_THM, FORALL_AND_THM, MEM_MAP,
                     GSYM LEFT_FORALL_IMP_THM] THEN
FULL_SIMP_TAC std_ss [EVERY_MEM]
QED


Theorem NOT_DEPTH_EMPTY:
  !t. ~(DEPTH t = EMPTY)
Proof
HO_MATCH_MP_TAC tree_INDUCT THEN
SIMP_TAC std_ss [DEPTH_THM, NOT_INSERT_EMPTY] THEN
Induct_on `tL` THEN (
   SIMP_TAC list_ss [DEPTH_THM, NOT_INSERT_EMPTY]
) THEN
SIMP_TAC std_ss [IMAGE_EQ_EMPTY, BIGUNION_INSERT,
                 EMPTY_UNION]
QED


Definition MIN_LIST_def:   (MIN_LIST [] = 0) /\
                           (MIN_LIST (t::l) = FOLDR MIN t l)
End
Definition MAX_LIST_def:   MAX_LIST l = FOLDR MAX 0 l
End

Theorem MIN_MAX_LIST_THM:
  (MIN_LIST [] = 0) /\ (MAX_LIST [] = 0) /\
  (!n. (MIN_LIST [n] = n) /\ (MAX_LIST [n] = n)) /\
  (!n ns. (MIN_LIST (n::ns) = if (ns = []) then n else MIN n (MIN_LIST ns))) /\
  (!n ns. (MAX_LIST (n::ns) = MAX n (MAX_LIST ns)))
Proof

SIMP_TAC list_ss [MIN_LIST_def, MAX_LIST_def] THEN
Induct_on `ns` THEN
ASM_SIMP_TAC list_ss [MIN_LIST_def, COND_RAND, COND_RATOR] THEN
PROVE_TAC[MIN_ASSOC, MIN_COMM]
QED


Theorem MAX_MAX_LIST:
  !n ns. MEM n ns ==> (n <= MAX_LIST ns)
Proof
Induct_on `ns` THEN
ASM_SIMP_TAC list_ss [MIN_MAX_LIST_THM, DISJ_IMP_THM]
QED

Theorem MIN_MIN_LIST:
  !n ns. MEM n ns ==> (MIN_LIST ns <= n)
Proof
Induct_on `ns` THEN
ASM_SIMP_TAC list_ss [MIN_MAX_LIST_THM, DISJ_IMP_THM,
                      COND_RAND, COND_RATOR]
QED


Theorem MIN_MAX_SUC:
  (MIN (SUC n1) (SUC n2) = SUC (MIN n1 n2)) /\
  (MAX (SUC n1) (SUC n2) = SUC (MAX n1 n2))
Proof
SIMP_TAC std_ss [MIN_DEF, MAX_DEF, COND_RAND, COND_RATOR]
QED

Theorem MIN_MAX_SET_SUC:
  (!s. (FINITE s /\ ~(s = EMPTY)) ==> (MAX_SET (IMAGE SUC s) = SUC (MAX_SET s))) /\
  (!s. (FINITE s /\ ~(s = EMPTY)) ==> (MIN_SET (IMAGE SUC s) = SUC (MIN_SET s)))
Proof
CONJ_TAC THEN (
   SIMP_TAC std_ss [GSYM AND_IMP_INTRO] THEN
   HO_MATCH_MP_TAC FINITE_INDUCT THEN
   SIMP_TAC (srw_ss()) [MAX_SET_THM, MIN_SET_THM, IMAGE_FINITE] THEN
   Cases THEN SIMP_TAC (srw_ss()) [MIN_MAX_SUC, MIN_SET_THM])
QED

Definition MAX_DEPTH_def:   MAX_DEPTH t = MAX_SET (DEPTH t)
End
Definition MIN_DEPTH_def:   MIN_DEPTH t = MIN_SET (DEPTH t)
End

Theorem MIN_MAX_DEPTH_THM:
  (MAX_DEPTH (leaf:'a tree) = 0) /\ (MIN_DEPTH (leaf:'a tree) = 0) /\
  (!v:'a. (MAX_DEPTH (node v []) = 0)) /\
  (!v:'a. (MIN_DEPTH (node v []) = 0)) /\
  (!v:'a tL. NULL tL ==> (MAX_DEPTH (node v tL) = 0)) /\
  (!v:'a tL. NULL tL ==> (MIN_DEPTH (node v tL) = 0)) /\
  (!v:'a tL. ~(NULL tL) ==> (MAX_DEPTH (node v tL) = SUC(MAX_LIST (MAP MAX_DEPTH tL)))) /\
  (!v:'a tL. ~(NULL tL) ==> (MIN_DEPTH (node v tL) = SUC(MIN_LIST (MAP MIN_DEPTH tL))))
Proof

SIMP_TAC (srw_ss()) [MAX_DEPTH_def, MIN_DEPTH_def,
                  DEPTH_THM, MIN_SET_THM, MAX_SET_THM, NULL_EQ] THEN

`!tL:'a tree list. ~(tL = []) ==> ((FINITE (BIGUNION (set (MAP DEPTH tL)))) /\
 ~((BIGUNION (set (MAP DEPTH tL))) = EMPTY))` by (
   Cases_on `tL` THEN
   SIMP_TAC list_ss [BIGUNION_INSERT, EMPTY_UNION, NOT_DEPTH_EMPTY,
                    FINITE_UNION, FINITE_DEPTH, FINITE_BIGUNION_EQ,
                    FINITE_LIST_TO_SET, MEM_MAP,
                    GSYM LEFT_FORALL_IMP_THM, IN_INSERT, FINITE_INSERT,
                    DISJ_IMP_THM]) THEN
ASM_SIMP_TAC std_ss [MIN_MAX_SET_SUC, GSYM FORALL_AND_THM] THEN
POP_ASSUM (K ALL_TAC) THEN
Induct_on `tL` THEN SIMP_TAC list_ss [] THEN
Cases_on `tL = []` THEN1 (
   ASM_SIMP_TAC list_ss [MIN_MAX_LIST_THM, BIGUNION_INSERT, BIGUNION_EMPTY,
                         UNION_EMPTY, MAX_DEPTH_def, MIN_DEPTH_def]
) THEN
POP_ASSUM_LIST (fn thmL => EVERY (map (fn thm => ASSUME_TAC (GSYM thm)) (rev thmL))) THEN
FULL_SIMP_TAC list_ss [BIGUNION_INSERT, MIN_MAX_LIST_THM, MAX_DEPTH_def, MIN_DEPTH_def] THEN
CONSEQ_REWRITE_TAC ([], [MAX_SET_UNION, MIN_SET_UNION], []) THEN
Cases_on `tL` THEN1 FULL_SIMP_TAC std_ss [] THEN
SIMP_TAC std_ss [FINITE_BIGUNION_EQ, FINITE_DEPTH, NOT_DEPTH_EMPTY,
                 FINITE_LIST_TO_SET, MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
                 BIGUNION_EQ_EMPTY, MAP, LIST_TO_SET_THM, NOT_EMPTY_INSERT] THEN
SIMP_TAC std_ss [EXTENSION] THEN
Q.EXISTS_TAC `DEPTH h` THEN
SIMP_TAC std_ss [IN_SING, NOT_DEPTH_EMPTY, IN_INSERT]
QED

Theorem MAX_DEPTH___DIRECT_SUBTREES:
  !t2:'a tree t1. t1 IN DIRECT_SUBTREES t2 ==> (MAX_DEPTH t1 < MAX_DEPTH t2)
Proof

Cases_on `t2` THEN
SIMP_TAC std_ss [DIRECT_SUBTREES_def, NOT_IN_EMPTY] THEN
REPEAT STRIP_TAC THEN
`~NULL l` by (Cases_on `l` THEN FULL_SIMP_TAC list_ss []) THEN
`!n1 n2. n1 < SUC n2 = n1 <= n2` by DECIDE_TAC THEN
ASM_SIMP_TAC list_ss [MIN_MAX_DEPTH_THM]  THEN
MATCH_MP_TAC MAX_MAX_LIST THEN
SIMP_TAC std_ss [MEM_MAP] THEN
Q.EXISTS_TAC `t1` THEN
ASM_REWRITE_TAC[]
QED



Theorem MAX_DEPTH___DIRECT_SUBTREES___NODE:
  !v tL t. MEM t tL ==> (MAX_DEPTH t < MAX_DEPTH (node v tL))
Proof
REPEAT STRIP_TAC THEN
MATCH_MP_TAC MAX_DEPTH___DIRECT_SUBTREES THEN
ASM_SIMP_TAC std_ss [DIRECT_SUBTREES_def]
QED




Theorem MAX_DEPTH___PSUBTREES:
  !t2:'a tree t1. t1 IN PSUBTREES t2 ==> (MAX_DEPTH t1 < MAX_DEPTH t2)
Proof
SIMP_TAC std_ss [PSUBTREES_def, IN_DEF] THEN
HO_MATCH_MP_TAC (ISPECL [``MAX_DEPTH``] (GEN_ALL TC_lifts_transitive_relations)) THEN
SIMP_TAC arith_ss [transitive_def, SIMP_RULE std_ss [IN_DEF] MAX_DEPTH___DIRECT_SUBTREES]
QED




Definition TREE_FOLD_def:
   (TREE_FOLD (base, f) leaf = base) /\
   (TREE_FOLD (base, f) (node v tL) =
      f v (MAP (TREE_FOLD (base, f)) tL))
Termination
 Q.EXISTS_TAC `(measure (λ(f,t). MAX_DEPTH t))` THEN
 REWRITE_TAC [prim_recTheory.WF_measure] THEN
 SIMP_TAC arith_ss [prim_recTheory.measure_thm,
                    MAX_DEPTH___DIRECT_SUBTREES___NODE]
End


Definition WIDTH_def:   WIDTH t n = TREE_FOLD (F,
   \v tL. (LENGTH tL = n) \/ EXISTS I tL) t
End


Theorem WIDTH_THM:
  (WIDTH (leaf:'a tree) = EMPTY) /\
  (!v:'a tL. (WIDTH (node v tL) = ((LENGTH tL) INSERT (BIGUNION (LIST_TO_SET (MAP WIDTH tL))))))
Proof

SIMP_TAC std_ss [WIDTH_def, EXTENSION, NOT_IN_EMPTY, IN_INSERT,
   IN_BIGUNION] THEN
SIMP_TAC list_ss [MEM_MAP, GSYM RIGHT_EXISTS_AND_THM,
  IN_DEF, WIDTH_def, EXISTS_MEM, TREE_FOLD_def] THEN
METIS_TAC[]
QED


Theorem FINITE_WIDTH:
  !t. FINITE (WIDTH t)
Proof
HO_MATCH_MP_TAC tree_INDUCT THEN
SIMP_TAC list_ss [WIDTH_THM, FINITE_EMPTY, FINITE_INSERT,
   FINITE_BIGUNION_EQ, MEM_MAP, GSYM LEFT_FORALL_IMP_THM,
   EVERY_MEM]
QED


Theorem EMPTY_WIDTH:
  !t. (WIDTH t = EMPTY) = (IS_LEAF t)
Proof
Cases_on `t` THEN
SIMP_TAC std_ss [WIDTH_THM, IS_LEAF_def, NOT_EMPTY_INSERT]
QED


Definition BALANCED_def:
 BALANCED t n = (DEPTH t = {n})
End

Definition NARY_def:
 NARY t n = (WIDTH t SUBSET {n})
End

Theorem BALANCED_11:
  !t n1 n2. BALANCED t n1 /\ BALANCED t n2 ==> (n1 = n2)
Proof
SIMP_TAC (std_ss++CONJ_ss) [BALANCED_def, EQUAL_SING]
QED

val SUBSET_SING = prove (
``!s x. s SUBSET {x} = ((s = {x}) \/ (s = EMPTY))``,
SIMP_TAC std_ss [EXTENSION, IN_SING, NOT_IN_EMPTY, SUBSET_DEF] THEN
PROVE_TAC[]);

Theorem NARY_CASES:
  !t n. NARY t n = (IS_LEAF t \/ (WIDTH t = {n}))
Proof
SIMP_TAC std_ss [NARY_def, SUBSET_SING, EMPTY_WIDTH] THEN
PROVE_TAC[]
QED


Theorem NARY_REWRITE:
  (!n. NARY leaf n) /\
  (!n v tL. NARY (node v tL) n =
           ((LENGTH tL = n) /\ EVERY (\t. NARY t n) tL))
Proof

SIMP_TAC std_ss [NARY_CASES, IS_LEAF_def] THEN
REPEAT STRIP_TAC THEN EQ_TAC THENL [
   DISCH_TAC THEN
   `WIDTH (node v tL) SUBSET {n}` by PROVE_TAC[SET_EQ_SUBSET] THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, WIDTH_THM,
                         IN_INSERT, DISJ_IMP_THM, IN_BIGUNION,
                         FORALL_AND_THM, NOT_IN_EMPTY,
                         GSYM RIGHT_EXISTS_AND_THM,
                         MEM_MAP, GSYM LEFT_FORALL_IMP_THM, EVERY_MEM] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   Cases_on `t` THEN
   SIMP_TAC list_ss [IS_LEAF_def, EXTENSION, IN_SING] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
      PROVE_TAC[],
      FULL_SIMP_TAC std_ss [WIDTH_THM, IN_INSERT, DISJ_IMP_THM]
   ],


   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC[EXTENSION] THEN
   ASM_SIMP_TAC (std_ss++EQUIV_EXTRACT_ss) [
      WIDTH_THM, IN_INSERT, NOT_IN_EMPTY, IN_SING] THEN
   REWRITE_TAC[GSYM MONO_NOT_EQ] THEN
   SIMP_TAC std_ss [IN_BIGUNION, GSYM LEFT_FORALL_IMP_THM, MEM_MAP,
                    GSYM RIGHT_EXISTS_AND_THM] THEN
   FULL_SIMP_TAC std_ss [EVERY_MEM] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN (
      Cases_on `y` THEN
      FULL_SIMP_TAC list_ss [WIDTH_THM, NOT_IN_EMPTY, IS_LEAF_def, IN_SING]
   )
]
QED



Theorem NARY_11:
  !t n1 n2. NARY t n1 /\ NARY t n2 /\ ~(IS_LEAF t) ==> (n1 = n2)
Proof
SIMP_TAC (std_ss++CONJ_ss) [NARY_CASES, EQUAL_SING]
QED



Theorem WIDTH_SUBTREES:
  !t t'. t' IN SUBTREES t ==> WIDTH t' SUBSET WIDTH t
Proof

SIMP_TAC std_ss [SUBTREES_THM, IN_INSERT, DISJ_IMP_THM, FORALL_AND_THM,
                 SUBSET_REFL, PSUBTREES_def] THEN
SIMP_TAC std_ss [IN_DEF] THEN
HO_MATCH_MP_TAC (ISPEC ``WIDTH`` (GEN_ALL TC_lifts_transitive_relations)) THEN
CONJ_TAC THENL [
   SIMP_TAC std_ss [DIRECT_SUBTREES_EXISTS2, GSYM LEFT_FORALL_IMP_THM,
                    WIDTH_THM, IN_INSERT, IN_BIGUNION,
                    SUBSET_DEF, MEM_MAP, GSYM RIGHT_EXISTS_AND_THM] THEN
   METIS_TAC[],

   SIMP_TAC std_ss [transitive_def] THEN
   PROVE_TAC[SUBSET_TRANS]
]
QED


Theorem NARY_SUBTREES:
  !t1 t2 n. (t2 IN SUBTREES t1 /\ NARY t1 n) ==> (NARY t2 n)
Proof

SIMP_TAC std_ss [NARY_def] THEN
REPEAT STRIP_TAC THEN
IMP_RES_TAC WIDTH_SUBTREES THEN
PROVE_TAC[SUBSET_TRANS]
QED



Definition TREE_MAP_def:
   TREE_MAP f = TREE_FOLD (leaf, \v tL. node (f v) tL)
End

Theorem TREE_MAP_THM:
   (TREE_MAP f leaf = leaf) /\
   (TREE_MAP f (node v tL) =
        node (f v) (MAP (TREE_MAP f) tL))
Proof
SIMP_TAC std_ss [TREE_MAP_def, TREE_FOLD_def, tree_11] THEN
METIS_TAC[]
QED


Definition TREE_EVERY_def:
    TREE_EVERY P = TREE_FOLD (T, \v tL. (P v) /\ EVERY I tL)
End
Definition TREE_EXISTS_def:   TREE_EXISTS = \P t. ~(TREE_EVERY (\t'. ~ P t') t)
End


Theorem TREE_EVERY_EXISTS_REWRITE:
  (!P. (TREE_EVERY P leaf)) /\
  (!P v tL. TREE_EVERY P (node v tL) = P v /\ EVERY (TREE_EVERY P) tL) /\
  (!P. ~(TREE_EXISTS P leaf)) /\
  (!P v tL. TREE_EXISTS P (node v tL) = P v \/ EXISTS (TREE_EXISTS P) tL)
Proof
SIMP_TAC (std_ss++boolSimps.ETA_ss) [TREE_EXISTS_def, TREE_EVERY_def, TREE_FOLD_def,
   EVERY_MAP, EVERY_NOT_EXISTS, EXISTS_MAP]
QED


Definition LIST_TO_TREE_def:
    (LIST_TO_TREE [] = leaf) /\
    (LIST_TO_TREE (v::vs) = node v [LIST_TO_TREE vs])
End


Theorem LIST_TO_TREE_DEPTH:
  !l. DEPTH (LIST_TO_TREE l) = {LENGTH l}
Proof
Induct_on `l` THEN (
   ASM_SIMP_TAC list_ss [LIST_TO_TREE_def, DEPTH_THM, BIGUNION_SING,
                         IMAGE_INSERT, IMAGE_EMPTY]
)
QED


Theorem LIST_TO_TREE_WIDTH:
  !l. WIDTH (LIST_TO_TREE l) = if NULL l then EMPTY else {1}
Proof
Induct_on `l` THEN (
   ASM_SIMP_TAC list_ss [LIST_TO_TREE_def, WIDTH_THM, COND_RATOR, COND_RAND,
                         BIGUNION_SING, INSERT_INSERT]
)
QED


Theorem LIST_TO_TREE_NARY:
  !l. NARY (LIST_TO_TREE l) 1
Proof
Cases_on `l` THENL [
   REWRITE_TAC[NARY_REWRITE, LIST_TO_TREE_def],
   REWRITE_TAC[NARY_CASES, LIST_TO_TREE_WIDTH, NULL_DEF]
]
QED


Definition TREE_TO_LIST_def:
   TREE_TO_LIST = TREE_FOLD ([], \v tL. v::(FLAT tL))
End

Theorem TREE_TO_LIST_THM:
  (TREE_TO_LIST leaf = []) /\
  (TREE_TO_LIST (node v tL) =
      v::(FLAT (MAP TREE_TO_LIST tL)))
Proof
SIMP_TAC (std_ss++boolSimps.ETA_ss) [TREE_TO_LIST_def, TREE_FOLD_def]
QED


Theorem TREE_TO_LIST___LIST_TO_TREE:
  !l. TREE_TO_LIST (LIST_TO_TREE l) = l
Proof
Induct_on `l` THEN
ASM_SIMP_TAC list_ss [LIST_TO_TREE_def, TREE_TO_LIST_THM]
QED


Theorem LIST_TO_TREE___TREE_TO_LIST:
  !t. NARY t 1 ==> (LIST_TO_TREE (TREE_TO_LIST t) = t)
Proof

HO_MATCH_MP_TAC tree_INDUCT THEN
ASM_SIMP_TAC list_ss [LIST_TO_TREE_def, TREE_TO_LIST_THM,
   NARY_REWRITE, tree_11] THEN
REPEAT STRIP_TAC THEN
`?x. tL = [x]` by (
   Cases_on `tL` THEN
   FULL_SIMP_TAC list_ss [LENGTH_NIL]
) THEN
FULL_SIMP_TAC list_ss []
QED



Definition TREE_PATHS_def:
   TREE_PATHS = TREE_FOLD ({[]},
      (\v ps. IMAGE (\l. v::l) (FOLDR $UNION EMPTY ps)))
End

Theorem TREE_PATHS_THM:
   (TREE_PATHS leaf = {[]}) /\
   (TREE_PATHS (node v tL) = \p.
      ?t' p'. MEM t' tL /\ p' IN TREE_PATHS t' /\
              (p = v::p'))
Proof

REPEAT STRIP_TAC THEN1 (
   SIMP_TAC std_ss [TREE_PATHS_def, TREE_FOLD_def]
) THEN
Induct_on `tL` THEN1 (
   SIMP_TAC list_ss [TREE_PATHS_def, TREE_FOLD_def,
      IMAGE_EMPTY] THEN
   SIMP_TAC std_ss [GSYM EMPTY_DEF]
) THEN
FULL_SIMP_TAC list_ss [TREE_PATHS_def,
   TREE_FOLD_def, IMAGE_UNION] THEN
SIMP_TAC std_ss [EXTENSION, IN_ABS, IN_IMAGE,
   IN_UNION] THEN
METIS_TAC[]
QED


Theorem TREE_PATHS_NOT_EMPTY:
    !t. (TREE_PATHS t = EMPTY) ==> (0 IN WIDTH t)
Proof
   HO_MATCH_MP_TAC tree_INDUCT THEN
   SIMP_TAC std_ss [TREE_PATHS_THM, NOT_IN_EMPTY,
      IN_ABS, IN_INSERT, EVERY_MEM, WIDTH_THM, NOT_INSERT_EMPTY] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   ONCE_REWRITE_TAC[EXTENSION] THEN
   SIMP_TAC std_ss [IN_ABS, NOT_IN_EMPTY, IN_BIGUNION,
      MEM_MAP, GSYM RIGHT_EXISTS_AND_THM] THEN
   ASM_SIMP_TAC std_ss [prove (``(~x \/ b) = (x ==> b)``, PROVE_TAC[]),
      RIGHT_FORALL_IMP_THM, prove (``(!x. ~(x IN X)) = (X = EMPTY)``,
         SIMP_TAC std_ss [EXTENSION, NOT_IN_EMPTY])] THEN
   REPEAT STRIP_TAC THEN
   Cases_on `tL` THEN
   FULL_SIMP_TAC list_ss [DISJ_IMP_THM, FORALL_AND_THM] THEN
   Q.EXISTS_TAC `h` THEN
   ASM_REWRITE_TAC[]
QED
