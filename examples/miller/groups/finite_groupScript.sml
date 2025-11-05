Theory finite_group
Ancestors
  list res_quan pred_set extra_pred_set relation extra_list
  arithmetic group subtype extra_num gcd divides extra_arith
Libs
  hurdUtils subtypeTools res_quanTools arithContext
  ho_proverTools listContext pred_setContext groupContext

val _ = ParseExtras.temp_loose_equality()

val EXISTS_DEF = boolTheory.EXISTS_DEF;

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val S_TAC = rpt (POP_ASSUM MP_TAC) >> rpt RESQ_STRIP_TAC;

val std_pc = precontext_mergel [arith_pc, list_pc, pred_set_pc];
val std_c = precontext_compile std_pc;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS std_c;

val Strip = S_TAC;
val Simplify = R_TAC;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

Definition finite_group_def:
   finite_group G = group G /\ FINITE (gset G)
End

Definition add_group_def:
   add_group (n : num) = ((\x. x < n), (\x y. (x + y) MOD n))
End

Definition gord_def:
  gord G g = LEAST n. 0 < n /\ (gpow G g n = gid G)
End

Definition elt_subgroup_def:
   elt_subgroup G g = ((\x. ?i. x = gpow G g i), gop G)
End

Definition lcoset_list_def:
  lcoset_list G H = nub (MAP (\g. lcoset G g H) (SET_TO_LIST (gset G)))
End

Definition cyclic_def:
   cyclic G = ?g :: gset G. elt_subgroup G g = G
End

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

(* basic theorems *)

Theorem IN_FINITE_GROUP:
     !G. G IN finite_group = G IN group /\ FINITE (gset G)
Proof
   R_TAC [finite_group_def, SPECIFICATION]
QED

Theorem FINITE_GROUP_GROUP:
     !G. G IN finite_group ==> G IN group
Proof
   R_TAC [IN_FINITE_GROUP]
QED

Theorem FINITE_GROUP_FINITE:
     !G. G IN finite_group ==> FINITE (gset G)
Proof
   R_TAC [IN_FINITE_GROUP]
QED

(* Consolidate theorems so far in a simplification context *)

val finite_group1_pc = precontext_add
  ("finite_group1",
   map C_FORWARDS
   [FINITE_GROUP_FINITE,
    FINITE_GROUP_GROUP])
  group_pc;

val finite_group1_c = precontext_compile finite_group1_pc;

val (G_TAC, AG_TAC, G_TAC', AG_TAC') = SIMPLIFY_TACS finite_group1_c;

(* back to proving theorems *)

Theorem ADD_GROUP_SET:
     !m n. m IN gset (add_group n) = m < n
Proof
   R_TAC [add_group_def, gset_def, SPECIFICATION]
QED

Theorem ADD_GROUP_SET_ZERO:
     gset (add_group 0) = {}
Proof
   R_TAC [EXTENSION, ADD_GROUP_SET]
   >> DECIDE_TAC
QED

Theorem ADD_GROUP_SET_SUC:
     !n. gset (add_group (SUC n)) = n INSERT gset (add_group n)
Proof
   R_TAC [EXTENSION, IN_INSERT, ADD_GROUP_SET]
   >> DECIDE_TAC
QED

Theorem ADD_GROUP_SET_FINITE:
     !n. FINITE (gset (add_group n))
Proof
   Induct >- R_TAC [ADD_GROUP_SET_ZERO, FINITE_EMPTY]
   >> R_TAC [ADD_GROUP_SET_SUC, FINITE_INSERT]
QED

Theorem ADD_GROUP_SET_MAX:
     !n. ~(n IN gset (add_group n))
Proof
   R_TAC [ADD_GROUP_SET]
   >> DECIDE_TAC
QED

Theorem ADD_GROUP_SET_CARD:
     !n. CARD (gset (add_group n)) = n
Proof
   Induct >- R_TAC [ADD_GROUP_SET_ZERO, CARD_DEF]
   >> R_TAC [ADD_GROUP_SET_SUC, ADD_GROUP_SET_FINITE, CARD_DEF,
             ADD_GROUP_SET_MAX]
QED

Theorem ADD_GROUP_OP:
     !n a b. gop (add_group n) a b = (a + b) MOD n
Proof
   R_TAC [add_group_def, gop_def]
QED

Theorem ADD_GROUP_OP_SUBTYPE:
     !n.
       0 < n ==>
       gop (add_group n) IN
       (gset (add_group n) -> gset (add_group n) -> gset (add_group n))
Proof
   S_TAC
   >> AR_TAC [IN_FUNSET, ADD_GROUP_SET, ADD_GROUP_OP]
QED

Theorem ADD_GROUP_ASSOC:
     !n. !x y z :: gset (add_group n).
       0 < n ==>
       (gop (add_group n) (gop (add_group n) x y) z =
        gop (add_group n) x (gop (add_group n) y z))
Proof
   S_TAC
   >> AR_TAC [ADD_GROUP_SET, ADD_GROUP_OP, ADD_ASSOC]
QED

Theorem ADD_GROUP_ID:
     !n.
       0 < n ==>
       0 IN gset (add_group n) /\
       !x :: gset (add_group n). gop (add_group n) 0 x = x
Proof
   S_TAC >- AR_TAC [ADD_GROUP_SET]
   >> AR_TAC [ADD_GROUP_OP, ADD_GROUP_SET]
QED

Theorem ADD_GROUP_INV:
     !n. !x :: gset (add_group n).
       0 < n ==>
       (if x = 0 then 0 else n - x) IN gset (add_group n) /\
       (gop (add_group n) (if x = 0 then 0 else n - x) x = 0)
Proof
   S_TAC >|
   [AR_TAC [ADD_GROUP_SET]
    >> DECIDE_TAC,
    AR_TAC [ADD_GROUP_SET, ADD_GROUP_OP]
    >> Cases_on `x = 0` >- R_TAC []
    >> R_TAC []]
QED

Theorem ADD_GROUP:
     !n. 0 < n ==> add_group n IN finite_group
Proof
   S_TAC
   >> R_TAC [IN_FINITE_GROUP, ADD_GROUP_SET_FINITE, IN_GROUP,
             ADD_GROUP_OP_SUBTYPE, ADD_GROUP_ASSOC]
   >> RESQ_EXISTS_TAC ``0:num``
   >> R_TAC [ADD_GROUP_ID]
   >> S_TAC
   >> RESQ_EXISTS_TAC ``if x = 0 then 0 : num else n - x``
   >> R_TAC [ADD_GROUP_INV]
QED

Theorem ADD_GROUP_SUBTYPE:
     add_group IN (gtnum 0 -> finite_group)
Proof
   R_TAC [IN_GTNUM, IN_FUNSET, ADD_GROUP]
QED

Theorem GORD_EXISTS:
     !G :: finite_group. !g :: gset G. ?n. 0 < n /\ (gpow G g n = gid G)
Proof
   S_TAC
   >> AR_TAC [IN_FINITE_GROUP]
   >> MP_TAC (Q.SPECL [`gset G`, `gpow G g`] NUM_TO_FINITE)
   >> SIMPLIFY_TAC' group_c []
   >> S_TAC
   >> Q.EXISTS_TAC `j - i`
   >> CONJ_TAC >- DECIDE_TAC
   >> Suff `gpow G g ((j - i) + i) = gpow G g i` >- G_TAC []
   >> R_TAC []
QED

Theorem GORD:
   !G :: finite_group. !g :: gset G.
       (0 < gord G g /\ (gpow G g (gord G g) = gid G)) /\
       !n. 0 < n /\ n < gord G g ==> ~(gpow G g n = gid G)
Proof
   NTAC 2 RESQ_STRIP_TAC
   >> simp[gord_def] >> numLib.LEAST_ELIM_TAC >> simp[]
   >> metis_tac[GORD_EXISTS, prim_recTheory.LESS_REFL]
QED

Theorem GORD_SUBTYPE:
     gord IN (finite_group --> (\G. gset G -> gtnum 0))
Proof
   R_TAC [IN_DFUNSET, IN_FUNSET]
   >> S_TAC
   >> R_TAC [GORD, IN_GTNUM]
QED

Theorem GPOW_GORD:
     !G :: finite_group. !g :: gset G. gpow G g (gord G g) = gid G
Proof
   R_TAC [GORD]
QED

Theorem GPOW_MOD_GORD:
     !G :: finite_group. !g :: gset G. !n.
       gpow G g (n MOD gord G g) = gpow G g n
Proof
   S_TAC
   >> MP_TAC (Q_RESQ_SPECL [`G`, `g`] GPOW_GORD)
   >> S_TAC
   >> MP_TAC (Q.SPEC `gord G g` (GSYM DIVISION))
   >> R_TAC [GORD]
   >> DISCH_THEN (CONV_TAC o RAND_CONV o ONCE_REWRITE_CONV o wrap o GSYM)
   >> ONCE_REWRITE_TAC [MULT_COMM]
   >> G_TAC [IN_FINITE_GROUP]
QED

Theorem ELT_SUBGROUP_SET:
     !G g x. x IN gset (elt_subgroup G g) = ?i. x = gpow G g i
Proof
   R_TAC [SPECIFICATION, elt_subgroup_def, gset_def]
QED

Theorem ELT_SUBGROUP_OP:
     !G g. gop (elt_subgroup G g) = gop G
Proof
   R_TAC [elt_subgroup_def, gop_def]
QED

Theorem ELT_SUBGROUP_HOMO:
     !G :: finite_group. !g :: gset G.
       gpow G g IN group_homo (add_group (gord G g)) (elt_subgroup G g)
Proof
   R_TAC [IN_GROUP_HOMO, IN_FUNSET, ELT_SUBGROUP_SET, SURJ_ALT]
   >> S_TAC >- ho_PROVE_TAC []
   >> AR_TAC [ADD_GROUP_SET, ADD_GROUP_OP, ELT_SUBGROUP_OP, GPOW_MOD_GORD]
   >> G_TAC [IN_FINITE_GROUP]
QED

Theorem ELT_SUBGROUP_ISO:
     !G :: finite_group. !g :: gset G.
       gpow G g IN group_iso (add_group (gord G g)) (elt_subgroup G g)
Proof
   R_TAC [IN_GROUP_ISO, ELT_SUBGROUP_HOMO, BIJ_ALT_RES, IN_FUNSET,
          ELT_SUBGROUP_SET]
   >> S_TAC >- ho_PROVE_TAC []
   >> POP_ASSUM MP_TAC
   >> R_TAC [ELT_SUBGROUP_SET]
   >> S_TAC
   >> R_TAC []
   >> POP_ASSUM K_TAC
   >> R_TAC [RES_EXISTS_UNIQUE]
   >> S_TAC >|
   [Q_RESQ_EXISTS_TAC `i MOD gord G g`
    >> G_TAC [ADD_GROUP_SET, GPOW_MOD_GORD, GORD, GORD_SUBTYPE],
    AR_TAC [ADD_GROUP_SET]
    >> Know `(x:num = y) \/ x < y \/ y < x` >- DECIDE_TAC
    >> S_TAC >|
    [Suff `0 < y - x /\ y - x < gord G g /\ (gpow G g (y - x) = gid G)`
     >- R_TAC [GORD]
     >> S_TAC >|
     [DECIDE_TAC,
      DECIDE_TAC,
      Suff `gpow G g (y - x + x) = gpow G g x` >- G_TAC [IN_FINITE_GROUP]
      >> R_TAC []],
     Suff `0 < x - y /\ x - y < gord G g /\ (gpow G g (x - y) = gid G)`
     >- R_TAC [GORD]
     >> S_TAC >|
     [DECIDE_TAC,
      DECIDE_TAC,
      Suff `gpow G g (x - y + y) = gpow G g y` >- G_TAC [IN_FINITE_GROUP]
      >> R_TAC []]]]
QED

Theorem ELT_SUBGROUP_SUBGROUP:
     !G :: finite_group. !g :: gset G. elt_subgroup G g IN subgroup G
Proof
   S_TAC
   >> AR_TAC [IN_SUBGROUP, SUBSET_DEF, ELT_SUBGROUP_OP, ELT_SUBGROUP_SET]
   >> REVERSE S_TAC >- G_TAC [IN_FINITE_GROUP]
   >> MP_TAC (Q.SPEC `gord G g` ADD_GROUP)
   >> R_TAC [GORD, IN_FINITE_GROUP]
   >> S_TAC
   >> MP_TAC
   (Q_RESQ_ISPECL [`add_group (gord G g)`, `elt_subgroup G g`] GROUP_ISO_GROUP)
   >> ASSUME_TAC (Q_RESQ_SPECL [`G`, `g`] ELT_SUBGROUP_ISO)
   >> RESQ_TAC
   >> ho_PROVE_TAC []
QED

Theorem ELT_SUBGROUP_SUBTYPE:
     elt_subgroup IN (finite_group --> (\G. gset G -> subgroup G))
Proof
   R_TAC [IN_DFUNSET, IN_FUNSET, ELT_SUBGROUP_SUBGROUP]
QED

Theorem SUBGROUP_FINITE_GROUP:
     !G H. G IN finite_group /\ H IN subgroup G ==> H IN finite_group
Proof
   RW_TAC std_ss [IN_SUBGROUP, IN_FINITE_GROUP]
   >> PROVE_TAC [SUBSET_FINITE]
QED

Theorem CARD_GROUP:
     !G :: finite_group. ~(CARD (gset G) = 0)
Proof
   S_TAC
   >> Know `gset G = {}` >- AR_TAC [IN_FINITE_GROUP, CARD_EQ_0]
   >> Know `gid G IN gset G` >- AR_TAC [IN_FINITE_GROUP, GROUP]
   >> PROVE_TAC [NOT_IN_EMPTY]
QED

Theorem LCOSET_REFL:
     !G :: finite_group. !H :: subgroup G. !g :: gset G. g IN lcoset G g H
Proof
   S_TAC
   >> R_TAC [lcoset_def, IN_IMAGE]
   >> Q.EXISTS_TAC `gid H`
   >> ASM_MATCH_MP_TAC [FINITE_GROUP_GROUP, SUBGROUP_ID]
   >> G_TAC' []
QED

Theorem CARD_LCOSET:
     !G :: finite_group. !H :: subgroup G. !g :: gset G.
       CARD (lcoset G g H) = CARD (gset H)
Proof
   S_TAC
   >> G_TAC [lcoset_def]
   >> MATCH_MP_TAC CARD_IMAGE
   >> Q.EXISTS_TAC `gset G`
   >> CONJ_TAC >- PROVE_TAC [IN_FINITE_GROUP, SUBGROUP_FINITE_GROUP]
   >> G_TAC' [INJ_DEF, IN_FINITE_GROUP]
QED

Theorem MAP_MEM[local] = ONCE_REWRITE_RULE [CONJ_COMM] MEM_MAP
Theorem UNIONL_LCOSET_LIST:
     !G :: finite_group. !H :: subgroup G. UNIONL (lcoset_list G H) = gset G
Proof
   SET_EQ_TAC
   >> S_TAC
   >> EQ_TAC >|
   [R_TAC [IN_UNIONL]
    >> S_TAC
    >> Q.PAT_X_ASSUM `MEM s t` MP_TAC
    >> R_TAC [lcoset_list_def, MEM_nub, MAP_MEM]
    >> S_TAC
    >> AR_TAC []
    >> POP_ASSUM K_TAC
    >> AR_TAC [MEM_SET_TO_LIST, IN_FINITE_GROUP]
    >> Q.PAT_X_ASSUM `v IN lcoset G y H` MP_TAC
    >> R_TAC [lcoset_def, IN_IMAGE]
    >> S_TAC
    >> G_TAC [],
    RW_TAC std_ss [lcoset_list_def, IN_UNIONL, MEM_nub, MEM_MAP]
    >> Q.EXISTS_TAC `lcoset G x H`
    >> G_TAC [MEM_SET_TO_LIST, LCOSET_REFL]
    >> ho_PROVE_TAC []]
QED

Theorem DISJOINTL_LCOSET_LIST:
     !G :: finite_group. !H :: subgroup G. DISJOINTL (lcoset_list G H)
Proof
   S_TAC
   >> G_TAC [lcoset_list_def, DISJOINTL_KILL_DUPS, MEM_MAP, MEM_SET_TO_LIST]
   >> S_TAC
   >> G_TAC [LCOSETS_EQUAL_OR_DISJOINT]
QED

Theorem CARD_LCOSET_LIST:
     !G :: finite_group. !H :: subgroup G. !c.
       MEM c (lcoset_list G H) ==> (CARD c = CARD (gset H))
Proof
   G_TAC [lcoset_list_def, MEM_nub, MAP_MEM]
   >> S_TAC
   >> Q.PAT_X_ASSUM `MEM y x` MP_TAC
   >> G_TAC [MEM_SET_TO_LIST, CARD_LCOSET]
QED

Theorem LAGRANGE:
     !G :: finite_group. !H :: subgroup G.
       divides (CARD (gset H)) (CARD (gset G))
Proof
   S_TAC
   >> MP_TAC (Q_RESQ_SPECL [`G`, `H`] (GSYM UNIONL_LCOSET_LIST))
   >> R_TAC []
   >> MP_TAC (Q_RESQ_SPECL [`G`, `H`] DISJOINTL_LCOSET_LIST)
   >> S_TAC
   >> Know `EVERY FINITE (lcoset_list G H)`
   >- PROVE_TAC [FINITE_UNIONL, IN_FINITE_GROUP]
   >> MP_TAC (Q.SPEC `lcoset_list G H` CARD_UNIONL)
   >> R_TAC []
   >> S_TAC
   >> NTAC 4 (POP_ASSUM K_TAC)
   >> MP_TAC
      (Q.SPECL [`MAP CARD (lcoset_list G H)`, `(CARD (gset H))`] SUM_CONST)
   >> Know `!x. MEM x (MAP CARD (lcoset_list G H)) ==> (x = CARD (gset H))`
   >- (R_TAC [MAP_MEM]
       >> S_TAC
       >> PROVE_TAC [Q_RESQ_SPECL [`G`, `H`] CARD_LCOSET_LIST])
   >> RW_TAC std_ss []
   >> POP_ASSUM (fn th => RW_TAC std_ss [th])
   >> PROVE_TAC [divides_def]
QED

Theorem LAGRANGE_PROPER:
     !G :: finite_group. !H :: psubgroup G.
       2 * CARD (gset H) <= CARD (gset G)
Proof
   S_TAC
   >> Know `divides (CARD (gset H)) (CARD (gset G))` >- G_TAC [LAGRANGE]
   >> R_TAC [divides_def]
   >> S_TAC
   >> R_TAC []
   >> MATCH_MP_TAC LESS_MONO_MULT
   >> Suff `~(q = 0) /\ ~(q = 1)` >- DECIDE_TAC
   >> S_TAC >|
   [Q.PAT_X_ASSUM `CARD x = y` MP_TAC
    >> R_TAC [CARD_GROUP],
    Q.PAT_X_ASSUM `CARD x = y` MP_TAC
    >> R_TAC []
    >> Suff `CARD (gset H) < CARD (gset G)` >- DECIDE_TAC
    >> G_TAC [CARD_PSUBSET]]
QED

Theorem GORD_DIVIDES_CARD:
     !G :: finite_group. !g :: gset G. divides (gord G g) (CARD (gset G))
Proof
   S_TAC
   >> Suff `divides (CARD (gset (add_group (gord G g)))) (CARD (gset G))`
   >- R_TAC [ADD_GROUP_SET_CARD]
   >> Suff `divides (CARD (gset (elt_subgroup G g))) (CARD (gset G))`
   >- (Suff
         `CARD (gset (add_group (gord G g))) = CARD (gset (elt_subgroup G g))`
       >- R_TAC []
       >> MATCH_MP_TAC FINITE_BIJ_CARD
       >> R_TAC [ADD_GROUP_SET_FINITE]
       >> PROVE_TAC [Q_RESQ_SPECL [`G`, `g`] ELT_SUBGROUP_ISO, IN_GROUP_ISO])
   >> Know `elt_subgroup G g IN subgroup G` >- R_TAC [ELT_SUBGROUP_SUBGROUP]
   >> S_TAC
   >> ACCEPT_TAC (Q_RESQ_SPECL [`G`, `elt_subgroup G g`] LAGRANGE)
QED

(* Fermat's little theorem for groups *)

Theorem POWER_ORDER:
     !G :: finite_group. !g :: gset G. gpow G g (CARD (gset G)) = gid G
Proof
   S_TAC
   >> Know `divides (gord G g) (CARD (gset G))` >- R_TAC [GORD_DIVIDES_CARD]
   >> R_TAC [divides_def]
   >> S_TAC
   >> POP_ASSUM (fn th => R_TAC [ONCE_REWRITE_RULE [MULT_COMM] th])
   >> G_TAC [GPOW_GORD]
QED

(* Some applications to div/mod *)

Theorem MOD_SUC_MOD:
     !n a b. 0 < n ==> ((SUC a MOD n = SUC b MOD n) = (a MOD n = b MOD n))
Proof
   S_TAC
   >> Suff `(gop (add_group n) (a MOD n) (1 MOD n) =
                 gop (add_group n) (b MOD n) (1 MOD n)) = (a MOD n = b MOD n)`
   >- R_TAC [ADD_GROUP_OP, ADD_GROUP_SET, ADD1]
   >> Know `!x. (x MOD n) IN gset (add_group n)` >- R_TAC [ADD_GROUP_SET]
   >> Know `add_group n IN group` >- R_TAC [ADD_GROUP, FINITE_GROUP_GROUP]
   >> G_TAC []
QED

Theorem MOD_MULT_MOD:
     !m n a. 0 < m /\ 0 < n ==> (a MOD (m * n) MOD n = a MOD n)
Proof
   S_TAC
   >> Know `0 < m * n` >- R_TAC []
   >> S_TAC
   >> Induct_on `a` >- R_TAC []
   >> Suff `(if divides (m * n) (SUC a) then 0 else SUC (a MOD (m * n))) MOD n = SUC a MOD n`
   >- R_TAC [SUC_MOD]
   >> REVERSE (Cases_on `divides (m * n) (SUC a)`)
   >- R_TAC [MOD_SUC_MOD]
   >> R_TAC []
   >> Suff `SUC a MOD n = 0` >- PROVE_TAC []
   >> R_TAC [DIVIDES_MOD]
   >> AR_TAC [divides_def]
   >> S_TAC
   >> Q.EXISTS_TAC `q * m`
   >> PROVE_TAC [MULT_ASSOC]
QED

Theorem MOD_ADD_CANCEL:
     !n x y.
       0 < n ==> (((x + y) MOD n = x MOD n) = (y MOD n = 0))
Proof
   S_TAC
   >> Induct_on `x` >- R_TAC []
   >> R_TAC [ADD, MOD_SUC_MOD]
QED

Theorem FINITE_GSET_SUBTYPE:
     gset IN ((group -> nonempty) INTER (finite_group -> FINITE))
Proof
   R_TAC [IN_INTER, GSET_SUBTYPE]
   >> R_TAC [IN_FUNSET, IN_FINITE_GROUP, IN_FINITE]
QED

(* Consolidate theorems so far in a simplification context *)

val finite_group2_sc =
  map SC_SIMPLIFICATION
  [] @
  map SC_JUDGEMENT
  [] @
  map SC_SUBTYPE
  [FINITE_GSET_SUBTYPE,
   GORD_SUBTYPE,
   ELT_SUBGROUP_SUBTYPE,
   ADD_GROUP_SUBTYPE];

val finite_group2_pc = precontext_add
  ("finite_group2",
   map C_SUBTYPE finite_group2_sc @
   map C_THM
   [ADD_GROUP_SET_ZERO,
    ADD_GROUP_SET_FINITE,
    ADD_GROUP_SET_CARD,
    GPOW_GORD,
    GPOW_MOD_GORD,
    LCOSET_REFL,
    CARD_GROUP,
    CARD_LCOSET,
    POWER_ORDER,
    MOD_SUC_MOD,
    MOD_MULT_MOD,
    MOD_ADD_CANCEL] @
   map C_FORWARDS
   [SUBGROUP_FINITE_GROUP])
  finite_group1_pc;

val finite_group2_c = precontext_compile finite_group2_pc;

val (G_TAC, AG_TAC, G_TAC', AG_TAC') = SIMPLIFY_TACS finite_group2_c;

(* back to proving theorems *)

Theorem MAXIMAL_ORDER:
     !G :: finite_group. ?g :: gset G. !h :: gset G. gord G h <= gord G g
Proof
   S_TAC
   >> MATCH_MP_TAC (Q.SPECL [`gord G`, `gset G`] FINITE_MAXIMAL)
   >> G_TAC [GROUP_SET_EMPTY]
QED

Theorem GPOW_GID_GORD:
     !G :: finite_group. !g :: gset G. !n.
       (gpow G g n = gid G) = divides (gord G g) n
Proof
   S_TAC
   >> REVERSE EQ_TAC
   >- (R_TAC [divides_def]
       >> S_TAC
       >> R_TAC []
       >> ONCE_REWRITE_TAC [MULT_COMM]
       >> G_TAC [])
   >> S_TAC
   >> Know `gpow G g (n MOD gord G g) = gid G` >- G_TAC []
   >> POP_ASSUM K_TAC
   >> S_TAC
   >> Suff `n MOD gord G g = 0` >- G_TAC [DIVIDES_MOD]
   >> POP_ASSUM MP_TAC
   >> Know `!a b. (~b ==> ~a) ==> (a ==> b)` >- PROVE_TAC []
   >> DISCH_THEN MATCH_MP_TAC
   >> S_TAC
   >> MP_TAC (Q_RESQ_SPECL [`G`, `g`] GORD)
   >> S_TAC
   >> POP_ASSUM (MP_TAC o Q.SPEC `n MOD gord G g`)
   >> Know `0 < n MOD gord G g` >- DECIDE_TAC
   >> G_TAC []
QED

Theorem GORD_UNIQUE:
     !G :: finite_group. !g :: gset G. !n.
       0 < n /\ (gpow G g n = gid G) /\
       (!m. 0 < m /\ m < n ==> ~(gpow G g m = gid G)) ==>
       (gord G g = n)
Proof
   S_TAC
   >> Suff `~(gord G g < n) /\ ~(n < gord G g)` >- DECIDE_TAC
   >> S_TAC >|
   [Q.PAT_X_ASSUM `!m. P m` (MP_TAC o Q.SPEC `gord G g`)
    >> G_TAC [GORD],
    MP_TAC (Q_RESQ_SPECL [`G`, `g`] GORD)
    >> S_TAC
    >> POP_ASSUM (MP_TAC o Q.SPEC `n`)
    >> G_TAC []]
QED

Theorem IS_GORD:
     !G :: finite_group. !g :: gset G. !n.
       (gord G g = n) =
       0 < n /\ (gpow G g n = gid G) /\
       !m. 0 < m /\ m < n ==> ~(gpow G g m = gid G)
Proof
   S_TAC
   >> EQ_TAC >- DISCH_THEN (fn th => R_TAC [SYM th, GORD])
   >> S_TAC
   >> MP_TAC (Q_RESQ_SPECL [`G`, `g`, `n`] GORD_UNIQUE)
   >> R_TAC []
QED

Theorem GORD_GPOW_PRIME:
     !G :: finite_group. !g :: gset G. !p.
       prime p ==>
       (gord G (gpow G g p) =
        if divides p (gord G g) then gord G g DIV p else gord G g)
Proof
   S_TAC
   >> G_TAC [IS_GORD]
   >> Cases_on `divides p (gord G g)` >|
   [R_TAC []
    >> S_TAC >|
    [Suff `~(gord G g DIV p = 0)` >- DECIDE_TAC
     >> S_TAC
     >> Q.PAT_X_ASSUM `divides x y` MP_TAC
     >> R_TAC [DIVIDES_ALT]
     >> Suff `0 < gord G g` >- DECIDE_TAC
     >> G_TAC [GORD],
     Suff `gpow G g (p * (gord G g DIV p)) = gid G`
     >- G_TAC []
     >> Q.PAT_X_ASSUM `divides x y` MP_TAC
     >> R_TAC [DIVIDES_ALT]
     >> DISCH_THEN (fn th => R_TAC [ONCE_REWRITE_RULE [MULT_COMM] th])
     >> G_TAC [GORD],
     Suff `~(gpow G g (p * m) = gid G)` >- G_TAC []
     >> (MATCH_MP_TAC o last o CONJUNCTS o Q_RESQ_SPECL [`G`, `g`]) GORD
     >> S_TAC
     >- (Suff `0 < p * m` >- R_TAC []
         >> R_TAC' [])
     >> Q.PAT_X_ASSUM `divides x y` MP_TAC
     >> R_TAC [DIVIDES_ALT]
     >> DISCH_THEN
        (fn th => ONCE_REWRITE_TAC [ONCE_REWRITE_RULE [MULT_COMM] (SYM th)])
     >> Cases_on `p` >- PROVE_TAC [NOT_PRIME_0]
     >> R_TAC [LESS_MULT_MONO]],
    R_TAC []
    >> REWRITE_TAC [CONJ_ASSOC]
    >> STRONG_CONJ_TAC
    >- (CONJ_TAC >- G_TAC [GORD]
        >> Suff `gpow G g (p * gord G g) = gid G` >- G_TAC []
        >> ONCE_REWRITE_TAC [MULT_COMM]
        >> G_TAC [GORD])
    >> S_TAC
    >> POP_ASSUM MP_TAC
    >> G_TAC [GPOW_GID_GORD]
    >> S_TAC
    >> Suff `gord G g <= m` >- DECIDE_TAC
    >> Suff `divides (gord G g) m`
    >- (S_TAC
        >> MATCH_MP_TAC DIVIDES_LE
        >> R_TAC [])
    >> MATCH_MP_TAC L_EUCLIDES
    >> Q.EXISTS_TAC `p`
    >> R_TAC []
    >> G_TAC [GSYM GPOW_GID_GORD]
    >> G_TAC [GPOW_GID_GORD, GCD_1_PRIMEL]]
QED

Theorem GORD_GID:
     !G :: finite_group. gord G (gid G) = 1
Proof
   S_TAC
   >> G_TAC [IS_GORD]
   >> DECIDE_TAC
QED

Theorem GORD_GID_UNIQUE:
     !G :: finite_group. !g :: gset G. (gord G g = 1) = (g = gid G)
Proof
   S_TAC
   >> REVERSE EQ_TAC >- G_TAC [GORD_GID]
   >> S_TAC
   >> MP_TAC (Q_RESQ_HALF_SPECL [`G`, `g`] GORD)
   >> R_TAC []
   >> G_TAC [GPOW_1]
QED

Theorem PRIME_DIVIDES_GORD_GPOW:
     !G :: finite_group. !g :: gset G. !n p.
       prime p /\ divides p (gord G (gpow G g n)) ==> divides p (gord G g)
Proof
   S_TAC
   >> POP_ASSUM MP_TAC
   >> Q.SPEC_TAC (`n`, `n`)
   >> HO_MATCH_MP_TAC FACTOR_INDUCT
   >> CONJ_TAC >- G_TAC [GORD_GID]
   >> CONJ_TAC >- G_TAC [GPOW_1]
   >> S_TAC
   >> Q.PAT_X_ASSUM `x ==> y` MATCH_MP_TAC
   >> POP_ASSUM MP_TAC
   >> ONCE_REWRITE_TAC [MULT_COMM]
   >> G_TAC []
   >> Know `gpow G g n IN gset G` >- G_TAC' []
   >> Q.PAT_X_ASSUM `g IN gset G` K_TAC
   >> Q.SPEC_TAC (`gpow G g n`, `g`)
   >> S_TAC
   >> CCONTR_TAC
   >> Q.PAT_X_ASSUM `divides x y` MP_TAC
   >> G_TAC [GORD_GPOW_PRIME]
   >> REVERSE (Cases_on `divides p' (gord G g)`) >- R_TAC []
   >> R_TAC []
   >> S_TAC
   >> Q.PAT_X_ASSUM `divides p' y` MP_TAC
   >> R_TAC [DIVIDES_ALT]
   >> S_TAC
   >> POP_ASSUM (ASSUME_TAC o ONCE_REWRITE_RULE [MULT_COMM] o SYM)
   >> Q.PAT_X_ASSUM `~divides x y` MP_TAC
   >> POP_ASSUM (PURE_ONCE_REWRITE_TAC o wrap)
   >> R_TAC []
   >> POP_ASSUM MP_TAC
   >> PROVE_TAC [divides_def, MULT_COMM, MULT_ASSOC]
QED

Theorem GORD_GINV:
     !G :: finite_group. !g :: gset G. gord G (ginv G g) = gord G g
Proof
   S_TAC
   >> G_TAC [IS_GORD, GSYM GINV_GPOW, GINV_GID]
   >> MP_TAC (Q_RESQ_SPECL [`G`, `g`] GORD)
   >> R_TAC []
   >> S_TAC
   >> POP_ASSUM MP_TAC
   >> G_TAC [GINV_EQ_GID]
QED

Theorem GORD_GT_0:
     !G :: finite_group. !g :: gset G. 0 < gord G g
Proof
   S_TAC
   >> G_TAC []
QED

Theorem GORD_EQ_0:
     !G :: finite_group. !g :: gset G. ~(gord G g = 0)
Proof
   S_TAC
   >> Suff `0 < gord G g` >- DECIDE_TAC
   >> POP_ASSUM K_TAC
   >> G_TAC [GORD_GT_0]
QED

(* Consolidate theorems so far in a simplification context *)

val finite_group3_pc = precontext_add
  ("finite_group3",
   map C_THM
   [GORD_GID,
    GORD_GINV])
  finite_group2_pc;

val finite_group3_c = precontext_compile finite_group3_pc;

val (G_TAC, AG_TAC, G_TAC', AG_TAC') = SIMPLIFY_TACS finite_group3_c;

(* back to proving theorems *)

Theorem CARD_ELT_SUBGROUP:
     !G :: finite_group. !g :: gset G.
       CARD (gset (elt_subgroup G g)) = gord G g
Proof
   S_TAC
   >> MP_TAC (Q_RESQ_SPECL [`G`, `g`] ELT_SUBGROUP_ISO)
   >> R_TAC [IN_GROUP_ISO]
   >> S_TAC
   >> MP_TAC (Q.ISPECL [`gpow G g`, `gset (add_group (gord G g))`,
                        `gset (elt_subgroup G g)`] FINITE_BIJ_CARD)
   >> G_TAC []
QED

Theorem GORD_DIVIDES:
     !G :: finite_group. !g :: gset G. !n.
       (gpow G g n = gid G) ==> divides (gord G g) n
Proof
   S_TAC
   >> Suff `n MOD (gord G g) = 0` >- G_TAC [DIVIDES_MOD]
   >> Know `gpow G g (n MOD (gord G g)) = gid G` >- G_TAC [GPOW_MOD_GORD]
   >> POP_ASSUM K_TAC
   >> Know `n MOD (gord G g) < gord G g` >- G_TAC []
   >> Q.SPEC_TAC (`n MOD (gord G g)`, `n`)
   >> S_TAC
   >> Suff `~(0 < n)` >- DECIDE_TAC
   >> MP_TAC (Q_RESQ_SPECL [`G`, `g`] GORD)
   >> PROVE_TAC []
QED

Theorem GORD_LE:
     !G :: finite_group. !g :: gset G. !n.
       0 < n /\ (gpow G g n = gid G) ==> gord G g <= n
Proof
   S_TAC
   >> MATCH_MP_TAC DIVIDES_LE
   >> R_TAC [GORD_DIVIDES]
QED

Theorem CYCLIC_ALT:
     !G :: finite_group. cyclic G = ?g :: gset G. gord G g = CARD (gset G)
Proof
   S_TAC
   >> R_TAC [cyclic_def]
   >> EQ_TAC >|
   [S_TAC
    >> Q_RESQ_EXISTS_TAC `g`
    >> G_TAC [IS_GORD, FINITE_GSET_SUBTYPE, CARD_SUBTYPE]
    >> S_TAC
    >> Know `CARD (gset (elt_subgroup G g)) = CARD (gset G)` >- R_TAC []
    >> R_TAC [CARD_ELT_SUBGROUP]
    >> Know `gord G g <= m` >- R_TAC [GORD_LE]
    >> DECIDE_TAC,
    S_TAC
    >> Q_RESQ_EXISTS_TAC `g`
    >> R_TAC []
    >> Suff `gset (elt_subgroup G g) = gset G`
    >- (Cases_on `G` >> R_TAC [gset_def, gop_def, elt_subgroup_def])
    >> MATCH_MP_TAC FINITE_SUBSET_CARD_EQ
    >> ASSUME_TAC (Q_RESQ_SPECL [`G`, `g`] ELT_SUBGROUP_SUBGROUP)
    >> G_TAC [CARD_ELT_SUBGROUP]]
QED

Theorem GORD_LE_CARD:
     !G :: finite_group. !g :: gset G. gord G g <= CARD (gset G)
Proof
   S_TAC
   >> MATCH_MP_TAC DIVIDES_LE
   >> G_TAC [CARD_SUBTYPE, FINITE_GSET_SUBTYPE, GORD_DIVIDES_CARD]
QED

Theorem MOD_ADD_LCANCEL:
     !n :: gtnum 0. !x y z.
       ((x + y) MOD n = (x + z) MOD n) = (y MOD n = z MOD n)
Proof
   S_TAC
   >> Induct_on `x` >- R_TAC []
   >> R_TAC [ADD, MOD_SUC_MOD]
QED

Theorem MOD_PRIME_CANCEL_1:
     !p x. prime p ==> (((p - 1 + x) MOD p = 0) = (x MOD p = 1))
Proof
   S_TAC
   >> Know `((p - 1 + x) MOD p = 0) = ((1 + (p - 1 + x)) MOD p = 1 MOD p)`
   >- R_TAC [MOD_ADD_CANCEL]
   >> DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   >> R_TAC [ADD_ASSOC]
QED

Theorem GPOW_MOD_ORDER:
     !G :: finite_group. !g :: gset G. !m n.
       0 < m /\ (gpow G g m = gid G) ==>
       (gpow G g (n MOD m) = gpow G g n)
Proof
   G_TAC [GPOW_GID_GORD, divides_def]
   >> S_TAC
   >> Suff `gpow G g (n MOD gord G g) = gpow G g ((n MOD m) MOD gord G g)`
   >- G_TAC [GPOW_MOD_GORD]
   >> Suff `((n MOD m) MOD gord G g) = (n MOD gord G g)`
   >- R_TAC []
   >> AR_TAC []
   >> R_TAC [MOD_MULT_MOD]
QED

Theorem GPOW_MOD_CARD:
     !G :: finite_group. !g :: gset G. !n.
       gpow G g (n MOD CARD (gset G)) = gpow G g n
Proof
   S_TAC
   >> MATCH_MP_TAC (Q_RESQ_SPECL [`G`, `g`] GPOW_MOD_ORDER)
   >> G_TAC []
QED

Theorem DIVIDES_GORD:
     !G :: finite_group. !g :: gset G. !n.
       divides n (gord G g) = (!m. (gpow G g m = gid G) ==> divides n m)
Proof
   G_TAC [GPOW_GID_GORD]
   >> S_TAC
   >> EQ_TAC >|
   [S_TAC
    >> PROVE_TAC [DIVIDES_TRANS],
    S_TAC
    >> PROVE_TAC [DIVIDES_ANTISYM, DIVIDES_REFL]]
QED

Theorem FINITE_SET_SUBGROUP:
     !s G.
       G IN finite_group /\ s SUBSET gset G /\ ~(s = {}) /\
       gop G IN (s -> s -> s) ==>
       (s, gop G) IN subgroup G
Proof
   Strip
   >> MATCH_MP_TAC SET_SUBGROUP
   >> G_TAC []
   >> Simplify [IN_FUNSET]
   >> Strip
   >> Know `!n. 0 < n ==> gpow G x n IN s`
   >- (Induct >- Simplify []
       >> Cases_on `0 < n` >- G_TAC [GPOW]
       >> Know `n = 0` >- DECIDE_TAC
       >> G_TAC [])
   >> MP_TAC (Q_RESQ_HALF_SPECL [`G`, `x`] GPOW_GORD)
   >> R_TAC' []
   >> Cases_on `gord G x` >- AG_TAC' []
   >> Cases_on `n`
   >- (rpt (DISCH_THEN K_TAC)
       >> AG_TAC [GORD_GID_UNIQUE]
       >> MP_TAC (Q_RESQ_HALF_SPEC `G` GINV_GID)
       >> G_TAC' [])
   >> STRIP_TAC
   >> DISCH_THEN (MP_TAC o Q.SPEC `SUC n'`)
   >> Simplify []
   >> STRIP_TAC
   >> Suff `ginv G x = gpow G x (SUC n')` >- Simplify []
   >> G_TAC [IS_GINV]
   >> POP_ASSUM K_TAC
   >> POP_ASSUM MP_TAC
   >> G_TAC []
QED

(* non-interactive mode
*)
