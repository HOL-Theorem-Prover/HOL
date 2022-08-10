open HolKernel Parse boolLib;

val _ = ParseExtras.temp_loose_equality()

open bossLib listTheory hurdUtils subtypeTools res_quanTools
     res_quanTheory pred_setTheory extra_pred_setTheory arithContext
     relationTheory ho_proverTools extra_listTheory
     listContext arithmeticTheory subtypeTheory extra_numTheory
     pred_setContext;

val _ = new_theory "group";

val EXISTS_DEF = boolTheory.EXISTS_DEF;

infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op!! = op REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val S_TAC = !! (POP_ASSUM MP_TAC) ++ !! RESQ_STRIP_TAC;

val std_pc = precontext_mergel [arith_pc, list_pc, pred_set_pc];
val std_c = precontext_compile std_pc;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS std_c;

val Strip = S_TAC;
val Simplify = R_TAC;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

val group_def = Define
  `group (gp : 'a -> bool, star) =
   star IN (gp -> gp -> gp) /\
   (!x y z :: gp. star (star x y) z = star x (star y z)) /\
   ?e :: gp. !x :: gp. ?ix :: gp. (star e x = x) /\ (star ix x = e)`;

val gset_def = Define `gset (gp : 'a -> bool, star : 'a -> 'a -> 'a) = gp`;

val gop_def = Define `gop (gp : 'a -> bool, star : 'a -> 'a -> 'a) = star`;

val gid_def = Define
  `gid (G : ('a -> bool) # ('a -> 'a -> 'a)) =
   @e :: gset G. !x :: gset G. ?ix :: gset G.
     (gop G e x = x) /\ (gop G ix x = e)`;

val ginv_def = Define
  `ginv (G : ('a -> bool) # ('a -> 'a -> 'a)) x =
   @ix :: gset G. gop G ix x = gid G`;

val prod_group_def = Define
  `prod_group G H =
   (gset G CROSS gset H, \ (x1, y1) (x2, y2). (gop G x1 x2, gop H y1 y2))`;

val subgroup_def = Define
  `subgroup G H =
  H IN group /\ gset H SUBSET gset G /\ !g h :: gset H. gop H g h = gop G g h`;

val psubgroup_def = Define
  `psubgroup G H = H IN subgroup G /\ gset H PSUBSET gset G`;

val gpow_def = Define
  `(gpow G g 0 = gid G) /\ (gpow G g (SUC n) = gop G g (gpow G g n))`;

val group_homo_def = Define
  `group_homo G H f
   = f IN (gset G -> gset H) /\
     (!x y :: gset G. gop H (f x) (f y) = f (gop G x y))`;

val group_iso_def = Define
  `group_iso G H f = f IN group_homo G H /\ BIJ f (gset G) (gset H)`;

val lcoset_def = Define
  `lcoset G g H = IMAGE (gop G g) (gset H)`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val IN_GROUP = store_thm
  ("IN_GROUP",
   ``!G.
       G IN group =
       gop G IN (gset G -> gset G -> gset G) /\
       (!x y z :: gset G. gop G (gop G x y) z = gop G x (gop G y z)) /\
       ?e :: gset G. !x :: gset G. ?ix :: gset G.
         (gop G e x = x) /\ (gop G ix x = e)``,
   Cases
   ++ R_TAC [group_def, SPECIFICATION, gop_def, gset_def]);

val GROUP = store_thm
  ("GROUP",
   ``!G.
       G IN group =
       gop G IN (gset G -> gset G -> gset G) /\
       (!x y z :: gset G. gop G (gop G x y) z = gop G x (gop G y z)) /\
       gid G IN gset G /\
       ginv G IN (gset G -> gset G) /\
       !x :: gset G. (gop G (gid G) x = x) /\ (gop G (ginv G x) x = gid G)``,
   R_TAC [IN_GROUP]
   ++ ONCE_REWRITE_TAC [RES_EXISTS_ALT]
   ++ BETA_TAC
   ++ R_TAC [GSYM gid_def]
   ++ STRIP_TAC
   ++ Suff
   `(!x :: gset G. ?ix :: gset G.
      (gop G (gid G) x = x) /\ (gop G ix x = gid G)) =
    (ginv G IN (gset G -> gset G) /\
      !x :: gset G. (gop G (gid G) x = x) /\ (gop G (ginv G x) x = gid G))`
   >> PROVE_TAC []
   ++ R_TAC [IN_FUNSET]
   ++ Suff
   `!x :: gset G.
      (?ix :: gset G. (gop G (gid G) x = x) /\ (gop G ix x = gid G)) =
      (ginv G x IN gset G /\ (gop G (gid G) x = x) /\
       (gop G (ginv G x) x = gid G))`
   >> (RESQ_TAC ++ PROVE_TAC [])
   ++ R_TAC [RES_EXISTS_ALT, ginv_def]);

val GSET_SUBTYPE = store_thm
  ("GSET_SUBTYPE",
   ``gset IN (group -> nonempty)``,
   R_TAC [IN_FUNSET, IN_NONEMPTY]
   ++ SET_EQ_TAC
   ++ R_TAC [GROUP]
   ++ PROVE_TAC []);

val GOP_SUBTYPE = store_thm
  ("GOP_SUBTYPE",
   ``gop IN (group --> \G. gset G -> gset G -> gset G)``,
   R_TAC [IN_DFUNSET]
   ++ R_TAC [GROUP]);

val GROUP_ASSOC = store_thm
  ("GROUP_ASSOC",
   ``!G :: group. !x y z :: gset G. gop G (gop G x y) z = gop G x (gop G y z)``,
   S_TAC
   ++ AR_TAC [GROUP]);

val GROUP_LASSOC = store_thm
  ("GROUP_LASSOC",
   ``!G :: group. !x y z :: gset G. gop G x (gop G y z) = gop G (gop G x y) z``,
   S_TAC
   ++ AR_TAC [GROUP]);

val GID_SUBTYPE = store_thm
  ("GID_SUBTYPE",
   ``gid IN (group --> gset)``,
   R_TAC [IN_DFUNSET, GROUP]);

val GROUP_LID = store_thm
  ("GROUP_LID",
   ``!G :: group. !x :: gset G. gop G (gid G) x = x``,
   S_TAC
   ++ AR_TAC [GROUP]);

val GINV_SUBTYPE = store_thm
  ("GINV_SUBTYPE",
   ``ginv IN (group --> \G. gset G -> gset G)``,
   R_TAC [IN_DFUNSET, GROUP]);

val GROUP_LINV = store_thm
  ("GROUP_LINV",
   ``!G :: group. !x :: gset G. gop G (ginv G x) x = gid G``,
   S_TAC
   ++ AR_TAC [GROUP]);

val GROUP_RINV = store_thm
  ("GROUP_RINV",
   ``!G :: group. !x :: gset G. gop G x (ginv G x) = gid G``,
   S_TAC
   ++ Suff `gop G (gid G) (gop G x (ginv G x)) = gid G`
   >> R_TAC [GROUP_LID, GOP_SUBTYPE, GID_SUBTYPE, GINV_SUBTYPE]
   ++ Suff
      `gop G (gop G (ginv G (ginv G x)) (ginv G x)) (gop G x (ginv G x)) =
       gid G`
   >> R_TAC [GROUP_LINV, GOP_SUBTYPE, GID_SUBTYPE, GINV_SUBTYPE]
   ++ Suff
      `gop G (ginv G (ginv G x)) (gop G (ginv G x) (gop G x (ginv G x))) =
       gid G`
   >> R_TAC [GROUP_ASSOC, GOP_SUBTYPE, GID_SUBTYPE, GINV_SUBTYPE]
   ++ Suff
      `gop G (ginv G (ginv G x)) (gop G (gop G (ginv G x) x) (ginv G x)) =
       gid G`
   >> R_TAC [GROUP_ASSOC, GOP_SUBTYPE, GID_SUBTYPE, GINV_SUBTYPE]
   ++ Suff `gop G (ginv G (ginv G x)) (gop G (gid G) (ginv G x)) = gid G`
   >> R_TAC [GROUP_LINV, GOP_SUBTYPE, GID_SUBTYPE, GINV_SUBTYPE]
   ++ Suff `gop G (ginv G (ginv G x)) (ginv G x) = gid G`
   >> R_TAC [GROUP_LID, GOP_SUBTYPE, GID_SUBTYPE, GINV_SUBTYPE]
   >> R_TAC [GROUP_LINV, GOP_SUBTYPE, GID_SUBTYPE, GINV_SUBTYPE]);

val GROUP_RID = store_thm
  ("GROUP_RID",
   ``!G :: group. !x :: gset G. gop G x (gid G) = x``,
   S_TAC
   ++ Suff `gop G x (gop G (ginv G x) x) = x`
   >> R_TAC [GROUP_LINV]
   ++ Suff `gop G (gop G x (ginv G x)) x = x`
   >> R_TAC [GROUP_ASSOC, GINV_SUBTYPE]
   ++ R_TAC [GROUP_RINV, GROUP_LID, GINV_SUBTYPE]);

val GROUP_LCANCEL = store_thm
  ("GROUP_LCANCEL",
   ``!G :: group. !g h h' :: gset G. (gop G g h = gop G g h') = (h = h')``,
   S_TAC
   ++ REVERSE EQ_TAC >> R_TAC []
   ++ S_TAC
   ++ Suff `gop G (gid G) h = gop G (gid G) h'`
   >> R_TAC [GROUP_LID]
   ++ Suff `gop G (gop G (ginv G g) g) h = gop G (gop G (ginv G g) g) h'`
   >> R_TAC [GROUP_LINV]
   ++ R_TAC [GROUP_ASSOC, GINV_SUBTYPE]);

val GROUP_RCANCEL = store_thm
  ("GROUP_RCANCEL",
   ``!G :: group. !g g' h :: gset G. (gop G g h = gop G g' h) = (g = g')``,
   S_TAC
   ++ REVERSE EQ_TAC >> R_TAC []
   ++ S_TAC
   ++ Suff `gop G g (gid G) = gop G g' (gid G)`
   >> R_TAC [GROUP_RID]
   ++ Suff `gop G g (gop G h (ginv G h)) = gop G g' (gop G h (ginv G h))`
   >> R_TAC [GROUP_RINV]
   ++ R_TAC [GROUP_LASSOC, GINV_SUBTYPE]);

val GROUP_LCANCEL_ID = store_thm
  ("GROUP_LCANCEL_ID",
   ``!G :: group. !g h :: gset G. (gop G g h = g) = (h = gid G)``,
   S_TAC
   ++ REVERSE EQ_TAC >> R_TAC [GROUP_RID]
   ++ S_TAC
   ++ Suff `gop G g h = gop G g (gid G)`
   >> R_TAC [GROUP_LCANCEL, GID_SUBTYPE]
   ++ R_TAC [GROUP_RID]);

val GROUP_RCANCEL_ID = store_thm
  ("GROUP_RCANCEL_ID",
   ``!G :: group. !g h :: gset G. (gop G g h = h) = (g = gid G)``,
   S_TAC
   ++ REVERSE EQ_TAC >> R_TAC [GROUP_LID]
   ++ S_TAC
   ++ Suff `gop G g h = gop G (gid G) h`
   >> R_TAC [GROUP_RCANCEL, GID_SUBTYPE]
   ++ R_TAC [GROUP_LID]);

val PROD_GROUP_SET = store_thm
  ("PROD_GROUP_SET",
   ``!G H. gset (prod_group G H) = gset G CROSS gset H``,
   R_TAC [prod_group_def, gset_def]);

val PROD_GROUP_OP = store_thm
  ("PROD_GROUP_OP",
   ``!G H g1 g2 h1 h2.
       gop (prod_group G H) (g1, h1) (g2, h2) = (gop G g1 g2, gop H h1 h2)``,
   R_TAC [prod_group_def, gop_def]);

val IN_ABELIAN = store_thm
  ("IN_ABELIAN",
   ``!G. G IN abelian = abelian G``,
   R_TAC [SPECIFICATION]);

(* Consolidate theorems so far in a simplification context *)

val group1_sc =
  map SC_SIMPLIFICATION
  [] @
  map SC_JUDGEMENT
  [] @
  map SC_SUBTYPE
  [GSET_SUBTYPE,
   GOP_SUBTYPE,
   GID_SUBTYPE,
   GINV_SUBTYPE]

val group1_pc = precontext_add
  ("group1",
   map C_SUBTYPE group1_sc @
   map C_THM
   [GROUP_LCANCEL,
    GROUP_RCANCEL,
    GROUP_LCANCEL_ID,
    GROUP_RCANCEL_ID,
    GROUP_LID,
    GROUP_RID,
    GROUP_LINV,
    GROUP_RINV,
    PROD_GROUP_SET,
    PROD_GROUP_OP])
  std_pc;

val group1_c = precontext_compile group1_pc;

val (G_TAC, AG_TAC, G_TAC', AG_TAC') = SIMPLIFY_TACS group1_c;

(* back to proving theorems *)

val GID_UNIQUE = store_thm
  ("GID_UNIQUE",
   ``!G :: group. !x :: gset G. (gop G x x = x) = (x = gid G)``,
   S_TAC
   ++ G_TAC []);

val IN_SUBGROUP = store_thm
  ("IN_SUBGROUP",
   ``!G H.
       H IN subgroup G =
       H IN group /\ gset H SUBSET gset G /\
       !g h :: gset H. gop H g h = gop G g h``,
   R_TAC [SPECIFICATION, subgroup_def]);

val SUBGROUP_GROUP = store_thm
  ("SUBGROUP_GROUP",
   ``!G H. H IN subgroup G ==> H IN group``,
   R_TAC [IN_SUBGROUP]);

val SUBGROUP_SET = store_thm
  ("SUBGROUP_SET",
   ``!G H. H IN subgroup G ==> gset H SUBSET gset G``,
   R_TAC [IN_SUBGROUP]);

val SUBGROUP_OP = store_thm
  ("SUBGROUP_OP",
   ``!G H. H IN subgroup G ==> !g h :: gset H. gop H g h = gop G g h``,
   R_TAC [IN_SUBGROUP]);

val SUBGROUP_ID = store_thm
  ("SUBGROUP_ID",
   ``!G H. G IN group /\ H IN subgroup G ==> (gid H = gid G)``,
   S_TAC
   ++ ASM_MATCH_MP_TAC [SUBGROUP_GROUP, SUBGROUP_SET, SUBGROUP_OP]
   ++ Know `gid H IN gset G` >> R_TAC [GID_SUBTYPE]
   ++ STRIP_TAC
   ++ Suff `gop G (gid H) (gid H) = gid H`
   >> R_TAC [GID_UNIQUE]
   ++ Suff `gop H (gid H) (gid H) = gid H`
   >> R_TAC [GID_SUBTYPE]
   ++ G_TAC []);

val SUBGROUP_INV = store_thm
  ("SUBGROUP_INV",
   ``!G H.
       G IN group /\ H IN subgroup G ==> !h :: gset H. ginv H h = ginv G h``,
   S_TAC
   ++ ASM_MATCH_MP_TAC [SUBGROUP_GROUP, SUBGROUP_SET, SUBGROUP_OP, SUBGROUP_ID]
   ++ Suff `gop G h (ginv H h) = gop G h (ginv G h)`
   >> G_TAC []
   ++ R_TAC [GROUP_RINV]
   ++ Suff `gop H h (ginv H h) = gid H` >> G_TAC []
   ++ R_TAC [GROUP_RINV]);

val IN_PSUBGROUP = store_thm
  ("IN_PSUBGROUP",
   ``!G H.
       H IN psubgroup G = H IN subgroup G /\ gset H PSUBSET gset G``,
   R_TAC [SPECIFICATION, psubgroup_def]);

val PSUBGROUP_SUBGROUP = store_thm
  ("PSUBGROUP_SUBGROUP",
   ``!G H. H IN psubgroup G ==> H IN subgroup G``,
   R_TAC [IN_PSUBGROUP]);

val PSUBGROUP_PSUBSET = store_thm
  ("PSUBGROUP_PSUBSET",
   ``!G H. H IN psubgroup G ==> gset H PSUBSET gset G``,
   R_TAC [IN_PSUBGROUP]);

(* Consolidate theorems so far in a simplification context *)

val group2_pc = precontext_add
  ("group2",
   map C_FORWARDS
   [SUBGROUP_SET,
    SUBGROUP_GROUP,
    SUBGROUP_OP,
    SUBGROUP_ID,
    SUBGROUP_INV,
    PSUBGROUP_SUBGROUP,
    PSUBGROUP_PSUBSET])
  group1_pc;

val group2_c = precontext_compile group2_pc;

val (G_TAC, AG_TAC, G_TAC', AG_TAC') = SIMPLIFY_TACS group2_c;

(* back to proving theorems *)

val GPOW = store_thm
  ("GPOW",
   ``!G. !g :: gset G.
       (gpow G g 0 = gid G) /\
       (!n. gpow G g (SUC n) = gop G g (gpow G g n))``,
   R_TAC [gpow_def]);

val GPOW_SUBTYPE = store_thm
  ("GPOW_SUBTYPE",
   ``gpow IN (group --> \G. gset G -> UNIV -> gset G)``,
   R_TAC [IN_DFUNSET, IN_FUNSET]
   ++ S_TAC
   ++ Induct_on `x`
   ++ G_TAC [GPOW]);

val GPOW_ID = store_thm
  ("GPOW_ID",
   ``!G :: group. !n. gpow G (gid G) n = gid G``,
   S_TAC
   ++ Induct_on `n`
   ++ G_TAC [GPOW]);

val GPOW_ADD = store_thm
  ("GPOW_ADD",
   ``!(G :: group) (g :: gset G) m n.
       gpow G g (m + n) = gop G (gpow G g m) (gpow G g n)``,
   S_TAC
   ++ Induct_on `m`
   ++ G_TAC [GPOW, GPOW_SUBTYPE, ADD_CLAUSES, GROUP_ASSOC]);

val GPOW_MULT = store_thm
  ("GPOW_MULT",
   ``!(G :: group) (g :: gset G) m n.
       gpow G g (m * n) = gpow G (gpow G g m) n``,
   S_TAC
   ++ Induct_on `n` >> G_TAC [GPOW, GPOW_SUBTYPE]
   ++ G_TAC [GPOW, MULT_CLAUSES, GPOW_ADD, GPOW_SUBTYPE]);

val IN_GROUP_HOMO = store_thm
  ("IN_GROUP_HOMO",
   ``!G H f.
       f IN group_homo G H =
       f IN (gset G -> gset H) /\
       !x y :: gset G. gop H (f x) (f y) = f (gop G x y)``,
   R_TAC [SPECIFICATION, group_homo_def]);

val IN_GROUP_ISO = store_thm
  ("IN_GROUP_ISO",
   ``!G H f.
       f IN group_iso G H = f IN group_homo G H /\ BIJ f (gset G) (gset H)``,
   R_TAC [SPECIFICATION, group_iso_def]);

val GROUP_SURJ_HOMO_GROUP = store_thm
  ("GROUP_SURJ_HOMO_GROUP",
   ``!(G :: group) H (f :: group_homo G H).
       SURJ f (gset G) (gset H) ==> H IN group``,
   S_TAC
   ++ Cases_on `H`
   ++ R_TAC [IN_GROUP]
   ++ AR_TAC [GROUP, IN_GROUP_HOMO, SURJ_ALT, gset_def, gop_def]
   ++ S_TAC <<
   [R_TAC [IN_FUNSET]
    ++ S_TAC
    ++ Q.PAT_X_ASSUM `!y :: q. P y`
        (fn th =>
         (MP_TAC o RESQ_SPEC ``x':'b``) th ++ (MP_TAC o RESQ_SPEC ``x:'b``) th)
    ++ S_TAC
    ++ R_TAC [],
    Q.PAT_X_ASSUM `!y :: q. P y`
      (fn th =>
       (MP_TAC o RESQ_SPEC ``x:'b``) th
        ++ (MP_TAC o RESQ_SPEC ``y:'b``) th
        ++ (MP_TAC o RESQ_SPEC ``z:'b``) th)
    ++ S_TAC
    ++ R_TAC [],
    RESQ_EXISTS_TAC ``f (gid G)``
    ++ S_TAC >> R_TAC []
    ++ RESQ_EXISTS_TAC
         ``(f :'a -> 'b) (ginv G (@y. y IN gset G /\ (x = f y)))``
    ++ R_TAC []
    ++ S_TAC <<
    [RW_TAC std_ss [IN_FUNSET]
     ++ Suff `(@y. y IN gset G /\ (x = f y)) IN gset G`
     >> (S_TAC ++ G_TAC [])
     ++ Q.PAT_X_ASSUM `!y::q. P y` (MP_TAC o RESQ_SPEC ``x : 'b``)
     ++ G_TAC [RES_EXISTS, EXISTS_DEF],
     Q.PAT_X_ASSUM `!y::q. P y` (MP_TAC o RESQ_SPEC ``x:'b``)
     ++ S_TAC
     ++ R_TAC [],
     Q.PAT_X_ASSUM `!y::q. P y` (MP_TAC o RESQ_SPEC ``x:'b``)
     ++ R_TAC [RES_EXISTS]
     ++ DISCH_THEN (fn th => MP_TAC th ++ MP_TAC th)
     ++ RESQ_STRIP_TAC
     ++ simpLib.ASM_SIMP_TAC std_ss [EXISTS_DEF]
     ++ Q.SPEC_TAC (`@y. y IN gset G /\ (f x' = f y)`, `y`)
     ++ simpLib.SIMP_TAC std_ss []
     ++ S_TAC
     ++ R_TAC []]]);

val GROUP_ISO_GROUP = store_thm
  ("GROUP_ISO_GROUP",
   ``!(G :: group) H (f :: group_iso G H). H IN group``,
   S_TAC
   ++ AR_TAC [IN_GROUP_ISO, BIJ_DEF]
   ++ MP_TAC GROUP_SURJ_HOMO_GROUP
   ++ RESQ_TAC
   ++ ho_PROVE_TAC []);

val LCOSETS_EQUAL_OR_DISJOINT = store_thm
  ("LCOSETS_EQUAL_OR_DISJOINT",
   ``!G :: group. !H :: subgroup G. !g1 g2 :: gset G.
       (lcoset G g1 H = lcoset G g2 H)
       \/ DISJOINT (lcoset G g1 H) (lcoset G g2 H)``,
   S_TAC
   ++ REVERSE
      (Cases_on `?g. g IN lcoset G g1 H
                     /\ g IN lcoset G g2 H`)
   >> (R_TAC [DISJOINT_DEF]
       ++ !! (POP_ASSUM MP_TAC)
       ++ RW_TAC std_ss [EXTENSION, IN_INTER, NOT_IN_EMPTY]
       ++ PROVE_TAC [])
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [DISJOINT_DEF]
   ++ Suff `!v. v IN lcoset G g1 H = v IN lcoset G g2 H`
   >> (!! (POP_ASSUM MP_TAC)
       ++ RW_TAC std_ss [EXTENSION, IN_INTER, NOT_IN_EMPTY]
       ++ PROVE_TAC [])
   ++ NTAC 4 (POP_ASSUM MP_TAC)
   ++ Q.SPEC_TAC (`g2`, `g2`)
   ++ Q.SPEC_TAC (`g1`, `g1`)
   ++ Suff `!g1 g2 :: gset G.
                  g IN lcoset G g1 H /\
                  g IN lcoset G g2 H ==>
                  !v.
                    v IN lcoset G g1 H ==>
                    v IN lcoset G g2 H`
   >> (RESQ_TAC ++ ho_PROVE_TAC [])
   ++ G_TAC [lcoset_def]
   ++ AR_TAC [IN_IMAGE]
   ++ S_TAC
   ++ RW_TAC std_ss []
   ++ Q.EXISTS_TAC `gop H x' (gop H (ginv H x) x'')`
   ++ REVERSE CONJ_TAC >> R_TAC [SUBGROUP_GROUP, GOP_SUBTYPE, GINV_SUBTYPE]
   ++ G_TAC []
   ++ Suff `gop G g1 x'' = gop G (gop G (gop G g2 x') (ginv G x)) x''`
   >> G_TAC [GROUP_ASSOC]
   ++ G_TAC []
   ++ G_TAC [GROUP_ASSOC]);

(* Consolidate all theorems in a theory simplification context *)

val group3_sc =
  map SC_SIMPLIFICATION
  [] @
  map SC_JUDGEMENT
  [] @
  map SC_SUBTYPE
  [GPOW_SUBTYPE];

val group3_pc = precontext_add
  ("group3",
   map C_SUBTYPE group3_sc @
   map C_THM
   [GPOW,
    GPOW_ID,
    GPOW_ADD,
    GPOW_MULT])
  group2_pc;

val group3_c = precontext_compile group3_pc;

val (G_TAC, AG_TAC, G_TAC', AG_TAC') = SIMPLIFY_TACS group3_c;

(* back to proving theorems *)

val GROUP_SET_EMPTY = store_thm
  ("GROUP_SET_EMPTY",
   ``!G :: group. ~(gset G = {})``,
   S_TAC
   ++ AR_TAC [IN_GROUP]);

val GINV_UNIQUE = store_thm
  ("GINV_UNIQUE",
   ``!G :: group. !g h :: gset G.
       (gop G g h = gid G) \/ (gop G h g = gid G) ==> (ginv G g = h)``,
   S_TAC <<
   [Suff `gop G g (ginv G g) = gop G g h` >> G_TAC []
    ++ ASM_REWRITE_TAC []
    ++ G_TAC [],
    Suff `gop G (ginv G g) g = gop G h g` >> G_TAC []
    ++ ASM_REWRITE_TAC []
    ++ G_TAC []]);

val IS_GINV = store_thm
  ("IS_GINV",
   ``!G :: group. !g h :: gset G.
       (ginv G g = h) = (gop G g h = gid G) \/ (gop G h g = gid G)``,
   S_TAC
   ++ EQ_TAC >> DISCH_THEN (fn th => G_TAC [SYM th])
   ++ S_TAC <<
   [MATCH_MP_TAC (Q_RESQ_SPECL [`G`, `g`, `h`] GINV_UNIQUE)
    ++ R_TAC [],
    MATCH_MP_TAC (Q_RESQ_SPECL [`G`, `g`, `h`] GINV_UNIQUE)
    ++ R_TAC []]);

val GINV_GID = store_thm
  ("GINV_GID",
   ``!G :: group. ginv G (gid G) = gid G``,
   S_TAC
   ++ R_TAC [IS_GINV, GID_SUBTYPE]
   ++ G_TAC []);

val GPOW_1 = store_thm
  ("GPOW_1",
   ``!G :: group. !g :: gset G. gpow G g 1 = g``,
   S_TAC
   ++ REWRITE_TAC [GSYM SUC_0, gpow_def]
   ++ G_TAC []);

val GINV_GOP = store_thm
  ("GINV_GOP",
   ``!G :: group. !g h :: gset G.
       ginv G (gop G g h) = gop G (ginv G h) (ginv G g)``,
   S_TAC
   ++ G_TAC [IS_GINV]
   ++ DISJ1_TAC
   ++ Suff `gop G g (gop G (gop G h (ginv G h)) (ginv G g)) = gid G`
   >> G_TAC [GROUP_ASSOC]
   ++ G_TAC []);

val GPOW_COMM = store_thm
  ("GPOW_COMM",
   ``!G :: group. !g :: gset G. !n.
       gop G g (gpow G g n) = gop G (gpow G g n) g``,
   NTAC 2 RESQ_STRIP_TAC
   ++ Induct >> G_TAC []
   ++ G_TAC []
   ++ Suff `gop G (gop G g (gpow G g n)) g = gop G (gpow G g n) (gop G g g)`
   >> G_TAC [GROUP_ASSOC]
   ++ ASM_REWRITE_TAC []
   ++ G_TAC [GROUP_ASSOC]);

val GINV_GPOW = store_thm
  ("GINV_GPOW",
   ``!G :: group. !g :: gset G. !n. ginv G (gpow G g n) = gpow G (ginv G g) n``,
   NTAC 2 RESQ_STRIP_TAC
   ++ Induct >> G_TAC [GINV_GID]
   ++ G_TAC []
   ++ G_TAC [GINV_GOP]
   ++ ONCE_REWRITE_TAC [EQ_SYM_EQ]
   ++ G_TAC [GPOW_COMM]);

val GINV_EQ_GID = store_thm
  ("GINV_EQ_GID",
   ``!G :: group. !g :: gset G. (ginv G g = gid G) = (g = gid G)``,
   S_TAC
   ++ REVERSE EQ_TAC >> G_TAC [GINV_GID]
   ++ S_TAC
   ++ Suff `gop G (ginv G g) g = gop G (ginv G g) (gid G)`
   >> G_TAC []
   ++ POP_ASSUM
   (fn th =>
    R_TAC [GROUP_RID, GINV_SUBTYPE, GROUP_LINV]
    ++ ASSUME_TAC th)
   ++ G_TAC []);

val SET_SUBGROUP = store_thm
  ("SET_SUBGROUP",
   ``!s G.
       G IN group /\ s SUBSET gset G /\ ~(s = {}) /\
       ginv G IN (s -> s) /\ gop G IN (s -> s -> s) ==>
       (s, gop G) IN subgroup G``,
   Strip
   ++ Simplify [IN_SUBGROUP, gset_def, gop_def, IN_GROUP]
   ++ Strip >> G_TAC [GROUP_ASSOC]
   ++ Q_RESQ_EXISTS_TAC `gid G`
   ++ STRONG_CONJ_TAC
   >> (Know `?x. x IN s`
       >> (Q.PAT_X_ASSUM `~(s = {})` MP_TAC
           ++ SET_EQ_TAC
           ++ Simplify [NOT_IN_EMPTY])
       ++ Strip
       ++ Know `ginv G x IN s` >> R_TAC' []
       ++ Strip
       ++ Know `gop G (ginv G x) x IN s` >> R_TAC' []
       ++ G_TAC [])
   ++ Strip
   ++ Q_RESQ_EXISTS_TAC `ginv G x`
   ++ G_TAC' []);

val GROUP_HOMO_GID = store_thm
  ("GROUP_HOMO_GID",
   ``!f G H.
       f IN group_homo G H /\ G IN group /\ H IN group ==>
       (f (gid G) = gid H)``,
   Simplify [IN_GROUP_HOMO]
   ++ Strip
   ++ Q.PAT_X_ASSUM `!x :: P. M x`
      (MP_TAC o Q_RESQ_HALF_SPECL [`gid G`, `gid G`])
   ++ G_TAC' []);

val GROUP_HOMO_GPOW = store_thm
  ("GROUP_HOMO_GPOW",
   ``!f G H g n.
       f IN group_homo G H /\ G IN group /\ H IN group /\ g IN gset G ==>
       (f (gpow G g n) = gpow H (f g) n)``,
   Strip
   ++ Q.PAT_X_ASSUM `f IN x`
      (fn th => MP_TAC th ++ Simplify [IN_GROUP_HOMO] ++ ASSUME_TAC th)
   ++ Strip
   ++ Induct_on `n` >> G_TAC [GROUP_HOMO_GID]
   ++ POP_ASSUM (ASSUME_TAC o SYM)
   ++ G_TAC []);

val PROD_GROUP_SUBTYPE = store_thm
  ("PROD_GROUP_SUBTYPE",
   ``prod_group IN (group -> group -> group)``,
   Simplify [IN_FUNSET]
   ++ Strip
   ++ Simplify [IN_GROUP, PROD_GROUP_OP, PROD_GROUP_SET, IN_FUNSET, IN_CROSS]
   ++ Strip <<
   [Cases_on `x'''`
    ++ Cases_on `x''`
    ++ AG_TAC' [],
    Cases_on `x'''`
    ++ Cases_on `x''`
    ++ AG_TAC' [],
    Cases_on `x''`
    ++ Cases_on `y`
    ++ Cases_on `z`
    ++ AG_TAC' [IN_CROSS, GROUP_ASSOC],
    Q_RESQ_EXISTS_TAC `(gid x', gid x)`
    ++ G_TAC' [IN_CROSS]
    ++ Strip
    ++ Cases_on `x''`
    ++ Q_RESQ_EXISTS_TAC `(ginv x' q, ginv x r)`
    ++ AG_TAC' [IN_CROSS]]);

val PROD_GROUP_GID = store_thm
  ("PROD_GROUP_GID",
   ``!G H :: group. gid (prod_group G H) = (gid G, gid H)``,
   Strip
   ++ MATCH_MP_TAC EQ_SYM
   ++ Know `(gid G, gid H) IN gset (prod_group G H)` >> G_TAC' [IN_CROSS]
   ++ Know `prod_group G H IN group` >> G_TAC' [PROD_GROUP_SUBTYPE]
   ++ Strip
   ++ Simplify [GSYM GID_UNIQUE]
   ++ MATCH_MP_TAC EQ_SYM
   ++ G_TAC []);

val PROD_GROUP_GPOW = store_thm
  ("PROD_GROUP_GPOW",
   ``!G H :: group. !g :: gset G. !h :: gset H. !n.
       gpow (prod_group G H) (g, h) n = (gpow G g n, gpow H h n)``,
   Strip
   ++ Know `(g,h) IN gset (prod_group G H)`
   >> G_TAC' [PROD_GROUP_SET, IN_CROSS]
   ++ Strip
   ++ Induct_on `n` >> G_TAC [PROD_GROUP_GID]
   ++ G_TAC [PROD_GROUP_OP]);

(* non-interactive mode
*)
val _ = export_theory ();
