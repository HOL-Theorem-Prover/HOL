open HolKernel boolLib integerTheory

infix THEN THENL THENC THEN1 |-> ++
infix 8 by

local open listTheory in end;

val _ = new_theory "Omega";

open simpLib boolSimps SingleStep BasicProvers TotalDefn

val ARITH_ss = numSimps.ARITH_ss

val _ = augment_srw_ss [intSimps.INT_REDUCE_ss, numSimps.REDUCE_ss]

val FORALL_PROD = pairTheory.FORALL_PROD;

val MAP2_def = Define
  `(MAP2 pad f [] [] = []) /\
   (MAP2 pad f [] (y::ys) = (f pad y) :: MAP2 pad f [] ys) /\
   (MAP2 pad f (x::xs) [] = (f x pad) :: MAP2 pad f xs []) /\
   (MAP2 pad f (x::xs) (y::ys) = f x y :: MAP2 pad f xs ys)`;

val MAP2_zero_ADD = store_thm(
  "MAP2_zero_ADD",
  ``!xs. (MAP2 0i $+ [] xs = xs) /\
         (MAP2 0 $+ xs [] = xs)``,
  Induct THEN ASM_SIMP_TAC bool_ss [MAP2_def, INT_ADD_LID, INT_ADD_RID]);

val sumc_def = Define
  `(sumc _ [] = 0i) /\
   (sumc [] _ = 0) /\
   (sumc (c::cs) (v::vs) = c * v + sumc cs vs)`;

val sumc_ind = theorem "sumc_ind"

val sumc_thm = store_thm(
  "sumc_thm",
  ``!cs vs c v.
       (sumc [] vs = 0) /\
       (sumc cs [] = 0) /\
       (sumc (c::cs) (v::vs) = c * v + sumc cs vs)``,
  HO_MATCH_MP_TAC sumc_ind THEN SIMP_TAC bool_ss [sumc_def]);

val sumc_ADD = store_thm(
  "sumc_ADD",
  ``!cs vs ds. sumc cs vs + sumc ds vs =
               sumc (MAP2 0 $+ cs ds) vs``,
  HO_MATCH_MP_TAC sumc_ind THEN REPEAT STRIP_TAC THENL [
    SIMP_TAC bool_ss [sumc_thm, MAP2_def, INT_ADD_LID],
    SIMP_TAC bool_ss [sumc_thm, MAP2_def, INT_ADD_LID],
    SIMP_TAC bool_ss [sumc_thm, MAP2_def, INT_ADD_LID,
                      MAP2_zero_ADD],
    Cases_on `ds` THEN
    SIMP_TAC bool_ss [sumc_thm, MAP2_zero_ADD, INT_ADD_RID, MAP2_def,
                      INT_RDISTRIB] THEN
    POP_ASSUM (fn th => REWRITE_TAC [GSYM th]) THEN
    CONV_TAC (AC_CONV(INT_ADD_ASSOC, INT_ADD_COMM))
  ]);

val sumc_MULT = store_thm(
  "sumc_MULT",
  ``!cs vs f. f * sumc cs vs = sumc (MAP (\x. f * x) cs) vs``,
  Induct THEN SRW_TAC [][sumc_thm] THEN
  Cases_on `vs` THEN SRW_TAC [][sumc_thm, INT_LDISTRIB]);

val modhat_def = Define
  `modhat x y = x - y * ((2 * x + y) / (2 * y))`;

val MAP_MAP = prove(
  ``!l f g. MAP f (MAP g l) = MAP (f o g) l``,
  Induct THEN SRW_TAC [][combinTheory.o_THM]);

val MAP2_MAP = prove(
  ``!l f g pad. MAP2 pad f (MAP g l) l = MAP (\x. f (g x) x) l``,
  Induct THEN SRW_TAC [][MAP2_def]);

val MAP_MAP2 = prove(
  ``!l f g h. MAP (\x. f (g x) (h x)) l = MAP2 0i f (MAP g l) (MAP h l)``,
  Induct THEN SRW_TAC [][MAP2_def]);

val equality_removal0 = prove(
  ``!c x cs vs.
       0 < c /\ (c * x + sumc cs vs = 0) ==>
       ?s. x = ~(c + 1) * s + sumc (MAP (\x. modhat x (c + 1)) cs) vs``,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [INT_ADD_COMM] THEN
  SIMP_TAC (srw_ss()) [GSYM int_sub, INT_EQ_SUB_LADD, GSYM INT_NEG_LMUL] THEN
  CONV_TAC (BINDER_CONV (LHS_CONV (REWR_CONV INT_ADD_COMM))) THEN
  SIMP_TAC (srw_ss()) [GSYM INT_EQ_SUB_LADD, int_sub] THEN
  Q_TAC SUFF_TAC
     `(c + 1) int_divides sumc (MAP (\x. modhat x (c + 1)) cs) vs + ~x` THEN1
     PROVE_TAC [INT_DIVIDES, INT_MUL_COMM] THEN
  Q_TAC SUFF_TAC
     `c * (c + 1) int_divides
        c * (sumc  (MAP (\x. modhat x (c+ 1)) cs) vs + ~x)` THEN1
     PROVE_TAC [INT_DIVIDES_MUL_BOTH, INT_LT_REFL] THEN
  CONV_TAC (RAND_CONV (SIMP_CONV bool_ss [INT_LDISTRIB, GSYM INT_NEG_RMUL,
                                          sumc_MULT, MAP_MAP,
                                          combinTheory.o_DEF])) THEN
  `~(c * x) = sumc cs vs` by
      FULL_SIMP_TAC (srw_ss()) [GSYM INT_EQ_SUB_LADD] THEN
  ASM_SIMP_TAC (srw_ss()) [sumc_ADD, MAP2_MAP, modhat_def, int_sub] THEN
  CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) [INT_LDISTRIB,
                                             GSYM INT_ADD_ASSOC])) THEN
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [INT_ADD_COMM])) THEN
  SIMP_TAC (srw_ss()) [GSYM INT_ADD_ASSOC] THEN
  SIMP_TAC (srw_ss()) [BETA_RULE
                         (Q.INST [`h` |-> `\x. x + c * x`]
                              (INST_TYPE [alpha |-> ``:int``]
                                         (SPEC_ALL MAP_MAP2)))] THEN
  SIMP_TAC (srw_ss()) [GSYM sumc_ADD, INT_NEG_RMUL] THEN

  `!f c l. MAP (\x:int. c * f x) l = MAP (\x. c * x) (MAP f l)`
     by SIMP_TAC (srw_ss()) [MAP_MAP, combinTheory.o_DEF] THEN
  POP_ASSUM (fn th =>
                CONV_TAC (RAND_CONV (LAND_CONV
                                       (LAND_CONV (HO_REWR_CONV th))))) THEN
  ASM_SIMP_TAC (srw_ss()) [GSYM sumc_MULT] THEN
  `!x c. x + c * x = (c + 1) * x`
    by SIMP_TAC (srw_ss()) [INT_RDISTRIB, INT_ADD_COMM] THEN
  ASM_REWRITE_TAC [GSYM sumc_MULT] THEN
  Q_TAC SUFF_TAC `~(c + 1 = 0) /\ c int_divides sumc cs vs` THEN1
    PROVE_TAC [INT_DIVIDES_MUL_BOTH, INT_MUL_COMM] THEN
  REPEAT STRIP_TAC THENL [
    FULL_SIMP_TAC (srw_ss()) [GSYM INT_EQ_SUB_LADD],
    PROVE_TAC [INT_DIVIDES, INT_MUL_COMM, INT_DIVIDES_NEG, INT_NEG_LMUL]
  ]);

val equality_removal = store_thm(
  "equality_removal",
  ``!c x cs vs.
       0 < c ==>
       ((c * x + sumc cs vs = 0) =
        ?s. (x = ~(c + 1) * s + sumc (MAP (\x. modhat x (c + 1)) cs) vs) /\
            (c * x + sumc cs vs = 0))``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN SRW_TAC [][] THEN
  MATCH_MP_TAC equality_removal0 THEN SRW_TAC [][]);

val evalleft_def = Define
  `(evalleft (x:int) [] = T) /\
   (evalleft x ((c,y) :: cs) = &c * x <= y /\ evalleft x cs)`
val evalright_def = Define
  `(evalright (x:int) [] = T) /\
   (evalright x ((c,y) :: cs) = y <= &c * x /\ evalright x cs)`

val lt_mono = prove(
  ``!n (x:int) y. 0 < n ==> (&n * x < & n * y = x < y)``,
  REPEAT STRIP_TAC THEN
  CONV_TAC (BINOP_CONV (LAND_CONV (REWR_CONV (GSYM INT_ADD_LID)))) THEN
  REWRITE_TAC [GSYM INT_LT_SUB_LADD, GSYM INT_SUB_LDISTRIB] THEN
  SRW_TAC [ARITH_ss][INT_MUL_SIGN_CASES]);

val le_mono = prove(
  ``!n (x:int) y. 0 < n ==> (&n * x <= & n * y = x <= y)``,
  REPEAT STRIP_TAC THEN
  CONV_TAC (BINOP_CONV (LAND_CONV (REWR_CONV (GSYM INT_ADD_LID)))) THEN
  REWRITE_TAC [GSYM INT_LT_SUB_LADD, GSYM INT_SUB_LDISTRIB] THEN
  SRW_TAC [ARITH_ss][INT_MUL_SIGN_CASES, INT_LE_LT, lt_mono]);

val bigger_satisfies_rights = store_thm(
  "bigger_satisfies_rights",
  ``!rights x y. evalright x rights /\ x < y ==> evalright y rights``,
  Induct THEN SRW_TAC [][evalright_def] THEN
  Cases_on `h` THEN FULL_SIMP_TAC (srw_ss()) [evalright_def] THEN
  Q_TAC SUFF_TAC `r <= &q * y` THEN1 PROVE_TAC [] THEN
  `(q = 0) \/ 0 < q` by SRW_TAC [ARITH_ss][]
     THEN1 FULL_SIMP_TAC (srw_ss())[] THEN
  PROVE_TAC [INT_LET_TRANS, lt_mono, INT_LE_LT]);

val LE_SIGN_CASES = prove(
  ``!x y:int. 0 <= x * y   =   0 <= x /\ 0 <= y \/ x <= 0 /\ y <= 0``,
  REWRITE_TAC [INT_LE_LT, INT_MUL_SIGN_CASES, INT_ENTIRE,
               Q.ISPEC `0i` EQ_SYM_EQ] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  PROVE_TAC [INT_LT_NEGTOTAL, INT_NEG_GT0]);

val LE_LT1 = prove(
  ``!x y. x <= y = x < y + 1``,
  REPEAT GEN_TAC THEN EQ_TAC THEN1 REWRITE_TAC [INT_LT_ADD1] THEN
  Q.SPECL_THEN [`y`, `x`] ASSUME_TAC
               (REWRITE_RULE [DE_MORGAN_THM] INT_DISCRETE) THEN
  REWRITE_TAC [IMP_DISJ_THM, GSYM INT_NOT_LT] THEN PROVE_TAC []);

val M_LE_XM = prove(
  ``!m x. m <= m * x =   0 <= m /\ 0 < x \/ m <= 0 /\ x <= 1``,
  REPEAT GEN_TAC THEN
  CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV (GSYM INT_MUL_RID) THENC
                                  REWR_CONV (GSYM INT_ADD_LID)))) THEN
  REWRITE_TAC [GSYM INT_LE_SUB_LADD, GSYM INT_SUB_LDISTRIB,
               LE_SIGN_CASES] THEN
  SRW_TAC [] [INT_LE_SUB_LADD, INT_LE_SUB_RADD] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  FULL_SIMP_TAC (srw_ss()) [LE_LT1]);

val fst_nzero_def = Define `fst_nzero x = 0n < FST x`
val fst1_def = Define`fst1 x = (FST x = 1n)`

val _ = augment_srw_ss [rewrites [fst1_def, fst_nzero_def]]

val onlyrights_satisfiable = store_thm(
  "onlyrights_satisfiable",
  ``!rights. EVERY fst_nzero rights ==> ?x. evalright x rights``,
  Induct THEN SRW_TAC [][evalright_def] THEN
  Cases_on `h` THEN
  FULL_SIMP_TAC (srw_ss()) [evalright_def] THEN
  Q.EXISTS_TAC `if x < r / &q + 1 then r / &q + 1 else x` THEN
  MP_TAC (Q.SPEC `&q` INT_DIVISION) THEN
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss)[] THEN
  DISCH_THEN (Q.SPEC_THEN `r` STRIP_ASSUME_TAC) THEN
  Q.ABBREV_TAC `rdivq = r / &q` THEN
  Q.ABBREV_TAC `rmodq = r % &q` THEN
  COND_CASES_TAC THENL [
    ASM_SIMP_TAC(srw_ss() ++ ARITH_ss) [INT_LDISTRIB, INT_MUL_COMM] THEN
    PROVE_TAC [bigger_satisfies_rights],
    FULL_SIMP_TAC (srw_ss())[INT_NOT_LT] THEN
    MATCH_MP_TAC INT_LE_TRANS THEN Q.EXISTS_TAC `rdivq * &q + &q` THEN
    ASM_SIMP_TAC (srw_ss()) [INT_LT_IMP_LE] THEN
    `&q * (rdivq + 1) <= &q * x` by PROVE_TAC [le_mono] THEN
    POP_ASSUM MP_TAC THEN
    SIMP_TAC (srw_ss() ++ ARITH_ss) [INT_LDISTRIB, INT_MUL_COMM]
  ]);

val rshadow_row_def = Define
  `(rshadow_row (leftc, (lefty:int)) [] = T) /\
   (rshadow_row (leftc, lefty) ((rightc, righty) :: rs) =
      (&leftc * righty <= &rightc * lefty) /\ rshadow_row (leftc, lefty) rs)`;
val real_shadow_def = Define
  `(real_shadow [] rights = T) /\
   (real_shadow (left::ls) rights =
      rshadow_row left rights /\ real_shadow ls rights)`;

val rshadow_row_FOLDL = prove(
  ``!rights lc ly.
       rshadow_row (lc,ly) rights =
       FOLDL (\a r. &lc * SND r <= &(FST r) * ly /\ a) T rights``,
  CONV_TAC (STRIP_QUANT_CONV
              (LHS_CONV (REWR_CONV (tautLib.TAUT_PROVE ``p = T /\ p``)))) THEN
  Q.SPEC_TAC (`T`, `acc`) THEN CONV_TAC SWAP_VARS_CONV THEN
  Induct THEN SIMP_TAC (srw_ss())[rshadow_row_def, FORALL_PROD] THEN
  POP_ASSUM (fn th => REWRITE_TAC [GSYM th]) THEN PROVE_TAC []);

val singleton_real_shadow = store_thm(
  "singleton_real_shadow",
  ``!c L x.
       &c * x <= L /\ 0 < c ==>
       !rights.
          EVERY fst_nzero rights /\ evalright x rights ==>
          rshadow_row (c,L) rights``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  Induct THEN ASM_SIMP_TAC (srw_ss()) [evalright_def, rshadow_row_def,
                                       FORALL_PROD] THEN
  CONV_TAC (RENAME_VARS_CONV ["rc", "ry"]) THEN
  REPEAT STRIP_TAC THEN
  `&c * ry <= &c * (&rc * x)` by PROVE_TAC [le_mono] THEN
  `&rc * (&c * x) <= &rc * L` by PROVE_TAC [le_mono] THEN
  `&c * (&rc * x) <= &rc * L` by PROVE_TAC [INT_MUL_COMM, INT_MUL_ASSOC] THEN
  PROVE_TAC [INT_LE_TRANS]);

val real_shadow_revimp_lefts1 = store_thm(
  "real_shadow_revimp_lefts1",
  ``!lefts rights L x.
        rshadow_row (1, L) rights /\ evalright x rights /\
        evalleft x lefts /\ EVERY fst_nzero rights /\
        EVERY fst1 lefts ==>
        ?x. x <= L /\ evalleft x lefts /\ evalright x rights``,
  Induct THENL [
    SIMP_TAC (srw_ss())[evalleft_def] THEN
    Induct THENL [
      SRW_TAC [][rshadow_row_def, evalright_def] THEN PROVE_TAC [INT_LE_REFL],
      ASM_SIMP_TAC (srw_ss()) [rshadow_row_def, evalright_def,
                               FORALL_PROD] THEN
      PROVE_TAC [bigger_satisfies_rights, INT_LE_LT, INT_LE_REFL]
    ],
    SIMP_TAC (srw_ss())[FORALL_PROD, evalleft_def] THEN
    REPEAT STRIP_TAC THEN
    `?y. y <= L /\ evalleft y lefts /\ evalright y rights` by PROVE_TAC [] THEN
    Q.EXISTS_TAC `if x < y then x else y` THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC (srw_ss()) [] THENL [
      PROVE_TAC [INT_LTE_TRANS, INT_LE_LT],
      PROVE_TAC [INT_NOT_LT, INT_LE_TRANS]
    ]
  ]);

val real_shadow_revimp_rights1 = store_thm(
  "real_shadow_revimp_rights1",
  ``!lefts rights c L x.
       0 < c /\ rshadow_row (c, L) rights /\ evalleft x lefts /\
       evalright x rights /\ EVERY fst_nzero lefts /\
       EVERY fst1 rights ==>
       ?x. &c * x <= L /\ evalleft x lefts /\ evalright x rights``,
  Induct THENL [
    SIMP_TAC (srw_ss())[evalleft_def] THEN
    Induct THENL [
      SRW_TAC [][rshadow_row_def, evalright_def] THEN
      Q.EXISTS_TAC `L / &c` THEN
      Q.SPEC_THEN `&c` MP_TAC INT_DIVISION THEN
      SRW_TAC [ARITH_ss][] THEN
      POP_ASSUM (Q.SPEC_THEN `L` STRIP_ASSUME_TAC) THEN
      Q.ABBREV_TAC `Ldivc = L / &c` THEN
      Q.ABBREV_TAC `Lmodc = L % &c` THEN
      ASM_SIMP_TAC (srw_ss())[INT_MUL_COMM],
      ASM_SIMP_TAC (srw_ss())[FORALL_PROD, rshadow_row_def,
                              evalright_def] THEN
      REPEAT STRIP_TAC THEN
      `?y. &c * y <= L /\ evalright y rights` by PROVE_TAC[] THEN
      Q.EXISTS_TAC `if y < p_2 then p_2 else y` THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC (srw_ss())[] THENL [
        PROVE_TAC [bigger_satisfies_rights],
        PROVE_TAC [INT_NOT_LT]
      ]
    ],
    SIMP_TAC (srw_ss()) [FORALL_PROD, evalleft_def] THEN
    CONV_TAC (RENAME_VARS_CONV ["c1", "L1"]) THEN
    REPEAT STRIP_TAC THEN
    `?y. &c * y <= L /\ evalleft y lefts /\ evalright y rights`
      by PROVE_TAC[] THEN
    Q.EXISTS_TAC `if x < y then x else y` THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC (srw_ss())[] THENL [
      `&c * x < &c * y` by PROVE_TAC [lt_mono] THEN
      PROVE_TAC [INT_LTE_TRANS, INT_LE_LT],
      `&c1 * y <= &c1 * x` by PROVE_TAC [le_mono, INT_NOT_LT] THEN
      PROVE_TAC [INT_LE_TRANS]
    ]
  ]);

val lemma =
    SIMP_RULE bool_ss [AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM]
              singleton_real_shadow

val real_shadow_always_implied = store_thm(
  "real_shadow_always_implied",
  ``!lefts rights x.
        evalleft x lefts /\ evalright x rights /\
        EVERY fst_nzero lefts /\ EVERY fst_nzero rights ==>
        real_shadow lefts rights``,
  Induct THEN ASM_SIMP_TAC (srw_ss())[evalleft_def, real_shadow_def,
                                      FORALL_PROD] THEN
  PROVE_TAC [lemma]);

val IMP_AND_THM =
    tautLib.TAUT_PROVE ``!p q r. p ==> q /\ r = (p ==> q) /\ (p ==> r)``


val exact_shadow_case = store_thm(
  "exact_shadow_case",
  ``!lefts rights.
      EVERY fst_nzero lefts /\ EVERY fst_nzero rights ==>
      (EVERY fst1 lefts \/ EVERY fst1 rights) ==>
      ((?x. evalleft x lefts /\ evalright x rights) =
       real_shadow lefts rights)``,
  SIMP_TAC (srw_ss()) [EQ_IMP_THM, IMP_AND_THM, FORALL_AND_THM] THEN
  REPEAT CONJ_TAC THENL [
    PROVE_TAC [real_shadow_always_implied],
    (* "reverse" implication case *)
    SIMP_TAC (srw_ss()) [DISJ_IMP_THM, FORALL_AND_THM, IMP_AND_THM] THEN
    CONJ_TAC THENL [
      (* lefts all one *)
      Induct THENL [
        SRW_TAC [][evalleft_def, real_shadow_def, onlyrights_satisfiable],
        SIMP_TAC (srw_ss()) [evalleft_def, real_shadow_def,
                             FORALL_PROD] THEN
        SRW_TAC [][] THEN
        FIRST_X_ASSUM (Q.SPECL_THEN [`rights`] MP_TAC) THEN
        ASM_SIMP_TAC (srw_ss())[] THEN STRIP_TAC THEN
        PROVE_TAC [real_shadow_revimp_lefts1]
      ],
      (* rights all one *)
      Induct THENL [
        SRW_TAC [][evalleft_def, real_shadow_def, onlyrights_satisfiable],
        SIMP_TAC (srw_ss()) [evalleft_def, real_shadow_def,
                             FORALL_PROD]  THEN
        REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss())[] THEN
        FIRST_X_ASSUM (Q.SPECL_THEN [`rights`] MP_TAC) THEN
        ASM_SIMP_TAC (srw_ss())[] THEN
        PROVE_TAC [real_shadow_revimp_rights1]
      ]
    ]
  ]);

val dark_shadow_row_def =
  Define`(dark_shadow_row (c,L:int) [] = T) /\
         (dark_shadow_row (c,L) ((d,R)::t) =
              ~(?i. &c * &d * i < &c * R /\ &c * R <= &d * L /\
                    &d * L < &c * &d * (i + 1)) /\ dark_shadow_row (c,L) t)`;

val dark_shadow_condition_def =
  Define`(dark_shadow_condition [] rights = T) /\
         (dark_shadow_condition ((c,L)::lefts) rights =
            dark_shadow_row (c,L) rights /\
            dark_shadow_condition lefts rights)`;

val constraint_mid_existence = prove(
  ``!x i j.  0 < x ==>
             ((!k. x * k < i ==> x * (k + 1) <= j) =
              (?k. i <= x * k /\ x * k <= j))``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    Q.SPEC_THEN `x` MP_TAC INT_DIVISION THEN
    `~(x = 0)` by PROVE_TAC [INT_LT_REFL] THEN
    `~(x < 0)` by PROVE_TAC [INT_LT_ANTISYM] THEN
    ASM_SIMP_TAC (srw_ss())[] THEN
    DISCH_THEN (Q.SPEC_THEN `j` STRIP_ASSUME_TAC) THEN
    Q.ABBREV_TAC `jdivx = j / x` THEN
    Q.ABBREV_TAC `jmodx = j % x` THEN
    SPOSE_NOT_THEN (Q.SPEC_THEN `jdivx` MP_TAC) THEN
    ASM_SIMP_TAC (srw_ss()) [INT_MUL_COMM] THEN
    FIRST_X_ASSUM (Q.SPEC_THEN `jdivx` MP_TAC) THEN
    Q_TAC SUFF_TAC `~(x * (jdivx + 1) <= j)` THEN1
      PROVE_TAC [INT_NOT_LE, INT_MUL_COMM] THEN
    ASM_SIMP_TAC (srw_ss()) [INT_LDISTRIB, INT_ADD_COMM, INT_MUL_COMM] THEN
    ASM_SIMP_TAC (srw_ss()) [INT_NOT_LE],
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    FULL_SIMP_TAC (srw_ss()) [INT_NOT_LE] THEN
    `?n. x = &n` by PROVE_TAC [NUM_POSINT_EXISTS, INT_LE_LT] THEN
    POP_ASSUM SUBST_ALL_TAC THEN FULL_SIMP_TAC (srw_ss())[] THEN
    `&n * k' < &n * k` by PROVE_TAC [INT_LTE_TRANS] THEN
    `&n * k < &n * (k' + 1)` by PROVE_TAC [INT_LET_TRANS] THEN
    PROVE_TAC [INT_DISCRETE, lt_mono]
  ]);

val dark_shadowrow_constraint_imp = prove(
  ``!rights lefts c L x.
       0 < c /\ EVERY fst_nzero rights /\
       evalleft x lefts /\ evalright x rights /\ &c * x <= L ==>
       dark_shadow_row (c,L) rights``,
  Induct THENL [
    SRW_TAC [][evalright_def, dark_shadow_row_def],
    SIMP_TAC (srw_ss()) [FORALL_PROD, evalright_def, dark_shadow_row_def] THEN
    CONV_TAC (RENAME_VARS_CONV ["d", "R"]) THEN REPEAT STRIP_TAC THENL [
      `&c * R <= &c * (&d * x)` by PROVE_TAC [le_mono] THEN
      `&d * (&c * x) <= &d * L` by PROVE_TAC [le_mono] THEN
      `&c * R <= (&c * &d) * x /\ (&c * &d) * x <= &d * L` by
         PROVE_TAC [INT_MUL_COMM, INT_MUL_ASSOC] THEN
      `&c * R <= &d * L` by PROVE_TAC [INT_LE_TRANS] THEN
      ASM_SIMP_TAC (srw_ss())[GSYM IMP_DISJ_THM] THEN
      REPEAT STRIP_TAC THEN FULL_SIMP_TAC (srw_ss())[] THEN
      `&(c * d) * i < &(c * d) * x` by PROVE_TAC [INT_LTE_TRANS] THEN
      `&(c * d) * x < &(c * d) * (i + 1)` by PROVE_TAC [INT_LET_TRANS] THEN
      `0 < c * d` by SRW_TAC [][arithmeticTheory.LESS_MULT2] THEN
      `i < x /\ x < i + 1` by PROVE_TAC [lt_mono] THEN
      PROVE_TAC [INT_DISCRETE],
      PROVE_TAC []
    ]
  ]);

val dark_shadow_constraint_implied = prove(
  ``!lefts rights x.
       evalleft x lefts /\ evalright x rights /\
       EVERY fst_nzero lefts /\ EVERY fst_nzero rights ==>
       dark_shadow_condition lefts rights``,
  Induct THENL [
    SRW_TAC [][dark_shadow_condition_def],
    SIMP_TAC (srw_ss()) [FORALL_PROD, evalleft_def,
                         dark_shadow_condition_def] THEN
    PROVE_TAC [dark_shadowrow_constraint_imp]
  ]);

val real_darkrow_implies_evals = prove(
  ``!lefts rights x c L.
       0 < c /\ evalleft x lefts /\ evalright x rights /\
       EVERY fst_nzero lefts /\ EVERY fst_nzero rights /\
       rshadow_row (c,L) rights /\ dark_shadow_row (c,L) rights ==>
       ?y. &c * y <= L /\ evalleft y lefts /\ evalright y rights``,
  Induct THENL [
    SIMP_TAC (srw_ss()) [evalleft_def] THEN
    Induct THENL [
      SIMP_TAC (srw_ss()) [evalright_def, rshadow_row_def,
                           dark_shadow_row_def] THEN REPEAT STRIP_TAC THEN
      Q.EXISTS_TAC `L / &c` THEN
      Q.SPEC_THEN `&c` MP_TAC INT_DIVISION THEN
      SRW_TAC [ARITH_ss][] THEN
      POP_ASSUM (Q.SPEC_THEN `L` STRIP_ASSUME_TAC) THEN
      Q.ABBREV_TAC `Ldivc = L / &c` THEN
      Q.ABBREV_TAC `Lmodc = L % &c` THEN
      ASM_SIMP_TAC (srw_ss())[INT_MUL_COMM],
      SIMP_TAC (srw_ss()) [evalright_def, rshadow_row_def,
                           dark_shadow_row_def, FORALL_PROD] THEN
      CONV_TAC (RENAME_VARS_CONV ["d", "R"]) THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o assert (is_forall o concl)) THEN
      ASM_SIMP_TAC (srw_ss())[GSYM IMP_DISJ_THM] THEN STRIP_TAC THEN
      `?y. &c * y <= L /\ evalright y rights` by PROVE_TAC [] THEN
      `&c * &d * y  <= &d * L` by PROVE_TAC [le_mono, INT_MUL_ASSOC,
                                             INT_MUL_COMM] THEN
      `&c * R <= &c * &d * x` by PROVE_TAC [le_mono, INT_MUL_ASSOC,
                                             INT_MUL_COMM] THEN
      Cases_on `&c * R <= &c * &d * y` THENL [
        Q.EXISTS_TAC `y` THEN ASM_SIMP_TAC (srw_ss()) [] THEN
        PROVE_TAC [le_mono, INT_MUL_COMM, INT_MUL_ASSOC],
        ALL_TAC
      ] THEN
      `0 < &(c * d)` by
         ASM_SIMP_TAC (srw_ss()) [arithmeticTheory.LESS_MULT2] THEN
      `?j. &c * R <= &(c * d) * j /\ &(c * d) * j <= &d * L` by
         PROVE_TAC [constraint_mid_existence, INT_NOT_LT] THEN
      FULL_SIMP_TAC (srw_ss()) [INT_NOT_LE] THEN
      Q.EXISTS_TAC `j` THEN
      `&c * &d * j <= &d * L` by PROVE_TAC [INT_MUL] THEN
      `&c * j <= L` by PROVE_TAC [le_mono, INT_MUL_ASSOC, INT_MUL_COMM] THEN
      `&c * R <= &c * &d * j` by PROVE_TAC [INT_MUL] THEN
      `R <= &d * j` by PROVE_TAC [le_mono, INT_MUL_ASSOC, INT_MUL_COMM] THEN
      Q_TAC SUFF_TAC `y < j` THEN1 PROVE_TAC [bigger_satisfies_rights] THEN
      Q_TAC SUFF_TAC `&d * y < &d * j` THEN1 PROVE_TAC [lt_mono] THEN
      Q_TAC SUFF_TAC `&c * (&d * y) < &c * (&d * j)` THEN1
                                PROVE_TAC [lt_mono] THEN
      MATCH_MP_TAC INT_LTE_TRANS THEN
      Q.EXISTS_TAC `&c * R` THEN
      PROVE_TAC [INT_MUL, INT_MUL_ASSOC, INT_MUL_COMM]
    ],
    SIMP_TAC (srw_ss()) [evalleft_def, FORALL_PROD] THEN
    CONV_TAC (RENAME_VARS_CONV ["d", "L2"]) THEN REPEAT STRIP_TAC THEN
    `?z. &c * z <= L /\ evalleft z lefts /\ evalright z rights` by
       (FIRST_X_ASSUM MATCH_MP_TAC THEN PROVE_TAC []) THEN
    Q.EXISTS_TAC `if x < z then x else z` THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC (srw_ss())[] THENL [
      PROVE_TAC [INT_LTE_TRANS, INT_LE_LT, lt_mono],
      PROVE_TAC [INT_LE_TRANS, INT_NOT_LE, le_mono]
    ]
  ]);


val real_darkcond_implies_evals = prove(
  ``!lefts rights.
       EVERY fst_nzero lefts /\ EVERY fst_nzero rights /\
       real_shadow lefts rights /\ dark_shadow_condition lefts rights ==>
       ?x. evalleft x lefts /\ evalright x rights``,
  Induct THENL [
    SIMP_TAC (srw_ss()) [evalleft_def, onlyrights_satisfiable],
    SIMP_TAC (srw_ss()) [evalleft_def, FORALL_PROD, dark_shadow_condition_def,
                         real_shadow_def] THEN
    CONV_TAC (RENAME_VARS_CONV ["c", "L"]) THEN REPEAT STRIP_TAC THEN
    `?y. evalleft y lefts /\ evalright y rights` by PROVE_TAC [] THEN
    REWRITE_TAC [GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC real_darkrow_implies_evals THEN PROVE_TAC []
  ]);


val basic_shadow_equivalence = store_thm(
  "basic_shadow_equivalence",
  ``!lefts rights.
       EVERY fst_nzero lefts /\ EVERY fst_nzero rights ==>
       ((?x. evalleft x lefts /\ evalright x rights) =
        real_shadow lefts rights /\ dark_shadow_condition lefts rights)``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    CONJ_TAC THEN1
      (MATCH_MP_TAC real_shadow_always_implied THEN PROVE_TAC []) THEN
    PROVE_TAC [dark_shadow_constraint_implied],
    PROVE_TAC [real_darkcond_implies_evals]
  ]);

val _ = export_theory();

