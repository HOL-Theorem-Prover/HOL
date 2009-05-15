open HolKernel Parse boolLib boolSimps
     numLib Prim_rec mnUtils pred_setTheory BasicProvers SingleStep
     metisLib dividesTheory arithmeticTheory

val hol_ss = mn_ss;

fun ARITH q = EQT_ELIM (ARITH_CONV (Parse.Term q));

infix >-

val _ = new_theory "bag";

val _ = type_abbrev("bag", Type`:'a -> num`)
val _ = disable_tyabbrev_printing "bag"
val _ = type_abbrev("multiset", Type`:'a -> num`)
val _ = disable_tyabbrev_printing "multiset"

val _ = print "Defining basic bag operations\n"

val EMPTY_BAG = new_definition (
  "EMPTY_BAG",
  ``(EMPTY_BAG:'a bag) = K 0``);

val EMPTY_BAG_alt = store_thm (
  "EMPTY_BAG_alt",
  ``EMPTY_BAG:'a bag = \x.0``,
  FUN_EQ_TAC THEN SIMP_TAC hol_ss [EMPTY_BAG]);

val BAG_INN = new_definition(
  "BAG_INN",
  ``BAG_INN (e:'a) n b = b e >= n``);

val SUB_BAG = Q.new_definition (
  "SUB_BAG",
  `SUB_BAG b1 b2 = !x n. BAG_INN x n b1 ==> BAG_INN x n b2`);

val PSUB_BAG = Q.new_definition (
  "PSUB_BAG",
  `PSUB_BAG b1 b2 = SUB_BAG b1 b2 /\ ~(b1 = b2)`);


val BAG_IN = new_definition (
  "BAG_IN",
  ``BAG_IN (e:'a) b = BAG_INN e 1 b``);

val BAG_UNION = new_definition ("BAG_UNION",
                ``BAG_UNION b (c:'a bag) = \x. b x + c x``);

val BAG_DIFF = new_definition (
  "BAG_DIFF",
  ``BAG_DIFF b1 (b2:'a bag) = \x. b1 x - b2 x``);

val BAG_INSERT = new_definition (
  "BAG_INSERT",
  Term`BAG_INSERT (e:'a) b = (\x. if (x = e) then b e + 1 else b x)`);

val _ = add_listform {cons = "BAG_INSERT", nilstr = "EMPTY_BAG",
                      separator = [TOK ";", BreakSpace(1,0)],
                      leftdelim = [TOK "{|"], rightdelim = [TOK "|}"],
                      block_info = (PP.INCONSISTENT, 0)};

val BAG_cases = Q.store_thm(
  "BAG_cases",
  `!b. (b = EMPTY_BAG) \/ (?b0 e. b = BAG_INSERT e b0)`,
  SIMP_TAC hol_ss [EMPTY_BAG, BAG_INSERT] THEN
  CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
  SIMP_TAC hol_ss [] THEN GEN_TAC THEN
  Q.ASM_CASES_TAC `!x. b x = 0` THEN ARWT THEN
  FULL_SIMP_TAC hol_ss [] THEN MAP_EVERY Q.EXISTS_TAC [
    `\y. if (y = x) then b x - 1 else b y`, `x`
  ] THEN ASM_SIMP_TAC hol_ss [fCOND_OUT_THM, aCOND_OUT_THM]);

val BAG_INTER = Q.new_definition(
  "BAG_INTER",
  `BAG_INTER b1 b2 = (\x. if (b1 x < b2 x) then b1 x else b2 x)`);

val BAG_MERGE = Q.new_definition(
  "BAG_MERGE",
  `BAG_MERGE b1 b2 = (\x. if (b1 x < b2 x) then b2 x else b1 x)`);

val _ = print "Properties relating BAG_IN(N) to other functions\n"
val BAG_INN_0 = store_thm (
  "BAG_INN_0",
  ``!b e:'a. BAG_INN e 0 b``,
  SIMP_TAC hol_ss [BAG_INN]);

val BAG_INN_LESS = Q.store_thm(
  "BAG_INN_LESS",
  `!b e n m. BAG_INN e n b /\ m < n ==> BAG_INN e m b`,
  SIMP_TAC hol_ss [BAG_INN]);

val BAG_IN_BAG_INSERT = store_thm(
  "BAG_IN_BAG_INSERT",
  ``!b e1 e2:'a.
        BAG_IN e1 (BAG_INSERT e2 b) = (e1 = e2) \/ BAG_IN e1 b``,
  SIMP_TAC hol_ss [BAG_IN, BAG_INN, BAG_INSERT] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN SIMP_TAC hol_ss [])
 before
 export_rewrites ["BAG_IN_BAG_INSERT"];

val BAG_INN_BAG_INSERT = store_thm(
  "BAG_INN_BAG_INSERT",
  ``!b e1 e2:'a. BAG_INN e1 n (BAG_INSERT e2 b) =
                   BAG_INN e1 (n - 1) b /\ (e1 = e2) \/
                   BAG_INN e1 n b``,
  SIMP_TAC hol_ss [BAG_INSERT, BAG_INN] THEN REPEAT GEN_TAC THEN
  EQ_TAC THEN COND_CASES_TAC THEN STRIP_TAC THEN
  ELIM_TAC THEN ASM_SIMP_TAC hol_ss []);


val BAG_INN_BAG_INSERT_STRONG = store_thm (
  "BAG_INN_BAG_INSERT_STRONG",
   ``!b n e1 e2.
        BAG_INN e1 n (BAG_INSERT e2 b) =
          BAG_INN e1 (n - 1) b /\ (e1 = e2) \/ 
          BAG_INN e1 n b /\ ~(e1 = e2)``,
  REWRITE_TAC [BAG_INN_BAG_INSERT] THEN 
  Cases_on `n` THEN SIMP_TAC hol_ss [BAG_INN_0] THEN
  `n' < SUC n'` by bossLib.DECIDE_TAC THEN
  PROVE_TAC[BAG_INN_LESS]);


val BAG_IN_BAG_UNION = Q.store_thm(
  "BAG_IN_BAG_UNION",
  `!b1 b2 e. BAG_IN e (BAG_UNION b1 b2) = BAG_IN e b1 \/ BAG_IN e b2`,
  SIMP_TAC hol_ss [BAG_IN, BAG_UNION, BAG_INN]);

val BAG_INN_BAG_UNION = Q.store_thm(
  "BAG_INN_BAG_UNION",
  `!n e b1 b2. BAG_INN e n (BAG_UNION b1 b2) =
               ?m1 m2. (n = m1 + m2) /\ BAG_INN e m1 b1 /\ BAG_INN e m2 b2`,
  SIMP_TAC hol_ss [BAG_INN, BAG_UNION] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC hol_ss [] THEN
  POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `n` THEN
  INDUCT_THEN numTheory.INDUCTION STRIP_ASSUME_TAC THENL [
    SIMP_TAC hol_ss [],
    REPEAT STRIP_TAC THEN
    IMP_RES_TAC (ARITH_PROVE (Term`!n m. n >= SUC m ==> n >= m`)) THEN
    FULL_SIMP_TAC hol_ss [] THEN
    Q.SUBGOAL_THEN `b1 e > m1 \/ b2 e > m2` STRIP_ASSUME_TAC THENL [
      myCONTR_TAC THEN FULL_SIMP_TAC hol_ss [],
      MAP_EVERY Q.EXISTS_TAC [`SUC m1`, `m2`] THEN
      ASM_SIMP_TAC hol_ss [],
      MAP_EVERY Q.EXISTS_TAC [`m1`, `SUC m2`] THEN
      ASM_SIMP_TAC hol_ss []
    ]
  ]);

val BAG_INN_BAG_MERGE = Q.store_thm (
  "BAG_INN_BAG_MERGE",
  `!n e b1 b2. (BAG_INN e n (BAG_MERGE b1 b2)) =
               (BAG_INN e n b1 \/ BAG_INN e n b2)`,
  SIMP_TAC hol_ss [BAG_INN, BAG_MERGE]);


val BAG_IN_BAG_MERGE = Q.store_thm (
  "BAG_IN_BAG_MERGE",
  `!e b1 b2. (BAG_IN e (BAG_MERGE b1 b2)) =
             (BAG_IN e b1 \/ BAG_IN e b2)`,
  SIMP_TAC hol_ss [BAG_IN, BAG_INN_BAG_MERGE]);

val geq_refl = ARITH_PROVE ``m >= m``

val BAG_EXTENSION = store_thm(
  "BAG_EXTENSION",
  ``!b1 b2. (b1 = b2) = (!n e:'a. BAG_INN e n b1 = BAG_INN e n b2)``,
  CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC [BAG_INN] THEN EQ_TAC THEN STRIP_TAC THENL [
    REPEAT STRIP_TAC THEN ARWT,
    GEN_TAC THEN REWRITE_TAC [
      ARITH_PROVE ``(x = y) = (x >= y) /\ (y >= x)``
    ] THEN CONJ_TAC THENL [
      ASM_REWRITE_TAC [geq_refl],
      POP_ASSUM (fn th => ASM_REWRITE_TAC [geq_refl, GSYM th])]
    ]);

val _ = print "Properties of BAG_INSERT\n"

val BAG_UNION_INSERT = Q.store_thm(
  "BAG_UNION_INSERT",
  `!e b1 b2.
     (BAG_UNION (BAG_INSERT e b1) b2 = BAG_INSERT e (BAG_UNION b1 b2)) /\
     (BAG_UNION b1 (BAG_INSERT e b2) = BAG_INSERT e (BAG_UNION b1 b2))`,
  SIMP_TAC hol_ss [BAG_EXTENSION, BAG_INSERT, BAG_INN, BAG_UNION] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC hol_ss []);


val BAG_INSERT_DIFF = store_thm (
  "BAG_INSERT_DIFF",
  ``!x b. ~(BAG_INSERT x b = b)``,
  REPEAT GEN_TAC THEN
  CONV_TAC (DEPTH_CONV FUN_EQ_CONV THENC NOT_FORALL_CONV) THEN
  SIMP_TAC hol_ss [BAG_INSERT, aCOND_OUT_THM, fCOND_OUT_THM]);

val BAG_INSERT_NOT_EMPTY = store_thm (
  "BAG_INSERT_NOT_EMPTY",
  Term`!x b. ~(BAG_INSERT x b = EMPTY_BAG)`,
  REPEAT GEN_TAC THEN
  CONV_TAC (DEPTH_CONV FUN_EQ_CONV THENC NOT_FORALL_CONV) THEN
  SIMP_TAC hol_ss [EMPTY_BAG_alt, BAG_INSERT, aCOND_OUT_THM,
                   fCOND_OUT_THM] THEN MESON_TAC [])
  before
  export_rewrites ["BAG_INSERT_NOT_EMPTY"]

val BAG_INSERT_ONE_ONE = store_thm(
  "BAG_INSERT_ONE_ONE",
  ``!b1 b2 x:'a.
      (BAG_INSERT x b1 = BAG_INSERT x b2) = (b1 = b2)``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC hol_ss [BAG_INSERT] THEN
  CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (MP_TAC o SPEC ``x':'a``) THEN
  SIMP_TAC hol_ss [] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC hol_ss []);

val C_BAG_INSERT_ONE_ONE = store_thm(
  "C_BAG_INSERT_ONE_ONE",
  ``!x y b. (BAG_INSERT x b = BAG_INSERT y b) = (x = y)``,
  REPEAT STRIP_TAC THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
  EQ_TAC THENL [
    DISCH_THEN (Q.SPEC_THEN `y` MP_TAC) THEN
    SIMP_TAC hol_ss [BAG_INSERT] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC hol_ss [],
    DISCH_THEN SUBST1_TAC THEN GEN_TAC THEN REFL_TAC
  ]);

val BAG_INSERT_commutes = store_thm(
  "BAG_INSERT_commutes",
  ``!b e1 e2. BAG_INSERT e1 (BAG_INSERT e2 b) =
                BAG_INSERT e2 (BAG_INSERT e1 b)``,
  REWRITE_TAC [BAG_EXTENSION] THEN
  SIMP_TAC hol_ss [BAG_INN_BAG_INSERT] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
  ELIM_TAC THEN ARWT);

val BAG_DECOMPOSE = store_thm
("BAG_DECOMPOSE",
 ``!e b. BAG_IN e b ==> ?b'. b = BAG_INSERT e b'``,
 REPEAT STRIP_TAC THEN 
 Q.EXISTS_TAC `BAG_DIFF b {|e|}` THEN POP_ASSUM MP_TAC THEN
 RW_TAC hol_ss [BAG_INSERT,BAG_DIFF,EMPTY_BAG,FUN_EQ_THM,BAG_IN,BAG_INN] THEN
 RW_TAC hol_ss []);

val _ = print "Properties of BAG_UNION\n";

val BAG_UNION_LEFT_CANCEL = store_thm(
  "BAG_UNION_LEFT_CANCEL",
  ``!b b1 b2:'a -> num. (BAG_UNION b b1 = BAG_UNION b b2) = (b1 = b2)``,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC hol_ss [BAG_UNION] THEN
  STRIP_TAC THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN
  POP_ASSUM (MP_TAC o C AP_THM ``x:'a``) THEN
  SIMP_TAC hol_ss []);

val COMM_BAG_UNION = store_thm(
  "COMM_BAG_UNION",
  ``!b1 b2. BAG_UNION b1 b2 = BAG_UNION b2 b1``,
  REWRITE_TAC [BAG_UNION] THEN
  REPEAT STRIP_TAC THEN FUN_EQ_TAC THEN SIMP_TAC hol_ss []);
val bu_comm = COMM_BAG_UNION;

val ASSOC_BAG_UNION = store_thm(
  "ASSOC_BAG_UNION",
  ``!b1 b2 b3. BAG_UNION b1 (BAG_UNION b2 b3)
                 =
                 BAG_UNION (BAG_UNION b1 b2) b3``,
  REWRITE_TAC [BAG_UNION] THEN
  REPEAT STRIP_TAC THEN FUN_EQ_TAC THEN SIMP_TAC hol_ss []);

val _ = print "Definition and properties of BAG_DELETE\n"
val BAG_DELETE = new_definition (
  "BAG_DELETE",
  ``BAG_DELETE b0 (e:'a) b = (b0 = BAG_INSERT e b)``);

val BAG_DELETE_EMPTY = store_thm(
  "BAG_DELETE_EMPTY",
  ``!(e:'a) b. ~(BAG_DELETE EMPTY_BAG e b)``,
  SIMP_TAC hol_ss [BAG_DELETE] THEN
  ACCEPT_TAC (GSYM BAG_INSERT_NOT_EMPTY));

val BAG_DELETE_commutes = store_thm(
  "BAG_DELETE_commutes",
  ``!b0 b1 b2 e1 e2:'a.
         BAG_DELETE b0 e1 b1 /\ BAG_DELETE b1 e2 b2 ==>
         ?b'. BAG_DELETE b0 e2 b' /\ BAG_DELETE b' e1 b2``,
  SIMP_TAC hol_ss [BAG_DELETE] THEN
  ACCEPT_TAC BAG_INSERT_commutes);

val BAG_DELETE_11 = store_thm(
  "BAG_DELETE_11",
  ``!b0 (e1:'a) e2 b1 b2.
         BAG_DELETE b0 e1 b1 /\ BAG_DELETE b0 e2 b2 ==>
         ((e1 = e2) = (b1 = b2))``,
  REWRITE_TAC [BAG_DELETE] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
  STRIP_TAC THEN ELIM_TAC THENL [
    IMP_RES_TAC BAG_INSERT_ONE_ONE THEN ARWT,
    IMP_RES_TAC C_BAG_INSERT_ONE_ONE THEN ARWT
  ]);

val BAG_INN_BAG_DELETE = store_thm(
  "BAG_INN_BAG_DELETE",
  Term`!b n e. BAG_INN e n b /\ n > 0 ==> ?b'. BAG_DELETE b e b'`,
  SIMP_TAC hol_ss [BAG_INN, BAG_DELETE, BAG_INSERT] THEN
  REPEAT STRIP_TAC THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
  SIMP_TAC hol_ss [fCOND_OUT_THM, aCOND_OUT_THM] THEN
  EXISTS_TAC ``\x. if x = e then b e - 1 else b x`` THEN
  ASM_SIMP_TAC hol_ss []);

val BAG_IN_BAG_DELETE = store_thm(
  "BAG_IN_BAG_DELETE",
  Term`!b e:'a. BAG_IN e b ==> ?b'. BAG_DELETE b e b'`,
  MESON_TAC [BAG_INN_BAG_DELETE, ARITH_PROVE (Term`1 > 0`), BAG_IN]);

val BAG_DELETE_INSERT = Q.store_thm(
  "BAG_DELETE_INSERT",
  `!x y b1 b2.
      BAG_DELETE (BAG_INSERT x b1) y b2 ==>
      (x = y) /\ (b1 = b2) \/ (?b3. BAG_DELETE b1 y b3) /\ ~(x = y)`,
  SIMP_TAC hol_ss [BAG_DELETE] THEN REPEAT STRIP_TAC THEN
  Q.ASM_CASES_TAC `x = y` THEN ARWT THENL [
    FULL_SIMP_TAC hol_ss [BAG_INSERT_ONE_ONE],
    Q.SUBGOAL_THEN `BAG_IN y b1`
      (STRIP_ASSUME_TAC o
       MATCH_MP (REWRITE_RULE [BAG_DELETE] BAG_IN_BAG_DELETE))
    THENL [
      ASM_MESON_TAC [BAG_IN_BAG_INSERT],
      ELIM_TAC THEN SIMP_TAC hol_ss [BAG_INSERT_ONE_ONE]
    ]
  ]);

val BAG_DELETE_BAG_IN_up = store_thm(
  "BAG_DELETE_BAG_IN_up",
  ``!b0 b e:'a. BAG_DELETE b0 e b ==>
                  !e'. BAG_IN e' b ==> BAG_IN e' b0``,
  REWRITE_TAC [BAG_DELETE] THEN REPEAT STRIP_TAC THEN ELIM_TAC THEN
  ASM_REWRITE_TAC [BAG_IN_BAG_INSERT]);

val BAG_DELETE_BAG_IN_down = store_thm(
  "BAG_DELETE_BAG_IN_down",
  ``!b0 b e1 e2:'a.
         BAG_DELETE b0 e1 b /\ ~(e1 = e2) /\ BAG_IN e2 b0 ==>
         BAG_IN e2 b``,
  SIMP_TAC hol_ss [BAG_DELETE, BAG_IN_BAG_INSERT, LEFT_AND_OVER_OR,
                   DISJ_IMP_THM]);

val BAG_DELETE_BAG_IN = store_thm(
  "BAG_DELETE_BAG_IN",
  ``!b0 b e:'a. BAG_DELETE b0 e b ==> BAG_IN e b0``,
  SIMP_TAC hol_ss [BAG_IN_BAG_INSERT, BAG_DELETE]);

val BAG_DELETE_concrete = store_thm(
  "BAG_DELETE_concrete",
  ``!b0 b e. BAG_DELETE b0 e b =
               b0 e > 0 /\ (b = \x. if (x = e) then b0 e - 1 else b0 x)``,
  REPEAT STRIP_TAC THEN REWRITE_TAC [BAG_DELETE, BAG_INSERT] THEN EQ_TAC
  THEN STRIP_TAC THEN ELIM_TAC THEN
  CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
  ASM_SIMP_TAC hol_ss [fCOND_OUT_THM, aCOND_OUT_THM]);

val BAG_DELETE_TWICE = store_thm(
  "BAG_DELETE_TWICE",
  ``!b0 e1 e2 b1 b2.
         BAG_DELETE b0 e1 b1 /\ BAG_DELETE b0 e2 b2 /\ ~(b1 = b2) ==>
         ?b. BAG_DELETE b1 e2 b /\ BAG_DELETE b2 e1 b``,
  REPEAT STRIP_TAC THEN
  Q.SUBGOAL_THEN `~(e1 = e2)` ASSUME_TAC THENL [
    ASM_MESON_TAC [BAG_DELETE_11],
    FULL_SIMP_TAC hol_ss [BAG_DELETE_concrete]
  ] THEN FUN_EQ_TAC THEN ASM_SIMP_TAC hol_ss [] THEN
  REPEAT COND_CASES_TAC THEN RWT THEN ELIM_TAC THEN RWT);

val SING_BAG = new_definition(
  "SING_BAG",
  ``SING_BAG (b:'a->num) = ?x. b = BAG_INSERT x EMPTY_BAG``);

val SING_BAG_THM = store_thm(
  "SING_BAG_THM",
  ``!e:'a. SING_BAG (BAG_INSERT e EMPTY_BAG)``,
  MESON_TAC [SING_BAG]);

val EL_BAG = new_definition(
  "EL_BAG",
  ``EL_BAG (e:'a) = BAG_INSERT e EMPTY_BAG``);

val EL_BAG_11 = Q.store_thm(
  "EL_BAG_11",
  `!x y. (EL_BAG x = EL_BAG y) ==> (x = y)`,
  SIMP_TAC hol_ss [EL_BAG, BAG_INSERT, EMPTY_BAG] THEN
  REPEAT GEN_TAC THEN CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
  SIMP_TAC hol_ss [] THEN
  DISCH_THEN (Q.SPEC_THEN `y` MP_TAC) THEN SIMP_TAC hol_ss [] THEN
  SIMP_TAC hol_ss [aCOND_OUT_THM, fCOND_OUT_THM]);

val EL_BAG_INSERT_squeeze0 = prove(
  Term`!x b y. (EL_BAG x = BAG_INSERT y b) ==> (b = EMPTY_BAG)`,
  SIMP_TAC hol_ss [EL_BAG, BAG_INSERT, EMPTY_BAG] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN (ASSUME_TAC o SIMP_RULE hol_ss [FUN_EQ_THM]) THEN
  FUN_EQ_TAC THEN SIMP_TAC hol_ss [] THEN
  FIRST_ASSUM (Q.SPEC_THEN `x'` MP_TAC) THEN
  REPEAT COND_CASES_TAC THEN ELIM_TAC THEN SIMP_TAC hol_ss [] THEN
  FIRST_ASSUM
    (Q.SPEC_THEN `y`
                 (MP_TAC o SIMP_RULE hol_ss [Q.ASSUME `~(x = y)`])) THEN
  SIMP_TAC hol_ss []);

val EL_BAG_INSERT_squeeze = Q.store_thm(
  "EL_BAG_INSERT_squeeze",
  `!x b y. (EL_BAG x = BAG_INSERT y b) ==> (x = y) /\ (b = EMPTY_BAG)`,
  REPEAT STRIP_TAC THEN IMP_RES_TAC EL_BAG_INSERT_squeeze0 THEN
  ASM_MESON_TAC [EL_BAG, EL_BAG_11]);

val SING_EL_BAG = store_thm(
  "SING_EL_BAG",
  ``!e:'a. SING_BAG (EL_BAG e)``,
  REWRITE_TAC [EL_BAG, SING_BAG_THM]);

val BAG_INSERT_UNION = store_thm(
  "BAG_INSERT_UNION",
  ``!b e. BAG_INSERT e b = BAG_UNION (EL_BAG e) b``,
  REPEAT GEN_TAC THEN FUN_EQ_TAC THEN
  SIMP_TAC hol_ss [
    BAG_UNION, BAG_INSERT, EL_BAG, EMPTY_BAG] THEN
  COND_CASES_TAC THEN ELIM_TAC THEN SIMP_TAC hol_ss []);

val one_equal =
  ARITH_PROVE (Term`(1 = n + m) = (n = 1) /\ (m = 0) \/ (m = 1) /\ (n = 0)`)
val BAG_INSERT_EQ_UNION = Q.store_thm(
  "BAG_INSERT_EQ_UNION",
  `!e b1 b2 b. (BAG_INSERT e b = BAG_UNION b1 b2) ==>
               BAG_IN e b1 \/ BAG_IN e b2`,
  SIMP_TAC hol_ss [BAG_EXTENSION, BAG_INN_BAG_UNION, BAG_IN,
                   BAG_INN_BAG_INSERT] THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM (Q.SPECL_THEN [`1`, `e`]
                          (STRIP_ASSUME_TAC o
                           SIMP_RULE hol_ss [BAG_INN_0, one_equal])) THEN
  ELIM_TAC THEN ASM_SIMP_TAC hol_ss []);

val BAG_DELETE_SING = store_thm(
  "BAG_DELETE_SING",
  ``!b e. BAG_DELETE b e EMPTY_BAG ==> SING_BAG b``,
  MESON_TAC [SING_BAG, BAG_DELETE]);

val NOT_IN_EMPTY_BAG = store_thm(
  "NOT_IN_EMPTY_BAG",
  ``!x:'a. ~(BAG_IN x EMPTY_BAG)``,
  SIMP_TAC hol_ss [BAG_IN, BAG_INN, EMPTY_BAG])
  before
  export_rewrites ["NOT_IN_EMPTY_BAG"];

val BAG_INN_EMPTY_BAG = Q.store_thm(
  "BAG_INN_EMPTY_BAG",
  `!e n. BAG_INN e n EMPTY_BAG = (n = 0)`,
  SIMP_TAC hol_ss [BAG_INN, EMPTY_BAG, EQ_IMP_THM])
  before
  export_rewrites ["BAG_INN_EMPTY_BAG"];

val MEMBER_NOT_EMPTY = store_thm(
  "MEMBER_NOT_EMPTY",
  ``!b. (?x. BAG_IN x b) = ~(b = EMPTY_BAG)``,
  SIMP_TAC hol_ss [BAG_IN,BAG_INN,EMPTY_BAG_alt] THEN
  CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
  SIMP_TAC hol_ss [ARITH_PROVE ``(x >= 1) = ~(x = 0)``]);

val _ = print "Properties of SUB_BAG\n"
val geq_lemma = prove(
  ``(!n. a >= n ==> b >= n) = (b >= a)``,
  EQ_TAC THENL [
    DISCH_THEN (SPEC ``a:num`` >- SIMP_RULE hol_ss [] >-
                ASSUME_TAC) THEN carwt,
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC hol_ss []
  ]);
val ZGTN = ARITH_PROVE (Term`!n. 0 >= n = (n = 0)`)

val SUB_BAG_EMPTY = store_thm (
  "SUB_BAG_EMPTY",
  ``(!b:'a->num. SUB_BAG EMPTY_BAG b) /\
      (!b:'a->num. SUB_BAG b EMPTY_BAG = (b = EMPTY_BAG))``,
  REPEAT STRIP_TAC THEN
  SIMP_TAC hol_ss [EMPTY_BAG, SUB_BAG, BAG_INN, geq_lemma] THEN
  EQ_TAC THEN STRIP_TAC THENL [
    FUN_EQ_TAC THEN
    POP_ASSUM (fn th => SIMP_TAC hol_ss [SPEC_ALL th]),
    ELIM_TAC THEN SIMP_TAC hol_ss []
  ]);

val SUB_BAG_REFL = store_thm(
  "SUB_BAG_REFL",
  ``!(b:'a -> num). SUB_BAG b b``,
  REWRITE_TAC [SUB_BAG]);

val PSUB_BAG_IRREFL = store_thm(
  "PSUB_BAG_IRREFL",
  ``!(b:'a -> num). ~(PSUB_BAG b b)``,
  REWRITE_TAC [PSUB_BAG]);

val SUB_BAG_ANTISYM = store_thm(
  "SUB_BAG_ANTISYM",
  ``!(b1:'a -> num) b2. SUB_BAG b1 b2 /\ SUB_BAG b2 b1 ==> (b1 = b2)``,
  REWRITE_TAC [SUB_BAG, BAG_INN] THEN REPEAT STRIP_TAC THEN
  FUN_EQ_TAC THEN
  MATCH_MP_TAC arithmeticTheory.LESS_EQUAL_ANTISYM THEN
  REWRITE_TAC [ARITH_PROVE ``x <= y = y >= x``] THEN
  CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN CONV_TAC ARITH_CONV);

val PSUB_BAG_ANTISYM = store_thm(
  "PSUB_BAG_ANTISYM",
  ``!(b1:'a -> num) b2. ~(PSUB_BAG b1 b2 /\ PSUB_BAG b2 b1)``,
  MESON_TAC [PSUB_BAG, SUB_BAG_ANTISYM]);

val SUB_BAG_TRANS = store_thm(
  "SUB_BAG_TRANS",
  ``!b1 b2 b3. SUB_BAG (b1:'a->num) b2 /\ SUB_BAG b2 b3 ==>
                 SUB_BAG b1 b3``,
  MESON_TAC [SUB_BAG, BAG_INN]);

val PSUB_BAG_TRANS = store_thm(
  "PSUB_BAG_TRANS",
  ``!(b1:'a -> num) b2 b3. PSUB_BAG b1 b2 /\ PSUB_BAG b2 b3 ==>
                             PSUB_BAG b1 b3``,
  MESON_TAC [PSUB_BAG, SUB_BAG_TRANS, SUB_BAG_ANTISYM]);


val PSUB_BAG_SUB_BAG = store_thm(
  "PSUB_BAG_SUB_BAG",
  ``!(b1:'a->num) b2. PSUB_BAG b1 b2 ==> SUB_BAG b1 b2``,
  SIMP_TAC hol_ss [PSUB_BAG]);

val PSUB_BAG_NOT_EQ = store_thm(
  "PSUB_BAG_NOT_EQ",
  ``!(b1:'a -> num) b2. PSUB_BAG b1 b2 ==> ~(b1 = b2)``,
  SIMP_TAC hol_ss [PSUB_BAG]);

val SUB_BAG_LEQ = store_thm(
  "SUB_BAG_LEQ",
  ``!b1 b2:'a -> num. SUB_BAG b1 b2 = !x. b1 x <= b2 x``,
  SIMP_TAC hol_ss [SUB_BAG, BAG_INN, geq_lemma] THEN
  SIMP_TAC hol_ss [arithmeticTheory.GREATER_EQ]);

val _ = print "Properties of BAG_DIFF\n";

val BAG_DIFF_EMPTY = store_thm(
  "BAG_DIFF_EMPTY",
  ``(!b. BAG_DIFF b b = EMPTY_BAG) /\
     (!b. BAG_DIFF b EMPTY_BAG = b) /\
     (!b. BAG_DIFF EMPTY_BAG b = EMPTY_BAG) /\
     (!b1 b2.
        SUB_BAG b1 b2 ==> (BAG_DIFF b1 b2 = EMPTY_BAG))``,
  SIMP_TAC hol_ss [BAG_DIFF,EMPTY_BAG,SUB_BAG,BAG_INN,geq_lemma] THEN
  REPEAT STRIP_TAC THEN FUN_EQ_TAC THEN
  ASSUM_LIST (fn thl => SIMP_TAC hol_ss (map SPEC_ALL thl)));

val BAG_DIFF_EMPTY_simple = save_thm(
  "BAG_DIFF_EMPTY_simple",
  LIST_CONJ (List.take(CONJUNCTS BAG_DIFF_EMPTY, 3)))
  before
  export_rewrites ["BAG_DIFF_EMPTY_simple"];

val BAG_DIFF_INSERT_same = Q.store_thm(
  "BAG_DIFF_INSERT_same",
  `!x b1 b2. BAG_DIFF (BAG_INSERT x b1) (BAG_INSERT x b2) =
             BAG_DIFF b1 b2`,
  SIMP_TAC hol_ss [BAG_DIFF, SUB_BAG, BAG_INN, geq_lemma,
                   BAG_INSERT] THEN
  REPEAT GEN_TAC THEN FUN_EQ_TAC THEN SIMP_TAC hol_ss [] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC hol_ss [])
  before
  export_rewrites ["BAG_DIFF_INSERT_same"];

val BAG_DIFF_INSERT = Q.store_thm(
  "BAG_DIFF_INSERT",
  `!x b1 b2.
      ~(BAG_IN x b1) ==>
      (BAG_DIFF (BAG_INSERT x b2) b1 = BAG_INSERT x (BAG_DIFF b2 b1))`,
  SIMP_TAC hol_ss [BAG_DIFF, SUB_BAG, BAG_INN, geq_lemma,
                   BAG_INSERT, BAG_IN] THEN REPEAT STRIP_TAC THEN
  FUN_EQ_TAC THEN SIMP_TAC hol_ss [] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC hol_ss []);

val NOT_IN_BAG_DIFF = Q.store_thm(
  "NOT_IN_BAG_DIFF",
  `!x b1 b2. ~(BAG_IN x b1) ==>
            (BAG_DIFF b1 (BAG_INSERT x b2) = BAG_DIFF b1 b2)`,
  SIMP_TAC hol_ss [BAG_INSERT, BAG_DIFF, BAG_IN, BAG_INN, BAG_EXTENSION,
                   ZGTN, aCOND_OUT_THM, fCOND_OUT_THM]);

val BAG_UNION_EMPTY = store_thm(
  "BAG_UNION_EMPTY",
  ``(!b. BAG_UNION b EMPTY_BAG = b) /\
     (!b. BAG_UNION EMPTY_BAG b = b) /\
     (!b1 b2. (BAG_UNION b1 b2 = EMPTY_BAG) =
              (b1 = EMPTY_BAG) /\ (b2 = EMPTY_BAG))``,
  SIMP_TAC (hol_ss ++ ETA_ss) [BAG_UNION, EMPTY_BAG] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN (REPEAT_TCL STRIP_THM_THEN (CONV_RULE FUN_EQ_CONV >-
              SIMP_RULE hol_ss [] >- ASSUME_TAC)) THEN
  REPEAT STRIP_TAC THEN FUN_EQ_TAC THEN
  ASSUM_LIST (fn thl => SIMP_TAC hol_ss (map SPEC_ALL thl)))
  before
  export_rewrites ["BAG_UNION_EMPTY"]

val BAG_UNION_DIFF = store_thm(
  "BAG_UNION_DIFF",
  ``!X Y Z.
        SUB_BAG Z Y ==>
        (BAG_UNION X (BAG_DIFF Y Z) = BAG_DIFF (BAG_UNION X Y) Z) /\
        (BAG_UNION (BAG_DIFF Y Z) X = BAG_DIFF (BAG_UNION X Y) Z)``,
  SIMP_TAC hol_ss [BAG_UNION,BAG_INN,SUB_BAG,BAG_DIFF,geq_lemma] THEN
  REPEAT STRIP_TAC THEN FUN_EQ_TAC THEN
  POP_ASSUM (fn th => SIMP_TAC hol_ss [SPEC_ALL th]));

val BAG_DIFF_2L = store_thm(
  "BAG_DIFF_2L",
  ``!X Y Z:'a->num.
         BAG_DIFF (BAG_DIFF X Y) Z = BAG_DIFF X (BAG_UNION Y Z)``,
  SIMP_TAC hol_ss [BAG_UNION,BAG_INN,SUB_BAG,BAG_DIFF]);

val BAG_DIFF_2R = store_thm(
  "BAG_DIFF_2R",
  ``!A B C:'a->num.
         SUB_BAG C B  ==>
         (BAG_DIFF A (BAG_DIFF B C) = BAG_DIFF (BAG_UNION A C) B)``,
  SIMP_TAC hol_ss [BAG_UNION,BAG_INN,SUB_BAG,BAG_DIFF,geq_lemma] THEN
  REPEAT STRIP_TAC THEN FUN_EQ_TAC THEN
  ASSUM_LIST (fn thl => SIMP_TAC hol_ss (map SPEC_ALL thl)));

val SUB_BAG_BAG_DIFF = store_thm(
  "SUB_BAG_BAG_DIFF",
  ``!X Y Y' Z W:'a->num.
        SUB_BAG (BAG_DIFF X Y) (BAG_DIFF Z W) ==>
        SUB_BAG (BAG_DIFF X (BAG_UNION Y Y'))
                (BAG_DIFF Z (BAG_UNION W Y'))``,
  SIMP_TAC hol_ss [
    BAG_DIFF, SUB_BAG, BAG_INN, BAG_UNION, geq_lemma, ZGTN,
    DISJ_IMP_THM] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM (Q.SPECL [`x:'a`, `n + Y' x`] >-
               SIMP_RULE hol_ss [] >- STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC hol_ss []);

local
  fun bdf (b1, b2) (b3, b4) =
    let val [b1v, b2v, b3v, b4v] =
          map (C (curry mk_var) (==`:'a->num`==)) [b1, b2, b3, b4]
    in
        ``BAG_DIFF (BAG_UNION ^b1v ^b2v) (BAG_UNION ^b3v ^b4v) =
            BAG_DIFF b2 b3``
    end
in
  val BAG_DIFF_UNION_eliminate = store_thm(
    "BAG_DIFF_UNION_eliminate",
    ``!(b1:'a->num) (b2:'a->num) (b3:'a->num).
          ^(bdf ("b1", "b2") ("b1", "b3")) /\
          ^(bdf ("b1", "b2") ("b3", "b1")) /\
          ^(bdf ("b2", "b1") ("b1", "b3")) /\
          ^(bdf ("b2", "b1") ("b3", "b1"))``,
    REPEAT STRIP_TAC THEN FUN_EQ_TAC THEN
    SIMP_TAC hol_ss [BAG_DIFF, BAG_UNION])
end;

local
  fun bdf (b1, b2) (b3, b4) =
    let val [b1v, b2v, b3v, b4v] =
          map (C (curry mk_var) (==`:'a->num`==)) [b1, b2, b3, b4]
    in
        ``SUB_BAG (BAG_UNION ^b1v ^b2v) (BAG_UNION ^b3v ^b4v) =
            SUB_BAG (b2:'a->num) b3``
    end
in
  val SUB_BAG_UNION_eliminate = store_thm(
    "SUB_BAG_UNION_eliminate",
    ``!(b1:'a->num) (b2:'a->num) (b3:'a->num).
          ^(bdf ("b1", "b2") ("b1", "b3")) /\
          ^(bdf ("b1", "b2") ("b3", "b1")) /\
          ^(bdf ("b2", "b1") ("b1", "b3")) /\
          ^(bdf ("b2", "b1") ("b3", "b1"))``,
    SIMP_TAC hol_ss [SUB_BAG, BAG_UNION, BAG_INN] THEN
    REWRITE_TAC [geq_lemma] THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
    STRIP_TAC THEN
    POP_ASSUM (fn th => SIMP_TAC hol_ss [SPEC_ALL th]))
end;

val move_BAG_UNION_over_eq = store_thm(
  "move_BAG_UNION_over_eq",
  ``!X Y Z:'a->num. (BAG_UNION X Y = Z) ==> (X = BAG_DIFF Z Y)``,
  SIMP_TAC (hol_ss ++ ETA_ss) [BAG_UNION, BAG_DIFF]);

val COMM_BAG_UNION = store_thm(
  "COMM_BAG_UNION",
  ``!b1 b2. BAG_UNION b1 b2 = BAG_UNION b2 b1``,
  REWRITE_TAC [BAG_UNION] THEN
  REPEAT STRIP_TAC THEN FUN_EQ_TAC THEN SIMP_TAC hol_ss []);
val bu_comm = COMM_BAG_UNION;

val ASSOC_BAG_UNION = store_thm(
  "ASSOC_BAG_UNION",
  ``!b1 b2 b3. BAG_UNION b1 (BAG_UNION b2 b3)
                 =
                 BAG_UNION (BAG_UNION b1 b2) b3``,
  REWRITE_TAC [BAG_UNION] THEN
  REPEAT STRIP_TAC THEN FUN_EQ_TAC THEN SIMP_TAC hol_ss []);

val std_bag_tac =
  SIMP_TAC hol_ss [BAG_UNION, SUB_BAG, BAG_INN, geq_lemma] THEN
  REPEAT STRIP_TAC THEN
  ASSUM_LIST (fn thl => SIMP_TAC hol_ss (map SPEC_ALL thl))

fun bag_thm t = prove(Term t, std_bag_tac);

val simplest_cases = map bag_thm [
  `!b1 b2:'a->num. SUB_BAG b1 b2 ==> !b. SUB_BAG b1 (BAG_UNION b2 b)`,
  `!b1 b2:'a->num. SUB_BAG b1 b2 ==> !b. SUB_BAG b1 (BAG_UNION b b2)`
];

val one_from_assocl = map bag_thm [
  `!b1 b2 b3:'a->num.
      SUB_BAG b1 (BAG_UNION b2 b3) ==>
      !b. SUB_BAG b1 (BAG_UNION (BAG_UNION b2 b) b3)`,
  `!b1 b2 b3:'a->num.
      SUB_BAG b1 (BAG_UNION b2 b3) ==>
      !b. SUB_BAG b1 (BAG_UNION (BAG_UNION b b2) b3)`]

val one_from_assocr =
  map (ONCE_REWRITE_RULE [bu_comm]) one_from_assocl;

val one_from_assoc = one_from_assocl @ one_from_assocr;

val union_from_union = map bag_thm [
  `!b1 b2 b3 b4:'a->num.
     SUB_BAG b1 b3 ==> SUB_BAG b2 b4 ==>
     SUB_BAG (BAG_UNION b1 b2) (BAG_UNION b3 b4)`,
  `!b1 b2 b3 b4:'a->num.
     SUB_BAG b1 b4 ==> SUB_BAG b2 b3 ==>
     SUB_BAG (BAG_UNION b1 b2) (BAG_UNION b3 b4)`];

val union_union2_assocl = map bag_thm [
  `!b1 b2 b3 b4 b5:'a->num.
     SUB_BAG b1 (BAG_UNION b3 b5) ==> SUB_BAG b2 b4 ==>
     SUB_BAG (BAG_UNION b1 b2) (BAG_UNION (BAG_UNION b3 b4) b5)`,
  `!b1 b2 b3 b4 b5:'a->num.
     SUB_BAG b1 (BAG_UNION b4 b5) ==> SUB_BAG b2 b3 ==>
     SUB_BAG (BAG_UNION b1 b2) (BAG_UNION (BAG_UNION b3 b4) b5)`,
  `!b1 b2 b3 b4 b5:'a->num.
     SUB_BAG b2 (BAG_UNION b3 b5) ==> SUB_BAG b1 b4 ==>
     SUB_BAG (BAG_UNION b1 b2) (BAG_UNION (BAG_UNION b3 b4) b5)`,
  `!b1 b2 b3 b4 b5:'a->num.
     SUB_BAG b2 (BAG_UNION b4 b5) ==> SUB_BAG b1 b3 ==>
     SUB_BAG (BAG_UNION b1 b2) (BAG_UNION (BAG_UNION b3 b4) b5)`];

val union_union2_assocr =
  map (ONCE_REWRITE_RULE [bu_comm]) union_union2_assocl;

val union_union2_assoc = union_union2_assocl @ union_union2_assocr;

val union2_union_assocl = map bag_thm [
  `!b1 b2 b3 b4 b5:'a->num.
     SUB_BAG (BAG_UNION b1 b2) b4 ==> SUB_BAG b3 b5 ==>
     SUB_BAG (BAG_UNION (BAG_UNION b1 b3) b2) (BAG_UNION b4 b5)`,
  `!b1 b2 b3 b4 b5:'a->num.
     SUB_BAG (BAG_UNION b1 b2) b5 ==> SUB_BAG b3 b4 ==>
     SUB_BAG (BAG_UNION (BAG_UNION b1 b3) b2) (BAG_UNION b4 b5)`,
  `!b1 b2 b3 b4 b5:'a->num.
     SUB_BAG (BAG_UNION b3 b2) b4 ==> SUB_BAG b1 b5 ==>
     SUB_BAG (BAG_UNION (BAG_UNION b1 b3) b2) (BAG_UNION b4 b5)`,
  `!b1 b2 b3 b4 b5:'a->num.
     SUB_BAG (BAG_UNION b3 b2) b5 ==> SUB_BAG b1 b4 ==>
     SUB_BAG (BAG_UNION (BAG_UNION b1 b3) b2) (BAG_UNION b4 b5)`];

val union2_union_assocr =
  map (ONCE_REWRITE_RULE [bu_comm]) union2_union_assocl;

val union2_union_assoc = union2_union_assocl @ union2_union_assocr;

val SUB_BAG_UNION = save_thm(
  "SUB_BAG_UNION",
  LIST_CONJ (simplest_cases @ one_from_assoc @ union_from_union @
             union_union2_assoc @ union2_union_assoc));

val SUB_BAG_EL_BAG = Q.store_thm(
  "SUB_BAG_EL_BAG",
  `!e b. SUB_BAG (EL_BAG e) b = BAG_IN e b`,
  SIMP_TAC (hol_ss ++ impnorm_set) [EL_BAG, BAG_IN, SUB_BAG,
    BAG_INN_BAG_INSERT, FORALL_AND_THM, BAG_INN_EMPTY_BAG,
    BAG_INN_0, ARITH_PROVE (Term`!n. (n - 1 = 0) = (n = 0) \/ (n = 1)`)]);

val GREATER_OR_EQ_TRANS =
  ARITH_PROVE (Term`!n m q. n >= m /\ m >= q ==> n >= q`)

val SUB_BAG_INSERT = Q.store_thm(
  "SUB_BAG_INSERT",
  `!e b1 b2. SUB_BAG (BAG_INSERT e b1) (BAG_INSERT e b2) =
              SUB_BAG b1 b2`,
  SIMP_TAC (hol_ss ++ impnorm_set) [SUB_BAG, BAG_INN_BAG_INSERT,
    FORALL_AND_THM, BAG_INN, geq_lemma,
    ARITH_PROVE
      (Term`!x n. (x >= n - 1) \/ (x >= n) = (x >= n - 1)`)] THEN
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
    Q.ASM_CASES_TAC `x = e` THENL [
      ELIM_TAC THEN
      FIRST_X_ASSUM (tofl (concl >- dest_forall >-
                           fst >- type_of >- curry op= (Type`:num`)) >-
        Q.SPEC `m + 1` >-
        SIMP_RULE hol_ss [] >- GEN_ALL >-
        SIMP_RULE hol_ss [geq_lemma] >- ACCEPT_TAC),
      FIRST_X_ASSUM (tofl (concl >- dest_forall >- fst >- type_of >-
        curry op= (Type`:'a`)) >- Q.SPEC `x` >-
        SIMP_RULE hol_ss [Q.ASSUME `~(x = e)`, geq_lemma] >-
        ACCEPT_TAC)
    ],
    ASM_MESON_TAC [GREATER_OR_EQ_TRANS],
    ASM_MESON_TAC [GREATER_OR_EQ_TRANS]
  ]);

val NOT_IN_SUB_BAG_INSERT = Q.store_thm(
  "NOT_IN_SUB_BAG_INSERT",
  `!b1 b2 e. ~(BAG_IN e b1) ==>
             (SUB_BAG b1 (BAG_INSERT e b2) = SUB_BAG b1 b2)`,
  SIMP_TAC hol_ss [SUB_BAG, BAG_INN_BAG_INSERT, BAG_IN] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
    RES_TAC THEN ELIM_TAC THEN
    STRIP_ASSUME_TAC (ARITH_PROVE (Term`(n = 0) \/ (n = 1) \/ (1 < n)`))
    THENL [
      FULL_SIMP_TAC hol_ss [],
      FULL_SIMP_TAC hol_ss [],
      ASM_MESON_TAC [BAG_INN_LESS]
    ],
    ASM_MESON_TAC []
  ]);

val SUB_BAG_BAG_IN = Q.store_thm(
  "SUB_BAG_BAG_IN",
  `!x b1 b2. SUB_BAG (BAG_INSERT x b1) b2 ==> BAG_IN x b2`,
  SIMP_TAC hol_ss [SUB_BAG, BAG_INSERT, BAG_IN, BAG_INN, geq_lemma] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN (Q.SPEC `x` >- SIMP_RULE hol_ss [] >- ASSUME_TAC) THEN
  ASM_SIMP_TAC hol_ss []);

val SUB_BAG_EXISTS = store_thm(
  "SUB_BAG_EXISTS",
  ``!b1 b2:'a->num. SUB_BAG b1 b2 = ?b. b2 = BAG_UNION b1 b``,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    FULL_SIMP_TAC hol_ss [SUB_BAG, BAG_INN, geq_lemma, BAG_UNION] THEN
    Q.EXISTS_TAC `\x. b2 x - b1 x` THEN FUN_EQ_TAC THEN
    POP_ASSUM (fn th => SIMP_TAC hol_ss [SPEC_ALL th]),
    ELIM_TAC THEN SIMP_TAC hol_ss [SUB_BAG_UNION, SUB_BAG_REFL]
  ]);

val SUB_BAG_UNION_DIFF = store_thm(
  "SUB_BAG_UNION_DIFF",
  ``!b1 b2 b3:'a->num.
         SUB_BAG b1 b3 ==>
         (SUB_BAG b2 (BAG_DIFF b3 b1) = SUB_BAG (BAG_UNION b1 b2) b3)
  ``,
  SIMP_TAC hol_ss [SUB_BAG,BAG_INN,geq_lemma,BAG_DIFF,BAG_UNION] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
    POP_ASSUM (Q.SPECL [`x`, `b2 x`] >- SIMP_RULE hol_ss [] >-
               STRIP_ASSUME_TAC) THEN
    FULL_SIMP_TAC hol_ss [ARITH_PROVE (Term`!n. 0 >= n = (n = 0)`)],
    ASSUM_LIST (SIMP_TAC hol_ss o map SPEC_ALL)
  ]);

val SUB_BAG_UNION_down = store_thm(
  "SUB_BAG_UNION_down",
  ``!b1 b2 b3:'a->num. SUB_BAG (BAG_UNION b1 b2) b3 ==>
                        SUB_BAG b1 b3 /\ SUB_BAG b2 b3``,
  SIMP_TAC hol_ss [BAG_UNION, SUB_BAG, BAG_INN, geq_lemma] THEN
  REPEAT STRIP_TAC THEN
  ASSUM_LIST (fn thl => SIMP_TAC hol_ss (map SPEC_ALL thl)));

val SUB_BAG_DIFF = store_thm(
  "SUB_BAG_DIFF",
  ``(!b1 b2:'a->num. SUB_BAG b1 b2 ==>
                      (!b3. SUB_BAG (BAG_DIFF b1 b3) b2)) /\
     (!b1 b2 b3 b4:'a->num.
         SUB_BAG b2 b1 ==> SUB_BAG b4 b3 ==>
         (SUB_BAG (BAG_DIFF b1 b2) (BAG_DIFF b3 b4) =
          SUB_BAG (BAG_UNION b1 b4) (BAG_UNION b2 b3)))``,
  SIMP_TAC hol_ss [BAG_DIFF, BAG_UNION, SUB_BAG, BAG_INN,
                   geq_lemma, ZGTN] THEN REPEAT STRIP_TAC THEN
  TRY EQ_TAC  THEN REPEAT STRIP_TAC THEN
  ASSUM_LIST (fn thl => SIMP_TAC hol_ss (map SPEC_ALL thl)) THEN
  POP_ASSUM_LIST (List.rev >- MAP_EVERY (Q.SPEC `x` >- ASSUME_TAC)) THEN
  POP_ASSUM (Q.SPEC `b1 x - b2 x` >- MP_TAC) THEN
  ASM_SIMP_TAC hol_ss []);

val BAG_delta = new_definition (
  "BAG_delta",
  ``BAG_delta (B1:'a->num, B2) B3 =
     BAG_DIFF (BAG_UNION B3 (BAG_DIFF B2 B1)) (BAG_DIFF B1 B2)``);

val SUB_BAG_delta = store_thm(
  "SUB_BAG_delta",
  ``(!A B0 B:'a -> num.
        SUB_BAG B0 A ==> SUB_BAG B (BAG_delta (B0, B) A)) /\
     (!A B0 B:'a -> num.
        SUB_BAG A B0 ==> SUB_BAG (BAG_delta (B0, B) A) B)``,
  REWRITE_TAC [BAG_delta, SUB_BAG, geq_lemma, BAG_INN, BAG_DIFF,
               BAG_UNION] THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
  ASM_CASES_TAC ``B (x:'a) >= B0 x`` THEN
  ASM_SIMP_TAC boolSimps.bool_ss
                (map ARITH_PROVE [``x >= y ==> (y - x = 0)``,
                                  ``~(x >= y) ==> (x - y = 0)``,
                                  ``x - 0 = x``,
                                  ``x + 0 = x``]) THEN
  ASSUM_LIST (fn thl => SIMP_TAC hol_ss (map SPEC_ALL thl)));

val BAG_delta_rm_lemma = prove(
  ``!A BU BD X:'a->num.
         SUB_BAG X A ==>
         (BAG_delta (A, BAG_DIFF (BAG_UNION A BU) BD) X =
          BAG_DIFF (BAG_UNION X BU) BD)``,
  REWRITE_TAC [BAG_delta] THEN
  SIMP_TAC hol_ss [BAG_DIFF_2L, BAG_DIFF_2R, SUB_BAG_DIFF,
                    SUB_BAG_UNION, BAG_UNION_DIFF,
                    BAG_DIFF_UNION_eliminate] THEN
  REWRITE_TAC [SUB_BAG, BAG_INN, geq_lemma, BAG_DIFF, BAG_UNION,
               BAG_delta] THEN REPEAT STRIP_TAC THEN FUN_EQ_TAC THEN
  SIMP_TAC boolSimps.bool_ss [] THEN
  ASM_CASES_TAC ``BU (x:'a) >= BD x`` THENL [
    ASM_SIMP_TAC boolSimps.bool_ss
                  (map ARITH_PROVE [``x >= y ==>
                                       ((a + x) - y = a + (x - y))``,
                                    ``x - (x + y) = 0``,
                                    ``x - 0 = x``]),
    ASM_SIMP_TAC boolSimps.bool_ss
                  (map ARITH_PROVE [``~(x >= y) ==> (x - y = 0)``,
                                    ``x + 0 = x``]) THEN
    ASM_CASES_TAC ``A (x:'a) + BU x >= BD x`` THENL [
      ASM_SIMP_TAC
        boolSimps.bool_ss
        (map ARITH_PROVE [``x >= y ==> (z - (x - y) = (z + y) - x)``,
                          ``(x + y) - (x + z) = y - z``]) THEN
      ASM_SIMP_TAC hol_ss [],
      ASM_SIMP_TAC boolSimps.bool_ss
                    (map ARITH_PROVE [``~(x >= y) ==> (x - y = 0)``,
                                      ``x + 0 = x``]) THEN
      ASSUM_LIST (fn thl => SIMP_TAC hol_ss (map SPEC_ALL thl))
    ]
  ]);

val BAG_delta_eliminate = save_thm(
  "BAG_delta_eliminate",
  CONJ BAG_delta_rm_lemma
       (ONCE_REWRITE_RULE [bu_comm] BAG_delta_rm_lemma));

val SUB_BAG_PSUB_BAG = store_thm(
  "SUB_BAG_PSUB_BAG",
  ``!(b1:'a -> num) b2.
         SUB_BAG b1 b2 = PSUB_BAG b1 b2 \/ (b1 = b2)``,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC hol_ss [PSUB_BAG, DISJ_IMP_THM, SUB_BAG_REFL])

val mono_cond = COND_RAND
val mono_cond2 = COND_RATOR

val BAG_DELETE_PSUB_BAG = store_thm(
  "BAG_DELETE_PSUB_BAG",
  ``!b0 (e:'a) b. BAG_DELETE b0 e b ==> PSUB_BAG b b0``,
  SIMP_TAC hol_ss [BAG_DELETE, SUB_BAG, PSUB_BAG, BAG_INSERT_DIFF,
                    BAG_INN_BAG_INSERT]);

val _ = print "Relating bags to (pred)sets\n";

val SET_OF_BAG = new_definition(
  "SET_OF_BAG",
  ``SET_OF_BAG (b:'a->num) = \x. BAG_IN x b``);

val BAG_OF_SET = new_definition(
  "BAG_OF_SET",
  ``BAG_OF_SET (P:'a->bool) = \x. if x IN P then 1 else 0``);


val SET_OF_EMPTY = store_thm (
  "SET_OF_EMPTY",
  ``BAG_OF_SET (EMPTY:'a->bool) = EMPTY_BAG``,
  FUN_EQ_TAC THEN
  SIMP_TAC hol_ss [BAG_OF_SET, EMPTY_BAG, NOT_IN_EMPTY])
  before
  export_rewrites ["SET_OF_EMPTY"];

val BAG_OF_EMPTY = store_thm (
  "BAG_OF_EMPTY",
  ``SET_OF_BAG (EMPTY_BAG:'a->num) = EMPTY``,
  FUN_EQ_TAC THEN
  SIMP_TAC hol_ss [SET_OF_BAG, NOT_IN_EMPTY_BAG, EMPTY_DEF])
 before
 export_rewrites ["BAG_OF_EMPTY"]

val SET_BAG_I = store_thm (
  "SET_BAG_I",
  ``!s:'a->bool. SET_OF_BAG (BAG_OF_SET s) = s``,
  GEN_TAC THEN FUN_EQ_TAC THEN
  SIMP_TAC hol_ss [BAG_OF_SET, SET_OF_BAG, mono_cond, mono_cond2,
                    BAG_IN, BAG_INN, SPECIFICATION]);

val SUB_BAG_SET = store_thm (
  "SUB_BAG_SET",
  ``!b1 b2:'a->num.
        SUB_BAG b1 b2 ==> (SET_OF_BAG b1) SUBSET (SET_OF_BAG b2)``,
  SIMP_TAC hol_ss [SUB_BAG, SET_OF_BAG, BAG_IN, SPECIFICATION,
                    SUBSET_DEF]);

val SET_OF_BAG_UNION = store_thm(
  "SET_OF_BAG_UNION",
  ``!b1 b2:'a->num. SET_OF_BAG (BAG_UNION b1 b2) =
                      SET_OF_BAG b1 UNION SET_OF_BAG b2``,
  REWRITE_TAC [SET_OF_BAG, BAG_IN, UNION_DEF, BAG_UNION, BAG_INN,
               SPECIFICATION] THEN REPEAT GEN_TAC THEN FUN_EQ_TAC THEN
  SIMP_TAC hol_ss [] THEN
  CONV_TAC (rhs_CONV (ONCE_REWRITE_CONV [GSYM SPECIFICATION])) THEN
  SIMP_TAC hol_ss [GSPECIFICATION]);

val SET_OF_BAG_MERGE = store_thm (
  "SET_OF_BAG_MERGE",
  ``!b1 b2. SET_OF_BAG (BAG_MERGE b1 b2) =
            SET_OF_BAG b1 UNION SET_OF_BAG b2``,
  ONCE_REWRITE_TAC[EXTENSION] THEN
  SIMP_TAC hol_ss [SET_OF_BAG, IN_UNION, IN_ABS,
		   BAG_IN_BAG_MERGE]);

val SET_OF_BAG_INSERT = Q.store_thm(
  "SET_OF_BAG_INSERT",
  `!e b. SET_OF_BAG (BAG_INSERT e b) = e INSERT (SET_OF_BAG b)`,
  SIMP_TAC hol_ss [SET_OF_BAG, BAG_INSERT, INSERT_DEF, BAG_IN,
                    EXTENSION, GSPECIFICATION, BAG_INN] THEN
  SIMP_TAC hol_ss [SPECIFICATION] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN SIMP_TAC hol_ss []);

val SET_OF_EL_BAG = Q.store_thm(
  "SET_OF_EL_BAG",
  `!e. SET_OF_BAG (EL_BAG e) = {e}`,
  SIMP_TAC hol_ss [EL_BAG, SET_OF_BAG_INSERT, BAG_OF_EMPTY]);

val SET_OF_BAG_DIFF_SUBSET_down = Q.store_thm(
  "SET_OF_BAG_DIFF_SUBSET_down",
  `!b1 b2. (SET_OF_BAG b1) DIFF (SET_OF_BAG b2) SUBSET
            SET_OF_BAG (BAG_DIFF b1 b2)`,
  SIMP_TAC hol_ss [SUBSET_DEF, IN_DIFF, BAG_DIFF, SET_OF_BAG, BAG_IN,
                    BAG_INN] THEN
  SIMP_TAC hol_ss [SPECIFICATION]);

val SET_OF_BAG_DIFF_SUBSET_up = Q.store_thm(
  "SET_OF_BAG_DIFF_SUBSET_up",
  `!b1 b2. SET_OF_BAG (BAG_DIFF b1 b2) SUBSET SET_OF_BAG b1`,
  SIMP_TAC hol_ss [SUBSET_DEF, BAG_DIFF, SET_OF_BAG, BAG_IN, BAG_INN]
  THEN SIMP_TAC hol_ss [SPECIFICATION]);

val IN_SET_OF_BAG = Q.store_thm(
  "IN_SET_OF_BAG",
  `!x b. x IN SET_OF_BAG b = BAG_IN x b`,
  SIMP_TAC hol_ss [SET_OF_BAG, SPECIFICATION])
 before
 export_rewrites ["IN_SET_OF_BAG"];

val SET_OF_BAG_EQ_EMPTY = store_thm(
  "SET_OF_BAG_EQ_EMPTY",
  ``!b. (({} = SET_OF_BAG b) = (b = {||})) /\
        ((SET_OF_BAG b = {}) = (b = {||}))``,
  GEN_TAC THEN
  Q.SPEC_THEN `b` STRIP_ASSUME_TAC BAG_cases THEN
  SRW_TAC [][SET_OF_BAG_INSERT])
 before
 export_rewrites ["SET_OF_BAG_EQ_EMPTY"];

val _ = print "Bag disjointness\n"
val BAG_DISJOINT = new_definition(
  "BAG_DISJOINT",
  ``BAG_DISJOINT (b1:'a->num) b2 =
        DISJOINT (SET_OF_BAG b1) (SET_OF_BAG b2)``);

val BAG_DISJOINT_EMPTY = store_thm(
  "BAG_DISJOINT_EMPTY",
  ``!b:'a->num.
       BAG_DISJOINT b EMPTY_BAG /\ BAG_DISJOINT EMPTY_BAG b``,
  REWRITE_TAC [BAG_OF_EMPTY, BAG_DISJOINT, DISJOINT_EMPTY]);

val BAG_DISJOINT_DIFF = store_thm(
  "BAG_DISJOINT_DIFF",
  ``!B1 B2:'a->num.
      BAG_DISJOINT (BAG_DIFF B1 B2) (BAG_DIFF B2 B1)``,
  SIMP_TAC hol_ss [INTER_DEF, DISJOINT_DEF, BAG_DISJOINT, BAG_DIFF,
                    SET_OF_BAG, BAG_IN, BAG_INN, EXTENSION,
                    GSPECIFICATION, NOT_IN_EMPTY] THEN
  SIMP_TAC hol_ss [SPECIFICATION]);

val BAG_DISJOINT_BAG_IN = store_thm (
  "BAG_DISJOINT_BAG_IN",
  ``!b1 b2. BAG_DISJOINT b1 b2 =
            !e. ~(BAG_IN e b1) \/ ~(BAG_IN e b2)``,
  SIMP_TAC hol_ss [BAG_DISJOINT, DISJOINT_DEF,
 		   EXTENSION, NOT_IN_EMPTY,
		   IN_INTER, IN_SET_OF_BAG]);

val BAG_DISJOINT_BAG_INSERT = store_thm (
  "BAG_DISJOINT_BAG_INSERT",
  ``(!b1 b2 e1.
      BAG_DISJOINT (BAG_INSERT e1 b1) b2 =
      (~(BAG_IN e1 b2) /\ (BAG_DISJOINT b1 b2))) /\
    (!b1 b2 e2.
      BAG_DISJOINT b1 (BAG_INSERT e2 b2) =
      (~(BAG_IN e2 b1) /\ (BAG_DISJOINT b1 b2)))``,
  SIMP_TAC hol_ss [BAG_DISJOINT_BAG_IN,
		   BAG_IN_BAG_INSERT] THEN
  METIS_TAC[]);

val _ = print "Developing theory of finite bags\n"

val FINITE_BAG = Q.new_definition(
  "FINITE_BAG",
  `FINITE_BAG (b:'a->num) =
     !P. P EMPTY_BAG /\ (!b. P b ==> (!e. P (BAG_INSERT e b))) ==>
         P b`);

val FINITE_EMPTY_BAG = Q.store_thm(
  "FINITE_EMPTY_BAG",
  `FINITE_BAG EMPTY_BAG`,
  SIMP_TAC hol_ss [FINITE_BAG]);

val FINITE_BAG_INSERT = Q.store_thm(
  "FINITE_BAG_INSERT",
  `!b. FINITE_BAG b ==> (!e. FINITE_BAG (BAG_INSERT e b))`,
  REWRITE_TAC [FINITE_BAG] THEN MESON_TAC []);

val FINITE_BAG_INDUCT = Q.store_thm(
  "FINITE_BAG_INDUCT",
  `!P. P EMPTY_BAG /\
        (!b. P b ==> (!e. P (BAG_INSERT e b))) ==>
        (!b. FINITE_BAG b ==> P b)`,
  SIMP_TAC hol_ss [FINITE_BAG]);

val STRONG_FINITE_BAG_INDUCT = save_thm(
  "STRONG_FINITE_BAG_INDUCT",
  (Q.SPEC `\b. FINITE_BAG b /\ P b` >-
   SIMP_RULE hol_ss [FINITE_EMPTY_BAG, FINITE_BAG_INSERT] >-
   GEN_ALL) FINITE_BAG_INDUCT)

val FINITE_BAG_INSERT_down' = prove(
  Term`!b. FINITE_BAG b ==> (!e b0. (b = BAG_INSERT e b0) ==> FINITE_BAG b0)`,
  HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN
  SIMP_TAC hol_ss [BAG_INSERT_NOT_EMPTY] THEN
  REPEAT STRIP_TAC THEN Q.ASM_CASES_TAC `e = e'` THENL [
    ELIM_TAC THEN IMP_RES_TAC BAG_INSERT_ONE_ONE THEN ELIM_TAC THEN
    ASM_SIMP_TAC hol_ss [],
    ALL_TAC
  ] THEN Q.SUBGOAL_THEN `?b'. b = BAG_INSERT e' b'` STRIP_ASSUME_TAC
  THENL [
    SIMP_TAC hol_ss [GSYM BAG_DELETE] THEN
    MATCH_MP_TAC BAG_IN_BAG_DELETE THEN
    Q.SUBGOAL_THEN `BAG_IN e' (BAG_INSERT e b)`
      (REWRITE_RULE [BAG_IN_BAG_INSERT] >- STRIP_ASSUME_TAC)
    THENL [
      ARWT THEN ASM_REWRITE_TAC [BAG_IN_BAG_INSERT],
      FULL_SIMP_TAC hol_ss []
    ],
    RES_TAC THEN ELIM_TAC THEN
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [BAG_INSERT_commutes]) THEN
    IMP_RES_TAC BAG_INSERT_ONE_ONE THEN ELIM_TAC THEN
    ASM_MESON_TAC [FINITE_BAG_INSERT]
  ])

val FINITE_BAG_INSERT_down =
  SIMP_RULE hol_ss [RIGHT_IMP_FORALL_THM] FINITE_BAG_INSERT_down'

val FINITE_BAG_INSERT = prove(
  Term`!e b. FINITE_BAG (BAG_INSERT e b) = FINITE_BAG b`,
  MESON_TAC [FINITE_BAG_INSERT, FINITE_BAG_INSERT_down])

val FINITE_BAG_THM = save_thm(
  "FINITE_BAG_THM",
  CONJ FINITE_EMPTY_BAG FINITE_BAG_INSERT)
 before
 export_rewrites ["FINITE_BAG_THM"];


val FINITE_BAG_DIFF = Q.store_thm(
  "FINITE_BAG_DIFF",
  `!b1. FINITE_BAG b1 ==> !b2. FINITE_BAG (BAG_DIFF b1 b2)`,
  HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN
  SIMP_TAC hol_ss [BAG_DIFF_EMPTY, FINITE_BAG_THM] THEN
  REPEAT STRIP_TAC THEN Q.ASM_CASES_TAC `BAG_IN e b2` THENL [
    IMP_RES_TAC (REWRITE_RULE [BAG_DELETE] BAG_IN_BAG_DELETE) THEN
    ASM_SIMP_TAC hol_ss [BAG_DIFF_INSERT_same],
    ASM_SIMP_TAC hol_ss [BAG_DIFF_INSERT, FINITE_BAG_THM]
  ]);

val FINITE_BAG_DIFF_dual = Q.store_thm(
  "FINITE_BAG_DIFF_dual",
  `!b1. FINITE_BAG b1 ==>
        !b2. FINITE_BAG (BAG_DIFF b2 b1) ==> FINITE_BAG b2`,
  HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN
  REWRITE_TAC [BAG_DIFF_EMPTY] THEN
  REPEAT STRIP_TAC THEN Q.ASM_CASES_TAC `BAG_IN e b2` THENL [
    IMP_RES_TAC (REWRITE_RULE [BAG_DELETE] BAG_IN_BAG_DELETE) THEN
    ELIM_TAC THEN ASM_MESON_TAC [FINITE_BAG_THM, BAG_DIFF_INSERT_same],
    ASM_MESON_TAC [NOT_IN_BAG_DIFF]
  ]);

val FINITE_BAG_UNION_1 = prove(
  Term`!b1. FINITE_BAG b1 ==>
            !b2. FINITE_BAG b2 ==> FINITE_BAG (BAG_UNION b1 b2)`,
  HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN
  SIMP_TAC hol_ss [FINITE_BAG_THM, BAG_UNION_EMPTY, BAG_UNION_INSERT]);
val FINITE_BAG_UNION_2 = prove(
  Term`!b. FINITE_BAG b ==>
           !b1 b2. (b = BAG_UNION b1 b2) ==> FINITE_BAG b1 /\ FINITE_BAG b2`,
  HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN
  CONJ_TAC THENL [
    REPEAT GEN_TAC THEN CONV_TAC (ant_CONV (REWR_CONV EQ_SYM_EQ)) THEN
    SIMP_TAC hol_ss [BAG_UNION_EMPTY, FINITE_BAG_THM],
    REPEAT (GEN_TAC ORELSE myDISCH_TAC) THEN
    MAP_EVERY IMP_RES_TAC [BAG_INSERT_EQ_UNION,
                           REWRITE_RULE [BAG_DELETE] BAG_IN_BAG_DELETE] THEN
    ELIM_TAC THEN
    FULL_SIMP_TAC hol_ss [BAG_UNION_INSERT, BAG_INSERT_ONE_ONE,
                          FINITE_BAG_THM] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC []
  ]);


val FINITE_BAG_UNION = Q.store_thm(
  "FINITE_BAG_UNION",
  `!b1 b2. FINITE_BAG (BAG_UNION b1 b2) =
           FINITE_BAG b1 /\ FINITE_BAG b2`,
  MESON_TAC [FINITE_BAG_UNION_1, FINITE_BAG_UNION_2]);

val FINITE_SUB_BAG = Q.store_thm(
  "FINITE_SUB_BAG",
  `!b1. FINITE_BAG b1 ==> !b2. SUB_BAG b2 b1 ==> FINITE_BAG b2`,
  HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN
  SIMP_TAC hol_ss [SUB_BAG_EMPTY, FINITE_BAG_THM] THEN
  REPEAT STRIP_TAC THEN Q.ASM_CASES_TAC `BAG_IN e b2` THENL [
    IMP_RES_TAC (REWRITE_RULE [BAG_DELETE] BAG_IN_BAG_DELETE) THEN
    ELIM_TAC THEN FULL_SIMP_TAC hol_ss [SUB_BAG_INSERT, FINITE_BAG_THM],
    ASM_MESON_TAC [NOT_IN_SUB_BAG_INSERT]
  ]);


val _ = print "Developing theory of bag cardinality\n"

val BAG_CARD_RELn = Q.new_definition(
  "BAG_CARD_RELn",
  `BAG_CARD_RELn (b:'a->num) n =
      !P. P EMPTY_BAG 0 /\
          (!b n. P b n ==> (!e. P (BAG_INSERT e b) (SUC n))) ==>
          P b n`);

val BCARD_imps = prove(
  Term`(BAG_CARD_RELn EMPTY_BAG 0) /\
       (!b n. BAG_CARD_RELn b n ==>
           (!e. BAG_CARD_RELn (BAG_INSERT e b) (n + 1)))`,
  REWRITE_TAC [BAG_CARD_RELn, arithmeticTheory.ADD1] THEN MESON_TAC [])

val BCARD_induct = prove(
  Term`!P. P EMPTY_BAG 0 /\
           (!b n. P b n ==> (!e. P (BAG_INSERT e b) (n + 1))) ==>
           (!b n. BAG_CARD_RELn b n ==> P b n)`,
  REWRITE_TAC [BAG_CARD_RELn, arithmeticTheory.ADD1] THEN MESON_TAC []);

val strong_BCARD_induct =
  (Q.SPEC `\b n. BAG_CARD_RELn b n /\ P b n` >-
   SIMP_RULE hol_ss [BCARD_imps]) BCARD_induct

val BCARD_R_cases = prove(
  Term`!b n. BAG_CARD_RELn b n ==>
             (b = EMPTY_BAG) /\ (n = 0) \/
             (?b0 e m. (b = BAG_INSERT e b0) /\
                       BAG_CARD_RELn b0 m /\ (n = m + 1))`,
  HO_MATCH_MP_TAC BCARD_induct THEN SIMP_TAC hol_ss [] THEN
  REPEAT STRIP_TAC THEN ELIM_TAC THEN ASM_MESON_TAC [BCARD_imps]);

val BCARD_rwts = prove(
  Term`!b n. BAG_CARD_RELn b n =
             (b = EMPTY_BAG) /\ (n = 0) \/
             (?b0 e m. (b = BAG_INSERT e b0) /\ (n = m + 1) /\
                       BAG_CARD_RELn b0 m)`,
  MESON_TAC [BCARD_R_cases, BCARD_imps]);

val BCARD_BINSERT_indifferent = prove(
  Term`!b n. BAG_CARD_RELn b n ==>
             !b0 e. (b = BAG_INSERT e b0) ==>
                    BAG_CARD_RELn b0 (n - 1) /\ ~(n = 0)`,
  HO_MATCH_MP_TAC strong_BCARD_induct THEN
  SIMP_TAC hol_ss [BAG_INSERT_NOT_EMPTY] THEN REPEAT STRIP_TAC THEN
  Q.ASM_CASES_TAC `e = e'` THENL [
    ELIM_TAC THEN IMP_RES_TAC BAG_INSERT_ONE_ONE THEN ELIM_TAC THEN
    ARWT,
    ALL_TAC
  ] THEN
  Q.SUBGOAL_THEN `?b'. b = BAG_INSERT e' b'` STRIP_ASSUME_TAC
  THENL [
    SIMP_TAC hol_ss [GSYM BAG_DELETE] THEN
    MATCH_MP_TAC BAG_IN_BAG_DELETE THEN
    Q.SUBGOAL_THEN `BAG_IN e' (BAG_INSERT e b)`
      (REWRITE_RULE [BAG_IN_BAG_INSERT] >- STRIP_ASSUME_TAC)
    THENL [
      ARWT THEN REWRITE_TAC [BAG_IN_BAG_INSERT],
      ELIM_TAC THEN FULL_SIMP_TAC hol_ss []
    ],
    RES_TAC THEN ELIM_TAC THEN
    RULE_ASSUM_TAC (ONCE_REWRITE_RULE [BAG_INSERT_commutes]) THEN
    FULL_SIMP_TAC hol_ss [BAG_INSERT_ONE_ONE] THEN ELIM_TAC THEN
    REPEAT_TCL STRIP_THM_THEN SUBST_ALL_TAC
      (Q.SPEC `n` arithmeticTheory.num_CASES) THEN
    FULL_SIMP_TAC hol_ss [arithmeticTheory.ADD1] THEN
    ASM_MESON_TAC [BCARD_imps]
  ]);

val BCARD_BINSERT' =
  SIMP_RULE hol_ss [RIGHT_IMP_FORALL_THM] BCARD_BINSERT_indifferent

val BCARD_EMPTY = prove(
  Term`!n. BAG_CARD_RELn EMPTY_BAG n = (n = 0)`,
  ONCE_REWRITE_TAC [BCARD_rwts] THEN
  SIMP_TAC hol_ss [BAG_INSERT_NOT_EMPTY]);

val BCARD_BINSERT = prove(
  Term`!b e n. BAG_CARD_RELn (BAG_INSERT e b) n =
               (?m. (n = m + 1) /\ BAG_CARD_RELn b m)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ELIM_TAC THENL [
    IMP_RES_TAC BCARD_BINSERT' THEN Q.EXISTS_TAC `n - 1` THEN
    ASM_SIMP_TAC hol_ss [],
    ASM_MESON_TAC [BCARD_imps]
  ]);

val BCARD_RWT = CONJ BCARD_EMPTY BCARD_BINSERT

val BCARD_R_det = prove(
  Term`!b n. BAG_CARD_RELn b n ==>
             !n'. BAG_CARD_RELn b n' ==> (n' = n)`,
  HO_MATCH_MP_TAC BCARD_induct THEN CONJ_TAC THENL [
    ONCE_REWRITE_TAC [BCARD_rwts] THEN
    SIMP_TAC hol_ss [BAG_INSERT_NOT_EMPTY],
    REPEAT STRIP_TAC THEN IMP_RES_TAC BCARD_BINSERT THEN RES_TAC THEN
    ASM_SIMP_TAC hol_ss []
  ]);

val FINITE_BAGS_BCARD = prove(
  Term`!b. FINITE_BAG b ==> ?n. BAG_CARD_RELn b n`,
  HO_MATCH_MP_TAC FINITE_BAG_INDUCT THEN MESON_TAC [BCARD_imps]);

val BAG_CARD = new_specification
  ("BAG_CARD",["BAG_CARD"],
   CONV_RULE SKOLEM_CONV (
    SIMP_RULE hol_ss
       [GSYM boolTheory.RIGHT_EXISTS_IMP_THM] FINITE_BAGS_BCARD));

val BAG_CARD_EMPTY =
  (Q.SPEC `EMPTY_BAG`  >- SIMP_RULE hol_ss [FINITE_EMPTY_BAG] >-
   ONCE_REWRITE_RULE [BCARD_rwts] >-
   SIMP_RULE hol_ss [BAG_INSERT_NOT_EMPTY]) BAG_CARD;
val _ = save_thm("BAG_CARD_EMPTY", BAG_CARD_EMPTY);
val _ = export_rewrites ["BAG_CARD_EMPTY"];

val BCARD_0 = Q.store_thm(
  "BCARD_0",
  `!b. FINITE_BAG b ==> ((BAG_CARD b = 0) = (b = EMPTY_BAG))`,
  GEN_TAC THEN STRIP_TAC THEN EQ_TAC THEN
  SIMP_TAC hol_ss [BAG_CARD_EMPTY] THEN
  IMP_RES_TAC BAG_CARD THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC (
    ONCE_REWRITE_RULE [BCARD_rwts] >- SIMP_RULE hol_ss []) THEN
  carwt);

val BAG_CARD_EL_BAG = prove(
  Term`!e. BAG_CARD (EL_BAG e) = 1`,
  GEN_TAC THEN SIMP_TAC hol_ss [EL_BAG] THEN
  Q.SUBGOAL_THEN `FINITE_BAG (BAG_INSERT e EMPTY_BAG)` ASSUME_TAC
  THENL [MESON_TAC [FINITE_BAG_INSERT, FINITE_EMPTY_BAG],
         ALL_TAC] THEN IMP_RES_TAC BAG_CARD THEN
  FULL_SIMP_TAC hol_ss [BCARD_RWT])

val BAG_CARD_INSERT = prove(
  Term`!b. FINITE_BAG b ==>
           !e. BAG_CARD (BAG_INSERT e b) = BAG_CARD b + 1`,
  REPEAT STRIP_TAC THEN
  Q.SUBGOAL_THEN `FINITE_BAG (BAG_INSERT e b)` ASSUME_TAC THENL [
    ASM_MESON_TAC [FINITE_BAG_INSERT], ALL_TAC] THEN
  IMP_RES_TAC BAG_CARD THEN
  FULL_SIMP_TAC hol_ss [BCARD_RWT] THEN IMP_RES_TAC BCARD_R_det);

val BAG_CARD_THM = save_thm(
  "BAG_CARD_THM",
  CONJ BAG_CARD_EMPTY BAG_CARD_INSERT);

val BCARD_SUC = Q.store_thm(
  "BCARD_SUC",
  `!b. FINITE_BAG b ==>
       !n. (BAG_CARD b = SUC n) =
           (?b0 e. (b = BAG_INSERT e b0) /\ (BAG_CARD b0 = n))`,
  GEN_TAC THEN STRUCT_CASES_TAC (Q.SPEC `b` BAG_cases) THEN
  SIMP_TAC hol_ss [BAG_CARD_THM, BAG_INSERT_NOT_EMPTY,
                   FINITE_BAG_THM, arithmeticTheory.ADD1] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    ASM_MESON_TAC [],
    FIRST_ASSUM (Q.AP_TERM `BAG_CARD` >- MP_TAC) THEN
    ASM_SIMP_TAC hol_ss [BAG_CARD_THM] THEN
    Q.SUBGOAL_THEN `FINITE_BAG b0'` ASSUME_TAC THENL [
      ASM_MESON_TAC [FINITE_BAG_THM],
      ASM_SIMP_TAC hol_ss [BAG_CARD_THM]
    ]
  ]);

val BAG_CARD_BAG_INN = Q.store_thm(
  "BAG_CARD_BAG_INN",
  `!b. FINITE_BAG b ==> !n e. BAG_INN e n b ==> n <= BAG_CARD b`,
  HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN
  SIMP_TAC hol_ss [BAG_CARD_THM, BAG_INN_BAG_INSERT,
                    BAG_INN_EMPTY_BAG] THEN REPEAT STRIP_TAC
  THENL [
    ELIM_TAC THEN RES_TAC THEN ASM_SIMP_TAC hol_ss [],
    RES_TAC THEN ASM_SIMP_TAC hol_ss []
  ]);

(* --------------------------------------------------------------------
    FILTER for bags (alternatively, intersection with a set)
   ---------------------------------------------------------------------- *)

val BAG_FILTER_DEF = new_definition(
  "BAG_FILTER_DEF",
  ``BAG_FILTER P (b :'a bag) : 'a bag = \e. if P e then b e else 0``);

val BAG_FILTER_EMPTY = store_thm(
  "BAG_FILTER_EMPTY",
  ``BAG_FILTER P {||} = {||}``,
  SRW_TAC [][BAG_FILTER_DEF, FUN_EQ_THM] THEN
  SRW_TAC [][EMPTY_BAG])
  before
  export_rewrites ["BAG_FILTER_EMPTY"];

val BAG_FILTER_BAG_INSERT = store_thm(
  "BAG_FILTER_BAG_INSERT",
  ``BAG_FILTER P (BAG_INSERT e b) = if P e then BAG_INSERT e (BAG_FILTER P b)
                                    else BAG_FILTER P b``,
  SRW_TAC [][BAG_FILTER_DEF, FUN_EQ_THM] THEN
  SRW_TAC [][BAG_INSERT] THEN RES_TAC)
  before
  export_rewrites ["BAG_FILTER_BAG_INSERT"];

val FINITE_BAG_FILTER = store_thm(
  "FINITE_BAG_FILTER",
  ``!b. FINITE_BAG b ==> FINITE_BAG (BAG_FILTER P b)``,
  HO_MATCH_MP_TAC FINITE_BAG_INDUCT THEN SRW_TAC [][] THEN
  SRW_TAC [][])
  before
  export_rewrites ["FINITE_BAG_FILTER"];

val BAG_INN_BAG_FILTER = store_thm(
  "BAG_INN_BAG_FILTER",
  ``BAG_INN e n (BAG_FILTER P b) = (n = 0) \/ P e /\ BAG_INN e n b``,
  SRW_TAC [numSimps.ARITH_ss][BAG_FILTER_DEF, BAG_INN]);
val _ = export_rewrites ["BAG_INN_BAG_FILTER"]

val BAG_IN_BAG_FILTER = store_thm(
  "BAG_IN_BAG_FILTER",
  ``BAG_IN e (BAG_FILTER P b) = P e /\ BAG_IN e b``,
  SRW_TAC [][BAG_IN])
 before
 export_rewrites ["BAG_IN_BAG_FILTER"];

val SET_OF_BAG_EQ_INSERT = store_thm(
  "SET_OF_BAG_EQ_INSERT",
  ``!b e s.
      (e INSERT s = SET_OF_BAG b) =
      ?b0 eb. (b = BAG_UNION eb b0) /\
              (s = SET_OF_BAG b0) /\
              (!e'. BAG_IN e' eb ==> (e' = e)) /\
              (~(e IN s) ==> BAG_IN e eb)``,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    `BAG_IN e b` by METIS_TAC [IN_INSERT, IN_SET_OF_BAG] THEN
    Cases_on `e IN s` THENL [
      MAP_EVERY Q.EXISTS_TAC [`b`, `{||}`] THEN
      SRW_TAC [][] THEN METIS_TAC [ABSORPTION],
      MAP_EVERY Q.EXISTS_TAC [`BAG_FILTER ((~) o (=) e) b`,
                              `BAG_FILTER ((=) e) b`] THEN
      REPEAT CONJ_TAC THENL [
        SRW_TAC [boolSimps.DNF_ss, boolSimps.CONJ_ss]
                [BAG_EXTENSION, BAG_INN_BAG_UNION] THEN
        PROVE_TAC [BAG_INN_0],
        FULL_SIMP_TAC (srw_ss()) [EXTENSION] THEN PROVE_TAC [],
        SRW_TAC [][],
        SRW_TAC [][]
      ]
    ],
    SRW_TAC [][EXTENSION, BAG_IN_BAG_UNION] THEN
    FULL_SIMP_TAC (srw_ss()) [] THEN PROVE_TAC []
  ]);

val FINITE_SET_OF_BAG = store_thm(
  "FINITE_SET_OF_BAG",
  ``!b. FINITE (SET_OF_BAG b) = FINITE_BAG b``,
  Q_TAC SUFF_TAC
        `(!b:'a bag. FINITE_BAG b ==> FINITE (SET_OF_BAG b)) /\
         (!s:'a set. FINITE s ==>
                     !b. (s = SET_OF_BAG b) ==> FINITE_BAG b)` THEN1
         METIS_TAC [] THEN CONJ_TAC
  THENL [
    HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN
    SRW_TAC [][SET_OF_BAG_INSERT],
    HO_MATCH_MP_TAC FINITE_INDUCT THEN
    SRW_TAC [][SET_OF_BAG_EQ_INSERT, SET_OF_BAG_EQ_EMPTY] THEN
    SRW_TAC [][FINITE_BAG_UNION] THEN
    Q_TAC SUFF_TAC `!n b e. (b e = n) /\ (!e'. BAG_IN e' b ==> (e' = e)) ==>
                            FINITE_BAG b` THEN1 METIS_TAC [] THEN
    REPEAT (POP_ASSUM (K ALL_TAC)) THEN Induct THENL [
      REPEAT STRIP_TAC THEN
      Q_TAC SUFF_TAC `b = {||}` THEN1 SRW_TAC [][] THEN
      SRW_TAC [][BAG_EXTENSION] THEN
      FULL_SIMP_TAC (srw_ss()) [BAG_INN, BAG_IN] THEN EQ_TAC THENL [
        SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
        `b e' >= 1`
           by PROVE_TAC [numLib.ARITH_PROVE
                           ``x >= n /\ ~(n = 0) ==> x >= 1n``] THEN
        `b e' = 0` by PROVE_TAC [] THEN
        FULL_SIMP_TAC (srw_ss()) [],
        SIMP_TAC (srw_ss()) []
      ],
      REPEAT STRIP_TAC THEN
      `BAG_IN e b` by SRW_TAC [numSimps.ARITH_ss][BAG_IN, BAG_INN] THEN
      `?b0. b = BAG_INSERT e b0`
         by PROVE_TAC [BAG_IN_BAG_DELETE, BAG_DELETE] THEN
      POP_ASSUM SUBST_ALL_TAC THEN
      FULL_SIMP_TAC (srw_ss()) [DISJ_IMP_THM] THEN
      `b0 e = n`
        by FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [BAG_INSERT] THEN
      PROVE_TAC []
    ]
  ])
 before 
 export_rewrites ["FINITE_SET_OF_BAG"];

(* ----------------------------------------------------------------------
    IMAGE for bags.

    This is complicated by the fact that a taking the image of a
    non-injective function over an infinite bag might produce a bag that
    wanted to have an infinite number of some element.  For example,
       BAG_IMAGE (\e. 1) (BAG_OF_SET (UNIV : num set))
    would want to populate a bag with an infinite number of ones.

    BAG_IMAGE is "safe" if the input bag is finite, or if the function is
    only finitely non-injective.  I don't want to have these side conditions
    hanging around on my theorems, so I've decided to simply make BAG_IMAGE
    take elements that want to be infinite to zero instead.
   ---------------------------------------------------------------------- *)

val _ = augment_srw_ss [simpLib.rewrites [LET_THM]]
val BAG_IMAGE_DEF = new_definition(
  "BAG_IMAGE_DEF",
  ``BAG_IMAGE f b = \e. let sb = BAG_FILTER (\e0. f e0 = e) b
                        in
                            if FINITE_BAG sb then BAG_CARD sb
                            else 0``);

val BAG_IMAGE_EMPTY = store_thm(
  "BAG_IMAGE_EMPTY",
  ``BAG_IMAGE f {||} = {||}``,
  SRW_TAC [][BAG_IMAGE_DEF] THEN SRW_TAC [][EMPTY_BAG_alt])
 before 
 export_rewrites ["BAG_IMAGE_EMPTY"];

val BAG_IMAGE_FINITE_INSERT = store_thm(
  "BAG_IMAGE_FINITE_INSERT",
  ``!b. FINITE_BAG b ==>
        (BAG_IMAGE f (BAG_INSERT e b) = BAG_INSERT (f e) (BAG_IMAGE f b))``,
  SRW_TAC [][BAG_IMAGE_DEF] THEN
  SRW_TAC [][FUN_EQ_THM] THEN
  Cases_on `f e = e'` THENL [
    SRW_TAC [][BAG_CARD_THM] THEN SRW_TAC [][BAG_INSERT],
    SRW_TAC [][] THEN SRW_TAC [][BAG_INSERT]
  ])
 before 
 export_rewrites ["BAG_IMAGE_FINITE_INSERT"];

val BAG_IMAGE_FINITE = store_thm(
  "BAG_IMAGE_FINITE",
  ``!b. FINITE_BAG b ==> FINITE_BAG (BAG_IMAGE f b)``,
  HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN SRW_TAC [][])
 before 
 export_rewrites ["BAG_IMAGE_FINITE"];

val BAG_IN_FINITE_BAG_IMAGE = store_thm(
  "BAG_IN_FINITE_BAG_IMAGE",
  ``FINITE_BAG b ==>
    (BAG_IN x (BAG_IMAGE f b) = ?y. (f y = x) /\ BAG_IN y b)``,
  SRW_TAC [][BAG_IMAGE_DEF] THEN EQ_TAC THEN STRIP_TAC THENL [
    FULL_SIMP_TAC (srw_ss()) [BAG_IN, BAG_INN] THEN
    Q.ABBREV_TAC `bf = BAG_FILTER (\e0. f e0 = x) b` THEN
    `FINITE_BAG bf` by (Q.UNABBREV_TAC `bf` THEN SRW_TAC [][]) THEN
    `0 < BAG_CARD bf` by SRW_TAC [numSimps.ARITH_ss][] THEN
    `?m. BAG_CARD bf = SUC m`
        by PROVE_TAC [arithmeticTheory.num_CASES,
                      arithmeticTheory.NOT_ZERO_LT_ZERO] THEN
    `?e bf0. (bf = BAG_INSERT e bf0)` by PROVE_TAC [BCARD_SUC] THEN
    `BAG_IN e bf` by SRW_TAC [][] THEN
    `BAG_IN e (BAG_FILTER (\e0. f e0 = x) b)` by PROVE_TAC [] THEN
    POP_ASSUM (STRIP_ASSUME_TAC o SIMP_RULE bool_ss [BAG_IN_BAG_FILTER]) THEN
    PROVE_TAC [BAG_IN, BAG_INN],
    `?b0. BAG_DELETE b y b0` by PROVE_TAC [BAG_IN_BAG_DELETE] THEN
    `b = BAG_INSERT y b0` by PROVE_TAC [BAG_DELETE] THEN
    SIMP_TAC (srw_ss()) [BAG_IN, BAG_INN] THEN SRW_TAC [][] THEN
    FULL_SIMP_TAC (srw_ss() ++ numSimps.ARITH_ss) [BAG_CARD_THM]
  ])
 before 
 export_rewrites ["BAG_IN_FINITE_BAG_IMAGE"];

(*---------------------------------------------------------------------------
        CHOICE and REST for bags.
 ---------------------------------------------------------------------------*)

val BAG_CHOICE_DEF = new_specification
  ("BAG_CHOICE_DEF",["BAG_CHOICE"],
   Q.prove(`?ch:('a -> num) -> 'a. !b. ~(b = {||}) ==> BAG_IN (ch b) b`,
           PROVE_TAC [MEMBER_NOT_EMPTY]));


(* ===================================================================== *)
(* The REST of a bag after removing a chosen element.			 *)
(* ===================================================================== *)

val BAG_REST_DEF = Q.new_definition
 ("BAG_REST_DEF",
  `BAG_REST b = BAG_DIFF b (EL_BAG (BAG_CHOICE b))`);


val BAG_INSERT_CHOICE_REST = Q.store_thm
("BAG_INSERT_CHOICE_REST",
 `!b:'a bag. ~(b = {||}) ==> (b = BAG_INSERT (BAG_CHOICE b) (BAG_REST b))`,
 REPEAT STRIP_TAC
   THEN IMP_RES_THEN MP_TAC BAG_CHOICE_DEF
   THEN NORM_TAC arith_ss
        [BAG_INSERT,BAG_REST_DEF,BAG_DIFF,EL_BAG,BAG_IN,BAG_INN,
         EMPTY_BAG,combinTheory.K_DEF,FUN_EQ_THM]);

val SUB_BAG_REST = Q.store_thm
("SUB_BAG_REST",
 `!b:'a bag. SUB_BAG (BAG_REST b) b`,
 NORM_TAC arith_ss [BAG_REST_DEF,SUB_BAG,BAG_INN,BAG_DIFF,EL_BAG,BAG_INSERT,
                  arithmeticTheory.GREATER_EQ]);

val PSUB_BAG_REST = Q.store_thm
("PSUB_BAG_REST",
 `!b:'a bag. ~(b = {||}) ==> PSUB_BAG (BAG_REST b) b`,
 REPEAT STRIP_TAC
   THEN IMP_RES_THEN MP_TAC BAG_CHOICE_DEF
   THEN NORM_TAC arith_ss [BAG_REST_DEF,PSUB_BAG, SUB_BAG,BAG_IN, BAG_INN,
       BAG_DIFF,EL_BAG,BAG_INSERT,EMPTY_BAG,combinTheory.K_DEF,FUN_EQ_THM]
   THENL [ALL_TAC, Q.EXISTS_TAC `BAG_CHOICE b`]
   THEN RW_TAC arith_ss []);


val SUB_BAG_DIFF_EQ = Q.store_thm
("SUB_BAG_DIFF_EQ",
 `!b1 b2. SUB_BAG b1 b2 ==> (b2 = BAG_UNION b1 (BAG_DIFF b2 b1))`,
 RW_TAC bool_ss [SUB_BAG,BAG_UNION,BAG_DIFF,BAG_INN,FUN_EQ_THM]
   THEN MATCH_MP_TAC (ARITH `a >= b ==> (a = b + (a - b))`)
   THEN POP_ASSUM (MP_TAC o Q.SPECL [`x`, `b1 x`])
   THEN RW_TAC arith_ss []);

val SUB_BAG_DIFF_EXISTS = Q.prove
(`!b1 b2. SUB_BAG b1 b2 ==> ?d. b2 = BAG_UNION b1 d`,
 PROVE_TAC [SUB_BAG_DIFF_EQ]);

val SUB_BAG_CARD = Q.store_thm
("SUB_BAG_CARD",
`!b1 b2:'a bag. FINITE_BAG b2 /\ SUB_BAG b1 b2 ==> BAG_CARD b1 <= BAG_CARD b2`,
RW_TAC bool_ss []
  THEN `?d. b2 = BAG_UNION b1 d` by PROVE_TAC [SUB_BAG_DIFF_EQ]
  THEN RW_TAC bool_ss []
  THEN `FINITE_BAG d /\ FINITE_BAG b1` by PROVE_TAC [FINITE_BAG_UNION]
  THEN Q.PAT_ASSUM `SUB_BAG x y` (K ALL_TAC)
  THEN Q.PAT_ASSUM `FINITE_BAG (BAG_UNION x y)` (K ALL_TAC)
  THEN REPEAT (POP_ASSUM MP_TAC)
  THEN Q.ID_SPEC_TAC `d`
  THEN HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT
  THEN RW_TAC arith_ss [BAG_UNION_EMPTY,BAG_UNION_INSERT]
  THEN PROVE_TAC [BAG_CARD_THM,FINITE_BAG_UNION,ARITH `x <=y ==> x <= y+1`]);

val BAG_UNION_STABLE = Q.prove
(`!b1 b2. (b1 = BAG_UNION b1 b2) = (b2 = {||})`,
 RW_TAC bool_ss [BAG_UNION,EMPTY_BAG_alt,FUN_EQ_THM] THEN
 EQ_TAC THEN DISCH_THEN (fn th => GEN_TAC THEN MP_TAC(SPEC_ALL th)) THEN
 RW_TAC arith_ss []);

val SUB_BAG_UNION_MONO = Q.store_thm
("SUB_BAG_UNION_MONO",
`!x y. SUB_BAG x (BAG_UNION x y)`,
RW_TAC arith_ss [SUB_BAG,BAG_UNION,BAG_INN]);

val PSUB_BAG_CARD = Q.store_thm
("PSUB_BAG_CARD",
`!b1 b2:'a bag. FINITE_BAG b2 /\ PSUB_BAG b1 b2 ==> BAG_CARD b1 < BAG_CARD b2`,
RW_TAC bool_ss [PSUB_BAG]
  THEN `?d. b2 = BAG_UNION b1 d` by PROVE_TAC [SUB_BAG_DIFF_EQ]
  THEN RW_TAC bool_ss []
  THEN `~(d = {||})` by PROVE_TAC [BAG_UNION_STABLE]
  THEN STRIP_ASSUME_TAC (Q.SPEC`d` BAG_cases)
  THEN RW_TAC bool_ss [BAG_UNION_INSERT]
  THEN POP_ASSUM (K ALL_TAC)
  THEN `FINITE_BAG (BAG_UNION b1 b0)`
        by PROVE_TAC[FINITE_BAG_UNION, BAG_UNION_INSERT, FINITE_BAG_THM]
  THEN PROVE_TAC [BAG_CARD_THM, ARITH `x <y+1n = x <= y`,
                  SUB_BAG_CARD, SUB_BAG_UNION_MONO]);

(* ----------------------------------------------------------------------
    A "fold"-like operation for bags, ITBAG, by analogy with the set
    theory's ITSET.
   ---------------------------------------------------------------------- *)

val ITBAG_defn = Defn.Hol_defn "ITBAG"
  `ITBAG (b: 'a bag) (acc: 'b) =
     if FINITE_BAG b then
        if b = {||} then acc
        else ITBAG (BAG_REST b) (f (BAG_CHOICE b) acc)
     else ARB`;

(* Termination of above *)
val (ITBAG_eqn0, ITBAG_IND) =
  Defn.tprove(ITBAG_defn,
    TotalDefn.WF_REL_TAC `measure (BAG_CARD o FST)` THEN
    PROVE_TAC [PSUB_BAG_CARD, PSUB_BAG_REST]);

(* derive the desired recursion equation:
     FINITE_BAG b ==>
        (ITBAG f b a = if b = {||} then a
                       else ITBAG f (BAG_REST b) (f (BAG_CHOICE b) a))
*)
val ITBAG_THM =
    GENL [``b: 'a -> num``, ``f:'a -> 'b -> 'b``, ``acc:'b``]
         (DISCH_ALL (ASM_REWRITE_RULE [Q.ASSUME `FINITE_BAG b`] ITBAG_eqn0))

val _ = save_thm("ITBAG_IND", ITBAG_IND);
val _ = save_thm("ITBAG_THM", ITBAG_THM);

val ITBAG_EMPTY = save_thm(
  "ITBAG_EMPTY",
  REWRITE_RULE [] (MATCH_MP (Q.SPEC `{||}` ITBAG_THM) FINITE_EMPTY_BAG))
 before
 export_rewrites ["ITBAG_EMPTY"];

val ITBAG_INSERT = save_thm(
  "ITBAG_INSERT",
  SIMP_RULE (srw_ss())[] (Q.SPEC `BAG_INSERT x b` ITBAG_THM))

val COMMUTING_ITBAG_INSERT = store_thm(
  "COMMUTING_ITBAG_INSERT",
  ``!f b. (!x y z. f x (f y z) = f y (f x z)) /\ FINITE_BAG b ==>
          !x a. ITBAG f (BAG_INSERT x b) a = ITBAG f b (f x a)``,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  completeInduct_on `BAG_CARD b` THEN
  FULL_SIMP_TAC (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM, AND_IMP_INTRO] THEN
  SRW_TAC [][ITBAG_INSERT, BAG_REST_DEF, EL_BAG] THEN
  Q.ABBREV_TAC `c = BAG_CHOICE (BAG_INSERT x b)` THEN
  `BAG_IN c (BAG_INSERT x b)`
     by PROVE_TAC [BAG_CHOICE_DEF, BAG_INSERT_NOT_EMPTY] THEN
  `(c = x) \/ BAG_IN c b` by PROVE_TAC [BAG_IN_BAG_INSERT] THENL [
    SRW_TAC [][],
    `?b0. b = BAG_INSERT c b0`
        by PROVE_TAC [BAG_IN_BAG_DELETE, BAG_DELETE] THEN
    `BAG_DIFF (BAG_INSERT x b) {| c |} = BAG_INSERT x b0`
        by SRW_TAC [][BAG_INSERT_commutes] THEN
    ASM_REWRITE_TAC [] THEN
    `FINITE_BAG b0` by FULL_SIMP_TAC (srw_ss()) [] THEN
    `BAG_CARD b0 < BAG_CARD b`
       by SRW_TAC [numSimps.ARITH_ss][BAG_CARD_THM] THEN
    SRW_TAC [][]
  ]);

val COMMUTING_ITBAG_RECURSES = store_thm(
  "COMMUTING_ITBAG_RECURSES",
  ``!f e b a. (!x y z. f x (f y z) = f y (f x z)) /\ FINITE_BAG b ==>
              (ITBAG f (BAG_INSERT e b) a = f e (ITBAG f b a))``,
  Q_TAC SUFF_TAC
     `!f. (!x y z.  f x (f y z) = f y (f x z)) ==>
          !b. FINITE_BAG b ==>
              !e a. ITBAG f (BAG_INSERT e b) a = f e (ITBAG f b a)` THEN1
     PROVE_TAC [] THEN
  GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [COMMUTING_ITBAG_INSERT] THEN
  HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN CONJ_TAC THENL [
    SRW_TAC [][ITBAG_EMPTY],
    SRW_TAC [][COMMUTING_ITBAG_INSERT]
  ]);

(*---------------------------------------------------------------------------*)
(* Sums and products on finite bags                                          *)
(*---------------------------------------------------------------------------*)

val BAG_GEN_SUM_def = 
 new_definition
 ("BAG_GEN_SUM_def",
  ``BAG_GEN_SUM bag n = ITBAG (+) bag n``);

val BAG_GEN_PROD_def = 
 new_definition
 ("BAG_GEN_PROD_def",
  ``BAG_GEN_PROD bag n = ITBAG $* bag n``);

val BAG_GEN_SUM_EMPTY = store_thm
("BAG_GEN_SUM_EMPTY",
 ``!n. BAG_GEN_SUM {||} n = n``,
 RW_TAC bool_ss [BAG_GEN_SUM_def,ITBAG_EMPTY]);

val BAG_GEN_PROD_EMPTY = store_thm
("BAG_GEN_PROD_EMPTY",
 ``!n. BAG_GEN_PROD {||} n = n``,
 RW_TAC bool_ss [BAG_GEN_PROD_def,ITBAG_EMPTY]);

val BAG_GEN_SUM_TAILREC = store_thm
("BAG_GEN_SUM_TAILREC",
 ``!b. FINITE_BAG b ==> 
   !x a. BAG_GEN_SUM (BAG_INSERT x b) a = BAG_GEN_SUM b (x + a)``,
 GEN_TAC THEN STRIP_TAC THEN
 SIMP_TAC bool_ss [BAG_GEN_SUM_def] THEN
 HO_MATCH_MP_TAC (SPEC_ALL COMMUTING_ITBAG_INSERT) THEN
 RW_TAC hol_ss []);

val BAG_GEN_SUM_REC = store_thm
("BAG_GEN_SUM_REC",
 ``!b. FINITE_BAG b ==> 
   !x a. BAG_GEN_SUM (BAG_INSERT x b) a = x + BAG_GEN_SUM b a``,
  GEN_TAC THEN REPEAT STRIP_TAC THEN
  SIMP_TAC bool_ss [BAG_GEN_SUM_def] THEN
  HO_MATCH_MP_TAC (SPEC_ALL COMMUTING_ITBAG_RECURSES) THEN
  RW_TAC hol_ss []);

val BAG_GEN_PROD_TAILREC = store_thm
("BAG_GEN_PROD_TAILREC",
 ``!b. FINITE_BAG b ==> 
   !x a. BAG_GEN_PROD (BAG_INSERT x b) a = BAG_GEN_PROD b (x * a)``,
 GEN_TAC THEN STRIP_TAC THEN
 SIMP_TAC bool_ss [BAG_GEN_PROD_def] THEN
 HO_MATCH_MP_TAC (SPEC_ALL COMMUTING_ITBAG_INSERT) THEN
 RW_TAC hol_ss []);

val BAG_GEN_PROD_REC = store_thm
("BAG_GEN_PROD_REC",
 ``!b. FINITE_BAG b ==> 
   !x a. BAG_GEN_PROD (BAG_INSERT x b) a = x * BAG_GEN_PROD b a``,
 GEN_TAC THEN REPEAT STRIP_TAC THEN
 SIMP_TAC bool_ss [BAG_GEN_PROD_def] THEN
 HO_MATCH_MP_TAC (SPEC_ALL COMMUTING_ITBAG_RECURSES) THEN
 RW_TAC hol_ss []);

val BAG_GEN_PROD_EQ_1 = Q.store_thm
("BAG_GEN_PROD_EQ_1",
 `!b. FINITE_BAG b ==> !e. (BAG_GEN_PROD b e = 1) ==> (e=1)`,
 HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN REPEAT STRIP_TAC THENL
 [METIS_TAC [BAG_GEN_PROD_EMPTY],
  Q.PAT_ASSUM `p=q` MP_TAC THEN 
  RW_TAC hol_ss [Once BAG_GEN_PROD_TAILREC] THEN 
  RES_TAC THEN FULL_SIMP_TAC hol_ss []]);

val BAG_GEN_PROD_ALL_ONES = Q.store_thm
("BAG_GEN_PROD_ALL_ONES",
 `!b. FINITE_BAG b ==> (BAG_GEN_PROD b 1 = 1) ==> !x. BAG_IN x b ==> (x=1)`,
 HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN REPEAT STRIP_TAC THENL
 [METIS_TAC [NOT_IN_EMPTY_BAG],
  Q.PAT_ASSUM `p=q` MP_TAC THEN
    RW_TAC hol_ss [BAG_GEN_PROD_TAILREC] THEN 
    `e=1` by METIS_TAC [BAG_GEN_PROD_EQ_1] THEN RW_TAC hol_ss [] THEN 
    `!x. BAG_IN x b ==> (x = 1)` by METIS_TAC[] THEN 
    METIS_TAC [BAG_IN_BAG_INSERT]]);

val BAG_GEN_PROD_POSITIVE = Q.store_thm
("BAG_GEN_PROD_POSITIVE",
 `!b. FINITE_BAG b ==> (!x. BAG_IN x b ==> 0 < x) ==> 0 < BAG_GEN_PROD b 1`,
 HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN REPEAT STRIP_TAC THENL
 [METIS_TAC [BAG_GEN_PROD_EMPTY,ARITH `0<1`],
  RW_TAC hol_ss [BAG_GEN_PROD_REC] THEN 
  `0 < e` by METIS_TAC [BAG_IN_BAG_INSERT] THEN
  `0 < BAG_GEN_PROD b 1` by METIS_TAC [BAG_IN_BAG_INSERT] THEN
 METIS_TAC [arithmeticTheory.LESS_MULT2]]);

val BAG_EVERY = 
 new_definition 
   ("BAG_EVERY",
    ``BAG_EVERY P b = !e. BAG_IN e b ==> P e``);

val BAG_EVERY_THM = store_thm ("BAG_EVERY_THM",
``(!P. (BAG_EVERY P EMPTY_BAG)) /\
  (!P e b. (BAG_EVERY P (BAG_INSERT e b) = P e /\ BAG_EVERY P b))``,
SIMP_TAC hol_ss [BAG_EVERY, BAG_IN_BAG_INSERT,
		 DISJ_IMP_THM, FORALL_AND_THM,
		 NOT_IN_EMPTY_BAG]);

val BAG_ALL_DISTINCT = new_definition ("BAG_ALL_DISTINCT",
  ``BAG_ALL_DISTINCT b = (!e. b e <= 1:num)``);

val BAG_ALL_DISTINCT_THM = store_thm ("BAG_ALL_DISTINCT_THM",
``BAG_ALL_DISTINCT EMPTY_BAG /\
  (!e b. (BAG_ALL_DISTINCT (BAG_INSERT e b) =
         ~(BAG_IN e b) /\ BAG_ALL_DISTINCT b))``,
SIMP_TAC hol_ss [BAG_ALL_DISTINCT, EMPTY_BAG,
		 BAG_IN, BAG_INN, BAG_INSERT,
		 COND_RAND, COND_RATOR,
		 COND_EXPAND_IMP, FORALL_AND_THM] THEN
REPEAT GEN_TAC THEN
`(b e + 1 <= 1) = (b e = 0)` by bossLib.DECIDE_TAC THEN
`~(b e >= 1) = (b e = 0)` by bossLib.DECIDE_TAC THEN
`0:num <= 1` by bossLib.DECIDE_TAC THEN
METIS_TAC[]);

val BAG_ALL_DISTINCT_BAG_MERGE = store_thm (
  "BAG_ALL_DISTINCT_BAG_MERGE",
  ``!b1 b2. BAG_ALL_DISTINCT (BAG_MERGE b1 b2) =
        (BAG_ALL_DISTINCT b1 /\  BAG_ALL_DISTINCT b2)``,
  SIMP_TAC hol_ss [BAG_ALL_DISTINCT, BAG_MERGE, 
                   GSYM FORALL_AND_THM, COND_RAND, COND_RATOR,
		   COND_EXPAND_IMP] THEN
  REPEAT STRIP_TAC THEN
  ConseqConv.CONSEQ_CONV_TAC (K ConseqConv.FORALL_EQ___CONSEQ_CONV) THEN
  GEN_TAC THEN bossLib.DECIDE_TAC);

val BAG_ALL_DISTINCT_BAG_UNION = store_thm (
  "BAG_ALL_DISTINCT_BAG_UNION",
  ``!b1 b2. 
        BAG_ALL_DISTINCT (BAG_UNION b1 b2) =
        (BAG_ALL_DISTINCT b1 /\ BAG_ALL_DISTINCT b2 /\
         BAG_DISJOINT b1 b2)``,
  SIMP_TAC hol_ss [BAG_ALL_DISTINCT, BAG_UNION,
		   BAG_DISJOINT, DISJOINT_DEF, EXTENSION,
		   NOT_IN_EMPTY, IN_INTER,
		   IN_SET_OF_BAG, BAG_IN,
     		   BAG_INN, GSYM FORALL_AND_THM] THEN
  REPEAT STRIP_TAC THEN
  ConseqConv.CONSEQ_CONV_TAC (K ConseqConv.FORALL_EQ___CONSEQ_CONV) THEN
  GEN_TAC THEN bossLib.DECIDE_TAC);

val BAG_ALL_DISTINCT_DIFF = store_thm (
  "BAG_ALL_DISTINCT_DIFF",
  ``!b1 b2. 
       BAG_ALL_DISTINCT b1 ==>
       BAG_ALL_DISTINCT (BAG_DIFF b1 b2)``,
  SIMP_TAC hol_ss [BAG_ALL_DISTINCT, BAG_DIFF] THEN
  REPEAT STRIP_TAC THEN
  `b1 e <= 1` by PROVE_TAC[] THEN
  bossLib.DECIDE_TAC);


val BAG_IN_BAG_DIFF_ALL_DISTINCT = store_thm (
  "BAG_IN_BAG_DIFF_ALL_DISTINCT",
  ``!b1 b2 e. BAG_ALL_DISTINCT b1 ==>
       (BAG_IN e (BAG_DIFF b1 b2) =
        BAG_IN e b1 /\ ~BAG_IN e b2)``,
  SIMP_TAC hol_ss [BAG_ALL_DISTINCT,
		   BAG_IN, BAG_INN, BAG_DIFF] THEN
  REPEAT STRIP_TAC THEN
  `b1 e <= 1` by PROVE_TAC[] THEN
  Cases_on `b1 e >= 1` THEN ASM_SIMP_TAC hol_ss []
);

val NOT_BAG_IN = Q.store_thm
("NOT_BAG_IN",
 `!b x. (b x = 0) = ~BAG_IN x b`,
 RW_TAC arith_ss [EQ_IMP_THM] THENL
 [STRIP_TAC THEN 
    `?b'. b = BAG_INSERT x b'` by METIS_TAC[BAG_DECOMPOSE] THEN 
    RW_TAC arith_ss [] THEN FULL_SIMP_TAC arith_ss [BAG_INSERT],
  FULL_SIMP_TAC arith_ss [BAG_IN,BAG_INN]]);

val BAG_UNION_EQ_LEFT = Q.store_thm
("BAG_UNION_EQ_LEFT",
 `!b c d. (BAG_UNION b c = BAG_UNION b d) ==> (c=d)`,
 RW_TAC arith_ss [BAG_UNION,FUN_EQ_THM]);

val lem = Q.prove
(`!b. FINITE_BAG b ==> !x a. BAG_IN x b ==> divides x (BAG_GEN_PROD b a)`,
 HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN
 RW_TAC arith_ss [NOT_IN_EMPTY_BAG,BAG_IN_BAG_INSERT] THENL
 [RW_TAC arith_ss [BAG_GEN_PROD_REC] THEN 
  METIS_TAC[DIVIDES_REFL,DIVIDES_MULT], 
  `divides x (BAG_GEN_PROD b a)` by METIS_TAC[] THEN 
  RW_TAC arith_ss [BAG_GEN_PROD_REC] THEN 
  METIS_TAC[DIVIDES_MULT,MULT_SYM]]);

val BAG_IN_DIVIDES = Q.store_thm
("BAG_IN_DIVIDES",
 `!b x a. FINITE_BAG b /\ BAG_IN x b ==> divides x (BAG_GEN_PROD b a)`,
 METIS_TAC [lem]);

val BAG_GEN_PROD_UNION_LEM = Q.store_thm
("BAG_GEN_PROD_UNION_LEM",
 `!b1. FINITE_BAG b1 ==>
  !b2 a b. FINITE_BAG b2 ==> 
            (BAG_GEN_PROD (BAG_UNION b1 b2) (a * b) = 
             BAG_GEN_PROD b1 a * BAG_GEN_PROD b2 b)`,
 HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN CONJ_TAC THENL
  [RW_TAC arith_ss [BAG_GEN_PROD_EMPTY,BAG_UNION_EMPTY] THEN 
    Q.ID_SPEC_TAC `b` THEN Q.ID_SPEC_TAC `a` THEN 
    POP_ASSUM MP_TAC THEN Q.ID_SPEC_TAC `b2` THEN 
    HO_MATCH_MP_TAC STRONG_FINITE_BAG_INDUCT THEN 
    RW_TAC arith_ss [BAG_GEN_PROD_EMPTY,BAG_UNION_EMPTY] THEN
    RW_TAC arith_ss [BAG_GEN_PROD_REC],
  REPEAT STRIP_TAC THEN
    RW_TAC arith_ss [BAG_GEN_PROD_REC,BAG_UNION_INSERT] THEN
    `FINITE_BAG (BAG_UNION b1 b2)` by METIS_TAC [FINITE_BAG_UNION] THEN
    RW_TAC arith_ss [BAG_GEN_PROD_REC] THEN
    METIS_TAC [MULT_ASSOC]]);

val BAG_GEN_PROD_UNION = Q.store_thm
("BAG_GEN_PROD_UNION",
 `!b1 b2. FINITE_BAG b1 /\ FINITE_BAG b2 ==> 
            (BAG_GEN_PROD (BAG_UNION b1 b2) 1 = 
             BAG_GEN_PROD b1 1 * BAG_GEN_PROD b2 1)`,
 METIS_TAC [BAG_GEN_PROD_UNION_LEM, ARITH `1 * 1 = 1`]);


val _ = export_theory();
