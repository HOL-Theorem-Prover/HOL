(* app load ["bossLib","combinTheory","arithmeticTheory","prim_recTheory"]; *)
open HolKernel boolLib Q Parse bossLib simpLib numLib
     combinTheory arithmeticTheory prim_recTheory;

infix 8 by;
infix THEN THENL ++;

(* --------------------------------------------------------*)

val _ = new_theory "onestep";

(* --------------------------------------------------------*)
(* - Iterated Maps ----------------------------------------*)
(* --------------------------------------------------------*)

val IMAP_def = Define `
  IMAP G init next =
    (!a. (G 0 a = init a)) /\
    (!t a. (G (SUC t) a = next (G t a)))`;

(* --------------------------------------------------------*)
(* - Data Abstraction Criterion ---------------------------*)
(* --------------------------------------------------------*)

val ONTO_INIT_def = Define `
  ONTO_INIT psi init init' =
    !a. ?b. psi (init' b) = init a`;

(* --------------------------------------------------------*)
(* - Immersions : General, Uniform and Adjunct ------------*)
(* --------------------------------------------------------*)

val IMM_def = Define `
  IMM imm =
    ((!a. imm a 0 = 0) /\
     (!a t1 t2. t1 < t2 ==> imm a t1 < imm a t2))`;

val UIMM_def = Define `
  UIMM imm G dur =
    ((!a. 0 < dur a) /\
     (!a. imm a 0 = 0) /\
     (!a t. imm a (SUC t) = dur (G (imm a t) a) + imm a t))`;

val AUIMM_def = Define `
  AUIMM imm1 imm2 G dur1 dur2 =
    ((UIMM imm2 G dur2) /\
     (!a. 0 < dur1 a) /\
     (!a. imm1 a 0 = 0) /\
     (!a t. imm1 a (SUC t) = dur1 (G (imm2 a t) a) + imm1 a t))`;

(* --------------------------------------------------------*)
(* - Correctness Definitions ------------------------------*)
(* --------------------------------------------------------*)

val CORRECT_def = Define `
  CORRECT spec impl imm psi =
    IMM imm /\ ONTO_INIT psi (spec 0) (impl 0) /\
    (!t a. spec t (psi a) = psi (impl (imm a t) a))`;

val CORRECT_SUP_def = Define `
  CORRECT_SUP spec impl imm1 imm2 psi =
    IMM imm1 /\ IMM imm2 /\ ONTO_INIT psi (spec 0) (impl 0) /\
    (!r a. spec (imm1 a r) (psi a) = psi (impl (imm2 a r) a))`;

(* --------------------------------------------------------*)
(* - Time-Consistent State Functions ----------------------*)
(* --------------------------------------------------------*)

val TCON_def = Define `
  TCON G = !t1 t2 a. G (t1 + t2) a = G t1 (G t2 a)`;

val TCON_IMM_def = Define `
  TCON_IMM G imm =
    !t1 t2 a.
      G (imm (G (imm a t2) a) t1 + imm a t2) a =
      G (imm (G (imm a t2) a) t1) (G (imm a t2) a)`;

(* --------------------------------------------------------*)
(* - Uniform Immersions are Immersions --------------------*)
(* --------------------------------------------------------*)

val SUC_COMM_LEMMA = prove(
  `!t p. t + (SUC p + 1) = SUC (t + (p + 1))`,
  RW_TAC arith_ss []
);

val UIMM_MONO_LEMMA = prove(
  `!imm G dur a t. UIMM imm G dur ==> imm a t < imm a (SUC t)`,
  RW_TAC std_ss [UIMM_def,ADD_COMM,LESS_NOT_EQ,LESS_ADD_NONZERO]
);

val UIMM_MONO_LEMMA2 = prove(
  `!imm G dur a t p. UIMM imm G dur ==> imm a t < imm a (t + (p + 1))`,
  REPEAT STRIP_TAC
   THEN IMP_RES_TAC UIMM_MONO_LEMMA
   THEN Induct_on `p`
   THENL [
     ASM_SIMP_TAC std_ss [SYM (num_CONV ``1``),GSYM ADD1,UIMM_MONO_LEMMA],
     FULL_SIMP_TAC std_ss  [SUC_COMM_LEMMA,LESS_IMP_LESS_ADD,ADD_COMM,UIMM_def]
   ]
);

val UIMM_IS_IMM_LEMMA = store_thm("UIMM_IS_IMM_LEMMA",
  `!imm G dur. UIMM imm G dur ==> IMM imm`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC UIMM_MONO_LEMMA2
    THEN FULL_SIMP_TAC std_ss [UIMM_def]
    THEN RW_TAC std_ss [IMM_def]
    THEN IMP_RES_TAC LESS_ADD_1
    THEN ASM_SIMP_TAC std_ss [UIMM_MONO_LEMMA2]
);

(* --------------------------------------------------------*)
(* - Uniform Adjunct Immersions are Immersions ------------*)
(* --------------------------------------------------------*)


val AUIMM_MONO_LEMMA = prove(
  `!G imm1 imm2 dur1 dur2 a t. AUIMM imm1 imm2 G dur1 dur2 ==>
                               imm1 a t < imm1 a (SUC t)`,
  RW_TAC std_ss [AUIMM_def,ADD_COMM,LESS_NOT_EQ,LESS_ADD_NONZERO]
);

val AUIMM_MONO_LEMMA2 = prove(
  `!G imm1 imm2 dur1 dur2 a t p. AUIMM imm1 imm2 G dur1 dur2 ==>
                                 imm1 a t < imm1 a (t + (p + 1))`,
  REPEAT STRIP_TAC
   THEN IMP_RES_TAC AUIMM_MONO_LEMMA
   THEN Induct_on `p` THENL [
     ASM_SIMP_TAC std_ss [SYM (num_CONV ``1``),GSYM ADD1,AUIMM_MONO_LEMMA],
     FULL_SIMP_TAC std_ss [SUC_COMM_LEMMA,LESS_IMP_LESS_ADD,ADD_COMM,AUIMM_def]
  ]
);

val AUIMM_IS_IMM_LEMMA = store_thm("AUIMM_IS_IMM_LEMMA",
  `!G imm1 imm2 dur1 dur2. AUIMM imm1 imm2 G dur1 dur2 ==> (IMM imm1 /\ IMM imm2)`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC AUIMM_MONO_LEMMA2
    THEN FULL_SIMP_TAC std_ss [AUIMM_def]
    THEN IMP_RES_TAC UIMM_IS_IMM_LEMMA
    THEN RW_TAC std_ss [IMM_def]
    THEN IMP_RES_TAC LESS_ADD_1
    THEN ASM_SIMP_TAC std_ss [AUIMM_MONO_LEMMA2]
);

(* --------------------------------------------------------*)
(* - Time-Consistency Results -----------------------------*)
(* --------------------------------------------------------*)

val TC_IMP_IMAP = store_thm("TC_IMP_IMAP",
  `!G. TCON G ==> ?init next. IMAP G init next`,
  RW_TAC std_ss [TCON_def,IMAP_def]
    THEN EXISTS_TAC `G 0`
    THEN EXISTS_TAC `G (SUC 0)`
    THEN POP_ASSUM (fn th => ASSUME_TAC (GEN_ALL (ONCE_REWRITE_RULE [ADD_COMM] (SPECL [`1`,`t`] th))))
    THEN ASM_SIMP_TAC std_ss [ADD1,SYM ONE]
);

val TC_LEMMA = store_thm("TC_LEMMA",
  `!G init next. IMAP G init next ==> (TCON G = (!t a. init (G t a) = G t a))`,
  RW_TAC std_ss [TCON_def,IMAP_def]
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THENL [
       POP_ASSUM (fn th => GEN_REWRITE_TAC (ONCE_DEPTH_CONV o RAND_CONV) empty_rewrites
                                           [(REDUCE_RULE (SPECL [`0`,`t`] th))])
         THEN ASM_REWRITE_TAC [],
     Induct_on `t1`
       THEN ASM_SIMP_TAC std_ss [ADD_CLAUSES]
    ]
);

val TC_I_LEMMA = store_thm("TC_I_LEMMA",
  `!G next. IMAP G I next ==> TCON G`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC TC_LEMMA
    THEN ASM_SIMP_TAC std_ss [I_THM]
);

val TC_IMP_TC_IMM = store_thm("TC_IMP_TC_IMM",
  `!G. TCON G ==> !Imm. TCON_IMM G Imm`,
  RW_TAC std_ss [TCON_def,TCON_IMM_def]
);
  
val FUNPOW_THM = store_thm("FUNPOW_THM",
  `!f n x. FUNPOW f n (f x) = f (FUNPOW f n x)`,
  Induct_on `n` THEN ASM_REWRITE_TAC [FUNPOW]
);

val FUNPOW_THM2 = store_thm("FUNPOW_THM2",
  `!f n x. FUNPOW f (SUC n) x = f (FUNPOW f n x)`,
  Induct_on `n` THEN RW_TAC std_ss [FUNPOW,FUNPOW_THM]
);

val FUNPOW_EVAL = store_thm("FUNPOW_EVAL",
  `!f n x. FUNPOW f n x = if n = 0 then x else FUNPOW f (n-1) (f x)`,
  Induct_on `n` THEN RW_TAC arith_ss [FUNPOW]
);

val FUNPOW_COMP_LEMMA = prove(
  `!f a b x. FUNPOW f (a+b) x = FUNPOW f a (FUNPOW f b x)`,
  Induct_on `b` THEN ASM_REWRITE_TAC [ADD_CLAUSES,FUNPOW]
);

val STATE_FUNPOW_LEMMA = store_thm("STATE_FUNPOW_LEMMA",
  `!G init next t a. IMAP G init next ==> (G t a = FUNPOW next t (init a))`,
  REWRITE_TAC [IMAP_def]
   THEN REPEAT STRIP_TAC
   THEN Induct_on `t`
   THEN ASM_REWRITE_TAC [FUNPOW,FUNPOW_THM]
);

val TC_IMM_LEMMA = store_thm("TC_IMM_LEMMA",
  `!G init next imm. (IMM imm /\ (IMAP G init next)) ==>
     (TCON_IMM G imm = (!t a. init (G (imm a t) a) = G (imm a t) a))`,
  RW_TAC std_ss [IMM_def,TCON_IMM_def]
   THEN EQ_TAC
   THEN REPEAT STRIP_TAC THENL [
     RULE_ASSUM_TAC (REWRITE_RULE [IMAP_def])
       THEN POP_ASSUM (fn th => ASSUME_TAC (SPECL [`0`,`t`] th))
       THEN PAT_ASSUM `!a. imm a 0 = 0` (fn th => RULE_ASSUM_TAC (SIMP_RULE arith_ss [th]))
       THEN POP_ASSUM (fn th => GEN_REWRITE_TAC (ONCE_DEPTH_CONV o RAND_CONV) empty_rewrites [th])
       THEN ASM_SIMP_TAC std_ss [],
     IMP_RES_TAC STATE_FUNPOW_LEMMA
       THEN ASSUME_TAC FUNPOW_COMP_LEMMA
       THEN ASM_REWRITE_TAC []
   ]
);

(* --------------------------------------------------------*)
(* - Time-Consistency One-Step Theorems -------------------*)
(* --------------------------------------------------------*)

val SPLIT_ITER_LEMMA = prove(
  `!G init next Imm dur t a. IMAP G init next ==>
    (G (SUC t) a = (FUNPOW next 1 (G t a)))`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC STATE_FUNPOW_LEMMA
    THEN FULL_SIMP_TAC std_ss [FUNPOW_COMP_LEMMA,UIMM_def,ONE,
                               ADD_CLAUSES,FUNPOW,FUNPOW_THM]
);

val TC_ONE_STEP_THM = store_thm("TC_ONE_STEP_THM",
  `!G init next. IMAP G init next ==>
    (TCON G =
      ((!a. init (G 0 a) = G 0 a) /\
       (!a. init (G 1 a) = G 1 a)))`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC TC_LEMMA
    THEN NTAC 2 (POP_ASSUM (K ALL_TAC))
    THEN POP_ASSUM (fn th => REWRITE_TAC [th])
    THEN EQ_TAC  THENL [
      RW_TAC std_ss [],
      REPEAT STRIP_TAC
        THEN Induct_on `t` THENL [
          ASM_REWRITE_TAC [],
          IMP_RES_TAC SPLIT_ITER_LEMMA
            THEN POP_ASSUM (fn th => REWRITE_TAC [th])
            THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [SYM th])
            THEN IMP_RES_TAC STATE_FUNPOW_LEMMA
            THEN POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
            THEN ASM_REWRITE_TAC []
        ]
    ]
);

val SPLIT_ITER_LEMMA' = prove(
  `!G init next imm dur t a. (IMAP G init next /\ UIMM imm G dur) ==>
    ((G (dur (init (G (imm a t) a)) + imm a t) a) =
    (FUNPOW next (imm (G (imm a t) a) 1) (G (imm a t) a)))`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC STATE_FUNPOW_LEMMA
    THEN FULL_SIMP_TAC std_ss [FUNPOW_COMP_LEMMA,UIMM_def,ONE,
                               ADD_CLAUSES,FUNPOW,FUNPOW_THM]
);

val TC_IMM_ONE_STEP_THM = store_thm("TC_IMM_ONE_STEP_THM",
  `!G init next imm dur. (IMAP G init next /\ UIMM imm G dur) ==>
    (TCON_IMM G imm =
      ((!a. init (G (imm a 0) a) = G (imm a 0) a) /\
       (!a. init (G (imm a 1) a) = G (imm a 1) a)))`,
  REPEAT STRIP_TAC
    THEN IMP_RES_TAC UIMM_IS_IMM_LEMMA
    THEN IMP_RES_TAC TC_IMM_LEMMA
    THEN NTAC 2 (POP_ASSUM (K ALL_TAC))
    THEN ASM_REWRITE_TAC []
    THEN EQ_TAC 
    THEN STRIP_TAC THENL [
        ASM_REWRITE_TAC [],
        Induct_on `t` THENL [
          ASM_REWRITE_TAC [],
          GEN_TAC
            THEN PAT_ASSUM `UIMM Imm G dur`
                 (fn th => REWRITE_TAC [REWRITE_RULE [UIMM_def] th] THEN
                 ASSUME_TAC th)
            THEN PAT_ASSUM `!a. init (G (Imm a t) a) = G (Imm a t) a`
                 (fn th => (ONCE_REWRITE_TAC [GSYM th] THEN
                 ASSUME_TAC th))
            THEN IMP_RES_TAC SPLIT_ITER_LEMMA'
            THEN POP_ASSUM (fn th => REWRITE_TAC [th])
            THEN POP_ASSUM (fn th => (ONCE_REWRITE_TAC [GSYM th] THEN
                 ASSUME_TAC th))
            THEN IMP_RES_TAC STATE_FUNPOW_LEMMA
            THEN POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
            THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
            THEN ASM_REWRITE_TAC []
        ]
    ]
);

(* --------------------------------------------------------*)
(* - Correctnes One-Step Theorems -------------------------*)
(* --------------------------------------------------------*)

val ONE_STEP_LEMMA = prove(
  `!G init next imm dur t a. (IMAP G init next /\ UIMM imm G dur /\
  TCON_IMM G imm) ==>
  (imm a (SUC t) = (imm (G (imm a t) a) 1 + imm a t))`,
  REPEAT STRIP_TAC
   THEN IMP_RES_TAC UIMM_IS_IMM_LEMMA
   THEN IMP_RES_TAC TC_IMM_LEMMA
   THEN FULL_SIMP_TAC std_ss [UIMM_def,ONE,ADD_CLAUSES,IMAP_def]
);

val ONE_STEP_THM = store_thm("ONE_STEP_THM",
  `!spec impl initf nextf initg nextg imm dur psi.
    (UIMM imm impl dur /\ ONTO_INIT psi initf initg /\
     IMAP spec initf nextf /\
     IMAP impl initg nextg /\
     TCON spec /\ TCON_IMM impl imm) ==>
    (CORRECT spec impl imm psi =
    (!a. spec 0 (psi a) = psi (impl (imm a 0) a)) /\
    (!a. spec 1 (psi a) = psi (impl (imm a 1) a)))`,
  RW_TAC std_ss [CORRECT_def,TCON_def]
    THEN IMP_RES_TAC ONE_STEP_LEMMA
    THEN NTAC 2 (POP_ASSUM (K ALL_TAC))
    THEN RULE_ASSUM_TAC (REWRITE_RULE [IMAP_def,GSYM FUN_EQ_THM])
    THEN EQ_TAC THENL [
      RW_TAC std_ss [],
      REPEAT STRIP_TAC THENL [
        IMP_RES_TAC UIMM_IS_IMM_LEMMA,
        ASM_REWRITE_TAC [],
        Induct_on `t` THENL [
          ASM_REWRITE_TAC [],
          PAT_ASSUM `!t a. imm a (SUC t) = imm (impl (imm a t) a) 1 + imm a t`
                 (fn th => REWRITE_TAC [th])
            THEN PAT_ASSUM `TCON_IMM impl imm`
                 (fn th => REWRITE_TAC [REWRITE_RULE [TCON_IMM_def] th])
            THEN PAT_ASSUM `!a. spec 1 (psi a) = psi (impl (imm a 1) a)`
                 (fn th => REWRITE_TAC [ONE,GSYM th])
            THEN POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
            THEN PAT_ASSUM `!t1 t2 a. spec (t1 + t2) a = spec t1 (spec t2 a)`
                 (fn th => REWRITE_TAC [SYM (num_CONV ``1``),GSYM (SPECL [`SUC 0`,`t`] th)])
            THEN SIMP_TAC arith_ss [ADD1]
        ]
      ]
    ]
);
      
(* --------------------------------------------------------*)

val ONE_STEP_SUP_LEMMA = prove(
  `!G init next Imm1 Imm2 dur1 dur2 r a.
  AUIMM Imm1 Imm2 G dur1 dur2 /\ IMAP G init next /\
  TCON_IMM G Imm2 ==>
  (Imm1 a (SUC r) = (Imm1 (G (Imm2 a r) a) 1 + Imm1 a r))`,
  REPEAT STRIP_TAC
   THEN IMP_RES_TAC AUIMM_IS_IMM_LEMMA
   THEN IMP_RES_TAC TC_IMM_LEMMA
   THEN FULL_SIMP_TAC std_ss [AUIMM_def,UIMM_def,ONE,ADD_CLAUSES,IMAP_def]
);

val ONE_STEP_SUP_THM = store_thm("ONE_STEP_SUP_THM",
  `!spec impl initf nextf initg nextg imm1 imm2 dur1 dur2 psi.
    (AUIMM imm1 imm2 impl dur1 dur2 /\
     ONTO_INIT psi initf initg /\
     IMAP spec initf nextf /\
     IMAP impl initg nextg /\
     TCON spec /\ TCON_IMM impl imm2) ==>
    (CORRECT_SUP spec impl imm1 imm2 psi =
    (!a. spec (imm1 a 0) (psi a) = psi (impl (imm2 a 0) a)) /\
    (!a. spec (imm1 a 1) (psi a) = psi (impl (imm2 a 1) a)))`,
  RW_TAC std_ss [CORRECT_SUP_def,TCON_def]
    THEN PAT_ASSUM `IMAP spec initf nextf`
         (fn th => ASSUME_TAC (CONJ th (CONJUNCT1 (REWRITE_RULE [IMAP_def,GSYM FUN_EQ_THM] th))))
    THEN PAT_ASSUM `IMAP impl initg nextg`
         (fn th => ASSUME_TAC (CONJ th (CONJUNCT1 (REWRITE_RULE [IMAP_def,GSYM FUN_EQ_THM] th))))
    THEN EQ_TAC THENL [
      RW_TAC std_ss  [],
      REPEAT STRIP_TAC THENL [
        IMP_RES_TAC AUIMM_IS_IMM_LEMMA,
        IMP_RES_TAC AUIMM_IS_IMM_LEMMA,
        ASM_REWRITE_TAC [],
        Induct_on `r` THENL [
          ASM_REWRITE_TAC [],
          FULL_SIMP_TAC std_ss []
           THEN IMP_RES_TAC ONE_STEP_SUP_LEMMA
           THEN POP_ASSUM (K ALL_TAC)
           THEN POP_ASSUM (fn th => REWRITE_TAC [th])
           THEN `UIMM imm2 impl dur2` by IMP_RES_TAC AUIMM_def
           THEN `!t a. imm2 a (SUC t) = imm2 (impl (imm2 a t) a) 1 + imm2 a t`
             by IMP_RES_TAC ONE_STEP_LEMMA
           THEN REWRITE_TAC [ONE]
           THEN POP_ASSUM (fn th => REWRITE_TAC [th])
           THEN PAT_ASSUM `TCON_IMM impl imm2`
                (fn th => REWRITE_TAC [REWRITE_RULE [TCON_IMM_def] th])
           THEN PAT_ASSUM `!a. spec (imm1 a 1) (psi a) = psi (impl (imm2 a 1) a)`
                (fn th => REWRITE_TAC [ONE,GSYM th])
           THEN POP_ASSUM (K ALL_TAC)
           THEN POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
           THEN ASM_REWRITE_TAC []
        ]
      ]
    ]
);

(* --------------------------------------------------------*)

val IMAP_COMP = store_thm("IMAP_COMP",
  `!G init next t a. IMAP G init next ==>
     (G t a = if t = 0 then init a else next (G (t-1) a))`,
   RW_TAC arith_ss [IMAP_def]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_ZERO_LT_ZERO])
    THEN IMP_RES_TAC LESS_ADD_1
    THEN RW_TAC arith_ss [GSYM ADD1]
);

val UIMM_COMP = prove(
  `!Imm G dur t a. UIMM Imm G dur ==>
     (Imm a t = if t = 0
                then 0
                else dur (G (Imm a (t-1)) a) + Imm a (t-1))`,
   RW_TAC arith_ss [UIMM_def]
    THEN RULE_ASSUM_TAC (REWRITE_RULE [NOT_ZERO_LT_ZERO])
    THEN IMP_RES_TAC LESS_ADD_1
    THEN RW_TAC arith_ss [GSYM ADD1]
);

(* --------------------------------------------------------*)

val _ = export_theory();
