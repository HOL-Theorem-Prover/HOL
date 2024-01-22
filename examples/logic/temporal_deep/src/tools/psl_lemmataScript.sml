open HolKernel Parse boolLib bossLib;

(*
quietdec := true;


loadPath := (Globals.HOLDIR ^ "/examples/PSL/path") ::
            (Globals.HOLDIR ^ "/examples/PSL/1.1/official-semantics") ::
            (Globals.HOLDIR ^ "/examples/temporal_deep/src/tools") ::
            !loadPath;

map load
 ["FinitePSLPathTheory", "PSLPathTheory", "ClockedSemanticsTheory", "UnclockedSemanticsTheory", "LemmasTheory", "RewritesTheory", "numLib",
  "RewritesPropertiesTheory", "ProjectionTheory", "SyntacticSugarTheory", "arithmeticTheory", "ModelTheory", "res_quanTools",
  "rich_listTheory", "pred_setTheory", "combinTheory", "tuerk_tacticsLib", "temporal_deep_mixedTheory",
  "set_lemmataTheory"];
*)

open FinitePSLPathTheory PSLPathTheory UnclockedSemanticsTheory ClockedSemanticsTheory LemmasTheory RewritesTheory RewritesPropertiesTheory
   ProjectionTheory SyntacticSugarTheory arithmeticTheory ModelTheory rich_listTheory pred_setTheory combinTheory
   res_quanTools numLib tuerk_tacticsLib temporal_deep_mixedTheory set_lemmataTheory listTheory;
open Sanity;

val _ = hide "S";
val _ = hide "I";

(*
show_assums := false;
show_assums := true;
show_types := true;
show_types := false;
quietdec := false;
*)




val _ = new_theory "psl_lemmata";
val std_ss = std_ss -* ["lift_disj_eq", "lift_imp_disj", "LT1_EQ0"]
val list_ss = list_ss -* ["lift_disj_eq", "lift_imp_disj", "LT1_EQ0"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj", "LT1_EQ0"]
val _ = ParseExtras.temp_loose_equality()


val IS_INFINITE_PROPER_PATH_def =
 Define
  `IS_INFINITE_PROPER_PATH f =  ?p. ((f = INFINITE p) /\ (!n. (p n = TOP) ==> (p (SUC n) = TOP)) /\
  (!n. (p n = BOTTOM) ==> (p (SUC n) = BOTTOM)))`;


val IS_FINITE_PROPER_PATH_def =
 Define
  `IS_FINITE_PROPER_PATH f =  ?p. ((f = FINITE p) /\ PATH_TOP_FREE f /\ PATH_BOTTOM_FREE f)`;


val IS_INFINITE_TOP_BOTTOM_FREE_PATH_def =
 Define
  `IS_INFINITE_TOP_BOTTOM_FREE_PATH f =  ?p. ((f = INFINITE p) /\ (!n. ?s. (p n = STATE s)))`;


val IS_INFINITE_TOP_BOTTOM_FREE_PATH___COMPLEMENT =
  store_thm
   ("IS_INFINITE_TOP_BOTTOM_FREE_PATH___COMPLEMENT",
    ``!f. IS_INFINITE_TOP_BOTTOM_FREE_PATH f ==>
          (COMPLEMENT f = f)``,

    REWRITE_TAC[IS_INFINITE_TOP_BOTTOM_FREE_PATH_def] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [COMPLEMENT_def, path_11, o_DEF] THEN
    ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
    BETA_TAC THEN GEN_TAC THEN
    `?s. p x = STATE s` by PROVE_TAC[] THEN
    ASM_REWRITE_TAC[COMPLEMENT_LETTER_def]);


val IS_INFINITE_TOP_BOTTOM_FREE_PATH___RESTN =
  store_thm
   ("IS_INFINITE_TOP_BOTTOM_FREE_PATH___RESTN",
    ``!f. IS_INFINITE_TOP_BOTTOM_FREE_PATH f ==>
          !n. IS_INFINITE_TOP_BOTTOM_FREE_PATH (RESTN f n)``,

    REWRITE_TAC[IS_INFINITE_TOP_BOTTOM_FREE_PATH_def] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [RESTN_INFINITE, path_11]);


val IS_PROPER_PATH_def =
 Define
  `IS_PROPER_PATH f =  IS_INFINITE_PROPER_PATH f \/ IS_FINITE_PROPER_PATH f`;

val BOTTOM_OMEGA_def =
 Define `BOTTOM_OMEGA = INFINITE(\n. BOTTOM)`;

val COMPLEMENT_LETTER_Cases =
 store_thm
  ("COMPLEMENT_LETTER_Cases",
   ``!l s. ((COMPLEMENT_LETTER l = STATE s) = (l = STATE s)) /\
            ((COMPLEMENT_LETTER l = TOP) = (l = BOTTOM)) /\
           ((COMPLEMENT_LETTER l = BOTTOM) = (l = TOP))``,
   Cases_on `l` THEN EVAL_TAC THEN PROVE_TAC[]);

val HEAD_ELEM =
 store_thm
  ("HEAD_ELEM",
    ``!p. HEAD p = ELEM p 0``,
    REWRITE_TAC[ELEM_def, RESTN_def]);


val RESTN_MAP =
 store_thm
  ("RESTN_MAP",
  ``!f v t. t < LENGTH v ==> (RESTN (MAP f v) t = MAP f (RESTN v t))``,
   Induct_on `v` THENL [
      EVAL_TAC THEN PROVE_TAC[],

      Induct_on `t` THENL [
         EVAL_TAC THEN PROVE_TAC[],

         EVAL_TAC THEN
         REPEAT STRIP_TAC THEN
         `t < LENGTH v` by DECIDE_TAC THEN
         PROVE_TAC[]
      ]
   ]);


val REST_RESTN =
 store_thm
  ("REST_RESTN",
   ``(!l:'a list. (REST l) = (RESTN l 1)) /\
     (!p:'a path. (REST p) = (RESTN p 1))``,

   `1 = SUC 0` by DECIDE_TAC THEN
    ASM_REWRITE_TAC [RESTN_def, FinitePSLPathTheory.RESTN_def]);


val RESTN_REST =
 store_thm
  ("RESTN_REST",
   ``(!l:'a list n. (RESTN (REST l) n) = (REST (RESTN l n))) /\
     (!p:'a path n. (RESTN (REST p) n) = (REST (RESTN p n)))``,

   SIMP_TAC arith_ss [FinitePSLPathTheory.RESTN_RESTN, RESTN_RESTN, REST_RESTN]);


val ELEM_CAT___LESS =
 store_thm
  ("ELEM_CAT___LESS",
   ``!l l' p. l < LENGTH l' ==> (ELEM (CAT (l',p)) l = EL l l')``,

   Induct_on `l` THENL [
      Cases_on `l'` THENL [
         SIMP_TAC list_ss [],
         SIMP_TAC list_ss [CAT_def, ELEM_def, RESTN_def, HEAD_CONS]
      ],

      Cases_on `l'` THENL [
         SIMP_TAC list_ss [],
         SIMP_TAC list_ss [CAT_def, ELEM_def, RESTN_def, REST_CONS] THEN PROVE_TAC [ELEM_def]
      ]
   ]);



val EL_SEL_REC =
 store_thm
  ("EL_SEL_REC",
  ``!j k l p. (j < k) ==>
    (EL j (SEL_REC k l p) = ELEM p (j+l))``,

Induct_on `l` THENL [
  SIMP_TAC std_ss [] THEN
  Induct_on `j` THENL [
    Cases_on `k` THEN SIMP_TAC std_ss [] THEN
    SIMP_TAC list_ss [SEL_REC_def, ELEM_def, RESTN_def],

    Cases_on `k` THEN SIMP_TAC std_ss [] THEN
    REPEAT STRIP_TAC THEN
    SIMP_TAC list_ss [SEL_REC_def] THEN
    Q_SPECL_NO_ASSUM 1 [`n`, `REST p`] THEN
    RES_TAC THEN
    ASM_REWRITE_TAC[ELEM_def, RESTN_def]
  ],

  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SEL_REC_REST] THEN
  Q_SPECL_NO_ASSUM 1 [`j`, `k`, `REST p`] THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC std_ss [prove (``j+SUC l = SUC(j+l)``, DECIDE_TAC)] THEN
  SIMP_TAC std_ss [ELEM_def, RESTN_def]
]);


val ELEM_CAT_SEL___LESS_EQ =
 store_thm
  ("ELEM_CAT_SEL___LESS_EQ",
   ``!v l u p. l <= u ==> (ELEM (CAT (SEL v (0, u),p)) l = ELEM v l)``,

   REPEAT STRIP_TAC THEN
   `LENGTH (SEL v (0, u)) = u -0 + 1` by PROVE_TAC[LENGTH_SEL] THEN
   ASM_SIMP_TAC arith_ss [ELEM_CAT___LESS, EL_SEL0]);


val ELEM_CAT___GREATER_EQ =
 store_thm
  ("ELEM_CAT___GREATER_EQ",
   ``!l l' p. l >= LENGTH l' ==> (ELEM (CAT (l',p)) l = ELEM p (l - (LENGTH l')))``,

   Induct_on `l` THENL [
      Cases_on `l'` THENL [
         SIMP_TAC list_ss [CAT_def],
         SIMP_TAC list_ss []
      ],

      Cases_on `l'` THENL [
         SIMP_TAC list_ss [CAT_def],

         SIMP_TAC list_ss [ELEM_def, CAT_def, REST_CONS, RESTN_def] THEN
         REPEAT STRIP_TAC THEN
         `l >= LENGTH t` by DECIDE_TAC THEN
         PROVE_TAC[ELEM_def]
      ]
   ]);


val ELEM_CAT_SEL___GREATER =
 store_thm
  ("ELEM_CAT_SEL___GREATER",
   ``!v l u p. l > u ==> (ELEM (CAT (SEL v (0, u),p)) l = ELEM p (l - SUC u))``,

   REPEAT STRIP_TAC THEN
   `LENGTH (SEL v (0, u)) = u -0 + 1` by PROVE_TAC[LENGTH_SEL] THEN
   ASM_SIMP_TAC arith_ss [ELEM_CAT___GREATER_EQ, SUC_ONE_ADD]);


val MAP_EQ_CONCAT =
 store_thm
  ("MAP_EQ_CONCAT",

   ``!f l L. (MAP f l = CONCAT L) =
            (?L'. (l = CONCAT L') /\ (L = MAP (\l. MAP f l) L'))``,

Induct_on `L` THENL [
  SIMP_TAC list_ss [CONCAT_def],

  ASM_SIMP_TAC list_ss [CONCAT_def, MAP_EQ_APPEND, GSYM LEFT_EXISTS_AND_THM,
    GSYM RIGHT_EXISTS_AND_THM] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL [
    Q_TAC EXISTS_TAC `l10::L'` THEN
    ASM_SIMP_TAC list_ss [CONCAT_def],


    Cases_on `L'` THEN
    FULL_SIMP_TAC list_ss [CONCAT_def] THEN
    Q_TAC EXISTS_TAC `h'` THEN
    Q_TAC EXISTS_TAC `t` THEN
    ASM_SIMP_TAC list_ss []
  ]
])

val CONCAT_APPEND =
 store_thm
  ("CONCAT_APPEND",
   ``!l1 l2. CONCAT (l1 <> l2) = (CONCAT l1 <> CONCAT l2)``,

   Induct_on `l1` THENL [
      SIMP_TAC list_ss [CONCAT_def],
      ASM_SIMP_TAC list_ss [CONCAT_def]
   ]);

val IS_FINITE_EXISTS =
 store_thm
  ("IS_FINITE_EXISTS",
   ``!w. IS_FINITE w = ?p. w = FINITE p``,

     Cases_on `w` THEN
     REWRITE_TAC[IS_FINITE_def] THEN
     METIS_TAC[path_distinct]);


val REST_REPLICATE =
 store_thm
  ("REST_REPLICATE",

   ``!n e. n > 0 ==> ((REST (REPLICATE n e)) = (REPLICATE (PRE n) e))``,

   Induct_on `n` THENL [
      SIMP_TAC arith_ss [],
      SIMP_TAC list_ss [REPLICATE, FinitePSLPathTheory.REST_def]
   ]);


val RESTN_REPLICATE =
 store_thm
  ("RESTN_REPLICATE",
   ``!m n e. m <= n ==> ((RESTN (REPLICATE n e)) m = (REPLICATE (n-m) e))``,

   Induct_on `m` THENL [
      SIMP_TAC arith_ss [FinitePSLPathTheory.RESTN_def],

      ASM_SIMP_TAC arith_ss [FinitePSLPathTheory.RESTN_def, RESTN_REST] THEN
      REPEAT STRIP_TAC THEN
      `n - m > 0` by DECIDE_TAC THEN
      `PRE (n - m) = (n - SUC m)` by DECIDE_TAC THEN
      ASM_SIMP_TAC std_ss [REST_REPLICATE]
   ]);


val FIRSTN_REPLICATE =
 store_thm
  ("FIRSTN_REPLICATE",
   ``!m n e. m <= n ==> ((FIRSTN m (REPLICATE n e)) = (REPLICATE m e))``,

   Induct_on `m` THENL [
      SIMP_TAC list_ss [FIRSTN, REPLICATE],

      REPEAT STRIP_TAC THEN
      `~(n = 0)` by DECIDE_TAC THEN
      `?n'. n = SUC n'` by PROVE_TAC[num_CASES] THEN
      ASM_SIMP_TAC list_ss [FIRSTN, REPLICATE]
   ]);


val ELEM_REPLICATE =
 store_thm
  ("ELEM_REPLICATE",
   ``!m n e. m < n ==> ((ELEM (REPLICATE n e)) m = e)``,

   SIMP_TAC list_ss [FinitePSLPathTheory.ELEM_def, RESTN_REPLICATE] THEN
   REPEAT STRIP_TAC THEN
   `~(n - m = 0)` by DECIDE_TAC THEN
   `?n':num. (n - m) = SUC n'` by PROVE_TAC[num_CASES] THEN
   ASM_SIMP_TAC list_ss [REPLICATE, FinitePSLPathTheory.HEAD_def]
);


val REPLICATE_CONCAT =
 store_thm
  ("REPLICATE_CONCAT",
   ``!n e v1 v2. (REPLICATE n e = (v1 <> v2)) = (?n1 n2. (v1 = REPLICATE n1 e) /\ (v2 = REPLICATE n2 e) /\ (n = n1 + n2))``,

   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      EXISTS_TAC ``LENGTH (v1:'a list)`` THEN
      EXISTS_TAC ``LENGTH (v2:'a list)`` THEN
      `LENGTH (v1 <> v2) = LENGTH (REPLICATE n e)` by PROVE_TAC[] THEN
      FULL_SIMP_TAC list_ss [LENGTH_REPLICATE] THEN
      REPEAT STRIP_TAC THENL [
         `?m. LENGTH v1 = m` by PROVE_TAC[] THEN
         `FIRSTN m (REPLICATE n e) = FIRSTN m (v1 <> v2)` by PROVE_TAC[] THEN
         `m <= LENGTH v1 /\ m <= n` by DECIDE_TAC THEN
         FULL_SIMP_TAC list_ss [FIRSTN_REPLICATE] THEN
         ASM_SIMP_TAC std_ss [FIRSTN_APPEND1] THEN
         PROVE_TAC[FIRSTN_LENGTH_ID],

         `RESTN (REPLICATE n e) (LENGTH v1) = RESTN (v1 <> v2) (LENGTH v1)` by PROVE_TAC[] THEN
         `(LENGTH v1 <= n) /\ (n - LENGTH v1 = (LENGTH v2))` by DECIDE_TAC THEN
         FULL_SIMP_TAC list_ss [RESTN_REPLICATE, RESTN_APPEND]
      ],

      ASM_REWRITE_TAC[] THEN
      REPEAT (WEAKEN_TAC (fn t => true)) THEN
      SPEC_TAC (``n1:num``,``n1:num``) THEN
      SPEC_TAC (``n2:num``,``n2:num``) THEN
      Induct_on `n1` THENL [
         SIMP_TAC list_ss [REPLICATE],
         ASM_SIMP_TAC list_ss [GSYM ADD_SUC, REPLICATE]
      ]
   ]);

val REPLICATE_11 =
 store_thm
  ("REPLICATE_11",

   ``!n e n' e'. (REPLICATE n e = REPLICATE n' e') = ((n = n') /\ ((n = 0) \/ (e = e')))``,

   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      PROVE_TAC[LENGTH_REPLICATE],

      Cases_on `n = 0` THEN ASM_REWRITE_TAC[] THEN
      `n = n'` by METIS_TAC[LENGTH_REPLICATE] THEN
      FULL_SIMP_TAC list_ss [] THEN
      `?n''. n' = SUC n''` by PROVE_TAC[num_CASES] THEN
      FULL_SIMP_TAC list_ss [REPLICATE],

      PROVE_TAC[REPLICATE],

      ASM_REWRITE_TAC[]
   ]);


val REPLICATE_SING_LIST =
 store_thm
  ("REPLICATE_SING_LIST",

   ``!n e l. ([l] = REPLICATE n e) = ((n = 1) /\ (e = l))``,

   REPEAT STRIP_TAC THEN EQ_TAC THENL [
      DISCH_TAC THEN
      `LENGTH (REPLICATE n e) = LENGTH [l]` by PROVE_TAC[] THEN
      FULL_SIMP_TAC list_ss [LENGTH_REPLICATE] THEN
      WEAKEN_TAC (fn t => true) THEN
      UNDISCH_TAC ``[l] = REPLICATE 1 e`` THEN
      `1 = SUC 0` by DECIDE_TAC THEN
      ASM_REWRITE_TAC [REPLICATE] THEN
      SIMP_TAC list_ss [],

      REPEAT STRIP_TAC THEN
      `n = SUC 0` by DECIDE_TAC THEN
      ASM_REWRITE_TAC [REPLICATE]
   ]);


val SEL_x_OMEGA___REPLICATE =
 store_thm
  ("SEL_x_OMEGA___REPLICATE",
   ``!n m x. (SEL (INFINITE (\n. x)) (n,m)) = REPLICATE (m-n+1) x``,

   REPEAT STRIP_TAC THEN
   `?t:num. (m-n+1) = t` by PROVE_TAC[] THEN
   ASM_REWRITE_TAC[SEL_def] THEN
   WEAKEN_TAC (fn t => true) THEN
   Induct_on `t` THENL [
      SIMP_TAC list_ss [SEL_REC_def, REPLICATE],

      SIMP_TAC list_ss [SEL_REC_SUC, REPLICATE, ELEM_INFINITE] THEN
      Cases_on `t` THENL [
         SIMP_TAC list_ss [SEL_REC_def, REPLICATE],
         ASM_SIMP_TAC list_ss [SEL_REC_def, REST_INFINITE]
      ]
   ]);


val SEL_TOP_BOTTOM_OMEGA___REPLICATE =
 store_thm
  ("SEL_TOP_BOTTOM_OMEGA___REPLICATE",

   ``(!n m. (SEL TOP_OMEGA (n,m)) = REPLICATE (m-n+1) TOP) /\
     (!n m. (SEL BOTTOM_OMEGA (n,m)) = REPLICATE (m-n+1) BOTTOM)``,

   REWRITE_TAC[TOP_OMEGA_def, BOTTOM_OMEGA_def, SEL_x_OMEGA___REPLICATE]);


val CAT_SEL_x_OMEGA_x_OMEGA =
 store_thm
  ("CAT_SEL_x_OMEGA_x_OMEGA",

   ``!m x. (CAT (SEL (INFINITE (\n. x)) (0,m),INFINITE (\n. x))) = INFINITE (\n. x)``,

   REPEAT STRIP_TAC THEN
   `IS_INFINITE (CAT (SEL (INFINITE (\n. x)) (0,m),INFINITE (\n. x)))` by PROVE_TAC[CAT_INFINITE] THEN
   `?q. (CAT (SEL (INFINITE (\n. x)) (0,m),INFINITE (\n. x))) = INFINITE q` by PROVE_TAC[IS_INFINITE_EXISTS] THEN
   ASM_REWRITE_TAC[path_11, FUN_EQ_THM] THEN
   ONCE_REWRITE_TAC[GSYM ELEM_INFINITE] THEN
   GEN_TAC THEN
   Cases_on `x' > m` THENL [
      `ELEM (INFINITE q) x' = ELEM (INFINITE (\n. x)) (x' - SUC m)` by PROVE_TAC[ELEM_CAT_SEL___GREATER] THEN
      ASM_SIMP_TAC std_ss [ELEM_INFINITE],

      `x' <= m` by DECIDE_TAC THEN
      `ELEM (INFINITE q) x' = ELEM (INFINITE (\n. x)) x'` by PROVE_TAC[ELEM_CAT_SEL___LESS_EQ] THEN
      ASM_SIMP_TAC std_ss [ELEM_INFINITE]
   ]);


val SEL_NOT_EMPTY_LIST =
 store_thm
  ("SEL_NOT_EMPTY_LIST",
   ``!v m n. ~(SEL v (n, m) = [])``,

   REPEAT GEN_TAC THEN
   REWRITE_TAC[SEL_def] THEN
   `(m - n) + 1 = SUC (m - n)` by DECIDE_TAC THEN
   ASM_REWRITE_TAC[SEL_REC_SUC] THEN
   SIMP_TAC list_ss []);


val TOP_ITER___EQ___REPLICATE_TOP =
 store_thm
  ("TOP_ITER___EQ___REPLICATE_TOP",
   ``!n. TOP_ITER n = REPLICATE n TOP``,

   Induct_on `n` THENL [
      REWRITE_TAC[TOP_ITER_def, REPLICATE],
      ASM_SIMP_TAC list_ss [TOP_ITER_def, REPLICATE]
   ]);


val IS_INFINITE_COMPLEMENT =
 store_thm
  ("IS_INFINITE_COMPLEMENT",
   ``!v. IS_INFINITE v ==> IS_INFINITE (COMPLEMENT v)``,


   Cases_on `v` THEN REWRITE_TAC [IS_INFINITE_def] THEN
   REWRITE_TAC[COMPLEMENT_def, IS_INFINITE_def]
);


val IS_FINITE_COMPLEMENT =
 store_thm
  ("IS_FINITE_COMPLEMENT",
   ``!v. IS_FINITE v ==> IS_FINITE (COMPLEMENT v)``,


   Cases_on `v` THEN REWRITE_TAC [IS_FINITE_def] THEN
   REWRITE_TAC[COMPLEMENT_def, IS_FINITE_def]
);


val IN_LESSX_REWRITE =
 store_thm
  ("IN_LESSX_REWRITE",
   ``!(m:num) (x:xnum). (m IN LESS x) = (m < x)``,

   Cases_on `x` THEN
   REWRITE_TAC[IN_LESSX, LS]);


val LENGTH_RESTN_LE =
 store_thm
  ("LENGTH_RESTN_LE",
   ``!n p. IS_FINITE p /\ n <= LENGTH p
           ==> (LENGTH(RESTN p n) = LENGTH p - n)``,

   Induct_on `n` THENL [
      REWRITE_TAC [RESTN_def] THEN
      Cases_on `LENGTH p` THEN SIMP_TAC arith_ss [LENGTH_def, SUB_xnum_num_def, xnum_11],

      REWRITE_TAC [RESTN_def] THEN
      REPEAT STRIP_TAC THEN
      `IS_FINITE (REST p)` by PROVE_TAC[IS_FINITE_REST] THEN
      `n <= LENGTH (REST p)` by (Cases_on `p` THEN
         FULL_SIMP_TAC arith_ss [REST_def, LENGTH_def, LE_num_xnum_def, LENGTH_TL]) THEN
      `LENGTH (RESTN (REST p) n) = LENGTH (REST p) - n` by PROVE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN
      Cases_on `p` THEN
      FULL_SIMP_TAC arith_ss [REST_def, LENGTH_def, LE_num_xnum_def, LENGTH_TL,
         xnum_11, SUB_xnum_num_def]
   ]);


val LENGTH_RESTN_THM_LE =
 store_thm
  ("LENGTH_RESTN_THM_LE",
   ``!n p. (n <= LENGTH p)
           ==> (LENGTH(RESTN p n) = LENGTH p - n)``,

   Cases_on `p` THENL [
      METIS_TAC[LENGTH_RESTN_LE, IS_FINITE_def],
      SIMP_TAC arith_ss [LENGTH_def, RESTN_INFINITE, SUB_xnum_num_def]
   ]);


val FINITE_INFINITE_PROPER_PATH_DISTINCT =
 store_thm
  ("FINITE_INFINITE_PROPER_PATH_DISTINCT",
   ``!v. ~(IS_INFINITE_PROPER_PATH v /\ IS_FINITE_PROPER_PATH v)``,

   SIMP_TAC std_ss [IS_INFINITE_PROPER_PATH_def, IS_FINITE_PROPER_PATH_def] THEN
   Cases_on `v` THEN
   SIMP_TAC std_ss [path_distinct]);


val COMPLEMENT_CONS =
 store_thm
  ("COMPLEMENT_CONS",
   ``!h v. COMPLEMENT (CONS (h, v)) = CONS (COMPLEMENT_LETTER h, COMPLEMENT v)``,

   Cases_on `v` THENL [
      REWRITE_TAC[PSLPathTheory.CONS_def, COMPLEMENT_def, GSYM MAP],

      SIMP_TAC std_ss [PSLPathTheory.CONS_def, COMPLEMENT_def, FUN_EQ_THM, path_11] THEN
      PROVE_TAC[]
   ]);


val COMPLEMENT_CAT =
 store_thm
  ("COMPLEMENT_CAT",
   ``!p v. COMPLEMENT (CAT (p, v)) = CAT (MAP COMPLEMENT_LETTER p, COMPLEMENT v)``,

   Induct_on `p` THENL [
      REWRITE_TAC [CAT_def, MAP],
      REWRITE_TAC [CAT_def, MAP, COMPLEMENT_CONS] THEN PROVE_TAC[]
   ]);




val TOP_BOTTOM_OMEGA___COMPLEMENT =
 store_thm
  ("TOP_BOTTOM_OMEGA___COMPLEMENT",
   ``(COMPLEMENT TOP_OMEGA = BOTTOM_OMEGA) /\
     (COMPLEMENT BOTTOM_OMEGA = TOP_OMEGA)``,

   SIMP_TAC std_ss [COMPLEMENT_def, TOP_OMEGA_def,
                    BOTTOM_OMEGA_def, path_11, o_DEF, COMPLEMENT_LETTER_def]);


val SEL_REC_CAT___LESS_EQ =
 store_thm
  ("SEL_REC_CAT___LESS_EQ",
   ``!v p n m. (n + m <= LENGTH p) ==> (SEL_REC m n (CAT (p, v)) = SEL_REC m n (FINITE p))``,

   Induct_on `m` THENL [
      SIMP_TAC arith_ss [SEL_REC_def],

      SIMP_TAC list_ss [SEL_REC_SUC] THEN
      REPEAT STRIP_TAC THENL [
         `n < LENGTH p` by DECIDE_TAC THEN
         ASM_SIMP_TAC std_ss [ELEM_CAT___LESS, ELEM_FINITE],

         `SUC n + m <= LENGTH p` by DECIDE_TAC THEN
         PROVE_TAC[]
      ]
   ]);


val SEL_CAT___LESS =
 store_thm
  ("SEL_CAT___LESS",
   ``!p v m n. (n + m < LENGTH p) ==> (SEL (CAT (p,v)) (m,n) = SEL (FINITE p) (m, n))``,

   REWRITE_TAC[SEL_def] THEN
   REPEAT STRIP_TAC THEN
   `?n':num. n - m + 1 = n'` by PROVE_TAC[] THEN
   ASM_REWRITE_TAC[] THEN
   `m + n' <= LENGTH p` by DECIDE_TAC THEN
   METIS_TAC[SEL_REC_CAT___LESS_EQ]);

val PATH_EQ_ELEM_THM =
 store_thm
  ("PATH_EQ_ELEM_THM",
   ``!v w. (v = w) = ((LENGTH v = LENGTH w) /\ (!j. j < LENGTH v ==> (ELEM v j = ELEM w j)))``,

   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      ASM_REWRITE_TAC[],
      ASM_REWRITE_TAC[],

      Cases_on `v` THEN
      Cases_on `w` THEN
      FULL_SIMP_TAC list_ss [ELEM_FINITE, LENGTH_def, path_11, xnum_11, LS, xnum_distinct,
         ELEM_INFINITE] THENL [

         PROVE_TAC[LIST_EQ_REWRITE],
         PROVE_TAC[FUN_EQ_THM]
      ]
   ]);





val RESTN_CAT___LESS =
 store_thm
  ("RESTN_CAT___LESS",
   ``!p v l. (l < LENGTH p) ==> ((RESTN (CAT (p, v)) l) = CAT (RESTN p l, v))``,

   Induct_on `l` THENL [
      SIMP_TAC std_ss [RESTN_def, FinitePSLPathTheory.RESTN_def],

      Cases_on `p` THEN SIMP_TAC list_ss [] THEN
      SIMP_TAC list_ss [RESTN_def, CAT_def, FinitePSLPathTheory.RESTN_def,
                        FinitePSLPathTheory.REST_def, REST_CONS] THEN
      PROVE_TAC[]
   ]);


val RESTN_CAT___EQ =
 store_thm
  ("RESTN_CAT___EQ",
   ``!p v. (RESTN (CAT (p, v)) (LENGTH p)) = v``,

   Induct_on `LENGTH (p:'a list)` THENL [
      REPEAT STRIP_TAC THEN
      `p = []` by (Cases_on `p` THEN FULL_SIMP_TAC list_ss []) THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC list_ss [CAT_def, RESTN_def],

      Cases_on `p` THEN SIMP_TAC list_ss [] THEN
      REPEAT STRIP_TAC THEN
      SIMP_TAC std_ss [RESTN_def, CAT_def, REST_CONS] THEN
      PROVE_TAC[]
   ]);


val RESTN_CAT___GREATER_EQ =
 store_thm
  ("RESTN_CAT___GREATER_EQ",
   ``!p v l. (l >= LENGTH p) ==> ((RESTN (CAT (p, v)) l) = RESTN v (l- LENGTH p))``,

   Induct_on `l:num - (LENGTH (p:'a list))` THENL [
      REPEAT STRIP_TAC THEN
      `l = LENGTH p` by DECIDE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC arith_ss [RESTN_CAT___EQ, RESTN_def],

      REPEAT STRIP_TAC THEN
      `~(l = 0)` by DECIDE_TAC THEN
      `?l'. l = SUC l'` by PROVE_TAC[num_CASES] THEN
      ASM_SIMP_TAC std_ss [RESTN_def, RESTN_REST] THEN
      `(l' >= LENGTH p) /\ (v = l' - LENGTH p) /\ (SUC l' - LENGTH p = l' - LENGTH p + 1)` by DECIDE_TAC THEN
      `RESTN (CAT (p,v')) l' = RESTN v' (l' - LENGTH p)` by PROVE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[RESTN_RESTN, REST_RESTN]
   ]);


val SEG_EL =
 store_thm
  ("SEG_EL",
   ``!n' n m l. (n + m <= LENGTH l /\ n' < n) ==> (EL n' (SEG n m l) = EL (n'+m) l)``,

   SIMP_TAC list_ss [EL_SEG, LENGTH_SEG, SEG_SEG]);


val SEG_SUC =
 store_thm
  ("SEG_SUC",
   ``!n m l. (LENGTH l > m) ==> (SEG (SUC n) m l = (EL m l)::SEG n (SUC m) l)``,

   Induct_on `m` THENL [
      Cases_on `l` THEN
      SIMP_TAC list_ss [SEG] THEN
      `1 = SUC 0` by DECIDE_TAC THEN
      Cases_on `n` THEN
      ASM_REWRITE_TAC[SEG],

      Cases_on `l` THEN
      SIMP_TAC list_ss [SEG] THEN
      REPEAT STRIP_TAC THEN
      `LENGTH t > m` by DECIDE_TAC THEN
      RES_TAC THEN
      ASM_SIMP_TAC list_ss [] THEN
      Cases_on `n` THEN
      ASM_REWRITE_TAC[SEG]
   ]);


val SEG_SING_LIST =
 store_thm
  ("SEG_SING_LIST",
   ``!n m l. ((m < LENGTH l) /\ (n > 0)) ==> ([HD (SEG n m l)] = SEG 1 m l)``,

   Induct_on `m` THENL [
      Cases_on `l` THEN Cases_on `n` THEN
      ASM_SIMP_TAC list_ss [SEG] THEN
      `1 = SUC 0` by DECIDE_TAC THEN
      PROVE_TAC [SEG],

      Cases_on `l` THEN Cases_on `n` THEN
      ASM_SIMP_TAC list_ss [SEG] THEN
      `1 = SUC 0` by DECIDE_TAC THEN
      ONCE_ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SEG]
   ]);


val SEG_SPLIT =
 store_thm
  ("SEG_SPLIT",
   ``!n1 n2 m l. (n1+n2+m <= LENGTH l) ==> (SEG (n1+n2) m l = (SEG n1 m l ++ SEG n2 (n1+m) l))``,

   Induct_on `n1` THEN
   SIMP_TAC list_ss [SEG] THEN
   REPEAT STRIP_TAC THEN
   `n1 + (SUC n2) + m <= LENGTH l` by DECIDE_TAC THEN
   RES_TAC THEN
   `n2 + SUC n1 = n1 + SUC n2` by DECIDE_TAC THEN
   ASM_REWRITE_TAC[] THEN
   `(n1 + 1 + m <= LENGTH l) /\ (SUC n1 = n1 + 1)` by DECIDE_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC[] THEN
   Tactical.REVERSE (SUBGOAL_THEN ``SEG (SUC n2) (n1 + m) (l:'a list) = SEG 1 (n1 + m) l ++ SEG n2 (m + (n1 + 1)) l`` ASSUME_TAC) THEN1 (
      ASM_REWRITE_TAC[APPEND_ASSOC]
   ) THEN

   `(LENGTH l > n1 + m) /\ 1:num > 0:num /\ (m + n1 < LENGTH l)` by DECIDE_TAC THEN
   `SEG 1 (m + n1) l = [HD (SEG 1 (m + n1) l)]` by PROVE_TAC[SEG_SING_LIST] THEN
   ASM_SIMP_TAC list_ss [SEG_SUC] THEN
   ONCE_ASM_REWRITE_TAC[] THEN
   SIMP_TAC list_ss [SUC_ONE_ADD] THEN
   PROVE_TAC[EL_SEG]);



val EL_FIRSTN =
 store_thm
  ("EL_FIRSTN",
   ``!m n l. (m <= LENGTH l /\ n < m) ==> (EL n (FIRSTN m l) = EL n l)``,

   Induct_on `m` THENL [
      SIMP_TAC arith_ss [],

      REPEAT STRIP_TAC THEN
      Cases_on `l` THEN FULL_SIMP_TAC list_ss [] THEN
      SIMP_TAC std_ss [FIRSTN] THEN
      Cases_on `n` THEN SIMP_TAC list_ss [] THEN
      `n' < m` by DECIDE_TAC THEN
      PROVE_TAC[]
   ]);


val LENGTH_CAT_SEL_TOP_OMEGA =
 store_thm
  ("LENGTH_CAT_SEL_TOP_OMEGA",
   ``!l v. LENGTH (CAT (SEL v (0,l),TOP_OMEGA)) = INFINITY``,

   REPEAT STRIP_TAC THEN
   REWRITE_TAC[TOP_OMEGA_def, LENGTH_CAT]);


val MEM_SEL_REC =
 store_thm
  ("MEM_SEL_REC",
    ``!x m n p. MEM x (SEL_REC m n p) =
              ?n':num. (x = ELEM p n') /\ (n' >= n) /\ (n' < n + m)``,


    Induct_on `m` THENL [
      SIMP_TAC list_ss [SEL_REC_def],

      Induct_on `n` THENL [
        ASM_SIMP_TAC list_ss [SEL_REC_def] THEN
        REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
          EXISTS_TAC ``0:num`` THEN
          FULL_SIMP_TAC std_ss [HEAD_ELEM],

          Q_TAC EXISTS_TAC `n' + 1` THEN
          ASM_SIMP_TAC std_ss [REST_RESTN, ELEM_RESTN, SUC_ONE_ADD],

          Cases_on `n'` THENL [
            ASM_REWRITE_TAC[HEAD_ELEM],

            DISJ2_TAC THEN
            Q_TAC EXISTS_TAC `n` THEN
            FULL_SIMP_TAC std_ss [REST_RESTN, ELEM_RESTN, SUC_ONE_ADD] THEN
            PROVE_TAC[ADD_COMM]
          ]
        ],

        ASM_SIMP_TAC std_ss [SEL_REC_def] THEN
        REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
          Q_TAC EXISTS_TAC `n' + 1` THEN
          ASM_SIMP_TAC arith_ss [REST_RESTN, ELEM_RESTN, SUC_ONE_ADD],

          Cases_on `n'` THEN SIMP_ALL_TAC arith_ss [] THEN
          Q_TAC EXISTS_TAC `n''` THEN
          ASM_SIMP_TAC arith_ss [REST_RESTN, ELEM_RESTN, SUC_ONE_ADD]
        ]
      ]
    ]);



val MEM_SEL =
 store_thm
  ("MEM_SEL",
    ``!x m n p. MEM x (SEL p (m, n)) =
              if (n < m) then x = ELEM p m else
              ?n':num. (x = ELEM p n') /\ (n' >= m) /\
                  (n' <= n)``,

    SIMP_TAC std_ss [SEL_def, MEM_SEL_REC] THEN
    REPEAT STRIP_TAC THEN
    Cases_on `n < m` THENL [
      `!n':num. (n' >= m /\ n' < SUC m) = (n' = m)` by DECIDE_TAC THEN
      `m + (n - m + 1) = SUC m` by DECIDE_TAC THEN
      ASM_SIMP_TAC std_ss [],


      `!x:num y:num. (x < SUC y) = (x <= y)` by DECIDE_TAC THEN
      `m + (n - m + 1) = (SUC n)` by DECIDE_TAC THEN
      ASM_SIMP_TAC std_ss []
    ]);



















val PATH_PROP_FREE_def =
 Define
  `PATH_PROP_FREE (p:'prop) v =  !n. !s. (n < LENGTH v) ==> ((ELEM v n = STATE s) ==> ~(p IN s))`;



val INSERT_PROP_def =
 Define
  `(INSERT_PROP (c:'prop) TOP   = TOP) /\
   (INSERT_PROP (c:'prop) BOTTOM   = BOTTOM) /\
   (INSERT_PROP (c:'prop) (STATE (s:'prop set)) = STATE (\x. ((s x) \/ (x = c))))`;


val INSERT_PROP_CASES =
 store_thm
  ("INSERT_PROP_CASES",

   ``!c l. ((INSERT_PROP c l = TOP) = (l = TOP)) /\
           ((INSERT_PROP c l = BOTTOM) = (l = BOTTOM))``,

   Cases_on `l` THEN SIMP_TAC std_ss [INSERT_PROP_def, letter_distinct]);


val F_SERE_FREE_def =
 Define
  `(F_SERE_FREE (F_STRONG_BOOL b)   = T)
   /\
   (F_SERE_FREE (F_WEAK_BOOL b)     = T)
   /\
   (F_SERE_FREE (F_NOT f)           = F_SERE_FREE f)
   /\
   (F_SERE_FREE (F_AND(f1,f2))      = F_SERE_FREE f1 /\ F_SERE_FREE f2)
   /\
   (F_SERE_FREE (F_STRONG_SERE r)   = F)
   /\
   (F_SERE_FREE (F_WEAK_SERE r)     = F)
   /\
   (F_SERE_FREE (F_NEXT f)          = F_SERE_FREE f)
   /\
   (F_SERE_FREE (F_UNTIL(f1,f2))    = F_SERE_FREE f1 /\ F_SERE_FREE f2)
   /\
   (F_SERE_FREE (F_ABORT (f,b))     = F_SERE_FREE f)
   /\
   (F_SERE_FREE (F_SUFFIX_IMP(r,f)) = F)
   /\
   (F_SERE_FREE (F_CLOCK (f,c))         = F_SERE_FREE f)`;


val F_CLOCK_SERE_FREE_def =
 Define
  `F_CLOCK_SERE_FREE f = (F_CLOCK_FREE f /\ F_SERE_FREE f)`;



val bexp_induct =
 save_thm
  ("bexp_induct",
   Q.GEN
    `P`
    (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2)) ==> (A ==> B1)``)
     (SIMP_RULE
       std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P x ==> Q(x,y)) = !x. P x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P y ==> Q(x,y)) = !y. P y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P`,`\(f1,f2). P f1 /\ P f2`]
         (TypeBase.induction_of ``:'a bexp``)))));



val LETTER_RESTRICT_def =
 Define
  `(LETTER_RESTRICT S TOP  = TOP) /\
   (LETTER_RESTRICT S BOTTOM  = BOTTOM) /\
   (LETTER_RESTRICT S (STATE s)  = STATE (s INTER S))`


val LETTER_RESTRICT_Cases =
 store_thm
  ("LETTER_RESTRICT_Cases",
   ``!l s S. ((LETTER_RESTRICT S l = STATE s) = (?s'. (l = STATE s') /\ (s = s' INTER S))) /\
            ((LETTER_RESTRICT S l = TOP) = (l = TOP)) /\
            ((LETTER_RESTRICT S l = BOTTOM) = (l = BOTTOM))``,
   Cases_on `l` THEN
   SIMP_TAC std_ss [LETTER_RESTRICT_def, letter_distinct, letter_11] THEN
   PROVE_TAC[]);


val PATH_MAP_def =
 Define
  `(PATH_MAP f (FINITE l) = FINITE (MAP f l)) /\
   (PATH_MAP f (INFINITE p) = INFINITE (\n. f (p n)))`;


val LENGTH_PATH_MAP =
 store_thm
  ("LENGTH_PATH_MAP",
   ``!f p. LENGTH (PATH_MAP f p) = LENGTH p``,

    Cases_on `p` THEN
    SIMP_TAC std_ss [PATH_MAP_def, LENGTH_def, LENGTH_MAP]);


val ELEM_PATH_MAP =
 store_thm
  ("ELEM_PATH_MAP",
   ``!f p n. (LENGTH p > n) ==>
             ((ELEM (PATH_MAP f p) n) = (f (ELEM p n)))``,

    Cases_on `p` THENL [
      SIMP_TAC list_ss [PATH_MAP_def, LENGTH_def, ELEM_FINITE,
        EL_MAP, GT_xnum_num_def],

      SIMP_TAC std_ss [PATH_MAP_def, LENGTH_def, GT, ELEM_INFINITE]
    ]);


val REST_PATH_MAP =
 store_thm
  ("REST_PATH_MAP",
   ``!f p. LENGTH p > 0 ==> ((REST (PATH_MAP f p)) = (PATH_MAP f (REST p)))``,

    Cases_on `p` THENL [
      REWRITE_TAC [REST_def, PATH_MAP_def, TL_MAP, LENGTH_def, GT] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_TAC `~(l = [])` THEN1 (
        CCONTR_TAC THEN
        FULL_SIMP_TAC list_ss []
      ) THEN
      PROVE_TAC[TL_MAP],

      SIMP_TAC std_ss [REST_def, PATH_MAP_def]
    ]);


val RESTN_PATH_MAP =
 store_thm
  ("RESTN_PATH_MAP",
   ``!f p n. LENGTH p >= n ==> (((RESTN (PATH_MAP f p) n) = (PATH_MAP f (RESTN p n))))``,

    Cases_on `p` THENL [
      SIMP_TAC std_ss [LENGTH_def, GE] THEN
      Induct_on `n` THENL [
        REWRITE_TAC [RESTN_def],

        ASM_SIMP_TAC list_ss [RESTN_def, REST_def, RESTN_REST] THEN
        REPEAT STRIP_TAC THEN
        SUBGOAL_TAC `LENGTH (RESTN (FINITE l) n) > 0` THEN1 (
          SUBGOAL_TAC `(LENGTH (RESTN (FINITE l) n)) = (LENGTH (FINITE l) - n)` THEN1 (
            MATCH_MP_TAC LENGTH_RESTN THEN
            ASM_SIMP_TAC arith_ss [IS_FINITE_def, LENGTH_def, LS]
          ) THEN
          ASM_SIMP_TAC arith_ss [LENGTH_def, SUB_xnum_num_def, GT]
        ) THEN
        ASM_SIMP_TAC std_ss [REST_PATH_MAP]
      ],

      SIMP_TAC std_ss [PATH_MAP_def, LENGTH_def, GE, ELEM_INFINITE,
        RESTN_INFINITE]
    ]);



val SEL_REC_PATH_MAP =
 store_thm
  ("SEL_REC_PATH_MAP",
   ``!m n f p. LENGTH p >= m + n ==>
             ((SEL_REC m n (PATH_MAP f p)) = (MAP f (SEL_REC m n p)))``,

    Induct_on `m` THENL [
      SIMP_TAC list_ss [SEL_REC_def],

      Induct_on `n` THENL [
        SIMP_TAC list_ss [SEL_REC_def, SEL_REC_REST, HEAD_ELEM,
          ELEM_PATH_MAP] THEN
        REPEAT STRIP_TAC THENL [
          SUBGOAL_TAC `LENGTH p > 0` THEN1 (
            Cases_on `p` THENL [
              FULL_SIMP_TAC arith_ss [LENGTH_def, GT, GE],
              REWRITE_TAC[LENGTH_def, GT]
            ]
          ) THEN
          PROVE_TAC[ELEM_PATH_MAP],

          Q_SPEC_NO_ASSUM 1 `1:num` THEN
          `m + 1 = SUC m` by DECIDE_TAC THEN
          FULL_SIMP_TAC std_ss []
        ],

        SIMP_TAC list_ss [SEL_REC_def] THEN
        REPEAT STRIP_TAC THEN
        SUBGOAL_TAC `(LENGTH (REST p) >= SUC m + n) /\ (LENGTH p > 0)` THEN1 (
          Cases_on `p` THENL [
            SUBGOAL_TAC `LENGTH (REST (FINITE l)) = LENGTH (FINITE l) - 1` THEN1 (
              MATCH_MP_TAC LENGTH_REST THEN
              FULL_SIMP_TAC arith_ss [IS_FINITE_def, LENGTH_def, GT, LS, GE]
            ) THEN
            FULL_SIMP_TAC arith_ss [LENGTH_def, GT, SUB_xnum_num_def, GE],


            REWRITE_TAC[LENGTH_def, GT, REST_def, GE]
          ]
        ) THEN
        FULL_SIMP_TAC std_ss [REST_PATH_MAP]
      ]
    ]);


val SEL_PATH_MAP =
 store_thm
  ("SEL_PATH_MAP",
   ``!m n f p. (LENGTH p > n /\ n >= m) ==>
             ((SEL (PATH_MAP f p) (m, n)) = (MAP f (SEL p (m, n))))``,

     REWRITE_TAC[SEL_def] THEN
     REPEAT STRIP_TAC THEN
     MATCH_MP_TAC SEL_REC_PATH_MAP THEN
     Cases_on `p` THENL [
        FULL_SIMP_TAC arith_ss [LENGTH_def, GT, GE],
        REWRITE_TAC[LENGTH_def, GE]
      ]);

val PATH_LETTER_RESTRICT_def =
 Define
  `PATH_LETTER_RESTRICT S p = PATH_MAP (LETTER_RESTRICT S) p`;


val LENGTH_PATH_LETTER_RESTRICT =
 store_thm
  ("LENGTH_PATH_LETTER_RESTRICT",
   ``!S p. LENGTH (PATH_LETTER_RESTRICT S p) = LENGTH p``,
    REWRITE_TAC[PATH_LETTER_RESTRICT_def, LENGTH_PATH_MAP]);


val ELEM_PATH_LETTER_RESTRICT =
 store_thm
  ("ELEM_PATH_LETTER_RESTRICT",
   ``!S p n. (LENGTH p > n) ==>
             ((ELEM (PATH_LETTER_RESTRICT S p) n) = (LETTER_RESTRICT S (ELEM p n)))``,
    REWRITE_TAC[PATH_LETTER_RESTRICT_def, ELEM_PATH_MAP]);


val RESTN_PATH_LETTER_RESTRICT =
 store_thm
  ("RESTN_PATH_LETTER_RESTRICT",
   ``!S p n. LENGTH p >= n ==> (((RESTN (PATH_LETTER_RESTRICT S p) n) = (PATH_LETTER_RESTRICT S (RESTN p n))))``,
    REWRITE_TAC[PATH_LETTER_RESTRICT_def, RESTN_PATH_MAP]);


val COMPLEMENT_PATH_LETTER_RESTRICT =
 store_thm
  ("COMPLEMENT_PATH_LETTER_RESTRICT",
   ``!S p. COMPLEMENT (PATH_LETTER_RESTRICT S p) = PATH_LETTER_RESTRICT S (COMPLEMENT p)``,

    SUBGOAL_TAC `!S x. COMPLEMENT_LETTER (LETTER_RESTRICT S x) =
                       LETTER_RESTRICT S (COMPLEMENT_LETTER x)` THEN1 (
      Cases_on `x` THEN
      REWRITE_TAC[LETTER_RESTRICT_def, COMPLEMENT_LETTER_def]
    ) THEN
    Cases_on `p` THENL [
      ASM_SIMP_TAC std_ss [PATH_LETTER_RESTRICT_def, PATH_MAP_def, COMPLEMENT_def,
        MAP_MAP_o, o_DEF],

      ASM_SIMP_TAC std_ss [PATH_LETTER_RESTRICT_def, PATH_MAP_def, COMPLEMENT_def,
        o_DEF]
    ]);


val LETTER_USED_VARS_def =
 Define
   `(LETTER_USED_VARS TOP = EMPTY) /\
    (LETTER_USED_VARS BOTTOM = EMPTY) /\
    (LETTER_USED_VARS (STATE s) = s)`;

val PATH_USED_VARS_def =
 Define
  `PATH_USED_VARS v =
    \x. (?n. LENGTH v > n /\ x IN LETTER_USED_VARS (ELEM v n))`

val B_USED_VARS_def =
 Define
  `(B_USED_VARS (B_PROP(p:'prop)) = {p}) /\
   (B_USED_VARS B_TRUE = EMPTY) /\
   (B_USED_VARS B_FALSE = EMPTY) /\
   (B_USED_VARS (B_NOT b) = B_USED_VARS b) /\
   (B_USED_VARS (B_AND(b1,b2)) = B_USED_VARS b1 UNION B_USED_VARS b2)`;


val S_USED_VARS_def =
 Define
  `(S_USED_VARS (S_BOOL b) = B_USED_VARS b) /\
   (S_USED_VARS (S_CAT(r1,r2)) = S_USED_VARS r1 UNION S_USED_VARS r2) /\
   (S_USED_VARS (S_FUSION(r1,r2)) = S_USED_VARS r1 UNION S_USED_VARS r2) /\
   (S_USED_VARS (S_OR(r1,r2)) = S_USED_VARS r1 UNION S_USED_VARS r2) /\
   (S_USED_VARS (S_AND(r1,r2)) = S_USED_VARS r1 UNION S_USED_VARS r2) /\
   (S_USED_VARS S_EMPTY = EMPTY) /\
   (S_USED_VARS (S_CLOCK (r, c)) = S_USED_VARS r UNION B_USED_VARS c) /\
   (S_USED_VARS (S_REPEAT r) = S_USED_VARS r)`;


val F_USED_VARS_def =
 Define
   `(F_USED_VARS (F_STRONG_BOOL b) = B_USED_VARS b) /\
    (F_USED_VARS (F_WEAK_BOOL b) = B_USED_VARS b) /\
    (F_USED_VARS (F_NOT f) = F_USED_VARS f) /\
    (F_USED_VARS (F_AND (f,g)) = (F_USED_VARS f UNION F_USED_VARS g)) /\
    (F_USED_VARS (F_NEXT f) = F_USED_VARS f) /\
    (F_USED_VARS (F_UNTIL(f,g)) = (F_USED_VARS f UNION F_USED_VARS g)) /\
    (F_USED_VARS (F_ABORT (f,p)) = (F_USED_VARS f UNION B_USED_VARS p)) /\
    (F_USED_VARS (F_STRONG_SERE r) = S_USED_VARS r) /\
    (F_USED_VARS (F_WEAK_SERE r) = S_USED_VARS r) /\
    (F_USED_VARS (F_SUFFIX_IMP (r,f)) = S_USED_VARS r UNION F_USED_VARS f) /\
    (F_USED_VARS (F_CLOCK (f, p)) = (F_USED_VARS f UNION B_USED_VARS p))`;


val BEXP_PROP_FREE_def = Define `BEXP_PROP_FREE c b = ~(c IN B_USED_VARS b)`;
val S_PROP_FREE_def = Define `S_PROP_FREE c r = ~(c IN S_USED_VARS r)`;
val F_PROP_FREE_def = Define `F_PROP_FREE c f = ~(c IN F_USED_VARS f)`;


val FINITE___B_USED_VARS =
 store_thm
  ("FINITE___B_USED_VARS",

  ``!b. FINITE(B_USED_VARS b)``,

  INDUCT_THEN bexp_induct ASSUME_TAC THEN (
      ASM_SIMP_TAC std_ss [B_USED_VARS_def, FINITE_SING, FINITE_UNION,
        FINITE_EMPTY]
  ));


val FINITE___S_USED_VARS =
 store_thm
  ("FINITE___S_USED_VARS",

  ``!r. FINITE(S_USED_VARS r)``,

  INDUCT_THEN sere_induct ASSUME_TAC THEN (
      ASM_SIMP_TAC std_ss [S_USED_VARS_def, FINITE_UNION,
        FINITE_EMPTY, FINITE___B_USED_VARS]
  ));


val FINITE___F_USED_VARS =
 store_thm
  ("FINITE___F_USED_VARS",

  ``!f. FINITE(F_USED_VARS f)``,

  INDUCT_THEN fl_induct ASSUME_TAC THEN (
      ASM_SIMP_TAC std_ss [F_USED_VARS_def, FINITE_UNION,
        FINITE_EMPTY, FINITE___B_USED_VARS, FINITE___S_USED_VARS]
  ));


val LETTER_USED_VARS_COMPLEMENT =
 store_thm
  ("LETTER_USED_VARS_COMPLEMENT",
    ``!l. LETTER_USED_VARS (COMPLEMENT_LETTER l) =
          LETTER_USED_VARS l``,

    Cases_on `l` THEN
    REWRITE_TAC[COMPLEMENT_LETTER_def, LETTER_USED_VARS_def]);

val PATH_USED_VARS_COMPLEMENT =
 store_thm
  ("PATH_USED_VARS_COMPLEMENT",
   ``!v. PATH_USED_VARS (COMPLEMENT v) = PATH_USED_VARS v``,

    SIMP_TAC std_ss [PATH_USED_VARS_def, FUN_EQ_THM, LENGTH_COMPLEMENT] THEN
    METIS_TAC[LETTER_USED_VARS_COMPLEMENT, GT_LS, ELEM_COMPLEMENT,
      LENGTH_COMPLEMENT]);


val RESTN_PATH_USED_VARS =
 store_thm
  ("RESTN_PATH_USED_VARS",
   ``!n p. LENGTH p > n ==> (PATH_USED_VARS (RESTN p n) SUBSET PATH_USED_VARS p)``,
     SIMP_TAC std_ss [PATH_USED_VARS_def, SUBSET_DEF, IN_ABS] THEN
     REPEAT STRIP_TAC THEN
     Q_TAC EXISTS_TAC `n' + n` THEN
     FULL_SIMP_TAC std_ss [ELEM_RESTN] THEN
     Cases_on `p` THENL [
        `LENGTH (FINITE l) - n > n'` by
          METIS_TAC[IS_FINITE_def, LENGTH_RESTN, GT_LS] THEN
        UNDISCH_HD_TAC THEN
        SIMP_TAC arith_ss [LENGTH_def, GT, SUB_xnum_num_def],

        REWRITE_TAC[LENGTH_def, GT]
     ]);


val PATH_USED_VARS___TOP_OMEGA =
 store_thm
  ("PATH_USED_VARS___TOP_OMEGA",
   ``PATH_USED_VARS TOP_OMEGA = EMPTY``,

    SIMP_TAC std_ss [PATH_USED_VARS_def, EXTENSION, NOT_IN_EMPTY,
      IN_ABS, TOP_OMEGA_def, ELEM_INFINITE, LETTER_USED_VARS_def]);


val SEL_REC_PATH_USED_VARS =
 store_thm
  ("SEL_REC_PATH_USED_VARS",
   ``!m n p. (LENGTH p >= m + n) ==>
             (LIST_BIGUNION (MAP LETTER_USED_VARS (SEL_REC m n p)) SUBSET (PATH_USED_VARS p))``,

    Induct_on `m` THENL [
      SIMP_TAC list_ss [SEL_REC_def, LIST_BIGUNION_def, EMPTY_SUBSET],

      Induct_on `n` THENL [
        SIMP_TAC list_ss [SEL_REC_def, SEL_REC_REST, LIST_BIGUNION_def,
          UNION_SUBSET] THEN
        REPEAT STRIP_TAC THENL [
          SUBGOAL_TAC `LENGTH p > 0` THEN1 (
            Cases_on `p` THENL [
              FULL_SIMP_TAC arith_ss [LENGTH_def, GT, GE],
              REWRITE_TAC[LENGTH_def, GT]
            ]
          ) THEN
          SIMP_TAC std_ss [HEAD_ELEM, PATH_USED_VARS_def, SUBSET_DEF, IN_ABS] THEN
          PROVE_TAC[],

          Q_SPEC_NO_ASSUM 1 `1:num` THEN
          `m + 1 = SUC m` by DECIDE_TAC THEN
          FULL_SIMP_TAC std_ss []
        ],

        REPEAT STRIP_TAC THEN
        SUBGOAL_TAC `(LENGTH (REST p) >= SUC m + n) /\ (LENGTH p > 1)` THEN1 (
          Cases_on `p` THENL [
            SUBGOAL_TAC `LENGTH (REST (FINITE l)) = LENGTH (FINITE l) - 1` THEN1 (
              MATCH_MP_TAC LENGTH_REST THEN
              FULL_SIMP_TAC arith_ss [IS_FINITE_def, LENGTH_def, GT, LS, GE]
            ) THEN
            FULL_SIMP_TAC arith_ss [LENGTH_def, GT, SUB_xnum_num_def, GE],

            REWRITE_TAC[LENGTH_def, GT, REST_def, GE]
          ]
        ) THEN

        RES_TAC THEN
        UNDISCH_HD_TAC THEN
        REWRITE_TAC[SEL_REC_REST, REST_RESTN] THEN
        `PATH_USED_VARS (RESTN p 1) SUBSET PATH_USED_VARS p`
          by PROVE_TAC[RESTN_PATH_USED_VARS] THEN
        PROVE_TAC [SUBSET_TRANS]
      ]
    ]);


val SEL_PATH_USED_VARS =
 store_thm
  ("SEL_PATH_USED_VARS",
   ``!m n p. (LENGTH p > n /\ n >= m) ==>
             (LIST_BIGUNION (MAP LETTER_USED_VARS (SEL p (m, n))) SUBSET (PATH_USED_VARS p))``,

     REWRITE_TAC[SEL_def] THEN
     REPEAT STRIP_TAC THEN
     MATCH_MP_TAC SEL_REC_PATH_USED_VARS THEN
     Cases_on `p` THENL [
        FULL_SIMP_TAC arith_ss [LENGTH_def, GT, GE],
        REWRITE_TAC[LENGTH_def, GE]
     ]);



val CONS_PATH_USED_VARS =
 store_thm
  ("CONS_PATH_USED_VARS",
   ``!h p. PATH_USED_VARS (CONS (h, p)) =
           (LETTER_USED_VARS h) UNION PATH_USED_VARS p``,

    Cases_on `p` THENL [
      SIMP_TAC list_ss [PATH_USED_VARS_def, CONS_def, EXTENSION, IN_ABS,
        IN_UNION, LENGTH_def, GT] THEN
      REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
        Cases_on `n` THENL [
          DISJ1_TAC THEN
          FULL_SIMP_TAC list_ss [ELEM_def, RESTN_def, HEAD_def],

          DISJ2_TAC THEN
          Q_TAC EXISTS_TAC `n'` THEN
          FULL_SIMP_TAC list_ss [ELEM_def, RESTN_def, REST_def]
        ],

        EXISTS_TAC ``0:num`` THEN
        FULL_SIMP_TAC list_ss [ELEM_def, RESTN_def, HEAD_def],

        EXISTS_TAC ``SUC n`` THEN
        FULL_SIMP_TAC list_ss [ELEM_def, RESTN_def, REST_def]
      ],


      SIMP_TAC std_ss [CONS_def, PATH_USED_VARS_def, LENGTH_def, GT,
        EXTENSION, IN_UNION, IN_ABS, ELEM_INFINITE] THEN
      REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
        Cases_on `n` THENL [
          FULL_SIMP_TAC std_ss [],

          FULL_SIMP_TAC arith_ss [] THEN
          PROVE_TAC[]
        ],

        PROVE_TAC[],

        EXISTS_TAC ``SUC n`` THEN
        FULL_SIMP_TAC arith_ss []
      ]
    ]);


val CAT_PATH_USED_VARS =
 store_thm
  ("CAT_PATH_USED_VARS",
   ``!l p. PATH_USED_VARS (CAT (l, p)) =
           (LIST_BIGUNION (MAP LETTER_USED_VARS l)) UNION PATH_USED_VARS p``,

    Induct_on `l` THENL [
      SIMP_TAC std_ss [CAT_def, MAP, LIST_BIGUNION_def, UNION_EMPTY],

      ASM_SIMP_TAC list_ss [CAT_def, CONS_PATH_USED_VARS, EXTENSION, IN_UNION,
        LIST_BIGUNION_def] THEN
      PROVE_TAC[]
    ])


val B_USED_VARS_INTER_SUBSET_THM =
 store_thm
  ("B_USED_VARS_INTER_SUBSET_THM",
   ``!l b S. (B_USED_VARS b) SUBSET S ==> (B_SEM l b = B_SEM (LETTER_RESTRICT S l) b)``,

   Cases_on `l` THEN REWRITE_TAC[B_SEM_def, LETTER_RESTRICT_def] THEN
   INDUCT_THEN bexp_induct ASSUME_TAC THENL [
      SIMP_TAC std_ss [B_USED_VARS_def, B_SEM_def, IN_INTER] THEN
      PROVE_TAC[SUBSET_DEF, IN_SING],

      REWRITE_TAC[B_SEM_def],
      REWRITE_TAC[B_SEM_def],

      REWRITE_TAC[B_SEM_def, B_USED_VARS_def] THEN
      PROVE_TAC[],

      REWRITE_TAC[B_SEM_def, B_USED_VARS_def, UNION_SUBSET] THEN
      PROVE_TAC[]
   ]);






val S_USED_VARS_INTER_SUBSET_THM =
 store_thm
  ("S_USED_VARS_INTER_SUBSET_THM",
   ``!r l S.  (S_CLOCK_FREE r) ==>
      (S_USED_VARS r) SUBSET S ==> (US_SEM l r = US_SEM (MAP (LETTER_RESTRICT S) l) r)``,

   INDUCT_THEN sere_induct ASSUME_TAC THENL [ (* 8 subgoals *)
      SIMP_TAC list_ss [S_USED_VARS_def, US_SEM_def, ELEM_EL,
        HD_MAP] THEN
      REPEAT STRIP_TAC THEN
      BOOL_EQ_STRIP_TAC THEN
      SUBGOAL_TAC `~(l = [])` THEN1 (
        CCONTR_TAC THEN
        FULL_SIMP_TAC list_ss []
      ) THEN
      ASM_SIMP_TAC std_ss [HD_MAP] THEN
      PROVE_TAC[B_USED_VARS_INTER_SUBSET_THM],

      SIMP_TAC list_ss [US_SEM_def, S_USED_VARS_def, UNION_SUBSET,
        MAP_EQ_APPEND, GSYM LEFT_EXISTS_AND_THM,
        S_CLOCK_FREE_def] THEN
      METIS_TAC[],

      SIMP_TAC list_ss [US_SEM_def, S_USED_VARS_def, UNION_SUBSET,
        S_CLOCK_FREE_def, MAP_EQ_APPEND, GSYM LEFT_EXISTS_AND_THM,
        GSYM RIGHT_EXISTS_AND_THM] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_TAC `!x l. ((LETTER_RESTRICT S x)::MAP (LETTER_RESTRICT S) l =
                         MAP (LETTER_RESTRICT S) (x::l)) /\

                         ((MAP (LETTER_RESTRICT S) l) <> [LETTER_RESTRICT S x] =
                         MAP (LETTER_RESTRICT S) (l<>[x]))` THEN1 (
        SIMP_TAC list_ss []
      ) THEN
      ASM_SIMP_TAC std_ss [] THEN
      METIS_TAC[],


      SIMP_TAC list_ss [US_SEM_def, S_USED_VARS_def, S_CLOCK_FREE_def, UNION_SUBSET] THEN
      METIS_TAC[],


      SIMP_TAC list_ss [US_SEM_def, S_USED_VARS_def, S_CLOCK_FREE_def, UNION_SUBSET] THEN
      METIS_TAC[],


      SIMP_TAC list_ss [US_SEM_def],

      SIMP_TAC list_ss [US_SEM_def, S_USED_VARS_def, S_CLOCK_FREE_def,
        MAP_EQ_CONCAT, GSYM LEFT_EXISTS_AND_THM, listTheory.EVERY_MAP] THEN
      REPEAT STRIP_TAC THEN
      EXISTS_EQ_STRIP_TAC THEN
      BOOL_EQ_STRIP_TAC THEN
      `!l. (US_SEM l r = US_SEM (MAP (LETTER_RESTRICT S) l) r)` by
        METIS_TAC[] THEN
      POP_NO_ASSUM 0 (fn thm => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [thm]))) THEN
      PROVE_TAC[],


      SIMP_TAC list_ss [S_CLOCK_FREE_def]
   ]);



val F_USED_VARS_INTER_SUBSET_THM =
 store_thm
  ("F_USED_VARS_INTER_SUBSET_THM",
   ``!f p S.  (F_CLOCK_FREE f) ==>
              (F_USED_VARS f) SUBSET S ==>
              (UF_SEM p f = UF_SEM (PATH_LETTER_RESTRICT S p) f)``,

  INDUCT_THEN fl_induct ASSUME_TAC THENL [ (* 11 subgoals *)
    SIMP_TAC std_ss [UF_SEM_def, LENGTH_PATH_LETTER_RESTRICT,
      F_USED_VARS_def] THEN
    REPEAT STRIP_TAC THEN
    BOOL_EQ_STRIP_TAC THEN
    ASM_SIMP_TAC std_ss [ELEM_PATH_LETTER_RESTRICT] THEN
    PROVE_TAC[B_USED_VARS_INTER_SUBSET_THM],


    SIMP_TAC std_ss [UF_SEM_def, LENGTH_PATH_LETTER_RESTRICT,
      F_USED_VARS_def] THEN
    REPEAT STRIP_TAC THEN
    BOOL_EQ_STRIP_TAC THEN
    SUBGOAL_TAC `LENGTH p > 0` THEN1 (
      Cases_on `LENGTH p` THENL [
        REWRITE_TAC[GT],
        FULL_SIMP_TAC arith_ss [xnum_11, GT]
      ]
    ) THEN
    ASM_SIMP_TAC std_ss [ELEM_PATH_LETTER_RESTRICT] THEN
    PROVE_TAC[B_USED_VARS_INTER_SUBSET_THM],


    SIMP_TAC std_ss [UF_SEM_def, F_USED_VARS_def, COMPLEMENT_PATH_LETTER_RESTRICT,
      F_CLOCK_FREE_def] THEN
    PROVE_TAC[],


    SIMP_TAC std_ss [UF_SEM_def, F_USED_VARS_def,  F_CLOCK_FREE_def,
      UNION_SUBSET] THEN
    PROVE_TAC[],



    SIMP_TAC (std_ss++resq_SS) [UF_SEM_def, F_USED_VARS_def,  F_CLOCK_FREE_def,
      LENGTH_PATH_LETTER_RESTRICT] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_EQ_STRIP_TAC THEN
    BOOL_EQ_STRIP_TAC THEN
    SUBGOAL_TAC `LENGTH p > j /\ j >= 0`  THEN1 (
      SIMP_TAC std_ss [] THEN
      Cases_on `p` THENL [
        FULL_SIMP_TAC arith_ss [LENGTH_def, IN_LESSX, GT],
        REWRITE_TAC[LENGTH_def, GT]
      ]
    ) THEN
    ASM_SIMP_TAC std_ss [PATH_LETTER_RESTRICT_def, SEL_PATH_MAP] THEN
    METIS_TAC[PATH_LETTER_RESTRICT_def, S_USED_VARS_INTER_SUBSET_THM],


    SIMP_TAC (std_ss++resq_SS) [UF_SEM_def, F_USED_VARS_def, F_CLOCK_FREE_def,
      LENGTH_PATH_LETTER_RESTRICT, LENGTH_CAT, TOP_OMEGA_def, IN_LESSX] THEN
    REPEAT STRIP_TAC THEN
    FORALL_EQ_STRIP_TAC THEN
    Cases_on `j IN LESS (LENGTH p)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_EQ_STRIP_TAC THEN
    REMAINS_TAC `(SEL (CAT (SEL (PATH_LETTER_RESTRICT S p) (0,j),INFINITE (\n. TOP)))
         (0,k)) =
         MAP (LETTER_RESTRICT S) (SEL (CAT (SEL p (0,j),INFINITE (\n. TOP))) (0,k))` THEN1 (
      PROVE_TAC[S_USED_VARS_INTER_SUBSET_THM]
    ) THEN
    ONCE_REWRITE_TAC [LIST_EQ_REWRITE] THEN
    SIMP_TAC arith_ss [LENGTH_SEL, LENGTH_MAP, EL_MAP] THEN
    REPEAT STRIP_TAC THEN
    rename1 `n < k + 1` THEN
    `(0:num) + n <= k` by DECIDE_TAC THEN
    ASM_SIMP_TAC std_ss [EL_SEL_THM] THEN
    Cases_on `n > j` THENL [
      ASM_SIMP_TAC std_ss [ELEM_CAT_SEL___GREATER, ELEM_INFINITE, LETTER_RESTRICT_def],

      `n <= j` by DECIDE_TAC THEN
      ASM_SIMP_TAC std_ss [ELEM_CAT_SEL___LESS_EQ] THEN
      MATCH_MP_TAC ELEM_PATH_LETTER_RESTRICT THEN
      Cases_on `p` THENL [
        FULL_SIMP_TAC arith_ss [LENGTH_def, GT, IN_LESSX],
        REWRITE_TAC[LENGTH_def, GT]
      ]
    ],



    SIMP_TAC std_ss [UF_SEM_def, F_USED_VARS_def,  F_CLOCK_FREE_def,
      LENGTH_PATH_LETTER_RESTRICT] THEN
    REPEAT STRIP_TAC THEN
    BOOL_EQ_STRIP_TAC THEN
    SUBGOAL_TAC `LENGTH p >= 1`  THEN1 (
      Cases_on `p` THEN
      FULL_SIMP_TAC arith_ss [LENGTH_def, GT, GE]
    ) THEN
    ASM_SIMP_TAC std_ss [RESTN_PATH_LETTER_RESTRICT],



    SIMP_TAC (std_ss++resq_SS) [UF_SEM_def, F_USED_VARS_def,  F_CLOCK_FREE_def,
      UNION_SUBSET, LENGTH_PATH_LETTER_RESTRICT, IN_LESSX_REWRITE, IN_LESS] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_EQ_STRIP_TAC THEN
    BOOL_EQ_STRIP_TAC THEN
    BINOP_TAC THENL [
      REMAINS_TAC `LENGTH p >= k` THEN1 (
        METIS_TAC[RESTN_PATH_LETTER_RESTRICT]
      ) THEN
      Cases_on `p` THEN
      FULL_SIMP_TAC arith_ss [LENGTH_def, GT, GE, LS],

      FORALL_EQ_STRIP_TAC THEN
      Cases_on `j < k` THEN ASM_REWRITE_TAC[] THEN
      REMAINS_TAC `LENGTH p >= j` THEN1 (
        METIS_TAC[RESTN_PATH_LETTER_RESTRICT]
      ) THEN
      Cases_on `p` THEN
      FULL_SIMP_TAC arith_ss [LENGTH_def, GT, GE, LS]
    ],



    SIMP_TAC (std_ss++resq_SS) [UF_SEM_def, F_USED_VARS_def,  F_CLOCK_FREE_def,
      UNION_SUBSET, LENGTH_PATH_LETTER_RESTRICT, IN_LESSX_REWRITE, IN_LESS] THEN
    REPEAT STRIP_TAC THEN
    BINOP_TAC THEN1 METIS_TAC[] THEN
    EXISTS_EQ_STRIP_TAC THEN
    REPEAT BOOL_EQ_STRIP_TAC THEN
    BINOP_TAC THENL [
      ASM_SIMP_TAC std_ss [ELEM_PATH_LETTER_RESTRICT, GT_LS] THEN
      PROVE_TAC[B_USED_VARS_INTER_SUBSET_THM],

      Cases_on `j = 0` THEN ASM_REWRITE_TAC[TOP_OMEGA_def] THEN
      REMAINS_TAC `(CAT (SEL (PATH_LETTER_RESTRICT S p) (0,j-1),INFINITE (\n. TOP))) =
          PATH_LETTER_RESTRICT S (CAT (SEL p (0,j-1),INFINITE (\n. TOP)))` THEN1 (
        METIS_TAC[]
      ) THEN
      ONCE_REWRITE_TAC [PATH_EQ_ELEM_THM] THEN
      SIMP_TAC arith_ss [LENGTH_CAT, LENGTH_PATH_LETTER_RESTRICT, LS] THEN
      GEN_TAC THEN
      `LENGTH (CAT (SEL p (0,j - 1),INFINITE (\n. TOP))) > j'` by
        SIMP_TAC std_ss [LENGTH_CAT, GT] THEN
      ASM_SIMP_TAC std_ss [ELEM_PATH_LETTER_RESTRICT] THEN
      Cases_on `j' > j-1` THENL [
        ASM_SIMP_TAC std_ss [ELEM_CAT_SEL___GREATER, ELEM_INFINITE, LETTER_RESTRICT_def],

        `j' <= j - 1` by DECIDE_TAC THEN
        ASM_SIMP_TAC std_ss [ELEM_CAT_SEL___LESS_EQ] THEN
        SUBGOAL_TAC `LENGTH p > j'` THEN1 (
          Cases_on `p` THEN
          FULL_SIMP_TAC arith_ss [LENGTH_def, GT, LS]
        ) THEN
        ASM_SIMP_TAC std_ss [ELEM_PATH_LETTER_RESTRICT]
      ]
    ],


    REWRITE_TAC[F_CLOCK_FREE_def],


    SIMP_TAC (std_ss++resq_SS) [UF_SEM_def, F_USED_VARS_def,  F_CLOCK_FREE_def,
      UNION_SUBSET, LENGTH_PATH_LETTER_RESTRICT, IN_LESSX_REWRITE, IN_LESS,
      COMPLEMENT_PATH_LETTER_RESTRICT] THEN
    REPEAT STRIP_TAC THEN
    FORALL_EQ_STRIP_TAC THEN
    Cases_on `j < LENGTH p` THEN ASM_REWRITE_TAC [] THEN
    BINOP_TAC THENL [
      `LENGTH (COMPLEMENT p) > j` by PROVE_TAC[GT_LS, LENGTH_COMPLEMENT] THEN
      `j >= 0` by DECIDE_TAC THEN
      ASM_SIMP_TAC std_ss [SEL_PATH_MAP, PATH_LETTER_RESTRICT_def] THEN
      PROVE_TAC[S_USED_VARS_INTER_SUBSET_THM],


      SUBGOAL_TAC `LENGTH p >= j` THEN1 (
        Cases_on `p` THEN
        FULL_SIMP_TAC arith_ss [LENGTH_def, GT, GE, LS]
      ) THEN
      PROVE_TAC[RESTN_PATH_LETTER_RESTRICT]
    ]
  ]);


val LETTER_VAR_RENAMING_def =
 Define
   `(LETTER_VAR_RENAMING (f:'a->'b) TOP = TOP) /\
    (LETTER_VAR_RENAMING f BOTTOM = BOTTOM) /\
    (LETTER_VAR_RENAMING f (STATE s) = STATE (IMAGE f s))`;

val PATH_VAR_RENAMING_def =
 Define
  `PATH_VAR_RENAMING f p = PATH_MAP (LETTER_VAR_RENAMING f) p`;


val LENGTH_PATH_VAR_RENAMING =
 store_thm
  ("LENGTH_PATH_VAR_RENAMING",
   ``!f p. LENGTH (PATH_VAR_RENAMING f p) = LENGTH p``,
    REWRITE_TAC[PATH_VAR_RENAMING_def, LENGTH_PATH_MAP]);

val SEL_PATH_VAR_RENAMING =
 store_thm
  ("SEL_PATH_VAR_RENAMING",
   ``!m n f p. (LENGTH p > n /\ n >= m) ==>
             ((SEL (PATH_VAR_RENAMING f p) (m, n)) = (MAP (LETTER_VAR_RENAMING f) (SEL p (m, n))))``,

     REWRITE_TAC[PATH_VAR_RENAMING_def, SEL_PATH_MAP]);


val ELEM_PATH_VAR_RENAMING =
 store_thm
  ("ELEM_PATH_VAR_RENAMING",
   ``!f p n. (LENGTH p > n) ==>
             ((ELEM (PATH_VAR_RENAMING f p) n) = (LETTER_VAR_RENAMING f (ELEM p n)))``,
    REWRITE_TAC[PATH_VAR_RENAMING_def, ELEM_PATH_MAP]);


val RESTN_PATH_VAR_RENAMING =
 store_thm
  ("RESTN_PATH_VAR_RENAMING",
   ``!f p n. LENGTH p >= n ==> (((RESTN (PATH_VAR_RENAMING f p) n) = (PATH_VAR_RENAMING f (RESTN p n))))``,
    REWRITE_TAC[PATH_VAR_RENAMING_def, RESTN_PATH_MAP]);


val COMPLEMENT_PATH_VAR_RENAMING =
 store_thm
  ("COMPLEMENT_PATH_VAR_RENAMING",
   ``!f p. COMPLEMENT (PATH_VAR_RENAMING f p) = PATH_VAR_RENAMING f (COMPLEMENT p)``,

    SUBGOAL_TAC `!f x. COMPLEMENT_LETTER (LETTER_VAR_RENAMING f x) =
                       LETTER_VAR_RENAMING f (COMPLEMENT_LETTER x)` THEN1 (
      Cases_on `x` THEN
      REWRITE_TAC[LETTER_VAR_RENAMING_def, COMPLEMENT_LETTER_def]
    ) THEN
    Cases_on `p` THENL [
      ASM_SIMP_TAC std_ss [PATH_VAR_RENAMING_def, PATH_MAP_def, COMPLEMENT_def,
        MAP_MAP_o, o_DEF],

      ASM_SIMP_TAC std_ss [PATH_VAR_RENAMING_def, PATH_MAP_def, COMPLEMENT_def,
        o_DEF]
    ]);


val PATH_VAR_RENAMING___CONS =
 store_thm
  ("PATH_VAR_RENAMING___CONS",

    ``!l v f.
    PATH_VAR_RENAMING f (CONS (l, v)) =
    CONS (LETTER_VAR_RENAMING f l, PATH_VAR_RENAMING f v)``,

    Cases_on `v` THENL [
      SIMP_TAC std_ss [CONS_def, PATH_VAR_RENAMING_def, PATH_MAP_def, MAP],
      SIMP_TAC std_ss [CONS_def, PATH_VAR_RENAMING_def, PATH_MAP_def, COND_RAND]
    ]);


val PATH_VAR_RENAMING___CAT =
 store_thm
  ("PATH_VAR_RENAMING___CAT",
  ``!f l p.
    PATH_VAR_RENAMING f (CAT(l, p)) =
    CAT (MAP (LETTER_VAR_RENAMING f) l, PATH_VAR_RENAMING f p)``,

  Induct_on `l` THENL [
    SIMP_TAC std_ss [CAT_def, MAP],
    ASM_SIMP_TAC std_ss [CAT_def, PATH_VAR_RENAMING___CONS, MAP]
  ]);


val PATH_VAR_RENAMING___TOP_OMEGA =
 store_thm
  ("PATH_VAR_RENAMING___TOP_OMEGA",

    ``!f. PATH_VAR_RENAMING f TOP_OMEGA = TOP_OMEGA``,
    REWRITE_TAC[PATH_VAR_RENAMING_def, TOP_OMEGA_def, PATH_MAP_def, LETTER_VAR_RENAMING_def]);


val PATH_VAR_RENAMING___BOTTOM_OMEGA =
 store_thm
  ("PATH_VAR_RENAMING___BOTTOM_OMEGA",

    ``!f. PATH_VAR_RENAMING f BOTTOM_OMEGA = BOTTOM_OMEGA``,
    REWRITE_TAC[PATH_VAR_RENAMING_def, BOTTOM_OMEGA_def, PATH_MAP_def, LETTER_VAR_RENAMING_def]);


val B_VAR_RENAMING_def =
 Define
   `(B_VAR_RENAMING (f:'a->'b) (B_TRUE) = B_TRUE) /\
    (B_VAR_RENAMING f (B_FALSE) = B_FALSE) /\
    (B_VAR_RENAMING f (B_PROP p) = (B_PROP (f p))) /\
    (B_VAR_RENAMING f (B_NOT b) = B_NOT (B_VAR_RENAMING f b)) /\
    (B_VAR_RENAMING f (B_AND(b1,b2)) = (B_AND(B_VAR_RENAMING f b1, B_VAR_RENAMING f b2)))`;


val S_VAR_RENAMING_def =
 Define
  `(S_VAR_RENAMING f (S_BOOL b) = S_BOOL (B_VAR_RENAMING f b)) /\
   (S_VAR_RENAMING f (S_CAT(r1,r2)) = S_CAT(S_VAR_RENAMING f r1, S_VAR_RENAMING f r2)) /\
   (S_VAR_RENAMING f (S_FUSION(r1,r2)) = S_FUSION(S_VAR_RENAMING f r1, S_VAR_RENAMING f r2)) /\
   (S_VAR_RENAMING f (S_OR(r1,r2)) = S_OR(S_VAR_RENAMING f r1, S_VAR_RENAMING f r2)) /\
   (S_VAR_RENAMING f (S_AND(r1,r2)) = S_AND(S_VAR_RENAMING f r1, S_VAR_RENAMING f r2)) /\
   (S_VAR_RENAMING f S_EMPTY = S_EMPTY) /\
   (S_VAR_RENAMING f (S_CLOCK (r, c)) = S_CLOCK (S_VAR_RENAMING f r, B_VAR_RENAMING f c)) /\
   (S_VAR_RENAMING f (S_REPEAT r) = S_REPEAT (S_VAR_RENAMING f r))`;


val F_VAR_RENAMING_def =
 Define
   `(F_VAR_RENAMING f' (F_STRONG_BOOL b) = F_STRONG_BOOL (B_VAR_RENAMING f' b)) /\
    (F_VAR_RENAMING f' (F_WEAK_BOOL b) = F_WEAK_BOOL (B_VAR_RENAMING f' b)) /\
    (F_VAR_RENAMING f' (F_NOT f) = F_NOT (F_VAR_RENAMING f' f)) /\
    (F_VAR_RENAMING f' (F_AND (f,g)) = F_AND(F_VAR_RENAMING f' f, F_VAR_RENAMING f' g)) /\
    (F_VAR_RENAMING f' (F_NEXT f) = F_NEXT(F_VAR_RENAMING f' f)) /\
    (F_VAR_RENAMING f' (F_UNTIL(f,g)) = F_UNTIL(F_VAR_RENAMING f' f, F_VAR_RENAMING f' g)) /\
    (F_VAR_RENAMING f' (F_ABORT (f,p)) = F_ABORT(F_VAR_RENAMING f' f, B_VAR_RENAMING f' p)) /\
    (F_VAR_RENAMING f' (F_STRONG_SERE r) = F_STRONG_SERE (S_VAR_RENAMING f' r)) /\
    (F_VAR_RENAMING f' (F_WEAK_SERE r) = F_WEAK_SERE (S_VAR_RENAMING f' r)) /\
    (F_VAR_RENAMING f' (F_SUFFIX_IMP (r,f)) = F_SUFFIX_IMP(S_VAR_RENAMING f' r, F_VAR_RENAMING f' f)) /\
    (F_VAR_RENAMING f' (F_CLOCK (f, p)) = F_CLOCK(F_VAR_RENAMING f' f, B_VAR_RENAMING f' p))`;


val B_SEM___VAR_RENAMING =
 store_thm
  ("B_SEM___VAR_RENAMING",
   ``!p l f. (INJ f (LETTER_USED_VARS l UNION B_USED_VARS p) UNIV) ==> ((B_SEM l p) = (B_SEM (LETTER_VAR_RENAMING f l) (B_VAR_RENAMING f p)))``,

   Cases_on `l` THEN (
      REWRITE_TAC[B_SEM_def, LETTER_VAR_RENAMING_def]
   ) THEN
   INDUCT_THEN bexp_induct ASSUME_TAC THENL [
      SIMP_TAC std_ss [B_SEM_def, B_VAR_RENAMING_def, IN_IMAGE,
        INJ_DEF, IN_UNIV, LETTER_USED_VARS_def, IN_UNION,
        B_USED_VARS_def, IN_SING] THEN
      PROVE_TAC[],

      REWRITE_TAC[B_SEM_def, B_VAR_RENAMING_def],
      REWRITE_TAC[B_SEM_def, B_VAR_RENAMING_def],
      ASM_SIMP_TAC std_ss [B_SEM_def, B_VAR_RENAMING_def, B_USED_VARS_def],

      ASM_SIMP_TAC std_ss [B_SEM_def, B_VAR_RENAMING_def, B_USED_VARS_def] THEN
      REPEAT STRIP_TAC THEN
      REMAINS_TAC `INJ f' (LETTER_USED_VARS (STATE f) UNION B_USED_VARS p) UNIV /\
                   INJ f' (LETTER_USED_VARS (STATE f) UNION B_USED_VARS p') UNIV` THEN1 (
        PROVE_TAC[]
      ) THEN
      UNDISCH_HD_TAC THEN
      SIMP_TAC std_ss [INJ_DEF, IN_UNION, IN_UNIV] THEN
      PROVE_TAC[]
   ]);



val US_SEM___VAR_RENAMING =
 store_thm
  ("US_SEM___VAR_RENAMING",
    ``!r l f. ((S_CLOCK_FREE r) /\
    (INJ f ((LIST_BIGUNION (MAP LETTER_USED_VARS l)) UNION S_USED_VARS r) UNIV)) ==>
    (US_SEM l r = US_SEM ((MAP (LETTER_VAR_RENAMING f)) l) (S_VAR_RENAMING f r))``,

INDUCT_THEN sere_induct ASSUME_TAC THENL [ (* 8 subgoals *)
  Cases_on `l` THEN
  SIMP_TAC list_ss [US_SEM_def, S_VAR_RENAMING_def,
    S_USED_VARS_def,
    LENGTH_NIL, FinitePSLPathTheory.ELEM_def, FinitePSLPathTheory.RESTN_def,
    FinitePSLPathTheory.HEAD_def, LIST_BIGUNION_def] THEN
  REPEAT STRIP_TAC THEN
  BOOL_EQ_STRIP_TAC THEN
  MATCH_MP_TAC B_SEM___VAR_RENAMING THEN
  UNDISCH_NO_TAC 1 THEN
  MATCH_MP_TAC set_lemmataTheory.INJ_SUBSET_DOMAIN THEN
  SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
  PROVE_TAC[],


  SIMP_TAC std_ss [US_SEM_def, S_USED_VARS_def, S_VAR_RENAMING_def,
    MAP_EQ_APPEND, GSYM LEFT_EXISTS_AND_THM, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THEN
  REPEAT EXISTS_EQ_STRIP_TAC THEN
  BOOL_EQ_STRIP_TAC THEN
  REMAINS_TAC `INJ f (LIST_BIGUNION (MAP LETTER_USED_VARS v1) UNION S_USED_VARS r) UNIV /\
               INJ f (LIST_BIGUNION (MAP LETTER_USED_VARS v2) UNION S_USED_VARS r') UNIV` THEN1 (
    PROVE_TAC[]
  ) THEN
  STRIP_TAC THEN
  UNDISCH_NO_TAC 1 THEN
  MATCH_MP_TAC set_lemmataTheory.INJ_SUBSET_DOMAIN THEN
  ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, MAP_APPEND,
    LIST_BIGUNION_APPEND] THEN
  PROVE_TAC[],


  SIMP_TAC std_ss [US_SEM_def, S_USED_VARS_def, S_VAR_RENAMING_def,
    MAP_EQ_APPEND, GSYM LEFT_EXISTS_AND_THM,
    GSYM RIGHT_EXISTS_AND_THM, S_CLOCK_FREE_def, MAP_EQ_SING] THEN

  (*Reorder Variables for later EXISTS_EQ_STRIP_TAC*)
  REPEAT STRIP_TAC THEN
  `(?v1 v2 l'. (l = v1 <> [l'] <> v2) /\ US_SEM (v1 <> [l']) r /\ US_SEM ([l'] <> v2) r') =
   (?v2 v1 l'. (l = v1 <> [l'] <> v2) /\ US_SEM (v1 <> [l']) r /\ US_SEM ([l'] <> v2) r')` by PROVE_TAC[] THEN
  ONCE_ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

  REPEAT EXISTS_EQ_STRIP_TAC THEN
  BOOL_EQ_STRIP_TAC THEN
  SUBGOAL_TAC `(MAP (LETTER_VAR_RENAMING f) v1 <> [LETTER_VAR_RENAMING f l'] =
                MAP (LETTER_VAR_RENAMING f) (v1 <> [l'])) /\
               ([LETTER_VAR_RENAMING f l'] <> MAP (LETTER_VAR_RENAMING f) v2  =
                MAP (LETTER_VAR_RENAMING f) ([l'] <> v2))` THEN1 (
    SIMP_TAC std_ss [MAP_APPEND, MAP]
  ) THEN
  ASM_REWRITE_TAC[] THEN NTAC 2 WEAKEN_HD_TAC THEN
  REMAINS_TAC `INJ f (LIST_BIGUNION (MAP LETTER_USED_VARS (v1<>[l'])) UNION S_USED_VARS r) UNIV /\
               INJ f (LIST_BIGUNION (MAP LETTER_USED_VARS ([l']<>v2)) UNION S_USED_VARS r') UNIV` THEN1 (
    PROVE_TAC[]
  ) THEN
  STRIP_TAC THEN
  UNDISCH_NO_TAC 1 THEN
  MATCH_MP_TAC set_lemmataTheory.INJ_SUBSET_DOMAIN THEN
  ASM_SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, MAP_APPEND,
    LIST_BIGUNION_APPEND, MAP] THEN
  PROVE_TAC[],



  SIMP_TAC std_ss [US_SEM_def, S_USED_VARS_def, S_VAR_RENAMING_def, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THEN
  REMAINS_TAC `INJ f (LIST_BIGUNION (MAP LETTER_USED_VARS l) UNION S_USED_VARS r) UNIV /\
               INJ f (LIST_BIGUNION (MAP LETTER_USED_VARS l) UNION S_USED_VARS r') UNIV` THEN1 (
    PROVE_TAC[]
  ) THEN
  STRIP_TAC THEN
  UNDISCH_HD_TAC THEN
  MATCH_MP_TAC set_lemmataTheory.INJ_SUBSET_DOMAIN THEN
  SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
  PROVE_TAC[],



  SIMP_TAC std_ss [US_SEM_def, S_USED_VARS_def, S_VAR_RENAMING_def, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THEN
  REMAINS_TAC `INJ f (LIST_BIGUNION (MAP LETTER_USED_VARS l) UNION S_USED_VARS r) UNIV /\
               INJ f (LIST_BIGUNION (MAP LETTER_USED_VARS l) UNION S_USED_VARS r') UNIV` THEN1 (
    PROVE_TAC[]
  ) THEN
  STRIP_TAC THEN
  UNDISCH_HD_TAC THEN
  MATCH_MP_TAC set_lemmataTheory.INJ_SUBSET_DOMAIN THEN
  SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
  PROVE_TAC[],


  SIMP_TAC list_ss [US_SEM_def, S_VAR_RENAMING_def],


  SIMP_TAC list_ss [US_SEM_def, S_VAR_RENAMING_def, S_USED_VARS_def,
    MAP_EQ_CONCAT, GSYM LEFT_EXISTS_AND_THM, listTheory.EVERY_MAP, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THEN
  EXISTS_EQ_STRIP_TAC THEN
  BOOL_EQ_STRIP_TAC THEN
  FULL_SIMP_TAC std_ss [] THEN
  WEAKEN_HD_TAC THEN
  Induct_on `vlist` THENL [
    SIMP_TAC list_ss [],

    SIMP_TAC list_ss [MAP_APPEND, LIST_BIGUNION_APPEND, CONCAT_def] THEN
    REPEAT STRIP_TAC THEN
    REMAINS_TAC `INJ f (LIST_BIGUNION (MAP LETTER_USED_VARS (CONCAT vlist)) UNION S_USED_VARS r) UNIV /\
                 INJ f (LIST_BIGUNION (MAP LETTER_USED_VARS h) UNION S_USED_VARS r) UNIV` THEN1 (
      PROVE_TAC[]
    ) THEN
    STRIP_TAC THEN
    UNDISCH_HD_TAC THEN
    MATCH_MP_TAC set_lemmataTheory.INJ_SUBSET_DOMAIN THEN
    SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
    PROVE_TAC[]
  ],


  REWRITE_TAC[S_CLOCK_FREE_def]
]);



val UF_SEM___VAR_RENAMING =
 store_thm
  ("UF_SEM___VAR_RENAMING",
    ``!f v f'. ((F_CLOCK_FREE f) /\
    (INJ f' (PATH_USED_VARS v UNION F_USED_VARS f) UNIV)) ==>
      (UF_SEM v f = UF_SEM (PATH_VAR_RENAMING f' v) (F_VAR_RENAMING f' f))``,

    INDUCT_THEN fl_induct ASSUME_TAC THENL [ (* 11 subgoals *)
      SIMP_TAC std_ss [F_CLOCK_FREE_def, F_USED_VARS_def,
                       F_VAR_RENAMING_def, UF_SEM_def,
                       LENGTH_PATH_VAR_RENAMING] THEN
      REPEAT STRIP_TAC THEN
      BOOL_EQ_STRIP_TAC THEN
      ASM_SIMP_TAC std_ss [ELEM_PATH_VAR_RENAMING] THEN
      MATCH_MP_TAC B_SEM___VAR_RENAMING THEN
      UNDISCH_NO_TAC 1 THEN
      MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
      SIMP_TAC std_ss [SUBSET_DEF, PATH_USED_VARS_def, IN_ABS,
        IN_UNION] THEN
      PROVE_TAC[],


      SIMP_TAC std_ss [F_CLOCK_FREE_def, F_USED_VARS_def,
                       F_VAR_RENAMING_def, UF_SEM_def,
                       LENGTH_PATH_VAR_RENAMING] THEN
      REPEAT STRIP_TAC THEN
      BOOL_EQ_STRIP_TAC THEN
      SUBGOAL_TAC `LENGTH v > 0` THEN1 (
        Cases_on `v` THEN
        FULL_SIMP_TAC arith_ss [LENGTH_def, GT, xnum_11]
      ) THEN
      ASM_SIMP_TAC std_ss [ELEM_PATH_VAR_RENAMING] THEN
      MATCH_MP_TAC B_SEM___VAR_RENAMING THEN
      UNDISCH_NO_TAC 2 THEN
      MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
      SIMP_TAC std_ss [SUBSET_DEF, PATH_USED_VARS_def, IN_ABS,
        IN_UNION] THEN
      PROVE_TAC[],


      SIMP_TAC std_ss [F_CLOCK_FREE_def, F_USED_VARS_def, UF_SEM_def,
        F_VAR_RENAMING_def, COMPLEMENT_PATH_VAR_RENAMING] THEN
      PROVE_TAC[PATH_USED_VARS_COMPLEMENT],


      SIMP_TAC std_ss [F_CLOCK_FREE_def, F_USED_VARS_def, UF_SEM_def,
        F_VAR_RENAMING_def] THEN
      REPEAT STRIP_TAC THEN
      REMAINS_TAC `INJ f'' (PATH_USED_VARS v UNION F_USED_VARS f) UNIV /\
                   INJ f'' (PATH_USED_VARS v UNION F_USED_VARS f') UNIV` THEN1 (
        PROVE_TAC[]
      ) THEN
      STRIP_TAC THEN
      UNDISCH_HD_TAC THEN
      MATCH_MP_TAC set_lemmataTheory.INJ_SUBSET_DOMAIN THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
      PROVE_TAC[],



      SIMP_TAC (std_ss++resq_SS) [F_CLOCK_FREE_def, F_USED_VARS_def, UF_SEM_def,
        F_VAR_RENAMING_def, IN_LESSX_REWRITE, LENGTH_PATH_VAR_RENAMING] THEN
      REPEAT STRIP_TAC THEN
      EXISTS_EQ_STRIP_TAC THEN
      BOOL_EQ_STRIP_TAC THEN
      `LENGTH v > j /\ j >= 0` by FULL_SIMP_TAC std_ss [GT_LS] THEN
      ASM_SIMP_TAC std_ss [SEL_PATH_VAR_RENAMING] THEN
      MATCH_MP_TAC US_SEM___VAR_RENAMING THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_NO_TAC  3 THEN
      MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
      PROVE_TAC[SEL_PATH_USED_VARS, SUBSET_DEF],



      SIMP_TAC (std_ss++resq_SS) [F_CLOCK_FREE_def, F_USED_VARS_def, UF_SEM_def,
        F_VAR_RENAMING_def, IN_LESSX_REWRITE, LENGTH_PATH_VAR_RENAMING,
        LENGTH_CAT_SEL_TOP_OMEGA, LS] THEN
      REPEAT STRIP_TAC THEN
      FORALL_EQ_STRIP_TAC THEN
      BOOL_EQ_STRIP_TAC THEN
      EXISTS_EQ_STRIP_TAC THEN

      SUBGOAL_TAC `(SEL (CAT (SEL (PATH_VAR_RENAMING f' v) (0,j),TOP_OMEGA)) (0,k)) =
                   MAP (LETTER_VAR_RENAMING f') (SEL (CAT (SEL v (0,j),TOP_OMEGA)) (0,k))` THEN1 (
        `TOP_OMEGA = PATH_VAR_RENAMING f' TOP_OMEGA` by REWRITE_TAC[PATH_VAR_RENAMING___TOP_OMEGA] THEN
        `LENGTH v > j /\ j >= 0` by FULL_SIMP_TAC std_ss [GT_LS] THEN
        `LENGTH (CAT (SEL v (0,j),TOP_OMEGA)) > k /\ k >= 0` by
          SIMP_TAC std_ss [LENGTH_CAT_SEL_TOP_OMEGA, GT] THEN
        ASM_SIMP_TAC std_ss [SEL_PATH_VAR_RENAMING, GSYM PATH_VAR_RENAMING___CAT]
      ) THEN
      ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

      MATCH_MP_TAC US_SEM___VAR_RENAMING THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_NO_TAC  1 THEN
      MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
      REPEAT STRIP_TAC THENL [
        ALL_TAC,
        ASM_REWRITE_TAC[]
      ] THEN
      DISJ1_TAC THEN
      UNDISCH_HD_TAC THEN
      SIMP_TAC list_ss [PATH_USED_VARS_def, IN_ABS, IN_LIST_BIGUNION,
        listTheory.MEM_MAP, GSYM LEFT_EXISTS_AND_THM, MEM_SEL] THEN
      REPEAT STRIP_TAC THEN
      UNDISCH_HD_TAC THEN
      Cases_on `n' > j` THENL [
        ASM_SIMP_TAC std_ss [ELEM_CAT_SEL___GREATER, TOP_OMEGA_def, ELEM_INFINITE,
          LETTER_USED_VARS_def, NOT_IN_EMPTY],

        ASM_SIMP_TAC arith_ss [ELEM_CAT_SEL___LESS_EQ, TOP_OMEGA_def] THEN
        REPEAT STRIP_TAC THEN
        Q_TAC EXISTS_TAC `n'` THEN
        ASM_REWRITE_TAC[] THEN
        Cases_on `v` THEN
        FULL_SIMP_TAC arith_ss [LENGTH_def, GT, LS]
      ],



      SIMP_TAC std_ss [F_CLOCK_FREE_def, UF_SEM_def, F_VAR_RENAMING_def,
        F_USED_VARS_def, LENGTH_PATH_VAR_RENAMING] THEN
      REPEAT STRIP_TAC THEN
      BOOL_EQ_STRIP_TAC THEN
      SUBGOAL_TAC `LENGTH v >= 1` THEN1 (
        Cases_on `v` THEN
        FULL_SIMP_TAC arith_ss [LENGTH_def, GT, GE]
      ) THEN
      ASM_SIMP_TAC std_ss [RESTN_PATH_VAR_RENAMING] THEN
      REMAINS_TAC `INJ f' (PATH_USED_VARS (RESTN v 1) UNION F_USED_VARS f) UNIV` THEN1 (
        PROVE_TAC[]
      ) THEN
      UNDISCH_NO_TAC 2 THEN
      MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
      SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
      PROVE_TAC[RESTN_PATH_USED_VARS, SUBSET_DEF],


      SIMP_TAC (std_ss++resq_SS) [F_CLOCK_FREE_def, UF_SEM_def, F_VAR_RENAMING_def,
        IN_LESSX_REWRITE, IN_LESS,  F_USED_VARS_def, LENGTH_PATH_VAR_RENAMING] THEN
      REPEAT STRIP_TAC THEN
      EXISTS_EQ_STRIP_TAC THEN
      BOOL_EQ_STRIP_TAC THEN
      BINOP_TAC THENL [
        SUBGOAL_TAC `LENGTH v >= k` THEN1 (
          Cases_on `v` THEN
          FULL_SIMP_TAC arith_ss [LENGTH_def, GT, GE, LS]
        ) THEN
        ASM_SIMP_TAC std_ss [RESTN_PATH_VAR_RENAMING] THEN
        REMAINS_TAC `INJ f'' (PATH_USED_VARS (RESTN v k) UNION F_USED_VARS f') UNIV` THEN1 (
          PROVE_TAC[]
        ) THEN
        UNDISCH_NO_TAC 2 THEN
        MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
        SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
        PROVE_TAC[RESTN_PATH_USED_VARS, SUBSET_DEF, GT_LS],


        FORALL_EQ_STRIP_TAC THEN
        BOOL_EQ_STRIP_TAC THEN
        SUBGOAL_TAC `LENGTH v >= j /\ LENGTH v > j` THEN1 (
          Cases_on `v` THEN
          FULL_SIMP_TAC arith_ss [LENGTH_def, GT, GE, LS]
        ) THEN
        ASM_SIMP_TAC std_ss [RESTN_PATH_VAR_RENAMING] THEN
        REMAINS_TAC `INJ f'' (PATH_USED_VARS (RESTN v j) UNION F_USED_VARS f) UNIV` THEN1 (
          PROVE_TAC[]
        ) THEN
        UNDISCH_NO_TAC 4 THEN
        MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
        SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
        PROVE_TAC[RESTN_PATH_USED_VARS, SUBSET_DEF]
      ],



      SIMP_TAC (std_ss++resq_SS) [F_CLOCK_FREE_def, UF_SEM_def, F_VAR_RENAMING_def,
        IN_LESSX_REWRITE, IN_LESS,  F_USED_VARS_def, LENGTH_PATH_VAR_RENAMING] THEN
      REPEAT STRIP_TAC THEN
      BINOP_TAC THENL [
        REMAINS_TAC `INJ f' (PATH_USED_VARS v UNION F_USED_VARS f) UNIV` THEN1 (
          PROVE_TAC[]
        ) THEN
        UNDISCH_HD_TAC THEN
        MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
        SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
        PROVE_TAC[],


        EXISTS_EQ_STRIP_TAC THEN
        BOOL_EQ_STRIP_TAC THEN
        BINOP_TAC THENL [
          ASM_SIMP_TAC std_ss [ELEM_PATH_VAR_RENAMING, GT_LS] THEN
          MATCH_MP_TAC B_SEM___VAR_RENAMING THEN
          UNDISCH_NO_TAC 1 THEN
          MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
          SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, PATH_USED_VARS_def, IN_ABS] THEN
          PROVE_TAC[GT_LS],

          Cases_on `j` THENL [
            REWRITE_TAC[] THEN
            REMAINS_TAC `INJ f' (PATH_USED_VARS TOP_OMEGA UNION F_USED_VARS f) UNIV` THEN1 (
              PROVE_TAC[PATH_VAR_RENAMING___TOP_OMEGA]
            ) THEN
            UNDISCH_NO_TAC 1 THEN
            MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
            SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, PATH_USED_VARS_def,
              PATH_USED_VARS___TOP_OMEGA, NOT_IN_EMPTY],


            SIMP_TAC arith_ss [] THEN
            SUBGOAL_TAC `CAT (SEL (PATH_VAR_RENAMING f' v) (0,n),TOP_OMEGA) =
                         PATH_VAR_RENAMING f' (CAT (SEL v (0,n),TOP_OMEGA))` THEN1 (
              SUBGOAL_TAC `LENGTH v > n /\ n >= 0` THEN1 (
                Cases_on `v` THEN
                FULL_SIMP_TAC arith_ss [LENGTH_def, GT, LS]
              ) THEN
              ASM_SIMP_TAC std_ss [PATH_VAR_RENAMING___CAT,
                                   SEL_PATH_VAR_RENAMING, PATH_VAR_RENAMING___TOP_OMEGA]
            ) THEN
            ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

            REMAINS_TAC `INJ f' (PATH_USED_VARS (CAT (SEL v (0,n),TOP_OMEGA)) UNION F_USED_VARS f) UNIV` THEN1 (
              PROVE_TAC[PATH_VAR_RENAMING___TOP_OMEGA]
            ) THEN
            UNDISCH_NO_TAC 1 THEN
            MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
            SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, CAT_PATH_USED_VARS, PATH_USED_VARS___TOP_OMEGA,
                NOT_IN_EMPTY] THEN
            REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
            DISJ1_TAC THEN
            SUBGOAL_TAC `LENGTH v > n /\ n >= 0` THEN1 (
                Cases_on `v` THEN
                FULL_SIMP_TAC arith_ss [LENGTH_def, GT, LS]
            ) THEN
            PROVE_TAC[SEL_PATH_USED_VARS, SUBSET_DEF]
          ]
        ]
      ],


      REWRITE_TAC[F_CLOCK_FREE_def],


      SIMP_TAC (std_ss++resq_SS) [F_CLOCK_FREE_def, UF_SEM_def, F_VAR_RENAMING_def,
        IN_LESSX_REWRITE, IN_LESS,  F_USED_VARS_def, LENGTH_PATH_VAR_RENAMING] THEN
      REPEAT STRIP_TAC THEN
      FORALL_EQ_STRIP_TAC THEN
      BOOL_EQ_STRIP_TAC THEN
      BINOP_TAC THENL [
            SUBGOAL_TAC `LENGTH (COMPLEMENT v) > j /\ j >= 0` THEN1 (
                FULL_SIMP_TAC arith_ss [LENGTH_def, LENGTH_COMPLEMENT, GT_LS]
            ) THEN
            ASM_SIMP_TAC std_ss [COMPLEMENT_PATH_VAR_RENAMING, SEL_PATH_VAR_RENAMING] THEN
            MATCH_MP_TAC US_SEM___VAR_RENAMING THEN
            ASM_REWRITE_TAC[] THEN
            UNDISCH_NO_TAC 3 THEN
            MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
            SIMP_TAC std_ss [SUBSET_DEF, IN_UNION, CAT_PATH_USED_VARS, PATH_USED_VARS___TOP_OMEGA,
                NOT_IN_EMPTY] THEN
            REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
            DISJ1_TAC THEN
            PROVE_TAC[SEL_PATH_USED_VARS, SUBSET_DEF, PATH_USED_VARS_COMPLEMENT],


            SUBGOAL_TAC `LENGTH v >= j` THEN1 (
                Cases_on `v` THEN
                FULL_SIMP_TAC arith_ss [LENGTH_def, GT, LS, GE]
            ) THEN
            ASM_SIMP_TAC std_ss [RESTN_PATH_VAR_RENAMING] THEN
            REMAINS_TAC `INJ f' (PATH_USED_VARS (RESTN v j) UNION F_USED_VARS f) UNIV`  THEN1 (
                PROVE_TAC[]
            ) THEN
            UNDISCH_NO_TAC 2 THEN
            MATCH_MP_TAC INJ_SUBSET_DOMAIN THEN
            SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
            PROVE_TAC[RESTN_PATH_USED_VARS, GT_LS, SUBSET_DEF]
      ]
   ]);



val S_VAR_RENAMING___S_CLOCK_FREE =
 store_thm
  ("S_VAR_RENAMING___S_CLOCK_FREE",

    ``!r g.  S_CLOCK_FREE (S_VAR_RENAMING g r) =
                S_CLOCK_FREE r``,

    INDUCT_THEN sere_induct ASSUME_TAC THEN (
        ASM_SIMP_TAC std_ss [S_VAR_RENAMING_def,
                                           S_CLOCK_FREE_def]
    ));


val F_VAR_RENAMING___F_CLOCK_SERE_FREE =
 store_thm
  ("F_VAR_RENAMING___F_CLOCK_SERE_FREE",

    ``!f g.  (F_CLOCK_SERE_FREE (F_VAR_RENAMING g f) =
                F_CLOCK_SERE_FREE f) /\
                (F_CLOCK_FREE (F_VAR_RENAMING g f) =
                F_CLOCK_FREE f) /\
                (F_SERE_FREE (F_VAR_RENAMING g f) =
                F_SERE_FREE f)``,

    INDUCT_THEN fl_induct ASSUME_TAC THEN (
        ASM_SIMP_TAC std_ss [F_VAR_RENAMING_def,
                                    F_CLOCK_SERE_FREE_def, F_CLOCK_FREE_def,
                                    F_SERE_FREE_def, S_VAR_RENAMING___S_CLOCK_FREE]
    ));


val WEAK_UF_SEM_def =
 Define
   `WEAK_UF_SEM v f = UF_SEM (PATH_APPEND v TOP_OMEGA) f`;


val STRONG_UF_SEM_def =
 Define
   `STRONG_UF_SEM v f = UF_SEM (PATH_APPEND v BOTTOM_OMEGA) f`;


val IS_PATH_WITH_REPLACEMENTS_def =
 Define
  `IS_PATH_WITH_REPLACEMENTS v w x = (LENGTH v = LENGTH w) /\
      (!n. n < LENGTH v ==> ((ELEM v n = ELEM w n) \/ (ELEM v n = x)))`;


val IS_LIST_WITH_REPLACEMENTS_def =
 Define
  `IS_LIST_WITH_REPLACEMENTS v w x = (LENGTH v = LENGTH w) /\
      (!n. n < LENGTH v ==> ((EL n v = EL n w) \/ (EL n v = x)))`;


val IS_TOP_BOTTOM_WELL_BEHAVED_def =
 Define
  `(IS_TOP_BOTTOM_WELL_BEHAVED (F_STRONG_BOOL b)   = T)
   /\
   (IS_TOP_BOTTOM_WELL_BEHAVED (F_WEAK_BOOL b)     = T)
   /\
   (IS_TOP_BOTTOM_WELL_BEHAVED (F_NOT f)           = IS_TOP_BOTTOM_WELL_BEHAVED f)
   /\
   (IS_TOP_BOTTOM_WELL_BEHAVED (F_AND(f1,f2))      = IS_TOP_BOTTOM_WELL_BEHAVED f1 /\ IS_TOP_BOTTOM_WELL_BEHAVED f2)
   /\
   (IS_TOP_BOTTOM_WELL_BEHAVED (F_STRONG_SERE r)   = ((UF_SEM TOP_OMEGA (F_STRONG_SERE r)) /\ ~(UF_SEM BOTTOM_OMEGA (F_STRONG_SERE r))))
   /\
   (IS_TOP_BOTTOM_WELL_BEHAVED (F_WEAK_SERE r)     = ((UF_SEM TOP_OMEGA (F_WEAK_SERE r)) /\ ~(UF_SEM BOTTOM_OMEGA (F_WEAK_SERE r))))
   /\
   (IS_TOP_BOTTOM_WELL_BEHAVED (F_NEXT f)          = IS_TOP_BOTTOM_WELL_BEHAVED f)
   /\
   (IS_TOP_BOTTOM_WELL_BEHAVED (F_UNTIL(f1,f2))    = IS_TOP_BOTTOM_WELL_BEHAVED f1 /\ IS_TOP_BOTTOM_WELL_BEHAVED f2)
   /\
   (IS_TOP_BOTTOM_WELL_BEHAVED (F_ABORT (f,b))     = IS_TOP_BOTTOM_WELL_BEHAVED f)
   /\
   (IS_TOP_BOTTOM_WELL_BEHAVED (F_SUFFIX_IMP(r,f)) = ((UF_SEM TOP_OMEGA (F_SUFFIX_IMP (r, f))) /\ ~(UF_SEM BOTTOM_OMEGA (F_SUFFIX_IMP (r, f)))) /\ IS_TOP_BOTTOM_WELL_BEHAVED f)`;





val IS_PSL_G_def =
 Define
   `(IS_PSL_G (F_STRONG_BOOL b) = T) /\
    (IS_PSL_G (F_WEAK_BOOL b) = T) /\
    (IS_PSL_G (F_NOT f) = IS_PSL_F f) /\
    (IS_PSL_G (F_AND (f,g)) = (IS_PSL_G f /\ IS_PSL_G g)) /\
    (IS_PSL_G (F_NEXT f) = IS_PSL_G f) /\
    (IS_PSL_G (F_UNTIL(f,g)) = F) /\
    (IS_PSL_G (F_ABORT (f,p)) = IS_PSL_G f) /\
    (IS_PSL_G (F_STRONG_SERE r) = F) /\
    (IS_PSL_G (F_WEAK_SERE r) = F) /\
    (IS_PSL_G (F_SUFFIX_IMP (r,f)) = F) /\
    (IS_PSL_G (F_CLOCK v) = F) /\
    (IS_PSL_F (F_STRONG_BOOL b) = T) /\
    (IS_PSL_F (F_WEAK_BOOL b) = T) /\
    (IS_PSL_F (F_NOT f) = IS_PSL_G f) /\
    (IS_PSL_F (F_AND (f,g)) = (IS_PSL_F f /\ IS_PSL_F g)) /\
    (IS_PSL_F (F_NEXT f) = IS_PSL_F f) /\
    (IS_PSL_F (F_UNTIL(f,g)) = (IS_PSL_F f /\ IS_PSL_F g)) /\
    (IS_PSL_F (F_ABORT (f,p)) = IS_PSL_F f) /\
    (IS_PSL_F (F_STRONG_SERE r) = F) /\
    (IS_PSL_F (F_WEAK_SERE r) = F) /\
    (IS_PSL_F (F_SUFFIX_IMP (r,f)) = F) /\
    (IS_PSL_F (F_CLOCK v) = F)`;


val IS_PSL_PREFIX_def =
  Define
   `(IS_PSL_PREFIX (F_NOT f) = IS_PSL_PREFIX f) /\
    (IS_PSL_PREFIX (F_AND (f,g)) = (IS_PSL_PREFIX f /\ IS_PSL_PREFIX g)) /\
    (IS_PSL_PREFIX (F_ABORT (f, p)) = (IS_PSL_PREFIX f)) /\
    (IS_PSL_PREFIX f = (IS_PSL_G f \/ IS_PSL_F f))`;


val IS_PSL_GF_def=
 Define
   `(IS_PSL_GF (F_STRONG_BOOL b) = T) /\
    (IS_PSL_GF (F_WEAK_BOOL b) = T) /\
    (IS_PSL_GF (F_NOT f) = IS_PSL_FG f) /\
    (IS_PSL_GF (F_AND (f,g)) = (IS_PSL_GF f /\ IS_PSL_GF g)) /\
    (IS_PSL_GF (F_NEXT f) = IS_PSL_GF f) /\
    (IS_PSL_GF (F_UNTIL(f,g)) = (IS_PSL_GF f /\ IS_PSL_F g)) /\
    (IS_PSL_GF (F_ABORT (f,p)) = IS_PSL_GF f) /\
    (IS_PSL_GF (F_STRONG_SERE r) = F) /\
    (IS_PSL_GF (F_WEAK_SERE r) = F) /\
    (IS_PSL_GF (F_SUFFIX_IMP (r,f)) = F) /\
    (IS_PSL_GF (F_CLOCK v) = F) /\

    (IS_PSL_FG (F_STRONG_BOOL b) = T) /\
    (IS_PSL_FG (F_WEAK_BOOL b) = T) /\
    (IS_PSL_FG (F_NOT f) = IS_PSL_GF f) /\
    (IS_PSL_FG (F_AND (f,g)) = (IS_PSL_FG f /\ IS_PSL_FG g)) /\
    (IS_PSL_FG (F_NEXT f) = IS_PSL_FG f) /\
    (IS_PSL_FG (F_UNTIL(f,g)) = (IS_PSL_FG f /\ IS_PSL_FG g)) /\
    (IS_PSL_FG (F_ABORT (f,p)) = IS_PSL_FG f) /\
    (IS_PSL_FG (F_STRONG_SERE r) = F) /\
    (IS_PSL_FG (F_WEAK_SERE r) = F) /\
    (IS_PSL_FG (F_SUFFIX_IMP (r,f)) = F) /\
    (IS_PSL_FG (F_CLOCK v) = F)`;


val IS_PSL_STREET_def =
  Define
   `(IS_PSL_STREET (F_NOT f) = IS_PSL_STREET f) /\
    (IS_PSL_STREET (F_AND (f,g)) = (IS_PSL_STREET f /\ IS_PSL_STREET g)) /\
    (IS_PSL_STREET (F_ABORT (f, p)) = (IS_PSL_STREET f)) /\
    (IS_PSL_STREET f = (IS_PSL_GF f \/ IS_PSL_FG f))`;


val IS_PSL_THM = save_thm("IS_PSL_THM",
   LIST_CONJ [IS_PSL_G_def,
              IS_PSL_GF_def,
              IS_PSL_PREFIX_def,
              IS_PSL_STREET_def]);


(*=============================================================================
= General lemmata about PSL
============================================================================*)

val IS_INFINITE_TOP_BOTTOM_FREE_PATH___IMPLIES___IS_INFINITE_PROPER_PATH =
 store_thm
  ("IS_INFINITE_TOP_BOTTOM_FREE_PATH___IMPLIES___IS_INFINITE_PROPER_PATH",
   ``!f. IS_INFINITE_TOP_BOTTOM_FREE_PATH f ==> IS_INFINITE_PROPER_PATH f``,

   REWRITE_TAC[IS_INFINITE_TOP_BOTTOM_FREE_PATH_def, IS_INFINITE_PROPER_PATH_def] THEN
   PROVE_TAC[letter_distinct]);



val BEXP_PROP_FREE___B_SEM =
 store_thm
  ("BEXP_PROP_FREE___B_SEM",

   ``!b s c. BEXP_PROP_FREE c b ==> (B_SEM s b = B_SEM (INSERT_PROP c s) b)``,

   REPEAT STRIP_TAC THEN
   REMAINS_TAC `LETTER_RESTRICT (B_USED_VARS b) s =
                LETTER_RESTRICT (B_USED_VARS b) (INSERT_PROP c s)` THEN1 (
     PROVE_TAC[B_USED_VARS_INTER_SUBSET_THM, SUBSET_REFL]
   ) THEN
   Cases_on `s` THEN
   REWRITE_TAC[LETTER_RESTRICT_def, INSERT_PROP_def, letter_11] THEN
   SIMP_TAC std_ss [EXTENSION, IN_INTER, IN_ABS] THEN
   REPEAT STRIP_TAC THEN
   BOOL_EQ_STRIP_TAC THEN
   `~(x = c)` by PROVE_TAC [BEXP_PROP_FREE_def] THEN
   ASM_SIMP_TAC std_ss [IN_DEF]);


val S_CLOCK_FREE___S_CLOCK_COMP =
 store_thm
  ("S_CLOCK_FREE___S_CLOCK_COMP",
   ``!r c. (S_CLOCK_FREE (S_CLOCK_COMP c r))``,

   INDUCT_THEN sere_induct ASSUME_TAC THEN
   ASM_SIMP_TAC std_ss [S_CLOCK_COMP_def, S_CLOCK_FREE_def]);


val F_CLOCK_FREE___F_CLOCK_COMP =
 store_thm
  ("F_CLOCK_FREE___F_CLOCK_COMP",
   ``!f c. (F_CLOCK_FREE (F_CLOCK_COMP c f))``,

   INDUCT_THEN fl_induct ASSUME_TAC THEN
   ASM_SIMP_TAC std_ss [F_CLOCK_COMP_def,
                        F_CLOCK_FREE_def,
                        F_U_CLOCK_def,
                        F_W_CLOCK_def,
                        F_W_def,
                        F_OR_def,
                        F_G_def,
                        F_F_def,
                        F_IMPLIES_def,
                        S_CLOCK_FREE___S_CLOCK_COMP]);


val F_SERE_FREE___IMPLIES___F_SERE_FREE_F_CLOCK_COMP =
 store_thm
  ("F_SERE_FREE___IMPLIES___F_SERE_FREE_F_CLOCK_COMP",
   ``!f c. F_SERE_FREE f ==> (F_SERE_FREE (F_CLOCK_COMP c f))``,

   INDUCT_THEN fl_induct ASSUME_TAC THEN
   ASM_SIMP_TAC std_ss [F_CLOCK_COMP_def,
                        F_SERE_FREE_def,
                        F_U_CLOCK_def,
                        F_W_CLOCK_def,
                        F_W_def,
                        F_OR_def,
                        F_G_def,
                        F_F_def,
                        F_IMPLIES_def]);


val S_USED_VARS___CLOCK_COMP =
 store_thm
  ("S_USED_VARS___CLOCK_COMP",
   ``!s c. S_USED_VARS (S_CLOCK_COMP c s) SUBSET S_USED_VARS s UNION B_USED_VARS c``,

   REWRITE_TAC[SUBSET_DEF, IN_UNION] THEN
   INDUCT_THEN sere_induct ASSUME_TAC THEN
   ASM_SIMP_TAC std_ss [S_CLOCK_COMP_def, S_USED_VARS_def,
                        B_USED_VARS_def, IN_UNION,
                        NOT_IN_EMPTY] THEN
   REPEAT STRIP_TAC THEN
   REPEAT BOOL_EQ_STRIP_TAC THEN
   ASM_SIMP_TAC std_ss [] THEN
   METIS_TAC[]);

val F_USED_VARS___CLOCK_COMP =
 store_thm
  ("F_USED_VARS___CLOCK_COMP",
   ``!f c. F_USED_VARS (F_CLOCK_COMP c f) SUBSET (F_USED_VARS f UNION B_USED_VARS c)``,

   ASSUME_TAC S_USED_VARS___CLOCK_COMP THEN
   FULL_SIMP_TAC std_ss [SUBSET_DEF, IN_UNION] THEN
   INDUCT_THEN fl_induct ASSUME_TAC THEN
   ASM_SIMP_TAC std_ss [F_CLOCK_COMP_def,
                        F_USED_VARS_def,
                        B_USED_VARS_def,
                        F_U_CLOCK_def,
                        F_W_CLOCK_def,
                        F_W_def,
                        F_OR_def,
                        F_G_def,
                        F_F_def,
                        F_IMPLIES_def,
                        IN_UNION,
                        NOT_IN_EMPTY] THEN
   REPEAT STRIP_TAC THEN
   REPEAT BOOL_EQ_STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   METIS_TAC[]);



val INFINITE_PROPER_PATH___RESTN_TOP_BOTTOM_OMEGA =
 store_thm
  ("INFINITE_PROPER_PATH___RESTN_TOP_BOTTOM_OMEGA",
   ``(!v t t'. ((IS_INFINITE_PROPER_PATH v) /\ (ELEM v t = TOP) /\ (t <= t')) ==>
   (RESTN v t' = TOP_OMEGA)) /\
     (!v t t'. ((IS_INFINITE_PROPER_PATH v) /\ (ELEM v t = BOTTOM) /\ (t <= t')) ==>
   (RESTN v t' = BOTTOM_OMEGA))``,

   REWRITE_TAC[IS_INFINITE_PROPER_PATH_def, TOP_OMEGA_def, BOTTOM_OMEGA_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC std_ss [RESTN_INFINITE, path_11, FUN_EQ_THM] THEN
   REPEAT STRIP_TAC THEN (
      `t <= n + t'` by DECIDE_TAC THEN
      `?u. n + t' = t + u` by PROVE_TAC[LESS_EQ_EXISTS] THEN
      FULL_SIMP_TAC arith_ss [] THEN
      WEAKEN_TAC (fn t => true) THEN
      Induct_on `u` THENL [
         EVAL_TAC THEN ASM_SIMP_TAC arith_ss [] THEN PROVE_TAC[ELEM_INFINITE],
         ASM_SIMP_TAC arith_ss [GSYM ADD_SUC]
      ]
   ));


val PROPER_PATH___IS_INFINITE_TOP_BOTTOM =
 store_thm
  ("PROPER_PATH___IS_INFINITE_TOP_BOTTOM",
   ``(!v t. ((IS_PROPER_PATH v) /\ (t < LENGTH v) /\ ((ELEM v t = TOP) \/ (ELEM v t = BOTTOM))) ==>
      IS_INFINITE_PROPER_PATH v)``,

   SIMP_TAC std_ss [IS_PROPER_PATH_def, IS_FINITE_PROPER_PATH_def] THEN
   REPEAT STRIP_TAC THEN
   PROVE_TAC[PATH_TOP_FREE_ELEM, PATH_BOTTOM_FREE_ELEM]);





val PATH_PROP_FREE_SEM =
 store_thm
  ("PATH_PROP_FREE_SEM",
     ``!s t f p. (PATH_PROP_FREE p (INFINITE f)) ==> ((f t = STATE s) ==> (~ s p))``,

   REWRITE_TAC [PATH_PROP_FREE_def, ELEM_INFINITE, IN_DEF] THEN
   EVAL_TAC THEN
   PROVE_TAC[]
);


val PATH_PROP_FREE_RESTN =
 store_thm
  ("PATH_PROP_FREE_RESTN",
   ``!v t p. t < LENGTH v ==> PATH_PROP_FREE p v ==> PATH_PROP_FREE p (RESTN v t)``,

   REWRITE_TAC [LENGTH_def, LS, PATH_PROP_FREE_def, ELEM_RESTN] THEN
   Cases_on `v` THEN REPEAT STRIP_TAC THENL [
     `LENGTH (RESTN (FINITE l) t) = LENGTH (FINITE l) - t` by PROVE_TAC[LENGTH_RESTN_COR] THEN
     FULL_SIMP_TAC list_ss [] THEN
     `n < (LENGTH l) - t` by PROVE_TAC [LENGTH_def, LS, SUB_xnum_num_def] THEN
     `n+t < LENGTH l` by DECIDE_TAC THEN
     `n + t < LENGTH (FINITE l)` by PROVE_TAC [LENGTH_def, LS, SUB_xnum_num_def] THEN
     PROVE_TAC[],

     FULL_SIMP_TAC list_ss [LENGTH_def, LS] THEN
     PROVE_TAC[]
   ]);


val PATH_PROP_FREE_COMPLEMENT =
 store_thm
  ("PATH_PROP_FREE_COMPLEMENT",
   ``!t f. PATH_PROP_FREE t f = PATH_PROP_FREE t (COMPLEMENT f)``,

   SIMP_TAC list_ss [PATH_PROP_FREE_def, LENGTH_COMPLEMENT, ELEM_COMPLEMENT, COMPLEMENT_LETTER_Cases]
);


val IS_INFINITE_PROPER_PATH___COMPLEMENT =
 store_thm
  ("IS_INFINITE_PROPER_PATH___COMPLEMENT",
   ``!v. IS_INFINITE_PROPER_PATH v = IS_INFINITE_PROPER_PATH (COMPLEMENT v)``,
   STRIP_TAC THEN
   REWRITE_TAC [IS_INFINITE_PROPER_PATH_def] THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC ``COMPLEMENT_LETTER o (p :num -> 'a letter)``
   THENL [
      ALL_TAC,
      `v = COMPLEMENT (INFINITE p)` by PROVE_TAC[COMPLEMENT_COMPLEMENT]
   ] THEN
   FULL_SIMP_TAC list_ss [COMPLEMENT_def, COMPLEMENT_LETTER_Cases]);


val IS_INFINITE_PROPER_PATH_RESTN =
 store_thm
  ("IS_INFINITE_PROPER_PATH_RESTN",
   ``!v t. IS_INFINITE_PROPER_PATH v ==> IS_INFINITE_PROPER_PATH (RESTN v t)``,

   REWRITE_TAC [IS_INFINITE_PROPER_PATH_def] THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC ``(\n. p (n + t)):num -> 'a letter`` THEN
   ASM_SIMP_TAC arith_ss [RESTN_INFINITE, GSYM ADD_SUC]);




val IS_INFINITE_PROPER_PATH___CAT_SEL_TOP_OMEGA =
 store_thm
  ("IS_INFINITE_PROPER_PATH___CAT_SEL_TOP_OMEGA",
   ``!v j. (IS_INFINITE_PROPER_PATH v /\ ~(ELEM v j = BOTTOM)) ==> IS_INFINITE_PROPER_PATH (CAT (SEL v (0,j - 1),TOP_OMEGA))``,

   REPEAT GEN_TAC THEN
   `? v'. (CAT (SEL v (0,j - 1),TOP_OMEGA)) = v'` by PROVE_TAC[] THEN
   REWRITE_TAC [IS_INFINITE_PROPER_PATH_def] THEN
   `IS_INFINITE v'` by PROVE_TAC[CAT_INFINITE, TOP_OMEGA_def] THEN
   `?q. INFINITE q = v'` by PROVE_TAC[IS_INFINITE_EXISTS] THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC ``q:num -> 'a letter`` THEN
   REPEAT STRIP_TAC THENL [
      PROVE_TAC[],

      Cases_on `SUC n <= j-1` THENL [
         `n <= j - 1` by DECIDE_TAC THEN
         `ELEM (INFINITE q) n = ELEM v n` by PROVE_TAC[ELEM_CAT_SEL___LESS_EQ] THEN
         `ELEM (INFINITE q) (SUC n) = ELEM v (SUC n)` by PROVE_TAC[ELEM_CAT_SEL___LESS_EQ] THEN
         `q n = p n` by PROVE_TAC[ELEM_INFINITE] THEN
         `q (SUC n) = p (SUC n)` by PROVE_TAC[ELEM_INFINITE] THEN
         `p n = TOP` by PROVE_TAC[] THEN
         `p (SUC n) = TOP` by PROVE_TAC[] THEN
         PROVE_TAC[],

         `SUC n > j - 1` by DECIDE_TAC THEN
         `ELEM (INFINITE q) (SUC n) = ELEM TOP_OMEGA (SUC n - (SUC (j-1)))` by PROVE_TAC[ELEM_CAT_SEL___GREATER] THEN
         FULL_SIMP_TAC arith_ss [ELEM_INFINITE, TOP_OMEGA_def]
      ],

      Cases_on `SUC n <= j-1` THENL [
         `n <= j - 1` by DECIDE_TAC THEN
         `ELEM (INFINITE q) n = ELEM v n` by PROVE_TAC[ELEM_CAT_SEL___LESS_EQ] THEN
         `ELEM (INFINITE q) (SUC n) = ELEM v (SUC n)` by PROVE_TAC[ELEM_CAT_SEL___LESS_EQ] THEN
         `q n = p n` by PROVE_TAC[ELEM_INFINITE] THEN
         `q (SUC n) = p (SUC n)` by PROVE_TAC[ELEM_INFINITE] THEN
         `p n = BOTTOM` by PROVE_TAC[] THEN
         `p (SUC n) = BOTTOM` by PROVE_TAC[] THEN
         PROVE_TAC[],

         Cases_on `n > j - 1` THENL [
            `ELEM (INFINITE q) n = ELEM TOP_OMEGA (n - SUC (j-1))` by PROVE_TAC[ELEM_CAT_SEL___GREATER] THEN
            FULL_SIMP_TAC arith_ss [ELEM_INFINITE, TOP_OMEGA_def] THEN
            `~ (TOP = BOTTOM)` by EVAL_TAC,

            `n <= j - 1` by DECIDE_TAC THEN
            `ELEM (INFINITE q) n = ELEM v n` by PROVE_TAC[ELEM_CAT_SEL___LESS_EQ] THEN
            `q n = p n` by PROVE_TAC[ELEM_INFINITE] THEN
            `p n = BOTTOM` by PROVE_TAC[] THEN
            Cases_on `j = 0` THENL [
               `n = j` by DECIDE_TAC THEN
               `p j = BOTTOM` by PROVE_TAC[],

               `p (SUC n) = BOTTOM` by PROVE_TAC[] THEN
               `SUC n = j` by DECIDE_TAC
            ] THEN
            `p j = BOTTOM` by PROVE_TAC[] THEN
            PROVE_TAC [ELEM_INFINITE]
         ]
      ]
   ]);



val PATH_PROP_FREE___CAT_SEL_INFINITE___IMPLIES =
 store_thm
  ("PATH_PROP_FREE___CAT_SEL_INFINITE___IMPLIES",
   ``!p a j. PATH_PROP_FREE a (INFINITE p) ==> PATH_PROP_FREE a (CAT (SEL (INFINITE p) (0,j - 1),TOP_OMEGA))``,

   REWRITE_TAC [PATH_PROP_FREE_def, IN_DEF] THEN
   ASM_REWRITE_TAC [LENGTH_def, LS, ELEM_INFINITE] THEN
   REPEAT STRIP_TAC THEN
   Cases_on `n <= j - 1` THENL [
      `ELEM (CAT (SEL (INFINITE p) (0,j - 1),TOP_OMEGA)) n = ELEM (INFINITE p) n` by PROVE_TAC[ELEM_CAT_SEL___LESS_EQ] THEN
      PROVE_TAC[ELEM_INFINITE],

      `n > j - 1` by DECIDE_TAC THEN
      `~(STATE s = TOP)` by EVAL_TAC THEN
      `ELEM (CAT (SEL (INFINITE p) (0,j - 1),TOP_OMEGA)) n = ELEM TOP_OMEGA (n-SUC (j-1))` by PROVE_TAC[ELEM_CAT_SEL___GREATER] THEN
      FULL_SIMP_TAC arith_ss [TOP_OMEGA_def, ELEM_INFINITE]
   ]);


val IS_FINITE_PROPER_PATH___COMPLEMENT =
 store_thm
  ("IS_FINITE_PROPER_PATH___COMPLEMENT",

   ``!v. IS_FINITE_PROPER_PATH v ==> ((COMPLEMENT v) = v)``,

   REPEAT STRIP_TAC THEN
   FULL_SIMP_TAC std_ss [IS_FINITE_PROPER_PATH_def] THEN

   REWRITE_TAC[COMPLEMENT_def, path_11] THEN
   `TOP_FREE p /\ BOTTOM_FREE p` by PROVE_TAC[PATH_TOP_FREE_def, PATH_BOTTOM_FREE_def] THEN
   UNDISCH_TAC ``TOP_FREE p`` THEN
   UNDISCH_TAC ``BOTTOM_FREE p`` THEN
   SPEC_TAC (``p:'a letter list``,``q:'a letter list``) THEN
   Induct_on `q` THENL [
      SIMP_TAC list_ss [],
      Cases_on `h` THEN ASM_SIMP_TAC list_ss [TOP_FREE_def, BOTTOM_FREE_def, COMPLEMENT_LETTER_def]
   ]);


val IS_FINITE_PROPER_PATH___RESTN =
 store_thm
  ("IS_FINITE_PROPER_PATH___RESTN",

   ``!v k. (IS_FINITE_PROPER_PATH v  /\ k < LENGTH v) ==> IS_FINITE_PROPER_PATH (RESTN v k)``,

   Induct_on `k` THENL [
      SIMP_TAC list_ss [IS_FINITE_PROPER_PATH_def, PSLPathTheory.RESTN_def, FinitePSLPathTheory.RESTN_def],

      FULL_SIMP_TAC list_ss [IS_FINITE_PROPER_PATH_def] THEN
      REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC list_ss [PSLPathTheory.RESTN_def, FinitePSLPathTheory.RESTN_def] THEN

      `?v'. v' = FINITE (REST p)` by PROVE_TAC[] THEN
      `SUC k < LENGTH p` by METIS_TAC[LENGTH_def, LS] THEN
      `0 < LENGTH p` by DECIDE_TAC THEN
      `REST v = v'` by ASM_SIMP_TAC list_ss [PSLPathTheory.REST_def, FinitePSLPathTheory.REST_def] THEN
      `LENGTH v' = LENGTH v - 1` by
         ASM_SIMP_TAC list_ss [LENGTH_def, SUB_xnum_num_def, xnum_11, FinitePSLPathTheory.REST_def, LENGTH_TL] THEN
      SUBGOAL_THEN ``PATH_TOP_FREE (v':'a letter path)`` ASSUME_TAC THEN1(
         FULL_SIMP_TAC std_ss [PATH_TOP_FREE_ELEM] THEN
         `!n. (n < LENGTH (FINITE p) - 1) = (n + 1 < LENGTH (FINITE p))` by
            SIMP_TAC arith_ss [LENGTH_def, SUB_xnum_num_def, LS] THEN
         `FINITE (REST p) = RESTN (FINITE p) 1` by EVAL_TAC THEN
         ASM_SIMP_TAC arith_ss [ELEM_RESTN] THEN
         METIS_TAC[]
      ) THEN
      SUBGOAL_THEN ``PATH_BOTTOM_FREE (v':'a letter path)`` ASSUME_TAC THEN1(
         FULL_SIMP_TAC std_ss [PATH_BOTTOM_FREE_ELEM] THEN
         `!n. (n < LENGTH (FINITE p) - 1) = (n + 1 < LENGTH (FINITE p))` by
            SIMP_TAC arith_ss [LENGTH_def, SUB_xnum_num_def, LS] THEN
         `FINITE (REST p) = RESTN (FINITE p) 1` by EVAL_TAC THEN
         ASM_SIMP_TAC arith_ss [ELEM_RESTN] THEN
         METIS_TAC[]
      ) THEN
      `k < LENGTH v'` by ASM_SIMP_TAC arith_ss [LENGTH_def, SUB_xnum_num_def, LS] THEN
      METIS_TAC[]
   ]);




(**************************************************************************)
(* Lemmata                                                                *)
(**************************************************************************)








val INFINITE_PROPER_PATH___TOP_BOTTOM_FOLLOWING =
 store_thm
  ("INFINITE_PROPER_PATH___TOP_BOTTOM_FOLLOWING",

   ``!v k l. (IS_INFINITE_PROPER_PATH v /\ l >= k) ==> (
         ((ELEM v k = TOP) ==> (ELEM v l = TOP)) /\
         ((ELEM v k = BOTTOM) ==> (ELEM v l = BOTTOM)))``,

   Induct_on `(l-k):num` THENL [
      SIMP_TAC arith_ss [] THEN
      REPEAT STRIP_TAC THEN
      `l = k` by DECIDE_TAC THEN
      PROVE_TAC[],

      REPEAT STRIP_TAC THEN
      `~(l = 0)` by DECIDE_TAC THEN
      `?l'. l = SUC l'` by PROVE_TAC[num_CASES] THEN
      `v = l' - k` by DECIDE_TAC THEN
      `l' >= k` by DECIDE_TAC THENL [
         `ELEM v' l' = TOP` by METIS_TAC[],
         `ELEM v' l' = BOTTOM` by METIS_TAC[]
      ] THEN
      METIS_TAC[ELEM_INFINITE, IS_INFINITE_PROPER_PATH_def]
   ]);


val IS_PROPER_PATH___COMPLEMENT =
 store_thm
  ("IS_PROPER_PATH___COMPLEMENT",
   ``!v. (IS_PROPER_PATH v) = (IS_PROPER_PATH (COMPLEMENT v))``,

   REWRITE_TAC[IS_PROPER_PATH_def] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      PROVE_TAC[IS_INFINITE_PROPER_PATH___COMPLEMENT],
      PROVE_TAC[IS_FINITE_PROPER_PATH___COMPLEMENT],
      PROVE_TAC[IS_INFINITE_PROPER_PATH___COMPLEMENT],
      PROVE_TAC[IS_FINITE_PROPER_PATH___COMPLEMENT, COMPLEMENT_COMPLEMENT]
   ]);


val IS_PATH_WITH_REPLACEMENTS___COMPLEMENT =
 store_thm
  ("IS_PATH_WITH_REPLACEMENTS___COMPLEMENT",
   ``!v w x. (IS_PATH_WITH_REPLACEMENTS v w x = IS_PATH_WITH_REPLACEMENTS (COMPLEMENT v) (COMPLEMENT w) (COMPLEMENT_LETTER x))``,

   REWRITE_TAC [IS_PATH_WITH_REPLACEMENTS_def] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      ASM_REWRITE_TAC[LENGTH_COMPLEMENT],

      FULL_SIMP_TAC std_ss [LENGTH_COMPLEMENT] THEN
      `n < LENGTH w` by PROVE_TAC[] THEN
      ASM_SIMP_TAC std_ss [ELEM_COMPLEMENT] THEN
      PROVE_TAC[COMPLEMENT_LETTER_COMPLEMENT_LETTER],

      PROVE_TAC[LENGTH_COMPLEMENT],

      FULL_SIMP_TAC std_ss [LENGTH_COMPLEMENT] THEN
      `n < LENGTH w` by PROVE_TAC[] THEN
      METIS_TAC[ELEM_COMPLEMENT, COMPLEMENT_LETTER_COMPLEMENT_LETTER]
   ]);

val IS_PATH_WITH_REPLACEMENTS___CAT_SEL =
 store_thm
  ("IS_PATH_WITH_REPLACEMENTS___CAT_SEL",
   ``!v w j x p. (IS_PATH_WITH_REPLACEMENTS v w x /\ j < LENGTH v) ==>
              IS_PATH_WITH_REPLACEMENTS (CAT (SEL v (0, j), p)) (CAT (SEL w (0, j), p)) x``,

   SIMP_TAC std_ss [IS_PATH_WITH_REPLACEMENTS_def] THEN
   REPEAT STRIP_TAC THENL [
      Cases_on `p` THEN SIMP_TAC std_ss [LENGTH_CAT, LENGTH_SEL],

      Cases_on `n <= j` THENL [
         SUBGOAL_TAC `n < LENGTH v` THEN1 (
            Cases_on `v` THEN Cases_on `w` THEN
            FULL_SIMP_TAC arith_ss [LENGTH_def, xnum_11, LS, xnum_distinct]
         ) THEN
         ASM_SIMP_TAC std_ss [ELEM_CAT_SEL___LESS_EQ],

         ASM_SIMP_TAC arith_ss [ELEM_CAT_SEL___GREATER]
      ]
   ]);


val IS_PATH_WITH_REPLACEMENTS___RESTN =
 store_thm
  ("IS_PATH_WITH_REPLACEMENTS___RESTN",
   ``!v w x n. (n <= LENGTH v /\ IS_PATH_WITH_REPLACEMENTS v w x) ==> IS_PATH_WITH_REPLACEMENTS (RESTN v n) (RESTN w n) x``,

   SIMP_TAC std_ss [IS_PATH_WITH_REPLACEMENTS_def, LENGTH_RESTN_THM_LE] THEN
   REPEAT STRIP_TAC THENL [
      PROVE_TAC[LENGTH_RESTN_THM_LE],

      REWRITE_TAC[ELEM_RESTN] THEN
      SUBGOAL_TAC `n' + n < LENGTH v` THEN1 (
        Cases_on `v` THEN Cases_on `w` THEN
        FULL_SIMP_TAC arith_ss [LENGTH_def, LS, xnum_11, LE_num_xnum_def, SUB_xnum_num_def]
      ) THEN
      PROVE_TAC[]
   ]);


val SEL_IS_PATH_WITH_REPLACEMENTS =
 store_thm
  ("SEL_IS_PATH_WITH_REPLACEMENTS",

   ``!v w x n m. (IS_PATH_WITH_REPLACEMENTS v w x /\ n < LENGTH v /\ m < LENGTH v) ==>
      IS_LIST_WITH_REPLACEMENTS (SEL v (n, m)) (SEL w (n, m)) x``,

   SIMP_TAC list_ss [LENGTH_SEL, IS_PATH_WITH_REPLACEMENTS_def, IS_LIST_WITH_REPLACEMENTS_def] THEN
   REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
   Cases_on `m <= n` THENL [
      SIMP_TAC std_ss [SEL_def] THEN
      `(m - n + 1 = SUC 0) /\ (n' = 0)` by DECIDE_TAC THEN
      ASM_REWRITE_TAC[SEL_REC_SUC, SEL_REC_def, EL, HD] THEN
      PROVE_TAC[],

      `?k. n' + n = k` by PROVE_TAC[] THEN
      `(n' = k - n) /\ (n <= k) /\ (k <= m)` by DECIDE_TAC THEN
      ASM_SIMP_TAC std_ss [EL_SEL] THEN
      SUBGOAL_TAC `k < LENGTH v`THEN1 (
         Cases_on `v` THEN  Cases_on `w` THEN
         FULL_SIMP_TAC arith_ss [LENGTH_def, LS, xnum_11, xnum_distinct]
      ) THEN
      PROVE_TAC[]
   ]);


val IS_LIST_WITH_REPLACEMENTS___SUC =
 store_thm
  ("IS_LIST_WITH_REPLACEMENTS___SUC",

   ``!l1 l2 x1 x2 x. IS_LIST_WITH_REPLACEMENTS (x1::l1) (x2::l2) x =
      (IS_LIST_WITH_REPLACEMENTS l1 l2 x /\ ((x1 = x2) \/ (x1 = x)))``,

   SIMP_TAC list_ss [IS_LIST_WITH_REPLACEMENTS_def] THEN
   REPEAT GEN_TAC THEN
   Cases_on `(LENGTH l1 = LENGTH l2)` THEN ASM_REWRITE_TAC[] THEN
   EQ_TAC THEN REPEAT STRIP_TAC THENL [
      `SUC n < SUC (LENGTH l2)` by DECIDE_TAC THEN
      RES_TAC THEN
      FULL_SIMP_TAC list_ss [],

      `0 < SUC (LENGTH l2)` by DECIDE_TAC THEN
      RES_TAC THEN
      FULL_SIMP_TAC list_ss [],

      Cases_on `n` THEN ASM_SIMP_TAC list_ss [],
      Cases_on `n` THEN ASM_SIMP_TAC list_ss []
   ]);




val IS_LIST_WITH_REPLACEMENTS___APPEND =
 store_thm
  ("IS_LIST_WITH_REPLACEMENTS___APPEND",

   ``!l l1 l2 l' l1' l2' x. ((l = l1 <> l2) /\ (l' = l1' <> l2') /\ (LENGTH l1 = LENGTH l1')) ==>
      (IS_LIST_WITH_REPLACEMENTS l l' x =
      (IS_LIST_WITH_REPLACEMENTS l1 l1' x /\ IS_LIST_WITH_REPLACEMENTS l2 l2' x))``,

   REWRITE_TAC[IS_LIST_WITH_REPLACEMENTS_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC list_ss [] THEN
   Cases_on `LENGTH l2 = LENGTH l2'` THEN ASM_REWRITE_TAC[] THEN
   EQ_TAC THEN REPEAT STRIP_TAC THENL [
      `n < LENGTH l1' + LENGTH l2'` by DECIDE_TAC THEN
      METIS_TAC[EL_APPEND1],

      `?k. k = LENGTH l1' + n` by PROVE_TAC[] THEN
      `(k - LENGTH l1' = n) /\ (LENGTH l1' <= k) /\ (k < LENGTH l1' + LENGTH l2')` by DECIDE_TAC THEN
      METIS_TAC[EL_APPEND2],

      Cases_on `n < LENGTH l1'` THENL [
         METIS_TAC[EL_APPEND1],

         `?k. k = n - LENGTH l1'` by PROVE_TAC[] THEN
         `(LENGTH l1' <= n) /\ (k < LENGTH l2')` by DECIDE_TAC THEN
         METIS_TAC[EL_APPEND2]
      ]
   ]);


val IS_LIST_WITH_REPLACEMENTS___SEG =
 store_thm
  ("IS_LIST_WITH_REPLACEMENTS___SEG",

   ``!x l l' n m. (n + m <= LENGTH l /\ IS_LIST_WITH_REPLACEMENTS l l' x) ==>
      (IS_LIST_WITH_REPLACEMENTS (SEG n m l) (SEG n m l') x)``,

   REWRITE_TAC[IS_LIST_WITH_REPLACEMENTS_def] THEN
   SIMP_TAC list_ss [LENGTH_SEG, SEG_EL]);


val F_CLOCK_SERE_FREE___IS_TOP_BOTTOM_WELL_BEHAVED =
 store_thm
  ("F_CLOCK_SERE_FREE___IS_TOP_BOTTOM_WELL_BEHAVED",
   ``!f. (F_CLOCK_SERE_FREE f) ==> (IS_TOP_BOTTOM_WELL_BEHAVED f)``,

   INDUCT_THEN fl_induct ASSUME_TAC THEN
   FULL_SIMP_TAC std_ss [F_CLOCK_SERE_FREE_def, IS_TOP_BOTTOM_WELL_BEHAVED_def, F_CLOCK_FREE_def, F_SERE_FREE_def]);


(***********************************************************
 * Important Lemmata
 ***********************************************************)

val UF_SEM___F_CLOCK_SERE_FREE___OMEGA_TOP_BOTTOM =
 store_thm
  ("UF_SEM___F_CLOCK_SERE_FREE___OMEGA_TOP_BOTTOM",
   ``!f. (F_CLOCK_SERE_FREE f) ==> (UF_SEM TOP_OMEGA f /\ ~UF_SEM BOTTOM_OMEGA f)``,
   REWRITE_TAC[TOP_OMEGA_def, BOTTOM_OMEGA_def] THEN
   INDUCT_THEN fl_induct ASSUME_TAC THEN
   ASM_SIMP_TAC (arith_ss++res_quanTools.resq_SS) [F_CLOCK_SERE_FREE_def, UF_SEM_def, COMPLEMENT_def, F_CLOCK_FREE_def, F_SERE_FREE_def,
     B_SEM_def, ELEM_INFINITE, LENGTH_def, GT, xnum_distinct, o_DEF, COMPLEMENT_LETTER_def, RESTN_INFINITE, IN_LESSX]);


val UF_SEM___DIRECT___F_F =
 store_thm
  ("UF_SEM___DIRECT___F_F",
   ``!v f. (IS_PROPER_PATH v) ==> (UF_SEM v (F_F f) = ?k. k IN LESS (LENGTH v) /\ UF_SEM (RESTN v k) f)``,

   SIMP_TAC (std_ss++resq_SS) [F_F_def, UF_SEM_def] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      METIS_TAC[],

      FULL_SIMP_TAC arith_ss [IN_LESSX_REWRITE] THEN
      SIMP_TAC std_ss [ELEM_RESTN, IN_LESS] THEN
      Cases_on `ELEM v k = BOTTOM` THENL [
         SUBGOAL_TAC `?j. (ELEM v j = BOTTOM) /\ !j'. j' < j ==> ~(ELEM v j' = BOTTOM)` THEN1 (
           ASSUME_TAC (EXISTS_LEAST_CONV ``?j. ELEM v j = BOTTOM``) THEN
           PROVE_TAC[]
         ) THEN
         EXISTS_TAC ``j:num`` THEN
         `~(k < j)` by PROVE_TAC[] THEN
         `j < LENGTH v` by (Cases_on `v` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS]) THEN
         `IS_INFINITE_PROPER_PATH v` by PROVE_TAC[PROPER_PATH___IS_INFINITE_TOP_BOTTOM] THEN
         `(RESTN v j = BOTTOM_OMEGA)` by PROVE_TAC[INFINITE_PROPER_PATH___RESTN_TOP_BOTTOM_OMEGA, LESS_EQ_REFL] THEN
         `(RESTN v k = BOTTOM_OMEGA)` by PROVE_TAC[INFINITE_PROPER_PATH___RESTN_TOP_BOTTOM_OMEGA, LESS_EQ_REFL] THEN
         ASM_REWRITE_TAC[] THEN
         REPEAT STRIP_TAC THENL [
            PROVE_TAC[],

            DISJ2_TAC THEN
            Cases_on `ELEM v j'` THEN REWRITE_TAC[B_SEM_def] THEN
            PROVE_TAC[]
         ],


         EXISTS_TAC ``k:num`` THEN
         ASM_REWRITE_TAC[] THEN
         REPEAT STRIP_TAC THEN
         DISJ2_TAC THEN
         Cases_on `ELEM v j` THEN REWRITE_TAC[B_SEM_def] THEN
         `j < LENGTH v` by (Cases_on `v` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS]) THEN
         `IS_INFINITE_PROPER_PATH v` by PROVE_TAC[PROPER_PATH___IS_INFINITE_TOP_BOTTOM] THEN
         `k >= j` by DECIDE_TAC THEN
         PROVE_TAC[INFINITE_PROPER_PATH___TOP_BOTTOM_FOLLOWING]
      ]
   ]);


val UF_SEM___DIRECT___F_G =
 store_thm
  ("UF_SEM___DIRECT___F_G",
   ``!v f. (IS_PROPER_PATH v) ==> (UF_SEM v (F_G f) = !k. k IN LESS (LENGTH v) ==> UF_SEM (RESTN v k) f)``,

   REWRITE_TAC[F_G_def, UF_SEM_def] THEN
   REPEAT STRIP_TAC THEN
   `IS_PROPER_PATH (COMPLEMENT v)` by PROVE_TAC[IS_PROPER_PATH___COMPLEMENT] THEN
   ASM_SIMP_TAC std_ss [LENGTH_COMPLEMENT, UF_SEM___DIRECT___F_F, IN_LESSX_REWRITE,
     UF_SEM_def, IMP_DISJ_THM] THEN
   METIS_TAC [RESTN_COMPLEMENT, COMPLEMENT_COMPLEMENT]);



val PSL_WEAK_UNTIL___ALTERNATIVE_DEF =
 store_thm
  ("PSL_WEAK_UNTIL___ALTERNATIVE_DEF",
   ``!v f1 f2. IS_PROPER_PATH v ==>
      (UF_SEM v (F_WEAK_UNTIL(f1,f2)) =
       UF_SEM v (F_NOT (F_UNTIL(F_NOT f2, F_AND(F_NOT f1, F_NOT f2)))))``,


   SIMP_TAC (std_ss++resq_SS) [F_WEAK_UNTIL_def, F_W_def, UF_SEM_F_OR, IN_LESS,
      UF_SEM___DIRECT___F_G, IN_LESSX_REWRITE, UF_SEM_def, LENGTH_COMPLEMENT] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL [
      Cases_on `k' < LENGTH v` THEN ASM_SIMP_TAC std_ss [] THEN
      ASM_SIMP_TAC std_ss [RESTN_COMPLEMENT, COMPLEMENT_COMPLEMENT] THEN
      Cases_on `UF_SEM (RESTN v k') f1` THEN ASM_REWRITE_TAC[] THEN
      `~(k' < k)` by PROVE_TAC[] THEN
      Cases_on `k = k'` THEN1 PROVE_TAC[] THEN
      `k < k'` by DECIDE_TAC THEN
      Cases_on `UF_SEM (RESTN v k') f2` THEN ASM_SIMP_TAC std_ss [] THEN
      EXISTS_TAC ``k:num`` THEN
      ASM_SIMP_TAC std_ss [RESTN_COMPLEMENT, COMPLEMENT_COMPLEMENT],

      Cases_on `k < LENGTH v` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC std_ss [RESTN_COMPLEMENT, COMPLEMENT_COMPLEMENT],

      Cases_on `!k. k < LENGTH v ==> UF_SEM (RESTN v k) f1` THEN ASM_SIMP_TAC std_ss [] THEN
      FULL_SIMP_TAC std_ss [] THEN
      SUBGOAL_TAC `?k. (~UF_SEM (RESTN v k) f1 /\ k < LENGTH v) /\
         !k'. k' < k ==> ~(~UF_SEM (RESTN v k') f1 /\ k' < LENGTH v)` THEN1 (

         ASSUME_TAC (EXISTS_LEAST_CONV ``?k. ~(UF_SEM (RESTN v k) f1) /\ (k < LENGTH v)``) THEN
         RES_TAC THEN
         EXISTS_TAC ``k':num`` THEN
         ASM_REWRITE_TAC[]
      ) THEN
      `!k'':num. k'' < k' ==> k'' < LENGTH v` by (Cases_on `v` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS]) THEN
      FULL_SIMP_TAC std_ss [] THEN
      Cases_on `UF_SEM (RESTN v k') f2` THEN1 METIS_TAC[] THEN
      `?j. j < k' /\ UF_SEM (RESTN v j) f2` by METIS_TAC[RESTN_COMPLEMENT, COMPLEMENT_COMPLEMENT] THEN
      EXISTS_TAC ``j:num`` THEN
      ASM_SIMP_TAC arith_ss []
   ]);



val US_SEM___S_CLOCK_FREE___OMEGA_BOTTOM =
 store_thm
  ("US_SEM___S_CLOCK_FREE___OMEGA_BOTTOM",
   ``!r l ls. (S_CLOCK_FREE r /\ IS_LIST_WITH_REPLACEMENTS ls l BOTTOM) ==> (
      (US_SEM ls r ==> US_SEM l r))``,

   REPEAT STRIP_TAC THEN
   Tactical.REVERSE (SUBGOAL_THEN ``l:'a letter list = ls`` ASSUME_TAC) THEN1 (
      ASM_REWRITE_TAC[]
   ) THEN
   `BOTTOM_FREE ls` by PROVE_TAC[Lemma5] THEN
   FULL_SIMP_TAC std_ss [IS_LIST_WITH_REPLACEMENTS_def, LIST_EQ_REWRITE] THEN
   PROVE_TAC[BOTTOM_FREE_EL]
  );


val US_SEM___S_CLOCK_FREE___OMEGA_TOP =
 store_thm
  ("US_SEM___S_CLOCK_FREE___OMEGA_TOP",
   ``!r l lw. (S_CLOCK_FREE r /\ IS_LIST_WITH_REPLACEMENTS lw l TOP) ==> (
      (US_SEM l r ==> US_SEM lw r))``,

   INDUCT_THEN sere_induct ASSUME_TAC THENL [ (* 8 subgoals *)
      SIMP_TAC std_ss [IS_LIST_WITH_REPLACEMENTS_def, S_CLOCK_FREE_def, US_SEM_def] THEN
      REPEAT STRIP_TAC THEN
      `0 < LENGTH lw` by DECIDE_TAC THEN
      `(EL 0 lw = EL 0 l) \/ (EL 0 lw = TOP)` by PROVE_TAC[] THENL [
         FULL_SIMP_TAC std_ss [ELEM_EL],
         ASM_SIMP_TAC std_ss [ELEM_EL, B_SEM_def]
      ],


      SIMP_TAC std_ss [S_CLOCK_FREE_def, US_SEM_def] THEN
      REPEAT STRIP_TAC THEN
      `?vw1. FIRSTN (LENGTH v1) lw = vw1` by PROVE_TAC[] THEN
      `?vw2. LASTN (LENGTH v2) lw = vw2` by PROVE_TAC[] THEN
      `LENGTH lw = LENGTH v1 + LENGTH v2` by PROVE_TAC[LENGTH_APPEND, IS_LIST_WITH_REPLACEMENTS_def] THEN
      `lw = vw1 <> vw2` by PROVE_TAC[APPEND_FIRSTN_LASTN, ADD_COMM] THEN
      EXISTS_TAC ``vw1:'a letter list`` THEN
      EXISTS_TAC ``vw2:'a letter list`` THEN
      ASM_REWRITE_TAC[] THEN
      `LENGTH v1 <= LENGTH lw` by DECIDE_TAC THEN
      `LENGTH v1 = LENGTH vw1` by PROVE_TAC[LENGTH_FIRSTN] THEN
      PROVE_TAC[IS_LIST_WITH_REPLACEMENTS___APPEND],


      SIMP_TAC list_ss [S_CLOCK_FREE_def, US_SEM_def] THEN
      REPEAT STRIP_TAC THEN
      `?vw1. vw1 = FIRSTN (LENGTH v1) lw` by PROVE_TAC[] THEN
      `?vw2. vw2 = LASTN (LENGTH v2) lw` by PROVE_TAC[] THEN
      `?lw'. lw' = EL (LENGTH v1) lw` by PROVE_TAC[] THEN
      EXISTS_TAC ``vw1:'a letter list`` THEN
      EXISTS_TAC ``vw2:'a letter list`` THEN
      EXISTS_TAC ``lw':'a letter`` THEN
      `?vw1'. vw1' = FIRSTN (SUC (LENGTH v1)) lw` by PROVE_TAC[] THEN
      `?v1'. v1' = v1 <> [l']` by PROVE_TAC[] THEN
      `LENGTH l = SUC (LENGTH v1) + LENGTH v2` by ASM_SIMP_TAC list_ss [] THEN
      `LENGTH lw = SUC (LENGTH v1) + LENGTH v2` by PROVE_TAC[IS_LIST_WITH_REPLACEMENTS_def] THEN
      SUBGOAL_THEN ``(vw1':'a letter list) = vw1 <> [lw']`` ASSUME_TAC THEN1(
         ASM_SIMP_TAC list_ss [FIRSTN_SEG, SEG_SPLIT, SUC_ONE_ADD] THEN
         `(1:num > 0:num) /\ (LENGTH v1 < LENGTH lw)` by DECIDE_TAC THEN
         `SEG 1 (LENGTH v1) lw = [HD (SEG 1 (LENGTH v1) lw)]` by PROVE_TAC[SEG_SING_LIST] THEN
         ONCE_ASM_REWRITE_TAC[] THEN
         ASM_SIMP_TAC list_ss [GSYM EL_SEG]
      ) THEN

      `vw1' <> vw2 = lw` by PROVE_TAC[APPEND_FIRSTN_LASTN, ADD_COMM] THEN
      STRIP_TAC THENL [
         PROVE_TAC[],

         `LENGTH v1' = SUC (LENGTH v1)` by ASM_SIMP_TAC list_ss [] THEN
         `LENGTH v1' <= LENGTH lw` by DECIDE_TAC THEN
         `LENGTH v1' = LENGTH vw1'` by ASM_SIMP_TAC list_ss [LENGTH_FIRSTN] THEN
         `l = v1' <> v2` by PROVE_TAC[] THEN

         `(IS_LIST_WITH_REPLACEMENTS vw1' v1' TOP /\ IS_LIST_WITH_REPLACEMENTS vw2 v2 TOP)` by
            PROVE_TAC[IS_LIST_WITH_REPLACEMENTS___APPEND] THEN
         REPEAT STRIP_TAC THENL [
            PROVE_TAC[],

            SUBGOAL_TAC `IS_LIST_WITH_REPLACEMENTS (lw'::vw2) (l'::v2) TOP` THEN1 (
               ASM_SIMP_TAC list_ss [IS_LIST_WITH_REPLACEMENTS___SUC] THEN
               `l' = EL(LENGTH v1) l` by
                  ASM_SIMP_TAC arith_ss [EL_APPEND2, GSYM APPEND_ASSOC, EL, HD, APPEND] THEN
               `LENGTH v1 < LENGTH lw` by DECIDE_TAC THEN
               PROVE_TAC [IS_LIST_WITH_REPLACEMENTS_def]
            ) THEN
            PROVE_TAC[]
         ]
      ],


      SIMP_TAC std_ss [S_CLOCK_FREE_def, US_SEM_def] THEN PROVE_TAC[],
      SIMP_TAC std_ss [S_CLOCK_FREE_def, US_SEM_def] THEN PROVE_TAC[],
      SIMP_TAC list_ss [IS_LIST_WITH_REPLACEMENTS_def, LENGTH_NIL, S_CLOCK_FREE_def, US_SEM_def],

      SIMP_TAC list_ss [S_CLOCK_FREE_def, US_SEM_def] THEN
      REPEAT STRIP_TAC THEN
      NTAC 3 (fn (asm, g) => UNDISCH_TAC (hd asm) (asm, g)) THEN
      SPEC_TAC (``l:'a letter list``, ``l:'a letter list``) THEN
      SPEC_TAC (``lw:'a letter list``, ``lw:'a letter list``) THEN
      Induct_on `vlist` THENL [
         SIMP_TAC list_ss [] THEN
         REPEAT STRIP_TAC THEN
         EXISTS_TAC ``[]:'a letter list list`` THEN
         FULL_SIMP_TAC list_ss [CONCAT_def, IS_LIST_WITH_REPLACEMENTS_def, LENGTH_NIL],

         SIMP_TAC list_ss [CONCAT_def] THEN
         REPEAT STRIP_TAC THEN
         `?hw. FIRSTN  (LENGTH h) lw = hw` by PROVE_TAC[] THEN
         `?lw'. BUTFIRSTN (LENGTH h) lw = lw'` by PROVE_TAC[] THEN
         `LENGTH lw = (LENGTH h + LENGTH (CONCAT vlist))` by FULL_SIMP_TAC list_ss [IS_LIST_WITH_REPLACEMENTS_def] THEN
         `LENGTH h <= LENGTH lw` by DECIDE_TAC THEN
         `hw <> lw' = lw` by PROVE_TAC[APPEND_FIRSTN_BUTFIRSTN] THEN
         `LENGTH hw = LENGTH h` by PROVE_TAC [LENGTH_FIRSTN] THEN
         `IS_LIST_WITH_REPLACEMENTS lw' (CONCAT vlist) TOP /\
          IS_LIST_WITH_REPLACEMENTS hw h TOP` by
            PROVE_TAC [IS_LIST_WITH_REPLACEMENTS___APPEND] THEN
         `?vlist'. (lw' = CONCAT vlist') /\ ALL_EL (\v'. US_SEM v' r) vlist'` by
            PROVE_TAC[] THEN
         EXISTS_TAC ``(hw::vlist'):'a letter list list`` THEN
         ASM_SIMP_TAC list_ss [] THEN
         PROVE_TAC[CONCAT_def]
      ],

      REWRITE_TAC[S_CLOCK_FREE_def]
   ]);


val UF_SEM___F_CLOCK_FREE___OMEGA_TOP_BOTTOM =
 store_thm
  ("UF_SEM___F_CLOCK_FREE___OMEGA_TOP_BOTTOM",
   ``!f v vw vs.
      ((F_CLOCK_FREE f /\ IS_PATH_WITH_REPLACEMENTS vw v TOP /\ UF_SEM v f) ==> UF_SEM vw f) /\
      ((F_CLOCK_FREE f /\ IS_PATH_WITH_REPLACEMENTS vs v BOTTOM /\ UF_SEM vs f) ==> UF_SEM v f)``,

   INDUCT_THEN fl_induct ASSUME_TAC THENL [

      ASM_SIMP_TAC list_ss [IS_PATH_WITH_REPLACEMENTS_def, F_CLOCK_FREE_def, UF_SEM_def] THEN
      REPEAT STRIP_TAC THENL [
         Cases_on `(ELEM vw 0) = (ELEM v 0)` THEN ASM_REWRITE_TAC[] THEN
         `ELEM vw 0 = TOP` by PROVE_TAC[GT_LS] THEN
         ASM_SIMP_TAC std_ss [B_SEM_def],

               PROVE_TAC[],

         Cases_on `(ELEM v 0) = (ELEM vs 0)` THEN ASM_REWRITE_TAC[] THEN
         `ELEM vs 0 = BOTTOM` by PROVE_TAC[GT_LS] THEN
         PROVE_TAC [B_SEM_def]
      ],

      ASM_SIMP_TAC std_ss [IS_PATH_WITH_REPLACEMENTS_def, F_CLOCK_FREE_def, UF_SEM_def] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      Cases_on `LENGTH v = XNUM 0` THEN ASM_REWRITE_TAC[] THEN
      `0 < LENGTH v` by (Cases_on `v` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS, xnum_11]) THENL [
         Cases_on `(ELEM vw 0) = (ELEM v 0)` THEN ASM_REWRITE_TAC[] THEN
         `ELEM vw 0 = TOP` by PROVE_TAC[] THEN
         ASM_SIMP_TAC std_ss [B_SEM_def],

         PROVE_TAC[],

         Cases_on `(ELEM v 0) = (ELEM vs 0)` THEN ASM_REWRITE_TAC[] THEN
         `ELEM vs 0 = BOTTOM` by PROVE_TAC[] THEN
         PROVE_TAC [B_SEM_def]
      ],


      SIMP_TAC std_ss [F_CLOCK_FREE_def, UF_SEM_def] THEN
      ONCE_REWRITE_TAC[IS_PATH_WITH_REPLACEMENTS___COMPLEMENT] THEN
      SIMP_TAC std_ss [COMPLEMENT_LETTER_def] THEN
      PROVE_TAC[],


      SIMP_TAC std_ss [F_CLOCK_FREE_def, UF_SEM_def] THEN PROVE_TAC[],


      ASM_SIMP_TAC (list_ss++resq_SS) [IN_LESSX_REWRITE, F_CLOCK_FREE_def, UF_SEM_def] THEN
      REPEAT STRIP_TAC THENL [
         EXISTS_TAC ``j:num`` THEN
         `?l. (SEL v (0,j)) = l` by PROVE_TAC[] THEN
         `?lw. (SEL vw (0,j)) = lw` by PROVE_TAC[] THEN
         `LENGTH vw = LENGTH v` by PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def] THEN
         ASM_REWRITE_TAC[] THEN
         `0 < LENGTH v` by (Cases_on `v` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS]) THEN
         `IS_LIST_WITH_REPLACEMENTS lw l TOP` by PROVE_TAC[SEL_IS_PATH_WITH_REPLACEMENTS] THEN
         PROVE_TAC[US_SEM___S_CLOCK_FREE___OMEGA_TOP],

         EXISTS_TAC ``j:num`` THEN
         `?l. (SEL v (0,j)) = l` by PROVE_TAC[] THEN
         `?ls. (SEL vs (0,j)) = ls` by PROVE_TAC[] THEN
         `LENGTH v = LENGTH vs` by PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def] THEN
         ASM_REWRITE_TAC[] THEN
         `0 < LENGTH vs` by (Cases_on `vs` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS]) THEN
         `IS_LIST_WITH_REPLACEMENTS ls l BOTTOM` by PROVE_TAC[SEL_IS_PATH_WITH_REPLACEMENTS] THEN
         PROVE_TAC[US_SEM___S_CLOCK_FREE___OMEGA_BOTTOM]
      ],


      ASM_SIMP_TAC (list_ss++resq_SS) [IN_LESSX_REWRITE, LENGTH_CAT, TOP_OMEGA_def, F_CLOCK_FREE_def, UF_SEM_def, LS] THEN
      REWRITE_TAC [GSYM TOP_OMEGA_def] THEN
      REPEAT STRIP_TAC THENL [
         `LENGTH v = LENGTH vw` by PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def] THEN
         `?k. US_SEM (SEL (CAT (SEL v (0,j),TOP_OMEGA)) (0,k)) s` by PROVE_TAC[] THEN

         `?vw'. CAT (SEL vw (0,j),TOP_OMEGA) = vw'` by PROVE_TAC[] THEN
         `?v'. CAT (SEL v (0,j),TOP_OMEGA) = v'` by PROVE_TAC[] THEN
         `IS_PATH_WITH_REPLACEMENTS vw' v' TOP` by PROVE_TAC[IS_PATH_WITH_REPLACEMENTS___CAT_SEL] THEN

         EXISTS_TAC ``k:num`` THEN
         `?l. (SEL v' (0,k)) = l` by PROVE_TAC[] THEN
         `?lw. (SEL vw' (0,k)) = lw` by PROVE_TAC[] THEN
         `0 < LENGTH v` by (Cases_on `v` THEN Cases_on `vw` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS]) THEN
         `LENGTH vw' = INFINITY` by PROVE_TAC[LENGTH_CAT, TOP_OMEGA_def] THEN
         `IS_LIST_WITH_REPLACEMENTS lw l TOP` by METIS_TAC[SEL_IS_PATH_WITH_REPLACEMENTS, LS] THEN
         PROVE_TAC[US_SEM___S_CLOCK_FREE___OMEGA_TOP],


         `LENGTH vs = LENGTH v` by PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def] THEN
         `?k. US_SEM (SEL (CAT (SEL vs (0,j),TOP_OMEGA)) (0,k)) s` by PROVE_TAC[] THEN

         `?vs'. CAT (SEL vs (0,j),TOP_OMEGA) = vs'` by PROVE_TAC[] THEN
         `?v'. CAT (SEL v (0,j),TOP_OMEGA) = v'` by PROVE_TAC[] THEN
         `IS_PATH_WITH_REPLACEMENTS vs' v' BOTTOM` by PROVE_TAC[IS_PATH_WITH_REPLACEMENTS___CAT_SEL] THEN

         EXISTS_TAC ``k:num`` THEN
         `?l. (SEL v' (0,k)) = l` by PROVE_TAC[] THEN
         `?ls. (SEL vs' (0,k)) = ls` by PROVE_TAC[] THEN
         `0 < LENGTH v` by (Cases_on `v` THEN Cases_on `vs` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS]) THEN
         `LENGTH vs' = INFINITY` by PROVE_TAC[LENGTH_CAT, TOP_OMEGA_def] THEN
         `IS_LIST_WITH_REPLACEMENTS ls l BOTTOM` by METIS_TAC[SEL_IS_PATH_WITH_REPLACEMENTS, LS] THEN
         PROVE_TAC[US_SEM___S_CLOCK_FREE___OMEGA_BOTTOM]
      ],


      SIMP_TAC std_ss [F_CLOCK_FREE_def, UF_SEM_def] THEN
      REPEAT STRIP_TAC THENL [
        PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def],

        `(LENGTH vw = LENGTH v)` by PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def] THEN
        `1 <= LENGTH v` by (Cases_on `v` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS, LE_num_xnum_def, GT]) THEN
        METIS_TAC[IS_PATH_WITH_REPLACEMENTS___RESTN],

        PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def],

        `(LENGTH vs = LENGTH v)` by PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def] THEN
        `1 <= LENGTH vs` by (Cases_on `v` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS, LE_num_xnum_def, GT]) THEN
        METIS_TAC[IS_PATH_WITH_REPLACEMENTS___RESTN]
      ],


      SIMP_TAC (list_ss++resq_SS) [IN_LESSX_REWRITE, F_CLOCK_FREE_def, UF_SEM_def, IN_LESS] THEN
      REPEAT STRIP_TAC THENL [

        EXISTS_TAC ``k:num`` THEN
        `(LENGTH vw = LENGTH v)` by PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def] THEN
        ASM_REWRITE_TAC [] THEN
        `k <= LENGTH v` by (Cases_on `v` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LE_num_xnum_def, LS]) THEN
        REPEAT STRIP_TAC THENL [
          PROVE_TAC[IS_PATH_WITH_REPLACEMENTS___RESTN],

          `j <= LENGTH v` by (Cases_on `v` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS, LE_num_xnum_def]) THEN
          PROVE_TAC[IS_PATH_WITH_REPLACEMENTS___RESTN]
        ],


        EXISTS_TAC ``k:num`` THEN
        `(LENGTH v = LENGTH vs)` by PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def] THEN
        `k <= LENGTH vs` by (Cases_on `vs` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS, LE_num_xnum_def]) THEN
        ASM_REWRITE_TAC [] THEN
        REPEAT STRIP_TAC THENL [
          PROVE_TAC[IS_PATH_WITH_REPLACEMENTS___RESTN],

          `j <= LENGTH vs` by (Cases_on `vs` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS, LE_num_xnum_def]) THEN
          PROVE_TAC[IS_PATH_WITH_REPLACEMENTS___RESTN]
        ]
      ],



      SIMP_TAC (list_ss++resq_SS) [IN_LESSX_REWRITE, F_CLOCK_FREE_def, UF_SEM_def, IN_LESS] THEN
      REPEAT STRIP_TAC THENL [
        PROVE_TAC[],

        DISJ2_TAC THEN
        EXISTS_TAC ``j:num`` THEN
        `(LENGTH vw = LENGTH v)` by PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def] THEN
        REPEAT STRIP_TAC THENL [
          ASM_REWRITE_TAC[],

          `(ELEM vw j = ELEM v j) \/ (ELEM vw j = TOP)` by
            PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def] THEN
          ASM_REWRITE_TAC [B_SEM_def],

          Cases_on `j = 0` THEN FULL_SIMP_TAC std_ss [] THEN
          `j - 1 < LENGTH vw` by (Cases_on `vw` THEN Cases_on `v` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS]) THEN
          METIS_TAC [IS_PATH_WITH_REPLACEMENTS___CAT_SEL]
        ],

        PROVE_TAC[],

        DISJ2_TAC THEN
        EXISTS_TAC ``j:num`` THEN
        `(LENGTH v = LENGTH vs)` by PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def] THEN
        REPEAT STRIP_TAC THENL [
          ASM_REWRITE_TAC[],

          `(ELEM v j = ELEM vs j) \/ (ELEM vs j = BOTTOM)` by
            PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def] THEN
          FULL_SIMP_TAC std_ss [B_SEM_def],

          Cases_on `j = 0` THEN FULL_SIMP_TAC std_ss [] THEN
          `j - 1 < LENGTH vs` by (Cases_on `vs` THEN Cases_on `v` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS]) THEN
          METIS_TAC [IS_PATH_WITH_REPLACEMENTS___CAT_SEL]
        ]
      ],


      ASM_REWRITE_TAC[F_CLOCK_FREE_def],




      SIMP_TAC (list_ss++resq_SS) [IN_LESSX_REWRITE, F_CLOCK_FREE_def, UF_SEM_def, IN_LESS] THEN
      REPEAT STRIP_TAC THENL [
        `(LENGTH vw = LENGTH v)` by PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def] THEN
        `IS_PATH_WITH_REPLACEMENTS (COMPLEMENT vw) (COMPLEMENT v) BOTTOM` by
            PROVE_TAC[IS_PATH_WITH_REPLACEMENTS___COMPLEMENT, COMPLEMENT_LETTER_def] THEN
        `?l. (SEL (COMPLEMENT v) (0, j)) = l` by PROVE_TAC[] THEN
        `?ls. (SEL (COMPLEMENT vw) (0, j)) = ls` by PROVE_TAC[] THEN
        `0 < LENGTH v` by (Cases_on `v` THEN FULL_SIMP_TAC arith_ss [LS, LENGTH_def]) THEN
        `IS_LIST_WITH_REPLACEMENTS ls l BOTTOM` by PROVE_TAC[SEL_IS_PATH_WITH_REPLACEMENTS, LENGTH_COMPLEMENT] THEN
        `US_SEM l p_1` by PROVE_TAC[US_SEM___S_CLOCK_FREE___OMEGA_BOTTOM] THEN
        `UF_SEM (RESTN v j) f` by PROVE_TAC[] THEN
        `j <= LENGTH v` by (Cases_on `v` THEN FULL_SIMP_TAC arith_ss [LS, LENGTH_def, LE_num_xnum_def]) THEN
        PROVE_TAC[IS_PATH_WITH_REPLACEMENTS___RESTN],


        `(LENGTH vs = LENGTH v)` by PROVE_TAC[IS_PATH_WITH_REPLACEMENTS_def] THEN
        `IS_PATH_WITH_REPLACEMENTS (COMPLEMENT vs) (COMPLEMENT v) TOP` by
            PROVE_TAC[IS_PATH_WITH_REPLACEMENTS___COMPLEMENT, COMPLEMENT_LETTER_def] THEN
        `?l. (SEL (COMPLEMENT v) (0, j)) = l` by PROVE_TAC[] THEN
        `?lw. (SEL (COMPLEMENT vs) (0, j)) = lw` by PROVE_TAC[] THEN
        `0 < LENGTH v` by (Cases_on `v` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS]) THEN
        `IS_LIST_WITH_REPLACEMENTS lw l TOP` by PROVE_TAC[SEL_IS_PATH_WITH_REPLACEMENTS, LENGTH_COMPLEMENT] THEN
        `US_SEM lw p_1` by PROVE_TAC[US_SEM___S_CLOCK_FREE___OMEGA_TOP] THEN
        `UF_SEM (RESTN vs j) f` by PROVE_TAC[] THEN
        `j <= LENGTH v` by (Cases_on `v` THEN FULL_SIMP_TAC arith_ss [LENGTH_def, LS, LE_num_xnum_def]) THEN
        PROVE_TAC[IS_PATH_WITH_REPLACEMENTS___RESTN]
      ]
   ]);



val PSL_WITH_SERES___STRICTLY_MORE_EXPRESSIVE_THAN___LTL___EXAMPLE =
 store_thm
  ("PSL_WITH_SERES___STRICTLY_MORE_EXPRESSIVE_THAN___LTL___EXAMPLE",
   ``!v p q.  (!n:num. (n < LENGTH v) ==> (?s. (ELEM v n) = STATE s)) ==>

       ((UF_SEM v (F_AND(F_SUFFIX_IMP (S_REPEAT(S_CAT(S_BOOL p, S_BOOL q)),
                 F_NEXT(F_AND(F_STRONG_BOOL p, F_NEXT (F_STRONG_BOOL q)))),

               F_AND(F_STRONG_BOOL p, F_NEXT (F_STRONG_BOOL q))))) =
       (!n:num. (LENGTH v > 2*n+1 /\ US_SEM (SEL v (0, 2*n+1)) (S_REPEAT
            (S_CAT (S_BOOL p,S_BOOL q)))) /\
            B_SEM (ELEM v (n+n)) p /\ B_SEM (ELEM v (n+n+1)) q))``,

   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN ``COMPLEMENT v = v`` ASSUME_TAC THEN1 (
      Cases_on `v` THEN
      REWRITE_TAC [COMPLEMENT_def, path_11] THENL [
         Induct_on `l` THENL [
            REWRITE_TAC [MAP],

            FULL_SIMP_TAC list_ss [LENGTH_def, LS] THEN
            REPEAT STRIP_TAC THENL [
               `ELEM (FINITE (h::l)) 0 = h` by SIMP_TAC list_ss [ELEM_FINITE] THEN
               `0 < SUC (LENGTH l)` by DECIDE_TAC THEN
               `?s. h = STATE s` by METIS_TAC[] THEN
               ASM_REWRITE_TAC[COMPLEMENT_LETTER_def],

               `!n. ELEM (FINITE l) n = (ELEM (FINITE (h::l)) (SUC n))` by SIMP_TAC list_ss [ELEM_FINITE] THEN
               `!n. n < LENGTH l ==> SUC n < SUC (LENGTH l)` by DECIDE_TAC THEN
               PROVE_TAC[]
            ]
         ],

         FULL_SIMP_TAC list_ss [LENGTH_def, LS, ELEM_INFINITE, FUN_EQ_THM, COMPLEMENT_def, o_DEF, path_11] THEN
         PROVE_TAC[COMPLEMENT_LETTER_def]
      ]
   ) THEN

   EQ_TAC THENL [
      FULL_SIMP_TAC (list_ss++resq_SS) [US_SEM_def, RESTN_RESTN, UF_SEM_def] THEN
      DISCH_TAC THEN
      FULL_SIMP_TAC std_ss [] THEN
      Induct_on `n` THENL [
         FULL_SIMP_TAC arith_ss [ELEM_RESTN] THEN

         EXISTS_TAC ``[SEL v (0, 1)]:'a letter list list`` THEN
         SIMP_TAC arith_ss [CONCAT_def, APPEND_NIL, ALL_EL] THEN
         EXISTS_TAC ``[(ELEM v 0)]:'a letter list`` THEN
         EXISTS_TAC ``[(ELEM v 1)]:'a letter list`` THEN
         `(ELEM [ELEM v 0] 0) = ELEM v 0` by (EVAL_TAC THEN PROVE_TAC[]) THEN
         `(ELEM [ELEM v 1] 0) = ELEM v 1` by (EVAL_TAC THEN PROVE_TAC[]) THEN
         ASM_SIMP_TAC list_ss [SEL_def] THEN
         `(2 = SUC (SUC 0)) /\ (1 = SUC 0)` by DECIDE_TAC THEN
         ONCE_ASM_REWRITE_TAC[] THEN
         SIMP_TAC list_ss [SEL_REC_def, ELEM_def, RESTN_def],



         FULL_SIMP_TAC std_ss [] THEN
         SUBGOAL_THEN ``((2*n + 1) IN LESS (LENGTH (v:'a letter path)))`` ASSUME_TAC THEN1 (
            Cases_on `v` THENL [
               FULL_SIMP_TAC arith_ss [LENGTH_def, IN_LESSX, GT],
               SIMP_TAC std_ss [IN_LESSX, LENGTH_def]
            ]
         ) THEN
         RES_TAC THEN
         FULL_SIMP_TAC arith_ss [ELEM_RESTN] THEN
         REPEAT STRIP_TAC THENL [
            Cases_on `v` THENL [
               SUBGOAL_THEN ``2 * n + 2 < LENGTH (FINITE l:'a letter path)`` ASSUME_TAC THEN1 (
                  `LENGTH (RESTN (FINITE l) (2 * n + 1)) = LENGTH (FINITE l) - (2 * n + 1)` by
                     METIS_TAC[GT_LS, LENGTH_RESTN, IS_FINITE_def] THEN
                  FULL_SIMP_TAC arith_ss [LENGTH_def, SUB_xnum_num_def, GT, LS]
               ) THEN

               `LENGTH (RESTN (FINITE l) (2 * n + 2)) = LENGTH (FINITE l) - (2 * n + 2)` by
                  METIS_TAC[LENGTH_RESTN, IS_FINITE_def] THEN
               FULL_SIMP_TAC arith_ss [LENGTH_def, SUB_xnum_num_def, GT, LS] THEN
               DECIDE_TAC,

               SIMP_TAC std_ss [GT, LENGTH_def]
            ],

            EXISTS_TAC ``(vlist:'a letter list list)<>[SEL v (2*SUC n, 2*SUC n + 1)]`` THEN
            REPEAT STRIP_TAC THENL [
               SIMP_TAC list_ss [CONCAT_APPEND, CONCAT_def] THEN
               `0 <= 2 * n + 1 /\ 2 * n + 1 < 2* (SUC n)+1` by DECIDE_TAC THEN
               `SEL v (0, 2* SUC n + 1) = SEL v (0, 2* n + 1) <> SEL v (2* n + 1 + 1, 2 * (SUC n)+1)` by
                  METIS_TAC[SEL_SPLIT] THEN
               `2 * n + 1 + 1 = 2 * (SUC n)` by DECIDE_TAC THEN
               ASM_REWRITE_TAC[],

               ASM_SIMP_TAC list_ss [] THEN
               EXISTS_TAC ``[(ELEM v (2*SUC n))]:'a letter list`` THEN
               EXISTS_TAC ``[(ELEM v (2*(SUC n) + 1))]:'a letter list`` THEN
               `(ELEM [ELEM v (2*SUC n)] 0) = ELEM v (2*SUC n)` by (EVAL_TAC THEN PROVE_TAC[]) THEN
               `(ELEM [ELEM v (2*SUC n+1)] 0) = ELEM v (2*SUC n+1)` by (EVAL_TAC THEN PROVE_TAC[]) THEN
               ASM_SIMP_TAC list_ss [SEL_def] THEN
               `(2*SUC n = 2*n + 2) /\ (2*SUC n +1 = 2*n + 3)` by DECIDE_TAC THEN
               ASM_REWRITE_TAC[] THEN
               `2 = SUC (SUC 0)` by DECIDE_TAC THEN
               ONCE_ASM_REWRITE_TAC[] THEN
               SIMP_TAC list_ss [SEL_REC_def, SEL_REC_SUC, ELEM_def] THEN
               `2 * n + 3 = SUC (2 * n + 2)` by DECIDE_TAC THEN
               ASM_REWRITE_TAC[RESTN_def]
            ],

            `2*(SUC n) = 2*n+2` by DECIDE_TAC THEN
            ASM_REWRITE_TAC[],

            `2*(SUC n)+1 = 2*n + 3` by DECIDE_TAC THEN
            ASM_REWRITE_TAC[]
         ]
      ],

      SIMP_TAC std_ss [FORALL_AND_THM] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN ``?v'. (v:'a letter path) = INFINITE v'`` STRIP_ASSUME_TAC THEN1 (
         Cases_on `v` THENL [
            FULL_SIMP_TAC arith_ss [LENGTH_def, GT] THEN
            `LENGTH l > 2*(LENGTH l) + 1` by PROVE_TAC[] THEN
            FULL_SIMP_TAC arith_ss [],

            PROVE_TAC[]
         ]
      ) THEN

      FULL_SIMP_TAC (arith_ss++resq_SS) [UF_SEM_def, RESTN_INFINITE, LENGTH_def, GT, IN_LESSX, ELEM_INFINITE,
        US_SEM_def] THEN
      Tactical.REVERSE (STRIP_TAC) THEN1 (
         `(2*0 = 0:num) /\ (2*0 + 1 = 1:num)` by SIMP_TAC arith_ss [] THEN
         METIS_TAC[]
      ) THEN

      GEN_TAC THEN DISCH_TAC THEN
      FULL_SIMP_TAC std_ss [] THEN
      Tactical.REVERSE (SUBGOAL_THEN ``ODD j`` ASSUME_TAC) THEN1 (
         FULL_SIMP_TAC arith_ss [ODD_EXISTS] THEN
         `(j + 1= 2 * (SUC m)) /\ (j + 2 = (2*SUC m) + 1)` by DECIDE_TAC THEN
         PROVE_TAC[]
      ) THEN

      SUBGOAL_THEN ``LENGTH (CONCAT vlist) = 2 * LENGTH (vlist:'a letter list list)`` ASSUME_TAC THEN1 (
         (fn (asm, g) => UNDISCH_TAC (hd asm) (asm, g)) THEN
         WEAKEN_TAC (fn f => true) THEN
         Induct_on `vlist` THENL [
            SIMP_TAC list_ss [CONCAT_def],

            SIMP_TAC list_ss [CONCAT_def] THEN
            REPEAT STRIP_TAC THEN
            RES_TAC THEN
            ASM_SIMP_TAC list_ss []
         ]
      ) THEN

      `LENGTH (SEL (INFINITE v') (0, j)) = 2* (LENGTH vlist)` by PROVE_TAC[] THEN
      FULL_SIMP_TAC list_ss [LENGTH_SEL] THEN

      `?m:num. LENGTH vlist = m` by PROVE_TAC[] THEN
      `(m > 0) /\ (j = (2 * m) - 1)` by DECIDE_TAC THEN
      REWRITE_TAC [ODD_EXISTS] THEN
      EXISTS_TAC ``PRE (m:num)`` THEN
      ASM_SIMP_TAC arith_ss []
   ]);



val IS_TOP_BOTTOM_WELL_BEHAVED_THM =
 store_thm
  ("IS_TOP_BOTTOM_WELL_BEHAVED_THM",
   ``!f. (IS_TOP_BOTTOM_WELL_BEHAVED f /\ F_CLOCK_FREE f) ==>
         ((UF_SEM TOP_OMEGA f) /\ ~(UF_SEM BOTTOM_OMEGA f))``,

     INDUCT_THEN fl_induct ASSUME_TAC THENL [
        SIMP_TAC std_ss [TOP_OMEGA_def, BOTTOM_OMEGA_def, UF_SEM_def, ELEM_INFINITE, B_SEM_def, LENGTH_def, GT],
        SIMP_TAC std_ss [TOP_OMEGA_def, BOTTOM_OMEGA_def, UF_SEM_def, ELEM_INFINITE, B_SEM_def, LENGTH_def, xnum_distinct],
        ASM_SIMP_TAC std_ss [TOP_BOTTOM_OMEGA___COMPLEMENT, IS_TOP_BOTTOM_WELL_BEHAVED_def, UF_SEM_def, F_CLOCK_FREE_def],
        ASM_SIMP_TAC std_ss [IS_TOP_BOTTOM_WELL_BEHAVED_def, UF_SEM_def, F_CLOCK_FREE_def],
        ASM_SIMP_TAC std_ss [IS_TOP_BOTTOM_WELL_BEHAVED_def],
        ASM_SIMP_TAC std_ss [IS_TOP_BOTTOM_WELL_BEHAVED_def],

        FULL_SIMP_TAC std_ss [IS_TOP_BOTTOM_WELL_BEHAVED_def, UF_SEM_def, F_CLOCK_FREE_def, TOP_OMEGA_def, BOTTOM_OMEGA_def,
          LENGTH_def, RESTN_INFINITE, GT],
        FULL_SIMP_TAC (std_ss++resq_SS) [IS_TOP_BOTTOM_WELL_BEHAVED_def, UF_SEM_def, F_CLOCK_FREE_def, TOP_OMEGA_def, BOTTOM_OMEGA_def,
          LENGTH_def, RESTN_INFINITE, GT, IN_LESSX],

        ASM_SIMP_TAC (std_ss++resq_SS) [IS_TOP_BOTTOM_WELL_BEHAVED_def, UF_SEM_def, F_CLOCK_FREE_def, BOTTOM_OMEGA_def, LENGTH_def, IN_LESSX,
          ELEM_INFINITE, B_SEM_def],

        SIMP_TAC std_ss [F_CLOCK_FREE_def],

        SIMP_TAC std_ss [IS_TOP_BOTTOM_WELL_BEHAVED_def]
     ]);





val WEAK_STRONG_UF_SEM___INFINITE_PATHS =
 store_thm
  ("WEAK_STRONG_UF_SEM___INFINITE_PATHS",

   ``!v f. (IS_INFINITE v) ==> ((WEAK_UF_SEM v f = UF_SEM v f) /\
                                (STRONG_UF_SEM v f = UF_SEM v f))``,

   Cases_on `v` THEN
   REWRITE_TAC[IS_INFINITE_def, WEAK_UF_SEM_def, STRONG_UF_SEM_def, PATH_APPEND_def]);



val WEAK_STRONG_UF_SEM___FINITE_PROPER_PATHS =
 store_thm
  ("WEAK_STRONG_UF_SEM___FINITE_PROPER_PATHS",

   ``!f p. (F_CLOCK_FREE f /\ IS_FINITE_PROPER_PATH (FINITE p) /\ IS_TOP_BOTTOM_WELL_BEHAVED f) ==> (
      (STRONG_UF_SEM (FINITE p) f ==> UF_SEM (FINITE p) f) /\
      (UF_SEM (FINITE p) f ==> WEAK_UF_SEM (FINITE p) f))``,


   REWRITE_TAC [WEAK_UF_SEM_def, STRONG_UF_SEM_def, PATH_APPEND_def, TOP_OMEGA_def, BOTTOM_OMEGA_def] THEN
   REWRITE_TAC [GSYM TOP_OMEGA_def, GSYM BOTTOM_OMEGA_def] THEN
   INDUCT_THEN fl_induct ASSUME_TAC THENL [
      SIMP_TAC arith_ss [BOTTOM_OMEGA_def, TOP_OMEGA_def, LENGTH_CAT, F_CLOCK_FREE_def, UF_SEM_def, GT] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      Cases_on `p` THENL [
         SIMP_TAC list_ss [CAT_def, ELEM_INFINITE, B_SEM_def],
         SIMP_TAC list_ss [CAT_def, ELEM_FINITE, ELEM_def, RESTN_def, HEAD_CONS, LENGTH_def, GT]
      ],

      SIMP_TAC arith_ss [BOTTOM_OMEGA_def, TOP_OMEGA_def, LENGTH_CAT, F_CLOCK_FREE_def, UF_SEM_def, xnum_distinct] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      Cases_on `p` THENL [
         SIMP_TAC list_ss [CAT_def, ELEM_INFINITE, B_SEM_def],
         SIMP_TAC list_ss [CAT_def, ELEM_FINITE, ELEM_def, RESTN_def, HEAD_CONS, LENGTH_def, xnum_11]
      ],


      SIMP_TAC std_ss [UF_SEM_def, COMPLEMENT_def, COMPLEMENT_CAT, IS_TOP_BOTTOM_WELL_BEHAVED_def, F_CLOCK_FREE_def,
        TOP_BOTTOM_OMEGA___COMPLEMENT] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      `MAP COMPLEMENT_LETTER p = p` by
         METIS_TAC[IS_FINITE_PROPER_PATH___COMPLEMENT, COMPLEMENT_def, path_11] THEN
      PROVE_TAC[],


      ASM_SIMP_TAC std_ss [IS_TOP_BOTTOM_WELL_BEHAVED_def, F_CLOCK_FREE_def, UF_SEM_def],


      ASM_SIMP_TAC (list_ss++resq_SS) [IN_LESSX_REWRITE, TOP_OMEGA_def, BOTTOM_OMEGA_def, LENGTH_CAT,
        F_CLOCK_FREE_def, UF_SEM_def, LENGTH_def, LS] THEN
      REPEAT STRIP_TAC THENL [
         `?p'. (SEL (CAT (p,INFINITE (\n. BOTTOM))) (0,j)) = p'` by PROVE_TAC[] THEN
         `BOTTOM_FREE p'` by PROVE_TAC[Lemma5] THEN
         SUBGOAL_THEN ``j:num < LENGTH (p:'a letter list)`` ASSUME_TAC THEN1 (
            CCONTR_TAC THEN
            `LENGTH p' = j -0 + 1` by PROVE_TAC[LENGTH_SEL] THEN
            `j < LENGTH p'` by DECIDE_TAC THEN
            `~(EL j p' = BOTTOM)` by PROVE_TAC[BOTTOM_FREE_EL] THEN
            `EL j p' = ELEM (CAT (p,INFINITE (\n. BOTTOM))) j` by PROVE_TAC[EL_SEL0, LESS_EQ_REFL] THEN
            `j >= LENGTH p` by DECIDE_TAC THEN
            FULL_SIMP_TAC arith_ss [ELEM_CAT___GREATER_EQ, ELEM_INFINITE]
         ) THEN
         `j + 0 < LENGTH p` by DECIDE_TAC THEN
         PROVE_TAC[SEL_CAT___LESS],

         `j + 0 < LENGTH p` by DECIDE_TAC THEN
         PROVE_TAC[SEL_CAT___LESS]
      ],


      REPEAT GEN_TAC THEN
      Cases_on `p = []` THEN1 (
         ASM_SIMP_TAC std_ss [IS_TOP_BOTTOM_WELL_BEHAVED_def, CAT_def]
      ) THEN
      ASM_SIMP_TAC (list_ss++resq_SS) [UF_SEM_def, IN_LESSX_REWRITE, TOP_OMEGA_def, BOTTOM_OMEGA_def, LENGTH_CAT, LS, LENGTH_def] THEN
      REPEAT STRIP_TAC THENL [
         `?k. US_SEM (SEL (CAT (SEL (CAT (p,INFINITE (\n. BOTTOM))) (0,j),
            INFINITE (\n. TOP))) (0,k)) s` by PROVE_TAC[] THEN
         `j + 0 < LENGTH p` by DECIDE_TAC THEN
         FULL_SIMP_TAC arith_ss [SEL_CAT___LESS] THEN
         PROVE_TAC[],



         Cases_on `j < LENGTH p` THENL [
            REMAINS_TAC `!k.
               ((SEL (CAT (SEL (FINITE p) (0,j),INFINITE (\n. TOP))) (0,k)) =
               (SEL (CAT (SEL (CAT (p,INFINITE (\n. TOP))) (0,j),INFINITE (\n. TOP))) (0,k)))` THEN1 (
               PROVE_TAC[]
            ) THEN
            SIMP_TAC arith_ss [LIST_EQ_REWRITE, LENGTH_SEL, EL_SEL_THM] THEN
            REPEAT STRIP_TAC THEN
            rename1 `n < k + 1` THEN
            Cases_on `n < j + 1` THENL [
               ASM_SIMP_TAC list_ss [ELEM_CAT___LESS, LENGTH_SEL, EL_SEL_THM, ELEM_FINITE],
               ASM_SIMP_TAC list_ss [ELEM_CAT___GREATER_EQ, LENGTH_SEL]
            ],


            `~(LENGTH p = 0)` by (Cases_on `p` THEN FULL_SIMP_TAC list_ss []) THEN
            `?j'. SUC j' = (LENGTH p)` by PROVE_TAC[num_CASES] THEN
            `j' < LENGTH p` by DECIDE_TAC THEN
            Tactical.REVERSE (SUBGOAL_THEN ``!k.
               ((SEL (CAT (SEL (FINITE p) (0,j'),INFINITE (\n. TOP))) (0,k)) =
               (SEL (CAT (SEL (CAT (p,INFINITE (\n. TOP))) (0,j),INFINITE (\n. TOP))) (0,k)))`` ASSUME_TAC) THEN1 (
               PROVE_TAC[]
            ) THEN
            SIMP_TAC arith_ss [LIST_EQ_REWRITE, LENGTH_SEL, EL_SEL_THM] THEN
            REPEAT STRIP_TAC THEN
            rename1 `n < k + 1` THEN
            Cases_on `n < j' + 1` THENL [
               ASM_SIMP_TAC list_ss [ELEM_CAT___LESS, LENGTH_SEL, EL_SEL_THM, ELEM_FINITE],


               ASM_SIMP_TAC list_ss [ELEM_CAT___GREATER_EQ, LENGTH_SEL, ELEM_INFINITE] THEN
               Cases_on `n >= j + 1` THENL [
                  ASM_SIMP_TAC list_ss [ELEM_CAT___GREATER_EQ, LENGTH_SEL, ELEM_INFINITE],

                  `n >= LENGTH p` by DECIDE_TAC THEN
                  ASM_SIMP_TAC list_ss [ELEM_CAT___LESS, LENGTH_SEL, EL_SEL_THM, ELEM_CAT___GREATER_EQ, ELEM_INFINITE]
               ]
            ]
         ]
      ],


      GEN_TAC THEN
      Cases_on `~(LENGTH p > 1)` THENL [
         ASM_SIMP_TAC list_ss [TOP_OMEGA_def, BOTTOM_OMEGA_def, LENGTH_CAT, CAT_def,
           F_CLOCK_FREE_def, UF_SEM_def, GT, LENGTH_def] THEN
         SUBGOAL_TAC `(RESTN (CAT (p,INFINITE (\n. BOTTOM))) 1) = INFINITE (\n. BOTTOM)` THEN1 (
            Cases_on `p` THEN
            SIMP_TAC list_ss [CAT_def, REST_CONS, GSYM REST_RESTN, REST_def] THEN
            Cases_on `t` THENL [
               SIMP_TAC std_ss [CAT_def],
               FULL_SIMP_TAC list_ss []
            ]
         ) THEN
         ASM_REWRITE_TAC[GSYM BOTTOM_OMEGA_def, IS_TOP_BOTTOM_WELL_BEHAVED_def] THEN
         PROVE_TAC[IS_TOP_BOTTOM_WELL_BEHAVED_THM],

         FULL_SIMP_TAC std_ss [] THEN
         ASM_SIMP_TAC list_ss [TOP_OMEGA_def, BOTTOM_OMEGA_def, LENGTH_CAT, F_CLOCK_FREE_def, UF_SEM_def,
           GT, LENGTH_def] THEN
         Cases_on `p` THEN FULL_SIMP_TAC list_ss [] THEN
         ASM_SIMP_TAC list_ss [GSYM REST_RESTN,
            REST_def, CAT_def, REST_CONS, IS_TOP_BOTTOM_WELL_BEHAVED_def] THEN
         STRIP_TAC THEN
         REWRITE_TAC[GSYM TOP_OMEGA_def, GSYM BOTTOM_OMEGA_def] THEN
         SUBGOAL_THEN ``IS_FINITE_PROPER_PATH (FINITE t)`` ASSUME_TAC THEN1 (
            FULL_SIMP_TAC arith_ss [IS_FINITE_PROPER_PATH_def, PATH_TOP_FREE_def, PATH_BOTTOM_FREE_def, path_11] THEN
            Cases_on `h` THEN FULL_SIMP_TAC std_ss [TOP_FREE_def, BOTTOM_FREE_def]
         ) THEN
         PROVE_TAC[]
      ],


      ASM_SIMP_TAC (list_ss++resq_SS) [TOP_OMEGA_def, BOTTOM_OMEGA_def, LENGTH_CAT, CAT_def,
         IS_TOP_BOTTOM_WELL_BEHAVED_def, UF_SEM_def, LENGTH_def, IN_LESSX, F_CLOCK_FREE_def, IN_LESS] THEN
      REPEAT STRIP_TAC THENL [
         Cases_on `k >= LENGTH p` THENL [
            FULL_SIMP_TAC std_ss [RESTN_CAT___GREATER_EQ, RESTN_INFINITE] THEN
            PROVE_TAC[IS_TOP_BOTTOM_WELL_BEHAVED_THM, BOTTOM_OMEGA_def],

            `k < LENGTH p` by DECIDE_TAC THEN
            EXISTS_TAC ``k:num`` THEN
            REPEAT STRIP_TAC THENL [
               ASM_REWRITE_TAC[],

               `k < LENGTH (FINITE p)` by ASM_SIMP_TAC std_ss [LENGTH_def, LS] THEN
               `IS_FINITE_PROPER_PATH (RESTN (FINITE p) k)` by PROVE_TAC[IS_FINITE_PROPER_PATH___RESTN] THEN
               FULL_SIMP_TAC arith_ss [RESTN_CAT___LESS, RESTN_FINITE] THEN
               PROVE_TAC[BOTTOM_OMEGA_def],

               `j < LENGTH p` by DECIDE_TAC THEN
               `j < LENGTH (FINITE p)` by ASM_SIMP_TAC std_ss [LENGTH_def, LS] THEN
               `IS_FINITE_PROPER_PATH (RESTN (FINITE p) j)` by PROVE_TAC[IS_FINITE_PROPER_PATH___RESTN] THEN
               FULL_SIMP_TAC arith_ss [RESTN_CAT___LESS, RESTN_FINITE] THEN
               PROVE_TAC[BOTTOM_OMEGA_def]
            ]
         ],

         EXISTS_TAC ``k:num`` THEN
         REPEAT STRIP_TAC THENL [
            `k < LENGTH (FINITE p)` by ASM_SIMP_TAC std_ss [LENGTH_def, LS] THEN
            `IS_FINITE_PROPER_PATH (RESTN (FINITE p) k)` by PROVE_TAC[IS_FINITE_PROPER_PATH___RESTN] THEN
            FULL_SIMP_TAC arith_ss [RESTN_CAT___LESS, RESTN_FINITE] THEN
            PROVE_TAC[TOP_OMEGA_def],

            `j < LENGTH p` by DECIDE_TAC THEN
            `j < LENGTH (FINITE p)` by ASM_SIMP_TAC std_ss [LENGTH_def, LS] THEN
            `IS_FINITE_PROPER_PATH (RESTN (FINITE p) j)` by PROVE_TAC[IS_FINITE_PROPER_PATH___RESTN] THEN
            FULL_SIMP_TAC arith_ss [RESTN_CAT___LESS, RESTN_FINITE] THEN
            PROVE_TAC[TOP_OMEGA_def]
         ]
      ],


      ASM_SIMP_TAC (list_ss++resq_SS) [TOP_OMEGA_def, BOTTOM_OMEGA_def, LENGTH_CAT, CAT_def,
         IS_TOP_BOTTOM_WELL_BEHAVED_def, UF_SEM_def, F_CLOCK_FREE_def, IN_LESSX, LENGTH_def] THEN
      REPEAT STRIP_TAC THENL [
         DISJ1_TAC THEN PROVE_TAC[BOTTOM_OMEGA_def],

         DISJ2_TAC THEN
         EXISTS_TAC ``j:num`` THEN
         Tactical.REVERSE (Cases_on `j < LENGTH p`) THEN1 (
            FULL_SIMP_TAC list_ss [ELEM_CAT___GREATER_EQ, ELEM_INFINITE, B_SEM_def]
         ) THEN
         FULL_SIMP_TAC arith_ss [ELEM_CAT___LESS, ELEM_FINITE] THEN
         Cases_on `j` THEN FULL_SIMP_TAC arith_ss [] THEN
         `n + 0 < LENGTH p` by DECIDE_TAC THEN
         FULL_SIMP_TAC std_ss [SEL_CAT___LESS],

         DISJ1_TAC THEN PROVE_TAC[TOP_OMEGA_def],

         DISJ2_TAC THEN
         EXISTS_TAC ``j:num`` THEN
         FULL_SIMP_TAC arith_ss [ELEM_CAT___LESS, ELEM_FINITE] THEN
         Cases_on `j` THEN FULL_SIMP_TAC arith_ss [] THEN
         `n + 0 < LENGTH p` by DECIDE_TAC THEN
         FULL_SIMP_TAC std_ss [SEL_CAT___LESS]
      ],


      ASM_REWRITE_TAC[F_CLOCK_FREE_def],


      ASM_SIMP_TAC (list_ss++resq_SS) [TOP_OMEGA_def, BOTTOM_OMEGA_def, LENGTH_CAT,
         IS_TOP_BOTTOM_WELL_BEHAVED_def, COMPLEMENT_CAT, COMPLEMENT_def, F_CLOCK_FREE_def, UF_SEM_def,
         LENGTH_def, IN_LESSX, o_DEF, COMPLEMENT_LETTER_def, RESTN_INFINITE] THEN
      REPEAT STRIP_TAC THENL [
         `US_SEM (SEL (CAT (MAP COMPLEMENT_LETTER p,INFINITE (\n. TOP))) (0,j')) p_1` by
            ASM_SIMP_TAC list_ss [SEL_CAT___LESS, LENGTH_MAP] THEN
         `UF_SEM ((CAT (RESTN p j',INFINITE (\n. BOTTOM)))) f` by PROVE_TAC[RESTN_CAT___LESS] THEN
         SIMP_TAC std_ss [RESTN_FINITE] THEN
         `IS_FINITE_PROPER_PATH (FINITE (RESTN p j'))` by
            PROVE_TAC[IS_FINITE_PROPER_PATH___RESTN, LS, LENGTH_def, RESTN_FINITE] THEN
         PROVE_TAC[BOTTOM_OMEGA_def],

         `?v'. v' = (SEL (CAT (MAP COMPLEMENT_LETTER p,INFINITE (\n. BOTTOM)))) (0, j')` by PROVE_TAC[] THEN
         Cases_on `~(j' < LENGTH p)` THEN1 (
            `BOTTOM_FREE v'` by PROVE_TAC[Lemma5] THEN
            `j' < LENGTH v'` by ASM_SIMP_TAC arith_ss [LENGTH_SEL] THEN
            `EL j' v' = BOTTOM` by ASM_SIMP_TAC arith_ss [EL_SEL_THM, ELEM_CAT___GREATER_EQ,
               LENGTH_MAP, ELEM_INFINITE] THEN
            PROVE_TAC[BOTTOM_FREE_EL]
         ) THEN

         FULL_SIMP_TAC arith_ss [RESTN_CAT___LESS, SEL_CAT___LESS, LENGTH_MAP, RESTN_FINITE] THEN
         `UF_SEM (FINITE (RESTN p j')) f` by PROVE_TAC[] THEN
         `IS_FINITE_PROPER_PATH (FINITE (RESTN p j'))` by
            PROVE_TAC[IS_FINITE_PROPER_PATH___RESTN, LS, LENGTH_def, RESTN_FINITE] THEN
         PROVE_TAC[TOP_OMEGA_def]
      ]
   ]);




val WEAK_STRONG_UF_SEM_THM =
 store_thm
  ("WEAK_STRONG_UF_SEM_THM",

   ``!f v. (F_CLOCK_FREE f /\ IS_PROPER_PATH v /\ IS_TOP_BOTTOM_WELL_BEHAVED f) ==> (
      (STRONG_UF_SEM v f ==> UF_SEM v f) /\ (UF_SEM v f ==> WEAK_UF_SEM v f))``,

   REWRITE_TAC [IS_PROPER_PATH_def] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THENL [
      FULL_SIMP_TAC std_ss [IS_INFINITE_PROPER_PATH_def] THEN
      PROVE_TAC[WEAK_STRONG_UF_SEM___INFINITE_PATHS, IS_INFINITE_def],

      `?p. v = FINITE p` by PROVE_TAC[IS_FINITE_PROPER_PATH_def] THEN
      PROVE_TAC[WEAK_STRONG_UF_SEM___FINITE_PROPER_PATHS]
   ]);


val UF_EQUIVALENT_def =
 Define `UF_EQUIVALENT f1 f2 =
         !v. ((UF_SEM v f1 = UF_SEM v f2))`


val UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def =
 Define `UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f1 f2 =
         !v. IS_INFINITE_TOP_BOTTOM_FREE_PATH v ==> ((UF_SEM v f1 = UF_SEM v f2))`

val F_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def =
 Define `F_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f1 f2 =
         !v c. IS_INFINITE_TOP_BOTTOM_FREE_PATH v ==> ((F_SEM v c f1 = F_SEM v c f2))`

val F_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE_def =
 Define
   `F_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE f =
      (!v c. IS_INFINITE_TOP_BOTTOM_FREE_PATH v ==> ~(F_SEM v c f))`;

val F_IS_TAUTOLOGY___INFINITE_TOP_BOTTOM_FREE_def =
 Define
   `F_IS_TAUTOLOGY___INFINITE_TOP_BOTTOM_FREE f =
      (!v c. IS_INFINITE_TOP_BOTTOM_FREE_PATH v ==> F_SEM v c f)`;

val UF_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE_def =
 Define
   `UF_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE f =
      (!v. IS_INFINITE_TOP_BOTTOM_FREE_PATH v ==> ~(UF_SEM v f))`;

val UF_IS_TAUTOLOGY___INFINITE_TOP_BOTTOM_FREE_def =
 Define
   `UF_IS_TAUTOLOGY___INFINITE_TOP_BOTTOM_FREE f =
      (!v. IS_INFINITE_TOP_BOTTOM_FREE_PATH v ==> UF_SEM v f)`;



val UF_IS_TAUTOLOGY_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE___DUAL =
 store_thm
  ("UF_IS_TAUTOLOGY_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE___DUAL",

  ``(!f. UF_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE (F_NOT f) = UF_IS_TAUTOLOGY___INFINITE_TOP_BOTTOM_FREE f) /\
    (!f. UF_IS_TAUTOLOGY___INFINITE_TOP_BOTTOM_FREE (F_NOT f) = UF_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE f)``,

    REWRITE_TAC[UF_IS_TAUTOLOGY___INFINITE_TOP_BOTTOM_FREE_def,
                UF_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE_def,
                UF_SEM_def] THEN
    PROVE_TAC[IS_INFINITE_TOP_BOTTOM_FREE_PATH___COMPLEMENT, COMPLEMENT_COMPLEMENT]);



val F_IS_TAUTOLOGY_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE___DUAL =
 store_thm
  ("F_IS_TAUTOLOGY_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE___DUAL",

  ``(!f. F_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE (F_NOT f) = F_IS_TAUTOLOGY___INFINITE_TOP_BOTTOM_FREE f) /\
    (!f. F_IS_TAUTOLOGY___INFINITE_TOP_BOTTOM_FREE (F_NOT f) = F_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE f)``,

    REWRITE_TAC[F_IS_TAUTOLOGY___INFINITE_TOP_BOTTOM_FREE_def,
                F_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE_def,
                F_SEM_def] THEN
    PROVE_TAC[IS_INFINITE_TOP_BOTTOM_FREE_PATH___COMPLEMENT, COMPLEMENT_COMPLEMENT]);


val UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___TO___CONTRADICTION =
 store_thm
  ("UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___TO___CONTRADICTION",

  ``!f1 f2. UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f1 f2 =
            UF_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE (F_NOT(F_IFF(f1, f2)))``,

    SIMP_TAC std_ss [UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def,
                UF_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE_def,
                UF_SEM_def, F_IFF_def, F_IMPLIES_def, F_OR_def,
                COMPLEMENT_COMPLEMENT,
                IS_INFINITE_TOP_BOTTOM_FREE_PATH___COMPLEMENT] THEN
    PROVE_TAC[]);



val F_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___TO___CONTRADICTION =
 store_thm
  ("F_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___TO___CONTRADICTION",

  ``!f1 f2. F_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f1 f2 =
            F_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE (F_NOT(F_IFF(f1, f2)))``,

    SIMP_TAC std_ss [F_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def,
                F_IS_CONTRADICTION___INFINITE_TOP_BOTTOM_FREE_def,
                F_SEM_def, F_IFF_def, F_IMPLIES_def, F_OR_def,
                COMPLEMENT_COMPLEMENT,
                IS_INFINITE_TOP_BOTTOM_FREE_PATH___COMPLEMENT] THEN
    PROVE_TAC[]);


val UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___REFL =
 store_thm
  ("UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___REFL",
   ``!f. UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f f``,
   SIMP_TAC std_ss [UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def]);


val UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___TRANS =
 store_thm
  ("UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___TRANS",
   ``!f1 f2 f3. (UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f1 f2 /\
                 UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f2 f3) ==>
                 UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE f1 f3``,
   SIMP_TAC std_ss [UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def]);


val UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___TRUE =
 store_thm
  ("UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___TRUE",

``!f. (UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE (F_SUFFIX_IMP (S_BOOL B_TRUE, f)) f)``,

SIMP_TAC (std_ss++resq_SS) [UF_SEM_def, IN_LESSX_REWRITE, UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def,
IS_INFINITE_TOP_BOTTOM_FREE_PATH___COMPLEMENT, US_SEM_def] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [IS_INFINITE_TOP_BOTTOM_FREE_PATH_def, LENGTH_def, US_SEM_def,
ELEM_def, LS, GT, LENGTH_SEL, SEL_def, RESTN_def] THEN
REWRITE_TAC[prove (``1 = SUC 0``, DECIDE_TAC), SEL_REC_def, HEAD_def] THEN
SIMP_TAC list_ss [FinitePSLPathTheory.ELEM_def, FinitePSLPathTheory.RESTN_def, FinitePSLPathTheory.HEAD_def, ETA_THM] THEN
`?s. p 0 = STATE s` by METIS_TAC[] THEN
ASM_REWRITE_TAC[B_SEM_def]);



val UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___BOOL =
 store_thm
  ("UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___BOOL",

``!b f. (UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE (F_SUFFIX_IMP ((S_BOOL b), f))
                                                (F_IMPLIES((F_STRONG_BOOL b), f)))``,

SIMP_TAC (std_ss++resq_SS) [UF_SEM_def, IN_LESSX_REWRITE, UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def,
IS_INFINITE_TOP_BOTTOM_FREE_PATH___COMPLEMENT, F_IMPLIES_def, F_OR_def] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [IS_INFINITE_TOP_BOTTOM_FREE_PATH_def, LENGTH_def, US_SEM_def,
ELEM_def, LS, GT, LENGTH_SEL, SEL_def] THEN
REWRITE_TAC[prove (``1 = SUC 0``, DECIDE_TAC), SEL_REC_def, HEAD_def] THEN
SIMP_TAC list_ss [RESTN_INFINITE, HEAD_def, FinitePSLPathTheory.ELEM_def, FinitePSLPathTheory.RESTN_def, FinitePSLPathTheory.HEAD_def, ETA_THM] THEN
METIS_TAC[]);


val UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CAT =
 store_thm
  ("UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CAT",

``!s1 s2 f. (~(US_SEM [] s1) /\ ~(US_SEM [] s2)) ==>
   UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE
    (F_SUFFIX_IMP (S_CAT(s1, s2), f))
    (F_SUFFIX_IMP (s1, (F_NEXT (F_SUFFIX_IMP (s2, f)))))``,

SIMP_TAC (std_ss++resq_SS) [UF_SEM_def, IN_LESSX_REWRITE, UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def,
IS_INFINITE_TOP_BOTTOM_FREE_PATH___COMPLEMENT] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [IS_INFINITE_TOP_BOTTOM_FREE_PATH_def, LENGTH_def, US_SEM_def,
ELEM_def, LS, GT, LENGTH_SEL, SEL_def, RESTN_INFINITE,
COMPLEMENT_def, combinTheory.o_DEF] THEN
SUBGOAL_TAC `!x. COMPLEMENT_LETTER (p x) = p x` THEN1 (
  GEN_TAC THEN
  `?s. p x = STATE s` by METIS_TAC[] THEN
  ASM_REWRITE_TAC[COMPLEMENT_LETTER_def]
) THEN
ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

EQ_TAC THEN REPEAT STRIP_TAC THENL [
  Q_SPEC_NO_ASSUM 2 `j' + 1 + j` THEN
  PROVE_CONDITION_NO_ASSUM 0 THENL [
    ALL_TAC,
    FULL_SIMP_TAC arith_ss []
  ] THEN

  Q_TAC EXISTS_TAC `SEL_REC (j + 1) 0 (INFINITE p)` THEN
  Q_TAC EXISTS_TAC `SEL_REC (j' + 1) 0  (INFINITE (\n. p (n + 1 + j)))` THEN
  ASM_REWRITE_TAC[] THEN

  REPEAT WEAKEN_HD_TAC THEN
  SPEC_TAC (``p:num -> 'a letter``, ``p:num -> 'a letter``) THEN
  Induct_on `j` THENL [
    SIMP_TAC arith_ss [] THEN
    REWRITE_TAC[prove (``(j' + 2 = SUC (SUC j')) /\ ((j' + 1) = SUC j') /\ (1 = SUC 0)``, DECIDE_TAC), SEL_REC_def] THEN
    SIMP_TAC list_ss [REST_INFINITE, HEAD_def] THEN
    GEN_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC arith_ss [path_11, FUN_EQ_THM] THEN
    GEN_TAC THEN
    AP_TERM_TAC THEN
    DECIDE_TAC,


    FULL_SIMP_TAC arith_ss [] THEN
    GEN_TAC THEN
    `(j' + (SUC j + 2)) = SUC (j + (j' + 2))` by DECIDE_TAC THEN
    ASM_REWRITE_TAC[SEL_REC_def, REST_INFINITE] THEN
    WEAKEN_HD_TAC THEN
    `(SUC j + 1) = SUC (j + 1)` by DECIDE_TAC THEN
    ASM_REWRITE_TAC[SEL_REC_def, REST_INFINITE] THEN
    SIMP_TAC list_ss [] THEN
    AP_TERM_TAC THEN
    SIMP_TAC arith_ss [path_11, FUN_EQ_THM] THEN
    GEN_TAC THEN
    AP_TERM_TAC THEN
    DECIDE_TAC
  ],







  `?k. k = PRE (LENGTH v1)` by METIS_TAC[] THEN
  `?k'. k' = PRE (LENGTH v2)` by METIS_TAC[] THEN

  SUBGOAL_TAC `LENGTH v1 > 0` THEN1 (
    Cases_on `v1` THENL [
      PROVE_TAC[],
      SIMP_TAC list_ss []
    ]
  ) THEN

  SUBGOAL_TAC `LENGTH v2 > 0` THEN1 (
    Cases_on `v2` THENL [
      PROVE_TAC[],
      SIMP_TAC list_ss []
    ]
  ) THEN

  FULL_SIMP_TAC std_ss [GSYM RIGHT_FORALL_IMP_THM] THEN
  Q_SPECL_NO_ASSUM 7 [`k`, `k'`] THEN
  `(?l. k + 1 = l) /\ (?l'. k' + 1 = l')` by METIS_TAC[] THEN

  SUBGOAL_TAC `j + 1 = l' + l` THEN1 (
    `j + 1 = LENGTH (v1 <> v2)` by METIS_TAC[LENGTH_SEL_REC] THEN
    ASM_SIMP_TAC std_ss [] THEN
    SIMP_TAC list_ss [] THEN
    DECIDE_TAC
  ) THEN
  FULL_SIMP_TAC std_ss [] THEN

  `LENGTH v1 = l` by DECIDE_TAC THEN
  `LENGTH v2 = l'` by DECIDE_TAC THEN
  FULL_SIMP_TAC std_ss [SEL_REC_SPLIT, APPEND_LENGTH_EQ,LENGTH_SEL_REC] THEN

  NTAC 2 (GSYM_NO_TAC 13) (*v1, v2*) THEN
  FULL_SIMP_TAC std_ss [LENGTH_SEL_REC] THEN
  CLEAN_ASSUMPTIONS_TAC THEN
  PROVE_CONDITION_NO_ASSUM 5 THEN1 ASM_REWRITE_TAC[] THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 (
    SUBGOAL_TAC `INFINITE (\n. p (n + 1 + k)) =
                 RESTN (INFINITE p) l` THEN1 (
      SIMP_TAC std_ss [RESTN_INFINITE, path_11, FUN_EQ_THM] THEN
      GEN_TAC THEN AP_TERM_TAC THEN DECIDE_TAC
    ) THEN
    ASM_SIMP_TAC std_ss [SEL_REC_RESTN]
  ) THEN

  UNDISCH_HD_TAC THEN IMP_TO_EQ_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC std_ss [path_11, FUN_EQ_THM] THEN
  GEN_TAC THEN AP_TERM_TAC THEN DECIDE_TAC
]);


val S_BOOL_BIGCAT_def =
 Define
  `(S_BOOL_BIGCAT [b1] = S_BOOL b1) /\
   (S_BOOL_BIGCAT (b1::b2::l) = S_CAT (S_BOOL b1, S_BOOL_BIGCAT (b2::l)))`



val UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___BOOL_BIGCAT =
 store_thm
  ("UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___BOOL_BIGCAT",

``(!f:'a fl b.
   UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE
    (F_SUFFIX_IMP (S_BOOL_BIGCAT [b], f)) (F_IMPLIES((F_STRONG_BOOL b), f))) /\
  (!f:'a fl b1 b2 l. UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE
    (F_SUFFIX_IMP (S_BOOL_BIGCAT (b1::b2::l), f))
    (F_IMPLIES((F_STRONG_BOOL b1), F_NEXT (F_SUFFIX_IMP (S_BOOL_BIGCAT (b2::l), f)))))``,

  REPEAT STRIP_TAC THENL [
    SIMP_TAC std_ss [S_BOOL_BIGCAT_def,
      UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___BOOL],

    SIMP_TAC std_ss [S_BOOL_BIGCAT_def] THEN
    ASSUME_TAC UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CAT THEN
    Q_SPECL_NO_ASSUM 0 [`S_BOOL b1`, `S_BOOL_BIGCAT (b2::l)`, `f`] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 (
      Cases_on `l` THEN SIMP_TAC list_ss [US_SEM_def, S_BOOL_BIGCAT_def]
    ) THEN
    ASSUME_TAC UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___BOOL THEN
    FULL_SIMP_TAC std_ss [UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def]
  ]);
























val UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CLOCK_BOOL =
 store_thm
  ("UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CLOCK_BOOL",

``!b f c. UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE
          (F_CLOCK_COMP c (F_SUFFIX_IMP ((S_BOOL b), f)))
          (F_W_CLOCK c (F_IMPLIES((F_STRONG_BOOL b), F_CLOCK_COMP c f)))``,


SIMP_TAC (std_ss++resq_SS) [UF_SEM_def, IN_LESSX_REWRITE, UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def,
IS_INFINITE_TOP_BOTTOM_FREE_PATH___COMPLEMENT, F_IMPLIES_def, F_OR_def,
F_CLOCK_COMP_def, F_W_CLOCK_def, S_CLOCK_COMP_def, US_SEM_def,
COMPLEMENT_COMPLEMENT, F_W_def, F_G_def, F_F_def
] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [IS_INFINITE_TOP_BOTTOM_FREE_PATH_def, LENGTH_def, ELEM_def, LS, GT, LENGTH_SEL, SEL_def, RESTN_INFINITE, IMP_DISJ_THM,
xnum_distinct, HEAD_def, LENGTH_COMPLEMENT, RESTN_COMPLEMENT, IN_LESS] THEN

SUBGOAL_TAC `!k. (COMPLEMENT (INFINITE (\n. p (n + k)))) =
                 (INFINITE (\n. p (n + k)))` THEN1 (
  SIMP_TAC std_ss [COMPLEMENT_def, path_11, FUN_EQ_THM] THEN
  REPEAT GEN_TAC THEN
  `?s. p (n + k) = STATE s` by METIS_TAC[] THEN
  ASM_SIMP_TAC std_ss [COMPLEMENT_LETTER_def]
) THEN
ASM_SIMP_TAC std_ss [HEAD_def] THEN WEAKEN_HD_TAC THEN
`!j. B_SEM (p j) B_TRUE` by METIS_TAC[B_SEM_def] THEN
ASM_SIMP_TAC std_ss [HEAD_def] THEN WEAKEN_HD_TAC THEN

`!j. B_SEM (p j) (B_NOT c) = ~(B_SEM (p j) c)` by METIS_TAC[B_SEM_def] THEN
ASM_SIMP_TAC std_ss [HEAD_def] THEN WEAKEN_HD_TAC THEN

EQ_TAC THENL [
  REPEAT STRIP_TAC THEN
  LEFT_DISJ_TAC THEN
  FULL_SIMP_TAC std_ss [] THEN
  Q_EXISTS_LEAST_TAC `?l:num. B_SEM (p l) c` THEN
  FULL_SIMP_TAC std_ss [] THEN
  Q_TAC EXISTS_TAC `l` THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THENL [
    ALL_TAC,
    METIS_TAC[]
  ] THEN
  Q_SPEC_NO_ASSUM 3 `l` THEN
  FULL_SIMP_TAC std_ss [] THEN
  DISJ1_TAC THEN
  Q_SPECL_NO_ASSUM 0 [`SEL_REC l 0 (INFINITE p)`,
                      `SEL_REC 1 l (INFINITE p)`] THEN
  FULL_SIMP_TAC std_ss [] THENL [
    FULL_SIMP_TAC std_ss [prove (``l + (1:num) = 1 + l``, DECIDE_TAC)] THEN
    FULL_SIMP_TAC std_ss [SEL_REC_SPLIT],

    CCONTR_TAC THEN WEAKEN_HD_TAC THEN
    UNDISCH_HD_TAC THEN
    SIMP_TAC std_ss [] THEN
    NTAC 2 (WEAKEN_NO_TAC 1) THEN
    Induct_on `l` THENL [
      SIMP_TAC std_ss [SEL_REC_def] THEN
      EXISTS_TAC ``[]:'a letter list list`` THEN
      SIMP_TAC list_ss [CONCAT_def],

      REPEAT STRIP_TAC THEN
      FULL_SIMP_TAC arith_ss [] THEN
      Q_TAC EXISTS_TAC `vlist <> [[p l]]` THEN
      ASM_SIMP_TAC list_ss [FinitePSLPathTheory.ELEM_def,
        FinitePSLPathTheory.RESTN_def, FinitePSLPathTheory.HEAD_def,
        CONCAT_APPEND, CONCAT_def] THEN
      REPEAT STRIP_TAC THENL [
        REWRITE_TAC [prove (``SUC l = 1 + l``, DECIDE_TAC)] THEN
        ASM_SIMP_TAC list_ss [SEL_REC_SPLIT] THEN
        ONCE_REWRITE_TAC [prove (``1 = SUC 0``, DECIDE_TAC)] THEN
        SIMP_TAC std_ss [SEL_REC_SUC, ELEM_INFINITE, SEL_REC_def],

        `l < SUC l` by DECIDE_TAC THEN
        METIS_TAC[B_SEM_def]
      ]
    ],

    FULL_SIMP_TAC std_ss [LENGTH_SEL_REC],

    UNDISCH_HD_TAC THEN
    ONCE_REWRITE_TAC [prove (``1 = SUC 0``, DECIDE_TAC)] THEN
    SIMP_TAC list_ss [SEL_REC_SUC, ELEM_INFINITE, SEL_REC_def,
      FinitePSLPathTheory.ELEM_def, FinitePSLPathTheory.RESTN_def,
      FinitePSLPathTheory.HEAD_def] THEN
    METIS_TAC[B_SEM_def]
  ],


  Q.ABBREV_TAC `XXX = (?k.
             (B_SEM (p k) c /\
              (~B_SEM (p k) b \/
               UF_SEM (INFINITE (\n. p (n + k))) (F_CLOCK_COMP c f))) /\
             !j. ~(j < k) \/ ~B_SEM (p j) c) \/ !k. ~B_SEM (p k) c` THEN
  REPEAT STRIP_TAC THEN
  LEFT_DISJ_TAC THEN
  REPEAT STRIP_TAC THEN
  RIGHT_DISJ_TAC THEN
  LEFT_DISJ_TAC THEN
  SIMP_ALL_TAC std_ss [] THEN

  SUBGOAL_TAC `(!vlist.
      ~(v1 = CONCAT vlist) \/
      ~EVERY (\v'. (LENGTH v' = 1) /\ B_SEM (ELEM v' 0) (B_NOT c)) vlist) =
      ~(EVERY (\s. B_SEM s (B_NOT c)) v1)` THEN1 (
    ONCE_REWRITE_TAC[prove (``(A = B) = (~A = ~B)``, PROVE_TAC[])] THEN
    EQ_TAC THEN SIMP_TAC std_ss [] THEN STRIP_TAC THENL [
      ASM_REWRITE_TAC[] THEN
      WEAKEN_NO_TAC 1 (*Def v1*) THEN
      Induct_on `vlist` THENL [
        SIMP_TAC list_ss [CONCAT_def],

        SIMP_TAC list_ss [CONCAT_def] THEN
        Cases_on `h` THEN
        FULL_SIMP_TAC list_ss [LENGTH_NIL, ELEM_EL]
      ],

      WEAKEN_NO_TAC 3 (*v1 <> v2 = SEL REC...*) THEN
      UNDISCH_HD_TAC THEN
      SPEC_TAC (``v1:'a letter list``, ``v1:'a letter list``) THEN
      INDUCT_THEN SNOC_INDUCT ASSUME_TAC THENL [
        REPEAT STRIP_TAC THEN
        EXISTS_TAC ``[]:'a letter list list`` THEN
        SIMP_TAC list_ss [CONCAT_def],


        SIMP_TAC list_ss [SNOC_APPEND] THEN
        REPEAT STRIP_TAC THEN
        FULL_SIMP_TAC std_ss [] THEN
        Q_TAC EXISTS_TAC `vlist <> [[x]]` THEN
        ASM_SIMP_TAC list_ss [CONCAT_APPEND, CONCAT_def,
          ELEM_EL]
      ]
    ]
  ) THEN
  ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN


  SUBGOAL_TAC `LENGTH v1 = j` THEN1 (
    `LENGTH (v1 <> v2) = j + 1` by METIS_TAC[LENGTH_SEL_REC] THEN
    UNDISCH_HD_TAC THEN
    ASM_SIMP_TAC list_ss []
  ) THEN
  UNDISCH_NO_TAC 3 (*v1 <> v2*) THEN
  REWRITE_TAC [prove (``l + (1:num) = 1 + l``, DECIDE_TAC)] THEN
  ASM_SIMP_TAC std_ss [SEL_REC_SPLIT, APPEND_LENGTH_EQ, LENGTH_SEL_REC] THEN
  ONCE_REWRITE_TAC [prove (``1 = SUC 0``, DECIDE_TAC)] THEN
  SIMP_TAC std_ss [SEL_REC_SUC, ELEM_INFINITE, SEL_REC_def] THEN
  REPEAT STRIP_TAC THEN
  GSYM_NO_TAC 1 THEN
  `?s. p j = STATE s` by METIS_TAC[] THEN
  `?P. P = \k. (B_SEM (p k) c /\
              (~B_SEM (p k) b \/
               UF_SEM (INFINITE (\n. p (k + n))) (F_CLOCK_COMP c f)) /\
               !j. ~(j < k) \/ ~B_SEM (p j) c)` by METIS_TAC[] THEN
  SUBGOAL_TAC `?k. P k` THEN1 (
    Q.UNABBREV_TAC `XXX` THEN
    FULL_SIMP_TAC list_ss [ELEM_EL, B_SEM_def] THENL [
      METIS_TAC[],
      Q_TAC EXISTS_TAC `k` THEN FULL_SIMP_TAC arith_ss [],
      METIS_TAC[]
    ]
  ) THEN
  NTAC 2 (WEAKEN_NO_TAC  10) THEN GSYM_NO_TAC 1 THEN

  FULL_SIMP_TAC list_ss [FinitePSLPathTheory.ELEM_def,
      FinitePSLPathTheory.RESTN_def, FinitePSLPathTheory.HEAD_def,
      B_SEM_def] THEN
  Q_EXISTS_LEAST_TAC `?l. P l` THEN
  SIMP_ALL_TAC std_ss [] THEN
  REMAINS_TAC `l = j` THEN1 METIS_TAC[] THEN
  REMAINS_TAC `~(l < j) /\ ~(j < l)` THEN1 DECIDE_TAC THEN
  STRIP_TAC THENL [
    CCONTR_TAC THEN
    SIMP_ALL_TAC std_ss [] THEN
    REMAINS_TAC `MEM (p l) v1` THEN1 (
      SIMP_ALL_TAC std_ss [listTheory.EVERY_MEM] THEN
      METIS_TAC[B_SEM_def]
    ) THEN
    GSYM_NO_TAC 8 (*v1 = SEL_REC ..*) THEN
    ASM_SIMP_TAC std_ss [MEM_SEL_REC, ELEM_INFINITE] THEN
    METIS_TAC[],

    METIS_TAC[B_SEM_def]
  ]
]);



val S_SEM___CLOCK_OCCURRENCE =
 store_thm
  ("S_SEM___CLOCK_OCCURRENCE",

  ``!s v c. S_SEM v c s /\ ~(v = []) /\ S_CLOCK_FREE s ==>
            B_SEM (EL (LENGTH v - 1) v) c``,

INDUCT_THEN sere_induct ASSUME_TAC THENL [
  SIMP_TAC (list_ss++resq_SS) [S_SEM_def, CLOCK_TICK_def, IN_LESS,
    ELEM_EL],

  SIMP_TAC (list_ss++resq_SS) [S_SEM_def, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THEN
  Cases_on `v2 = []` THENL [
    FULL_SIMP_TAC list_ss [],

    `LENGTH v2 > 0` by (Cases_on `v2` THEN FULL_SIMP_TAC list_ss []) THEN
    ASM_SIMP_TAC list_ss [EL_APPEND2]
  ],

  SIMP_TAC (list_ss++resq_SS) [S_SEM_def, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THEN
  FULL_SIMP_TAC list_ss [] THEN
  ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC, EL_APPEND2] THEN
  `LENGTH (l::v2) - 1 = LENGTH v2` by SIMP_TAC list_ss [] THEN
  `~(l::v2 = [])` by SIMP_TAC list_ss [] THEN
  SIMP_TAC list_ss [] THEN
  METIS_TAC[],


  SIMP_TAC std_ss [S_SEM_def, S_CLOCK_FREE_def] THEN METIS_TAC[],
  SIMP_TAC std_ss [S_SEM_def, S_CLOCK_FREE_def] THEN METIS_TAC[],
  SIMP_TAC std_ss [S_SEM_def],

  SIMP_TAC std_ss [S_SEM_def, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_TAC `?vlist' x. (v = CONCAT vlist' <> x) /\ (~(x = [])) /\
    S_SEM x c s` THEN1 (
    UNDISCH_ALL_TAC THEN
    SPEC_TAC (``v:'a letter list``, ``v:'a letter list``) THEN
    SPEC_TAC (``vlist:'a letter list list``, ``vlist:'a letter list list``) THEN
    INDUCT_THEN SNOC_INDUCT ASSUME_TAC THENL [
      ASM_SIMP_TAC list_ss [CONCAT_def],

      REPEAT STRIP_TAC THEN
      FULL_SIMP_TAC list_ss [SNOC_APPEND, CONCAT_APPEND, CONCAT_def] THEN
      Cases_on `x = []` THENL [
        FULL_SIMP_TAC list_ss [] THEN
        METIS_TAC[],

        METIS_TAC[]
      ]
    ]
  ) THEN

  WEAKEN_NO_TAC 5 (*v = CONCAT vlist*) THEN
  `LENGTH x > 0` by (Cases_on `x` THEN ASM_SIMP_TAC list_ss [] THEN PROVE_TAC[]) THEN
  ASM_SIMP_TAC list_ss [EL_APPEND2],


  SIMP_TAC std_ss [S_CLOCK_FREE_def]
]);





val S_SEM___EXTEND_NO_CLOCK_CYCLES =
 store_thm
  ("S_SEM___EXTEND_NO_CLOCK_CYCLES",

``!s k m n0 c p.
((!l. (l < k) ==> B_SEM (ELEM p (n0 + l)) (B_NOT c)) /\
 (S_SEM (SEL_REC m (n0+k) p) c s) /\
 (m > 0) /\
 (S_CLOCK_FREE s)) ==>
 (S_SEM (SEL_REC (m+k) n0 p) c s)``,


INDUCT_THEN sere_induct ASSUME_TAC THENL [
  SIMP_TAC (std_ss++resq_SS) [S_SEM_def, CLOCK_TICK_def, IN_LESSX_REWRITE,
    LENGTH_SEL_REC, IN_LESS, ELEM_EL, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THENL [
    DECIDE_TAC,

    UNDISCH_NO_TAC 2 THEN
    ASM_SIMP_TAC arith_ss [EL_SEL_REC],

    FULL_SIMP_TAC arith_ss [EL_SEL_REC] THEN
    Cases_on `i < k` THENL [
      PROVE_TAC[],

      REMAINS_TAC `?i'. (i' < m - 1) /\ ((i' + (k + n0)) = (i + n0))` THEN1 PROVE_TAC[] THEN
      Q_TAC EXISTS_TAC `i - k` THEN
      ASM_SIMP_TAC arith_ss []
    ],

    UNDISCH_NO_TAC 0 THEN
    ASM_SIMP_TAC arith_ss [EL_SEL_REC]
  ],




  SIMP_TAC std_ss [S_SEM_def, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THEN
  Cases_on `~(LENGTH v1 > 0)` THEN1 (
    `LENGTH v1 = 0` by DECIDE_TAC THEN
    Q_TAC EXISTS_TAC `[]:'a letter list` THEN
    Q_TAC EXISTS_TAC `SEL_REC (k + m) n0 p` THEN
    FULL_SIMP_TAC list_ss [LENGTH_NIL]
  ) THEN

  Q_TAC EXISTS_TAC `SEL_REC (LENGTH v1 + k) n0 p` THEN
  Q_TAC EXISTS_TAC `SEL_REC (LENGTH v2) (n0 + (LENGTH v1 + k)) p` THEN
  ASM_SIMP_TAC arith_ss [GSYM SEL_REC_SPLIT] THEN


  Q.ABBREV_TAC `m1 = LENGTH v1` THEN
  Q.ABBREV_TAC `m2 = LENGTH v2` THEN
  `m = m1 + m2` by METIS_TAC[LENGTH_SEL_REC, LENGTH_APPEND] THEN
  ASM_REWRITE_TAC[] THEN

  UNDISCH_NO_TAC 9 (*SEL REC m (n0 + k) p = v1 <> v2*) THEN
  SUBGOAL_TAC `SEL_REC m (n0 + k) p =
               SEL_REC m1 (n0 + k) p <> SEL_REC m2 ((n0 + k) + m1) p` THEN1 (
    METIS_TAC[SEL_REC_SPLIT, ADD_COMM]
  ) THEN

  ASM_SIMP_TAC arith_ss [APPEND_LENGTH_EQ, LENGTH_SEL_REC] THEN
  METIS_TAC[ADD_COMM],




  SIMP_TAC std_ss [S_SEM_def, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THEN

  Q_TAC EXISTS_TAC `SEL_REC (LENGTH v1 + k) n0 p` THEN
  Q_TAC EXISTS_TAC `SEL_REC (LENGTH v2) (n0 + ((LENGTH v1 + 1) + k)) p` THEN
  Q_TAC EXISTS_TAC `l` THEN

  Q.ABBREV_TAC `m1 = LENGTH v1` THEN
  Q.ABBREV_TAC `m2 = LENGTH v2` THEN
  SUBGOAL_TAC `m = (m1 + 1) + m2` THEN1 (
    `LENGTH (SEL_REC m (n0 + k) p) = LENGTH (v1 <> [l] <> v2)` by METIS_TAC[] THEN
    UNDISCH_HD_TAC THEN
    ASM_SIMP_TAC list_ss [LENGTH_SEL_REC]
  ) THEN
  ASM_REWRITE_TAC[] THEN

  SUBGOAL_TAC `[l] = SEL_REC (1:num) (n0 + (m1 + k)) p` THEN1 (
    MATCH_RIGHT_EQ_MP_TAC LIST_EQ_REWRITE THEN
    SIMP_TAC list_ss [LENGTH_SEL_REC] THEN
    REPEAT STRIP_TAC THEN
    rename1 `EL n [l]` THEN
    `n = 0` by DECIDE_TAC THEN
    ASM_SIMP_TAC std_ss [EL_SEL_REC] THEN
    `EL m1 (SEL_REC m (n0 + k) p) = EL m1 (v1 <> [l] <> v2)` by METIS_TAC[] THEN
    UNDISCH_HD_TAC THEN
    ASM_SIMP_TAC list_ss [EL_SEL_REC, EL_APPEND1, EL_APPEND2]
  ) THEN

  SUBGOAL_TAC `(v1 = SEL_REC m1 (n0 + k) p) /\
               (v2 = SEL_REC m2 ((n0 + k) + m1 + 1) p)` THEN1 (
    SUBGOAL_TAC `SEL_REC m (n0 + k) p =
                SEL_REC m1 (n0 + k) p <> [l] <> SEL_REC m2 ((n0 + k) + m1 + 1) p` THEN1 (
      GSYM_NO_TAC 9 (*SEL_REC m (n0 + k) = ...*) THEN
      `m1 + 1 + m2 =  m2 + 1 + m1` by DECIDE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[SEL_REC_SPLIT] THEN
      SIMP_TAC list_ss []
    ) THEN
    UNDISCH_NO_TAC 10 (*SEL_REC m (n0 + k) = ...*) THEN
    ASM_SIMP_TAC arith_ss [APPEND_LENGTH_EQ, LENGTH_SEL_REC, LENGTH_APPEND]
  ) THEN

  REPEAT STRIP_TAC THENL [
    `(n0 + (m1 + 1 + k)) = n0 + (1 + (m1 + k))` by DECIDE_TAC THEN
    ASM_REWRITE_TAC[GSYM SEL_REC_SPLIT] THEN
    SIMP_TAC arith_ss [],


    UNDISCH_NO_TAC 10 (*S_SEM v1 <> [l] *) THEN
    ASM_REWRITE_TAC [GSYM SEL_REC_SPLIT] THEN
    `(n0 + (m1 + k)) = (n0 + k) + m1` by DECIDE_TAC THEN
    ASM_REWRITE_TAC [GSYM SEL_REC_SPLIT] THEN
    `((1 + m1) > 0) /\ ((1 + (m1 + k)) = ((1 + m1) + k))` by DECIDE_TAC THEN
    METIS_TAC[],

    FULL_SIMP_TAC arith_ss []
  ],



  SIMP_TAC std_ss [S_SEM_def, S_CLOCK_FREE_def] THEN
  METIS_TAC[],


  SIMP_TAC std_ss [S_SEM_def, S_CLOCK_FREE_def] THEN
  METIS_TAC[],


  SIMP_TAC std_ss [S_SEM_def, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THEN
  `LENGTH (SEL_REC m (n0 + k) p) = LENGTH ([]:'a letter list)` by PROVE_TAC[] THEN
  FULL_SIMP_TAC list_ss [LENGTH_SEL_REC],


  SIMP_TAC std_ss [S_SEM_def, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_TAC `?h l. (CONCAT vlist = CONCAT (h::l)) /\ (!e. MEM e (h::l) ==> MEM e vlist) /\ (LENGTH h > 0)` THEN1 (
    Induct_on `vlist` THENL [
      REPEAT STRIP_TAC THEN
      `LENGTH (SEL_REC m (n0 + k) p) = LENGTH (CONCAT ([]:'a letter list list))` by PROVE_TAC[] THEN
      FULL_SIMP_TAC list_ss [CONCAT_def, LENGTH_SEL_REC],

      GEN_TAC THEN
      Cases_on `h = []` THENL [
        FULL_SIMP_TAC list_ss [CONCAT_def] THEN
        METIS_TAC[],

        FULL_SIMP_TAC list_ss [CONCAT_def] THEN
        REMAINS_TAC `LENGTH h > 0` THEN1 METIS_TAC[] THEN
        Cases_on `h` THEN FULL_SIMP_TAC list_ss []
      ]
    ]
  ) THEN
  FULL_SIMP_TAC list_ss [listTheory.EVERY_MEM, CONCAT_def] THEN


  Q_TAC EXISTS_TAC `(SEL_REC (LENGTH h + k) n0 p)::l` THEN
  Q.ABBREV_TAC `m1 = LENGTH h` THEN
  Q.ABBREV_TAC `m2 = LENGTH (CONCAT l)` THEN
  `m = m1 + m2` by METIS_TAC[LENGTH_SEL_REC, LENGTH_APPEND] THEN
  ASM_SIMP_TAC list_ss [DISJ_IMP_THM, CONCAT_def] THEN


  GSYM_NO_TAC 9 (*SEL REC m (n0 + k) p = v1 <> v2*) THEN
  UNDISCH_HD_TAC THEN
  SUBGOAL_TAC `SEL_REC (m1 + m2) (k + n0) p =
               SEL_REC m1 (k + n0) p <> SEL_REC m2 ((k+ n0) + m1) p` THEN1 (
    METIS_TAC[SEL_REC_SPLIT, ADD_COMM]
  ) THEN

  ASM_SIMP_TAC list_ss [APPEND_LENGTH_EQ, LENGTH_SEL_REC, CONCAT_def] THEN
  REPEAT STRIP_TAC THEN
  `(k + (m1 + n0)) = (n0 + (k + m1))` by DECIDE_TAC THEN
  ASM_REWRITE_TAC[GSYM SEL_REC_SPLIT] THEN
  SIMP_TAC arith_ss [],


  SIMP_TAC std_ss [S_CLOCK_FREE_def]
]);





val S_SEM___RESTRICT_NO_CLOCK_CYCLES =
 store_thm
  ("S_SEM___RESTRICT_NO_CLOCK_CYCLES",

``!s k m n0 c p.
((!l. (l < k) ==> ((B_SEM (ELEM p (n0 + l)) (B_NOT c)) /\ ?s'. (ELEM p (n0 + l) = STATE s'))) /\
 (S_SEM (SEL_REC (m+k) n0 p) c s) /\
 (m > 0) /\
 (S_CLOCK_FREE s)) ==>
 (S_SEM (SEL_REC m (n0+k) p) c s)``,


INDUCT_THEN sere_induct ASSUME_TAC THENL [
  SIMP_TAC (std_ss++resq_SS) [S_SEM_def, CLOCK_TICK_def, IN_LESSX_REWRITE,
    LENGTH_SEL_REC, IN_LESS, ELEM_EL, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THENL [
    FULL_SIMP_TAC arith_ss [EL_SEL_REC],

    FULL_SIMP_TAC arith_ss [EL_SEL_REC] THEN
    REMAINS_TAC `?i'. (i' < k + m - 1) /\ ((i' + n0) = (i + (k + n0)))` THEN1 PROVE_TAC[] THEN
    Q_TAC EXISTS_TAC `i + k` THEN
    ASM_SIMP_TAC arith_ss [],

    FULL_SIMP_TAC arith_ss [EL_SEL_REC]
  ],




  SIMP_TAC std_ss [S_SEM_def, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THEN
  Cases_on `~(LENGTH v1 > 0)` THEN1 (
    `LENGTH v1 = 0` by DECIDE_TAC THEN
    Q_TAC EXISTS_TAC `[]:'a letter list` THEN
    Q_TAC EXISTS_TAC `SEL_REC m (n0 + k) p` THEN
    FULL_SIMP_TAC list_ss [LENGTH_NIL]
  ) THEN

  Q.ABBREV_TAC `m1 = LENGTH v1` THEN
  Q.ABBREV_TAC `m2 = LENGTH v2` THEN
  `m + k = m1 + m2` by METIS_TAC[LENGTH_SEL_REC, LENGTH_APPEND] THEN

  SUBGOAL_TAC `m1 > k` THEN1 (
    ASSUME_TAC S_SEM___CLOCK_OCCURRENCE THEN
    Q_SPECL_NO_ASSUM 0 [`s`, `v1`, `c`] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 (
      ASM_REWRITE_TAC[] THEN
      Cases_on `v1` THEN FULL_SIMP_TAC list_ss []
    ) THEN
    UNDISCH_HD_TAC THEN

    `EL (m1 - 1) v1 = EL (m1 - 1) (v1 <> v2)` by ASM_SIMP_TAC list_ss [EL_APPEND1] THEN
    ASM_SIMP_TAC std_ss [] THEN
    GSYM_NO_TAC 10 (* SEL REC = v1 <> v2*) THEN
    ASM_SIMP_TAC arith_ss [EL_SEL_REC] THEN

    REPEAT STRIP_TAC THEN CCONTR_TAC THEN
    Q_SPEC_NO_ASSUM 13 `m1 - 1` THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 DECIDE_TAC THEN
    CLEAN_ASSUMPTIONS_TAC THEN
    `m1 + n0 - 1 = (n0 + (m1 - 1))` by DECIDE_TAC THEN
    METIS_TAC[B_SEM_def]
  ) THEN

  Q_TAC EXISTS_TAC `SEL_REC (m1 - k) (n0 + k) p` THEN
  Q_TAC EXISTS_TAC `SEL_REC m2 ((n0 + k) + (m1 - k)) p` THEN
  REWRITE_TAC [GSYM SEL_REC_SPLIT] THEN
  `(m2 + (m1 - k) = m) /\ ((n0 + k + (m1 - k)) = n0 + m1)` by DECIDE_TAC THEN
  ASM_REWRITE_TAC[] THEN

  UNDISCH_NO_TAC 12 (*SEL REC (m + k) n0 p = v1 <> v2*) THEN
  SUBGOAL_TAC `SEL_REC (m+k) n0 p =
               SEL_REC m1 n0 p <> SEL_REC m2 (n0 + m1) p` THEN1 (
    METIS_TAC[SEL_REC_SPLIT, ADD_COMM]
  ) THEN

  ASM_SIMP_TAC arith_ss [APPEND_LENGTH_EQ, LENGTH_SEL_REC],



  SIMP_TAC std_ss [S_SEM_def, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THEN

  Q.ABBREV_TAC `m1 = LENGTH v1` THEN
  Q.ABBREV_TAC `m2 = LENGTH v2` THEN
  SUBGOAL_TAC `m + k = (m1 + 1) + m2` THEN1 (
    `LENGTH (SEL_REC (m + k) n0 p) = LENGTH (v1 <> [l] <> v2)` by PROVE_TAC[] THEN
    UNDISCH_HD_TAC THEN
    ASM_SIMP_TAC list_ss [LENGTH_SEL_REC]
  ) THEN
  SUBGOAL_TAC `m1 >= k` THEN1 (
    ASSUME_TAC S_SEM___CLOCK_OCCURRENCE THEN
    Q_SPECL_NO_ASSUM 0 [`s`, `v1<>[l]`, `c`] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 (
      ASM_SIMP_TAC list_ss []
    ) THEN
    UNDISCH_HD_TAC THEN


    `EL m1 (v1 <> [l]) = EL m1 (v1 <> [l] <> v2)` by ASM_SIMP_TAC list_ss [EL_APPEND1] THEN
    ASM_SIMP_TAC list_ss [] THEN
    GSYM_NO_TAC 9 (* SEL REC = v1 <> [l] <> v2*) THEN
    ASM_SIMP_TAC arith_ss [EL_SEL_REC] THEN

    REPEAT STRIP_TAC THEN CCONTR_TAC THEN
    Q_SPEC_NO_ASSUM 12 `m1` THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 DECIDE_TAC THEN
    CLEAN_ASSUMPTIONS_TAC THEN
    METIS_TAC[B_SEM_def, ADD_COMM]
  ) THEN

  Q_TAC EXISTS_TAC `SEL_REC (m1 - k) (n0 + k) p` THEN
  Q_TAC EXISTS_TAC `SEL_REC m2 ((n0 + k) + ((m1 - k)+ 1)) p` THEN
  Q_TAC EXISTS_TAC `l` THEN

  SUBGOAL_TAC `[l] = SEL_REC (1:num) (n0 + m1) p` THEN1 (
    MATCH_RIGHT_EQ_MP_TAC LIST_EQ_REWRITE THEN
    SIMP_TAC list_ss [LENGTH_SEL_REC] THEN
    REPEAT STRIP_TAC THEN
    rename1 `EL n [l]` THEN
    `n = 0` by DECIDE_TAC THEN
    ASM_SIMP_TAC list_ss [EL_SEL_REC] THEN
    `EL m1 (SEL_REC (m + k) n0 p) = EL m1 (v1 <> [l] <> v2)` by METIS_TAC[] THEN
    UNDISCH_HD_TAC THEN
    ASM_SIMP_TAC list_ss [EL_SEL_REC, EL_APPEND1, EL_APPEND2]
  ) THEN

  SUBGOAL_TAC `(v1 = SEL_REC m1 n0 p) /\
               (v2 = SEL_REC m2 (n0 + m1 + 1) p)` THEN1 (
    SUBGOAL_TAC `SEL_REC (m+k) n0 p =
                SEL_REC m1 n0 p <> [l] <> SEL_REC m2 (n0 + m1 + 1) p` THEN1 (
      GSYM_NO_TAC 10 (*SEL_REC (m+k) n0 = ...*) THEN
      `m1 + 1 + m2 =  m2 + 1 + m1` by DECIDE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[SEL_REC_SPLIT] THEN
      SIMP_TAC list_ss []
    ) THEN
    UNDISCH_NO_TAC 11 (*SEL_REC (m+k) n0 = ...*) THEN
    ASM_SIMP_TAC arith_ss [APPEND_LENGTH_EQ, LENGTH_SEL_REC, LENGTH_APPEND]
  ) THEN

  REPEAT STRIP_TAC THENL [
    `(n0 + (m1 + 1 + k)) = n0 + (1 + (m1 + k))` by DECIDE_TAC THEN
    `(n0 + m1 = ((n0 + k) + (m1 - k))) /\
     ((n0 + k + (m1 - k + 1)) = ((n0 + k) + (1 + (m1 - k))))` by
     ASM_SIMP_TAC arith_ss [] THEN
    ASM_REWRITE_TAC[GSYM SEL_REC_SPLIT] THEN
    NTAC 2 WEAKEN_HD_TAC THEN
    `(m2 + (1 + (m1 - k))) = m` by DECIDE_TAC THEN
    ASM_REWRITE_TAC[],


    UNDISCH_NO_TAC 11 (*S_SEM v1 <> [l] *) THEN
    ASM_REWRITE_TAC [GSYM SEL_REC_SPLIT] THEN
    `n0 + m1 = ((n0 + k) + (m1 - k))` by DECIDE_TAC THEN
    ASM_REWRITE_TAC [GSYM SEL_REC_SPLIT] THEN
    WEAKEN_HD_TAC THEN
    `((1 + (m1 - k)) > 0) /\ ((((1 + (m1 -k)) + k)) = (1 + m1))` by DECIDE_TAC THEN
    METIS_TAC[],

    FULL_SIMP_TAC arith_ss []
  ],



  SIMP_TAC std_ss [S_SEM_def, S_CLOCK_FREE_def] THEN
  METIS_TAC[],


  SIMP_TAC std_ss [S_SEM_def, S_CLOCK_FREE_def] THEN
  METIS_TAC[],


  SIMP_TAC std_ss [S_SEM_def, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THEN
  `LENGTH (SEL_REC (m + k) n0 p) = LENGTH ([]:'a letter list)` by PROVE_TAC[] THEN
  FULL_SIMP_TAC list_ss [LENGTH_SEL_REC],


  SIMP_TAC std_ss [S_SEM_def, S_CLOCK_FREE_def] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_TAC `?h l. (CONCAT vlist = CONCAT (h::l)) /\ (!e. MEM e (h::l) ==> MEM e vlist) /\ (LENGTH h > 0)` THEN1 (
    Induct_on `vlist` THENL [
      REPEAT STRIP_TAC THEN
      `LENGTH (SEL_REC (m+k) n0 p) = LENGTH (CONCAT ([]:'a letter list list))` by PROVE_TAC[] THEN
      FULL_SIMP_TAC list_ss [CONCAT_def, LENGTH_SEL_REC],

      GEN_TAC THEN
      Cases_on `h = []` THENL [
        FULL_SIMP_TAC list_ss [CONCAT_def] THEN
        METIS_TAC[],

        FULL_SIMP_TAC list_ss [CONCAT_def] THEN
        REMAINS_TAC `LENGTH h > 0` THEN1 METIS_TAC[] THEN
        Cases_on `h` THEN FULL_SIMP_TAC list_ss []
      ]
    ]
  ) THEN
  FULL_SIMP_TAC list_ss [listTheory.EVERY_MEM, CONCAT_def] THEN


  Q.ABBREV_TAC `m1 = LENGTH h` THEN
  Q.ABBREV_TAC `m2 = LENGTH (CONCAT l)` THEN
  `k + m = m1 + m2` by METIS_TAC[LENGTH_SEL_REC, LENGTH_APPEND] THEN


  SUBGOAL_TAC `m1 > k` THEN1 (
    ASSUME_TAC S_SEM___CLOCK_OCCURRENCE THEN
    Q_SPECL_NO_ASSUM 0 [`s`, `h`, `c`] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 (
      REPEAT STRIP_TAC THENL [
        PROVE_TAC[],
        Cases_on `h` THEN FULL_SIMP_TAC list_ss [],
        ASM_REWRITE_TAC[]
      ]
    ) THEN
    UNDISCH_HD_TAC THEN

    `EL (m1 - 1) h = EL (m1 - 1) (h<>(CONCAT l))` by ASM_SIMP_TAC list_ss [EL_APPEND1] THEN
    ASM_SIMP_TAC std_ss [] THEN
    GSYM_NO_TAC 10 (* SEL REC = h <> concat l*) THEN
    ASM_SIMP_TAC arith_ss [EL_SEL_REC] THEN

    REPEAT STRIP_TAC THEN CCONTR_TAC THEN
    Q_SPEC_NO_ASSUM 13 `m1 - 1` THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 DECIDE_TAC THEN
    CLEAN_ASSUMPTIONS_TAC THEN
    `m1 - 1 + n0 = (m1 + n0 - 1)` by DECIDE_TAC THEN
    METIS_TAC[B_SEM_def]
  ) THEN

  Q_TAC EXISTS_TAC `(SEL_REC (m1 - k) (k+n0) p)::l` THEN
  ASM_SIMP_TAC list_ss [DISJ_IMP_THM, CONCAT_def] THEN

  GSYM_NO_TAC 10 (*SEL REC m (n0 + k) p = v1 <> v2*) THEN
  UNDISCH_HD_TAC THEN
  SUBGOAL_TAC `SEL_REC (m1 + m2) n0 p =
               SEL_REC m1 n0 p <> SEL_REC m2 (n0 + m1) p` THEN1 (
    METIS_TAC[SEL_REC_SPLIT, ADD_COMM]
  ) THEN

  ASM_SIMP_TAC list_ss [APPEND_LENGTH_EQ, LENGTH_SEL_REC, CONCAT_def] THEN
  REPEAT STRIP_TAC THEN
  `((m1 + n0) = ((k + n0) + (m1 - k))) /\
   ((m2 + (m1 - k)) = m)` by DECIDE_TAC THEN
  ASM_REWRITE_TAC[GSYM SEL_REC_SPLIT],


  SIMP_TAC std_ss [S_CLOCK_FREE_def]
]);



val S_SEM___EXTEND_RESTRICT_NO_CLOCK_CYCLES =
 store_thm
  ("S_SEM___EXTEND_RESTRICT_NO_CLOCK_CYCLES",

``!s k m n0 c p.
((!l. (l < k) ==> ((B_SEM (ELEM p (n0 + l)) (B_NOT c)) /\ ?s'. (ELEM p (n0 + l) = STATE s'))) /\
 (m > 0) /\
 (S_CLOCK_FREE s)) ==>
 ((S_SEM (SEL_REC m (n0+k) p) c s) = (S_SEM (SEL_REC (m+k) n0 p) c s))``,

 METIS_TAC[S_SEM___RESTRICT_NO_CLOCK_CYCLES,
           S_SEM___EXTEND_NO_CLOCK_CYCLES]);



val UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CLOCK_CAT =
 store_thm
  ("UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CLOCK_CAT",

``!s1 s2 f c. (S_CLOCK_FREE s1 /\ S_CLOCK_FREE s2 /\
              (~(S_SEM [] c s1) /\ ~(S_SEM [] c s2))) ==>

   UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE
    (F_CLOCK_COMP c (F_SUFFIX_IMP (S_CAT(s1, s2), f)))
    (F_CLOCK_COMP c (F_SUFFIX_IMP (s1, (F_WEAK_X (F_SUFFIX_IMP (s2, f))))))``,

SIMP_TAC (std_ss++resq_SS) [UF_SEM_def, IN_LESSX_REWRITE, UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def,
IS_INFINITE_TOP_BOTTOM_FREE_PATH___COMPLEMENT,
F_CLOCK_COMP_def, S_CLOCK_COMP_def, F_U_CLOCK_def,
RESTN_RESTN, F_WEAK_X_def] THEN
REPEAT STRIP_TAC THEN
FULL_SIMP_TAC std_ss [IS_INFINITE_TOP_BOTTOM_FREE_PATH_def, LENGTH_def, US_SEM_def,
ELEM_def, LS, GT, LENGTH_SEL, SEL_def, RESTN_INFINITE,
COMPLEMENT_def, combinTheory.o_DEF,
GSYM S_CLOCK_COMP_CORRECT,
IN_LESSX_REWRITE, LS, xnum_distinct,
HEAD_def, IN_LESS] THEN
SUBGOAL_TAC `!x. COMPLEMENT_LETTER (p x) = p x` THEN1 (
  GEN_TAC THEN
  `?s. p x = STATE s` by METIS_TAC[] THEN
  ASM_REWRITE_TAC[COMPLEMENT_LETTER_def]
) THEN
ASM_REWRITE_TAC[] THEN WEAKEN_HD_TAC THEN

EQ_TAC THEN REPEAT STRIP_TAC THENL [
  LEFT_DISJ_TAC THEN
  RIGHT_DISJ_TAC THEN
  GEN_TAC THEN
  LEFT_DISJ_TAC THEN
  RIGHT_DISJ_TAC THEN
  GEN_TAC THEN
  RIGHT_DISJ_TAC THEN
  FULL_SIMP_TAC std_ss [] THEN

  Q_SPEC_NO_ASSUM 6 `j' + (k + (1 + k')) + j` THEN
  PROVE_CONDITION_NO_ASSUM 0 THENL [
    ALL_TAC,
    FULL_SIMP_TAC arith_ss []
  ] THEN

  SUBGOAL_TAC `k = 0` THEN1 (
    ASSUME_TAC S_SEM___CLOCK_OCCURRENCE THEN
    Q_SPECL_NO_ASSUM 0 [`s1`, `SEL_REC (j + 1) 0 (INFINITE p)`, `c`] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 (
      ASM_SIMP_TAC list_ss [prove (``j + 1 = SUC j``, DECIDE_TAC),
        SEL_REC_def]
    ) THEN
    UNDISCH_HD_TAC THEN
    SIMP_TAC std_ss [LENGTH_SEL_REC, EL_SEL_REC, ELEM_INFINITE] THEN
    STRIP_TAC THEN
    CCONTR_TAC THEN
    `0 < k` by DECIDE_TAC THEN
    `B_SEM (p (0 + j)) (B_NOT c)` by METIS_TAC[] THEN
    SIMP_ALL_TAC std_ss [] THEN
    METIS_TAC[B_SEM_def]
  ) THEN
  FULL_SIMP_TAC std_ss [] THEN

  Q_TAC EXISTS_TAC `SEL_REC (j + 1) 0 (INFINITE p)` THEN
  Q_TAC EXISTS_TAC `SEL_REC (k' + j' + 1) (0 + (j + 1)) (INFINITE p)` THEN
  REWRITE_TAC[GSYM SEL_REC_SPLIT] THEN
  SIMP_TAC arith_ss [] THEN

  CONJ_TAC THENL [
    METIS_TAC[],


    ASSUME_TAC S_SEM___EXTEND_NO_CLOCK_CYCLES THEN
    Q_SPECL_NO_ASSUM 0 [`s2`, `k'`, `j' + 1`, `j+1`, `c`, `INFINITE p`] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 (
      ASM_SIMP_TAC arith_ss [ELEM_INFINITE] THEN
      REPEAT STRIP_TAC THENL [
        `j + (l + 1) = 1 + l + j` by DECIDE_TAC THEN
        PROVE_TAC[],

        `(j + (k' + 1)) = (0 + (j + (k' + 1)))` by DECIDE_TAC THEN
        ONCE_ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM SEL_REC_RESTN] THEN
        WEAKEN_HD_TAC THEN
        FULL_SIMP_TAC arith_ss [RESTN_INFINITE]
      ]
    ) THEN
    FULL_SIMP_TAC arith_ss []
  ],



  `?k. k = PRE (LENGTH v1)` by METIS_TAC[] THEN
  `?k'. k' = PRE (LENGTH v2)` by METIS_TAC[] THEN

  SUBGOAL_TAC `LENGTH v1 > 0` THEN1 (
    Cases_on `v1` THENL [
      PROVE_TAC[],
      SIMP_TAC list_ss []
    ]
  ) THEN

  SUBGOAL_TAC `LENGTH v2 > 0` THEN1 (
    Cases_on `v2` THENL [
      PROVE_TAC[],
      SIMP_TAC list_ss []
    ]
  ) THEN

  `(?l. k + 1 = l) /\ (?l'. k' + 1 = l')` by METIS_TAC[] THEN

  SUBGOAL_TAC `j + 1 = l' + l` THEN1 (
    `j + 1 = LENGTH (v1 <> v2)` by METIS_TAC[LENGTH_SEL_REC] THEN
    ASM_SIMP_TAC std_ss [] THEN
    SIMP_TAC list_ss [] THEN
    DECIDE_TAC
  ) THEN
  FULL_SIMP_TAC std_ss [] THEN

  SUBGOAL_TAC `(v1 = SEL_REC l 0 (INFINITE p)) /\
               (v2 = SEL_REC l' l (INFINITE p))` THEN1 (
    `LENGTH v1 = l` by DECIDE_TAC THEN
    `LENGTH v2 = l'` by DECIDE_TAC THEN
    FULL_SIMP_TAC std_ss [SEL_REC_SPLIT, APPEND_LENGTH_EQ,LENGTH_SEL_REC]
  ) THEN
  NTAC 2 (WEAKEN_NO_TAC 7) (*Def k, k'*) THEN

  Q_SPEC_NO_ASSUM 10 `k` THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 (ASM_SIMP_TAC arith_ss [] THEN PROVE_TAC[]) THEN
  Q_SPEC_NO_ASSUM 0 `0:num` THEN
  FULL_SIMP_TAC std_ss [] THEN1 (
    ASSUME_TAC S_SEM___CLOCK_OCCURRENCE THEN
    Q_SPECL_NO_ASSUM 0 [`s1`, `SEL_REC l 0 (INFINITE p)`, `c`] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 (
      ASM_REWRITE_TAC[] THEN
      GSYM_NO_TAC 5 (*Def l*) THEN
      ASM_SIMP_TAC list_ss [SEL_REC_def, prove (``k + 1 = SUC k``, DECIDE_TAC)]
    ) THEN
    UNDISCH_HD_TAC THEN

    ASM_SIMP_TAC arith_ss [LENGTH_SEL_REC, EL_SEL_REC, ELEM_INFINITE] THEN
    `l - 1 = k` by DECIDE_TAC THEN
    ASM_REWRITE_TAC[]
  ) THEN

  SUBGOAL_TAC `B_SEM (p (1 + k' + k)) c` THEN1 (
    ASSUME_TAC S_SEM___CLOCK_OCCURRENCE THEN
    Q_SPECL_NO_ASSUM 0 [`s2`, `SEL_REC l' l (INFINITE p)`, `c`] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 (
      ASM_REWRITE_TAC[] THEN
      GSYM_NO_TAC 4 (*Def l'*) THEN
      ONCE_REWRITE_TAC[prove (``l:num = 0 + l``, DECIDE_TAC)] THEN
      REWRITE_TAC[GSYM SEL_REC_RESTN] THEN
      ASM_SIMP_TAC list_ss [SEL_REC_def, prove (``k' + 1 = SUC k'``, DECIDE_TAC)]
    ) THEN
    UNDISCH_HD_TAC THEN

    ASM_SIMP_TAC arith_ss [LENGTH_SEL_REC, EL_SEL_REC, ELEM_INFINITE] THEN
    `l + l' - 1 = k + l'` by DECIDE_TAC THEN
    ASM_REWRITE_TAC[]
  ) THEN
  Q_EXISTS_LEAST_TAC `?m. B_SEM (p (1 + m + k)) c` THEN
  CLEAN_ASSUMPTIONS_TAC THEN


  Q_SPEC_NO_ASSUM 3 `m` THEN
  FULL_SIMP_TAC std_ss [] THENL [
    PROVE_TAC[],
    ALL_TAC,
    METIS_TAC[B_SEM_def]
  ] THEN

  SUBGOAL_TAC `?j'. m + j' = k'` THEN1 (
    `~(k' < m)` by PROVE_TAC[] THEN
    Q_TAC EXISTS_TAC `k' - m` THEN
    DECIDE_TAC
  ) THEN

  Q_SPEC_NO_ASSUM 1 `j'` THEN
  CLEAN_ASSUMPTIONS_TAC THENL [
    ALL_TAC,

    UNDISCH_HD_TAC THEN
    `!n:num. n + j' + (1 + m) + k = n + j` by DECIDE_TAC THEN
    ASM_SIMP_TAC std_ss []
  ] THEN

  ASSUME_TAC S_SEM___EXTEND_RESTRICT_NO_CLOCK_CYCLES THEN
  Q_SPECL_NO_ASSUM 0 [`s2`, `m`, `j'+1`, `1 + k`, `c`, `INFINITE p`] THEN
  PROVE_CONDITION_NO_ASSUM 0 THEN1 (
    ASM_SIMP_TAC arith_ss [ELEM_INFINITE] THEN
    REPEAT STRIP_TAC THEN
    `(l + l'') = 1 + l'' + k` by DECIDE_TAC THEN
    METIS_TAC[B_SEM_def]
  ) THEN

  SUBGOAL_TAC `SEL_REC (j' + 1) (1+k+m) (INFINITE p) =
               SEL_REC (j' + 1) 0 (INFINITE (\n. p (n + (1 + m) + k)))` THEN1 (
      `(1 + k + m) = (0 + (1 + k + m))` by DECIDE_TAC THEN
      ONCE_ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM SEL_REC_RESTN] THEN
      WEAKEN_HD_TAC THEN
      SIMP_TAC arith_ss [RESTN_INFINITE]
  ) THEN
  NTAC 2 (UNDISCH_NO_TAC 1) THEN
  `j' + (m + 1) = l'` by DECIDE_TAC THEN
  ASM_SIMP_TAC arith_ss []
]);



val UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CLOCK_BOOL_BIGCAT =
 store_thm
  ("UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CLOCK_BOOL_BIGCAT",

``(!f:'a fl b c .
   UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE
    (F_CLOCK_COMP c (F_SUFFIX_IMP (S_BOOL_BIGCAT [b], f)))
    (F_W_CLOCK c (F_IMPLIES (F_STRONG_BOOL b,F_CLOCK_COMP c f)))
  ) /\
  (!f:'a fl b1 b2 l c. UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE
    (F_CLOCK_COMP c (F_SUFFIX_IMP (S_BOOL_BIGCAT (b1::b2::l), f)))
    (F_CLOCK_COMP c (F_SUFFIX_IMP (S_BOOL b1, F_WEAK_X (F_SUFFIX_IMP (S_BOOL_BIGCAT (b2::l), f))))))``,

  REPEAT STRIP_TAC THENL [
    SIMP_TAC std_ss [S_BOOL_BIGCAT_def,
      UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CLOCK_BOOL],

    SIMP_TAC std_ss [S_BOOL_BIGCAT_def] THEN
    ASSUME_TAC UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CLOCK_CAT THEN
    Q_SPECL_NO_ASSUM 0 [`S_BOOL b1`, `S_BOOL_BIGCAT (b2::l)`, `f`, `c`] THEN
    PROVE_CONDITION_NO_ASSUM 0 THEN1 (
      SIMP_TAC list_ss [S_SEM_def, S_CLOCK_FREE_def, CLOCK_TICK_def] THEN
      Induct_on `l` THENL [
        SIMP_TAC list_ss [S_SEM_def, S_BOOL_BIGCAT_def, S_CLOCK_FREE_def,
          CLOCK_TICK_def],

        Cases_on `l` THEN
        FULL_SIMP_TAC list_ss [S_SEM_def, S_BOOL_BIGCAT_def, S_CLOCK_FREE_def,
          CLOCK_TICK_def]
      ]
    ) THEN
    ASSUME_TAC UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE___F_SUFFIX_IMP___CLOCK_BOOL THEN
    FULL_SIMP_TAC std_ss [UF_EQUIVALENT___INFINITE_TOP_BOTTOM_FREE_def]
  ]);




val _ = export_theory();
