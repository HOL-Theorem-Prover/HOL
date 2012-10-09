(* =====================================================================
    Theory: GAUGE INTEGRALS
    Description: Generalized gauge intgrals and related theorems
       (ported from the HOL Light theory of the same)

    Email: grace_gwq@163.com
    DATE: 08-10-2012

    Ported by:
      Weiqing Gu, Zhiping Shi, Yong Guan, Shengzhen Jin, Xiaojuan Li

    Beijing Engineering Research Center of High Reliable Embedded System

    College of Information Engineering, Capital Normal University (CNU)
                        Beijing, China
   ===================================================================== *)

(*
app load ["arithmeticTheory","realTheory","transcTheory","limTheory",
          "boolTheory","hol88Lib","numLib","reduceLib","pairTheory","jrhUtils",
          "powserTheory","Diff","mesonLib","RealArith","tautLib","pairLib",
          "seqTheory", "numTheory","prim_recTheory","topologyTheory",
          "netsTheory","PairedLambda", "pred_setTheory"];
*)

open boolTheory powserTheory PairedLambda Diff mesonLib RealArith
     tautLib transcTheory limTheory
     HolKernel Parse bossLib boolLib hol88Lib numLib reduceLib pairLib
     pairTheory arithmeticTheory numTheory prim_recTheory
     jrhUtils realTheory topologyTheory netsTheory seqTheory pred_setTheory;

val _ = new_theory "integral";

val _ = Parse.reveal "B";


(* ------------------------------------------------------------------------ *)
(* Divisions of adjacent intervals can be combined into one                 *)
(* ------------------------------------------------------------------------ *)

(*lemmas about sums*)

val SUM_SPLIT = store_thm("SUM_SPLIT",
  (--`!f n p. sum(m,n) f + sum(m + n,p) f = sum(m,n + p) f`--),
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC(LAND_CONV o LAND_CONV)[SUM_DIFF][] THEN
  GEN_REWRITE_TAC(LAND_CONV o RAND_CONV)[][SUM_DIFF] THEN CONV_TAC SYM_CONV THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_DIFF][] THEN RW_TAC arith_ss[] THEN
  SUBGOAL_THEN(--`!a b c. b-a + (c-b)=c-a`--)
                                (fn th => ONCE_REWRITE_TAC[GEN_ALL th]) THENL
  [REAL_ARITH_TAC, REWRITE_TAC[]]);

val D_tm = Term`\n. if n < dsize D1 then D1(n) else D2(n - dsize D1)`
and p_tm = Term`\n. if n < dsize D1 then (p1:num->real)(n) else p2(n - dsize D1)`;

val DIVISION_APPEND_LEMMA1 = prove(
 Term `!a b c D1 D2.
   division(a,b) D1 /\ division(b,c) D2
    ==>
    (!n. n < dsize D1 + dsize D2
         ==>
         (\n. if n < dsize D1 then D1(n) else D2(n - dsize D1)) (n)
            <
         (\n. if n < dsize D1 then D1(n) else D2(n - dsize D1)) (SUC n)) /\
    (!n. n >= dsize D1 + dsize D2
         ==>
         ((\n. if n<dsize D1 then D1(n) else D2(n - dsize D1)) (n)
           =
          (\n. if n<dsize D1 then D1(n) else D2(n - dsize D1)) (dsize D1 + dsize D2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  X_GEN_TAC (Term`n:num`) THEN DISCH_TAC THEN BETA_TAC THENL
   [ASM_CASES_TAC (Term`SUC n < dsize D1`) THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN (Term`n < dsize D1`) ASSUME_TAC THEN
      ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC n`) THEN
        ASM_REWRITE_TAC[LESS_SUC_REFL],
        UNDISCH_TAC (Term`division(a,b) D1`) THEN REWRITE_TAC[DIVISION_THM] THEN
        STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC],
      ASM_CASES_TAC (Term`n < dsize D1`) THEN ASM_REWRITE_TAC[] THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[NOT_LESS]) THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (Term`b:real`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC DIVISION_UBOUND_LT THEN
          EXISTS_TAC (Term`a:real`) THEN ASM_REWRITE_TAC[],
          MATCH_MP_TAC DIVISION_LBOUND THEN
          EXISTS_TAC (Term`c:real`) THEN ASM_REWRITE_TAC[]],
        UNDISCH_TAC (Term`~(n < dsize D1)`) THEN
        REWRITE_TAC[NOT_LESS] THEN
        DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) SUBST_ALL_TAC o
          REWRITE_RULE[LESS_EQ_EXISTS]) THEN
        REWRITE_TAC[SUB, GSYM NOT_LESS_EQUAL, LESS_EQ_ADD] THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
        FIRST_ASSUM(MATCH_MP_TAC o Lib.trye el 2 o CONJUNCTS o
          REWRITE_RULE[DIVISION_THM]) THEN
        UNDISCH_TAC (Term`dsize D1 + d < dsize D1 + dsize D2`) THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[LESS_MONO_ADD_EQ]]],
    REWRITE_TAC[GSYM NOT_LESS_EQUAL, LESS_EQ_ADD] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
    REWRITE_TAC[NOT_LESS_EQUAL] THEN COND_CASES_TAC THEN
    UNDISCH_TAC (Term`n >= dsize D1 + dsize D2`) THENL
     [CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
      REWRITE_TAC[GREATER_EQ, NOT_LESS_EQUAL] THEN
      MATCH_MP_TAC LESS_IMP_LESS_ADD THEN ASM_REWRITE_TAC[],
      REWRITE_TAC[GREATER_EQ, LESS_EQ_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) SUBST_ALL_TAC) THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[ADD_SUB] THEN
      FIRST_ASSUM(CHANGED_TAC o
       (SUBST1_TAC o MATCH_MP DIVISION_RHS)) THEN
      FIRST_ASSUM(MATCH_MP_TAC o el 3 o CONJUNCTS o
        REWRITE_RULE[DIVISION_THM]) THEN
      REWRITE_TAC[GREATER_EQ, LESS_EQ_ADD]]]);


val DIVISION_APPEND_LEMMA2 = prove(
 Term`!a b c D1 D2.
    division(a,b) D1 /\ division(b,c) D2
      ==>
      (dsize(\n. if n < dsize D1 then D1(n) else D2(n - dsize D1))
         =
       dsize D1 + dsize D2)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [] [dsize] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC (Term`N:num`) THEN BETA_TAC THEN EQ_TAC THENL
   [DISCH_THEN(curry op THEN (MATCH_MP_TAC LESS_EQUAL_ANTISYM) o MP_TAC) THEN
    CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC[DE_MORGAN_THM, NOT_LESS_EQUAL] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [DISJ1_TAC THEN
      DISCH_THEN(MP_TAC o SPEC (Term`dsize D1 + dsize D2`)) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM NOT_LESS_EQUAL, LESS_EQ_ADD] THEN
      SUBGOAL_THEN (Term`!x y. x <= SUC(x + y)`) ASSUME_TAC THENL
       [REPEAT GEN_TAC THEN MATCH_MP_TAC LESS_EQ_TRANS THEN
        EXISTS_TAC (Term`(x:num) + y`) THEN
        REWRITE_TAC[LESS_EQ_ADD, LESS_EQ_SUC_REFL], ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUB, GSYM NOT_LESS_EQUAL] THEN
      REWRITE_TAC[LESS_EQ_ADD] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[ADD_SUB] THEN
      MP_TAC(ASSUME (Term`division(b,c) D2`)) THEN REWRITE_TAC[DIVISION_THM]
      THEN DISCH_THEN(MP_TAC o SPEC (Term`SUC(dsize D2)`) o el 3 o CONJUNCTS)
      THEN REWRITE_TAC[GREATER_EQ, LESS_EQ_SUC_REFL] THEN
      DISCH_THEN SUBST1_TAC THEN
      FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_RHS) THEN
      REWRITE_TAC[REAL_LT_REFL],
      DISJ2_TAC THEN
      DISCH_THEN(MP_TAC o SPEC (Term`dsize D1 + dsize D2`)) THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP LESS_IMP_LESS_OR_EQ) THEN
      ASM_REWRITE_TAC[GREATER_EQ] THEN
      REWRITE_TAC[GSYM NOT_LESS_EQUAL, LESS_EQ_ADD] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
      COND_CASES_TAC THENL
       [SUBGOAL_THEN (Term`D1(N:num) < D2(dsize D2)`) MP_TAC THENL
         [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (Term`b:real`) THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC DIVISION_UBOUND_LT THEN EXISTS_TAC (Term`a:real`) THEN
            ASM_REWRITE_TAC[GSYM NOT_LESS_EQUAL],
            MATCH_MP_TAC DIVISION_LBOUND THEN
            EXISTS_TAC (Term`c:real`) THEN ASM_REWRITE_TAC[]],
          CONV_TAC CONTRAPOS_CONV THEN ASM_REWRITE_TAC[] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LT_REFL]],
        RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
        SUBGOAL_THEN (Term`D2(N - dsize D1) < D2(dsize D2)`) MP_TAC THENL
         [MATCH_MP_TAC DIVISION_LT_GEN THEN
          MAP_EVERY EXISTS_TAC [Term`b:real`, Term`c:real`] THEN
          ASM_REWRITE_TAC[LESS_EQ_REFL] THEN
          REWRITE_TAC[GSYM NOT_LESS_EQUAL] THEN
          REWRITE_TAC[SUB_LEFT_LESS_EQ, DE_MORGAN_THM] THEN
          ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[NOT_LESS_EQUAL] THEN
          UNDISCH_TAC (Term`dsize(D1) <= N`) THEN
          REWRITE_TAC[LESS_EQ_EXISTS] THEN
          DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) SUBST_ALL_TAC) THEN
          RULE_ASSUM_TAC(ONCE_REWRITE_RULE[ADD_SYM]) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[LESS_MONO_ADD_EQ]) THEN
          MATCH_MP_TAC LESS_EQ_LESS_TRANS THEN EXISTS_TAC (Term`d:num`) THEN
          ASM_REWRITE_TAC[ZERO_LESS_EQ],
          CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
          DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LT_REFL]]]],
  DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC (Term`n:num`) THEN DISCH_TAC THEN
    ASM_CASES_TAC (Term`SUC n < dsize D1`) THEN
    ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN (Term`n < dsize D1`) ASSUME_TAC THENL
       [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC n`) THEN
        ASM_REWRITE_TAC[LESS_SUC_REFL], ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIVISION_LT_GEN THEN
      MAP_EVERY EXISTS_TAC [Term`a:real`, Term`b:real`] THEN
      ASM_REWRITE_TAC[LESS_SUC_REFL] THEN
      MATCH_MP_TAC LESS_IMP_LESS_OR_EQ THEN ASM_REWRITE_TAC[],
      COND_CASES_TAC THENL
           [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC (Term`b:real`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC DIVISION_UBOUND_LT THEN EXISTS_TAC (Term`a:real`) THEN
          ASM_REWRITE_TAC[],
          FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP DIVISION_LBOUND)],
        MATCH_MP_TAC DIVISION_LT_GEN THEN
        MAP_EVERY EXISTS_TAC [Term`b:real`, Term`c:real`] THEN
        ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[SUB, LESS_SUC_REFL], ALL_TAC] THEN
        REWRITE_TAC[REWRITE_RULE[GREATER_EQ] SUB_LEFT_GREATER_EQ] THEN
        ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[GSYM LESS_EQ]]],
    X_GEN_TAC (Term`n:num`) THEN REWRITE_TAC[GREATER_EQ] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM NOT_LESS_EQUAL,LESS_EQ_ADD] THEN
    SUBGOAL_THEN (Term`dsize D1 <= n`) ASSUME_TAC THENL
     [MATCH_MP_TAC LESS_EQ_TRANS THEN
      EXISTS_TAC (Term `dsize D1 + dsize D2`) THEN
      ASM_REWRITE_TAC[LESS_EQ_ADD],
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[ADD_SUB] THEN
      FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_RHS) THEN
      FIRST_ASSUM(MATCH_MP_TAC o el 3 o
        CONJUNCTS o REWRITE_RULE[DIVISION_THM]) THEN
      REWRITE_TAC[GREATER_EQ, SUB_LEFT_LESS_EQ] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]]]]);


val DIVISION_APPEND_EXPLICIT = store_thm("DIVISION_APPEND_EXPLICIT",
 ``!a b c g d1 p1 d2 p2.
        tdiv(a,b) (d1,p1) /\
        fine g (d1,p1) /\
        tdiv(b,c) (d2,p2) /\
        fine g (d2,p2)
        ==> tdiv(a,c)
              ((\n. if n < dsize d1 then  d1(n) else d2(n - (dsize d1))),
               (\n. if n < dsize d1
                    then p1(n) else p2(n - (dsize d1)))) /\
            fine g ((\n. if n < dsize d1 then  d1(n) else d2(n - (dsize d1))),
               (\n. if n < dsize d1
                    then p1(n) else p2(n - (dsize d1)))) /\
            !f. rsum((\n. if n < dsize d1 then  d1(n) else d2(n - (dsize d1))),
                     (\n. if n < dsize d1
                          then p1(n) else p2(n - (dsize d1)))) f =
                rsum(d1,p1) f + rsum(d2,p2) f``,
  MAP_EVERY X_GEN_TAC
   [Term`a:real`, Term`b:real`, Term`c:real`, Term`g:real->real`,
    Term`D1:num->real`, Term`p1:num->real`, Term`D2:num->real`,
    Term`p2:num->real`] THEN
  STRIP_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [DISJ_CASES_TAC(GSYM (SPEC (--`dsize(D1)`--) LESS_0_CASES)) THENL
    [ASM_REWRITE_TAC[NOT_LESS_0, SUB_0] THEN
         CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
         SUBGOAL_THEN (--`a:real = b`--) (fn th => ASM_REWRITE_TAC[th]) THEN
         MP_TAC(SPECL [Term`D1:num->real`,Term`a:real`,Term`b:real`]
                        DIVISION_EQ) THEN
         RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
         CONJ_TAC THENL
          [ALL_TAC,
           REWRITE_TAC[fine] THEN X_GEN_TAC (Term`n:num`) THEN
           RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN
           MP_TAC(SPECL [Term`a:real`, Term`b:real`, Term`c:real`,
                  Term`D1:num->real`, Term`D2:num->real`]
                                  DIVISION_APPEND_LEMMA2) THEN
           ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
           BETA_TAC THEN DISCH_TAC THEN ASM_CASES_TAC (Term`SUC n < dsize D1`) THEN
           ASM_REWRITE_TAC[] THENL
            [SUBGOAL_THEN (Term`n < dsize D1`) ASSUME_TAC THENL
                 [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC n`) THEN
                  ASM_REWRITE_TAC[LESS_SUC_REFL], ALL_TAC] THEN
                  ASM_REWRITE_TAC[] THEN
          FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[fine]) THEN
          ASM_REWRITE_TAC[],ALL_TAC] THEN
        ASM_CASES_TAC (Term`n < dsize D1`) THEN ASM_REWRITE_TAC[] THENL
         [SUBGOAL_THEN (Term`SUC n = dsize D1`) ASSUME_TAC THENL
           [MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN
            ASM_REWRITE_TAC[GSYM NOT_LESS] THEN
            REWRITE_TAC[NOT_LESS] THEN MATCH_MP_TAC LESS_OR THEN
                ASM_REWRITE_TAC[],
            ASM_REWRITE_TAC[SUB_EQUAL_0] THEN
            FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_LHS o
              CONJUNCT1) THEN
            FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o SYM o
              MATCH_MP DIVISION_RHS o CONJUNCT1) THEN
            SUBST1_TAC(SYM(ASSUME (Term`SUC n = dsize D1`))) THEN
            FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[fine]) THEN
            ASM_REWRITE_TAC[]],
          ASM_REWRITE_TAC[SUB] THEN UNDISCH_TAC (Term`~(n < (dsize D1))`) THEN
          REWRITE_TAC[LESS_EQ_EXISTS, NOT_LESS] THEN
          DISCH_THEN(X_CHOOSE_THEN (Term`d:num`) SUBST_ALL_TAC) THEN
          ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
          FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[fine]) THEN
          RULE_ASSUM_TAC(ONCE_REWRITE_RULE[ADD_SYM]) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[LESS_MONO_ADD_EQ]) THEN
          FIRST_ASSUM ACCEPT_TAC]] THEN
  REWRITE_TAC[tdiv] THEN BETA_TAC THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN
    REWRITE_TAC[DIVISION_THM] THEN CONJ_TAC THENL
         [BETA_TAC THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC DIVISION_LHS THEN EXISTS_TAC (--`b:real`--) THEN
          ASM_REWRITE_TAC[], ALL_TAC] THEN
        SUBGOAL_THEN (--`c = (\n. if (n < (dsize D1)) then  D1(n) else D2(n -
                  (dsize D1))) (dsize(D1) + dsize(D2))`--) SUBST1_TAC THENL
         [BETA_TAC THEN REWRITE_TAC[GSYM NOT_LESS_EQUAL, LESS_EQ_ADD] THEN
         ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB] THEN
         CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIVISION_RHS THEN
         EXISTS_TAC (Term`b:real`) THEN ASM_REWRITE_TAC[], ALL_TAC] THEN
        MP_TAC(SPECL [Term`a:real`, Term`b:real`, Term`c:real`,
                  Term`D1:num->real`, Term`D2:num->real`]
                                  DIVISION_APPEND_LEMMA2) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fn th => REWRITE_TAC[th]) THEN
        MATCH_MP_TAC DIVISION_APPEND_LEMMA1 THEN
        MAP_EVERY EXISTS_TAC [Term`a:real`, Term`b:real`, Term`c:real`] THEN
        ASM_REWRITE_TAC[], ALL_TAC] THEN
  X_GEN_TAC (Term`n:num`) THEN RULE_ASSUM_TAC(REWRITE_RULE[tdiv]) THEN
  ASM_CASES_TAC (Term`SUC n < dsize D1`) THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN (Term`n < dsize D1`) ASSUME_TAC THENL
         [MATCH_MP_TAC LESS_TRANS THEN EXISTS_TAC (Term`SUC n`) THEN
          ASM_REWRITE_TAC[LESS_SUC_REFL], ALL_TAC] THEN
          ASM_REWRITE_TAC[],ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[SUB] THEN
    FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o MATCH_MP DIVISION_LHS o
          CONJUNCT1) THEN
        FIRST_ASSUM(CHANGED_TAC o SUBST1_TAC o SYM o
          MATCH_MP DIVISION_RHS o  CONJUNCT1) THEN
        SUBGOAL_THEN (Term`dsize D1 = SUC n`) (fn th => ASM_REWRITE_TAC[th]) THEN
        MATCH_MP_TAC LESS_EQUAL_ANTISYM THEN
        ASM_REWRITE_TAC[GSYM NOT_LESS] THEN REWRITE_TAC[NOT_LESS] THEN
        MATCH_MP_TAC LESS_OR THEN ASM_REWRITE_TAC[],
        ASM_REWRITE_TAC[SUB]],
 GEN_TAC THEN REWRITE_TAC[rsum] THEN
   SUBGOAL_THEN(Term`(dsize(\n. if n < dsize D1 then D1 n else D2(n- dsize D1))
      = dsize D1 + dsize D2)`)MP_TAC THENL
        [UNDISCH_TAC(Term`tdiv(a,b)(D1,p1)`) THEN
         UNDISCH_TAC(Term`tdiv(b,c)(D2,p2)`) THEN
         REWRITE_TAC[tdiv] THEN REPEAT STRIP_TAC THEN
         MP_TAC(SPECL [Term`a:real`, Term`b:real`, Term`c:real`,
                   Term`D1:num->real`, Term`D2:num->real`]
                                   DIVISION_APPEND_LEMMA2) THEN
         PROVE_TAC[],
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM SUM_SPLIT] THEN
        REWRITE_TAC[SUM_REINDEX] THEN BINOP_TAC THENL
         [MATCH_MP_TAC SUM_EQ THEN SIMP_TAC pure_ss[ADD_CLAUSES] THEN
          RW_TAC arith_ss[ETA_AX] THEN
          SUBGOAL_THEN(Term`dsize D1 = SUC r`)MP_TAC THENL
           [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LESS] THEN
            REWRITE_TAC[LESS_EQ] THEN RW_TAC arith_ss[], DISCH_TAC THEN
                ASM_SIMP_TAC arith_ss[] THEN UNDISCH_TAC(Term`tdiv(a,b)(D1,p1)`) THEN
                UNDISCH_TAC(Term`tdiv(b,c)(D2,p2)`) THEN REWRITE_TAC[tdiv] THEN
                REWRITE_TAC[DIVISION_THM] THEN REPEAT STRIP_TAC THEN
                ASM_REWRITE_TAC[] THEN
                SUBGOAL_THEN(Term`D1(SUC r) - D1 r = D1(dsize D1) - D1 r`)MP_TAC THENL
                 [PROVE_TAC[], ASM_SIMP_TAC arith_ss[]]],
         ASM_SIMP_TAC arith_ss[GSYM ADD]]]]);

val DIVISION_APPEND_STRONG = store_thm("DIVISION_APPEND_STRONG",
  ``!a b c D1 p1 D2 p2.
        tdiv(a,b) (D1,p1) /\ fine(g) (D1,p1) /\
        tdiv(b,c) (D2,p2) /\ fine(g) (D2,p2)
        ==> ?D p. tdiv(a,c) (D,p) /\ fine(g) (D,p) /\
                  !f. rsum(D,p) f = rsum(D1,p1) f + rsum(D2,p2) f``,
  REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
   [Term`\n. if n < dsize D1 then D1(n):real else D2(n - (dsize D1))`,
    Term`\n. if n < dsize D1 then p1(n):real else p2(n - (dsize D1))`] THEN
  MATCH_MP_TAC DIVISION_APPEND_EXPLICIT THEN ASM_MESON_TAC[]);

  val DIVISION_APPEND = store_thm("DIVISION_APPEND",
  ``!a b c.
      (?D1 p1. tdiv(a,b) (D1,p1) /\ fine(g) (D1,p1)) /\
      (?D2 p2. tdiv(b,c) (D2,p2) /\ fine(g) (D2,p2)) ==>
        ?D p. tdiv(a,c) (D,p) /\ fine(g) (D,p)``,
  MESON_TAC[DIVISION_APPEND_STRONG]);


(* ------------------------------------------------------------------------- *)
(* Definition of integral and integrability.                                 *)
(* ------------------------------------------------------------------------- *)

val integrable = Define`integrable(a,b) f = ?i. Dint(a,b) f i`;

val integral = Define`integral(a,b) f = @i. Dint(a,b) f i`;

val INTEGRABLE_DINT = store_thm("INTEGRABLE_DINT",
 (--`!f a b. integrable(a,b) f ==> Dint(a,b) f (integral(a,b) f)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[integrable, integral] THEN
  CONV_TAC(RAND_CONV SELECT_CONV) THEN REWRITE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Other more or less trivial lemmas.                                        *)
(* ------------------------------------------------------------------------- *)

val DIVISION_BOUNDS = store_thm("DIVISION_BOUNDS",
 (--`!d a b. division(a,b) d ==> !n. a <= d(n) /\ d(n) <= b`--),
  MESON_TAC[DIVISION_UBOUND, DIVISION_LBOUND]);

val TDIV_BOUNDS = store_thm("TDIV_BOUNDS",
 (--`!d p a b. tdiv(a,b) (d,p)
             ==> !n. a <= d(n) /\ d(n) <= b /\ a <= p(n) /\ p(n) <= b`--),
  REWRITE_TAC[tdiv] THEN ASM_MESON_TAC[DIVISION_BOUNDS, REAL_LE_TRANS]);

val TDIV_LE = store_thm("TDIV_LE",
 (--`!d p a b. tdiv(a,b) (d,p) ==> a <= b`--),
  MESON_TAC[tdiv, DIVISION_LE]);

val DINT_WRONG = store_thm("DINT_WRONG",
 (--`!a b f i. b < a ==> Dint(a,b) f i`--),
  REWRITE_TAC[Dint, gauge] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC (--`\x:real. &0`--) THEN
  ASM_SIMP_TAC std_ss[REAL_ARITH ``b < a ==> (a <= x /\ x <= b <=> F)``] THEN
  ASM_MESON_TAC[REAL_NOT_LE, TDIV_LE]);

val DINT_INTEGRAL = store_thm("DINT_INTEGRAL",
 (--`!f a b i. a <= b /\ Dint(a,b) f i ==> (integral(a,b) f = i)`--),
  REPEAT STRIP_TAC THEN REWRITE_TAC[integral] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[DINT_UNIQ]);

(* ------------------------------------------------------------------------- *)
(* Linearity.                                                                *)
(* ------------------------------------------------------------------------- *)

val DINT_NEG = store_thm("DINT_NEG",
 (--`!f a b i. Dint(a,b) f i ==> Dint(a,b) (\x. ~f x) (~i)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[Dint] THEN
  SIMP_TAC arith_ss[rsum, REAL_MUL_LNEG, SUM_NEG] THEN
  SIMP_TAC arith_ss[REAL_SUB_LNEG, ABS_NEG, real_sub]);

val DINT_0 = store_thm("DINT_0",
 (--`!a b. Dint(a,b) (\x. &0) (&0)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[Dint] THEN GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC (Term`\x:real. &1`) THEN REWRITE_TAC[gauge,REAL_LT_01] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  REWRITE_TAC[rsum, REAL_MUL_LZERO, SUM_0, ABS_0] THEN RW_TAC arith_ss[]);

val DINT_ADD = store_thm("DINT_ADD",
(--`!f g a b i j.
        Dint(a,b) f i /\ Dint(a,b) g j
        ==> Dint(a,b) (\x. f x + g x) (i + j)`--),
        REPEAT GEN_TAC THEN REWRITE_TAC[Dint] THEN STRIP_TAC THEN
        X_GEN_TAC (Term`e:real`) THEN DISCH_TAC THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC ``e / &2``)) THEN
        ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
        DISCH_THEN(X_CHOOSE_THEN (Term`g1:real->real`) STRIP_ASSUME_TAC) THEN
        DISCH_THEN(X_CHOOSE_THEN (Term`g2:real->real`) STRIP_ASSUME_TAC) THEN
        EXISTS_TAC (--`\x:real. if g1(x) < g2(x) then g1(x) else g2(x)`--) THEN
        ASM_SIMP_TAC arith_ss[GAUGE_MIN, rsum] THEN REPEAT STRIP_TAC THEN
        SIMP_TAC arith_ss[REAL_ADD_RDISTRIB, SUM_ADD] THEN
        SIMP_TAC arith_ss[REAL_ADD2_SUB2] THEN REWRITE_TAC[GSYM rsum] THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FINE_MIN) THEN
        REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPECL [Term`D:num->real`, Term`p:num->real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
        SUBGOAL_THEN (Term`abs(rsum(D,p) f -i) + abs(rsum(D,p) g - j) < e`)
                MP_TAC THENL
         [GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_HALF_DOUBLE] THEN
          MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[],
          STRIP_TAC THEN
          KNOW_TAC``abs (rsum (D,p) f - i + (rsum (D,p) g - j)) <=
          abs (rsum (D,p) f - i) + abs (rsum (D,p) g - j) /\ (abs (rsum (D,p) f - i) +
          abs (rsum (D,p) g - j)< e)`` THENL
           [CONJ_TAC THEN REWRITE_TAC[ABS_TRIANGLE], ASM_REWRITE_TAC[]]
            THEN PROVE_TAC [REAL_LET_TRANS]]);

val DINT_SUB = store_thm("DINT_SUB",
 (--`!f g a b i j.
        Dint(a,b) f i /\ Dint(a,b) g j
        ==> Dint(a,b) (\x. f x - g x) (i - j)`--),
  SIMP_TAC arith_ss[real_sub, DINT_ADD, DINT_NEG]);

val DSIZE_EQ = store_thm("DSIZE_EQ",
(--`!a b D. division(a,b) D ==>
        (sum(0,dsize D)(\n. D(SUC n) - D n) - (b - a) = 0)`--),
  REPEAT GEN_TAC THEN STRIP_TAC THEN SIMP_TAC arith_ss[SUM_CANCEL] THEN
  RW_TAC arith_ss[REAL_SUB_0] THEN MP_TAC DIVISION_LHS THEN
  MP_TAC DIVISION_RHS THEN PROVE_TAC []);

val DINT_CONST = store_thm("DINT_CONST",
 (--`!a b c. Dint(a,b) (\x. c) (c * (b - a))`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[Dint] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC (Term`\x:real. &1`) THEN REWRITE_TAC[gauge,REAL_LT_01] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[rsum] THEN
  SIMP_TAC arith_ss[SUM_CMUL] THEN
  SIMP_TAC arith_ss[GSYM REAL_SUB_LDISTRIB] THEN REWRITE_TAC[ABS_MUL] THEN
  UNDISCH_TAC(Term`tdiv(a,b)(D,p)`) THEN REWRITE_TAC[tdiv] THEN
  STRIP_TAC THEN UNDISCH_TAC(Term`division(a,b) D`) THEN
  SIMP_TAC arith_ss[DSIZE_EQ] THEN REWRITE_TAC[ABS_0] THEN STRIP_TAC THEN
  RW_TAC arith_ss[REAL_MUL_RZERO]);

val DINT_CMUL = store_thm("DINT_CMUL",
(--`!f a b c i. Dint(a,b) f i ==> Dint(a,b) (\x. c * f x) (c * i)`--),
  REPEAT GEN_TAC THEN ASM_CASES_TAC (Term`c = &0`) THENL
   [MP_TAC(SPECL [Term`a:real`, Term`b:real`, Term`c:real`] DINT_CONST) THEN
    ASM_SIMP_TAC arith_ss[REAL_MUL_LZERO],
        REWRITE_TAC[Dint] THEN STRIP_TAC THEN X_GEN_TAC(Term`e:real`) THEN
        DISCH_TAC THEN  FIRST_X_ASSUM(MP_TAC o SPEC (--`e / abs(c)`--)) THEN
        SUBGOAL_THEN(Term`0 < abs(c)`) MP_TAC THENL
         [UNDISCH_TAC(Term`c<>0`) THEN SIMP_TAC arith_ss[ABS_NZ],
          ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN STRIP_TAC THEN
          DISCH_THEN(X_CHOOSE_THEN (Term`g1:real->real`) STRIP_ASSUME_TAC) THEN
          EXISTS_TAC(--`g1:real->real`--) THEN ASM_SIMP_TAC arith_ss[] THEN
          REPEAT STRIP_TAC THEN REWRITE_TAC[rsum] THEN
          RW_TAC arith_ss[ETA_AX] THEN
          SUBGOAL_THEN(--`!a b c d. a*b*(c-d) = a*(b*(c-d))`--)
                (fn th => ONCE_REWRITE_TAC[GEN_ALL th]) THENL
           [RW_TAC arith_ss[GSYM REAL_MUL_ASSOC],
            SIMP_TAC arith_ss[SUM_CMUL] THEN
                SIMP_TAC arith_ss[GSYM REAL_SUB_LDISTRIB] THEN REWRITE_TAC[ABS_MUL] THEN
                REWRITE_TAC[GSYM rsum] THEN
                REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
                DISCH_THEN(MP_TAC o SPECL [Term`D:num->real`, Term`p:num->real`]) THEN
                ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
                POP_ASSUM MP_TAC THEN UNDISCH_TAC(Term`0 < abs c`) THEN
                RW_TAC arith_ss[REAL_LT_RDIV_EQ] THEN PROVE_TAC[REAL_MUL_SYM]]]]);

val DINT_LINEAR = store_thm("DINT_LINEAR",
  ``!f g a b i j.
        Dint(a,b) f i /\ Dint(a,b) g j
        ==> Dint(a,b) (\x. m*(f x) + n*(g x)) (m*i + n*j)``,
  REPEAT STRIP_TAC THEN HO_MATCH_MP_TAC DINT_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC DINT_CMUL THEN ASM_REWRITE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Ordering properties of integral.                                          *)
(* ------------------------------------------------------------------------- *)

(*Auxiliary lemmas.*)
val LT = store_thm("LT",
  ``(!(m:num). m < 0 = F) /\ (!m n. m < SUC n = ((m = n) \/ m < n))``,
  SIMP_TAC arith_ss[ZERO_LESS_EQ, LESS_OR_EQ]);

val LE_0 = store_thm ("LE_0",``!(n:num). 0 <= n``,
      INDUCT_TAC THEN ASM_REWRITE_TAC[LE]);

val LT_0 = store_thm("LT_0",``!(n:num). 0 < SUC n``,
      SIMP_TAC arith_ss[SUC_ONE_ADD]);
val EQ_SUC = store_thm("EQ_SUC", ``!(m:num) (n:num). (SUC m = SUC n) = (m = n)``,
        SIMP_TAC arith_ss[]);

val LE_LT = store_thm("LE_LT",
        ``!(m:num) (n:num). (m <= n) <=> (m < n) \/ (m = n)``,
        REPEAT INDUCT_TAC THEN
        ASM_SIMP_TAC arith_ss[LESS_EQ_MONO, LESS_MONO_EQ, EQ_SUC, ZERO_LESS_EQ, LT_0]
        THEN REWRITE_TAC[LE, LT]);

val LT_LE = store_thm("LT_LE",
        ``!(m:num) (n:num). (m < n) <=> (m <= n) /\ ~(m = n)``,
        REWRITE_TAC[LE_LT] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
         [DISCH_TAC THEN ASM_SIMP_TAC arith_ss[],
          DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
          ASM_REWRITE_TAC[]]);

val REAL_LT_MIN = store_thm("REAL_LT_MIN",
  ``!x y z. z < min x y <=> z < x /\ z < y``,
  RW_TAC boolSimps.bool_ss [min_def] THENL [PROVE_TAC[REAL_LTE_TRANS],
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN PROVE_TAC[REAL_LT_TRANS]]);

val REAL_LE_RMUL1 = store_thm("REAL_LE_RMUL1",
  ``!x y z. x <= y /\ &0 <= z ==> x * z <= y * z``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  REWRITE_TAC[GSYM REAL_SUB_RDISTRIB, REAL_SUB_RZERO, REAL_LE_MUL]);

val REAL_LE_LMUL1 = store_thm("REAL_LE_LMUL1",
  ``!x y z. &0 <= x /\ y <= z ==> x * y <= x * z``,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB, REAL_SUB_RZERO, REAL_LE_MUL]);

val INTEGRAL_LE = store_thm("INTEGRAL_LE",
  ``!f g a b i j.
        a <= b /\ integrable(a,b) f /\ integrable(a,b) g /\
        (!x. a <= x /\ x <= b ==> f(x) <= g(x))
        ==> integral(a,b) f <= integral(a,b) g``,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP INTEGRABLE_DINT)) THEN
  MATCH_MP_TAC(REAL_ARITH ``~(&0 < x - y) ==> x <= y``) THEN
  ABBREV_TAC ``e = integral(a,b) f - integral(a,b) g`` THEN DISCH_TAC THEN
  NTAC 2(FIRST_X_ASSUM(MP_TAC o SPEC ``e / &2`` o REWRITE_RULE [Dint])) THEN
  ASM_REWRITE_TAC[REAL_LT_HALF1] THEN
  DISCH_THEN(X_CHOOSE_THEN ``g1:real->real`` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN ``g2:real->real`` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [Term`\x. a <= x /\ x <= b`,
                                Term`g1:real->real`, Term`g2:real->real`] GAUGE_MIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [``a:real``, ``b:real``,
                ``\x:real. if g1(x) < g2(x) then g1(x) else g2(x)``]
               DIVISION_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN (Term`D:num->real`)
     (X_CHOOSE_THEN(Term`p:num->real`) STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FINE_MIN) THEN
  REPEAT(FIRST_ASSUM(UNDISCH_TAC o assert is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPECL [Term`D:num->real`, Term`p:num->real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  SUBGOAL_THEN (Term`abs((rsum(D,p) g - integral(a,b) g) -
                                (rsum(D,p) f - integral(a,b) f)) < e`) MP_TAC THENL
        [MATCH_MP_TAC REAL_LET_TRANS THEN
         EXISTS_TAC (Term`abs(rsum(D,p) g - integral(a,b) g) +
                                abs(rsum(D,p) f - integral(a,b) f)`) THEN
         CONJ_TAC THENL
          [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [] [real_sub] THEN
           GEN_REWRITE_TAC (funpow 2 RAND_CONV) [] [GSYM ABS_NEG] THEN
           MATCH_ACCEPT_TAC ABS_TRIANGLE,
           GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_HALF_DOUBLE] THEN
           MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]],
         REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEG_SUB] THEN
         ONCE_REWRITE_TAC[AC (REAL_ADD_ASSOC,REAL_ADD_SYM)
      (Term`(a + b) + (c + d) = (d + a) + (c + b)`)] THEN
         REWRITE_TAC[GSYM real_sub] THEN ASM_REWRITE_TAC[] THEN
         ONCE_REWRITE_TAC[GSYM ABS_NEG] THEN
         REWRITE_TAC[real_sub, REAL_NEG_ADD, REAL_NEGNEG] THEN
         REWRITE_TAC[GSYM real_sub] THEN DISCH_TAC THEN
         SUBGOAL_THEN``0<rsum(D,p) f - rsum(D,p) g``MP_TAC THENL
           [PROVE_TAC[ABS_SIGN], REWRITE_TAC[] THEN
            ONCE_REWRITE_TAC[REAL_NOT_LT] THEN REWRITE_TAC[real_sub] THEN
                ONCE_REWRITE_TAC[GSYM REAL_LE_RNEG] THEN REWRITE_TAC[REAL_NEGNEG] THEN
                REWRITE_TAC[rsum] THEN MATCH_MP_TAC SUM_LE THEN
                X_GEN_TAC``r:num`` THEN REWRITE_TAC[ADD_CLAUSES] THEN
                STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC REAL_LE_RMUL1 THEN
                REWRITE_TAC[REAL_SUB_LE] THEN
                ASM_MESON_TAC[TDIV_BOUNDS, REAL_LT_IMP_LE, DIVISION_THM, tdiv]]]);

val DINT_LE = store_thm("DINT_LE",
  ``!f g a b i j. a <= b /\ Dint(a,b) f i /\ Dint(a,b) g j /\
                 (!x. a <= x /\ x <= b ==> f(x) <= g(x))
                 ==> i <= j``,
  REPEAT GEN_TAC THEN MP_TAC(SPEC_ALL INTEGRAL_LE) THEN
  MESON_TAC[integrable, DINT_INTEGRAL]);

 val DINT_TRIANGLE = store_thm("DINT_TRIANGLE",
  ``!f a b i j. a <= b /\ Dint(a,b) f i /\ Dint(a,b) (\x. abs(f x)) j
               ==> abs(i) <= j``,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH``~a <= b /\ b <= a ==> abs(b) <= a``) THEN
  CONJ_TAC THEN MATCH_MP_TAC DINT_LE THENL
   [MAP_EVERY EXISTS_TAC [``\x:real. ~abs(f x)``, ``f:real->real``],
        MAP_EVERY EXISTS_TAC [``f:real->real``, ``\x:real. abs(f x)``]] THEN
        MAP_EVERY EXISTS_TAC [``a:real``, ``b:real``] THEN
        ASM_SIMP_TAC arith_ss[DINT_NEG] THEN REAL_ARITH_TAC);

val DINT_EQ = store_thm("DINT_EQ",
  ``!f g a b i j. a <= b /\ Dint(a,b) f i /\ Dint(a,b) g j /\
                 (!x. a <= x /\ x <= b ==> (f(x) = g(x)))
                 ==> (i = j)``,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN MESON_TAC[DINT_LE]);

val INTEGRAL_EQ = store_thm("INTEGRAL_EQ",
  ``!f g a b i. Dint(a,b) f i /\
               (!x. a <= x /\ x <= b ==> (f(x) = g(x)))
               ==> Dint(a,b) g i``,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC ``a <= b`` THENL
   [UNDISCH_TAC``Dint(a,b) f i`` THEN REWRITE_TAC[Dint] THEN
        HO_MATCH_MP_TAC MONO_ALL THEN X_GEN_TAC ``e:real`` THEN
        ASM_CASES_TAC ``&0 < e`` THEN ASM_REWRITE_TAC[] THEN
        HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``d:real->real`` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_REWRITE_TAC[] THEN
        HO_MATCH_MP_TAC MONO_ALL THEN X_GEN_TAC ``D:num->real`` THEN
        HO_MATCH_MP_TAC MONO_ALL THEN X_GEN_TAC ``p:num->real`` THEN
        DISCH_THEN(fn th => STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH ``(x = y) ==> (abs(x - i) < e) ==>
                                                                (abs(y - i) < e)``) THEN
        REWRITE_TAC[rsum] THEN MATCH_MP_TAC SUM_EQ THEN
        REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN BETA_TAC THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC[tdiv, DIVISION_LBOUND, DIVISION_UBOUND,
                                        DIVISION_THM, REAL_LE_TRANS],
        ASM_MESON_TAC[REAL_NOT_LE, DINT_WRONG]]);

(* ------------------------------------------------------------------------- *)
(* Integration by parts.                                                     *)
(* ------------------------------------------------------------------------- *)

val INTEGRATION_BY_PARTS = store_thm("INTEGRATION_BY_PARTS",
  ``!f g f' g' a b.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        (!x. a <= x /\ x <= b ==> (g diffl g'(x))(x))
        ==> Dint(a,b) (\x. f'(x) * g(x) + f(x) * g'(x))
                        (f(b) * g(b) - f(a) * g(a))``,
  REPEAT STRIP_TAC THEN HO_MATCH_MP_TAC FTC1 THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH ``a + b * c = a + c * b``] THEN
  ASM_SIMP_TAC arith_ss[DIFF_MUL]);

 (* ------------------------------------------------------------------------- *)
(* Various simple lemmas about divisions.                                    *)
(* ------------------------------------------------------------------------- *)

val DIVISION_LE_SUC = store_thm("DIVISION_LE_SUC",
 (--`!d a b. division(a,b) d ==> !n. d(n) <= d(SUC n)`--),
  REWRITE_TAC[DIVISION_THM, GREATER_EQ] THEN
  MESON_TAC[LESS_CASES, LE, REAL_LE_REFL, REAL_LT_IMP_LE]);

val DIVISION_MONO_LE = store_thm("DIVISION_MONO_LE",
  ``!d a b. division(a,b) d ==> !m n. m <= n ==> d(m) <= d(n)``,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP DIVISION_LE_SUC) THEN
  SIMP_TAC arith_ss[LESS_EQ_EXISTS] THEN GEN_TAC THEN
  SIMP_TAC arith_ss[GSYM LEFT_FORALL_IMP_THM] THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES, REAL_LE_REFL] THEN REWRITE_TAC[GSYM ADD_SUC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC(Term`(d:num ->real)(m + p)`) THEN ASM_REWRITE_TAC[]);

val DIVISION_MONO_LE_SUC = store_thm("DIVISION_MONO_LE_SUC",
  ``!d a b. division(a,b) d ==> !n. d(n) <= d(SUC n)``,
  MESON_TAC[DIVISION_MONO_LE, LE, LESS_EQ_REFL]);

val DIVISION_DSIZE_LE = store_thm("DIVISION_DSIZE_LE",
  ``!a b d n. division(a,b) d /\ (d(SUC n) = d(n)) ==> (dsize d <= n)``,
  REWRITE_TAC[DIVISION_THM] THEN MESON_TAC[REAL_LT_REFL, NOT_LESS]);

val DIVISION_DSIZE_GE = store_thm("DIVISION_DSIZE_GE",
  ``!a b d n. division(a,b) d /\ d(n) < d(SUC n) ==> SUC n <= dsize d``,
  REWRITE_TAC[DIVISION_THM, GSYM LESS_EQ, GREATER_EQ] THEN
  MESON_TAC[REAL_LT_REFL, LE, NOT_LESS]);

val DIVISION_DSIZE_EQ = store_thm("DIVISION_DSIZE_EQ",
  ``!a b d n. division(a,b) d /\ (d(n) < d(SUC n)) /\ (d(SUC(SUC n)) = d(SUC n))
           ==> (dsize d = SUC n)``,
  REWRITE_TAC[EQ_LESS_EQ] THEN MESON_TAC[DIVISION_DSIZE_LE, DIVISION_DSIZE_GE]);

val DIVISION_DSIZE_EQ_ALT = store_thm("DIVISION_DSIZE_EQ_ALT",
  ``!a b d n. division(a,b) d /\ (d(SUC n) = d(n)) /\
             (!i. i < n ==> (d(i) < d(SUC i)))
             ==> (dsize d = n)``,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [SUBGOAL_THEN(Term`dsize d <=0 ==> (dsize d = 0)`)MP_TAC THENL
    [ASM_MESON_TAC[DIVISION_DSIZE_LE, DIVISION_DSIZE_GE, LE],
         MESON_TAC[DIVISION_DSIZE_LE]], REPEAT STRIP_TAC THEN
         REWRITE_TAC[EQ_LESS_EQ] THEN
         ASM_MESON_TAC[DIVISION_DSIZE_LE, DIVISION_DSIZE_GE, LT]]);


val num_MAX = store_thm("num_MAX",
  ``!P. (?(x:num). P x) /\ (?(M:num). !x. P x ==> x <= M) <=>
       ?m. P m /\ (!x. P x ==> x <= m)``,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    SUBGOAL_THEN
     (Term`(?(M:num). !(x:num). P x ==> x <= M) =
         (?M. (\M. !x. P x ==> x <= M) M)`) SUBST1_TAC THENL
         [BETA_TAC THEN REFL_TAC,
          DISCH_THEN (MP_TAC o MATCH_MP WOP) THEN
          BETA_TAC THEN CONV_TAC (DEPTH_CONV NOT_FORALL_CONV) THEN
          STRIP_TAC THEN EXISTS_TAC ``n:num`` THEN ASM_REWRITE_TAC[] THEN
          NTAC 2 (POP_ASSUM MP_TAC) THEN
          STRUCT_CASES_TAC (SPEC (Term`n:num`) num_CASES) THEN
          REPEAT STRIP_TAC THENL
          [UNDISCH_THEN (Term`!(x:num). P x ==> x <= (0:num)`)
            (MP_TAC o CONV_RULE (ONCE_DEPTH_CONV CONTRAPOS_CONV)) THEN
            REWRITE_TAC[NOT_LESS_EQUAL] THEN STRIP_TAC THEN
            POP_ASSUM(MP_TAC o CONV_RULE (ONCE_DEPTH_CONV CONTRAPOS_CONV)) THEN
            REWRITE_TAC[] THEN STRIP_TAC THEN RES_TAC THEN
            MP_TAC (SPEC (Term`x:num`) LESS_0_CASES) THEN
            ASM_REWRITE_TAC[] THEN DISCH_THEN (SUBST_ALL_TAC o SYM) THEN
            ASM_REWRITE_TAC[],
            POP_ASSUM (MP_TAC o SPEC (Term`n':num`)) THEN
                REWRITE_TAC [prim_recTheory.LESS_SUC_REFL] THEN
                SUBGOAL_THEN (Term`!x y. ~(x ==> y) = x /\ ~y`)
               (fn th => REWRITE_TAC[th] THEN STRIP_TAC) THENL
                 [REWRITE_TAC [NOT_IMP],
                  UNDISCH_THEN (Term`!(x:num). P x ==> x <= SUC n'`)
                        (MP_TAC o SPEC (Term`x':num`)) THEN
                  ASM_REWRITE_TAC[LESS_OR_EQ] THEN
                  DISCH_THEN (DISJ_CASES_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
                   [NTAC 2 (POP_ASSUM MP_TAC) THEN REWRITE_TAC[NOT_LESS_EQUAL] THEN
                    REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_LESS_SUC,
                         ASM_REWRITE_TAC[]]]]],
        REPEAT STRIP_TAC THEN EXISTS_TAC``m:num`` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC``m:num`` THEN ASM_REWRITE_TAC[]]);

val DIVISION_INTERMEDIATE = store_thm("DIVISION_INTERMEDIATE",
  ``!d a b c. division(a,b) d /\ a <= c /\ c <= b
             ==> ?n. n <= dsize d /\ d(n) <= c /\ c <= d(SUC n)``,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC (Term`\n. n <= dsize d /\ (d:num->real)(n) <= c`) num_MAX) THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  SUBGOAL_THEN``(?x. (\n. n <= dsize d /\ d n <= c) x) /\
        (?M. !x. (\n. n <= dsize d /\ d n <= c) x ==> x <= M)``MP_TAC THENL
    [CONJ_TAC THEN BETA_TAC THENL
      [EXISTS_TAC``0:num`` THEN UNDISCH_TAC``division(a,b) d`` THEN
           REWRITE_TAC[DIVISION_THM] THEN STRIP_TAC THEN
           ASM_MESON_TAC[ZERO_LESS_EQ],
           EXISTS_TAC``dsize (d:num -> real)`` THEN
           X_GEN_TAC``x:num`` THEN STRIP_TAC],
     DISCH_TAC THEN ASM_REWRITE_TAC[] THEN HO_MATCH_MP_TAC MONO_EXISTS THEN
         X_GEN_TAC ``n:num`` THEN SIMP_TAC bool_ss[] THEN STRIP_TAC THEN
         FIRST_X_ASSUM(MP_TAC o SPEC ``SUC n``) THEN
         SUBGOAL_THEN``~(SUC n <= n)``ASSUME_TAC THENL
          [SIMP_TAC arith_ss[LESS_OR],
           CONV_TAC CONTRAPOS_CONV THEN
           REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
           ASM_SIMP_TAC arith_ss[REAL_LT_IMP_LE, GSYM LESS_EQ, LT_LE] THEN
           DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC``division(a,b) d`` THEN
           REWRITE_TAC[DIVISION_THM] THEN
           DISCH_THEN(MP_TAC o SPEC ``SUC(dsize d)`` o repeat CONJUNCT2) THEN
           REWRITE_TAC[GREATER_EQ, LE, LESS_EQ_REFL] THEN
           SUBGOAL_THEN``d(SUC (dsize d)) < b``ASSUME_TAC THENL
             [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC``c:real`` THEN
                  ASM_REWRITE_TAC[],
                  POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_LT_IMP_NE]]]]);


(* ------------------------------------------------------------------------- *)
(* Combination of adjacent intervals (quite painful in the details).         *)
(* ------------------------------------------------------------------------- *)

val DINT_COMBINE = store_thm("DINT_COMBINE",
  ``!f a b c i j. a <= b /\ b <= c /\ (Dint(a,b) f i) /\ (Dint(b,c) f j)
                 ==> (Dint(a,c) f (i + j))``,
  REPEAT GEN_TAC THEN
  NTAC 2(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ASSUME (--`a <= b`--)) THEN REWRITE_TAC[REAL_LE_LT] THEN
  ASM_CASES_TAC (--`a:real = b`--) THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[INTEGRAL_NULL, DINT_UNIQ, REAL_LE_TRANS, REAL_ADD_LID],
    DISCH_TAC] THEN
  MP_TAC(ASSUME (--`b <= c`--)) THEN REWRITE_TAC[REAL_LE_LT] THEN
  ASM_CASES_TAC (--`b:real = c`--) THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[INTEGRAL_NULL, DINT_UNIQ, REAL_LE_TRANS, REAL_ADD_RID],
    DISCH_TAC] THEN
  SIMP_TAC arith_ss[Dint, GSYM FORALL_AND_THM] THEN
  DISCH_THEN(fn th => X_GEN_TAC (--`e:real`--) THEN DISCH_TAC THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o SPEC (--`e / &2`--)) THEN
  ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN (--`g1:real->real`--) STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN (--`g2:real->real`--) STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC
   (--`\x. if x < b then min (g1 x) (b - x)
        else if b < x then min (g2 x) (x - b)
        else min (g1 x) (g2 x)`--) THEN
  CONJ_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[gauge])) THEN
    REWRITE_TAC[gauge] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
        REPEAT COND_CASES_TAC THEN
        ASM_SIMP_TAC arith_ss[REAL_LT_MIN, REAL_SUB_LT] THEN
        TRY CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC arith_ss[REAL_LT_IMP_LE,real_lte], ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [Term`d:num->real`, Term`p:num->real`] THEN
  REWRITE_TAC[tdiv, rsum] THEN STRIP_TAC THEN
  MP_TAC(SPECL [Term`d:num->real`, Term`a:real`, Term`c:real`,
                                Term`b:real`]DIVISION_INTERMEDIATE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN ``m:num``
   (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
   REWRITE_TAC[LESS_EQ_EXISTS] THEN
   DISCH_THEN(X_CHOOSE_TAC ``n:num``) THEN ASM_REWRITE_TAC[] THEN
   ASM_CASES_TAC ``(n:num) = 0`` THENL
    [FIRST_X_ASSUM SUBST_ALL_TAC THEN
         RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
         FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
         ASM_MESON_TAC[DIVISION_THM, GREATER_EQ, LESS_EQ_REFL, REAL_NOT_LT],
         ALL_TAC] THEN
        REWRITE_TAC[GSYM SUM_SPLIT, ADD_CLAUSES] THEN
        SUBGOAL_THEN``n= 1 + PRE n``ASSUME_TAC THENL
         [ASM_SIMP_TAC arith_ss[PRE_SUB1], ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM SUM_SPLIT, SUM_1] THEN
        BETA_TAC THEN
        SUBGOAL_THEN ``(p:num->real) m = b`` ASSUME_TAC THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC ``m:num`` o REWRITE_RULE [fine]) THEN
          SUBGOAL_THEN``m < dsize d``ASSUME_TAC THENL
           [ONCE_ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LESS_ADD_NONZERO THEN
            ASM_REWRITE_TAC[],ALL_TAC] THEN
           ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC ``m:num``) THEN
           MAP_EVERY UNDISCH_TAC [``(d:num->real) m <= b``,
                                                          ``b:real <= d(SUC m)``] THEN BETA_TAC THEN
           REPEAT STRIP_TAC THEN
           SUBGOAL_THEN``(d:num->real)(SUC m) - d m <
                                min((g1:real->real)(p m)) (g2(p m))``MP_TAC THENL
            [POP_ASSUM MP_TAC THEN RW_TAC std_ss[] THEN
                 POP_ASSUM MP_TAC THEN CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
                 REWRITE_TAC[GSYM real_lte,REAL_MIN_LE] THEN DISJ2_TAC THEN
                 REWRITE_TAC[real_sub] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
                 ASM_REWRITE_TAC[REAL_LE_NEG],ALL_TAC] THEN
             POP_ASSUM MP_TAC THEN RW_TAC std_ss[] THENL
              [UNDISCH_TAC``(d:num->real) (SUC m) - d m <
                                min ((g1:real->real) (p m)) (b - p m)`` THEN
                   CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
                   REWRITE_TAC[GSYM real_lte,REAL_MIN_LE] THEN DISJ2_TAC THEN
                   REWRITE_TAC[real_sub] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
                   ASM_REWRITE_TAC[REAL_LE_NEG],
                   UNDISCH_TAC``(d:num->real) (SUC m) - d m <
                                min ((g2:real->real) (p m)) (p m - b)``THEN
           CONV_TAC CONTRAPOS_CONV THEN DISCH_TAC THEN
                   REWRITE_TAC[GSYM real_lte,REAL_MIN_LE] THEN DISJ2_TAC THEN
                   REWRITE_TAC[real_sub] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
                   ASM_REWRITE_TAC[REAL_LE_NEG],
                   ASM_SIMP_TAC arith_ss[GSYM REAL_LE_ANTISYM,real_lte]],ALL_TAC] THEN
        ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC arith_ss[PRE_SUB1] THEN
        REWRITE_TAC[GSYM PRE_SUB1] THEN
        ABBREV_TAC``s1 = sum(0,m)(\n.
                                (f:real->real)((p:num->real) n) * (d(SUC n) - d n))`` THEN
    ABBREV_TAC``s2 = sum(m + 1, PRE n)
                (\n. (f:real->real)((p:num->real) n) * (d(SUC n) - d n))`` THEN
        ONCE_REWRITE_TAC[REAL_ARITH
    ``(s1 + (f b * (d (SUC m) - d m) + s2) - (i + j)) =
      (s1 + (f b * (b - d m)) - i) + (s2 + (f b * (d(SUC m) - b)) - j)``] THEN
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC``abs((s1 + f b * (b - d m)) - i) +
                          abs((s2 + f b * (d(SUC m) - b)) - j)`` THEN
        REWRITE_TAC[REAL_ABS_TRIANGLE] THEN
        GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_HALF_DOUBLE] THEN
        MATCH_MP_TAC REAL_LT_ADD2 THEN CONJ_TAC THENL
         [UNDISCH_TAC
      ``!D p. tdiv(a,b) (D,p) /\ fine g1 (D,p)
            ==> abs(rsum(D,p) f - i) < e / &2`` THEN
          DISCH_THEN(MP_TAC o SPEC ``\i.
                        if i <= m then (d:num->real)(i) else b``) THEN
          DISCH_THEN(MP_TAC o SPEC ``\i.
                        if i <= m then (p:num->real)(i) else b``) THEN
          MATCH_MP_TAC(TAUT_CONV ``a /\ (a ==> b) /\ (a /\ c ==> d)
                       ==> (a /\ b ==> c) ==> d``) THEN
          CONJ_TAC THENL
           [REWRITE_TAC[tdiv, division] THEN REPEAT CONJ_TAC THENL
             [BETA_TAC THEN REWRITE_TAC[LE_0] THEN ASM_MESON_TAC[division],
                  ASM_CASES_TAC ``(d:num->real) m = b`` THENL
                   [EXISTS_TAC ``m:num`` THEN
                    SIMP_TAC arith_ss[ARITH_CONV ``n < m ==> n <= m /\ SUC n <= m``] THEN
                        CONJ_TAC THENL
                         [UNDISCH_TAC``division(a,c) d`` THEN REWRITE_TAC[DIVISION_THM] THEN
                          STRIP_TAC THEN ASM_MESON_TAC[ARITH_CONV``(i:num) < m ==> i < m + n``],
                          RW_TAC arith_ss[] THEN SUBGOAL_THEN``(n':num) = m``ASSUME_TAC THENL
                           [ASM_SIMP_TAC arith_ss[REAL_LE_ANTISYM], ASM_SIMP_TAC arith_ss[]]],
                          EXISTS_TAC ``SUC m`` THEN
                          SIMP_TAC arith_ss[ARITH_CONV ``n >= SUC m ==> ~(n <= m)``] THEN
                          RW_TAC arith_ss[] THENL
                           [UNDISCH_TAC``division(a,c) d`` THEN
                            REWRITE_TAC[DIVISION_THM] THEN STRIP_TAC THEN
                            SUBGOAL_THEN``(n':num) < dsize d``ASSUME_TAC THENL
                             [MATCH_MP_TAC LESS_LESS_EQ_TRANS THEN EXISTS_TAC``m:num`` THEN
                              CONJ_TAC THENL
                                   [MATCH_MP_TAC OR_LESS THEN ASM_REWRITE_TAC[],
                                    ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC [LESS_EQ_ADD]],
                                   ASM_SIMP_TAC arith_ss[]],
                            SUBGOAL_THEN``(n':num) = m``ASSUME_TAC THENL
                             [ASM_SIMP_TAC arith_ss[],ONCE_ASM_REWRITE_TAC[] THEN
                              ONCE_REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[]]]],
                BETA_TAC THEN GEN_TAC THEN RW_TAC std_ss[] THENL
                 [REWRITE_TAC[REAL_LE_REFL],
                  SUBGOAL_THEN``(n':num) = m``ASSUME_TAC THENL
                   [ASM_SIMP_TAC arith_ss[],
                    MATCH_MP_TAC REAL_EQ_IMP_LE THEN RW_TAC arith_ss[]],
                  SUBGOAL_THEN``~(SUC n' <= m)``ASSUME_TAC THENL
                   [RW_TAC arith_ss[],ASM_MESON_TAC[]],
                  REWRITE_TAC[REAL_LE_REFL]]],ALL_TAC] THEN
          CONJ_TAC THENL
          [REWRITE_TAC[tdiv, fine] THEN BETA_TAC THEN
           STRIP_TAC THEN X_GEN_TAC ``k:num`` THEN
           UNDISCH_TAC``fine
                (\x.
                        if x < b then
                          min (g1 x) (b - x)
                        else if b < x then
                          min (g2 x) (x - b)
                        else
                          min (g1 x) (g2 x)) (d,p)`` THEN REWRITE_TAC[fine] THEN
          DISCH_THEN(MP_TAC o SPEC ``k:num``) THEN MATCH_MP_TAC MONO_IMP THEN
          ASM_CASES_TAC ``k:num = m`` THENL
           [ASM_SIMP_TAC arith_ss[LESS_EQ_REFL, REAL_LT_REFL] THEN DISCH_TAC THEN
            MATCH_MP_TAC REAL_LET_TRANS THEN
                EXISTS_TAC``(d:num->real) (SUC m) - d m`` THEN CONJ_TAC THENL
                 [REWRITE_TAC[real_sub] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
                  ASM_REWRITE_TAC[REAL_LE_REFL],
                  MATCH_MP_TAC REAL_LTE_TRANS THEN
                  EXISTS_TAC``min ((g1:real->real) b) ((g2:real->real) b)`` THEN
                  ASM_REWRITE_TAC[REAL_MIN_LE1]],ALL_TAC] THEN
          ASM_CASES_TAC ``k:num <= m`` THEN ONCE_ASM_REWRITE_TAC[] THENL
           [ASM_SIMP_TAC arith_ss[] THEN
            SUBGOAL_THEN ``(p:num->real) k <= b`` MP_TAC THENL
            [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC ``(d:num->real) m`` THEN
                 ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
                 EXISTS_TAC ``(d:num->real) (SUC k)`` THEN ASM_REWRITE_TAC[] THEN
                 ASM_MESON_TAC[DIVISION_MONO_LE, ARITH_CONV
                                ``k <= m /\ ~(k = m) ==> SUC k <= m``],ALL_TAC] THEN
                 COND_CASES_TAC THENL
                  [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
                   EXISTS_TAC``min ((g1 :real -> real)
                                        ((p :num -> real) k)) ((b :real) - p k)`` THEN
                   ASM_SIMP_TAC arith_ss[REAL_MIN_LE1],
                   DISCH_TAC THEN
                   SUBGOAL_THEN``(p :num -> real) k = b``ASSUME_TAC THENL
                   [ASM_SIMP_TAC arith_ss[REAL_ARITH
                                ``~(a < b) /\ (a <= b) ==> (a = b)``],
                        ASM_SIMP_TAC arith_ss[REAL_LT_REFL] THEN DISCH_TAC THEN
                        MATCH_MP_TAC REAL_LTE_TRANS THEN
                        EXISTS_TAC``min ((g1 :real -> real) b) (g2 b)`` THEN
                        ASM_SIMP_TAC arith_ss[REAL_MIN_LE1]]],ALL_TAC] THEN
                        CONJ_TAC THENL
                         [DISCH_TAC THEN
                          SUBGOAL_THEN``dsize
                                (\(i :num). if i <= (m :num) then (d :num -> real) i
                                        else (b :real)) <=  SUC (m:num)``MP_TAC THENL
                           [MATCH_MP_TAC DIVISION_DSIZE_LE THEN
                            MAP_EVERY EXISTS_TAC [``a:real``, ``b:real``] THEN
                            ASM_REWRITE_TAC[] THEN SIMP_TAC arith_ss[],
                            ASM_SIMP_TAC arith_ss[]],
                          UNDISCH_TAC ``gauge (\x. a <= x /\ x <= b) g1`` THEN
                          ASM_SIMP_TAC arith_ss[REAL_SUB_REFL, gauge, REAL_LE_REFL]],
          ALL_TAC] THEN
          DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
          HO_MATCH_MP_TAC(REAL_ARITH
                ``(x = y) ==> abs(x - i) < e ==> abs(y - i) < e``) THEN
          REWRITE_TAC[rsum] THEN ASM_CASES_TAC ``(d:num->real) m = b`` THENL
           [SUBGOAL_THEN ``dsize (\i. if i <= m then d i else b) = m`` ASSUME_TAC THENL
            [MATCH_MP_TAC DIVISION_DSIZE_EQ_ALT THEN
                 MAP_EVERY EXISTS_TAC [``a:real``, ``b:real``] THEN CONJ_TAC THENL
                  [ASM_MESON_TAC[tdiv], ALL_TAC] THEN
                 BETA_TAC THEN
                 ASM_SIMP_TAC arith_ss[LESS_EQ_REFL, ARITH_CONV ``~(SUC m <= m)``] THEN
                 UNDISCH_TAC``division (a,c) d`` THEN REWRITE_TAC[DIVISION_THM] THEN
                 ONCE_ASM_REWRITE_TAC[] THEN
                 MESON_TAC[ARITH_CONV ``i < m:num ==> i < m + n``], ALL_TAC] THEN
                ONCE_ASM_REWRITE_TAC[] THEN
                ASM_SIMP_TAC arith_ss[REAL_SUB_REFL, REAL_MUL_RZERO, REAL_ADD_RID] THEN
                UNDISCH_TAC``sum (0,m) (\n. (f:real->real) (p n) *
                                        ((d:num->real) (SUC n) - d n)) = s1`` THEN
                CONV_TAC(LAND_CONV SYM_CONV) THEN SIMP_TAC arith_ss[] THEN
                DISCH_TAC THEN MATCH_MP_TAC SUM_EQ THEN
                SIMP_TAC arith_ss[ADD_CLAUSES, LESS_IMP_LESS_OR_EQ, GSYM LESS_EQ],
                ALL_TAC] THEN
                SUBGOAL_THEN ``dsize (\i. if i <= m then d i else b) = SUC m``
                        ASSUME_TAC THENL
                 [MATCH_MP_TAC DIVISION_DSIZE_EQ THEN
                  MAP_EVERY EXISTS_TAC [``a:real``, ``b:real``] THEN CONJ_TAC THENL
                   [ASM_MESON_TAC[tdiv],
                    BETA_TAC THEN
                        ASM_SIMP_TAC arith_ss[LESS_EQ_REFL, ARITH_CONV ``~(SUC m <= m)``] THEN
                        ASM_REWRITE_TAC[REAL_LT_LE]],ALL_TAC] THEN
                ASM_SIMP_TAC arith_ss[sum, ADD_CLAUSES, LESS_EQ_REFL,
                      ARITH_CONV ``~(SUC m <= m)``] THEN
                UNDISCH_TAC``sum (0,m) (\n. (f:real->real) (p n) *
                                ((d:num->real) (SUC n) - d n)) = s1`` THEN
                CONV_TAC(LAND_CONV SYM_CONV) THEN SIMP_TAC arith_ss[] THEN
                DISCH_TAC THEN ONCE_REWRITE_TAC[REAL_EQ_RADD] THEN
                MATCH_MP_TAC SUM_EQ THEN
                SIMP_TAC arith_ss[ADD_CLAUSES, LESS_IMP_LESS_OR_EQ, GSYM LESS_EQ],
          ALL_TAC] THEN
        ASM_CASES_TAC ``d(SUC m):real = b`` THEN ASM_REWRITE_TAC[] THENL
         [ASM_REWRITE_TAC[REAL_SUB_REFL, REAL_MUL_RZERO, REAL_ADD_RID] THEN
          UNDISCH_TAC``sum (m + 1,PRE n)
                        (\n. (f:real->real) ((p:num->real) n) *
                                ((d:num->real) (SUC n) - d n)) = s2`` THEN
          CONV_TAC(LAND_CONV SYM_CONV) THEN SIMP_TAC arith_ss[] THEN DISCH_TAC THEN
          UNDISCH_TAC
                ``!D p. tdiv(b,c) (D,p) /\ fine g2 (D,p)
            ==> abs(rsum(D,p) f - j) < e / &2`` THEN
          DISCH_THEN(MP_TAC o SPEC ``\i. (d:num->real) (i + SUC m)``) THEN
          DISCH_THEN(MP_TAC o SPEC ``\i. (p:num->real) (i + SUC m)``) THEN
          MATCH_MP_TAC(TAUT_CONV ``a /\ (a ==> b /\ (b /\ c ==> d))
                       ==> (a /\ b ==> c) ==> d``) THEN
          CONJ_TAC THENL
           [ASM_SIMP_TAC arith_ss[tdiv, division, ADD_CLAUSES] THEN
            EXISTS_TAC ``PRE n`` THEN
                UNDISCH_TAC``division(a,c) d`` THEN REWRITE_TAC[DIVISION_THM] THEN
                ASM_MESON_TAC[ARITH_CONV
                     ``~(n = 0) /\ k < PRE n ==> SUC(k + m) < m + n``,
                    ARITH_CONV
                     ``~(n = 0) /\ k >= PRE n ==> SUC(k + m) >= m + n``],
                 DISCH_TAC] THEN
                SUBGOAL_THEN ``dsize(\i. d (i + SUC m)) = PRE n`` ASSUME_TAC THENL
                 [MATCH_MP_TAC DIVISION_DSIZE_EQ_ALT THEN
                  MAP_EVERY EXISTS_TAC [``b:real``, ``c:real``] THEN
                  CONJ_TAC THENL
                   [ASM_MESON_TAC[tdiv],
                    BETA_TAC THEN SIMP_TAC arith_ss[] THEN
                    UNDISCH_TAC``division(a,c) d`` THEN REWRITE_TAC[DIVISION_THM] THEN
                    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
                    ASM_SIMP_TAC arith_ss[ADD_CLAUSES]],ALL_TAC] THEN
                CONJ_TAC THENL
                 [ASM_SIMP_TAC arith_ss[fine] THEN X_GEN_TAC ``k:num`` THEN
                  DISCH_TAC THEN
                  UNDISCH_TAC``fine
                                                (\x.
                                                        if x < b then
                                                          min ((g1:real->real) x) (b - x)
                                                        else if b < x then
                                                          min ((g2:real->real) x) (x - b)
                                                        else
                                                          min (g1 x) (g2 x)) (d,p)`` THEN
                  REWRITE_TAC[fine] THEN DISCH_THEN(MP_TAC o SPEC ``k + SUC m``) THEN
                  UNDISCH_TAC ``b <= d (SUC m)`` THEN
                  ASM_SIMP_TAC arith_ss[ADD_CLAUSES] THEN REWRITE_TAC[REAL_LE_REFL] THEN
                  MATCH_MP_TAC(REAL_ARITH ``b <= a ==> x < b ==> x < a``) THEN
                  SUBGOAL_THEN ``~(p(SUC (k + m)) < b)``ASSUME_TAC THENL
                   [RW_TAC arith_ss[GSYM real_lte] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
                    EXISTS_TAC``(d:num->real)(SUC (k + m))`` THEN CONJ_TAC THENL
                         [SUBGOAL_THEN``SUC m <= SUC (k+m)``MP_TAC THENL
                           [SIMP_TAC arith_ss[], MATCH_MP_TAC DIVISION_MONO_LE THEN
                            MAP_EVERY EXISTS_TAC [``a:real``, ``c:real``] THEN
                                ASM_REWRITE_TAC[]],
                          UNDISCH_TAC``tdiv (d (SUC m),c)
                                        ((\i. d (i + SUC m)),(\i. p (i + SUC m)))`` THEN
                          REWRITE_TAC[tdiv] THEN BETA_TAC THEN STRIP_TAC THEN
                          ASM_SIMP_TAC arith_ss[]],ASM_SIMP_TAC arith_ss[]] THEN
                      RW_TAC arith_ss[] THENL
                        [REWRITE_TAC[REAL_MIN_LE1],REWRITE_TAC[REAL_MIN_LE2]],ALL_TAC] THEN
                REWRITE_TAC[rsum] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
                SUBGOAL_THEN``(m:num) + 1 = 0 + SUC m``ASSUME_TAC THENL
                 [SIMP_TAC arith_ss[],ALL_TAC] THEN
                ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUM_REINDEX] THEN
                SIMP_TAC arith_ss[PRE_SUB1] THEN
                SIMP_TAC arith_ss[ADD1, ADD_CLAUSES],ALL_TAC] THEN
        UNDISCH_TAC
                ``!D p. tdiv(b,c) (D,p) /\ fine g2 (D,p)
          ==> abs(rsum(D,p) f - j) < e / &2`` THEN
        DISCH_THEN(MP_TAC o SPEC ``\i. if i = 0 then (b:real)
                                else (d:num->real)(i + m)``) THEN
        DISCH_THEN(MP_TAC o SPEC ``\i. if i = 0 then (b:real)
                                else (p:num->real)(i + m)``) THEN
        MATCH_MP_TAC(TAUT_CONV ``a /\ (a ==> b /\ (b /\ c ==> d))
                     ==> (a /\ b ==> c) ==> d``) THEN
        CONJ_TAC THENL
         [SIMP_TAC arith_ss[tdiv, division, ADD_CLAUSES] THEN CONJ_TAC THENL
          [EXISTS_TAC ``n:num`` THEN UNDISCH_TAC``division(a,c) d`` THEN
           REWRITE_TAC[DIVISION_THM] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
           MATCH_MP_TAC MONO_AND THEN ASM_SIMP_TAC arith_ss[] THEN
           DISCH_THEN(fn th =>
                        X_GEN_TAC ``k:num`` THEN MP_TAC(SPEC ``k + m:num`` th)) THEN
           ASM_CASES_TAC ``k:num < n`` THENL
            [ASM_SIMP_TAC arith_ss[ARITH_CONV
                                                                ``(k + (m:num) < m + n) = (k < n)``] THEN
                 COND_CASES_TAC THENL
                  [ASM_SIMP_TAC arith_ss[ADD_CLAUSES,REAL_LT_LE],REWRITE_TAC[]],
                 ASM_SIMP_TAC arith_ss[ADD_CLAUSES]],ALL_TAC] THEN
                GEN_TAC THEN COND_CASES_TAC THENL
                 [ASM_SIMP_TAC arith_ss[REAL_LE_REFL],
                  ASM_SIMP_TAC arith_ss[REAL_LE_REFL]], ALL_TAC] THEN DISCH_TAC THEN
        SUBGOAL_THEN ``dsize(\i. if i = 0 then b else d (i + m)) = n``
                                ASSUME_TAC THENL
         [MATCH_MP_TAC DIVISION_DSIZE_EQ_ALT THEN
          MAP_EVERY EXISTS_TAC [``b:real``, ``c:real``] THEN
          CONJ_TAC THENL [ASM_MESON_TAC[tdiv],ALL_TAC] THEN BETA_TAC THEN
          UNDISCH_TAC``division(a,c) d`` THEN REWRITE_TAC[DIVISION_THM] THEN
          DISCH_THEN(MP_TAC o CONJUNCT2) THEN ONCE_ASM_REWRITE_TAC[ADD_CLAUSES] THEN
          GEN_REWRITE_TAC RAND_CONV [][CONJ_SYM] THEN MATCH_MP_TAC MONO_AND THEN
          CONJ_TAC THENL
           [DISCH_THEN(fn th =>
                        X_GEN_TAC ``k:num`` THEN MP_TAC(SPEC ``k + (m:num)`` th)) THEN
                ASM_CASES_TAC ``(k:num) < n`` THENL
                 [ASM_SIMP_TAC arith_ss[ARITH_CONV ``(k + (m:num) < m + n) = (k < n)``] THEN
                  COND_CASES_TAC THEN ASM_SIMP_TAC arith_ss[ADD_CLAUSES] THEN
                  ASM_SIMP_TAC arith_ss[REAL_LT_LE],
                  ASM_SIMP_TAC arith_ss[]], ASM_SIMP_TAC arith_ss[]],ALL_TAC] THEN
        CONJ_TAC THENL
         [ASM_SIMP_TAC arith_ss[fine] THEN X_GEN_TAC ``k:num`` THEN DISCH_TAC THEN
          UNDISCH_TAC``fine
                                        (\x.
                                                if x < b then
                                                  min ((g1:real->real) x) (b - x)
                                                else if b < x then
                                                  min ((g2:real->real) x) (x - b)
                                                else
                                                  min (g1 x) (g2 x)) (d,p)`` THEN REWRITE_TAC[fine] THEN
          DISCH_THEN(MP_TAC o SPEC ``k + m:num``) THEN
          ASM_SIMP_TAC arith_ss[ADD_CLAUSES,ARITH_CONV
                                                        ``(k + m < m + n) = ((k:num) < n)``] THEN
          ASM_CASES_TAC ``(k:num) = 0`` THENL
           [ASM_SIMP_TAC arith_ss[ADD_CLAUSES, REAL_LT_REFL] THEN DISCH_TAC THEN
            MATCH_MP_TAC REAL_LTE_TRANS THEN
                EXISTS_TAC``min (g1 b) ((g2:real->real) b)`` THEN
                REWRITE_TAC[REAL_MIN_LE2] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
                EXISTS_TAC``(d:num->real) (SUC m) - d m`` THEN
                ASM_SIMP_TAC arith_ss[] THEN
                ASM_REWRITE_TAC[real_sub,REAL_LE_LADD,REAL_LE_NEG2],ALL_TAC] THEN
          ASM_SIMP_TAC arith_ss[] THEN
          MATCH_MP_TAC(REAL_ARITH ``b <= a ==> x < b ==> x < a``) THEN
          SUBGOAL_THEN ``~((p:num->real) (k + m) < b)``ASSUME_TAC THENL
           [RW_TAC arith_ss[GSYM real_lte] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
            EXISTS_TAC``(d:num->real)(SUC m)`` THEN ASM_SIMP_TAC arith_ss[] THEN
                MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC``(d:num->real) (k + m)`` THEN
                CONJ_TAC THENL
                 [FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVISION_MONO_LE) THEN
                  DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC arith_ss[],
                  FIRST_ASSUM(MP_TAC o CONJUNCT1 o SPEC ``(k + m):num``) THEN
                  SIMP_TAC arith_ss[]],ALL_TAC] THEN
          ASM_SIMP_TAC arith_ss[] THEN RW_TAC arith_ss[] THENL
           [REWRITE_TAC[REAL_MIN_LE1],REWRITE_TAC[REAL_MIN_LE2]],ALL_TAC] THEN
        ASM_SIMP_TAC arith_ss[rsum] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        MATCH_MP_TAC(REAL_ARITH
                ``(x = y) ==> abs(x - i) < e ==> abs(y - i) < e``) THEN
        ONCE_ASM_REWRITE_TAC[] THEN
        SIMP_TAC arith_ss[GSYM SUM_SPLIT, SUM_1, ADD_CLAUSES] THEN
        MATCH_MP_TAC(REAL_ARITH ``(a = b) ==> (x + a = b + x)``) THEN
        UNDISCH_TAC``sum(m + 1, PRE n)
                (\n. (f:real->real)((p:num->real) n) * (d(SUC n) - d n)) = s2`` THEN
        CONV_TAC(LAND_CONV SYM_CONV) THEN SIMP_TAC arith_ss[] THEN DISCH_TAC THEN
        SUBGOAL_THEN``(1:num) = 0 + 1``ASSUME_TAC THENL
         [SIMP_TAC arith_ss[],ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN``(m:num) + (0 + 1) = 0 + m + 1``ASSUME_TAC THENL
         [SIMP_TAC arith_ss[],ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUM_REINDEX] THEN MATCH_MP_TAC SUM_EQ THEN
        SIMP_TAC arith_ss[ADD_CLAUSES, ADD_EQ_0]);

 (* ------------------------------------------------------------------------- *)
(* Pointwise perturbation and spike functions.                               *)
(* ------------------------------------------------------------------------- *)

val SUM_EQ_0 = store_thm("SUM_EQ_0",
  ``(!r. m <= r /\ r < m + n ==> (f(r) = &0)) ==> (sum(m,n) f = &0)``,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC ``sum(m,n) (\r. &0)`` THEN
  CONJ_TAC THENL [ALL_TAC, REWRITE_TAC[SUM_0]] THEN
  MATCH_MP_TAC SUM_EQ THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]);

val DINT_DELTA_LEFT = store_thm("DINT_DELTA_LEFT",
  ``!a b. Dint(a,b) (\x. if x = a then &1 else &0) (&0)``,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(REAL_ARITH ``b < a \/ a <= b``) THENL
   [ASM_SIMP_TAC arith_ss[DINT_WRONG],
    REWRITE_TAC[Dint] THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
    EXISTS_TAC ``(\x. e):real->real`` THEN
        ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT, gauge,
                                                fine, rsum, tdiv, REAL_SUB_RZERO] THEN
    MAP_EVERY X_GEN_TAC[(--`d:num->real`--),(--`p:num->real`--)] THEN
        STRIP_TAC THEN ASM_CASES_TAC(Term`dsize d = 0`) THEN
        ASM_REWRITE_TAC[sum, ABS_N] THEN
    SUBGOAL_THEN(--`dsize d = 1 + PRE (dsize d)`--)ASSUME_TAC THENL
     [ASM_SIMP_TAC arith_ss[PRE_SUB1],
          ONCE_ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[GSYM SUM_SPLIT, SUM_1, ADD_CLAUSES] THEN
          MATCH_MP_TAC(REAL_ARITH
       ``(&0 <= x /\ x < e) /\ (y = &0) ==> (abs(x + y) < e)``) THEN
          CONJ_TAC THENL
           [BETA_TAC THEN COND_CASES_TAC THENL
            [REWRITE_TAC[REAL_MUL_LID, REAL_SUB_LE] THEN
             ASM_MESON_TAC[DIVISION_THM, ZERO_LESS_EQ, NOT_ZERO_LT_ZERO],
             ASM_REWRITE_TAC [REAL_MUL_LZERO, REAL_LE_REFL]],
            MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC ``r:num`` THEN STRIP_TAC THEN
            BETA_TAC THEN REWRITE_TAC[REAL_ENTIRE] THEN DISJ1_TAC THEN
            SUBGOAL_THEN``(a:real) < (p:num->real) r``MP_TAC THENL
             [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC``(d:num->real)r`` THEN
              CONJ_TAC THENL
               [SUBGOAL_THEN``(a:real) = (d:num->real) 0``MP_TAC THENL
                [UNDISCH_TAC``division (a,b) d`` THEN REWRITE_TAC[DIVISION_THM] THEN
                     STRIP_TAC THEN UNDISCH_TAC``(d:num->real) 0 = a`` THEN
                     CONV_TAC(LAND_CONV SYM_CONV) THEN PROVE_TAC[],
                     DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
                     MATCH_MP_TAC DIVISION_LT_GEN THEN
                     MAP_EVERY EXISTS_TAC[``a:real``,``b:real``] THEN
                     ASM_SIMP_TAC arith_ss[LESS_EQ, GSYM ONE]],
                     POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
                         ASM_SIMP_TAC arith_ss[]],
              SIMP_TAC arith_ss[REAL_LT_IMP_NE]]]]]);

val DINT_DELTA_RIGHT = store_thm("DINT_DELTA_RIGHT",
  ``!a b. Dint(a,b) (\x. if x = b then &1 else &0) (&0)``,
  REPEAT GEN_TAC THEN DISJ_CASES_TAC(REAL_ARITH ``b < a \/ a <= b``) THENL
   [ASM_SIMP_TAC arith_ss[DINT_WRONG],
    REWRITE_TAC[Dint] THEN
    X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
        EXISTS_TAC ``(\x. e):real->real`` THEN
        ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT,
                                                gauge, fine, rsum, tdiv, REAL_SUB_RZERO] THEN
    MAP_EVERY X_GEN_TAC [``d:num->real``, ``p:num->real``] THEN
        STRIP_TAC THEN ASM_CASES_TAC ``dsize d = 0`` THEN
        ASM_REWRITE_TAC[sum, ABS_N] THEN
        SUBGOAL_THEN``dsize d = PRE (dsize d) + 1``ASSUME_TAC THENL
         [ASM_SIMP_TAC arith_ss[PRE_SUB1],
          ONCE_ASM_REWRITE_TAC[] THEN ABBREV_TAC ``m = PRE(dsize d)`` THEN
          ASM_REWRITE_TAC[GSYM SUM_SPLIT, SUM_1, ADD_CLAUSES] THEN
          MATCH_MP_TAC(REAL_ARITH
        ``(&0 <= x /\ x < e) /\ (y = &0) ==> abs(y + x) < e``) THEN
      CONJ_TAC THENL
           [BETA_TAC THEN COND_CASES_TAC THENL
            [REWRITE_TAC[REAL_MUL_LID, REAL_SUB_LE] THEN CONJ_TAC THENL
                 [PROVE_TAC[DIVISION_MONO_LE_SUC], ASM_SIMP_TAC arith_ss[]],
                  ASM_REWRITE_TAC[REAL_MUL_LZERO, REAL_LE_REFL]],
                  MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC ``r:num`` THEN
                  REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN BETA_TAC THEN
                  REWRITE_TAC[REAL_ENTIRE] THEN DISJ1_TAC THEN
                  SUBGOAL_THEN``(p:num->real) r < b``MP_TAC THENL
                   [MATCH_MP_TAC REAL_LET_TRANS THEN
                    EXISTS_TAC``(d:num->real)(SUC r)`` THEN CONJ_TAC THENL
                         [ASM_REWRITE_TAC[],
                          SUBGOAL_THEN``b = d(dsize d)``MP_TAC THENL
                           [UNDISCH_TAC``division(a,b) (d:num->real)`` THEN
                            REWRITE_TAC[DIVISION_THM] THEN STRIP_TAC THEN
                                POP_ASSUM MP_TAC THEN SIMP_TAC arith_ss[],
                                DISCH_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
                                ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUC_ONE_ADD] THEN
                                MATCH_MP_TAC DIVISION_LT_GEN THEN
                                MAP_EVERY EXISTS_TAC[``a:real``,``b:real``] THEN
                                ASM_SIMP_TAC arith_ss[LESS_EQ]]],
                                SIMP_TAC arith_ss[REAL_LT_IMP_NE]]]]]);

val DINT_DELTA = store_thm("DINT_DELTA",
  ``!a b c. Dint(a,b) (\x. if x = c then &1 else &0) (&0)``,
  REPEAT GEN_TAC THEN ASM_CASES_TAC ``a <= b`` THENL
   [ALL_TAC, ASM_MESON_TAC[REAL_NOT_LE, DINT_WRONG]] THEN
  ASM_CASES_TAC ``a <= c /\ c <= b`` THENL
   [ALL_TAC,
    MATCH_MP_TAC INTEGRAL_EQ THEN EXISTS_TAC ``\x:real. &0`` THEN
    ASM_REWRITE_TAC[DINT_0] THEN RW_TAC arith_ss[]] THEN
  GEN_REWRITE_TAC RAND_CONV [][GSYM REAL_ADD_LID] THEN
  MATCH_MP_TAC DINT_COMBINE THEN EXISTS_TAC ``c:real`` THEN
  ASM_REWRITE_TAC[DINT_DELTA_LEFT, DINT_DELTA_RIGHT]);

val DINT_POINT_SPIKE = store_thm("DINT_POINT_SPIKE",
        ``!f g a b c i.
        (!x. a <= x /\ x <= b /\ ~(x = c) ==> (f x = g x)) /\ Dint(a,b) f i
        ==> Dint(a,b) g i``,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC ``a <= b`` THENL
   [ALL_TAC, ASM_MESON_TAC[REAL_NOT_LE, DINT_WRONG]] THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN
  EXISTS_TAC ``\x:real. f(x) + (g c - f c) * (if x = c then &1 else &0)`` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBST1_TAC(REAL_ARITH ``i = i + ((g:real->real) c - f c) * &0``) THEN
    HO_MATCH_MP_TAC DINT_ADD THEN ASM_REWRITE_TAC[] THEN
    HO_MATCH_MP_TAC DINT_CMUL THEN REWRITE_TAC[DINT_DELTA],
    REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC arith_ss[REAL_MUL_RZERO, REAL_ADD_RID] THEN
    REAL_ARITH_TAC]);

val DINT_FINITE_SPIKE = store_thm("DINT_FINITE_SPIKE",
  ``!f g a b s i.
        FINITE s /\
        (!x. a <= x /\ x <= b /\ ~(x IN s) ==> (f x = g x)) /\
        Dint(a,b) f i
        ==> Dint(a,b) g i``,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT_CONV ``a /\ b /\ c ==> d <=> c ==> a ==> b ==> d``] THEN
  DISCH_TAC THEN
  MAP_EVERY (fn t => SPEC_TAC(t,t))[``g:real->real``, ``s:real->bool``] THEN
  SIMP_TAC bool_ss[RIGHT_FORALL_IMP_THM] THEN
  HO_MATCH_MP_TAC FINITE_INDUCT THEN REWRITE_TAC[NOT_IN_EMPTY] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INTEGRAL_EQ], ALL_TAC] THEN
  X_GEN_TAC``s:real->bool`` THEN DISCH_TAC THEN X_GEN_TAC``c:real`` THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[TAUT_CONV``a /\ b ==> c ==> d <=> b /\ c /\ a ==> d``] THEN
  STRIP_TAC THEN X_GEN_TAC ``g:real->real`` THEN
  REWRITE_TAC[IN_INSERT, DE_MORGAN_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC DINT_POINT_SPIKE THEN
  EXISTS_TAC ``\x. if x = c then (f:real->real) x else g x`` THEN
  EXISTS_TAC ``c:real`` THEN SIMP_TAC arith_ss[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN BETA_TAC THEN RW_TAC std_ss[]);

(* ------------------------------------------------------------------------- *)
(* Cauchy-type integrability criterion.                                      *)
(* ------------------------------------------------------------------------- *)

val REAL_POW_LBOUND = store_thm("REAL_POW_LBOUND",
  ``!x n. &0 <= x ==> &1 + &n * x <= (&1 + x) pow n``,
  GEN_TAC THEN SIMP_TAC arith_ss[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[pow, REAL_MUL_LZERO, REAL_ADD_RID, REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC ``(&1 + x) * (&1 + &n * x)`` THEN
  ASM_SIMP_TAC arith_ss[REAL_LE_MUL, REAL_POS, REAL_ARITH
   ``&1 + (n + &1) * x <= (&1 + x) * (&1 + n * x) <=> &0 <= n * x * x``] THEN
  REWRITE_TAC[SUC_ONE_ADD, REAL_POW_ADD, POW_1] THEN
  ASM_SIMP_TAC arith_ss[REAL_LE_LMUL1, REAL_ARITH ``&0 <= x ==> &0 <= &1 + x``]);

val REAL_ARCH_POW = store_thm("REAL_ARCH_POW",
  ``!x y. &1 < x ==> ?n. y < x pow n``,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC ``x - &1`` REAL_ARCH) THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(MP_TAC o SPEC ``y:real``) THEN HO_MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC ``n:num`` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC ``&1 + &n * (x - &1)`` THEN
  ASM_SIMP_TAC arith_ss[REAL_ARITH ``x < y ==> x < &1 + y``] THEN
  ASM_MESON_TAC[REAL_POW_LBOUND, REAL_SUB_ADD2, REAL_ARITH
    ``&1 < x ==> &0 <= x - &1``]);

val REAL_ARCH_POW2 = store_thm("REAL_ARCH_POW2",
  ``!x. ?n. x < &2 pow n``,
  SIMP_TAC arith_ss[REAL_ARCH_POW, REAL_LT]);

val REAL_POW_LE_1 = store_thm(
  "REAL_POW_LE_1",
  (--`!(n:num) (x:real). (&1:real) <= x ==> (&1:real) <= x pow n`--),
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[pow, REAL_LE_REFL],
    GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [pow] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] [] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_01] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);

val REAL_POW_MONO = store_thm (
  "REAL_POW_MONO",
  (--`!(m:num) n x. &1 <= x /\ m <= n ==> x pow m <= x pow n`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[LESS_EQ_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN (--`d:num`--) SUBST1_TAC) THEN
  REWRITE_TAC[REAL_POW_ADD] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] [] THEN
  MATCH_MP_TAC REAL_LE_LMUL_IMP THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC (--`&1`--) THEN
    RW_TAC arith_ss [REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[],
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]]);

val REAL_LE_INV2 = store_thm ("REAL_LE_INV2",
  (--`!x y. (&0:real) < x /\ x <= y ==> inv(y) <= inv(x)`--),
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
  ASM_CASES_TAC (--`x:real = y`--) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN DISJ1_TAC THEN MATCH_MP_TAC REAL_LT_INV THEN
  ASM_REWRITE_TAC[]);

val GAUGE_MIN_FINITE = store_thm("GAUGE_MIN_FINITE",
    ``!s gs n. (!m:num. m <= n ==> gauge s (gs m))
            ==> ?g. gauge s g /\
                    !d p. fine g (d,p) ==> !m. m <= n ==> fine (gs m) (d,p)``,
        GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
        [MESON_TAC[LE],
         REWRITE_TAC[LE] THEN
         REWRITE_TAC[TAUT_CONV ``(a \/ b ==> c) = ((a ==> c) /\ (b ==> c))``] THEN
         SIMP_TAC arith_ss[FORALL_AND_THM, LEFT_FORALL_IMP_THM, EXISTS_REFL] THEN
         STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o assert (is_imp o concl)) THEN
         ASM_REWRITE_TAC[] THEN
         DISCH_THEN(X_CHOOSE_THEN ``gm:real->real`` STRIP_ASSUME_TAC) THEN
         EXISTS_TAC ``\x:real. if gm x <
                gs(SUC n) x then gm x else gs(SUC n) x`` THEN
         SUBGOAL_THEN``gauge s (\x:real. if gm x <
                gs(SUC n) x then gm x else gs(SUC n) x)``ASSUME_TAC THENL
          [MATCH_MP_TAC GAUGE_MIN THEN ASM_REWRITE_TAC[],
           ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN
           DISCH_THEN(MP_TAC o MATCH_MP FINE_MIN) THEN
           ASM_SIMP_TAC arith_ss[ETA_AX]]]);

val INTEGRABLE_CAUCHY = store_thm("INTEGRABLE_CAUCHY",
  ``!f a b. integrable(a,b) f <=>
           !e. &0 < e
               ==> ?g. gauge (\x. a <= x /\ x <= b) g /\
                       !d1 p1 d2 p2.
                            tdiv (a,b) (d1,p1) /\ fine g (d1,p1) /\
                            tdiv (a,b) (d2,p2) /\ fine g (d2,p2)
                            ==> abs (rsum(d1,p1) f - rsum(d2,p2) f) < e``,
  REPEAT GEN_TAC THEN REWRITE_TAC[integrable] THEN EQ_TAC THENL
   [REWRITE_TAC[Dint] THEN DISCH_THEN(X_CHOOSE_TAC ``i:real``) THEN
    X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC ``e / &2``) THEN
        ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
        HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``g:real->real`` THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY X_GEN_TAC
     [``d1:num->real``, ``p1:num->real``,
                ``d2:num->real``, ``p2:num->real``] THEN STRIP_TAC THEN
          FIRST_X_ASSUM(fn th =>
        MP_TAC(SPECL [``d1:num->real``, ``p1:num->real``] th) THEN
        MP_TAC(SPECL [``d2:num->real``, ``p2:num->real``] th)) THEN
          ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
          ONCE_REWRITE_TAC[REAL_ARITH``abs(a - b) = abs(a - i + -(b - i))``] THEN
          MATCH_MP_TAC REAL_LET_TRANS THEN
          EXISTS_TAC``abs(rsum(d1,p1) f -i) + abs(-(rsum(d2,p2) f - i))`` THEN
          REWRITE_TAC[ABS_TRIANGLE] THEN REWRITE_TAC[ABS_NEG] THEN
          GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_HALF_DOUBLE] THEN
          MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[],ALL_TAC] THEN
        DISCH_TAC THEN DISJ_CASES_TAC(REAL_ARITH ``b < a \/ a <= b``) THENL
        [ASM_MESON_TAC[DINT_WRONG], ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o GEN ``n:num`` o SPEC ``&1 / &2 pow n``) THEN
        SIMP_TAC arith_ss[REAL_LT_DIV, REAL_POW_LT, REAL_LT] THEN
        SIMP_TAC arith_ss[FORALL_AND_THM, SKOLEM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN ``g:num->real->real`` STRIP_ASSUME_TAC) THEN
        MP_TAC(GEN ``n:num``
     (SPECL [``\x. a <= x /\ x <= b``, ``g:num->real->real``, ``n:num``]
          GAUGE_MIN_FINITE)) THEN
        ASM_SIMP_TAC arith_ss[SKOLEM_THM, FORALL_AND_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN ``G:num->real->real`` STRIP_ASSUME_TAC) THEN
        MP_TAC(GEN ``n:num``
     (SPECL [``a:real``, ``b:real``,
                         ``(G:num->real->real) n``] DIVISION_EXISTS)) THEN
        ASM_SIMP_TAC bool_ss[SKOLEM_THM,GSYM LEFT_FORALL_IMP_THM,
                                                        FORALL_AND_THM] THEN
        MAP_EVERY X_GEN_TAC [``d:num->num->real``, ``p:num->num->real``] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN ``cauchy (\n. rsum(d n,p n) f)`` MP_TAC THENL
         [REWRITE_TAC[cauchy] THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
          MP_TAC(SPEC ``&1 / e`` REAL_ARCH_POW2) THEN
          HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``N:num`` THEN
          ASM_SIMP_TAC arith_ss[REAL_LT_LDIV_EQ] THEN DISCH_TAC THEN
          REWRITE_TAC[GREATER_EQ] THEN
          MAP_EVERY X_GEN_TAC [``m:num``,``n:num``] THEN STRIP_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPECL
      [``N:num``, ``(d:num->num->real) m``, ``(p:num->num->real) m``,
       ``(d:num->num->real) n``, ``(p:num->num->real) n``]) THEN
          SUBGOAL_THEN
                ``tdiv (a,b) ((d:num->num->real) m,(p:num->num->real) m) /\
                fine ((g:num->real->real) N) (d m,p m) /\ tdiv (a,b) (d n,p n) /\
                fine (g N) (d n,p n)``ASSUME_TAC THENL
           [ASM_MESON_TAC[],ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC(REAL_ARITH ``d < e ==> x < d ==> x < e``) THEN
          ASM_SIMP_TAC arith_ss[REAL_LT_LDIV_EQ, REAL_POW_LT, REAL_LT] THEN
          ASM_MESON_TAC[REAL_MUL_SYM], ALL_TAC] THEN
         REWRITE_TAC[SEQ_CAUCHY, convergent, SEQ, Dint] THEN
         HO_MATCH_MP_TAC MONO_EXISTS THEN
         X_GEN_TAC ``i:real`` THEN STRIP_TAC THEN
         X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
         FIRST_X_ASSUM(MP_TAC o SPEC ``e / &2``) THEN
         ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
         DISCH_THEN(X_CHOOSE_THEN ``N1:num`` MP_TAC) THEN
         X_CHOOSE_TAC ``N2:num`` (SPEC ``&2 / e`` REAL_ARCH_POW2) THEN
         DISCH_THEN(MP_TAC o SPEC ``N1 + N2:num``) THEN
         REWRITE_TAC[GREATER_EQ, LESS_EQ_ADD] THEN
         DISCH_TAC THEN EXISTS_TAC ``(G:num->real->real)(N1 + N2)`` THEN
         ASM_REWRITE_TAC[] THEN
         MAP_EVERY X_GEN_TAC [``dx:num->real``, ``px:num->real``] THEN
         STRIP_TAC THEN
         FIRST_X_ASSUM(MP_TAC o SPECL
     [``N1 + N2:num``, ``dx:num->real``, ``px:num->real``,
      ``(d:num->num->real)(N1 + N2)``, ``(p:num->num->real)(N1 + N2)``]) THEN
         SUBGOAL_THEN``tdiv (a,b) (dx,px) /\ fine (g ((N1:num) + N2)) (dx,px) /\
                tdiv (a,b) (d (N1 + N2),p (N1 + N2)) /\
                fine (g ((N1:num) + N2)) (d (N1 + N2),p (N1 + N2))``ASSUME_TAC THENL
         [ASM_MESON_TAC[LESS_EQ_REFL], ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN``1 / 2 pow ((N1:num)+ N2) < e / &2``ASSUME_TAC THENL
          [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC``inv(&2 / e)`` THEN
           CONJ_TAC THENL
            [REWRITE_TAC[GSYM REAL_INV_1OVER] THEN MATCH_MP_TAC REAL_LT_INV THEN
             ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
                 MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC ``&2 pow N2`` THEN
                 ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_ADD] THEN
                 GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] [] THEN
                 MATCH_MP_TAC REAL_LE_RMUL_IMP THEN REWRITE_TAC[POW_2_LE1] THEN
                 MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC``&1`` THEN
                 REWRITE_TAC[REAL_LE_01,POW_2_LE1],
                 MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
                 MATCH_MP_TAC REAL_LINV_UNIQ THEN
                 REWRITE_TAC[REAL_DIV_INNER_CANCEL2] THEN
                 MATCH_MP_TAC REAL_DIV_REFL THEN MATCH_MP_TAC REAL_POS_NZ THEN
                 ASM_REWRITE_TAC[]],
           DISCH_TAC THEN
           SUBGOAL_THEN``
                        abs (rsum (dx,px) f - rsum ((d :num -> num -> real) (N1 + N2),
                        p (N1 + N2)) f) < e / &2``ASSUME_TAC THENL
                 [MATCH_MP_TAC REAL_LT_TRANS THEN
                  EXISTS_TAC``1 / &2 pow(N1 + N2)`` THEN
                  ASM_REWRITE_TAC[],ALL_TAC] THEN
                MATCH_MP_TAC REAL_LET_TRANS THEN
                EXISTS_TAC``abs((rsum(dx,px) f -
                                rsum((d:num->num->real)(N1 + N2),p(N1 + N2)) f)
                                + (rsum((d:num->num->real)(N1 + N2),p(N1 + N2)) f - i))`` THEN
                CONJ_TAC THENL
                 [REWRITE_TAC[real_sub, REAL_ADD_ASSOC] THEN
                  REWRITE_TAC[GSYM real_sub] THEN
                  SIMP_TAC arith_ss[REAL_SUB_ADD,REAL_LE_REFL],
                  MATCH_MP_TAC REAL_LET_TRANS THEN
                  EXISTS_TAC``abs(rsum(dx,px) f -
                        rsum((d:num->num->real)(N1 + N2),p(N1 + N2)) f)
                    + abs(rsum((d:num->num->real)(N1 + N2),p(N1 + N2)) f - i)`` THEN
                   SIMP_TAC arith_ss[REAL_ABS_TRIANGLE] THEN
                   GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_HALF_DOUBLE] THEN
                   MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]]]);

(* ------------------------------------------------------------------------- *)
(* Limit theorem.                                                            *)
(* ------------------------------------------------------------------------- *)

val SUM_DIFFS = store_thm("SUM_DIFFS",
 (--`!m n. sum(m,n) (\i. d(SUC i) - d(i)) = d(m + n) - d m`--),
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[sum, ADD_CLAUSES, REAL_SUB_REFL] THEN REWRITE_TAC[sum] THEN
  RW_TAC arith_ss[ETA_AX] THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN(--`!a b c d. a-b+(c-a) = -b+a+(c-a)`--)
        (fn th => ONCE_REWRITE_TAC[GEN_ALL th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[real_sub] THEN
    ASM_SIMP_TAC arith_ss[GSYM REAL_ADD_SYM],
        SUBGOAL_THEN(--`!a b c d. a+b+(c-b) = a+c`--)
          (fn th => ONCE_REWRITE_TAC[GEN_ALL th]) THENL
         [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
          REWRITE_TAC[REAL_EQ_LADD] THEN
          REWRITE_TAC[REAL_SUB_ADD2], REWRITE_TAC[real_sub] THEN
          GEN_REWR_TAC LAND_CONV [REAL_ADD_COMM] THEN PROVE_TAC[]]]);

val RSUM_BOUND = store_thm("RSUM_BOUND",
  ``!a b d p e f.
        tdiv(a,b) (d,p) /\
        (!x. a <= x /\ x <= b ==> abs(f x) <= e)
        ==> abs(rsum(d,p) f) <= e * (b - a)``,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rsum] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (Term`sum(0,dsize d) (\i. abs(f(p i :real) * (d(SUC i) - d i)))`) THEN
  SIMP_TAC arith_ss[SUM_ABS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC (Term`sum(0,dsize d) (\i. e * abs(d(SUC i) - d(i)))`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[ADD_CLAUSES, REAL_ABS_MUL] THEN
    X_GEN_TAC (Term`r:num`) THEN STRIP_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC REAL_LE_RMUL1 THEN REWRITE_TAC[REAL_ABS_POS] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC[tdiv, DIVISION_UBOUND, DIVISION_LBOUND, REAL_LE_TRANS],
        ALL_TAC] THEN
   SIMP_TAC arith_ss[SUM_CMUL] THEN MATCH_MP_TAC REAL_LE_LMUL1 THEN
   CONJ_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC (Term`a:real`)) THEN
         ASM_MESON_TAC[REAL_LE_REFL, REAL_ABS_POS, REAL_LE_TRANS, DIVISION_LE,
                                        tdiv], ALL_TAC] THEN
         FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o REWRITE_RULE[tdiv]) THEN
         FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_LE_SUC) THEN
         ASM_REWRITE_TAC[abs, REAL_SUB_LE, SUM_DIFFS, ADD_CLAUSES] THEN
         PROVE_TAC[DIVISION_RHS, DIVISION_LHS, REAL_LE_REFL]);

val RSUM_DIFF_BOUND = store_thm ("RSUM_DIFF_BOUND",
  ``!a b d p e f g.
        tdiv(a,b) (d,p) /\
        (!x. a <= x /\ x <= b ==> abs(f x - g x) <= e)
        ==> abs(rsum (d,p) f - rsum (d,p) g) <= e * (b - a)``,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o HO_MATCH_MP RSUM_BOUND) THEN
  SIMP_TAC bool_ss[rsum, SUM_SUB, REAL_SUB_RDISTRIB]);

val INTEGRABLE_LIMIT = store_thm("INTEGRABLE_LIMIT",
  ``!f a b. (!e. &0 < e
                ==> ?g. (!x. a <= x /\ x <= b ==> abs(f x - g x) <= e) /\
                        integrable(a,b) g)
           ==> integrable(a,b) f``,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC ``a <= b`` THENL
  [FIRST_X_ASSUM(MP_TAC o GEN ``n:num`` o SPEC ``&1 / &2 pow n``) THEN
   SIMP_TAC arith_ss[REAL_LT_DIV, REAL_POW_LT, REAL_LT] THEN
   SIMP_TAC arith_ss[FORALL_AND_THM, SKOLEM_THM, integrable] THEN
   DISCH_THEN(X_CHOOSE_THEN ``g:num->real->real`` (CONJUNCTS_THEN2
    ASSUME_TAC (X_CHOOSE_TAC ``i:num->real``))) THEN
   SUBGOAL_THEN ``cauchy i`` MP_TAC THENL
    [REWRITE_TAC[cauchy] THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
     MP_TAC(SPEC ``(&2 * &2 * (b - a)) / e`` REAL_ARCH_POW2) THEN
         HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``N:num`` THEN DISCH_TAC THEN
         MAP_EVERY X_GEN_TAC [``m:num``, ``n:num``] THEN REWRITE_TAC[GREATER_EQ] THEN
         STRIP_TAC THEN UNDISCH_TAC``!(n:num). Dint(a,b) (g n) (i n)`` THEN
         REWRITE_TAC[Dint] THEN SIMP_TAC bool_ss[Once SWAP_FORALL_THM] THEN
         DISCH_THEN(MP_TAC o SPEC ``e / &2 / &2``) THEN
         ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
         DISCH_THEN(fn th => MP_TAC(SPEC ``m:num`` th) THEN
      MP_TAC(SPEC ``n:num`` th)) THEN
         DISCH_THEN(X_CHOOSE_THEN ``gn:real->real`` STRIP_ASSUME_TAC) THEN
         DISCH_THEN(X_CHOOSE_THEN ``gm:real->real`` STRIP_ASSUME_TAC) THEN
         MP_TAC(SPECL [``a:real``, ``b:real``,
                ``\x:real. if gm x < gn x then gm x else gn x``]
                DIVISION_EXISTS) THEN
         ASM_SIMP_TAC arith_ss[GAUGE_MIN, GSYM LEFT_FORALL_IMP_THM] THEN
         MAP_EVERY X_GEN_TAC [``d:num->real``, ``p:num->real``] THEN
         STRIP_TAC THEN
         FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o MATCH_MP FINE_MIN) THEN
         REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [``d:num->real``,
                                        ``p:num->real``])) THEN
         ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN ``abs(rsum(d,p) (g(m:num)) - rsum(d,p) (g n)) <= e / &2``
     (fn th => MP_TAC th) THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC ``&2 / &2 pow N * (b - a)`` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC RSUM_DIFF_BOUND THEN ASM_REWRITE_TAC[] THEN
            REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
                HO_MATCH_MP_TAC(REAL_ARITH
        ``!f. abs(f - gm) <= inv(k) /\ abs(f - gn) <= inv(k)
            ==> (abs(gm - gn) <= &2*inv(k))``) THEN
                EXISTS_TAC ``(f:real->real) x`` THEN CONJ_TAC THEN
                MATCH_MP_TAC REAL_LE_TRANS THENL
                 [EXISTS_TAC ``&1 / &2 pow m``,EXISTS_TAC``&1 / &2 pow n``] THEN
                ASM_SIMP_TAC arith_ss[] THEN REWRITE_TAC[real_div, REAL_MUL_LID] THEN
                MATCH_MP_TAC REAL_LE_INV2 THEN
                ASM_SIMP_TAC arith_ss[REAL_POW_LT, REAL_POW_MONO, REAL_LE,REAL_LT],
                MATCH_MP_TAC REAL_LE_RDIV THEN CONJ_TAC THENL
                 [REAL_ARITH_TAC, GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] [] THEN
                  ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC [real_div] THEN
                  REWRITE_TAC [REAL_MUL_ASSOC] THEN
                  ONCE_REWRITE_TAC [GSYM REAL_MUL_ASSOC] THEN
                  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [] [REAL_MUL_SYM] THEN
                  REWRITE_TAC [REAL_MUL_ASSOC] THEN REWRITE_TAC [GSYM real_div] THEN
                  ASM_SIMP_TAC arith_ss[REAL_LE_LDIV_EQ, REAL_POW_LT, REAL_LT] THEN
                  GEN_REWRITE_TAC RAND_CONV [] [REAL_MUL_SYM] THEN
                  ASM_SIMP_TAC arith_ss[GSYM REAL_LE_LDIV_EQ, REAL_LT_IMP_LE]]],
          REPEAT STRIP_TAC THEN
          SUBGOAL_THEN ``abs(rsum(d,p) (g(m:num)) - rsum(d,p) (g n) -
                (i m - i n)) < e / &2``(fn th => MP_TAC th) THENL
           [SUBGOAL_THEN(--`!a b c d. a-b-(c-d) = a-c - (b-d)`--)
                (fn th => ONCE_REWRITE_TAC[GEN_ALL th]) THENL
                [REAL_ARITH_TAC, ALL_TAC] THEN
                MATCH_MP_TAC REAL_LET_TRANS THEN
                EXISTS_TAC``abs(rsum(d,p)(g (m:num)) - i m)
                                        + abs(rsum(d,p) (g n) - i n)`` THEN CONJ_TAC THENL
                 [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [] [real_sub] THEN
                  GEN_REWRITE_TAC (funpow 2 RAND_CONV) [] [GSYM ABS_NEG] THEN
                  MATCH_ACCEPT_TAC ABS_TRIANGLE,
                  GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_HALF_DOUBLE] THEN
                  MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]],
          DISCH_TAC THEN
          ABBREV_TAC``s = rsum(d,p)(g (m:num)) - rsum(d,p) (g n)`` THEN
          ABBREV_TAC``t= s- (i (m:num) - i n)`` THEN POP_ASSUM MP_TAC THEN
          GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [real_sub] [] THEN
          ONCE_REWRITE_TAC [GSYM REAL_ADD_SYM] THEN
          ONCE_REWRITE_TAC [GSYM REAL_EQ_SUB_LADD] THEN
          ONCE_REWRITE_TAC [REAL_NEG_EQ] THEN ONCE_REWRITE_TAC [REAL_NEG_SUB] THEN
          DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_sub] THEN
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC``abs s + abs (-t)`` THEN
          REWRITE_TAC[ABS_TRIANGLE] THEN
          GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_HALF_DOUBLE] THEN
          MATCH_MP_TAC REAL_LET_ADD2 THEN PROVE_TAC[ABS_NEG]]],
  REWRITE_TAC[SEQ_CAUCHY, convergent] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``s:real`` THEN DISCH_TAC THEN
  REWRITE_TAC[Dint] THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``e / &3`` o REWRITE_RULE[SEQ]) THEN
  ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT, GREATER_EQ] THEN
  DISCH_THEN(X_CHOOSE_TAC ``N1:num``) THEN
  MP_TAC(SPEC ``(&3 * (b - a)) / e`` REAL_ARCH_POW2) THEN
  DISCH_THEN(X_CHOOSE_TAC ``N2:num``) THEN
  UNDISCH_TAC``!(n:num). Dint(a,b) (g (n:num)) ( i n)`` THEN
  REWRITE_TAC[Dint] THEN
  DISCH_THEN(MP_TAC o SPECL [``N1 + N2:num``, ``e / &3``]) THEN
  ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
  HO_MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC ``g:real->real`` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [``d:num->real``, ``p:num->real``] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [``d:num->real``, ``p:num->real``]) THEN
  ASM_REWRITE_TAC[] THEN SUBGOAL_THEN``N1:num <= N1 + N2``MP_TAC THENL
   [REWRITE_TAC[LESS_EQ_ADD], ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN``abs(i ((N1:num) + N2) - s) < e/3``MP_TAC THENL
   [ASM_MESON_TAC[], ALL_TAC] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN``abs(rsum(d,p) f - rsum(d,p)
  (g ((N1:num) + N2))) <= e/ &3``MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC ``&1 / &2 pow (N1 + N2) * (b - a)`` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RSUM_DIFF_BOUND THEN ASM_REWRITE_TAC[],
          MATCH_MP_TAC REAL_LE_RDIV THEN CONJ_TAC THENL
          [REAL_ARITH_TAC,
           GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] [] THEN
           ONCE_REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC [real_div] THEN
           REWRITE_TAC [REAL_MUL_ASSOC] THEN
           ONCE_REWRITE_TAC [GSYM REAL_MUL_ASSOC] THEN
           GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [] [REAL_MUL_SYM] THEN
           REWRITE_TAC [REAL_MUL_ASSOC] THEN REWRITE_TAC [GSYM real_div] THEN
           ASM_SIMP_TAC arith_ss[REAL_LE_LDIV_EQ, REAL_POW_LT, REAL_LT] THEN
           GEN_REWRITE_TAC RAND_CONV [] [REAL_MUL_SYM] THEN
           REWRITE_TAC[REAL_MUL_RID] THEN
           ASM_SIMP_TAC arith_ss[GSYM REAL_LE_LDIV_EQ, REAL_LT_IMP_LE] THEN
           SUBGOAL_THEN``N2:num <= N1 + N2``MP_TAC THENL
            [ONCE_REWRITE_TAC[ADD_COMM] THEN REWRITE_TAC[LESS_EQ_ADD],
                 DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
                 MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC``2 pow N2`` THEN
                 ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_MONO THEN
                 ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]],
        DISCH_TAC THEN ABBREV_TAC``sf = rsum(d,p) f`` THEN
        ABBREV_TAC``sg = rsum(d,p) (g ((N1:num) + N2))`` THEN
        SUBGOAL_THEN``abs(sf - i((N1:num) + N2)) < 2*e/3``MP_TAC THENL
         [MATCH_MP_TAC REAL_LET_TRANS THEN
          EXISTS_TAC``abs(sf - sg) + abs(sg - i((N1:num)+ N2))`` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_TRANS THEN
            EXISTS_TAC``abs((sf - sg) + (sg - i((N1:num) + N2)))`` THEN
                REWRITE_TAC[ABS_TRIANGLE] THEN REAL_ARITH_TAC,
                REWRITE_TAC[real_div, GSYM REAL_MUL_ASSOC] THEN
                REWRITE_TAC[GSYM REAL_DOUBLE, GSYM real_div] THEN
                PROVE_TAC[REAL_LET_ADD2]],
          ONCE_REWRITE_TAC [GSYM REAL_NEG_THIRD] THEN DISCH_TAC THEN
          MATCH_MP_TAC REAL_LET_TRANS THEN
          EXISTS_TAC``abs((sf - i((N1:num) + N2)) + (i((N1:num) + N2) - s))`` THEN
          CONJ_TAC THENL
           [REAL_ARITH_TAC, MATCH_MP_TAC REAL_LET_TRANS THEN
            EXISTS_TAC``abs((sf - i((N1:num) + N2))) +
                        abs((i((N1:num) + N2) - s))`` THEN REWRITE_TAC[ABS_TRIANGLE] THEN
                MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC``(e - e / 3) + e/3`` THEN
                CONJ_TAC THENL [PROVE_TAC[REAL_LT_ADD2],REAL_ARITH_TAC]]]]],
   ASM_MESON_TAC[REAL_NOT_LE, DINT_WRONG, integrable]]);

(* ------------------------------------------------------------------------- *)
(* Hence continuous functions are integrable.                                *)
(* ------------------------------------------------------------------------- *)

val INTEGRABLE_CONST = store_thm("INTEGRABLE_CONST",
 (--`!a b c. integrable(a,b) (\x. c)`--),
  REWRITE_TAC[integrable] THEN REPEAT GEN_TAC THEN
  EXISTS_TAC(Term`c*(b-a):real`) THEN SIMP_TAC arith_ss[DINT_CONST]);

val INTEGRABLE_ADD = store_thm("INTEGRABLE_ADD",
  ``!f g a b. a<=b /\ integrable(a,b) f /\ integrable(a,b) g ==>
    integrable(a,b)(\x. f x + g x)``,
  RW_TAC std_ss[] THEN REWRITE_TAC[integrable] THEN
  EXISTS_TAC``integral(a,b) f + integral(a,b) g`` THEN
  MATCH_MP_TAC DINT_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC INTEGRABLE_DINT THEN ASM_REWRITE_TAC[]);

val INTEGRABLE_CMUL = store_thm("INTEGRABLE_CMUL",
  ``!f a b c. a<=b /\ integrable(a,b) f ==> integrable(a,b)(\x. c* f x)``,
  RW_TAC std_ss[] THEN REWRITE_TAC[integrable] THEN
  EXISTS_TAC``c*integral(a,b)f`` THEN HO_MATCH_MP_TAC DINT_CMUL THEN
  MATCH_MP_TAC INTEGRABLE_DINT THEN ASM_REWRITE_TAC[]);

val INTEGRABLE_COMBINE = store_thm("INTEGRABLE_COMBINE",
        ``!f a b c. a <= b /\ b <= c /\ integrable(a,b) f /\ integrable(b,c) f
         ==> integrable(a,c) f``,
  REWRITE_TAC[integrable] THEN MESON_TAC[DINT_COMBINE]);

val INTEGRABLE_POINT_SPIKE = store_thm("INTEGRABLE_POINT_SPIKE",
        ``!f g a b c.
         (!x. a <= x /\ x <= b /\ ~(x = c) ==> (f x = g x)) /\ integrable(a,b) f
                        ==> integrable(a,b) g``,
  REWRITE_TAC[integrable] THEN MESON_TAC[DINT_POINT_SPIKE]);


(*INTEGRABLE_CONTINUOUS*)

val SUP_INTERVAL = store_thm("SUP_INTERVAL",
        ``!P a b.
        (?x. a <= x /\ x <= b /\ P x)
        ==> ?s. a <= s /\ s <= b /\
                !y. y < s <=> (?x. a <= x /\ x <= b /\ P x /\ y < x)``,
        REPEAT STRIP_TAC THEN
        MP_TAC(SPEC ``\x. a <= x /\ x <= b /\ P x`` REAL_SUP) THEN
        SUBGOAL_THEN``(?x. (\x. a <= x /\ x <= b /\ P x) x) /\
                (?z. !x. (\x. a <= x /\ x <= b /\ P x) x ==> x < z)``MP_TAC THENL
          [CONJ_TAC THENL
            [BETA_TAC THEN EXISTS_TAC``x:real`` THEN ASM_REWRITE_TAC[],
                 BETA_TAC THEN EXISTS_TAC``(b+1:real)`` THEN REPEAT STRIP_TAC THEN
                 ASM_SIMP_TAC arith_ss[REAL_LT_ADD1]],
           DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
           ABBREV_TAC ``s = sup (\x. a <= x /\ x <= b /\ P x)`` THEN
           DISCH_TAC THEN EXISTS_TAC ``s:real`` THEN
           ASM_MESON_TAC[REAL_LTE_TRANS, REAL_NOT_LE, REAL_LT_ANTISYM]]);

val BOLZANO_LEMMA_ALT = store_thm("BOLZANO_LEMMA_ALT",
  ``!P. (!a b c. a <= b /\ b <= c /\ P a b /\ P b c ==> P a c) /\
       (!x. ?d. &0 < d /\ (!a b. a <= x /\ x <= b /\ b - a < d ==> P a b))
       ==> !a b. a <= b ==> P a b``,
  GEN_TAC THEN MP_TAC(SPEC ``\(x:real,y:real). P x y :bool`` BOLZANO_LEMMA) THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);

val CONT_UNIFORM = store_thm("CONT_UNIFORM",
  ``!f a b. a <= b /\ (!x. a <= x /\ x <= b ==> f contl x)
           ==> !e. &0 < e ==> ?d. &0 < d /\
                                  !x y. a <= x /\ x <= b /\
                                        a <= y /\ y <= b /\
                                        abs(x - y) < d
                                        ==> abs(f(x) - f(y)) < e``,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC ``\c. ?d. &0 < d /\
                       !x y. a <= x /\ x <= c /\
                             a <= y /\ y <= c /\
                             abs(x - y) < d
                             ==> abs(f(x) - f(y)) < e``
         SUP_INTERVAL) THEN
  DISCH_THEN(MP_TAC o SPECL [``a:real``, ``b:real``]) THEN
  SUBGOAL_THEN``?x.
   a <= x /\ x <= b /\
   (\c.
      ?d.
        0 < d /\
        !x y.
          a <= x /\ x <= c /\ a <= y /\ y <= c /\ abs (x - y) < d ==>
          abs (f x - f y) < e) x``ASSUME_TAC THENL
   [EXISTS_TAC ``a:real`` THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    BETA_TAC THEN EXISTS_TAC ``&1`` THEN SIMP_TAC arith_ss[REAL_LT] THEN
        ASM_MESON_TAC[REAL_LE_ANTISYM, REAL_ARITH ``abs(x - x) = &0``],
        ALL_TAC] THEN
        ASM_SIMP_TAC arith_ss[] THEN
        DISCH_THEN(X_CHOOSE_THEN ``s:real`` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN ``?t. s < t /\ ?d. &0 < d /\
                                 !x y. a <= x /\ x <= t /\ a <= y /\ y <= t /\
                                       abs(x - y) < d ==> abs(f(x) - f(y)) < e``
     MP_TAC THENL
          [UNDISCH_TAC ``!x. a <= x /\ x <= b ==> f contl x`` THEN
           DISCH_THEN(MP_TAC o SPEC ``s:real``) THEN ASM_REWRITE_TAC[] THEN
           REWRITE_TAC[CONTL_LIM, LIM] THEN DISCH_THEN(MP_TAC o SPEC ``e / &2``) THEN
           ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT] THEN
           DISCH_THEN(X_CHOOSE_THEN ``d1:real`` STRIP_ASSUME_TAC) THEN
           SUBGOAL_THEN ``&0 < d1 / &2 /\ d1 / &2 < d1`` STRIP_ASSUME_TAC THENL
            [ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT, REAL_LT_LDIV_EQ,
                   REAL_ARITH ``(d < d * &2) = (&0 < d)``], ALL_TAC] THEN
           SUBGOAL_THEN ``!x y. abs(x - s) < d1 /\ abs(y - s) < d1
                        ==> abs(f(x) - f(y)) < e`` ASSUME_TAC THENL
                [REPEAT STRIP_TAC THEN
                 GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_HALF_DOUBLE] THEN
                 HO_MATCH_MP_TAC(REAL_ARITH
                                ``!a. abs(x - a) < e / &2 /\ abs(y - a) < e / &2
                                        ==> abs(x - y) < e / &2 + e / &2``) THEN
                 EXISTS_TAC ``(f:real->real) s`` THEN
                 SUBGOAL_THEN ``!x. abs(x - s) < d1 ==> abs(f x - f s) < e / &2``
                        (fn th => ASM_MESON_TAC[th]) THEN
             X_GEN_TAC ``u:real`` THEN REPEAT STRIP_TAC THEN
                 ASM_CASES_TAC ``u:real = s`` THENL
                  [ASM_SIMP_TAC arith_ss[REAL_SUB_REFL, ABS_N, REAL_LT_DIV, REAL_LT],
                   ALL_TAC] THEN
                 ASM_MESON_TAC[REAL_ARITH ``&0 < abs(x - s) <=> ~(x = s)``],
                 ALL_TAC] THEN
                 SUBGOAL_THEN ``s - d1 / &2 < s`` MP_TAC THENL
                  [ASM_REWRITE_TAC[REAL_ARITH ``x - y < x <=> &0 < y``],ALL_TAC] THEN
                 DISCH_THEN(fn th => FIRST_ASSUM(fn th' =>
                         MP_TAC(GEN_REWRITE_RULE I [][th'] th))) THEN
                 DISCH_THEN(X_CHOOSE_THEN ``r:real`` MP_TAC) THEN
                 DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
                 DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
                 DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
                 DISCH_THEN(X_CHOOSE_THEN ``d2:real`` STRIP_ASSUME_TAC) THEN
                 MP_TAC(SPECL [``d2:real``, ``d1 / &2``] REAL_DOWN2) THEN
                 ASM_REWRITE_TAC[] THEN
                 DISCH_THEN(X_CHOOSE_THEN ``d:real`` STRIP_ASSUME_TAC) THEN
                 EXISTS_TAC ``s + d / &2`` THEN
                 ASM_SIMP_TAC arith_ss[REAL_LT_DIV, REAL_LT,
                                                REAL_ARITH ``s < s + d = &0 < d``] THEN
                 EXISTS_TAC ``d:real`` THEN ASM_REWRITE_TAC[] THEN
                 MAP_EVERY X_GEN_TAC[``x:real``, ``y:real``] THEN STRIP_TAC THEN
                 ASM_CASES_TAC ``x <= r /\ y <= r`` THENL
                  [ASM_MESON_TAC[REAL_LT_TRANS], ALL_TAC] THEN
                 MATCH_MP_TAC(ASSUME ``!x y. abs(x - s) < d1 /\ abs(y - s) < d1 ==>
                                        abs(f x - f y) < e``) THEN
                 MATCH_MP_TAC(REAL_ARITH
                        ``!r t d d12.
                          ~(x <= r /\ y <= r) /\
                          abs(x - y) < d /\
                          s - d12 < r /\ t <= s + d /\
                          x <= t /\ y <= t /\ &2 * d12 <= e /\
                          &2 * d < e ==> abs(x - s) < e /\ abs(y - s) < e``) THEN
                 MAP_EVERY EXISTS_TAC[``r:real``,``s + d / &2``,``d:real``,``d1 / &2``] THEN
                 ASM_REWRITE_TAC[REAL_LE_LADD] THEN
                 SIMP_TAC arith_ss[REAL_DIV_LMUL, REAL_OF_NUM_EQ] THEN
                 ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
                 SIMP_TAC arith_ss[REAL_LE_LDIV_EQ, GSYM REAL_LT_RDIV_EQ, REAL_LT] THEN
                 ASM_SIMP_TAC arith_ss[REAL_ARITH ``&0 < d ==> d <= d * &2``, REAL_LE_REFL],
                 ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN ``t:real`` (CONJUNCTS_THEN ASSUME_TAC)) THEN
          SUBGOAL_THEN ``b <= t`` (fn th => ASM_MESON_TAC[REAL_LE_TRANS, th]) THEN
          FIRST_X_ASSUM(X_CHOOSE_THEN ``d:real`` STRIP_ASSUME_TAC) THEN
          UNDISCH_THEN ``!x. a <= x /\ x <= b ==> f contl x`` (K ALL_TAC) THEN
          FIRST_X_ASSUM(MP_TAC o assert(is_eq o concl) o SPEC ``s:real``) THEN
          REWRITE_TAC[REAL_LT_REFL] THEN CONV_TAC CONTRAPOS_CONV THEN
          REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN EXISTS_TAC ``t:real`` THEN
          ASM_MESON_TAC[REAL_LT_IMP_LE, REAL_LE_TRANS]);

val INTEGRABLE_CONTINUOUS = store_thm("INTEGRABLE_CONTINUOUS",
 ``!f a b. (!x. a <= x /\ x <= b ==> f contl x) ==> integrable(a,b) f``,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(REAL_ARITH ``b < a \/ a <= b``) THENL
   [ASM_MESON_TAC[integrable, DINT_WRONG], ALL_TAC] THEN
  MATCH_MP_TAC INTEGRABLE_LIMIT THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
  MP_TAC(SPECL[``f:real->real``, ``a:real``, ``b:real``] CONT_UNIFORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC ``e:real``) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN ``d:real`` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  UNDISCH_TAC ``a <= b`` THEN MAP_EVERY (fn t => SPEC_TAC(t,t))
   [``b:real``, ``a:real``] THEN
  HO_MATCH_MP_TAC BOLZANO_LEMMA_ALT THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [``u:real``, ``v:real``, ``w:real``] THEN
    NTAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fn th => DISCH_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC(TAUT_CONV
      ``(a /\ b) /\ (c /\ d ==> e) ==> (a ==> c) /\ (b ==> d) ==> e``) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS], ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC ``g:real->real``)
                               (X_CHOOSE_TAC ``h:real->real``)) THEN
    EXISTS_TAC ``\x. if x <= v then g(x):real else h(x)`` THEN
    CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THENL
          [ASM_MESON_TAC[REAL_LE_TOTAL],ASM_MESON_TAC[REAL_LE_TOTAL]],ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_COMBINE THEN EXISTS_TAC ``v:real`` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC INTEGRABLE_POINT_SPIKE THENL
     [EXISTS_TAC ``g:real->real``, EXISTS_TAC ``h:real->real``] THEN
    EXISTS_TAC ``v:real`` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC arith_ss[] THEN
        GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN``~(x<=v)``ASSUME_TAC THENL
         [ASM_MESON_TAC[REAL_ARITH ``b <= x /\ x <= c /\ ~(x = b) ==> ~(x <= b)``],
          RW_TAC std_ss[]], ALL_TAC] THEN
  X_GEN_TAC ``x:real`` THEN EXISTS_TAC ``d:real`` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [``u:real``, ``v:real``] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC ``\x:real. (f:real->real) u`` THEN
  ASM_REWRITE_TAC[INTEGRABLE_CONST] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss[REAL_LE_REFL] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC``x:real`` THEN
    ASM_REWRITE_TAC[],
        MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC``(x'-u):real`` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_EQ_IMP_LE THEN ONCE_REWRITE_TAC[ABS_REFL] THEN
          ASM_SIMP_TAC arith_ss[REAL_SUB_LE],
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC``(v-u):real`` THEN
          ASM_REWRITE_TAC[REAL_LE_SUB_CANCEL2]]]);

(* ------------------------------------------------------------------------- *)
(* Integrability on a subinterval.                                           *)
(* ------------------------------------------------------------------------- *)

val INTEGRABLE_SPLIT_SIDES = store_thm("INTEGRABLE_SPLIT_SIDES",
  ``!f a b c.
        a <= c /\ c <= b /\ integrable(a,b) f
        ==> ?i. !e. &0 < e
                    ==> ?g. gauge(\x. a <= x /\ x <= b) g /\
                            !d1 p1 d2 p2. tdiv(a,c) (d1,p1) /\
                                          fine g (d1,p1) /\
                                          tdiv(c,b) (d2,p2) /\
                                          fine g (d2,p2)
                                          ==> abs((rsum(d1,p1) f +
                                                   rsum(d2,p2) f) - i) < e``,
  REPEAT GEN_TAC THEN REWRITE_TAC[integrable, Dint] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``i:real`` THEN
  HO_MATCH_MP_TAC MONO_ALL THEN X_GEN_TAC ``e:real`` THEN
  ASM_CASES_TAC ``&0 < e`` THEN ASM_REWRITE_TAC[] THEN
  HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``g:real->real`` THEN
  ASM_MESON_TAC[DIVISION_APPEND_STRONG] THEN ASM_REWRITE_TAC[]);

val INTEGRABLE_SUBINTERVAL_LEFT = store_thm("INTEGRABLE_SUBINTERVAL_LEFT",
  ``!f a b c. a <= c /\ c <= b /\ integrable(a,b) f ==> integrable(a,c) f``,
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   FIRST_ASSUM(X_CHOOSE_TAC ``i:real`` o MATCH_MP INTEGRABLE_SPLIT_SIDES) THEN
   REWRITE_TAC[INTEGRABLE_CAUCHY] THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC ``e / &2``) THEN
   SIMP_TAC arith_ss[ASSUME ``&0 < e``, REAL_LT_DIV, REAL_LT] THEN
   HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``g:real->real`` THEN STRIP_TAC THEN
   CONJ_TAC THENL
    [UNDISCH_TAC ``gauge (\x. a <= x /\ x <= b) g`` THEN
         REWRITE_TAC[gauge] THEN ASM_MESON_TAC[REAL_LE_TRANS],ALL_TAC] THEN
         REPEAT STRIP_TAC THEN
         MP_TAC(SPECL [``c:real``, ``b:real``, ``g:real->real``]
                                DIVISION_EXISTS) THEN
         SUBGOAL_THEN``c <= b /\ gauge (\x. c <= x /\ x <= b) g``ASSUME_TAC THENL
          [ASM_REWRITE_TAC[] THEN
           UNDISCH_TAC ``gauge (\x. a <= x /\ x <= b) g`` THEN
           REWRITE_TAC[gauge] THEN ASM_MESON_TAC[REAL_LE_TRANS],ALL_TAC] THEN
           ASM_REWRITE_TAC[] THEN SIMP_TAC arith_ss[GSYM LEFT_FORALL_IMP_THM] THEN
         MAP_EVERY X_GEN_TAC [``d:num->real``, ``p:num->real``] THEN STRIP_TAC THEN
         FIRST_X_ASSUM(fn th =>
      MP_TAC(SPECL [``d1:num->real``, ``p1:num->real``] th) THEN
      MP_TAC(SPECL [``d2:num->real``, ``p2:num->real``] th)) THEN
         SIMP_TAC arith_ss[AND_IMP_INTRO, GSYM FORALL_AND_THM] THEN
         DISCH_THEN(MP_TAC o SPECL [``d:num->real``, ``p:num->real``]) THEN
         ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
         MATCH_MP_TAC REAL_LET_TRANS THEN
         EXISTS_TAC``abs ((rsum (d1,p1) f + rsum (d,p) f - i) -
                                (rsum (d2,p2) f + rsum (d,p) f - i))`` THEN
         CONJ_TAC THENL
          [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
           REWRITE_TAC[REAL_ARITH``a + b - i -(c + b - i) = a - c``],
           MATCH_MP_TAC REAL_LET_TRANS THEN
           EXISTS_TAC``abs (rsum (d1,p1) f + rsum (d,p) f - i) +
                                        abs(rsum (d2,p2) f + rsum (d,p) f - i)`` THEN
           CONJ_TAC THENL
            [REWRITE_TAC[REAL_ARITH``abs(a - b) <= abs a + abs b``],
                 GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_HALF_DOUBLE] THEN
                 MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]]]);

val INTEGRABLE_SUBINTERVAL_RIGHT = store_thm("INTEGRABLE_SUBINTERVAL_RIGHT",
  ``!f a b c. a <= c /\ c <= b /\ integrable(a,b) f ==> integrable(c,b) f``,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC ``i:real`` o MATCH_MP INTEGRABLE_SPLIT_SIDES) THEN
  REWRITE_TAC[INTEGRABLE_CAUCHY] THEN X_GEN_TAC ``e:real`` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC ``e / &2``) THEN
  SIMP_TAC arith_ss[ASSUME ``&0 < e``, REAL_LT_DIV, REAL_LT] THEN
  HO_MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC ``g:real->real`` THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC ``gauge (\x. a <= x /\ x <= b) g`` THEN
         REWRITE_TAC[gauge] THEN ASM_MESON_TAC[REAL_LE_TRANS], ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
         MP_TAC(SPECL [``a:real``, ``c:real``, ``g:real->real``]
                                DIVISION_EXISTS) THEN
  SUBGOAL_THEN``a <= c /\ gauge (\x. a <= x /\ x <= c) g``ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC ``gauge (\x. a <= x /\ x <= b) g`` THEN
        REWRITE_TAC[gauge] THEN ASM_MESON_TAC[REAL_LE_TRANS], ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN SIMP_TAC arith_ss[GSYM LEFT_FORALL_IMP_THM] THEN
         MAP_EVERY X_GEN_TAC [``d:num->real``, ``p:num->real``] THEN STRIP_TAC THEN
         FIRST_X_ASSUM(MP_TAC o SPECL [``d:num->real``, ``p:num->real``]) THEN
         DISCH_THEN(fn th =>
   MP_TAC(SPECL [``d1:num->real``, ``p1:num->real``] th) THEN
   MP_TAC(SPECL [``d2:num->real``, ``p2:num->real``] th)) THEN
   ASM_REWRITE_TAC[] THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC``abs ((rsum (d,p) f + rsum (d1,p1) f - i) -
                                (rsum (d,p) f + rsum (d2,p2) f - i))`` THEN
   CONJ_TAC THENL
    [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
         REWRITE_TAC[REAL_ARITH``a + b - i -(a + c - i) = b - c``], ALL_TAC] THEN
   MATCH_MP_TAC REAL_LET_TRANS THEN
   EXISTS_TAC``abs (rsum (d,p) f + rsum (d1,p1) f - i) +
                                abs(rsum (d,p) f + rsum (d2,p2) f - i)`` THEN
   CONJ_TAC THENL
    [REWRITE_TAC[REAL_ARITH``abs(a - b) <= abs a + abs b``],
         GEN_REWRITE_TAC RAND_CONV [] [GSYM REAL_HALF_DOUBLE] THEN
                 MATCH_MP_TAC REAL_LT_ADD2 THEN ASM_REWRITE_TAC[]]);

val INTEGRABLE_SUBINTERVAL = store_thm("INTEGRABLE_SUBINTERVAL",
  ``!f a b c d. a <= c /\ c <= d /\ d <= b /\ integrable(a,b) f
               ==> integrable(c,d) f``,
  MESON_TAC[INTEGRABLE_SUBINTERVAL_LEFT, INTEGRABLE_SUBINTERVAL_RIGHT,
            REAL_LE_TRANS]);

(* ------------------------------------------------------------------------- *)
(* More basic lemmas about integration.                                      *)
(* ------------------------------------------------------------------------- *)

val INTEGRAL_0 = store_thm("INTEGRAL_0",
  ``!a b. a <= b ==> (integral(a,b) (\x. 0) = 0)``,
  RW_TAC std_ss[] THEN MATCH_MP_TAC DINT_INTEGRAL THEN
  ASM_REWRITE_TAC[DINT_0]);

val INTEGRAL_CONST = store_thm("INTEGRAL_CONST",
 (--`!a b c. a <= b ==> (integral(a,b) (\x. c) = c * (b - a))`--),
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DINT_INTEGRAL THEN
  ASM_SIMP_TAC arith_ss[DINT_CONST]);

val INTEGRAL_CMUL = store_thm("INTEGRAL_CMUL",
(--`!f c a b. a <= b /\ integrable(a,b) f
           ==> (integral(a,b) (\x. c * f(x)) = c * integral(a,b) f)`--),
        REPEAT STRIP_TAC THEN MATCH_MP_TAC DINT_INTEGRAL THEN
        ASM_SIMP_TAC arith_ss[DINT_CMUL, INTEGRABLE_DINT]);

val INTEGRAL_ADD = store_thm("INTEGRAL_ADD",
(--`!f g a b. a <= b /\ integrable(a,b) f /\ integrable(a,b) g
             ==> (integral(a,b) (\x. f(x) + g(x)) =
                 integral(a,b) f + integral(a,b) g)`--),
        REPEAT STRIP_TAC THEN MATCH_MP_TAC DINT_INTEGRAL THEN
        ASM_SIMP_TAC arith_ss[DINT_ADD, INTEGRABLE_DINT]);

val INTEGRAL_SUB = store_thm("INTEGRAL_SUB",
 (--`!f g a b. a <= b /\ integrable(a,b) f /\ integrable(a,b) g
             ==> (integral(a,b) (\x. f(x) - g(x)) =
                 integral(a,b) f - integral(a,b) g)`--),
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DINT_INTEGRAL THEN
  ASM_SIMP_TAC arith_ss[DINT_SUB, INTEGRABLE_DINT]);

val INTEGRAL_BY_PARTS = store_thm("INTEGRAL_BY_PARTS",
  ``!f g f' g' a b.
         a <= b /\
         (!x. a <= x /\ x <= b ==> (f diffl f' x) x) /\
         (!x. a <= x /\ x <= b ==> (g diffl g' x) x) /\
         integrable(a,b) (\x. f' x * g x) /\
         integrable(a,b) (\x. f x * g' x)
         ==> (integral(a,b) (\x. f x * g' x) =
              (f b * g b - f a * g a) - integral(a,b) (\x. f' x * g x))``,
  MP_TAC INTEGRATION_BY_PARTS THEN REPEAT(HO_MATCH_MP_TAC MONO_ALL THEN GEN_TAC) THEN
  DISCH_THEN(fn th => STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJ (ASSUME ``a <= b``)) THEN
  DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP DINT_INTEGRAL) THEN
  ASM_SIMP_TAC arith_ss[INTEGRAL_ADD] THEN REAL_ARITH_TAC);

val INTEGRAL_COMBINE = store_thm("INTEGRAL_COMBINE",
  ``!f a b c. a <= b /\ b <= c /\ (integrable (a,c) f) ==>
      (integral (a,c) f = (integral (a,b) f) + (integral (b,c) f))``,
  RW_TAC std_ss[integral] THEN SELECT_ELIM_TAC THEN RW_TAC std_ss[] THENL
   [FULL_SIMP_TAC std_ss[integrable] THEN EXISTS_TAC ``i:real`` THEN
    ASM_REWRITE_TAC[],
        SELECT_ELIM_TAC THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM integrable] THEN MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
          MAP_EVERY EXISTS_TAC[``a:real``,``c:real``] THEN
          RW_TAC std_ss[REAL_LE_REFL, integrable],
          SELECT_ELIM_TAC THEN CONJ_TAC THENL
           [REWRITE_TAC[GSYM integrable] THEN MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
                MAP_EVERY EXISTS_TAC[``a:real``,``c:real``] THEN
                RW_TAC std_ss[REAL_LE_REFL, integrable],
                RW_TAC std_ss[] THEN MATCH_MP_TAC DINT_UNIQ THEN
                MAP_EVERY EXISTS_TAC[``a:real``,``c:real``,``f:real->real``] THEN
                RW_TAC std_ss[] THENL
                 [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC ``b:real`` THEN
                  RW_TAC std_ss[],
                  MATCH_MP_TAC DINT_COMBINE THEN EXISTS_TAC ``b:real`` THEN
                  RW_TAC std_ss[]]]]]);

(* ------------------------------------------------------------------------- *)
(* Mean value theorem of integral.                                           *)
(* ------------------------------------------------------------------------- *)

val INTEGRAL_MVT1 = store_thm("INTEGRAL_MVT1",
  ``!f a b. (a <= b /\(!x. a<=x /\ x<=b ==> f contl x)) ==>
  (?x. a<=x /\ x<=b /\ (integral(a,b) f = f(x)*(b-a)))``,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL[``f:real->real``,``a:real``,``b:real``]CONT_ATTAINS_ALL) THEN
  REWRITE_TAC[TAUT_CONV``((a ==> b) ==> (a ==> c)) = (a ==> b ==> c)``] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC``a:real=b`` THENL
   [EXISTS_TAC``b:real`` THEN ASM_SIMP_TAC std_ss[REAL_LE_REFL] THEN
    ASM_SIMP_TAC std_ss[REAL_SUB_REFL,REAL_MUL_RZERO] THEN
        MATCH_MP_TAC DINT_INTEGRAL THEN
        ASM_SIMP_TAC std_ss[REAL_LE_REFL,INTEGRAL_NULL], ALL_TAC] THEN
  SUBGOAL_THEN``?x:real. a<=x /\ x<=b /\
                                (f x = inv(b-a)* integral(a,b) f)``ASSUME_TAC THENL
   [UNDISCH_TAC``!y. L <= y /\ y <= M ==> ?x. a <= x /\ x<=b /\ (f x = y)`` THEN
    DISCH_THEN(MP_TAC o SPEC``inv(b-a)* integral(a,b)f``) THEN
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN``(L*(b-a) <= integral(a,b) f) /\
                                (integral(a,b) f <= M*(b-a))``ASSUME_TAC THENL
        [CONJ_TAC THENL
     [SUBGOAL_THEN``L*(b-a)=integral(a,b)(\x. L)``ASSUME_TAC THENL
           [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_CONST THEN
            ASM_REWRITE_TAC[],ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_LE THEN
                ASM_SIMP_TAC std_ss[INTEGRABLE_CONTINUOUS,
                                                  INTEGRABLE_CONST,REAL_LT_IMP_LE]],
          SUBGOAL_THEN``M*(b-a) = integral(a,b)(\x. M)``ASSUME_TAC THENL
           [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_CONST THEN
            ASM_REWRITE_TAC[], ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRAL_LE THEN
                ASM_SIMP_TAC std_ss[INTEGRABLE_CONTINUOUS,
                                                  INTEGRABLE_CONST,REAL_LT_IMP_LE]]],ALL_TAC] THEN
    SUBGOAL_THEN``L <= inv(b-a) * integral(a,b) f /\
                                inv(b-a) * integral(a,b) f <= M``MP_TAC THENL
         [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
          CONJ_TAC THENL
          [MATCH_MP_TAC REAL_LE_RDIV THEN
           ASM_SIMP_TAC std_ss[REAL_SUB_LT,REAL_LT_LE],
           MATCH_MP_TAC REAL_LE_LDIV THEN
           ASM_SIMP_TAC std_ss[REAL_SUB_LT,REAL_LT_LE]],ALL_TAC] THEN
        ASM_SIMP_TAC std_ss[],ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN``x:real``STRIP_ASSUME_TAC) THEN
  EXISTS_TAC``x:real``THEN ASM_SIMP_TAC std_ss[REAL_ARITH``a*b*c=c*a*b``] THEN
  SUBGOAL_THEN``(b:real -a)*inv(b-a)=1``ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN MATCH_MP_TAC REAL_POS_NZ THEN
    ASM_SIMP_TAC std_ss[REAL_SUB_LT,REAL_LT_LE],ALL_TAC] THEN
  ASM_SIMP_TAC std_ss[REAL_MUL_LID]);

val _ = export_theory();
