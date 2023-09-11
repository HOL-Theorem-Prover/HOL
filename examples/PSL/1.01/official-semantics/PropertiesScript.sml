
(*****************************************************************************)
(* Some properties of the Sugar 2.0 semantics                                *)
(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* Started: Tue Dec 31 2002                                                  *)
(* Semantics changed (additional ``LENGTH w > 0`` added): Mon Feb 10 2003    *)
(*****************************************************************************)

(*****************************************************************************)
(* START BOILERPLATE                                                         *)
(*****************************************************************************)

(******************************************************************************
* Load theories
* (commented out for compilation)
******************************************************************************)
(*
quietdec := true;
loadPath := "../official-semantics" :: "../regexp" :: !loadPath;
map load
 ["bossLib", "KripkeTheory", "UnclockedSemanticsTheory",
  "SyntacticSugarTheory", "ClockedSemanticsTheory", "RewritesTheory",
  "rich_listTheory", "intLib", "res_quanLib", "res_quanTheory"];
open KripkeTheory FinitePSLPathTheory PSLPathTheory SyntaxTheory SyntacticSugarTheory
     UnclockedSemanticsTheory ClockedSemanticsTheory RewritesTheory
     arithmeticTheory listTheory rich_listTheory res_quanLib res_quanTheory
     ClockedSemanticsTheory;
val _ = intLib.deprecate_int();
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;

(******************************************************************************
* Open theories
******************************************************************************)
open KripkeTheory FinitePSLPathTheory PSLPathTheory SyntaxTheory SyntacticSugarTheory
     UnclockedSemanticsTheory ClockedSemanticsTheory RewritesTheory
     arithmeticTheory listTheory rich_listTheory res_quanLib res_quanTheory
     ClockedSemanticsTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Versions of simpsets that deal properly with theorems containing SUC
******************************************************************************)
val simp_arith_ss = simpLib.++ (arith_ss, numSimps.SUC_FILTER_ss);
val simp_list_ss  = simpLib.++ (list_ss,  numSimps.SUC_FILTER_ss);

(******************************************************************************
* Set default parsing to natural numbers rather than integers
******************************************************************************)
val _ = intLib.deprecate_int();

(******************************************************************************
* A simpset fragment to rewrite away quantifiers restricted with :: (a to b)
******************************************************************************)
val resq_SS =
 simpLib.merge_ss
  [res_quanTools.resq_SS,
   rewrites
    [num_to_def,xnum_to_def,IN_DEF,num_to_def,xnum_to_def,LENGTH_def]];

(******************************************************************************
* Start a new theory called Properties
******************************************************************************)
val _ = new_theory "Properties";
val _ = ParseExtras.temp_loose_equality()


(******************************************************************************
* Set default path theory to FinitePSLPathTheory
******************************************************************************)
local open FinitePSLPathTheory in

(******************************************************************************
* w |=T b is equivalent to ?l. (w =[l]) /\ l |= b
******************************************************************************)
val S_BOOL_TRUE =
 store_thm
  ("S_BOOL_TRUE",
   ``S_SEM w B_TRUE (S_BOOL b) = ?l. (w =[l]) /\ B_SEM l b``,
   RW_TAC (arith_ss ++ resq_SS)
    [S_SEM_def,B_SEM,CONJ_ASSOC,LENGTH1,B_SEM_def,
     Cooper.COOPER_PROVE``(n:num >= 1 /\ (!i:num. ~(i < n-1))) = (n = 1)``]
    THEN EQ_TAC
    THEN RW_TAC simp_list_ss []
    THEN FULL_SIMP_TAC simp_list_ss [LENGTH,ELEM_def,RESTN_def,HEAD_def]);

(******************************************************************************
* Some lemmas about NEXT_RISE
******************************************************************************)
val S_REPEAT_BOOL_TRUE =
 store_thm
  ("S_REPEAT_BOOL_TRUE",
   ``S_SEM w B_TRUE (S_REPEAT(S_BOOL b))  =
      !i. i < LENGTH w ==> B_SEM (EL i w) b``,
   RW_TAC (arith_ss ++ resq_SS)
    [S_SEM_def,B_SEM,CONJ_ASSOC,LENGTH_CONS,LENGTH_NIL,ELEM_EL,
     Cooper.COOPER_PROVE ``(n:num >= 1 /\ !i:num. ~(i < n-1)) = (n = 1)``]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [IMP_RES_TAC
       (SIMP_RULE std_ss [] (Q.ISPEC `\x. B_SEM x b` ALL_EL_CONCAT))
       THEN POP_ASSUM(ASSUME_TAC o SIMP_RULE std_ss [EVERY_EL])
       THEN RES_TAC,
      Q.EXISTS_TAC `MAP (\l. [l]) w`
       THEN RW_TAC list_ss
             [EVERY_EL,CONCAT_MAP_SINGLETON,LENGTH_EL_MAP_SINGLETON,
              HD_EL_MAP]]);

end;

(******************************************************************************
* NEXT_RISE w c (i,j)  =   w^{i,j} |=T {(\neg c)[*];c}
* (i is the first rising edge after j of clock c in word w)
******************************************************************************)
val NEXT_RISE_def =
 Define
  `NEXT_RISE w c (i,j) =
    S_SEM
     (SEL w (i,j))
     B_TRUE
     (S_CAT(S_REPEAT(S_BOOL(B_NOT c)),S_BOOL c))`;

val NEXT_RISE_IMP =
 store_thm
  ("NEXT_RISE_IMP",
   ``NEXT_RISE p c (i,j) ==>
      (!k. i <= k /\ k < j ==> ~B_SEM (ELEM p k) c)
      /\
      (i <= j ==> B_SEM (ELEM p j) c)``,
   REWRITE_TAC [NEXT_RISE_def,ELEM_EL]
    THEN ONCE_REWRITE_TAC[S_SEM_def]
    THEN SIMP_TAC list_ss
          [S_REPEAT_BOOL_TRUE,S_BOOL_TRUE,B_SEM]
    THEN ONCE_REWRITE_TAC [EQ_SINGLETON]
    THEN RW_TAC std_ss []
    THENL
     [ASSUM_LIST(fn thl => ASSUME_TAC(ONCE_REWRITE_RULE[el 4 thl](el 6 thl)))
       THEN IMP_RES_TAC(DECIDE ``i <= k ==> k < j ==> k < j``)
       THEN `j > i` by DECIDE_TAC
       THEN IMP_RES_TAC SEL_APPEND_SINGLETON
       THEN ASSUM_LIST(fn thl => ASSUME_TAC(Q.AP_TERM `EL (k-i)` (el 2 thl)))
       THEN `k <= j-1` by DECIDE_TAC
       THEN IMP_RES_TAC(Q.INST_TYPE[`:'a`|->`:'a->bool`]EL_SEL)
       THEN `ELEM p k = EL (k - i) w1` by PROVE_TAC[]
       THEN ASM_REWRITE_TAC []
       THEN ASSUM_LIST
              (fn thl
                => ASSUME_TAC
                    (Q.AP_TERM
                     `list$LENGTH`
                     (el 7 thl)))
       THEN POP_ASSUM(ASSUME_TAC o REWRITE_RULE[LENGTH_SEL])
       THEN `k-i < LENGTH w1` by DECIDE_TAC
       THEN PROVE_TAC[],
      ASSUM_LIST(fn thl => ASSUME_TAC(ONCE_REWRITE_RULE[el 3 thl](el 5 thl)))
       THEN ASSUM_LIST
             (fn thl =>
               ASSUME_TAC
                (SIMP_RULE arith_ss
                  [LENGTH_MAP,LENGTH_APPEND,LENGTH,SEL_def,
                   LENGTH_SEL_REC]
                  (Q.AP_TERM `list$LENGTH` (el 1 thl))))
       THEN Cases_on `i=j`
       THENL
        [`w1 = []` by PROVE_TAC [LENGTH_NIL, SUB_EQUAL_0]
          THEN RW_TAC arith_ss []
          THEN FULL_SIMP_TAC list_ss [LENGTH,SEL_ELEM]
          THEN PROVE_TAC[ELEM_EL],
         `j > i` by DECIDE_TAC
          THEN IMP_RES_TAC SEL_APPEND_SINGLETON
          THEN PROVE_TAC[ELEM_EL]]]);

val NEXT_RISE_REVIMP =
 store_thm
  ("NEXT_RISE_REVIMP",
   ``i <= j                                         /\
     (!k. i <= k /\ k < j ==> ~B_SEM (ELEM p k) c)  /\
     B_SEM (ELEM p j) c
     ==>
     NEXT_RISE p c (i,j)``,
   REWRITE_TAC [NEXT_RISE_def]
    THEN ONCE_REWRITE_TAC[S_SEM_def]
    THEN RW_TAC list_ss
          [S_REPEAT_BOOL_TRUE,S_BOOL_TRUE,B_SEM]
    THEN Cases_on `i=j`
     THENL
      [RW_TAC std_ss []
        THEN Q.EXISTS_TAC `[]`
        THEN Q.EXISTS_TAC `SEL p (i,i)`
        THEN RW_TAC list_ss [SEL_ELEM],
      Q.EXISTS_TAC `SEL p (i,j-1)`
        THEN Q.EXISTS_TAC `SEL p (j,j)`
        THEN RW_TAC list_ss []
        THENL
         [`i <= j-1 /\ j-1 < j /\ ((j-1)+1 = j)` by DECIDE_TAC
            THEN PROVE_TAC[SEL_SPLIT],
          POP_ASSUM
            (ASSUME_TAC o
             SIMP_RULE arith_ss
              [SEL_def,SEL_REC_def,LENGTH_SEL_REC])
           THEN `i <= i+i' /\ i+i' < j` by DECIDE_TAC
           THEN RES_TAC
           THEN POP_ASSUM(K ALL_TAC)
           THEN `(i+i') - i = i'` by DECIDE_TAC
           THEN `i <= i+i' /\ i+i' <= j-1` by DECIDE_TAC
           THEN IMP_RES_TAC(Q.INST_TYPE[`:'a`|->`:'a->bool`]EL_SEL)
           THEN POP_ASSUM(K ALL_TAC)
           THEN POP_ASSUM
                 (ASSUME_TAC o REWRITE_RULE[DECIDE``i + i' - i = i'``] o SPEC_ALL)
           THEN RW_TAC std_ss [],
          Q.EXISTS_TAC `ELEM p j`
           THEN RW_TAC list_ss [SEL_ELEM]]]);

val NEXT_RISE =
 store_thm
  ("NEXT_RISE",
   ``i <= j
     ==>
     (NEXT_RISE p c (i,j) =
       (!k. i <= k /\ k < j ==> ~B_SEM (ELEM p k) c)
       /\
       B_SEM (ELEM p j) c)``,
   PROVE_TAC[NEXT_RISE_IMP, NEXT_RISE_REVIMP]);

val NEXT_RISE_TRUE =
 store_thm
  ("NEXT_RISE_TRUE",
   ``i <= j ==> (NEXT_RISE p B_TRUE (i,j) = (i = j))``,
   RW_TAC std_ss [NEXT_RISE,B_SEM]
    THEN EQ_TAC
    THENL
     [RW_TAC arith_ss []
       THEN POP_ASSUM(ASSUME_TAC o SIMP_RULE arith_ss [] o SPEC ``i:num``)
       THEN DECIDE_TAC,
      intLib.COOPER_TAC]);

val NEXT_RISE_TRUE_COR =
 store_thm
  ("NEXT_RISE_TRUE_COR",
   ``i <= j /\ NEXT_RISE p B_TRUE (i,j) = (i = j)``,
   EQ_TAC
    THEN RW_TAC arith_ss [NEXT_RISE_TRUE]
    THEN PROVE_TAC[NEXT_RISE_TRUE]);

val NEXT_RISE_TRUE_EXISTS =
 store_thm
  ("NEXT_RISE_TRUE_EXISTS",
   ``?k. NEXT_RISE p B_TRUE (j,k)``,
   Q.EXISTS_TAC `j`
    THEN RW_TAC std_ss
     [SIMP_RULE arith_ss [] (Q.SPECL[`p`,`j`,`j`](GEN_ALL NEXT_RISE_TRUE))]);

val NEXT_RISE_LEQ_TRUE_EXISTS =
 store_thm
  ("NEXT_RISE_LEQ_TRUE_EXISTS",
   ``?k. j <= k /\ NEXT_RISE p B_TRUE (j,k)``,
   Q.EXISTS_TAC `j`
    THEN RW_TAC arith_ss
     [SIMP_RULE arith_ss [] (Q.SPECL[`p`,`j`,`j`](GEN_ALL NEXT_RISE_TRUE))]);

val NEXT_RISE_LESS =
 store_thm
  ("NEXT_RISE_LESS",
   ``i <= j /\ NEXT_RISE p c (i,j) =
      i <= j
      /\
      (!k. i <= k /\ k < j ==> ~B_SEM (ELEM p k) c)
      /\
      B_SEM (ELEM p j) c``,
   PROVE_TAC[NEXT_RISE]);

val NEXT_RISE_RESTN =
 store_thm
  ("NEXT_RISE_RESTN",
   ``!i j p. NEXT_RISE (RESTN p i) c (j,k) = NEXT_RISE p c (i+j,i+k)``,
   Induct
    THEN RW_TAC arith_ss [NEXT_RISE, RESTN_def,ELEM_RESTN]
    THEN RW_TAC arith_ss [NEXT_RISE_def]
    THEN `SEL (REST p) (i + j,i + k) = SEL (RESTN p 1) (i + j,i + k)`
         by PROVE_TAC[RESTN_def, DECIDE``SUC 0 = 1``]
    THEN RW_TAC arith_ss [SEL_RESTN, DECIDE``i + (j + 1) = j + SUC i``]);

val NEXT_TRUE_GE =
 store_thm
  ("NEXT_TRUE_GE",
   ``x' >= x /\ NEXT_RISE p B_TRUE (x,x') = (x=x')``,
   EQ_TAC
    THEN RW_TAC arith_ss [NEXT_RISE_TRUE]
    THEN IMP_RES_TAC(DECIDE``x':num >= x:num = x <= x'``)
    THEN FULL_SIMP_TAC std_ss [NEXT_RISE_TRUE]);

(******************************************************************************
* Structural induction rule for SEREs
******************************************************************************)
val sere_induct = save_thm
  ("sere_induct",
   Q.GEN
    `P`
    (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2 /\ B3)) ==> (A ==> B1)``)
     (SIMP_RULE
       std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P x ==> Q(x,y)) = !x. P x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P y ==> Q(x,y)) = !y. P y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P`,`\ (r,b). P r`,`\ (r1,r2). P r1 /\ P r2`]
         (TypeBase.induction_of ``:'a sere``)))));

(******************************************************************************
* S_CLOCK_FREE r means r contains no clocking statements
******************************************************************************)
val S_CLOCK_FREE_def =
 Define
  `(S_CLOCK_FREE (S_BOOL b)          = T)
   /\
   (S_CLOCK_FREE (S_CAT(r1,r2))      =  S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2)
   /\
   (S_CLOCK_FREE (S_FUSION(r1,r2))   = S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2)
   /\
   (S_CLOCK_FREE (S_OR(r1,r2))       = S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2)
   /\
   (S_CLOCK_FREE (S_AND(r1,r2))      = S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2)
   /\
   (S_CLOCK_FREE (S_REPEAT r)        = S_CLOCK_FREE r)
   /\
   (S_CLOCK_FREE (S_CLOCK v)         = F)`;

(******************************************************************************
* Proof that if S_CLOCK_FREE r then the unclocked semantics of
* a SERE r is the same as the clocked semantics with clock equal to T
******************************************************************************)

val S_SEM_TRUE_LEMMA =
 store_thm
  ("S_SEM_TRUE_LEMMA",
   ``!r w.
      S_CLOCK_FREE r
      ==>
      (S_SEM w B_TRUE r = US_SEM w r)``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THEN RW_TAC std_ss [S_SEM_def, US_SEM_def, S_CLOCK_FREE_def]
    THEN RW_TAC (arith_ss ++ resq_SS)
          [B_SEM,CONJ_ASSOC,LENGTH1,
           Cooper.COOPER_PROVE``(n:num >= 1 /\ (!i:num. ~(i < n-1))) = (n = 1)``]
    THEN EQ_TAC
    THEN RW_TAC list_ss [LENGTH]
    THEN FULL_SIMP_TAC list_ss [LENGTH]);

val S_SEM_TRUE =
 store_thm
  ("S_SEM_TRUE",
   ``S_CLOCK_FREE r ==> !w. S_SEM w B_TRUE r = US_SEM w r``,
   Cases_on `r`
    THEN RW_TAC std_ss [S_SEM_TRUE_LEMMA]);

(******************************************************************************
* Structural induction rule for FL formulas
******************************************************************************)
val fl_induct =
 save_thm
  ("fl_induct",
   Q.GEN
    `P`
    (MATCH_MP
     (DECIDE ``(A ==> (B1 /\ B2 /\ B3)) ==> (A ==> B1)``)
     (SIMP_RULE
       std_ss
       [pairTheory.FORALL_PROD,
        PROVE[]``(!x y. P x ==> Q(x,y)) = !x. P x ==> !y. Q(x,y)``,
        PROVE[]``(!x y. P y ==> Q(x,y)) = !y. P y ==> !x. Q(x,y)``]
       (Q.SPECL
         [`P`,`\ (r,f). P f`,`\ (f,b). P f`,`\ (f1,f2). P f1 /\ P f2`]
         (TypeBase.induction_of ``:'a fl``)))));

(******************************************************************************
* Negated clocking of f with T! equal to clocking with T of F_NOT f:
* p |=T !f  <==>  ~(p |=T f)
******************************************************************************)
val F_SEM_TRUE_WEAK_NOT_EQ =
 store_thm
  ("F_SEM_TRUE_WEAK_NOT_EQ",
   ``!f p. F_SEM p B_TRUE (F_NOT f) = ~(F_SEM p B_TRUE f)``,
   INDUCT_THEN fl_induct ASSUME_TAC
    THEN RW_TAC std_ss [F_SEM_def]);

(******************************************************************************
* F_CLOCK_FREE f means f contains no clocking statements
******************************************************************************)
val F_CLOCK_FREE_def =
 Define
  `(F_CLOCK_FREE (F_BOOL b)            = T)
   /\
   (F_CLOCK_FREE (F_NOT f)             = F_CLOCK_FREE f)
   /\
   (F_CLOCK_FREE (F_AND(f1,f2))        = F_CLOCK_FREE f1 /\ F_CLOCK_FREE f2)
   /\
   (F_CLOCK_FREE (F_NEXT f)            = F_CLOCK_FREE f)
   /\
   (F_CLOCK_FREE (F_UNTIL(f1,f2))      = F_CLOCK_FREE f1 /\ F_CLOCK_FREE f2)
   /\
   (F_CLOCK_FREE (F_SUFFIX_IMP(r,f))   = F_CLOCK_FREE f /\ S_CLOCK_FREE r)
   /\
   (F_CLOCK_FREE (F_STRONG_IMP(r1,r2)) = S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2)
   /\
   (F_CLOCK_FREE (F_WEAK_IMP(r1,r2))   = S_CLOCK_FREE r1 /\ S_CLOCK_FREE r2)
   /\
   (F_CLOCK_FREE (F_ABORT (f,b))       = F_CLOCK_FREE f)
   /\
   (F_CLOCK_FREE (F_STRONG_CLOCK v)    = F)`;

(******************************************************************************
* If F_CLOCK_FREE f then the unclocked semantics of an
* FL formula f is the same as the clocked semantics with clock equal to T!
* (i.e. strongly clocked)
******************************************************************************)
local
val INIT_TAC =
 RW_TAC (arith_ss  ++ resq_SS)
  [F_SEM_def,UF_SEM_def,F_CLOCK_FREE_def,RESTN_def,GSYM NEXT_RISE_def];
in
val F_SEM_TRUE_LEMMA =
 store_thm
  ("F_SEM_TRUE_LEMMA",
   ``!f p. F_CLOCK_FREE f ==> (F_SEM p B_TRUE f = UF_SEM p f)``,
   INDUCT_THEN fl_induct ASSUME_TAC (* 10 subgoals *)
    THENL
     [(* 1. F_BOOL b *)
      INIT_TAC,
      (* 2. F_NOT b *)
      INIT_TAC,
      (* 3. F_AND (f1,f2) *)
      INIT_TAC,
      (* 4. F_NEXT f *)
      Cases
       THEN INIT_TAC
       THEN EQ_TAC
       THEN RW_TAC (arith_ss ++ resq_SS) [GT]
       THEN IMP_RES_TAC NEXT_RISE_TRUE
       THEN TRY DECIDE_TAC
       THEN FULL_SIMP_TAC (std_ss++resq_SS) [num_to_def,xnum_to_def,NEXT_RISE_TRUE]
       THEN TRY(PROVE_TAC[])
       THEN RW_TAC arith_ss [NEXT_RISE_TRUE]
       THEN Q.EXISTS_TAC `1`
       THEN RW_TAC arith_ss [NEXT_RISE_TRUE],
      (* 5. F_UNTIL(f1,f2) f *)
      Cases THEN INIT_TAC THEN RW_TAC std_ss [B_SEM],
      (* 6. F_SUFFIX_IMP(s,f) *)
      Cases_on `p`
       THEN INIT_TAC
       THEN RW_TAC (std_ss ++ resq_SS) [S_SEM_TRUE,B_SEM]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN RES_TAC
       THEN FULL_SIMP_TAC std_ss [NEXT_RISE_LESS,CONJ_ASSOC]
       THEN IMP_RES_TAC NEXT_RISE
       THEN FULL_SIMP_TAC std_ss [B_SEM]
       THENL
        [PROVE_TAC
          [DECIDE ``m:num <= n:num /\ n <= m = (m = n)``,
           Cooper.COOPER_PROVE ``(!k:num. k < j':num ==> ~(j:num <= k)) = j' <= j``],
         Q.EXISTS_TAC `i`
          THEN RW_TAC arith_ss [NEXT_RISE,B_SEM],
         PROVE_TAC
          [DECIDE ``m:num <= n:num /\ n <= m = (m = n)``,
           Cooper.COOPER_PROVE ``(!k:num. k < j':num ==> ~(j:num <= k)) = j' <= j``],
         Q.EXISTS_TAC `i`
          THEN RW_TAC arith_ss [NEXT_RISE,B_SEM]],
      (* 7. F_STRONG_IMP(s1,s2) *)
      INIT_TAC
       THEN RW_TAC std_ss [S_SEM_TRUE,NEXT_TRUE_GE,DECIDE``m:num <= n:num = n >= m``]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN PROVE_TAC[],
      (* 8. F_WEAK_IMP(s1,s2) *)
      INIT_TAC
       THEN RW_TAC std_ss [S_SEM_TRUE,NEXT_TRUE_GE,DECIDE``m:num <= n:num = n >= m``]
       THEN EQ_TAC
       THEN RW_TAC std_ss [],
      (* 9. F_ABORT(f,b)) *)
      INIT_TAC THEN RW_TAC std_ss [B_SEM,DECIDE``(A\/B=A\/C) = A \/ (B=C)``]
       THEN Cases_on`UF_SEM p f \/ LENGTH p > 0 /\ B_SEM (ELEM p 0) p_2`
       THEN RW_TAC std_ss []
       THEN RW_TAC std_ss [DISJ_ASSOC]
       THEN FULL_SIMP_TAC std_ss [DE_MORGAN_THM]
       THEN EQ_TAC
       THEN RW_TAC arith_ss [ELEM_RESTN]
       THENL
        [Cases_on `p`
          THEN FULL_SIMP_TAC arith_ss [xnum_to_def,LENGTH_def,GT_xnum_num_def],
         Cases_on `p`
          THEN FULL_SIMP_TAC arith_ss [xnum_to_def,LENGTH_def,GT_xnum_num_def],
         Q.EXISTS_TAC `i`
          THEN RW_TAC std_ss []
          THEN rename1 `UF_SEM (CAT (SEL p (0,i − 1),w'')) f`
          THEN Q.EXISTS_TAC `w''` (* was: w' *)
          THEN RW_TAC std_ss []
          THEN Cases_on `p`
          THEN FULL_SIMP_TAC arith_ss
                [xnum_to_def,LENGTH_def,GT_xnum_num_def,RESTN_FINITE,LENGTH_def,
                 FinitePSLPathTheory.LENGTH_RESTN,LENGTH_RESTN_INFINITE],
         Q.EXISTS_TAC `j`
          THEN RW_TAC std_ss []
          THEN PROVE_TAC []],
      (* 10. F_STRONG_CLOCK(f,c) *)
      INIT_TAC]);
end;

val F_SEM_TRUE =
 store_thm
  ("F_SEM_TRUE",
   ``!f. F_CLOCK_FREE f ==> !w. F_SEM w B_TRUE f = UF_SEM w f``,
   PROVE_TAC[F_SEM_TRUE_LEMMA]);

(******************************************************************************
* Formula disjunction: f1 \/ f2
******************************************************************************)
val UF_SEM_F_OR =
 store_thm
  ("UF_SEM_F_OR",
   ``UF_SEM p (F_OR(f1,f2)) = UF_SEM p f1 \/ UF_SEM p f2``,
   RW_TAC (std_ss ++ resq_SS) [UF_SEM_def,F_OR_def]);

(******************************************************************************
* Formula implication: f1 --> f2
******************************************************************************)
val UF_SEM_F_IMPLIES =
 store_thm
  ("UF_SEM_F_IMPLIES",
   ``UF_SEM p (F_IMPLIES (f1,f2)) = UF_SEM p f1 ==> UF_SEM p f2``,
   RW_TAC (std_ss ++ resq_SS) [UF_SEM_def,F_IMPLIES_def,UF_SEM_F_OR]
    THEN PROVE_TAC[]);

(******************************************************************************
* Eventually: F f
******************************************************************************)
val UF_SEM_F_F =
 store_thm
  ("UF_SEM_F_F",
   ``UF_SEM p (F_F f) = ?i :: (0 to LENGTH p). UF_SEM (RESTN p i) f``,
   RW_TAC (arith_ss ++ resq_SS) [UF_SEM_def,F_F_def,B_SEM]
    THEN Cases_on `p`
    THEN RW_TAC arith_ss
          [xnum_to_def,LENGTH_def,GT_xnum_num_def,RESTN_FINITE,LENGTH_def,
           FinitePSLPathTheory.LENGTH_RESTN,LENGTH_RESTN_INFINITE]
    THEN EQ_TAC
    THEN ZAP_TAC arith_ss []
    THEN Q.EXISTS_TAC `i`
    THEN RW_TAC arith_ss [FinitePSLPathTheory.LENGTH_RESTN]);

(******************************************************************************
* Always: G f
******************************************************************************)
val UF_SEM_F_G =
 store_thm
  ("UF_SEM_F_G",
   ``UF_SEM p (F_G f) = !i :: (0 to LENGTH p). UF_SEM (RESTN p i) f``,
   RW_TAC (std_ss ++ resq_SS) [UF_SEM_def,F_G_def,UF_SEM_F_F]
    THEN PROVE_TAC[]);

(******************************************************************************
* Weak until: [f1 W f2]
******************************************************************************)
val UF_SEM_F_W =
 store_thm
  ("UF_SEM_F_W",
   ``UF_SEM p (F_W(f1,f2)) = UF_SEM p (F_UNTIL(f1,f2)) \/ UF_SEM p (F_G f1)``,
   RW_TAC (std_ss ++ resq_SS) [UF_SEM_def,F_W_def,UF_SEM_F_OR]);

(******************************************************************************
* Strongly on first posedge.
* Exists a posedge and true on it: [!c U (c /\ f)]
******************************************************************************)
val UF_SEM_F_U_CLOCK =
 store_thm
  ("UF_SEM_F_U_CLOCK",
   ``UF_SEM p (F_U_CLOCK c f) =
      ?i :: (0 to LENGTH p). NEXT_RISE p c (0,i) /\ UF_SEM (RESTN p i) f``,
   RW_TAC (arith_ss ++ resq_SS)
    [F_U_CLOCK_def,ELEM_RESTN,UF_SEM_def,B_SEM,NEXT_RISE]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Q.EXISTS_TAC `k`
       THEN RW_TAC std_ss [],
      Q.EXISTS_TAC `i`
       THEN RW_TAC std_ss []
       THEN Cases_on `p`
       THEN FULL_SIMP_TAC arith_ss
             [xnum_to_def,LENGTH_def,GT_xnum_num_def,RESTN_FINITE,LENGTH_def,
              FinitePSLPathTheory.LENGTH_RESTN,LENGTH_RESTN_INFINITE]]);

(******************************************************************************
* Weakly on first posedge.
* On first posedge, if there is a posedge: [!c U (c /\ f)]
******************************************************************************)
val UF_SEM_F_W_CLOCK =
 store_thm
  ("UF_SEM_F_W_CLOCK",
   ``UF_SEM p (F_W_CLOCK c f) =
      UF_SEM p (F_U_CLOCK c f)
      \/
      !i :: (0 to LENGTH p).~UF_SEM (RESTN p i) (F_BOOL c)``,
   RW_TAC (std_ss ++ resq_SS)
    [F_U_CLOCK_def,F_W_CLOCK_def,UF_SEM_F_W,UF_SEM_F_G,B_SEM,UF_SEM_def]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THEN Cases_on `p`
    THEN FULL_SIMP_TAC arith_ss
          [xnum_to_def,LENGTH_def,GT_xnum_num_def,RESTN_FINITE,LENGTH_def,
           FinitePSLPathTheory.LENGTH_RESTN,LENGTH_RESTN_INFINITE]
    THENL
     [Cases_on `!i. i < LENGTH l ==> ~B_SEM (ELEM (FINITE (RESTN l i)) 0) c`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
       THEN Q.EXISTS_TAC `k`
       THEN RW_TAC std_ss [],
      Cases_on `!i. ~B_SEM (ELEM (RESTN (INFINITE f') i) 0) c`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
       THEN Q.EXISTS_TAC `k`
       THEN RW_TAC std_ss [],
      Cases_on `!i. i < LENGTH l ==> ~B_SEM (ELEM (FINITE (RESTN l i)) 0) c`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
       THEN Q.EXISTS_TAC `k`
       THEN RW_TAC std_ss [],
      Cases_on `!i. ~B_SEM (ELEM (RESTN (INFINITE f') i) 0) c`
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC std_ss [NOT_FORALL_THM]
       THEN Q.EXISTS_TAC `k`
       THEN RW_TAC std_ss []]);

(******************************************************************************
* S_CLOCK_COMP c r contains no clocked SEREs
******************************************************************************)
val S_CLOCK_COMP_CLOCK_FREE =
 store_thm
  ("S_CLOCK_COMP_CLOCK_FREE",
   ``!r c. S_CLOCK_FREE(S_CLOCK_COMP c r)``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THEN RW_TAC std_ss [S_CLOCK_FREE_def,S_CLOCK_COMP_def]);

(******************************************************************************
* F_CLOCK_COMP c f contains no clocked formulas
******************************************************************************)
val F_CLOCK_COMP_CLOCK_FREE_LEMMA =
 store_thm
  ("F_CLOCK_COMP_CLOCK_FREE_LEMMA",
   ``!f c. F_CLOCK_FREE(F_CLOCK_COMP c f)``,
   INDUCT_THEN fl_induct ASSUME_TAC
    THEN RW_TAC std_ss
          [F_CLOCK_FREE_def,F_CLOCK_COMP_def,F_U_CLOCK_def,F_IMPLIES_def,
           F_OR_def,S_CLOCK_COMP_CLOCK_FREE])

val F_CLOCK_COMP_CLOCK_FREE =
 store_thm
  ("F_CLOCK_COMP_CLOCK_FREE",
   ``!c f. F_CLOCK_FREE(F_CLOCK_COMP c f)``,
   RW_TAC std_ss [F_CLOCK_COMP_CLOCK_FREE_LEMMA]);

(******************************************************************************
* w |=c r  <==>  w |= (S_CLOCK_COMP c r)
******************************************************************************)
local open FinitePSLPathTheory

val INIT_TAC0 =
 RW_TAC (std_ss ++ resq_SS) [S_SEM_def, US_SEM_def, S_CLOCK_COMP_def];

val INIT_TAC1 =
 INIT_TAC0
  THEN RW_TAC list_ss [EVERY_EL]
  THEN EQ_TAC
  THEN RW_TAC list_ss [LENGTH_APPEND,ELEM_EL,LENGTH1];

val INIT_TAC2 =
 `!n:num. n < LENGTH wlist ==> (?x. EL n wlist = [x])` by PROVE_TAC[]
  THEN IMP_RES_TAC(INST_TYPE[``:'a``|->``:'a->bool``]EVERY_EL_SINGLETON_LENGTH)
  THEN IMP_RES_TAC(INST_TYPE[``:'a``|->``:'a->bool``]EVERY_EL_SINGLETON)
  THEN FULL_SIMP_TAC list_ss [LENGTH_APPEND]
  THEN RW_TAC list_ss [EL_MAP,EL_APPEND1,EL_APPEND2];

in

val S_CLOCK_COMP_ELIM =
 store_thm
  ("S_CLOCK_COMP_ELIM",
   ``!r w c. S_SEM w c r = US_SEM w (S_CLOCK_COMP c r)``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THENL
     [(* S_BOOL b *)
      INIT_TAC1 THEN TRY INIT_TAC2
       THEN Q.EXISTS_TAC `BUTLAST w`
       THEN Q.EXISTS_TAC `[LAST w]`
       THEN RW_TAC list_ss []
       THEN RW_TAC list_ss [APPEND_BUTLAST_LAST,LENGTH_NIL_LEMMA]
       THENL
        [Q.EXISTS_TAC `MAP(\l.[l])(BUTLAST w)`
          THEN RW_TAC list_ss [CONCAT_MAP_SINGLETON,EL_MAP]
          THEN IMP_RES_TAC LENGTH_NIL_LEMMA
          THEN IMP_RES_TAC LENGTH_BUTLAST
          THEN `n:num < LENGTH w - 1` by DECIDE_TAC
          THEN PROVE_TAC[EL_BUTLAST],
         IMP_RES_TAC EL_PRE_LENGTH
          THEN POP_ASSUM(fn th => RW_TAC list_ss [GSYM th])],
      (* S_CAT(r,r') *)
      INIT_TAC0,
      (* S_FUSION (r,r') *)
      INIT_TAC0,
      (* S_OR (r,r') *)
      INIT_TAC0,
      (* S_AND (r,r') *)
      INIT_TAC0,
      (* S_REPEAT r *)
      INIT_TAC0,
      (* S_CLOCK (r,p_2) *)
      INIT_TAC0
       THEN EQ_TAC
       THEN RW_TAC list_ss
             [LENGTH_APPEND,LENGTH_NIL,ELEM_EL,EVERY_EL,LENGTH1,
              APPEND_SINGLETON_EQ]
       THEN FULL_SIMP_TAC list_ss []
       THENL
        [Q.EXISTS_TAC `CONCAT wlist`
          THEN Q.EXISTS_TAC `x :: RESTN w (i+1)`
          THEN RW_TAC list_ss []
          THENL
           [ONCE_REWRITE_TAC [APPEND_CONS]
             THEN ASSUM_LIST(fn thl => REWRITE_TAC[SYM(el 4 thl)])
             THEN Cases_on `i:num = LENGTH w - 1`
             THENL
              [RW_TAC arith_ss []
                THEN `0 < LENGTH w` by DECIDE_TAC
                THEN ASSUM_LIST(fn thl => SIMP_TAC std_ss (mapfilter SYM thl))
                THEN IMP_RES_TAC SEL_RESTN_EQ0
                THEN POP_ASSUM(fn th => REWRITE_TAC[th,RESTN_LENGTH,APPEND_NIL]),
               `i:num < LENGTH w - 1` by DECIDE_TAC
                THEN IMP_RES_TAC(DECIDE``i:num < m:num-1 ==> i+1 < m``)
                THEN IMP_RES_TAC SEL_RESTN_EQ
                THEN ASSUM_LIST(fn thl => SIMP_TAC std_ss (mapfilter SYM thl))
                THEN POP_ASSUM(ASSUME_TAC o SYM)
                THEN IMP_RES_TAC
                      (SIMP_RULE
                        arith_ss
                        []
                        (GSYM(Q.SPECL[`w`,`i`,`0`,`list$LENGTH w - 1`]FinitePSLPathTheory.SEL_SPLIT)))
                THEN POP_ASSUM(fn th => REWRITE_TAC[th])
                THEN PROVE_TAC[DECIDE``i:num < n:num-1 ==> 0 < n``,SEL_RESTN_EQ0]],
            PROVE_TAC[],
            `!n. n < LENGTH wlist ==> (?x. EL n wlist = [x])` by PROVE_TAC[]
             THEN IMP_RES_TAC(INST_TYPE[``:'a``|->``:'a->bool``]EVERY_EL_SINGLETON_LENGTH)
             THEN PROVE_TAC[RESTN_EL,LAST_SINGLETON,EL_LAST_SEL]],
         Q.EXISTS_TAC `LENGTH(CONCAT wlist)`
          THEN RW_TAC list_ss [RESTN_APPEND]
          THEN Q.EXISTS_TAC `CONCAT wlist`
          THEN Q.EXISTS_TAC `[l]`
          THEN RW_TAC list_ss []
          THENL
           [ONCE_REWRITE_TAC [APPEND_CONS]
             THEN Cases_on `CONCAT wlist = []`
             THEN RW_TAC list_ss [SEL_ELEM,ELEM_EL]
             THEN POP_ASSUM(ASSUME_TAC o SIMP_RULE std_ss [GSYM LENGTH_NIL])
             THEN `0 < LENGTH(CONCAT wlist)` by DECIDE_TAC
             THEN `1 <= LENGTH([l] <> w2')` by RW_TAC list_ss []
             THEN RW_TAC std_ss [SEL_APPEND_COR,GSYM APPEND_ASSOC,SEL_RESTN_EQ0]
             THEN RW_TAC list_ss [],
            PROVE_TAC[]]]]);

end;

(******************************************************************************
* Make theorems that apply to both finite and infinite paths
* (maybe not needed)
******************************************************************************)
val HEAD_def =
 LIST_CONJ[FinitePSLPathTheory.HEAD_def,PSLPathTheory.HEAD_def];

val REST_def =
 LIST_CONJ[FinitePSLPathTheory.REST_def,PSLPathTheory.REST_def];

val RESTN_def =
 LIST_CONJ[FinitePSLPathTheory.RESTN_def,PSLPathTheory.RESTN_def];

val ELEM_def =
 LIST_CONJ[FinitePSLPathTheory.ELEM_def,PSLPathTheory.ELEM_def];

val LENGTH_REST =
 LIST_CONJ[FinitePSLPathTheory.LENGTH_REST,PSLPathTheory.LENGTH_REST];

val LENGTH_RESTN =
 LIST_CONJ[FinitePSLPathTheory.LENGTH_RESTN,PSLPathTheory.LENGTH_RESTN];

(******************************************************************************
* F_INIT_CLOCK_COMP_CORRECT f  =  (p |=T f  <==>  p |= (F_INIT_CLOCK_COMP T f))
******************************************************************************)
val F_INIT_CLOCK_COMP_CORRECT_def =
 Define
  `F_INIT_CLOCK_COMP_CORRECT f =
    !w c. (F_SEM w c f = UF_SEM w (F_INIT_CLOCK_COMP c f))`;

val F_BOOL_INIT_CLOCK_COMP_ELIM =
 store_thm
  ("F_BOOL_INIT_CLOCK_COMP_ELIM",
   ``!b. F_INIT_CLOCK_COMP_CORRECT (F_BOOL b)``,
   RW_TAC (std_ss ++ resq_SS)
    [F_INIT_CLOCK_COMP_CORRECT_def,F_SEM,UF_SEM_def,F_INIT_CLOCK_COMP_def]);

val F_NOT_INIT_CLOCK_COMP_ELIM =
 store_thm
  ("F_NOT_INIT_CLOCK_COMP_ELIM",
   ``!f. F_INIT_CLOCK_COMP_CORRECT f ==> F_INIT_CLOCK_COMP_CORRECT (F_NOT f)``,
   RW_TAC (std_ss ++ resq_SS)
    [F_INIT_CLOCK_COMP_CORRECT_def,F_SEM,UF_SEM_def,F_INIT_CLOCK_COMP_def]);

val F_AND_INIT_CLOCK_COMP_ELIM =
 store_thm
  ("F_AND_INIT_CLOCK_COMP_ELIM",
   ``!f1 f2. F_INIT_CLOCK_COMP_CORRECT f1 /\ F_INIT_CLOCK_COMP_CORRECT f2
             ==> F_INIT_CLOCK_COMP_CORRECT (F_AND(f1,f2))``,
   RW_TAC (std_ss ++ resq_SS)
    [F_INIT_CLOCK_COMP_CORRECT_def,F_SEM,UF_SEM_def,F_INIT_CLOCK_COMP_def]);

val F_NEXT_INIT_CLOCK_COMP_ELIM =
 store_thm
  ("F_NEXT_INIT_CLOCK_COMP_ELIM",
   ``!f. F_INIT_CLOCK_COMP_CORRECT f ==> F_INIT_CLOCK_COMP_CORRECT (F_NEXT f)``,
   RW_TAC (std_ss ++ resq_SS)
    [F_INIT_CLOCK_COMP_CORRECT_def,F_SEM,UF_SEM_def,F_INIT_CLOCK_COMP_def]
    THEN Cases_on `w`
    THEN ONCE_REWRITE_TAC[ONE]
    THENL
     [RW_TAC (arith_ss ++ resq_SS)
       [UF_SEM_F_U_CLOCK,GSYM NEXT_RISE_def,NEXT_RISE,LENGTH_def,
        RESTN_def,xnum_to_def,GT_xnum_num_def,RESTN_FINITE]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [DECIDE_TAC,
         Q.EXISTS_TAC `i-1`
          THEN IMP_RES_TAC NEXT_RISE
          THEN RW_TAC arith_ss
                [REST_def,LENGTH_def,xnum_to_def,RESTN_def,RESTN_FINITE,LENGTH_TL,
                 RESTN_TL,ELEM_FINITE_TL]
          THEN `0 < i /\ k+1 < i /\ 1 <= k+1 /\ 0 < LENGTH l` by DECIDE_TAC
          THEN RES_TAC
          THEN RW_TAC arith_ss [ELEM_FINITE_TL_COR],
         Q.EXISTS_TAC `i+1`
          THEN ZAP_TAC arith_ss [RESTN_def,ADD1]
          THENL
           [`0 < LENGTH l` by DECIDE_TAC
              THEN IMP_RES_TAC LENGTH_REST
              THEN DECIDE_TAC,
             RW_TAC arith_ss [NEXT_RISE]
              THENL
               [`k-1 < i /\ 0 < k /\ 0 < LENGTH l` by DECIDE_TAC
                 THEN PROVE_TAC[ELEM_FINITE_TL,REST_def],
                `0 < LENGTH l` by DECIDE_TAC
                 THEN PROVE_TAC[ELEM_FINITE_TL_COR,REST_def]]]],
      RW_TAC (arith_ss  ++ resq_SS)
       [LENGTH_def,xnum_to_def,GT_xnum_num_def,
        UF_SEM_F_U_CLOCK,GSYM NEXT_RISE_def,NEXT_RISE,
        RESTN_def,xnum_to_def,NEXT_RISE_LESS,REST_def,CONJ_ASSOC]
       THEN RW_TAC std_ss [GSYM REST_def]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THENL
        [Q.EXISTS_TAC `i-1`
          THEN RW_TAC arith_ss [ELEM_REST_INFINITE,RESTN_REST_INFINITE]
          THEN `1 <= k+1 /\ k+1 < i` by DECIDE_TAC
          THEN RES_TAC
          THEN RW_TAC arith_ss [ELEM_REST_INFINITE_COR],
         Q.EXISTS_TAC `i+1`
          THEN RW_TAC arith_ss [RESTN_def,ADD1]
          THENL
           [`0 < k /\ k-1 < i` by DECIDE_TAC
             THEN PROVE_TAC[ELEM_REST_INFINITE],
            PROVE_TAC[ELEM_REST_INFINITE_COR],
            PROVE_TAC[RESTN_REST_INFINITE_COR]]]]);

val F_UNTIL_INIT_CLOCK_COMP_ELIM =
 store_thm
  ("F_UNTIL_INIT_CLOCK_COMP_ELIM",
   ``!f1 f2.
       F_INIT_CLOCK_COMP_CORRECT f1 /\ F_INIT_CLOCK_COMP_CORRECT f2 ==>
        F_INIT_CLOCK_COMP_CORRECT (F_UNTIL(f1, f2))``,
   RW_TAC (std_ss ++ resq_SS)
    [F_INIT_CLOCK_COMP_CORRECT_def,F_SEM,UF_SEM_def,F_INIT_CLOCK_COMP_def]
    THEN Cases_on `w`
    THEN RW_TAC (arith_ss  ++ resq_SS)
          [LENGTH_def,num_to_def,xnum_to_def,UF_SEM_def,UF_SEM_F_IMPLIES,ELEM_RESTN]
    THEN PROVE_TAC[]);

val F_SUFFIX_IMP_INIT_CLOCK_COMP_ELIM =
 store_thm
  ("F_SUFFIX_IMP_INIT_CLOCK_COMP_ELIM",
   ``!r f. F_INIT_CLOCK_COMP_CORRECT f ==> F_INIT_CLOCK_COMP_CORRECT (F_SUFFIX_IMP(r,f))``,
   RW_TAC (std_ss ++ resq_SS)
    [F_INIT_CLOCK_COMP_CORRECT_def,F_INIT_CLOCK_COMP_def,S_CLOCK_COMP_ELIM,
     F_SEM_def,NEXT_RISE,GSYM NEXT_RISE_def,UF_SEM_def,UF_SEM_F_U_CLOCK]
    THEN Cases_on `w`
    THEN RW_TAC (arith_ss  ++ resq_SS)
          [LENGTH_def,num_to_def,xnum_to_def,UF_SEM_def,UF_SEM_F_IMPLIES,LENGTH_RESTN,
           LENGTH_RESTN_INFINITE,RESTN_FINITE,ELEM_RESTN,B_SEM,RESTN_RESTN]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THEN RES_TAC
    THEN IMP_RES_TAC NEXT_RISE
    THENL
     [Q.EXISTS_TAC `j'-j`
       THEN RW_TAC arith_ss []
       THEN `0 <= j' - j` by DECIDE_TAC
       THEN RW_TAC arith_ss [NEXT_RISE,ELEM_RESTN,GSYM RESTN_FINITE],
      Q.EXISTS_TAC `i'+i`
       THEN RW_TAC arith_ss [NEXT_RISE]
       THEN `0 <= i'` by DECIDE_TAC
       THEN POP_ASSUM
             (fn th => FULL_SIMP_TAC std_ss
                        [ELEM_RESTN,GSYM RESTN_FINITE,MATCH_MP NEXT_RISE th])
       THEN `0 <= k-i /\ k-i < i' /\ (i+(k-i) = k)` by DECIDE_TAC
       THEN PROVE_TAC[] (* PROVE_TAC[ADD_SYM] *),
      Q.EXISTS_TAC `j'-j`
       THEN RW_TAC arith_ss []
       THEN `0 <= j' - j` by DECIDE_TAC
       THEN RW_TAC arith_ss [NEXT_RISE,ELEM_RESTN],
      Q.EXISTS_TAC `i'+i`
       THEN RW_TAC arith_ss [NEXT_RISE]
       THEN `0 <= i'` by DECIDE_TAC
       THEN POP_ASSUM
             (fn th => FULL_SIMP_TAC std_ss
                        [ELEM_RESTN,GSYM RESTN_FINITE,MATCH_MP NEXT_RISE th])
       THEN `0 <= k-i /\ k-i < i' /\ (i+(k-i) = k)` by DECIDE_TAC
       THEN PROVE_TAC[]]);

val F_STRONG_IMP_INIT_CLOCK_COMP_ELIM =
 store_thm
  ("F_STRONG_IMP_INIT_CLOCK_COMP_ELIM",
   ``!r1 r2. F_INIT_CLOCK_COMP_CORRECT(F_STRONG_IMP(r1,r2))``,
   RW_TAC (std_ss ++ resq_SS)
    [F_INIT_CLOCK_COMP_CORRECT_def,F_SEM,UF_SEM_def,F_INIT_CLOCK_COMP_def,S_CLOCK_COMP_ELIM]
    THEN Cases_on `w`
    THEN RW_TAC (arith_ss  ++ resq_SS)
          [LENGTH_def,num_to_def,xnum_to_def,UF_SEM_def,UF_SEM_F_IMPLIES,ELEM_RESTN]);

val F_WEAK_IMP_INIT_CLOCK_COMP_ELIM =
 store_thm
  ("F_WEAK_IMP_INIT_CLOCK_COMP_ELIM",
   ``!r1 r2. F_INIT_CLOCK_COMP_CORRECT(F_WEAK_IMP(r1,r2))``,
   RW_TAC (std_ss ++ resq_SS)
    [F_INIT_CLOCK_COMP_CORRECT_def,F_SEM,UF_SEM_def,F_INIT_CLOCK_COMP_def,S_CLOCK_COMP_ELIM]
    THEN Cases_on `w`
    THEN RW_TAC (arith_ss  ++ resq_SS)
          [LENGTH_def,num_to_def,xnum_to_def,UF_SEM_def,UF_SEM_F_IMPLIES,ELEM_RESTN]);

val F_ABORT_INIT_CLOCK_COMP_ELIM =
 store_thm
  ("F_ABORT_INIT_CLOCK_COMP_ELIM",
   ``!b f. F_INIT_CLOCK_COMP_CORRECT f ==> F_INIT_CLOCK_COMP_CORRECT (F_ABORT(f,b))``,
   RW_TAC (std_ss ++ resq_SS)
    [F_INIT_CLOCK_COMP_CORRECT_def,F_SEM,UF_SEM_def,F_INIT_CLOCK_COMP_def]
    THEN Cases_on `w`
    THEN RW_TAC (arith_ss  ++ resq_SS)
          [LENGTH_def,num_to_def,xnum_to_def,UF_SEM_def,
           UF_SEM_F_OR,UF_SEM_F_IMPLIES,ELEM_RESTN,B_SEM_def]
    THEN PROVE_TAC[]);

val F_STRONG_CLOCK_INIT_CLOCK_COMP_ELIM =
 store_thm
  ("F_STRONG_CLOCK_INIT_CLOCK_COMP_ELIM",
   ``!f. F_INIT_CLOCK_COMP_CORRECT f ==>
          !c1. F_INIT_CLOCK_COMP_CORRECT (F_STRONG_CLOCK(f,c1))``,
   RW_TAC (std_ss ++ resq_SS)
    [F_INIT_CLOCK_COMP_CORRECT_def,F_SEM,UF_SEM_def,F_INIT_CLOCK_COMP_def]
    THEN Cases_on `w`
    THEN RW_TAC (arith_ss  ++ resq_SS)
          [LENGTH_def,num_to_def,xnum_to_def,UF_SEM_def,UF_SEM_F_IMPLIES,ELEM_RESTN,
           UF_SEM_F_U_CLOCK,GSYM NEXT_RISE_def,NEXT_RISE]);

val F_INIT_CLOCK_COMP_ELIM =
 store_thm
  ("F_INIT_CLOCK_COMP_ELIM",
   ``!f. F_INIT_CLOCK_COMP_CORRECT f``,
   INDUCT_THEN fl_induct ASSUME_TAC
    THEN RW_TAC std_ss
          [F_BOOL_INIT_CLOCK_COMP_ELIM,
           F_NOT_INIT_CLOCK_COMP_ELIM,
           F_AND_INIT_CLOCK_COMP_ELIM,
           F_SUFFIX_IMP_INIT_CLOCK_COMP_ELIM,
           F_ABORT_INIT_CLOCK_COMP_ELIM,
           F_WEAK_IMP_INIT_CLOCK_COMP_ELIM,
           F_STRONG_IMP_INIT_CLOCK_COMP_ELIM,
           F_STRONG_CLOCK_INIT_CLOCK_COMP_ELIM,
           F_NEXT_INIT_CLOCK_COMP_ELIM,
           F_UNTIL_INIT_CLOCK_COMP_ELIM]);

(******************************************************************************
* Proof that if the clock is initially true, then the two rewrites for
* abort (defined in F_CLOCK_COMP and F_INIT_CLOCK_COMP) are equivalent.
******************************************************************************)
local
val INIT_TAC =
 RW_TAC std_ss [F_CLOCK_COMP_def,F_INIT_CLOCK_COMP_def,UF_SEM_def,B_SEM];
in
val INIT_CLOCK_COMP_EQUIV =
 store_thm
  ("INIT_CLOCK_COMP_EQUIV",
   ``!f w c.
      B_SEM (ELEM w 0) c
      ==>
      (UF_SEM w (F_CLOCK_COMP c f) = UF_SEM w (F_INIT_CLOCK_COMP c f))``,
   INDUCT_THEN fl_induct ASSUME_TAC
    THENL
     [(* F_BOOL b *)
      INIT_TAC,
      (* F_NOT b *)
      INIT_TAC,
      (* F_AND (f1,f2) *)
      INIT_TAC,
      (* F_NEXT f *)
      INIT_TAC
       THEN RW_TAC (arith_ss++resq_SS) [UF_SEM_F_U_CLOCK,RESTN_RESTN]
       THEN Cases_on `w`
       THEN RW_TAC arith_ss
             [LENGTH_def,GT_xnum_num_def,LENGTH_RESTN_INFINITE,
              num_to_def,xnum_to_def,NEXT_RISE,ELEM_RESTN]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN Q.EXISTS_TAC `i`
       THEN PROVE_TAC[SIMP_RULE arith_ss [] (Q.SPECL[`j`,`0`]ELEM_RESTN)],
      (* F_UNTIL(f1,f2) f *)
      INIT_TAC
       THEN RW_TAC (arith_ss++resq_SS) [ELEM_RESTN,UF_SEM_F_IMPLIES,UF_SEM_def]
       THEN Cases_on `w`
       THEN RW_TAC arith_ss
             [LENGTH_def,GT_xnum_num_def,LENGTH_RESTN_INFINITE,
              num_to_def,xnum_to_def,NEXT_RISE,ELEM_RESTN]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN Q.EXISTS_TAC `k`
       THEN PROVE_TAC[SIMP_RULE arith_ss [] (Q.SPECL[`j`,`0`]ELEM_RESTN)],
      (* F_SUFFIX_IMP(s,f) *)
      INIT_TAC
       THEN RW_TAC (arith_ss++resq_SS) [ELEM_RESTN,UF_SEM_F_IMPLIES,UF_SEM_def]
       THEN Cases_on `w`
       THEN RW_TAC (arith_ss ++resq_SS)
             [LENGTH_def,GT_xnum_num_def,LENGTH_RESTN_INFINITE,UF_SEM_F_U_CLOCK,LENGTH_RESTN,
              RESTN_FINITE,num_to_def,xnum_to_def,NEXT_RISE,ELEM_RESTN,RESTN_RESTN]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN RES_TAC
       THEN Q.EXISTS_TAC `i`
       THEN RW_TAC arith_ss []
       THEN FULL_SIMP_TAC std_ss [GSYM(SIMP_RULE arith_ss [] (Q.SPECL[`i+j`,`0`]ELEM_RESTN))]
       THEN PROVE_TAC[RESTN_FINITE],
      (* F_STRONG_IMP(s1,s2) *)
      INIT_TAC,
      (* F_WEAK_IMP(s1,s2) *)
      INIT_TAC,
      (* F_ABORT(f,b)) *)
      INIT_TAC
       THEN RW_TAC (arith_ss++resq_SS) [ELEM_RESTN,UF_SEM_F_OR,UF_SEM_def]
       THEN Cases_on `w`
       THEN RW_TAC arith_ss
             [LENGTH_def,GT_xnum_num_def,LENGTH_RESTN_INFINITE,B_SEM,
              num_to_def,xnum_to_def,NEXT_RISE,ELEM_RESTN]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN RW_TAC std_ss []
       THENL
        [ASSUM_LIST
          (fn thl =>
            ASSUME_TAC
             (GEN_ALL
              (SIMP_RULE std_ss [ELEM_CAT_SEL]
               (Q.SPECL[`(CAT (SEL w (0,j - 1),w'))`,`c`] (el 8 thl)))))
          THEN PROVE_TAC[],
         ASSUM_LIST
          (fn thl =>
            ASSUME_TAC
             (GEN_ALL
              (SIMP_RULE std_ss [ELEM_CAT_SEL]
               (Q.SPECL[`(CAT (SEL w (0,j - 1),w'))`,`c`] (el 8 thl)))))
          THEN PROVE_TAC[],
         ASSUM_LIST
          (fn thl =>
            ASSUME_TAC
             (GEN_ALL
              (SIMP_RULE std_ss [ELEM_CAT_SEL]
               (Q.SPECL[`(CAT (SEL w (0,j - 1),w'))`,`c`] (el 6 thl)))))
          THEN PROVE_TAC[],
         ASSUM_LIST
          (fn thl =>
            ASSUME_TAC
             (GEN_ALL
              (SIMP_RULE std_ss [ELEM_CAT_SEL]
               (Q.SPECL[`(CAT (SEL w (0,j - 1),w'))`,`c`] (el 6 thl)))))
          THEN PROVE_TAC[]],
      (* F_STRONG_CLOCK(f,c) *)
      INIT_TAC
       THEN RW_TAC (arith_ss++resq_SS) [UF_SEM_F_U_CLOCK,RESTN_RESTN]
       THEN Cases_on `w`
       THEN RW_TAC arith_ss
             [LENGTH_def,GT_xnum_num_def,LENGTH_RESTN_INFINITE,
              num_to_def,xnum_to_def,NEXT_RISE,ELEM_RESTN]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN Q.EXISTS_TAC `i`
       THEN RW_TAC std_ss []
       THEN PROVE_TAC[SIMP_RULE arith_ss [] (Q.SPECL[`j`,`0`]ELEM_RESTN)]]);
end;

val F_CLOCK_COMP_CORRECT =
 store_thm
  ("F_CLOCK_COMP_CORRECT",
   `` !f w c.
         B_SEM (ELEM w 0) c ==>
         (F_SEM w c f = UF_SEM w (F_CLOCK_COMP c f))``,
   PROVE_TAC[F_INIT_CLOCK_COMP_ELIM,F_INIT_CLOCK_COMP_CORRECT_def,INIT_CLOCK_COMP_EQUIV]);

(******************************************************************************
* w |=T f <==> w |= T^{T}(f)
******************************************************************************)
val F_TRUE_COMP_CORRECT_LEMMA =
 save_thm
  ("F_TRUE_COMP_CORRECT_LEMMA",
    SIMP_CONV std_ss [B_SEM] ``B_SEM (ELEM w 0) B_TRUE``);

val F_TRUE_CLOCK_COMP_ELIM =
 store_thm
  ("F_TRUE_CLOCK_COMP_ELIM",
   ``F_SEM w B_TRUE f = UF_SEM w (F_CLOCK_COMP B_TRUE f)``,
   PROVE_TAC
    [F_CLOCK_COMP_CORRECT,F_TRUE_COMP_CORRECT_LEMMA]);

local
val INIT_TAC =
 RW_TAC (arith_ss  ++ resq_SS)
  [F_SEM_def,UF_SEM_def,OLD_F_SEM_def,OLD_UF_SEM_def,
   F_CLOCK_FREE_def,RESTN_def,GSYM NEXT_RISE_def,xnum_to_def,num_to_def];

fun FIN_TAC v =
 `LENGTH(RESTN l ^v) = LENGTH l - ^v` by PROVE_TAC[LENGTH_RESTN]
  THEN `0 < LENGTH(RESTN l ^v)` by DECIDE_TAC
  THEN `0 < LENGTH(FINITE(RESTN l ^v))` by PROVE_TAC[LENGTH_def,PSLPathTheory.LS,xnum_11]
  THEN PROVE_TAC[];

fun INF_TAC f v =
 `0 < LENGTH(RESTN(INFINITE ^f) ^v)`
  by PROVE_TAC[LENGTH_RESTN_INFINITE,LENGTH_def,PSLPathTheory.LS,xnum_11]
  THEN PROVE_TAC[];
in
val OLD_UF_SEM_UF_SEM =
 store_thm
  ("OLD_UF_SEM_UF_SEM",
   ``!f w. LENGTH w > 0 /\ F_CLOCK_FREE f ==> (OLD_UF_SEM w f = UF_SEM w f)``,
   INDUCT_THEN fl_induct ASSUME_TAC (* 10 subgoals *)
    THENL
     [(* F_BOOL b *)
      INIT_TAC,
      (* F_NOT b *)
      INIT_TAC,
      (* F_AND (f1,f2) *)
      INIT_TAC,
      (* F_NEXT f *)
      INIT_TAC
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC arith_ss [GT_LS]
       THEN IMP_RES_TAC LENGTH_RESTN_THM
       THEN Cases_on `w`
       THEN FULL_SIMP_TAC arith_ss [LENGTH_def,GT,LS,PSLPathTheory.SUB,RESTN_FINITE,xnum_11]
       THENL
        [FIN_TAC ``1``,
         INF_TAC ``f' :num -> 'a -> bool`` ``1``],
      (* F_UNTIL(f1,f2) f *)
      INIT_TAC
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC arith_ss [GT_LS]
       THEN IMP_RES_TAC LENGTH_RESTN_THM
       THEN Cases_on `w`
       THEN FULL_SIMP_TAC arith_ss
             [LENGTH_def,GT,LS,PSLPathTheory.SUB,RESTN_FINITE,xnum_11,xnum_to_def]
       THEN Q.EXISTS_TAC `k`
       THEN RW_TAC std_ss []
       THENL
        [FIN_TAC ``k:num``,
         `j < LENGTH l` by DECIDE_TAC THEN FIN_TAC ``j:num``,
         INF_TAC ``f'' :num -> 'a -> bool`` ``k:num``,
         INF_TAC ``f'' :num -> 'a -> bool`` ``j:num``,
         FIN_TAC ``k:num``,
         `j < LENGTH l` by DECIDE_TAC THEN FIN_TAC ``j:num``,
         INF_TAC ``f'' :num -> 'a -> bool`` ``k:num``,
         INF_TAC ``f'' :num -> 'a -> bool`` ``j:num``],
      (* F_SUFFIX_IMP(s,f) *)
      INIT_TAC
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN Cases_on `w`
       THEN FULL_SIMP_TAC arith_ss
             [LENGTH_def,GT,LS,PSLPathTheory.SUB,RESTN_FINITE,xnum_11,xnum_to_def,GT_LS]
       THEN RES_TAC
       THENL
        [FIN_TAC ``j:num``,
         INF_TAC ``f' :num -> 'a -> bool`` ``j:num``,
         FIN_TAC ``j:num``,
         INF_TAC ``f' :num -> 'a -> bool`` ``j:num``],
      (* F_STRONG_IMP(s1,s2) *)
      INIT_TAC ,
      (* F_WEAK_IMP(s1,s2) *)
      INIT_TAC ,
      (* F_ABORT(f,b)) *)
      INIT_TAC
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC arith_ss [GT_LS]
       THEN IMP_RES_TAC LENGTH_RESTN_THM
       THEN Cases_on `w`
       THEN FULL_SIMP_TAC arith_ss [xnum_to_def,LENGTH_def,GT,LS,PSLPathTheory.SUB,RESTN_FINITE,xnum_11]
       THENL (* 4 subgoals *)
        [REPEAT DISJ2_TAC
          THEN Q.EXISTS_TAC `j`
          THEN RW_TAC std_ss []
          THEN rename1 `OLD_UF_SEM (CAT (SEL (FINITE l) (0,j − 1),w'')) f`
          THEN Q.EXISTS_TAC `w''` (* was: w' *)
          THEN RW_TAC arith_ss [FinitePSLPathTheory.LENGTH_RESTN]
          THEN Cases_on `w''`
          THEN RW_TAC std_ss []
          THENL
           [`LENGTH(CAT (SEL (FINITE l) (0,j - 1),FINITE l')) = XNUM(j + LENGTH l')`
             by RW_TAC arith_ss [LENGTH_CAT,LENGTH_SEL]
             THEN FULL_SIMP_TAC std_ss [CAT_FINITE_APPEND,CAT_FINITE_APPEND,LENGTH_def,xnum_11]
             THEN `0 < LENGTH (SEL (FINITE l) (0,j - 1) <> l')` by DECIDE_TAC
             THEN `0 < LENGTH (FINITE(SEL (FINITE l) (0,j - 1) <> l'))`
                   by PROVE_TAC[LENGTH_def,PSLPathTheory.LS,xnum_11]
             THEN PROVE_TAC[],
            `LENGTH(CAT (SEL (FINITE l) (0,j - 1),INFINITE f')) = INFINITY`
             by RW_TAC arith_ss [LENGTH_CAT]
             THEN `0 < LENGTH (CAT (SEL (FINITE l) (0,j - 1),INFINITE f'))`
                   by PROVE_TAC[LENGTH_RESTN_INFINITE,LENGTH_def,PSLPathTheory.LS,xnum_11]
             THEN PROVE_TAC[]],
         REPEAT DISJ2_TAC
          THEN Q.EXISTS_TAC `j`
          THEN RW_TAC std_ss [LENGTH_RESTN_INFINITE,LS]
          THEN rename1 `OLD_UF_SEM (CAT (SEL (INFINITE f') (0,j − 1),w'')) f`
          THEN Q.EXISTS_TAC `w''`
          THEN RW_TAC arith_ss [FinitePSLPathTheory.LENGTH_RESTN]
          THEN Cases_on `w''`
          THEN RW_TAC std_ss []
          THENL
           [`LENGTH(CAT (SEL (INFINITE f') (0,j - 1),FINITE l)) = XNUM(j + LENGTH l)`
             by RW_TAC arith_ss [LENGTH_CAT,LENGTH_SEL]
             THEN FULL_SIMP_TAC std_ss [CAT_FINITE_APPEND,CAT_FINITE_APPEND,LENGTH_def,xnum_11]
             THEN `0 < LENGTH (SEL (INFINITE f') (0,j - 1) <> l)` by DECIDE_TAC
             THEN `0 < LENGTH (FINITE(SEL (INFINITE f') (0,j - 1) <> l))`
                   by PROVE_TAC[LENGTH_def,PSLPathTheory.LS,xnum_11]
             THEN PROVE_TAC[],
            `LENGTH(CAT (SEL (INFINITE f') (0,j - 1),INFINITE f'')) = INFINITY`
             by RW_TAC arith_ss [LENGTH_CAT]
             THEN `0 < LENGTH (CAT (SEL (INFINITE f') (0,j - 1),INFINITE f''))`
                   by PROVE_TAC[LENGTH_RESTN_INFINITE,LENGTH_def,PSLPathTheory.LS,xnum_11]
             THEN PROVE_TAC[]],
         REPEAT DISJ2_TAC
          THEN Q.EXISTS_TAC `j`
          THEN RW_TAC std_ss []
          THEN rename1 `UF_SEM (CAT (SEL (FINITE l) (0,j − 1),w'')) f`
          THEN Q.EXISTS_TAC `w''`
          THEN RW_TAC arith_ss [FinitePSLPathTheory.LENGTH_RESTN]
          THEN Cases_on `w''`
          THEN RW_TAC std_ss []
          THENL
           [`LENGTH(CAT (SEL (FINITE l) (0,j - 1),FINITE l')) = XNUM(j + LENGTH l')`
             by RW_TAC arith_ss [LENGTH_CAT,LENGTH_SEL]
             THEN FULL_SIMP_TAC std_ss [CAT_FINITE_APPEND,CAT_FINITE_APPEND,LENGTH_def,xnum_11]
             THEN `0 < LENGTH (SEL (FINITE l) (0,j - 1) <> l')` by DECIDE_TAC
             THEN `0 < LENGTH (FINITE(SEL (FINITE l) (0,j - 1) <> l'))`
                   by PROVE_TAC[LENGTH_def,PSLPathTheory.LS,xnum_11]
             THEN PROVE_TAC[],
            `LENGTH(CAT (SEL (FINITE l) (0,j - 1),INFINITE f')) = INFINITY`
             by RW_TAC arith_ss [LENGTH_CAT]
             THEN `0 < LENGTH (CAT (SEL (FINITE l) (0,j - 1),INFINITE f'))`
                   by PROVE_TAC[LENGTH_RESTN_INFINITE,LENGTH_def,PSLPathTheory.LS,xnum_11]
             THEN PROVE_TAC[]],
         REPEAT DISJ2_TAC
          THEN Q.EXISTS_TAC `j`
          THEN RW_TAC std_ss [LENGTH_RESTN_INFINITE,LS]
          THEN rename1 `UF_SEM (CAT (SEL (INFINITE f') (0,j − 1),w'')) f`
          THEN Q.EXISTS_TAC `w''`
          THEN RW_TAC arith_ss [FinitePSLPathTheory.LENGTH_RESTN]
          THEN Cases_on `w''`
          THEN RW_TAC std_ss []
          THENL
           [`LENGTH(CAT (SEL (INFINITE f') (0,j - 1),FINITE l)) = XNUM(j + LENGTH l)`
             by RW_TAC arith_ss [LENGTH_CAT,LENGTH_SEL]
             THEN FULL_SIMP_TAC std_ss [CAT_FINITE_APPEND,CAT_FINITE_APPEND,LENGTH_def,xnum_11]
             THEN `0 < LENGTH (SEL (INFINITE f') (0,j - 1) <> l)` by DECIDE_TAC
             THEN `0 < LENGTH (FINITE(SEL (INFINITE f') (0,j - 1) <> l))`
                   by PROVE_TAC[LENGTH_def,PSLPathTheory.LS,xnum_11]
             THEN PROVE_TAC[],
            `LENGTH(CAT (SEL (INFINITE f') (0,j - 1),INFINITE f'')) = INFINITY`
             by RW_TAC arith_ss [LENGTH_CAT]
             THEN `0 < LENGTH (CAT (SEL (INFINITE f') (0,j - 1),INFINITE f''))`
                   by PROVE_TAC[LENGTH_RESTN_INFINITE,LENGTH_def,PSLPathTheory.LS,xnum_11]
             THEN PROVE_TAC[]]],
      (* F_STRONG_CLOCK(f,c) *)
      INIT_TAC]);
end;

(******************************************************************************
* F_ABORT_FREE f means f contains no abort statements
******************************************************************************)
val F_ABORT_FREE_def =
 Define
  `(F_ABORT_FREE (F_BOOL b)            = T)
   /\
   (F_ABORT_FREE (F_NOT f)             = F_ABORT_FREE f)
   /\
   (F_ABORT_FREE (F_AND(f1,f2))        = F_ABORT_FREE f1 /\ F_ABORT_FREE f2)
   /\
   (F_ABORT_FREE (F_NEXT f)            = F_ABORT_FREE f)
   /\
   (F_ABORT_FREE (F_UNTIL(f1,f2))      = F_ABORT_FREE f1 /\ F_ABORT_FREE f2)
   /\
   (F_ABORT_FREE (F_SUFFIX_IMP(r,f))   = F_ABORT_FREE f)
   /\
   (F_ABORT_FREE (F_STRONG_IMP(r1,r2)) = T)
   /\
   (F_ABORT_FREE (F_WEAK_IMP(r1,r2))   = T)
   /\
   (F_ABORT_FREE (F_ABORT (f,b))       = F)
   /\
   (F_ABORT_FREE (F_STRONG_CLOCK(f,c)) = F_ABORT_FREE f)`;

(******************************************************************************
* Proof that if there are no aborts then
* F_CLOCK_COMP and F_INIT_CLOCK_COMP are equivalent.
******************************************************************************)
local
val INIT_TAC =
 RW_TAC std_ss
  [F_ABORT_FREE_def,F_CLOCK_COMP_def,F_INIT_CLOCK_COMP_def,UF_SEM_def,B_SEM];
in
val ABORT_FREE_INIT_CLOCK_COMP_EQUIV =
 store_thm
  ("ABORT_FREE_INIT_CLOCK_COMP_EQUIV",
   ``!f.
      F_ABORT_FREE f
      ==>
      !w c. UF_SEM w (F_CLOCK_COMP c f) = UF_SEM w (F_INIT_CLOCK_COMP c f)``,
   INDUCT_THEN fl_induct ASSUME_TAC
    THENL
     [(* F_BOOL b *)
      INIT_TAC,
      (* F_NOT b *)
      INIT_TAC,
      (* F_AND (f1,f2) *)
      INIT_TAC,
      (* F_NEXT f *)
      INIT_TAC
       THEN RW_TAC (arith_ss++resq_SS) [UF_SEM_F_U_CLOCK,RESTN_RESTN]
       THEN Cases_on `w`
       THEN RW_TAC arith_ss
             [LENGTH_def,GT_xnum_num_def,LENGTH_RESTN_INFINITE,
              num_to_def,xnum_to_def,NEXT_RISE,ELEM_RESTN]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN Q.EXISTS_TAC `i`
       THEN PROVE_TAC[SIMP_RULE arith_ss [] (Q.SPECL[`j`,`0`]ELEM_RESTN)],
      (* F_UNTIL(f1,f2) f *)
      INIT_TAC
       THEN RW_TAC (arith_ss++resq_SS) [ELEM_RESTN,UF_SEM_F_IMPLIES,UF_SEM_def]
       THEN Cases_on `w`
       THEN RW_TAC arith_ss
             [LENGTH_def,GT_xnum_num_def,LENGTH_RESTN_INFINITE,
              num_to_def,xnum_to_def,NEXT_RISE,ELEM_RESTN]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN Q.EXISTS_TAC `k`
       THEN PROVE_TAC[SIMP_RULE arith_ss [] (Q.SPECL[`j`,`0`]ELEM_RESTN)],
      (* F_SUFFIX_IMP(s,f) *)
      INIT_TAC
       THEN RW_TAC (arith_ss++resq_SS) [ELEM_RESTN,UF_SEM_F_IMPLIES,UF_SEM_def]
       THEN Cases_on `w`
       THEN RW_TAC (arith_ss ++resq_SS)
             [LENGTH_def,GT_xnum_num_def,LENGTH_RESTN_INFINITE,UF_SEM_F_U_CLOCK,LENGTH_RESTN,
              RESTN_FINITE,num_to_def,xnum_to_def,NEXT_RISE,ELEM_RESTN,RESTN_RESTN]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN RES_TAC
       THEN Q.EXISTS_TAC `i`
       THEN RW_TAC arith_ss []
       THEN FULL_SIMP_TAC std_ss [GSYM(SIMP_RULE arith_ss [] (Q.SPECL[`i+j`,`0`]ELEM_RESTN))]
       THEN PROVE_TAC[RESTN_FINITE],
      (* F_STRONG_IMP(s1,s2) *)
      INIT_TAC,
      (* F_WEAK_IMP(s1,s2) *)
      INIT_TAC,
      (* F_ABORT(f,b)) *)
      INIT_TAC,
      (* F_STRONG_CLOCK(f,c) *)
      INIT_TAC
       THEN RW_TAC (arith_ss++resq_SS) [UF_SEM_F_U_CLOCK,RESTN_RESTN]
       THEN Cases_on `w`
       THEN RW_TAC arith_ss
             [LENGTH_def,GT_xnum_num_def,LENGTH_RESTN_INFINITE,
              num_to_def,xnum_to_def,NEXT_RISE,ELEM_RESTN]
       THEN EQ_TAC
       THEN RW_TAC std_ss []
       THEN Q.EXISTS_TAC `i`
       THEN RW_TAC std_ss []
       THEN PROVE_TAC[SIMP_RULE arith_ss [] (Q.SPECL[`j`,`0`]ELEM_RESTN)]]);
end;

val ABORT_FREE_F_CLOCK_COMP_CORRECT =
 store_thm
  ("ABORT_FREE_F_CLOCK_COMP_CORRECT",
   ``!f. F_ABORT_FREE f ==>
         !w c. F_SEM w c f = UF_SEM w (F_CLOCK_COMP c f)``,
   PROVE_TAC[F_INIT_CLOCK_COMP_ELIM,F_INIT_CLOCK_COMP_CORRECT_def,
             ABORT_FREE_INIT_CLOCK_COMP_EQUIV]);

(******************************************************************************
* Version of Define that doesn't add to the EVAL compset
******************************************************************************)
val pureDefine = with_flag (computeLib.auto_import_definitions, false) Define;

(******************************************************************************
* Joe Hurd hack: EVAL should never get hold of this definition
******************************************************************************)
val UNINT_def = pureDefine `UNINT x = x`;

val F_CLOCK_COMP_ELIM =
 store_thm
  ("F_CLOCK_COMP_ELIM",
   ``F_SEM w c f =
      if B_SEM (ELEM w 0) c
       then UF_SEM w (F_CLOCK_COMP c f)
       else (UNINT F_SEM) w c f``,
   RW_TAC std_ss [UNINT_def,F_CLOCK_COMP_CORRECT]);

val ABORT_FREE_F_CLOCK_COMP_CORRECT_COR =
 store_thm
  ("ABORT_FREE_F_CLOCK_COMP_CORRECT_COR",
   ``F_SEM w c f =
      if F_ABORT_FREE f
       then UF_SEM w (F_CLOCK_COMP c f)
       else (UNINT F_SEM) w c f``,
   RW_TAC std_ss [UNINT_def,ABORT_FREE_F_CLOCK_COMP_CORRECT]);

(******************************************************************************
* Associativity of SERE concantenation (;)
******************************************************************************)

val S_CAT_ASSOC =
 store_thm
  ("S_CAT_ASSOC",
   ``!w r1 r2 r3.
      US_SEM w (S_CAT(S_CAT(r1,r2),r3)) =
       US_SEM w (S_CAT(r1, S_CAT(r2,r3)))``,
   RW_TAC simp_list_ss [US_SEM_def]
    THEN PROVE_TAC[APPEND_ASSOC]);

val S_NONEMPTY_def =
 Define `S_NONEMPTY r = !w. US_SEM w r ==> ~(NULL w)`;

val TL_APPEND =
 store_thm
  ("TL_APPEND",
   ``~(NULL l1) ==> (TL(l1 <> l2) = TL l1 <> l2)``,
   Induct_on `l1`
    THEN RW_TAC simp_list_ss []);

(******************************************************************************
* (r1:r2);r3 = r1:(r2;r3)
******************************************************************************)

val S_CAT_FUSION_ASSOC =
 store_thm
  ("S_CAT_FUSION_ASSOC",
   ``!w r1 r2 r3.
      S_NONEMPTY r2
      ==>
      (US_SEM w (S_CAT(S_FUSION(r1,r2),r3)) =
       US_SEM w (S_FUSION(r1, S_CAT(r2,r3))))``,
   RW_TAC simp_list_ss [US_SEM_def]
    THEN EQ_TAC
    THEN RW_TAC simp_list_ss [APPEND_ASSOC]
    THEN FULL_SIMP_TAC simp_list_ss [S_NONEMPTY_def]
    THENL
     [Q.EXISTS_TAC `w1'` THEN Q.EXISTS_TAC `w2'<>w2` THEN Q.EXISTS_TAC `l`
       THEN RW_TAC std_ss [APPEND_ASSOC]
       THEN Q.EXISTS_TAC `l::w2'` THEN Q.EXISTS_TAC `w2`
       THEN RW_TAC simp_list_ss [APPEND_ASSOC],
      Q.EXISTS_TAC `w1<>[l]<>(TL w1')` THEN Q.EXISTS_TAC `w2'`
       THEN ASSUM_LIST
             (fn thl =>
               ASSUME_TAC
                (SIMP_RULE simp_list_ss [](Q.AP_TERM `TL` (el 3 thl))))
       THEN RW_TAC simp_list_ss [APPEND_ASSOC]
       THENL
        [PROVE_TAC[TL_APPEND,APPEND_ASSOC],
         Q.EXISTS_TAC `w1` THEN Q.EXISTS_TAC `TL w1'` THEN Q.EXISTS_TAC `l`
          THEN RW_TAC simp_list_ss [APPEND_ASSOC]
          THEN RES_TAC
          THEN IMP_RES_TAC TL_APPEND
          THEN POP_ASSUM(fn th => ASSUME_TAC(Q.SPEC `w2'` th))
          THEN PROVE_TAC[APPEND_RIGHT_CANCEL,APPEND_ASSOC,APPEND]]]);

val CONCAT_APPEND =
 store_thm
  ("CONCAT_APPEND",
   ``!ll1 ll2: 'a list list. CONCAT(ll1<>ll2) = (CONCAT ll1)<>(CONCAT ll2)``,
   Induct
    THEN RW_TAC simp_list_ss [CONCAT_def]);

(******************************************************************************
* Idempotency  of r[*]: r[*];r[*] = [*]
******************************************************************************)

Theorem S_REPEAT_IDEMPOTENT:
  !w r. US_SEM w (S_CAT(S_REPEAT r,S_REPEAT r)) = US_SEM w (S_REPEAT r)
Proof
   RW_TAC simp_list_ss [US_SEM_def,B_SEM]
    THEN EQ_TAC
    THEN RW_TAC simp_list_ss []
    THENL
     [Q.EXISTS_TAC `wlist<>wlist'`
       THEN RW_TAC simp_list_ss [ALL_EL_APPEND,CONCAT_APPEND],
      Q.EXISTS_TAC `[]` THEN Q.EXISTS_TAC `CONCAT wlist`
       THEN RW_TAC simp_list_ss []
       THENL
        [Q.EXISTS_TAC `[]`
          THEN RW_TAC simp_list_ss [CONCAT_def],
         PROVE_TAC[]]]
QED

val _ = export_theory();
