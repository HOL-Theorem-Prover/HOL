
(*****************************************************************************)
(* Some properties of the PSL 1.1 semantics from Eisner, Fisman, Havlicek    *)
(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* Started: Thu Dec 18, 2003 in Haifa                                        *)
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
loadPath 
 := 
 "../official-semantics" :: "../../regexp" :: "../../path" :: !loadPath;
map load 
 ["UnclockedSemanticsTheory", 
  "SyntacticSugarTheory", "ClockedSemanticsTheory", "RewritesTheory", 
  "rich_listTheory", "intLib", "res_quanLib", "res_quanTheory"];
open FinitePathTheory PathTheory SyntaxTheory SyntacticSugarTheory
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
open FinitePathTheory PathTheory SyntaxTheory SyntacticSugarTheory
     UnclockedSemanticsTheory ClockedSemanticsTheory RewritesTheory
     arithmeticTheory listTheory rich_listTheory res_quanLib res_quanTheory
     ClockedSemanticsTheory;

(******************************************************************************
* Set default parsing to natural numbers rather than integers 
******************************************************************************)
val _ = intLib.deprecate_int();

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Start a new theory called Lemmas
******************************************************************************)
val _ = new_theory "Lemmas";

(******************************************************************************
* A simpset fragment to rewrite away quantifiers restricted with :: (a to b)
******************************************************************************)
val resq_SS = 
 simpLib.merge_ss
  [res_quanTools.resq_SS,
   rewrites
    [IN_DEF,LESS_def,LENGTH_def]];

(******************************************************************************
* Set default path theory to FinitePathTheory
******************************************************************************)
open FinitePathTheory;

(******************************************************************************
* Make SEL executable. (Why doesn't this happen automatically?)
******************************************************************************)
val _ = computeLib.add_funs[SEL_REC_AUX];

(******************************************************************************
* \top^k
******************************************************************************)
val TOP_ITER_def =
 Define `(TOP_ITER 0 = []) /\
         (TOP_ITER (SUC k) = [TOP] <> TOP_ITER k)`;

val LENGTH_TOP_ITER =
 store_thm
  ("LENGTH_TOP_ITER",
   ``LENGTH(TOP_ITER k) = k``,
   Induct_on `k`
    THEN RW_TAC list_ss [TOP_ITER_def]);

val TOP_B_NOT_B_TRUE =
 store_thm
  ("TOP_B_NOT_B_TRUE",
   ``B_SEM l (B_NOT B_TRUE) = (l = TOP)``,
   Cases_on `l`
    THEN PROVE_TAC[B_SEM_def]);

val SNOC_LAST_BUTLAST =
 store_thm
  ("SNOC_LAST_BUTLAST",
   ``!l. ~(NULL l) ==> (l = SNOC(LAST l)(BUTLAST l))``,
   Induct
     THEN RW_TAC list_ss [LAST_DEF,FRONT_DEF]
     THEN FULL_SIMP_TAC list_ss [SNOC,NULL_EQ_NIL]
     THEN PROVE_TAC[]);

val NULL_SNOC =
 store_thm
  ("NULL_SNOC",
   ``~NULL(SNOC x l)``,
   Cases_on `l`
    THEN RW_TAC list_ss [SNOC]);

val BUTLAST_LAST_EQ =
 store_thm
  ("BUTLAST_LAST_EQ",
   ``(lx = l <> [x]) = ~(NULL lx) /\ (l = BUTLAST lx) /\ (x = LAST lx)``,
   RW_TAC std_ss [GSYM SNOC_APPEND]
    THEN EQ_TAC
    THEN RW_TAC list_ss [BUTLAST,LAST,NULL_SNOC]
    THEN PROVE_TAC[SNOC_LAST_BUTLAST]);

val ELEM_LENGTH =
 store_thm
  ("ELEM_LENGTH",
   ``!v. ~(NULL v) ==> (ELEM v (LENGTH v - 1) = LAST v)``,
   Induct
    THEN RW_TAC list_ss []
    THEN Cases_on `NULL v`
    THEN RW_TAC list_ss [ELEM_def,HEAD_def,RESTN_def]
    THEN FULL_SIMP_TAC list_ss [NULL_EQ_NIL,RESTN_def,LAST_DEF]
    THEN FULL_SIMP_TAC list_ss [GSYM NULL_EQ_NIL]
    THEN IMP_RES_TAC CONS
    THEN `LENGTH v = SUC(LENGTH(TL v))` by PROVE_TAC[LENGTH]
    THEN RW_TAC list_ss [RESTN_def,REST_def]
    THEN `0 < LENGTH v` by DECIDE_TAC
    THEN PROVE_TAC [LENGTH_TL,ELEM_def,HEAD_def]);

val TOP_ITER_LENGTH =
 store_thm
  ("TOP_ITER_LENGTH",
   ``!v. ~(NULL v) /\ (!i. i < LENGTH v - 1 ==> (ELEM v i = TOP))
         ==> 
         (TOP_ITER (LENGTH v - 1) = BUTLAST v)``,
   Induct
    THEN RW_TAC list_ss []
    THEN Cases_on `NULL v`
    THEN RW_TAC list_ss [ELEM_def,HEAD_def,RESTN_def]
    THEN FULL_SIMP_TAC list_ss [NULL_EQ_NIL,RESTN_def,FRONT_DEF,LAST_DEF,TOP_ITER_def]
    THEN FULL_SIMP_TAC list_ss [GSYM NULL_EQ_NIL]
    THEN IMP_RES_TAC CONS
    THEN `LENGTH v = SUC(LENGTH(TL v))` by PROVE_TAC[LENGTH]
    THEN RW_TAC list_ss [RESTN_def,REST_def]
    THEN `0 < LENGTH v` by DECIDE_TAC
    THEN RW_TAC list_ss [TOP_ITER_def]
    THENL
     [PROVE_TAC [ELEM_def,HEAD_def,RESTN_def,HD],
      `!i. SUC i < LENGTH v ==> (ELEM (h::v) (SUC i) = TOP)` by PROVE_TAC[]
      THEN `SUC i < LENGTH v = i < LENGTH v - 1` by DECIDE_TAC
      THEN FULL_SIMP_TAC list_ss [ELEM_def,HEAD_def,RESTN_def,REST_def,HD,TL]]);
      
val EL_TOP_ITER =
 store_thm
  ("EL_TOP_ITER",
   ``!i k. i < k ==> (EL i (TOP_ITER k) = TOP)``,
   Induct THEN Induct
     THEN RW_TAC list_ss [TOP_ITER_def,EL_APPEND1]);

val Lemma1 =
 store_thm
  ("Lemma1",
   ``CLOCK_TICK v B_TRUE = ?k l. ~(l = BOTTOM) /\ (v = TOP_ITER k <> [l])``,
   RW_TAC (arith_ss ++ resq_SS) [CLOCK_TICK_def,LENGTH]
    THEN EQ_TAC
    THEN RW_TAC list_ss [LENGTH_APPEND]
    THEN FULL_SIMP_TAC list_ss [LENGTH_APPEND,LENGTH_TOP_ITER]
    THENL
     [Q.EXISTS_TAC `LENGTH v -1` THEN Q.EXISTS_TAC `ELEM v (LENGTH v - 1)`
       THEN Cases_on `ELEM v (LENGTH v - 1) = BOTTOM`
       THEN RW_TAC std_ss []
       THENL
        [PROVE_TAC[B_SEM_def],
         PROVE_TAC[B_SEM_def],
         FULL_SIMP_TAC list_ss 
          [TOP_B_NOT_B_TRUE,BUTLAST_LAST_EQ,LENGTH_NOT_NULL,ELEM_LENGTH,
           TOP_ITER_LENGTH, DECIDE ``n:num > 0 = 0 < n``]],
      RW_TAC std_ss [ELEM_EL]
       THEN `EL k (TOP_ITER k <> [l]) = l` 
            by PROVE_TAC[LENGTH_TOP_ITER,HD,NULL,EL_LENGTH_APPEND]
       THEN RW_TAC std_ss []
       THEN Cases_on `l`
       THEN RW_TAC std_ss [B_SEM_def],
      RW_TAC std_ss [ELEM_EL]
       THEN `i < LENGTH(TOP_ITER k)` by RW_TAC arith_ss [LENGTH_TOP_ITER]
       THEN RW_TAC std_ss [EL_APPEND1,EL_TOP_ITER,B_SEM_def]]);

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
   (S_CLOCK_FREE S_EMPTY             = T)
   /\
   (S_CLOCK_FREE (S_REPEAT r)        = S_CLOCK_FREE r)
   /\
   (S_CLOCK_FREE (S_CLOCK v)         = F)`;


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
         [`P`,`\(r1,r2). P r1 /\ P r2`,`\(r,b). P r`]
         (TypeBase.induction_of ``:'a sere``)))));

val LAST_APPEND_CONS =
 store_thm
  ("LAST_APPEND_CONS",
   ``!l1 l2 x. LAST(l1 <> (x::l2)) = LAST(x::l2)``,
   Induct
    THEN RW_TAC list_ss [LAST_CONS,LAST_DEF]);

val LAST_CONS_APPEND =
 store_thm
  ("LAST_CONS_APPEND",
   ``!l1 l2 x1 x2. LAST(x1 :: l1 <> (x2 :: l2)) = LAST(x2 :: l2)``,
    RW_TAC list_ss [LAST_DEF,LAST_APPEND_CONS]);

val LENGTH_APPEND_CONS_NULL =
 store_thm
  ("LENGTH_APPEND_CONS_NULL",
   ``~NULL(v1 <> (l::v2))``,
   Cases_on `v1` 
    THEN RW_TAC list_ss []);

val Lemma2 =
 store_thm
  ("Lemma2",
   ``!r v c. 
      LENGTH v > 0 /\ S_CLOCK_FREE r /\ S_SEM v c r 
      ==> 
      B_SEM (ELEM v (LENGTH v - 1)) c``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THEN RW_TAC list_ss [S_SEM_def, US_SEM_def, S_CLOCK_FREE_def]
    THEN FULL_SIMP_TAC list_ss [CLOCK_TICK_def]
    THEN RW_TAC std_ss []
    THENL
     [FULL_SIMP_TAC std_ss 
        [GSYM LENGTH_APPEND, ELEM_LENGTH,
         REWRITE_RULE[DECIDE ``0 < n:num = n > 0``]LENGTH_NOT_NULL]
       THEN Cases_on `v1` THEN Cases_on `v2`
       THEN FULL_SIMP_TAC list_ss [LAST_CONS]
       THEN RW_TAC list_ss [LAST_DEF]       
       THEN ASSUM_LIST
             (fn thl => 
               ASSUME_TAC
                (SIMP_RULE list_ss [el 1 thl] (Q.SPECL [`h'::t'`,`c`] (el 5 thl))))
       THEN RW_TAC list_ss [LAST_APPEND_CONS],
      FULL_SIMP_TAC std_ss 
        [GSYM APPEND_CONS,
         REWRITE_RULE[DECIDE ``0 < n:num = n > 0``]LENGTH_NOT_NULL]
       THEN SUBST_TAC 
             [GSYM(SIMP_CONV list_ss [DECIDE ``m + SUC n - 1 = m + n``] 
                                     ``LENGTH(v1 <> (l:'a letter::v2)) - 1``)]
             (* Rewriting fails, maybe as ``l`` in RHS, but not LHS, of equation *)
       THEN RW_TAC std_ss [ELEM_LENGTH,LENGTH_APPEND_CONS_NULL]
       THEN RW_TAC list_ss [LAST_APPEND_CONS]
       THEN ASSUM_LIST
             (fn thl => 
               ASSUME_TAC
                (SIMP_RULE list_ss [el 1 thl] (Q.SPECL [`l::v2`,`c`] (el 5 thl))))
       THEN PROVE_TAC
             [GSYM(SIMP_CONV list_ss [DECIDE ``m + SUC n - 1 = m + n``] 
                                     ``LENGTH(l:'a letter::v2) - 1``),
             SIMP_CONV list_ss [] ``~(NULL(l:'a letter::v2))``,
             ELEM_LENGTH],
      FULL_SIMP_TAC std_ss 
        [ELEM_LENGTH,
         REWRITE_RULE[DECIDE ``0 < n:num = n > 0``]LENGTH_NOT_NULL]
       THEN Induct_on `vlist`
       THEN RW_TAC list_ss [CONCAT_def]
       THEN Cases_on `h`
       THEN FULL_SIMP_TAC list_ss [CONCAT_def]
       THEN Cases_on `CONCAT vlist`
       THEN FULL_SIMP_TAC list_ss [CONCAT_def,LAST_CONS_APPEND]]);

val Conjecture1_COUNTEREXAMPLE =
 store_thm
  ("Conjecture1_COUNTEREXAMPLE",
   ``(v = [STATE(\p.F);STATE(\p.T)]) /\ (r = S_BOOL B_TRUE) /\ (c = (B_PROP clk))
     ==>
     LENGTH v > 0 /\ S_CLOCK_FREE r /\ S_SEM v c r /\ ~B_SEM (ELEM v 0) c``,
   RW_TAC (list_ss ++ resq_SS)
    [S_SEM_def,B_SEM_def,CONJ_ASSOC,LENGTH1,B_SEM_def,CLOCK_TICK_def,LENGTH,
     S_CLOCK_FREE_def, DECIDE``i<1 = (i=0)``,ELEM_def, HEAD_def,RESTN_def]
    THEN REWRITE_TAC [ONE]
    THEN RW_TAC list_ss [ELEM_def,RESTN_def,HEAD_def,B_SEM_def,REST_def,IN_DEF]);

val Proposition1 =
 store_thm
  ("Proposition1",
   ``!r v. S_CLOCK_FREE r /\  US_SEM v r ==> S_SEM v B_TRUE r``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THEN RW_TAC std_ss [S_SEM_def, US_SEM_def, S_CLOCK_FREE_def]
    THEN TRY (PROVE_TAC[])
    THENL
     [RW_TAC std_ss [Lemma1]
       THEN Q.EXISTS_TAC `0` THEN Q.EXISTS_TAC `ELEM v 0`
       THEN FULL_SIMP_TAC list_ss [LENGTH1,TOP_ITER_def,ELEM_def,HEAD_def,RESTN_def]
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss []
       THEN Cases_on `x`
       THEN RW_TAC std_ss [B_SEM_def]
       THEN FULL_SIMP_TAC list_ss [B_SEM_def],
      Q.EXISTS_TAC `vlist`
       THEN RW_TAC list_ss []
       THEN Induct_on `vlist`
       THEN RW_TAC list_ss [CONCAT_def]]);

val IS_STATE_WORD_def =
 Define
  `(IS_STATE_WORD[]             = T) /\
   (IS_STATE_WORD(TOP::v)       = F) /\
   (IS_STATE_WORD(BOTTOM::v)    = F) /\
   (IS_STATE_WORD((STATE s)::v) = IS_STATE_WORD v)`;

val IS_STATE_WORD_CLOCK_TICK_TRUE =
 store_thm
  ("IS_STATE_WORD_CLOCK_TICK_TRUE",
   ``!v. IS_STATE_WORD v /\ CLOCK_TICK v B_TRUE ==> ?s. v = [s]``,
   Induct
    THEN RW_TAC list_ss [Lemma1,ELEM_def,HEAD_def,RESTN_def]
    THEN Cases_on `k`
    THEN FULL_SIMP_TAC list_ss [TOP_ITER_def,IS_STATE_WORD_def]);

val IS_STATE_WORD_APPEND =
 store_thm
  ("IS_STATE_WORD_APPEND",
   ``!v1 v2. IS_STATE_WORD (v1 <> v2) = IS_STATE_WORD v1 /\ IS_STATE_WORD v2``,
   Induct
    THEN RW_TAC list_ss [IS_STATE_WORD_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss [IS_STATE_WORD_def]);

val Proposition1PartialConverse =
 store_thm
  ("Proposition1PartialConverse",
   ``!r v. S_CLOCK_FREE r /\  S_SEM v B_TRUE r /\ IS_STATE_WORD v ==> US_SEM v r``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THEN RW_TAC std_ss [S_SEM_def, US_SEM_def, S_CLOCK_FREE_def]
    THEN TRY (PROVE_TAC[IS_STATE_WORD_APPEND])
    THENL
     [IMP_RES_TAC IS_STATE_WORD_CLOCK_TICK_TRUE
       THEN RW_TAC list_ss [],
      IMP_RES_TAC IS_STATE_WORD_CLOCK_TICK_TRUE
       THEN RW_TAC list_ss []
       THEN FULL_SIMP_TAC list_ss [],
      Q.EXISTS_TAC `vlist`
       THEN RW_TAC list_ss []
       THEN Induct_on `vlist`
       THEN RW_TAC list_ss [CONCAT_def]
       THEN FULL_SIMP_TAC list_ss [IS_STATE_WORD_APPEND]]);

val Lemma3 =
 store_thm
  ("Lemma3",
   ``!r. S_CLOCK_FREE r 
         ==> 
         !v. US_SEM v (S_NON_ZERO_REPEAT r) = 
             ?vlist. (v = CONCAT vlist) /\
                     LENGTH vlist > 0   /\ 
                     EVERY (\v. US_SEM v r) vlist``,
   RW_TAC list_ss [US_SEM_def,S_CLOCK_FREE_def,S_NON_ZERO_REPEAT_def]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Q.EXISTS_TAC `v1::vlist`
       THEN RW_TAC list_ss [CONCAT_def],
      Q.EXISTS_TAC `HD vlist` THEN Q.EXISTS_TAC `CONCAT(TL vlist)`
       THEN RW_TAC list_ss [CONCAT_def]
       THENL
        [Cases_on `vlist`
          THEN FULL_SIMP_TAC list_ss [CONCAT_def],
         Cases_on `vlist`
          THEN FULL_SIMP_TAC list_ss [CONCAT_def,ALL_EL],
         Q.EXISTS_TAC`(TL vlist)`
          THEN Cases_on `vlist`
          THEN FULL_SIMP_TAC list_ss [CONCAT_def,ALL_EL]]]);

val Lemma4 =
 store_thm
  ("Lemma4",
   ``!r c v. 
      S_SEM v c (S_NON_ZERO_REPEAT r) = 
      ?vlist. (v = CONCAT vlist) /\
              LENGTH vlist > 0   /\ 
              EVERY (\v. S_SEM v c r) vlist``,
   RW_TAC list_ss [S_SEM_def,S_NON_ZERO_REPEAT_def]
    THEN EQ_TAC
    THEN RW_TAC std_ss []
    THENL
     [Q.EXISTS_TAC `v1::vlist`
       THEN RW_TAC list_ss [CONCAT_def],
      Q.EXISTS_TAC `HD vlist` THEN Q.EXISTS_TAC `CONCAT(TL vlist)`
       THEN RW_TAC list_ss [CONCAT_def]
       THENL
        [Cases_on `vlist`
          THEN FULL_SIMP_TAC list_ss [CONCAT_def],
         Cases_on `vlist`
          THEN FULL_SIMP_TAC list_ss [CONCAT_def,ALL_EL],
         Q.EXISTS_TAC`(TL vlist)`
          THEN Cases_on `vlist`
          THEN FULL_SIMP_TAC list_ss [CONCAT_def,ALL_EL]]]);

val BOTTOM_FREE_def =
 Define
  `(BOTTOM_FREE[]             = T) /\
   (BOTTOM_FREE(TOP::v)       = BOTTOM_FREE v) /\
   (BOTTOM_FREE(BOTTOM::v)    = F) /\
   (BOTTOM_FREE((STATE s)::v) = BOTTOM_FREE v)`;

val BOTTOM_FREE_APPEND =
 store_thm
  ("BOTTOM_FREE_APPEND",
   ``!v1 v2. BOTTOM_FREE (v1 <> v2) = BOTTOM_FREE v1 /\ BOTTOM_FREE v2``,
   Induct
    THEN RW_TAC list_ss [BOTTOM_FREE_def]
    THEN Cases_on `h`
    THEN FULL_SIMP_TAC list_ss [BOTTOM_FREE_def]);

val Lemma5 =
 store_thm
  ("Lemma5",
   ``!r. S_CLOCK_FREE r ==> !v. US_SEM v r ==> BOTTOM_FREE v``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THEN RW_TAC std_ss [US_SEM_def,S_CLOCK_FREE_def,BOTTOM_FREE_def]
    THEN RW_TAC std_ss [BOTTOM_FREE_APPEND]
    THEN TRY (PROVE_TAC[])
    THENL
     [Cases_on `ELEM v 0`
       THEN FULL_SIMP_TAC std_ss [B_SEM_def,LENGTH1]
       THEN RW_TAC std_ss []
       THEN FULL_SIMP_TAC list_ss 
             [ELEM_def,HEAD_def,BOTTOM_FREE_def,RESTN_def],
      PROVE_TAC[BOTTOM_FREE_APPEND],
      PROVE_TAC[BOTTOM_FREE_APPEND],
      PROVE_TAC[BOTTOM_FREE_APPEND],
      Induct_on `vlist`
       THEN RW_TAC list_ss [CONCAT_def]
       THEN FULL_SIMP_TAC list_ss [BOTTOM_FREE_APPEND,BOTTOM_FREE_def]]);

val CLOCK_TICK_BOTTOM_FREE =
 store_thm
  ("CLOCK_TICK_BOTTOM_FREE",
   ``!v c. CLOCK_TICK v c ==> BOTTOM_FREE v``,
   RW_TAC (list_ss ++ resq_SS) [CLOCK_TICK_def]
    THEN Induct_on `v`    
    THEN RW_TAC list_ss []
    THEN Cases_on `LENGTH v > 0`
    THEN FULL_SIMP_TAC list_ss [ELEM_def,HEAD_def,RESTN_def]
    THENL
     [`LENGTH v = SUC(LENGTH v - 1)` by DECIDE_TAC
        THEN ASSUM_LIST(fn thl => ASSUME_TAC(ONCE_REWRITE_RULE[el 1 thl](el 4 thl)))
        THEN FULL_SIMP_TAC list_ss [RESTN_def,REST_def]
        THEN ASSUM_LIST(fn thl => ASSUME_TAC(Q.GEN `i`(Q.SPEC `SUC i` (el 4 thl))))
        THEN `!i. SUC i < LENGTH v = i < LENGTH v -1` by DECIDE_TAC
        THEN ASSUM_LIST
               (fn thl => 
                 ASSUME_TAC(SIMP_RULE list_ss [el 1 thl,RESTN_def,REST_def](el 2 thl)))
        THEN RES_TAC
        THEN `0 < LENGTH v` by DECIDE_TAC
        THEN ASSUM_LIST
              (fn thl => 
                ASSUME_TAC
                 (SIMP_RULE list_ss [el 1 thl,RESTN_def] (Q.SPEC `0` (el 9 thl))))
        THEN Cases_on `h` 
        THEN FULL_SIMP_TAC list_ss [BOTTOM_FREE_def,B_SEM_def],
      `LENGTH v = 0` by DECIDE_TAC
        THEN FULL_SIMP_TAC list_ss [LENGTH_NIL,RESTN_def]
        THEN Cases_on `h` 
        THEN FULL_SIMP_TAC list_ss [BOTTOM_FREE_def,B_SEM_def]]);

val Lemma6 =
 store_thm
  ("Lemma6",
   ``!r c v. S_SEM v c r ==> BOTTOM_FREE v``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THEN RW_TAC std_ss [S_SEM_def,S_CLOCK_FREE_def,BOTTOM_FREE_def]
    THEN RW_TAC std_ss [BOTTOM_FREE_APPEND]
    THEN TRY (PROVE_TAC[])
    THENL
     [PROVE_TAC[CLOCK_TICK_BOTTOM_FREE],
      PROVE_TAC[BOTTOM_FREE_APPEND],
      PROVE_TAC[BOTTOM_FREE_APPEND],
      PROVE_TAC[BOTTOM_FREE_APPEND],
      Induct_on `vlist`
       THEN RW_TAC list_ss [CONCAT_def]
       THEN FULL_SIMP_TAC list_ss [BOTTOM_FREE_APPEND,BOTTOM_FREE_def]
       THEN PROVE_TAC[]]);

(* Duplicate definition commented out, then proved as TOP_ITER_CONS 
val TOP_ITER_def =
 Define
  `(TOP_ITER 0 = []) /\ (TOP_ITER(SUC n) = TOP :: TOP_ITER n)`;

val LENGTH_TOP_ITER =
 store_thm
  ("LENGTH_TOP_ITER",
   ``!n. LENGTH(TOP_ITER n) = n``,
   Induct
    THEN RW_TAC list_ss [TOP_ITER_def]);
*)

val TOP_ITER_CONS =
 store_thm
  ("TOP_ITER_CONS",
  ``(TOP_ITER 0 = []) /\ (TOP_ITER(SUC n) = TOP :: TOP_ITER n)``,
  PROVE_TAC[TOP_ITER_def,APPEND]);

val TOP_ITER_APPEND =
 store_thm
  ("TOP_ITER_APPEND",
   ``!m n. TOP_ITER(m + n) = TOP_ITER m <> TOP_ITER n``,
   Induct
    THEN RW_TAC list_ss [TOP_ITER_CONS,ADD_CLAUSES]);

val TOP_ITER_APPEND_TOP =
 store_thm
  ("TOP_ITER_APPEND_TOP",
   ``!m. TOP_ITER m <> [TOP] = [TOP] <> TOP_ITER m``,
   Induct
    THEN RW_TAC list_ss [TOP_ITER_CONS,ADD_CLAUSES]);

val US_SEM_TOP =
 store_thm
  ("US_SEM_TOP",
   ``!r v. S_CLOCK_FREE r /\ US_SEM v r ==> US_SEM (TOP_ITER(LENGTH v)) r``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THEN RW_TAC (list_ss ++ resq_SS) 
          [US_SEM_def,S_CLOCK_FREE_def,BOTTOM_FREE_def,TOP_ITER_CONS,
           LENGTH_TOP_ITER,LENGTH_APPEND,LENGTH_SEL]
    THENL
     [REWRITE_TAC[ONE,TOP_ITER_CONS]
       THEN FULL_SIMP_TAC std_ss [LENGTH1,ELEM_def,HEAD_def,RESTN_def,REST_def]
       THEN RW_TAC list_ss [HD_SEL0,TOP_ITER_CONS,HEAD_def,B_SEM_def],
      Q.EXISTS_TAC `TOP_ITER(LENGTH v1)` THEN Q.EXISTS_TAC `TOP_ITER (LENGTH v2)`
       THEN RW_TAC list_ss [TOP_ITER_APPEND],
      Q.EXISTS_TAC `TOP_ITER(LENGTH v1)` THEN Q.EXISTS_TAC `TOP_ITER (LENGTH v2)`
       THEN Q.EXISTS_TAC `TOP`
       THEN RW_TAC list_ss [TOP_ITER_APPEND]
       THENL
        [REWRITE_TAC[ONE,TOP_ITER_CONS,TOP_ITER_APPEND_TOP,GSYM APPEND_ASSOC],
         RES_TAC
          THEN FULL_SIMP_TAC list_ss [TOP_ITER_APPEND]
          THEN PROVE_TAC[ONE,TOP_ITER_CONS],
         RES_TAC
          THEN FULL_SIMP_TAC list_ss [TOP_ITER_CONS]],
      PROVE_TAC[],
      PROVE_TAC[],
      Q.EXISTS_TAC `MAP (\v. TOP_ITER(LENGTH v)) vlist`
       THEN Induct_on `vlist`
       THEN RW_TAC list_ss [CONCAT_def,TOP_ITER_CONS,TOP_ITER_APPEND]]);

val ALL_EL_US_SEM_TOP =
 store_thm
  ("ALL_EL_US_SEM_TOP",
   ``!vlist r. S_CLOCK_FREE r /\ ALL_EL (\v'. US_SEM v' r) vlist
               ==> 
               ALL_EL (\v. US_SEM (TOP_ITER (LENGTH v)) r) vlist``,
   Induct
    THEN RW_TAC list_ss [US_SEM_TOP]);

val SEL_REC_APPEND1 = 
 store_thm
  ("SEL_REC_APPEND1",
   ``!n m (l1:'a list). ((n + m) <= LENGTH l1) ==>
      (!l2. SEL_REC n m (APPEND l1 l2) = SEL_REC n m l1)``,
   REPEAT Induct
    THEN RW_TAC list_ss [LENGTH,SEL_REC_def,NOT_SUC_LESS_EQ_0,
                         HEAD_def,REST_def,ADD,ADD_0]);

val SEL_APPEND1 =
 store_thm
  ("SEL_APPEND1",
   ``!(w1:'a list) w2 k. k < LENGTH w1 ==> (SEL (w1 <> w2) (0,k) = SEL w1 (0,k))``,
   RW_TAC list_ss [SEL_def,SEL_REC_APPEND1]);

val SEL_REC_APPEND2 = 
 store_thm
  ("SEL_REC_APPEND2",
   ``!n m l1:'a list l2.
       (LENGTH l1 <= m) ==>
       (SEL_REC n m (APPEND l1 l2) = SEL_REC n (m - (LENGTH l1)) l2)``,
   REPEAT Induct
    THEN RW_TAC list_ss [LENGTH,SEL_REC_def,NOT_SUC_LESS_EQ_0,
                         HEAD_def,REST_def,ADD,ADD_0]);

val SEL_REC_LENGTH = 
 store_thm
  ("SEL_REC_LENGTH",
   ``!l:'a list. SEL_REC (LENGTH l) 0 l = l``,
   REPEAT Induct
    THEN RW_TAC list_ss [LENGTH,SEL_REC_def,NOT_SUC_LESS_EQ_0,
                         HEAD_def,REST_def,ADD,ADD_0]);

val SEL_LENGTH = 
 store_thm
  ("SEL_LENGTH",
   ``!l:'a list. 0 < LENGTH l ==> (SEL l (0,LENGTH l - 1) = l)``,
   RW_TAC arith_ss [SEL_def,SEL_REC_LENGTH]);

val SEL_SING_LENGTH = 
 store_thm
  ("SEL_SING_LENGTH",
   ``!x:'a. SEL [x] (0,0) = [x]``,
   GEN_TAC
    THEN `0 < LENGTH[x]` by RW_TAC list_ss []
    THEN `LENGTH[x] - 1 = 0` by RW_TAC list_ss []
    THEN PROVE_TAC[SEL_LENGTH]);

val SEL_APPEND2 =
 store_thm
  ("SEL_APPEND2",
   ``!(w1:'a list) w2 m n. 
      LENGTH w1 <= m /\ m <= n 
      ==> 
      (SEL (w1 <> w2) (m,n) = SEL w2 (m - LENGTH w1, n - LENGTH w1))``,
   RW_TAC arith_ss [SEL_def,SEL_REC_APPEND2]);

val SEL_APPEND3 =
 store_thm
  ("SEL_APPEND3",
   ``!(w1:'a list) w2 m. 
      LENGTH w1 <= m 
      ==> 
      (SEL (w1 <> w2) (0,m) = w1 <> SEL w2 (0,m - LENGTH w1))``,
   REPEAT GEN_TAC
    THEN Cases_on `w1=[]`
    THEN RW_TAC list_ss []
    THEN `~(LENGTH w1 = 0)` by PROVE_TAC[LENGTH_NIL]
    THEN RW_TAC arith_ss 
          [Q.SPECL [`w1<>w2`,`LENGTH w1 - 1`,`0`,`m`] SEL_SPLIT,
           SEL_APPEND1,SEL_LENGTH,APPEND_LEFT_CANCEL,SEL_APPEND2]);

val MAP_TOP_ITER_LENGTH =
 store_thm
  ("MAP_TOP_ITER_LENGTH",
   ``!vl. CONCAT(MAP (\v. TOP_ITER (LENGTH v)) vl) = 
          TOP_ITER (LENGTH(CONCAT vl))``,
   Induct
    THEN RW_TAC list_ss [CONCAT_def,TOP_ITER_CONS,TOP_ITER_APPEND]);

(* 
Ad hoc definition and lemma for the r[*] case of Lemma 7 below.

vlist              = [[....];[....];[....];[....]; ... ;[....]]

CONCAT vlist       = [ ....   ....   ....   ....   ...   ....]
                     |--------k-------|TT   TTTT   ...   TTTT]
                     |                |

SEL_CONCAT vlist k = [[....];[....];[..TT];[TTTT]; ... ;[TTTT]]  

*)

val SEL_CONCAT_def =
 Define
  `(SEL_CONCAT [] k = [SEL [] (0,k)]) (* Yuk! Simplifies SEL_CONCAT_LEMMA *)
   /\
   (SEL_CONCAT (x::xl) k = 
     if k < LENGTH x
      then 
       (SEL x (0,k) <> TOP_ITER(LENGTH x - (k+1))) :: MAP (\v. TOP_ITER (LENGTH v)) xl
      else x :: SEL_CONCAT xl (k - LENGTH x))`;

val SEL_CONCAT_LEMMA =
 store_thm
  ("SEL_CONCAT_LEMMA",
   ``!vlist k.
       SEL (CONCAT vlist) (0,k) <> TOP_ITER (LENGTH (CONCAT vlist) - (k+1)) 
        = CONCAT(SEL_CONCAT vlist k)``,
   Induct
    THEN RW_TAC list_ss 
          [SEL_CONCAT_def,CONCAT_def,SEL_APPEND1,SEL_APPEND3,
           TOP_ITER_def,MAP_TOP_ITER_LENGTH]
    THEN RW_TAC std_ss 
          [GSYM APPEND_ASSOC,APPEND_LEFT_CANCEL,TOP_ITER_APPEND,
           DECIDE ``k < m ==> (m + n - (k+1) = (m - (k+1)) + n)``]
    THEN ASSUM_LIST(fn thl => ASSUME_TAC(Q.SPEC `k - LENGTH h` (el 2 thl)))
    THEN RW_TAC std_ss 
           [DECIDE ``~(k:num < m) ==> (m + n - (k + 1) = n - (k - m + 1))``]);

val LAMBDA_COMP =
 store_thm
  ("LAMBDA_COMP",
   ``(\x. f x) o (\y. g y) = \y. f(g y)``,
   CONV_TAC FUN_EQ_CONV
    THEN RW_TAC std_ss []);

val Lemma7 =
 store_thm
  ("Lemma7",
   ``!r v.
       S_CLOCK_FREE r /\ US_SEM v r
       ==> 
       !k :: LESS(LENGTH v). 
        US_SEM (SEL v (0,k) <> TOP_ITER(LENGTH v - k - 1)) r``,
   INDUCT_THEN sere_induct ASSUME_TAC
    THEN RW_TAC (list_ss ++ resq_SS) 
          [US_SEM_def,S_CLOCK_FREE_def,BOTTOM_FREE_def,TOP_ITER_CONS,
           LENGTH_TOP_ITER,LENGTH_APPEND,LENGTH_SEL]
    THENL
     [`k=0` by DECIDE_TAC
       THEN FULL_SIMP_TAC list_ss [LENGTH1,ELEM_def,HEAD_def,RESTN_def,REST_def]
       THEN RW_TAC list_ss [HD_SEL0,TOP_ITER_CONS,HEAD_def]
       THEN FULL_SIMP_TAC list_ss [],
      FULL_SIMP_TAC (list_ss ++ resq_SS) []
       THEN Cases_on `k < LENGTH v1`
       THEN RES_TAC
       THENL
        [Q.EXISTS_TAC `SEL v1 (0,k) <> TOP_ITER (LENGTH v1 - (k + 1))` 
          THEN Q.EXISTS_TAC `TOP_ITER (LENGTH v2)`
          THEN RW_TAC arith_ss 
                [US_SEM_TOP,SEL_APPEND1,GSYM TOP_ITER_APPEND,GSYM APPEND_ASSOC],
         Q.EXISTS_TAC `v1` 
          THEN Q.EXISTS_TAC 
                `SEL v2 (0,k - LENGTH v1) <> 
                 TOP_ITER (LENGTH v1 + LENGTH v2 - (k + 1))`
          THEN RW_TAC arith_ss [SEL_APPEND3,APPEND_LEFT_CANCEL,GSYM APPEND_ASSOC]
          THEN ASSUM_LIST(fn thl => ASSUME_TAC(Q.SPEC `k - LENGTH v1` (el 2 thl)))
          THEN IMP_RES_TAC  (* Not sure why DECIDE_TAC fails here! *)
                (DECIDE ``k:num < m + n ==> ~(k < m) ==> k - m < n``)
          THEN IMP_RES_TAC
                (DECIDE ``k:num < m + n ==> ~(k < m) 
                          ==> 
                          (n - (k - m + 1) = m + n - (k + 1))``)
          THEN PROVE_TAC[]],
      FULL_SIMP_TAC (list_ss ++ resq_SS) []
       THEN Cases_on `k < LENGTH v1`
       THEN RES_TAC
       THENL
        [Q.EXISTS_TAC `SEL (v1<>[l]) (0,k) <> TOP_ITER (LENGTH v1 - (k + 1))` 
          THEN Q.EXISTS_TAC `TOP_ITER (LENGTH v2)`
          THEN Q.EXISTS_TAC `TOP`
          THEN `(LENGTH v1 - (k + 1) + 1 = LENGTH v1 - k) /\
                (LENGTH v1 - (k + 1) + (1 + LENGTH v2) = 
                 LENGTH v1 + LENGTH v2 - k)` by DECIDE_TAC
          THEN RW_TAC list_ss 
                [US_SEM_TOP,SEL_APPEND1,GSYM(EVAL ``TOP_ITER 1``)]
          THEN RW_TAC std_ss [GSYM APPEND_ASSOC,GSYM TOP_ITER_APPEND]
          THENL
           [FULL_SIMP_TAC list_ss [LENGTH_APPEND]
             THEN `k < LENGTH v1 + 1` by DECIDE_TAC
             THEN `US_SEM (SEL (v1 <> [l]) (0,k) <> TOP_ITER (LENGTH v1 - k)) r` 
                   by PROVE_TAC[]
             THEN `k < LENGTH v1` by DECIDE_TAC
             THEN PROVE_TAC[SEL_APPEND1],
            PROVE_TAC[US_SEM_TOP,TOP_ITER_CONS,LENGTH]],
         Cases_on `k = LENGTH v1`
          THEN RW_TAC std_ss []
          THENL
           [Q.EXISTS_TAC `v1` 
             THEN Q.EXISTS_TAC 
                   `TOP_ITER (LENGTH v2)`
             THEN Q.EXISTS_TAC `l` 
             THEN RW_TAC arith_ss [APPEND_RIGHT_CANCEL,APPEND_ASSOC]
             THEN `LENGTH v1 < LENGTH(v1 <> [l])` 
                   by RW_TAC arith_ss [LENGTH_APPEND, LENGTH]
             THEN RW_TAC arith_ss [SEL_APPEND1]
             THEN `LENGTH(v1 <> [l]) - 1 = LENGTH v1`
                    by RW_TAC arith_ss [LENGTH_APPEND, LENGTH]
             THEN `0 < LENGTH(v1 <> [l])` by RW_TAC arith_ss [LENGTH_APPEND, LENGTH]
             THEN ASSUM_LIST(fn thl => ONCE_REWRITE_TAC[GSYM(el 2 thl)])
             THENL
              [PROVE_TAC[SEL_LENGTH],
               `0 < LENGTH(l::v2)` by RW_TAC list_ss []
                THEN RES_TAC
                THEN `LENGTH (l::v2) - (0 + 1) = LENGTH v2` by RW_TAC list_ss []
                THEN `l::v2 = [l] <> v2` by RW_TAC list_ss []
                THEN `0 < LENGTH [l]` by RW_TAC list_ss []
                THEN ASSUM_LIST
                      (fn thl => 
                        ASSUME_TAC
                         (SIMP_RULE arith_ss 
                           [SEL_SING_LENGTH,SEL_APPEND1,el 1 thl, el 2 thl,el 3 thl]
                           (el 4 thl)))
                THEN PROVE_TAC[APPEND]],
            Q.EXISTS_TAC `v1` 
             THEN Q.EXISTS_TAC 
                   `SEL v2 (0,k - (LENGTH v1 + 1)) <> 
                    TOP_ITER (LENGTH v1 + LENGTH v2 - k)`
             THEN Q.EXISTS_TAC `l` 
             THEN RW_TAC arith_ss [SEL_APPEND3,APPEND_LEFT_CANCEL,GSYM APPEND_ASSOC]
             THEN ASSUM_LIST
                   (fn thl => ASSUME_TAC(Q.SPEC `k - (LENGTH v1 + 1)` (el 2 thl)))
             THEN FULL_SIMP_TAC std_ss [LENGTH,LENGTH_APPEND]
             THEN `LENGTH [l] = 1` by RW_TAC list_ss []
             THEN IMP_RES_TAC
                   (DECIDE ``(l:num = 1) ==> ~(k:num < m) ==> ~(k = m) ==> l <= k - m``)
             THEN RW_TAC arith_ss [SEL_APPEND3,APPEND_RIGHT_CANCEL,APPEND_ASSOC]
             THEN IMP_RES_TAC
                   (DECIDE ``k:num < m + (n + 1) 
                             ==> ~(k < m) 
                             ==> ~(k = m)
                             ==> k - m < SUC n``)
             THEN RES_TAC
             THEN POP_ASSUM(K ALL_TAC)
             THEN POP_ASSUM(K ALL_TAC)
             THEN IMP_RES_TAC
                   (DECIDE ``k:num < m + (n + 1) 
                             ==> ~(k < m) 
                             ==> ~(k = m)
                             ==> (SUC n - (k - m + 1) = m + n - k)``)
             THEN POP_ASSUM(fn th => FULL_SIMP_TAC std_ss [th])
             THEN `l::v2 = [l] <> v2` by RW_TAC list_ss []
             THEN POP_ASSUM(fn th => FULL_SIMP_TAC std_ss [th])
             THEN IMP_RES_TAC SEL_APPEND3
             THEN POP_ASSUM(fn th => FULL_SIMP_TAC std_ss [APPEND,LENGTH,th])
             THEN `k - (LENGTH(v1:'a letter list) + 1) = k - LENGTH v1 - 1` by DECIDE_TAC
             THEN PROVE_TAC[]]],
      FULL_SIMP_TAC (list_ss ++ resq_SS) [],
      FULL_SIMP_TAC (list_ss ++ resq_SS) [],
      FULL_SIMP_TAC (list_ss ++ resq_SS) []
       THEN Q.EXISTS_TAC `SEL_CONCAT vlist k`
       THEN RW_TAC std_ss [SEL_CONCAT_LEMMA]
       THEN ASSUM_LIST(fn thl => UNDISCH_TAC(concl(el 1 thl)))
       THEN Q.SPEC_TAC(`k`,`k`)
       THEN Induct_on `vlist`
       THEN RW_TAC list_ss [SEL_CONCAT_def,CONCAT_def]
       THEN Cases_on `k < LENGTH (CONCAT vlist)`
       THEN RW_TAC list_ss [ALL_EL_US_SEM_TOP,ALL_EL_MAP,LAMBDA_COMP]]);

val Lemmas1_7 =  [Lemma1,Lemma2,Lemma3,Lemma4,Lemma5,Lemma6,Lemma7];

val _ = export_theory();







