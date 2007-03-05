(* =====================================================================*)
(* FILE: mk_word_bitop.ml           DATE: 14 Aug 1992                   *)
(* AUTHOR: Wai WONG                                                     *)
(* TRANSLATOR: Paul Curzon  1 June 1993, September 1994                 *)
(* UPDATED for new res_quan theories by Joe Hurd, November 2001         *)
(* Writes: word_bitop.th                                                *)
(* Uses: Libraries: arith res_quan                                      *)
(* Description: Creates a theore for generic word bitwise operations    *)
(* =====================================================================*)
(* PC 18/11/93: SEG ->WSEG *)


open HolKernel Parse boolLib Prim_rec;
open Base numLib res_quanLib;
open rich_listTheory pairTheory arithmeticTheory prim_recTheory numTheory;
open Cond_rewrite word_baseTheory;
open res_quanTheory bossLib pred_setTheory;

val ARITH_TAC = Base.ARITH_TAC;

val _ = new_theory "word_bitop";

val word_CASES_TAC =
    let val cthm = word_baseTheory.word_cases
    in
       (fn w => CHOOSE_THEN SUBST1_TAC (ISPEC w cthm))
    end;

val word_INDUCT_TAC =
    let val ithm = word_baseTheory.word_induct
    in
     (INDUCT_THEN ithm (fn t => ALL_TAC))
    end;

val RESQ_WORDLEN_TAC =
    (CONV_TAC RES_FORALL_CONV THEN word_INDUCT_TAC
     THEN PURE_ONCE_REWRITE_TAC[word_baseTheory.IN_PWORDLEN]
     THEN GEN_TAC THEN DISCH_TAC);

val GGEN_TAC = RESQ_GEN_TAC ORELSE GEN_TAC;

(* --------------------------------------------------------------------- *)
(* We begin with some lemmas about lists. They are used in the proofs.  *)
(* --------------------------------------------------------------------- *)
val LASTN_BUTLASTN_SEG = prove(
    (--`!m k (l:'a list). (m + k) <= (LENGTH l) ==>
     (LASTN m (BUTLASTN k l) = SEG m((LENGTH l) - (m + k))l)`--),
    let val lem1 = ARITH_PROVE
         (--`!l m k. (m+k)<=l ==>((m + (l - (m + k))) = (l - k))`--)
    val lem2 = ARITH_PROVE
         (--`!l m k. (m+k)<=l ==> ((l - (m + (l - (m + k)))) = k)`--)
    in
    REPEAT STRIP_TAC THEN COND_REWRITE1_TAC SEG_LASTN_BUTLASTN THENL[
        IMP_RES_THEN (fn t => REWRITE_TAC[t])lem1
        THEN MATCH_ACCEPT_TAC SUB_LESS_EQ,
        IMP_RES_THEN (fn t => REWRITE_TAC[t])lem2]
    end);

(*---------------------------------------------------------------*)
(* Bitwise operators                                             *)
(*---------------------------------------------------------------*)

(*---------------------------------------------------------------*)
(* PBITOP (op:'a word -> 'b word) is true if op is a bitwise     *)
(* unary operator                                                *)
(*---------------------------------------------------------------*)

val PBITOP_def = Define
  `PBITOP =
   {(op:'a word -> 'b word) |
    !n. !w:'a word ::PWORDLEN n. (op w) IN PWORDLEN n /\
    !m k. ((m + k) <= n) ==> (op(WSEG m k w) = WSEG m k (op w))}`;

val IN_PBITOP = store_thm
  ("IN_PBITOP",
   ``!op.
       op IN PBITOP =
       !n. !w:'a word ::PWORDLEN n. (op w) IN PWORDLEN n /\
       !m k. ((m + k) <= n) ==> (op(WSEG m k w) = WSEG m k (op w))``,
   RW_TAC std_ss [PBITOP_def, GSPECIFICATION]);

val PBITOP_PWORDLEN = store_thm("PBITOP_PWORDLEN",
    (--`!op:('a)word->('b)word::PBITOP. !n. !w:('a)word::PWORDLEN n.
     ((op w) IN PWORDLEN n)`--),
    REPEAT (RESQ_GEN_TAC ORELSE GEN_TAC)
    THEN IMP_RES_TAC IN_PBITOP THEN RESQ_RES_TAC);

val PBITOP_WSEG = store_thm("PBITOP_WSEG",
    (--`!op:('a)word->('b)word::PBITOP. !n. !w:('a)word::PWORDLEN n.
     !m k. ((m + k) <= n) ==> (op(WSEG m k w) = WSEG m k (op w))`--),
    RESQ_GEN_TAC THEN GEN_TAC THEN RESQ_GEN_TAC
    THEN IMP_RES_TAC IN_PBITOP THEN RESQ_RES_TAC);

val PBITOP_BIT = store_thm("PBITOP_BIT",
    (--`!op:('a)word->('b)word::PBITOP.
     !n. !w:'a word ::PWORDLEN n. !k. (k < n) ==>
     (op(WORD[BIT k w]) = WORD[BIT k (op w)])`--),
    CONV_TAC RES_FORALL_CONV THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[IN_PBITOP]
    THEN DISCH_TAC THEN GEN_TAC THEN RESQ_GEN_TAC
    THEN REPEAT STRIP_TAC THEN RESQ_RES_TAC
    THEN RESQ_IMP_RES_TAC (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV) WSEG_BIT)
    THEN RES_TAC THEN POP_ASSUM SUBST1_TAC THEN POP_ASSUM SUBST1_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
    THEN PURE_REWRITE_TAC[ADD] THEN IMP_RES_TAC LESS_EQ);

val BIT_op_EXISTS = prove(
    (--`!op:('a)word->('b)word::PBITOP. ?op':'a->'b. !n. !w:('a)word::PWORDLEN n.
     !k. (k < n) ==> ((BIT k (op w)) = (op'(BIT k w)))`--),
    RESQ_GEN_TAC THEN EXISTS_TAC(--`\b:'a.BIT 0((op:('a)word->('b)word)(WORD[b]))`--)
    THEN GEN_TAC THEN CONV_TAC RES_FORALL_CONV THEN GEN_TAC
    THEN REPEAT STRIP_TAC
    THEN RW_TAC std_ss []
    THEN RESQ_IMP_RES_TAC PBITOP_BIT THEN RES_THEN SUBST1_TAC
    THEN REWRITE_TAC[BIT0]);

(*---------------------------------------------------------------*)
(* PBITBOP (op:'a word -> 'b word -> 'c word) is true if op is a *)
(*  bitwise binary operator                                     *)
(*---------------------------------------------------------------*)

val PBITBOP_def = Define
  `PBITBOP =
   {(op:'a word  -> 'b word -> 'c word) |
    !n. !w1:'a word ::PWORDLEN n. !w2:'b word ::PWORDLEN n.
    ((op w1 w2) IN PWORDLEN n) /\
    !m k. ((m + k) <= n) ==>
    (op (WSEG m k w1) (WSEG m k w2) = WSEG m k (op w1 w2))}`;

val IN_PBITBOP = store_thm
  ("IN_PBITBOP",
   ``!op.
       op IN PBITBOP =
       !n. !w1:'a word ::PWORDLEN n. !w2:'b word ::PWORDLEN n.
       ((op w1 w2) IN PWORDLEN n) /\
       !m k. ((m + k) <= n) ==>
       (op (WSEG m k w1) (WSEG m k w2) = WSEG m k (op w1 w2))``,
   RW_TAC std_ss [PBITBOP_def, GSPECIFICATION]);

val PBITBOP_PWORDLEN = store_thm("PBITBOP_PWORDLEN",
    (--`!op:'a word  -> 'b word -> 'c word::PBITBOP.
     !n. !w1:'a word ::PWORDLEN n. !w2:'b word ::PWORDLEN n.
     ((op w1 w2) IN PWORDLEN n)`--),
    REPEAT (RESQ_GEN_TAC ORELSE GEN_TAC)
    THEN IMP_RES_TAC IN_PBITBOP THEN RESQ_RES_TAC);

val PBITBOP_WSEG = store_thm("PBITBOP_WSEG",
    (--`!op:'a word  -> 'b word -> 'c word::PBITBOP.
     !n. !w1:'a word ::PWORDLEN n. !w2:'b word ::PWORDLEN n.
     !m k. ((m + k) <= n) ==>
     (op (WSEG m k w1) (WSEG m k w2) = WSEG m k (op w1 w2))`--),
    RESQ_GEN_TAC THEN GEN_TAC THEN  REPEAT RESQ_GEN_TAC
    THEN IMP_RES_TAC IN_PBITBOP
    THEN RESQ_RES_TAC
    THEN ASM_REWRITE_TAC[]);

val PBITBOP_EXISTS = store_thm("PBITBOP_EXISTS",
    (--`!f:'a->'b->'c. ?fn. !l1 l2.
           fn (WORD l1)(WORD l2) = WORD(MAP2 f l1 l2)`--),
    let val th = prove_rec_fn_exists word_Ax
                       (--`bt (WORD l) = (l:'a list)`--)
    in
     GEN_TAC THEN CHOOSE_TAC
         (INST_TYPE [{residue =(==`:'b`==),redex=(==`:'a`==)}] th)
     THEN CHOOSE_TAC th THEN EXISTS_TAC
      (--`\(w1:('a)word) (w2:('b)word).
                WORD(MAP2 (f:'a->'b->'c) (bt' w1) (bt w2))`--)
     THEN CONV_TAC (DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[]
    end);

(*---------------------------------------------------------------*)
(* WMAP: applies a function to every bit of a word              *)
(* WMAP: ('a->'b) -> 'a word -> 'b word                         *)
(*---------------------------------------------------------------*)

val WMAP_DEF = new_recursive_definition {
 name = "WMAP_DEF",
 rec_axiom = word_Ax,
 def =
 --`
   !f:'a->'b. !l. WMAP f (WORD l) = WORD (MAP f l)
 `--
 };

val WMAP_PWORDLEN = store_thm("WMAP_PWORDLEN",
    (--`!w::PWORDLEN n. !f:'a->'b. (WMAP f w) IN PWORDLEN n`--),
    CONV_TAC RES_FORALL_CONV THEN word_INDUCT_TAC
    THEN REWRITE_TAC[WMAP_DEF,IN_PWORDLEN,LENGTH_MAP]);

val WMAP0 = store_thm("WMAP_0",
    (--`!f:'a->'b. (WMAP f (WORD[]:'a word) = (WORD []:'b word))`--),
    REWRITE_TAC[WMAP_DEF,MAP]);

val WMAP_BIT = store_thm("WMAP_BIT",
    (--`!n. !w:'a word ::PWORDLEN n. !k. k < n ==>
     !f:'a->'b. BIT k (WMAP f w) = f (BIT k w)`--),
    GEN_TAC THEN RESQ_WORDLEN_TAC THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[BIT_DEF,WMAP_DEF]
    THEN MATCH_MP_TAC ELL_MAP THEN FIRST_ASSUM (SUBST1_TAC)
    THEN FIRST_ASSUM ACCEPT_TAC);

val WMAP_WSEG = store_thm("WMAP_WSEG",
    (--`!n. !w :: PWORDLEN n.
     !m k. (m + k) <= n ==>
     !f:'a->'b. (WMAP f(WSEG m k w) = WSEG m k(WMAP f w))`--),
    GEN_TAC THEN CONV_TAC RES_FORALL_CONV THEN word_INDUCT_TAC
    THEN REWRITE_TAC[WMAP_DEF,WSEG_DEF,IN_PWORDLEN,WORD_11]
    THEN GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM)
    THEN REPEAT STRIP_TAC THEN COND_REWRITE1_TAC BUTLASTN_MAP THENL[
     IMP_RES_TAC LESS_EQ_SPLIT,
     COND_REWRITE1_TAC LASTN_MAP THENL[
      COND_REWRITE1_TAC LENGTH_BUTLASTN
      THEN COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB)
      THEN FIRST_ASSUM ACCEPT_TAC,
      REFL_TAC]]);

val WMAP_PBITOP = store_thm("WMAP_PBITOP",
    (--`!f:'a->'b. (WMAP f) IN PBITOP`--),
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[IN_PBITOP]
    THEN GEN_TAC THEN RESQ_GEN_TAC THEN CONJ_TAC THENL[
     RESQ_IMP_RES_THEN MATCH_ACCEPT_TAC WMAP_PWORDLEN,
     REPEAT STRIP_TAC THEN RESQ_IMP_RES_TAC WMAP_WSEG
     THEN RES_THEN MATCH_ACCEPT_TAC]);

val WMAP_WCAT = store_thm("WMAP_WCAT",
    (--`!w1 w2 (f:'a->'b).
     WMAP f(WCAT (w1,w2)) = WCAT ((WMAP f w1), (WMAP f w2))`--),
    REPEAT (word_INDUCT_TAC THEN GEN_TAC) THEN GEN_TAC
    THEN REWRITE_TAC[WCAT_DEF,WMAP_DEF,MAP_APPEND]);

val WMAP_o = store_thm("WMAP_o",
    (--`!w. !f:'a->'b. !g:'b->'c. WMAP g (WMAP f w) = WMAP (g o f) w`--),
    word_INDUCT_TAC THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[WMAP_DEF,MAP_MAP_o]);

(*---------------------------------------------------------------*)
(* FORALLBITS : ('a -> bool) -> ('a)word -> bool                        *)
(*---------------------------------------------------------------*)

val FORALLBITS_DEF = new_recursive_definition {
 name = "FORALLBITS_DEF",
 rec_axiom = word_Ax,
 def =
 --`
   !P:'a->bool. !l. FORALLBITS P (WORD l) = ALL_EL P l
 `--
 };

val FORALLBITS = store_thm("FORALLBITS",
    (--`!n. !w:('a)word::PWORDLEN n. !P.
     FORALLBITS P w = (!k. k < n ==> P(BIT k w))`--),
    GEN_TAC THEN CONV_TAC RES_FORALL_CONV THEN word_INDUCT_TAC THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[IN_PWORDLEN,FORALLBITS_DEF,BIT_DEF]
    THEN MAP_EVERY SPEC_TAC [((--`n:num`--),(--`n:num`--)),
                             ((--`l:'a list`--),(--`l:'a list`--))]
    THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[LENGTH,ALL_EL]
    THEN DISCH_THEN (SUBST1_TAC o SYM) THENL[
      REWRITE_TAC[NOT_LESS_0],
      GEN_TAC THEN EQ_TAC THEN PURE_ONCE_REWRITE_TAC[LESS_THM] THENL[
        STRIP_TAC THEN GEN_TAC
        THEN DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL[
          ASM_REWRITE_TAC[ELL_LENGTH_CONS],
          IMP_RES_THEN (fn t => REWRITE_TAC[t]) ELL_CONS
          THEN FIRST_ASSUM (SUBST_ALL_TAC o SPEC_ALL o (REWRITE_RULE[]) o
            (SPEC(--`LENGTH (l:'a list)`--))) THEN RES_TAC],
      DISCH_TAC THEN CONJ_TAC THEN POP_ASSUM MP_TAC
      THEN (PURE_ONCE_REWRITE_TAC [EQ_SYM_EQ])
      THEN FIRST_ASSUM (SUBST_ALL_TAC o SPEC_ALL o (REWRITE_RULE[]) o
            (SPEC(--`LENGTH (l:'a list)`--))) THENL[
        CONV_TAC LEFT_IMP_FORALL_CONV
        THEN EXISTS_TAC(--`LENGTH (l:'a list)`--)
        THEN REWRITE_TAC[LESS_REFL,ELL_LENGTH_CONS],
        REPEAT STRIP_TAC THEN RES_THEN MP_TAC
        THEN IMP_RES_THEN (fn t => REWRITE_TAC[t]) ELL_CONS]]]);


val FORALLBITS_WSEG = store_thm("FORALLBITS_WSEG",
    (--`!n. !w:('a)word::PWORDLEN n. !P.
     FORALLBITS P w ==>
     !m k. (m + k) <= n ==> FORALLBITS P (WSEG m k w)`--),
    GEN_TAC THEN CONV_TAC RES_FORALL_CONV THEN word_INDUCT_TAC
    THEN REWRITE_TAC[WSEG_DEF,IN_PWORDLEN,FORALLBITS_DEF]
    THEN GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM)
    THEN SPEC_TAC((--`l:'a list`--),(--`l:'a list`--))
    THEN SNOC_INDUCT_TAC THENL[
     REWRITE_TAC[LENGTH,ALL_EL] THEN REPEAT STRIP_TAC
     THEN IMP_RES_THEN  (SUBST_TAC o CONJUNCTS o
         (PURE_ONCE_REWRITE_RULE[ADD_EQ_0])) LESS_EQ_0_EQ
     THEN REWRITE_TAC[LASTN,BUTLASTN,ALL_EL],
     REWRITE_TAC[LENGTH_SNOC,ALL_EL_SNOC]
     THEN REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL[
      REWRITE_TAC[LASTN,ALL_EL],
      INDUCT_TAC THENL[
       REWRITE_TAC[BUTLASTN,ADD_CLAUSES,LASTN,ALL_EL_SNOC,LESS_EQ_MONO]
       THEN DISCH_TAC THEN IMP_RES_TAC ALL_EL_LASTN
       THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC,
       REWRITE_TAC[BUTLASTN,LESS_EQ_MONO,GEN_ALL(el 4(CONJUNCTS ADD_CLAUSES))]
       THEN REWRITE_TAC[GEN_ALL(el 4 (CONJUNCTS ADD_CLAUSES)),LESS_EQ_MONO]
       THEN DISCH_TAC THEN RES_TAC]]]);

val FORALLBITS_WCAT = store_thm("FORALLBITS_WCAT",
    (--`!w1 w2:('a)word.  !P.
     FORALLBITS P (WCAT(w1,w2)) = (FORALLBITS P w1 /\ FORALLBITS P w2)`--),
    REPEAT (word_INDUCT_TAC THEN GEN_TAC) THEN GEN_TAC
    THEN REWRITE_TAC[FORALLBITS_DEF,WCAT_DEF,ALL_EL_APPEND]);

(*---------------------------------------------------------------*)
(* EXISTSABIT : ('a -> bool) -> ('a)word -> bool                 *)
(*---------------------------------------------------------------*)

val EXISTSABIT_DEF = new_recursive_definition
{
 rec_axiom = word_Ax,
 name = "EXISTSABIT_DEF",
 def =   (--`!P:'a->bool. !l.
     EXISTSABIT P (WORD l) = SOME_EL P l`--)
};

val NOT_EXISTSABIT = store_thm("NOT_EXISTSABIT",
    (--`!P:'a->bool. !w:('a)word.
     ~(EXISTSABIT P w) = (FORALLBITS ($~ o P) w)`--),
    GEN_TAC THEN word_INDUCT_TAC
    THEN REWRITE_TAC[EXISTSABIT_DEF,FORALLBITS_DEF,NOT_SOME_EL_ALL_EL]);

val NOT_FORALLBITS = store_thm("NOT_FORALLBITS",
    (--`!P:'a->bool. !w:('a)word.
     ~(FORALLBITS P w) = (EXISTSABIT ($~ o P) w)`--),
    GEN_TAC THEN word_INDUCT_TAC
    THEN REWRITE_TAC[EXISTSABIT_DEF,FORALLBITS_DEF,NOT_ALL_EL_SOME_EL]);


val EXISTSABIT_BIT = store_thm("EXISTSABIT",
    (--`!n. !w:('a)word::PWORDLEN n. !P.
     EXISTSABIT P w = ?k. k < n /\ P(BIT k w)`--),
    GEN_TAC THEN CONV_TAC RES_FORALL_CONV THEN word_INDUCT_TAC THEN GEN_TAC
    THEN PURE_ONCE_REWRITE_TAC[IN_PWORDLEN,EXISTSABIT_DEF,BIT_DEF]
    THEN DISCH_THEN (SUBST1_TAC o SYM)
    THEN MAP_EVERY SPEC_TAC
         [((--`n:num`--),(--`n:num`--)),((--`l:'a list`--),(--`l:'a list`--))]
    THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC
    THEN REWRITE_TAC[LENGTH,SOME_EL,NOT_LESS_0]
    THEN PURE_ONCE_REWRITE_TAC[LESS_THM] THEN EQ_TAC THENL[
       STRIP_TAC THENL[
      EXISTS_TAC (--`LENGTH(l:'a list)`--)
      THEN ASM_REWRITE_TAC[ELL_LENGTH_CONS],
        RES_TAC THEN EXISTS_TAC (--`k:num`--)
        THEN COND_REWRITE1_TAC ELL_CONS THEN ASM_REWRITE_TAC[]],
      PURE_ONCE_REWRITE_TAC[RIGHT_AND_OVER_OR]
      THEN DISCH_THEN (STRIP_THM_THEN
        (DISJ_CASES_THEN2 STRIP_ASSUME_TAC MP_TAC)) THENL[
        FIRST_ASSUM SUBST_ALL_TAC
        THEN RULE_ASSUM_TAC (REWRITE_RULE[ELL_LENGTH_CONS])
        THEN DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC,
        DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)
        THEN COND_REWRITE1_TAC ELL_CONS THEN DISCH_TAC THEN RES_TAC
        THEN DISJ2_TAC THEN FIRST_ASSUM ACCEPT_TAC]]);

val EXISTSABIT_WSEG = store_thm("EXISTSABIT_WSEG",
    (--`!n. !w:('a)word::PWORDLEN n. !m k. ((m + k) <= n) ==>
     !P. (EXISTSABIT P (WSEG m k w)) ==> (EXISTSABIT P w)`--),
  let val lem1 = ARITH_PROVE
         (--`!l m k. (m+k)<=l ==>((m + (l - (m + k))) = (l - k))`--)
  in
     GEN_TAC THEN CONV_TAC RES_FORALL_CONV THEN word_INDUCT_TAC
     THEN REWRITE_TAC[EXISTSABIT_DEF,IN_PWORDLEN,WSEG_DEF]
     THEN GEN_TAC THEN DISCH_THEN (SUBST1_TAC o SYM)
     THEN REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC
     THEN COND_REWRITE1_TAC LASTN_BUTLASTN_SEG
     THEN MATCH_MP_TAC (SPECL
        [(--`m:num`--),(--`(LENGTH (l:'a list)) - (m + k)`--),
         (--`l:'a list`--)] SOME_EL_SEG)
     THEN IMP_RES_THEN SUBST1_TAC lem1
     THEN MATCH_ACCEPT_TAC SUB_LESS_EQ
  end);

val EXISTSABIT_WCAT = store_thm("EXISTSABIT_WCAT",
    (--`!w1 w2:('a)word.  !P.
     EXISTSABIT P (WCAT(w1,w2)) = (EXISTSABIT P w1 \/ EXISTSABIT P w2)`--),
    REPEAT (word_INDUCT_TAC THEN GEN_TAC) THEN GEN_TAC
    THEN REWRITE_TAC[EXISTSABIT_DEF,WCAT_DEF,SOME_EL_APPEND]);

(*---------------------------------------------------------------*)
(* Shift and rotation                                                   *)
(*---------------------------------------------------------------*)

val SHR_DEF = new_definition("SHR_DEF",
    (--`SHR f b (w:('a)word) =
      (WCAT((if f then (WSEG 1 (PRE(WORDLEN w)) w) else WORD[b]),
            (WSEG (PRE(WORDLEN w)) 1 w)), (BIT 0 w))`--));

val SHL_DEF = new_definition("SHL_DEF",
    (--`SHL f (w:('a)word) b =
     (BIT (PRE(WORDLEN w)) w,
     WCAT((WSEG (PRE(WORDLEN w)) 0 w),(if f then (WSEG 1 0 w) else WORD[b])))`--));

val SHR_WSEG = store_thm("SHR_WSEG",
    (--`!n. !w:('a)word::PWORDLEN n. ! m k. ((m + k) <= n) ==> (0 < m) ==>
     (!f b. SHR f b (WSEG m k w) =
      ((if f then (WCAT((WSEG 1 (k+(m-1)) w),(WSEG (m-1)(k+1)w))) else
            (WCAT( (WORD[b]),       (WSEG (m-1)(k+1)w)))), (BIT k w)))`--),

 let val lem1 = ARITH_PROVE (--`0 < m ==> (((m-1)+1) <= m)`--)
 in
    GEN_TAC THEN RESQ_GEN_TAC THEN PURE_REWRITE_TAC[SHR_DEF]
    THEN REPEAT STRIP_TAC
    THEN PURE_ONCE_REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL[
      BOOL_CASES_TAC (--`f:bool`--) THEN PURE_ONCE_REWRITE_TAC[COND_CLAUSES]
    THEN RESQ_IMP_RES_THEN (IMP_RES_THEN SUBST1_TAC) WSEG_WORDLEN
      THEN AP_TERM_TAC THEN PURE_ONCE_REWRITE_TAC[PAIR_EQ]
      THEN PURE_ONCE_REWRITE_TAC[PRE_SUB1] THEN CONJ_TAC THEN TRY REFL_TAC
      THEN MATCH_MP_TAC (RESQ_SPEC(--`w:'a word`--)(SPEC(--`n:num`--) WSEG_WSEG))
      THEN IMP_RES_TAC lem1 THEN ASM_REWRITE_TAC[]
      THEN PURE_ONCE_REWRITE_TAC[ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC,
      RESQ_IMP_RES_TAC BIT_WSEG THEN RES_TAC THEN ASM_REWRITE_TAC[ADD]]
 end);


(* |- !n. !w :: PWORDLEN n.
     !b m k. (m + k) <= n ==> 0 < m ==>
      (SHR F b(WSEG m k w) = WCAT(WORD[b],WSEG(m - 1)(k + 1)w),BIT k w) *)
val SHR_WSEG_1F = save_thm("SHR_WSEG_1F",
    let val th1 = RESQ_SPECL [``n : num``, ``w : 'a word``, ``m : num``, ``k : num``] SHR_WSEG
    val (P,v) = dest_comb(hd(hyp th1))
    val ante = fst(strip_imp(concl th1))
    val th2 = SPEC ``b : 'a`` (CONV_RULE(ONCE_DEPTH_CONV COND_CONV)
        (SPEC (--`F`--) (UNDISCH_ALL th1)))
    in
    GEN_ALL
    (CONV_RULE (HO_REWR_CONV (GSYM RES_FORALL))
     (GEN ``w : 'a word``
      (DISCH_ALL (GENL[``b : 'a``, ``m:num``, ``k:num``]
                  (itlist DISCH ante th2)))))
    end);

val SHR_WSEG_NF_lem1 =  ARITH_PROVE (--`0<m ==>((m-1)+1 = m)`--);

val SHR_WSEG_NF_lem2 =  ARITH_PROVE (--`0 < m ==>( (m-1) + (k+1) = m+k)`--);

open SingleStep
infix 8 by
val SHR_WSEG_NF = store_thm("SHR_WSEG_NF",
    (--`!n. !w :('a)word :: PWORDLEN n.
     !m k. (m + k) < n ==> 0 < m ==>
      (SHR F(BIT(m + k)w)(WSEG m k w) = (WSEG m (k + 1)w, BIT k w))`--),

    REPEAT GGEN_TAC THEN REPEAT DISCH_TAC
    THEN RESQ_IMP_RES_TAC SHR_WSEG THEN POP_ASSUM
      (ASSUME_TAC o (CONV_RULE (TOP_DEPTH_CONV RIGHT_IMP_FORALL_CONV)))
    THEN FIRST_ASSUM COND_REWRITE1_TAC THENL[
      IMP_RES_TAC LESS_IMP_LESS_OR_EQ,
      CONV_TAC (ONCE_DEPTH_CONV COND_CONV)
      THEN PURE_ONCE_REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL[
        RESQ_IMP_RES_THEN COND_REWRITE1_TAC
          (CONV_RULE (ONCE_DEPTH_CONV SYM_CONV)WSEG_BIT)
        THEN RESQ_IMP_RES_TAC WCAT_WSEG_WSEG
        THEN `WCAT (WSEG 1 (m - 1 + (k + 1)) w, WSEG (m - 1) (k + 1) w) =
              WSEG (m - 1 + 1) (k + 1) w` by
                   simpLib.ASM_SIMP_TAC bossLib.arith_ss []
        THEN POP_ASSUM MP_TAC THEN MP_TAC (Q.ASSUME`0<m`)
        THEN simpLib.SIMP_TAC bossLib.arith_ss [],
        REFL_TAC]]);

val SHL_WSEG = store_thm("SHL_WSEG",
    (--`!n. !w:('a)word::PWORDLEN n. ! m k. ((m + k) <= n) ==> (0 < m) ==>
     (!f b. SHL f (WSEG m k w) b = ((BIT (k+(m-1)) w),
      (if f then (WCAT((WSEG (m-1) k w),(WSEG 1 k w))) else
            (WCAT((WSEG (m-1) k w),(WORD[b]))))))`--),
    let fun f t1 tms =
        ((IMP_RES_THEN SUBST1_TAC) o (fn th => MATCH_MP th t1)
          o (PURE_ONCE_REWRITE_RULE[ADD_CLAUSES]) o (SPECL tms))
    in
    REPEAT GGEN_TAC THEN PURE_REWRITE_TAC[SHL_DEF] THEN REPEAT DISCH_TAC
    THEN REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[PAIR_EQ]
    THEN CONJ_TAC THENL[
      RESQ_IMP_RES_THEN (IMP_RES_THEN SUBST1_TAC) WSEG_WORDLEN
      THEN RESQ_IMP_RES_THEN (IMP_RES_THEN COND_REWRITE1_TAC) BIT_WSEG
      THENL[
        IMP_RES_TAC PRE_LESS_REFL,

        CONV_TAC ((RAND_CONV o RATOR_CONV o RAND_CONV) (REWR_CONV ADD_SYM))
        THEN PURE_ONCE_REWRITE_TAC[PRE_SUB1]
        THEN REFL_TAC
           ],
      BOOL_CASES_TAC (--`f:bool`--) THEN CONV_TAC (ONCE_DEPTH_CONV COND_CONV)
      THEN AP_TERM_TAC THEN PURE_ONCE_REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC
      THEN TRY REFL_TAC THENL[
        RESQ_IMP_RES_THEN (IMP_RES_THEN SUBST1_TAC) WSEG_WORDLEN
        THEN PURE_ONCE_REWRITE_TAC[PRE_SUB1]
        THEN RESQ_REWRITE1_TAC WSEG_WSEG THENL[
          ARITH_TAC,
          REWRITE_TAC[ADD_0]],
        RESQ_REWRITE1_TAC WSEG_WSEG THENL[
          ARITH_TAC,
          REWRITE_TAC[ADD_0]],

        RESQ_IMP_RES_THEN (IMP_RES_THEN SUBST1_TAC) WSEG_WORDLEN
        THEN PURE_ONCE_REWRITE_TAC[PRE_SUB1]
        THEN RESQ_REWRITE1_TAC WSEG_WSEG THENL[
          ARITH_TAC,
          REWRITE_TAC[ADD_0]]]]
   end);

(* |- !n. !w :: PWORDLEN n.
     !m k. (m + k) <= n ==> 0 < m ==>
      (!b. SHL F(WSEG m k w)b = BIT(k + (m - 1))w,WCAT(WSEG(m - 1)k w,WORD[b])) *)
val SHL_WSEG_1F = save_thm("SHL_WSEG_1F",
    let val th1 = RESQ_SPECL [``n : num``, ``w : 'a word``, ``m : num``, ``k : num``] SHL_WSEG
    val (P,v) = dest_comb(hd(hyp th1))
    val ante = fst(strip_imp(concl th1))
    val th2 = SPEC ``b : 'a`` (CONV_RULE(ONCE_DEPTH_CONV COND_CONV)
        (SPEC (--`F`--) (UNDISCH_ALL th1)))
    in
    GEN_ALL
    (CONV_RULE (HO_REWR_CONV (GSYM RES_FORALL))
     (GEN ``w : 'a word``
      (DISCH_ALL
       (GENL[``b : 'a``, (--`m:num`--),(--`k:num`--)]
        (itlist DISCH ante th2)))))
    end);


val SHL_WSEG_NF = store_thm("SHL_WSEG_NF",
    (--`!n. !w :('a)word :: PWORDLEN n.
     !m k. (m + k) <= n ==> 0 < m ==> (0 < k) ==>
      (SHL F (WSEG m k w)(BIT(k - 1)w) =
               (BIT (k + (m - 1)) w, WSEG m (k - 1)w))`--),
    REPEAT GGEN_TAC THEN REPEAT DISCH_TAC THEN RESQ_REWRITE1_TAC SHL_WSEG
    THEN REWRITE_TAC[PAIR_EQ]
    THEN RESQ_REWRITE1_TAC (GSYM WSEG_BIT) THENL[
      ARITH_TAC,
      RESQ_IMP_RES_THEN ASSUME_TAC WCAT_WSEG_WSEG
      THEN POP_ASSUM (fn th =>
                         `WCAT (WSEG (m - 1) (1 + (k - 1)) w,
                                WSEG 1 (k - 1) w) =
                          WSEG (1 + (m - 1)) (k - 1) w` by
                      simpLib.ASM_SIMP_TAC bossLib.arith_ss [th])
      THEN POP_ASSUM MP_TAC
      THEN simpLib.ASM_SIMP_TAC bossLib.arith_ss []
    ]);

val WSEG_SHL = store_thm("WSEG_SHL",
    (--`!n. !w:'a word :: PWORDLEN (SUC n). !m k.
     0 < k /\ (m + k) <= (SUC n) ==>
     (!b. WSEG m k (SND (SHL f w b)) = WSEG m (k - 1) w)`--),
    REPEAT GGEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SHL_DEF]
    THEN FIRST_ASSUM (SUBST1_TAC o (MATCH_EQ_MP PWORDLEN))
    THEN REPEAT STRIP_TAC THEN PURE_ONCE_REWRITE_TAC[PRE]
    THEN RESQ_REWRITE1_TAC (SPECL[(--`n:num`--), (--`1`--)] WSEG_WCAT_WSEG1) THENL[
      RESQ_IMP_RES_THEN MATCH_MP_TAC WSEG_PWORDLEN
      THEN REWRITE_TAC[ADD_0,LESS_EQ_SUC_REFL],
      COND_CASES_TAC THENL[
        RESQ_IMP_RES_THEN MATCH_MP_TAC WSEG_PWORDLEN
        THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
        THEN REWRITE_TAC[ADD,LESS_EQ_MONO,ZERO_LESS_EQ],
        MATCH_ACCEPT_TAC PWORDLEN1],
      ARITH_TAC,
      CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN IMP_RES_TAC LESS_OR,
      RESQ_REWRITE1_TAC WSEG_WSEG THENL[
       REWRITE_TAC[ADD_0,LESS_EQ_SUC_REFL],
       ARITH_TAC,
       REWRITE_TAC[ADD]]]);

val WSEG_SHL_0 = store_thm("WSEG_SHL_0",
    (--`!n. !w:'a word :: PWORDLEN (SUC n). !m b.
     0 < m /\ m <= (SUC n) ==>
     (WSEG m 0 (SND (SHL f w b)) =
     WCAT((WSEG (m - 1) 0 w), (if f then WSEG 1 0 w else WORD[b])))`--),

REPEAT GGEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[SHL_DEF]
    THEN FIRST_ASSUM (SUBST1_TAC o (MATCH_EQ_MP PWORDLEN))
    THEN PURE_ONCE_REWRITE_TAC[PRE]
    THEN RESQ_REWRITE1_TAC (SPECL[(--`n:num`--), (--`1`--)] WSEG_WCAT_WSEG) THENL[
     RESQ_IMP_RES_THEN MATCH_MP_TAC WSEG_PWORDLEN
     THEN REWRITE_TAC[ADD_0,LESS_EQ_SUC_REFL],
     COND_CASES_TAC THENL[
      RESQ_IMP_RES_THEN MATCH_MP_TAC WSEG_PWORDLEN
      THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
      THEN REWRITE_TAC[(GSYM ADD1),ADD_0,LESS_EQ_MONO,ZERO_LESS_EQ],
      MATCH_ACCEPT_TAC PWORDLEN1],
     ASM_REWRITE_TAC[GSYM ADD1,ADD_0],
     CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0,
     CONV_TAC (ONCE_DEPTH_CONV num_CONV)
     THEN ASM_REWRITE_TAC[ADD_0,GSYM LESS_EQ],
     PURE_ONCE_REWRITE_TAC[ADD_0,SUB_0]
     THEN AP_TERM_TAC THEN PURE_ONCE_REWRITE_TAC[PAIR_EQ] THEN CONJ_TAC THENL[
      RESQ_REWRITE1_TAC WSEG_WSEG THEN REWRITE_TAC[ADD_0,LESS_EQ_SUC_REFL]
      THEN ARITH_TAC,
      BOOL_CASES_TAC (--`f:bool`--) THEN REWRITE_TAC[] THENL[
       RESQ_REWRITE1_TAC WSEG_WSEG THEN REWRITE_TAC[ADD_0,LESS_EQ_SUC_REFL]
       THEN ARITH_TAC,
       RESQ_REWRITE1_TAC WSEG_WORD_LENGTH THEN TRY REFL_TAC
       THEN MATCH_ACCEPT_TAC PWORDLEN1]]]);

val _ = export_theory();

val _ = export_doc_theorems();
