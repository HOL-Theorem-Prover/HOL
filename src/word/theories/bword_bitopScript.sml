(* ===================================================================== *)
(* FILE: mk_bword_bitop.ml	    DATE: 14 Aug 1992			*)
(* AUTHOR: Wai WONG  	    	    					*)
(* TRANSLATOR: Paul Curzon  1 June 1993, September 1994			*)
(* Writes: bword_bitop.th	    	    				*)
(* Uses: Libraries: more_lists res_quan					*)
(* Description: Creates a theorey for boolean word bitwise operations	*)
(* ===================================================================== *)
(* PC 18/11/93: SEG ->WSEG *)

open HolKernel Parse basicHol90Lib Let_conv Num_conv Num_induct;
open ConstrProofs Define_type Base;
open arithLib numLib res_quanLib;
open rich_listTheory pairTheory arithmeticTheory prim_recTheory numTheory;
infix THEN THENL THENC ORELSE ORELSEC;
open Cond_rewrite Res_quan word_baseTheory word_bitopTheory;

val _ = new_theory "bword_bitop";

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
    (CONV_TAC RESQ_FORALL_CONV THEN word_INDUCT_TAC
     THEN PURE_ONCE_REWRITE_TAC[word_baseTheory.PWORDLEN_DEF]
     THEN GEN_TAC THEN DISCH_TAC);


(* --------------------------------------------------------------------- *)
(* We begin with some lemmas about lists. They are used in the proofs.	*)
(* --------------------------------------------------------------------- *)

val MAP2_SNOC = prove(
    (--`!(f:'a->'b->'c) h1 h2 l1 l2. (LENGTH l1 = LENGTH l2) ==>
     (MAP2 f(SNOC h1 l1)(SNOC h2 l2) = SNOC(f h1 h2)(MAP2 f l1 l2))`--),
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN EQ_LENGTH_INDUCT_TAC THENL[
      REWRITE_TAC[SNOC,MAP2],
      REWRITE_TAC[LENGTH,INV_SUC_EQ,SNOC,MAP2,CONS_11]
      THEN REPEAT STRIP_TAC THEN RES_TAC]);

val BUTLASTN_MAP2 = prove(
    (--`!l1 l2. (LENGTH l1 = LENGTH l2) ==> !n. (n <= LENGTH l1) ==>
     !(f:'a->'b->'c).
      BUTLASTN n (MAP2 f l1 l2) = MAP2 f (BUTLASTN n l1) (BUTLASTN n l2)`--),
    let val lem1 = ARITH_PROVE (--`!n. n <= 0 ==> (n = 0)`--)
    in
    EQ_LENGTH_SNOC_INDUCT_TAC THENL[
      PURE_ONCE_REWRITE_TAC[LENGTH] THEN GEN_TAC
      THEN DISCH_THEN (SUBST1_TAC o (MATCH_MP lem1))
      THEN REWRITE_TAC[BUTLASTN,MAP2],
      INDUCT_TAC THEN REWRITE_TAC[BUTLASTN,MAP2_SNOC,LESS_EQ_MONO]
      THEN IMP_RES_THEN (fn t => PURE_REWRITE_TAC[t]) MAP2_SNOC
      THEN REWRITE_TAC[BUTLASTN] THEN DISCH_TAC THEN RES_TAC]
    end);

val LASTN_MAP2 = prove(
    (--`!l1 l2. (LENGTH l1 = LENGTH l2) ==> !n. (n <= LENGTH l1) ==>
     !(f:'a->'b->'c).
      LASTN n (MAP2 f l1 l2) = MAP2 f (LASTN n l1) (LASTN n l2)`--),
    let val lem1 = ARITH_PROVE (--`!n. n <= 0 ==> (n = 0)`--) in
    EQ_LENGTH_SNOC_INDUCT_TAC THENL[
      GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LENGTH]
      THEN DISCH_THEN (SUBST1_TAC o (MATCH_MP lem1))
      THEN REWRITE_TAC[LASTN,MAP2],
      INDUCT_TAC THEN REWRITE_TAC[LASTN,MAP2,LESS_EQ_MONO]
      THEN REPEAT STRIP_TAC THEN COND_REWRITE1_TAC MAP2_SNOC THENL[
    	COND_REWRITE1_TAC LENGTH_LASTN THEN TRY REFL_TAC
    	THEN FIRST_ASSUM (SUBST1_TAC o SYM)
    	THEN FIRST_ASSUM ACCEPT_TAC,
    	REWRITE_TAC[LASTN,SNOC_11] THEN RES_TAC
    	THEN FIRST_ASSUM MATCH_ACCEPT_TAC]]
    end);


(* --------------------------------------------------------------------- *)
(* WNOT	    	    	    	    					*)
(* --------------------------------------------------------------------- *)


val WNOT_DEF = new_recursive_definition {
 name = "WNOT_DEF",
 fixity = Prefix,
 rec_axiom = word_Ax,
 def =
 --`
   WNOT (WORD l) = WORD((MAP $~) l)
 `--
 };

val BIT_WNOT_SYM_lemma = TAC_PROOF(([],
     (--`!n. !w:(bool)word ::PWORDLEN n. PWORDLEN n (WNOT w) /\
      !m k. ((m + k) <= n) ==> (WNOT(WSEG m k w) = WSEG m k (WNOT w))`--)),
    GEN_TAC THEN RESQ_WORDLEN_TAC THEN PURE_ASM_REWRITE_TAC
    	[PWORDLEN_DEF,WNOT_DEF,WSEG_DEF,LENGTH_MAP,WORD_11]
    THEN CONJ_TAC THENL[
      REFL_TAC,
      REPEAT GEN_TAC THEN DISCH_TAC
      THEN FIRST_ASSUM (ASSUME_TAC o CONJUNCT2 o (MATCH_MP LESS_EQ_SPLIT))
      THEN COND_REWRITE1_TAC BUTLASTN_MAP THENL[
    	IMP_RES_TAC LESS_EQ_SPLIT,
        COND_REWRITE1_TAC LASTN_MAP THENL[
          COND_REWRITE1_TAC LENGTH_BUTLASTN
          THEN COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB)
          THEN FIRST_ASSUM ACCEPT_TAC,
    	  REFL_TAC]]]);


(* PBITOP_WNOT = |- PBITOP WNOT *)

val PBITOP_WNOT = save_thm("PBITOP_WNOT",
    EQT_ELIM (TRANS (ISPEC (--`WNOT`--) PBITOP_DEF)
     (EQT_INTRO BIT_WNOT_SYM_lemma)));

val WNOT_WNOT = store_thm("WNOT_WNOT",
    (--`!w. WNOT(WNOT w) = w`--),
    word_INDUCT_TAC THEN PURE_REWRITE_TAC[WNOT_DEF]
    THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP,WORD_11,CONS_11]
    THEN POP_ASSUM (ACCEPT_TAC o (REWRITE_RULE[WORD_11])));

val WCAT_WNOT = store_thm("WCAT_WNOT",
    (--`!n1 n2 . !w1:(bool)word::PWORDLEN n1. !w2:(bool)word::PWORDLEN n2.
     WCAT ((WNOT w1), (WNOT w2)) =  (WNOT (WCAT (w1,w2)))`--),
    REPEAT GEN_TAC THEN REPEAT RESQ_GEN_TAC
    THEN MAP_EVERY word_CASES_TAC [(--`w1:(bool)word`--), (--`w2:(bool)word`--)]
    THEN REWRITE_TAC[WCAT_DEF,WNOT_DEF,MAP_APPEND]);

val LENGTH_MAP22 = GEN_ALL (DISCH_ALL (CONJUNCT2 (SPEC_ALL (UNDISCH_ALL
    (SPEC_ALL LENGTH_MAP2)))));

(* --------------------------------------------------------------------- *)
(* WAND	    	    	    	    					*)
(* --------------------------------------------------------------------- *)
(* WAND_DEF = |- !l1 l2. WAND(WORD l1)(WORD l2) = WORD(MAP2 $/\ l1 l2) *)

val WAND_DEF = new_specification
 {name="WAND_DEF",
  consts= [{fixity= Infixr 400,const_name="WAND"}],
  sat_thm = (ISPEC (--`$/\`--) PBITBOP_EXISTS)
};

val PBITBOP_WAND_lemma = prove(
    (--`!n. !w1:(bool)word ::PWORDLEN n. !w2:(bool)word ::PWORDLEN n.
     (PWORDLEN n (w1 WAND w2)) /\
     !m k. ((m + k) <= n) ==>
     ((WSEG m k w1) WAND (WSEG m k w2) = WSEG m k (w1 WAND w2))`--),
    GEN_TAC THEN REPEAT RESQ_WORDLEN_TAC
    THEN PURE_ASM_REWRITE_TAC[PWORDLEN_DEF,WAND_DEF,WORD_11,WSEG_DEF]
    THEN CONJ_TAC THENL[
     POP_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC (GSYM LENGTH_MAP22)
     THEN FIRST_ASSUM ACCEPT_TAC,
     POP_ASSUM (fn t => RULE_ASSUM_TAC (TRANS (SYM t)))
     THEN REPEAT STRIP_TAC THEN COND_REWRITE1_TAC BUTLASTN_MAP2 THENL[
      FIRST_ASSUM (ACCEPT_TAC o SYM),
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN IMP_RES_TAC LESS_EQ_SPLIT,
      COND_REWRITE1_TAC LASTN_MAP2 THENL[
       COND_REWRITE1_TAC LENGTH_BUTLASTN THENL[
        FIRST_ASSUM (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC,
        FIRST_ASSUM SUBST1_TAC THEN REFL_TAC],
       COND_REWRITE1_TAC LENGTH_BUTLASTN
       THEN COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB)
       THEN FIRST_ASSUM SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC,
       REFL_TAC]]]);

val PBITBOP_WAND = save_thm("PBITBOP_WAND",
    EQT_ELIM (TRANS (ISPEC (--`$WAND`--) PBITBOP_DEF)
     (EQT_INTRO PBITBOP_WAND_lemma)));

(* --------------------------------------------------------------------- *)
(* WOR	    	    	    	    					*)
(* --------------------------------------------------------------------- *)
(* WOR_DEF = |- !l1 l2. WOR(WORD l1)(WORD l2) = WORD(MAP2 $\/ l1 l2)   *)

val WOR_DEF = new_specification
 {name="WOR_DEF",
  consts= [{fixity= Infixr 300,const_name="WOR"}],
  sat_thm = (ISPEC (--`$\/`--) PBITBOP_EXISTS)
};

val PBITBOP_WOR_lemma = prove(
    (--`!n. !w1:(bool)word ::PWORDLEN n. !w2:(bool)word ::PWORDLEN n.
     (PWORDLEN n (w1 WOR w2)) /\
     !m k. ((m + k) <= n) ==>
     ((WSEG m k w1) WOR  (WSEG m k w2) = WSEG m k (w1 WOR w2))`--),
    GEN_TAC THEN REPEAT RESQ_WORDLEN_TAC
    THEN PURE_ASM_REWRITE_TAC[PWORDLEN_DEF,WOR_DEF,WORD_11,WSEG_DEF]
    THEN CONJ_TAC THENL[
     POP_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC (GSYM LENGTH_MAP22)
     THEN FIRST_ASSUM ACCEPT_TAC,
     POP_ASSUM (fn t => RULE_ASSUM_TAC (TRANS (SYM t)))
     THEN REPEAT STRIP_TAC THEN COND_REWRITE1_TAC BUTLASTN_MAP2 THENL[
      FIRST_ASSUM (ACCEPT_TAC o SYM),
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN IMP_RES_TAC LESS_EQ_SPLIT,
      COND_REWRITE1_TAC LASTN_MAP2 THENL[
       COND_REWRITE1_TAC LENGTH_BUTLASTN THENL[
        FIRST_ASSUM (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC,
        FIRST_ASSUM SUBST1_TAC THEN REFL_TAC],
       COND_REWRITE1_TAC LENGTH_BUTLASTN
       THEN COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB)
       THEN FIRST_ASSUM SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC,
       REFL_TAC]]]);

val PBITBOP_WOR = save_thm("PBITBOP_WOR",
    EQT_ELIM (TRANS (ISPEC (--`$WOR`--) PBITBOP_DEF)
     (EQT_INTRO PBITBOP_WOR_lemma)));

(* --------------------------------------------------------------------- *)
(* WXOR	    	    	    	    					*)
(* --------------------------------------------------------------------- *)
(* |- !l1 l2. WXOR(WORD l1)(WORD l2) = WORD(MAP2(\x y. ~(x = y))l1 l2) *)

val WXOR_DEF = new_specification
 {name="WXOR_DEF",
  consts= [{fixity= Infixr 300,const_name="WXOR"}],
  sat_thm = (ISPEC (--`(\x y:bool. ~(x = y))`--) PBITBOP_EXISTS)
};

val PBITBOP_WXOR_lemma = prove(
    (--`!n. !w1:(bool)word ::PWORDLEN n. !w2:(bool)word ::PWORDLEN n.
     (PWORDLEN n (w1 WXOR w2)) /\
     !m k. ((m + k) <= n) ==>
     ((WSEG m k w1) WXOR (WSEG m k w2) = WSEG m k (w1 WXOR w2))`--),
    GEN_TAC THEN REPEAT RESQ_WORDLEN_TAC
    THEN PURE_ASM_REWRITE_TAC[PWORDLEN_DEF,WXOR_DEF,WORD_11,WSEG_DEF]
    THEN CONJ_TAC THEN POP_ASSUM SUBST_ALL_TAC THENL[
     MATCH_MP_TAC (GSYM LENGTH_MAP22) THEN FIRST_ASSUM ACCEPT_TAC,
     REPEAT STRIP_TAC THEN COND_REWRITE1_TAC BUTLASTN_MAP2 THENL[
      FIRST_ASSUM (ACCEPT_TAC o SYM),
      FIRST_ASSUM (SUBST1_TAC o SYM) THEN IMP_RES_TAC LESS_EQ_SPLIT,
      COND_REWRITE1_TAC LASTN_MAP2 THENL[
       COND_REWRITE1_TAC LENGTH_BUTLASTN THENL[
        FIRST_ASSUM (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC,
        FIRST_ASSUM SUBST1_TAC THEN REFL_TAC],
       COND_REWRITE1_TAC LENGTH_BUTLASTN THENL[
        COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB)
        THEN FIRST_ASSUM SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC],
       REFL_TAC]]]);

val PBITBOP_WXOR = save_thm("PBITBOP_WXOR",
    EQT_ELIM (TRANS (ISPEC (--`$WXOR`--) PBITBOP_DEF)
     (EQT_INTRO PBITBOP_WXOR_lemma)));

val _ = export_theory();

val _ = export_doc_theorems();
