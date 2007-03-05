(* ===================================================== *)
(* FILE: mk_bword_num.ml            DATE: 14 Aug 1992    *)
(* AUTHOR: Wai WONG                                      *)
(* TRANSLATOR: Paul Curzon  2 June 1993, Sept 1994       *)
(* UPDATED for new res_quan theories by Joe Hurd, 2001   *)
(* Writes: bword_base.th                                 *)
(* Uses: Libraries: more_lists res_quan                  *)
(* Description: Creates a theorey for mapping between    *)
(* natural numbers and boolean words                     *)
(* ===================================================== *)


open HolKernel Parse boolLib Prim_rec numLib res_quanLib;
open rich_listTheory pairTheory arithmeticTheory prim_recTheory numTheory;
open Cond_rewrite word_baseTheory word_bitopTheory word_numTheory;
open Base;
open res_quanTheory bossLib pred_setTheory;

val _ = new_theory "bword_num";

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



(*---------------------------------------------------------------*)
(* Mapping between (bool)word and num                            *)
(*---------------------------------------------------------------*)

val BV_DEF = new_definition("BV_DEF",
    (--`BV b = (if b then SUC 0 else 0)`--));

(* BNVAL w converts the boolean word w to a num *)

val BNVAL_DEF = new_recursive_definition {
 name = "BNVAL_DEF",
 rec_axiom = word_Ax,
 def =
 --`
   BNVAL (WORD l) = LVAL BV 2 l
 `--
 };

val BV_LESS_2 = store_thm("BV_LESS_2", (--`!x. BV x < 2`--),
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[BV_DEF]
    THEN COND_CASES_TAC THEN CONV_TAC (REDEPTH_CONV num_CONV)
    THEN REWRITE_TAC[LESS_0,LESS_MONO_EQ]);

val BNVAL_NVAL = store_thm("BNVAL_NVAL",
    (--`!w. BNVAL w = NVAL BV 2 w`--),
    let val lem1 = REWRITE_RULE[GSYM NVAL_DEF] BNVAL_DEF
    in
    word_INDUCT_TAC THEN MATCH_ACCEPT_TAC lem1
    end);

val BNVAL0 = save_thm("BNVAL0",    (* BNVAL (WORD[]) = 0 *)
    TRANS (SPEC (--`WORD[]:bool word`--) BNVAL_NVAL)
               (ISPECL [(--`BV`--), (--`2`--)] NVAL0));

val BNVAL_11_lem = prove((--`!m n p. m < p /\ n < p ==> ~((p + m) =  n)`--),
    INDUCT_TAC THENL[
      REPEAT GEN_TAC THEN STRIP_TAC THEN PURE_ONCE_REWRITE_TAC[ADD_0]
      THEN CONV_TAC (RAND_CONV SYM_CONV) THEN IMP_RES_TAC LESS_NOT_EQ,
      INDUCT_TAC THEN GEN_TAC THEN STRIP_TAC THENL[
        PURE_ONCE_REWRITE_TAC[ADD_EQ_0]
        THEN PURE_ONCE_REWRITE_TAC[DE_MORGAN_THM]
        THEN DISJ2_TAC THEN MATCH_ACCEPT_TAC NOT_SUC,
        PURE_REWRITE_TAC[ADD_CLAUSES,INV_SUC_EQ]
        THEN IMP_RES_TAC SUC_LESS THEN RES_TAC]]);

val BNVAL_11 = store_thm("BNVAL_11",
    (--`!w1 w2:(bool)word. (WORDLEN w1 = WORDLEN w2) ==>
     (BNVAL w1 = BNVAL w2) ==> (w1 = w2)`--),
    let val lem1 = BNVAL_11_lem
    val lem2 = GEN_ALL(MATCH_MP LVAL_MAX BV_LESS_2)
    in
    word_INDUCT_TAC THEN GEN_TAC THEN word_INDUCT_TAC
    THEN REWRITE_TAC[WORDLEN_DEF,WORD_11,BNVAL_DEF]
    THEN SPEC_TAC ((--`l:(bool)list`--),(--`l:(bool)list`--))
    THEN EQ_LENGTH_INDUCT_TAC THEN REWRITE_TAC[LVAL,BV_DEF,CONS_11]
    THEN FIRST_ASSUM SUBST1_TAC THEN REPEAT COND_CASES_TAC THENL[
      PURE_ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[EQ_MONO_ADD_EQ]
      THEN DISCH_TAC THEN RES_TAC,
      PURE_REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES]
      THEN ASSUME_TAC (ISPEC (--`l':bool list`--) lem2)
      THEN ASSUME_TAC(SUBS[ASSUME(--`LENGTH(l:bool list) = LENGTH(l':bool list)`--)]
        (ISPEC (--`l:bool list`--) lem2))
      THEN IMP_RES_TAC lem1 THEN ASM_REWRITE_TAC[],
      PURE_REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES]
      THEN ASSUME_TAC (ISPEC (--`l':bool list`--) lem2)
      THEN ASSUME_TAC(SUBS[ASSUME(--`LENGTH(l:bool list) = LENGTH(l':bool list)`--)]
        (ISPEC (--`l:bool list`--) lem2))
      THEN CONV_TAC ((RATOR_CONV o RAND_CONV) SYM_CONV)
      THEN IMP_RES_TAC lem1 THEN ASM_REWRITE_TAC[],
      PURE_REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES]
      THEN RES_TAC THEN ASM_REWRITE_TAC[]]
     end);

val BNVAL_ONTO = store_thm("BNVAL_ONTO",
    (--`!w. ?n. BNVAL w = n`--),
    word_INDUCT_TAC THEN REWRITE_TAC[BNVAL_DEF]
    THEN LIST_INDUCT_TAC THENL[
      EXISTS_TAC (--`0`--),
      GEN_TAC THEN EXISTS_TAC
       (--`((BV x) * (2 EXP (LENGTH (l:bool list)))) + (LVAL BV 2 l)`--)]
    THEN REWRITE_TAC[LVAL]);

val BNVAL_MAX = store_thm("BNVAL_MAX",
    (--`!n. !w:(bool)word ::PWORDLEN n. BNVAL w < (2 EXP n)`--),
    GEN_TAC THEN RESQ_WORDLEN_TAC
    THEN PURE_REWRITE_TAC[BNVAL_DEF]
    THEN FIRST_ASSUM (SUBST1_TAC o SYM) THEN MATCH_MP_TAC LVAL_MAX
    THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[BV_DEF]
    THEN COND_CASES_TAC THEN CONV_TAC (REDEPTH_CONV num_CONV)
    THEN REWRITE_TAC[LESS_0,LESS_MONO_EQ]);

val BNVAL_WCAT1 = store_thm("BNVAL_WCAT1",
    (--`!n. !w:(bool)word::PWORDLEN n.
     !x:bool. BNVAL (WCAT (w,WORD[x])) = ((BNVAL w) * 2)  + (BV x)`--),
    GEN_TAC THEN RESQ_WORDLEN_TAC THEN GEN_TAC
    THEN REWRITE_TAC[BNVAL_DEF,WCAT_DEF]
    THEN PURE_ONCE_REWRITE_TAC[GSYM SNOC_APPEND]
    THEN MATCH_ACCEPT_TAC LVAL_SNOC);

val BNVAL_WCAT2 = store_thm
  ("BNVAL_WCAT2",
   ``!n. !w:(bool)word::PWORDLEN n.
          !x:bool. BNVAL (WCAT (WORD[x],w))
                   = ((BV x) * (2 EXP n)) + (BNVAL w)``,
   REPEAT RESQ_STRIP_TAC
   THEN MP_TAC ((RESQ_SPECL [``n : num``, ``w : bool word``, ``BV``, ``2``, ``x : bool``]) (INST_TYPE [alpha |-> bool] NVAL_WCAT2))
   THEN PROVE_TAC [BNVAL_NVAL]);

val BNVAL_WCAT = store_thm
  ("BNVAL_WCAT",
   ``!n m. !w1 :: PWORDLEN n. !w2 :: PWORDLEN m.
       BNVAL (WCAT (w1, w2)) = (BNVAL w1 * (2 EXP m)) + (BNVAL w2)``,
   REPEAT RESQ_STRIP_TAC
   THEN MP_TAC ((RESQ_SPECL [``n : num``, ``m : num``, ``w1 : bool word``, ``w2 : bool word``, ``BV``, ``2``]) (INST_TYPE [alpha |-> bool] NVAL_WCAT))
   THEN PROVE_TAC [BNVAL_NVAL]);

val VB_DEF = new_definition("VB_DEF",
    (--`VB n = ~((n MOD 2) = 0)`--));

(* NBWORD n m converts m to n-bit boolean word *)
val NBWORD_DEF = new_definition("NBWORD_DEF",
    (--`NBWORD n m = WORD(NLIST n VB 2 m)`--));

val NBWORD0 = store_thm("NBWORD0",
    (--`!m. NBWORD 0 m = WORD[]`--),
    REWRITE_TAC[NBWORD_DEF,NLIST_DEF]);

val NLIST_LENGTH = prove(
    (--`!n (f:num->'a) b m. LENGTH(NLIST n f b m) = n`--),
    INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC[NLIST_DEF]
    THEN ASM_REWRITE_TAC[LENGTH,LENGTH_SNOC]);

val WORDLEN_NBWORD = store_thm("WORDLEN_NBWORD",
    (--`!n m. WORDLEN(NBWORD n m) = n`--),
    REWRITE_TAC[NBWORD_DEF,WORDLEN_DEF,NLIST_LENGTH]);

val PWORDLEN_NBWORD = store_thm("PWORDLEN_NBWORD",
    (--`!n m. (NBWORD n m) IN PWORDLEN n`--),
    REWRITE_TAC[PWORDLEN,WORDLEN_NBWORD]);

val NBWORD_SUC = store_thm("NBWORD_SUC",
    (--`!n m. NBWORD (SUC n) m = WCAT((NBWORD n (m DIV 2)), WORD [VB (m MOD 2)])`--),
    REPEAT GEN_TAC THEN REWRITE_TAC[NBWORD_DEF,NLIST_DEF]
    THEN MATCH_ACCEPT_TAC WORD_SNOC_WCAT);

val VB_BV = store_thm("VB_BV", (--`!x. VB(BV x) = x`--),
    GEN_TAC THEN PURE_ONCE_REWRITE_TAC[BV_DEF]
    THEN PURE_ONCE_REWRITE_TAC[VB_DEF] THEN BOOL_CASES_TAC (--`x:bool`--)
    THEN CONV_TAC(EVERY_CONV[ONCE_DEPTH_CONV COND_CONV,REDEPTH_CONV num_CONV])
    THEN COND_REWRITE1_TAC LESS_MOD
    THEN REWRITE_TAC[LESS_MONO_EQ,LESS_0,SUC_ID]);

val BV_VB = store_thm("BV_VB", (--`!x. x < 2 ==> (BV(VB x) = x)`--),
    let val lem1 = SUBS[SYM (num_CONV (--`2`--))] (SPEC (--`1`--) LESS_0)
    val lems = map (fn th => MP(REWRITE_RULE[LESS_0] (SPEC (--`2`--) th)) lem1)
        [ZERO_DIV,ZERO_MOD]
   in
    CONV_TAC (REDEPTH_CONV num_CONV)
    THEN PURE_REWRITE_TAC[LESS_THM,NOT_LESS_0,OR_CLAUSES,BV_DEF,VB_DEF]
    THEN GEN_TAC THEN  DISCH_THEN (DISJ_CASES_THEN SUBST1_TAC) THENL[
     COND_REWRITE1_TAC LESS_MOD THENL[
      CONV_TAC (REDEPTH_CONV num_CONV) THEN REWRITE_TAC[LESS_MONO_EQ,LESS_0],
      REWRITE_TAC[NOT_SUC]],
     REWRITE_TAC lems]
   end);

val NBWORD_BNVAL = store_thm("NBWORD_BNVAL",
    (--`!n. !w::PWORDLEN n. NBWORD n (BNVAL w) = w`--),
    GEN_TAC THEN RESQ_WORDLEN_TAC
    THEN PURE_REWRITE_TAC[BNVAL_DEF,NBWORD_DEF]
    THEN FIRST_ASSUM (SUBST1_TAC o SYM) THEN PURE_ONCE_REWRITE_TAC[WORD_11]
    THEN SPEC_TAC ((--`l: bool list`--),(--`l:bool list`--))
    THEN SNOC_INDUCT_TAC THEN REWRITE_TAC[LVAL_SNOC,LENGTH,LENGTH_SNOC,NLIST_DEF]
    THEN PURE_ONCE_REWRITE_TAC[MATCH_MP DIV_MULT (SPEC (--`h:bool`--) BV_LESS_2)]
    THEN GEN_TAC THEN PURE_ONCE_REWRITE_TAC[SNOC_11] THEN CONJ_TAC THENL[
      PURE_REWRITE_TAC[BV_DEF,VB_DEF]
      THEN COND_REWRITE1_TAC MOD_MOD THENL[
        CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0,
        BOOL_CASES_TAC (--`x:bool`--) THENL[
          CONV_TAC (ONCE_DEPTH_CONV COND_CONV)
          THEN COND_REWRITE1_TAC MOD_TIMES
          THEN COND_REWRITE1_TAC LESS_MOD THENL[
            CONV_TAC (TOP_DEPTH_CONV num_CONV)
            THEN PURE_ONCE_REWRITE_TAC[LESS_MONO_EQ]
            THEN MATCH_ACCEPT_TAC LESS_0,
            REWRITE_TAC[SUC_ID]],
          REWRITE_TAC[ADD_0] THEN MATCH_MP_TAC MOD_EQ_0
          THEN FIRST_ASSUM ACCEPT_TAC]],
      FIRST_ASSUM ACCEPT_TAC]);

val BNVAL_NBWORD = store_thm("BNVAL_NBWORD",
    (--`!n m. (m < (2 EXP n)) ==> (BNVAL (NBWORD n m) = m)`--),
    let val SUM_LESS = ARITH_PROVE
         (--`!m n p. ((m + n) < p) ==> ((m < p) /\ (n < p))`--)
    val lem1 = SUBS[SYM (num_CONV (--`2`--))] (SPEC (--`1`--) LESS_0)
    val lems = map (fn th => MP(REWRITE_RULE[LESS_0] (SPEC (--`2`--) th)) lem1)
        [ZERO_DIV,ZERO_MOD]
    val lem2 = RESQ_MATCH_MP (SPEC_ALL BNVAL_WCAT1)
     (SPECL [(--`n:num`--), (--`(SUC m) DIV 2`--)]PWORDLEN_NBWORD)
    val (lem31,lem32) =
          CONJ_PAIR(SPEC (--`SUC m`--) (MP (SPEC (--`2`--) DIVISION) lem1))
    in
    REPEAT INDUCT_TAC THENL[
      REWRITE_TAC[NBWORD0,BNVAL_DEF,LVAL],
      PURE_ONCE_REWRITE_TAC[EXP] THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
      THEN REWRITE_TAC[LESS_MONO_EQ,NOT_LESS_0],
      DISCH_TAC THEN PURE_REWRITE_TAC[NBWORD_DEF,NLIST_DEF,BNVAL_DEF,LVAL_SNOC]
      THEN PURE_REWRITE_TAC lems THEN COND_REWRITE1_TAC BV_VB THENL[
        CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0,
        FIRST_ASSUM (fn t => COND_REWRITE1_TAC (PURE_REWRITE_RULE
          [NBWORD_DEF,BNVAL_DEF,LVAL_SNOC](SPEC (--`0`--) t))) THENL[
          CONV_TAC (ONCE_DEPTH_CONV num_CONV)
          THEN MATCH_ACCEPT_TAC ZERO_LESS_EXP,
          REWRITE_TAC[MULT,ADD_0]]],
      DISCH_TAC THEN PURE_ONCE_REWRITE_TAC[NBWORD_SUC]
      THEN PURE_ONCE_REWRITE_TAC[lem2]
      THEN COND_REWRITE1_TAC BV_VB THENL[
        ACCEPT_TAC lem32,
        FIRST_ASSUM (fn t => COND_REWRITE1_TAC (SPEC (--`(SUC m) DIV 2`--) t)) THENL[
          ACCEPT_TAC (PURE_ONCE_REWRITE_RULE[LESS_MULT_MONO]
            (SUBS_OCCS[([1,3],(num_CONV (--`2`--)))]
            (CONV_RULE ((RATOR_CONV o RAND_CONV) (REWR_CONV MULT_SYM))
            (PURE_REWRITE_RULE[EXP] (CONJUNCT1 (MATCH_MP SUM_LESS
            (SUBS [lem31](ASSUME (--`(SUC m) < (2 EXP (SUC n))`--))) )))))),
          ACCEPT_TAC (SYM lem31)]]]
     end);

val ZERO_WORD_VAL = store_thm
  ("ZERO_WORD_VAL",
   ``!w :: PWORDLEN n. (w = NBWORD n 0) = (BNVAL w = 0)``,
   REPEAT (RESQ_STRIP_TAC ORELSE EQ_TAC) THENL
   [PROVE_TAC [DISCH_ALL (SUBS[(MP (SPECL [(--`n:num`--),(--`0`--)] BNVAL_NBWORD)
         (SUBS[SYM(num_CONV (--`2`--))]
          (SPECL [(--`n:num`--), (--`1`--)] ZERO_LESS_EXP)))]
          (AP_TERM (--`BNVAL`--) (ASSUME (--`NBWORD n 0 = w`--))))],
    PROVE_TAC [(DISCH (--`0 = BNVAL w`--) (RIGHT_CONV_RULE
       (RESQ_REWRITE1_CONV [] NBWORD_BNVAL)
         (AP_TERM (--`NBWORD n`--) (ASSUME (--`0 = BNVAL w`--)))))]]);

val WCAT_NBWORD_0 = store_thm("WCAT_NBWORD_0",
    (--`!n1 n2. WCAT((NBWORD n1 0), (NBWORD n2 0)) = (NBWORD (n1 + n2) 0)`--),
    let val lemma1 =
      let val lem1 = SUBS[SYM (num_CONV (--`2`--))] (SPEC (--`1`--) LESS_0)
      val lems = map (fn th => MP(REWRITE_RULE[LESS_0] (SPEC (--`2`--) th)) lem1)
        [ZERO_DIV,ZERO_MOD]
      in
        GEN_ALL(SUBS lems (SPECL [(--`n:num`--) , (--`0`--)] NBWORD_SUC))
      end
   in
    REPEAT INDUCT_TAC THENL[
      REWRITE_TAC[NBWORD0,WCAT0,ADD_CLAUSES],
      REWRITE_TAC[NBWORD0,WCAT0,ADD_CLAUSES],
      REWRITE_TAC[NBWORD0,WCAT0,ADD_CLAUSES],
      PURE_ONCE_REWRITE_TAC[GSYM ADD_SUC]
      THEN SUBST_TAC (map (fn t => SPEC t lemma1) [(--`n2:num`--), (--`(SUC n1) + n2`--)])
      THEN PURE_ONCE_REWRITE_TAC[WCAT_ASSOC]
      THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[PAIR_EQ]]
   end);

(*|- !n m. m <= n ==> (WSPLIT m (NBWORD n 0) = (NBWORD (n - m) 0,NBWORD m 0))*)
val WSPLIT_NBWORD_0 = save_thm("WSPLIT_NBWORD_0",
    let val tms = [(--`NBWORD (n-m) 0`--), (--`NBWORD m 0`--)]
    val ths = map (fn t => SPECL t PWORDLEN_NBWORD)
       [ [(--`n-m`--), (--`0`--)], [(--`m:num`--), (--`0`--)]]
    in
    GEN_ALL(DISCH_ALL
    (CONV_RULE (ONCE_DEPTH_CONV (COND_REWRITE1_CONV [] SUB_ADD))
     (itlist PROVE_HYP ths
      (PURE_ONCE_REWRITE_RULE[WCAT_NBWORD_0]
       (RESQ_SPECL tms (SPECL [(--`n - m`--), (--`m:num`--)]
        (INST_TYPE [alpha |-> bool]
         (CONJUNCT2(word_baseTheory.WORD_PARTITION)))))))))
    end);

val EQ_NBWORD0_SPLIT = store_thm
  ("EQ_NBWORD0_SPLIT",
   ``!n. !w :: PWORDLEN n. !m.
       m <= n ==>
       ((w = NBWORD n 0) =
        ((WSEG (n-m) m w = NBWORD (n-m) 0) /\
         (WSEG m 0 w = NBWORD m 0)))``,
    let
      val lem0 = SPEC_ALL
        (INST_TYPE [{residue =(==`:bool`==), redex =(==`:'a`==)}]
         (CONJUNCT1(word_baseTheory.WORD_PARTITION)))
      val lem1 =
        SYM (UNDISCH (RESQ_SPECL [``w : bool word``, ``m : num``] lem0))
      val lem4 = (SPECL[(--`n:num`--), (--`0`--)] PWORDLEN_NBWORD)
      val lem3 = SYM (UNDISCH_ALL (SPEC_ALL (RESQ_MATCH_MP lem0 lem4)))
      val lem2 = UNDISCH_ALL (SPEC (--`m:num`--) (RESQ_SPEC (--`w:bool word`--)
                                                  (SPEC_ALL (INST_TYPE [{residue =(==`:bool`==),
                                                                         redex =(==`:'a`==)}] WSPLIT_WSEG))))
      val lem5 = SPECL [(--`n-m`--), (--`m:num`--)] WCAT_11
      val lem6 = (RESQ_SPEC (--`w:(bool)word`--)(SPEC (--`n:num`--) (INST_TYPE [alpha |-> bool] WSEG_PWORDLEN)))
      val lem7 = UNDISCH_ALL
        (PURE_ONCE_REWRITE_RULE[ADD_0] (SPECL[(--`m:num`--),(--`0`--)]lem6))
      val lem8 =
        let val lem = PURE_ONCE_REWRITE_RULE[ADD_SYM]
          (UNDISCH_ALL (SPECL[(--`n:num`--),(--`m:num`--)]SUB_ADD))
        in
          MP (SUBS[lem ]
              (PURE_ONCE_REWRITE_RULE[ADD_SYM]
               (SPECL [(--`n-m`--),(--`m:num`--)] lem6)))
          (SPEC (--`n:num`--) LESS_EQ_REFL)
        end
      val [nbwm,nbwn] = map (fn tls => SPECL tls PWORDLEN_NBWORD)
        [[(--`m:num`--), (--`0`--)], [(--`n-m`--), (--`0`--)]]
      val lem10 = itlist (fn t1 => fn t2 => RESQ_MATCH_MP t2 t1)
        [nbwm, lem7, nbwn, lem8] lem5
    in
      GEN_TAC THEN CONV_TAC RES_FORALL_CONV THEN GEN_TAC THEN REPEAT STRIP_TAC
      THEN SUBST_OCCS_TAC[([1],lem1), ([1],lem3)]
      THEN ASSUME_TAC lem4 THEN SUBST1_TAC lem2
      THEN COND_REWRITE1_TAC WSPLIT_NBWORD_0
      THEN ACCEPT_TAC lem10
    end);

val LESS2_DIV2 = prove(
    (--`!r y. 0 < y /\ (r < (2 * y)) ==> ((r DIV 2) < y)`--),
    REPEAT INDUCT_TAC THENL[
      REWRITE_TAC[NOT_LESS_0],
      STRIP_TAC THEN COND_REWRITE1_TAC ZERO_DIV THENL[
        CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0,
        FIRST_ASSUM ACCEPT_TAC],
      REWRITE_TAC[NOT_LESS_0],
    PURE_ONCE_REWRITE_TAC[MULT_CLAUSES]
    THEN SUBST_OCCS_TAC[([1],(num_CONV(--`2`--)))] THEN SUBST1_TAC(num_CONV(--`1`--))
    THEN REWRITE_TAC[ADD,LESS_THM] THEN STRIP_TAC THENL[
      POP_ASSUM SUBST1_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
      THEN PURE_ONCE_REWRITE_TAC[MULT_0] THEN DISJ1_TAC
      THEN MATCH_MP_TAC LESS_DIV_EQ_ZERO THEN CONV_TAC (REDEPTH_CONV num_CONV)
      THEN REWRITE_TAC[LESS_0,LESS_MONO_EQ],
      POP_ASSUM SUBST1_TAC THEN DISJ1_TAC THEN PURE_ONCE_REWRITE_TAC[MULT_SYM]
      THEN MATCH_MP_TAC MULT_DIV THEN CONV_TAC (REDEPTH_CONV num_CONV)
      THEN REWRITE_TAC[LESS_0],
      POP_ASSUM MP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
      THEN REWRITE_TAC[MULT_0,NOT_LESS_0],
      POP_ASSUM SUBST1_TAC THEN DISJ1_TAC
      THEN PURE_ONCE_REWRITE_TAC[ADD1] THEN PURE_ONCE_REWRITE_TAC[MULT_SYM]
      THEN COND_REWRITE1_TAC ADD_DIV_ADD_DIV THENL[
         CONV_TAC (REDEPTH_CONV num_CONV) THEN REWRITE_TAC[LESS_0],
         COND_REWRITE1_TAC LESS_DIV_EQ_ZERO THENL[
           CONV_TAC (REDEPTH_CONV num_CONV)
           THEN REWRITE_TAC[LESS_0,LESS_MONO_EQ],
           MATCH_ACCEPT_TAC ADD_0]],
      POP_ASSUM SUBST1_TAC THEN DISJ1_TAC THEN PURE_ONCE_REWRITE_TAC[MULT_SYM]
      THEN MATCH_MP_TAC MULT_DIV THEN CONV_TAC (REDEPTH_CONV num_CONV)
      THEN REWRITE_TAC[LESS_0],
      DISJ2_TAC THEN RES_TAC]]);

val less2 = SUBS[SYM (num_CONV (--`2`--))] (SPEC (--`1`--) LESS_0);

val MOD_DIV_lemma = prove(
    (--`!x y. 0 < y ==> (((x MOD (2 * y)) DIV 2) = ((x DIV 2) MOD y))`--),
    let val lem1 = MATCH_MP NOT_MULT_LESS_0
                         (CONJ less2 (ASSUME (--`0 < y`--)))
    in
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN CHOOSE_THEN (CHOOSE_THEN STRIP_ASSUME_TAC)
     (MATCH_MP (SPEC (--`x:num`--) DA) lem1)
    THEN SUBST1_TAC (ASSUME (--`x = (q * (2 * y)) + r`--))
    THEN PURE_ONCE_REWRITE_TAC[MATCH_MP MOD_MULT (ASSUME (--`r < (2 * y)`--))]
    THEN PURE_ONCE_REWRITE_TAC [MULT_SYM]
    THEN PURE_ONCE_REWRITE_TAC [GSYM MULT_ASSOC]
    THEN PURE_ONCE_REWRITE_TAC [MULT_SYM]
    THEN COND_REWRITE1_TAC ADD_DIV_ADD_DIV THENL[
      CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0,
      PURE_ONCE_REWRITE_TAC [MULT_SYM]
      THEN IMP_RES_THEN (fn t => REWRITE_TAC[t]) MOD_TIMES
      THEN IMP_RES_TAC LESS2_DIV2 THEN COND_REWRITE1_TAC LESS_MOD
      THEN REFL_TAC]
    end);

val NBWORD_MOD = store_thm("NBWORD_MOD",
    (--`!n m. NBWORD n (m MOD (2 EXP n)) = NBWORD n m`--),
    let val lemma1 =
    (* |- (WCAT
    (NBWORD n((m MOD (2 EXP (SUC n))) DIV 2),
     WORD[VB((m MOD (2 EXP (SUC n))) MOD 2)]) =
    WCAT(NBWORD n(m DIV 2),WORD[VB(m MOD 2)])) =
   (NBWORD n((m MOD (2 EXP (SUC n))) DIV 2) = NBWORD n(m DIV 2)) /\
   (WORD[VB((m MOD (2 EXP (SUC n))) MOD 2)] = WORD[VB(m MOD 2)]) *)
        let val tms1 = [(--`NBWORD n((m MOD (2 EXP (SUC n))) DIV 2)`--),
            (--`NBWORD n(m DIV 2)`--)]
        val tms2 = [(--`WORD[VB((m MOD (2 EXP (SUC n))) MOD 2)]`--),
            (--`WORD[VB(m MOD 2)]`--)]
        val lem1 = RESQ_SPECL (tms1 @ tms2)
                        (SPECL[(--`n:num`--),(--`1`--)] (INST_TYPE [alpha |-> bool] WCAT_11))
        val lems2 =
            let val lm =  GEN_ALL (REWRITE_RULE[LENGTH]
                (RIGHT_CONV_RULE (RAND_CONV num_CONV)
                 (SPECL [(--`1`--), (--`[x:'a]`--)] IN_PWORDLEN)))
            in
               map (fn t =>
                    ISPEC (hd (#1 (listSyntax.dest_list (rand t)))) lm) tms2
            end
        val lems3 =
            map (fn t => ISPECL (snd (strip_comb t)) PWORDLEN_NBWORD) tms1
        in
         (itlist PROVE_HYP (lems2 @ lems3) lem1)
        end
    in
    INDUCT_TAC THENL[
      REWRITE_TAC[NBWORD0],
      REWRITE_TAC[NBWORD_SUC] THEN GEN_TAC
      THEN SUBST1_TAC lemma1 THEN CONJ_TAC THEN PURE_ONCE_REWRITE_TAC[EXP]
      THENL[
        COND_REWRITE1_TAC MOD_DIV_lemma THENL[
          CONV_TAC (ONCE_DEPTH_CONV num_CONV)
          THEN MATCH_ACCEPT_TAC ZERO_LESS_EXP,
          FIRST_ASSUM MATCH_ACCEPT_TAC],
        COND_REWRITE1_TAC MOD_MULT_MOD THENL[
          CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0,
          CONV_TAC (ONCE_DEPTH_CONV num_CONV)
          THEN MATCH_ACCEPT_TAC ZERO_LESS_EXP,
          REFL_TAC]]]
    end);

val WSEG_NBWORD_SUC = store_thm("WSEG_NBWORD_SUC",
    (--`!n m. (WSEG n 0(NBWORD (SUC n) m) = NBWORD n m)`--),
    INDUCT_TAC THENL[
     REWRITE_TAC[NBWORD0,WSEG0],
     GEN_TAC THEN PURE_ONCE_REWRITE_TAC[NBWORD_SUC]
     THEN RESQ_REWRITE1_TAC
                 (SPECL[(--`SUC n`--), (--`1`--)] WSEG_WCAT_WSEG) THENL[
      MATCH_ACCEPT_TAC PWORDLEN_NBWORD,
      MATCH_ACCEPT_TAC PWORDLEN1,
      PURE_ONCE_REWRITE_TAC[GSYM ADD1,ADD_0]
      THEN MATCH_ACCEPT_TAC LESS_EQ_SUC_REFL,
      CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0,
      CONV_TAC ((RATOR_CONV o RAND_CONV) num_CONV)
      THEN PURE_REWRITE_TAC[ADD_0,LESS_EQ_MONO]
      THEN MATCH_ACCEPT_TAC ZERO_LESS_EQ,
      PURE_REWRITE_TAC[SUB_0,ADD_0,SUC_SUB1]
      THEN PURE_ONCE_ASM_REWRITE_TAC[]
      THEN RESQ_REWRITE1_TAC (SPEC (--`1`--) WSEG_WORD_LENGTH)
      THEN REFL_TAC]]);

open SingleStep
infix 8 by
val NBWORD_SUC_WSEG = store_thm("NBWORD_SUC_WSEG",
    (--`!n. !w::PWORDLEN(SUC n). NBWORD n(BNVAL w) = WSEG n 0 w`--),
    GEN_TAC THEN RESQ_GEN_TAC
    THEN FIRST_ASSUM (fn t => SUBST_OCCS_TAC [([1],(RESQ_MATCH_MP
        (SPEC_ALL WORDLEN_SUC_WCAT_BIT_WSEG) t))])
    THEN PURE_ONCE_REWRITE_TAC[BNVAL_NVAL]
    THEN `(WSEG n 0 w) IN PWORDLEN n` by
       (RESQ_IMP_RES_TAC WSEG_PWORDLEN THEN
        simpLib.ASM_SIMP_TAC bossLib.arith_ss [])
    THEN FIRST_ASSUM (fn t => PURE_ONCE_REWRITE_TAC
        [(RESQ_MATCH_MP (SPEC_ALL NVAL_WCAT2) t)])
    THEN PURE_ONCE_REWRITE_TAC[GSYM NBWORD_MOD]
    THEN COND_REWRITE1_TAC MOD_MULT THENL[
        RESQ_IMP_RES_TAC (MATCH_MP NVAL_MAX BV_LESS_2),
        PURE_ONCE_REWRITE_TAC[GSYM BNVAL_NVAL]
        THEN RESQ_IMP_RES_TAC NBWORD_BNVAL]);

val DOUBLE_EQ_SHL = store_thm("DOUBL_EQ_SHL",
    (--`!n. 0 < n ==>  !w::PWORDLEN n. !b.
     (NBWORD n ((BNVAL w) + (BNVAL w) + (BV b))) = SND(SHL F w b)`--),
    let val WORD1 = REWRITE_RULE[LENGTH]
                        (RIGHT_CONV_RULE(ONCE_DEPTH_CONV num_CONV)
        (ISPECL [(--`1`--), (--`[b:bool]`--)] IN_PWORDLEN))
    val bnval_lem = (SPECL[(--`n:num`--),(--`BNVAL w`--)]PWORDLEN_NBWORD)
    in
    PURE_ONCE_REWRITE_TAC[ADD_ASSOC,SHL_DEF]
    THEN PURE_ONCE_REWRITE_TAC[GSYM TIMES2,SND]
    THEN PURE_ONCE_REWRITE_TAC[MULT_SYM,COND_CLAUSES]
    THEN INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0,LESS_0]
    THEN RESQ_GEN_TAC THEN PURE_ONCE_REWRITE_TAC[NBWORD_SUC]
    THEN PURE_ONCE_REWRITE_TAC
            (map (fn th => MATCH_MP th(SPEC (--`b:bool`--) BV_LESS_2))
     [MOD_MULT, DIV_MULT])
    THEN PURE_ONCE_REWRITE_TAC[VB_BV] THEN IMP_RES_THEN SUBST1_TAC PWORDLEN
    THEN PURE_ONCE_REWRITE_TAC[PRE] THEN GEN_TAC
    THEN RESQ_IMP_RES_THEN
             (fn t => ASSUME_TAC(REWRITE_RULE[ADD,LESS_EQ_SUC_REFL]
        (SPECL[(--`n:num`--),(--`0`--)] t))) WSEG_PWORDLEN
    THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ]
    THEN RESQ_IMP_RES_TAC NBWORD_SUC_WSEG
   end);

val ZERO_LESS_TWO_EXP = (GEN_ALL(SUBS[SYM(num_CONV (--`2`--))]
        (SPECL[(--`m:num`--),(--`1`--)]ZERO_LESS_EXP)));

val MSB_NBWORD = store_thm("MSB_NBWORD",
    (--`!n m. BIT n (NBWORD (SUC n) m) = VB((m DIV (2 EXP n)) MOD 2)`--),
    INDUCT_TAC THENL[
     REWRITE_TAC[NBWORD_DEF,NLIST_DEF,EXP,BIT0,
      MULT_CLAUSES,(num_CONV (--`1`--)),DIV_ONE,SNOC],
     GEN_TAC THEN PURE_ONCE_REWRITE_TAC[NBWORD_SUC,EXP]
     THEN RESQ_REWRITE1_TAC
              (SPECL [(--`SUC n`--), (--`1`--)] BIT_WCAT_FST) THENL[
      MATCH_ACCEPT_TAC PWORDLEN_NBWORD,
      MATCH_ACCEPT_TAC PWORDLEN1,
      CONV_TAC (ONCE_DEPTH_CONV num_CONV)
      THEN REWRITE_TAC[LESS_EQ_MONO,ZERO_LESS_EQ],
      CONV_TAC (ONCE_DEPTH_CONV num_CONV)
      THEN REWRITE_TAC[LESS_ADD_SUC],
      ASM_REWRITE_TAC[SUC_SUB1] THEN COND_REWRITE1_TAC DIV_DIV_DIV_MULT THENL[
       CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0,
       CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN MATCH_ACCEPT_TAC ZERO_LESS_EXP,
       REFL_TAC]]]);

val NBWORD_SPLIT = store_thm("NBWORD_SPLIT",
    (--`!n1 n2 m. NBWORD (n1 + n2) m =
     WCAT ((NBWORD n1 (m DIV (2 EXP n2))), (NBWORD n2 m))`--),
    let val  exp_lems =
        let val lm = CONJUNCT2 EXP in
        (map GSYM [lm, PURE_ONCE_REWRITE_RULE[MULT_SYM]lm])
        end
    in
    INDUCT_TAC THENL[
     REWRITE_TAC[ADD,NBWORD0,WCAT0],
     REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[ADD]
     THEN PURE_ONCE_REWRITE_TAC[NBWORD_SUC]
     THEN PURE_ONCE_ASM_REWRITE_TAC[]
     THEN PURE_ONCE_REWRITE_TAC[GSYM WCAT_ASSOC]
     THEN COND_REWRITE1_TAC DIV_DIV_DIV_MULT THENL[
      MATCH_ACCEPT_TAC ZERO_LESS_TWO_EXP,
      CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0,
      PURE_ONCE_REWRITE_TAC exp_lems
      THEN PURE_ONCE_REWRITE_TAC (map GSYM [NBWORD_SUC, MSB_NBWORD])
      THEN SUBST1_TAC (SYM (SPECL [(--`n2:num`--),(--`m:num`--)] WSEG_NBWORD_SUC))
      THEN RESQ_REWRITE1_TAC (GSYM WORDLEN_SUC_WCAT_BIT_WSEG) THENL[
       MATCH_ACCEPT_TAC PWORDLEN_NBWORD,
       REFL_TAC]]]
    end);

val WSEG_NBWORD = store_thm("WSEG_NBWORD",
    (--`!m k n.  (m + k) <= n ==>
     (!l. WSEG m k(NBWORD n l) = NBWORD m (l DIV (2 EXP k)))`--),
    let val lem1 = CONV_RULE (COND_REWRITE1_CONV [] SUB_ADD)
        (SPECL[(--`n-k`--), (--`k:num`--), (--`l:num`--)]NBWORD_SPLIT)
    val lem2 = CONV_RULE (COND_REWRITE1_CONV [] SUB_ADD)
        (SPECL[(--`(n-k)-m`--), (--`m:num`--)]NBWORD_SPLIT)
    in
    REPEAT STRIP_TAC THEN IMP_RES_TAC LESS_EQ_SPLIT
    THEN SUBST1_TAC lem1
    THEN RESQ_REWRITE1_TAC
           (SPECL[(--`n-k`--), (--`k:num`--)]WSEG_WCAT_WSEG1) THENL[
      MATCH_ACCEPT_TAC PWORDLEN_NBWORD,
      MATCH_ACCEPT_TAC PWORDLEN_NBWORD,
      COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB) THEN FIRST_ASSUM ACCEPT_TAC,
      MATCH_ACCEPT_TAC LESS_EQ_REFL,
      PURE_ONCE_REWRITE_TAC[SUB_EQUAL_0]
      THEN PURE_ONCE_REWRITE_TAC [lem2]
      THEN RESQ_REWRITE1_TAC (SPECL[(--`(n-k)-m`--), (--`m:num`--)]WSEG_WCAT2)
      THEN TRY (MATCH_ACCEPT_TAC PWORDLEN_NBWORD)
      THEN REFL_TAC]
   end);

(* NBWORD_SUC_FST =
|- !n m.
    NBWORD(SUC n)m = WCAT(WORD[VB((m DIV (2 EXP n)) MOD 2)],NBWORD n m) *)

val NBWORD_SUC_FST = save_thm("NBWORD_SUC_FST",
    GEN_ALL (REWRITE_RULE[ADD](REWRITE_RULE[NBWORD_SUC,NBWORD0,WCAT0]
    (SUBS[num_CONV(--`1`--)](SPECL[(--`1`--), (--`n:num`--)] NBWORD_SPLIT)))));

val BIT_NBWORD0 = store_thm("BIT_NBWORD0",
    (--`!k n. k < n ==> (BIT k (NBWORD n 0) = F)`--),
    let val les1 = SUBS[SYM (num_CONV (--`1`--))](SPEC(--`0`--)LESS_SUC_REFL)
       val lem1 = REWRITE_RULE[ADD,les1]
                (PROVE_HYP (SPECL [(--`n:num`--),(--`0`--)]PWORDLEN_NBWORD)
     (RESQ_SPECL[(--`n:num`--),(--`NBWORD n 0`--),(--`1`--),
               (--`k:num`--),(--`0`--)](INST_TYPE [alpha |-> bool]BIT_WSEG)))
    in
    REPEAT STRIP_TAC THEN COND_REWRITE1_TAC (GSYM lem1) THENL[
     ARITH_TAC,
     RESQ_REWRITE1_TAC WSEG_NBWORD THEN COND_REWRITE1_TAC ZERO_DIV THENL[
      MATCH_ACCEPT_TAC ZERO_LESS_TWO_EXP,
      SUBST1_TAC (num_CONV (--`1`--)) THEN PURE_ONCE_REWRITE_TAC[MSB_NBWORD]
      THEN REWRITE_TAC [EXP,(num_CONV (--`1`--)),DIV_ONE,VB_DEF]
      THEN COND_REWRITE1_TAC MOD_MOD THENL[
       CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0,
       COND_REWRITE1_TAC LESS_MOD THEN REFL_TAC]]]
    end);

val add_lem = prove(
    (--`!m1 m2 n1 n2 p. (((m1 * p) + n1)  + ((m2 * p) + n2) =
        ((m1 * p) + (m2 * p)) + (n1 + n2))`--),
    REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[GSYM ADD_ASSOC]
    THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
    THEN PURE_ONCE_REWRITE_TAC[EQ_MONO_ADD_EQ]
    THEN CONV_TAC (AC_CONV(ADD_ASSOC,ADD_SYM)));

val ADD_BNVAL_LEFT = store_thm("ADD_BNVAL_LEFT",
    (--`!n. !w1 w2:bool word::PWORDLEN (SUC n).
     ((BNVAL w1) + (BNVAL w2)) =
      (((BV (BIT n w1)) + (BV (BIT n w2))) * (2 EXP n)) +
       ((BNVAL (WSEG n 0 w1)) + (BNVAL (WSEG n 0 w2)))`--),
    let val mk_lem =
        let val lem = SPEC_ALL WSEG_PWORDLEN
        val lem2 = SPEC_ALL BNVAL_WCAT2
        in
        (fn t => RESQ_MATCH_MP lem2
            (REWRITE_RULE[ADD_0,LESS_EQ_SUC_REFL]
                     (SPECL[(--`n:num`--), (--`0`--)]
            (RESQ_MATCH_MP lem t))))
        end
   in
    GEN_TAC THEN REPEAT RESQ_GEN_TAC
    THEN EVERY_ASSUM (fn t =>SUBST_OCCS_TAC [([1],
                (RESQ_MATCH_MP (SPEC_ALL WORDLEN_SUC_WCAT_BIT_WSEG) t))])
    THEN EVERY_ASSUM ((fn t => REWRITE_TAC[t]) o mk_lem)
    THEN PURE_ONCE_REWRITE_TAC[add_lem]
    THEN REWRITE_TAC[RIGHT_ADD_DISTRIB]
   end);

val ADD_BNVAL_RIGHT = store_thm("ADD_BNVAL_RIGHT",
    (--`!n. !w1 w2:bool word::PWORDLEN (SUC n).
     ((BNVAL w1) + (BNVAL w2)) =
      (((BNVAL (WSEG n 1 w1)) + (BNVAL (WSEG n 1 w2))) * 2) +
       ((BV (BIT 0 w1)) + (BV (BIT 0 w2))) `--),
    let val mk_lem =
        let val lem = SPEC_ALL WSEG_PWORDLEN
        val lem2 = SPEC_ALL BNVAL_WCAT1
        in
        (fn t => RESQ_MATCH_MP lem2
            (REWRITE_RULE[GSYM ADD1,LESS_EQ_REFL]
            (SPECL[(--`n:num`--), (--`1`--)]
            (RESQ_MATCH_MP lem t))))
       end
    in
    GEN_TAC THEN REPEAT RESQ_GEN_TAC
    THEN EVERY_ASSUM (fn t => SUBST_OCCS_TAC [([1],
        (RESQ_MATCH_MP (SPEC_ALL WORDLEN_SUC_WCAT_BIT_WSEG_RIGHT) t))])
    THEN EVERY_ASSUM ((fn t =>REWRITE_TAC[t]) o mk_lem)
    THEN PURE_ONCE_REWRITE_TAC[add_lem]
    THEN REWRITE_TAC[RIGHT_ADD_DISTRIB]
    end);

val ADD_BNVAL_SPLIT = store_thm("ADD_BNVAL_SPLIT",
    (--`!n1 n2. !w1 w2:bool word::PWORDLEN (n1 + n2).
     ((BNVAL w1) + (BNVAL w2)) =
      (((BNVAL (WSEG n1 n2 w1)) + (BNVAL (WSEG n1 n2 w2))) * (2 EXP n2)) +
       ((BNVAL (WSEG n2 0 w1)) + (BNVAL (WSEG n2 0 w2)))`--),
    let val seg_lem = PURE_ONCE_REWRITE_RULE[ADD_SYM]
        (CONV_RULE (HO_REWR_CONV (GSYM RES_FORALL))
        (GEN ``w : 'a word``
        (DISCH_ALL
         (SYM
          (TRANS
           (REWRITE_RULE[LESS_EQ_REFL] (PURE_ONCE_REWRITE_RULE[ADD_0]
               (RESQ_SPECL [``n2 + n1``, ``w : 'a word``, ``n2:num``, ``n1:num``, ``0``] WCAT_WSEG_WSEG)))
           (RESQ_SPECL [``n2 + n1``, ``w : 'a word``] WSEG_WORD_LENGTH))))))
    val lem = SPEC_ALL WSEG_PWORDLEN
    val lem2 = SPECL [(--`n1:num`--), (--`n2:num`--)] BNVAL_WCAT
    val LESS_EQ_ADD2 = PURE_ONCE_REWRITE_RULE[ADD_SYM]LESS_EQ_ADD
    in
    REPEAT GEN_TAC THEN REPEAT RESQ_GEN_TAC
    THEN EVERY_ASSUM
           (fn t => SUBST_OCCS_TAC [([1], (RESQ_MATCH_MP seg_lem t))])
    THEN RESQ_REWRITE1_TAC lem2
    THEN TRY
        (RULE_ASSUM_TAC (RESQ_MATCH_MP lem) THEN FIRST_ASSUM MATCH_MP_TAC
         THEN REWRITE_TAC[ADD_0,LESS_EQ_ADD2,LESS_EQ_REFL])
    THEN PURE_ONCE_REWRITE_TAC[add_lem]
    THEN REWRITE_TAC[RIGHT_ADD_DISTRIB]
   end);

val _ = export_theory();
val _ = export_doc_theorems();
