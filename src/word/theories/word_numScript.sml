(* ===================================================== *)
(* FILE: mk_word_num.ml	    DATE: 14 Aug 1992		 *)
(* AUTHOR: Wai WONG  	    	    			 *)
(* TRANSLATOR: Paul Curzon  2 June 1993, Sept 1994	 *)
(* Writes: word_base.th	    	    			 *)
(* Uses: Libraries: list res_quan			 *)
(* Description: Creates a theory for mapping between 	 *)
(* natural numbers and generic words	    	    	 *)
(* ===================================================== *)
(* PC 18/11/93: SEG ->WSEG *)



open HolKernel Parse boolLib Prim_rec Num_conv Num_induct;
open Base;
open arithLib numLib res_quanLib;
open rich_listTheory pairTheory arithmeticTheory prim_recTheory numTheory;
infix THEN THENL THENC ORELSE ORELSEC;
open Res_quan word_baseTheory;

val _ = new_theory "word_num";

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


(*---------------------------------------------------------------*)
(* Mapping between word and num 	    			 *)
(*---------------------------------------------------------------*)

(* LVAL f b [bn-1,...,b0] returns the value represnted by a list of digits. *)
(* where b is the base and f is the function mapping the digit to its value *)

val LVAL_DEF = new_definition ("LVAL_DEF",
 (--`
   (LVAL (f:'a->num) b l = FOLDL (\e x. (b * e) + (f x)) 0 l)`--));

val NVAL_DEF = new_recursive_definition {
 name = "NVAL_DEF",
 rec_axiom = word_Ax,
 def = --`NVAL f b (WORD l:'a word) = LVAL f b l`--
 };

val LVAL = store_thm("LVAL",
    (--`(!f:'a->num. !b. LVAL f b [] = 0) /\
     (!l. !f:'a->num. !b x. LVAL f b (CONS (x:'a) l) =
      ((f x) * (b EXP (LENGTH l))) + (LVAL f b l))`--),
    REWRITE_TAC [LVAL_DEF,FOLDL,MULT_CLAUSES,ADD_CLAUSES]
    THEN BETA_TAC THEN REWRITE_TAC[LENGTH,MULT_CLAUSES,ADD_CLAUSES]
    THEN SNOC_INDUCT_TAC THEN REPEAT GEN_TAC THENL[
      REWRITE_TAC[FOLDL,LENGTH,MULT_CLAUSES,EXP,ADD_CLAUSES],
      REWRITE_TAC[FOLDL_SNOC,LENGTH_SNOC,MULT_CLAUSES,EXP,ADD_CLAUSES]
      THEN BETA_TAC THEN PURE_ONCE_REWRITE_TAC[MULT_ASSOC]
      THEN SUBST1_TAC (SPECL[(--`(f:'a->num) x'`--),(--`b:num`--)]MULT_SYM)
      THEN PURE_ONCE_REWRITE_TAC[GSYM MULT_ASSOC]
      THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC]
      THEN PURE_ONCE_REWRITE_TAC[GSYM LEFT_ADD_DISTRIB]
      THEN ASM_REWRITE_TAC[]]);

val LVAL_SNOC = store_thm("LVAL_SNOC",
    (--`!l:'a list. !h f b.
     LVAL f b (SNOC h l) = (((LVAL f b l) * b) + (f h))`--),
    LIST_INDUCT_TAC THEN REWRITE_TAC[SNOC,LVAL,
    	MULT,ADD_CLAUSES,LENGTH,LENGTH_SNOC,EXP,MULT_CLAUSES]
    THEN REPEAT GEN_TAC THEN PURE_ONCE_ASM_REWRITE_TAC[]
    THEN PURE_ONCE_REWRITE_TAC[RIGHT_ADD_DISTRIB]
    THEN CONV_TAC ((RAND_CONV o ONCE_DEPTH_CONV) (REWR_CONV (GSYM MULT_ASSOC)))
    THEN SUBST1_TAC (SPECL[(--`b EXP (LENGTH (l:'a list))`--), (--`b:num`--)] MULT_SYM)
    THEN MATCH_ACCEPT_TAC ADD_ASSOC);

val LESS_SUC_IMP_LESS_EQ = GENL [(--`m:num`--),(--`n:num`--)]
        (TRANS (SPEC_ALL LESS_THM)
          (PURE_ONCE_REWRITE_RULE[DISJ_SYM](SYM (SPEC_ALL LESS_OR_EQ))));

val LVAL_MAX_lem = prove(
    (--`!a b c y. ((a+b)<SUC c) /\ (y < b) ==> ((a+y) < c)`--),
    REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[LESS_SUC_IMP_LESS_EQ]
    THEN STRIP_TAC THEN IMP_RES_THEN (ASSUME_TAC o
    	(SPEC (--`a:num`--)) o (PURE_ONCE_REWRITE_RULE[ADD_SYM])) LESS_MONO_ADD
    THEN IMP_RES_TAC LESS_LESS_EQ_TRANS);

val LESS_MULT_PLUS_DIFF = prove(
   (--`!n k l . (k < l) ==> (((k * n) + n) <= (l * n))`--),
  INDUCT_THEN INDUCTION MP_TAC THEN
  REWRITE_TAC [MULT_CLAUSES,ADD_CLAUSES,LESS_EQ_REFL] THEN
  DISCH_THEN (fn t =>
    REPEAT GEN_TAC THEN
    DISCH_THEN (fn t' =>
         ACCEPT_TAC
         (REWRITE_RULE [ADD_CLAUSES,ADD_ASSOC]
           (MATCH_MP LESS_EQ_LESS_EQ_MONO
             (CONJ (MATCH_MP LESS_OR t') (MATCH_MP t t')))) )));

val LVAL_MAX = store_thm("LVAL_MAX",
    (--`!(l:'a list) f b. (!x. f x < b) ==>
              ((LVAL f b l) < (b EXP (LENGTH l)))`--),
    LIST_INDUCT_TAC THEN REPEAT STRIP_TAC
    THEN PURE_REWRITE_TAC[LVAL,LENGTH,EXP] THENL[
      CONV_TAC (RAND_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0,
      let val lem1 = GEN (--`a:num`--)
           (SPECL[(--`a:num`--),(--`b EXP (LENGTH (l:'a list))`--),
    	(--`b * (b EXP (LENGTH (l:'a list)))`--),(--`LVAL f b (l:'a list)`--)]
    	LVAL_MAX_lem)
      in
       RES_THEN MP_TAC THEN POP_ASSUM (ASSUME_TAC o (SPEC(--`x:'a`--)))
       THEN DISCH_TAC THEN MATCH_MP_TAC lem1 THEN CONJ_TAC
       THEN (MAP_EVERY MATCH_MP_TAC [LESS_EQ_IMP_LESS_SUC,
                                     LESS_MULT_PLUS_DIFF] ORELSE ALL_TAC)
       THEN FIRST_ASSUM ACCEPT_TAC
      end
   ]);

val NVAL_MAX = store_thm("NVAL_MAX",
    (--`!f b. (!x. f x < b) ==>
     !n. !w:'a word ::PWORDLEN n. NVAL f b w < (b EXP n)`--),
    REPEAT STRIP_TAC THEN RESQ_WORDLEN_TAC
    THEN PURE_REWRITE_TAC[NVAL_DEF]
    THEN FIRST_ASSUM SUBST1_TAC
    THEN MATCH_MP_TAC LVAL_MAX THEN FIRST_ASSUM ACCEPT_TAC);

val NVAL0 = store_thm("NVAL0",
    (--`!f b. NVAL f b (WORD[]:('a)word) = 0`--),
    REWRITE_TAC[NVAL_DEF,LVAL]);

val NVAL1 = store_thm("NVAL1",
    (--`!f b (x:'a). NVAL f b (WORD[x]) = (f x)`--),
    REWRITE_TAC[NVAL_DEF,LVAL,LENGTH,EXP,MULT_CLAUSES,ADD_CLAUSES]);

val NVAL_WORDLEN_0 = store_thm("NVAL_WORDLEN_0",
    (--`!w:('a)word::PWORDLEN 0. !fv r. NVAL fv r w = 0`--),
    RESQ_GEN_TAC THEN IMP_RES_THEN SUBST1_TAC PWORDLEN0
    THEN REWRITE_TAC[NVAL_DEF,LVAL]);

val NVAL_WCAT1 = store_thm("NVAL_WCAT1",
    (--`!w:('a)word. !f b x.
     NVAL f b (WCAT (w,WORD[x])) = ((NVAL f b w) * b) + (f x)`--),
    word_INDUCT_TAC THEN REPEAT STRIP_TAC
    THEN REWRITE_TAC[NVAL_DEF,WCAT_DEF]
    THEN PURE_ONCE_REWRITE_TAC[GSYM SNOC_APPEND]
    THEN MATCH_ACCEPT_TAC LVAL_SNOC);

val NVAL_WCAT2 = store_thm("NVAL_WCAT2",
    (--`!n. !w:('a)word::PWORDLEN n. !f b x.
     NVAL f b (WCAT (WORD[x],w)) = ((f x) * (b EXP n)) + (NVAL f b w)`--),
    GEN_TAC THEN RESQ_WORDLEN_TAC THEN REPEAT GEN_TAC
    THEN ASM_REWRITE_TAC[NVAL_DEF,WCAT_DEF]
    THEN PURE_ONCE_REWRITE_TAC[GSYM CONS_APPEND]
    THEN MATCH_ACCEPT_TAC (CONJUNCT2 LVAL));

val NVAL_WCAT = store_thm("NVAL_WCAT",
    (--`!n m. !w1:('a)word::PWORDLEN n. !w2:('a)word::PWORDLEN m. !f b.
     NVAL f b (WCAT (w1,w2)) = ((NVAL f b w1) * (b EXP m)) + (NVAL f b w2)`--),
    let val deres = (GEN_ALL o RESQ_HALF_SPEC o SPEC_ALL)
    val lem1 = deres NVAL_WCAT2
    val lem2 = (REWRITE_RULE[ADD_0,LESS_EQ_SUC_REFL]
                     (SPECL[(--`n:num`--),(--`0`--)]
    	 (RESQ_SPEC (--`w1:('a)word`--)(SPEC (--`SUC n`--) WSEG_PWORDLEN))))
    in
    INDUCT_TAC THEN GEN_TAC THEN REPEAT GGEN_TAC THENL[
     IMP_RES_THEN SUBST1_TAC PWORDLEN0
     THEN PURE_REWRITE_TAC[WCAT0,NVAL0,ADD,MULT] THEN REFL_TAC,
     RESQ_IMP_RES_THEN SUBST1_TAC WORDLEN_SUC_WCAT_BIT_WSEG
     THEN PURE_ONCE_REWRITE_TAC[GSYM WCAT_ASSOC]
     THEN PURE_ONCE_REWRITE_TAC[MATCH_MP lem1 lem2]
     THEN FIRST_ASSUM (ASSUME_TAC o
    	 (MATCH_MP (deres(MATCH_MP (deres WCAT_PWORDLEN) lem2))))
     THEN POP_ASSUM (fn t => PURE_ONCE_REWRITE_TAC[MATCH_MP lem1 t])
     THEN FIRST_ASSUM (fn t => ASSUME_TAC(MATCH_MP (deres t)lem2))
     THEN POP_ASSUM (fn t1 => POP_ASSUM (fn t2 =>
    	PURE_ONCE_REWRITE_TAC[MATCH_MP (deres t1) t2]))
     THEN CONV_TAC (LHS_CONV (REWR_CONV ADD_ASSOC))
     THEN CONV_TAC (REWR_CONV EQ_MONO_ADD_EQ)
     THEN PURE_ONCE_REWRITE_TAC[RIGHT_ADD_DISTRIB]
     THEN CONV_TAC (REWR_CONV EQ_MONO_ADD_EQ)
     THEN PURE_ONCE_REWRITE_TAC[EXP_ADD]
     THEN MATCH_ACCEPT_TAC MULT_ASSOC]
    end);

(* NLIST n fmod b m returns a list of length n which represents the value m *)
(* where b is the base and fmod is the remainder function converting a value*)
(* to fit in a digit.	    	    					   *)

val NLIST_DEF = new_recursive_definition {
 name = "NLIST_DEF",
 rec_axiom = num_Axiom,
 def =
 --`
   (NLIST 0 (frep:num->'a) b m = []) /\
   (NLIST (SUC n) frep b m =
       SNOC (frep (m MOD b)) (NLIST n frep b (m DIV b)))
 `--
 };

val NWORD_DEF = new_definition("NWORD_DEF",
    (--`NWORD n (frep:num->'a) b m = WORD(NLIST n frep b m)`--));

val NLIST_LENGTH = prove(
    (--`!n (f:num->'a) b m. LENGTH(NLIST n f b m) = n`--),
    INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC[NLIST_DEF]
    THEN ASM_REWRITE_TAC[LENGTH,LENGTH_SNOC]);

val NWORD_LENGTH = store_thm("NWORD_LENGTH",
    (--`!n (f:num->'a) b m. WORDLEN(NWORD n f b m) = n`--),
    REWRITE_TAC[NWORD_DEF,WORDLEN_DEF,NLIST_LENGTH]);

val NWORD_PWORDLEN = store_thm("NWORD_PWORDLEN",
    (--`!n (f:num->'a) b m. PWORDLEN n (NWORD n f b m)`--),
    REWRITE_TAC[PWORDLEN_DEF,NWORD_DEF,NLIST_LENGTH]);

val _ = export_theory();
val _ = export_doc_theorems();
