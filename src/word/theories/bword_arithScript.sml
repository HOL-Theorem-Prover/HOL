(*-----------------------------------------------------------------------*)
(* FILE: bword_arith.ml	DATE: 15 Jan 93					 *)
(* WRITES: bword_arith.th    	    					 *)
(* TRANSLATOR: Paul Curzon  3 June 1993, Sept 1994			 *)
(* This theory contains defintions and theorems on boolean word 	 *)
(* arithmetic, e.g. addition.	    					 *)
(*-----------------------------------------------------------------------*)


open HolKernel Parse basicHol90Lib Let_conv Num_conv Num_induct;
open arithLib numLib res_quanLib;
open rich_listTheory pairTheory arithmeticTheory prim_recTheory numTheory;
open Cond_rewrite Res_quan;
open word_baseTheory word_numTheory bword_numTheory;
open Base;

infix THEN THENL THENC ORELSE ORELSEC;

val _ = new_theory"bword_arith";

(* butlast [x1;...x(n-1);xn]   --->   [x1;...;x(n-1)] *)

fun butlast l =
 if null (tl l) then [] else (hd l) :: (butlast(tl l));
(*-----------------------------------------------------------------------*)
(* We begin with with lemmas about arithmetic of natural numbers.	 *)
(* They are used to proof the interesting theorems about word arithmetic *)
(*-----------------------------------------------------------------------*)
val MULT_LEFT_1 = GEN_ALL (el 3 (CONJ_LIST 6 (SPEC_ALL MULT_CLAUSES)));

val ADD_DIV_SUC_DIV = prove(
    (--`!n. 0 < n ==> !r. (((n + r) DIV n) = SUC (r DIV n))`--),
    let val MULT_LEM = SYM (PURE_ONCE_REWRITE_RULE[ADD_SYM]
    	(el 5 (CONJ_LIST 6 (SPECL[(--`q:num`--),(--`n:num`--)] MULT_CLAUSES)))) in
    CONV_TAC (ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV)
    THEN REPEAT GEN_TAC THEN ASM_CASES_TAC (--`r < n`--) THENL[
      IMP_RES_THEN SUBST1_TAC LESS_DIV_EQ_ZERO THEN DISCH_TAC
      THEN SUBST_OCCS_TAC [([1],(SYM (SPEC(--`n:num`--) MULT_LEFT_1)))]
      THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
      THEN MATCH_MP_TAC DIV_MULT THEN FIRST_ASSUM ACCEPT_TAC,
      DISCH_THEN (CHOOSE_TAC o (MATCH_MP (SPEC (--`r:num`--) DA)))
      THEN POP_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC)
      THEN SUBST1_TAC (ASSUME (--`r = (q * n) + r'`--))
      THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC]
      THEN SUBST1_TAC MULT_LEM
      THEN IMP_RES_THEN (fn t =>  REWRITE_TAC[t]) DIV_MULT]
   end);

val LESS_IMP_LESS_EQ_PRE = prove(
    (--`!m n. 0 < n ==> ((m < n) = (m <= (PRE n)))`--),
    REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0] THENL[
     DISCH_TAC THEN REWRITE_TAC[PRE,ZERO_LESS_EQ,LESS_0],
     REWRITE_TAC[PRE,LESS_MONO_EQ] THEN STRIP_TAC
     THEN MATCH_ACCEPT_TAC LESS_EQ]);

val LESS_MONO_DIV = prove(
    (--`!n. 0 < n ==> !p q. p < q ==> ((p DIV n) <= (q DIV n))`--),
    CONV_TAC (REDEPTH_CONV RIGHT_IMP_FORALL_CONV)
    THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN DISCH_THEN ((CHOOSE_THEN (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) o
    	(MATCH_MP Less_lemma))
    THEN REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)
    	(SPEC (--`p:num`--) (MATCH_MP DA (ASSUME (--`0 < n`--))))
    THEN IMP_RES_THEN (fn t => REWRITE_TAC[t]) DIV_MULT
    THEN PURE_ONCE_REWRITE_TAC[GSYM ADD_ASSOC]
    THEN IMP_RES_TAC ADD_DIV_ADD_DIV
    THEN ASM_REWRITE_TAC[LESS_EQ_ADD]);

val LESS_EQ_MONO_DIV = prove(
    (--`!n. 0 < n ==> !p q. p <= q ==> ((p DIV n) <= (q DIV n))`--),
    CONV_TAC (REDEPTH_CONV RIGHT_IMP_FORALL_CONV)
    THEN REPEAT GEN_TAC THEN DISCH_TAC
    THEN DISCH_THEN (fn t =>  DISJ_CASES_THEN2 ASSUME_TAC SUBST1_TAC
    	(REWRITE_RULE[LESS_OR_EQ]t)) THENL[
     IMP_RES_TAC LESS_MONO_DIV,
     REWRITE_TAC[LESS_EQ_REFL]]);

val SUC_PRE = prove(
  (--`!n . (0 < n) ==> ((SUC (PRE n)) = n)`--),
  REPEAT STRIP_TAC THEN
  (ACCEPT_TAC
       (REWRITE_RULE[]
          (MATCH_MP (SPECL[(--`PRE n`--),(--`n:num`--)] PRE_SUC_EQ)
                 (ASSUME (--`0 < n`--)) ))));

val ONE_LESS_TWO_EXP_SUC = prove( (--`!n. 1 < (2 EXP (SUC n))`--),
   INDUCT_TAC THENL
   [REWRITE_TAC [EXP] THEN
    REWRITE_TAC [num_CONV (--`2`--),MULT_CLAUSES] THEN
    REWRITE_TAC [LESS_SUC_REFL],
    PURE_ONCE_REWRITE_TAC [EXP] THEN
    REWRITE_TAC [TIMES2] THEN
    ASSUME_TAC (SPEC (--`2 EXP (SUC n)`--) (SPEC (--`2 EXP (SUC n)`--) LESS_EQ_ADD)) THEN
    IMP_RES_TAC LESS_LESS_EQ_TRANS]);

val ADD_MONO_EQ = ARITH_PROVE (--`!m n p. ((p + m) = (p + n)) = (m = n)`--);



(*-----------------------------------------------------------------------*)
(* ACARRY n w1 w2 cin is the carry input at position n. It is		*)
(* defined in terms of addition of the bits --- classic definition of	*)
(* ripple carry.	    	    	    				*)
(*-----------------------------------------------------------------------*)

val ACARRY_DEF = new_recursive_definition {
 name = "ACARRY_DEF",
 rec_axiom = num_Axiom,
 def =
 --`
   (ACARRY 0 w1 w2 cin = (cin:bool)) /\
   (ACARRY (SUC n) w1 w2 cin =
      VB(((BV (BIT n w1)) + (BV (BIT n w2)) +
    	  (BV (ACARRY n w1 w2 cin))) DIV 2))
 `--
 };

(*-----------------------------------------------------------------------*)
(* ICARRY n w1 w1 cin is the implementation of ripple carry using logic  *)
(* gates only, i.e. /\, \/ only.	    				*)
(*-----------------------------------------------------------------------*)

val ICARRY_DEF = new_recursive_definition {
 name = "ICARRY_DEF",
 rec_axiom = num_Axiom,
 def =
 --`
   (ICARRY 0 w1 w2 cin = (cin:bool)) /\
   (ICARRY (SUC n) w1 w2 cin =
      ((BIT n w1) /\ (BIT n w2)) \/
      (((BIT n w1) \/ (BIT n w2)) /\ (ICARRY n w1 w2 cin)))
 `--
 };

(*-----------------------------------------------------------------------*)
(* We now prove that the implementation of ripple carry is equivalent to *)
(* the specification for all position k less the the word size,		*)
(* i.e. ACARRY_EQ_ICARRY						*)
(*-----------------------------------------------------------------------*)

val div_mod_lemmas =
    let val lm = prove((--`2 + x = SUC(SUC x)`--),
    	CONV_TAC (REDEPTH_CONV num_CONV) THEN REWRITE_TAC[ADD_CLAUSES])
    val less2 = SUBS[SYM (num_CONV (--`2`--))](SPEC (--`1`--) LESS_0)
    val less21 = SUBS[SYM (REDEPTH_CONV num_CONV (--`2`--))]
        (SPEC (--`SUC 0`--) LESS_SUC_REFL)
    val div22 = GEN_ALL(SUBS[lm]
    	(SPEC (--`x:num`--)(MP (SPEC (--`2`--) ADD_DIV_SUC_DIV) less2)))
    val div21 =
          MP (SPECL[(--`SUC 0`--), (--`2`--)] LESS_DIV_EQ_ZERO) less21
    val div20 = MP (SPEC (--`2`--) ZERO_DIV) less2
    val	mod20 = MP (SPEC (--`2`--) ZERO_MOD) less2
    val	mod21 = REWRITE_RULE[MULT,ADD]
    	    (SPEC (--`0`--)
                 (MP (SPECL [(--`2`--), (--`SUC 0`--)] MOD_MULT) less21))
   in
    [div22,div21,div20,mod21,mod20]
   end;

val ACARRY_EQ_ICARRY = store_thm("ACARRY_EQ_ICARRY",
    (--`!n. !w1 w2::PWORDLEN n. !cin k. k <= n ==>
     (ACARRY k w1 w2 cin = ICARRY k w1 w2 cin)`--),
    let val lem1 = GEN_ALL (IMP_TRANS
    	(snd(EQ_IMP_RULE(SPEC_ALL LESS_EQ)))
    	(SPEC_ALL LESS_IMP_LESS_OR_EQ))
    in
    GEN_TAC THEN REPEAT RESQ_GEN_TAC
    THEN GEN_TAC THEN INDUCT_TAC THEN DISCH_TAC
    THEN REWRITE_TAC[ACARRY_DEF,ICARRY_DEF]
    THEN PURE_REWRITE_TAC[BV_DEF,VB_DEF]
    THEN IMP_RES_TAC lem1 THEN RES_TAC
    THEN PURE_ONCE_ASM_REWRITE_TAC[]
    THEN MAP_EVERY BOOL_CASES_TAC [(--`BIT k (w1:bool word)`--),
    	(--`BIT k (w2:bool word)`--), (--`ICARRY k w1 w2 cin`--)]
    THEN REWRITE_TAC([ADD_CLAUSES,NOT_SUC,SUC_NOT] @ div_mod_lemmas)
   end);

(*-----------------------------------------------------------------------*)
(*   	    Word Addition   	    					*)
(* We now develop a theory about word addition. The addition of two n-bit*)
(* words can be carried out in two different ways:			*)
(* 1) convert the operands into natural numbers and do addition (+),	*)
(* 2) split the operands into segments, then using method 1 to add the	*)
(*    corresponding segments as they were smaller words, then concatenate*)
(*    the sums to form the final result.					*)
(* We need to prove that these two methods give the same results.	*)
(*-----------------------------------------------------------------------*)

(* We need a series of lemmas starting here
Less2 = |- 0 < 2
Less2_SUC0 = |- (SUC 0) < 2 *)

val Less2 = SUBS[SYM (num_CONV (--`2`--))](SPEC (--`1`--) LESS_0);

val Less2_SUC0 =
     SUBS[SYM (REDEPTH_CONV num_CONV (--`2`--))](SPEC (--`SUC 0`--) LESS_SUC_REFL);

val MULT_LEFT_1 = GEN_ALL (el 3 (CONJ_LIST 6 (SPEC_ALL MULT_CLAUSES)));
val MULT_RIGHT_1 = GEN_ALL (el 4 (CONJ_LIST 6 (SPEC_ALL MULT_CLAUSES)));

val BV_LESS_EQ_1 = prove((--`!x. BV x <= 1`--),
    GEN_TAC THEN REWRITE_TAC[BV_DEF] THEN COND_CASES_TAC
    THEN CONV_TAC (RAND_CONV num_CONV)
    THEN REWRITE_TAC[LESS_EQ_REFL,LESS_EQ_SUC_REFL]);

val ADD_BV_LESS_EQ_2 = prove(
    (--`!x1 x2. ((BV x1) + (BV x2)) <= 2`--),
    REPEAT GEN_TAC THEN CONV_TAC (RAND_CONV num_CONV)
    THEN SUBST1_TAC (SPEC (--`1`--) ADD1) THEN MATCH_MP_TAC LESS_EQ_LESS_EQ_MONO
    THEN REWRITE_TAC[BV_LESS_EQ_1]);

(* LESS_EQ1_LESS2 = |- n < 2 = n <= 1  *)

val LESS_EQ1_LESS2 = REWRITE_RULE[Less2,PRE]
    (CONV_RULE ((RAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV)num_CONV)
     (SPECL [(--`n:num`--),(--`2`--)] LESS_IMP_LESS_EQ_PRE));

(* BNVAL_LESS_EQ =
    |- !n. !w :: PWORDLEN n. (BNVAL w) <= ((2 EXP n) - 1) *)

val BNVAL_LESS_EQ =
    GEN_ALL (RESQ_GEN_ALL (PURE_ONCE_REWRITE_RULE[PRE_SUB1]
    (EQ_MP
      (SPEC (--`BNVAL w`--)
(*       (GEN  (--`m:num`--)*)
       (MATCH_MP LESS_IMP_LESS_EQ_PRE
     	(SUBS[SYM (num_CONV (--`2`--))]
             (SPECL [(--`n:num`--), (--`1`--)] ZERO_LESS_EXP) )))
      (GQSPEC_ALL BNVAL_MAX))));

val ADD_BNVAL_LESS_EQ = prove(
    (--`!n. !w1 w2::PWORDLEN n. !cin.
     ((BNVAL w1) + (BNVAL w2) + (BV cin)) <= ((2 EXP (SUC n)) - 1)`--),
    let val LESS_EQ_SUB_ADD =
       ARITH_PROVE (--`!m n p. (p <= m) ==> ((m - p) + n = (m + n) - p)`--)
    val [t1,t2] = map (fn t => RESQ_SPEC t (SPEC_ALL BNVAL_LESS_EQ))
    	 [(--`w1:bool word`--), (--`w2:bool word`--)]
    val lem = PURE_REWRITE_RULE[GSYM TIMES2,LEFT_SUB_DISTRIB,MULT_CLAUSES]
    	(MATCH_MP LESS_EQ_LESS_EQ_MONO (CONJ t1 t2))
    val lem2 = (MATCH_MP LESS_EQ_LESS_EQ_MONO
    	(CONJ lem (SPEC (--`cin:bool`--)  BV_LESS_EQ_1)))
    in
    REPEAT GGEN_TAC THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC,EXP]
    THEN MP_TAC lem2 THEN COND_REWRITE1_TAC LESS_EQ_SUB_ADD THENL[
     SUBST_OCCS_TAC [([1],(SYM (SPEC (--`2`--) MULT_RIGHT_1)))]
     THEN PURE_ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC LESS_MONO_MULT
     THEN CONV_TAC (ONCE_DEPTH_CONV num_CONV)
     THEN REWRITE_TAC[GSYM LESS_EQ, ZERO_LESS_EXP],
     PURE_ONCE_REWRITE_TAC[GSYM ADD1]
     THEN CONV_TAC ((LHS_CONV o RHS_CONV o RHS_CONV)num_CONV)
     THEN REWRITE_TAC[SUB_MONO_EQ]]
    end);

val ZERO_LESS_TWO_EXP = (* |- !m. 0 < (2 EXP m) *)
    (GEN_ALL(SUBS[SYM(num_CONV (--`2`--))]
          (SPECL[(--`m:num`--),(--`1`--)]ZERO_LESS_EXP)));


val EXP_SUB1_LESS = prove((--`((2 EXP n) - 1) < (2 EXP n)`--),
    PURE_ONCE_REWRITE_TAC[GSYM PRE_SUB1]
    THEN MATCH_MP_TAC PRE_LESS_REFL
    THEN MATCH_ACCEPT_TAC ZERO_LESS_TWO_EXP);


(* ADD_BNVAL_LESS_EQ1 =
    |- !n cin.
       !w1 w2 :: PWORDLEN n.
     (((BNVAL w1) + ((BNVAL w2) + (BV cin))) DIV (2 EXP n)) <= (SUC 0) *)

val ADD_BNVAL_LESS_EQ1 =
  let val LESS_EQ_ADD_SUB1 = ARITH_PROVE (--`!m n p. (p <= n) ==>
    	(m + (n - p) = (m + n) - p)`--)
    val ONE_LESS_EQ_TWO_EXP =
    	REWRITE_RULE[LESS_EQ,GSYM(num_CONV(--`1`--))]ZERO_LESS_TWO_EXP
    val lm1 = SYM (SPECL[(--`n:num`--), (--`2 EXP n`--)]
        (GEN(--`m:num`--)
    	 (MATCH_MP LESS_EQ_ADD_SUB1 (SPEC_ALL ONE_LESS_EQ_TWO_EXP))))
  in
  GENL[(--`n:num`--),(--`cin:bool`--)]
   (RESQ_GEN_ALL (PROVE_HYP (SPEC_ALL ZERO_LESS_TWO_EXP)
   (CONV_RULE ((RAND_CONV o RAND_CONV)
        (COND_REWRITE1_CONV [EXP_SUB1_LESS] LESS_DIV_EQ_ZERO))
    (CONV_RULE (RAND_CONV
         (COND_REWRITE1_CONV
              [SPEC(--`n:num`--) ZERO_LESS_TWO_EXP] ADD_DIV_SUC_DIV))
     (SPEC(--`n:num`--) (GEN(--`n':num`--)
     (MATCH_MP
           (MATCH_MP
              (SPEC (--`2 EXP n`--) LESS_EQ_MONO_DIV)
              (SPEC(--`n:num`--) ZERO_LESS_TWO_EXP)
              )
        (SUBS[lm1](REWRITE_RULE[EXP,TIMES2](GQSPEC_ALL ADD_BNVAL_LESS_EQ)))
     )))
     ))))
  end;

(* ADD_BV_BNVAL_DIV_LESS_EQ1 =
|- !n x1 x2 cin.
    !w1 w2 :: PWORDLEN n.
     ((((BV x1) + (BV x2)) +
       (((BNVAL w1) + ((BNVAL w2) + (BV cin))) DIV (2 EXP n))) DIV 2) <= 1 *)

val ADD_BV_BNVAL_DIV_LESS_EQ1 =
    GENL[(--`n:num`--),(--`x1:bool`--),(--`x2:bool`--),(--`cin:bool`--)]
    (RESQ_GEN_ALL (SUBS[SYM (num_CONV (--`1`--))]
     (CONV_RULE ((RAND_CONV o RAND_CONV)
    	(COND_REWRITE1_CONV [Less2_SUC0] LESS_DIV_EQ_ZERO))
      (CONV_RULE (RAND_CONV
    	(COND_REWRITE1_CONV [Less2] ADD_DIV_SUC_DIV))
       (MATCH_MP (MATCH_MP LESS_EQ_MONO_DIV Less2)
        (MATCH_MP LESS_EQ_LESS_EQ_MONO (CONJ (SPEC_ALL ADD_BV_LESS_EQ_2)
    	(GQSPEC_ALL ADD_BNVAL_LESS_EQ1))))))));

(* ADD_BV_BNVAL_LESS_EQ =
|- !n x1 x2 cin.
    !w1 w2 :: PWORDLEN n.
     (((BV x1) + (BV x2)) + ((BNVAL w1) + ((BNVAL w2) + (BV cin)))) <=
     (SUC(2 EXP (SUC n))) *)

val ADD_BV_BNVAL_LESS_EQ =
    let val lm = MATCH_MP SUC_PRE (MATCH_MP SUC_LESS
    	(CONV_RULE (LHS_CONV num_CONV) (SPEC_ALL ONE_LESS_TWO_EXP_SUC)))
    in
    GENL[(--`n:num`--),(--`x1:bool`--),(--`x2:bool`--),(--`cin:bool`--)]
     (RESQ_GEN_ALL
    (REWRITE_RULE[GSYM PRE_SUB1,ADD,lm]
    (CONV_RULE ((RAND_CONV o LHS_CONV)(REDEPTH_CONV num_CONV))
    (MATCH_MP LESS_EQ_LESS_EQ_MONO
    (CONJ (SPEC_ALL ADD_BV_LESS_EQ_2) (GQSPEC_ALL ADD_BNVAL_LESS_EQ))))))
    end;

(* ADD_BV_BNVAL_LESS_EQ1 =
|- !n x1 x2 cin. !w1 w2 :: PWORDLEN n.
 ((((BV x1) + (BV x2)) + ((BNVAL w1) + ((BNVAL w2) + (BV cin)))) DIV
  (2 EXP (SUC n))) <= 1 *)

val ADD_BV_BNVAL_LESS_EQ1 =
  (GENL[(--`n:num`--),(--`x1:bool`--),(--`x2:bool`--),(--`cin:bool`--)] o
     RESQ_GEN_ALL)
  (SUBS[SYM (SPEC_ALL ADD1)]
   (PROVE_HYP (MATCH_MP SUC_LESS
    	(CONV_RULE (LHS_CONV num_CONV) (SPEC_ALL ONE_LESS_TWO_EXP_SUC)))
    (SUBS[(REWRITE_RULE[MULT_LEFT_1,ADD1]
    	  (SPEC (--`1`--) (MATCH_MP DIV_MULT(SPEC_ALL ONE_LESS_TWO_EXP_SUC))))]
    	(PURE_REWRITE_RULE[ADD1] (MATCH_MP
    	 (GEN_ALL(UNDISCH (SPEC_ALL(SPEC (--`2 EXP (SUC n)`--) LESS_EQ_MONO_DIV))))
    	  (GQSPEC_ALL ADD_BV_BNVAL_LESS_EQ))))));

(* seg_pw =
    |- !w. PWORDLEN n w ==> (SUC k) <= n ==> PWORDLEN(SUC k)(WSEG(SUC k)0 w) *)

val seg_pw = GEN (--`w:'a word`--) (DISCH_ALL
    (REWRITE_RULE[ADD_0] (SPECL[(--`SUC k`--),(--`0`--)]
     (RESQ_SPEC_ALL (SPEC (--`n:num`--) WSEG_PWORDLEN))))) ;

(* bit_thm =
|- !w.
    PWORDLEN n w ==> (SUC k) <= n ==> (BIT k(WSEG(SUC k)0 w) = BIT k w) *)

val bit_thm = GEN (--`w:'a word`--) (DISCH_ALL
    (REWRITE_RULE[ADD_CLAUSES,LESS_SUC_REFL]
    (SPECL [(--`SUC k`--), (--`0`--),(--`k:num`--)](RESQ_SPEC_ALL(SPEC (--`n:num`--) BIT_WSEG)))));

(* seg_thm =
|- !w. PWORDLEN n w ==> (SUC k) <= n ==>
    (WSEG k 0(WSEG(SUC k)0 w) = WSEG k 0 w) *)

val seg_thm = GEN (--`w:'a word`--) (DISCH_ALL
    (REWRITE_RULE[ADD_CLAUSES,LESS_EQ_SUC_REFL]
    (SPECL [(--`SUC k`--), (--`0`--),(--`k:num`--),(--`0`--)](RESQ_SPEC_ALL(SPEC (--`n:num`--) WSEG_WSEG)))));

(* seg_pw_thm' = |- !w. PWORDLEN n w ==> k <= n ==> PWORDLEN k(WSEG k 0 w) *)

val seg_pw_thm' = GEN (--`w:bool word`--) (DISCH_ALL (REWRITE_RULE[ADD_CLAUSES]
    (GQSPECL [(--`n:num`--), (--`w:bool word`--), (--`k:num`--), (--`0`--)] WSEG_PWORDLEN)));

fun spec_thm th =
     (map (fn t => UNDISCH_ALL(ISPEC t th)) [(--`w2:bool word`--), (--`w1:bool word`--)]);

(* add_left =
PWORDLEN n w1, (SUC k) <= n, PWORDLEN n w2
|- (BNVAL(WSEG(SUC k)0 w1)) + (BNVAL(WSEG(SUC k)0 w2)) =
   (((BV(BIT k w1)) + (BV(BIT k w2))) 'a (2 EXP k)) +
   ((BNVAL(WSEG k 0 w1)) + (BNVAL(WSEG k 0 w2))) *)

val add_left =
    SUBS ((spec_thm bit_thm) @ (spec_thm seg_thm))
      (itlist (fn t1 => fn  t2 => RESQ_MATCH_MP t2 t1)
           (spec_thm seg_pw) (SPEC (--`k:num`--) ADD_BNVAL_LEFT));

(* less1_lem =
PWORDLEN n w1, k <= n, PWORDLEN n w2
|- ((((BV(BIT k w1)) + (BV(BIT k w2))) +
     (((BNVAL(WSEG k 0 w1)) + ((BNVAL(WSEG k 0 w2)) + (BV cin))) DIV
      (2 EXP k))) DIV 2) <= 1 *)

val less1_lem = itlist PROVE_HYP (spec_thm seg_pw_thm')
    (GQSPECL [(--`k:num`--), (--`BIT k (w1:bool word)`--),
              (--`BIT k (w2:bool word)`--), (--`cin:bool`--),
              (--`WSEG k 0 (w1:bool word)`--), (--`WSEG k 0 (w2:bool word)`--)]
       ADD_BV_BNVAL_DIV_LESS_EQ1);

(*-----------------------------------------------------------------------*)
(* ACARRY_EQ_ADD_DIV 	    	    					*)
(* We can now prove the ripple carry at position k (ACARRY k ...) is	*)
(* equal to the arithmetic carry resulting from adding the lower-order	*)
(* segments of the operands. 	    					*)
(*-----------------------------------------------------------------------*)

val ACARRY_EQ_ADD_DIV = store_thm("ACARRY_EQ_ADD_DIV",
    (--`!n. !w1 w2::PWORDLEN n. !k. k < n ==>
     (BV(ACARRY k w1 w2 cin) =
      (((BNVAL(WSEG k 0 w1)) + (BNVAL(WSEG k 0 w2)) + (BV cin)) DIV (2 EXP k)))`--),
    GEN_TAC THEN REPEAT RESQ_GEN_TAC
    THEN INDUCT_TAC THENL[
     REWRITE_TAC[WSEG0,BNVAL0,EXP,ADD,ACARRY_DEF,(num_CONV (--`1`--)),DIV_ONE],
     DISCH_TAC THEN PURE_ONCE_REWRITE_TAC[ACARRY_DEF]
     THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC]
     THEN MAP_EVERY IMP_RES_TAC [LESS_IMP_LESS_OR_EQ,seg_pw]
     THEN SUBST1_TAC add_left
     THEN CONV_TAC ((RAND_CONV o RATOR_CONV o RAND_CONV)
    	 (REWR_CONV (GSYM ADD_ASSOC)))
     THEN PURE_ONCE_REWRITE_TAC[EXP]
     THEN CONV_TAC ((RAND_CONV o RAND_CONV)(REWR_CONV MULT_SYM))
     THEN COND_REWRITE1_TAC (GSYM DIV_DIV_DIV_MULT) THENL[
      CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN MATCH_ACCEPT_TAC ZERO_LESS_EXP,
      CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN MATCH_ACCEPT_TAC LESS_0,
      COND_REWRITE1_TAC ADD_DIV_ADD_DIV
      THEN IMP_RES_TAC SUC_LESS THEN RES_THEN SUBST1_TAC
      THEN COND_REWRITE1_TAC BV_VB THENL[
       PURE_ONCE_REWRITE_TAC[LESS_EQ1_LESS2]
       THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
       THEN MATCH_ACCEPT_TAC less1_lem,
       PURE_ONCE_REWRITE_TAC[ADD_ASSOC] THEN REFL_TAC]]]);

(*-----------------------------------------------------------------------*)
(* The theorem asserting the equivalence ot the two addition methods.	*)
(*-----------------------------------------------------------------------*)

val ADD_WORD_SPLIT = store_thm("ADD_WORD_SPLIT",
    (--`!n1 n2. !w1 w2::PWORDLEN (n1 + n2). !cin.
     NBWORD (n1 + n2) ((BNVAL w1) + (BNVAL w2) + (BV cin)) =
     WCAT ((NBWORD n1 ((BNVAL (WSEG n1 n2 w1)) + (BNVAL (WSEG n1 n2 w2)) +
    	    	       (BV (ACARRY n2 w1 w2 cin)))),
    	   (NBWORD n2 ((BNVAL (WSEG n2 0 w1)) + (BNVAL (WSEG n2 0 w2)) +
    	    	       (BV cin))))`--),
     let val lem1 = itlist (fn t1 => fn t2 => RESQ_MATCH_MP t2 t1)
    	(map ASSUME [(--`PWORDLEN(n1 + (SUC n2))(w2:bool word)`--),
    	    (--`PWORDLEN(n1 + (SUC n2))(w1:bool word)`--)])
    	(SPECL[(--`n1:num`--), (--`SUC n2`--)] ADD_BNVAL_SPLIT)
     val wcat_11 =
         let val lm = (SPECL [(--`n1:num`--), (--`SUC n2`--)] WCAT_11)
    	 val lms = map (fn t => SPECL t PWORDLEN_NBWORD)
    	    [[(--`n1:num`--), (--`m11:num`--)],
             [(--`n1:num`--), (--`m12:num`--)],
    	     [(--`SUC n2`--), (--`m21:num`--)],
             [(--`SUC n2`--), (--`m22:num`--)]]
         in
    	  GENL[(--`m11:num`--), (--`m12:num`--),
               (--`m21:num`--), (--`m22:num`--)]
      	    (rev_itlist (fn t1 => fn t2 => RESQ_MATCH_MP t2 t1) lms lm)
        end
     val acarry_lem = SPEC (--`SUC n2`--)(RESQ_SPEC_ALL
    	  (SPEC (--`n1 + (SUC n2)`--) ACARRY_EQ_ADD_DIV))
   in
    GEN_TAC THEN INDUCT_TAC THENL[
     REWRITE_TAC[ADD_0,NBWORD0,WCAT0,ACARRY_DEF]
     THEN REPEAT RESQ_GEN_TAC THEN GEN_TAC
     THEN RESQ_REWRITE1_TAC WSEG_WORD_LENGTH THEN REFL_TAC,
     REPEAT RESQ_GEN_TAC THEN GEN_TAC
     THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC] THEN SUBST1_TAC lem1
     THEN PURE_ONCE_REWRITE_TAC[NBWORD_SPLIT]
     THEN PURE_ONCE_REWRITE_TAC[GSYM ADD_ASSOC]
     THEN COND_REWRITE1_TAC ADD_DIV_ADD_DIV THENL[
      CONV_TAC (ONCE_DEPTH_CONV num_CONV) THEN MATCH_ACCEPT_TAC ZERO_LESS_EXP,
      PURE_ONCE_REWRITE_TAC[wcat_11] THEN CONJ_TAC THENL[
       CONV_TAC ((RAND_CONV o RAND_CONV)(REWR_CONV ADD_ASSOC))
       THEN DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC
    	   (SPEC (--`n1 = 0`--) EXCLUDED_MIDDLE) THENL[
    	REWRITE_TAC[NBWORD0],
    	IMP_RES_THEN (ASSUME_TAC o (SPEC (--`SUC n2`--)))
    	  (PURE_ONCE_REWRITE_RULE[ADD_SYM] LESS_ADD_NONZERO)
        THEN FIRST_ASSUM (SUBST1_TAC o (MATCH_MP acarry_lem))
    	THEN REWRITE_TAC[ADD_ASSOC]],
       CONV_TAC (LHS_CONV (REWR_CONV (GSYM NBWORD_MOD)))
       THEN COND_REWRITE1_TAC MOD_TIMES
       THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC]
       THEN MATCH_ACCEPT_TAC NBWORD_MOD]]]
    end);

(*-----------------------------------------------------------------------*)
(* This theorem states the fact about taking a segment of the sum of	*)
(* two words.	    	    	    					*)
(*-----------------------------------------------------------------------*)

val WSEG_NBWORD_ADD = store_thm("WSEG_NBWORD_ADD",
    (--`!n. !w1 w2::PWORDLEN n. !m k cin. (m + k) <= n ==>
    (WSEG m k(NBWORD n ((BNVAL w1) + (BNVAL w2) + (BV cin))) =
     NBWORD m ((BNVAL (WSEG m k w1)) + (BNVAL (WSEG m k w2)) +
    	       (BV(ACARRY k w1 w2 cin))))`--),
    let val lem1 = RESQ_SPEC_ALL (CONV_RULE (COND_REWRITE1_CONV [] SUB_ADD)
    	(SPECL[(--`n - k`--), (--`k:num`--)] ADD_WORD_SPLIT))
    val lem2 = REWRITE_RULE[SUB_EQUAL_0,LESS_EQ_REFL]
                (ISPECL[(--`n-k`--),(--`k:num`--),
                      (--`w1:bool word`--),(--`w2:bool word`--),
    	(--`m:num`--),(--`k:num`--)](RESQ_REWR_CANON WSEG_WCAT_WSEG1))
    val lem3 = (CONV_RULE (COND_REWRITE1_CONV [] SUB_ADD)
    	(SPECL[(--`(n-k)-m`--), (--`m:num`--)] ADD_WORD_SPLIT))
    val PW_WSEG_TAC =
    	RESQ_IMP_RES_TAC WSEG_PWORDLEN THEN FIRST_ASSUM MATCH_MP_TAC
        THEN COND_REWRITE1_TAC SUB_ADD
    	THEN MATCH_ACCEPT_TAC LESS_EQ_REFL
   in
    GEN_TAC THEN REPEAT RESQ_GEN_TAC THEN REPEAT GEN_TAC
    THEN DISCH_TAC THEN IMP_RES_TAC LESS_EQ_SPLIT
    THEN PURE_ONCE_REWRITE_TAC[lem1]
    THEN COND_REWRITE1_TAC lem2 THENL[
     MATCH_ACCEPT_TAC PWORDLEN_NBWORD,
     MATCH_ACCEPT_TAC PWORDLEN_NBWORD,
     COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB) THEN FIRST_ASSUM ACCEPT_TAC,
     RESQ_REWRITE1_TAC lem3 THENL[
      PW_WSEG_TAC,
      PW_WSEG_TAC,
      RESQ_REWRITE1_TAC (SPEC (--`(n-k)-m`--) WSEG_WCAT2) THENL[
      MATCH_ACCEPT_TAC PWORDLEN_NBWORD,
      MATCH_ACCEPT_TAC PWORDLEN_NBWORD,
      RESQ_REWRITE1_TAC WSEG_WSEG THENL[
      COND_REWRITE1_TAC SUB_ADD THEN MATCH_ACCEPT_TAC LESS_EQ_REFL,
      PURE_ONCE_REWRITE_TAC[ADD_0]
       THEN COND_REWRITE1_TAC (GSYM ADD_LESS_EQ_SUB)
       THEN FIRST_ASSUM ACCEPT_TAC,
       REWRITE_TAC[ADD_0]]]]]
    end);

val ADD_NBWORD_EQ0_SPLIT = store_thm("ADD_NBWORD_EQ0_SPLIT",
    (--`!n1 n2. !w1 w2 :: PWORDLEN (n1 + n2). !cin.
     (NBWORD (n1+n2) ((BNVAL w1) + (BNVAL w2) + (BV cin)) = NBWORD (n1+n2) 0)
     =
     ((NBWORD n1 ((BNVAL (WSEG n1 n2 w1)) + (BNVAL (WSEG n1 n2 w2)) +
    	    	(BV (ACARRY n2 w1 w2 cin))) = NBWORD n1 0) /\
      (NBWORD n2 ((BNVAL (WSEG n2 0 w1)) + (BNVAL (WSEG n2 0 w2)) +
    	    	(BV cin)) = NBWORD n2 0))`--),
    REPEAT GEN_TAC THEN REPEAT RESQ_GEN_TAC THEN GEN_TAC
    THEN RESQ_REWRITE1_TAC ADD_WORD_SPLIT
    THEN RESQ_REWRITE1_TAC NBWORD_SPLIT
    THEN COND_REWRITE1_TAC ZERO_DIV THENL[
     MATCH_ACCEPT_TAC ZERO_LESS_TWO_EXP,
     RESQ_REWRITE1_TAC (SPECL [(--`n1:num`--), (--`n2:num`--)] WCAT_11)
     THEN ((MATCH_ACCEPT_TAC PWORDLEN_NBWORD) ORELSE REFL_TAC)]);

(*-----------------------------------------------------------------------*)
(* The theorem ACARRY_MSB states the value of the carry at the most 	*)
(* significant position.	    	    					*)
(*-----------------------------------------------------------------------*)

val VB_MOD_2 = prove((--`!n. VB(n MOD 2) = VB n`--),
    GEN_TAC THEN REWRITE_TAC[VB_DEF] THEN COND_REWRITE1_TAC MOD_MOD THENL[
     ACCEPT_TAC Less2,
     REFL_TAC]);

val ACARRY_MSB = store_thm("ACARRY_MSB",
    (--`!n. !w1 w2::PWORDLEN n. !cin.
     ACARRY n w1 w2 cin =
     BIT n (NBWORD (SUC n) ((BNVAL w1) + (BNVAL w2) + (BV cin)))`--),
    let val bit_lem = GEN_ALL
    	(itlist PROVE_HYP
    	 [(ISPEC (--`x:bool`--) PWORDLEN1),
              (SPECL [(--`SUC n`--),(--`m:num`--)] PWORDLEN_NBWORD)]
         (REWRITE_RULE[LESS_EQ_REFL,SUB_EQUAL_0,LESS_ADD_SUC,BIT0]
    	  (PURE_ONCE_REWRITE_RULE[ADD_SYM](SUBS[num_CONV (--`1`--)]
       	   (GQSPECL [(--`1`--),(--`SUC n`--),(--`WORD[x:bool]`--),
                     (--`NBWORD (SUC n) m`--), (--`SUC n`--)]
    	    BIT_WCAT_FST)))))
    val lem1 = MP (GQSPECL [(--`SUC n`--), (--`w1:bool word`--),
                            (--`w2:bool word`--),(--`n:num`--)]
    	      ACARRY_EQ_ADD_DIV) (SPEC (--`n:num`--) LESS_SUC_REFL)
    in
    INDUCT_TAC THEN REPEAT RESQ_GEN_TAC THENL[
     ASSUM_LIST (fn asl =>  SUBST_TAC (map (MATCH_MP PWORDLEN0) asl))
     THEN REWRITE_TAC[BNVAL_NVAL,NBWORD_SUC,NBWORD0,WCAT0,NVAL0,ADD,ACARRY_DEF]
     THEN PURE_REWRITE_TAC[MATCH_MP LESS_MOD (SPEC (--`cin:bool`--) BV_LESS_2)]
     THEN REWRITE_TAC[VB_BV,BIT0],
     GEN_TAC THEN PURE_ONCE_REWRITE_TAC[ACARRY_DEF]
     THEN PURE_ONCE_REWRITE_TAC[NBWORD_SUC_FST]
     THEN PURE_ONCE_REWRITE_TAC[bit_lem]
     THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC,EXP]
     THEN ASSUM_LIST (fn asl =>
        SUBST1_TAC (itlist (fn t1 => fn t2 => RESQ_MATCH_MP t2 t1)
    	(butlast asl) (SPEC (--`n:num`--) ADD_BNVAL_LEFT)))
     THEN COND_REWRITE1_TAC
    	 (GSYM (PURE_ONCE_REWRITE_RULE[MULT_SYM]DIV_DIV_DIV_MULT)) THENL[
      MATCH_ACCEPT_TAC ZERO_LESS_TWO_EXP,
      MATCH_ACCEPT_TAC Less2,
      CONV_TAC ((RAND_CONV o ONCE_DEPTH_CONV) (REWR_CONV (GSYM ADD_ASSOC)))
      THEN COND_REWRITE1_TAC ADD_DIV_ADD_DIV
      THEN SUBST1_TAC lem1 THEN REWRITE_TAC[VB_MOD_2]
      THEN CONV_TAC ((RAND_CONV o RAND_CONV o LHS_CONV o RAND_CONV)
    	 (ONCE_DEPTH_CONV (REWR_CONV (GSYM ADD_ASSOC))))
      THEN REFL_TAC]]
    end);

(*-----------------------------------------------------------------------*)
(* ACARRY_WSEG	    	    	    					*)
(*-----------------------------------------------------------------------*)

val ACARRY_WSEG = store_thm("ACARRY_WSEG",
    (--`!n. !w1 w2::PWORDLEN n. !cin k m. k < m /\ m <= n ==>
     (ACARRY k (WSEG m 0 w1) (WSEG m 0 w2) cin = ACARRY k w1 w2 cin)`--),
    let val bit_seg = RESQ_GEN_ALL
    	(REWRITE_RULE[LESS_MONO_EQ,LESS_EQ_MONO,ADD_CLAUSES]
    	(GQSPECL[(--`SUC n`--), (--`w:bool word`--),
                 (--`SUC m`--), (--`0`--), (--`k:num`--)] BIT_WSEG))
    in
    INDUCT_TAC THEN REPEAT RESQ_GEN_TAC THEN GEN_TAC THENL[
      REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)
      THEN IMP_RES_THEN SUBST1_TAC LESS_EQ_0_EQ
      THEN REWRITE_TAC[NOT_LESS_0],
      REPEAT INDUCT_TAC THEN REWRITE_TAC
    	[NOT_LESS_0,LESS_MONO_EQ,LESS_EQ_MONO,ACARRY_DEF]
      THEN STRIP_TAC THEN IMP_RES_TAC LESS_SUC THEN AP_TERM_TAC
      THEN RESQ_REWRITE1_TAC bit_seg THEN AP_THM_TAC THEN AP_TERM_TAC
      THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC]
      THEN PURE_ONCE_REWRITE_TAC[ADD_MONO_EQ] THEN AP_TERM_TAC
      THEN FIRST_ASSUM MATCH_MP_TAC
      THEN ASM_REWRITE_TAC[LESS_EQ_MONO]]
    end);

val ICARRY_WSEG = store_thm("ICARRY_WSEG",
    (--`!n. !w1 w2::PWORDLEN n. !cin k m. k < m /\ m <= n ==>
     (ICARRY k (WSEG m 0 w1) (WSEG m 0 w2) cin = ICARRY k w1 w2 cin)`--),
   let val i_eq_a = DISCH_ALL
     (SYM(UNDISCH_ALL(GQSPECL [(--`m:num`--),(--`WSEG m 0 (w1:bool word)`--),
     (--`WSEG m 0 (w2:bool word)`--), (--`cin:bool`--),(--`k:num`--)]  ACARRY_EQ_ICARRY)))
    in
    GEN_TAC THEN REPEAT RESQ_GEN_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC
    THEN COND_REWRITE1_TAC i_eq_a THENL[
      IMP_RES_TAC LESS_IMP_LESS_OR_EQ,
      RESQ_IMP_RES_TAC WSEG_PWORDLEN THEN FIRST_ASSUM MATCH_MP_TAC
      THEN ASM_REWRITE_TAC[ADD_0],
      RESQ_IMP_RES_TAC WSEG_PWORDLEN THEN FIRST_ASSUM MATCH_MP_TAC
      THEN ASM_REWRITE_TAC[ADD_0],
      RESQ_REWRITE1_TAC ACARRY_WSEG
      THEN RESQ_REWRITE1_TAC (SPEC (--`n:num`--) ACARRY_EQ_ICARRY) THENL[
    	IMP_RES_TAC LESS_EQ_TRANS, REFL_TAC]]
    end);

(*-----------------------------------------------------------------------*)
(* ACARRY_ACARRY_WSEG 	    	    					*)
(*-----------------------------------------------------------------------*)

val ACARRY_ACARRY_WSEG = store_thm("ACARRY_ACARRY_WSEG",
    (--`!n. !w1 w2::PWORDLEN n.
     !cin m k1 k2. k1 < m /\ k2 < n /\ (m + k2) <= n ==>
     (ACARRY k1 (WSEG m k2 w1) (WSEG m k2 w2) (ACARRY k2 w1 w2 cin) =
       ACARRY (k1 + k2) w1 w2 cin)`--),
    let val bit_seg = RESQ_GEN_ALL
    	(GQSPECL[(--`SUC n`--),(--`w:bool word`--),(--`SUC m`--),
                 (--`SUC k2`--),(--`k1:num`--)]BIT_WSEG)
    in
    INDUCT_TAC THEN REPEAT RESQ_GEN_TAC THEN GEN_TAC THENL[
     REWRITE_TAC[NOT_LESS_0],
     INDUCT_TAC THENL[
      REWRITE_TAC[NOT_LESS_0],
      INDUCT_TAC THENL[
       REWRITE_TAC[ADD,ACARRY_DEF],
       INDUCT_TAC THENL[
        PURE_ONCE_REWRITE_TAC[ADD_0,(CONJUNCT1 ACARRY_DEF)]
        THEN STRIP_TAC THEN MATCH_MP_TAC
    	 (GQSPECL [(--`SUC n`--), (--`w1:bool word`--),
                   (--`w2:bool word`--), (--`cin:bool`--),
    	    	  (--`SUC k1`--), (--`SUC m`--)] ACARRY_WSEG)
      THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC,
      STRIP_TAC THEN PURE_ONCE_REWRITE_TAC[ADD]
      THEN PURE_ONCE_REWRITE_TAC[ACARRY_DEF] THEN AP_TERM_TAC
      THEN AP_THM_TAC THEN AP_TERM_TAC THEN IMP_RES_TAC SUC_LESS
      THEN RESQ_REWRITE1_TAC bit_seg
      THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC]
      THEN PURE_ONCE_REWRITE_TAC[ADD_MONO_EQ] THEN AP_TERM_TAC
      THEN FIRST_ASSUM (IMP_RES_TAC o
    	 (PURE_ONCE_REWRITE_RULE[LESS_EQ_MONO]) o (SPEC (--`SUC k2`--)))]]]]
    end);

val _ = export_theory();
val _ = export_doc_theorems();
