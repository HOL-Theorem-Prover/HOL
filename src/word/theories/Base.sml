structure Base =
struct

local
 open numLib arithLib
 open rich_listTheory pairTheory arithmeticTheory prim_recTheory numTheory
 open HolKernel Parse basicHol90Lib Num_conv Num_induct
 infix THEN THENL |->;

in
val _ = Portable.output(Portable.std_out, "\nloading Base.\n");
val LESS_EQ_SPLIT = 
    let val asm_thm = ASSUME (--`(m + n) <= p`--)
    in
    GEN_ALL(DISCH_ALL
     (CONJ(MP(SPECL [(--`n:num`--),(--`m+n`--),(--`p:num`--)] LESS_EQ_TRANS)
       	      (CONJ (SUBS [SPECL [(--`n:num`--),(--`m:num`--)] ADD_SYM]
                     (SPECL [(--`n:num`--),(--`m:num`--)] LESS_EQ_ADD))
                    asm_thm))
	  (MP (SPECL [(--`m:num`--),(--`m+n`--),(--`p:num`--)] LESS_EQ_TRANS)
               (CONJ (SPEC_ALL LESS_EQ_ADD) asm_thm))))
    end;


val SUB_GREATER_EQ_ADD = prove(
    (--`!p n m. (p >= n) ==> (((p - n) >= m) = (p >= (m + n)))`--),
    REWRITE_TAC[
      SYM (SPEC (--`n:num`--) (SPEC (--`p-n`--) (SPEC (--`m:num`--) 
           (REWRITE_RULE[GSYM GREATER_EQ] LESS_EQ_MONO_ADD_EQ))))]
    THEN REPEAT STRIP_TAC
    THEN POP_ASSUM ( fn th  => ASSUME_TAC
      (MP (SPEC (--`n:num`--) (SPEC (--`p:num`--) SUB_ADD)) 
        (REWRITE_RULE[SPEC (--`n:num`--) (SPEC (--`p:num`--) GREATER_EQ)] th)))
    THEN SUBST_TAC[(SPEC_ALL ADD_SYM)] THEN ASM_REWRITE_TAC[]);

(*ba bb wa wb *)
(* ADD_LESS_EQ_SUB = |- !p n m. n <= p ==> ((n + m) <= p = m <= (p - n)) *)
val ADD_LESS_EQ_SUB = 
   GSYM (REWRITE_RULE[GREATER_EQ] SUB_GREATER_EQ_ADD);

(*wa *)
val ADD_LESS_EQ_TRANS = prove(
    (--`!m n p q. ((m + n) <= p) /\ (q <= n) ==> ((m + q) <= p)`--),
    INDUCT_TAC THEN PURE_ONCE_REWRITE_TAC[ADD]
      THENL[
      REPEAT GEN_TAC THEN PURE_ONCE_REWRITE_TAC[CONJ_SYM]
      THEN MATCH_ACCEPT_TAC LESS_EQ_TRANS,
      GEN_TAC THEN INDUCT_TAC THENL[
        REWRITE_TAC[NOT_SUC_LESS_EQ_0],
        PURE_ONCE_REWRITE_TAC[LESS_EQ_MONO] THEN REPEAT STRIP_TAC
        THEN RES_TAC]]);
(**)
val ADD_SUB_LEM = prove(
    (--`!m n p. p < n ==> ((m + n) - p = m + (n - p))`--),
    REPEAT INDUCT_TAC
    THEN ASM_REWRITE_TAC[NOT_LESS_0,ADD_CLAUSES,LESS_MONO_EQ,SUB_0]
   THEN DISCH_TAC THEN REWRITE_TAC[SUB_MONO_EQ]
   THEN REWRITE_TAC[SUB,LESS_MONO_EQ]
    THEN IMP_RES_THEN (ASSUME_TAC o (PURE_ONCE_REWRITE_RULE[ADD_SYM])
        o (SPEC(--`m:num`--))) LESS_IMP_LESS_ADD
    THEN DISJ_CASES_THEN2 (fn t => ASSUME_TAC t THEN RES_TAC)
                          (fn t => REWRITE_TAC[t])
        (REWRITE_RULE[DE_MORGAN_THM]
                     (SPECL[(--`p:num`--),(--`m + n`--)] LESS_ANTISYM))
    THEN RES_TAC THEN ASM_REWRITE_TAC[]);

(*ba wa wb *)
val LESS_EQ_0_EQ = prove(
    (--`!m. m <= 0 ==> (m = 0)`--),
    INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0]);

(*wb *)
val PRE_LESS_REFL = prove((--`!m . (0 < m) ==> (PRE m < m)`--),
  INDUCT_THEN INDUCTION MP_TAC THEN
  REWRITE_TAC [LESS_REFL,LESS_0,PRE,LESS_SUC_REFL]);

(*ba bn *)
(* LESS_DIV_EQ_ZERO = |- !r n. r < n ==> (r DIV n = 0) *)
val LESS_DIV_EQ_ZERO = 
    GENL [(--`r:num`--),(--`n:num`--)] (DISCH_ALL (PURE_REWRITE_RULE[MULT,ADD]
    (SPEC (--`0`--)(UNDISCH_ALL (SPEC_ALL  DIV_MULT)))));

(*bn *)
(* MULT_DIV = |- !n q. 0 < n ==> ((q * n) DIV n = q) *)
val MULT_DIV = 
    GEN_ALL (PURE_REWRITE_RULE[ADD_0]
    (CONV_RULE RIGHT_IMP_FORALL_CONV 
               (SPECL[(--`n:num`--),(--`0`--)] DIV_MULT)));

(* ba bn *)
val ADD_DIV_ADD_DIV = prove(
    (--`!n. 0 < n ==> !x r. ((((x * n) + r) DIV n) = x + (r DIV n))`--),
    CONV_TAC (REDEPTH_CONV RIGHT_IMP_FORALL_CONV)
    THEN REPEAT GEN_TAC THEN ASM_CASES_TAC (--`r < n`--) THENL[
      IMP_RES_THEN SUBST1_TAC LESS_DIV_EQ_ZERO THEN DISCH_TAC
      THEN PURE_ONCE_REWRITE_TAC[ADD_0]
      THEN MATCH_MP_TAC DIV_MULT THEN FIRST_ASSUM ACCEPT_TAC,
      DISCH_THEN (CHOOSE_TAC o (MATCH_MP (SPEC (--`r:num`--) DA)))
      THEN POP_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC)
      THEN SUBST1_TAC (ASSUME (--`r = (q * n) + r'`--))
      THEN PURE_ONCE_REWRITE_TAC[ADD_ASSOC]
      THEN PURE_ONCE_REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB]
      THEN IMP_RES_THEN (fn t => REWRITE_TAC[t]) DIV_MULT]);

(*bn *)
val NOT_MULT_LESS_0 = prove(
    (--`!m n. (0 < m) /\ (0 < n) ==> 0 < (m * n)`--),
    REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0]
    THEN STRIP_TAC THEN REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES,LESS_0]);

(*bn *)
val MOD_MULT_MOD = prove(
    (--`!m n. (0 < n) /\ (0 < m)  ==> !x. ((x MOD (n * m)) MOD n = x  MOD n)`--),
    REPEAT GEN_TAC THEN DISCH_TAC
    THEN FIRST_ASSUM (ASSUME_TAC o (MATCH_MP NOT_MULT_LESS_0)) THEN GEN_TAC
    THEN POP_ASSUM (CHOOSE_TAC o (MATCH_MP (SPECL [(--`x:num`--),(--`m * n`--)]DA)))
    THEN POP_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC)
    THEN SUBST1_TAC (ASSUME(--`x = (q * (n * m)) + r`--))
    THEN POP_ASSUM (SUBST1_TAC o (SPEC (--`q:num`--)) o (MATCH_MP MOD_MULT))
    THEN PURE_ONCE_REWRITE_TAC [MULT_SYM]
    THEN PURE_ONCE_REWRITE_TAC [GSYM MULT_ASSOC]
    THEN PURE_ONCE_REWRITE_TAC [MULT_SYM]
    THEN STRIP_ASSUME_TAC (ASSUME  (--`0 < n /\ 0 < m`--))
    THEN PURE_ONCE_REWRITE_TAC[UNDISCH_ALL(SPEC_ALL MOD_TIMES)]
    THEN REFL_TAC);

val MULT_RIGHT_1 = GEN_ALL (el 4 (CONJ_LIST 6 (SPEC_ALL MULT_CLAUSES)));

(*ba bn *)
(* |- !q. q DIV (SUC 0) = q *)
val DIV_ONE = 
    GEN_ALL (REWRITE_RULE[CONV_RULE (ONCE_DEPTH_CONV num_CONV) MULT_RIGHT_1]
    (MP (SPECL [(--`SUC 0`--), (--`q:num`--)] MULT_DIV) 
        (SPEC (--`0`--) LESS_0)));

val Less_lemma = prove(
    (--`!m n. m < n ==> ?p. (n = m + p) /\ 0 < p`--),
    GEN_TAC THEN INDUCT_TAC THENL[
      REWRITE_TAC[NOT_LESS_0],
      REWRITE_TAC[LESS_THM]
      THEN DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL[
    	EXISTS_TAC (--`1`--) THEN CONV_TAC ((RAND_CONV o RAND_CONV)num_CONV)
    	THEN REWRITE_TAC[LESS_0,ADD1],
    	RES_TAC THEN EXISTS_TAC (--`SUC p`--)
    	THEN ASM_REWRITE_TAC[ADD_CLAUSES,LESS_0]]]);

val Less_MULT_lemma = prove(
    (--`!r m p. 0 < p ==> (r < m) ==> (r < (p * m))`--),
    let val lem1 = MATCH_MP LESS_LESS_EQ_TRANS 
    	(CONJ (SPEC (--`m:num`--) LESS_SUC_REFL)
    	      (SPECL[(--`SUC m`--), (--`p * (SUC m)`--)] LESS_EQ_ADD))
   in
    GEN_TAC THEN REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0]
    THEN DISCH_TAC THEN REWRITE_TAC[LESS_THM]
    THEN DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC)
    THEN PURE_ONCE_REWRITE_TAC[MULT]
    THEN PURE_ONCE_REWRITE_TAC[ADD_SYM] THENL[
      ACCEPT_TAC lem1,
      ACCEPT_TAC (MATCH_MP LESS_TRANS (CONJ (ASSUME (--`r < m`--)) lem1))]
   end);

val Less_MULT_ADD_lemma = prove(
  (--`!m n r r'. 0 < m /\ 0 < n /\ r < m /\ r' < n ==> ((r' * m) + r) < (n * m)`--),
    REPEAT STRIP_TAC
    THEN CHOOSE_THEN STRIP_ASSUME_TAC (MATCH_MP Less_lemma (ASSUME (--`r < m`--)))
    THEN CHOOSE_THEN STRIP_ASSUME_TAC (MATCH_MP Less_lemma (ASSUME (--`r' < n`--)))
    THEN ASM_REWRITE_TAC[]
    THEN PURE_ONCE_REWRITE_TAC[RIGHT_ADD_DISTRIB]
    THEN PURE_ONCE_REWRITE_TAC[ADD_SYM]
    THEN PURE_ONCE_REWRITE_TAC[LESS_MONO_ADD_EQ]
    THEN SUBST1_TAC (SYM (ASSUME(--`m = r + p`--)))
    THEN IMP_RES_TAC Less_MULT_lemma);

(*ba bn *)
val DIV_DIV_DIV_MULT = prove(
    (--`!m n. (0 < m) /\ (0 < n)  ==> !x. ((x DIV m) DIV n = x  DIV (m * n))`--),
    CONV_TAC (ONCE_DEPTH_CONV RIGHT_IMP_FORALL_CONV) THEN REPEAT STRIP_TAC
    THEN REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)
    	(SPEC (--`x:num`--) (MATCH_MP DA (ASSUME (--`0 < m`--))))
    THEN REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)
    	(SPEC (--`q:num`--) (MATCH_MP DA (ASSUME (--`0 < n`--))))
    THEN IMP_RES_THEN (fn t => REWRITE_TAC[t]) DIV_MULT
    THEN IMP_RES_THEN (fn t => REWRITE_TAC[t]) DIV_MULT
    THEN PURE_ONCE_REWRITE_TAC[RIGHT_ADD_DISTRIB]
    THEN PURE_ONCE_REWRITE_TAC[GSYM MULT_ASSOC]
    THEN PURE_ONCE_REWRITE_TAC[GSYM ADD_ASSOC]
    THEN ASSUME_TAC (MATCH_MP NOT_MULT_LESS_0
    	(CONJ (ASSUME (--`0 < n`--)) (ASSUME (--`0 < m`--))))
    THEN CONV_TAC ((RAND_CONV o RAND_CONV) (REWR_CONV MULT_SYM))
    THEN CONV_TAC SYM_CONV THEN PURE_ONCE_REWRITE_TAC[ADD_INV_0_EQ]
    THEN FIRST_ASSUM (fn t => REWRITE_TAC[MATCH_MP ADD_DIV_ADD_DIV t])
    THEN PURE_ONCE_REWRITE_TAC[ADD_INV_0_EQ]
    THEN MATCH_MP_TAC LESS_DIV_EQ_ZERO
    THEN IMP_RES_TAC Less_MULT_ADD_lemma);

(*-----------------------------------------------------------------------*)
(* Derived inference rules   	    					 *)
(*-----------------------------------------------------------------------*)

val MATCH_EQ_MP = fn eq => fn lh => EQ_MP (PART_MATCH lhs eq (concl lh)) lh;

val REWRITE1_TAC = fn t => REWRITE_TAC[t];

fun ARITH_TAC (asml,gl) =
    let val a = filter is_presburger asml in
    (MAP_EVERY (MP_TAC o ASSUME) a THEN CONV_TAC ARITH_CONV)(asml,gl)
    end;

val ARITH_PROVE = EQT_ELIM o ARITH_CONV;


(* ----------------------------------------------------------------------
 * Some simple list reasoning functions, in order to avoid loading in the
 * entire library of lists.
 *---------------------------------------------------------------------------*)

fun WORD_ERR{function,message} = 
     HOL_ERR{origin_structure="Word library",
             origin_function = function,
             message = message};

open Rsyntax;

val % = Parse.term_parser;
val alpha_ty = ==`:'a`==
val bool_ty = ==`:bool`==


(* --------------------------------------------------------------------*)
(*   LIST_INDUCT: (thm # thm) -> thm			               *)
(*							               *)
(*     A1 |- t[[]]      A2 |- !tl. t[tl] ==> !h. t[CONS h t]           *)
(* ----------------------------------------------------------          *)
(*                   A1 u A2 |- !l. t[l]			       *)
(*							               *)
(* --------------------------------------------------------------------*)

fun LIST_INDUCT (base,step) =
   let val {Bvar,Body} = dest_forall(concl step)
       val {ant,conseq} = dest_imp Body
       val {Bvar=h,Body=con} = dest_forall conseq
       val P  = %`\^Bvar.^ant` 
       val b1 = genvar bool_ty
       val b2 = genvar bool_ty
       val base'  = EQ_MP (SYM(BETA_CONV (%`^P []`))) base 
       val step'  = DISCH ant (SPEC h (UNDISCH(SPEC Bvar step)))
       val hypth  = SYM(RIGHT_BETA(REFL (%`^P ^Bvar`)))
       val concth = SYM(RIGHT_BETA(REFL (%`^P(CONS ^h ^Bvar)`)))
       val IND    = SPEC P (INST_TYPE [{redex=alpha_ty, residue = type_of h}]
                                      list_INDUCT)
       val th1 = SUBST[b1 |-> hypth, b2 |-> concth]
                      (%`^(concl step') = (^b1 ==> ^b2)`)
                      (REFL (concl step'))
       val th2 = GEN Bvar (DISCH (%`^P ^Bvar`)
                                 (GEN h(UNDISCH (EQ_MP th1 step'))))
       val th3 = SPEC Bvar (MP IND (CONJ base' th2))
   in
   GEN Bvar (EQ_MP (BETA_CONV(concl th3)) th3)
   end
   handle _ => raise WORD_ERR{function="LIST_INDUCT", message = ""};


(* --------------------------------------------------------------------*)
(*							               *)
(* LIST_INDUCT_TAC					               *)
(*							               *)
(*             [A] !l.t[l]				               *)
(*  ================================			               *)
(*   [A] t[[]],  [A,t[l]] !h. t[CONS h t]		               *)
(*							               *)
(* --------------------------------------------------------------------*)

val LIST_INDUCT_TAC  = INDUCT_THEN list_INDUCT ASSUME_TAC;

(* --------------------------------------------------------------------*)
(*                                                                     *)
(* SNOC_INDUCT_TAC                                                     *)
(*                                                                     *)
(*             [A] !l.t[l]                                             *)
(*  ================================                                   *)
(*   [A] t[[]],  [A,t[l]] !h. t[SNOC x t]                              *)
(*                                                                     *)
(* --------------------------------------------------------------------*)
(* PC 11/7/94 *)

val SNOC_INDUCT_TAC = INDUCT_THEN SNOC_INDUCT ASSUME_TAC;


(* --------------------------------------------------------------------*)
(* Definition by primitive recursion for lists		               *)
(* (For compatibility of new/old HOL.)			               *)
(* --------------------------------------------------------------------*)

local val list_Axiom = listTheory.list_Axiom
in
fun new_list_rec_definition (name,tm) =
  new_recursive_definition{name=name,rec_axiom=list_Axiom,def=tm,fixity=Prefix}

fun new_infix_list_rec_definition (name,tm,prec) =
   new_recursive_definition {name=name,rec_axiom=list_Axiom,def=tm,
                             fixity=Infix prec}
end;


(* ------------------------------------------------------------------------- *)
(* EQ_LENGTH_INDUCT_TAC : tactic                                             *)
(*  A ?- !l1 l2. (LENGTH l1 = LENGTH l2) ==> t[l1, l2]                       *)
(* ==================================================== EQ_LENGTH_INDUCT_TAC *)
(*  A                       ?- t[ []/l1, []/l2 ]                             *)
(*  A,LENGTH l1 = LENGTH l2 ?- t[(CONS h l1)/l1,(CONS h' l2)/l2]             *)
(* ------------------------------------------------------------------------- *)

val EQ_LENGTH_INDUCT_TAC =
 LIST_INDUCT_TAC THENL[
 LIST_INDUCT_TAC THENL[
   REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_THEN (K ALL_TAC),
   REWRITE_TAC[LENGTH,SUC_NOT]],
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,NOT_SUC,INV_SUC_EQ]
   THEN GEN_TAC THEN REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_TAC];


(* ------------------------------------------------------------------------- *)
(* EQ_LENGTH_SNOC_INDUCT_TAC : tactic                                        *)
(* A ?- !l1 l2.(LENGTH l1 = LENGTH l2) ==> t[l1,l2]                          *)
(* =============================================== EQ_LENGTH_SNOC_INDUCT_TAC *)
(*  A                       ?- t[ []/l1, []/l2 ]                             *)
(*  A,LENGTH l1 = LENGTH l2 ?- t[(SNOC h l1)/l1,(SNOC h' l2)/l2]             *)
(* ------------------------------------------------------------------------- *)

val EQ_LENGTH_SNOC_INDUCT_TAC =
    SNOC_INDUCT_TAC THENL[
     SNOC_INDUCT_TAC THENL[
      REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_THEN (K ALL_TAC),
      REWRITE_TAC[LENGTH,LENGTH_SNOC,SUC_NOT]],
     GEN_TAC THEN SNOC_INDUCT_TAC
     THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,NOT_SUC,INV_SUC_EQ]
     THEN GEN_TAC THEN REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_TAC];

end (* local *)

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;

end;
