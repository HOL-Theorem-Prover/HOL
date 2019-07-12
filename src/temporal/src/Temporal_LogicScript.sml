(*
  app load ["tautLib", "numLib", "pairLib", "schneiderUtils"];
*)

open HolKernel Parse boolLib numLib pairLib
     numTheory prim_recTheory arithmeticTheory pairTheory
     Rsyntax schneiderUtils;

val _ = new_theory "Temporal_Logic";
val _ = ParseExtras.temp_loose_equality()

fun TAC_PROOF(g,t) = Tactical.TAC_PROOF(g,t) handle e => Raise e;

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;



(* ************************************************************ *)
(*              Definitions via Hardware-Formulae               *)
(* ************************************************************ *)


val NEXT     = new_definition("NEXT", “NEXT P = \t. P(SUC t):bool”);

val ALWAYS   = new_definition("ALWAYS", “ALWAYS P t0 = !t:num.P(t+t0)”);

val EVENTUAL = new_definition("EVENTUAL", “EVENTUAL P t0 = ?t:num.P(t+t0)”);

val WATCH = new_infixr_definition("WATCH",
  “$WATCH q b t0 =
          !t. (q t0 = F) /\ (q (SUC (t+t0)) = (q (t+t0) \/ b (t+t0)))”,200);

val UPTO = new_definition("UPTO",
        “UPTO(t0,t1,a) =
                !t2.  t0<=t2 /\ t2<t1 ==> a t2”);

val WHEN = new_infixr_definition("WHEN",
        “$WHEN a b t0 =
                ?q. (q WATCH b) t0
                  /\ !t.(q(t+t0) \/ (b(t+t0) ==> a(t+t0)))”,200);

val UNTIL = new_infixr_definition("UNTIL",
        “$UNTIL a b t0 =
                ?q. (q WATCH b) t0
                  /\ !t.(q (t+t0) \/ b(t+t0) \/ a(t+t0)) ”,200);

val BEFORE = new_infixr_definition("BEFORE",
        “$BEFORE a b t0 =
                ?q. (q WATCH b) t0
                  /\ ((?t.~q(t+t0) /\ ~b(t+t0) /\ a(t+t0))
                      \/ !t.~b(t+t0)) ”,200);

val SWHEN = new_infixr_definition("SWHEN",
        “$SWHEN a b t0 =
                ?q. (q WATCH b) t0
                  /\ ?t.~q(t+t0) /\ b(t+t0) /\ a(t+t0)”,200);

val SUNTIL = new_infixr_definition("SUNTIL",
        “$SUNTIL a b t0 =
                ?q. (q WATCH b) t0
                  /\ (!t.q (t+t0) \/ b(t+t0) \/ a(t+t0))
                  /\ (?t. b(t+t0))”,200);

val SBEFORE = new_infixr_definition("SBEFORE",
        “$SBEFORE a b t0 =
                ?q. (q WATCH b) t0
                  /\ (?t.~q(t+t0) /\ ~b(t+t0) /\ a(t+t0))”,200);


(* %%%%%% use "lemmata.sml"; %%%%%%%%%% *)

(* ************************************************************ *)
(*              General Lemmata                                 *)
(* ************************************************************ *)

val WATCH_EXISTS = TAC_PROOF(([],“!b.!t0.?q. (q WATCH b) t0”),
    let val lem1 = INST_TYPE[alpha |-> bool] num_Axiom_old
        val lem2 = SPECL [“F”,“\z t. z \/ b(t:num)”] lem1
        val lem3 = EXISTENCE (BETA_RULE lem2)
        val lem4 = BETA_RULE(SPEC “\t.b(t+t0):bool” (GEN “b:num->bool” lem3))
     in PURE_REWRITE_TAC[WATCH] THEN REPEAT GEN_TAC
        THEN ASSUME_TAC lem4 THEN LEFT_EXISTS_TAC
        THEN EXISTS_TAC “\t.fn1(t-t0):bool”
        THEN BETA_TAC THEN REWRITE_TAC[]
        THEN ASM_REWRITE_TAC[SYM(SPEC_ALL(CONJUNCT2 ADD)),SUB_EQUAL_0,ADD_SUB]
    end)



val WELL_ORDER = TAC_PROOF(
        ([],“(?n.P n) = (?m.P m /\ !n. n<m ==> ~P n)”),
        EQ_TAC THENL[REWRITE_TAC[WOP],
                     STRIP_TAC THEN EXISTS_TAC “m:num”
                     THEN ASM_REWRITE_TAC[]])


val WELL_ORDER_UNIQUE = TAC_PROOF(
        ([],“!m2 m1 P.
               (P m1 /\ !n. n<m1 ==> ~P n) /\
               (P m2 /\ !n. n<m2 ==> ~P n) ==> (m1 = m2)”),
        REPEAT GEN_TAC THEN STRIP_TAC
        THEN DISJ_CASES_TAC(SPECL[“m1:num”,“m2:num”]LESS_LESS_CASES)
        THENL[ASM_REWRITE_TAC[],POP_ASSUM DISJ_CASES_TAC THEN RES_TAC])



Theorem DELTA_CASES:
  (?d. (!t. t<d ==> ~b(t+t0)) /\ b(d+t0)) \/ !d. ~b(d+t0)
Proof
  SUBST1_TAC (SYM(NOT_EXISTS_CONV “~?d.b(d+t0)”))
  THEN ONCE_REWRITE_TAC[BETA_RULE(SPEC “\t.b(t+t0):bool” (GEN_ALL WELL_ORDER))]
  THEN RIGHT_DISJ_TAC
  THEN ONCE_REWRITE_TAC[CONJ_COMM]
  THEN ASM_REWRITE_TAC[]
QED



(* ************************************************************ *)
(*                      Implicational Forms                     *)
(* ************************************************************ *)

val WHEN_IMP = TAC_PROOF(
        ([],“(a WHEN b) t0 =  !q. (q WATCH b) t0 ==>
                                    !t.(q(t+t0) \/ (b(t+t0) ==> a(t+t0)))”),
        REWRITE_TAC[WHEN,WATCH] THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[MY_MP_TAC “!t. q'(t+t0):bool = q(t+t0)”
              THENL[INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES],
                    DISCH_TAC THEN ASM_REWRITE_TAC[]],
              ASSUME_TAC(SPEC_ALL WATCH_EXISTS)
              THEN LEFT_EXISTS_TAC
              THEN RULE_ASSUM_TAC(REWRITE_RULE[WATCH])
              THEN EXISTS_TAC“q:num->bool”
              THEN LEFT_NO_FORALL_TAC 1 “q:num->bool”
              THEN ASM_REWRITE_TAC[] THEN RES_TAC])


val UNTIL_IMP = TAC_PROOF(
        ([],“(a UNTIL b) t0 =  !q. (q WATCH b) t0 ==>
                                    !t.(q(t+t0) \/ b(t+t0) \/ a(t+t0))”),
        REWRITE_TAC[UNTIL,WATCH] THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[MY_MP_TAC “!t. q'(t+t0):bool = q(t+t0)”
              THENL[INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES],
                    DISCH_TAC THEN ASM_REWRITE_TAC[]],
              ASSUME_TAC(SPEC_ALL WATCH_EXISTS)
              THEN LEFT_EXISTS_TAC
              THEN RULE_ASSUM_TAC(REWRITE_RULE[WATCH])
              THEN EXISTS_TAC“q:num->bool”
              THEN LEFT_NO_FORALL_TAC 1 “q:num->bool”
              THEN ASM_REWRITE_TAC[] THEN RES_TAC])



val BEFORE_IMP = TAC_PROOF(
        ([],“(a BEFORE b) t0 =
                !q. (q WATCH b) t0 ==>
                        ((?t.~q(t+t0)/\~b(t+t0)/\a(t+t0)) \/ (!t.~b(t+t0)))”),
        REWRITE_TAC[BEFORE,WATCH] THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[
            MY_MP_TAC “!t. q'(t+t0):bool = q(t+t0)”
            THENL[
                INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES],
                DISCH_TAC THEN ASM_REWRITE_TAC[]]
            THEN DISJ1_TAC THEN EXISTS_TAC “t:num”
            THEN ASM_REWRITE_TAC[],
            ASM_REWRITE_TAC[],
            ASSUME_TAC(SPEC_ALL WATCH_EXISTS)
            THEN LEFT_EXISTS_TAC
            THEN RULE_ASSUM_TAC(REWRITE_RULE[WATCH])
            THEN EXISTS_TAC“q:num->bool”
            THEN LEFT_NO_FORALL_TAC 1 “q:num->bool”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]])



val SWHEN_IMP = TAC_PROOF(
        ([],“(a SWHEN b) t0 =
                        !q. (q WATCH b) t0 ==>
                                    ?t.~q(t+t0) /\ b(t+t0) /\ a(t+t0)”),
        REWRITE_TAC[SWHEN,WATCH] THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[
            MY_MP_TAC “!t. q'(t+t0):bool = q(t+t0)”
            THENL[
                INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES],
                DISCH_TAC]
            THEN EXISTS_TAC“t:num” THEN ASM_REWRITE_TAC[],
            ASSUME_TAC(SPEC_ALL WATCH_EXISTS)
            THEN LEFT_EXISTS_TAC
            THEN RULE_ASSUM_TAC(REWRITE_RULE[WATCH])
            THEN EXISTS_TAC“q:num->bool”
            THEN LEFT_NO_FORALL_TAC 1 “q:num->bool”
            THEN RES_TAC THEN ASM_REWRITE_TAC[]
            THEN EXISTS_TAC“t:num” THEN ASM_REWRITE_TAC[]])


val SUNTIL_IMP = TAC_PROOF(
        ([],“(a SUNTIL b) t0 =
                        !q. (q WATCH b) t0 ==>
                                    (!t.q(t+t0) \/ b(t+t0) \/ a(t+t0))
                                 /\ ?t. b(t+t0)”),
        REWRITE_TAC[SUNTIL,WATCH] THEN BETA_TAC
        THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC
        THEN ASM_REWRITE_TAC[]
        THENL[
            MY_MP_TAC “!t. q'(t+t0):bool = q(t+t0)”
            THENL[
                INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES],
                DISCH_TAC THEN ASM_REWRITE_TAC[]],
            EXISTS_TAC“t:num” THEN ASM_REWRITE_TAC[],
            ASSUME_TAC(SPEC_ALL WATCH_EXISTS)
            THEN LEFT_EXISTS_TAC
            THEN RULE_ASSUM_TAC(REWRITE_RULE[WATCH])
            THEN EXISTS_TAC“q:num->bool”
            THEN LEFT_NO_FORALL_TAC 1 “q:num->bool”
            THEN RES_TAC THEN ASM_REWRITE_TAC[]
            THEN EXISTS_TAC“t:num” THEN ASM_REWRITE_TAC[]])


val SBEFORE_IMP = TAC_PROOF(
        ([],“(a SBEFORE b) t0 =
                        !q. (q WATCH b) t0 ==>
                                (?t.~q(t+t0)/\~b(t+t0)/\a(t+t0))”),
        REWRITE_TAC[SBEFORE,WATCH] THEN BETA_TAC
        THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC
        THEN ASM_REWRITE_TAC[]
        THENL[
            MY_MP_TAC “!t. q'(t+t0):bool = q(t+t0)”
            THENL[
                INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES],
                DISCH_TAC]
            THEN EXISTS_TAC “t:num” THEN ASM_REWRITE_TAC[],
            ASSUME_TAC(SPEC_ALL WATCH_EXISTS)
            THEN LEFT_EXISTS_TAC
            THEN RULE_ASSUM_TAC(REWRITE_RULE[WATCH])
            THEN EXISTS_TAC“q:num->bool”
            THEN LEFT_NO_FORALL_TAC 1 “q:num->bool”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]]);



(* ************************************************************ *)
(*                      Signal Theorems                         *)
(* ************************************************************ *)


val ALWAYS_SIGNAL = TAC_PROOF(
        ([],“ALWAYS a t0 = (!t. a(t+t0))”),
        REWRITE_TAC[ALWAYS])


val EVENTUAL_SIGNAL = TAC_PROOF(
        ([],“EVENTUAL a t0 = (?t. a(t+t0))”),
        REWRITE_TAC[EVENTUAL])




Theorem WATCH_SIGNAL:
   (q WATCH b) t0 <=>
                ((!t. ~b(t+t0)) ==> (!t. ~q(t+t0))) /\
                (!d. b(d+t0) /\ (!t. t<d ==> ~b(t+t0)) ==>
                        (!t. t<=d ==> ~q(t+t0)) /\ (!t. q(SUC(t+(d+t0)))))
Proof
        PURE_REWRITE_TAC[WATCH]
        THEN RIGHT_LEMMA_DISJ_CASES_TAC DELTA_CASES THEN ASM_REWRITE_TAC[]
        THENL[ALL_TAC,
              EQ_TAC THEN DISCH_TAC
              THENL[
                INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES],
                ASM_REWRITE_TAC[] THEN GEN_TAC THEN CONJ_TAC
                THENL[LEFT_FORALL_TAC “0”,LEFT_FORALL_TAC “SUC t”]
                THEN UNDISCH_HD_TAC THEN REWRITE_TAC[ADD_CLAUSES]]]
        THEN EQ_TAC THEN STRIP_TAC
        THENL[
        GEN_TAC THEN STRIP_TAC THEN LEFT_CONJ_TAC
        THENL[
            INDUCT_TAC THEN ASM_REWRITE_TAC[ZERO_LESS_EQ,ADD_CLAUSES]
            THEN DISCH_TAC THEN IMP_RES_TAC OR_LESS
            THEN IMP_RES_TAC LESS_IMP_LESS_OR_EQ
            THEN RES_TAC THEN ASM_REWRITE_TAC[],
            INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
            THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV“SUC(t+(d'+t0))=SUC(t+d')+t0”))
            THEN ASM_REWRITE_TAC[ADD_CLAUSES,SYM(SPEC_ALL ADD_ASSOC)]],
        ALL_TAC]
        THEN RES_TAC THEN POP_NO_TAC 2 THEN POP_NO_TAC 2
        THEN GEN_TAC THEN CONJ_TAC
        THENL[LEFT_NO_FORALL_TAC 1 “0” THEN UNDISCH_HD_TAC
              THEN REWRITE_TAC[ADD_CLAUSES,ZERO_LESS_EQ],
              ALL_TAC]
        THEN DISJ_CASES_TAC (SPECL[“d:num”,“t:num”]LESS_LESS_CASES)
        THENL[POP_ASSUM(SUBST1_TAC o SYM) THEN LEFT_FORALL_TAC “0”
              THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])
              THEN ASM_REWRITE_TAC[],
              ALL_TAC]
        THEN POP_ASSUM DISJ_CASES_TAC
        THENL[IMP_RES_TAC LESS_ADD_1 THEN POP_ASSUM SUBST1_TAC
              THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV“(d+(p+1))+t0=SUC(p+(d+t0))”))
              THEN ASM_REWRITE_TAC[]
              THEN LEFT_NO_FORALL_TAC 1 “SUC p” THEN UNDISCH_HD_TAC
              THEN REWRITE_TAC[ADD_CLAUSES],
              IMP_RES_TAC LESS_IMP_LESS_OR_EQ THEN IMP_RES_TAC LESS_OR
              THEN RES_TAC THEN UNDISCH_NO_TAC 2
              THEN ASM_REWRITE_TAC[ADD_CLAUSES]])



val WHEN_SIGNAL = prove(
  “(a WHEN b) t0 =
     !delta.((!t. t<delta ==> ~b(t+t0)) /\ b(delta+t0) ==> a(delta+t0))”,
  PURE_REWRITE_TAC[WHEN,WATCH_SIGNAL]
  >> RIGHT_LEMMA_DISJ_CASES_TAC DELTA_CASES >> ASM_REWRITE_TAC[]
  THENL[ALL_TAC, EXISTS_TAC“\t:num.F” >> BETA_TAC >> REWRITE_TAC[]]
  >> EQ_TAC >> STRIP_TAC
  THENL[
      GEN_TAC >> LEFT_NO_FORALL_TAC 1 “delta:num”
      >> STRIP_TAC >> RES_TAC
      >> LEFT_NO_FORALL_TAC 5 “delta:num”
      >> LEFT_NO_FORALL_TAC 2 “delta:num”
      >> RULE_ASSUM_TAC (REWRITE_RULE[LESS_EQ_REFL])
      >> POP_ASSUM (fn x=> RULE_ASSUM_TAC (REWRITE_RULE[x]))
      >> UNDISCH_HD_TAC >> ASM_REWRITE_TAC[],
      ASSUME_TAC (SPEC_ALL(REWRITE_RULE[WATCH_SIGNAL]WATCH_EXISTS))
      >> LEFT_EXISTS_TAC >> EXISTS_TAC “q:num->bool”
      >> UNDISCH_HD_TAC >> ASM_REWRITE_TAC[] >> STRIP_TAC
      >> ASM_REWRITE_TAC[]
      >> LEFT_FORALL_TAC “d:num” >> RES_TAC >> POP_NO_TAC 3
      >> POP_NO_TAC 3
      >> GEN_TAC >> DISJ_CASES_TAC (SPECL[“t:num”,“d:num”]LESS_LESS_CASES)
      THENL[POP_ASSUM SUBST1_TAC >> ASM_REWRITE_TAC[],
            POP_ASSUM DISJ_CASES_TAC]
      THENL[IMP_RES_TAC LESS_IMP_LESS_OR_EQ,
            IMP_RES_TAC LESS_ADD_1 >> POP_ASSUM SUBST1_TAC
            >> SUBST1_TAC(EQT_ELIM(ARITH_CONV“(d+(p+1))+t0 = (SUC(p+(d+t0)))”))]
      >> RES_TAC >> ASM_REWRITE_TAC[]])




val UNTIL_SIGNAL = TAC_PROOF(
  ([],“(a UNTIL b) t0 =
           (((!t. ~b(t+t0)) ==> (!t. a(t+t0))) /\
            (!d. (!t.t<d ==> ~b(t+t0)) /\ b(d+t0) ==> (!t. t<d ==> a(t+t0))))”),
  PURE_REWRITE_TAC[UNTIL,WATCH_SIGNAL,ALWAYS]
  >> RIGHT_LEMMA_DISJ_CASES_TAC DELTA_CASES >> ASM_REWRITE_TAC[]
  THENL[ALL_TAC,
        EQ_TAC >> STRIP_TAC
        THENL[UNDISCH_HD_TAC >> ASM_REWRITE_TAC[],
              EXISTS_TAC “\t:num.F” >> BETA_TAC
              >> ASM_REWRITE_TAC[]]]
  >> EQ_TAC >> STRIP_TAC
  THENL[
      GEN_TAC >> STRIP_TAC
      >> LEFT_NO_FORALL_TAC 3 “d':num” >> RES_TAC
      >> POP_NO_TAC 2
      >> GEN_TAC >> DISCH_TAC
      >> IMP_RES_TAC LESS_IMP_LESS_OR_EQ >> RES_TAC
      >> LEFT_NO_FORALL_TAC 8 “t:num”
      >> UNDISCH_HD_TAC >> ASM_REWRITE_TAC[],
      ASSUME_TAC (SPEC_ALL(REWRITE_RULE[WATCH_SIGNAL]WATCH_EXISTS))
      >> LEFT_EXISTS_TAC >> EXISTS_TAC “q:num->bool”
      >> UNDISCH_HD_TAC >> ASM_REWRITE_TAC[] >> STRIP_TAC
      >> ASM_REWRITE_TAC[]
      >> LEFT_FORALL_TAC “d:num” >> RES_TAC >> POP_NO_TAC 3 >> POP_NO_TAC 3
      >> GEN_TAC >> DISJ_CASES_TAC (SPECL[“t:num”,“d:num”]LESS_LESS_CASES)
      THENL[POP_ASSUM SUBST1_TAC >> ASM_REWRITE_TAC[],POP_ASSUM DISJ_CASES_TAC]
      THENL[IMP_RES_TAC LESS_IMP_LESS_OR_EQ,
            IMP_RES_TAC LESS_ADD_1 >> POP_ASSUM SUBST1_TAC
            >> SUBST1_TAC(EQT_ELIM(ARITH_CONV“(d+(p+1))+t0 = (SUC(p+(d+t0)))”))]
      >> RES_TAC >> ASM_REWRITE_TAC[]])



val BEFORE_SIGNAL = TAC_PROOF(
  ([],“(a BEFORE b) t0
          = !delta.
                  ((!t. t<delta ==> ~b(t+t0)) /\ b(delta+t0))
                          ==> ?t. t<delta /\ a(t+t0)”),
  REWRITE_TAC[BEFORE,WATCH] THEN EQ_TAC THEN REPEAT STRIP_TAC
  THENL[
      EXISTS_TAC “t:num” THEN ASM_REWRITE_TAC[]
      THEN MY_MP_TAC “!t.q(SUC((t+delta)+t0)):bool”
      THENL[
          INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
          THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
          THEN STRIP_TAC THEN ASM_REWRITE_TAC[],
          DISCH_TAC]
      THEN DISJ_CASES_TAC(SPECL[“t:num”,“delta:num”]LESS_CASES)
      THEN ASM_REWRITE_TAC[] THEN UNDISCH_HD_TAC
      THEN REWRITE_TAC[LESS_OR_EQ] THEN STRIP_TAC
      THENL[
          IMP_RES_TAC LESS_ADD_1 THEN LEFT_NO_FORALL_TAC 2 “p:num”
          THEN UNDISCH_HD_TAC THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
                          “(t=delta+(p+1)) ==> (SUC((p+delta)+t0) = t+t0)”))
          THEN POP_ASSUM REWRITE1_TAC THEN ASM_REWRITE_TAC[],
          UNDISCH_NO_TAC 2 THEN ASM_REWRITE_TAC[]],
      UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[],
      ASSUME_TAC(SPEC_ALL(REWRITE_RULE[WATCH]WATCH_EXISTS))
      THEN LEFT_EXISTS_TAC THEN EXISTS_TAC“q:num->bool”
      THEN ASM_REWRITE_TAC[] THEN DISJ_CASES_TAC DELTA_CASES
      THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN LEFT_EXISTS_TAC
      THEN LEFT_NO_FORALL_TAC 2 “d:num” THEN UNDISCH_HD_TAC
      THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC “t:num”
      THEN RES_TAC THEN ASM_REWRITE_TAC[]
      THEN MY_MP_TAC “!t. t<d ==> ~q(t+t0)”
      THENL[
          INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
          THEN DISCH_TAC THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
                          “(SUC t < d) ==> t < d”))
          THEN RES_TAC THEN ASM_REWRITE_TAC[],
          DISCH_TAC]
      THEN POP_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);

val SWHEN_SIGNAL = TAC_PROOF(
  ([],“(a SWHEN b) t0 =
          ?delta. (!t. t<delta ==> ~b(t+t0)) /\ b(delta+t0) /\ a(delta+t0)”),
  REWRITE_TAC[SWHEN] THEN EQ_TAC THEN STRIP_TAC
  THENL[
      RULE_ASSUM_TAC(REWRITE_RULE[WATCH_SIGNAL])
      THEN UNDISCH_NO_TAC 3 THEN DISJ_CASES_TAC DELTA_CASES
      THEN RES_TAC THEN LEFT_EXISTS_TAC
      THEN STRIP_TAC THEN LEFT_FORALL_TAC “d:num”
      THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
      THEN MY_MP_TAC “d=(t:num)”
      THENL[
          DISJ_CASES_TAC(SPECL[“t:num”,“d:num”]LESS_CASES)
          THEN RES_TAC THEN UNDISCH_HD_TAC THEN REWRITE_TAC[LESS_OR_EQ]
          THEN STRIP_TAC THEN IMP_RES_TAC LESS_ADD_1 THEN UNDISCH_NO_TAC 8
          THEN POP_ASSUM SUBST1_TAC
          THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV“(d+(p+1))+t0 = SUC(p+(d+t0))”))
          THEN ASM_REWRITE_TAC[],
          DISCH_TAC]
      THEN POP_ASSUM(fn x=> RULE_ASSUM_TAC(REWRITE_RULE[SYM x]))
      THEN EXISTS_TAC“d:num” THEN ASM_REWRITE_TAC[],
      ASSUME_TAC(SPEC_ALL WATCH_EXISTS) THEN LEFT_EXISTS_TAC
      THEN EXISTS_TAC “q:num->bool” THEN ASM_REWRITE_TAC[]
      THEN EXISTS_TAC“delta:num” THEN ASM_REWRITE_TAC[]
      THEN RULE_ASSUM_TAC(REWRITE_RULE[WATCH_SIGNAL])
      THEN UNDISCH_HD_TAC THEN STRIP_TAC
      THEN LEFT_FORALL_TAC “delta:num” THEN UNDISCH_HD_TAC
      THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
      THEN POP_NO_ASSUM 1 MATCH_MP_TAC
      THEN CONV_TAC ARITH_CONV])




Theorem SUNTIL_SIGNAL:
  (a SUNTIL b) t0 =
          ?delta. (!t. t<delta ==> a(t+t0) /\~b(t+t0)) /\ b(delta+t0)
Proof
  REWRITE_TAC[SUNTIL] >> EQ_TAC >> STRIP_TAC
  THENL[
      RULE_ASSUM_TAC(REWRITE_RULE[WATCH_SIGNAL])
      >> UNDISCH_NO_TAC 2 >> DISJ_CASES_TAC DELTA_CASES
      THENL[LEFT_EXISTS_TAC, UNDISCH_NO_TAC 1 >> ASM_REWRITE_TAC[]]
      >> STRIP_TAC >> LEFT_FORALL_TAC “d:num”
      >> UNDISCH_HD_TAC >> ASM_REWRITE_TAC[] >> DISCH_TAC
      >> EXISTS_TAC “d:num” >> ASM_REWRITE_TAC[]
      >> GEN_TAC >> STRIP_TAC
      >> IMP_RES_TAC(EQT_ELIM(ARITH_CONV“x<y==>x<=y”))
      >> RES_TAC >> LEFT_NO_FORALL_TAC 8 “t':num”
      >> UNDISCH_HD_TAC >> ASM_REWRITE_TAC[] ,
      ASSUME_TAC(SPEC_ALL WATCH_EXISTS) >> LEFT_EXISTS_TAC
      >> EXISTS_TAC “q:num->bool” >> ASM_REWRITE_TAC[]
      >> CONJ_TAC
      THENL[ALL_TAC, EXISTS_TAC“delta:num” >> ASM_REWRITE_TAC[]]
      >> UNDISCH_NO_TAC 2 >> REWRITE_TAC[IMP_CONJ_THM]
      >> CONV_TAC(DEPTH_CONV FORALL_AND_CONV) >> STRIP_TAC
      >> RULE_ASSUM_TAC(REWRITE_RULE[WATCH_SIGNAL])
      >> UNDISCH_NO_TAC 2 >> STRIP_TAC
      >> LEFT_FORALL_TAC “delta:num” >> UNDISCH_HD_TAC
      >> ASM_REWRITE_TAC[] >> STRIP_TAC >> GEN_TAC
      >> DISJ_CASES_TAC(SPECL[“t:num”,“delta:num”]LESS_CASES)
      THENL[RES_TAC >> ASM_REWRITE_TAC[],ALL_TAC]
      >> UNDISCH_HD_TAC >> REWRITE_TAC[LESS_OR_EQ] >> STRIP_TAC
      THENL[ALL_TAC,POP_ASSUM(SUBST1_TAC o SYM) >> ASM_REWRITE_TAC[]]
      >> IMP_RES_TAC LESS_ADD_1 >> POP_ASSUM SUBST1_TAC >> DISJ1_TAC
      >> SUBST1_TAC(EQT_ELIM(ARITH_CONV“(delta+(p+1))+t0 = SUC(p+(delta+t0))”))
      >> ASM_REWRITE_TAC[]]
QED

val SBEFORE_SIGNAL = TAC_PROOF(
        ([],“(a SBEFORE b) t0
                = ?delta.
                        a(delta+t0) /\
                        (!t. t<=delta ==> ~b(t+t0))”),
        REWRITE_TAC[SBEFORE,WATCH] THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[
            EXISTS_TAC “t:num” THEN ASM_REWRITE_TAC[]
            THEN MY_MP_TAC “!t. b(t+t0) ==> !x. q(SUC(x+(t+t0)))”
            THENL[
                GEN_TAC THEN DISCH_TAC
                THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
                THEN LEFT_NO_FORALL_TAC 5 “SUC(x+t')”
                THEN UNDISCH_HD_TAC
                THEN SUBST1_TAC(EQT_ELIM(ARITH_CONV
                        “ SUC(x+t')+t0 = SUC(x+(t'+t0))”))
                THEN ASM_TAC 0 REWRITE1_TAC
                THEN STRIP_TAC,
                DISCH_TAC]
            THEN GEN_TAC THEN DISCH_TAC
            THEN IMP_RES_TAC LESS_EQUAL_ADD
            THEN UNDISCH_NO_TAC 4 THEN UNDISCH_NO_TAC 4
            THEN POP_ASSUM SUBST1_TAC
            THEN SPEC_TAC(“p:num”,“p:num”)
            THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
            THEN UNDISCH_HD_TAC THEN PROP_TAC,
            ASSUME_TAC(SPEC_ALL(REWRITE_RULE[WATCH]WATCH_EXISTS))
            THEN LEFT_EXISTS_TAC THEN EXISTS_TAC “q:num->bool”
            THEN ASM_REWRITE_TAC[]
            THEN EXISTS_TAC “delta:num” THEN ASM_REWRITE_TAC[]
            THEN CONJ_TAC
            THENL[
                MY_MP_TAC “!t. t<=delta ==> ~q(t+t0)”
                THENL[
                    INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
                    THEN DISCH_TAC
                    THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
                        “ SUC t <= delta ==> t<=delta”))
                    THEN RES_TAC THEN ASM_REWRITE_TAC[],
                    DISCH_TAC]
                THEN POP_ASSUM MATCH_MP_TAC THEN CONV_TAC ARITH_CONV,
                POP_NO_ASSUM 1 MATCH_MP_TAC THEN CONV_TAC ARITH_CONV
                ]])




(* ************************************************************ *)
(*              Expressiveness of WHEN                          *)
(* ************************************************************ *)

val ALWAYS_AS_WHEN = TAC_PROOF(
        ([],“ALWAYS a = ((\t.F) WHEN (\t. ~a t))”),
        CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN PURE_REWRITE_TAC[ALWAYS,WHEN,WATCH] THEN BETA_TAC
        THEN REWRITE_TAC[] THEN EQ_TAC THEN STRIP_TAC
        THENL[
            ASSUME_TAC(SPECL[“\t:num.F”,“t0:num”] WATCH_EXISTS)
            THEN LEFT_EXISTS_TAC THEN RULE_ASSUM_TAC (REWRITE_RULE[WATCH])
            THEN EXISTS_TAC“q:num->bool” THEN ASM_REWRITE_TAC[],
            MY_MP_TAC“!t. ~q(t+t0)”
            THENL[
                INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
                THEN LEFT_NO_FORALL_TAC 1 “t:num”
                THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[],
                DISCH_TAC THEN UNDISCH_NO_TAC 1
                THEN ASM_REWRITE_TAC[]]])

val EVENTUAL_AS_WHEN = TAC_PROOF(
        ([],“EVENTUAL a = \t. ~((\t.F) WHEN a) t”),
        ASSUME_TAC(SPEC“\t:num.~a t”(GEN“a:num->bool”ALWAYS_AS_WHEN))
        THEN UNDISCH_HD_TAC THEN BETA_TAC THEN REWRITE_TAC[]
        THEN CONV_TAC(DEPTH_CONV ETA_CONV) THEN DISCH_TAC
        THEN POP_ASSUM (SUBST1_TAC o SYM)
        THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC
        THEN REWRITE_TAC[EVENTUAL,ALWAYS]
        THEN BETA_TAC THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
        THEN REWRITE_TAC[])

val UNTIL_AS_WHEN = TAC_PROOF(
  ([],“(a UNTIL b) = (b WHEN (\t. a t ==> b t))”),
  CONV_TAC (X_FUN_EQ_CONV “t0:num”) >> GEN_TAC
  >> PURE_REWRITE_TAC[UNTIL, WHEN,WATCH]
  >> BETA_TAC >> EQ_TAC >> STRIP_TAC
  THENL[
      ASSUME_TAC(SPECL[“\t:num. a t ==> b t”,“t0:num”]WATCH_EXISTS)
      >> LEFT_EXISTS_TAC >> RULE_ASSUM_TAC (BETA_RULE o REWRITE_RULE[WATCH])
      >> EXISTS_TAC“q':num->bool” >> ASM_REWRITE_TAC[],
      ASSUME_TAC(SPEC_ALL WATCH_EXISTS)
      >> LEFT_EXISTS_TAC >> RULE_ASSUM_TAC (REWRITE_RULE[WATCH])
      >> EXISTS_TAC“q':num->bool” >> ASM_REWRITE_TAC[]]
  >> (MY_MP_TAC “!t. q(t+t0):bool = q'(t+t0)” THENL[
        INDUCT_TAC >> ASM_REWRITE_TAC[ADD_CLAUSES]
        >> LEFT_NO_FORALL_TAC 2 “t:num”
        >> UNDISCH_HD_TAC >> ASM_REWRITE_TAC[] >> PROP_TAC,
        DISCH_TAC
        >> POP_ASSUM (fn x=> REWRITE_TAC[x] >> RULE_ASSUM_TAC(REWRITE_RULE[x]))
        >> GEN_TAC >> LEFT_NO_FORALL_TAC 1 “t:num”
        >> UNDISCH_HD_TAC >> PROP_TAC]));



Theorem BEFORE_AS_WHEN:
    a BEFORE b = (\t. ~b t) WHEN (\t.a t \/ b t)
Proof
        CONV_TAC(X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[BEFORE_SIGNAL,WHEN_SIGNAL] THEN BETA_TAC
        THEN MY_MP_TAC “!delta.
                           (!t. t<delta ==> ~a(t+t0) /\ ~b(t+t0))
                        <=>
                           (!t. t<delta ==> ~a(t+t0)) /\
                           (!t. t<delta ==> ~b(t+t0))”
        THENL[GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC,
              DISCH_TAC]
        THEN REWRITE_TAC[DE_MORGAN_THM] THEN POP_ASSUM REWRITE1_TAC
        THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[
            LEFT_NO_FORALL_TAC 4 “delta:num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
            THEN CONV_TAC NOT_EXISTS_CONV THEN GEN_TAC
            THEN REWRITE_TAC[DECIDE “~(a/\b) <=> a==>~b”]
            THEN DISCH_TAC THEN RES_TAC,
            LEFT_NO_FORALL_TAC 3 “delta:num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
            THEN STRIP_TAC THEN RES_TAC,
            LEFT_NO_FORALL_TAC 2 “delta:num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
            THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
            THEN REWRITE_TAC[DECIDE “~(a==>b) <=> a/\~b”]]
QED



val SWHEN_AS_WHEN = TAC_PROOF(
        ([],“(a SWHEN b) = \t0. (a WHEN b) t0 /\ EVENTUAL b t0”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN BETA_TAC THEN GEN_TAC
        THEN REWRITE_TAC[SWHEN_SIGNAL,WHEN_SIGNAL,EVENTUAL]
        THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[
            MY_MP_TAC “delta=(delta':num)”
            THENL[
                DISJ_CASES_TAC(SPECL[“delta':num”,“delta:num”]LESS_CASES)
                THENL[RES_TAC,ALL_TAC]
                THEN UNDISCH_HD_TAC THEN REWRITE_TAC[LESS_OR_EQ] THEN STRIP_TAC
                THEN RES_TAC,
                DISCH_TAC]
            THEN POP_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[],
            EXISTS_TAC“delta:num”  THEN ASM_REWRITE_TAC[],
            DISJ_CASES_TAC DELTA_CASES THEN RES_TAC
            THEN LEFT_NO_EXISTS_TAC 1 THEN LEFT_NO_FORALL_TAC 3 “d:num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
            THEN EXISTS_TAC “d:num” THEN ASM_REWRITE_TAC[]])


val SWHEN_AS_NOT_WHEN =
    let
        val NOT_WHEN = TAC_PROOF(
                ([],“~((a WHEN b)t0) = ((\t.~a t) SWHEN b) t0”),
                REWRITE_TAC[WHEN_SIGNAL,SWHEN_SIGNAL] THEN BETA_TAC
                THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
                THEN REWRITE_TAC[TAC_PROOF(([],“~(a==>b) = a/\~b”),PROP_TAC)]
                THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC
                THEN EXISTS_TAC“delta:num” THEN ASM_REWRITE_TAC[])
        val thm1 = BETA_RULE(SPEC“\t:num.~a t”(GEN“a:num->bool”NOT_WHEN))
        val thm2 = SYM(REWRITE_RULE[]thm1)
        val thm3 = (CONV_RULE(DEPTH_CONV ETA_CONV)) thm2
     in thm3
    end


val SUNTIL_AS_WHEN = TAC_PROOF(
        ([],“(a SUNTIL b) = \t. (b WHEN (\t. a t ==> b t)) t /\ EVENTUAL b t”),
        REWRITE_TAC[SYM UNTIL_AS_WHEN]
        THEN CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN BETA_TAC THEN GEN_TAC
        THEN REWRITE_TAC[SUNTIL_SIGNAL,UNTIL_SIGNAL,EVENTUAL]
        THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[
            RES_TAC,
            MY_MP_TAC “delta=(d:num)”
            THENL[
                DISJ_CASES_TAC(SPECL[“d:num”,“delta:num”]LESS_CASES)
                THENL[RES_TAC,ALL_TAC]
                THEN UNDISCH_HD_TAC THEN REWRITE_TAC[LESS_OR_EQ] THEN STRIP_TAC
                THEN RES_TAC,
                DISCH_TAC]
            THEN POP_ASSUM(fn x=> RULE_ASSUM_TAC(REWRITE_RULE[SYM x]))
            THEN RES_TAC,
            EXISTS_TAC“delta:num”  THEN ASM_REWRITE_TAC[],
            DISJ_CASES_TAC DELTA_CASES THEN RES_TAC
            THEN LEFT_NO_EXISTS_TAC 1 THEN LEFT_NO_FORALL_TAC 3 “d:num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
            THEN EXISTS_TAC “d:num” THEN ASM_REWRITE_TAC[]
            THEN GEN_TAC THEN DISCH_TAC THEN RES_TAC
            THEN ASM_REWRITE_TAC[]])



val SBEFORE_AS_WHEN = prove(
  “a SBEFORE b = \t0. ((\t.~b t) WHEN (\t.a t \/ b t)) t0 /\ EVENTUAL a t0”,
  REWRITE_TAC[SYM BEFORE_AS_WHEN]
  THEN CONV_TAC(X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC THEN BETA_TAC
  THEN REWRITE_TAC[SBEFORE,BEFORE,EVENTUAL] THEN EQ_TAC
  THEN REPEAT STRIP_TAC
  THENL[
      EXISTS_TAC “q:num->bool” THEN ASM_REWRITE_TAC[]
      THEN DISJ1_TAC THEN EXISTS_TAC “t:num”
      THEN ASM_REWRITE_TAC[],
      EXISTS_TAC “t:num” THEN ASM_REWRITE_TAC[],
      EXISTS_TAC “q:num->bool” THEN ASM_REWRITE_TAC[]
      THEN EXISTS_TAC “t:num” THEN ASM_REWRITE_TAC[],
      EXISTS_TAC “q:num->bool” THEN ASM_REWRITE_TAC[]
      THEN EXISTS_TAC “t:num” THEN ASM_REWRITE_TAC[]
      THEN UNDISCH_NO_TAC 2 THEN ASM_REWRITE_TAC[WATCH_SIGNAL]
      THEN DISCH_TAC THEN ASM_REWRITE_TAC[]]);





val BEFORE_AS_WHEN_UNTIL = TAC_PROOF(
  ([],“(a BEFORE b) = \t. ((\t.~b t) UNTIL a) t /\ ((\t.~b t) WHEN a) t”),
  CONV_TAC(X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
  THEN REWRITE_TAC[BEFORE_SIGNAL,UNTIL_SIGNAL,WHEN_SIGNAL]
  THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
  THENL[
      UNDISCH_NO_TAC 2 THEN ASM_REWRITE_TAC[]
      THEN IMP_RES_TAC(BETA_RULE(ISPEC“\t.b(t+t0):bool”WOP))
      THEN CONV_TAC NOT_FORALL_CONV THEN EXISTS_TAC “n:num”
      THEN ASM_REWRITE_TAC[],
      DISJ_CASES_TAC DELTA_CASES THENL[ALL_TAC,RES_TAC]
      THEN LEFT_EXISTS_TAC THEN LEFT_NO_FORALL_TAC 5 “d':num”
      THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
      THEN CONV_TAC NOT_EXISTS_CONV THEN GEN_TAC
      THEN REWRITE_TAC[TAC_PROOF(([],“~(a/\b) = a==>~b”),PROP_TAC)]
      THEN DISCH_TAC THEN ASM_TAC 5 MATCH_MP_TAC
      THEN MY_MP_TAC “d'<=d”
      THENL[
          DISJ_CASES_TAC(SPECL[“d:num”,“d':num”]LESS_CASES)
          THEN ASM_REWRITE_TAC[] THEN IMP_RES_TAC LESS_TRANS
          THEN RES_TAC,
          DISCH_TAC]
      THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV“x<y /\ y<=z ==> x<z”)),
      DISJ_CASES_TAC DELTA_CASES THENL[ALL_TAC,RES_TAC] THEN LEFT_EXISTS_TAC
      THEN LEFT_NO_FORALL_TAC 4 “d:num”
      THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
      THEN CONV_TAC NOT_EXISTS_CONV THEN GEN_TAC
      THEN REWRITE_TAC[TAC_PROOF(([],“~(a/\b) = a==>~b”),PROP_TAC)]
      THEN DISCH_TAC THEN ASM_TAC 4 MATCH_MP_TAC
      THEN MY_MP_TAC “d<=delta”
      THENL[
          DISJ_CASES_TAC(SPECL[“delta:num”,“d:num”]LESS_CASES)
          THEN ASM_REWRITE_TAC[] THEN IMP_RES_TAC LESS_TRANS
          THEN RES_TAC,
          DISCH_TAC]
      THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV“x<y /\ y<=z ==> x<z”)),
      DISJ_CASES_TAC(SPEC“a:num->bool”(GEN“b:num->bool”DELTA_CASES))
      THENL[ALL_TAC,RES_TAC] THEN LEFT_EXISTS_TAC
      THEN LEFT_NO_FORALL_TAC 3 “d:num” THEN UNDISCH_HD_TAC
      THEN LEFT_NO_FORALL_TAC 3 “d:num” THEN UNDISCH_HD_TAC
      THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC
      THEN MY_MP_TAC “d<delta”
      THENL[
          DISJ_CASES_TAC(SPECL[“d:num”,“delta:num”]LESS_CASES)
          THEN ASM_REWRITE_TAC[] THEN UNDISCH_HD_TAC
          THEN REWRITE_TAC[LESS_OR_EQ] THEN STRIP_TAC THEN RES_TAC
          THEN UNDISCH_NO_TAC 4 THEN ASM_REWRITE_TAC[],
          DISCH_TAC]
      THEN EXISTS_TAC “d:num” THEN ASM_REWRITE_TAC[]])



val BEFORE_HW = TAC_PROOF(
        ([],“(a BEFORE b) t0 = ?q. (q WATCH a) t0 /\ !t. q(t+t0)\/ ~b(t+t0)”),
        REWRITE_TAC[BEFORE_AS_WHEN_UNTIL,WHEN,UNTIL] THEN BETA_TAC
        THEN EQ_TAC THEN REPEAT STRIP_TAC
        THEN EXISTS_TAC “q:num->bool” THEN ASM_REWRITE_TAC[]
        THENL[
            ALL_TAC,
            GEN_TAC THEN REWRITE_TAC[TAC_PROOF(([],“(a\/b) = ~a==>b”),PROP_TAC)]
            THEN DISCH_TAC THEN LEFT_NO_FORALL_TAC 1 “t':num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
            THEN ASM_REWRITE_TAC[],
            GEN_TAC THEN REWRITE_TAC[TAC_PROOF(([],“(a\/b) = ~a==>b”),PROP_TAC)]
            THEN DISCH_TAC THEN LEFT_NO_FORALL_TAC 1 “t':num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
            THEN ASM_REWRITE_TAC[]]
        THEN RULE_ASSUM_TAC(REWRITE_RULE[WATCH])
        THEN MY_MP_TAC“!t. q(t+t0):bool = q'(t+t0)”
        THENL[INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES],DISCH_TAC]
        THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[SYM(SPEC_ALL x)]))
        THEN GEN_TAC THEN LEFT_NO_FORALL_TAC 2 “t:num”
        THEN UNDISCH_HD_TAC THEN LEFT_NO_FORALL_TAC 0 “t:num”
        THEN UNDISCH_HD_TAC THEN PROP_TAC)

(* ************************************************************ *)
(*              Expressiveness of UNTIL                         *)
(* ************************************************************ *)

val ALWAYS_AS_UNTIL = TAC_PROOF(
        ([],“(ALWAYS a) = (a UNTIL (\t.F))”),
        CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN PURE_REWRITE_TAC[UNTIL_AS_WHEN] THEN BETA_TAC
        THEN REWRITE_TAC[ALWAYS_AS_WHEN])

val EVENTUAL_AS_UNTIL = TAC_PROOF(
        ([],“(EVENTUAL a) = \t. ~((\t.~a t) UNTIL (\t.F)) t”),
        ASSUME_TAC(SPEC“\t:num.~a t”(GEN“a:num->bool”ALWAYS_AS_UNTIL))
        THEN UNDISCH_HD_TAC THEN BETA_TAC THEN REWRITE_TAC[]
        THEN CONV_TAC(DEPTH_CONV ETA_CONV) THEN DISCH_TAC
        THEN POP_ASSUM (SUBST1_TAC o SYM)
        THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC
        THEN REWRITE_TAC[EVENTUAL,ALWAYS]
        THEN BETA_TAC THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
        THEN REWRITE_TAC[])


val WHEN_AS_UNTIL = TAC_PROOF(
        ([],“(a WHEN b) = ((\t.~b t) UNTIL (\t.a t /\ b t))”),
        CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN PURE_REWRITE_TAC[UNTIL_AS_WHEN] THEN BETA_TAC
        THEN REWRITE_TAC[TAC_PROOF(([],“(~b==> a/\b) = b”), PROP_TAC)]
        THEN PURE_REWRITE_TAC[WHEN_SIGNAL]
        THEN BETA_TAC THEN EQ_TAC THEN STRIP_TAC
        THEN GEN_TAC THEN STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[])


val BEFORE_AS_UNTIL = TAC_PROOF(
  ([],“(a BEFORE b) = \t0. ~((\t.~a t) UNTIL b) t0 \/ ALWAYS (\t.~b t) t0”),
  CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
  THEN REWRITE_TAC[BEFORE_IMP,UNTIL,ALWAYS]
  THEN BETA_TAC THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
  THEN REWRITE_TAC[TAC_PROOF(([],“(a==>b) = (~a\/b)”), PROP_TAC)]
  THEN REWRITE_TAC[DE_MORGAN_THM]
  THEN CONV_TAC(DEPTH_CONV LEFT_OR_FORALL_CONV)
  THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
  THEN REWRITE_TAC[DE_MORGAN_THM]
  THEN REWRITE_TAC[TAC_PROOF(([],“(a\/b)\/c = a\/b\/c”), PROP_TAC)])




val SWHEN_AS_UNTIL = TAC_PROOF(
        ([],“(a SWHEN b) = \t.((\t.~b t) UNTIL (\t.a t /\ b t)) t /\
                                EVENTUAL b t”),
        CONV_TAC FUN_EQ_CONV THEN BETA_TAC
        THEN REWRITE_TAC[SWHEN_AS_WHEN,WHEN_AS_UNTIL]
        THEN BETA_TAC THEN REWRITE_TAC[])





val SUNTIL_AS_UNTIL = TAC_PROOF(
        ([],“(a SUNTIL b) = \t0. (a UNTIL b) t0 /\ EVENTUAL b t0”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN BETA_TAC THEN GEN_TAC
        THEN REWRITE_TAC[SUNTIL_SIGNAL,UNTIL_SIGNAL,EVENTUAL]
        THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[
            RES_TAC,
            MY_MP_TAC “delta=(d:num)”
            THENL[
                DISJ_CASES_TAC(SPECL[“d:num”,“delta:num”]LESS_CASES)
                THENL[RES_TAC,ALL_TAC]
                THEN UNDISCH_HD_TAC THEN REWRITE_TAC[LESS_OR_EQ] THEN STRIP_TAC
                THEN RES_TAC,
                DISCH_TAC]
            THEN POP_ASSUM(fn x=> RULE_ASSUM_TAC(REWRITE_RULE[SYM x]))
            THEN RES_TAC,
            EXISTS_TAC“delta:num”  THEN ASM_REWRITE_TAC[],
            DISJ_CASES_TAC DELTA_CASES THEN RES_TAC
            THEN LEFT_NO_EXISTS_TAC 1 THEN LEFT_NO_FORALL_TAC 3 “d:num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
            THEN EXISTS_TAC “d:num” THEN ASM_REWRITE_TAC[]
            THEN GEN_TAC THEN DISCH_TAC THEN RES_TAC
            THEN ASM_REWRITE_TAC[]])




val SBEFORE_AS_UNTIL = TAC_PROOF(
        ([],“(a SBEFORE b) = \t0. ~((\t.~a t) UNTIL b) t0 ”),
        CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[SBEFORE,UNTIL_IMP]
        THEN BETA_TAC THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
        THEN REWRITE_TAC[TAC_PROOF(([],“~(a==>b) = a/\~b”), PROP_TAC)]
        THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
        THEN REWRITE_TAC[DE_MORGAN_THM])

(* ************************************************************ *)
(*              Expressiveness of BEFORE                        *)
(* ************************************************************ *)


val EVENTUAL_AS_BEFORE = TAC_PROOF(
        ([],“EVENTUAL b = \t0. ~((\t.F) BEFORE b) t0”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN BETA_TAC THEN GEN_TAC
        THEN REWRITE_TAC[BEFORE_SIGNAL,EVENTUAL] THEN BETA_TAC
        THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
        THEN REWRITE_TAC[] THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[
            DISJ_CASES_TAC DELTA_CASES THEN RES_TAC
            THEN ASM_REWRITE_TAC[],
            EXISTS_TAC“delta:num” THEN ASM_REWRITE_TAC[]])


val ALWAYS_AS_BEFORE = TAC_PROOF(
        ([],“ALWAYS b = (\t.F) BEFORE (\t.~b t)”),
    let val thm1 = GEN_ALL EVENTUAL_AS_BEFORE
        val thm2 = SPEC“\t:num.~b t”thm1
        val thm3 = (CONV_RULE(X_FUN_EQ_CONV“t0:num”)) thm2
        val thm4 = SPEC_ALL(BETA_RULE thm3)
     in
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC
        THEN ONCE_REWRITE_TAC[TAC_PROOF(([],“(a=b) = (~a= ~b)”),PROP_TAC)]
        THEN REWRITE_TAC[SYM thm4,ALWAYS,EVENTUAL] THEN BETA_TAC
        THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
        THEN REWRITE_TAC[]
    end)


val UNTIL_AS_BEFORE = TAC_PROOF(
        ([],“(a UNTIL b) = \t0. ~((\t.~a t) BEFORE b) t0 \/ ALWAYS a t0”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN BETA_TAC THEN GEN_TAC
        THEN REWRITE_TAC[UNTIL_SIGNAL,BEFORE_SIGNAL,ALWAYS] THEN BETA_TAC
        THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
        THEN REWRITE_TAC[DE_MORGAN_THM,TAC_PROOF(
                        ([],“~(a==>b) = a/\~b”),PROP_TAC)]
        THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
        THEN REWRITE_TAC[TAC_PROOF(([],“~(a/\~b) = a==>b”),PROP_TAC)]
        THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]
        THENL[
            DISJ_CASES_TAC DELTA_CASES
            THENL[
                LEFT_EXISTS_TAC THEN LEFT_NO_FORALL_TAC 1 “d:num”
                THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
                THEN DISJ1_TAC THEN EXISTS_TAC “d:num”
                THEN ASM_REWRITE_TAC[],
                UNDISCH_NO_TAC 2 THEN ASM_REWRITE_TAC[]],
            UNDISCH_NO_TAC 2 THEN ASM_REWRITE_TAC[],
            MY_MP_TAC“(d:num)=delta”
            THENL[
                DISJ_CASES_TAC(SPECL[“delta:num”,“d:num”]LESS_CASES)
                THENL[RES_TAC,ALL_TAC]
                THEN UNDISCH_HD_TAC THEN REWRITE_TAC[LESS_OR_EQ] THEN STRIP_TAC
                THEN RES_TAC,
                DISCH_TAC]
            THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x]))
            THEN RES_TAC])


val WHEN_AS_BEFORE =
    let
        val thm1 = GEN_ALL UNTIL_AS_BEFORE
        val thm2 = SPECL[“\t:num. a t /\ b t”,“\t:num. ~b t”]thm1
        val thm3 = REWRITE_RULE[SYM WHEN_AS_UNTIL]thm2
        val thm4 = REWRITE_RULE[](BETA_RULE thm3)
        val thm5 = (CONV_RULE(DEPTH_CONV ETA_CONV)) thm4
     in thm5
    end


val SWHEN_AS_BEFORE = TAC_PROOF(
        ([],“a SWHEN b = \t0.~(b BEFORE (\t. a t /\ b t)) t0”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN BETA_TAC THEN GEN_TAC
        THEN REWRITE_TAC[SWHEN_AS_WHEN,WHEN_AS_BEFORE,ALWAYS,EVENTUAL]
        THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]
        THEN RES_TAC THEN UNDISCH_HD_TAC THEN REWRITE_TAC[BEFORE_IMP]
        THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV) THEN BETA_TAC
        THEN REWRITE_TAC[TAC_PROOF(([],“~(a==>b) = a/\~b”),PROP_TAC)]
        THEN REWRITE_TAC[DE_MORGAN_THM]
        THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
        THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
        THEN REWRITE_TAC[DE_MORGAN_THM]
        THEN REPEAT STRIP_TAC THEN EXISTS_TAC“t:num”
        THEN ASM_REWRITE_TAC[])



val SUNTIL_AS_BEFORE = TAC_PROOF(
        ([],“(a SUNTIL b) = \t0. ~((\t.~a t) BEFORE b) t0”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN BETA_TAC THEN GEN_TAC
        THEN REWRITE_TAC[SUNTIL_AS_UNTIL,UNTIL_AS_BEFORE,ALWAYS,EVENTUAL]
        THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]
        THEN RES_TAC
        THENL[
            UNDISCH_HD_TAC THEN REWRITE_TAC[BEFORE]
            THEN BETA_TAC THEN ASM_REWRITE_TAC[]
            THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
            THEN REWRITE_TAC[DE_MORGAN_THM] THEN GEN_TAC THEN DISJ2_TAC
            THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
            THEN EXISTS_TAC“t:num” THEN ASM_REWRITE_TAC[],
            UNDISCH_HD_TAC THEN REWRITE_TAC[BEFORE_IMP]
            THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV) THEN BETA_TAC
            THEN REWRITE_TAC[TAC_PROOF(([],“~(a==>b) = a/\~b”),PROP_TAC)]
            THEN REWRITE_TAC[DE_MORGAN_THM]
            THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
            THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
            THEN REWRITE_TAC[DE_MORGAN_THM]
            THEN REPEAT STRIP_TAC THEN EXISTS_TAC“t:num”
            THEN ASM_REWRITE_TAC[]])




val SBEFORE_AS_BEFORE = TAC_PROOF(
        ([],“(a SBEFORE b) = \t0.(a BEFORE b) t0  /\ EVENTUAL a t0”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN BETA_TAC THEN GEN_TAC
        THEN REWRITE_TAC[SBEFORE,BEFORE,EVENTUAL] THEN EQ_TAC
        THEN REPEAT STRIP_TAC
        THENL[
            EXISTS_TAC “q:num->bool” THEN ASM_REWRITE_TAC[]
            THEN DISJ1_TAC THEN EXISTS_TAC “t:num”
            THEN ASM_REWRITE_TAC[],
            EXISTS_TAC “t:num” THEN ASM_REWRITE_TAC[],
            EXISTS_TAC “q:num->bool” THEN ASM_REWRITE_TAC[]
            THEN EXISTS_TAC “t:num” THEN ASM_REWRITE_TAC[],
            EXISTS_TAC “q:num->bool” THEN ASM_REWRITE_TAC[]
            THEN EXISTS_TAC “t:num” THEN ASM_REWRITE_TAC[]
            THEN UNDISCH_NO_TAC 2 THEN ASM_REWRITE_TAC[WATCH_SIGNAL]
            THEN DISCH_TAC THEN ASM_REWRITE_TAC[]])

(* ************************************************************ *)
(*              Expressiveness of SWHEN                         *)
(* ************************************************************ *)


val WHEN_SWHEN_LEMMA = TAC_PROOF(
  ([],“if (!t1.?t2.b(t2+t1))
         then (!t0. (a WHEN b) t0 = (a SWHEN b) t0)
         else ?t1.!t2. (a WHEN b)(t2+t1) /\ ~(a SWHEN b)(t2+t1)”),
  REWRITE_TAC[SWHEN_SIGNAL,WHEN_SIGNAL]
  THEN ASM_CASES_TAC“!t1.?t2.b(t2+t1)” THEN ASM_TAC 0 REWRITE1_TAC
  THENL[
      GEN_TAC THEN EQ_TAC THEN STRIP_TAC
      THENL[
          DISJ_CASES_TAC DELTA_CASES
          THENL[
              ALL_TAC,
              LEFT_NO_FORALL_TAC 2 “t0:num” THEN UNDISCH_HD_TAC
              THEN ASM_TAC 0 REWRITE1_TAC]
          THEN UNDISCH_HD_TAC THEN STRIP_TAC
          THEN RES_TAC THEN POP_NO_TAC 3 THEN EXISTS_TAC “d:num”
          THEN ASM_REWRITE_TAC[],
          REPEAT STRIP_TAC
          THEN MY_MP_TAC “delta'=(delta:num)”
          THENL[
              DISJ_CASES_TAC(SPECL[“delta:num”,“delta':num”]LESS_CASES)
              THENL[RES_TAC,ALL_TAC]
              THEN UNDISCH_HD_TAC THEN REWRITE_TAC[LESS_OR_EQ] THEN STRIP_TAC
              THEN RES_TAC,
              DISCH_TAC]
          THEN ASM_REWRITE_TAC[]],
      RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NOT_FORALL_CONV))
      THEN RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV NOT_EXISTS_CONV))
      THEN LEFT_EXISTS_TAC THEN EXISTS_TAC “t1:num”
      THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
      THEN REPEAT STRIP_TAC
      THENL[UNDISCH_NO_TAC 0,UNDISCH_NO_TAC 1]
      THEN ASM_REWRITE_TAC[ADD_ASSOC]])


val EVENTUAL_AS_SWHEN = TAC_PROOF(
        ([],“EVENTUAL a = (\t.T) SWHEN a”),
        CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[SWHEN_SIGNAL,EVENTUAL_SIGNAL] THEN BETA_TAC
        THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC
        THENL[
            DISJ_CASES_TAC(SPEC“a:num->bool”(GEN“b:num->bool” DELTA_CASES))
            THENL[ALL_TAC, UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[]]
            THEN LEFT_EXISTS_TAC THEN EXISTS_TAC “d:num”
            THEN ASM_REWRITE_TAC[],
            EXISTS_TAC “delta:num” THEN ASM_REWRITE_TAC[]])


val ALWAYS_AS_SWHEN = TAC_PROOF(
        ([],“ALWAYS a = \t. ~((\t.T) SWHEN (\t.~a t)) t”),
        ASSUME_TAC(SPEC“\t:num.~a t”(GEN“a:num->bool”EVENTUAL_AS_SWHEN))
        THEN UNDISCH_HD_TAC THEN BETA_TAC THEN REWRITE_TAC[]
        THEN DISCH_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
        THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC
        THEN REWRITE_TAC[EVENTUAL,ALWAYS]
        THEN BETA_TAC THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
        THEN REWRITE_TAC[])


val WHEN_AS_SWHEN = TAC_PROOF(
        ([],“a WHEN b = \t. (a SWHEN b) t \/ ALWAYS (\t.~b t) t”),
        CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[SWHEN_SIGNAL,WHEN_SIGNAL,ALWAYS] THEN BETA_TAC
        THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC
        THENL[
            DISJ_CASES_TAC DELTA_CASES THEN ASM_REWRITE_TAC[]
            THEN LEFT_EXISTS_TAC THEN LEFT_NO_FORALL_TAC 1 “d:num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
            THEN DISJ1_TAC THEN EXISTS_TAC “d:num” THEN ASM_REWRITE_TAC[],
            MY_MP_TAC “delta=(delta':num)”
            THENL[
                DISJ_CASES_TAC(SPECL[“delta':num”,“delta:num”]LESS_CASES)
                THENL[RES_TAC,ALL_TAC]
                THEN UNDISCH_HD_TAC THEN REWRITE_TAC[LESS_OR_EQ] THEN STRIP_TAC
                THEN RES_TAC,
                DISCH_TAC]
            THEN POP_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]])


val WHEN_AS_NOT_SWHEN = TAC_PROOF(
        ([],“((a WHEN b)t0) = ~((\t.~a t) SWHEN b) t0”),
        REWRITE_TAC[WHEN_SIGNAL,SWHEN_SIGNAL] THEN BETA_TAC
        THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
        THEN REWRITE_TAC[TAC_PROOF(([],“~(a/\b/\~x) = a/\b==>x”),PROP_TAC)])


val BEFORE_AS_SWHEN = TAC_PROOF(
  ([],“a BEFORE b =
  \t0. ((\t.~b t) SWHEN (\t. a t \/ b t)) t0 \/ ALWAYS (\t. ~a t /\ ~b t) t0”),
  CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
  THEN REWRITE_TAC[BEFORE_AS_WHEN,SWHEN_AS_WHEN,EVENTUAL,ALWAYS,WHEN_SIGNAL]
  THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
  THEN RES_TAC THEN ASM_REWRITE_TAC[] THEN UNDISCH_HD_TAC
  THEN REWRITE_TAC[TAC_PROOF(([],“a/\(x\/b) ==> ~b = b ==> ~a”),PROP_TAC)]
  THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
  THEN REWRITE_TAC[TAC_PROOF(([],“~(a==>~b) = b /\ a”),PROP_TAC)]
  THEN STRIP_TAC
  THEN DISJ_CASES_TAC DELTA_CASES
  THENL[
      LEFT_EXISTS_TAC THEN DISJ1_TAC THEN EXISTS_TAC“d:num”
      THEN ASM_REWRITE_TAC[],
      UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[]
      THEN MY_MP_TAC“~(?t.a(t+t0)) = !t.~a(t+t0)”
      THENL[CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV) THEN REWRITE_TAC[],DISCH_TAC]
      THEN POP_ASSUM (SUBST1_TAC o SYM)
      THEN REWRITE_TAC[TAC_PROOF(([],“a\/~a”),PROP_TAC)]])


val BEFORE_AS_NOT_SWHEN = TAC_PROOF(
        ([],“a BEFORE b = \t0. ~(b SWHEN (\t. a t \/ b t)) t0”),
        CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[BEFORE_AS_WHEN,WHEN_AS_NOT_SWHEN]
        THEN BETA_TAC THEN REWRITE_TAC[]
        THEN CONV_TAC(DEPTH_CONV ETA_CONV)
        THEN REWRITE_TAC[])



val SUNTIL_AS_SWHEN = TAC_PROOF(
  ([],“a SUNTIL b = b SWHEN (\t. a t ==> b t)”),
  REWRITE_TAC[SUNTIL_AS_UNTIL,SWHEN_AS_WHEN,UNTIL_AS_WHEN,EVENTUAL,WHEN_SIGNAL]
  THEN CONV_TAC FUN_EQ_CONV THEN BETA_TAC THEN X_GEN_TAC “t0:num”
  THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]
  THENL[EXISTS_TAC “t:num” THEN ASM_REWRITE_TAC[], ALL_TAC]
  THEN DISJ_CASES_TAC(BETA_RULE
          (SPEC“\t:num.a t==>b t”(GEN“b:num->bool”DELTA_CASES)))
  THENL[
      LEFT_EXISTS_TAC THEN LEFT_NO_FORALL_TAC 3 “d:num”
      THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
      THEN EXISTS_TAC“d:num” THEN ASM_REWRITE_TAC[],
      UNDISCH_HD_TAC
      THEN REWRITE_TAC[TAC_PROOF(([],“~(a==>b) = a/\~b”),PROP_TAC)]
      THEN DISCH_TAC THEN UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[]])



val UNTIL_AS_SWHEN = TAC_PROOF(
        ([],“a UNTIL b = \t. (b SWHEN (\t. a t ==> b t)) t \/ ALWAYS a t”),
        CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[SYM SUNTIL_AS_SWHEN,SUNTIL_AS_UNTIL] THEN BETA_TAC
        THEN REWRITE_TAC[EVENTUAL,ALWAYS]
        THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC
        THENL[ALL_TAC,ASM_REWRITE_TAC[UNTIL,WATCH_EXISTS]]
        THEN ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[UNTIL_SIGNAL])
        THEN UNDISCH_HD_TAC THEN STRIP_TAC
        THEN DISJ_CASES_TAC DELTA_CASES THEN RES_TAC
        THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN LEFT_EXISTS_TAC
        THEN EXISTS_TAC“d:num” THEN ASM_REWRITE_TAC[])





val SBEFORE_AS_SWHEN = TAC_PROOF(
        ([],“a SBEFORE b = ((\t. ~b t) SWHEN (\t.a t \/ b t))”),
        CONV_TAC(X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[SBEFORE_AS_BEFORE,BEFORE_AS_WHEN,SWHEN_AS_WHEN]
        THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]
        THENL[
            UNDISCH_HD_TAC THEN REWRITE_TAC[EVENTUAL]
            THEN BETA_TAC THEN STRIP_TAC
            THEN EXISTS_TAC“t:num” THEN ASM_REWRITE_TAC[],
            ALL_TAC]
        THEN UNDISCH_ALL_TAC THEN REWRITE_TAC[WHEN_SIGNAL,EVENTUAL]
        THEN BETA_TAC THEN STRIP_TAC THEN DISCH_TAC
        THEN ASSUME_TAC (BETA_RULE(SPEC“\t.a(t+t0)\/b(t+t0)”WOP))
        THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
        THEN STRIP_TAC
        THENL[ EXISTS_TAC“n:num” THEN ASM_REWRITE_TAC[], ALL_TAC]
        THEN LEFT_NO_FORALL_TAC 3 “n:num”
        THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[])



(* ************************************************************ *)
(*              Expressiveness of SUNTIL                        *)
(* ************************************************************ *)


val EVENTUAL_AS_SUNTIL = TAC_PROOF(
        ([],“EVENTUAL a = (\t.T) SUNTIL a”),
        REWRITE_TAC[SUNTIL_AS_UNTIL,UNTIL_SIGNAL]
        THEN CONV_TAC(DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[])

val ALWAYS_AS_SUNTIL = TAC_PROOF(
        ([],“ALWAYS a = \t. ~((\t.T) SUNTIL (\t.~a t)) t”),
        ASSUME_TAC(SPEC“\t:num.~a t”
                        (GEN“a:num->bool”EVENTUAL_AS_SUNTIL))
        THEN UNDISCH_HD_TAC THEN BETA_TAC THEN REWRITE_TAC[]
        THEN DISCH_TAC THEN POP_ASSUM (SUBST1_TAC o SYM)
        THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC
        THEN REWRITE_TAC[EVENTUAL,ALWAYS]
        THEN BETA_TAC THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
        THEN REWRITE_TAC[])


val UNTIL_AS_SUNTIL = TAC_PROOF(
  ([],“a UNTIL b = \t. (a SUNTIL b) t \/ ALWAYS a t”),
  CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
  THEN REWRITE_TAC[SUNTIL_SIGNAL,UNTIL_SIGNAL,ALWAYS_SIGNAL] THEN BETA_TAC
  THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC[]
  THENL[
      DISJ_CASES_TAC DELTA_CASES
      THENL[
          LEFT_EXISTS_TAC THEN LEFT_NO_FORALL_TAC 1 “d:num”
          THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
          THEN DISJ1_TAC THEN EXISTS_TAC “d:num”
          THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN DISCH_TAC THEN RES_TAC
          THEN ASM_REWRITE_TAC[],
          DISJ2_TAC THEN POP_NO_ASSUM 2 MATCH_MP_TAC
          THEN ASM_REWRITE_TAC[]],
      MY_MP_TAC “delta=(d:num)”
      THENL[
          DISJ_CASES_TAC(SPECL[“d:num”,“delta:num”]LESS_CASES)
          THENL[RES_TAC,ALL_TAC]
          THEN UNDISCH_HD_TAC THEN REWRITE_TAC[LESS_OR_EQ] THEN STRIP_TAC
          THEN RES_TAC,
          DISCH_TAC]
      THEN UNDISCH_NO_TAC 6 THEN POP_ASSUM SUBST1_TAC THEN DISCH_TAC
      THEN RES_TAC])


val SWHEN_AS_SUNTIL = TAC_PROOF(
        ([],“a SWHEN b = (\t. ~b t) SUNTIL (\t. a t /\ b t)”),
        REWRITE_TAC[SUNTIL_AS_SWHEN] THEN BETA_TAC
        THEN REWRITE_TAC[TAC_PROOF(([],“(~b ==> a /\ b) = b”),PROP_TAC)]
        THEN CONV_TAC FUN_EQ_CONV THEN BETA_TAC THEN REWRITE_TAC[SWHEN_SIGNAL]
        THEN GEN_TAC THEN BETA_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
        THEN EXISTS_TAC “delta:num” THEN ASM_REWRITE_TAC[])

val WHEN_AS_SUNTIL = prove(
  “a WHEN b =
    \t. ((\t. ~b t) SUNTIL (\t. a t /\ b t)) t \/ ALWAYS (\t. ~b t) t”,
  REWRITE_TAC[SYM SWHEN_AS_SUNTIL,WHEN_AS_SWHEN])


val BEFORE_AS_SUNTIL = TAC_PROOF(
  ([],“a BEFORE b = \t. ~((\t. ~a t) SUNTIL b) t”),
  CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
  THEN REWRITE_TAC[SUNTIL_AS_UNTIL,BEFORE_AS_UNTIL]
  THEN REWRITE_TAC[DE_MORGAN_THM,ALWAYS,EVENTUAL] THEN BETA_TAC
  THEN REWRITE_TAC[DE_MORGAN_THM] THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
  THEN PROP_TAC)


val SBEFORE_AS_SUNTIL = TAC_PROOF(
        ([],“a SBEFORE b = \t0. ~((\t. ~a t) SUNTIL b) t0 /\ EVENTUAL a t0”),
        CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[SBEFORE_AS_BEFORE,BEFORE_AS_SUNTIL]
        THEN BETA_TAC THEN PROP_TAC)


(* ************************************************************ *)
(*              Expressiveness of SBEFORE                       *)
(* ************************************************************ *)

val EVENTUAL_AS_SBEFORE = TAC_PROOF(
        ([],“EVENTUAL b = (b SBEFORE (\t.F))”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN BETA_TAC THEN GEN_TAC
        THEN ONCE_REWRITE_TAC[TAC_PROOF(([],“(a=b) = (~a= ~b)”),PROP_TAC)]
        THEN REWRITE_TAC[SBEFORE_AS_UNTIL] THEN BETA_TAC
        THEN REWRITE_TAC[SYM ALWAYS_AS_UNTIL]
        THEN REWRITE_TAC[ALWAYS,EVENTUAL] THEN BETA_TAC
        THEN CONV_TAC(DEPTH_CONV(NOT_EXISTS_CONV))
        THEN REWRITE_TAC[])


val ALWAYS_AS_SBEFORE = TAC_PROOF(
        ([],“ALWAYS b = \t0. ~((\t.~b t) SBEFORE(\t.F)) t0”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC THEN BETA_TAC
        THEN ONCE_REWRITE_TAC[TAC_PROOF(([],“(a=b) = (~a= ~b)”),PROP_TAC)]
        THEN REWRITE_TAC[SBEFORE_AS_UNTIL] THEN BETA_TAC
        THEN REWRITE_TAC[SYM ALWAYS_AS_UNTIL]
        THEN CONV_TAC(DEPTH_CONV ETA_CONV)
        THEN REWRITE_TAC[])



val WHEN_AS_SBEFORE = prove(
  “(a WHEN b) = \t0. (b SBEFORE (\t. ~a t /\ b t)) t0 \/ ALWAYS(\t. ~b t) t0”,
  CONV_TAC(X_FUN_EQ_CONV“t0:num”) >> GEN_TAC >> BETA_TAC
  >> ONCE_REWRITE_TAC[TAC_PROOF(([],“(a=b) = (~a= ~b)”),PROP_TAC)]
  >> ASSUME_TAC (REWRITE_RULE[](BETA_RULE
                  (SPEC“\t:num.~a t”(GEN“a:num->bool”SWHEN_AS_NOT_WHEN))))
  >> UNDISCH_HD_TAC >> CONV_TAC(DEPTH_CONV ETA_CONV)
  >> DISCH_TAC >> POP_ASSUM (SUBST1_TAC o SYM)
  >> REWRITE_TAC[SBEFORE_AS_WHEN] >> BETA_TAC
  >> REWRITE_TAC[DE_MORGAN_THM]
  >> REWRITE_TAC[TAC_PROOF(([],“(b\/a/\b) = b”),PROP_TAC)]
  >> CONV_TAC(DEPTH_CONV ETA_CONV)
  >> ASSUME_TAC
       (REWRITE_RULE[](
           BETA_RULE
             (SPEC“\t:num. ~a t /\b t”(GEN“a:num->bool”SWHEN_AS_NOT_WHEN))))
  >> UNDISCH_HD_TAC >> CONV_TAC(DEPTH_CONV ETA_CONV)
  >> REWRITE_TAC[DE_MORGAN_THM]
  >> DISCH_TAC >> POP_ASSUM (SUBST1_TAC o SYM)
  >> MY_MP_TAC “~(ALWAYS (\t. ~(b t)) t0) = EVENTUAL b t0”
  THENL[
      REWRITE_TAC[EVENTUAL,ALWAYS]
      >> CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
      >> BETA_TAC >> REWRITE_TAC[],
      DISCH_TAC]
  >> POP_ASSUM SUBST1_TAC
  >> REWRITE_TAC[TAC_PROOF(([],“(b\/~a)/\a = b/\a”),PROP_TAC)]
  >> REWRITE_TAC[SWHEN_AS_WHEN] >> BETA_TAC
  >> REWRITE_TAC[TAC_PROOF(([],“(a/\b)/\b = a/\b”),PROP_TAC)]
  >> MATCH_MP_TAC (TAC_PROOF(([],“(a=c) ==> (a/\b = c/\b)”),PROP_TAC))
  >> REWRITE_TAC[WHEN_SIGNAL] >> BETA_TAC
  >> EQ_TAC >> REPEAT STRIP_TAC >> ASM_REWRITE_TAC[]
  >> LEFT_NO_FORALL_TAC 3 “delta:num”
  >> UNDISCH_HD_TAC >> ASM_REWRITE_TAC[])


val UNTIL_AS_SBEFORE = TAC_PROOF(
        ([],“a UNTIL b = \t0.~((\t.~a t) SBEFORE b) t0”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC THEN BETA_TAC
        THEN ONCE_REWRITE_TAC[TAC_PROOF(([],“(a=b) = (~a= ~b)”),PROP_TAC)]
        THEN ASSUME_TAC (REWRITE_RULE[](BETA_RULE
                        (SPEC“\t:num.~a t”(GEN“a:num->bool”SBEFORE_AS_UNTIL))))
        THEN POP_ASSUM REWRITE1_TAC
        THEN BETA_TAC THEN CONV_TAC(DEPTH_CONV ETA_CONV)
        THEN REWRITE_TAC[])



val BEFORE_AS_SBEFORE = TAC_PROOF(
        ([],“a BEFORE b = \t0. (a SBEFORE b) t0 \/ ALWAYS (\t.~b t) t0”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC THEN BETA_TAC
        THEN REWRITE_TAC[BEFORE_AS_SUNTIL,SBEFORE_AS_SUNTIL]
        THEN BETA_TAC THEN REWRITE_TAC[SUNTIL_SIGNAL,EVENTUAL,ALWAYS]
        THEN BETA_TAC THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
        THEN REWRITE_TAC[TAC_PROOF(([],“~(a/\b) = a ==> ~b”),PROP_TAC)]
        THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]
        THEN REWRITE_TAC[TAC_PROOF(([],“a\/b = ~a ==> b”),PROP_TAC)]
        THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
        THEN DISCH_TAC THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x]))
        THEN MATCH_MP_TAC
               (BETA_RULE(SPEC“\t.~b(t+t0)” COMPLETE_INDUCTION))

        THEN ASM_REWRITE_TAC[]);



val SWHEN_AS_SBEFORE = TAC_PROOF(
        ([],“(a SWHEN b) = (b SBEFORE (\t.~a t/\b t))”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC THEN BETA_TAC
        THEN REWRITE_TAC[SWHEN_AS_WHEN,SBEFORE_AS_WHEN]
        THEN BETA_TAC
        THEN REWRITE_TAC[TAC_PROOF(([],“b\/~a/\b= b”),PROP_TAC)]
        THEN CONV_TAC(DEPTH_CONV ETA_CONV)
        THEN MATCH_MP_TAC (TAC_PROOF(([],“(a=c) ==> (a/\b = c/\b)”),PROP_TAC))
        THEN REWRITE_TAC[WHEN_SIGNAL] THEN BETA_TAC
        THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[
            LEFT_NO_FORALL_TAC 3 “delta:num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[],
            LEFT_NO_FORALL_TAC 2 “delta:num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]])



val SUNTIL_AS_SBEFORE = TAC_PROOF(
        ([],“(a SUNTIL b) = \t0. ~((\t.~a t) SBEFORE b) t0 /\ EVENTUAL b t0”),
    let val thm1 = GEN“a:num->bool” SBEFORE_AS_UNTIL
        val thm2 = BETA_RULE(SPEC“\t:num.~a t”thm1)
        val thm3 = (CONV_RULE(DEPTH_CONV ETA_CONV))(REWRITE_RULE[]thm2)
     in
        SUBST1_TAC thm3 THEN CONV_TAC(X_FUN_EQ_CONV“t0:num”)
        THEN BETA_TAC THEN GEN_TAC THEN REWRITE_TAC[DE_MORGAN_THM]
        THEN REWRITE_TAC[SUNTIL_AS_UNTIL] THEN BETA_TAC THEN REWRITE_TAC[]
    end)



(* ************************************************************ *)
(*      Homomorphism of the NEXT operator                       *)
(* ************************************************************ *)


val NOT_NEXT = TAC_PROOF(
        ([],“!P. NEXT (\t.~P t) = \t. ~NEXT P t”),
        GEN_TAC THEN REWRITE_TAC[NEXT] THEN BETA_TAC THEN REWRITE_TAC[])

val AND_NEXT = TAC_PROOF(
        ([],“!Q P. NEXT (\t.P t /\ Q t) = \t. NEXT P t /\ NEXT Q t”),
        REPEAT GEN_TAC THEN REWRITE_TAC[NEXT]
        THEN BETA_TAC THEN REWRITE_TAC[])

val OR_NEXT = TAC_PROOF(
        ([],“!Q P. NEXT (\t.P t \/ Q t) = \t. NEXT P t \/ NEXT Q t”),
        REPEAT GEN_TAC THEN REWRITE_TAC[NEXT]
        THEN BETA_TAC THEN REWRITE_TAC[])

val IMP_NEXT = TAC_PROOF(
        ([],“!Q P. NEXT (\t.P t ==> Q t) = \t. NEXT P t ==> NEXT Q t”),
        REPEAT GEN_TAC THEN REWRITE_TAC[NEXT]
        THEN BETA_TAC THEN REWRITE_TAC[])

val EQUIV_NEXT = TAC_PROOF(
        ([],“!Q P. NEXT (\t.P t = Q t) = \t. NEXT P t = NEXT Q t”),
        REPEAT GEN_TAC THEN REWRITE_TAC[NEXT]
        THEN BETA_TAC THEN REWRITE_TAC[])


val ALWAYS_NEXT = TAC_PROOF(
        ([],“!a. NEXT (ALWAYS a) = ALWAYS(NEXT a)”),
        GEN_TAC THEN REWRITE_TAC[NEXT,ALWAYS]
        THEN CONV_TAC (X_FUN_EQ_CONV “t0:num”)
        THEN BETA_TAC
        THEN REWRITE_TAC[ALWAYS] THEN BETA_TAC
        THEN REWRITE_TAC[ADD_CLAUSES])


val EVENTUAL_NEXT = TAC_PROOF(
        ([],“!a. NEXT (EVENTUAL a) = EVENTUAL(NEXT a)”),
        GEN_TAC THEN REWRITE_TAC[NEXT,EVENTUAL]
        THEN CONV_TAC (X_FUN_EQ_CONV “t0:num”)
        THEN BETA_TAC
        THEN REWRITE_TAC[EVENTUAL] THEN BETA_TAC
        THEN REWRITE_TAC[ADD_CLAUSES])

val WHEN_NEXT = TAC_PROOF(
        ([],“!a b.(NEXT (a WHEN b)) = (NEXT a) WHEN (NEXT b)”),
        REPEAT GEN_TAC
        THEN CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[NEXT,WHEN,WATCH] THEN BETA_TAC
        THEN REWRITE_TAC[ADD_CLAUSES]
        THEN EQ_TAC THEN STRIP_TAC
        THENL[EXISTS_TAC “\t.q(SUC t):bool”,
              EXISTS_TAC “\t.q(PRE t):bool”]
        THEN BETA_TAC
        THEN ASM_REWRITE_TAC[PRE])


val UNTIL_NEXT = TAC_PROOF(
        ([],“!a b.(NEXT (a UNTIL b)) = (NEXT a) UNTIL (NEXT b)”),
        REPEAT GEN_TAC
        THEN CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[NEXT,UNTIL,WATCH] THEN BETA_TAC
        THEN REWRITE_TAC[ADD_CLAUSES]
        THEN EQ_TAC THEN STRIP_TAC
        THENL[EXISTS_TAC “\t.q(SUC t):bool”,
              EXISTS_TAC “\t.q(PRE t):bool”]
        THEN BETA_TAC
        THEN ASM_REWRITE_TAC[PRE])

val BEFORE_NEXT = TAC_PROOF(
        ([],“!a b.(NEXT (a BEFORE b)) = (NEXT a) BEFORE (NEXT b)”),
        REPEAT GEN_TAC
        THEN CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[BEFORE_AS_WHEN,WHEN_NEXT,NOT_NEXT,OR_NEXT])

val SWHEN_NEXT = TAC_PROOF(
        ([],“!a b.(NEXT (a SWHEN b)) = (NEXT a) SWHEN (NEXT b)”),
        REWRITE_TAC[SWHEN_AS_WHEN,AND_NEXT,EVENTUAL_NEXT,WHEN_NEXT])

val SUNTIL_NEXT = TAC_PROOF(
        ([],“!a b.(NEXT (a SUNTIL b)) = (NEXT a) SUNTIL (NEXT b)”),
        REWRITE_TAC[SUNTIL_AS_UNTIL,AND_NEXT,EVENTUAL_NEXT,UNTIL_NEXT])

val SBEFORE_NEXT = TAC_PROOF(
        ([],“!a b.(NEXT (a SBEFORE b)) = (NEXT a) SBEFORE (NEXT b)”),
        REPEAT GEN_TAC
        THEN CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[SBEFORE_AS_BEFORE,AND_NEXT,BEFORE_NEXT,EVENTUAL_NEXT])


(* ************************************************************ *)
(*              Recursion Theorems                              *)
(* ************************************************************ *)


val NEXT2 = prove(``NEXT P x = P (SUC x)``,
                  REWRITE_TAC [NEXT] THEN BETA_TAC THEN REWRITE_TAC []);


val ALWAYS_REC = TAC_PROOF(
        ([],“ALWAYS P t0 = (P t0 /\ NEXT (ALWAYS P) t0)”),
        REWRITE_TAC [NEXT2,ALWAYS] THEN
        REWRITE_TAC[ADD_CLAUSES]
        THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[
                LEFT_FORALL_TAC “0” THEN UNDISCH_HD_TAC
                THEN REWRITE_TAC[ADD_CLAUSES],
                LEFT_FORALL_TAC “SUC t” THEN UNDISCH_HD_TAC
                THEN REWRITE_TAC[ADD_CLAUSES],
                SPEC_TAC(“t:num”,“t:num”) THEN INDUCT_TAC
                THEN ASM_REWRITE_TAC[ADD_CLAUSES]])


val EVENTUAL_ALWAYS_THM = TAC_PROOF(
        ([],“EVENTUAL P = \t.~ALWAYS (\t.~P t) t”),
        CONV_TAC (X_FUN_EQ_CONV “t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[EVENTUAL,ALWAYS] THEN BETA_TAC
        THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
        THEN REWRITE_TAC[])



val EVENTUAL_REC = TAC_PROOF(
        ([],“EVENTUAL P t0 = (P t0 \/ NEXT (EVENTUAL P) t0)”),
        PURE_ONCE_REWRITE_TAC[TAC_PROOF(([],“(a=b) = (~a= ~b)”),
                                BOOL_CASES_TAC “a:bool” THEN REWRITE_TAC[])]
        THEN REWRITE_TAC[DE_MORGAN_THM,EVENTUAL_ALWAYS_THM]
        THEN BETA_TAC
        THEN SUBST1_TAC(SPECL[“t0:num”,“(\t:num.~P t)”](GEN_ALL ALWAYS_REC))
        THEN BETA_TAC THEN BETA_TAC
        THEN SUBST1_TAC(SPEC“ALWAYS (\t. ~(P t))”NOT_NEXT)
        THEN BETA_TAC THEN REWRITE_TAC[])


val WATCH_REC = TAC_PROOF(
        ([],“(q WATCH b) t0 =
                 ~q t0 /\ (if b t0 then (NEXT (ALWAYS q) t0)
                                else (NEXT (q WATCH b) t0))”),
        PURE_REWRITE_TAC[WATCH,NEXT,ALWAYS]
        THEN BETA_TAC THEN EQ_TAC THEN STRIP_TAC
        THENL[
          ASM_REWRITE_TAC[] THEN COND_CASES_TAC
          THENL[
            REWRITE_TAC[ADD_CLAUSES] THEN INDUCT_TAC
            THEN ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[ADD_CLAUSES],
            REWRITE_TAC[EQT_ELIM(ARITH_CONV“SUC(t'+SUC t0) = SUC((SUC t')+t0)”)]
            THEN ASM_REWRITE_TAC[ADD_CLAUSES]
            THEN LEFT_NO_FORALL_TAC 1 “0”
            THEN RULE_ASSUM_TAC (REWRITE_RULE[ADD_CLAUSES])
            THEN ASM_REWRITE_TAC[]],
          ASM_REWRITE_TAC[]
          THEN RULE_ASSUM_TAC (REWRITE_RULE[EQT_ELIM
                              (ARITH_CONV“SUC(t'+SUC t0) = SUC((SUC t')+t0)”)])
          THEN DISJ_CASES_TAC (SPEC“(b:num->bool) t0” BOOL_CASES_AX)
          THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC (REWRITE_RULE[x])
                               THEN REWRITE_TAC[x] THEN ASSUME_TAC x)
          THENL[
            RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])
            THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]
            THEN POP_ASSUM (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[],
            INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]]])


val WHEN_REC = TAC_PROOF(
  ([],“(a WHEN b) t0 = if b t0 then a t0 else NEXT (a WHEN b) t0”),
  PURE_REWRITE_TAC[NEXT2,WHEN_SIGNAL]  THEN BETA_TAC
  THEN DISJ_CASES_TAC(SPEC“(b:num->bool) t0” BOOL_CASES_AX)
  THEN ASM_REWRITE_TAC[]
  THENL[
      EQ_TAC THEN STRIP_TAC
      THENL[
          LEFT_FORALL_TAC “0”
          THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[NOT_LESS_0,ADD_CLAUSES],
          GEN_TAC THEN STRIP_TAC
          THEN RULE_ASSUM_TAC((CONV_RULE(ONCE_DEPTH_CONV CONTRAPOS_CONV))
                           handle _=>(fn x=> x))
          THEN LEFT_NO_FORALL_TAC 1 “0”
          THEN UNDISCH_HD_TAC
          THEN ASM_REWRITE_TAC[ADD_CLAUSES]
          THEN REWRITE_TAC[NOT_LESS,LESS_EQ_0]
          THEN DISCH_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]],
      REWRITE_TAC[ADD_CLAUSES]
      THEN EQ_TAC THEN STRIP_TAC
      THENL[
          GEN_TAC THEN LEFT_FORALL_TAC “SUC delta”
          THEN STRIP_TAC
          THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])
          THEN POP_NO_ASSUM 2 MATCH_MP_TAC
          THEN ASM_REWRITE_TAC[] THEN INDUCT_TAC
          THEN ASM_REWRITE_TAC[ADD_CLAUSES,LESS_MONO_EQ],
          INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES,NOT_LESS_0]
          THEN LEFT_NO_FORALL_TAC 1 “delta:num”
          THEN STRIP_TAC THEN POP_NO_ASSUM 2 MATCH_MP_TAC
          THEN ASM_REWRITE_TAC[]
          THEN GEN_TAC THEN LEFT_NO_FORALL_TAC 1 “SUC t”
          THEN UNDISCH_HD_TAC THEN REWRITE_TAC[LESS_MONO_EQ,ADD_CLAUSES]]])



val UNTIL_REC = TAC_PROOF(
        ([],“(a UNTIL b) t0 = (~b t0 ==> a t0 /\ NEXT (a UNTIL b) t0)”),
        PURE_REWRITE_TAC[UNTIL_AS_WHEN,NEXT]
        THEN SUBST1_TAC(SPECL[“t0:num”,“\t:num. a t ==> b t”,“b:num->bool”]
                        (GEN_ALL WHEN_REC))
        THEN REWRITE_TAC[NEXT] THEN BETA_TAC
        THEN MAP_EVERY BOOL_CASES_TAC [“(b:num->bool) t0”,“(a:num->bool) t0”]
        THEN REWRITE_TAC[])


val BEFORE_REC = TAC_PROOF(
        ([],“(a BEFORE b) t0 = ~b t0 /\ (a t0 \/ NEXT (a BEFORE b) t0)”),
        REWRITE_TAC[BEFORE_AS_WHEN_UNTIL]
        THEN CONV_TAC(RATOR_CONV(REWRITE_CONV[WHEN_REC,UNTIL_REC]))
        THEN BETA_TAC THEN REWRITE_TAC[AND_NEXT] THEN BETA_TAC
        THEN PROP_TAC)


val SWHEN_REC = TAC_PROOF(
  ([],“(a SWHEN b) t0 = (if (b t0) then (a t0) else (NEXT (a SWHEN b) t0))”),
  REWRITE_TAC[SWHEN_AS_WHEN,AND_NEXT]
  THEN CONV_TAC(RATOR_CONV(REWRITE_CONV[WHEN_REC,EVENTUAL_REC]))
  THEN BETA_TAC THEN PROP_TAC)


val SUNTIL_REC = TAC_PROOF(
        ([],“(a SUNTIL b) t0 = ~(b t0) ==> a t0 /\ NEXT (a SUNTIL b) t0”),
        REWRITE_TAC[SUNTIL_AS_UNTIL,AND_NEXT]
        THEN CONV_TAC(RATOR_CONV(REWRITE_CONV[UNTIL_REC,EVENTUAL_REC]))
        THEN BETA_TAC THEN PROP_TAC)


val SBEFORE_REC = TAC_PROOF(
        ([],“(a SBEFORE b) t0 = ~b t0 /\ (a t0 \/ NEXT (a SBEFORE b) t0)”),
        REWRITE_TAC[SBEFORE_AS_SWHEN,AND_NEXT]
        THEN CONV_TAC(RATOR_CONV(REWRITE_CONV[SWHEN_REC,EVENTUAL_REC]))
        THEN BETA_TAC THEN PROP_TAC)


(*---------------------------------------------------------------------------
      Useful simplifications
 ---------------------------------------------------------------------------*)

val WHEN_SIMP = TAC_PROOF(
        ([],“ ( ((\t.F) WHEN b) = ALWAYS(\t.~b t)) /\
                ( ((\t.T) WHEN b) = \t.T) /\
                ( (a WHEN (\t.F)) = \t.T) /\
                ( (a WHEN (\t.T)) = \t. a t) /\
                ( (a WHEN a) = \t.T)”),
        CONV_TAC(DEPTH_CONV(X_FUN_EQ_CONV“t0:num”))
        THEN REWRITE_TAC[WHEN_SIGNAL,ALWAYS]
        THEN BETA_TAC THEN REWRITE_TAC[DE_MORGAN_THM]
        THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
        THEN REWRITE_TAC[TAC_PROOF(([],“~(a==>~b) = a/\b”),PROP_TAC)]
        THEN MY_MP_TAC “!delta.(!t.~(t<delta)) = (delta=0)”
        THENL[
            GEN_TAC THEN REWRITE_TAC[NOT_LESS] THEN EQ_TAC THEN REPEAT STRIP_TAC
            THEN ASM_REWRITE_TAC[] THENL[LEFT_FORALL_TAC “0”,ALL_TAC]
            THEN UNDISCH_HD_TAC THEN CONV_TAC ARITH_CONV,
            DISCH_TAC]
        THEN POP_ASSUM REWRITE1_TAC
        THEN REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[
            UNDISCH_NO_TAC 1 THEN REWRITE_TAC[]
            THEN DISJ_CASES_TAC DELTA_CASES THEN RES_TAC
            THEN LEFT_EXISTS_TAC
            THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
            THEN REWRITE_TAC[DE_MORGAN_THM] THEN EXISTS_TAC“d:num”
            THEN ASM_REWRITE_TAC[] THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
            THEN ASM_REWRITE_TAC[TAC_PROOF(([],“~(a/\b) = a==>~b”),PROP_TAC)],
            ASM_REWRITE_TAC[],
            LEFT_FORALL_TAC “0” THEN UNDISCH_HD_TAC
            THEN REWRITE_TAC[ADD_CLAUSES],
            ASM_REWRITE_TAC[ADD_CLAUSES]])




val UNTIL_SIMP = TAC_PROOF(
        ([],“ ( ((\t.F) UNTIL b) = \t.b t) /\
                ( ((\t.T) UNTIL b) = \t.T) /\
                ( (a UNTIL (\t.F)) = ALWAYS a) /\
                ( (a UNTIL (\t.T)) = \t. T) /\
                ( (a UNTIL a) = \t.a t)”),
        CONV_TAC(DEPTH_CONV(X_FUN_EQ_CONV“t0:num”))
        THEN REWRITE_TAC[UNTIL_AS_WHEN,WHEN_SIMP] THEN BETA_TAC
        THEN CONV_TAC(DEPTH_CONV ETA_CONV)
        THEN REWRITE_TAC[WHEN_SIMP]
        THEN CONV_TAC(DEPTH_CONV ETA_CONV)
        THEN REWRITE_TAC[])





val BEFORE_SIMP = TAC_PROOF(
        ([],“ ( ((\t.F) BEFORE b) = ALWAYS (\t.~b t)) /\
                ( ((\t.T) BEFORE b) = \t.~ b t) /\
                ( (a BEFORE (\t.F)) = \t. T) /\
                ( (a BEFORE (\t.T)) = \t. F) /\
                ( (a BEFORE a) = ALWAYS (\t.~a t))”),
        CONV_TAC(DEPTH_CONV(X_FUN_EQ_CONV“t0:num”))
        THEN REWRITE_TAC[BEFORE_AS_WHEN,WHEN_SIMP] THEN BETA_TAC
        THEN REWRITE_TAC[WHEN_SIGNAL,ALWAYS] THEN BETA_TAC
        THEN REWRITE_TAC[TAC_PROOF(([],“(a/\b==>~b) = a==>~b”),PROP_TAC)]
        THEN REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC
        THENL[
            DISJ_CASES_TAC DELTA_CASES THEN RES_TAC
            THEN LEFT_EXISTS_TAC THEN LEFT_NO_FORALL_TAC 2 “d:num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[],
            DISJ_CASES_TAC(SPEC“a:num->bool”(GEN“b:num->bool”DELTA_CASES))
            THEN RES_TAC THEN LEFT_EXISTS_TAC THEN LEFT_NO_FORALL_TAC 2 “d:num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]])





val SWHEN_SIMP = TAC_PROOF(
        ([],“ ( ((\t.F) SWHEN b) = \t.F) /\
                ( ((\t.T) SWHEN b) = EVENTUAL b) /\
                ( (a SWHEN (\t.F)) = \t.F) /\
                ( (a SWHEN (\t.T)) = \t. a t) /\
                ( (a SWHEN a) = EVENTUAL a)”),
        CONV_TAC(DEPTH_CONV(X_FUN_EQ_CONV“t0:num”))
        THEN REWRITE_TAC[SWHEN_AS_WHEN,WHEN_SIMP] THEN BETA_TAC
        THEN REWRITE_TAC[EVENTUAL,ALWAYS] THEN BETA_TAC
        THEN REWRITE_TAC[DE_MORGAN_THM]
        THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
        THEN REWRITE_TAC[TAC_PROOF(([],“b\/~b”),PROP_TAC)])




val SUNTIL_SIMP = TAC_PROOF(
        ([],“ ( ((\t.F) SUNTIL b) = \t.b t) /\
                ( ((\t.T) SUNTIL b) = EVENTUAL b) /\
                ( (a SUNTIL (\t.F)) = \t.F) /\
                ( (a SUNTIL (\t.T)) = \t.T) /\
                ( (a SUNTIL a) = \t. a t)”),
        CONV_TAC(DEPTH_CONV(X_FUN_EQ_CONV“t0:num”))
        THEN REWRITE_TAC[SUNTIL_AS_UNTIL,UNTIL_SIMP] THEN BETA_TAC
        THEN REWRITE_TAC[EVENTUAL,ALWAYS] THEN BETA_TAC
        THEN MY_MP_TAC“!b.(!t0. b t0 /\ (?t. b(t+t0)) = b t0)”
        THENL[
            REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
            THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC“0”
            THEN ASM_REWRITE_TAC[ADD_CLAUSES],
            DISCH_TAC]
        THEN ASM_REWRITE_TAC[])




val SBEFORE_SIMP = TAC_PROOF(
        ([],“ ( ((\t.F) SBEFORE b) = \t.F) /\
                ( ((\t.T) SBEFORE b) = \t.~b t) /\
                ( (a SBEFORE (\t.F)) = EVENTUAL a) /\
                ( (a SBEFORE (\t.T)) = \t.F) /\
                ( (a SBEFORE a) = \t.F)”),
        CONV_TAC(DEPTH_CONV(X_FUN_EQ_CONV“t0:num”))
        THEN REWRITE_TAC[SBEFORE_AS_BEFORE,BEFORE_SIMP] THEN BETA_TAC
        THEN REWRITE_TAC[EVENTUAL,ALWAYS] THEN BETA_TAC
        THEN REWRITE_TAC[DE_MORGAN_THM]
        THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
        THEN REWRITE_TAC[TAC_PROOF(([],“b\/~b”),PROP_TAC)])





val WHEN_EVENT = TAC_PROOF(
        ([],“a WHEN b = (\t.a t /\ b t) WHEN b”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[WHEN,WATCH] THEN BETA_TAC THEN EQ_TAC
        THEN REPEAT STRIP_TAC THEN EXISTS_TAC“q:num->bool”
        THEN ASM_REWRITE_TAC[] THEN GEN_TAC
        THEN LEFT_FORALL_TAC“t:num” THEN UNDISCH_HD_TAC
        THEN PROP_TAC)

val UNTIL_EVENT = TAC_PROOF(
        ([],“a UNTIL b = (\t.a t /\ ~b t) UNTIL b”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[UNTIL,WATCH] THEN BETA_TAC THEN EQ_TAC
        THEN REPEAT STRIP_TAC THEN EXISTS_TAC“q:num->bool”
        THEN ASM_REWRITE_TAC[] THEN GEN_TAC
        THEN LEFT_FORALL_TAC“t:num” THEN UNDISCH_HD_TAC
        THEN PROP_TAC)

val BEFORE_EVENT = TAC_PROOF(
        ([],“a BEFORE b = (\t.a t /\ ~b t) BEFORE b”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[BEFORE,WATCH] THEN BETA_TAC THEN EQ_TAC
        THEN REPEAT STRIP_TAC THEN EXISTS_TAC“q:num->bool”
        THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC
        THEN EXISTS_TAC“t:num” THEN ASM_REWRITE_TAC[])



val SWHEN_EVENT = TAC_PROOF(
        ([],“a SWHEN b = (\t.a t /\ b t) SWHEN b”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[SWHEN,WATCH] THEN BETA_TAC THEN EQ_TAC
        THEN REPEAT STRIP_TAC THEN EXISTS_TAC“q:num->bool”
        THEN ASM_REWRITE_TAC[]
        THEN EXISTS_TAC“t:num” THEN ASM_REWRITE_TAC[])

val SUNTIL_EVENT = TAC_PROOF(
        ([],“a SUNTIL b = (\t.a t /\ ~b t) SUNTIL b”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[SUNTIL,WATCH] THEN BETA_TAC THEN EQ_TAC
        THEN REPEAT STRIP_TAC THEN EXISTS_TAC“q:num->bool”
        THEN ASM_REWRITE_TAC[] THEN CONJ_TAC
        THENL[
            ASM_REWRITE_TAC[TAC_PROOF(([],“q\/b\/a/\~b=q\/b\/a”),PROP_TAC)],
            EXISTS_TAC“t:num” THEN ASM_REWRITE_TAC[],
            UNDISCH_NO_TAC 1 THEN
            REWRITE_TAC[TAC_PROOF(([],“q\/b\/a/\~b=q\/b\/a”),PROP_TAC)],
            EXISTS_TAC“t:num” THEN ASM_REWRITE_TAC[]])


val SBEFORE_EVENT = TAC_PROOF(
        ([],“a SBEFORE b = (\t.a t /\ ~b t) SBEFORE b”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[SBEFORE,WATCH] THEN BETA_TAC THEN EQ_TAC
        THEN REPEAT STRIP_TAC THEN EXISTS_TAC“q:num->bool”
        THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC“t:num”
        THEN ASM_REWRITE_TAC[])



val IMMEDIATE_EVENT = TAC_PROOF(
        ([],“b t0 ==>
                (!a. (a WHEN b) t0 = a t0) /\
                (!a. (a UNTIL b) t0 = T) /\
                (!a. (a BEFORE b) t0 = F) /\
                (!a. (a SWHEN b) t0 = a t0) /\
                (!a. (a SUNTIL b) t0 = T) /\
                (!a. (a SBEFORE b) t0 = F)”),
        DISCH_TAC
        THEN ASM_REWRITE_TAC[WHEN_REC,UNTIL_REC,BEFORE_REC]
        THEN ASM_REWRITE_TAC[SWHEN_REC,SUNTIL_REC,SBEFORE_REC])


val NO_EVENT = TAC_PROOF(
        ([],“ALWAYS(\t.~b t) t0 ==>
                (!a. (a WHEN b) t0 = T) /\
                (!a. (a UNTIL b) t0 = ALWAYS a t0) /\
                (!a. (a BEFORE b) t0 = T) /\
                (!a. (a SWHEN b) t0 = F) /\
                (!a. (a SUNTIL b) t0 = F) /\
                (!a. (a SBEFORE b) t0 = EVENTUAL a t0)”),
        REWRITE_TAC[ALWAYS,EVENTUAL] THEN BETA_TAC THEN DISCH_TAC
        THEN ASM_REWRITE_TAC[WHEN_SIGNAL,UNTIL_SIGNAL,BEFORE_SIGNAL]
        THEN ASM_REWRITE_TAC[SWHEN_SIGNAL,SUNTIL_SIGNAL,SBEFORE_SIGNAL])


val SOME_EVENT = TAC_PROOF(
  ([],“ (EVENTUAL b t0 = (!a. (a WHEN b) t0 = (a SWHEN b) t0)) /\
          (EVENTUAL b t0 = (!a. (a UNTIL b) t0 = (a SUNTIL b) t0)) /\
          (EVENTUAL b t0 = (!a. (a BEFORE b) t0 = (a SBEFORE b) t0))”),
  REPEAT STRIP_TAC >> EQ_TAC >> REPEAT STRIP_TAC
  >> REWRITE_TAC[SWHEN_AS_WHEN,SUNTIL_AS_UNTIL,BEFORE_AS_SBEFORE]
  >> BETA_TAC >> ASM_REWRITE_TAC[]
  >> (MATCH_MP_TAC (TAC_PROOF(([],“~b ==> (a\/b=a)”),PROP_TAC)) ORELSE ALL_TAC)
  THENL[
      LEFT_FORALL_TAC “\t:num.T”,
      LEFT_FORALL_TAC “\t:num.T”,
      ALL_TAC,
      LEFT_FORALL_TAC “\t:num.F”]
  >> UNDISCH_HD_TAC
  >> REWRITE_TAC[WHEN_SIMP,SWHEN_SIMP,UNTIL_SIMP,SUNTIL_SIMP]
  >> REWRITE_TAC[BEFORE_SIMP,SBEFORE_SIMP,ALWAYS,EVENTUAL]
  >> BETA_TAC >> CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
  >> REWRITE_TAC[])



val MORE_EVENT = TAC_PROOF(
        ([],“   ((a WHEN b) = (\t. a t /\ b t) WHEN b) /\
                ((a UNTIL b) = (\t. a t /\ ~b t) UNTIL b) /\
                ((a BEFORE b) = (\t. a t /\ ~b t) BEFORE b) /\
                ((a SWHEN b) = (\t. a t /\ b t) SWHEN b) /\
                ((a SUNTIL b) = (\t. a t /\ ~b t) SUNTIL b) /\
                ((a SBEFORE b) = (\t. a t /\ ~b t) SBEFORE b)”),
        CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
        THEN REWRITE_TAC[WHEN_SIGNAL,SWHEN_SIGNAL,
                    UNTIL_SIGNAL,SUNTIL_SIGNAL,
                    BEFORE_SIGNAL,SBEFORE_SIGNAL]
        THEN BETA_TAC THEN REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC
        THEN RES_TAC THEN ASM_REWRITE_TAC[]
        THENL[
            EXISTS_TAC“t:num” THEN ASM_REWRITE_TAC[] THEN RES_TAC,
            EXISTS_TAC“t:num” THEN ASM_REWRITE_TAC[],
            EXISTS_TAC“delta:num” THEN ASM_REWRITE_TAC[],
            EXISTS_TAC“delta:num” THEN ASM_REWRITE_TAC[],
            EXISTS_TAC“delta:num” THEN ASM_REWRITE_TAC[]
            THEN REPEAT STRIP_TAC THEN RES_TAC,
            EXISTS_TAC“delta:num” THEN ASM_REWRITE_TAC[]
            THEN REPEAT STRIP_TAC THEN RES_TAC,
            EXISTS_TAC“delta:num” THEN ASM_REWRITE_TAC[]
            THEN POP_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LESS_EQ_REFL],
            EXISTS_TAC“delta:num” THEN ASM_REWRITE_TAC[]])



(*---------------------------------------------------------------------------
      Fixpoint theorems.
 ---------------------------------------------------------------------------*)

val WHEN_FIX = prove(
  “(y = \t:num. if b t then a t else y(t+1)) =
   ((y = a WHEN b) \/ (y = a SWHEN b))”,
  EQ_TAC >> REPEAT STRIP_TAC
  THENL[
      ALL_TAC,
      POP_ASSUM SUBST1_TAC >> CONV_TAC FUN_EQ_CONV >> BETA_TAC >> GEN_TAC
      >> CONV_TAC(RATOR_CONV(REWRITE_CONV[WHEN_REC]))
      >> REWRITE_TAC[NEXT] >> BETA_TAC >> REWRITE_TAC[ADD1],
      POP_ASSUM SUBST1_TAC >> CONV_TAC FUN_EQ_CONV >> BETA_TAC >> GEN_TAC
      >> CONV_TAC(RATOR_CONV(REWRITE_CONV[SWHEN_REC]))
      >> REWRITE_TAC[NEXT] >> BETA_TAC >> REWRITE_TAC[ADD1]]
  (* ----------------------------------------------------------------- *)
  >> MY_MP_TAC “!y. (y = (\t. if b t then a t else y(t+1)))
                  ==> !t0. (!t.~b(t+t0)) ==> (!t. y(t+t0):bool = y t0)”
  (* ----------------------------------------------------------------- *)
  THENL[
      GEN_TAC >> DISCH_TAC >> GEN_TAC >> DISCH_TAC
      >> INDUCT_TAC >> REWRITE_TAC[ADD_CLAUSES]
      >> POP_ASSUM(SUBST1_TAC o SYM)
      >> POP_NO_ASSUM 1 (fn x=> CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[x])))
      >> BETA_TAC >> ASM_REWRITE_TAC[ADD1],
      DISCH_TAC]
  (* ----------------------------------------------------------------- *)
  >> MY_MP_TAC “!y. (y = (\t. if b t then a t else y(t+1)))
                   ==> ( !delta t0. (!t. t<delta ==> ~b(t+t0))
                         ==> (!t. t<delta ==> (y(t+t0):bool = y t0)))”
  (* ----------------------------------------------------------------- *)
  THENL[
      GEN_TAC >> DISCH_TAC >> REPEAT GEN_TAC >> DISCH_TAC
      >> INDUCT_TAC >> REWRITE_TAC[ADD_CLAUSES] >> DISCH_TAC
      >> IMP_RES_TAC(EQT_ELIM(ARITH_CONV“SUC d <delta ==> d<delta”))
      >> RES_TAC
      >> POP_NO_ASSUM 10 (fn x=> CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[SYM x])))
      >> POP_NO_ASSUM 14 (fn x=> CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[x])))
      >> BETA_TAC >> ASM_REWRITE_TAC[ADD1],
      DISCH_TAC]
  (* ----------------------------------------------------------------- *)
  >> MY_MP_TAC
       “!y. (y = (\t. if b t then a t else y(t+1)))
               ==>
            !delta t0. b(delta+t0) ==> (y(delta+t0):bool = a(delta+t0))”
  (* ----------------------------------------------------------------- *)
  THENL[
      GEN_TAC >> DISCH_TAC >> REPEAT STRIP_TAC
      >> POP_NO_ASSUM 1 (fn x=> CONV_TAC(RATOR_CONV(ONCE_REWRITE_CONV[x])))
      >> BETA_TAC >> ASM_REWRITE_TAC[],
      DISCH_TAC]
  (* ----------------------------------------------------------------- *)
  >> MY_MP_TAC “!y. (y = (\t. if b t then a t else y(t+1)))
                   ==> !t0. (?d.b(d+t0)) ==> (y t0 = (a WHEN b) t0)”
  (* ----------------------------------------------------------------- *)
  THENL[
      REPEAT STRIP_TAC
      >> IMP_RES_TAC(BETA_RULE(ISPEC“\d.b(d+t0):bool”WOP))
      >> REWRITE_TAC[WHEN_SIGNAL] >> EQ_TAC >> REPEAT STRIP_TAC
      THENL[
          MY_MP_TAC “n=(delta:num)”
          THENL[
              DISJ_CASES_TAC(SPECL[“delta:num”,“n:num”]LESS_CASES)
              THENL[RES_TAC,ALL_TAC]
              >> UNDISCH_HD_TAC >> REWRITE_TAC[LESS_OR_EQ] >> STRIP_TAC
              >> RES_TAC,
              DISCH_TAC]
          >> POP_ASSUM (SUBST1_TAC o SYM) >> POP_NO_TAC 0 >> POP_NO_TAC 0
          >> POP_NO_TAC 8 >> RES_TAC
          >> POP_NO_ASSUM 11 (SUBST1_TAC o SYM)
          >> DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV“(n=0)\/(0<n)”))
          THENL[
              POP_ASSUM REWRITE1_TAC >> REWRITE_TAC[ADD_CLAUSES]
              >> POP_NO_ASSUM 11 REWRITE1_TAC,
              ALL_TAC]
          >> IMP_RES_TAC LESS_ADD_1
          >> IMP_RES_TAC(EQT_ELIM(ARITH_CONV“(d=0+(p+1))==>(p<d)”))
          >> RES_TAC >> UNDISCH_NO_TAC 4
          >> POP_NO_ASSUM 22 (fn x=> CONV_TAC(RATOR_CONV(ONCE_REWRITE_CONV[x])))
          >> BETA_TAC >> ASM_TAC 2 REWRITE1_TAC
          >> IMP_RES_TAC(EQT_ELIM(ARITH_CONV“(d=0+(p+1))==>((p+t0)+1 = d+t0)”))
          >> ASM_TAC 0 REWRITE1_TAC,
          LEFT_FORALL_TAC “n:num” >> UNDISCH_HD_TAC
          >> ASM_TAC 1 REWRITE1_TAC >> ASM_TAC 0 REWRITE1_TAC
          >> POP_NO_TAC 7 >> POP_NO_TAC 6 >> RES_TAC
          >> POP_NO_ASSUM 8 (SUBST1_TAC o SYM)
          >> DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV“(n=0)\/(0<n)”))
          THENL[
              POP_ASSUM REWRITE1_TAC >> REWRITE_TAC[ADD_CLAUSES],
              ALL_TAC]
          >> IMP_RES_TAC LESS_ADD_1
          >> IMP_RES_TAC(EQT_ELIM(ARITH_CONV“(d=0+(p+1))==>(p<d)”))
          >> RES_TAC >> POP_NO_ASSUM 4 (SUBST1_TAC o SYM)
          >> POP_NO_ASSUM 22 (fn x=> CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[x])))
          >> BETA_TAC >> ASM_TAC 2 REWRITE1_TAC
          >> IMP_RES_TAC(EQT_ELIM(ARITH_CONV“(d=0+(p+1))==>((p+t0)+1 = d+t0)”))
          >> ASM_TAC 0 REWRITE1_TAC],
      DISCH_TAC]
  >> CONV_TAC(DEPTH_CONV FUN_EQ_CONV)
  >> ASSUME_TAC WHEN_SWHEN_LEMMA >> UNDISCH_HD_TAC
  >> ASM_CASES_TAC“!t1.?t2.b(t2+t1)” >> ASM_TAC 0 REWRITE1_TAC
  THENL[
  (* ----------------------------------------------------------------- *)
  (*      first case : !t1.?t2.b(t2+t1)                                *)
  (* ----------------------------------------------------------------- *)
      DISCH_TAC >> ASM_TAC 0 (REWRITE1_TAC o SYM o SPEC_ALL)
      >> REWRITE_TAC[WHEN_SIGNAL] >> BETA_TAC
      >> X_GEN_TAC “t0:num” >> EQ_TAC
      >> REPEAT STRIP_TAC
      THENL[
          RES_TAC >> POP_NO_ASSUM 8 (SUBST1_TAC o SYM)
          >> DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV“(delta=0)\/(0<delta)”))
          THENL[
              POP_ASSUM REWRITE1_TAC >> REWRITE_TAC[ADD_CLAUSES]
              >> ASM_TAC 11 REWRITE1_TAC,
              ALL_TAC]
          >> IMP_RES_TAC LESS_ADD_1
          >> IMP_RES_TAC(EQT_ELIM(ARITH_CONV“(d=0+(p+1))==>(p<d)”))
          >> RES_TAC >> UNDISCH_NO_TAC 5
          >> POP_NO_ASSUM 26 (fn x=> CONV_TAC(RATOR_CONV(ONCE_REWRITE_CONV[x])))
          >> BETA_TAC >> ASM_TAC 3 REWRITE1_TAC
          >> IMP_RES_TAC(EQT_ELIM(ARITH_CONV“(d=0+(p+1))==>((p+t0)+1 = d+t0)”))
          >> ASM_TAC 0 REWRITE1_TAC,
          LEFT_NO_FORALL_TAC 2 “t0:num” >> LEFT_EXISTS_TAC
          >> IMP_RES_TAC(BETA_RULE(ISPEC“\t2.b(t2+t0):bool”WOP))
          >> LEFT_NO_FORALL_TAC 3 “n:num” >> UNDISCH_HD_TAC
          >> ASM_TAC 0 REWRITE1_TAC >> ASM_TAC 1 REWRITE1_TAC
          >> POP_NO_TAC 2 >> RES_TAC
          >> POP_NO_ASSUM 8 (SUBST1_TAC o SYM)
          >> DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV“(n=0)\/(0<n)”))
          THENL[
              POP_ASSUM REWRITE1_TAC >> REWRITE_TAC[ADD_CLAUSES],
              ALL_TAC]
          >> IMP_RES_TAC LESS_ADD_1
          >> IMP_RES_TAC(EQT_ELIM(ARITH_CONV“(d=0+(p+1))==>(p<d)”))
          >> RES_TAC >> POP_NO_ASSUM 4 (SUBST1_TAC o SYM)
          >> POP_NO_ASSUM 29 (fn x=> CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[x])))
          >> BETA_TAC >> ASM_TAC 2 REWRITE1_TAC
          >> IMP_RES_TAC(EQT_ELIM(ARITH_CONV“(d=0+(p+1))==>((p+t0)+1 = d+t0)”))
          >> ASM_TAC 0 REWRITE1_TAC],
      ALL_TAC]
  (* ----------------------------------------------------------------- *)
  (*      second case : ?t1.!t2.~b(t2+t1)                              *)
  (* ----------------------------------------------------------------- *)
  >> UNDISCH_HD_TAC >> CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
  >> CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV) >> DISCH_TAC
  >> LEFT_EXISTS_TAC >> DISCH_TAC >> LEFT_EXISTS_TAC
  >> IMP_RES_TAC(BETA_RULE(ISPEC“\t1.!t2.~b(t2+t1)”WOP))
  >> POP_NO_TAC 3 >> UNDISCH_HD_TAC
  >> CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
  >> REWRITE_TAC[] >> DISCH_TAC
  (* ----------------------------------------------------------------- *)
  >> MY_MP_TAC“!y. (y = (\t. if b t then a t else y(t+1)))
                   ==> !m. m<n ==> (y m = (a WHEN b) m)”
  (* ----------------------------------------------------------------- *)
  THENL[
      REPEAT STRIP_TAC >> POP_NO_TAC 9 >> RES_TAC,
      DISCH_TAC]
  (* ----------------------------------------------------------------- *)
  >> MY_MP_TAC“!y:num->bool. (y = (\t. if b t then a t else y(t+1)))
                   ==> !m. y(m+n) = y n”
  (* ----------------------------------------------------------------- *)
  THENL[
      GEN_TAC >> DISCH_TAC >> POP_NO_TAC 9 >> RES_TAC,
      DISCH_TAC]
  (* ----------------------------------------------------------------- *)
  >> MY_MP_TAC“!m. m<n ==> (y m = (a WHEN b) m)”
  (* ----------------------------------------------------------------- *)
  THENL[
      POP_NO_ASSUM 1 MATCH_MP_TAC >> POP_NO_ASSUM 8 (REWRITE1_TAC o SYM),
      DISCH_TAC]
  (* ----------------------------------------------------------------- *)
  >> MY_MP_TAC“!m. m<n ==> ((a SWHEN b) m = (a WHEN b) m)”
  (* ----------------------------------------------------------------- *)
  THENL[
      POP_NO_ASSUM 2 MATCH_MP_TAC >> CONV_TAC FUN_EQ_CONV >> GEN_TAC
      >> CONV_TAC(RATOR_CONV(REWRITE_CONV[SWHEN_REC]))
      >> REWRITE_TAC[NEXT] >> BETA_TAC >> REWRITE_TAC[ADD1],
      DISCH_TAC]
  >> ASM_CASES_TAC “(y:num->bool) n”
  THENL[
      DISJ1_TAC >> GEN_TAC
      >> DISJ_CASES_TAC(SPECL[“n':num”,“n:num”] LESS_CASES)
      THENL[RES_TAC,ALL_TAC]
      >> IMP_RES_TAC LESS_EQUAL_ADD
      >> POP_ASSUM SUBST1_TAC >> POP_NO_TAC 0
      >> ONCE_REWRITE_TAC[ADD_SYM] >> RES_TAC
      >> ASM_TAC 12 REWRITE1_TAC
      >> ASM_REWRITE_TAC[WHEN_SIGNAL,ADD_ASSOC],
      DISJ2_TAC >> GEN_TAC
      >> DISJ_CASES_TAC(SPECL[“n':num”,“n:num”] LESS_CASES)
      THENL[
          RES_TAC >> ASM_TAC 12 REWRITE1_TAC >> ASM_TAC 15 REWRITE1_TAC,
          ALL_TAC]
      >> IMP_RES_TAC LESS_EQUAL_ADD
      >> POP_ASSUM SUBST1_TAC >> POP_NO_TAC 0
      >> ONCE_REWRITE_TAC[ADD_SYM] >> RES_TAC
      >> ASM_TAC 13 REWRITE1_TAC >> ASM_TAC 14 REWRITE1_TAC
      >> ASM_REWRITE_TAC[SWHEN_SIGNAL,ADD_ASSOC]])



val UNTIL_FIX =
  let val th1 = SPEC“z:num->bool”(GEN“a:num->bool”WHEN_FIX)
      val th2 = GENL[“b:num->bool”,“z:num->bool”]th1
      val th3 = SPECL[“\t:num.a t ==> b t”,“b:num->bool”]th2
      val th4 = REWRITE_RULE[SYM UNTIL_AS_WHEN,SYM SUNTIL_AS_SWHEN] th3
      val th5 = BETA_RULE th4
      val rwt = prove(“(if (a==>b) then b else y) = (~b ==> a /\ y)”,PROP_TAC)
      val th6 = REWRITE_RULE[rwt] th5
   in
      th6
  end



val ALWAYS_FIX =
    let val th1 = BETA_RULE(SPEC“\t:num.F”(GEN“a:num->bool”WHEN_FIX))
        val th2 = BETA_RULE(SPEC“\t:num.~a t”(GEN“b:num->bool”th1))
        val th3 = REWRITE_RULE[SYM ALWAYS_AS_WHEN] th2
        val th4 = REWRITE_RULE[prove(“(if ~a then F else y) = a/\y”,PROP_TAC)]
                              th3
        val th5 = TAC_PROOF(
                        ([],“(\t.F) SWHEN (\t.~a t) = \t.F”),
                        CONV_TAC FUN_EQ_CONV THEN BETA_TAC
                        THEN REWRITE_TAC[SWHEN_SIGNAL])
        val th6 = REWRITE_RULE[th5] th4
     in
        th6
    end




val EVENTUAL_FIX = TAC_PROOF(
      ([],“(y = \t. a t \/ y(t+1)) = (y = EVENTUAL a) \/ (y = (\t. T))”),
  let val th1 = SPECL[“\t:num.~y t”,“\t:num.~a t”](GEN_ALL ALWAYS_FIX)
      val th2 = BETA_RULE(CONV_RULE(DEPTH_CONV FUN_EQ_CONV) th1)
   in
      CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
      THEN ONCE_REWRITE_TAC[
             TAC_PROOF(([],“(y (n:num)=b) = (~y n = ~b)”),PROP_TAC)]
      THEN REWRITE_TAC[DE_MORGAN_THM,
              TAC_PROOF(([],“EVENTUAL a = \t.~ALWAYS (\t.~a t) t”),
                      CONV_TAC FUN_EQ_CONV THEN REWRITE_TAC[ALWAYS,EVENTUAL]
                      THEN BETA_TAC THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
                      THEN REWRITE_TAC[])]
      THEN BETA_TAC THEN REWRITE_TAC[th2]
  end)



val BEFORE_FIX = TAC_PROOF(
        ([],“!y.
                (y = (\t. ~(b t) /\ (a t \/ y (t + 1)))) =
                (y = a BEFORE b) \/ (y = a SBEFORE b)”),
        REWRITE_TAC[BEFORE_AS_WHEN,SBEFORE_AS_SWHEN]
        THEN ASSUME_TAC (Q.GEN `y`
                           (Q.INST [(`a` |-> `\t:num.~b t`),
                                    (`b` |-> `\t:num. a t \/ b t`)] WHEN_FIX))
        THEN GEN_TAC THEN UNDISCH_HD_TAC THEN BETA_TAC
        THEN DISCH_TAC THEN POP_ASSUM (REWRITE1_TAC o SYM o SPEC_ALL)
        THEN REWRITE_TAC[prove(“(if (a\/b) then ~b else y) = ~b/\(a\/y)”,
                               PROP_TAC)])


(* ************************************************************ *)
(*              Invariant Theorems of the Operators             *)
(* ************************************************************ *)

(* -------------------------------------------- *)
(*     Proving the invariant theorem of WHEN    *)
(* -------------------------------------------- *)


val WHEN_INVARIANT = TAC_PROOF(
  ([],“(a WHEN b) t0 =
       ?J.J t0 /\
          (!t. ~(b (t + t0)) /\ J (t + t0) ==> J (SUC (t + t0))) /\
          (!d. b (d + t0) /\ J (d + t0) ==> a (d + t0))”),
  EQ_TAC THENL[
  REWRITE_TAC[WHEN,WATCH] >> REPEAT STRIP_TAC
  >> EXISTS_TAC “a WHEN b” >> BETA_TAC
  >> REPEAT CONJ_TAC
  THENL[
      ALL_TAC,
      GEN_TAC >> SUBST1_TAC(SPEC“t+t0”(GEN“t0:num”WHEN_REC))
      >> REWRITE_TAC[NEXT] >> BETA_TAC
      >> REPEAT STRIP_TAC >> UNDISCH_HD_TAC >> ASM_REWRITE_TAC[],
      REWRITE_TAC[WHEN_SIGNAL] >> REPEAT STRIP_TAC
      >> LEFT_FORALL_TAC “0”
      >> UNDISCH_HD_TAC >> ASM_REWRITE_TAC[NOT_LESS_0,ADD_CLAUSES]]
  >> REWRITE_TAC[WHEN] >> ASSUME_TAC (SPEC_ALL WATCH_EXISTS)
  >> LEFT_EXISTS_TAC >> EXISTS_TAC “q':num->bool”
  >> UNDISCH_HD_TAC >> ASM_REWRITE_TAC[WATCH] >> STRIP_TAC
  >> MY_MP_TAC“!t.q'(t+t0):bool = q(t+t0)”
  THENL[INDUCT_TAC >> ASM_REWRITE_TAC[ADD_CLAUSES],ALL_TAC]
  >> DISCH_TAC >> ASM_REWRITE_TAC[],
  REPEAT STRIP_TAC >> PURE_REWRITE_TAC[WHEN]
  >> ASSUME_TAC (SPEC_ALL(REWRITE_RULE[WATCH]WATCH_EXISTS))
  >> LEFT_EXISTS_TAC >> EXISTS_TAC “q:num->bool” >> ASM_REWRITE_TAC[WATCH]
  >> DISJ_CASES_TAC DELTA_CASES
  THENL[ALL_TAC,UNDISCH_NO_TAC 1 >> PURE_REWRITE_TAC[WATCH_SIGNAL]
        >> ASM_REWRITE_TAC[]]
  >> LEFT_EXISTS_TAC >> UNDISCH_HD_TAC >> STRIP_TAC >> GEN_TAC
  >> DISJ_CASES_TAC (SPECL [“t:num”,“d:num”] LESS_LESS_CASES)
  THENL[MY_MP_TAC “!t. t<=d ==> J(t+t0)”
        THENL[INDUCT_TAC THENL[ASM_REWRITE_TAC[ADD_CLAUSES],ALL_TAC]
              >> REWRITE_TAC[SYM(SPEC_ALL LESS_EQ)]
              >> DISCH_TAC >> IMP_RES_TAC LESS_IMP_LESS_OR_EQ
              >> RES_TAC >> RES_TAC
              >> UNDISCH_HD_TAC >> ASM_REWRITE_TAC[ADD_CLAUSES],
              DISCH_TAC >> LEFT_FORALL_TAC “d:num”
              >> RULE_ASSUM_TAC(REWRITE_RULE[LESS_EQ_REFL])
              >> RES_TAC >> ASM_REWRITE_TAC[]],
        POP_ASSUM DISJ_CASES_TAC THENL[RES_TAC >> ASM_REWRITE_TAC[],ALL_TAC]
        >> UNDISCH_HD_TAC >> REWRITE_TAC[LESS_EQ] >> DISCH_TAC
        >> IMP_RES_TAC LESS_EQUAL_ADD >> POP_ASSUM SUBST1_TAC
        >> DISJ1_TAC >> ASSUME_TAC(SPEC_ALL WATCH_SIGNAL)
        >> UNDISCH_HD_TAC >> ASM_REWRITE_TAC[WATCH] >> STRIP_TAC
        >> RES_TAC >> LEFT_NO_FORALL_TAC 2 “p:num”
        >> UNDISCH_HD_TAC
        >> REWRITE_TAC[(EQT_ELIM(ARITH_CONV“(SUC d+p)+t0 = SUC(p+(d+t0))”))]]])



val UNTIL_INVARIANT =
  let
    val t0 = “t0:num”
    val a = “b:num->bool”
    val b = “\t:num. a t ==> b t”
    val lemma1 = BETA_RULE(SPECL[t0,b,a](GEN_ALL WHEN_INVARIANT))
    val lemma2 = X_FUN_EQ_CONV t0 (concl UNTIL_AS_WHEN)
    val lemma3 = EQ_MP lemma2 UNTIL_AS_WHEN
    val lemma4 = REWRITE_RULE[lemma1] lemma3
    val t1 = #conj2(dest_conj(#Body(dest_exists(rhs(concl(SPEC_ALL lemma4))))))
    val {Rand=t2,Rator=fa} = dest_comb(#conj2(dest_conj t1))
    val lemma5 = AP_TERM fa (ALPHA_CONV “t:num” t2)
    val lemma6 = ONCE_REWRITE_RULE[lemma5] lemma4
    val lemma7 = CONV_RULE(DEPTH_CONV AND_FORALL_CONV) lemma6
    val lemma8 = TAC_PROOF(
            ([],“((~(a==>b) /\ j ==> J) /\
                    ( (a==>b) /\ j ==> b) )
                  = (j /\ ~b ==> (a /\ J))”),
                    PROP_TAC)
  in
    REWRITE_RULE[lemma8]lemma7
  end



val BEFORE_INVARIANT = TAC_PROOF(
        ([],“(a BEFORE b) t0 =
                    ?J.
                        J t0 /\
                        (!t. J(t+t0) /\ ~a(t+t0) ==> J(SUC(t+t0))) /\
                        (!d. J(d+t0) ==> ~b(d+t0))”),
        REWRITE_TAC[BEFORE_AS_WHEN,WHEN_INVARIANT] THEN BETA_TAC
        THEN REWRITE_TAC[TAC_PROOF(([],“(a\/b)/\J==> ~b = J==>~b”),PROP_TAC)]
        THEN EQ_TAC THEN REPEAT STRIP_TAC THEN EXISTS_TAC“J:num->bool”
        THEN ASM_REWRITE_TAC[] THEN GEN_TAC
        THEN LEFT_FORALL_TAC“t:num” THEN UNDISCH_HD_TAC
        THEN LEFT_FORALL_TAC“t:num” THEN UNDISCH_HD_TAC
        THEN PROP_TAC)


val ALWAYS_INVARIANT = TAC_PROOF(
        ([],“ALWAYS a t0 = ?J. J t0 /\ (!t. J(t+t0) ==> a(t+t0)/\J(t+(t0+1)))”),
        REWRITE_TAC[ALWAYS_AS_UNTIL,UNTIL_INVARIANT,ONE,ADD_CLAUSES])



val EVENTUAL_INVARIANT = TAC_PROOF(
  ([],“EVENTUAL b t0 =
       ?J.
          (0<J t0) /\
          (!t. (J(SUC(t+t0)) < J(t+t0)) \/  (J(SUC(t+t0))=0)) /\
          (!t. (0<J(t+t0)) /\ (J(SUC(t+t0))=0) ==> b(t+t0))”),
  REWRITE_TAC[EVENTUAL] >> EQ_TAC >> REPEAT STRIP_TAC
  THENL[
      EXISTS_TAC “\x:num.SUC(t+t0)-x”
      >> BETA_TAC >> REPEAT STRIP_TAC
      THENL[
          CONV_TAC ARITH_CONV,
          CONV_TAC ARITH_CONV,
          IMP_RES_TAC(EQT_ELIM(ARITH_CONV
                  “(SUC(t+t0)-SUC(t'+t0)=0) ==> (t<=t')”))
          >> IMP_RES_TAC(EQT_ELIM(ARITH_CONV
                  “(0<SUC(t+t0)-(t'+t0)) ==> (t'<=t)”))
          >> IMP_RES_TAC(EQT_ELIM(ARITH_CONV
                  “(t<=t')/\(t'<=t)==>(t'=t)”))
          >> POP_ASSUM SUBST1_TAC >> ASM_TAC 5 REWRITE1_TAC],
      ALL_TAC]
  >> MY_MP_TAC “!n t0 J.
          (!t. J(SUC(t+t0))<J(t+t0) \/ (J(SUC(t+t0))=0))
          ==>
            ((J t0 <= n) ==> (J(n+t0)=0))”
  THENL[
   INDUCT_TAC >> REWRITE_TAC[ADD_CLAUSES] >> REPEAT STRIP_TAC
   THENL[
       RULE_ASSUM_TAC(REWRITE_RULE[LESS_EQ_0]) >> ASM_REWRITE_TAC[ADD_CLAUSES],
       REPEAT STRIP_TAC >> LEFT_NO_FORALL_TAC 2 “t0':num”
       >> LEFT_FORALL_TAC“\x.J'(SUC x):num”
       >> RULE_ASSUM_TAC BETA_RULE
       >> RULE_ASSUM_TAC(REWRITE_RULE[
               TAC_PROOF(([],“a==>(b==>c)= a/\b==>c”),PROP_TAC)])
       >> POP_ASSUM MATCH_MP_TAC >> CONJ_TAC
       THENL[
           GEN_TAC >> LEFT_NO_FORALL_TAC 1 “SUC t”
           >> UNDISCH_HD_TAC >> REWRITE_TAC[ADD_CLAUSES],
           LEFT_NO_FORALL_TAC 1 “0” >> UNDISCH_HD_TAC
           >> REWRITE_TAC[ADD_CLAUSES] >> STRIP_TAC
           >> ASM_REWRITE_TAC[] THENL[ALL_TAC,CONV_TAC ARITH_CONV]
           >> IMP_RES_TAC(EQT_ELIM(ARITH_CONV
               “!m n p. m<n /\ n<=p ==> m<p”))
           >> UNDISCH_NO_TAC 1 >> CONV_TAC ARITH_CONV]],
   DISCH_TAC
  ] >>
  LEFT_FORALL_TAC “(J:num->num) t0”
  >> LEFT_FORALL_TAC “t0:num”
  >> LEFT_FORALL_TAC “J:num->num”
  >> UNDISCH_HD_TAC >> ASM_REWRITE_TAC[LESS_EQ_REFL]
  >> DISCH_TAC
  >> IMP_RES_TAC(BETA_RULE(ISPEC“\t.J(t+t0)=0”WOP))
  >> DISJ_CASES_TAC(SPEC“n:num”num_CASES)
  THENL[
      UNDISCH_NO_TAC 2 >> ASM_REWRITE_TAC[ADD_CLAUSES]
      >> IMP_RES_TAC(EQT_ELIM(ARITH_CONV“0<x ==> ~(x=0)”))
      >> ASM_REWRITE_TAC[],
      LEFT_EXISTS_TAC >> LEFT_NO_FORALL_TAC 4 “n':num”
      >> EXISTS_TAC“n':num” >> POP_ASSUM MATCH_MP_TAC
      >> LEFT_NO_FORALL_TAC 1 “n':num”
      >> UNDISCH_HD_TAC >> ASM_REWRITE_TAC[LESS_SUC_REFL,
                  EQT_ELIM(ARITH_CONV“~(x=0) = (0<x)”)]
      >> DISCH_TAC >> POP_ASSUM REWRITE1_TAC
      >> UNDISCH_NO_TAC 1 >> ASM_REWRITE_TAC[ADD_CLAUSES]])






val SWHEN_INVARIANT = TAC_PROOF(
        ([],“(a SWHEN b) t0 =
             (?J1.J1 t0 /\
                (!t. ~b(t+t0) /\ J1(t+t0) ==> J1(SUC(t+t0))) /\
                (!d. b(d+t0) /\ J1(d+t0) ==> a(d+t0))) /\
             (?J2.
                0 < J2 t0 /\
                (!t. J2(SUC(t+t0))<J2(t+t0) \/ (J2(SUC(t+t0))=0)) /\
                (!t. 0<J2(t+t0) /\ (J2(SUC(t+t0))=0) ==> b(t+t0)))”),
        REWRITE_TAC[SWHEN_AS_WHEN,WHEN_INVARIANT,EVENTUAL_INVARIANT]
        THEN BETA_TAC THEN REWRITE_TAC[])




val SUNTIL_INVARIANT = TAC_PROOF(
        ([],“(a SUNTIL b) t0 =
             (?J1.J1 t0 /\
                (!t. J1(t+t0) /\ ~b(t+t0) ==> a(t+t0) /\ J1(SUC(t+t0)))) /\
             (?J2.
                0 < J2 t0 /\
                (!t. J2(SUC(t+t0))<J2(t+t0) \/ (J2(SUC(t+t0))=0)) /\
                (!t. 0<J2(t+t0) /\ (J2(SUC(t+t0))=0) ==> b(t+t0)))”),
        REWRITE_TAC[SUNTIL_AS_UNTIL,UNTIL_INVARIANT,EVENTUAL_INVARIANT]
        THEN BETA_TAC THEN REWRITE_TAC[])



val SBEFORE_INVARIANT = TAC_PROOF(
        ([],“(a SBEFORE b) t0 =
             (?J1. J1 t0 /\
                (!t.J1(t+t0) /\ ~a(t+t0) ==> J1(SUC(t+t0))) /\
                (!d.J1(d+t0) ==> ~b(d+t0))) /\
             (?J2.
                0 < J2 t0 /\
                (!t. J2(SUC(t+t0))<J2(t+t0) \/ (J2(SUC(t+t0))=0)) /\
                (!t. 0<J2(t+t0) /\ (J2(SUC(t+t0))=0) ==> a(t+t0)))”),
        REWRITE_TAC[SBEFORE_AS_BEFORE,BEFORE_INVARIANT,EVENTUAL_INVARIANT]
        THEN BETA_TAC THEN REWRITE_TAC[])




(* ************************************************************************* *)
(*              Negations of temporal expressions                            *)
(* ************************************************************************* *)

val NOT_ALWAYS = TAC_PROOF(
        ([],“~(ALWAYS a t0) = EVENTUAL (\t.~a t) t0”),
        REWRITE_TAC[ALWAYS,EVENTUAL] THEN BETA_TAC
        THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
        THEN REWRITE_TAC[])


val NOT_EVENTUAL = TAC_PROOF(
        ([],“~(EVENTUAL a t0) = ALWAYS (\t.~a t) t0”),
        REWRITE_TAC[ALWAYS,EVENTUAL] THEN BETA_TAC
        THEN CONV_TAC(DEPTH_CONV NOT_EXISTS_CONV)
        THEN REWRITE_TAC[])


val NOT_WHEN = TAC_PROOF(
        ([],“~((a WHEN b)t0) = ((\t.~a t) SWHEN b) t0”),
        REWRITE_TAC[WHEN_SIGNAL,SWHEN_SIGNAL] THEN BETA_TAC
        THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
        THEN REWRITE_TAC[TAC_PROOF(([],“~(a==>b) = a/\~b”),PROP_TAC)]
        THEN EQ_TAC THEN REPEAT STRIP_TAC THEN RES_TAC
        THEN EXISTS_TAC“delta:num” THEN ASM_REWRITE_TAC[])


val NOT_UNTIL = TAC_PROOF(
        ([],“~((a UNTIL b)t0) = ((\t.~a t) SBEFORE b) t0”),
        REWRITE_TAC[UNTIL_AS_SBEFORE] THEN BETA_TAC
        THEN REWRITE_TAC[])



val NOT_BEFORE = TAC_PROOF(
        ([],“~((a BEFORE b)t0) = ((\t.~a t) SUNTIL b) t0”),
        REWRITE_TAC[BEFORE_AS_SUNTIL] THEN BETA_TAC
        THEN REWRITE_TAC[])


val NOT_SWHEN =
    let
      val thm1 = BETA_RULE(SPEC“\t:num.~a t”(GEN“a:num->bool”NOT_WHEN))
      val thm2 = SYM(REWRITE_RULE[]thm1)
      val thm3 = (CONV_RULE(DEPTH_CONV ETA_CONV)) thm2
      val thm4 = ONCE_REWRITE_RULE[prove(“(a= ~b) = (~a=b)”,PROP_TAC)] thm3
     in thm4
    end


val NOT_SUNTIL = TAC_PROOF(
        ([],“~((a SUNTIL b)t0) = ((\t.~a t) BEFORE b) t0”),
        REWRITE_TAC[SUNTIL_AS_BEFORE] THEN BETA_TAC
        THEN REWRITE_TAC[DE_MORGAN_THM,NOT_ALWAYS])




val NOT_SBEFORE = TAC_PROOF(
        ([],“~((a SBEFORE b)t0) = ((\t.~a t) UNTIL b) t0”),
        REWRITE_TAC[SBEFORE_AS_UNTIL] THEN BETA_TAC
        THEN REWRITE_TAC[])


(* ************************************************************ *)
(*                      IDEMPOTENCY THEOREMS                    *)
(* ************************************************************ *)


val ALWAYS_IDEM = TAC_PROOF(
        ([],“ALWAYS a = ALWAYS (ALWAYS a)”),
        CONV_TAC (X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[ALWAYS_SIGNAL]
        THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[
            LEFT_FORALL_TAC “t' + t”THEN UNDISCH_HD_TAC
            THEN REWRITE_TAC[ADD_ASSOC],
            LEFT_FORALL_TAC “t:num” THEN LEFT_FORALL_TAC “0”
            THEN UNDISCH_HD_TAC THEN REWRITE_TAC[ADD_CLAUSES]])



val EVENTUAL_IDEM = TAC_PROOF(
        ([],“EVENTUAL a = EVENTUAL (EVENTUAL a)”),
        CONV_TAC (X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[EVENTUAL_SIGNAL]
        THEN EQ_TAC THEN STRIP_TAC
        THENL[
            EXISTS_TAC“t:num” THEN EXISTS_TAC“0”
            THEN ASM_REWRITE_TAC[ADD_CLAUSES],
            EXISTS_TAC“t'+t”THEN UNDISCH_HD_TAC
            THEN REWRITE_TAC[ADD_ASSOC]])



val WHEN_IDEM = TAC_PROOF(
  ([],“(a WHEN b) = ((a WHEN b) WHEN b)”),
  CONV_TAC (X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC
  THEN REWRITE_TAC[WHEN_SIGNAL] THEN EQ_TAC THEN REPEAT STRIP_TAC
  THENL[
      LEFT_NO_FORALL_TAC 4 “delta'+delta”
      THEN RULE_ASSUM_TAC(REWRITE_RULE[SYM(SPEC_ALL ADD_ASSOC)])
      THEN POP_ASSUM MATCH_MP_TAC
      THEN ASM_REWRITE_TAC[]
      THEN DISJ_CASES_TAC(SPEC“delta':num” num_CASES)
      THEN ASM_REWRITE_TAC[ADD_CLAUSES]
      THEN LEFT_EXISTS_TAC
      THEN POP_ASSUM (fn x=> SUBST1_TAC x THEN RULE_ASSUM_TAC(SUBS[x]))
      THEN LEFT_NO_FORALL_TAC 1 “0”
      THEN UNDISCH_HD_TAC
      THEN ASM_REWRITE_TAC[LESS_0,ADD_CLAUSES],
      LEFT_NO_FORALL_TAC 2 “delta:num” THEN UNDISCH_HD_TAC
      THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC
      THEN LEFT_FORALL_TAC“0” THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])
      THEN POP_ASSUM MATCH_MP_TAC
      THEN ASM_REWRITE_TAC[NOT_LESS_0]])



val UNTIL_IDEM = TAC_PROOF(
        ([],“(a UNTIL b) = ((a UNTIL b) UNTIL b)”),
        CONV_TAC (X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[UNTIL_SIGNAL]
        THEN RIGHT_LEMMA_DISJ_CASES_TAC DELTA_CASES
        THEN ASM_REWRITE_TAC[ADD_ASSOC]
        THENL[
            EQ_TAC THEN REPEAT STRIP_TAC,
            EQ_TAC THEN REPEAT STRIP_TAC
            THENL[
                LEFT_FORALL_TAC “t'+t”,
                LEFT_FORALL_TAC “t:num” THEN LEFT_FORALL_TAC “0”]
            THEN UNDISCH_HD_TAC THEN REWRITE_TAC[ADD_CLAUSES]]
        THENL[
            IMP_RES_TAC LESS_ADD
            THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(SUBS[SYM x]))
            THEN LEFT_FORALL_TAC“p:num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[ADD_ASSOC],
            LEFT_NO_FORALL_TAC 6 “d':num” THEN UNDISCH_HD_TAC
            THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
            THEN MY_MP_TAC“d'=d''+t”
            THENL[ALL_TAC,
                DISCH_TAC THEN POP_ASSUM(fn x=> RULE_ASSUM_TAC(SUBS[x]))
                THEN LEFT_FORALL_TAC“t'+t” THEN UNDISCH_HD_TAC
                THEN ASM_REWRITE_TAC[LESS_MONO_ADD_EQ,ADD_ASSOC]]
            THEN DISJ_CASES_TAC (SPECL[“d':num”,“d''+t”]LESS_LESS_CASES)
            THENL[ASM_REWRITE_TAC[], POP_ASSUM DISJ_CASES_TAC]
            THENL[
                ASM_TAC 5 (fn x=> ASSUME_TAC(MATCH_MP LESS_IMP_LESS_OR_EQ x))
                THEN ASM_TAC 0 (fn x=> ASSUME_TAC(MATCH_MP SUB_ADD x))
                THEN UNDISCH_NO_TAC 2
                THEN ASM_TAC 0 (fn x=> SUBST1_TAC(SYM x))
                THEN REWRITE_TAC[LESS_MONO_ADD_EQ]
                THEN DISCH_TAC THEN POP_NO_ASSUM 6 IMP_RES_TAC
                THEN UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[ADD_ASSOC],
                POP_NO_ASSUM 7 IMP_RES_TAC
                THEN UNDISCH_NO_TAC 5 THEN ASM_REWRITE_TAC[ADD_ASSOC]],
            LEFT_NO_FORALL_TAC 3 “d':num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
            THEN LEFT_FORALL_TAC “t:num”
            THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
            THEN LEFT_FORALL_TAC “d'-t”
            THEN ASM_TAC 2 (fn x=> ASSUME_TAC(MATCH_MP LESS_IMP_LESS_OR_EQ x))
            THEN ASM_TAC 0 (fn x=> ASSUME_TAC(MATCH_MP SUB_ADD x))
            THEN UNDISCH_NO_TAC 2
            THEN ONCE_REWRITE_TAC[SYM(SPECL[“t'':num”,
                        “d' - t”,“t:num”]LESS_MONO_ADD_EQ)]
            THEN ASM_REWRITE_TAC[ADD_ASSOC] THEN DISCH_TAC
            THEN LEFT_FORALL_TAC “0”
            THEN RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES])
            THEN RES_TAC])



val SWHEN_IDEM = TAC_PROOF(
        ([],“(a SWHEN b) = ((a SWHEN b) SWHEN b)”),
        CONV_TAC (X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC
        THEN REWRITE_TAC[SWHEN_SIGNAL] THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[
            EXISTS_TAC “delta:num” THEN ASM_REWRITE_TAC[]
            THEN EXISTS_TAC “0” THEN ASM_REWRITE_TAC[ADD_CLAUSES]
            THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV“~(t<0)”)],
            MY_MP_TAC “delta' = 0”
            THENL[
                DISJ_CASES_TAC(SPEC“delta':num”num_CASES)
                THEN ASM_REWRITE_TAC[] THEN LEFT_EXISTS_TAC
                THEN LEFT_NO_FORALL_TAC 3 “0” THEN UNDISCH_HD_TAC
                THEN POP_ASSUM SUBST1_TAC
                THEN ASM_REWRITE_TAC[ADD_CLAUSES,LESS_0],
                DISCH_TAC]
            THEN EXISTS_TAC “delta:num” THEN ASM_REWRITE_TAC[ADD_CLAUSES]
            THEN UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[ADD_CLAUSES]])



val SUNTIL_IDEM = TAC_PROOF(
  ([],“(a SUNTIL b) = ((a SUNTIL b) SUNTIL b)”),
  CONV_TAC (X_FUN_EQ_CONV“t0:num”) THEN GEN_TAC
  THEN REWRITE_TAC[SUNTIL_SIGNAL] THEN EQ_TAC THEN REPEAT STRIP_TAC
  THENL[
      EXISTS_TAC “delta:num” THEN ASM_REWRITE_TAC[]
      THEN GEN_TAC THEN DISCH_TAC THEN IMP_RES_TAC LESS_ADD
      THEN RES_TAC THEN ASM_REWRITE_TAC[]
      THEN EXISTS_TAC “p:num” THEN ASM_REWRITE_TAC[ADD_ASSOC]
      THEN GEN_TAC THEN DISCH_TAC THEN POP_NO_ASSUM 6 MATCH_MP_TAC
      THEN UNDISCH_NO_TAC 3 THEN UNDISCH_NO_TAC 0
      THEN CONV_TAC ARITH_CONV,
      ALL_TAC]
  THEN DISJ_CASES_TAC(SPEC“delta:num”num_CASES)
  THENL[
      EXISTS_TAC “0”
      THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV“~(t<0)”)]
      THEN UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[ADD_CLAUSES],
      ALL_TAC]
  THEN LEFT_EXISTS_TAC THEN POP_ASSUM (fn x=> RULE_ASSUM_TAC(REWRITE_RULE[x]))
  THEN LEFT_NO_FORALL_TAC 1 “0” THEN UNDISCH_HD_TAC
  THEN REWRITE_TAC[LESS_0,ADD_CLAUSES] THEN STRIP_TAC
  THEN EXISTS_TAC “delta:num” THEN ASM_REWRITE_TAC[])




val BEFORE_IDEM = TAC_PROOF(
        ([],“(a BEFORE b) = ((a BEFORE b) BEFORE b)”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN BETA_TAC THEN GEN_TAC
        THEN ONCE_REWRITE_TAC[TAC_PROOF(([],“(a=b) = (~a= ~b)”),PROP_TAC)]
        THEN REWRITE_TAC[NOT_BEFORE]
        THEN CONV_TAC(DEPTH_CONV ETA_CONV)
        THEN REWRITE_TAC[SYM SUNTIL_IDEM])



val SBEFORE_IDEM = TAC_PROOF(
        ([],“(a SBEFORE b) = ((a SBEFORE b) SBEFORE b)”),
        CONV_TAC(X_FUN_EQ_CONV“t0:num”) THEN BETA_TAC THEN GEN_TAC
        THEN ONCE_REWRITE_TAC[TAC_PROOF(([],“(a=b) = (~a= ~b)”),PROP_TAC)]
        THEN REWRITE_TAC[NOT_SBEFORE]
        THEN CONV_TAC(DEPTH_CONV ETA_CONV)
        THEN REWRITE_TAC[SYM UNTIL_IDEM])



(* ************************************************************ *)
(*      Signal Theorems for Translation to LinOrd               *)
(* ************************************************************ *)



val SUNTIL_LINORD = TAC_PROOF(
  ([],“(a SUNTIL b) t0 = ?t1. (t0<=t1) /\ b t1 /\ UPTO(t0,t1,a)”),
  REWRITE_TAC[SUNTIL_SIGNAL,UPTO] THEN EQ_TAC
  THENL[
      STRIP_TAC
      THEN EXISTS_TAC“delta+t0” THEN ASM_REWRITE_TAC[]
      THEN REPEAT STRIP_TAC THENL[CONV_TAC ARITH_CONV,ALL_TAC]
      THEN IMP_RES_TAC LESS_EQUAL_ADD
      THEN LEFT_NO_FORALL_TAC 4 “p:num”
      THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV
                  “(t2=t0+p) /\ (t2<delta+t0) ==> p<delta”))
      THEN RES_TAC THEN UNDISCH_NO_TAC 1
      THEN ONCE_REWRITE_TAC[ADD_SYM]
      THEN ASM_REWRITE_TAC[],
      DISCH_TAC
      THEN ASSUME_TAC(BETA_RULE(SPEC
                  “\t1.t0<=t1 /\ b t1 /\ (!t2. t0<=t2 /\ t2<t1 ==> a t2)”WOP))
      THEN UNDISCH_HD_TAC THEN POP_ASSUM REWRITE1_TAC
      THEN REPEAT STRIP_TAC
      THEN IMP_RES_TAC LESS_EQUAL_ADD THEN EXISTS_TAC“p:num”
      THEN REPEAT STRIP_TAC
      THENL[
          POP_NO_ASSUM 3 MATCH_MP_TAC
          THEN UNDISCH_HD_TAC THEN UNDISCH_HD_TAC
          THEN CONV_TAC ARITH_CONV,
          LEFT_NO_FORALL_TAC 3 “t+t0”
          THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
          THEN IMP_RES_TAC(EQT_ELIM(ARITH_CONV“t<p ==> t+t0<t0+p”))
          THEN POP_ASSUM REWRITE1_TAC
          THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV“t0<=t+t0”)]
          THEN REPEAT STRIP_TAC THEN POP_NO_ASSUM 5 MATCH_MP_TAC
          THEN ASM_REWRITE_TAC[] THEN UNDISCH_HD_TAC
          THEN UNDISCH_NO_TAC 2 THEN CONV_TAC ARITH_CONV,
          ONCE_REWRITE_TAC[ADD_SYM] THEN POP_ASSUM (SUBST1_TAC o SYM)
          THEN ASM_REWRITE_TAC[]
          ]
      ]);


val SWHEN_LINORD = prove(
  “(a SWHEN b) t0 = ?t1. (t0<=t1) /\ a t1 /\ b t1 /\ UPTO(t0,t1,(\t.~b t))”,
  REWRITE_TAC[SWHEN_SIGNAL,UPTO] THEN BETA_TAC THEN EQ_TAC
  THENL[
      STRIP_TAC
      THEN EXISTS_TAC“delta+t0” THEN ASM_REWRITE_TAC[]
      THEN REPEAT STRIP_TAC THENL[CONV_TAC ARITH_CONV,ALL_TAC]
      THEN IMP_RES_TAC LESS_EQUAL_ADD
      THEN LEFT_NO_FORALL_TAC 6 “p:num”
      THEN UNDISCH_NO_TAC 2 THEN ASM_REWRITE_TAC[]
      THEN ONCE_REWRITE_TAC[ADD_SYM]
      THEN POP_ASSUM MATCH_MP_TAC
      THEN UNDISCH_NO_TAC 1 THEN ASM_REWRITE_TAC[]
      THEN CONV_TAC ARITH_CONV,
      DISCH_TAC
      THEN ASSUME_TAC(BETA_RULE(SPEC
                  “\t1.t0<=t1 /\ a t1 /\ b t1 /\
                           (!t2. t0<=t2 /\ t2<t1 ==> ~b t2)”WOP))
      THEN UNDISCH_HD_TAC THEN POP_ASSUM REWRITE1_TAC
      THEN REPEAT STRIP_TAC
      THEN IMP_RES_TAC LESS_EQUAL_ADD THEN EXISTS_TAC“p:num”
      THEN REPEAT STRIP_TAC
      THENL[
          UNDISCH_HD_TAC THEN REWRITE_TAC[]
          THEN POP_NO_ASSUM 3 MATCH_MP_TAC
          THEN UNDISCH_HD_TAC THEN UNDISCH_HD_TAC
          THEN CONV_TAC ARITH_CONV,
          ONCE_REWRITE_TAC[ADD_SYM] THEN POP_ASSUM (SUBST1_TAC o SYM)
          THEN ASM_REWRITE_TAC[],
          ONCE_REWRITE_TAC[ADD_SYM] THEN POP_ASSUM (SUBST1_TAC o SYM)
          THEN ASM_REWRITE_TAC[]
          ]
      ]);




val SBEFORE_LINORD = prove(
  “(a SBEFORE b) t0 = ?t1. (t0<=t1) /\ a t1 /\ ~b t1 /\ UPTO(t0,t1,(\t.~b t))”,
  REWRITE_TAC[SBEFORE_SIGNAL,UPTO] THEN BETA_TAC THEN EQ_TAC
  THENL[
      STRIP_TAC
      THEN EXISTS_TAC“delta+t0” THEN ASM_REWRITE_TAC[]
      THEN REPEAT STRIP_TAC
      THENL[
          CONV_TAC ARITH_CONV,
          LEFT_NO_FORALL_TAC 1 “delta:num”
          THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[LESS_EQ_REFL],
          UNDISCH_HD_TAC THEN IMP_RES_TAC LESS_EQUAL_ADD
          THEN ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM]
          THEN POP_NO_ASSUM 3 MATCH_MP_TAC
          THEN UNDISCH_HD_TAC THEN UNDISCH_HD_TAC
          THEN CONV_TAC ARITH_CONV],
      DISCH_TAC
      THEN ASSUME_TAC(BETA_RULE(SPEC
                  “\t1.t0<=t1 /\ a t1 /\ ~b t1 /\
                          (!t2. t0<=t2 /\ t2<t1 ==> ~b t2)”WOP))
      THEN UNDISCH_HD_TAC THEN POP_ASSUM REWRITE1_TAC
      THEN REPEAT STRIP_TAC
      THEN IMP_RES_TAC LESS_EQUAL_ADD THEN EXISTS_TAC“p:num”
      THEN REPEAT STRIP_TAC
      THENL[
          ONCE_REWRITE_TAC[ADD_SYM] THEN POP_ASSUM (SUBST1_TAC o SYM)
          THEN ASM_REWRITE_TAC[],
          LEFT_NO_FORALL_TAC 4 “t+t0”
          THEN UNDISCH_HD_TAC THEN ASM_REWRITE_TAC[]
          THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV“t0<=t+t0”)]
          THEN UNDISCH_NO_TAC 1 THEN REWRITE_TAC[LESS_OR_EQ]
          THEN STRIP_TAC
          THENL[UNDISCH_HD_TAC THEN CONV_TAC ARITH_CONV,ALL_TAC]
          THEN POP_ASSUM (fn x => RULE_ASSUM_TAC(REWRITE_RULE[x]))
          THEN UNDISCH_HD_TAC THEN ONCE_REWRITE_TAC[ADD_SYM]
          THEN POP_ASSUM (SUBST1_TAC o SYM)
          THEN ASM_REWRITE_TAC[]
          ]
      ]);




val UNTIL_LINORD = prove(
  “(a UNTIL b) t0 = !t1. (t0<=t1) /\ ~b t1 /\ UPTO(t0,t1,(\t.~b t)) ==> a t1”,
  ONCE_REWRITE_TAC[TAC_PROOF(([],“(a=b) = (~a= ~b)”),PROP_TAC)]
  THEN REWRITE_TAC[NOT_UNTIL,SBEFORE_LINORD]
  THEN BETA_TAC THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
  THEN REWRITE_TAC[TAC_PROOF(([],“~(a==>b) = (a/\~b)”),PROP_TAC)]
  THEN EQ_TAC THEN REPEAT STRIP_TAC
  THENL[
      EXISTS_TAC“t1:num” THEN ASM_REWRITE_TAC[],
      EXISTS_TAC“t1:num” THEN ASM_REWRITE_TAC[]]
  );





val WHEN_LINORD = prove(
  “(a WHEN b) t0 = !t1. (t0<=t1) /\ b t1 /\ UPTO(t0,t1,(\t.~b t)) ==> a t1”,
  ONCE_REWRITE_TAC[TAC_PROOF(([],“(a=b) = (~a= ~b)”),PROP_TAC)]
  THEN REWRITE_TAC[NOT_WHEN,SWHEN_LINORD]
  THEN BETA_TAC THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
  THEN REWRITE_TAC[TAC_PROOF(([],“~(a==>b) = (a/\~b)”),PROP_TAC)]
  THEN EQ_TAC THEN REPEAT STRIP_TAC
  THENL[
      EXISTS_TAC“t1:num” THEN ASM_REWRITE_TAC[],
      EXISTS_TAC“t1:num” THEN ASM_REWRITE_TAC[]]
  );





val BEFORE_LINORD = TAC_PROOF(
  ([],“(a BEFORE b) t0 = !t1. (t0<=t1) /\ UPTO(t0,t1,(\t.~a t)) ==> ~b t1”),
  ONCE_REWRITE_TAC[TAC_PROOF(([],“(a=b) = (~a= ~b)”),PROP_TAC)]
  THEN REWRITE_TAC[NOT_BEFORE,SUNTIL_LINORD]
  THEN BETA_TAC THEN CONV_TAC(DEPTH_CONV NOT_FORALL_CONV)
  THEN REWRITE_TAC[TAC_PROOF(([],“~(a==>b) = (a/\~b)”),PROP_TAC)]
  THEN EQ_TAC THEN REPEAT STRIP_TAC
  THENL[
      EXISTS_TAC“t1:num” THEN ASM_REWRITE_TAC[],
      EXISTS_TAC“t1:num” THEN ASM_REWRITE_TAC[]]
  );



val ALWAYS_LINORD = TAC_PROOF(
        ([],“(ALWAYS a) t0 = !t1. (t0<=t1) ==> a t1”),
        REWRITE_TAC[ALWAYS_AS_UNTIL,UNTIL_LINORD,UPTO]
        );



val EVENTUAL_LINORD = TAC_PROOF(
        ([],“(EVENTUAL a) t0 = ?t1. (t0<=t1) /\ a t1”),
        REWRITE_TAC[EVENTUAL_AS_SUNTIL,SUNTIL_LINORD,UPTO]
        );


val NEXT_LINORD = TAC_PROOF(
        ([],“(NEXT a) t0 = ?t1. t0<t1 /\ (!t3. t0<t3 ==> t1<=t3) /\ a t1”),
        REWRITE_TAC[NEXT] THEN BETA_TAC
        THEN EQ_TAC THEN REPEAT STRIP_TAC
        THENL[
            EXISTS_TAC“SUC t0” THEN ASM_REWRITE_TAC[]
            THEN CONV_TAC ARITH_CONV,
            MY_MP_TAC “t1 = SUC t0”
            THENL[
                DISJ_CASES_TAC(EQT_ELIM(ARITH_CONV
                        “(t1<SUC t0) \/ (t1=SUC t0) \/ (SUC t0<t1)”))
                THENL[ALL_TAC,POP_ASSUM DISJ_CASES_TAC]
                THENL[
                    UNDISCH_NO_TAC 3 THEN UNDISCH_NO_TAC 0
                    THEN CONV_TAC ARITH_CONV,
                    POP_ASSUM REWRITE1_TAC,
                    LEFT_NO_FORALL_TAC 2 “SUC t0” THEN UNDISCH_HD_TAC
                    THEN REWRITE_TAC[EQT_ELIM(ARITH_CONV“t0<SUC t0”)]
                    THEN UNDISCH_HD_TAC THEN UNDISCH_NO_TAC 1
                    THEN CONV_TAC ARITH_CONV],
                DISCH_TAC]
            THEN POP_ASSUM (SUBST1_TAC o SYM)
            THEN ASM_REWRITE_TAC[]
            ]);


(* ************************************************************ *)
(*              Saving the most interesting theorems            *)
(* ************************************************************ *)

(* ----------------- from file lemmata.sml ------------------   *)
val _ = save_thm("WATCH_EXISTS",WATCH_EXISTS);
val _ = save_thm("WELL_ORDER",WELL_ORDER);
val _ = save_thm("WELL_ORDER_UNIQUE",WELL_ORDER_UNIQUE);

(* ----------------- from file hw_imp.sml ------------------    *)
val _ = save_thm("WHEN_IMP",WHEN_IMP);
val _ = save_thm("UNTIL_IMP",UNTIL_IMP);
val _ = save_thm("BEFORE_IMP",BEFORE_IMP);
val _ = save_thm("SWHEN_IMP",SWHEN_IMP);
val _ = save_thm("SUNTIL_IMP",SUNTIL_IMP);
val _ = save_thm("SBEFORE_IMP",SBEFORE_IMP);

(* ----------------- from file signal.sml ------------------    *)
val _ = save_thm("ALWAYS_SIGNAL",ALWAYS_SIGNAL);
val _ = save_thm("EVENTUAL_SIGNAL",EVENTUAL_SIGNAL);
val _ = save_thm("WHEN_SIGNAL",WHEN_SIGNAL);
val _ = save_thm("UNTIL_SIGNAL",UNTIL_SIGNAL);
val _ = save_thm("BEFORE_SIGNAL",BEFORE_SIGNAL);
val _ = save_thm("SWHEN_SIGNAL",SWHEN_SIGNAL);
val _ = save_thm("SBEFORE_SIGNAL",SBEFORE_SIGNAL);

(* ----------------- from file temp2linord.sml ---------------- *)
val _ = save_thm("NEXT_LINORD",NEXT_LINORD);
val _ = save_thm("ALWAYS_LINORD",ALWAYS_LINORD);
val _ = save_thm("EVENTUAL_LINORD",EVENTUAL_LINORD);
val _ = save_thm("SUNTIL_LINORD",SUNTIL_LINORD);
val _ = save_thm("UNTIL_LINORD",UNTIL_LINORD);
val _ = save_thm("SBEFORE_LINORD",SBEFORE_LINORD);
val _ = save_thm("BEFORE_LINORD",BEFORE_LINORD);
val _ = save_thm("SWHEN_LINORD",SWHEN_LINORD);
val _ = save_thm("WHEN_LINORD",WHEN_LINORD);

(* ----------------- from file when_expressive.sml ------------------ *)
val _ = save_thm("ALWAYS_AS_WHEN",ALWAYS_AS_WHEN);
val _ = save_thm("EVENTUAL_AS_WHEN",EVENTUAL_AS_WHEN);
val _ = save_thm("UNTIL_AS_WHEN",UNTIL_AS_WHEN);
val _ = save_thm("SWHEN_AS_WHEN",SWHEN_AS_WHEN);
val _ = save_thm("SWHEN_AS_NOT_WHEN",SWHEN_AS_NOT_WHEN);
val _ = save_thm("SUNTIL_AS_WHEN",SUNTIL_AS_WHEN);
val _ = save_thm("SBEFORE_AS_WHEN",SBEFORE_AS_WHEN);
val _ = save_thm("BEFORE_AS_WHEN_UNTIL",BEFORE_AS_WHEN_UNTIL);
val _ = save_thm("BEFORE_HW",BEFORE_HW);

(* ----------------- from file until_expressive.sml ------------------ *)
val _ = save_thm("ALWAYS_AS_UNTIL",ALWAYS_AS_UNTIL);
val _ = save_thm("EVENTUAL_AS_UNTIL",EVENTUAL_AS_UNTIL);
val _ = save_thm("WHEN_AS_UNTIL",WHEN_AS_UNTIL);
val _ = save_thm("BEFORE_AS_UNTIL",BEFORE_AS_UNTIL);
val _ = save_thm("SWHEN_AS_UNTIL",SWHEN_AS_UNTIL);
val _ = save_thm("SUNTIL_AS_UNTIL",SUNTIL_AS_UNTIL);
val _ = save_thm("SBEFORE_AS_UNTIL",SBEFORE_AS_UNTIL);

(* ----------------- from file before_expressive.sml ------------------ *)
val _ = save_thm("ALWAYS_AS_BEFORE",ALWAYS_AS_BEFORE);
val _ = save_thm("EVENTUAL_AS_BEFORE",EVENTUAL_AS_BEFORE);
val _ = save_thm("WHEN_AS_BEFORE",WHEN_AS_BEFORE);
val _ = save_thm("UNTIL_AS_BEFORE",UNTIL_AS_BEFORE);
val _ = save_thm("SWHEN_AS_BEFORE",SWHEN_AS_BEFORE);
val _ = save_thm("SUNTIL_AS_BEFORE",SUNTIL_AS_BEFORE);
val _ = save_thm("SBEFORE_AS_BEFORE",SBEFORE_AS_BEFORE);

(* ----------------- from file swhen_expressive.sml ------------------ *)
val _ = save_thm("WHEN_SWHEN_LEMMA",WHEN_SWHEN_LEMMA);

val _ = save_thm("ALWAYS_AS_SWHEN",ALWAYS_AS_SWHEN);
val _ = save_thm("EVENTUAL_AS_SWHEN",EVENTUAL_AS_SWHEN);
val _ = save_thm("WHEN_AS_SWHEN",WHEN_AS_SWHEN);
val _ = save_thm("WHEN_AS_NOT_SWHEN",WHEN_AS_NOT_SWHEN);
val _ = save_thm("UNTIL_AS_SWHEN",UNTIL_AS_SWHEN);
val _ = save_thm("BEFORE_AS_SWHEN",BEFORE_AS_SWHEN);
val _ = save_thm("BEFORE_AS_NOT_SWHEN",BEFORE_AS_NOT_SWHEN);
val _ = save_thm("SUNTIL_AS_SWHEN",SUNTIL_AS_SWHEN);
val _ = save_thm("SBEFORE_AS_SWHEN",SBEFORE_AS_SWHEN);

(* ----------------- from file suntil_expressive.sml ------------------ *)
val _ = save_thm("ALWAYS_AS_SUNTIL",ALWAYS_AS_SUNTIL);
val _ = save_thm("EVENTUAL_AS_SUNTIL",EVENTUAL_AS_SUNTIL);
val _ = save_thm("WHEN_AS_SUNTIL",WHEN_AS_SUNTIL);
val _ = save_thm("UNTIL_AS_SUNTIL",UNTIL_AS_SUNTIL);
val _ = save_thm("BEFORE_AS_SUNTIL",BEFORE_AS_SUNTIL);
val _ = save_thm("SWHEN_AS_SUNTIL",SWHEN_AS_SUNTIL);
val _ = save_thm("SBEFORE_AS_SUNTIL",SBEFORE_AS_SUNTIL);

(* ----------------- from file sbefore_expressive.sml ------------------ *)
val _ = save_thm("ALWAYS_AS_SBEFORE",ALWAYS_AS_SBEFORE);
val _ = save_thm("EVENTUAL_AS_SBEFORE",EVENTUAL_AS_SBEFORE);
val _ = save_thm("WHEN_AS_SBEFORE",WHEN_AS_SBEFORE);
val _ = save_thm("UNTIL_AS_SBEFORE",UNTIL_AS_SBEFORE);
val _ = save_thm("SWHEN_AS_SBEFORE",SWHEN_AS_SBEFORE);
val _ = save_thm("SUNTIL_AS_SBEFORE",SUNTIL_AS_SBEFORE);
val _ = save_thm("BEFORE_AS_SBEFORE",BEFORE_AS_SBEFORE);

(* ----------------- from file simplify.sml ------------------ *)
val _ = save_thm("WHEN_SIMP",WHEN_SIMP);
val _ = save_thm("UNTIL_SIMP",UNTIL_SIMP);
val _ = save_thm("BEFORE_SIMP",BEFORE_SIMP);
val _ = save_thm("SWHEN_SIMP",SWHEN_SIMP);
val _ = save_thm("SUNTIL_SIMP",SUNTIL_SIMP);
val _ = save_thm("SBEFORE_SIMP",SBEFORE_SIMP);
val _ = save_thm("WHEN_EVENT",WHEN_EVENT);
val _ = save_thm("UNTIL_EVENT",UNTIL_EVENT);
val _ = save_thm("BEFORE_EVENT",BEFORE_EVENT);
val _ = save_thm("SWHEN_EVENT",SWHEN_EVENT);
val _ = save_thm("SUNTIL_EVENT",SUNTIL_EVENT);
val _ = save_thm("SBEFORE_EVENT",SBEFORE_EVENT);
val _ = save_thm("IMMEDIATE_EVENT",IMMEDIATE_EVENT);
val _ = save_thm("NO_EVENT",NO_EVENT);
val _ = save_thm("SOME_EVENT",SOME_EVENT);
val _ = save_thm("MORE_EVENT",MORE_EVENT);

(* ----------------- from file next_homo.sml ------------------ *)
val _ = save_thm("NOT_NEXT",NOT_NEXT);
val _ = save_thm("AND_NEXT",AND_NEXT);
val _ = save_thm("OR_NEXT",OR_NEXT);
val _ = save_thm("IMP_NEXT",IMP_NEXT);
val _ = save_thm("EQUIV_NEXT",EQUIV_NEXT);
val _ = save_thm("ALWAYS_NEXT",ALWAYS_NEXT);
val _ = save_thm("EVENTUAL_NEXT",EVENTUAL_NEXT);
val _ = save_thm("WHEN_NEXT",WHEN_NEXT);
val _ = save_thm("UNTIL_NEXT",UNTIL_NEXT);
val _ = save_thm("BEFORE_NEXT",BEFORE_NEXT);
val _ = save_thm("SWHEN_NEXT",SWHEN_NEXT);
val _ = save_thm("SUNTIL_NEXT",SUNTIL_NEXT);
val _ = save_thm("SBEFORE_NEXT",SBEFORE_NEXT);

(* ----------------- from file recursion.sml ------------------ *)
val _ = save_thm("ALWAYS_REC",ALWAYS_REC);
val _ = save_thm("EVENTUAL_REC",EVENTUAL_REC);
val _ = save_thm("WATCH_REC",WATCH_REC);
val _ = save_thm("WHEN_REC",WHEN_REC);
val _ = save_thm("UNTIL_REC",UNTIL_REC);
val _ = save_thm("BEFORE_REC",BEFORE_REC);
val _ = save_thm("SWHEN_REC",SWHEN_REC);
val _ = save_thm("SUNTIL_REC",SUNTIL_REC);
val _ = save_thm("SBEFORE_REC",SBEFORE_REC);

(* ----------------- from file fixpoints.sml ------------------ *)
val _ = save_thm("ALWAYS_FIX",ALWAYS_FIX);
val _ = save_thm("EVENTUAL_FIX",EVENTUAL_FIX);
val _ = save_thm("WHEN_FIX",WHEN_FIX);
val _ = save_thm("UNTIL_FIX",UNTIL_FIX);
val _ = save_thm("BEFORE_FIX",BEFORE_FIX);

(* ----------------- from file invariant.sml ------------------ *)
val _ = save_thm("WHEN_INVARIANT",WHEN_INVARIANT);
val _ = save_thm("UNTIL_INVARIANT",UNTIL_INVARIANT);
val _ = save_thm("BEFORE_INVARIANT",BEFORE_INVARIANT);
val _ = save_thm("ALWAYS_INVARIANT",ALWAYS_INVARIANT);
val _ = save_thm("EVENTUAL_INVARIANT",EVENTUAL_INVARIANT);
val _ = save_thm("SWHEN_INVARIANT",SWHEN_INVARIANT);
val _ = save_thm("SUNTIL_INVARIANT",SUNTIL_INVARIANT);
val _ = save_thm("SBEFORE_INVARIANT",SBEFORE_INVARIANT);

(* ----------------- from file idem.sml ------------------ *)
val _ = save_thm("ALWAYS_IDEM",ALWAYS_IDEM);
val _ = save_thm("EVENTUAL_IDEM",EVENTUAL_IDEM);
val _ = save_thm("WHEN_IDEM",WHEN_IDEM);
val _ = save_thm("UNTIL_IDEM",UNTIL_IDEM);
val _ = save_thm("BEFORE_IDEM",BEFORE_IDEM);
val _ = save_thm("SWHEN_IDEM",SWHEN_IDEM);
val _ = save_thm("SUNTIL_IDEM",SUNTIL_IDEM);
val _ = save_thm("SBEFORE_IDEM",SBEFORE_IDEM);

(* ----------------- from file negation.sml ------------------ *)
val _ = save_thm("NOT_ALWAYS",NOT_ALWAYS);
val _ = save_thm("NOT_EVENTUAL",NOT_EVENTUAL);
val _ = save_thm("NOT_WHEN",NOT_WHEN);
val _ = save_thm("NOT_UNTIL",NOT_UNTIL);
val _ = save_thm("NOT_BEFORE",NOT_BEFORE);
val _ = save_thm("NOT_SWHEN",NOT_SWHEN);
val _ = save_thm("NOT_SUNTIL",NOT_SUNTIL);
val _ = save_thm("NOT_SBEFORE",NOT_SBEFORE);


val _ = export_theory();

(* html_theory "-"; *)
