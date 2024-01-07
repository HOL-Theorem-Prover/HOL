(*---------------------------------------------------------------------------*
 *     The multiplier example from the LCF_LSM paper.                        *
 *---------------------------------------------------------------------------*)

open HolKernel Parse boolLib
open Prim_rec numLib unwindLib bossLib Rsyntax

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;


(*---------------------------------------------------------------------------*
 * Do some profiling.                                                        *
 *---------------------------------------------------------------------------*)

val meter = Count.mk_meter();
val timer = Lib.start_time();

(*---------------------------------------------------------------------------
 * Theorem for projection of a sequence of microcycles into a single
 *  macrocycle.
 *---------------------------------------------------------------------------*)

val _ = new_theory "Bmark";

val INDUCTION        = numTheory.INDUCTION;
val INDUCT_TAC       = INDUCT_THEN INDUCTION ASSUME_TAC;

val SUC_LESS         = prim_recTheory.SUC_LESS;
val LESS_REFL        = prim_recTheory.LESS_REFL;
val LESS_SUC_REFL    = prim_recTheory.LESS_SUC_REFL;

val LESS_LESS_SUC    = arithmeticTheory.LESS_LESS_SUC;
val LESS_SUC_EQ_COR  = arithmeticTheory.LESS_SUC_EQ_COR;
val LESS_TRANS       = arithmeticTheory.LESS_TRANS;
val LESS_OR_EQ       = arithmeticTheory.LESS_OR_EQ;
val LESS_ADD_NONZERO = arithmeticTheory.LESS_ADD_NONZERO;
val LESS_EQ_SUC_REFL = arithmeticTheory.LESS_EQ_SUC_REFL;
val LESS_CASES_IMP   = arithmeticTheory.LESS_CASES_IMP;
val ADD_INV_0        = arithmeticTheory.ADD_INV_0;
val ADD1             = arithmeticTheory.ADD1;
val ADD_CLAUSES      = arithmeticTheory.ADD_CLAUSES;

val FUN_EQ_LEMMA = store_thm ("FUN_EQ_LEMMA",
   “!f:'a->bool. !x1 x2. f x1 /\ ~f x2 ==> ~(x1 = x2)”,
   REPEAT STRIP_TAC
    THEN IMP_RES_TAC
          (DISCH_ALL(SUBS[ASSUME “(x1:'a)=x2”]
                         (ASSUME“(f:'a->bool)x1”)))
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);

val NEXT =
 new_definition
  ("NEXT",
   “!done x1 x2.
      NEXT (x1,x2) done =
       (x1 < x2 /\ done x2 /\ !x. x1 < x /\ x < x2 ==> ~done x)”);

val STABLE =
 new_definition
  ("STABLE",
   “!(i:num->'a). !x1 x2.
      STABLE (x1,x2) i = !x. ((x1 <= x) /\ (x < x2)) ==> (i x = i x1)”);

val NEXT_SUC1 =
 store_thm
  ("NEXT_SUC1",
   “!done x. done(SUC x) ==> NEXT (x,SUC x) done”,
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[NEXT]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[LESS_SUC_REFL]
    THEN IMP_RES_TAC LESS_LESS_SUC
    THEN ASM_REWRITE_TAC[]);

(* LESS_SUC_EQ_LEMMA = |- ~(n = SUC m) ==> m < n ==> (SUC m) < n *)
val LESS_SUC_EQ_LEMMA =
 (DISCH_ALL
  (MP (SPEC_ALL LESS_SUC_EQ_COR)
      (CONJ (ASSUME (“m < n”))
            (NOT_EQ_SYM(ASSUME (“~(n = SUC m)”))))));

local val FUN_EQ_LEMMA' = INST_TYPE[alpha |-> Type`:num`] FUN_EQ_LEMMA
in
val NEXT_SUC2 =
 store_thm
  ("NEXT_SUC2",
   “!done x1 x2.
      (NEXT (x1,x2) done /\ ~(done(SUC x1))) ==> NEXT (SUC x1,x2) done”,
   REPEAT GEN_TAC
    THEN REWRITE_TAC[NEXT]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC SUC_LESS
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC
         (SPECL[“done:num->bool”,
                “x2:num”,
                “SUC x1”] FUN_EQ_LEMMA')
    THEN IMP_RES_TAC LESS_SUC_EQ_LEMMA
    THEN ASM_REWRITE_TAC[])
end;

val STABLE_SUC =
 store_thm
  ("STABLE_SUC",
   “!x1 x2 (i:num->'a). (STABLE (x1,x2) i) ==> (STABLE ((SUC x1),x2) i)”,
   REPEAT GEN_TAC
    THEN REWRITE_TAC[STABLE,LESS_OR_EQ]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC SUC_LESS
    THEN IMP_RES_TAC LESS_TRANS
    THEN ASSUME_TAC(SPEC (“x1:num”) LESS_SUC_REFL)
    THEN RES_TAC
    THEN ASM_REWRITE_TAC[]);

val SUC_LEMMA =
 let val [th1,th2,th3,th4] = CONJUNCTS ADD_CLAUSES
 in save_thm("SUC_LEMMA",LIST_CONJ[th1,th2,SYM th3,th4])
 end;

val stb_SUC =
 SPEC (“SUC x”)
  (ASSUME (“!x'. ((x <= x') /\ (x' < ((SUC x) + d))) ==>
                   ((i:num->'a) x' = (i x))”));

val STABLE_LEMMA = store_thm("STABLE_LEMMA",
   “!x d (i:num->'a).
     ((STABLE (x,((SUC x)+d)) i) /\ ~(d = 0)) ==> (i x = i(SUC x))”,
   REWRITE_TAC[STABLE]
    THEN REPEAT STRIP_TAC
    THEN ASSUME_TAC stb_SUC
    THEN IMP_RES_TAC(SPECL[“SUC x”, “d:num”] LESS_ADD_NONZERO)
    THEN CONV_TAC SYM_CONV
    THEN FIRST_ASSUM MATCH_MP_TAC
    THEN ASSUME_TAC(SPEC (“x:num”) LESS_EQ_SUC_REFL)
    THEN ASM_REWRITE_TAC[]);

val NEXT_LEMMA1 =
 store_thm
  ("NEXT_LEMMA1",
   “!done x1 x2.
      (NEXT (x1,x2) done /\ NEXT (x1,x3) done) ==> (x2 = x3)”,
   REPEAT GEN_TAC
    THEN REWRITE_TAC[NEXT]
    THEN STRIP_TAC
    THEN ASM_CASES_TAC (“(x2:num) = x3”)
    THEN ASM_CASES_TAC (“x2 < x3”)
    THEN ASM_REWRITE_TAC[]
    THEN IMP_RES_TAC LESS_CASES_IMP
    THEN RES_TAC);

val next_SUC =
 DISCH_ALL
  (REWRITE_RULE
   [ADD_CLAUSES]
   (SUBS [ASSUME (“d = 0”)]
         (ASSUME (“(done:num->bool) (SUC x + d)”))));

val NEXT_LEMMA2 =
 store_thm
  ("NEXT_LEMMA2",
   “!x d done.
      (NEXT (x,(SUC x)+d) done /\ ~(done(SUC x))) ==> ~(d = 0)”,
   REWRITE_TAC[NEXT]
    THEN REPEAT STRIP_TAC
    THEN IMP_RES_TAC next_SUC
    THEN RES_TAC);

val assm =
 ASSUME (“(!x. (done x = f(s x)) /\ (s(SUC x) = g(i x,s x))) /\
            (!a b. (FN:('a#'b)->'b)(a,b) = (if f b then b else FN(a,g(a,b))))”) ;

val [done_s,FN] = CONJUNCTS assm;

val ind_hyp =
 ASSUME (“!x. (NEXT(x,x + d)done /\ STABLE(x,x + d)i) ==>
                (s(x + d) = (FN:('a#'b)->'b)(i x,g(i x,s x)))”);

val s_tm =
 ASSUME (“s(SUC x + d) = (FN:('a#'b)->'b)(i(SUC x),g(i(SUC x),s(SUC x)))”);

val NEXT_THM =
 store_thm
  ("NEXT_THM",
   “!(FN : 'a#'b -> 'b).
      !(f:'b->bool).
      !(g: 'a#'b -> 'b).
      !(done : num->bool).
      !(i:num->'a).
      !(s:num->'b).
      ((!x. (done x = f(s x)) /\ (s(x+1) = g(i x,s x))) /\
      (!a b. FN(a,b) = (if f b then b else FN(a,g(a,b)))))    ==>
      (!d x.
        (NEXT(x,x+d)done /\ STABLE(x,x+d)i) ==>
        (s(x+d) = FN(i x,g(i x,s x))))”,
   REPEAT GEN_TAC
    THEN REWRITE_TAC[SYM(SPEC_ALL ADD1)]
    THEN REPEAT DISCH_TAC
    THEN INDUCT_TAC
    THENL [REWRITE_TAC[NEXT,LESS_REFL,ADD_CLAUSES],ALL_TAC]
    THEN REWRITE_TAC[SUC_LEMMA]
    THEN REPEAT STRIP_TAC
    THEN ASM_CASES_TAC (“(done(SUC x)):bool”)
    THENL
     [IMP_RES_TAC NEXT_SUC1
       THEN IMP_RES_TAC NEXT_LEMMA1
       THEN IMP_RES_TAC ADD_INV_0
       THEN REWRITE_TAC[ASSUME (“d=0”),ADD_CLAUSES]
       THEN REWRITE_TAC
             ([SPECL[“(i:num->'a)x”,
                     “(g:('a#'b)->'b)(i(x:num),s x)”] FN,
               ASSUME (“(done(SUC x)):bool”)] @
              (map SYM (CONJUNCTS(SPEC_ALL done_s)))),
      ALL_TAC]
    THEN ASSUME_TAC(SPEC (“SUC x”) ind_hyp)
    THEN IMP_RES_TAC STABLE_SUC
    THEN IMP_RES_TAC NEXT_SUC2
    THEN RES_TAC
    THEN REWRITE_TAC[s_tm]
    THEN SUBST_TAC[SPECL[“(i:num->'a)x”,
                         “(g:('a#'b)->'b)(i(x:num),s x)”]FN]
    THEN REWRITE_TAC
          (ASSUME (“~done(SUC x)”)::(map SYM (CONJUNCTS(SPEC_ALL done_s))))
    THEN IMP_RES_TAC NEXT_LEMMA2
    THEN IMP_RES_TAC STABLE_LEMMA
    THEN REWRITE_TAC[ASSUME (“(i:num->'a) x = i(SUC x)”),done_s]);

(****************************************************************************)
(****************************************************************************)
(****************************************************************************)


val num_Axiom = prim_recTheory.num_Axiom;
val num_CASES = arithmeticTheory.num_CASES;
val SUC_SUB1  = arithmeticTheory.SUC_SUB1;
val SUB       = arithmeticTheory.SUB;

val MULT_FUN_CURRY = new_recursive_definition
   {name = "MULT_FUN_CURRY", rec_axiom = num_Axiom,
    def = “(MULT_FUN_CURRY 0 i1 i2 m t =
                  (if t then (m,0,t) else (if i1=0 then m else i2+m,0,T)))
             /\
             (MULT_FUN_CURRY (SUC n) i1 i2 m t =
                  (if t then (m,SUC n,t)
                   else MULT_FUN_CURRY n i1 i2 (if i1=0 then m else i2+m)
                                       (((n-1)=0) \/ (i2=0))))”};

(*---------------------------------------------------------------------------
 * Rewriting ambiguity between SUC_SUB1 and SUB means that hol88
 * does the following proof properly, but hol90 won't. Both will do
 * the "non-commented-out version"
 *
 * val MULT_FUN_CURRY_THM =
 *  store_thm
 *   ("MULT_FUN_CURRY_THM",
 *    “!i1 i2 m n t.
 *      MULT_FUN_CURRY n i1 i2 m t =
 *       (if t then (m,n,t)
 *        else MULT_FUN_CURRY (n-1) i1 i2 (if i1=0 then m else i2+m)
 *                            ((((n-1)-1)=0) \/ (i2=0)))”,
 *    REPEAT GEN_TAC
 *     THEN STRUCT_CASES_TAC(SPEC (“n:num”) num_CASES)
 *    THEN ASM_CASES_TAC (“t:bool”)
 *     THEN ASM_REWRITE_TAC[MULT_FUN_CURRY,SUC_SUB1,SUB]);
 *---------------------------------------------------------------------------*)

val MULT_FUN_CURRY_THM = store_thm("MULT_FUN_CURRY_THM",
   “!i1 i2 m n t.
      MULT_FUN_CURRY n i1 i2 m t =
       (if t then (m,n,t)
        else MULT_FUN_CURRY(n-1) i1 i2 (if i1=0 then m else i2+m) (((n-1)-1=0)\/(i2=0)))”,
   REPEAT GEN_TAC
    THEN STRUCT_CASES_TAC(SPEC (“n:num”) num_CASES)
    THEN ASM_CASES_TAC (“t:bool”)
    THEN REWRITE_TAC[SUC_SUB1]
    THEN ASM_REWRITE_TAC[MULT_FUN_CURRY,SUB]);


val MULT_FUN = new_definition("MULT_FUN",
   “MULT_FUN((i1,i2),m,n,t) = MULT_FUN_CURRY n i1 i2 m t”);

val MULT_FUN_DEF = store_thm("MULT_FUN_DEF",
   “!i1 i2 m n t.
     MULT_FUN((i1,i2),m,n,t) =
      (if t then (m,n,t)
       else MULT_FUN ((i1,i2), (if i1=0 then m else i2+m), (n-1),
                     ((((n-1)-1)=0) \/ (i2=0))))”,
   REPEAT GEN_TAC
    THEN REWRITE_TAC[MULT_FUN]
    THEN ACCEPT_TAC(SPEC_ALL MULT_FUN_CURRY_THM));

(****************************************************************************)
(****************************************************************************)
(****************************************************************************)


val LESS_0            = prim_recTheory.LESS_0;

val LESS_OR_EQ        = arithmeticTheory.LESS_OR_EQ;
val LESS_MONO_EQ      = arithmeticTheory.LESS_MONO_EQ;
val ADD_EQ_SUB        = arithmeticTheory.ADD_EQ_SUB;
val ADD_CLAUSES       = arithmeticTheory.ADD_CLAUSES;
val SUB_0             = arithmeticTheory.SUB_0;
val MULT_CLAUSES      = arithmeticTheory.MULT_CLAUSES;
val ADD_SYM           = arithmeticTheory.ADD_SYM;
val ADD_ASSOC         = arithmeticTheory.ADD_ASSOC;
val LESS_EQ_ADD       = arithmeticTheory.LESS_EQ_ADD;
val RIGHT_SUB_DISTRIB = arithmeticTheory.RIGHT_SUB_DISTRIB;
val SUB_ADD           = arithmeticTheory.SUB_ADD;
val SUC_SUB1          = arithmeticTheory.SUC_SUB1;

(* val MULT_FUN_DEF = MULT_FUN_CURRYTheory.MULT_FUN_DEF; *)

val MULT_FUN_T =
 store_thm
  ("MULT_FUN_T",
   “!i1 i2 m n.
     MULT_FUN((i1,i2),m,n,T) = (m,n,T)”,
   REPEAT GEN_TAC
    THEN ASM_CASES_TAC (“t:bool”)
    THEN REWRITE_TAC[INST [“t:bool” |-> “T”] (SPEC_ALL MULT_FUN_DEF)]);

val MULT_FUN_F =
 store_thm
  ("MULT_FUN_F",
   “!i1 i2 m n.
     MULT_FUN((i1,i2),m,n,F) =
     MULT_FUN((i1,i2),(if i1=0 then m else i2+m),(n-1),((((n-1)-1)=0) \/ (i2=0)))”,
   REPEAT GEN_TAC
    THEN ASM_CASES_TAC (“t:bool”)
    THEN REWRITE_TAC[INST[“t:bool” |-> “F”] (SPEC_ALL MULT_FUN_DEF)]);

val LESS_EQ_0 =
 store_thm
  ("LESS_EQ_0",
   “!m. 0 <= m”,
   INDUCT_TAC
   THEN ASM_REWRITE_TAC[LESS_OR_EQ,LESS_0]);

val LESS_EQ_SUC_1 =
 store_thm
  ("LESS_EQ_SUC_1",
   “!m. 1 <= SUC m”,
   INDUCT_TAC
   THEN ASM_REWRITE_TAC[num_CONV (“1”),LESS_OR_EQ,LESS_MONO_EQ,LESS_0]);

val EQ_SYM_EQ' = INST_TYPE[alpha |-> Type`:num`] EQ_SYM_EQ;

val SUB_LEMMA1 =
 store_thm
  ("SUB_LEMMA1",
   “!m.(~(m=0)) ==> (((m-1)=0) ==> (m=1))”,
   INDUCT_TAC
    THEN REWRITE_TAC
          [SYM
           (SUBS
             [SPECL[“0”, “(SUC m)-1”]EQ_SYM_EQ']
             (MP
              (SPECL
                [“0”, “1”, “SUC m”]ADD_EQ_SUB)
              (SPEC (“m:num”) LESS_EQ_SUC_1))),
           ADD_CLAUSES]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]);

val SUB_LEMMA2 =
 store_thm
  ("SUB_LEMMA2",
   “!m.(m=0) ==> ((~((m-1)=0)) ==> F)”,
    GEN_TAC
     THEN DISCH_TAC
     THEN ASM_REWRITE_TAC[SUB_0]);

val MULT_NOT_0_LESS =
 store_thm
  ("MULT_NOT_0_LESS",
   “!m n. (~(m = 0)) ==> (n <= (m * n))”,
   INDUCT_TAC
   THEN GEN_TAC
   THEN REWRITE_TAC[MULT_CLAUSES,SUBS[SPEC_ALL ADD_SYM]
                                     (SPEC_ALL LESS_EQ_ADD)]);

val MULT_ADD_LEMMA1 =
 store_thm
  ("MULT_ADD_LEMMA1",
   “!m. (~(m=0)) ==> (!n p. (((m-1)*n)+(n+p)) = ((m*n)+p))”,
   REPEAT STRIP_TAC
   THEN REWRITE_TAC[ADD_ASSOC,RIGHT_SUB_DISTRIB,MULT_CLAUSES]
   THEN IMP_RES_THEN (ASSUME_TAC o SPEC (“n:num”)) MULT_NOT_0_LESS
   THEN IMP_RES_TAC SUB_ADD
   THEN ASM_REWRITE_TAC[]);

val MULT_FUN_THM =
 store_thm
  ("MULT_FUN_THM",
   “!n i1 i2 m t.
     MULT_FUN((i1,i2),m,n,t) =
       if t then
       (m,n,t)
       else
       (if ((n-1)=0)\/(i2=0) then
        ((if i1=0 then m else i2+m),(n-1),T)
        else
        ((if i1=0 then m else ((n-1)*i2)+m),1,T))”,
       INDUCT_TAC
       THEN REPEAT GEN_TAC
       THEN ASM_CASES_TAC (“t:bool”)
       THEN ASM_REWRITE_TAC[MULT_FUN_T,MULT_FUN_F,SUC_SUB1,SUB_0]
       THEN ASM_CASES_TAC (“i1=0”)
       THEN ASM_CASES_TAC (“i2=0”)
       THEN ASM_CASES_TAC (“n=0”)
       THEN ASM_CASES_TAC (“(n-1)=0”)
       THEN ASM_REWRITE_TAC[MULT_FUN_T,MULT_FUN_F,SUC_SUB1,SUB_0]
       THEN IMP_RES_TAC SUB_LEMMA1
       THEN IMP_RES_TAC SUB_LEMMA2
       THEN IMP_RES_TAC MULT_ADD_LEMMA1
       THEN ASM_REWRITE_TAC[MULT_CLAUSES]);

val MULT_ADD_LEMMA2 =
 store_thm
  ("MULT_ADD_LEMMA2",
   “!m. ~(m=0) ==> !n. ((m-1)*n)+n = m*n”,
   REPEAT STRIP_TAC
    THEN REWRITE_TAC[RIGHT_SUB_DISTRIB,MULT_CLAUSES]
    THEN IMP_RES_THEN (ASSUME_TAC o SPEC (“n:num”)) MULT_NOT_0_LESS
    THEN IMP_RES_TAC SUB_ADD
    THEN ASM_REWRITE_TAC[]);

val MULT_FUN_LEMMA =
     store_thm
      ("MULT_FUN_LEMMA",
       “!i1 i2.
         (MULT_FUN((i1,i2),(if i1=0 then 0 else i2),i1,(((i1-1)=0)\/(i2=0)))) =
          ((i1*i2), (if ((i1-1)=0)\/(i2=0) then i1 else 1), T)”,
       REPEAT GEN_TAC
        THEN ASM_CASES_TAC (“i1=0”)
        THEN ASM_CASES_TAC (“i2=0”)
        THEN ASM_REWRITE_TAC[MULT_FUN_THM,MULT_CLAUSES,SUB_0]
        THEN ASM_CASES_TAC (“(i1-1)=0”)
        THEN IMP_RES_TAC SUB_LEMMA1
        THEN IMP_RES_TAC MULT_ADD_LEMMA2
        THEN ASM_REWRITE_TAC[MULT_CLAUSES]);

(****************************************************************************)
(****************************************************************************)
(****************************************************************************)

(*---------------------------------------------------------------------------
 * Define the basic components of the circuit.
 *---------------------------------------------------------------------------*)

val [MUX,REG,FLIPFLOP,DEC,ADDER,ZERO_TEST,OR_GATE,IS_ZERO] =
 map new_definition
 [("MUX"      , “MUX(switch,(i1:num->num),(i2:num->num),out) =
                      !(x:num). out x = (if switch x then i1 x else i2 x)”),

  ("REG"      , “REG((i:num->num),out) = !x. out(x+1) = i x”),

  ("FLIPFLOP" , “FLIPFLOP((i:num->bool),out) = !x. out(x+1) = i x”),

  ("DEC"      , “DEC(i,out) = !x:num. out x = (i x - 1)”),

  ("ADDER"    , “ADDER(i1,i2,out) = !x:num. out x = i1 x + i2 x”),

  ("ZERO_TEST", “ZERO_TEST(i,out) = !x:num. out x = (i x = 0)”),

  ("OR_GATE"  , “OR_GATE(i1,i2,out) = !x:num. out x = (i1 x \/ i2 x)”),

  ("IS_ZERO"  , “IS_ZERO(out) = !x:num. out x = 0”)];

(*---------------------------------------------------------------------------
 * Define the implementation of the circuit.
 *---------------------------------------------------------------------------*)

val MULT_IMP = new_definition
 ("MULT_IMP",
  “MULT_IMP(i1,i2,o1,o2,done) =
    ?b1 b2 b3 b4 l1 l2 l3 l4 l5 l6 l7 l8 l9.
       MUX(done,l8,l7,l6) /\
       REG(l6,o2)         /\
       ADDER(l8,o2,l7)    /\
       DEC(i1,l5)         /\
       MUX(done,l5,l3,l4) /\
       MUX(done,i1,l2,l1) /\
       REG(l1,o1)         /\
       DEC(o1,l2)         /\
       DEC(l2,l3)         /\
       IS_ZERO(l9)        /\
       MUX(b4,l9,i2,l8)   /\
       ZERO_TEST(i1,b4)   /\
       ZERO_TEST(l4,b1)   /\
       ZERO_TEST(i2,b2)   /\
       OR_GATE(b1,b2,b3)  /\
       FLIPFLOP(b3,done)”);

val ADD_CLAUSES = arithmeticTheory.ADD_CLAUSES;
val prims = [MUX,REG,FLIPFLOP,DEC,ADDER,ZERO_TEST,IS_ZERO,OR_GATE]


(* Now use the unwinding rules.  *)
val MULT_IMP_UNFOLD =
  save_thm("MULT_IMP_UNFOLD",
       unwindLib.UNFOLD_RIGHT_RULE prims MULT_IMP);

val MULT_IMP_UNWIND =
  save_thm("MULT_IMP_UNWIND",
       unwindLib.UNWIND_AUTO_RIGHT_RULE MULT_IMP_UNFOLD);

val MULT_IMP_PRUNE =
  save_thm("MULT_IMP_PRUNE",
       unwindLib.PRUNE_RIGHT_RULE MULT_IMP_UNWIND
       handle HOL_ERR _ => MULT_IMP_UNWIND);  (* pruning does nothing *)

val MULT_IMP_EXPAND =
  save_thm("MULT_IMP_EXPAND",
         unwindLib.EXPAND_AUTO_RIGHT_RULE prims MULT_IMP);

val COND_ADD_LEMMA = store_thm("COND_ADD_LEMMA",
   “((if b then m else n) + p) = (if b then m + p else n + p)”,
   COND_CASES_TAC
    THEN ASM_REWRITE_TAC[]);


val MULT_FUN_EXPANDED_DEF = store_thm("MULT_FUN_EXPANDED_DEF",
   “!i1 i2 m n t.
     MULT_FUN((i1,i2),m,n,t) =
      (if t then
       (m,n,t)
       else
       MULT_FUN
        ((i1, i2),
         (if t then (if i1 = 0 then 0 else i2) else (if i1 = 0 then 0 else i2) + m),
         (if t then i1 else n - 1),
         (((if t then i1 - 1 else (n - 1) - 1) = 0) \/ (i2 = 0))))”,
    REPEAT GEN_TAC
     THEN ASM_CASES_TAC (“t:bool”)
     THEN ASM_REWRITE_TAC[MULT_FUN_T,MULT_FUN_F,COND_ADD_LEMMA,ADD_CLAUSES]);


val G_FUN = new_definition("G_FUN",
 “!i1 i2 m n t.
    G_FUN((i1,i2),(m,n,t)) =
    ((if t then (if i1 = 0 then 0 else i2) else (if i1 = 0 then 0 else i2) + m),
     (if t then i1 else n - 1),
     (((if t then i1 - 1 else (n - 1) - 1) = 0) \/ (i2 = 0)))”);

val NEXT_THM' =
 INST_TYPE[alpha |-> Type`:num#num`, beta  |-> Type`:num#num#bool`] NEXT_THM;


val NEXT_MULT_LEMMA1 = save_thm("NEXT_MULT_LEMMA1",
   REWRITE_RULE []
        (CONV_RULE (DEPTH_CONV BETA_CONV)
                   (SPECL  [“MULT_FUN”,
                            “\(x:num#num#bool).SND(SND x)”,
                            “G_FUN”,
                            “done:num->bool”,
                            “\x. ((i1:num->num) x, (i2:num->num) x)”,
                            “\x. ((o2:num->num) x,
                                    (o1:num->num) x,
                                    (done:num->bool) x)”]
                           NEXT_THM')));

val NEXT_MULT_LEMMA2 = store_thm("NEXT_MULT_LEMMA2",
   “MULT_IMP(i1,i2,o1,o2,done)
      ==> !x.
            (o2(x + 1),o1(x + 1),done(x + 1)) =
             G_FUN((i1 x,i2 x),o2 x,o1 x,done x)”,
   REWRITE_TAC[MULT_IMP_EXPAND]
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[G_FUN]);

val PAIR = pairTheory.PAIR;

val G_FUN_LEMMA = save_thm("G_FUN_LEMMA",
   PURE_REWRITE_RULE [PAIR]
       (SPECL [“FST(a:num#num)”,
               “SND(a:num#num)”,
               “FST(b:num#num#bool)”,
               “FST(SND(b:num#num#bool))”,
               “SND(SND(b:num#num#bool))”]  G_FUN));

val NEXT_MULT_LEMMA3 = save_thm("NEXT_MULT_LEMMA3",
   PURE_REWRITE_RULE [PAIR,SYM G_FUN_LEMMA]
      (SPECL [“FST(a:num#num)”,
              “SND(a:num#num)”,
              “FST(b:num#num#bool)”,
              “FST(SND(b:num#num#bool))”,
              “SND(SND(b:num#num#bool))”] MULT_FUN_EXPANDED_DEF));

val NEXT_MULT_LEMMA4 = save_thm("NEXT_MULT_LEMMA4",
   DISCH_ALL (REWRITE_RULE [UNDISCH NEXT_MULT_LEMMA2,SYM NEXT_MULT_LEMMA3]
                           NEXT_MULT_LEMMA1));

val MULT_FUN_LEMMA1 = MULT_FUN_LEMMA;

val MULT_FUN_LEMMA2 = store_thm("MULT_FUN_LEMMA2",
 “(done:num->bool) x ==>
    (MULT_FUN((i1 x,i2 x),G_FUN((i1 x,i2 x),o2 x,o1 x,done x)) =
             ((i1 x * i2 x),
              (if ((i1 x - 1) = 0) \/ (i2 x = 0)
               then i1 x
               else 1),
              T))”,
   DISCH_TAC THEN ASM_REWRITE_TAC[MULT_FUN_LEMMA1,G_FUN]);

(* Already exists in theory "pair" *)

val PAIR_SPLIT = store_thm("PAIR_SPLIT",
   “!(x1:'a) (y1:'b) x2 y2.
     ((x1,y1) = (x2,y2)) <=> (x1 = x2) /\ (y1 = y2)”,
   REPEAT GEN_TAC
    THEN EQ_TAC
    THEN REPEAT STRIP_TAC
    THEN ASM_REWRITE_TAC[]
    THEN ASSUME_TAC (REWRITE_RULE []
       (AP_TERM (“FST:('a#'b)->'a”)
            (ASSUME (“(x1:'a,(y1:'b)) = (x2,y2)”))))
    THEN ASSUME_TAC (REWRITE_RULE []
       (AP_TERM (“SND:('a#'b)->'b”)
            (ASSUME (“(x1:'a,(y1:'b)) = (x2,y2)”))))
    THEN ASM_REWRITE_TAC[]);

val MULT_CORRECTNESS = store_thm("MULT_CORRECTNESS",
   “MULT_IMP(i1,i2,o1,o2,done)        /\
      NEXT(x,x + d) done                /\
      STABLE(x,x + d)(\x'. i1 x',i2 x') /\
      done x                           ==>
       (o2(x + d) = i1 x * i2 x)”,
   REPEAT STRIP_TAC
    THEN IMP_RES_TAC NEXT_MULT_LEMMA4
    THEN ASSUME_TAC (UNDISCH MULT_FUN_LEMMA2)
    THEN IMP_RES_TAC EQ_TRANS
    THEN IMP_RES_TAC(fst(EQ_IMP_RULE(SPEC_ALL PAIR_SPLIT))));


val _ = export_theory ();


(*---------------------------------------------------------------------------*
 * All done, print out time and inference rule breakdown.                    *
 *---------------------------------------------------------------------------*)

val _ = Lib.end_time timer;
val _ = Count.report(Count.read meter);

(* end; *)
