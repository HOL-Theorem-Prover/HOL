(*****************************************************************************)
(* Factorial over 32-bit words and how it implements mathematical factorial. *)
(* This theory doesn't deal with hardware generation at all; rather, it      *)
(* proves a data refinement result.                                          *)
(*****************************************************************************)

(******************************************************************************
 * Open theories
 ******************************************************************************)
open HolKernel Parse boolLib bossLib wordsLib
     wordsTheory arithmeticTheory pairLib pairTheory PairRules combinTheory;

(******************************************************************************
 * Set default parsing to natural numbers rather than integers
 ******************************************************************************)

val _ = numLib.temp_prefer_num();

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Start new theory "Fact32"                                                 *)
(*****************************************************************************)

val _ = new_theory "Fact32";

(*---------------------------------------------------------------------------*)
(* Iterative multiplication on nums                                          *)
(*---------------------------------------------------------------------------*)

val MultIter_def =
 Define
   `MultIter (m:num,n:num,acc:num) =
       if m = 0 then (0,n,acc) else MultIter(m-1,n,n + acc)`;

val MultIter_ind = fetch "-" "MultIter_ind";

(*****************************************************************************)
(* Verify that MultIter does compute multiplication                          *)
(*****************************************************************************)

val MultIterThm =                 (* proof adapted from similar one from KXS *)
 Q.store_thm
  ("MultIterThm",
   `!m n acc. MultIter (m,n,acc) = (0, n, (m * n) + acc)`,
   recInduct MultIter_ind THEN RW_TAC std_ss []
      THEN RW_TAC arith_ss [Once MultIter_def]
      THEN Cases_on `m`
      THEN FULL_SIMP_TAC arith_ss [MULT]);

(*****************************************************************************)
(* Create an implementation of a multiplier from MultIter                    *)
(*****************************************************************************)

val Mult_def =
 Define
  `Mult(m,n) = SND(SND(MultIter(m,n,0)))`;

(*****************************************************************************)
(* Verify Mult is actually multiplication                                    *)
(*****************************************************************************)

val MultThm =
 Q.store_thm
  ("MultThm",
   `Mult = UNCURRY $*`,
   RW_TAC arith_ss [FUN_EQ_THM,FORALL_PROD,Mult_def,MultIterThm]);


(*---------------------------------------------------------------------------*)
(* Iterative multiplication on word32s                                       *)
(*---------------------------------------------------------------------------*)

val Mult32Iter_def =
 Define
   `Mult32Iter (m:word32,n:word32,acc) =
       if m = 0w then (0w:word32,n,acc) else Mult32Iter(m-1w,n,n + acc)`;

val Mult32Iter_ind = fetch "-" "Mult32Iter_ind";

(*****************************************************************************)
(* Create an implementation of a multiplier from Mult32Iter                  *)
(*****************************************************************************)

val Mult32_def = Define `Mult32(m,n) = SND(SND(Mult32Iter(m,n,0w)))`;

(*---------------------------------------------------------------------------*)
(* Equivalence of MultIter and Mult32Iter                                    *)
(*---------------------------------------------------------------------------*)

val MultIterAbs =
 Q.store_thm
  ("MultIterAbs",
   `!m n acc.
      n < dimword(:32) /\ (m * n) + acc < dimword(:32)
      ==>
      (MultIter(m,n,acc) =
       ((w2n ## w2n ## w2n) o Mult32Iter o (n2w ## n2w ## n2w))
        (m,n,acc))`,
   recInduct MultIter_ind THEN RW_TAC std_ss []
     THEN RW_TAC arith_ss [Once MultIter_def,Once Mult32Iter_def]
     THENL
      [RW_TAC (srw_ss()) [],
       FULL_SIMP_TAC arith_ss [MULT,w2n_n2w],
       FULL_SIMP_TAC arith_ss [MULT,w2n_n2w],
       FULL_SIMP_TAC arith_ss [MULT,w2n_n2w,n2w_11,dimword_32,MultIterThm]
        THEN Cases_on `n = 0`
        THEN FULL_SIMP_TAC arith_ss []
        THEN `?p. n = p+1`
          by PROVE_TAC[intLib.COOPER_PROVE ``~(n = 0) ==> ?p. n = p+1``]
        THEN FULL_SIMP_TAC std_ss [LEFT_ADD_DISTRIB,MULT_CLAUSES]
        THEN `m < 4294967296` by DECIDE_TAC
        THEN IMP_RES_TAC LESS_MOD
        THEN DECIDE_TAC,
       FULL_SIMP_TAC arith_ss
        [MULT,w2n_n2w,n2w_11,dimword_32,MultIterThm,RIGHT_SUB_DISTRIB]
        THEN `?p. m = p+1`
          by PROVE_TAC[intLib.COOPER_PROVE ``~(n = 0) ==> ?p. n = p+1``]
        THEN FULL_SIMP_TAC std_ss [RIGHT_ADD_DISTRIB,MULT_CLAUSES]
        THEN `p * n + n - n + (acc + n) < 4294967296` by DECIDE_TAC
        THEN RW_TAC arith_ss [GSYM word_add_n2w,WORD_ADD_SUB]
        THEN PROVE_TAC [WORD_ADD_COMM]]);

val FUN_PAIR_REDUCE =
 Q.store_thm
  ("FUN_PAIR_REDUCE",
   `((n2w ## f) ((w2n ## g) p) = (FST p, f(g(SND p))))`,
   Cases_on `p` THEN RW_TAC std_ss [n2w_w2n]);

(*---------------------------------------------------------------------------*)
(* Equivalence of Mult32Iter and palin old multiplication.                   *)
(*---------------------------------------------------------------------------*)

val MultIterAbsCor =
 Q.store_thm
  ("MultIterAbsCor",
   `!m n acc.
      (m * n) + acc < dimword(:32)
      ==>
      (Mult32Iter (n2w m,n2w n,n2w acc) =
         (0w,n2w n,(n2w m) * (n2w n) + (n2w acc)))`,
   RW_TAC std_ss []
    THEN IMP_RES_TAC MultIterAbs
    THEN FULL_SIMP_TAC std_ss [MultIterThm]
    THEN Cases_on `m=0`
    THENL
     [RW_TAC arith_ss [Once Mult32Iter_def,WORD_MULT_CLAUSES,WORD_ADD_0],
      `?p. m = p+1`
         by PROVE_TAC[intLib.COOPER_PROVE ``~(n = 0) ==> ?p. n = p+1``]
       THEN FULL_SIMP_TAC std_ss [RIGHT_ADD_DISTRIB,MULT_CLAUSES]
       THEN `n < dimword(:32)` by DECIDE_TAC
       THEN RES_TAC
       THEN POP_ASSUM(ASSUME_TAC o GSYM o AP_TERM ``(n2w ## n2w ## n2w) :
               num # num # num -> bool[32] # bool[32] # bool[32]``)
       THEN FULL_SIMP_TAC std_ss [FUN_PAIR_REDUCE, n2w_w2n]
       THEN RW_TAC arith_ss [GSYM word_mul_n2w, GSYM word_add_n2w, n2w_w2n,
              WORD_RIGHT_ADD_DISTRIB,WORD_MULT_CLAUSES]]);

val MultAbs =
 Q.store_thm
  ("MultAbs",
   `!m n.
      m * n < dimword(:32)
      ==>
      (Mult(m,n) = w2n(Mult32(n2w m, n2w n)))`,
   RW_TAC arith_ss [Mult_def, Mult32_def,Once MultIterThm]
    THEN RW_TAC arith_ss
           [MultIterAbsCor,WORD_ADD_0,word_mul_n2w,n2w_w2n,w2n_n2w]);

val MultAbsCor1 =
 Q.store_thm
  ("MultAbsCor1",
   `!m n.
      m * n < dimword(:32)
      ==>
      (m * n = w2n(Mult32(n2w m, n2w n)))`,
   RW_TAC arith_ss [SIMP_RULE std_ss [MultThm] MultAbs]);

val MultAbsCor2 =
 Q.store_thm
  ("MultAbsCor2",
   `!m n.
      m * n < dimword(:32)
      ==>
      (Mult32(n2w m, n2w n) = n2w m * n2w n)`,
   PROVE_TAC[n2w_w2n,word_mul_n2w,MultAbsCor1]);

(*---------------------------------------------------------------------------*)
(* Iterative factorial on nums                                               *)
(*---------------------------------------------------------------------------*)

val FactIter_def =
 Define
   `FactIter (n,acc) =
       if n = 0 then (n,acc) else FactIter (n - 1,n * acc)`;

val FactIter_ind = fetch "-" "FactIter_ind";

(*****************************************************************************)
(* Lemma showing how FactIter computes factorial                             *)
(*****************************************************************************)

val FactIterThm =                                       (* proof from KXS *)
 Q.store_thm
  ("FactIterThm",
   `!n acc. FactIter (n,acc) = (0, acc * FACT n)`,
   recInduct FactIter_ind THEN RW_TAC arith_ss []
     THEN RW_TAC arith_ss [Once FactIter_def,FACT]
     THEN Cases_on `n`
     THEN FULL_SIMP_TAC arith_ss [FACT]);

(*****************************************************************************)
(* Iterative factorial on word32                                             *)
(*****************************************************************************)

val Fact32Iter_def =
 Define
   `Fact32Iter (n,acc) =
       if n = 0w then (n,acc) else Fact32Iter(n-1w, Mult32(n,acc))`;

val FACT_0 =
 Q.store_thm
  ("FACT_0",
   `!n. 0 < FACT n`,
   Induct
    THEN RW_TAC arith_ss [FACT,ADD1,LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]);

val FACT_LESS_EQ =
 Q.store_thm
  ("FACT_LESS_EQ",
   `!n. n <= FACT n`,
   Induct
    THEN RW_TAC arith_ss [FACT,ADD1,LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]
    THEN `0 < FACT n` by PROVE_TAC[FACT_0]
    THEN `?p. FACT n = SUC p` by Cooper.COOPER_TAC
    THEN RW_TAC arith_ss [FACT,ADD1,LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]);

val FACT_LESS =
 Q.store_thm
  ("FACT_LESS",
   `!n. (n = 0) \/ (n = 1) \/ (n = 2) \/ n < FACT n`,
   Induct
    THEN RW_TAC arith_ss [FACT,ADD1,LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]
    THEN CONV_TAC EVAL
    THEN `0 < FACT n` by PROVE_TAC[FACT_0]
    THEN `?p. FACT n = SUC p` by Cooper.COOPER_TAC
    THEN RW_TAC arith_ss [FACT,ADD1,LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]);

val MULT_LESS_LEMMA =
 Q.store_thm
  ("MULT_LESS_LEMMA",
   `!n. 0 < n ==>  m <= m * n`,
   Induct
    THEN RW_TAC arith_ss [MULT_CLAUSES]);

(*---------------------------------------------------------------------------*)
(* Equivalence of FactIter and Fact32Iter                                    *)
(*---------------------------------------------------------------------------*)

val FactIterAbs =
 Q.store_thm
  ("FactIterAbs",
   `!n acc.
      acc * FACT n < dimword(:32)
      ==>
      (FactIter(n,acc) =
       (w2n ## w2n)(Fact32Iter((n2w ## n2w)(n,acc))))`,
    recInduct FactIter_ind THEN RW_TAC std_ss []
     THEN RW_TAC arith_ss [Once FactIter_def,Once Fact32Iter_def]
     THEN FULL_SIMP_TAC arith_ss [FACT]
     THENL
      [REWRITE_TAC [word_0_n2w],
       ASM_SIMP_TAC arith_ss [w2n_n2w],
       FULL_SIMP_TAC arith_ss
        [MULT,w2n_n2w,n2w_11,dimword_32,FactIterThm]
        THEN Cases_on `acc = 0`
        THEN FULL_SIMP_TAC arith_ss []
        THEN `?p. acc = p+1`
          by PROVE_TAC[intLib.COOPER_PROVE ``~(n = 0) ==> ?p. n = p+1``]
        THEN FULL_SIMP_TAC arith_ss
             [LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB,MULT_CLAUSES]
        THEN Cases_on `n=1`
        THEN FULL_SIMP_TAC arith_ss []
        THEN ASSUME_TAC(EVAL ``2 MOD 4294967296``)
        THEN `~(n = 2)` by PROVE_TAC[EVAL ``0 = 2``]
        THEN `n < FACT n` by PROVE_TAC[FACT_LESS]
        THEN `n < 4294967296` by DECIDE_TAC
        THEN PROVE_TAC[LESS_MOD],
       `n = SUC(n-1)` by DECIDE_TAC
        THEN `FACT n = n * FACT(n-1)` by PROVE_TAC[FACT]
        THEN `acc * n * FACT (n - 1) < dimword(:32)`
          by PROVE_TAC[MULT_SYM,MULT_ASSOC]
        THEN RW_TAC arith_ss []
        THEN `1 <= n` by DECIDE_TAC
        THEN RW_TAC arith_ss [WORD_LITERAL_ADD, word_sub_def]
        THEN `n * acc < dimword(:32)`
              by PROVE_TAC
                  [FACT_0,MULT_LESS_LEMMA,MULT_SYM,
                   DECIDE``m:num <= n /\ n < p ==> m < p``]
        THEN ONCE_REWRITE_TAC [MULT_SYM]
        THEN RW_TAC arith_ss [MultAbsCor1,n2w_w2n]]);

(*****************************************************************************)
(* Lemma showing how FactIter computes factorial                             *)
(*****************************************************************************)

val FactIterThm =                                       (* proof from KXS *)
 Q.store_thm
  ("FactIterThm",
   `!n acc. FactIter (n,acc) = (0, acc * FACT n)`,
     recInduct FactIter_ind THEN RW_TAC arith_ss []
      THEN RW_TAC arith_ss [Once FactIter_def,FACT]
      THEN Cases_on `n`
      THEN FULL_SIMP_TAC arith_ss [FACT]);

val FactIterAbsCor =
 Q.store_thm
  ("FactIterAbsCor",
   `!m n acc.
      acc * FACT n < dimword(:32)
      ==>
      (Fact32Iter (n2w n, n2w acc) = (0w, n2w acc * n2w(FACT n)))`,
   RW_TAC std_ss []
    THEN IMP_RES_TAC FactIterAbs
    THEN POP_ASSUM(ASSUME_TAC o GSYM o AP_TERM ``(n2w ## n2w) :
           num # num -> bool[32] # bool[32]``)
    THEN FULL_SIMP_TAC std_ss
           [FUN_PAIR_REDUCE,n2w_w2n,FactIterThm,word_mul_n2w]);

(*****************************************************************************)
(* Implement a function Fact32 to compute SND(Fact32Iter (n,1))              *)
(*****************************************************************************)

val Fact32_def =
 Define
  `Fact32 n = SND(Fact32Iter (n,1w))`;

val FactAbs =
 Q.store_thm
  ("FactAbs",
   `!n. FACT n < dimword(:32) ==> (FACT n = w2n(Fact32(n2w n)))`,
   RW_TAC arith_ss [Fact32_def,Once Fact32Iter_def]
    THENL
     [FULL_SIMP_TAC (srw_ss()) []
       THEN `n < 4294967296`
         by PROVE_TAC[DECIDE ``m:num <= n /\ n < p ==> m < p``,FACT_LESS_EQ]
       THEN `n = 0` by PROVE_TAC[LESS_MOD]
       THEN RW_TAC arith_ss [FACT],
      `n < dimword(:32)`
         by PROVE_TAC[DECIDE ``m:num <= n /\ n < p ==> m < p``,FACT_LESS_EQ]
       THEN RW_TAC arith_ss [MultAbsCor2,MultAbsCor2,WORD_MULT_CLAUSES]
       THEN ASSUME_TAC (INST_TYPE [alpha |-> ``:32``] ONE_LT_dimword)
       THEN Cases_on `n=0`
       THEN FULL_SIMP_TAC arith_ss []
       THEN `1 <= n` by DECIDE_TAC
       THEN RW_TAC arith_ss [WORD_LITERAL_ADD, word_sub_def]
       THEN `SUC(n-1) = n` by DECIDE_TAC
       THEN `n * FACT(n-1) < dimword(:32)` by PROVE_TAC[FACT]
       THEN RW_TAC arith_ss [FactIterAbsCor,word_mul_n2w]
       THEN `n * FACT(n-1) = FACT n` by PROVE_TAC[FACT]
       THEN RW_TAC arith_ss [w2n_n2w]]);

(*
  |- FACT 12 < dimword(:32) = T : thm
  |- FACT 13 < dimword(:32) = F : thm
*)
val _ = export_theory();
