(*---------------------------------------------------------------------------*)
(* Multiplication by a constant. Recursive, iterative, and table-lookup      *)
(* versions.                                                                 *)
(*---------------------------------------------------------------------------*)

(* For interactive work
  app load ["word8Theory", "metisLib", "word8CasesLib"];
  quietdec := true;
  open word8Theory (*tablesTheory*) bitsTheory
     word8Lib arithmeticTheory metisLib word8CasesLib;
  quietdec := false;
*)

open HolKernel Parse boolLib bossLib 
     word8Theory (*tablesTheory*) bitsTheory
     word8Lib arithmeticTheory metisLib word8CasesLib;

val _ = new_theory "Mult";

fun n2w_TAC v = ASSUME_TAC (Q.SPEC v word_nchotomy) THEN RW_TAC std_ss []

val lem = Q.prove (
`!n h a. n <= h ==> (BIT n (BITS h 0 a) = BIT n a)`,
RW_TAC arith_ss [BIT_def, BITS_COMP_THM])

val EQ_BIT_THM = Q.prove (
`!a b. (a = b) = (!n. n < 8 ==> (BIT n (w2n a) = BIT n (w2n b)))`,
REPEAT STRIP_TAC THEN n2w_TAC `a` THEN n2w_TAC `b` THEN
RW_TAC arith_ss [n2w_11, w2n_EVAL, MOD_WL_THM, GSYM BIT_BITS_THM, HB_def,
                 LE_LT1, lem])

val BIT_SHIFT_THM = Q.prove (
`!n a s. BIT (n + s) (a * 2 ** s) = BIT n a`,
EVAL_TAC THEN
RW_TAC arith_ss [SUC_SUB, EXP_ADD] THEN
METIS_TAC [GSYM DIV_DIV_DIV_MULT, ZERO_LT_TWOEXP,
           MULT_DIV, MULT_SYM])

val BIT_SHIFT_THM2 = Q.prove (
`!n a s. s <= n ==> (BIT n (a * 2 ** s) = BIT (n - s) a)`,
RW_TAC arith_ss [GSYM (Q.SPECL [`n-s`, `a`, `s`] BIT_SHIFT_THM)])

val EXP_SUB = Q.prove (
`!p q n. 0 < n /\ q <= p ==> (n ** (p - q) = n ** p DIV n ** q)`,
REPEAT STRIP_TAC THEN
(`0 < n ** p /\ 0 < n ** q` by Cases_on `n` THEN 
    FULL_SIMP_TAC arith_ss [ZERO_LESS_EXP]) THEN
RW_TAC arith_ss [DIV_P] THEN
Q.EXISTS_TAC `0` THEN RW_TAC arith_ss [GSYM EXP_ADD])

val EVEN_EVENEXP = Q.prove (
`!m n. n > 0 /\ EVEN m ==> EVEN (m ** n)`,
STRIP_TAC THEN Cases_on `n` THEN RW_TAC arith_ss [EXP, EVEN_MULT])

val BIT_ZERO = Q.prove (
`!n a s. (n < s) ==> (BIT n (a * 2 ** s) = F)`,
EVAL_TAC THEN
RW_TAC arith_ss [SUC_SUB, NOT_MOD2_LEM2, GSYM EVEN_MOD2] THEN
RW_TAC arith_ss [DIV_P, ZERO_LT_TWOEXP] THEN
Q.EXISTS_TAC `a * 2 ** (s - n)` THEN Q.EXISTS_TAC `0` THEN
RW_TAC arith_ss [ZERO_LT_TWOEXP,GSYM MULT_ASSOC, GSYM EXP_ADD, EVEN_MULT,
                 EVEN_EVENEXP])

val EOR_AC = Q.store_thm
("EOR_AC",
`!a b c. ((a # b) # c = a # (b # c)) /\ (a # b = b # a)`,
REPEAT STRIP_TAC THEN
n2w_TAC `a` THEN n2w_TAC `b` THEN n2w_TAC `c` THEN
RW_TAC arith_ss [EQ_BIT_THM, EOR_EVAL, EOR_def, w2n_EVAL, MOD_WL_THM, lem,
                 HB_def, WL_def, BITWISE_THM] THEN
METIS_TAC []);

(* Should prove this without brute force, so the proof would work for other 
   bit widths *)
val EOR_ID = Q.store_thm ("EOR_ID",
`!x. x # 0w = x`,
STRIP_TAC THEN word8Cases_on `x` THEN POP_ASSUM SUBST_ALL_TAC THEN WORD_TAC);

val [a, c] = map GEN_ALL (CONJUNCTS (SPEC_ALL EOR_AC))

val EOR_INV = Q.store_thm 
("EOR_INV",
 `!x. x # x = 0w`,
 STRIP_TAC THEN word8Cases_on `x` THEN POP_ASSUM SUBST_ALL_TAC THEN WORD_TAC);

(*
val LSR1_LESS = Q.prove (
`!n. 0w < n ==> n >>> 1 < n`,
REPEAT STRIP_TAC THEN n2w_TAC `n` THEN WORD_TAC THEN EVAL_TAC THEN
RW_TAC arith_ss []
*)

(*---------------------------------------------------------------------------
    Multiply a byte (representing a polynomial) by x. 

 ---------------------------------------------------------------------------*)

val xtime_def = Define
  `xtime (w : word8) =
     if MSB w then
       w << 1 # 0x1Bw
     else
       w << 1`;

val MSB_lem = Q.prove (
`!a b. MSB (a # b) = ~(MSB a = MSB b)`,
REPEAT STRIP_TAC THEN n2w_TAC `a` THEN n2w_TAC `b` THEN 
RW_TAC arith_ss [EOR_EVAL, EOR_def, MSB_EVAL, MSBn_def, HB_def, WL_def,
                 BITWISE_THM]);


val xtime_distrib = Q.store_thm
("xtime_distrib",
 `!a b. xtime (a # b) = xtime a # xtime b`,
 RW_TAC std_ss [EQ_BIT_THM, xtime_def, MSB_lem] THEN
 FULL_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
 n2w_TAC `a` THEN n2w_TAC `b` THEN
 RW_TAC arith_ss [EOR_EVAL, LSL_EVAL, HB_def, MUL_EVAL, w2n_EVAL, MOD_WL_THM,
                  MIN_DEF, lem, EOR_def, WL_def, BITWISE_THM] THEN
 PURE_ONCE_REWRITE_TAC [Q.prove (`!a. a * 2 = a * 2 ** 1`, RW_TAC arith_ss [])]
 THEN
 Cases_on `n<1` THEN
 FULL_SIMP_TAC arith_ss [BIT_ZERO, NOT_LESS, BIT_SHIFT_THM2, BITWISE_THM] THEN
 METIS_TAC []);


(*---------------------------------------------------------------------------*)
(* Multiplication by a constant                                              *)
(*---------------------------------------------------------------------------*)

val _ = set_fixity "**" (Infixl 675);

val (ConstMult_def,ConstMult_ind) = 
 Defn.tprove
  (Hol_defn "ConstMult"
     `b1 ** b2 =
        if b1 = 0w then 0w else 
        if LSB b1
           then b2 # ((b1 >>> 1) ** xtime b2)
           else      ((b1 >>> 1) ** xtime b2)`,
   WF_REL_TAC `measure (w2n o FST)` THEN 
   (* It would be nice to use LSR1_LESS instead of brute force, but
      I didn't finish proving it.  *)
   STRIP_TAC THEN word8Cases_on `b1` THEN 
   RW_TAC std_ss [] THEN REPEAT (POP_ASSUM MP_TAC) THEN WORD_TAC)

val _ = save_thm("ConstMult_def",ConstMult_def);
val _ = save_thm("ConstMult_ind",ConstMult_ind);
val _ = computeLib.add_persistent_funs [("ConstMult_def",ConstMult_def)];

val ConstMultDistrib = Q.store_thm
("ConstMultDistrib",
 `!x y z. x ** (y # z) = (x ** y) # (x ** z)`,
 recInduct ConstMult_ind
   THEN REPEAT STRIP_TAC
   THEN ONCE_REWRITE_TAC [ConstMult_def]
   THEN RW_TAC std_ss [xtime_distrib, AC a c] THEN WORD_TAC);

(*---------------------------------------------------------------------------*)
(* Iterative version                                                         *)
(*---------------------------------------------------------------------------*)

val defn = Hol_defn 
  "IterConstMult"
  `IterConstMult (b1,b2,acc) =
     if b1 = 0w then (b1,b2,acc)
     else IterConstMult (b1 >>> 1, xtime b2,
                         if LSB b1 then (b2 # acc) else acc)`;

val (IterConstMult_def,IterConstMult_ind) = 
 Defn.tprove
  (defn,
   WF_REL_TAC `measure (w2n o FST)` THEN STRIP_TAC THEN
   word8Cases_on `b1` THEN 
   RW_TAC std_ss [] THEN REPEAT (POP_ASSUM MP_TAC) THEN WORD_TAC);

val _ = save_thm("IterConstMult_def",IterConstMult_def);
val _ = save_thm("IterConstMult_ind",IterConstMult_ind);
val _ = computeLib.add_persistent_funs [("IterConstMult_def",IterConstMult_def)];

(*---------------------------------------------------------------------------*)
(* Equivalence between recursive and iterative forms.                        *)
(*---------------------------------------------------------------------------*)

val ConstMultEq = Q.store_thm
("ConstMultEq",
 `!b1 b2 acc. (b1 ** b2) # acc = SND(SND(IterConstMult (b1,b2,acc)))`,
 recInduct IterConstMult_ind THEN RW_TAC std_ss []
   THEN ONCE_REWRITE_TAC [ConstMult_def,IterConstMult_def]
   THEN RW_TAC std_ss [AC a c]
   THEN FULL_SIMP_TAC std_ss [AC a c, EOR_ID]);


(*---------------------------------------------------------------------------*)
(* Specialized version, with partially evaluated multiplication. Uses tables *)
(* from tablesTheory.                                                        *)
(*---------------------------------------------------------------------------*)
(*
val TableConstMult_def = word8Define
 `(tcm 0x2w = GF256_by_2)  /\
  (tcm 0x3w = GF256_by_3)  /\
  (tcm 0x9w = GF256_by_9)  /\
  (tcm 0xBw = GF256_by_11) /\
  (tcm 0xDw = GF256_by_13) /\
  (tcm 0xEw = GF256_by_14)`
*)
(*---------------------------------------------------------------------------*)
(* Unrolled version                                                          *)
(*---------------------------------------------------------------------------*)

fun UNROLL_RULE 0 def = def
  | UNROLL_RULE n def = 
     SIMP_RULE arith_ss [LSR_ADD]
     (GEN_REWRITE_RULE (RHS_CONV o DEPTH_CONV) empty_rewrites [def]
                       (UNROLL_RULE (n - 1) def))
val instantiate =
 SIMP_RULE arith_ss [EOR_ID, GSYM xtime_distrib] o 
 WORD_RULE o
 ONCE_REWRITE_CONV [UNROLL_RULE 4 ConstMult_def]

val IterMult2 = UNROLL_RULE 1 IterConstMult_def

val mult_thm =
LIST_CONJ (map instantiate [``0x2w ** x``, ``0x3w ** x``, ``0x9w ** x``,
                            ``0xBw ** x``, ``0xDw ** x``, ``0xEw ** x``])

val eval_mult =
WORD_RULE o PURE_REWRITE_CONV [mult_thm, xtime_def]

fun build_table arg1 = 
LIST_CONJ (map (fn x => eval_mult ``^arg1 ** n2w ^(numSyntax.term_of_int x)``)
               (upto 0 255))

val mult_tables =
LIST_CONJ (map (Count.apply build_table)
               [``0x2w``, ``0x3w``, ``0x9w``, ``0xBw``, ``0xDw``, ``0xEw``])

val _ = save_thm ("mult_tables", mult_tables)
(*---------------------------------------------------------------------------*)
(* Directly looking up answers in specialized tables is equivalent to        *)
(* the multiplication algorithm each time. And should be much faster!        *)
(*---------------------------------------------------------------------------*)
(*
val MultEquiv = Count.apply Q.store_thm
 ("MultEquiv",
  `!b. (tcm 0x2w b = 0x2w ** b) /\
       (tcm 0x3w b = 0x3w ** b) /\
       (tcm 0x9w b = 0x9w ** b) /\
       (tcm 0xBw b = 0xBw ** b) /\
       (tcm 0xDw b = 0xDw ** b) /\
       (tcm 0xEw b = 0xEw ** b)`,
 STRIP_TAC THEN PURE_ONCE_REWRITE_TAC [TableConstMult_def] THEN
 word8Cases_on `b` THEN
 RW_TAC arith_ss [GF256_by_2_def, GF256_by_3_def,
                  GF256_by_9_def, GF256_by_11_def, GF256_by_13_def,
                  GF256_by_14_def, mult_thm] THEN
 PURE_REWRITE_TAC [xtime_def] THEN WORD_TAC)
*)
(*---------------------------------------------------------------------------*)
(* Exponentiation                                                            *)
(*---------------------------------------------------------------------------*)

val PolyExp_def = 
 Define
   `PolyExp x n = if n=0 then 1w else x ** PolyExp x (n-1)`;


val _ = export_theory();
