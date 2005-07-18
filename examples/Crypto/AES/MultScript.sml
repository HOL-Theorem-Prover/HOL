(*---------------------------------------------------------------------------*)
(* Multiplication by a constant. Recursive, iterative, and table-lookup      *)
(* versions.                                                                 *)
(*---------------------------------------------------------------------------*)

(* For interactive work
  app load ["word8Theory", "metisLib", "word8CasesLib"];
  quietdec := true;
  open word8Theory bitsTheory
     word8Lib arithmeticTheory metisLib word8CasesLib;
  quietdec := false;
*)

open HolKernel Parse boolLib bossLib 
     word8Theory bitsTheory
     word8Lib arithmeticTheory metisLib word8CasesLib;

val _ = new_theory "Mult";

fun n2w_TAC v = STRIP_ASSUME_TAC (Q.SPEC v word_nchotomy) THEN
                ASM_REWRITE_TAC []

val EQ_BIT_THM = Q.prove (
`!a b. (a = b) = (!n. n < 8 ==> (WORD_BIT n a = WORD_BIT n b))`,
REPEAT STRIP_TAC THEN n2w_TAC `a` THEN n2w_TAC `b` THEN
RW_TAC arith_ss [BIT_EVAL, n2w_11, w2n_EVAL, MOD_WL_THM, GSYM BIT_BITS_THM,
                 HB_def, LE_LT1, BIT_OF_BITS_THM])

(*---------------------------------------------------------------------------
    Multiply a byte (representing a polynomial) by x. 

 ---------------------------------------------------------------------------*)

val xtime_def = Define
  `xtime (w : word8) =
     w << 1 # (if MSB w then
                 0x1Bw
               else
                 0w)`;

val MSB_lem = Q.prove (
`!a b. MSB (a # b) = ~(MSB a = MSB b)`,
REPEAT STRIP_TAC THEN n2w_TAC `a` THEN n2w_TAC `b` THEN 
RW_TAC arith_ss [EOR_EVAL, EOR_def, MSB_EVAL, MSBn_def, HB_def, WL_def,
                 BITWISE_THM]);

val xtime_distrib = Q.store_thm
("xtime_distrib",
 `!a b. xtime (a # b) = xtime a # xtime b`,
 RW_TAC std_ss [EQ_BIT_THM, xtime_def, MSB_lem, WORD_EOR_ID] THEN
 FULL_SIMP_TAC std_ss [] THEN RW_TAC std_ss [] THEN
 n2w_TAC `a` THEN n2w_TAC `b` THEN
 RW_TAC arith_ss [BIT_EVAL, EOR_EVAL, LSL_EVAL, HB_def, MUL_EVAL, w2n_EVAL,
                  MOD_WL_THM, MIN_DEF, BIT_OF_BITS_THM, EOR_def, WL_def,
                  BITWISE_THM] THEN
 PURE_ONCE_REWRITE_TAC [Q.prove (`!a. a * 2 = a * 2 ** 1`, RW_TAC arith_ss [])]
 THEN
 Cases_on `n<1` THEN
 FULL_SIMP_TAC arith_ss [BIT_SHIFT_THM3, NOT_LESS, BIT_SHIFT_THM2, BITWISE_THM] THEN
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
   THEN RW_TAC std_ss [xtime_distrib, AC WORD_EOR_ASSOC WORD_EOR_COMM]
   THEN WORD_TAC);

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
   THEN RW_TAC std_ss [AC WORD_EOR_ASSOC WORD_EOR_COMM]
   THEN FULL_SIMP_TAC std_ss [AC WORD_EOR_ASSOC WORD_EOR_COMM, WORD_EOR_ID]);


(*---------------------------------------------------------------------------*)
(* Tabled versions                                                           *)
(*---------------------------------------------------------------------------*)

fun UNROLL_RULE 0 def = def
  | UNROLL_RULE n def = 
     SIMP_RULE arith_ss [LSR_ADD]
     (GEN_REWRITE_RULE (RHS_CONV o DEPTH_CONV) empty_rewrites [def]
                       (UNROLL_RULE (n - 1) def))
val instantiate =
 SIMP_RULE arith_ss [WORD_EOR_ID, GSYM xtime_distrib] o 
 WORD_RULE o
 ONCE_REWRITE_CONV [UNROLL_RULE 4 ConstMult_def]

val IterMult2 = UNROLL_RULE 1 IterConstMult_def

val mult_thm =
LIST_CONJ (map instantiate [``0x2w ** x``, ``0x3w ** x``, ``0x9w ** x``,
                            ``0xBw ** x``, ``0xDw ** x``, ``0xEw ** x``])

val eval_mult =
WORD_RULE o PURE_REWRITE_CONV [mult_thm, xtime_def]

fun build_table arg1 = word8GenCases `$** ^arg1` eval_mult

(*---------------------------------------------------------------------------*)
(* Construct specialized multiplication tables.                              *)
(*---------------------------------------------------------------------------*)

val (mult_tables, mult_ifs) =
let val (ifs, tables) =
        unzip (map (Count.apply build_table)
               [``0x2w``, ``0x3w``, ``0x9w``, ``0xBw``, ``0xDw``, ``0xEw``])
in
(LIST_CONJ tables, LIST_CONJ ifs)
end

(*---------------------------------------------------------------------------*)
(* mult_unroll                                                               *)
(*    |- (2w ** x = xtime x) /\                                              *)
(*       (3w ** x = x # xtime x) /\                                          *)
(*       (9w ** x = x # xtime (xtime (xtime x)))      /\                     *)
(*       (11w ** x = x # xtime (x # xtime (xtime x))) /\                     *)
(*       (13w ** x = x # xtime (xtime (x # xtime x))) /\                     *)
(*       (14w ** x = xtime (x # xtime (x # xtime x)))                        *)
(*---------------------------------------------------------------------------*)

val _ = save_thm ("mult_unroll", mult_thm)

(*---------------------------------------------------------------------------*)
(* Multiplication by constant implemented by one-step rewrites.              *)
(*---------------------------------------------------------------------------*)

val _ = save_thm ("mult_tables", mult_tables)

(*---------------------------------------------------------------------------*)
(* Multiplication by constant implemented by lookup into balanced binary     *)
(* tree. Lookup is done bit-by-bit.                                          *)
(*---------------------------------------------------------------------------*)

val _ = save_thm ("mult_ifs", mult_ifs)
 
(*---------------------------------------------------------------------------*)
(* Exponentiation                                                            *)
(*---------------------------------------------------------------------------*)

val PolyExp_def = 
 Define
   `PolyExp x n = if n=0 then 1w else x ** PolyExp x (n-1)`;


val _ = export_theory();
