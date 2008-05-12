(*---------------------------------------------------------------------------*)
(* Multiplication by a constant. Recursive, iterative, and table-lookup      *)
(* versions.                                                                 *)
(*---------------------------------------------------------------------------*)

(* For interactive work
  load "wordsLib";
  quietdec := true;
  open wordsTheory bitTheory wordsLib arithmeticTheory;
  quietdec := false;
*)

open HolKernel Parse boolLib bossLib 
     wordsTheory bitTheory wordsLib arithmeticTheory;

val _ = new_theory "Mult";

(*---------------------------------------------------------------------------
    Multiply a byte (representing a polynomial) by x. 

 ---------------------------------------------------------------------------*)

val xtime_def = Define
  `xtime (w : word8) =
     w << 1 ?? (if word_msb w then 0x1Bw else 0w)`;

val MSB_lem = Q.prove (
  `!a b. word_msb (a ?? b) = ~(word_msb a = word_msb b)`,
  SRW_TAC [WORD_BIT_EQ_ss] []);

val xtime_distrib = Q.store_thm
("xtime_distrib",
 `!a b. xtime (a ?? b) = xtime a ?? xtime b`,
  SRW_TAC [] [xtime_def, MSB_lem] THEN FULL_SIMP_TAC std_ss []);

(*---------------------------------------------------------------------------*)
(* Multiplication by a constant                                              *)
(*---------------------------------------------------------------------------*)

val _ = set_fixity "**" (Infixl 675);

val (ConstMult_def,ConstMult_ind) = 
 Defn.tprove
  (Hol_defn "ConstMult"
     `b1 ** b2 =
        if b1 = 0w:word8 then 0w else 
        if word_lsb b1
           then b2 ?? ((b1 >>> 1) ** xtime b2)
           else       ((b1 >>> 1) ** xtime b2)`,
   WF_REL_TAC `measure (w2n o FST)`);

val _ = save_thm("ConstMult_def",ConstMult_def);
val _ = save_thm("ConstMult_ind",ConstMult_ind);
val _ = computeLib.add_persistent_funs [("ConstMult_def",ConstMult_def)];

val ConstMultDistrib = Q.store_thm
("ConstMultDistrib",
 `!x y z. x ** (y ?? z) = (x ** y) ?? (x ** z)`,
 recInduct ConstMult_ind
   THEN REPEAT STRIP_TAC
   THEN ONCE_REWRITE_TAC [ConstMult_def]
   THEN SRW_TAC [] [xtime_distrib]);

(*---------------------------------------------------------------------------*)
(* Iterative version                                                         *)
(*---------------------------------------------------------------------------*)

val defn = Hol_defn 
  "IterConstMult"
  `IterConstMult (b1,b2,acc) =
     if b1 = 0w:word8 then (b1,b2,acc)
     else IterConstMult (b1 >>> 1, xtime b2,
                         if word_lsb b1 then (b2 ?? acc) else acc)`;

val (IterConstMult_def,IterConstMult_ind) = 
 Defn.tprove
  (defn, WF_REL_TAC `measure (w2n o FST)`);

val _ = save_thm("IterConstMult_def",IterConstMult_def);
val _ = save_thm("IterConstMult_ind",IterConstMult_ind);
val _ = computeLib.add_persistent_funs [("IterConstMult_def",IterConstMult_def)];

(*---------------------------------------------------------------------------*)
(* Equivalence between recursive and iterative forms.                        *)
(*---------------------------------------------------------------------------*)

val ConstMultEq = Q.store_thm
("ConstMultEq",
 `!b1 b2 acc. (b1 ** b2) ?? acc = SND(SND(IterConstMult (b1,b2,acc)))`,
 recInduct IterConstMult_ind THEN RW_TAC std_ss []
   THEN ONCE_REWRITE_TAC [ConstMult_def,IterConstMult_def]
   THEN FULL_SIMP_TAC (srw_ss()) [] THEN SRW_TAC [] []);

(*---------------------------------------------------------------------------*)
(* Tabled versions                                                           *)
(*---------------------------------------------------------------------------*)

fun UNROLL_RULE 0 def = def
  | UNROLL_RULE n def = 
     SIMP_RULE arith_ss [LSR_ADD]
     (GEN_REWRITE_RULE (RHS_CONV o DEPTH_CONV) empty_rewrites [def]
                       (UNROLL_RULE (n - 1) def))
val instantiate =
 SIMP_RULE (srw_ss()) [WORD_XOR_CLAUSES, GSYM xtime_distrib] o 
 ONCE_REWRITE_CONV [UNROLL_RULE 4 ConstMult_def]

val IterMult2 = UNROLL_RULE 1 IterConstMult_def

(*---------------------------------------------------------------------------*)
(* mult_unroll                                                               *)
(*    |- (2w ** x = xtime x) /\                                              *)
(*       (3w ** x = x # xtime x) /\                                          *)
(*       (9w ** x = x # xtime (xtime (xtime x)))      /\                     *)
(*       (11w ** x = x # xtime (x # xtime (xtime x))) /\                     *)
(*       (13w ** x = x # xtime (xtime (x # xtime x))) /\                     *)
(*       (14w ** x = xtime (x # xtime (x # xtime x)))                        *)
(*---------------------------------------------------------------------------*)

val mult_unroll = save_thm("mult_unroll",
  LIST_CONJ (map instantiate
    [``0x2w ** x``, ``0x3w ** x``, ``0x9w ** x``,
     ``0xBw ** x``, ``0xDw ** x``, ``0xEw ** x``]));

val eval_mult = WORD_EVAL_RULE o PURE_REWRITE_CONV [mult_unroll, xtime_def]

fun mk_word8 i = wordsSyntax.mk_n2w(numSyntax.term_of_int i, ``:8``);

(*---------------------------------------------------------------------------*)
(* Construct specialized multiplication tables.                              *)
(*---------------------------------------------------------------------------*)

val mult_tables =
  LIST_CONJ (List.concat (map (fn x => List.tabulate(256,
       fn i => let val y = mk_word8 i in eval_mult ``^x ** ^y`` end))
  [``0x2w:word8``, ``0x3w:word8``, ``0x9w:word8``,
   ``0xBw:word8``, ``0xDw:word8``, ``0xEw:word8``]));

(*---------------------------------------------------------------------------*)
(* Multiplication by constant implemented by one-step rewrites.              *)
(*---------------------------------------------------------------------------*)

val _ = save_thm ("mult_tables", mult_tables)

(*---------------------------------------------------------------------------*)
(* Multiplication by constant implemented by lookup into balanced binary     *)
(* tree. Lookup is done bit-by-bit.                                          *)
(*---------------------------------------------------------------------------*)

(*
val _ = save_thm ("mult_ifs", mult_ifs)
*)
 
(*---------------------------------------------------------------------------*)
(* Exponentiation                                                            *)
(*---------------------------------------------------------------------------*)

val PolyExp_def = 
 Define
   `PolyExp x n = if n=0 then 1w else x ** PolyExp x (n-1)`;


val _ = export_theory();
