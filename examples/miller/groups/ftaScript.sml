(* non-interactive mode
*)
open HolKernel Parse boolLib;
val _ = new_theory "fta";
val _ = ParseExtras.temp_loose_equality()

(* interactive mode
show_assums := true;
loadPath := union ["..", "../finished"] (!loadPath);
app load
["bossLib", "listTheory", "millerTools", "subtypeTools",
"res_quanTools", "res_quan2Theory", "pred_setTheory",
"extra_pred_setTheory", "arithContext", "listContext",
"relationTheory", "ho_proverTools", "prob_extraTools",
"prob_extraTheory", "extra_listTheory", "orderTheory",
"arithmeticTheory", "extra_arithTheory", "subtypeTheory",
"primeTheory", "dividesTheory", "gcdTheory"];
*)

open bossLib listTheory hurdUtils subtypeTools
     pred_setTheory dividesTheory gcdTheory extra_pred_setTheory
     arithContext listContext relationTheory
     ho_proverTools extra_listTheory
     orderTheory arithmeticTheory extra_arithTheory subtypeTheory


infixr 0 ++ << || THENC ORELSEC ORELSER ##;
infix 1 >>;

val op!! = op REPEAT;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Tools.                                                                    *)
(* ------------------------------------------------------------------------- *)

val S_TAC = !! (POP_ASSUM MP_TAC) ++ !! STRIP_TAC;

val std_pc = precontext_mergel [arith_pc, list_pc];
val std_c = precontext_compile std_pc;

val (R_TAC, AR_TAC, R_TAC', AR_TAC') = SIMPLIFY_TACS std_c;


(* ------------------------------------------------------------------------- *)
(* Definitions.                                                             *)
(* ------------------------------------------------------------------------- *)

val factorizes_def = Define
  `factorizes n l = EVERY prime l /\ sorted $<= l /\ (prod l = n)`;

(* ------------------------------------------------------------------------- *)
(* Theorems.                                                                 *)
(* ------------------------------------------------------------------------- *)

val EMPTY_FACTORIZES = store_thm
  ("EMPTY_FACTORIZES",
   ``factorizes 1 []``,
   R_TAC [factorizes_def, EVERY_DEF, prod_def, sorted_def]);

val LEQ_TOTALORDER = store_thm
  ("LEQ_TOTALORDER",
   ``totalorder ($<= : num -> num -> bool)``,
   R_TAC [totalorder_def, partialorder_def, preorder_def,
          reflexive_def, antisym_def, transitive_def, total_def]
   ++ DECIDE_TAC);

val PROD_INSERT = store_thm
  ("PROD_INSERT",
   ``!p f l. prod (insert f p l) = p * prod l``,
   S_TAC
   ++ Induct_on `l` >> R_TAC [prod_def, insert_def]
   ++ R_TAC [prod_def, insert_def]
   ++ S_TAC
   ++ Cases_on `f p h` >> R_TAC [prod_def]
   ++ R_TAC [prod_def]
   ++ PROVE_TAC [MULT_COMM, MULT_ASSOC]);

val EVERY_INSERT = store_thm
  ("EVERY_INSERT",
   ``!f p x l. EVERY p (insert f x l) = (p x) /\ EVERY p l``,
   S_TAC
   ++ Induct_on `l` >> R_TAC [EVERY_DEF, insert_def]
   ++ R_TAC [EVERY_DEF, insert_def]
   ++ S_TAC
   ++ Cases_on `f x h` >> R_TAC [EVERY_DEF]
   ++ R_TAC [EVERY_DEF]
   ++ ho_PROVE_TAC []);

val FACTORIZES_MULT = store_thm
  ("FACTORIZES_MULT",
   ``!p n l.
       prime p ==>
       (factorizes (p * n) (insert $<= p l) = factorizes n l)``,
   S_TAC
   ++ R_TAC [factorizes_def, LEQ_TOTALORDER, INSERT_SORTED,
             PROD_INSERT, EVERY_INSERT, EQ_MULT_LCANCEL]);

val CONS_SORTED = store_thm
  ("CONS_SORTED",
   ``!f h t.
       totalorder f ==>
       (sorted f (h :: t) = (!x. MEM x t ==> f h x) /\ sorted f t)``,
   S_TAC
   ++ Q.SPEC_TAC (`h`, `y`)
   ++ Induct_on `t` >> R_TAC [sorted_def, MEM]
   ++ R_TAC [sorted_def, MEM]
   ++ POP_ASSUM K_TAC
   ++ AR_TAC [totalorder_def, partialorder_def, preorder_def, transitive_def]
   ++ PROVE_TAC []);

val CONS_FACTORIZES = store_thm
  ("CONS_FACTORIZES",
   ``!p n l.
       factorizes n (p :: l) =
       prime p /\ divides p n /\ (!x. MEM x l ==> p <= x) /\
       factorizes (n DIV p) l``,
   R_TAC [factorizes_def, EVERY_DEF, CONS_SORTED,
          LEQ_TOTALORDER, prod_def, DIVIDES_ALT]
   ++ S_TAC
   ++ REVERSE EQ_TAC >> PROVE_TAC [MULT_COMM]
   ++ STRIP_TAC
   ++ Suff `prod l = n DIV p` >> PROVE_TAC [MULT_COMM]
   ++ Suff `p * prod l = p * (n DIV p)` >> R_TAC []
   ++ ASM_REWRITE_TAC []
   ++ Know `divides p n` >> PROVE_TAC [MULT_COMM, divides_def]
   ++ R_TAC [DIVIDES_ALT]
   ++ PROVE_TAC [MULT_COMM]);

val FACTORIZES_EXISTS = store_thm
  ("FACTORIZES_EXISTS",
   ``!n. 0 < n ==> ?l. factorizes n l``,
   R_TAC []
   ++ HO_MATCH_MP_TAC FACTOR_INDUCT
   ++ CONJ_TAC >> AR_TAC []
   ++ CONJ_TAC >> PROVE_TAC [EMPTY_FACTORIZES]
   ++ S_TAC
   ++ AR_TAC []
   ++ PROVE_TAC [FACTORIZES_MULT, MULT_COMM]);

val EMPTY_FACTORIZES_UNIQUE = store_thm
  ("EMPTY_FACTORIZES_UNIQUE",
   ``!n. factorizes n [] = (n = 1)``,
   S_TAC
   ++ R_TAC [factorizes_def, EVERY_DEF, sorted_def, prod_def]
   ++ PROVE_TAC []);

val FACTORIZES_1_UNIQUE = store_thm
  ("FACTORIZES_1_UNIQUE",
   ``!l. factorizes 1 l = (l = [])``,
   Cases >> R_TAC [EMPTY_FACTORIZES]
   ++ AR_TAC [factorizes_def, EVERY_DEF, sorted_def, prod_def]
   ++ S_TAC
   ++ Know `divides h 1`
   >> (R_TAC [divides_def] ++ PROVE_TAC [MULT_COMM])
   ++ S_TAC
   ++ AR_TAC []);

val FACTORIZES_0 = store_thm
  ("FACTORIZES_0",
   ``!l. ~factorizes 0 l``,
   Induct >> (R_TAC [EMPTY_FACTORIZES_UNIQUE] ++ DECIDE_TAC)
   ++ R_TAC [CONS_FACTORIZES]);

val PRIME_FACTORIZES = store_thm
  ("PRIME_FACTORIZES",
   ``!p l n. prime p /\ factorizes n l ==> (divides p n = MEM p l)``,
   STRIP_TAC
   ++ Induct >> R_TAC [EMPTY_FACTORIZES_UNIQUE, MEM]
   ++ R_TAC [CONS_FACTORIZES]
   ++ S_TAC
   ++ Know `n = (n DIV h) * h` >> AR_TAC [DIVIDES_ALT]
   ++ DISCH_THEN (ONCE_REWRITE_TAC o wrap)
   ++ R_TAC [EUCLID, MEM]
   ++ PROVE_TAC []);

val FACTORIZES_UNIQUE = store_thm
  ("FACTORIZES_UNIQUE",
   ``!n l l'. factorizes n l /\ factorizes n l' ==> (l = l')``,
   Suff `!l l' n. factorizes n l /\ factorizes n l' ==> (l = l')`
   >> PROVE_TAC []
   ++ Induct >> R_TAC [EMPTY_FACTORIZES_UNIQUE, FACTORIZES_1_UNIQUE]
   ++ STRIP_TAC
   ++ Cases >> R_TAC [EMPTY_FACTORIZES_UNIQUE, FACTORIZES_1_UNIQUE]
   ++ S_TAC
   ++ AR_TAC [CONS_FACTORIZES]
   ++ REVERSE STRONG_CONJ_TAC >> PROVE_TAC []
   ++ CCONTR_TAC
   ++ Suff `h' <= h /\ h <= h'` >> DECIDE_TAC
   ++ S_TAC <<
   [Know `divides h ((n DIV h') * h')`
    >> (Suff `(n DIV h') * h' = n` >> R_TAC [] ++ AR_TAC [DIVIDES_ALT])
    ++ R_TAC [EUCLID, PRIME_FACTORIZES],
    Know `divides h' ((n DIV h) * h)`
    >> (Suff `(n DIV h) * h = n` >> R_TAC [] ++ AR_TAC [DIVIDES_ALT])
    ++ R_TAC [EUCLID, PRIME_FACTORIZES]
    ++ PROVE_TAC []]);

val FUNDAMENTAL_ARITHMETIC = store_thm
  ("FUNDAMENTAL_ARITHMETIC",
   ``!n. 0 < n ==> ?!l. factorizes n l``,
   R_TAC [EXISTS_UNIQUE_DEF, FACTORIZES_EXISTS]
   ++ S_TAC
   ++ PROVE_TAC [FACTORIZES_UNIQUE]);

(* non-interactive mode
*)
val _ = export_theory ();
