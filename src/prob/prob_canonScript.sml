(* non-interactive mode
*)
open HolKernel Parse boolLib;

val _ = new_theory "prob_canon";

(* interactive mode
if !show_assums then () else (
  load "bossLib";
  load "realLib";
  load "arithmeticTheory";
  load "pred_setTheory";
  load "rich_listTheory";
  load "pairTheory";
  load "probUtil";
  load "probExtraTheory";
  show_assums := true
);
*)

open bossLib arithmeticTheory realTheory seqTheory pred_setTheory pairLib
     listTheory rich_listTheory pairTheory realLib
     probTools prob_extraTheory;

infixr 0 ++ << || ORELSEC ##;
infix 1 >>;
nonfix THEN THENL ORELSE;

val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;

(* ------------------------------------------------------------------------- *)
(* Definition of the canonicalisation of algebra elements.                   *)
(* ------------------------------------------------------------------------- *)

val alg_twin_def = Define
  `alg_twin x y = ?l. (x = SNOC T l) /\ (y = SNOC F l)`;

val alg_order_def = Define
    `(alg_order [] _ = T)
  /\ (alg_order _ [] = F)
  /\ (alg_order (h::t) (h'::t') = ((h = T) /\ (h' = F))
      \/ ((h = h') /\ alg_order t t'))`;

val alg_sorted_def = Define `(alg_sorted (x::y::z)
      = alg_order x y /\ alg_sorted (y::z))
  /\ (alg_sorted l = T)`;

val alg_prefixfree_def = Define `(alg_prefixfree ((x:bool list)::y::z)
      = ~IS_PREFIX y x /\ alg_prefixfree (y::z))
  /\ (alg_prefixfree l = T)`;

val alg_twinfree_def = Define `(alg_twinfree (x::y::z)
      = ~(alg_twin x y) /\ alg_twinfree (y::z))
  /\ (alg_twinfree l = T)`;

val alg_longest_def = Define `alg_longest
  = FOLDR (\h t. if t <= LENGTH (h:bool list) then LENGTH h else t) 0`

val alg_canon_prefs_def = Define `(alg_canon_prefs (l:bool list) [] = [l])
  /\ (alg_canon_prefs l (h::t) = if IS_PREFIX h l then alg_canon_prefs l t
				 else l::h::t)`;

val alg_canon_find_def = Define `(alg_canon_find l [] = [l])
  /\ (alg_canon_find l (h::t) = if alg_order h l then
          if IS_PREFIX l h then (h::t) else h::(alg_canon_find l t)
	else alg_canon_prefs l (h::t))`;

val alg_canon1_def = Define `alg_canon1 = FOLDR alg_canon_find []`;

val alg_canon_merge_def = Define `(alg_canon_merge l [] = [l])
  /\ (alg_canon_merge l (h::t)
      = if alg_twin l h then alg_canon_merge (BUTLAST h) t else l::h::t)`;

val alg_canon2_def = Define `alg_canon2 = FOLDR alg_canon_merge []`;

val alg_canon_def = Define `alg_canon l = alg_canon2 (alg_canon1 l)`;

val algebra_canon_def = Define `algebra_canon l = (alg_canon l = l)`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1. Canonical form is the same as sorted, prefixfree and twinfree.         *)
(* 2. Induction principle on elements in canonical form.                     *)
(* ------------------------------------------------------------------------- *)

val ALG_TWIN_NIL = store_thm
  ("ALG_TWIN_NIL",
   ``!l. ~(alg_twin l []) /\ ~(alg_twin [] l)``,
   RW_TAC std_ss [alg_twin_def]
   ++ Cases_on `l'`
   ++ RW_TAC std_ss [SNOC]);

val ALG_TWIN_SING = store_thm
  ("ALG_TWIN_SING",
   ``!x l. (alg_twin [x] l = (x = T) /\ (l = [F]))
           /\ (alg_twin l [x] = (l = [T]) /\ (x = F))``,
   GEN_TAC ++ Q.X_GEN_TAC `m` ++ RW_TAC std_ss [alg_twin_def] <<
   [EQ_TAC <<
    [Cases_on `m` >> PROVE_TAC [NOT_NIL_SNOC]
     ++ STRIP_TAC
     ++ NTAC 2 (POP_ASSUM MP_TAC)
     ++ REVERSE (Cases_on `l`) >> RW_TAC std_ss [SNOC, NOT_NIL_SNOC]
     ++ RW_TAC std_ss [SNOC],
     RW_TAC std_ss []
     ++ Q.EXISTS_TAC `[]`
     ++ RW_TAC std_ss [SNOC]],
    EQ_TAC <<
    [Cases_on `m` >> PROVE_TAC [NOT_NIL_SNOC]
     ++ STRIP_TAC
     ++ NTAC 2 (POP_ASSUM MP_TAC)
     ++ REVERSE (Cases_on `l`) >> RW_TAC std_ss [SNOC, NOT_NIL_SNOC]
     ++ RW_TAC std_ss [SNOC],
     RW_TAC std_ss []
     ++ Q.EXISTS_TAC `[]`
     ++ RW_TAC std_ss [SNOC]]]);

val ALG_TWIN_CONS = store_thm
  ("ALG_TWIN_CONS",
   ``!x y z h t. (alg_twin (x::y::z) (h::t) = (x = h) /\ alg_twin (y::z) t)
              /\ (alg_twin (h::t) (x::y::z) = (x = h) /\ alg_twin t (y::z))``,
   RW_TAC std_ss [alg_twin_def] <<
   [EQ_TAC <<
    [STRIP_TAC
     ++ NTAC 2 (POP_ASSUM MP_TAC)
     ++ Cases_on `l` >> RW_TAC std_ss [SNOC]
     ++ Cases_on `t'`
     >> (RW_TAC std_ss [SNOC]
         ++ Q.EXISTS_TAC `[]`
         ++ RW_TAC std_ss [SNOC])
     ++ RW_TAC std_ss [SNOC]
     ++ Q.EXISTS_TAC `h''::t''`
     ++ RW_TAC std_ss [SNOC],
     RW_TAC std_ss []
     ++ Q.EXISTS_TAC `h::l`
     ++ RW_TAC std_ss [SNOC]],
    EQ_TAC <<
    [STRIP_TAC
     ++ NTAC 2 (POP_ASSUM MP_TAC)
     ++ Cases_on `l` >> RW_TAC std_ss [SNOC]
     ++ Cases_on `t'`
     >> (RW_TAC std_ss [SNOC]
         ++ Q.EXISTS_TAC `[]`
         ++ RW_TAC std_ss [SNOC])
     ++ RW_TAC std_ss [SNOC]
     ++ Q.EXISTS_TAC `h''::t''`
     ++ RW_TAC std_ss [SNOC],
     RW_TAC std_ss []
     ++ Q.EXISTS_TAC `h::l`
     ++ RW_TAC std_ss [SNOC]]]);

val ALG_TWIN_REDUCE = store_thm
  ("ALG_TWIN_REDUCE",
   ``!h t t'. alg_twin (h::t) (h::t') = alg_twin t t'``,
   Cases_on `t`
   ++ RW_TAC std_ss [ALG_TWIN_CONS, ALG_TWIN_SING, ALG_TWIN_NIL]
   ++ PROVE_TAC []);

val ALG_TWINS_PREFIX = store_thm
  ("ALG_TWINS_PREFIX",
   ``!x l. IS_PREFIX x l
           ==> (x = l) \/ IS_PREFIX x (SNOC T l) \/ IS_PREFIX x (SNOC F l)``,
   Induct_on `x` >> RW_TAC list_ss [IS_PREFIX_NIL]
   ++ Cases_on `l` >> RW_TAC list_ss [SNOC, IS_PREFIX]
   ++ RW_TAC list_ss [IS_PREFIX, SNOC]);

val ALG_ORDER_NIL = store_thm
  ("ALG_ORDER_NIL",
   ``!x. alg_order [] x /\ (alg_order x [] = (x = []))``,
   Induct >> RW_TAC list_ss [alg_order_def]
   ++ RW_TAC list_ss [alg_order_def]);

val ALG_ORDER_REFL = store_thm
  ("ALG_ORDER_REFL",
   ``!x. alg_order x x``,
   Induct >> RW_TAC list_ss [alg_order_def]
   ++ RW_TAC list_ss [alg_order_def]);

val ALG_ORDER_ANTISYM = store_thm
  ("ALG_ORDER_ANTISYM",
   ``!x y. alg_order x y /\ alg_order y x ==> (x = y)``,
   Induct >> (Cases ++ RW_TAC list_ss [alg_order_def])
   ++ STRIP_TAC
   ++ Cases >> RW_TAC list_ss [alg_order_def]
   ++ (RW_TAC std_ss [alg_order_def] ++ PROVE_TAC []));

val ALG_ORDER_TRANS = store_thm
  ("ALG_ORDER_TRANS",
   ``!x y z. alg_order x y /\ alg_order y z ==> alg_order x z``,
   Induct >> (Cases_on `z` ++ RW_TAC list_ss [alg_order_def])
   ++ STRIP_TAC
   ++ Cases >> RW_TAC list_ss [alg_order_def]
   ++ Cases >> RW_TAC list_ss [alg_order_def]
   ++ (RW_TAC list_ss [alg_order_def] ++ PROVE_TAC []));

val ALG_ORDER_TOTAL = store_thm
  ("ALG_ORDER_TOTAL",
   ``!x y. alg_order x y \/ alg_order y x``,
   Induct >> PROVE_TAC [ALG_ORDER_NIL]
   ++ Cases_on `y` >> PROVE_TAC [ALG_ORDER_NIL]
   ++ RW_TAC list_ss [alg_order_def]
   ++ PROVE_TAC []);

val ALG_ORDER_PREFIX = store_thm
  ("ALG_ORDER_PREFIX",
   ``!x y. IS_PREFIX y x ==> alg_order x y``,
   Induct >> (Cases ++ RW_TAC list_ss [alg_order_def])
   ++ Cases_on `y` >> RW_TAC list_ss [IS_PREFIX_NIL]
   ++ RW_TAC list_ss [IS_PREFIX, alg_order_def]);

val ALG_ORDER_PREFIX_ANTI = store_thm
  ("ALG_ORDER_PREFIX_ANTI",
   ``!x y. alg_order x y /\ IS_PREFIX x y ==> (x = y)``,
   Induct >> RW_TAC list_ss [IS_PREFIX_NIL]
   ++ Cases_on `y` >> RW_TAC list_ss [IS_PREFIX_NIL, alg_order_def]
   ++ (RW_TAC list_ss [IS_PREFIX, alg_order_def]
	 ++ PROVE_TAC []))

val ALG_ORDER_PREFIX_MONO = store_thm
  ("ALG_ORDER_PREFIX_MONO",
   ``!x y z. alg_order x y /\ alg_order y z /\ IS_PREFIX z x
             ==> IS_PREFIX y x``,
   Induct >> RW_TAC list_ss [IS_PREFIX]
   ++ Cases_on `y` >> RW_TAC list_ss [alg_order_def]
   ++ Cases_on `z` >> RW_TAC list_ss [IS_PREFIX_NIL]
   ++ (RW_TAC list_ss [alg_order_def, IS_PREFIX]
         ++ PROVE_TAC []));

val ALG_ORDER_PREFIX_TRANS = store_thm
  ("ALG_ORDER_PREFIX_TRANS",
   ``!x y z. alg_order x y /\ IS_PREFIX y z
             ==> alg_order x z \/ IS_PREFIX x z``,
   Induct >> (Cases_on `z` ++ RW_TAC list_ss [alg_order_def])
   ++ Cases_on `y` >> RW_TAC list_ss [ALG_ORDER_NIL]
   ++ Cases_on `z` >> RW_TAC list_ss [IS_PREFIX]
   ++ (RW_TAC list_ss [alg_order_def, IS_PREFIX] ++ PROVE_TAC []));

val ALG_ORDER_SNOC = store_thm
  ("ALG_ORDER_SNOC",
   ``!x l. ~alg_order (SNOC x l) l``,
   Induct_on `l` >> RW_TAC std_ss [alg_order_def, SNOC]
   ++ RW_TAC std_ss [alg_order_def, SNOC]);

val ALG_SORTED_MIN = store_thm
  ("ALG_SORTED_MIN",
   ``!h t. alg_sorted (h::t) ==> (!x. MEM x t ==> alg_order h x)``,
   Induct_on `t` >> RW_TAC list_ss [MEM]
   ++ RW_TAC list_ss [alg_sorted_def, MEM] >> PROVE_TAC []
   ++ KNOW_TAC `alg_order h x` >> PROVE_TAC []
   ++ PROVE_TAC [ALG_ORDER_TRANS]);

val ALG_SORTED_DEF_ALT = store_thm
  ("ALG_SORTED_DEF_ALT",
   ``!h t. alg_sorted (h::t)
           = (!x. MEM x t ==> alg_order h x) /\ alg_sorted t``,
   REPEAT STRIP_TAC
   ++ EQ_TAC
     >> (Cases_on `t` ++ PROVE_TAC [ALG_SORTED_MIN, alg_sorted_def])
   ++ Cases_on `t` >> RW_TAC list_ss [alg_sorted_def]
   ++ RW_TAC list_ss [alg_sorted_def]
   ++ PROVE_TAC [MEM]);

val ALG_SORTED_TL = store_thm
  ("ALG_SORTED_TL",
   ``!h t. alg_sorted (h::t) ==> alg_sorted t``,
   PROVE_TAC [ALG_SORTED_DEF_ALT]);

val ALG_SORTED_MONO = store_thm
  ("ALG_SORTED_MONO",
   ``!x y z. alg_sorted (x::y::z) ==> alg_sorted (x::z)``,
   RW_TAC list_ss [ALG_SORTED_DEF_ALT, MEM]);

val ALG_SORTED_TLS = store_thm
  ("ALG_SORTED_TLS",
   ``!l b. alg_sorted (MAP (CONS b) l) = alg_sorted l``,
   Induct >> RW_TAC list_ss [MAP]
   ++ Cases_on `l` >> RW_TAC list_ss [MAP, alg_sorted_def]
   ++ RW_TAC list_ss [alg_sorted_def, alg_order_def]
   ++ PROVE_TAC [MAP]);

val ALG_SORTED_STEP = store_thm
  ("ALG_SORTED_STEP",
   ``!l1 l2. alg_sorted (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
             = alg_sorted l1 /\ alg_sorted l2``,
   NTAC 2 STRIP_TAC
   ++ Induct_on `l1` >> RW_TAC list_ss [MAP, ALG_SORTED_TLS, alg_sorted_def]
   ++ STRIP_TAC
   ++ POP_ASSUM MP_TAC
   ++ Cases_on `l1` <<
   [Cases_on `l2` >> RW_TAC list_ss [MAP, alg_sorted_def]
    ++ RW_TAC list_ss [MAP, alg_sorted_def, alg_order_def],
    RW_TAC list_ss [alg_sorted_def, alg_order_def]
    ++ PROVE_TAC []]);

val ALG_SORTED_APPEND = store_thm
  ("ALG_SORTED_APPEND",
   ``!h h' t t'. alg_sorted (APPEND (h::t) (h'::t'))
                 = alg_sorted (h::t) /\ alg_sorted (h'::t')
                   /\ alg_order (LAST (h::t)) h'``,
   Induct_on `t`
     >> (RW_TAC list_ss [alg_sorted_def, LAST_CONS]
	 ++ PROVE_TAC [])
   ++ RW_TAC list_ss [alg_sorted_def]
   ++ RW_TAC std_ss [(GSYM o CONJUNCT2) APPEND, LAST_CONS]
   ++ PROVE_TAC []);

val ALG_SORTED_FILTER = store_thm
  ("ALG_SORTED_FILTER",
   ``!P b. alg_sorted b ==> alg_sorted (FILTER P b)``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [FILTER]
   ++ RW_TAC list_ss [ALG_SORTED_DEF_ALT, FILTER]
   ++ PROVE_TAC [MEM_FILTER]);

val ALG_PREFIXFREE_TL = store_thm
  ("ALG_PREFIXFREE_TL",
   ``!h t. alg_prefixfree (h::t) ==> alg_prefixfree t``,
   STRIP_TAC
   ++ (Cases ++ RW_TAC list_ss [alg_prefixfree_def]));

val ALG_PREFIXFREE_MONO = store_thm
  ("ALG_PREFIXFREE_MONO",
   ``!x y z. alg_sorted (x::y::z) /\ alg_prefixfree (x::y::z)
             ==> alg_prefixfree (x::z)``,
   Cases_on `z` >> RW_TAC list_ss [alg_prefixfree_def]
   ++ RW_TAC list_ss [alg_prefixfree_def, alg_sorted_def]
   ++ PROVE_TAC [ALG_ORDER_PREFIX_MONO]);

val ALG_PREFIXFREE_ELT = store_thm
  ("ALG_PREFIXFREE_ELT",
   ``!h t. alg_sorted (h::t) /\ alg_prefixfree (h::t)
         ==> (!x. MEM x t ==> ~IS_PREFIX x h /\ ~IS_PREFIX h x)``,
   Induct_on `t` >> RW_TAC list_ss [MEM]
   ++ ONCE_REWRITE_TAC [MEM]
   ++ NTAC 5 STRIP_TAC <<
   [CONJ_TAC >> PROVE_TAC [alg_prefixfree_def]
    ++ KNOW_TAC `alg_order h' h` >> PROVE_TAC [alg_sorted_def]
    ++ PROVE_TAC [ALG_ORDER_PREFIX_ANTI, IS_PREFIX_REFL, alg_prefixfree_def],
    SUFF_TAC `alg_sorted (h'::t) /\ alg_prefixfree (h'::t)`
      >> PROVE_TAC []
    ++ PROVE_TAC [ALG_SORTED_MONO, ALG_PREFIXFREE_MONO]]);

val ALG_PREFIXFREE_TLS = store_thm
  ("ALG_PREFIXFREE_TLS",
   ``!l b. alg_prefixfree (MAP (CONS b) l) = alg_prefixfree l``,
   Induct >> RW_TAC list_ss [MAP]
   ++ Cases_on `l` >> RW_TAC list_ss [MAP, alg_prefixfree_def]
   ++ RW_TAC list_ss [alg_prefixfree_def, IS_PREFIX]
   ++ PROVE_TAC [MAP]);

val ALG_PREFIXFREE_STEP = store_thm
  ("ALG_PREFIXFREE_STEP",
   ``!l1 l2. alg_prefixfree (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
             = alg_prefixfree l1 /\ alg_prefixfree l2``,
   NTAC 2 STRIP_TAC
   ++ Induct_on `l1`
   >> RW_TAC list_ss [MAP, ALG_PREFIXFREE_TLS, alg_prefixfree_def]
   ++ STRIP_TAC
   ++ POP_ASSUM MP_TAC
   ++ Cases_on `l1` <<
   [Cases_on `l2` >> RW_TAC list_ss [MAP, alg_prefixfree_def]
    ++ RW_TAC list_ss [MAP, alg_prefixfree_def, IS_PREFIX],
    RW_TAC list_ss [alg_prefixfree_def, IS_PREFIX]
    ++ PROVE_TAC []]);

val ALG_PREFIXFREE_APPEND = store_thm
  ("ALG_PREFIXFREE_APPEND",
   ``!h h' t t'. alg_prefixfree (APPEND (h::t) (h'::t'))
                 = alg_prefixfree (h::t) /\ alg_prefixfree (h'::t')
                   /\ ~IS_PREFIX h' (LAST (h::t))``,
   Induct_on `t`
     >> (RW_TAC list_ss [alg_prefixfree_def, LAST_CONS]
	 ++ PROVE_TAC [])
   ++ RW_TAC list_ss [alg_prefixfree_def]
   ++ RW_TAC std_ss [(GSYM o CONJUNCT2) APPEND, LAST_CONS]
   ++ PROVE_TAC []);

val ALG_PREFIXFREE_FILTER = store_thm
  ("ALG_PREFIXFREE_FILTER",
   ``!P b. alg_sorted b /\ alg_prefixfree b ==> alg_prefixfree (FILTER P b)``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [FILTER]
   ++ NTAC 2 STRIP_TAC
   ++ KNOW_TAC `alg_prefixfree (FILTER P b)`
     >> PROVE_TAC [ALG_SORTED_TL, ALG_PREFIXFREE_TL]
   ++ RW_TAC list_ss [FILTER]
   ++ Cases_on `FILTER P b` >> RW_TAC list_ss [alg_prefixfree_def]
   ++ RW_TAC list_ss [alg_prefixfree_def]
   ++ KNOW_TAC `MEM (h':bool list) b` >> PROVE_TAC [MEM_FILTER, MEM]
   ++ PROVE_TAC [ALG_PREFIXFREE_ELT]);

val ALG_TWINFREE_TL = store_thm
  ("ALG_TWINFREE_TL",
   ``!h t. alg_twinfree (h::t) ==> alg_twinfree t``,
   Cases_on `t` ++ RW_TAC list_ss [alg_twinfree_def]);

val ALG_TWINFREE_TLS = store_thm
  ("ALG_TWINFREE_TLS",
   ``!l b. alg_twinfree (MAP (CONS b) l) = alg_twinfree l``,
   NTAC 2 STRIP_TAC
   ++ Induct_on `l` >> RW_TAC list_ss [MAP]
   ++ STRIP_TAC
   ++ Cases_on `l` >> RW_TAC std_ss [MAP, alg_twinfree_def]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [MAP, alg_twinfree_def, alg_twin_def]
   ++ KILL_ALL_TAC
   ++ SUFF_TAC `(?l. (b::h = SNOC T l) /\ (b::h' = SNOC F l))
                = (?l. (h = SNOC T l) /\ (h' = SNOC F l))`
   >> PROVE_TAC []
   ++ EQ_TAC <<
   [RW_TAC std_ss []
    ++ NTAC 2 (POP_ASSUM MP_TAC)
    ++ Cases_on `l` >> RW_TAC std_ss [SNOC]
    ++ RW_TAC std_ss [SNOC]
    ++ PROVE_TAC [],
    RW_TAC std_ss []
    ++ Q.EXISTS_TAC `b::l`
    ++ Cases_on `l`
    ++ RW_TAC std_ss [SNOC]]);

val ALG_TWINFREE_STEP1 = store_thm
  ("ALG_TWINFREE_STEP1",
   ``!l1 l2. alg_twinfree (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
             ==> alg_twinfree l1 /\ alg_twinfree l2``,
   NTAC 2 STRIP_TAC
   ++ Induct_on `l1`
   >> RW_TAC list_ss [MAP, ALG_TWINFREE_TLS, alg_twinfree_def]
   ++ STRIP_TAC
   ++ POP_ASSUM MP_TAC
   ++ Cases_on `l1` <<
   [Cases_on `l2` >> RW_TAC list_ss [MAP, alg_twinfree_def]
    ++ RW_TAC list_ss [MEM, MAP, alg_twinfree_def],
    RW_TAC list_ss [alg_twinfree_def, ALG_TWIN_REDUCE, MEM]]);

val ALG_TWINFREE_STEP2 = store_thm
  ("ALG_TWINFREE_STEP2",
   ``!l1 l2. (~(MEM [] l1) \/ ~(MEM [] l2))
             /\ alg_twinfree l1 /\ alg_twinfree l2
             ==> alg_twinfree (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))``,
   NTAC 2 STRIP_TAC
   ++ Induct_on `l1`
   >> RW_TAC list_ss [MAP, ALG_TWINFREE_TLS, alg_twinfree_def]
   ++ STRIP_TAC
   ++ POP_ASSUM MP_TAC
   ++ Cases_on `l1` <<
   [Cases_on `l2` >> RW_TAC list_ss [MAP, alg_twinfree_def]
    ++ RW_TAC list_ss [MEM, MAP, alg_twinfree_def] <<
    [Cases_on `h` >> RW_TAC std_ss []
     ++ RW_TAC std_ss [ALG_TWIN_CONS],
     Cases_on `h'` >> RW_TAC std_ss []
     ++ RW_TAC std_ss [ALG_TWIN_CONS]],
    RW_TAC list_ss [alg_twinfree_def, ALG_TWIN_REDUCE, MEM]
    ++ RES_TAC]);

val ALG_TWINFREE_STEP = store_thm
  ("ALG_TWINFREE_STEP",
   ``!l1 l2. ~(MEM [] l1) \/ ~(MEM [] l2)
             ==> (alg_twinfree (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
                  = alg_twinfree l1 /\ alg_twinfree l2)``,
   PROVE_TAC [ALG_TWINFREE_STEP1, ALG_TWINFREE_STEP2]);

val ALG_LONGEST_HD = store_thm
  ("ALG_LONGEST_HD",
   ``!h t. LENGTH h <= alg_longest (h::t)``,
   Induct_on `t` >> RW_TAC arith_ss [alg_longest_def, FOLDR]
   ++ RW_TAC arith_ss [alg_longest_def, FOLDR]);

val ALG_LONGEST_TL = store_thm
  ("ALG_LONGEST_TL",
   ``!h t. alg_longest t <= alg_longest (h::t)``,
   Induct_on `t` >> RW_TAC arith_ss [alg_longest_def, FOLDR]
   ++ RW_TAC arith_ss [alg_longest_def, FOLDR]);

val ALG_LONGEST_TLS = store_thm
  ("ALG_LONGEST_TLS",
   ``!h t b. alg_longest (MAP (CONS b) (h::t)) = SUC (alg_longest (h::t))``,
   Induct_on `t`
     >> RW_TAC arith_ss [alg_longest_def, FOLDR_MAP, FOLDR, LENGTH]
   ++ RW_TAC arith_ss [alg_longest_def]
   ++ ONCE_REWRITE_TAC [MAP]
   ++ ONCE_REWRITE_TAC [FOLDR]
   ++ REWRITE_TAC [GSYM alg_longest_def]
   ++ RW_TAC arith_ss [LENGTH]);

val ALG_LONGEST_APPEND = store_thm
  ("ALG_LONGEST_APPEND",
   ``!l1 l2. alg_longest l1 <= alg_longest (APPEND l1 l2)
             /\ alg_longest l2 <= alg_longest (APPEND l1 l2)``,
   NTAC 2 STRIP_TAC
   ++ Induct_on `l1` >> RW_TAC arith_ss [APPEND, alg_longest_def, FOLDR]
   ++ REWRITE_TAC [APPEND, alg_longest_def, FOLDR]
   ++ REWRITE_TAC [GSYM alg_longest_def]
   ++ RW_TAC arith_ss []);

val ALG_CANON_PREFS_HD = store_thm
  ("ALG_CANON_PREFS_HD",
   ``!l b. HD (alg_canon_prefs l b) = l``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [alg_canon_prefs_def]
   ++ RW_TAC list_ss [alg_canon_prefs_def]);

val ALG_CANON_PREFS_DELETES = store_thm
  ("ALG_CANON_PREFS_DELETES",
   ``!l b x. MEM x (alg_canon_prefs l b) ==> MEM x (l::b)``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [alg_canon_prefs_def]
   ++ RW_TAC list_ss [alg_canon_prefs_def]
   ++ RES_TAC
   ++ POP_ASSUM MP_TAC
   ++ KILL_ALL_TAC
   ++ RW_TAC list_ss [MEM]
   ++ PROVE_TAC []);

val ALG_CANON_PREFS_SORTED = store_thm
  ("ALG_CANON_PREFS_SORTED",
   ``!l b. alg_sorted (l::b) ==> alg_sorted (alg_canon_prefs l b)``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [alg_canon_prefs_def]
   ++ RW_TAC list_ss [alg_canon_prefs_def]
   ++ PROVE_TAC [ALG_SORTED_MONO]);

val ALG_CANON_PREFS_PREFIXFREE = store_thm
  ("ALG_CANON_PREFS_PREFIXFREE",
   ``!l b. alg_sorted b /\ alg_prefixfree b
           ==> alg_prefixfree (alg_canon_prefs l b)``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [alg_canon_prefs_def, alg_prefixfree_def]
   ++ RW_TAC list_ss [alg_canon_prefs_def, alg_prefixfree_def]
   ++ PROVE_TAC [ALG_SORTED_TL, ALG_PREFIXFREE_TL]);

val ALG_CANON_PREFS_CONSTANT = store_thm
  ("ALG_CANON_PREFS_CONSTANT",
   ``!l b. alg_prefixfree (l::b)
           ==> (alg_canon_prefs l b = l::b)``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [alg_prefixfree_def, alg_canon_prefs_def]
   ++ RW_TAC list_ss [alg_prefixfree_def, alg_canon_prefs_def]);

val ALG_CANON_FIND_HD = store_thm
  ("ALG_CANON_FIND_HD",
   ``!l h t. (HD (alg_canon_find l (h::t)) = l)
             \/ (HD (alg_canon_find l (h::t)) = h)``,
   Induct_on `t` >> RW_TAC list_ss [alg_canon_find_def, ALG_CANON_PREFS_HD]
   ++ RW_TAC list_ss [alg_canon_find_def, ALG_CANON_PREFS_HD]);

val ALG_CANON_FIND_DELETES = store_thm
  ("ALG_CANON_FIND_DELETES",
   ``!l b x. MEM x (alg_canon_find l b) ==> MEM x (l::b)``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [alg_canon_find_def]
   ++ RW_TAC list_ss [alg_canon_find_def, MEM] >>
   (PROVE_TAC [MEM]) >>
   (PROVE_TAC [MEM, ALG_CANON_PREFS_DELETES]));

val ALG_CANON_FIND_SORTED = store_thm
  ("ALG_CANON_FIND_SORTED",
   ``!l b. alg_sorted b ==> alg_sorted (alg_canon_find l b)``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [alg_canon_find_def, alg_sorted_def]
   ++ RW_TAC list_ss [alg_canon_find_def] >>
   (POP_ASSUM MP_TAC
    ++ RW_TAC list_ss [ALG_SORTED_DEF_ALT]
    ++ PROVE_TAC [ALG_CANON_FIND_DELETES, MEM]) >>
   (SUFF_TAC `alg_sorted (l::h::b)` >> PROVE_TAC [ALG_CANON_PREFS_SORTED]
    ++ REWRITE_TAC [alg_sorted_def]
    ++ PROVE_TAC [ALG_ORDER_TOTAL]));

val ALG_CANON_FIND_PREFIXFREE = store_thm
  ("ALG_CANON_FIND_PREFIXFREE",
   ``!l b. alg_sorted b /\ alg_prefixfree b
           ==> alg_prefixfree (alg_canon_find l b)``,
   STRIP_TAC
   ++ Induct >> RW_TAC list_ss [alg_canon_find_def, alg_prefixfree_def]
   ++ RW_TAC list_ss [alg_canon_find_def] <<
   [Cases_on `b` >> RW_TAC list_ss [alg_prefixfree_def, alg_canon_find_def]
    ++ Cases_on `alg_canon_find l (h'::t)`
      >> RW_TAC list_ss [alg_prefixfree_def, alg_canon_find_def]
    ++ REVERSE (RW_TAC list_ss [alg_prefixfree_def])
      >> PROVE_TAC [ALG_SORTED_TL, ALG_PREFIXFREE_TL]
    ++ SUFF_TAC `(h'' = h') \/ (h'' = (l:bool list))`
      >> PROVE_TAC [alg_prefixfree_def]
    ++ POP_ASSUM MP_TAC
    ++ KILL_ALL_TAC
    ++ PROVE_TAC [ALG_CANON_FIND_HD, HD],
    PROVE_TAC [ALG_CANON_PREFS_PREFIXFREE]]);

val ALG_CANON_FIND_CONSTANT = store_thm
  ("ALG_CANON_FIND_CONSTANT",
   ``!l b. alg_sorted (l::b) /\ alg_prefixfree (l::b)
           ==> (alg_canon_find l b = l::b)``,
   STRIP_TAC
   ++ Cases >> RW_TAC list_ss [alg_canon_find_def]
   ++ STRIP_TAC
   ++ KNOW_TAC `~((l:bool list) = h)`
     >> PROVE_TAC [alg_prefixfree_def, IS_PREFIX_REFL]
   ++ (RW_TAC list_ss [alg_canon_find_def, ALG_CANON_PREFS_CONSTANT]
         ++ PROVE_TAC [alg_sorted_def, ALG_ORDER_ANTISYM]));

val ALG_CANON1_SORTED = store_thm
  ("ALG_CANON1_SORTED",
   ``!l. alg_sorted (alg_canon1 l)``,
   REWRITE_TAC [alg_canon1_def]
   ++ Induct >> RW_TAC list_ss [FOLDR, alg_sorted_def]
   ++ RW_TAC list_ss [ALG_CANON_FIND_SORTED, FOLDR]);

val ALG_CANON1_PREFIXFREE = store_thm
  ("ALG_CANON1_PREFIXFREE",
   ``!l. alg_prefixfree (alg_canon1 l)``,
   Induct >> RW_TAC list_ss [alg_prefixfree_def, alg_canon1_def, FOLDR]
   ++ RW_TAC list_ss [alg_canon1_def, FOLDR]
   ++ RW_TAC list_ss [GSYM alg_canon1_def]
   ++ KNOW_TAC `alg_sorted (alg_canon1 l)` >> PROVE_TAC [ALG_CANON1_SORTED]
   ++ PROVE_TAC [ALG_CANON_FIND_PREFIXFREE]);

val ALG_CANON1_CONSTANT = store_thm
  ("ALG_CANON1_CONSTANT",
   ``!l. alg_sorted l /\ alg_prefixfree l ==> (alg_canon1 l = l)``,
   RW_TAC list_ss [alg_canon1_def]
   ++ Induct_on `l` >> RW_TAC list_ss [FOLDR]
   ++ RW_TAC list_ss [FOLDR]
   ++ PROVE_TAC [ALG_CANON_FIND_CONSTANT, ALG_SORTED_TL, ALG_PREFIXFREE_TL]);

val ALG_CANON_MERGE_SORTED_PREFIXFREE_TWINFREE = store_thm
  ("ALG_CANON_MERGE_SORTED_PREFIXFREE_TWINFREE",
   ``!l b. alg_sorted (l::b) /\ alg_prefixfree (l::b) /\ alg_twinfree b
           ==> alg_sorted (alg_canon_merge l b)
               /\ alg_prefixfree (alg_canon_merge l b)
               /\ alg_twinfree (alg_canon_merge l b)``,
   Induct_on `b` >> RW_TAC std_ss [alg_canon_merge_def, alg_twinfree_def]
   ++ NTAC 3 STRIP_TAC
   ++ KNOW_TAC `alg_twinfree b` >> PROVE_TAC [ALG_TWINFREE_TL]
   ++ RW_TAC std_ss [alg_canon_merge_def, alg_twinfree_def, alg_twin_def]
   ++ KNOW_TAC `alg_sorted (l'::b)`
   >> (KNOW_TAC `alg_sorted (SNOC T l'::b)`
       >> PROVE_TAC [ALG_SORTED_MONO]
       ++ Cases_on `b` >> RW_TAC std_ss [alg_sorted_def]
       ++ POP_ASSUM MP_TAC
       ++ RW_TAC std_ss [alg_sorted_def]
       ++ SUFF_TAC `alg_order l' (SNOC T l')`
       >> PROVE_TAC [ALG_ORDER_TRANS]
       ++ MATCH_MP_TAC ALG_ORDER_PREFIX
       ++ RW_TAC std_ss [IS_PREFIX_SNOC, IS_PREFIX_REFL])
   ++ KNOW_TAC `alg_prefixfree (l'::b)`
   >> (KNOW_TAC `alg_prefixfree (SNOC T l'::b)`
       >> PROVE_TAC [ALG_PREFIXFREE_MONO]
       ++ Cases_on `b` >> RW_TAC std_ss [alg_prefixfree_def]
       ++ POP_ASSUM MP_TAC
       ++ Q.PAT_ASSUM `alg_prefixfree X` MP_TAC
       ++ Q.PAT_ASSUM `alg_sorted (SNOC T X::Y)` MP_TAC
       ++ RW_TAC std_ss [alg_prefixfree_def, alg_sorted_def]
       ++ STRIP_TAC
       ++ MP_TAC (Q.SPECL [`h`, `l'`] ALG_TWINS_PREFIX)
       ++ RW_TAC std_ss []
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `alg_order (SNOC F l') h` MP_TAC
       ++ RW_TAC std_ss [ALG_ORDER_SNOC])
   ++ RW_TAC std_ss [BUTLAST]);

val ALG_CANON_MERGE_PREFIXFREE_PRESERVE = store_thm
  ("ALG_CANON_MERGE_PREFIXFREE_PRESERVE",
   ``!l b h. (!x. MEM x (l::b) ==> ~IS_PREFIX h x /\ ~IS_PREFIX x h)
           ==> (!x. MEM x (alg_canon_merge l b)
                    ==> ~IS_PREFIX h x /\ ~IS_PREFIX x h)``,
   Induct_on `b` >> RW_TAC std_ss [MEM, alg_canon_merge_def, IS_PREFIX]
   ++ REWRITE_TAC [alg_canon_merge_def]
   ++ NTAC 5 STRIP_TAC
   ++ REVERSE (Cases_on `alg_twin l h`) >> ASM_REWRITE_TAC []
   ++ ASM_REWRITE_TAC []
   ++ POP_ASSUM MP_TAC
   ++ REWRITE_TAC [alg_twin_def]
   ++ NTAC 2 STRIP_TAC
   ++ SUFF_TAC `!x. MEM x (BUTLAST h::b)
                ==> ~IS_PREFIX h' x /\ ~IS_PREFIX x h'`
     >> PROVE_TAC []
   ++ REWRITE_TAC [MEM]
   ++ REVERSE (NTAC 2 STRIP_TAC) >> PROVE_TAC [MEM]
   ++ ASM_REWRITE_TAC [BUTLAST]
   ++ REVERSE (SUFF_TAC `~IS_PREFIX h' l /\ ~IS_PREFIX l h'
                            /\ ~IS_PREFIX h' h /\ ~IS_PREFIX h h'`)
   >> PROVE_TAC [MEM]
   ++ ASM_REWRITE_TAC []
   ++ KILL_ALL_TAC
   ++ RW_TAC std_ss [IS_PREFIX_SNOC]
   ++ PROVE_TAC [ALG_TWINS_PREFIX]);

val ALG_CANON_MERGE_SHORTENS = store_thm
  ("ALG_CANON_MERGE_SHORTENS",
   ``!l b x. MEM x (alg_canon_merge l b)
             ==> (?y. MEM y (l::b) /\ IS_PREFIX y x)``,
   Induct_on `b` >> RW_TAC std_ss [alg_canon_merge_def, MEM, IS_PREFIX_REFL]
   ++ REVERSE (RW_TAC std_ss [alg_canon_merge_def, alg_twin_def])
   >> PROVE_TAC [IS_PREFIX_REFL]
   ++ Q.PAT_ASSUM `!l. P l` (MP_TAC o Q.SPECL [`l'`, `x`])
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [BUTLAST, MEM] <<
   [Q.EXISTS_TAC `SNOC F l'`
    ++ RW_TAC std_ss [IS_PREFIX_SNOC],
    PROVE_TAC []]);

val ALG_CANON_MERGE_CONSTANT = store_thm
  ("ALG_CANON_MERGE_CONSTANT",
   ``!l b. alg_twinfree (l::b) ==> (alg_canon_merge l b = l::b)``,
   STRIP_TAC
   ++ Cases >> RW_TAC list_ss [alg_canon_merge_def]
   ++ RW_TAC list_ss [alg_twinfree_def, alg_canon_merge_def, ALG_TWIN_NIL]);

val ALG_CANON2_PREFIXFREE_PRESERVE = store_thm
  ("ALG_CANON2_PREFIXFREE_PRESERVE",
   ``!l h. (!x. MEM x l ==> ~IS_PREFIX h x /\ ~IS_PREFIX x h)
           ==> (!x. MEM x (alg_canon2 l)
                    ==> ~IS_PREFIX h x /\ ~IS_PREFIX x h)``,
   REWRITE_TAC [alg_canon2_def]
   ++ NTAC 2 STRIP_TAC
   ++ Induct_on `l` >> RW_TAC list_ss [FOLDR, MEM]
   ++ REWRITE_TAC [FOLDR, MEM]
   ++ NTAC 2 STRIP_TAC
   ++ SUFF_TAC `!x. MEM x (h'::FOLDR alg_canon_merge [] l)
                       ==> ~IS_PREFIX h x /\ ~IS_PREFIX x h`
     >> PROVE_TAC [ALG_CANON_MERGE_PREFIXFREE_PRESERVE]
   ++ REWRITE_TAC [MEM]
   ++ PROVE_TAC []);

val ALG_CANON2_SHORTENS = store_thm
  ("ALG_CANON2_SHORTENS",
   ``!l x. MEM x (alg_canon2 l) ==> ?y. MEM y l /\ IS_PREFIX y x``,
   REWRITE_TAC [alg_canon2_def]
   ++ Induct >> RW_TAC list_ss [MEM, FOLDR]
   ++ RW_TAC list_ss [FOLDR]
   ++ KNOW_TAC
           `?y. IS_PREFIX y x /\ MEM y (h::(FOLDR alg_canon_merge [] l))`
     >> PROVE_TAC [ALG_CANON_MERGE_SHORTENS]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC list_ss [MEM] >> PROVE_TAC []
   ++ KNOW_TAC `?y''. MEM y'' l /\ IS_PREFIX (y'':bool list) y`
     >> PROVE_TAC []
   ++ PROVE_TAC [IS_PREFIX_TRANS]);

val ALG_CANON2_SORTED_PREFIXFREE_TWINFREE = store_thm
  ("ALG_CANON2_SORTED_PREFIXFREE_TWINFREE",
   ``!l. alg_sorted l /\ alg_prefixfree l
         ==> alg_sorted (alg_canon2 l)
             /\ alg_prefixfree (alg_canon2 l)
             /\ alg_twinfree (alg_canon2 l)``,
   REWRITE_TAC [alg_canon2_def]
   ++ Induct >> RW_TAC list_ss [FOLDR, alg_sorted_def, alg_prefixfree_def,
				  alg_twinfree_def]
   ++ REWRITE_TAC [FOLDR]
   ++ NTAC 2 STRIP_TAC
   ++ KNOW_TAC `alg_sorted l /\ alg_prefixfree l`
     >> PROVE_TAC [ALG_SORTED_TL, ALG_PREFIXFREE_TL]
   ++ RES_TAC
   ++ SUFF_TAC `alg_sorted (h::FOLDR alg_canon_merge [] l)
                   /\ alg_prefixfree (h::FOLDR alg_canon_merge [] l)`
     >> PROVE_TAC [ALG_CANON_MERGE_SORTED_PREFIXFREE_TWINFREE]
   ++ POP_ASSUM (K ALL_TAC)
   ++ NTAC 2 (POP_ASSUM MP_TAC) ++ NTAC 2 (POP_ASSUM (K ALL_TAC))
   ++ NTAC 2 (POP_ASSUM MP_TAC) ++ POP_ASSUM (K ALL_TAC)
   ++ Cases_on `FOLDR alg_canon_merge [] l`
     >> RW_TAC list_ss [alg_sorted_def, alg_prefixfree_def]
   ++ NTAC 4 STRIP_TAC
   ++ KNOW_TAC `~IS_PREFIX h h' /\ ~IS_PREFIX h' (h:bool list)`
     >> (SUFF_TAC `!x. MEM x (alg_canon2 l)
                        ==> ~IS_PREFIX h x /\ ~IS_PREFIX (x:bool list) h`
           >> (REWRITE_TAC [alg_canon2_def] ++ PROVE_TAC [MEM])
	 ++ SUFF_TAC
             `!x. MEM x l ==> ~IS_PREFIX h x /\ ~IS_PREFIX (x:bool list) h`
           >> PROVE_TAC [ALG_CANON2_PREFIXFREE_PRESERVE]
         ++ PROVE_TAC [ALG_PREFIXFREE_ELT])
   ++ RW_TAC list_ss [alg_sorted_def, alg_prefixfree_def]
   ++ KNOW_TAC `?x. MEM x l /\ IS_PREFIX x (h':bool list)`
     >> (KNOW_TAC `MEM h' (alg_canon2 l)` >> PROVE_TAC [alg_canon2_def, MEM]
	 ++ PROVE_TAC [ALG_CANON2_SHORTENS])
   ++ KNOW_TAC `alg_order h x` >> PROVE_TAC [ALG_SORTED_DEF_ALT]
   ++ PROVE_TAC [ALG_ORDER_PREFIX_TRANS]);

val ALG_CANON2_CONSTANT = store_thm
  ("ALG_CANON2_CONSTANT",
   ``!l. alg_twinfree l ==> (alg_canon2 l = l)``,
   RW_TAC list_ss [alg_canon2_def]
   ++ Induct_on `l` >> RW_TAC list_ss [FOLDR]
   ++ RW_TAC list_ss [FOLDR]
   ++ PROVE_TAC [ALG_CANON_MERGE_CONSTANT, ALG_TWINFREE_TL]);

val ALG_CANON_SORTED_PREFIXFREE_TWINFREE = store_thm
  ("ALG_CANON_SORTED_PREFIXFREE_TWINFREE",
   ``!l. alg_sorted (alg_canon l)
         /\ alg_prefixfree (alg_canon l)
         /\ alg_twinfree (alg_canon l)``,
   RW_TAC list_ss [alg_canon_def,
		   ALG_CANON1_SORTED, ALG_CANON1_PREFIXFREE,
		   ALG_CANON2_SORTED_PREFIXFREE_TWINFREE]);

val ALG_CANON_CONSTANT = store_thm
  ("ALG_CANON_CONSTANT",
   ``!l. alg_sorted l /\ alg_prefixfree l /\ alg_twinfree l
         ==> (alg_canon l = l)``,
   RW_TAC std_ss [alg_canon_def, ALG_CANON1_CONSTANT, ALG_CANON2_CONSTANT]);

val ALG_CANON_IDEMPOT = store_thm
  ("ALG_CANON_IDEMPOT",
   ``!l. alg_canon (alg_canon l) = alg_canon l``,
   STRIP_TAC
   ++ MP_TAC (Q.SPEC `l` ALG_CANON_SORTED_PREFIXFREE_TWINFREE)
   ++ RW_TAC std_ss [ALG_CANON_CONSTANT]);

val ALGEBRA_CANON_DEF_ALT = store_thm
  ("ALGEBRA_CANON_DEF_ALT",
   ``!l. algebra_canon l
         = alg_sorted l /\ alg_prefixfree l /\ alg_twinfree l``,
   RW_TAC std_ss [algebra_canon_def]
   ++ EQ_TAC <<
   [PROVE_TAC [ALG_CANON_SORTED_PREFIXFREE_TWINFREE],
    PROVE_TAC [ALG_CANON_CONSTANT]]);

val ALGEBRA_CANON_BASIC = store_thm
  ("ALGEBRA_CANON_BASIC",
   ``algebra_canon [] /\ algebra_canon [[]] /\ !x. algebra_canon [x]``,
   RW_TAC list_ss [ALGEBRA_CANON_DEF_ALT, alg_sorted_def,
		   alg_prefixfree_def, alg_twinfree_def]);

val ALG_CANON_BASIC = store_thm
  ("ALG_CANON_BASIC",
   ``(alg_canon [] = []) /\ (alg_canon [[]] = [[]])
     /\ (!x. alg_canon [x] = [x])``,
   PROVE_TAC [algebra_canon_def, ALGEBRA_CANON_BASIC]);

val ALGEBRA_CANON_TL = store_thm
  ("ALGEBRA_CANON_TL",
   ``!h t. algebra_canon (h::t) ==> algebra_canon t``,
   RW_TAC std_ss [ALGEBRA_CANON_DEF_ALT] <<
   [PROVE_TAC [ALG_SORTED_TL],
    PROVE_TAC [ALG_PREFIXFREE_TL],
    PROVE_TAC [ALG_TWINFREE_TL]]);

val ALGEBRA_CANON_NIL_MEM = store_thm
  ("ALGEBRA_CANON_NIL_MEM",
   ``!l. algebra_canon l /\ MEM [] l = (l = [[]])``,
   RW_TAC std_ss []
   ++ REVERSE EQ_TAC >> RW_TAC std_ss [ALGEBRA_CANON_BASIC, MEM]
   ++ Induct_on `l` >> RW_TAC std_ss [MEM]
   ++ NTAC 2 STRIP_TAC
   ++ KNOW_TAC `algebra_canon l` >> PROVE_TAC [ALGEBRA_CANON_TL]
   ++ Q.PAT_ASSUM `algebra_canon (h::l)` MP_TAC
   ++ Q.PAT_ASSUM `X ==> Y` MP_TAC
   ++ Q.PAT_ASSUM `MEM X Y` MP_TAC
   ++ Cases_on `l` >> RW_TAC std_ss [MEM]
   ++ RW_TAC std_ss [MEM, ALGEBRA_CANON_DEF_ALT, alg_sorted_def,
                     alg_prefixfree_def, ALG_ORDER_NIL, IS_PREFIX_NIL] <<
   [RW_TAC std_ss [IS_PREFIX_NIL],
    RW_TAC std_ss [IS_PREFIX_NIL, ALG_ORDER_NIL]
    ++ PROVE_TAC [],
    RES_TAC
    ++ RW_TAC std_ss []
    ++ PROVE_TAC [MEM]]);

val ALGEBRA_CANON_TLS = store_thm
  ("ALGEBRA_CANON_TLS",
   ``!l b. algebra_canon (MAP (CONS b) l) = algebra_canon l``,
   RW_TAC list_ss [ALGEBRA_CANON_DEF_ALT, ALG_SORTED_TLS, ALG_PREFIXFREE_TLS]
   ++ (EQ_TAC ++ PROVE_TAC [ALG_TWINFREE_TLS]));

val ALGEBRA_CANON_STEP1 = store_thm
  ("ALGEBRA_CANON_STEP1",
   ``!l1 l2. algebra_canon (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
             ==> algebra_canon l1 /\ algebra_canon l2``,
   RW_TAC std_ss [ALGEBRA_CANON_DEF_ALT, ALG_SORTED_STEP, ALG_PREFIXFREE_STEP]
   ++ PROVE_TAC [ALG_TWINFREE_STEP1]);

val ALGEBRA_CANON_STEP2 = store_thm
  ("ALGEBRA_CANON_STEP2",
   ``!l1 l2. (~(l1 = [[]]) \/ ~(l2 = [[]]))
             /\ algebra_canon l1 /\ algebra_canon l2
             ==> algebra_canon (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))``,
   NTAC 2 STRIP_TAC
   ++ DISCH_TAC
   ++ REVERSE (SUFF_TAC `~(MEM [] l1) \/ ~(MEM [] l2)`)
   >> PROVE_TAC [ALGEBRA_CANON_NIL_MEM]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC std_ss [ALGEBRA_CANON_DEF_ALT, ALG_SORTED_STEP,
		     ALG_PREFIXFREE_STEP]
   ++ PROVE_TAC [ALG_TWINFREE_STEP2]);

val ALGEBRA_CANON_STEP = store_thm
  ("ALGEBRA_CANON_STEP",
   ``!l1 l2. ~(l1 = [[]]) \/ ~(l2 = [[]])
             ==> (algebra_canon (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
		  = algebra_canon l1 /\ algebra_canon l2)``,
   PROVE_TAC [ALGEBRA_CANON_STEP1, ALGEBRA_CANON_STEP2]);

val ALGEBRA_CANON_CASES_THM = store_thm
  ("ALGEBRA_CANON_CASES_THM",
   ``!l. algebra_canon l ==> (l = []) \/ (l = [[]])
            \/ ?l1 l2. algebra_canon l1 /\ algebra_canon l2
                       /\ (l = APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))``,
   Induct >> PROVE_TAC []
   ++ Cases
   >> (MP_TAC (SPEC ``([]:bool list)::l`` ALGEBRA_CANON_NIL_MEM)
       ++ RW_TAC list_ss [MEM])
   ++ STRIP_TAC
   ++ KNOW_TAC `algebra_canon l` >> PROVE_TAC [ALGEBRA_CANON_TL]
   ++ RES_TAC <<
   [RW_TAC std_ss []
    ++ Cases_on `h'` <<
    [Q.EXISTS_TAC `[t]`
     ++ Q.EXISTS_TAC `[]`
     ++ RW_TAC list_ss [ALGEBRA_CANON_BASIC],
     Q.EXISTS_TAC `[]`
     ++ Q.EXISTS_TAC `[t]`
     ++ RW_TAC list_ss [ALGEBRA_CANON_BASIC]],
    SUFF_TAC `F` >> PROVE_TAC []
    ++ Q.PAT_ASSUM `algebra_canon (X::Y)` MP_TAC
    ++ MP_TAC (Q.SPEC `(h'::t)::l` ALGEBRA_CANON_NIL_MEM)
    ++ RW_TAC std_ss [MEM],
    DISJ2_TAC
    ++ DISJ2_TAC
    ++ Cases_on `h'` <<
    [Q.EXISTS_TAC `t::l1`
     ++ Q.EXISTS_TAC `l2`
     ++ RW_TAC list_ss []
     ++ Q.PAT_ASSUM `algebra_canon (X::APPEND Y Z)` MP_TAC
     ++ KILL_ALL_TAC
     ++ MP_TAC (Q.SPECL [`t::l1`, `l2`] ALGEBRA_CANON_STEP1)
     ++ RW_TAC list_ss [MAP],
     Q.EXISTS_TAC `l1`
     ++ Q.EXISTS_TAC `t::l2`
     ++ Cases_on `l1` <<
     [RW_TAC list_ss []
      ++ Q.PAT_ASSUM `algebra_canon (X::APPEND Y Z)` MP_TAC
      ++ KILL_ALL_TAC
      ++ MP_TAC (Q.SPECL [`[]`, `t::l2`] ALGEBRA_CANON_STEP1)
      ++ RW_TAC list_ss [MAP],
      SUFF_TAC `~alg_sorted ((F::t)::l)` >> PROVE_TAC [ALGEBRA_CANON_DEF_ALT]
      ++ RW_TAC list_ss [MAP, alg_sorted_def, alg_order_def]]]]);

val ALGEBRA_CANON_CASES = store_thm
  ("ALGEBRA_CANON_CASES",
   ``!P. P [] /\ P [[]]
         /\ (!l1 l2. algebra_canon l1 /\ algebra_canon l2
	       /\ algebra_canon (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
               ==> P (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2)))
         ==> (!l. algebra_canon l ==> P l)``,
   RW_TAC list_ss []
   ++ MP_TAC (SPEC ``l:bool list list`` ALGEBRA_CANON_CASES_THM)
   ++ (RW_TAC list_ss [] ++ PROVE_TAC []));

val ALGEBRA_CANON_INDUCTION = store_thm
  ("ALGEBRA_CANON_INDUCTION",
   ``!P. P [] /\ P [[]]
         /\ (!l1 l2. algebra_canon l1 /\ algebra_canon l2 /\ P l1 /\ P l2
	       /\ algebra_canon (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
	       ==> P (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2)))
         ==> (!l. algebra_canon l ==> P l)``,
   RW_TAC list_ss []
   ++ completeInduct_on `alg_longest l`
   ++ RW_TAC list_ss []
   ++ REVERSE (SUFF_TAC `((l = []) \/ (l = [[]])) \/ ?l1 l2.
            algebra_canon l1 /\ algebra_canon l2 /\
            (l = APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))`)
     >> (POP_ASSUM (MP_TAC
		    o MP (SPEC ``l:bool list list`` ALGEBRA_CANON_CASES_THM))
	 ++ PROVE_TAC [])
   ++ DISCH_THEN DISJ_CASES_TAC >> PROVE_TAC []
   ++ POP_ASSUM MP_TAC
   ++ STRIP_TAC
   ++ SUFF_TAC `P (l1:bool list list) /\ P l2` >> PROVE_TAC []
   ++ CONJ_TAC <<
   [Cases_on `l1` >> PROVE_TAC []
    ++ SUFF_TAC `alg_longest (h::t) < alg_longest l` >> PROVE_TAC []
    ++ POP_ASSUM MP_TAC
    ++ KILL_ALL_TAC
    ++ MP_TAC (SPECL [``MAP (CONS T) (h::t)``, ``MAP (CONS F) l2``]
		 ALG_LONGEST_APPEND)
    ++ RW_TAC arith_ss [ALG_LONGEST_TLS],
    Cases_on `l2` >> PROVE_TAC []
    ++ SUFF_TAC `alg_longest (h::t) < alg_longest l` >> PROVE_TAC []
    ++ POP_ASSUM MP_TAC
    ++ KILL_ALL_TAC
    ++ MP_TAC (SPECL [``MAP (CONS T) l1``, ``MAP (CONS F) (h::t)``]
		 ALG_LONGEST_APPEND)
    ++ RW_TAC arith_ss [ALG_LONGEST_TLS]]);

val MEM_NIL_STEP = store_thm
  ("MEM_NIL_STEP",
   ``!l1 l2. ~MEM [] (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))``,
   RW_TAC list_ss [APPEND_MEM, MEM_NIL_MAP_CONS]);

val ALG_SORTED_PREFIXFREE_MEM_NIL = store_thm
  ("ALG_SORTED_PREFIXFREE_MEM_NIL",
   ``!l. alg_sorted l /\ alg_prefixfree l /\ MEM [] l = (l = [[]])``,
   Induct >> RW_TAC list_ss [MEM]
   ++ STRIP_TAC
   ++ REVERSE EQ_TAC
     >> RW_TAC std_ss [alg_prefixfree_def, alg_sorted_def, MEM]
   ++ Cases_on `l` >> RW_TAC list_ss [MEM]
   ++ ONCE_REWRITE_TAC [MEM]
   ++ RW_TAC std_ss [alg_prefixfree_def, alg_sorted_def]
   ++ Cases_on `h` >> RW_TAC list_ss [MEM, alg_order_def, IS_PREFIX]
   ++ Cases_on `h'` >> RW_TAC list_ss [MEM, alg_order_def]
   ++ RW_TAC list_ss [] <<
   [RW_TAC list_ss [],
    RW_TAC list_ss [],
    RW_TAC list_ss []]);

val ALG_SORTED_PREFIXFREE_EQUALITY = store_thm
  ("ALG_SORTED_PREFIXFREE_EQUALITY",
   ``!l l'. (!x. MEM x l = MEM x l') /\ alg_sorted l /\ alg_sorted l'
            /\ alg_prefixfree l /\ alg_prefixfree l'
            ==> (l = l')``,
   Induct >> RW_TAC list_ss [MEM, MEM_NIL]
   ++ STRIP_TAC
   ++ Cases >> (RW_TAC std_ss [MEM, MEM_NIL] ++ PROVE_TAC [])
   ++ REPEAT STRIP_TAC
   ++ KNOW_TAC `h = h'` <<
   [SUFF_TAC `alg_order h h' /\ alg_order h' h` >> PROVE_TAC [ALG_ORDER_ANTISYM]
    ++ CONJ_TAC <<
    [KNOW_TAC `MEM h' (h::l)` >> PROVE_TAC [MEM]
     ++ POP_ASSUM MP_TAC
     ++ REWRITE_TAC [MEM]
     ++ RW_TAC std_ss [] >> PROVE_TAC [ALG_ORDER_REFL]
     ++ Q.PAT_ASSUM `alg_sorted (h::l)` MP_TAC
     ++ RW_TAC std_ss [ALG_SORTED_DEF_ALT],
     KNOW_TAC `MEM h (h'::t)` >> PROVE_TAC [MEM]
     ++ POP_ASSUM MP_TAC
     ++ REWRITE_TAC [MEM]
     ++ RW_TAC std_ss [] >> PROVE_TAC [ALG_ORDER_REFL]
     ++ Q.PAT_ASSUM `alg_sorted (h'::t)` MP_TAC
     ++ RW_TAC std_ss [ALG_SORTED_DEF_ALT]],
    RW_TAC std_ss []
    ++ Q.PAT_ASSUM `!l'. P l' ==> Q l'` MATCH_MP_TAC
    ++ REVERSE CONJ_TAC >> PROVE_TAC [ALG_SORTED_TL, ALG_PREFIXFREE_TL]
    ++ RW_TAC std_ss []
    ++ Q.PAT_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
    ++ REWRITE_TAC [MEM]
    ++ REVERSE (Cases_on `x = h`) >> RW_TAC std_ss []
    ++ RW_TAC std_ss []
    ++ ASSUME_TAC ALG_PREFIXFREE_ELT
    ++ RES_TAC
    ++ NTAC 2 (POP_ASSUM (MP_TAC o Q.SPEC `h`))
    ++ NTAC 3 (POP_ASSUM (K ALL_TAC))
    ++ RW_TAC std_ss [IS_PREFIX_REFL]]);

val _ = export_theory ();
