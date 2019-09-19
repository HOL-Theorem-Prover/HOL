open HolKernel Parse boolLib;
open bossLib pred_setTheory listTheory rich_listTheory pairTheory realLib
     hurdUtils extra_listTheory;

val _ = new_theory "prob_canon";
val _ = ParseExtras.temp_loose_equality()

(* ------------------------------------------------------------------------- *)
(* Definition of the canonicalisation of algebra elements.                   *)
(* ------------------------------------------------------------------------- *)

val prob_twin_def = Define
  `prob_twin x y = ?l. (x = SNOC T l) /\ (y = SNOC F l)`;

val prob_order_def = Define
  `(prob_order [] _ = T) /\
   (prob_order _ [] = F) /\
   (prob_order (h :: t) (h' :: t') =
    ((h = T) /\ (h' = F)) \/ ((h = h') /\ prob_order t t'))`;

val prob_sorted_def = Define `(prob_sorted (x :: y :: z)
      = prob_order x y /\ prob_sorted (y :: z))
  /\ (prob_sorted l = T)`;

val prob_prefixfree_def = Define `(prob_prefixfree ((x:bool list)::y::z)
      = ~IS_PREFIX y x /\ prob_prefixfree (y::z))
  /\ (prob_prefixfree l = T)`;

val prob_twinfree_def = Define `(prob_twinfree (x::y::z)
      = ~(prob_twin x y) /\ prob_twinfree (y::z))
  /\ (prob_twinfree l = T)`;

val prob_longest_def = Define `prob_longest
  = FOLDR (\h t. if t <= LENGTH (h:bool list) then LENGTH h else t) 0`

val prob_canon_prefs_def = Define `(prob_canon_prefs (l:bool list) [] = [l])
  /\ (prob_canon_prefs l (h::t) = if IS_PREFIX h l then prob_canon_prefs l t
                                 else l::h::t)`;

val prob_canon_find_def = Define `(prob_canon_find l [] = [l])
  /\ (prob_canon_find l (h::t) = if prob_order h l then
          if IS_PREFIX l h then (h::t) else h::(prob_canon_find l t)
        else prob_canon_prefs l (h::t))`;

val prob_canon1_def = Define `prob_canon1 = FOLDR prob_canon_find []`;

val prob_canon_merge_def = Define `(prob_canon_merge l [] = [l])
  /\ (prob_canon_merge l (h::t)
      = if prob_twin l h then prob_canon_merge (BUTLAST h) t else l::h::t)`;

val prob_canon2_def = Define `prob_canon2 = FOLDR prob_canon_merge []`;

val prob_canon_def = Define `prob_canon l = prob_canon2 (prob_canon1 l)`;

val prob_canonical_def = Define `prob_canonical l = (prob_canon l = l)`;

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1. Canonical form is the same as sorted, prefixfree and twinfree.         *)
(* 2. Induction principle on elements in canonical form.                     *)
(* ------------------------------------------------------------------------- *)

val PROB_TWIN_NIL = store_thm
  ("PROB_TWIN_NIL",
   ``!l. ~(prob_twin l []) /\ ~(prob_twin [] l)``,
   RW_TAC std_ss [prob_twin_def]
   >> Cases_on `l'`
   >> RW_TAC std_ss [SNOC]);

val PROB_TWIN_SING = store_thm
  ("PROB_TWIN_SING",
   ``!x l. (prob_twin [x] l = (x = T) /\ (l = [F]))
           /\ (prob_twin l [x] = (l = [T]) /\ (x = F))``,
   RW_TAC std_ss [prob_twin_def] >|
   [EQ_TAC >|
    [Cases_on `l` >- PROVE_TAC [NOT_NIL_SNOC]
     >> DISCH_THEN (Q.X_CHOOSE_THEN `l` STRIP_ASSUME_TAC)
     >> NTAC 2 (POP_ASSUM MP_TAC)
     >> Reverse (Cases_on `l`) >- RW_TAC std_ss [SNOC, NOT_NIL_SNOC]
     >> RW_TAC std_ss [SNOC],
     RW_TAC std_ss []
     >> Q.EXISTS_TAC `[]`
     >> RW_TAC std_ss [SNOC]],
    EQ_TAC >|
    [Cases_on `l` >- PROVE_TAC [NOT_NIL_SNOC]
     >> DISCH_THEN (Q.X_CHOOSE_THEN `l` STRIP_ASSUME_TAC)
     >> NTAC 2 (POP_ASSUM MP_TAC)
     >> Reverse (Cases_on `l`) >- RW_TAC std_ss [SNOC, NOT_NIL_SNOC]
     >> RW_TAC std_ss [SNOC],
     RW_TAC std_ss []
     >> Q.EXISTS_TAC `[]`
     >> RW_TAC std_ss [SNOC]]]);

val PROB_TWIN_CONS = store_thm
  ("PROB_TWIN_CONS",
   ``!x y z h t. (prob_twin (x::y::z) (h::t) = (x = h) /\ prob_twin (y::z) t)
              /\ (prob_twin (h::t) (x::y::z) = (x = h) /\ prob_twin t (y::z))``,
   RW_TAC std_ss [prob_twin_def] >|
   [EQ_TAC >|
    [STRIP_TAC
     >> NTAC 2 (POP_ASSUM MP_TAC)
     >> Cases_on `l` >- RW_TAC std_ss [SNOC]
     >> Cases_on `t'`
     >- (RW_TAC std_ss [SNOC]
         >> Q.EXISTS_TAC `[]`
         >> RW_TAC std_ss [SNOC])
     >> RW_TAC std_ss [SNOC]
     >> Q.EXISTS_TAC `h''::t''`
     >> RW_TAC std_ss [SNOC],
     RW_TAC std_ss []
     >> Q.EXISTS_TAC `h::l`
     >> RW_TAC std_ss [SNOC]],
    EQ_TAC >|
    [STRIP_TAC
     >> NTAC 2 (POP_ASSUM MP_TAC)
     >> Cases_on `l` >- RW_TAC std_ss [SNOC]
     >> Cases_on `t'`
     >- (RW_TAC std_ss [SNOC]
         >> Q.EXISTS_TAC `[]`
         >> RW_TAC std_ss [SNOC])
     >> RW_TAC std_ss [SNOC]
     >> Q.EXISTS_TAC `h''::t''`
     >> RW_TAC std_ss [SNOC],
     RW_TAC std_ss []
     >> Q.EXISTS_TAC `h::l`
     >> RW_TAC std_ss [SNOC]]]);

val PROB_TWIN_REDUCE = store_thm
  ("PROB_TWIN_REDUCE",
   ``!h t t'. prob_twin (h::t) (h::t') = prob_twin t t'``,
   Cases_on `t`
   >> RW_TAC std_ss [PROB_TWIN_CONS, PROB_TWIN_SING, PROB_TWIN_NIL]
   >> PROVE_TAC []);

val PROB_TWINS_PREFIX = store_thm
  ("PROB_TWINS_PREFIX",
   ``!x l. IS_PREFIX x l
           ==> (x = l) \/ IS_PREFIX x (SNOC T l) \/ IS_PREFIX x (SNOC F l)``,
   Induct_on `x` >- RW_TAC list_ss [IS_PREFIX_NIL]
   >> Cases_on `l` >- RW_TAC list_ss [SNOC, IS_PREFIX]
   >> RW_TAC list_ss [IS_PREFIX, SNOC]);

val PROB_ORDER_NIL = store_thm
  ("PROB_ORDER_NIL",
   ``!x. prob_order [] x /\ (prob_order x [] = (x = []))``,
   Induct >- RW_TAC list_ss [prob_order_def]
   >> RW_TAC list_ss [prob_order_def]);

val PROB_ORDER_REFL = store_thm
  ("PROB_ORDER_REFL",
   ``!x. prob_order x x``,
   Induct >- RW_TAC list_ss [prob_order_def]
   >> RW_TAC list_ss [prob_order_def]);

val PROB_ORDER_ANTISYM = store_thm
  ("PROB_ORDER_ANTISYM",
   ``!x y. prob_order x y /\ prob_order y x ==> (x = y)``,
   Induct >- (Cases >> RW_TAC list_ss [prob_order_def])
   >> STRIP_TAC
   >> Cases >- RW_TAC list_ss [prob_order_def]
   >> (RW_TAC std_ss [prob_order_def] >> PROVE_TAC []));

val PROB_ORDER_TRANS = store_thm
  ("PROB_ORDER_TRANS",
   ``!x y z. prob_order x y /\ prob_order y z ==> prob_order x z``,
   Induct >- (Cases_on `z` >> RW_TAC list_ss [prob_order_def])
   >> STRIP_TAC
   >> Cases >- RW_TAC list_ss [prob_order_def]
   >> Cases >- RW_TAC list_ss [prob_order_def]
   >> (RW_TAC list_ss [prob_order_def] >> PROVE_TAC []));

val PROB_ORDER_TOTAL = store_thm
  ("PROB_ORDER_TOTAL",
   ``!x y. prob_order x y \/ prob_order y x``,
   Induct >- PROVE_TAC [PROB_ORDER_NIL]
   >> Cases_on `y` >- PROVE_TAC [PROB_ORDER_NIL]
   >> RW_TAC list_ss [prob_order_def]
   >> PROVE_TAC []);

val PROB_ORDER_PREFIX = store_thm
  ("PROB_ORDER_PREFIX",
   ``!x y. IS_PREFIX y x ==> prob_order x y``,
   Induct >- (Cases >> RW_TAC list_ss [prob_order_def])
   >> Cases_on `y` >- RW_TAC list_ss [IS_PREFIX_NIL]
   >> RW_TAC list_ss [IS_PREFIX, prob_order_def]);

val PROB_ORDER_PREFIX_ANTI = store_thm
  ("PROB_ORDER_PREFIX_ANTI",
   ``!x y. prob_order x y /\ IS_PREFIX x y ==> (x = y)``,
   Induct >- RW_TAC list_ss [IS_PREFIX_NIL]
   >> Cases_on `y` >- RW_TAC list_ss [IS_PREFIX_NIL, prob_order_def]
   >> (RW_TAC list_ss [IS_PREFIX, prob_order_def]
         >> PROVE_TAC []))

val PROB_ORDER_PREFIX_MONO = store_thm
  ("PROB_ORDER_PREFIX_MONO",
   ``!x y z. prob_order x y /\ prob_order y z /\ IS_PREFIX z x
             ==> IS_PREFIX y x``,
   Induct >- RW_TAC list_ss [IS_PREFIX]
   >> Cases_on `y` >- RW_TAC list_ss [prob_order_def]
   >> Cases_on `z` >- RW_TAC list_ss [IS_PREFIX_NIL]
   >> (RW_TAC list_ss [prob_order_def, IS_PREFIX]
         >> PROVE_TAC []));

val PROB_ORDER_PREFIX_TRANS = store_thm
  ("PROB_ORDER_PREFIX_TRANS",
   ``!x y z. prob_order x y /\ IS_PREFIX y z
             ==> prob_order x z \/ IS_PREFIX x z``,
   Induct >- (Cases_on `z` >> RW_TAC list_ss [prob_order_def])
   >> Cases_on `y` >- RW_TAC list_ss [PROB_ORDER_NIL]
   >> Cases_on `z` >- RW_TAC list_ss [IS_PREFIX]
   >> (RW_TAC list_ss [prob_order_def, IS_PREFIX] >> PROVE_TAC []));

val PROB_ORDER_SNOC = store_thm
  ("PROB_ORDER_SNOC",
   ``!x l. ~prob_order (SNOC x l) l``,
   Induct_on `l` >- RW_TAC std_ss [prob_order_def, SNOC]
   >> RW_TAC std_ss [prob_order_def, SNOC]);

val PROB_SORTED_MIN = store_thm
  ("PROB_SORTED_MIN",
   ``!h t. prob_sorted (h::t) ==> (!x. MEM x t ==> prob_order h x)``,
   Induct_on `t` >- RW_TAC list_ss [MEM]
   >> RW_TAC list_ss [prob_sorted_def, MEM] >- PROVE_TAC []
   >> Know `prob_order h x` >- PROVE_TAC []
   >> PROVE_TAC [PROB_ORDER_TRANS]);

val PROB_SORTED_DEF_ALT = store_thm
  ("PROB_SORTED_DEF_ALT",
   ``!h t. prob_sorted (h::t)
           = (!x. MEM x t ==> prob_order h x) /\ prob_sorted t``,
   REPEAT STRIP_TAC
   >> EQ_TAC
     >- (Cases_on `t` >> PROVE_TAC [PROB_SORTED_MIN, prob_sorted_def])
   >> Cases_on `t` >- RW_TAC list_ss [prob_sorted_def]
   >> RW_TAC list_ss [prob_sorted_def]
   >> PROVE_TAC [MEM]);

val PROB_SORTED_TL = store_thm
  ("PROB_SORTED_TL",
   ``!h t. prob_sorted (h::t) ==> prob_sorted t``,
   PROVE_TAC [PROB_SORTED_DEF_ALT]);

val PROB_SORTED_MONO = store_thm
  ("PROB_SORTED_MONO",
   ``!x y z. prob_sorted (x::y::z) ==> prob_sorted (x::z)``,
   RW_TAC list_ss [PROB_SORTED_DEF_ALT, MEM]);

val PROB_SORTED_TLS = store_thm
  ("PROB_SORTED_TLS",
   ``!l b. prob_sorted (MAP (CONS b) l) = prob_sorted l``,
   Induct >- RW_TAC list_ss [MAP]
   >> Cases_on `l` >- RW_TAC list_ss [MAP, prob_sorted_def]
   >> RW_TAC list_ss [prob_sorted_def, prob_order_def]
   >> PROVE_TAC [MAP]);

val PROB_SORTED_STEP = store_thm
  ("PROB_SORTED_STEP",
   ``!l1 l2. prob_sorted (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
             = prob_sorted l1 /\ prob_sorted l2``,
   NTAC 2 STRIP_TAC
   >> Induct_on `l1` >- RW_TAC list_ss [MAP, PROB_SORTED_TLS, prob_sorted_def]
   >> STRIP_TAC
   >> POP_ASSUM MP_TAC
   >> Cases_on `l1` >|
   [Cases_on `l2` >- RW_TAC list_ss [MAP, prob_sorted_def]
    >> RW_TAC list_ss [MAP, prob_sorted_def, prob_order_def],
    RW_TAC list_ss [prob_sorted_def, prob_order_def]
    >> PROVE_TAC []]);

val PROB_SORTED_APPEND = store_thm
  ("PROB_SORTED_APPEND",
   ``!h h' t t'. prob_sorted (APPEND (h::t) (h'::t'))
                 = prob_sorted (h::t) /\ prob_sorted (h'::t')
                   /\ prob_order (LAST (h::t)) h'``,
   Induct_on `t`
     >- (RW_TAC list_ss [prob_sorted_def, LAST_CONS]
         >> PROVE_TAC [])
   >> RW_TAC list_ss [prob_sorted_def]
   >> RW_TAC std_ss [(GSYM o CONJUNCT2) APPEND, LAST_CONS]
   >> PROVE_TAC []);

val PROB_SORTED_FILTER = store_thm
  ("PROB_SORTED_FILTER",
   ``!P b. prob_sorted b ==> prob_sorted (FILTER P b)``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [FILTER]
   >> RW_TAC list_ss [PROB_SORTED_DEF_ALT, FILTER]
   >> PROVE_TAC [MEM_FILTER]);

val PROB_PREFIXFREE_TL = store_thm
  ("PROB_PREFIXFREE_TL",
   ``!h t. prob_prefixfree (h::t) ==> prob_prefixfree t``,
   STRIP_TAC
   >> (Cases >> RW_TAC list_ss [prob_prefixfree_def]));

val PROB_PREFIXFREE_MONO = store_thm
  ("PROB_PREFIXFREE_MONO",
   ``!x y z. prob_sorted (x::y::z) /\ prob_prefixfree (x::y::z)
             ==> prob_prefixfree (x::z)``,
   Cases_on `z` >- RW_TAC list_ss [prob_prefixfree_def]
   >> RW_TAC list_ss [prob_prefixfree_def, prob_sorted_def]
   >> PROVE_TAC [PROB_ORDER_PREFIX_MONO]);

val PROB_PREFIXFREE_ELT = store_thm
  ("PROB_PREFIXFREE_ELT",
   ``!h t. prob_sorted (h::t) /\ prob_prefixfree (h::t)
         ==> (!x. MEM x t ==> ~IS_PREFIX x h /\ ~IS_PREFIX h x)``,
   Induct_on `t` >- RW_TAC list_ss [MEM]
   >> ONCE_REWRITE_TAC [MEM]
   >> NTAC 5 STRIP_TAC >|
   [CONJ_TAC >- PROVE_TAC [prob_prefixfree_def]
    >> Know `prob_order h' h` >- PROVE_TAC [prob_sorted_def]
    >> PROVE_TAC [PROB_ORDER_PREFIX_ANTI, IS_PREFIX_REFL, prob_prefixfree_def],
    Suff `prob_sorted (h'::t) /\ prob_prefixfree (h'::t)`
      >- PROVE_TAC []
    >> PROVE_TAC [PROB_SORTED_MONO, PROB_PREFIXFREE_MONO]]);

val PROB_PREFIXFREE_TLS = store_thm
  ("PROB_PREFIXFREE_TLS",
   ``!l b. prob_prefixfree (MAP (CONS b) l) = prob_prefixfree l``,
   Induct >- RW_TAC list_ss [MAP]
   >> Cases_on `l` >- RW_TAC list_ss [MAP, prob_prefixfree_def]
   >> RW_TAC list_ss [prob_prefixfree_def, IS_PREFIX]
   >> PROVE_TAC [MAP]);

val PROB_PREFIXFREE_STEP = store_thm
  ("PROB_PREFIXFREE_STEP",
   ``!l1 l2. prob_prefixfree (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
             = prob_prefixfree l1 /\ prob_prefixfree l2``,
   NTAC 2 STRIP_TAC
   >> Induct_on `l1`
   >- RW_TAC list_ss [MAP, PROB_PREFIXFREE_TLS, prob_prefixfree_def]
   >> STRIP_TAC
   >> POP_ASSUM MP_TAC
   >> Cases_on `l1` >|
   [Cases_on `l2` >- RW_TAC list_ss [MAP, prob_prefixfree_def]
    >> RW_TAC list_ss [MAP, prob_prefixfree_def, IS_PREFIX],
    RW_TAC list_ss [prob_prefixfree_def, IS_PREFIX]
    >> PROVE_TAC []]);

val PROB_PREFIXFREE_APPEND = store_thm
  ("PROB_PREFIXFREE_APPEND",
   ``!h h' t t'. prob_prefixfree (APPEND (h::t) (h'::t'))
                 = prob_prefixfree (h::t) /\ prob_prefixfree (h'::t')
                   /\ ~IS_PREFIX h' (LAST (h::t))``,
   Induct_on `t`
     >- (RW_TAC list_ss [prob_prefixfree_def, LAST_CONS]
         >> PROVE_TAC [])
   >> RW_TAC list_ss [prob_prefixfree_def]
   >> RW_TAC std_ss [(GSYM o CONJUNCT2) APPEND, LAST_CONS]
   >> PROVE_TAC []);

val PROB_PREFIXFREE_FILTER = store_thm
  ("PROB_PREFIXFREE_FILTER",
   ``!P b. prob_sorted b /\ prob_prefixfree b ==> prob_prefixfree (FILTER P b)``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [FILTER]
   >> NTAC 2 STRIP_TAC
   >> Know `prob_prefixfree (FILTER P b)`
     >- PROVE_TAC [PROB_SORTED_TL, PROB_PREFIXFREE_TL]
   >> RW_TAC list_ss [FILTER]
   >> Cases_on `FILTER P b` >- RW_TAC list_ss [prob_prefixfree_def]
   >> RW_TAC list_ss [prob_prefixfree_def]
   >> Know `MEM (h':bool list) b` >- PROVE_TAC [MEM_FILTER, MEM]
   >> PROVE_TAC [PROB_PREFIXFREE_ELT]);

val PROB_TWINFREE_TL = store_thm
  ("PROB_TWINFREE_TL",
   ``!h t. prob_twinfree (h::t) ==> prob_twinfree t``,
   Cases_on `t` >> RW_TAC list_ss [prob_twinfree_def]);

val PROB_TWINFREE_TLS = store_thm
  ("PROB_TWINFREE_TLS",
   ``!l b. prob_twinfree (MAP (CONS b) l) = prob_twinfree l``,
   NTAC 2 STRIP_TAC
   >> Induct_on `l` >- RW_TAC list_ss [MAP]
   >> STRIP_TAC
   >> Cases_on `l` >- RW_TAC std_ss [MAP, prob_twinfree_def]
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [MAP, prob_twinfree_def, prob_twin_def]
   >> KILL_TAC
   >> Suff `(?l. (b::h = SNOC T l) /\ (b::h' = SNOC F l))
                = (?l. (h = SNOC T l) /\ (h' = SNOC F l))`
   >- PROVE_TAC []
   >> EQ_TAC >|
   [RW_TAC std_ss []
    >> NTAC 2 (POP_ASSUM MP_TAC)
    >> Cases_on `l` >- RW_TAC std_ss [SNOC]
    >> RW_TAC std_ss [SNOC]
    >> PROVE_TAC [],
    RW_TAC std_ss []
    >> Q.EXISTS_TAC `b::l`
    >> Cases_on `l`
    >> RW_TAC std_ss [SNOC]]);

val PROB_TWINFREE_STEP1 = store_thm
  ("PROB_TWINFREE_STEP1",
   ``!l1 l2. prob_twinfree (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
             ==> prob_twinfree l1 /\ prob_twinfree l2``,
   NTAC 2 STRIP_TAC
   >> Induct_on `l1`
   >- RW_TAC list_ss [MAP, PROB_TWINFREE_TLS, prob_twinfree_def]
   >> STRIP_TAC
   >> POP_ASSUM MP_TAC
   >> Cases_on `l1` >|
   [Cases_on `l2` >- RW_TAC list_ss [MAP, prob_twinfree_def]
    >> RW_TAC list_ss [MEM, MAP, prob_twinfree_def],
    RW_TAC list_ss [prob_twinfree_def, PROB_TWIN_REDUCE, MEM]]);

val PROB_TWINFREE_STEP2 = store_thm
  ("PROB_TWINFREE_STEP2",
   ``!l1 l2. (~(MEM [] l1) \/ ~(MEM [] l2))
             /\ prob_twinfree l1 /\ prob_twinfree l2
             ==> prob_twinfree (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))``,
   NTAC 2 STRIP_TAC
   >> Induct_on `l1`
   >- RW_TAC list_ss [MAP, PROB_TWINFREE_TLS, prob_twinfree_def]
   >> STRIP_TAC
   >> POP_ASSUM MP_TAC
   >> Cases_on `l1` >|
   [Cases_on `l2` >- RW_TAC list_ss [MAP, prob_twinfree_def]
    >> RW_TAC list_ss [MEM, MAP, prob_twinfree_def] >|
    [Cases_on `h` >- RW_TAC std_ss []
     >> RW_TAC std_ss [PROB_TWIN_CONS],
     Cases_on `h'` >- RW_TAC std_ss []
     >> RW_TAC std_ss [PROB_TWIN_CONS]],
    RW_TAC list_ss [prob_twinfree_def, PROB_TWIN_REDUCE, MEM]
    >> RES_TAC]);

val PROB_TWINFREE_STEP = store_thm
  ("PROB_TWINFREE_STEP",
   ``!l1 l2. ~(MEM [] l1) \/ ~(MEM [] l2)
             ==> (prob_twinfree (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
                  = prob_twinfree l1 /\ prob_twinfree l2)``,
   PROVE_TAC [PROB_TWINFREE_STEP1, PROB_TWINFREE_STEP2]);

val PROB_LONGEST_HD = store_thm
  ("PROB_LONGEST_HD",
   ``!h t. LENGTH h <= prob_longest (h::t)``,
   Induct_on `t` >- RW_TAC arith_ss [prob_longest_def, FOLDR]
   >> RW_TAC arith_ss [prob_longest_def, FOLDR]);

val PROB_LONGEST_TL = store_thm
  ("PROB_LONGEST_TL",
   ``!h t. prob_longest t <= prob_longest (h::t)``,
   Induct_on `t` >- RW_TAC arith_ss [prob_longest_def, FOLDR]
   >> RW_TAC arith_ss [prob_longest_def, FOLDR]);

val PROB_LONGEST_TLS = store_thm
  ("PROB_LONGEST_TLS",
   ``!h t b. prob_longest (MAP (CONS b) (h::t)) = SUC (prob_longest (h::t))``,
   Induct_on `t`
     >- RW_TAC arith_ss [prob_longest_def, FOLDR_MAP, FOLDR, LENGTH]
   >> RW_TAC arith_ss [prob_longest_def]
   >> ONCE_REWRITE_TAC [MAP]
   >> ONCE_REWRITE_TAC [FOLDR]
   >> REWRITE_TAC [GSYM prob_longest_def]
   >> RW_TAC arith_ss [LENGTH]);

val PROB_LONGEST_APPEND = store_thm
  ("PROB_LONGEST_APPEND",
   ``!l1 l2. prob_longest l1 <= prob_longest (APPEND l1 l2)
             /\ prob_longest l2 <= prob_longest (APPEND l1 l2)``,
   NTAC 2 STRIP_TAC
   >> Induct_on `l1` >- RW_TAC arith_ss [APPEND, prob_longest_def, FOLDR]
   >> REWRITE_TAC [APPEND, prob_longest_def, FOLDR]
   >> REWRITE_TAC [GSYM prob_longest_def]
   >> RW_TAC arith_ss []);

val PROB_CANON_PREFS_HD = store_thm
  ("PROB_CANON_PREFS_HD",
   ``!l b. HD (prob_canon_prefs l b) = l``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_prefs_def]
   >> RW_TAC list_ss [prob_canon_prefs_def]);

val PROB_CANON_PREFS_DELETES = store_thm
  ("PROB_CANON_PREFS_DELETES",
   ``!l b x. MEM x (prob_canon_prefs l b) ==> MEM x (l::b)``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_prefs_def]
   >> RW_TAC list_ss [prob_canon_prefs_def]
   >> RES_TAC
   >> POP_ASSUM MP_TAC
   >> KILL_TAC
   >> RW_TAC list_ss [MEM]
   >> PROVE_TAC []);

val PROB_CANON_PREFS_SORTED = store_thm
  ("PROB_CANON_PREFS_SORTED",
   ``!l b. prob_sorted (l::b) ==> prob_sorted (prob_canon_prefs l b)``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_prefs_def]
   >> RW_TAC list_ss [prob_canon_prefs_def]
   >> PROVE_TAC [PROB_SORTED_MONO]);

val PROB_CANON_PREFS_PREFIXFREE = store_thm
  ("PROB_CANON_PREFS_PREFIXFREE",
   ``!l b. prob_sorted b /\ prob_prefixfree b
           ==> prob_prefixfree (prob_canon_prefs l b)``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_prefs_def, prob_prefixfree_def]
   >> RW_TAC list_ss [prob_canon_prefs_def, prob_prefixfree_def]
   >> PROVE_TAC [PROB_SORTED_TL, PROB_PREFIXFREE_TL]);

val PROB_CANON_PREFS_CONSTANT = store_thm
  ("PROB_CANON_PREFS_CONSTANT",
   ``!l b. prob_prefixfree (l::b)
           ==> (prob_canon_prefs l b = l::b)``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_prefixfree_def, prob_canon_prefs_def]
   >> RW_TAC list_ss [prob_prefixfree_def, prob_canon_prefs_def]);

val PROB_CANON_FIND_HD = store_thm
  ("PROB_CANON_FIND_HD",
   ``!l h t. (HD (prob_canon_find l (h::t)) = l)
             \/ (HD (prob_canon_find l (h::t)) = h)``,
   Induct_on `t` >- RW_TAC list_ss [prob_canon_find_def, PROB_CANON_PREFS_HD]
   >> RW_TAC list_ss [prob_canon_find_def, PROB_CANON_PREFS_HD]);

val PROB_CANON_FIND_DELETES = store_thm
  ("PROB_CANON_FIND_DELETES",
   ``!l b x. MEM x (prob_canon_find l b) ==> MEM x (l::b)``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_find_def]
   >> RW_TAC list_ss [prob_canon_find_def, MEM] >-
   (PROVE_TAC [MEM]) >-
   (PROVE_TAC [MEM, PROB_CANON_PREFS_DELETES]));

val PROB_CANON_FIND_SORTED = store_thm
  ("PROB_CANON_FIND_SORTED",
   ``!l b. prob_sorted b ==> prob_sorted (prob_canon_find l b)``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_find_def, prob_sorted_def]
   >> RW_TAC list_ss [prob_canon_find_def] >-
   (POP_ASSUM MP_TAC
    >> RW_TAC list_ss [PROB_SORTED_DEF_ALT]
    >> PROVE_TAC [PROB_CANON_FIND_DELETES, MEM]) >-
   (Suff `prob_sorted (l::h::b)` >- PROVE_TAC [PROB_CANON_PREFS_SORTED]
    >> REWRITE_TAC [prob_sorted_def]
    >> PROVE_TAC [PROB_ORDER_TOTAL]));

val PROB_CANON_FIND_PREFIXFREE = store_thm
  ("PROB_CANON_FIND_PREFIXFREE",
   ``!l b. prob_sorted b /\ prob_prefixfree b
           ==> prob_prefixfree (prob_canon_find l b)``,
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_find_def, prob_prefixfree_def]
   >> RW_TAC list_ss [prob_canon_find_def] >|
   [Cases_on `b` >- RW_TAC list_ss [prob_prefixfree_def, prob_canon_find_def]
    >> Cases_on `prob_canon_find l (h'::t)`
      >- RW_TAC list_ss [prob_prefixfree_def, prob_canon_find_def]
    >> Reverse (RW_TAC list_ss [prob_prefixfree_def])
      >- PROVE_TAC [PROB_SORTED_TL, PROB_PREFIXFREE_TL]
    >> Suff `(h'' = h') \/ (h'' = (l:bool list))`
      >- PROVE_TAC [prob_prefixfree_def]
    >> POP_ASSUM MP_TAC
    >> KILL_TAC
    >> PROVE_TAC [PROB_CANON_FIND_HD, HD],
    PROVE_TAC [PROB_CANON_PREFS_PREFIXFREE]]);

val PROB_CANON_FIND_CONSTANT = store_thm
  ("PROB_CANON_FIND_CONSTANT",
   ``!l b. prob_sorted (l::b) /\ prob_prefixfree (l::b)
           ==> (prob_canon_find l b = l::b)``,
   STRIP_TAC
   >> Cases >- RW_TAC list_ss [prob_canon_find_def]
   >> STRIP_TAC
   >> Know `~((l:bool list) = h)`
     >- PROVE_TAC [prob_prefixfree_def, IS_PREFIX_REFL]
   >> (RW_TAC list_ss [prob_canon_find_def, PROB_CANON_PREFS_CONSTANT]
         >> PROVE_TAC [prob_sorted_def, PROB_ORDER_ANTISYM]));

val PROB_CANON1_SORTED = store_thm
  ("PROB_CANON1_SORTED",
   ``!l. prob_sorted (prob_canon1 l)``,
   REWRITE_TAC [prob_canon1_def]
   >> Induct >- RW_TAC list_ss [FOLDR, prob_sorted_def]
   >> RW_TAC list_ss [PROB_CANON_FIND_SORTED, FOLDR]);

val PROB_CANON1_PREFIXFREE = store_thm
  ("PROB_CANON1_PREFIXFREE",
   ``!l. prob_prefixfree (prob_canon1 l)``,
   Induct >- RW_TAC list_ss [prob_prefixfree_def, prob_canon1_def, FOLDR]
   >> RW_TAC list_ss [prob_canon1_def, FOLDR]
   >> RW_TAC list_ss [GSYM prob_canon1_def]
   >> Know `prob_sorted (prob_canon1 l)` >- PROVE_TAC [PROB_CANON1_SORTED]
   >> PROVE_TAC [PROB_CANON_FIND_PREFIXFREE]);

val PROB_CANON1_CONSTANT = store_thm
  ("PROB_CANON1_CONSTANT",
   ``!l. prob_sorted l /\ prob_prefixfree l ==> (prob_canon1 l = l)``,
   RW_TAC list_ss [prob_canon1_def]
   >> Induct_on `l` >- RW_TAC list_ss [FOLDR]
   >> RW_TAC list_ss [FOLDR]
   >> PROVE_TAC [PROB_CANON_FIND_CONSTANT, PROB_SORTED_TL, PROB_PREFIXFREE_TL]);

val PROB_CANON_MERGE_SORTED_PREFIXFREE_TWINFREE = store_thm
  ("PROB_CANON_MERGE_SORTED_PREFIXFREE_TWINFREE",
   ``!l b. prob_sorted (l::b) /\ prob_prefixfree (l::b) /\ prob_twinfree b
           ==> prob_sorted (prob_canon_merge l b)
               /\ prob_prefixfree (prob_canon_merge l b)
               /\ prob_twinfree (prob_canon_merge l b)``,
    Induct_on `b`
 >- RW_TAC std_ss [prob_canon_merge_def, prob_twinfree_def]
 >> NTAC 3 STRIP_TAC
 >> Know `prob_twinfree b` >- PROVE_TAC [PROB_TWINFREE_TL]
 >> RW_TAC std_ss [prob_canon_merge_def, prob_twinfree_def, prob_twin_def] (* 3 sub-goals here *)
 >> (Know `prob_sorted (l'::b)`
     >- (Know `prob_sorted (SNOC T l'::b)`
         >- PROVE_TAC [PROB_SORTED_MONO]
         >> Cases_on `b` >- RW_TAC std_ss [prob_sorted_def]
         >> POP_ASSUM MP_TAC
         >> RW_TAC std_ss [prob_sorted_def]
         >> Suff `prob_order l' (SNOC T l')`
         >- PROVE_TAC [PROB_ORDER_TRANS]
         >> MATCH_MP_TAC PROB_ORDER_PREFIX
         >> RW_TAC std_ss [IS_PREFIX_SNOC, IS_PREFIX_REFL]) \\
     Know `prob_prefixfree (l'::b)`
     >- (Know `prob_prefixfree (SNOC T l'::b)`
         >- PROVE_TAC [PROB_PREFIXFREE_MONO]
         >> Cases_on `b` >- RW_TAC std_ss [prob_prefixfree_def]
         >> POP_ASSUM MP_TAC
         >> Q.PAT_X_ASSUM `prob_prefixfree X` MP_TAC
         >> Q.PAT_X_ASSUM `prob_sorted (SNOC T X::Y)` MP_TAC
         >> RW_TAC std_ss [prob_prefixfree_def, prob_sorted_def]
         >> STRIP_TAC
         >> MP_TAC (Q.SPECL [`h`, `l'`] PROB_TWINS_PREFIX)
         >> RW_TAC std_ss []
         >> STRIP_TAC
         >> Q.PAT_X_ASSUM `prob_order (SNOC F l') h` MP_TAC
         >> RW_TAC std_ss [PROB_ORDER_SNOC]) \\
     RW_TAC std_ss [BUTLAST]) );

val PROB_CANON_MERGE_PREFIXFREE_PRESERVE = store_thm
  ("PROB_CANON_MERGE_PREFIXFREE_PRESERVE",
   ``!l b h. (!x. MEM x (l::b) ==> ~IS_PREFIX h x /\ ~IS_PREFIX x h)
           ==> (!x. MEM x (prob_canon_merge l b)
                    ==> ~IS_PREFIX h x /\ ~IS_PREFIX x h)``,
   Induct_on `b` >- RW_TAC std_ss [MEM, prob_canon_merge_def, IS_PREFIX]
   >> REWRITE_TAC [prob_canon_merge_def]
   >> NTAC 5 STRIP_TAC
   >> Reverse (Cases_on `prob_twin l h`) >- ASM_REWRITE_TAC []
   >> ASM_REWRITE_TAC []
   >> POP_ASSUM MP_TAC
   >> REWRITE_TAC [prob_twin_def]
   >> NTAC 2 STRIP_TAC
   >> Suff `!x. MEM x (BUTLAST h::b)
                ==> ~IS_PREFIX h' x /\ ~IS_PREFIX x h'`
     >- PROVE_TAC []
   >> REWRITE_TAC [MEM]
   >> Reverse (NTAC 2 STRIP_TAC) >- PROVE_TAC [MEM]
   >> ASM_REWRITE_TAC [BUTLAST]
   >> Reverse (Suff `~IS_PREFIX h' l /\ ~IS_PREFIX l h'
                            /\ ~IS_PREFIX h' h /\ ~IS_PREFIX h h'`)
   >- PROVE_TAC [MEM]
   >> ASM_REWRITE_TAC []
   >> KILL_TAC
   >> RW_TAC std_ss [IS_PREFIX_SNOC]
   >> PROVE_TAC [PROB_TWINS_PREFIX]);

val PROB_CANON_MERGE_SHORTENS = store_thm
  ("PROB_CANON_MERGE_SHORTENS",
   ``!l b x. MEM x (prob_canon_merge l b)
             ==> (?y. MEM y (l::b) /\ IS_PREFIX y x)``,
   Induct_on `b` >- RW_TAC std_ss [prob_canon_merge_def, MEM, IS_PREFIX_REFL]
   >> Reverse (RW_TAC std_ss [prob_canon_merge_def, prob_twin_def])
   >- PROVE_TAC [IS_PREFIX_REFL]
   >> Q.PAT_X_ASSUM `!l. P l` (MP_TAC o Q.SPECL [`l'`, `x`])
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [BUTLAST, MEM] >|
   [Q.EXISTS_TAC `SNOC F l'`
    >> RW_TAC std_ss [IS_PREFIX_SNOC],
    PROVE_TAC []]);

val PROB_CANON_MERGE_CONSTANT = store_thm
  ("PROB_CANON_MERGE_CONSTANT",
   ``!l b. prob_twinfree (l::b) ==> (prob_canon_merge l b = l::b)``,
   STRIP_TAC
   >> Cases >- RW_TAC list_ss [prob_canon_merge_def]
   >> RW_TAC list_ss [prob_twinfree_def, prob_canon_merge_def, PROB_TWIN_NIL]);

val PROB_CANON2_PREFIXFREE_PRESERVE = store_thm
  ("PROB_CANON2_PREFIXFREE_PRESERVE",
   ``!l h. (!x. MEM x l ==> ~IS_PREFIX h x /\ ~IS_PREFIX x h)
           ==> (!x. MEM x (prob_canon2 l)
                    ==> ~IS_PREFIX h x /\ ~IS_PREFIX x h)``,
   REWRITE_TAC [prob_canon2_def]
   >> NTAC 2 STRIP_TAC
   >> Induct_on `l` >- RW_TAC list_ss [FOLDR, MEM]
   >> REWRITE_TAC [FOLDR, MEM]
   >> NTAC 2 STRIP_TAC
   >> Suff `!x. MEM x (h'::FOLDR prob_canon_merge [] l)
                       ==> ~IS_PREFIX h x /\ ~IS_PREFIX x h`
     >- PROVE_TAC [PROB_CANON_MERGE_PREFIXFREE_PRESERVE]
   >> REWRITE_TAC [MEM]
   >> PROVE_TAC []);

val PROB_CANON2_SHORTENS = store_thm
  ("PROB_CANON2_SHORTENS",
   ``!l x. MEM x (prob_canon2 l) ==> ?y. MEM y l /\ IS_PREFIX y x``,
   REWRITE_TAC [prob_canon2_def]
   >> Induct >- RW_TAC list_ss [MEM, FOLDR]
   >> RW_TAC list_ss [FOLDR]
   >> Know
           `?y. IS_PREFIX y x /\ MEM y (h::(FOLDR prob_canon_merge [] l))`
     >- PROVE_TAC [PROB_CANON_MERGE_SHORTENS]
   >> POP_ASSUM MP_TAC
   >> RW_TAC list_ss [MEM] >- PROVE_TAC []
   >> Know `?y''. MEM y'' l /\ IS_PREFIX (y'':bool list) y`
     >- PROVE_TAC []
   >> PROVE_TAC [IS_PREFIX_TRANS]);

val PROB_CANON2_SORTED_PREFIXFREE_TWINFREE = store_thm
  ("PROB_CANON2_SORTED_PREFIXFREE_TWINFREE",
   ``!l. prob_sorted l /\ prob_prefixfree l
         ==> prob_sorted (prob_canon2 l)
             /\ prob_prefixfree (prob_canon2 l)
             /\ prob_twinfree (prob_canon2 l)``,
   REWRITE_TAC [prob_canon2_def]
   >> Induct
   >- RW_TAC list_ss [FOLDR, prob_sorted_def, prob_prefixfree_def,
                      prob_twinfree_def]
   >> REWRITE_TAC [FOLDR]
   >> NTAC 2 STRIP_TAC
   >> Know `prob_sorted l /\ prob_prefixfree l`
   >- PROVE_TAC [PROB_SORTED_TL, PROB_PREFIXFREE_TL]
   >> STRIP_TAC
   >> RES_TAC
   >> Suff `prob_sorted (h::FOLDR prob_canon_merge [] l)
                /\ prob_prefixfree (h::FOLDR prob_canon_merge [] l)`
   >- PROVE_TAC [PROB_CANON_MERGE_SORTED_PREFIXFREE_TWINFREE]
   >> POP_ASSUM (K ALL_TAC)
   >> NTAC 2 (POP_ASSUM MP_TAC) >> NTAC 2 (POP_ASSUM (K ALL_TAC))
   >> NTAC 2 (POP_ASSUM MP_TAC) >> POP_ASSUM (K ALL_TAC)
   >> Cases_on `FOLDR prob_canon_merge [] l`
     >- RW_TAC list_ss [prob_sorted_def, prob_prefixfree_def]
   >> NTAC 4 STRIP_TAC
   >> Know `~IS_PREFIX h h' /\ ~IS_PREFIX h' (h:bool list)`
     >- (Suff `!x. MEM x (prob_canon2 l)
                        ==> ~IS_PREFIX h x /\ ~IS_PREFIX (x:bool list) h`
           >- (REWRITE_TAC [prob_canon2_def] >> PROVE_TAC [MEM])
         >> Suff
             `!x. MEM x l ==> ~IS_PREFIX h x /\ ~IS_PREFIX (x:bool list) h`
           >- PROVE_TAC [PROB_CANON2_PREFIXFREE_PRESERVE]
         >> PROVE_TAC [PROB_PREFIXFREE_ELT])
   >> RW_TAC list_ss [prob_sorted_def, prob_prefixfree_def]
   >> Know `?x. MEM x l /\ IS_PREFIX x (h':bool list)`
     >- (Know `MEM h' (prob_canon2 l)` >- PROVE_TAC [prob_canon2_def, MEM]
         >> PROVE_TAC [PROB_CANON2_SHORTENS])
   >> STRIP_TAC
   >> Know `prob_order h x` >- PROVE_TAC [PROB_SORTED_DEF_ALT]
   >> PROVE_TAC [PROB_ORDER_PREFIX_TRANS]);

val PROB_CANON2_CONSTANT = store_thm
  ("PROB_CANON2_CONSTANT",
   ``!l. prob_twinfree l ==> (prob_canon2 l = l)``,
   RW_TAC list_ss [prob_canon2_def]
   >> Induct_on `l` >- RW_TAC list_ss [FOLDR]
   >> RW_TAC list_ss [FOLDR]
   >> PROVE_TAC [PROB_CANON_MERGE_CONSTANT, PROB_TWINFREE_TL]);

val PROB_CANON_SORTED_PREFIXFREE_TWINFREE = store_thm
  ("PROB_CANON_SORTED_PREFIXFREE_TWINFREE",
   ``!l. prob_sorted (prob_canon l)
         /\ prob_prefixfree (prob_canon l)
         /\ prob_twinfree (prob_canon l)``,
   RW_TAC list_ss [prob_canon_def,
                   PROB_CANON1_SORTED, PROB_CANON1_PREFIXFREE,
                   PROB_CANON2_SORTED_PREFIXFREE_TWINFREE]);

val PROB_CANON_CONSTANT = store_thm
  ("PROB_CANON_CONSTANT",
   ``!l. prob_sorted l /\ prob_prefixfree l /\ prob_twinfree l
         ==> (prob_canon l = l)``,
   RW_TAC std_ss [prob_canon_def, PROB_CANON1_CONSTANT, PROB_CANON2_CONSTANT]);

val PROB_CANON_IDEMPOT = store_thm
  ("PROB_CANON_IDEMPOT",
   ``!l. prob_canon (prob_canon l) = prob_canon l``,
   STRIP_TAC
   >> MP_TAC (Q.SPEC `l` PROB_CANON_SORTED_PREFIXFREE_TWINFREE)
   >> RW_TAC std_ss [PROB_CANON_CONSTANT]);

val PROB_CANONICAL_DEF_ALT = store_thm
  ("PROB_CANONICAL_DEF_ALT",
   ``!l. prob_canonical l
         = prob_sorted l /\ prob_prefixfree l /\ prob_twinfree l``,
   RW_TAC std_ss [prob_canonical_def]
   >> EQ_TAC >|
   [PROVE_TAC [PROB_CANON_SORTED_PREFIXFREE_TWINFREE],
    PROVE_TAC [PROB_CANON_CONSTANT]]);

val PROB_CANONICAL_BASIC = store_thm
  ("PROB_CANONICAL_BASIC",
   ``prob_canonical [] /\ prob_canonical [[]] /\ !x. prob_canonical [x]``,
   RW_TAC list_ss [PROB_CANONICAL_DEF_ALT, prob_sorted_def,
                   prob_prefixfree_def, prob_twinfree_def]);

val PROB_CANON_BASIC = store_thm
  ("PROB_CANON_BASIC",
   ``(prob_canon [] = []) /\ (prob_canon [[]] = [[]])
     /\ (!x. prob_canon [x] = [x])``,
   PROVE_TAC [prob_canonical_def, PROB_CANONICAL_BASIC]);

val PROB_CANONICAL_TL = store_thm
  ("PROB_CANONICAL_TL",
   ``!h t. prob_canonical (h::t) ==> prob_canonical t``,
   RW_TAC std_ss [PROB_CANONICAL_DEF_ALT] >|
   [PROVE_TAC [PROB_SORTED_TL],
    PROVE_TAC [PROB_PREFIXFREE_TL],
    PROVE_TAC [PROB_TWINFREE_TL]]);

val PROB_CANONICAL_NIL_MEM = store_thm
  ("PROB_CANONICAL_NIL_MEM",
   ``!l. prob_canonical l /\ MEM [] l = (l = [[]])``,
   RW_TAC std_ss []
   >> Reverse EQ_TAC >- RW_TAC std_ss [PROB_CANONICAL_BASIC, MEM]
   >> Induct_on `l` >- RW_TAC std_ss [MEM]
   >> NTAC 2 STRIP_TAC
   >> Know `prob_canonical l` >- PROVE_TAC [PROB_CANONICAL_TL]
   >> STRIP_TAC
   >> Q.PAT_X_ASSUM `prob_canonical (h::l)` MP_TAC
   >> Q.PAT_X_ASSUM `X ==> Y` MP_TAC
   >> Q.PAT_X_ASSUM `MEM X Y` MP_TAC
   >> Cases_on `l` >- RW_TAC std_ss [MEM]
   >> RW_TAC std_ss [MEM, PROB_CANONICAL_DEF_ALT, prob_sorted_def,
                     prob_prefixfree_def, PROB_ORDER_NIL, IS_PREFIX_NIL] >|
   [RW_TAC std_ss [IS_PREFIX_NIL],
    RW_TAC std_ss [IS_PREFIX_NIL, PROB_ORDER_NIL]
    >> PROVE_TAC [],
    RES_TAC
    >> RW_TAC std_ss []
    >> PROVE_TAC [MEM]]);

val PROB_CANONICAL_TLS = store_thm
  ("PROB_CANONICAL_TLS",
   ``!l b. prob_canonical (MAP (CONS b) l) = prob_canonical l``,
   RW_TAC list_ss [PROB_CANONICAL_DEF_ALT, PROB_SORTED_TLS, PROB_PREFIXFREE_TLS]
   >> (EQ_TAC >> PROVE_TAC [PROB_TWINFREE_TLS]));

val PROB_CANONICAL_STEP1 = store_thm
  ("PROB_CANONICAL_STEP1",
   ``!l1 l2. prob_canonical (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
             ==> prob_canonical l1 /\ prob_canonical l2``,
   RW_TAC std_ss [PROB_CANONICAL_DEF_ALT, PROB_SORTED_STEP, PROB_PREFIXFREE_STEP]
   >> PROVE_TAC [PROB_TWINFREE_STEP1]);

val PROB_CANONICAL_STEP2 = store_thm
  ("PROB_CANONICAL_STEP2",
   ``!l1 l2. (~(l1 = [[]]) \/ ~(l2 = [[]]))
             /\ prob_canonical l1 /\ prob_canonical l2
             ==> prob_canonical (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))``,
   NTAC 2 STRIP_TAC
   >> DISCH_TAC
   >> Reverse (Suff `~(MEM [] l1) \/ ~(MEM [] l2)`)
   >- PROVE_TAC [PROB_CANONICAL_NIL_MEM]
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [PROB_CANONICAL_DEF_ALT, PROB_SORTED_STEP,
                     PROB_PREFIXFREE_STEP]
   >> PROVE_TAC [PROB_TWINFREE_STEP2]);

val PROB_CANONICAL_STEP = store_thm
  ("PROB_CANONICAL_STEP",
   ``!l1 l2. ~(l1 = [[]]) \/ ~(l2 = [[]])
             ==> (prob_canonical (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
                  = prob_canonical l1 /\ prob_canonical l2)``,
   PROVE_TAC [PROB_CANONICAL_STEP1, PROB_CANONICAL_STEP2]);

val PROB_CANONICAL_CASES_THM = store_thm
  ("PROB_CANONICAL_CASES_THM",
   ``!l. prob_canonical l ==> (l = []) \/ (l = [[]])
            \/ ?l1 l2. prob_canonical l1 /\ prob_canonical l2
                       /\ (l = APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))``,
   Induct >- PROVE_TAC []
   >> Cases
   >- (MP_TAC (SPEC ``([]:bool list)::l`` PROB_CANONICAL_NIL_MEM)
       >> RW_TAC list_ss [MEM])
   >> STRIP_TAC
   >> Know `prob_canonical l` >- PROVE_TAC [PROB_CANONICAL_TL]
   >> STRIP_TAC
   >> RES_TAC >|
   [RW_TAC std_ss []
    >> Cases_on `h'` >|
    [Q.EXISTS_TAC `[t]`
     >> Q.EXISTS_TAC `[]`
     >> RW_TAC list_ss [PROB_CANONICAL_BASIC],
     Q.EXISTS_TAC `[]`
     >> Q.EXISTS_TAC `[t]`
     >> RW_TAC list_ss [PROB_CANONICAL_BASIC]],
    Suff `F` >- PROVE_TAC []
    >> Q.PAT_X_ASSUM `prob_canonical (X::Y)` MP_TAC
    >> MP_TAC (Q.SPEC `(h'::t)::l` PROB_CANONICAL_NIL_MEM)
    >> RW_TAC std_ss [MEM],
    DISJ2_TAC
    >> DISJ2_TAC
    >> Cases_on `h'` >|
    [Q.EXISTS_TAC `t::l1`
     >> Q.EXISTS_TAC `l2`
     >> RW_TAC list_ss []
     >> Q.PAT_X_ASSUM `prob_canonical (X::APPEND Y Z)` MP_TAC
     >> KILL_TAC
     >> MP_TAC (Q.SPECL [`t::l1`, `l2`] PROB_CANONICAL_STEP1)
     >> RW_TAC list_ss [MAP],
     Q.EXISTS_TAC `l1`
     >> Q.EXISTS_TAC `t::l2`
     >> Cases_on `l1` >|
     [RW_TAC list_ss []
      >> Q.PAT_X_ASSUM `prob_canonical (X::APPEND Y Z)` MP_TAC
      >> KILL_TAC
      >> MP_TAC (Q.SPECL [`[]`, `t::l2`] PROB_CANONICAL_STEP1)
      >> RW_TAC list_ss [MAP],
      Suff `~prob_sorted ((F::t)::l)` >- PROVE_TAC [PROB_CANONICAL_DEF_ALT]
      >> RW_TAC list_ss [MAP, prob_sorted_def, prob_order_def]]]]);

val PROB_CANONICAL_CASES = store_thm
  ("PROB_CANONICAL_CASES",
   ``!P. P [] /\ P [[]]
         /\ (!l1 l2. prob_canonical l1 /\ prob_canonical l2
               /\ prob_canonical (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
               ==> P (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2)))
         ==> (!l. prob_canonical l ==> P l)``,
   RW_TAC list_ss []
   >> MP_TAC (SPEC ``l:bool list list`` PROB_CANONICAL_CASES_THM)
   >> (RW_TAC list_ss [] >> PROVE_TAC []));

val PROB_CANONICAL_INDUCT = store_thm
  ("PROB_CANONICAL_INDUCT",
   ``!P. P [] /\ P [[]]
         /\ (!l1 l2. prob_canonical l1 /\ prob_canonical l2 /\ P l1 /\ P l2
               /\ prob_canonical (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
               ==> P (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2)))
         ==> (!l. prob_canonical l ==> P l)``,
   RW_TAC list_ss []
   >> completeInduct_on `prob_longest l`
   >> RW_TAC list_ss []
   >> Reverse (Suff `((l = []) \/ (l = [[]])) \/ ?l1 l2.
            prob_canonical l1 /\ prob_canonical l2 /\
            (l = APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))`)
     >- (POP_ASSUM (MP_TAC
                    o MP (SPEC ``l:bool list list`` PROB_CANONICAL_CASES_THM))
         >> PROVE_TAC [])
   >> DISCH_THEN DISJ_CASES_TAC >- PROVE_TAC []
   >> POP_ASSUM MP_TAC
   >> STRIP_TAC
   >> Suff `P (l1:bool list list) /\ P l2` >- PROVE_TAC []
   >> CONJ_TAC >|
   [Cases_on `l1` >- PROVE_TAC []
    >> Suff `prob_longest (h::t) < prob_longest l` >- PROVE_TAC []
    >> POP_ASSUM MP_TAC
    >> KILL_TAC
    >> MP_TAC (SPECL [``MAP (CONS T) (h::t)``, ``MAP (CONS F) l2``]
                 PROB_LONGEST_APPEND)
    >> RW_TAC arith_ss [PROB_LONGEST_TLS],
    Cases_on `l2` >- PROVE_TAC []
    >> Suff `prob_longest (h::t) < prob_longest l` >- PROVE_TAC []
    >> POP_ASSUM MP_TAC
    >> KILL_TAC
    >> MP_TAC (SPECL [``MAP (CONS T) l1``, ``MAP (CONS F) (h::t)``]
                 PROB_LONGEST_APPEND)
    >> RW_TAC arith_ss [PROB_LONGEST_TLS]]);

val MEM_NIL_STEP = store_thm
  ("MEM_NIL_STEP",
   ``!l1 l2. ~MEM [] (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))``,
   RW_TAC list_ss [APPEND_MEM, MEM_NIL_MAP_CONS]);

val PROB_SORTED_PREFIXFREE_MEM_NIL = store_thm
  ("PROB_SORTED_PREFIXFREE_MEM_NIL",
   ``!l. prob_sorted l /\ prob_prefixfree l /\ MEM [] l = (l = [[]])``,
   Induct >- RW_TAC list_ss [MEM]
   >> STRIP_TAC
   >> Reverse EQ_TAC
     >- RW_TAC std_ss [prob_prefixfree_def, prob_sorted_def, MEM]
   >> Cases_on `l` >- RW_TAC list_ss [MEM]
   >> ONCE_REWRITE_TAC [MEM]
   >> RW_TAC std_ss [prob_prefixfree_def, prob_sorted_def]
   >> Cases_on `h` >- RW_TAC list_ss [MEM, prob_order_def, IS_PREFIX]
   >> Cases_on `h'` >- RW_TAC list_ss [MEM, prob_order_def]
   >> RW_TAC list_ss [] >|
   [RW_TAC list_ss [],
    RW_TAC list_ss [],
    RW_TAC list_ss []]);

val PROB_SORTED_PREFIXFREE_EQUALITY = store_thm
  ("PROB_SORTED_PREFIXFREE_EQUALITY",
   ``!l l'. (!x. MEM x l = MEM x l') /\ prob_sorted l /\ prob_sorted l'
            /\ prob_prefixfree l /\ prob_prefixfree l'
            ==> (l = l')``,
   Induct >- RW_TAC list_ss [MEM, MEM_NIL]
   >> STRIP_TAC
   >> Cases >- (RW_TAC std_ss [MEM, MEM_NIL] >> PROVE_TAC [])
   >> REPEAT STRIP_TAC
   >> Know `h = h'` >|
   [Suff `prob_order h h' /\ prob_order h' h` >- PROVE_TAC [PROB_ORDER_ANTISYM]
    >> CONJ_TAC >|
    [Know `MEM h' (h::l)` >- PROVE_TAC [MEM]
     >> REWRITE_TAC [MEM]
     >> RW_TAC std_ss [] >- PROVE_TAC [PROB_ORDER_REFL]
     >> Q.PAT_X_ASSUM `prob_sorted (h::l)` MP_TAC
     >> RW_TAC std_ss [PROB_SORTED_DEF_ALT],
     Know `MEM h (h'::t)` >- PROVE_TAC [MEM]
     >> REWRITE_TAC [MEM]
     >> RW_TAC std_ss [] >- PROVE_TAC [PROB_ORDER_REFL]
     >> Q.PAT_X_ASSUM `prob_sorted (h'::t)` MP_TAC
     >> RW_TAC std_ss [PROB_SORTED_DEF_ALT]],
    RW_TAC std_ss []
    >> Q.PAT_X_ASSUM `!l'. P l' ==> Q l'` MATCH_MP_TAC
    >> Reverse CONJ_TAC >- PROVE_TAC [PROB_SORTED_TL, PROB_PREFIXFREE_TL]
    >> RW_TAC std_ss []
    >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
    >> REWRITE_TAC [MEM]
    >> Reverse (Cases_on `x = h`) >- RW_TAC std_ss []
    >> RW_TAC std_ss []
    >> ASSUME_TAC PROB_PREFIXFREE_ELT
    >> RES_TAC
    >> NTAC 2 (POP_ASSUM (MP_TAC o Q.SPEC `h`))
    >> NTAC 3 (POP_ASSUM (K ALL_TAC))
    >> RW_TAC std_ss [IS_PREFIX_REFL]]);

val PROB_CANONICAL_PREFIXFREE = store_thm
  ("PROB_CANONICAL_PREFIXFREE",
   ``!l a b.
       prob_canonical l /\ MEM a l /\ MEM b l /\ IS_PREFIX a b ==> (a = b)``,
   Induct >- RW_TAC std_ss [MEM]
   >> RW_TAC std_ss [MEM] >|
   [Know `prob_sorted (a::l) /\ prob_prefixfree (a::l)`
    >- PROVE_TAC [prob_canonical_def, PROB_CANON_SORTED_PREFIXFREE_TWINFREE]
    >> RW_TAC std_ss []
    >> MP_TAC (Q.SPECL [`a`, `l`] PROB_PREFIXFREE_ELT)
    >> RW_TAC std_ss []
    >> RES_TAC,
    Know `prob_sorted (b::l) /\ prob_prefixfree (b::l)`
    >- PROVE_TAC [prob_canonical_def, PROB_CANON_SORTED_PREFIXFREE_TWINFREE]
    >> RW_TAC std_ss []
    >> MP_TAC (Q.SPECL [`b`, `l`] PROB_PREFIXFREE_ELT)
    >> RW_TAC std_ss []
    >> RES_TAC,
    PROVE_TAC [PROB_CANONICAL_TL]]);

val _ = export_theory ();
