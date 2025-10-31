Theory prob_canon
Ancestors
  pred_set list rich_list pair extra_list
Libs
  realLib hurdUtils

val _ = ParseExtras.temp_loose_equality()

(* ------------------------------------------------------------------------- *)
(* Definition of the canonicalisation of algebra elements.                   *)
(* ------------------------------------------------------------------------- *)

Definition prob_twin_def:
   prob_twin x y = ?l. (x = SNOC T l) /\ (y = SNOC F l)
End

Definition prob_order_def:
   (prob_order [] _ = T) /\
   (prob_order _ [] = F) /\
   (prob_order (h :: t) (h' :: t') =
    ((h = T) /\ (h' = F)) \/ ((h = h') /\ prob_order t t'))
End

Definition prob_sorted_def:   (prob_sorted (x :: y :: z)
      = prob_order x y /\ prob_sorted (y :: z))
  /\ (prob_sorted l = T)
End

Definition prob_prefixfree_def:   (prob_prefixfree ((x:bool list)::y::z)
      = ~IS_PREFIX y x /\ prob_prefixfree (y::z))
  /\ (prob_prefixfree l = T)
End

Definition prob_twinfree_def:   (prob_twinfree (x::y::z)
      = ~(prob_twin x y) /\ prob_twinfree (y::z))
  /\ (prob_twinfree l = T)
End

Definition prob_longest_def:   prob_longest
  = FOLDR (\h t. if t <= LENGTH (h:bool list) then LENGTH h else t) 0
End

Definition prob_canon_prefs_def:   (prob_canon_prefs (l:bool list) [] = [l])
  /\ (prob_canon_prefs l (h::t) = if IS_PREFIX h l then prob_canon_prefs l t
                                 else l::h::t)
End

Definition prob_canon_find_def:   (prob_canon_find l [] = [l])
  /\ (prob_canon_find l (h::t) = if prob_order h l then
          if IS_PREFIX l h then (h::t) else h::(prob_canon_find l t)
        else prob_canon_prefs l (h::t))
End

Definition prob_canon1_def:   prob_canon1 = FOLDR prob_canon_find []
End

Definition prob_canon_merge_def:   (prob_canon_merge l [] = [l])
  /\ (prob_canon_merge l (h::t)
      = if prob_twin l h then prob_canon_merge (BUTLAST h) t else l::h::t)
End

Definition prob_canon2_def:   prob_canon2 = FOLDR prob_canon_merge []
End

Definition prob_canon_def:   prob_canon l = prob_canon2 (prob_canon1 l)
End

Definition prob_canonical_def:   prob_canonical l = (prob_canon l = l)
End

(* ------------------------------------------------------------------------- *)
(* Theorems leading to:                                                      *)
(* 1. Canonical form is the same as sorted, prefixfree and twinfree.         *)
(* 2. Induction principle on elements in canonical form.                     *)
(* ------------------------------------------------------------------------- *)

Theorem PROB_TWIN_NIL:
  !l. ~prob_twin l [] /\ ~prob_twin [] l
Proof rw[prob_twin_def]
QED

Theorem PROB_TWIN_SING:
     !x l. (prob_twin [x] l = (x = T) /\ (l = [F]))
           /\ (prob_twin l [x] = (l = [T]) /\ (x = F))
Proof
   RW_TAC std_ss [prob_twin_def] >|
   [EQ_TAC >|
    [Cases_on `l` >- PROVE_TAC [NOT_NIL_SNOC]
     >> DISCH_THEN (Q.X_CHOOSE_THEN `l` STRIP_ASSUME_TAC)
     >> NTAC 2 (POP_ASSUM MP_TAC)
     >> reverse (Cases_on `l`) >- RW_TAC std_ss [SNOC, NOT_NIL_SNOC]
     >> RW_TAC std_ss [SNOC],
     RW_TAC std_ss []
     >> Q.EXISTS_TAC `[]`
     >> RW_TAC std_ss [SNOC]],
    EQ_TAC >|
    [Cases_on `l` >- PROVE_TAC [NOT_NIL_SNOC]
     >> DISCH_THEN (Q.X_CHOOSE_THEN `l` STRIP_ASSUME_TAC)
     >> NTAC 2 (POP_ASSUM MP_TAC)
     >> reverse (Cases_on `l`) >- RW_TAC std_ss [SNOC, NOT_NIL_SNOC]
     >> RW_TAC std_ss [SNOC],
     RW_TAC std_ss []
     >> Q.EXISTS_TAC `[]`
     >> RW_TAC std_ss [SNOC]]]
QED

Theorem PROB_TWIN_CONS:
     !x y z h t. (prob_twin (x::y::z) (h::t) = (x = h) /\ prob_twin (y::z) t)
              /\ (prob_twin (h::t) (x::y::z) = (x = h) /\ prob_twin t (y::z))
Proof
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
     >> RW_TAC std_ss [SNOC]]]
QED

Theorem PROB_TWIN_REDUCE:
     !h t t'. prob_twin (h::t) (h::t') = prob_twin t t'
Proof
   Cases_on `t`
   >> RW_TAC std_ss [PROB_TWIN_CONS, PROB_TWIN_SING, PROB_TWIN_NIL]
   >> PROVE_TAC []
QED

Theorem PROB_TWINS_PREFIX:
     !x l. IS_PREFIX x l
           ==> (x = l) \/ IS_PREFIX x (SNOC T l) \/ IS_PREFIX x (SNOC F l)
Proof
   Induct_on `x` >- RW_TAC list_ss [IS_PREFIX_NIL]
   >> Cases_on `l` >- RW_TAC list_ss [SNOC, IS_PREFIX]
   >> RW_TAC list_ss [IS_PREFIX, SNOC]
QED

Theorem PROB_ORDER_NIL:
     !x. prob_order [] x /\ (prob_order x [] = (x = []))
Proof
   Induct >- RW_TAC list_ss [prob_order_def]
   >> RW_TAC list_ss [prob_order_def]
QED

Theorem PROB_ORDER_REFL:
     !x. prob_order x x
Proof
   Induct >- RW_TAC list_ss [prob_order_def]
   >> RW_TAC list_ss [prob_order_def]
QED

Theorem PROB_ORDER_ANTISYM:
     !x y. prob_order x y /\ prob_order y x ==> (x = y)
Proof
   Induct >- (Cases >> RW_TAC list_ss [prob_order_def])
   >> STRIP_TAC
   >> Cases >- RW_TAC list_ss [prob_order_def]
   >> (RW_TAC std_ss [prob_order_def] >> PROVE_TAC [])
QED

Theorem PROB_ORDER_TRANS:
     !x y z. prob_order x y /\ prob_order y z ==> prob_order x z
Proof
   Induct >- (Cases_on `z` >> RW_TAC list_ss [prob_order_def])
   >> STRIP_TAC
   >> Cases >- RW_TAC list_ss [prob_order_def]
   >> Cases >- RW_TAC list_ss [prob_order_def]
   >> (RW_TAC list_ss [prob_order_def] >> PROVE_TAC [])
QED

Theorem PROB_ORDER_TOTAL:
     !x y. prob_order x y \/ prob_order y x
Proof
   Induct >- PROVE_TAC [PROB_ORDER_NIL]
   >> Cases_on `y` >- PROVE_TAC [PROB_ORDER_NIL]
   >> RW_TAC list_ss [prob_order_def]
   >> PROVE_TAC []
QED

Theorem PROB_ORDER_PREFIX:
     !x y. IS_PREFIX y x ==> prob_order x y
Proof
   Induct >- (Cases >> RW_TAC list_ss [prob_order_def])
   >> Cases_on `y` >- RW_TAC list_ss [IS_PREFIX_NIL]
   >> RW_TAC list_ss [IS_PREFIX, prob_order_def]
QED

Theorem PROB_ORDER_PREFIX_ANTI:
     !x y. prob_order x y /\ IS_PREFIX x y ==> (x = y)
Proof
   Induct >- RW_TAC list_ss [IS_PREFIX_NIL]
   >> Cases_on `y` >- RW_TAC list_ss [IS_PREFIX_NIL, prob_order_def]
   >> (RW_TAC list_ss [IS_PREFIX, prob_order_def]
         >> PROVE_TAC [])
QED

Theorem PROB_ORDER_PREFIX_MONO:
     !x y z. prob_order x y /\ prob_order y z /\ IS_PREFIX z x
             ==> IS_PREFIX y x
Proof
   Induct >- RW_TAC list_ss [IS_PREFIX]
   >> Cases_on `y` >- RW_TAC list_ss [prob_order_def]
   >> Cases_on `z` >- RW_TAC list_ss [IS_PREFIX_NIL]
   >> (RW_TAC list_ss [prob_order_def, IS_PREFIX]
         >> PROVE_TAC [])
QED

Theorem PROB_ORDER_PREFIX_TRANS:
     !x y z. prob_order x y /\ IS_PREFIX y z
             ==> prob_order x z \/ IS_PREFIX x z
Proof
   Induct >- (Cases_on `z` >> RW_TAC list_ss [prob_order_def])
   >> Cases_on `y` >- RW_TAC list_ss [PROB_ORDER_NIL]
   >> Cases_on `z` >- RW_TAC list_ss [IS_PREFIX]
   >> (RW_TAC list_ss [prob_order_def, IS_PREFIX] >> PROVE_TAC [])
QED

Theorem PROB_ORDER_SNOC:
     !x l. ~prob_order (SNOC x l) l
Proof
   Induct_on `l` >- RW_TAC std_ss [prob_order_def, SNOC]
   >> RW_TAC std_ss [prob_order_def, SNOC]
QED

Theorem PROB_SORTED_MIN:
     !h t. prob_sorted (h::t) ==> (!x. MEM x t ==> prob_order h x)
Proof
   Induct_on `t` >- RW_TAC list_ss [MEM]
   >> RW_TAC list_ss [prob_sorted_def, MEM] >- PROVE_TAC []
   >> Know `prob_order h x` >- PROVE_TAC []
   >> PROVE_TAC [PROB_ORDER_TRANS]
QED

Theorem PROB_SORTED_DEF_ALT:
     !h t. prob_sorted (h::t)
           = (!x. MEM x t ==> prob_order h x) /\ prob_sorted t
Proof
   REPEAT STRIP_TAC
   >> EQ_TAC
     >- (Cases_on `t` >> PROVE_TAC [PROB_SORTED_MIN, prob_sorted_def])
   >> Cases_on `t` >- RW_TAC list_ss [prob_sorted_def]
   >> RW_TAC list_ss [prob_sorted_def]
   >> PROVE_TAC [MEM]
QED

Theorem PROB_SORTED_TL:
     !h t. prob_sorted (h::t) ==> prob_sorted t
Proof
   PROVE_TAC [PROB_SORTED_DEF_ALT]
QED

Theorem PROB_SORTED_MONO:
     !x y z. prob_sorted (x::y::z) ==> prob_sorted (x::z)
Proof
   RW_TAC list_ss [PROB_SORTED_DEF_ALT, MEM]
QED

Theorem PROB_SORTED_TLS:
     !l b. prob_sorted (MAP (CONS b) l) = prob_sorted l
Proof
   Induct >- RW_TAC list_ss [MAP]
   >> Cases_on `l` >- RW_TAC list_ss [MAP, prob_sorted_def]
   >> RW_TAC list_ss [prob_sorted_def, prob_order_def]
   >> PROVE_TAC [MAP]
QED

Theorem PROB_SORTED_STEP:
     !l1 l2. prob_sorted (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
             = prob_sorted l1 /\ prob_sorted l2
Proof
   NTAC 2 STRIP_TAC
   >> Induct_on `l1` >- RW_TAC list_ss [MAP, PROB_SORTED_TLS, prob_sorted_def]
   >> STRIP_TAC
   >> POP_ASSUM MP_TAC
   >> Cases_on `l1` >|
   [Cases_on `l2` >- RW_TAC list_ss [MAP, prob_sorted_def]
    >> RW_TAC list_ss [MAP, prob_sorted_def, prob_order_def],
    RW_TAC list_ss [prob_sorted_def, prob_order_def]
    >> PROVE_TAC []]
QED

Theorem PROB_SORTED_APPEND:
     !h h' t t'. prob_sorted (APPEND (h::t) (h'::t'))
                 = prob_sorted (h::t) /\ prob_sorted (h'::t')
                   /\ prob_order (LAST (h::t)) h'
Proof
   Induct_on `t`
     >- (RW_TAC list_ss [prob_sorted_def, LAST_CONS]
         >> PROVE_TAC [])
   >> RW_TAC list_ss [prob_sorted_def]
   >> RW_TAC std_ss [(GSYM o CONJUNCT2) APPEND, LAST_CONS]
   >> PROVE_TAC []
QED

Theorem PROB_SORTED_FILTER:
     !P b. prob_sorted b ==> prob_sorted (FILTER P b)
Proof
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [FILTER]
   >> RW_TAC list_ss [PROB_SORTED_DEF_ALT, FILTER]
   >> PROVE_TAC [MEM_FILTER]
QED

Theorem PROB_PREFIXFREE_TL:
     !h t. prob_prefixfree (h::t) ==> prob_prefixfree t
Proof
   STRIP_TAC
   >> (Cases >> RW_TAC list_ss [prob_prefixfree_def])
QED

Theorem PROB_PREFIXFREE_MONO:
     !x y z. prob_sorted (x::y::z) /\ prob_prefixfree (x::y::z)
             ==> prob_prefixfree (x::z)
Proof
   Cases_on `z` >- RW_TAC list_ss [prob_prefixfree_def]
   >> RW_TAC list_ss [prob_prefixfree_def, prob_sorted_def]
   >> PROVE_TAC [PROB_ORDER_PREFIX_MONO]
QED

Theorem PROB_PREFIXFREE_ELT:
     !h t. prob_sorted (h::t) /\ prob_prefixfree (h::t)
         ==> (!x. MEM x t ==> ~IS_PREFIX x h /\ ~IS_PREFIX h x)
Proof
   Induct_on `t` >- RW_TAC list_ss [MEM]
   >> ONCE_REWRITE_TAC [MEM]
   >> NTAC 5 STRIP_TAC >|
   [CONJ_TAC >- PROVE_TAC [prob_prefixfree_def]
    >> Know `prob_order h' h` >- PROVE_TAC [prob_sorted_def]
    >> PROVE_TAC [PROB_ORDER_PREFIX_ANTI, IS_PREFIX_REFL, prob_prefixfree_def],
    Suff `prob_sorted (h'::t) /\ prob_prefixfree (h'::t)`
      >- PROVE_TAC []
    >> PROVE_TAC [PROB_SORTED_MONO, PROB_PREFIXFREE_MONO]]
QED

Theorem PROB_PREFIXFREE_TLS:
     !l b. prob_prefixfree (MAP (CONS b) l) = prob_prefixfree l
Proof
   Induct >- RW_TAC list_ss [MAP]
   >> Cases_on `l` >- RW_TAC list_ss [MAP, prob_prefixfree_def]
   >> RW_TAC list_ss [prob_prefixfree_def, IS_PREFIX]
   >> PROVE_TAC [MAP]
QED

Theorem PROB_PREFIXFREE_STEP:
     !l1 l2. prob_prefixfree (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
             = prob_prefixfree l1 /\ prob_prefixfree l2
Proof
   NTAC 2 STRIP_TAC
   >> Induct_on `l1`
   >- RW_TAC list_ss [MAP, PROB_PREFIXFREE_TLS, prob_prefixfree_def]
   >> STRIP_TAC
   >> POP_ASSUM MP_TAC
   >> Cases_on `l1` >|
   [Cases_on `l2` >- RW_TAC list_ss [MAP, prob_prefixfree_def]
    >> RW_TAC list_ss [MAP, prob_prefixfree_def, IS_PREFIX],
    RW_TAC list_ss [prob_prefixfree_def, IS_PREFIX]
    >> PROVE_TAC []]
QED

Theorem PROB_PREFIXFREE_APPEND:
     !h h' t t'. prob_prefixfree (APPEND (h::t) (h'::t'))
                 = prob_prefixfree (h::t) /\ prob_prefixfree (h'::t')
                   /\ ~IS_PREFIX h' (LAST (h::t))
Proof
   Induct_on `t`
     >- (RW_TAC list_ss [prob_prefixfree_def, LAST_CONS]
         >> PROVE_TAC [])
   >> RW_TAC list_ss [prob_prefixfree_def]
   >> RW_TAC std_ss [(GSYM o CONJUNCT2) APPEND, LAST_CONS]
   >> PROVE_TAC []
QED

Theorem PROB_PREFIXFREE_FILTER:
     !P b. prob_sorted b /\ prob_prefixfree b ==> prob_prefixfree (FILTER P b)
Proof
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [FILTER]
   >> NTAC 2 STRIP_TAC
   >> Know `prob_prefixfree (FILTER P b)`
     >- PROVE_TAC [PROB_SORTED_TL, PROB_PREFIXFREE_TL]
   >> RW_TAC list_ss [FILTER]
   >> Cases_on `FILTER P b` >- RW_TAC list_ss [prob_prefixfree_def]
   >> RW_TAC list_ss [prob_prefixfree_def]
   >> Know `MEM (h':bool list) b` >- PROVE_TAC [MEM_FILTER, MEM]
   >> PROVE_TAC [PROB_PREFIXFREE_ELT]
QED

Theorem PROB_TWINFREE_TL:
     !h t. prob_twinfree (h::t) ==> prob_twinfree t
Proof
   Cases_on `t` >> RW_TAC list_ss [prob_twinfree_def]
QED

Theorem PROB_TWINFREE_TLS:
     !l b. prob_twinfree (MAP (CONS b) l) = prob_twinfree l
Proof
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
    >> RW_TAC std_ss [SNOC]]
QED

Theorem PROB_TWINFREE_STEP1:
     !l1 l2. prob_twinfree (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
             ==> prob_twinfree l1 /\ prob_twinfree l2
Proof
   NTAC 2 STRIP_TAC
   >> Induct_on `l1`
   >- RW_TAC list_ss [MAP, PROB_TWINFREE_TLS, prob_twinfree_def]
   >> STRIP_TAC
   >> POP_ASSUM MP_TAC
   >> Cases_on `l1` >|
   [Cases_on `l2` >- RW_TAC list_ss [MAP, prob_twinfree_def]
    >> RW_TAC list_ss [MEM, MAP, prob_twinfree_def],
    RW_TAC list_ss [prob_twinfree_def, PROB_TWIN_REDUCE, MEM]]
QED

Theorem PROB_TWINFREE_STEP2:
  !l1 l2. (~MEM [] l1 \/ ~MEM [] l2) /\
          prob_twinfree l1 /\ prob_twinfree l2
          ==> prob_twinfree (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
Proof
   NTAC 2 STRIP_TAC
   >> Induct_on `l1`
   >- RW_TAC list_ss [MAP, PROB_TWINFREE_TLS, prob_twinfree_def]
   >> STRIP_TAC
   >> POP_ASSUM MP_TAC
   >> Cases_on `l1` >| [
    Cases_on `l2` >- RW_TAC list_ss [MAP, prob_twinfree_def]
    >> RW_TAC list_ss [MEM, MAP, prob_twinfree_def]
    >> Cases_on ‘h’ >> fs[PROB_TWIN_CONS]
    >> Cases_on `h'` >> fs[PROB_TWIN_CONS],
    RW_TAC list_ss [prob_twinfree_def, PROB_TWIN_REDUCE, MEM]
    >> RES_TAC
  ]
QED

Theorem PROB_TWINFREE_STEP:
     !l1 l2. ~(MEM [] l1) \/ ~(MEM [] l2)
             ==> (prob_twinfree (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
                  = prob_twinfree l1 /\ prob_twinfree l2)
Proof
   PROVE_TAC [PROB_TWINFREE_STEP1, PROB_TWINFREE_STEP2]
QED

Theorem PROB_LONGEST_HD:
     !h t. LENGTH h <= prob_longest (h::t)
Proof
   Induct_on `t` >- RW_TAC arith_ss [prob_longest_def, FOLDR]
   >> RW_TAC arith_ss [prob_longest_def, FOLDR]
QED

Theorem PROB_LONGEST_TL:
     !h t. prob_longest t <= prob_longest (h::t)
Proof
   Induct_on `t` >- RW_TAC arith_ss [prob_longest_def, FOLDR]
   >> RW_TAC arith_ss [prob_longest_def, FOLDR]
QED

Theorem PROB_LONGEST_TLS:
     !h t b. prob_longest (MAP (CONS b) (h::t)) = SUC (prob_longest (h::t))
Proof
   Induct_on `t`
     >- RW_TAC arith_ss [prob_longest_def, FOLDR_MAP, FOLDR, LENGTH]
   >> RW_TAC arith_ss [prob_longest_def]
   >> ONCE_REWRITE_TAC [MAP]
   >> ONCE_REWRITE_TAC [FOLDR]
   >> REWRITE_TAC [GSYM prob_longest_def]
   >> RW_TAC arith_ss [LENGTH]
QED

Theorem PROB_LONGEST_APPEND:
     !l1 l2. prob_longest l1 <= prob_longest (APPEND l1 l2)
             /\ prob_longest l2 <= prob_longest (APPEND l1 l2)
Proof
   NTAC 2 STRIP_TAC
   >> Induct_on `l1` >- RW_TAC arith_ss [APPEND, prob_longest_def, FOLDR]
   >> REWRITE_TAC [APPEND, prob_longest_def, FOLDR]
   >> REWRITE_TAC [GSYM prob_longest_def]
   >> RW_TAC arith_ss []
QED

Theorem PROB_CANON_PREFS_HD:
     !l b. HD (prob_canon_prefs l b) = l
Proof
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_prefs_def]
   >> RW_TAC list_ss [prob_canon_prefs_def]
QED

Theorem PROB_CANON_PREFS_DELETES:
     !l b x. MEM x (prob_canon_prefs l b) ==> MEM x (l::b)
Proof
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_prefs_def]
   >> RW_TAC list_ss [prob_canon_prefs_def]
   >> RES_TAC
   >> POP_ASSUM MP_TAC
   >> KILL_TAC
   >> RW_TAC list_ss [MEM]
   >> PROVE_TAC []
QED

Theorem PROB_CANON_PREFS_SORTED:
     !l b. prob_sorted (l::b) ==> prob_sorted (prob_canon_prefs l b)
Proof
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_prefs_def]
   >> RW_TAC list_ss [prob_canon_prefs_def]
   >> PROVE_TAC [PROB_SORTED_MONO]
QED

Theorem PROB_CANON_PREFS_PREFIXFREE:
     !l b. prob_sorted b /\ prob_prefixfree b
           ==> prob_prefixfree (prob_canon_prefs l b)
Proof
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_prefs_def, prob_prefixfree_def]
   >> RW_TAC list_ss [prob_canon_prefs_def, prob_prefixfree_def]
   >> PROVE_TAC [PROB_SORTED_TL, PROB_PREFIXFREE_TL]
QED

Theorem PROB_CANON_PREFS_CONSTANT:
     !l b. prob_prefixfree (l::b)
           ==> (prob_canon_prefs l b = l::b)
Proof
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_prefixfree_def, prob_canon_prefs_def]
   >> RW_TAC list_ss [prob_prefixfree_def, prob_canon_prefs_def]
QED

Theorem PROB_CANON_FIND_HD:
     !l h t. (HD (prob_canon_find l (h::t)) = l)
             \/ (HD (prob_canon_find l (h::t)) = h)
Proof
   Induct_on `t` >- RW_TAC list_ss [prob_canon_find_def, PROB_CANON_PREFS_HD]
   >> RW_TAC list_ss [prob_canon_find_def, PROB_CANON_PREFS_HD]
QED

Theorem PROB_CANON_FIND_DELETES:
     !l b x. MEM x (prob_canon_find l b) ==> MEM x (l::b)
Proof
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_find_def]
   >> RW_TAC list_ss [prob_canon_find_def, MEM] >-
   (PROVE_TAC [MEM]) >-
   (PROVE_TAC [MEM, PROB_CANON_PREFS_DELETES])
QED

Theorem PROB_CANON_FIND_SORTED:
     !l b. prob_sorted b ==> prob_sorted (prob_canon_find l b)
Proof
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_find_def, prob_sorted_def]
   >> RW_TAC list_ss [prob_canon_find_def] >-
   (POP_ASSUM MP_TAC
    >> RW_TAC list_ss [PROB_SORTED_DEF_ALT]
    >> PROVE_TAC [PROB_CANON_FIND_DELETES, MEM]) >-
   (Suff `prob_sorted (l::h::b)` >- PROVE_TAC [PROB_CANON_PREFS_SORTED]
    >> REWRITE_TAC [prob_sorted_def]
    >> PROVE_TAC [PROB_ORDER_TOTAL])
QED

Theorem PROB_CANON_FIND_PREFIXFREE:
     !l b. prob_sorted b /\ prob_prefixfree b
           ==> prob_prefixfree (prob_canon_find l b)
Proof
   STRIP_TAC
   >> Induct >- RW_TAC list_ss [prob_canon_find_def, prob_prefixfree_def]
   >> RW_TAC list_ss [prob_canon_find_def] >|
   [Cases_on `b` >- RW_TAC list_ss [prob_prefixfree_def, prob_canon_find_def]
    >> Cases_on `prob_canon_find l (h'::t)`
      >- RW_TAC list_ss [prob_prefixfree_def, prob_canon_find_def]
    >> reverse (RW_TAC list_ss [prob_prefixfree_def])
      >- PROVE_TAC [PROB_SORTED_TL, PROB_PREFIXFREE_TL]
    >> Suff `(h'' = h') \/ (h'' = (l:bool list))`
      >- PROVE_TAC [prob_prefixfree_def]
    >> POP_ASSUM MP_TAC
    >> KILL_TAC
    >> PROVE_TAC [PROB_CANON_FIND_HD, HD],
    PROVE_TAC [PROB_CANON_PREFS_PREFIXFREE]]
QED

Theorem PROB_CANON_FIND_CONSTANT:
     !l b. prob_sorted (l::b) /\ prob_prefixfree (l::b)
           ==> (prob_canon_find l b = l::b)
Proof
   STRIP_TAC
   >> Cases >- RW_TAC list_ss [prob_canon_find_def]
   >> STRIP_TAC
   >> Know `~((l:bool list) = h)`
     >- PROVE_TAC [prob_prefixfree_def, IS_PREFIX_REFL]
   >> (RW_TAC list_ss [prob_canon_find_def, PROB_CANON_PREFS_CONSTANT]
         >> PROVE_TAC [prob_sorted_def, PROB_ORDER_ANTISYM])
QED

Theorem PROB_CANON1_SORTED:
     !l. prob_sorted (prob_canon1 l)
Proof
   REWRITE_TAC [prob_canon1_def]
   >> Induct >- RW_TAC list_ss [FOLDR, prob_sorted_def]
   >> RW_TAC list_ss [PROB_CANON_FIND_SORTED, FOLDR]
QED

Theorem PROB_CANON1_PREFIXFREE:
     !l. prob_prefixfree (prob_canon1 l)
Proof
   Induct >- RW_TAC list_ss [prob_prefixfree_def, prob_canon1_def, FOLDR]
   >> RW_TAC list_ss [prob_canon1_def, FOLDR]
   >> RW_TAC list_ss [GSYM prob_canon1_def]
   >> Know `prob_sorted (prob_canon1 l)` >- PROVE_TAC [PROB_CANON1_SORTED]
   >> PROVE_TAC [PROB_CANON_FIND_PREFIXFREE]
QED

Theorem PROB_CANON1_CONSTANT:
     !l. prob_sorted l /\ prob_prefixfree l ==> (prob_canon1 l = l)
Proof
   RW_TAC list_ss [prob_canon1_def]
   >> Induct_on `l` >- RW_TAC list_ss [FOLDR]
   >> RW_TAC list_ss [FOLDR]
   >> PROVE_TAC [PROB_CANON_FIND_CONSTANT, PROB_SORTED_TL, PROB_PREFIXFREE_TL]
QED

Theorem PROB_CANON_MERGE_SORTED_PREFIXFREE_TWINFREE:
     !l b. prob_sorted (l::b) /\ prob_prefixfree (l::b) /\ prob_twinfree b
           ==> prob_sorted (prob_canon_merge l b)
               /\ prob_prefixfree (prob_canon_merge l b)
               /\ prob_twinfree (prob_canon_merge l b)
Proof
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
     RW_TAC std_ss [BUTLAST])
QED

Theorem PROB_CANON_MERGE_PREFIXFREE_PRESERVE:
     !l b h. (!x. MEM x (l::b) ==> ~IS_PREFIX h x /\ ~IS_PREFIX x h)
           ==> (!x. MEM x (prob_canon_merge l b)
                    ==> ~IS_PREFIX h x /\ ~IS_PREFIX x h)
Proof
   Induct_on `b` >- RW_TAC std_ss [MEM, prob_canon_merge_def, IS_PREFIX]
   >> REWRITE_TAC [prob_canon_merge_def]
   >> NTAC 5 STRIP_TAC
   >> reverse (Cases_on `prob_twin l h`) >- ASM_REWRITE_TAC []
   >> ASM_REWRITE_TAC []
   >> POP_ASSUM MP_TAC
   >> REWRITE_TAC [prob_twin_def]
   >> NTAC 2 STRIP_TAC
   >> Suff `!x. MEM x (BUTLAST h::b)
                ==> ~IS_PREFIX h' x /\ ~IS_PREFIX x h'`
     >- PROVE_TAC []
   >> REWRITE_TAC [MEM]
   >> reverse (NTAC 2 STRIP_TAC) >- PROVE_TAC [MEM]
   >> ASM_REWRITE_TAC [BUTLAST]
   >> reverse (Suff `~IS_PREFIX h' l /\ ~IS_PREFIX l h'
                            /\ ~IS_PREFIX h' h /\ ~IS_PREFIX h h'`)
   >- PROVE_TAC [MEM]
   >> ASM_REWRITE_TAC []
   >> KILL_TAC
   >> RW_TAC std_ss [IS_PREFIX_SNOC]
   >> PROVE_TAC [PROB_TWINS_PREFIX]
QED

Theorem PROB_CANON_MERGE_SHORTENS:
     !l b x. MEM x (prob_canon_merge l b)
             ==> (?y. MEM y (l::b) /\ IS_PREFIX y x)
Proof
   Induct_on `b` >- RW_TAC std_ss [prob_canon_merge_def, MEM, IS_PREFIX_REFL]
   >> reverse (RW_TAC std_ss [prob_canon_merge_def, prob_twin_def])
   >- PROVE_TAC [IS_PREFIX_REFL]
   >> Q.PAT_X_ASSUM `!l. P l` (MP_TAC o Q.SPECL [`l'`, `x`])
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [BUTLAST, MEM] >|
   [Q.EXISTS_TAC `SNOC F l'`
    >> RW_TAC std_ss [IS_PREFIX_SNOC],
    PROVE_TAC []]
QED

Theorem PROB_CANON_MERGE_CONSTANT:
     !l b. prob_twinfree (l::b) ==> (prob_canon_merge l b = l::b)
Proof
   STRIP_TAC
   >> Cases >- RW_TAC list_ss [prob_canon_merge_def]
   >> RW_TAC list_ss [prob_twinfree_def, prob_canon_merge_def, PROB_TWIN_NIL]
QED

Theorem PROB_CANON2_PREFIXFREE_PRESERVE:
     !l h. (!x. MEM x l ==> ~IS_PREFIX h x /\ ~IS_PREFIX x h)
           ==> (!x. MEM x (prob_canon2 l)
                    ==> ~IS_PREFIX h x /\ ~IS_PREFIX x h)
Proof
   REWRITE_TAC [prob_canon2_def]
   >> NTAC 2 STRIP_TAC
   >> Induct_on `l` >- RW_TAC list_ss [FOLDR, MEM]
   >> REWRITE_TAC [FOLDR, MEM]
   >> NTAC 2 STRIP_TAC
   >> Suff `!x. MEM x (h'::FOLDR prob_canon_merge [] l)
                       ==> ~IS_PREFIX h x /\ ~IS_PREFIX x h`
     >- PROVE_TAC [PROB_CANON_MERGE_PREFIXFREE_PRESERVE]
   >> REWRITE_TAC [MEM]
   >> PROVE_TAC []
QED

Theorem PROB_CANON2_SHORTENS:
     !l x. MEM x (prob_canon2 l) ==> ?y. MEM y l /\ IS_PREFIX y x
Proof
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
   >> PROVE_TAC [IS_PREFIX_TRANS]
QED

Theorem PROB_CANON2_SORTED_PREFIXFREE_TWINFREE:
     !l. prob_sorted l /\ prob_prefixfree l
         ==> prob_sorted (prob_canon2 l)
             /\ prob_prefixfree (prob_canon2 l)
             /\ prob_twinfree (prob_canon2 l)
Proof
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
   >> PROVE_TAC [PROB_ORDER_PREFIX_TRANS]
QED

Theorem PROB_CANON2_CONSTANT:
     !l. prob_twinfree l ==> (prob_canon2 l = l)
Proof
   RW_TAC list_ss [prob_canon2_def]
   >> Induct_on `l` >- RW_TAC list_ss [FOLDR]
   >> RW_TAC list_ss [FOLDR]
   >> PROVE_TAC [PROB_CANON_MERGE_CONSTANT, PROB_TWINFREE_TL]
QED

Theorem PROB_CANON_SORTED_PREFIXFREE_TWINFREE:
     !l. prob_sorted (prob_canon l)
         /\ prob_prefixfree (prob_canon l)
         /\ prob_twinfree (prob_canon l)
Proof
   RW_TAC list_ss [prob_canon_def,
                   PROB_CANON1_SORTED, PROB_CANON1_PREFIXFREE,
                   PROB_CANON2_SORTED_PREFIXFREE_TWINFREE]
QED

Theorem PROB_CANON_CONSTANT:
     !l. prob_sorted l /\ prob_prefixfree l /\ prob_twinfree l
         ==> (prob_canon l = l)
Proof
   RW_TAC std_ss [prob_canon_def, PROB_CANON1_CONSTANT, PROB_CANON2_CONSTANT]
QED

Theorem PROB_CANON_IDEMPOT:
     !l. prob_canon (prob_canon l) = prob_canon l
Proof
   STRIP_TAC
   >> MP_TAC (Q.SPEC `l` PROB_CANON_SORTED_PREFIXFREE_TWINFREE)
   >> RW_TAC std_ss [PROB_CANON_CONSTANT]
QED

Theorem PROB_CANONICAL_DEF_ALT:
     !l. prob_canonical l
         = prob_sorted l /\ prob_prefixfree l /\ prob_twinfree l
Proof
   RW_TAC std_ss [prob_canonical_def]
   >> EQ_TAC >|
   [PROVE_TAC [PROB_CANON_SORTED_PREFIXFREE_TWINFREE],
    PROVE_TAC [PROB_CANON_CONSTANT]]
QED

Theorem PROB_CANONICAL_BASIC:
     prob_canonical [] /\ prob_canonical [[]] /\ !x. prob_canonical [x]
Proof
   RW_TAC list_ss [PROB_CANONICAL_DEF_ALT, prob_sorted_def,
                   prob_prefixfree_def, prob_twinfree_def]
QED

Theorem PROB_CANON_BASIC:
     (prob_canon [] = []) /\ (prob_canon [[]] = [[]])
     /\ (!x. prob_canon [x] = [x])
Proof
   PROVE_TAC [prob_canonical_def, PROB_CANONICAL_BASIC]
QED

Theorem PROB_CANONICAL_TL:
     !h t. prob_canonical (h::t) ==> prob_canonical t
Proof
   RW_TAC std_ss [PROB_CANONICAL_DEF_ALT] >|
   [PROVE_TAC [PROB_SORTED_TL],
    PROVE_TAC [PROB_PREFIXFREE_TL],
    PROVE_TAC [PROB_TWINFREE_TL]]
QED

Theorem PROB_CANONICAL_NIL_MEM:
     !l. prob_canonical l /\ MEM [] l = (l = [[]])
Proof
   RW_TAC std_ss []
   >> reverse EQ_TAC >- RW_TAC std_ss [PROB_CANONICAL_BASIC, MEM]
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
    >> PROVE_TAC [MEM]]
QED

Theorem PROB_CANONICAL_TLS:
     !l b. prob_canonical (MAP (CONS b) l) = prob_canonical l
Proof
   RW_TAC list_ss [PROB_CANONICAL_DEF_ALT, PROB_SORTED_TLS, PROB_PREFIXFREE_TLS]
   >> (EQ_TAC >> PROVE_TAC [PROB_TWINFREE_TLS])
QED

Theorem PROB_CANONICAL_STEP1:
     !l1 l2. prob_canonical (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
             ==> prob_canonical l1 /\ prob_canonical l2
Proof
   RW_TAC std_ss [PROB_CANONICAL_DEF_ALT, PROB_SORTED_STEP, PROB_PREFIXFREE_STEP]
   >> PROVE_TAC [PROB_TWINFREE_STEP1]
QED

Theorem PROB_CANONICAL_STEP2:
     !l1 l2. (~(l1 = [[]]) \/ ~(l2 = [[]]))
             /\ prob_canonical l1 /\ prob_canonical l2
             ==> prob_canonical (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
Proof
   NTAC 2 STRIP_TAC
   >> DISCH_TAC
   >> reverse (Suff `~(MEM [] l1) \/ ~(MEM [] l2)`)
   >- PROVE_TAC [PROB_CANONICAL_NIL_MEM]
   >> POP_ASSUM MP_TAC
   >> RW_TAC std_ss [PROB_CANONICAL_DEF_ALT, PROB_SORTED_STEP,
                     PROB_PREFIXFREE_STEP]
   >> PROVE_TAC [PROB_TWINFREE_STEP2]
QED

Theorem PROB_CANONICAL_STEP:
     !l1 l2. ~(l1 = [[]]) \/ ~(l2 = [[]])
             ==> (prob_canonical (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
                  = prob_canonical l1 /\ prob_canonical l2)
Proof
   PROVE_TAC [PROB_CANONICAL_STEP1, PROB_CANONICAL_STEP2]
QED

Theorem PROB_CANONICAL_CASES_THM:
     !l. prob_canonical l ==> (l = []) \/ (l = [[]])
            \/ ?l1 l2. prob_canonical l1 /\ prob_canonical l2
                       /\ (l = APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
Proof
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
      >> RW_TAC list_ss [MAP, prob_sorted_def, prob_order_def]]]]
QED

Theorem PROB_CANONICAL_CASES:
     !P. P [] /\ P [[]]
         /\ (!l1 l2. prob_canonical l1 /\ prob_canonical l2
               /\ prob_canonical (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
               ==> P (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2)))
         ==> (!l. prob_canonical l ==> P l)
Proof
   RW_TAC list_ss []
   >> MP_TAC (SPEC ``l:bool list list`` PROB_CANONICAL_CASES_THM)
   >> (RW_TAC list_ss [] >> PROVE_TAC [])
QED

Theorem PROB_CANONICAL_INDUCT:
     !P. P [] /\ P [[]]
         /\ (!l1 l2. prob_canonical l1 /\ prob_canonical l2 /\ P l1 /\ P l2
               /\ prob_canonical (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
               ==> P (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2)))
         ==> (!l. prob_canonical l ==> P l)
Proof
   RW_TAC list_ss []
   >> completeInduct_on `prob_longest l`
   >> RW_TAC list_ss []
   >> reverse (Suff `((l = []) \/ (l = [[]])) \/ ?l1 l2.
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
    >> RW_TAC arith_ss [PROB_LONGEST_TLS]]
QED

Theorem MEM_NIL_STEP:
     !l1 l2. ~MEM [] (APPEND (MAP (CONS T) l1) (MAP (CONS F) l2))
Proof
   RW_TAC list_ss [MEM_NIL_MAP_CONS]
QED

Theorem PROB_SORTED_PREFIXFREE_MEM_NIL:
     !l. prob_sorted l /\ prob_prefixfree l /\ MEM [] l = (l = [[]])
Proof
   Induct >- RW_TAC list_ss [MEM]
   >> STRIP_TAC
   >> reverse EQ_TAC
     >- RW_TAC std_ss [prob_prefixfree_def, prob_sorted_def, MEM]
   >> Cases_on `l` >- RW_TAC list_ss [MEM]
   >> ONCE_REWRITE_TAC [MEM]
   >> RW_TAC std_ss [prob_prefixfree_def, prob_sorted_def]
   >> Cases_on `h` >- RW_TAC list_ss [MEM, prob_order_def, IS_PREFIX]
   >> Cases_on `h'` >- RW_TAC list_ss [MEM, prob_order_def]
   >> RW_TAC list_ss [] >|
   [RW_TAC list_ss [],
    RW_TAC list_ss [],
    RW_TAC list_ss []]
QED

Theorem PROB_SORTED_PREFIXFREE_EQUALITY:
     !l l'. (!x. MEM x l = MEM x l') /\ prob_sorted l /\ prob_sorted l'
            /\ prob_prefixfree l /\ prob_prefixfree l'
            ==> (l = l')
Proof
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
    >> reverse CONJ_TAC >- PROVE_TAC [PROB_SORTED_TL, PROB_PREFIXFREE_TL]
    >> RW_TAC std_ss []
    >> Q.PAT_X_ASSUM `!x. P x` (MP_TAC o Q.SPEC `x`)
    >> REWRITE_TAC [MEM]
    >> reverse (Cases_on `x = h`) >- RW_TAC std_ss []
    >> RW_TAC std_ss []
    >> ASSUME_TAC PROB_PREFIXFREE_ELT
    >> RES_TAC
    >> NTAC 2 (POP_ASSUM (MP_TAC o Q.SPEC `h`))
    >> NTAC 3 (POP_ASSUM (K ALL_TAC))
    >> RW_TAC std_ss [IS_PREFIX_REFL]]
QED

Theorem PROB_CANONICAL_PREFIXFREE:
     !l a b.
       prob_canonical l /\ MEM a l /\ MEM b l /\ IS_PREFIX a b ==> (a = b)
Proof
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
    PROVE_TAC [PROB_CANONICAL_TL]]
QED

