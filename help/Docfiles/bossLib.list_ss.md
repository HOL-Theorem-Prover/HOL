## `list_ss`

``` hol4
bossLib.list_ss : simpset
```

------------------------------------------------------------------------

Simplification set for lists.

The simplification set `list_ss` is a version of `arith_ss` enhanced for
the theory of lists. The following rewrites are currently used to
augment those already present from `arith_ss`:

``` hol4
    |- (!l. APPEND [] l = l) /\
        !l1 l2 h. APPEND (h::l1) l2 = h::APPEND l1 l2
    |- (!l1 l2 l3. (APPEND l1 l2 = APPEND l1 l3) = (l2 = l3)) /\
        !l1 l2 l3. (APPEND l2 l1 = APPEND l3 l1) = (l2 = l3)
    |- (!l. EL 0 l = HD l) /\ !l n. EL (SUC n) l = EL n (TL l)
    |- (!P. EVERY P [] = T) /\ !P h t. EVERY P (h::t) = P h /\ EVERY P t
    |- (FLAT [] = []) /\ !h t. FLAT (h::t) = APPEND h (FLAT t)
    |- (LENGTH [] = 0) /\ !h t. LENGTH (h::t) = SUC (LENGTH t)
    |- (!f. MAP f [] = []) /\ !f h t. MAP f (h::t) = f h::MAP f t
    |- (!f. MAP2 f [] [] = []) /\
        !f h1 t1 h2 t2.
           MAP2 f (h1::t1) (h2::t2) = f h1 h2::MAP2 f t1 t2
    |- (!x. MEM x [] = F) /\ !x h t. MEM x (h::t) = (x = h) \/ MEM x t
    |- (NULL [] = T) /\ !h t. NULL (h::t) = F
    |- (REVERSE [] = []) /\ !h t. REVERSE (h::t) = APPEND (REVERSE t) [h]
    |- (SUM [] = 0) /\ !h t. SUM (h::t) = h + SUM t
    |- !h t. HD (h::t) = h
    |- !h t. TL (h::t) = t
    |- !l1 l2 l3. APPEND l1 (APPEND l2 l3) = APPEND (APPEND l1 l2) l3
    |- !l. ~NULL l ==> (HD l::TL l = l)
    |- !a0 a1 a0' a1'. (a0::a1 = a0'::a1') = (a0 = a0') /\ (a1 = a1')
    |- !l1 l2. LENGTH (APPEND l1 l2) = LENGTH l1 + LENGTH l2
    |- !l f. LENGTH (MAP f l) = LENGTH l
    |- !f l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)
    |- !a1 a0. ~(a0::a1 = [])
    |- !a1 a0. ~([] = a0::a1)
    |- !l f. ((MAP f l = []) = (l = [])) /\
             (([] = MAP f l) = (l = []))
    |- !l. APPEND l [] = l
    |- !l x. ~(l = x::l) /\ ~(x::l = l)
    |- (!v f. case v f [] = v) /\
        !v f a0 a1. case v f (a0::a1) = f a0 a1
    |- (!l1 l2. ([] = APPEND l1 l2) = (l1 = []) /\ (l2 = [])) /\
        !l1 l2. (APPEND l1 l2 = []) = (l1 = []) /\ (l2 = [])
    |- (ZIP ([][]) = []) /\
        !x1 l1 x2 l2. ZIP (x1::l1,x2::l2) = (x1,x2)::ZIP (l1,l2)
    |- (UNZIP [] = ([],[])) /\
        !x l. UNZIP (x::l) = (FST x::FST (UNZIP l),SND x::SND (UNZIP l))
    |- !P l1 l2. EVERY P (APPEND l1 l2) = EVERY P l1 /\ EVERY P l2
    |- !P l1 l2. EXISTS P (APPEND l1 l2) = EXISTS P l1 \/ EXISTS P l2
    |- !e l1 l2. MEM e (APPEND l1 l2) = MEM e l1 \/ MEM e l2
    |- (!x. LAST [x] = x) /\ !x y z. LAST (x::y::z) = LAST (y::z)
    |- (!x. FRONT [x] = []) /\ !x y z. FRONT (x::y::z) = x::FRONT (y::z)
    |- (!f e. FOLDL f e [] = e) /\
        !f e x l. FOLDL f e (x::l) = FOLDL f (f e x) l
    |- (!f e. FOLDR f e [] = e) /\
        !f e x l. FOLDR f e (x::l) = f x (FOLDR f e l)
```

### See also

[`BasicProvers.RW_TAC`](#BasicProvers.RW_TAC),
[`BasicProvers.SRW_TAC`](#BasicProvers.SRW_TAC),
[`simpLib.SIMP_TAC`](#simpLib.SIMP_TAC),
[`simpLib.SIMP_CONV`](#simpLib.SIMP_CONV),
[`simpLib.SIMP_RULE`](#simpLib.SIMP_RULE),
[`BasicProvers.bool_ss`](#BasicProvers.bool_ss),
[`bossLib.std_ss`](#bossLib.std_ss),
[`bossLib.arith_ss`](#bossLib.arith_ss)
