## `SIMP_CONV` {#bossLib.SIMP_CONV}


```
SIMP_CONV : simpset -> thm list -> conv
```



Applies a simpset and a list of rewrite rules to simplify a term.


`SIMP_CONV` is the fundamental engine of the HOL simplification
library.  It repeatedly applies the transformations included in
the provided simpset (which is augmented with the given rewrite rules)
to a term, ultimately yielding a theorem equating the original
term to another.

Values of the `simpset` type embody a suite of different
transformations that might be applicable to given terms.  These
“transformational components” are rewrites, conversions, AC-rules,
congruences, decision procedures and a filter, which is used to modify
the way in which rewrite rules are added to the simpset.  The exact
types for these components, known as simpset fragments, and the way
they can be combined to create simpsets is given in the reference
entry for `SSFRAG`.

Rewrite rules are used similarly to the way in they are used in the
rewriting system (`REWRITE_TAC` et al.).  These are equational
theorems oriented to rewrite from left-hand-side to right-hand-side.
Further, `SIMP_CONV` handles obvious problems.  If a rewrite rule is
of the general form `[...] |- x = f x`, then it will be discarded, and
a message is printed to this effect.  On the other hand, if the
right-hand-side is a permutation of the pattern on the left, as in
`|- x + y = y + x` and `|- x INSERT (y INSERT s) = y INSERT (x INSERT s)`,
then such rules will only be applied if the term to which they are
being applied is strictly reduced according to some term ordering.

Rewriting is done using a form of higher-order matching, and also uses
conditional rewriting.  This latter means that theorems of the form
`|- P ==> (x = y)` can be used as rewrites.  If a term matching `x` is
found, the simplifier will attempt to satisfy the side-condition `P`.
If it is able to do so, then the rewriting will be performed.  In the
process of attempting to rewrite `P` to true, further side conditions
may be generated.  The simplifier limits the size of the stack of side
conditions to be solved (the reference variable
`Cond_rewr.stack_limit` holds this limit), so this will not introduce
an infinite loop.

Rewrite rules can always be added “on the fly” as all of the
simplification functions take a `thm list` argument where these rules
can be specified.  If a set of rewrite rules is frequently used, then
these should probably be made into a `ssfrag` value with the
`rewrites` function and then added to an existing simpset with `++`.

The conversions which are part of simpsets are useful for situations
where simple rewriting is not enough to transform certain terms.  For
example, the `BETA_CONV` conversion is not expressible as a standard
first order rewrite, but is part of the `bool_ss` simpset and the
application of this simpset will thus simplify all occurrences of
`(\x. e1) e2`.

In fact, conversions in simpsets are not typically applied
indiscriminately to all sub-terms.  (If a conversion is applied to an
inappropriate sub-term and fails, this failure is caught by the
simplifier and ignored.)  Instead, conversions in simpsets are
accompanied by a term-pattern which specifies the sort of situations
in which they should be applied.  This facility is used in the
definition of `bool_ss` to include `ETA_CONV`, but stop it from
transforming `!x. P x` into `$! P`.

AC-rules allow simpsets to be constructed that automatically normalise
terms involving associative and commutative operators, again according
to some arbitrary term ordering metric.

Congruence rules allow `SIMP_CONV` to assume additional context as a
term is rewritten.  In a term such as `P ==> Q /\ f x` the truth of
term P may be assumed as an additional piece of context in the
rewriting of `Q /\ f x`.  The congruence theorem that states this is
valid is (`IMP_CONG`):
    
       |- (P = P') ==> (P' ==> (Q = Q')) ==> ((P ==> Q) = (P' ==> Q'))
    
Other congruence theorems can be part of simpsets.  The system
provides `IMP_CONG` above and `COND_CONG` as part of the `CONG_ss`
`ssfrag` value.  (These `simpset` fragments can be incorporated into
simpsets with the `++` function.)  Other congruence theorems are
already proved for operators such as conjunction and disjunction, but
use of these in standard simpsets is not recommended as the
computation of all the additional contexts for a simple chain of
conjuncts or disjuncts can be very computationally intensive.

Decision procedures in simpsets are similar to conversions.  They are
arbitrary pieces of code that are applied to sub-terms at low
priority.  They are given access to the wider context through a list
of relevant theorems.  The `arith_ss` simpset includes an arithmetic
decision procedure implemented in this way.

### Failure

`SIMP_CONV` never fails, but may diverge.

### Example

    
    - SIMP_CONV arith_ss [] ``(\x. x + 3) 4``;
    > val it = |- (\x. x + 3) 4 = 7 : thm
    




`SIMP_CONV` is a powerful way of manipulating terms.  Other functions
in the simplification library provide the same facilities when in the
contexts of goals and tactics (`SIMP_TAC`, `ASM_SIMP_TAC` etc.), and
theorems (`SIMP_RULE`), but `SIMP_CONV` provides the underlying
functionality, and is useful in its own right, just as conversions are
generally.

### See also

[`bossLib.++`](#bossLib..KAL), [`bossLib.ASM_SIMP_TAC`](#bossLib.ASM_SIMP_TAC), [`bossLib.FULL_SIMP_TAC`](#bossLib.FULL_SIMP_TAC), [`simpLib.mk_simpset`](#simpLib.mk_simpset), [`bossLib.rewrites`](#bossLib.rewrites), [`bossLib.SIMP_RULE`](#bossLib.SIMP_RULE), [`bossLib.SIMP_TAC`](#bossLib.SIMP_TAC), [`simpLib.SSFRAG`](#simpLib.SSFRAG), [`bossLib.EVAL`](#bossLib.EVAL)

