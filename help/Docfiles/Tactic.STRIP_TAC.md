## `STRIP_TAC`

``` hol4
Tactic.STRIP_TAC : tactic
```

------------------------------------------------------------------------

Splits a goal by eliminating one outermost connective.

Given a goal `(A,t)`, `STRIP_TAC` removes one outermost occurrence of
one of the connectives `!`, `==>`, `~` or `/\` from the conclusion of
the goal `t`. If `t` is a universally quantified term, then `STRIP_TAC`
strips off the quantifier:

``` hol4
      A ?- !x.u
   ==============  STRIP_TAC
     A ?- u[x'/x]
```

where `x'` is a primed variant that does not appear free in the
assumptions `A`. If `t` is a conjunction, then `STRIP_TAC` simply splits
the conjunction into two subgoals:

``` hol4
      A ?- v /\ w
   =================  STRIP_TAC
    A ?- v   A ?- w
```

If `t` is an implication, `STRIP_TAC` moves the antecedent into the
assumptions, stripping conjunctions, disjunctions and existential
quantifiers according to the following rules:

``` hol4
    A ?- v1 /\ ... /\ vn ==> v            A ?- v1 \/ ... \/ vn ==> v
   ============================        =================================
       A u {v1,...,vn} ?- v             A u {v1} ?- v ... A u {vn} ?- v

     A ?- ?x.w ==> v
   ====================
    A u {w[x'/x]} ?- v
```

where `x'` is a primed variant of `x` that does not appear free in `A`.
Finally, a negation `~t` is treated as the implication `t ==> F`.

### Failure

`STRIP_TAC (A,t)` fails if `t` is not a universally quantified term, an
implication, a negation or a conjunction.

### Example

Applying `STRIP_TAC` twice to the goal:

``` hol4
    ?- !n. m <= n /\ n <= m ==> (m = n)
```

results in the subgoal:

``` hol4
   {n <= m, m <= n} ?- m = n
```

When trying to solve a goal, often the best thing to do first is
`REPEAT STRIP_TAC` to split the goal up into manageable pieces.

### See also

[`Tactic.CONJ_TAC`](#Tactic.CONJ_TAC),
[`Tactic.DISCH_TAC`](#Tactic.DISCH_TAC),
[`Thm_cont.DISCH_THEN`](#Thm_cont.DISCH_THEN),
[`Tactic.GEN_TAC`](#Tactic.GEN_TAC),
[`Tactic.STRIP_ASSUME_TAC`](#Tactic.STRIP_ASSUME_TAC),
[`Tactic.STRIP_GOAL_THEN`](#Tactic.STRIP_GOAL_THEN)
