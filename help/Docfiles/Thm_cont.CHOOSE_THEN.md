## `CHOOSE_THEN`

``` hol4
Thm_cont.CHOOSE_THEN : thm_tactical
```

------------------------------------------------------------------------

Applies a tactic generated from the body of existentially quantified
theorem.

When applied to a theorem-tactic `ttac`, an existentially quantified
theorem `A' |- ?x. t`, and a goal, `CHOOSE_THEN` applies the tactic
`ttac (t[x'/x] |- t[x'/x])` to the goal, where `x'` is a variant of `x`
chosen not to be free in the assumption list of the goal. Thus if:

``` hol4
    A ?- s1
   =========  ttac (t[x'/x] |- t[x'/x])
    B ?- s2
```

then

``` hol4
    A ?- s1
   ==========  CHOOSE_THEN ttac (A' |- ?x. t)
    B ?- s2
```

This is invalid unless `A'` is a subset of `A`.

### Failure

Fails unless the given theorem is existentially quantified, or if the
resulting tactic fails when applied to the goal.

### Example

This theorem-tactical and its relatives are very useful for using
existentially quantified theorems. For example one might use the inbuilt
theorem

``` hol4
   LESS_ADD_1 = |- !m n. n < m ==> (?p. m = n + (p + 1))
```

to help solve the goal

``` hol4
   ?- x < y ==> 0 < y * y
```

by starting with the following tactic

``` hol4
   DISCH_THEN (CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1)
```

which reduces the goal to

``` hol4
   ?- 0 < ((x + (p + 1)) * (x + (p + 1)))
```

which can then be finished off quite easily, by, for example:

``` hol4
   REWRITE_TAC[ADD_ASSOC, SYM (SPEC_ALL ADD1),
               MULT_CLAUSES, ADD_CLAUSES, LESS_0]
```

### See also

[`Tactic.CHOOSE_TAC`](#Tactic.CHOOSE_TAC),
[`Thm_cont.X_CHOOSE_THEN`](#Thm_cont.X_CHOOSE_THEN)
