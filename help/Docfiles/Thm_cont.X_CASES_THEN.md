## `X_CASES_THEN`

``` hol4
Thm_cont.X_CASES_THEN : term list list -> thm_tactical
```

------------------------------------------------------------------------

Applies a theorem-tactic to all disjuncts of a theorem, choosing
witnesses.

Let `[yl1,...,yln]` represent a list of variable lists, each of length
zero or more, and `xl1,...,xln` each represent a vector of zero or more
variables, so that the variables in each of `yl1...yln` have the same
types as the corresponding `xli`. `X_CASES_THEN` expects such a list of
variable lists, `[yl1,...,yln]`, a tactic generating function
`f:thm->tactic`, and a disjunctive theorem, where each disjunct may be
existentially quantified:

``` hol4
   th = |-(?xl1.B1)  \/...\/  (?xln.Bn)
```

each disjunct having the form `(?xi1 ... xim. Bi)`. If applying `f` to
the theorem obtained by introducing witness variables `yli` for the
objects `xli` whose existence is asserted by each disjunct, typically
`({Bi[yli/xli]} |- Bi[yli/xli])`, produce the following results when
applied to a goal `(A ?- t)`:

``` hol4
    A ?- t
   ========= f ({B1[yl1/xl1]} |- B1[yl1/xl1])
    A ?- t1

    ...

    A ?- t
   =========  f ({Bn[yln/xln]} |- Bn[yln/xln])
    A ?- tn
```

then applying `(X_CHOOSE_THEN [yl1,...,yln] f th)` to the goal
`(A ?- t)` produces `n` subgoals.

``` hol4
           A ?- t
   =======================  X_CHOOSE_THEN [yl1,...,yln] f th
    A ?- t1  ...  A ?- tn
```

### Failure

Fails (with `X_CHOOSE_THEN`) if any `yli` has more variables than the
corresponding `xli`, or (with `SUBST`) if corresponding variables have
different types. Failures may arise in the tactic-generating function.
An invalid tactic is produced if any variable in any of the `yli` is
free in the corresponding `Bi` or in `t`, or if the theorem has any
hypothesis which is not alpha-convertible to an assumption of the goal.

### Example

Given the goal `?- (x MOD 2) <= 1`, the following theorem may be used to
split into 2 cases:

``` hol4
   th = |- (?m. x = 2 * m) \/ (?m. x = (2 * m) + 1)
```

by the tactic

``` hol4
   X_CASES_THEN [[Term`n:num`],[Term`n:num]] ASSUME_TAC th
```

to produce the subgoals:

``` hol4
   {x = (2 * n) + 1} ?- (x MOD 2) <= 1

   {x = 2 * n} ?- (x MOD 2) <= 1
```

### See also

[`Thm_cont.DISJ_CASES_THENL`](#Thm_cont.DISJ_CASES_THENL),
[`Thm_cont.X_CASES_THENL`](#Thm_cont.X_CASES_THENL),
[`Thm_cont.X_CHOOSE_THEN`](#Thm_cont.X_CHOOSE_THEN)
