## `RES_TAC`

``` hol4
Tactic.RES_TAC : tactic
```

------------------------------------------------------------------------

Enriches assumptions by repeatedly resolving them against each other.

`RES_TAC` searches for pairs of assumed assumptions of a goal (that is,
for a candidate implication and a candidate antecedent, respectively)
which can be 'resolved' to yield new results. The conclusions of all the
new results are returned as additional assumptions of the subgoal(s).
The effect of `RES_TAC` on a goal is to enrich the assumptions set with
some of its collective consequences.

When applied to a goal `A ?- g`, the tactic `RES_TAC` uses `RES_CANON`
to obtain a set of implicative theorems in canonical form from the
assumptions `A` of the goal. Each of the resulting theorems (if there
are any) will have the form:

``` hol4
   A |- u1 ==> u2 ==> ... ==> un ==> v
```

`RES_TAC` then tries to repeatedly 'resolve' these theorems against the
assumptions of a goal by attempting to match the antecedents `u1`, `u2`,
..., `un` (in that order) to some assumption of the goal (i.e. to some
candidate antecedents among the assumptions). If all the antecedents can
be matched to assumptions of the goal, then an instance of the theorem

``` hol4
   A u {a1,...,an} |- v
```

called a 'final resolvent' is obtained by repeated specialization of the
variables in the implicative theorem, type instantiation, and
applications of modus ponens. If only the first `i` antecedents `u1`,
..., `ui` can be matched to assumptions and then no further matching is
possible, then the final resolvent is an instance of the theorem:

``` hol4
   A u {a1,...,ai} |- u(i+1) ==> ... ==> v
```

All the final resolvents obtained in this way (there may be several,
since an antecedent `ui` may match several assumptions) are added to the
assumptions of the goal, in the stripped form produced by using
`STRIP_ASSUME_TAC`. If the conclusion of any final resolvent is a
contradiction '`F`' or is alpha-equivalent to the conclusion of the
goal, then `RES_TAC` solves the goal.

### Failure

`RES_TAC` cannot fail and so should not be unconditionally
`REPEAT`ed. However, since the final resolvents added to the original
assumptions are never used as 'candidate antecedents' it is sometimes
necessary to apply `RES_TAC` more than once to derive the desired
result.

### See also

[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC),
[`Thm_cont.IMP_RES_THEN`](#Thm_cont.IMP_RES_THEN),
[`Drule.RES_CANON`](#Drule.RES_CANON),
[`Thm_cont.RES_THEN`](#Thm_cont.RES_THEN)
