## `IMP_RES_TAC`

``` hol4
Tactic.IMP_RES_TAC : thm_tactic
```

------------------------------------------------------------------------

Enriches assumptions by repeatedly resolving an implication with them.

Given a theorem `th`, the theorem-tactic `IMP_RES_TAC` uses `RES_CANON`
to derive a canonical list of implications, each of which has the form:

``` hol4
   A |- u1 ==> u2 ==> ... ==> un ==> v
```

`IMP_RES_TAC` then tries to repeatedly 'resolve' these theorems against
the assumptions of a goal by attempting to match the antecedents `u1`,
`u2`, ..., `un` (in that order) to some assumption of the goal (i.e. to
some candidate antecedents among the assumptions). If all the
antecedents can be matched to assumptions of the goal, then an instance
of the theorem

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
goal, then `IMP_RES_TAC` solves the goal.

### Failure

Never fails.

### See also

[`Tactic.drule`](#Tactic.drule),
[`Thm_cont.IMP_RES_THEN`](#Thm_cont.IMP_RES_THEN),
[`Drule.RES_CANON`](#Drule.RES_CANON),
[`Tactic.RES_TAC`](#Tactic.RES_TAC),
[`Thm_cont.RES_THEN`](#Thm_cont.RES_THEN)
