## `P_PCHOOSE_THEN`

``` hol4
PairRules.P_PCHOOSE_THEN : (term -> thm_tactical)
```

------------------------------------------------------------------------

Replaces existentially quantified pair with given witness, and passes it
to a theorem-tactic.

`P_PCHOOSE_THEN` expects a pair `q`, a tactic-generating function
`f:thm->tactic`, and a theorem of the form `(A1 |- ?p. u)` as arguments.
A new theorem is created by introducing the given pair `q` as a witness
for the pair `p` whose existence is asserted in the original theorem,
`(u[q/p] |- u[q/p])`. If the tactic-generating function `f` applied to
this theorem produces results as follows when applied to a goal
`(A ?- u)`:

``` hol4
    A ?- t
   =========  f ({u[q/p]} |- u[q/p])
    A ?- t1
```

then applying `(P_PCHOOSE_THEN "q" f (A1 |- ?p. u))` to the goal
`(A ?- t)` produces the subgoal:

``` hol4
    A ?- t
   =========  P_PCHOOSE_THEN "q" f (A1 |- ?p. u)
    A ?- t1         ("q" not free anywhere)
```

### Failure

Fails if the theorem's conclusion is not existentially quantified, or if
the first argument is not a paired structure of variables. Failures may
arise in the tactic-generating function. An invalid tactic is produced
if the introduced variable is free in `u` or `t`, or if the theorem has
any hypothesis which is not alpha-convertible to an assumption of the
goal.

### See also

[`Thm_cont.X_CHOOSE_THEN`](#Thm_cont.X_CHOOSE_THEN),
[`PairRules.PCHOOSE`](#PairRules.PCHOOSE),
[`PairRules.PCHOOSE_THEN`](#PairRules.PCHOOSE_THEN),
[`PairRules.P_PCHOOSE_TAC`](#PairRules.P_PCHOOSE_TAC)
