## `PCHOOSE_THEN`

``` hol4
PairRules.PCHOOSE_THEN : thm_tactical
```

------------------------------------------------------------------------

Applies a tactic generated from the body of paired existentially
quantified theorem.

When applied to a theorem-tactic `ttac`, a paired existentially
quantified theorem:

``` hol4
    A' |- ?p. t
```

and a goal, `CHOOSE_THEN` applies the tactic `ttac (t[p'/p] |- t[p'/p])`
to the goal, where `p'` is a variant of the pair `p` chosen to have no
components free in the assumption list of the goal. Thus if:

``` hol4
    A ?- s1
   =========  ttac (t[q'/q] |- t[q'/q])
    B ?- s2
```

then

``` hol4
    A ?- s1
   ==========  CHOOSE_THEN ttac (A' |- ?q. t)
    B ?- s2
```

This is invalid unless `A'` is a subset of `A`.

### Failure

Fails unless the given theorem is a paired existential quantification,
or if the resulting tactic fails when applied to the goal.

### See also

[`Thm_cont.CHOOSE_THEN`](#Thm_cont.CHOOSE_THEN),
[`PairRules.PCHOOSE_TAC`](#PairRules.PCHOOSE_TAC),
[`PairRules.P_PCHOOSE_THEN`](#PairRules.P_PCHOOSE_THEN)
