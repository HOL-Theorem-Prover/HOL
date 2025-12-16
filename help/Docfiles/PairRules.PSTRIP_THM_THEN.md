## `PSTRIP_THM_THEN`

``` hol4
PairRules.PSTRIP_THM_THEN : thm_tactical
```

------------------------------------------------------------------------

`PSTRIP_THM_THEN` applies the given theorem-tactic using the result of
stripping off one outer connective from the given theorem.

Given a theorem-tactic `ttac`, a theorem `th` whose conclusion is a
conjunction, a disjunction or a paired existentially quantified term,
and a goal `(A,t)`, `STRIP_THM_THEN ttac th` first strips apart the
conclusion of `th`, next applies `ttac` to the theorem(s) resulting from
the stripping and then applies the resulting tactic to the goal.

In particular, when stripping a conjunctive theorem `A'|- u /\ v`, the
tactic

``` hol4
   ttac(u|-u) THEN ttac(v|-v)
```

resulting from applying `ttac` to the conjuncts, is applied to the goal.
When stripping a disjunctive theorem `A'|- u \/ v`, the tactics
resulting from applying `ttac` to the disjuncts, are applied to split
the goal into two cases. That is, if

``` hol4
    A ?- t                           A ?- t
   =========  ttac (u|-u)    and    =========  ttac (v|-v)
    A ?- t1                          A ?- t2
```

then:

``` hol4
         A ?- t
   ================== PSTRIP_THM_THEN ttac (A'|- u \/ v)
    A ?- t1  A ?- t2
```

When stripping a paired existentially quantified theorem `A'|- ?p. u`,
the tactic resulting from applying `ttac` to the body of the paired
existential quantification, `ttac(u|-u)`, is applied to the goal. That
is, if:

``` hol4
    A ?- t
   =========  ttac (u|-u)
    A ?- t1
```

then:

``` hol4
      A ?- t
   =============  PSTRIP_THM_THEN ttac (A'|- ?p. u)
      A ?- t1
```

The assumptions of the theorem being split are not added to the
assumptions of the goal(s) but are recorded in the proof. If `A'` is not
a subset of the assumptions `A` of the goal (up to alpha-conversion),
`PSTRIP_THM_THEN ttac th` results in an invalid tactic.

### Failure

`PSTRIP_THM_THEN ttac th` fails if the conclusion of `th` is not a
conjunction, a disjunction or a paired existentially quantification.
Failure also occurs if the application of `ttac` fails, after stripping
the outer connective from the conclusion of `th`.

`PSTRIP_THM_THEN` is used enrich the assumptions of a goal with a
stripped version of a previously-proved theorem.

### See also

[`Thm_cont.STRIP_THM_THEN`](#Thm_cont.STRIP_THM_THEN),
[`PairRules.PSTRIP_ASSUME_TAC`](#PairRules.PSTRIP_ASSUME_TAC),
[`PairRules.PSTRIP_GOAL_THEN`](#PairRules.PSTRIP_GOAL_THEN),
[`PairRules.PSTRIP_TAC`](#PairRules.PSTRIP_TAC)
