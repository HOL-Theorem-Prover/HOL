## `RESQ_EXISTS_TAC`

``` hol4
res_quanTools.RESQ_EXISTS_TAC : term -> tactic
```

------------------------------------------------------------------------

Strips the outermost restricted existential quantifier from the
conclusion of a goal.

When applied to a goal `A ?- ?x::P. t`, the tactic `RESQ_EXISTS_TAC`
reduces it to a new subgoal `A ?- P x' /\ t[x'/x]` where `x'` is a
variant of `x` chosen to avoid clashing with any variables free in the
goal's assumption list. Normally `x'` is just `x`.

``` hol4
     A ?- ?x::P. t
   ======================  RESQ_EXISTS_TAC
    A ?- P x' /\ t[x'/x]
```

### Failure

Fails unless the goal's conclusion is a restricted extistential
quantification.
