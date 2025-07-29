## `PEXISTS_TAC`

``` hol4
PairRules.PEXISTS_TAC : (term -> tactic)
```

------------------------------------------------------------------------

Reduces paired existentially quantified goal to one involving a specific
witness.

When applied to a term `q` and a goal `?p. t`, the tactic `PEXISTS_TAC`
reduces the goal to `t[q/p]`.

``` hol4
    A ?- ?p. t
   =============  EXISTS_TAC "q"
    A ?- t[q/p]
```

### Failure

Fails unless the goal's conclusion is a paired existential
quantification and the term supplied has the same type as the quantified
pair in the goal.

### Example

The goal:

``` hol4
   ?- ?(x,y). (x,y)=(1,2)
```

can be solved by:

``` hol4
   PEXISTS_TAC "(1,2)" THEN REFL_TAC
```

### See also

[`Tactic.EXISTS_TAC`](#Tactic.EXISTS_TAC),
[`PairRules.PEXISTS`](#PairRules.PEXISTS)
