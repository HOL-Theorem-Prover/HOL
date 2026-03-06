## `X_GEN_TAC`

``` hol4
Tactic.X_GEN_TAC : (term -> tactic)
```

------------------------------------------------------------------------

Specializes a goal with the given variable.

When applied to a term `x'`, which should be a variable, and a goal
`A ?- !x. t`, the tactic `X_GEN_TAC` returns the goal `A ?- t[x'/x]`.

``` hol4
     A ?- !x. t
   ==============  X_GEN_TAC "x'"
    A ?- t[x'/x]
```

### Failure

Fails unless the goal's conclusion is universally quantified and the
term a variable of the appropriate type. It also fails if the variable
given is free in either the assumptions or (initial) conclusion of the
goal.

### See also

[`Tactic.FILTER_GEN_TAC`](#Tactic.FILTER_GEN_TAC),
[`Thm.GEN`](#Thm.GEN), [`Thm.GENL`](#Thm.GENL),
[`Drule.GEN_ALL`](#Drule.GEN_ALL), [`Thm.SPEC`](#Thm.SPEC),
[`Drule.SPECL`](#Drule.SPECL), [`Drule.SPEC_ALL`](#Drule.SPEC_ALL),
[`Tactic.SPEC_TAC`](#Tactic.SPEC_TAC),
[`Tactic.STRIP_TAC`](#Tactic.STRIP_TAC)
