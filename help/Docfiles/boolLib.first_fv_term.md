## `first_fv_term`

``` hol4
boolLib.first_fv_term : (term -> tactic) -> tactic
```

------------------------------------------------------------------------

Applies a term-tactic to goal's first free variable that makes it
succeed

A call to `first_fv_term tmtac` applies the function `tmtac` to all of a
goal's free variables. This generates a list of tactics, which is then
applied to the goal tactic-by-tactic (this is the action of the tactical
`MAP_FIRST`). The first application that succeeds (doesn't raise a
`HOL_ERR`) is taken as the result. Later applications are not attempted.

### Failure

Fails if there is no free variable `v` in the goal `A ?- g` that makes
the application `tmtac v (A?-g)` succeed.

### See also

[`Tactical.MAP_FIRST`](#Tactical.MAP_FIRST)
