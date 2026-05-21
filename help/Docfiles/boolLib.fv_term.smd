## `fv_term`

``` hol4
boolLib.fv_term : (term -> tactic) -> tactic
```

------------------------------------------------------------------------

Applies a term-tactic to a goal's "first" free variable

Applying `fv_term tmtac` to a goal `A ?- g`, finds the first free
variable in the goal, and passes that variable to the function `tmtac`,
generating a tactic, which is then applied to the goal. The first free
variable is the first returned by successive calls to `free_vars`
applied to first `g` and then each assumption in `A` in turn.

### Failure

Fails if a goal does not have any free variables, or if `tmtac v` fails
when applied to the goal, with `v` the "first" free variable as defined
above.

### Example

``` hol4
            ?- 0 < f (n:num)
   ================================== fv_term (C tmCases_on ["", "j"])
     ?- 0 < f 0    ?- 0 < f (SUC j)
```

### See also

[`boolLib.first_fv_term`](#boolLib.first_fv_term)
