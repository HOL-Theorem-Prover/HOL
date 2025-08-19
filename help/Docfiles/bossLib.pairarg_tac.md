## `pairarg_tac`

``` hol4
bossLib.pairarg_tac : tactic
```

------------------------------------------------------------------------

Adds a "splitting" equation for a pair term to goal assumptions.

A call to `pairarg_tac` will search the goal (starting with the
conclusion and moving onto each assumption in turn), for a sub-term of
the form `(\(x,y,...). body) arg`, where the variables appearing in
`arg` are free in the goal. The tactic will then introduce a new
assumption in the goal of the form

``` hol4
   arg = (x,y,...)
```

where the variables `x`, `y` etc., are chosen to be as close as possible
to the names in the paired abstraction. In other words, they will vary
only if those names are already free in the goal.

### Failure

Fails if there is no such sub-term.

### Example

``` hol4
> pairarg_tac ([], ``(\(x,y). x + y) p = 10``);
val it = ([([``p = (x,y)``], ``(\(x,y). x + y) p = 10``)], fn)
```

### See also

[`pairLib.PairCases_on`](#pairLib.PairCases_on),
[`bossLib.split_pair_case_tac`](#bossLib.split_pair_case_tac)
