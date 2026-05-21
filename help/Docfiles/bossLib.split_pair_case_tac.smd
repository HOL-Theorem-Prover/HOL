## `split_pair_case_tac`

``` hol4
bossLib.split_pair_case_tac : tactic
```

------------------------------------------------------------------------

Splits pairs that are arguments to a pair-case expression.

A call to `split_pair_case_tac` will search the goal (starting with the
conclusion and moving onto each assumption in turn), for a sub-term of
the form `case p of (x,y,...) => e`, where the variables appearing in
`p` are free in the goal. The tactic will then introduce a new
assumption in the goal of the form

``` hol4
   p = (x,y,...)
```

where the variables `x`, `y` etc., are chosen to be as close as possible
to the names in the case expression. In other words, they will vary only
if those names are already free in the goal.

### Failure

Fails if there is no such sub-term.

### Example

``` hol4
> split_pair_case_tac ([], ``(case p of (x,y,z) => x + y * z) > 10``);
val it =
   ([([``p = (x,y,z)``], ``(case p of (x,y,z) => x + y * z) > 10``)], fn)
```

### See also

[`bossLib.pairarg_tac`](#bossLib.pairarg_tac),
[`pairLib.Pair_Cases_on`](#pairLib.Pair_Cases_on)
