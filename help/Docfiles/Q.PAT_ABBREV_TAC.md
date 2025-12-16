## `PAT_ABBREV_TAC`

``` hol4
Q.PAT_ABBREV_TAC : term quotation -> tactic
```

------------------------------------------------------------------------

Introduces an abbreviation within the goal statement.

When applied to the goal `(asl, w)`, the tactic `Q.PAT_ABBREV_TAC q`
parses the quotation `q` in the context of the goal, producing an
equality term `v = p`. The tactic then uses `HolKernel.gen_find_term` to
search for a sub-term of `w` that `p` matches against. If such a
sub-term `t` is found then all occurrences of `t` (in `asl` and `w`)
will be replaced by `v` and an assumption `Abbrev(v = t)` is added to
the goal.

The trace variable `"PAT_ABBREV_TAC: match var/const"` controls whether
or not trivial matches (with constants or variables) are allowed. By
default trivial matches are permitted but when the trace variable is
false the tactic will ignore trivial matches, which could result in
failure.

### Failure

`PAT_ABBREV_TAC` fails if `q` does not successfully parse as an equality
or if no matching sub-term is found in the goal, or if the only matching
sub-terms would bind pattern variables to variables that are bound in
the goal.

### Example

If the current goal is

``` hol4
   ?- (n + 10) * y <= 42315
```

then applying the tactic `` Q.PAT_ABBREV_TAC `X = a * b: num` `` results
in the goal

``` hol4
   Abbrev (X = (n + 10) * y)
      ?-
   X <= 42315
```

By default trivial matches are permitted. If the current goal is

``` hol4
   ?- y <= 42315
```

then `` Q.PAT_ABBREV_TAC `X = a: num` `` will give

``` hol4
   Abbrev (X = y)
      ?-
   X <= 42315
```

However, if this is not desirable then setting

``` hol4
Feedback.set_trace "PAT_ABBREV_TAC: match var/const" 0
```

and applying `` Q.PAT_ABBREV_TAC `X = a: num` `` will give

``` hol4
   Abbrev (X = 42315)
      ?-
   y <= X
```

If the current goal is

``` hol4
   ?- !x. x < 3
```

then applying `` Q.PAT_ABBREV_TAC `v = (a < b)` `` will result in a
failure because the pattern's variable `a` would have to bind the bound
variable `x` in the goal.

### See also

[`Q.ABBREV_TAC`](#Q.ABBREV_TAC),
[`HolKernel.gen_find_term`](#HolKernel.gen_find_term),
[`Q.MATCH_ABBREV_TAC`](#Q.MATCH_ABBREV_TAC)
