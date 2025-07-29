## `UNABBREV_TAC`

``` hol4
Q.UNABBREV_TAC : term quotation -> tactic
```

------------------------------------------------------------------------

Removes an abbreviation from a goal's assumptions by substituting it
out.

The argument to `UNABBREV_TAC` must be a quotation containing the name
of a variable that is abbreviated in the current goal. In other words,
when calling `` UNABBREV_TAC `v` ``, there must be an assumption of the
form `Abbrev(v = e)` in the goal's assumptions. This assumption is
removed, and all occurrences of the variable `v` in the goal are
replaced by `e`. If there are two abbreviation assumptions for `v` in
the goal, the more recent is removed.

### Example

The goal

``` hol4
   Abbrev(v = 2 * x + 1), v + x < 10 ?- P(v)
```

is transformed by `` Q.UNABBREV_TAC `v` `` to

``` hol4
   2 * x + 1 + x < 10 ?- P(2 * x + 1)
```

### Failure

Fails if there is no abbreviation of the required form in the goal's
assumptions, or if the quotation doesn't parse to a variable.

### See also

[`BasicProvers.Abbr`](#BasicProvers.Abbr),
[`Q.ABBREV_TAC`](#Q.ABBREV_TAC)
