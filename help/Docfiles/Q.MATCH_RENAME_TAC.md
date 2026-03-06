## `MATCH_RENAME_TAC`

``` hol4
Q.MATCH_RENAME_TAC : term quotation -> tactic
```

------------------------------------------------------------------------

Replaces selected terms with new variables by matching a pattern against
the goal statement.

When applied to the goal `(asl, w)`, the tactic
`Q.MATCH_RENAME_TAC q ls` parses the quotation `q` in the context of the
goal, producing a term to use as a pattern. The tactic then attempts a
(first order) match of the pattern against the term `w`.

For each variable `v` in the pattern, there will be an instantiation
term `t`, such that the substitution

``` hol4
   pattern[v1 |-> t1, v2 |-> t2, ...]
```

produces `w`. The effect of the tactic is to then replace each `t` with
the corresponding `v`, yielding a new goal. Note that underscores within
a pattern, though strictly speaking variables, are not included in this
reverse instantiation.

### Failure

`MATCH_RENAME_TAC` fails if the pattern provided does not match the
goal, or if variables from the goal are used in the pattern in ways that
make the pattern fail to type-check.

### Example

If the current goal is

``` hol4
   ?- (f x = Pair C'' C0') ==> (f C'' = f C0')
```

then applying the tactic
`` Q.MATCH_RENAME_TAC `(f x = Pair c1 c2) ==> _` `` results in the goal

``` hol4
   ?- (f x = Pair c1 c2) ==> (f c1 = f c2)
```

### Comments

This tactic is equivalent to first applying `Q.MATCH_ABBREV_TAC q`, then
applying `` Q.RM_ABBREV_TAC `v` `` for each underscore in `q`.

### See also

[`Q.MATCH_ABBREV_TAC`](#Q.MATCH_ABBREV_TAC),
[`Q.MATCH_ASSUM_RENAME_TAC`](#Q.MATCH_ASSUM_RENAME_TAC)
