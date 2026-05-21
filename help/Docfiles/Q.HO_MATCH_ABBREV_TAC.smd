## `HO_MATCH_ABBREV_TAC`

``` hol4
Q.HO_MATCH_ABBREV_TAC : term quotation -> tactic
```

------------------------------------------------------------------------

Introduces abbreviations by doing a higher-order match against the goal.

This tactic is just like `Q.MATCH_ABBREV_TAC`, but does a higher-order
match against the goal rather than a first order match. See the
documentation for `MATCH_ABBREV_TAC` for more details.

### Example

The goal

``` hol4
   ?- !n. (n + 1) * (n - 1) = n * n - 1
```

is transformed by `` Q.HO_MATCH_ABBREV_TAC `!k. P k` `` to

``` hol4
   Abbrev(P = (\n. (n + 1) * (n - 1) = n * n - 1)) ?-  !k. P k
```

Note how the bound variable changes to match that used in the pattern.

### See also

[`Q.ABBREV_TAC`](#Q.ABBREV_TAC),
[`Q.MATCH_ABBREV_TAC`](#Q.MATCH_ABBREV_TAC)
