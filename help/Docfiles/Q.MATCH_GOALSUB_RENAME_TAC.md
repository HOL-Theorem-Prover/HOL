## `MATCH_GOALSUB_RENAME_TAC`

``` hol4
Q.MATCH_GOALSUB_RENAME_TAC : term quotation -> tactic
```

------------------------------------------------------------------------

Renames a goal in accordance with a pattern matched against a subterm of
the goal.

A call to `MATCH_GOALSUB_RENAME_TAC pat` attempts to find a match for
the pattern `pat` in the current goal (using `gen_find_term` to find a
sub-term of the goal that matches). If a match is found, the goal is
adjusted so that the variables occurring in the pattern now also appear
in the goal. This may rename variables in the goal, or even cause larger
sub-terms to be replaced by variables (as with `SPEC_TAC`). Underscores
may be used in `pat` to indicate "don't care" bindings, where no
renaming or instantiation will take place.

### Failure

Fails if there is no sub-term of the goal that matches the pattern.
Fails if the instantiation changes a pattern variable that already
exists in the goal.

### Example

If the goal is

``` hol4
    ?- !x. x * 2 < y * (z + 1) * (y + a)
```

then applying `` Q.MATCH_GOALSUB_RENAME_TAC `y + c` `` will match the
pattern `y + c` against the various subterms within the goal. The first
obvious match, with `z + 1` will be rejected because the variable `y` is
free in the goal, and is treated as if it were a local constant. Because
of this, `y + a` is the matching sub-term, and after renaming the goal
becomes

``` hol4
    ?- !x. x * 2 < y * (z + 1) * (y + c)
```

### See also

[`Q.MATCH_RENAME_TAC`](#Q.MATCH_RENAME_TAC)
