## `subgoal`

``` hol4
bossLib.subgoal : term quotation -> tactic
```

------------------------------------------------------------------------

Produces a subgoal.

A call to `subgoal q` is equivalent (by definition) to a call to
`Q.SUBGOAL_THEN q STRIP_ASSUME_TAC`.

### Failure

Fails if the provided quotation does not parse to a term of boolean type
in the context of the current goal.

### Comments

The `subgoal` tactic is also available via the name `sg`.

### See also

[`bossLib.by`](#bossLib.by), [`Q.SUBGOAL_THEN`](#Q.SUBGOAL_THEN)
