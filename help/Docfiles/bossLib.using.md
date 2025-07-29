## `using`

``` hol4
bossLib.using : tactic * thm -> tactic
```

------------------------------------------------------------------------

Specifies alternative theorem to use for given tactic

The standard HOL environment has `using` an infix, so one writes
`tac using thm`. Such a call stashes an encoding of `thm`'s name onto
the goal's assumption list and then calls `tac`. If `tac` is aware of
the possibility, it can use this theorem instead of the theorem it would
usually consult. After `tac` completes, the implementation of `using`
removes the reference.

This is typically used with the tactics `Induct`, `Induct_on`, `Cases`,
or `Cases_on` which consult the TypeBase to find the theorems their
underlying code requires.

### Failure

Fails if the specified theorem has no hypotheses, is polymorphic, and
cannot be found by reverse lookup in the theorem database (using
`DB.revlookup`). Also fails if the underlying tactic fails.

### Example

``` hol4
Induct_on ‘l’ using SNOC_INDUCT
```

sets up an induction on the term `“l”` using the `SNOC_INDUCT` principle
("structural induction from the back of the list").

### Comments

Tactics unaware of the possibility of the presence of augmented
assumption lists can behave strangely.

### See also

[`bossLib.Induct_on`](#bossLib.Induct_on),
[`markerSyntax.MK_USING`](#markerSyntax.MK_USING)
