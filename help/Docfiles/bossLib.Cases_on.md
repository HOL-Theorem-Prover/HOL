## `Cases_on`

``` hol4
bossLib.Cases_on : term quotation -> tactic
```

------------------------------------------------------------------------

Performs case analysis on the type of a given term.

An application `Cases_on M` performs a case-split based on the type `ty`
of `M`, using the cases theorem for `ty` from the global `TypeBase`
database.

`Cases_on` can be used to specify variables that are buried in the
quantifier prefix. `Cases_on` can also be used to perform case splits on
non-variable terms. If `M` is a non-variable term that does not occur
bound in the goal, then the cases theorem is instantiated with `M` and
used to generate as many sub-goals as there are disjuncts in the cases
theorem.

### Failure

Fails if `ty` does not have a case theorem in the `TypeBase`.

### Example

None yet.

### See also

[`bossLib.Cases`](#bossLib.Cases), [`bossLib.Induct`](#bossLib.Induct),
[`bossLib.Induct_on`](#bossLib.Induct_on),
[`Tactic.STRUCT_CASES_TAC`](#Tactic.STRUCT_CASES_TAC)
