## `POP_ASSUM_LIST`

``` hol4
Tactical.POP_ASSUM_LIST : (thm list -> tactic) -> tactic
```

------------------------------------------------------------------------

Generates a tactic from the assumptions, discards the assumptions and
applies the tactic.

When applied to a function and a goal, `POP_ASSUM_LIST` applies the
function to a list of theorems corresponding to the `ASSUME`d
assumptions of the goal, then applies the resulting tactic to the goal
with an empty assumption list.

``` hol4
    POP_ASSUM_LIST f ({A1,...,An} ?- t) = f [A1 |- A1, ..., An |- An] (?- t)
```

### Failure

Fails if the function fails when applied to the list of `ASSUME`d
assumptions, or if the resulting tactic fails when applied to the goal
with no assumptions.

### Comments

There is nothing magical about `POP_ASSUM_LIST`: the same effect can be
achieved by using `ASSUME a` explicitly wherever the assumption `a` is
used. If `POP_ASSUM_LIST` is used, it is unwise to select elements by
number from the `ASSUME`d-assumption list, since this introduces a
dependency on ordering.

### Example

Suppose we have a goal of the following form:

``` hol4
   {a /\ b, c, (d /\ e) /\ f} ?- t
```

Then we can split the conjunctions in the assumption list apart by
applying the tactic:

``` hol4
   POP_ASSUM_LIST (MAP_EVERY STRIP_ASSUME_TAC)
```

which results in the new goal:

``` hol4
   {a, b, c, d, e, f} ?- t
```

Making more delicate use of the assumption list than simply rewriting or
using resolution.

### See also

[`Tactical.ASSUM_LIST`](#Tactical.ASSUM_LIST),
[`Tactical.EVERY_ASSUM`](#Tactical.EVERY_ASSUM),
[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC),
[`Tactical.POP_ASSUM`](#Tactical.POP_ASSUM),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC)
