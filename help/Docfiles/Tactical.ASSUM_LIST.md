## `ASSUM_LIST`

``` hol4
Tactical.ASSUM_LIST : (thm list -> tactic) -> tactic
```

------------------------------------------------------------------------

Applies a tactic generated from the goal's assumption list.

When applied to a function of type `thm list -> tactic` and a goal,
`ASSUM_LIST` constructs a tactic by applying `f` to a list of `ASSUME`d
assumptions of the goal, then applies that tactic to the goal.

``` hol4
   ASSUM_LIST f ({A1,...,An} ?- t)
         = f [A1 |- A1, ... , An |- An] ({A1,...,An} ?- t)
```

### Failure

Fails if the function fails when applied to the list of `ASSUME`d
assumptions, or if the resulting tactic fails when applied to the goal.

### Comments

There is nothing magical about `ASSUM_LIST`: the same effect can usually
be achieved just as conveniently by using `ASSUME a` wherever the
assumption `a` is needed. If `ASSUM_LIST` is used, it is extremely
unwise to use a function which selects elements from its argument list
by number, since the ordering of assumptions should not be relied on.

### Example

The tactic:

``` hol4
   ASSUM_LIST SUBST_TAC
```

makes a single parallel substitution using all the assumptions, which
can be useful if the rewriting tactics are too blunt for the required
task.

Making more careful use of the assumption list than simply rewriting or
using resolution.

### See also

[`Rewrite.ASM_REWRITE_TAC`](#Rewrite.ASM_REWRITE_TAC),
[`Tactical.EVERY_ASSUM`](#Tactical.EVERY_ASSUM),
[`Tactic.IMP_RES_TAC`](#Tactic.IMP_RES_TAC),
[`Tactical.POP_ASSUM`](#Tactical.POP_ASSUM),
[`Tactical.POP_ASSUM_LIST`](#Tactical.POP_ASSUM_LIST),
[`Rewrite.REWRITE_TAC`](#Rewrite.REWRITE_TAC)
