## `RULE_L_ASSUM_TAC`

``` hol4
Tactic.RULE_L_ASSUM_TAC : ((thm -> thm list) -> tactic)
```

------------------------------------------------------------------------

Maps an inference rule, which produces a list of result theorems, over
the assumptions of a goal.

When applied to an inference rule `f` and a goal `({A1,...,An} ?- t)`,
the `RULE_L_ASSUM_TAC` tactical applies the inference rule to each of
the `ASSUME`d assumptions to give a new goal.

``` hol4
             {A1,...,An} ?- t
   ====================================  RULE_L_ASSUM_TAC f
    {f(A1 |- A1),...,f(An |- An)} ?- t
```

Here each `f(Ai |- Ai)` is a list of assumptions.

### Failure

The application of `RULE_L_ASSUM_TAC f` to a goal fails iff `f` fails
when applied to any of the assumptions of the goal.

### Comments

It does not matter if the goal has no assumptions, but in this case
`RULE_L_ASSUM_TAC` has no effect.

### Example

With a goal

``` hol4
g
------------------------------------
  0.  a /\ b
  1.  c
  2.  d /\ e /\ f
```

the tactic `RULE_L_ASSUM_TAC CONJUNCTS` gives the new goal

``` hol4
g
------------------------------------
  0.  a
  1.  b
  2.  c
  3.  d
  4.  e
  5.  f
```

`RULE_L_ASSUM_TAC` can also be used to delete unwanted assumptions: let
`f ass = [ass]` for an assumption which is to be kept, and `f ass = []`
for an assumption which is to be deleted.

### See also

[`Tactic.RULE_ASSUM_TAC`](#Tactic.RULE_ASSUM_TAC),
[`Tactical.ASSUM_LIST`](#Tactical.ASSUM_LIST),
[`Tactical.MAP_EVERY`](#Tactical.MAP_EVERY),
[`Tactical.MAP_FIRST`](#Tactical.MAP_FIRST),
[`Tactical.POP_ASSUM_LIST`](#Tactical.POP_ASSUM_LIST)
