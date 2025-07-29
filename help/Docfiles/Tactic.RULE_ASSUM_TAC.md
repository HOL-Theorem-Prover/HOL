## `RULE_ASSUM_TAC`

``` hol4
Tactic.RULE_ASSUM_TAC : ((thm -> thm) -> tactic)
```

------------------------------------------------------------------------

Maps an inference rule over the assumptions of a goal.

When applied to an inference rule `f` and a goal `({A1,...,An} ?- t)`,
the `RULE_ASSUM_TAC` tactical applies the inference rule to each of the
`ASSUME`d assumptions to give a new goal.

``` hol4
             {A1,...,An} ?- t
   ====================================  RULE_ASSUM_TAC f
    {f(A1 |- A1),...,f(An |- An)} ?- t
```

### Failure

The application of `RULE_ASSUM_TAC f` to a goal fails iff `f` fails when
applied to any of the assumptions of the goal.

### Comments

It does not matter if the goal has no assumptions, but in this case
`RULE_ASSUM_TAC` has no effect.

### See also

[`Tactic.RULE_L_ASSUM_TAC`](#Tactic.RULE_L_ASSUM_TAC),
[`Tactical.ASSUM_LIST`](#Tactical.ASSUM_LIST),
[`Tactical.MAP_EVERY`](#Tactical.MAP_EVERY),
[`Tactical.MAP_FIRST`](#Tactical.MAP_FIRST),
[`Tactical.POP_ASSUM_LIST`](#Tactical.POP_ASSUM_LIST)
