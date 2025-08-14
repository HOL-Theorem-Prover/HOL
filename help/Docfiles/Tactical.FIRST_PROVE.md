## `FIRST_PROVE`

``` hol4
Tactical.FIRST_PROVE : (tactic list -> tactic)
```

------------------------------------------------------------------------

Applies the first tactic in a tactic list which completely proves the
goal.

When applied to a list of tactics `[T1;...;Tn]`, and a goal `g`, the
tactical `FIRST_PROVE` tries applying the tactics to the goal until one
proves the goal. If the first tactic which proves the goal is `Tm`, then
the effect is the same as just `Tm`. Thus `FIRST_PROVE` effectively
behaves as follows:

``` hol4
   FIRST_PROVE [T1;...;Tn] = (T1 THEN NO_TAC) ORELSE ... ORELSE (Tn THEN NO_TAC)
```

### Failure

The application of `FIRST_PROVE` to a tactic list never fails. The
resulting tactic fails iff none of the supplied tactics completely
proves the goal by itself, or if the tactic list is empty.

### See also

[`Tactical.EVERY`](#Tactical.EVERY),
[`Tactical.ORELSE`](#Tactical.ORELSE),
[`Tactical.FIRST`](#Tactical.FIRST)
