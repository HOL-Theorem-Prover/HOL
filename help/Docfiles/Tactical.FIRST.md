## `FIRST`

``` hol4
Tactical.FIRST : (tactic list -> tactic)
```

------------------------------------------------------------------------

Applies the first tactic in a tactic list which succeeds.

When applied to a list of tactics `[T1;...;Tn]`, and a goal `g`, the
tactical `FIRST` tries applying the tactics to the goal until one
succeeds. If the first tactic which succeeds is `Tm`, then the effect is
the same as just `Tm`. Thus `FIRST` effectively behaves as follows:

``` hol4
   FIRST [T1;...;Tn] = T1 ORELSE ... ORELSE Tn
```

### Failure

The application of `FIRST` to a tactic list never fails. The resulting
tactic fails iff all the component tactics do when applied to the goal,
or if the tactic list is empty.

### See also

[`Tactical.EVERY`](#Tactical.EVERY),
[`Tactical.ORELSE`](#Tactical.ORELSE)
