## `MAP_FIRST`

``` hol4
Tactical.MAP_FIRST : (('a -> tactic) -> 'a list -> tactic)
```

------------------------------------------------------------------------

Applies first tactic that succeeds in a list given by mapping a function
over a list.

When applied to a tactic-producing function `f` and an operand list
`[x1,...,xn]`, the elements of which have the same type as `f`'s domain
type, `MAP_FIRST` maps the function `f` over the list, producing a list
of tactics, then tries applying these tactics to the goal till one
succeeds. If `f(xm)` is the first to succeed, then the overall effect is
the same as applying `f(xm)`. Thus:

``` hol4
   MAP_FIRST f [x1,...,xn] = (f x1) ORELSE ... ORELSE (f xn)
```

### Failure

The application of `MAP_FIRST` to a function and tactic list fails iff
the function does when applied to any of the elements of the list. The
resulting tactic fails iff all the resulting tactics fail when applied
to the goal.

### See also

[`Tactical.EVERY`](#Tactical.EVERY),
[`Tactical.FIRST`](#Tactical.FIRST),
[`Tactical.MAP_EVERY`](#Tactical.MAP_EVERY),
[`Tactical.ORELSE`](#Tactical.ORELSE)
