## `MAP_EVERY`

``` hol4
Tactical.MAP_EVERY : (('a -> tactic) -> 'a list -> tactic)
```

------------------------------------------------------------------------

Sequentially applies all tactics given by mapping a function over a
list.

When applied to a tactic-producing function `f` and an operand list
`[x1;...;xn]`, the elements of which have the same type as `f`'s domain
type, `MAP_EVERY` maps the function `f` over the list, producing a list
of tactics, then applies these tactics in sequence as in the case of
`EVERY`. The effect is:

``` hol4
   MAP_EVERY f [x1;...;xn] = (f x1) THEN ... THEN (f xn)
```

If the operand list is empty, then `MAP_EVERY` has no effect.

### Failure

The application of `MAP_EVERY` to a function and operand list fails iff
the function fails when applied to any element in the list. The
resulting tactic fails iff any of the resulting tactics fails.

### Example

A convenient way of doing case analysis over several boolean variables
is:

``` hol4
   MAP_EVERY BOOL_CASES_TAC ["var1:bool";...;"varn:bool"]
```

### See also

[`Tactical.EVERY`](#Tactical.EVERY),
[`Tactical.FIRST`](#Tactical.FIRST),
[`Tactical.MAP_FIRST`](#Tactical.MAP_FIRST),
[`Tactical.THEN`](#Tactical.THEN)
