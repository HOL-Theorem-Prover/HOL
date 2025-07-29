## `namedCases`

``` hol4
BasicProvers.namedCases : string list -> tactic
```

------------------------------------------------------------------------

Case split on type of leading universally quantified variable in the
goal, using given names for introduced constructor arguments.

`bossLib.namedCases` is identical to `BasicProvers.namedCases`.

### See also

[`bossLib.namedCases_on`](#bossLib.namedCases_on),
[`bossLib.Cases_on`](#bossLib.Cases_on),
[`bossLib.Cases`](#bossLib.Cases)
