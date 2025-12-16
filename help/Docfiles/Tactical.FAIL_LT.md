## `FAIL_LT`

``` hol4
Tactical.FAIL_LT : string -> list_tactic
```

------------------------------------------------------------------------

List-tactic which always fails, with the supplied string.

Whatever goal list it is applied to, `FAIL_LT s` always fails with the
string `s`.

### Failure

The application of `FAIL_LT` to a string never fails; the resulting
list-tactic always fails.

### See also

[`Tactical.FAIL_TAC`](#Tactical.FAIL_TAC),
[`Tactical.ALL_LT`](#Tactical.ALL_LT),
[`Tactical.NO_LT`](#Tactical.NO_LT)
