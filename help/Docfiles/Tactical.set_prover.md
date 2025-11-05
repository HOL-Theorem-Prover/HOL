## `set_prover`

``` hol4
Tactical.set_prover : (goal * tactic -> thm) -> unit
```

------------------------------------------------------------------------

Specifies the function to be used by `prove_goal` and `prove`.

A call to `set_prover f` sets the function used by `prove_goal` and `prove` to be `f`.
The initial value is `TAC_PROOF`.
The `prove` function takes a single term `t` as argument and passes this along with an empty list of assumptions to `f`.

### Failure

Never fails.

### Comments

This function is used by `Holmake` when called with the `--noqof` and `--fast` options to set the prove function to one that will call `cheat` as appropriate (if a tactic otherwise fails, or in all cases, respectively).

### See also

[`Tactical.prove`](#Tactical.prove),
[`Tactical.prove_goal`](#Tactical.prove_goal).
