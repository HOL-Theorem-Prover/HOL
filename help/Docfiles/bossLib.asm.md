## `asm`

``` hol4
bossLib.asm : string -> thm_tactic -> tactic
```

------------------------------------------------------------------------

Passes the named assumption to the continuation.

Given a name `n`, applies the continuation to the assumption `n :- t`.

### Failure

Fails if there is no assumption with name `n`, i.e., no assumption
`n :- t`, or if the continuation fails for the given assumption.


### See also

[`bossLib.asm_x`](#bossLib.asm_x),
[`bossLib.mk_asm`](#bossLib.mk_asm)
