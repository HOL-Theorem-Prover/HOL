## `asm_x`

``` hol4
bossLib.asm_x : string -> thm_tactic -> tactic
```

------------------------------------------------------------------------

Passes the named assumption to the continuation.

Given a name `n`, applies the continuation to the assumption `n :- t` and
removes `n :- t` from the assumption list.

### Failure

Fails if there is no assumption with name `n`, i.e., no assumption
`n :- t`, or if the continuation fails for the given assumption.


### See also

[`bossLib.asm`](#bossLib.asm),
[`bossLib.mk_asm`](#bossLib.mk_asm)
