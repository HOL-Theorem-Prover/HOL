## `REDUCE_RULE`

``` hol4
reduceLib.REDUCE_RULE : thm -> thm
```

------------------------------------------------------------------------

Performs arithmetic or boolean reduction on a theorem at all levels
possible.

`REDUCE_RULE` attempts to transform a theorem by applying `REDUCE_CONV`.

### Failure

Never fails, but may just return the original theorem.

### Example

``` hol4
> reduceLib.REDUCE_RULE (ASSUME “x = 100 + (60 - 17)”);
val it = [.] ⊢ x = 143 : thm

> reduceLib.REDUCE_RULE (REFL “100 + 12 DIV 6”);
val it = ⊢ T : thm
```

### See also

[`reduceLib.RED_CONV`](#reduceLib.RED_CONV),
[`reduceLib.REDUCE_CONV`](#reduceLib.REDUCE_CONV),
[`reduceLib.REDUCE_TAC`](#reduceLib.REDUCE_TAC)
