## `CURRY_CONV`

``` hol4
PairRules.CURRY_CONV : conv
```

------------------------------------------------------------------------

Currys an application of a paired abstraction.

### Example

``` hol4
- CURRY_CONV (Term `(\(x,y). x + y) (1,2)`);
> val it = |- (\(x,y). x + y) (1,2) = (\x y. x + y) 1 2 : thm

- CURRY_CONV (Term `(\(x,y). x + y) z`);
> val it = |- (\(x,y). x + y) z = (\x y. x + y) (FST z) (SND z) : thm
```

### Failure

`CURRY_CONV tm` fails if `tm` is not an application of a paired
abstraction.

### See also

[`PairRules.UNCURRY_CONV`](#PairRules.UNCURRY_CONV)
