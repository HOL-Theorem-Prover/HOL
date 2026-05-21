## `UNCURRY_CONV`

``` hol4
PairRules.UNCURRY_CONV : conv
```

------------------------------------------------------------------------

Uncurrys an application of an abstraction.

### Example

``` hol4
- UNCURRY_CONV (Term `(\x y. x + y) 1 2`);
> val it = |- (\x y. x + y) 1 2 = (\(x,y). x + y) (1,2) : thm
```

### Failure

`UNCURRY_CONV tm` fails if `tm` is not double abstraction applied to two
arguments

### See also

[`PairRules.CURRY_CONV`](#PairRules.CURRY_CONV)
