## `UNCURRY_FORALL_CONV`

``` hol4
PairRules.UNCURRY_FORALL_CONV : conv
```

------------------------------------------------------------------------

Uncurrys consecutive universal quantifications into a paired universal
quantification.

### Example

``` hol4
- UNCURRY_FORALL_CONV (Term `!x y. x + y = y + x`);
> val it = |- (!x y. x + y = y + x) = !(x,y). x + y = y + x : thm

- UNCURRY_FORALL_CONV (Term `!(w,x) (y,z). w+x+y+z = z+y+x+w`);
> val it =
    |- (!(w,x) (y,z). w + x + y + z = z + y + x + w) =
       !((w,x),y,z). w + x + y + z = z + y + x + w : thm
```

### Failure

`UNCURRY_FORALL_CONV tm` fails if `tm` is not a consecutive universal
quantification.

### See also

[`PairRules.CURRY_CONV`](#PairRules.CURRY_CONV),
[`PairRules.UNCURRY_CONV`](#PairRules.UNCURRY_CONV),
[`PairRules.CURRY_FORALL_CONV`](#PairRules.CURRY_FORALL_CONV),
[`PairRules.CURRY_EXISTS_CONV`](#PairRules.CURRY_EXISTS_CONV),
[`PairRules.UNCURRY_EXISTS_CONV`](#PairRules.UNCURRY_EXISTS_CONV)
