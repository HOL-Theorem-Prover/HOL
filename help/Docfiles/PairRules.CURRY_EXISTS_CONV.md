## `CURRY_EXISTS_CONV`

``` hol4
PairRules.CURRY_EXISTS_CONV : conv
```

------------------------------------------------------------------------

Currys paired existential quantifications into consecutive existential
quantifications.

### Example

``` hol4
- CURRY_EXISTS_CONV (Term `?(x,y). x + y = y + x`);
> val it = |- (?(x,y). x + y = y + x) = ?x y. x + y = y + x : thm

- CURRY_EXISTS_CONV (Term `?((w,x),(y,z)). w+x+y+z = z+y+x+w`);
> val it =
    |- (?((w,x),y,z). w + x + y + z = z + y + x + w) =
       ?(w,x) (y,z). w + x + y + z = z + y + x + w : thm
```

### Failure

`CURRY_EXISTS_CONV tm` fails if `tm` is not a paired existential
quantification.

### See also

[`PairRules.CURRY_CONV`](#PairRules.CURRY_CONV),
[`PairRules.UNCURRY_CONV`](#PairRules.UNCURRY_CONV),
[`PairRules.UNCURRY_EXISTS_CONV`](#PairRules.UNCURRY_EXISTS_CONV),
[`PairRules.CURRY_FORALL_CONV`](#PairRules.CURRY_FORALL_CONV),
[`PairRules.UNCURRY_FORALL_CONV`](#PairRules.UNCURRY_FORALL_CONV)
